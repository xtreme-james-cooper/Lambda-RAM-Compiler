theory LetFloating
  imports Multisubst "../00Utils/Iteration" 
begin

subsection \<open>Let Floating\<close>

text \<open>We perform a small source-level optimization here that will pay off for our tree code. Our 
language is a lexically-scoped one, meaning that the application of a function is evaluated in the 
function's static defining environment rather than its dynamic evaluating environment. This has a 
number of significant consequences - alpha conversion, type safety - but what we are concerned with 
now is that it means that every time we _finish_ evaluating a function application, we discard the
 current environment and return to the previous one. Now, consider the effects of a let-expression 
on the environment. When the evaluation of the definition is finished, its value is pushed into the 
environment; when the evaluation of the body is finished, it is popped off. But if the 
let-expression is the last thing being evaluated in a function body, the pop will be followed by a 
return - which means that the pop was unnecessary, since the environment is about to be discarded 
anyways. By collapsing together all \<open>PopEnv\<^sub>e ... PopEnv\<^sub>e, Return\<^sub>e\<close> sequences into just a \<open>Return\<^sub>e\<close>, 
we can save ever executing these \<open>PopEnv\<^sub>e\<close>s. But we can do even better.\<close>

text \<open>If we have an expression like \<open>App\<^sub>s (Let\<^sub>s e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2) e\<^sub>2\<close>, the above optimization will not apply; 
the code for \<open>e\<^sub>2\<close> (and an \<open>Apply\<^sub>e\<close>) will sit between the \<open>PopEnv\<^sub>e\<close> and any eventual \<open>Return\<^sub>e\<close>. But 
the expression \<open>Let\<^sub>s e\<^sub>1\<^sub>1 (App\<^sub>s e\<^sub>1\<^sub>2 (incr\<^sub>s 0 e\<^sub>2))\<close> has the same runtime behaviour - since we are in an 
eagerly-evaluated language, all three subexpressions must be evaluated in the same order - but the 
scope of the \<open>Let\<^sub>s\<close> now extends to the end of the expression. Similar transformations can be applied 
to \<open>App\<^sub>s e\<^sub>1 (Let\<^sub>s e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2)\<close> and \<open>Let\<^sub>s (Let\<^sub>s e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2) e\<^sub>2\<close>, meaning that we can arrive at a form where 
every lambda-expression is of the shape \<open>Lam\<^sub>s t (Let\<^sub>s e\<^sub>1 (... (Let\<^sub>s e\<^sub>n e) ...))\<close>, n \<ge> 0, and there 
are no \<open>Let\<^sub>s\<close>s in any of the \<open>e\<close>s except under similarly-shaped lambda-expressions. (The top-level 
program could in general not be a lambda-expression, but it will end with a \<open>Return\<^sub>e\<close> as well, so 
similar remarks apply.) This means that _every_ \<open>PopEnv\<^sub>e\<close> will occur right before a \<open>Return\<^sub>e\<close>, and 
so can be eliminated - and we can avoid compiling any code for \<open>PopEnv\<^sub>e\<close> at all.\<close>

text \<open>There is one slight catch - naively floating the lets out of the argument of an application 
\<open>App\<^sub>s e\<^sub>1 (Let\<^sub>s e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2)\<close> changes the evaluation order - before, \<open>e\<^sub>1\<close> is evaluated before \<open>e\<^sub>2\<^sub>1\<close>, but 
once the latter has been floated out, it will be evaluated first. This is not necessarily fatal, 
since our language is normalizing and has no side effects, but this would not extend to a richer 
language, and would force us to work with big-step evaluation for proofs instead of the simpler 
small-step relation. Fortunately, we can solve it another way: just let-bind \<open>e\<^sub>1\<close> too, thereby 
fixing the evaluation order. Because of our lifting of application left-sides, there will be one 
extra evaluation step substituting it back away in each \<open>App\<^sub>s\<close>, equivalent to one extra \<open>Lookup\<^sub>e\<close> in 
the compiled tree-code. It will be made up for, hopefully, by the savings from not having to pop the 
environments at the end of each function.\<close>

text \<open>This transformation has one even more useful consequence, but it is not yet implemented - see
the "Further Work" section at the end.\<close>

text \<open>We begin by defining our let-floated normal form.\<close>

primrec let_free :: "expr\<^sub>d \<Rightarrow> bool" where
  "let_free (Var\<^sub>d x) = True"
| "let_free (Const\<^sub>d n) = True"
| "let_free (Lam\<^sub>d t e) = True"
| "let_free (App\<^sub>d e\<^sub>1 e\<^sub>2) = (let_free e\<^sub>1 \<and> let_free e\<^sub>2)"
| "let_free (Let\<^sub>d e\<^sub>1 e\<^sub>2) = False"

primrec let_floated :: "expr\<^sub>d \<Rightarrow> bool" where
  "let_floated (Var\<^sub>d x) = True"
| "let_floated (Const\<^sub>d n) = True"
| "let_floated (Lam\<^sub>d t e) = let_floated e"
| "let_floated (App\<^sub>d e\<^sub>1 e\<^sub>2) = (let_free e\<^sub>1 \<and> let_free e\<^sub>2 \<and> let_floated e\<^sub>1 \<and> let_floated e\<^sub>2)"
| "let_floated (Let\<^sub>d e\<^sub>1 e\<^sub>2) = (let_free e\<^sub>1 \<and> let_floated e\<^sub>1 \<and> let_floated e\<^sub>2)"

text \<open>Then, the let-floating transformation itself. We have to define a multiple-increment function
to make sure the variables match properly.\<close>

primrec multiincr :: "nat \<Rightarrow> nat \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "multiincr 0 y = id"
| "multiincr (Suc x) y = incr\<^sub>d y \<circ> multiincr x y"

lemma multiincr_var [simp]: "multiincr x 0 (Var\<^sub>d 0) = Var\<^sub>d x"
  by (induction x) simp_all

lemma multiincr_incr_swap' [simp]: "multiincr x y (incr\<^sub>d y e) = incr\<^sub>d y (multiincr x y e)"
  by (induction x) simp_all

lemma multiincr_subst_swap' [simp]: "y \<le> z \<Longrightarrow> 
    multiincr x y (subst\<^sub>d z e' e) = subst\<^sub>d (x + z) (multiincr x y e') (multiincr x y e)"
  by (induction x) simp_all

lemma multiincr_incr_swap [simp]: "z \<ge> y \<Longrightarrow> 
    multiincr x y (incr\<^sub>d z e) = incr\<^sub>d (z + x) (multiincr x y e)"
  by (induction x) simp_all

lemma multiincr_incr_swap2 [simp]: "z \<le> y \<Longrightarrow> 
    multiincr x (Suc y) (incr\<^sub>d z e) = incr\<^sub>d z (multiincr x y e)"
  by (induction x) simp_all

lemma subst_multiincr_lemma [simp]: "(\<lambda>k. subst\<^sub>d (Suc (k + x)) (incr\<^sub>d y (multiincr k y e))) = 
    ((\<lambda>k. subst\<^sub>d (k + x) (multiincr k y e)) \<circ> Suc)"
  by auto

lemma multiincr_plus [simp]: "multiincr n k (multiincr k 0 e) = multiincr k 0 (multiincr n 0 e)"
  by (induction k arbitrary: n) simp_all

lemma multiincr_val [simp]: "value\<^sub>d (multiincr x y e) = value\<^sub>d e"
  by (induction x) simp_all

lemma incr_multiincr_higher: "incr\<^sub>d y (multiincr x y e) = incr\<^sub>d (x + y) (multiincr x y e)"
  by (induction x) simp_all

lemma multiincr_lam [simp]: "multiincr x y (Lam\<^sub>d t e) = Lam\<^sub>d t (multiincr x (Suc y) e)"
  by (induction x) simp_all

lemma multiincr_app [simp]: "multiincr x y (App\<^sub>d e\<^sub>1 e\<^sub>2) = App\<^sub>d (multiincr x y e\<^sub>1) (multiincr x y e\<^sub>2)"
  by (induction x) simp_all

lemma multiincr_let [simp]: "multiincr x y (Let\<^sub>d e\<^sub>1 e\<^sub>2) = 
    Let\<^sub>d (multiincr x y e\<^sub>1) (multiincr x (Suc y) e\<^sub>2)"
  by (induction x) simp_all

lemma multiincr_subst [simp]: "z \<le> y \<Longrightarrow> multiincr x y (subst\<^sub>d z e' e) = 
    subst\<^sub>d z (multiincr x y e') (multiincr x (Suc y) e)"
  by (induction x) simp_all

lemma eval_multiincr [simp]: "e \<leadsto>\<^sub>d e' \<Longrightarrow> multiincr x y e \<leadsto>\<^sub>d multiincr x y e'"
  by (induction e e' rule: eval\<^sub>d.induct) simp_all

fun strip_lets :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d list" where
  "strip_lets (Let\<^sub>d e\<^sub>1 e\<^sub>2) = e\<^sub>1 # strip_lets e\<^sub>2"
| "strip_lets e = []"

fun inner_expr :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "inner_expr (Let\<^sub>d e\<^sub>1 e\<^sub>2) = inner_expr e\<^sub>2"
| "inner_expr e = e"

definition reapply_lets :: "expr\<^sub>d list \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "reapply_lets es e = foldr Let\<^sub>d es e"

lemma strip_lets_nil [dest]: "strip_lets e = [] \<Longrightarrow> inner_expr e = e"
  by (induction e rule: strip_lets.induct) simp_all

lemma strip_reapply_lets [simp]: "reapply_lets (strip_lets e) (inner_expr e) = e"
  by (induction e rule: strip_lets.induct) (auto simp add: reapply_lets_def)

lemma reapply_strip_lets [simp]: "strip_lets (reapply_lets es e) = es @ strip_lets e"
  by (induction es) (simp_all add: reapply_lets_def)

lemma reapply_next_lets [simp]: "inner_expr (reapply_lets es e) = inner_expr e"
  by (induction es) (simp_all add: reapply_lets_def)

lemma reapply_nil [simp]: "reapply_lets [] e = e"
  by (simp add: reapply_lets_def)

lemma reapply_append [simp]: "reapply_lets (es @ es') e = reapply_lets es (reapply_lets es' e)"
  by (simp add: reapply_lets_def)

fun is_reducible :: "expr\<^sub>d \<Rightarrow> bool" where
  "is_reducible (App\<^sub>d e\<^sub>1 e\<^sub>2) = True"
| "is_reducible e = False"

lemma value_not_reducible [simp]: "value\<^sub>d v \<Longrightarrow> \<not> is_reducible v"
  by (induction v) simp_all

lemma is_reducible_incr [simp]: "is_reducible (incr\<^sub>d x e) = is_reducible e"
  by (induction e) simp_all

lemma is_reducible_subst [simp]: "value\<^sub>d v \<Longrightarrow> is_reducible (subst\<^sub>d x v e) = is_reducible e"
  by (induction e) simp_all

primrec float_lets :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "float_lets (Var\<^sub>d x) = Var\<^sub>d x"
| "float_lets (Const\<^sub>d n) = Const\<^sub>d n"
| "float_lets (Lam\<^sub>d t e) = Lam\<^sub>d t (float_lets e)"
| "float_lets (App\<^sub>d e\<^sub>1 e\<^sub>2) = (
    let es\<^sub>1 = strip_lets (float_lets e\<^sub>1)
    in let e\<^sub>1' = inner_expr (float_lets e\<^sub>1)
    in let es\<^sub>2 = strip_lets (float_lets e\<^sub>2) 
    in let e\<^sub>2' = inner_expr (float_lets e\<^sub>2) 
    in let es\<^sub>1' = if is_reducible e\<^sub>1' then es\<^sub>1 @ [e\<^sub>1'] else es\<^sub>1
    in let e\<^sub>1'' = if is_reducible e\<^sub>1' then Var\<^sub>d 0 else e\<^sub>1'
    in reapply_lets (es\<^sub>1' @ map_with_idx (multiincr (length es\<^sub>1')) es\<^sub>2) 
         (App\<^sub>d (multiincr (length es\<^sub>2) 0 e\<^sub>1'') (multiincr (length es\<^sub>1') (length es\<^sub>2) e\<^sub>2')))"
| "float_lets (Let\<^sub>d e\<^sub>1 e\<^sub>2) = (
    let es\<^sub>1 = strip_lets (float_lets e\<^sub>1)
    in reapply_lets es\<^sub>1 
          (Let\<^sub>d (inner_expr (float_lets e\<^sub>1)) (multiincr (length es\<^sub>1) 1 (float_lets e\<^sub>2))))"

lemma incr_let_free [simp]: "let_free (incr\<^sub>d x e) = let_free e"
  by (induction e arbitrary: x) simp_all

lemma incr_let_free_map [simp]: "list_all let_free (map (incr\<^sub>d x) es) = list_all let_free es"
  by (induction es) simp_all

lemma multiincr_let_free [simp]: "let_free (multiincr x y e) = let_free e"
  by (induction x) simp_all

lemma incr_let_floated [simp]: "let_floated (incr\<^sub>d x e) = let_floated e"
  by (induction e arbitrary: x) simp_all

lemma incr_let_floated_map [simp]: "list_all let_floated (map (incr\<^sub>d x) es) = 
    list_all let_floated es"
  by (induction es) simp_all

lemma multiincr_let_floated [simp]: "let_floated (multiincr x y e) = let_floated e"
  by (induction x) simp_all

lemma strip_lets_free [simp]: "let_floated e \<Longrightarrow> list_all let_free (strip_lets e)"
  by (induction e) simp_all

lemma inner_expr_free [simp]: "let_floated e \<Longrightarrow> let_free (inner_expr e)"
  by (induction e) simp_all

lemma strip_lets_normalized [simp]: "let_floated e \<Longrightarrow> list_all let_floated (strip_lets e)"
  by (induction e) simp_all

lemma inner_expr_normalized [simp]: "let_floated e \<Longrightarrow> let_floated (inner_expr e)"
  by (induction e) simp_all

lemma reapply_lets_normalized [simp]: "let_floated (reapply_lets es e) = 
    (list_all let_free es \<and> list_all let_floated es \<and> let_floated e)"
  by (induction es) (auto simp add: reapply_lets_def)

lemma float_lets_normalizes [simp]: "let_floated (float_lets e)"
  by (induction e) (simp_all add: Let_def)

text \<open>And the safety and correctness proofs:\<close>

inductive typing\<^sub>d_bindings :: "ty list \<Rightarrow> expr\<^sub>d list \<Rightarrow> ty list \<Rightarrow> bool" (infix "\<turnstile>\<^sub>d\<^sub>b _ :" 50) where
  tc\<^sub>d_bind_nil [simp]: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b [] : []" 
| tc\<^sub>d_bind_cons [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> insert_at 0 t \<Gamma> \<turnstile>\<^sub>d\<^sub>b es : ts \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d\<^sub>b e # es : ts @ [t]" 

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b [] : ts"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b e # es : ts"

lemma typing_bindings_append [simp]: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b es\<^sub>1 : ts\<^sub>1 \<Longrightarrow> ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d\<^sub>b es\<^sub>2 : ts\<^sub>2 \<Longrightarrow> 
  \<Gamma> \<turnstile>\<^sub>d\<^sub>b es\<^sub>1 @ es\<^sub>2 : ts\<^sub>2 @ ts\<^sub>1"
proof (induction es\<^sub>1 arbitrary: \<Gamma> ts\<^sub>1)
  case (Cons e es\<^sub>1)
  moreover then obtain t ts\<^sub>1' where T: "(\<Gamma> \<turnstile>\<^sub>d e : t) \<and> (insert_at 0 t \<Gamma> \<turnstile>\<^sub>d\<^sub>b es\<^sub>1 : ts\<^sub>1') \<and> 
    ts\<^sub>1 = ts\<^sub>1' @ [t]" by fastforce
  moreover with Cons have "ts\<^sub>1' @ insert_at 0 t \<Gamma> \<turnstile>\<^sub>d\<^sub>b es\<^sub>2 : ts\<^sub>2" by (induction \<Gamma>) simp_all
  ultimately show ?case using tc\<^sub>d_bind_cons by fastforce
qed auto

lemma typing_bindings_eq_length [simp]: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b es : ts \<Longrightarrow> length es = length ts"
  by (induction \<Gamma> es ts rule: typing\<^sub>d_bindings.induct) simp_all

lemma typing_bindings_eq_length_map [simp]: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b map_with_idx f es : ts \<Longrightarrow> length es = length ts"
proof (induction es arbitrary: \<Gamma> f ts)
  case (Cons e es)
  thus ?case by (induction ts rule: rev_induct) auto
qed auto

lemma typing_multiincr [simp]: "\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d e : t \<Longrightarrow> 
  \<Gamma>\<^sub>1 @ \<Gamma>' @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d multiincr (length \<Gamma>') (length \<Gamma>\<^sub>1) e : t"
proof (induction \<Gamma>')
  case (Cons tt \<Gamma>')
  moreover have "length \<Gamma>\<^sub>1 \<le> length (\<Gamma>\<^sub>1 @ \<Gamma>' @ \<Gamma>\<^sub>2)" by simp
  ultimately have "insert_at (length \<Gamma>\<^sub>1) tt (\<Gamma>\<^sub>1 @ \<Gamma>' @ \<Gamma>\<^sub>2) \<turnstile>\<^sub>d 
    incr\<^sub>d (length \<Gamma>\<^sub>1) (multiincr (length \<Gamma>') (length \<Gamma>\<^sub>1) e) : t" by (metis tc\<^sub>d_incr)
  thus ?case by simp
qed simp_all

lemma typing_binding_incr [simp]: "\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b es : ts \<Longrightarrow> 
  \<Gamma>\<^sub>1 @ t # \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b map_with_idx (\<lambda>k. incr\<^sub>d (k + length \<Gamma>\<^sub>1)) es : ts" 
proof (induction es arbitrary: \<Gamma>\<^sub>1 ts)
  case (Cons e es)
  then obtain ts' t' where T: "(\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d e : t') \<and> (insert_at 0 t' (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) \<turnstile>\<^sub>d\<^sub>b es : ts') \<and> 
    ts = ts' @ [t']" by fastforce
  hence "insert_at 0 t' \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b es : ts'" by simp
  with Cons have "insert_at 0 t' \<Gamma>\<^sub>1 @ t # \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b 
    map_with_idx (\<lambda>k. incr\<^sub>d (k + length (insert_at 0 t' \<Gamma>\<^sub>1))) es : ts'" by blast
  hence X: "insert_at 0 t' (\<Gamma>\<^sub>1 @ t # \<Gamma>\<^sub>2) \<turnstile>\<^sub>d\<^sub>b 
    map_with_idx ((\<lambda>k. incr\<^sub>d (k + length \<Gamma>\<^sub>1)) \<circ> Suc) es : ts'" by (simp add: comp_def)
  from T have "insert_at (length \<Gamma>\<^sub>1) t (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) \<turnstile>\<^sub>d incr\<^sub>d (length \<Gamma>\<^sub>1) e : t'"
    by (metis tc\<^sub>d_incr le_add1 length_append)
  with T X show ?case by simp
qed auto

lemma typing_binding_multiincr' [simp]: "\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b es : ts \<Longrightarrow> 
  \<Gamma>\<^sub>1 @ \<Gamma>' @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b map_with_idx (\<lambda>k. multiincr (length \<Gamma>') (k + length \<Gamma>\<^sub>1)) es : ts"
proof (induction \<Gamma>')
  case Nil
  then show ?case by simp
next
  case (Cons t \<Gamma>')
  hence "\<Gamma>\<^sub>1 @ t # \<Gamma>' @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b map_with_idx (\<lambda>k. multiincr (Suc (length \<Gamma>')) (k + length \<Gamma>\<^sub>1)) es : 
    ts" by simp
  hence "\<Gamma>\<^sub>1 @ (t # \<Gamma>') @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b map_with_idx (\<lambda>k. multiincr (length (t # \<Gamma>')) (k + length \<Gamma>\<^sub>1)) es : 
    ts" by (simp del: multiincr.simps)
  thus ?case by blast
qed

lemma typing_binding_multiincr: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b es : ts \<Longrightarrow> 
  \<Gamma>' @ \<Gamma> \<turnstile>\<^sub>d\<^sub>b map_with_idx (multiincr (length \<Gamma>')) es : ts"
proof -
  assume "\<Gamma> \<turnstile>\<^sub>d\<^sub>b es : ts"
  hence "[] @ \<Gamma>' @ \<Gamma> \<turnstile>\<^sub>d\<^sub>b map_with_idx (\<lambda>k. multiincr (length \<Gamma>') (k + length [])) es : ts" 
    by (metis typing_binding_multiincr' append_Nil list.size(3))
  thus ?thesis by simp
qed

lemma typing_strip_lets [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> 
  \<exists>ts. (\<Gamma> \<turnstile>\<^sub>d\<^sub>b strip_lets e : ts) \<and> (ts @ \<Gamma> \<turnstile>\<^sub>d inner_expr e : t)"
proof (induction \<Gamma> e t rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_var \<Gamma> x t)
  hence "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b [] : []) \<and> ([] @ \<Gamma> \<turnstile>\<^sub>d Var\<^sub>d x : t)" by auto
  hence "\<exists>ts. (\<Gamma> \<turnstile>\<^sub>d\<^sub>b [] : ts) \<and> (ts @ \<Gamma> \<turnstile>\<^sub>d Var\<^sub>d x : t)" by blast
  thus ?case by auto
next
  case (tc\<^sub>d_const \<Gamma> n)
  hence "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b [] : []) \<and> ([] @ \<Gamma> \<turnstile>\<^sub>d Const\<^sub>d n : Num)" by auto
  hence "\<exists>ts. (\<Gamma> \<turnstile>\<^sub>d\<^sub>b [] : ts) \<and> (ts @ \<Gamma> \<turnstile>\<^sub>d Const\<^sub>d n : Num)" by blast
  thus ?case by auto
next
  case (tc\<^sub>d_lam t\<^sub>1 \<Gamma> e t\<^sub>2)
  hence "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b [] : []) \<and> ([] @ \<Gamma> \<turnstile>\<^sub>d Lam\<^sub>d t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2)" by auto
  hence "\<exists>ts. (\<Gamma> \<turnstile>\<^sub>d\<^sub>b [] : ts) \<and> (ts @ \<Gamma> \<turnstile>\<^sub>d Lam\<^sub>d t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2)" by blast
  thus ?case by auto
next
  case (tc\<^sub>d_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  hence "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b [] : []) \<and> ([] @ \<Gamma> \<turnstile>\<^sub>d App\<^sub>d e\<^sub>1 e\<^sub>2 : t\<^sub>2)" by auto
  hence "\<exists>ts. (\<Gamma> \<turnstile>\<^sub>d\<^sub>b [] : ts) \<and> (ts @ \<Gamma> \<turnstile>\<^sub>d App\<^sub>d e\<^sub>1 e\<^sub>2 : t\<^sub>2)" by blast
  thus ?case by auto
next
  case (tc\<^sub>d_let \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
  moreover then obtain ts\<^sub>2 where "(insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d\<^sub>b strip_lets e\<^sub>2 : ts\<^sub>2) \<and> 
    (ts\<^sub>2 @ insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d inner_expr e\<^sub>2 : t\<^sub>2)" by auto
  moreover hence "ts\<^sub>2 @ [t\<^sub>1] @ \<Gamma> \<turnstile>\<^sub>d inner_expr e\<^sub>2 : t\<^sub>2" by (cases \<Gamma>) simp_all
  ultimately have "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b e\<^sub>1 # strip_lets e\<^sub>2 : ts\<^sub>2 @ [t\<^sub>1]) \<and> (ts\<^sub>2 @ [t\<^sub>1] @ \<Gamma> \<turnstile>\<^sub>d inner_expr e\<^sub>2 : t\<^sub>2)" 
    by simp
  thus ?case by auto
qed

lemma typing_reapply_lets [simp]: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b es : ts \<Longrightarrow> ts @ \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d reapply_lets es e : t"
proof (induction \<Gamma> es ts rule: typing\<^sub>d_bindings.induct)
  case (tc\<^sub>d_bind_cons \<Gamma> e t es ts)
  thus ?case by (induction \<Gamma>) (simp_all add: reapply_lets_def)
qed (simp_all add: reapply_lets_def)

theorem typing_float_lets [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d float_lets e : t"
proof (induction \<Gamma> e t rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  let ?es\<^sub>1 = "strip_lets (float_lets e\<^sub>1)"
  let ?e\<^sub>1' = "inner_expr (float_lets e\<^sub>1)"
  let ?es\<^sub>2 = "strip_lets (float_lets e\<^sub>2)"
  let ?es\<^sub>1' = "if is_reducible ?e\<^sub>1' then ?es\<^sub>1 @ [?e\<^sub>1'] else ?es\<^sub>1"
  from tc\<^sub>d_app obtain ts\<^sub>1 where T1: "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b ?es\<^sub>1 : ts\<^sub>1) \<and> (ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d ?e\<^sub>1' : Arrow t\<^sub>1 t\<^sub>2)" 
    by fastforce
  from tc\<^sub>d_app obtain ts\<^sub>2 where T2: "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b ?es\<^sub>2 : ts\<^sub>2) \<and> 
    (ts\<^sub>2 @ \<Gamma> \<turnstile>\<^sub>d inner_expr (float_lets e\<^sub>2) : t\<^sub>1)" by fastforce
  let ?ts\<^sub>1 = "if is_reducible ?e\<^sub>1' then Arrow t\<^sub>1 t\<^sub>2 # ts\<^sub>1 else ts\<^sub>1"
  from T1 have "insert_at 0 (Arrow t\<^sub>1 t\<^sub>2) (ts\<^sub>1 @ \<Gamma>) \<turnstile>\<^sub>d\<^sub>b [] : []" by simp
  with T1 have "\<Gamma> \<turnstile>\<^sub>d\<^sub>b ?es\<^sub>1 @ [?e\<^sub>1'] : [Arrow t\<^sub>1 t\<^sub>2] @ ts\<^sub>1" 
    by (metis typing_bindings_append tc\<^sub>d_bind_cons append_Nil)
  with T1 have TS1: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b ?es\<^sub>1' : ?ts\<^sub>1" by simp
  with T2 have TS2: "?ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d\<^sub>b map_with_idx (multiincr (length ?es\<^sub>1')) ?es\<^sub>2 : ts\<^sub>2" 
    by (simp add: typing_binding_multiincr)
  from T1 have "[] @ ?ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d (if is_reducible ?e\<^sub>1' then Var\<^sub>d 0 else ?e\<^sub>1') : Arrow t\<^sub>1 t\<^sub>2" by simp
  hence "[] @ ts\<^sub>2 @ ?ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d 
    multiincr (length ts\<^sub>2) 0 (if is_reducible ?e\<^sub>1' then Var\<^sub>d 0 else ?e\<^sub>1') : Arrow t\<^sub>1 t\<^sub>2" 
      by (metis list.size(3) typing_multiincr)
  with T2 TS1 TS2 show ?case by (simp add: Let_def)
next
  case (tc\<^sub>d_let \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
  let ?es\<^sub>1 = "strip_lets (float_lets e\<^sub>1)"
  from tc\<^sub>d_let obtain ts\<^sub>1 where T1: "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b ?es\<^sub>1 : ts\<^sub>1) \<and> 
    (ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d (inner_expr (float_lets e\<^sub>1)) : t\<^sub>1)" by fastforce
  from tc\<^sub>d_let have "insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d float_lets e\<^sub>2 : t\<^sub>2" by simp
  hence "[t\<^sub>1] @ \<Gamma> \<turnstile>\<^sub>d float_lets e\<^sub>2 : t\<^sub>2" by (cases \<Gamma>) simp_all
  hence "[t\<^sub>1] @ ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d multiincr (length ts\<^sub>1) (length [t\<^sub>1]) (float_lets e\<^sub>2) : t\<^sub>2" 
    by (metis typing_multiincr)
  with T1 show ?case by (cases "ts\<^sub>1 @ \<Gamma>") auto
qed simp_all

lemma strip_lets_val [simp]: "value\<^sub>d v \<Longrightarrow> strip_lets v = []"
  by (induction v) simp_all

lemma inner_expr_val [simp]: "value\<^sub>d v \<Longrightarrow> inner_expr v = v"
  by (induction v) simp_all

lemma reapply_let_val [simp]: "value\<^sub>d (reapply_lets es e) = (es = [] \<and> value\<^sub>d e)"
  by (induction es) (simp_all add: reapply_lets_def)

lemma float_lets_val [simp]: "value\<^sub>d (float_lets e) = value\<^sub>d e"
  by (induction e) (auto simp add: Let_def split: prod.splits)

lemma strip_lets_subst [simp]: "value\<^sub>d v \<Longrightarrow>
    strip_lets (subst\<^sub>d x v e) = map_with_idx (\<lambda>k. subst\<^sub>d (k + x) (multiincr k 0 v)) (strip_lets e)"
  by (induction e arbitrary: x v) (auto split: prod.splits)

lemma inner_expr_subst [simp]: "value\<^sub>d v \<Longrightarrow> inner_expr (subst\<^sub>d x v e) = 
    subst\<^sub>d (length (strip_lets e) + x) (multiincr (length (strip_lets e)) 0 v) (inner_expr e)"
  by (induction e arbitrary: x v) (auto split: prod.splits)

lemma reapply_let_subst [simp]: "subst\<^sub>d x v (reapply_lets es e) = 
  reapply_lets (map_with_idx (\<lambda>k. subst\<^sub>d (k + x) (multiincr k 0 v)) es) 
    (subst\<^sub>d (x + length es) (multiincr (length es) 0 v) e)"
  by (induction es arbitrary: x v) (simp_all add: reapply_lets_def)

lemma strip_lets_incr [simp]: "strip_lets (incr\<^sub>d x e) = 
    map_with_idx (\<lambda>k. incr\<^sub>d (k + x)) (strip_lets e)"
  by (induction e arbitrary: x) (auto simp add: comp_def split: prod.splits)

lemma inner_expr_incr [simp]: "inner_expr (incr\<^sub>d x e) = 
    incr\<^sub>d (length (strip_lets e) + x) (inner_expr e)"
  by (induction e arbitrary: x) (auto simp add: comp_def split: prod.splits)

lemma reapply_let_incr [simp]: "incr\<^sub>d x (reapply_lets es e) = 
    reapply_lets (map_with_idx (\<lambda>k. incr\<^sub>d (k + x)) es) (incr\<^sub>d (x + length es) e)"
  by (induction es arbitrary: x) (simp_all add: comp_def reapply_lets_def)

lemma float_lets_lemma [simp]: "map_with_idx (multiincr y) (map_with_idx (\<lambda>k. incr\<^sub>d (k + x)) es) = 
  map_with_idx (\<lambda>k. incr\<^sub>d (k + (x + y))) (map_with_idx (multiincr y) es)"
proof (induction y)
  case (Suc y)
  have "\<And>k. incr\<^sub>d k \<circ> incr\<^sub>d (k + (x + y)) = incr\<^sub>d (Suc (k + (x + y))) \<circ> incr\<^sub>d k" by auto
  hence "map_with_idx (\<lambda>k. incr\<^sub>d k \<circ> incr\<^sub>d (k + (x + y)) \<circ> multiincr y k) es =
    map_with_idx (\<lambda>k. incr\<^sub>d (Suc (k + (x + y))) \<circ> incr\<^sub>d k \<circ> multiincr y k) es" by simp
  with Suc have "map_with_idx (\<lambda>k. incr\<^sub>d k \<circ> multiincr y k) (map_with_idx (\<lambda>k. incr\<^sub>d (k + x)) es) =
    map_with_idx (\<lambda>k. incr\<^sub>d (k + (x + Suc y))) (map_with_idx (\<lambda>k. incr\<^sub>d k \<circ> multiincr y k) es)" 
      by simp
  then show ?case by (simp add: comp_def)
qed simp_all

lemma float_lets_lemma2 [simp]: "multiincr y 0 (incr\<^sub>d (z + x) e) = 
    incr\<^sub>d (x + z + y) (multiincr y 0 e)"
  by (induction y) (simp_all add: add.commute)

lemma float_lets_lemma3 [simp]: "multiincr y z (incr\<^sub>d (z + x) e) = 
    incr\<^sub>d (x + y + z) (multiincr y z e)"
  by (induction y) (simp_all add: add.commute)

lemma float_lets_incr [simp]: "float_lets (incr\<^sub>d x e) = incr\<^sub>d x (float_lets e)"
proof (induction e arbitrary: x)
  case (App\<^sub>d e1 e2)
  thus ?case by (simp add: Let_def incr_above)
qed (simp_all add: Let_def add.commute)

lemma float_lets_subst [simp]: "value\<^sub>d v \<Longrightarrow> 
  float_lets (subst\<^sub>d x v e) = subst\<^sub>d x (float_lets v) (float_lets e)"
proof (induction e arbitrary: x v)
  case (App\<^sub>d e1 e2)
  from App\<^sub>d have "value\<^sub>d xv \<Longrightarrow> float_lets (subst\<^sub>d xx xv e1) = subst\<^sub>d xx (float_lets xv) (float_lets e1)" by simp
  from App\<^sub>d have "value\<^sub>d xv \<Longrightarrow> float_lets (subst\<^sub>d xx xv e2) = subst\<^sub>d xx (float_lets xv) (float_lets e2)" by simp
  from App\<^sub>d have "value\<^sub>d v" by simp


  let ?es\<^sub>1 = "strip_lets (float_lets e1)"
  let ?es\<^sub>1\<^sub>s = "map_with_idx (\<lambda>k. subst\<^sub>d (k + x) (multiincr k 0 (float_lets v))) ?es\<^sub>1"
  let ?e\<^sub>1' = "inner_expr (float_lets e1)"
  let ?e\<^sub>1\<^sub>s' = "subst\<^sub>d (length ?es\<^sub>1 + x) (multiincr (length ?es\<^sub>1) 0 (float_lets v)) ?e\<^sub>1'"
  let ?es\<^sub>2 = "strip_lets (float_lets e2)"
  let ?es\<^sub>2\<^sub>s = "map_with_idx (\<lambda>k. subst\<^sub>d (k + x) (multiincr k 0 (float_lets v))) ?es\<^sub>2"
  let ?es\<^sub>1' = "if is_reducible ?e\<^sub>1' then ?es\<^sub>1 @ [?e\<^sub>1'] else ?es\<^sub>1"
  let ?es\<^sub>1\<^sub>s' = "if is_reducible ?e\<^sub>1\<^sub>s' then ?es\<^sub>1\<^sub>s @ [?e\<^sub>1\<^sub>s'] else ?es\<^sub>1\<^sub>s"

  from App\<^sub>d have X: "(map_with_idx (\<lambda>k. subst\<^sub>d (k + (x + length ?es\<^sub>1')) (multiincr k 0 (multiincr (length ?es\<^sub>1') 0 (float_lets v)))) 
      (map_with_idx (multiincr (length ?es\<^sub>1')) ?es\<^sub>2)) = (map_with_idx (multiincr (length ?es\<^sub>1\<^sub>s')) ?es\<^sub>2\<^sub>s)"
    by simp

  have Y: "subst\<^sub>d (x + length ?es\<^sub>1' + length (map_with_idx (multiincr (length ?es\<^sub>1')) ?es\<^sub>2)) 
    (multiincr (length (map_with_idx (multiincr (length ?es\<^sub>1')) ?es\<^sub>2)) 0 (multiincr (length ?es\<^sub>1') 0 (float_lets v))) 
      (multiincr (length ?es\<^sub>2) 0 (if is_reducible ?e\<^sub>1' then Var\<^sub>d 0 else ?e\<^sub>1')) =
        multiincr (length ?es\<^sub>2\<^sub>s) 0 (if is_reducible ?e\<^sub>1\<^sub>s' then Var\<^sub>d 0 else ?e\<^sub>1\<^sub>s')" by simp


  have "multiincr (length ?es\<^sub>1\<^sub>s') (length ?es\<^sub>2\<^sub>s) (subst\<^sub>d (length ?es\<^sub>2 + x) 
    (multiincr (length ?es\<^sub>2) 0 (float_lets v)) (inner_expr (float_lets e2))) =
      subst\<^sub>d (x + length ?es\<^sub>1' + length (map_with_idx (multiincr (length ?es\<^sub>1')) ?es\<^sub>2)) 
        (multiincr (length (map_with_idx (multiincr (length ?es\<^sub>1')) ?es\<^sub>2)) 0 
            (multiincr (length ?es\<^sub>1') 0 (float_lets v))) (multiincr (length ?es\<^sub>1') (length ?es\<^sub>2) 
            (inner_expr (float_lets e2)))" by simp
  with App\<^sub>d X Y show ?case by (simp add: Let_def)
qed (simp_all add: Let_def add.commute)

theorem correctness\<^sub>f\<^sub>l [simp]: "e \<leadsto>\<^sub>d e' \<Longrightarrow> iter (\<leadsto>\<^sub>d) (float_lets e) (float_lets e')"
proof (induction e e' rule: eval\<^sub>d.induct)
  case (ev\<^sub>d_app1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
  thus ?case by simpx 
next
  case (ev\<^sub>d_app2 e\<^sub>1 e\<^sub>2 e\<^sub>2')
  then show ?case by simpx
next
  case (ev\<^sub>d_app3 e\<^sub>2 t e\<^sub>1)
  then show ?case by simp
next
  case (ev\<^sub>d_let1 e\<^sub>1 e\<^sub>1' e\<^sub>2)

  have "iter (\<leadsto>\<^sub>d)
     (let es\<^sub>1 = strip_lets (float_lets e\<^sub>1)
      in reapply_lets es\<^sub>1
          (Let\<^sub>d (inner_expr (float_lets e\<^sub>1)) (multiincr (length es\<^sub>1) (Suc 0) (float_lets e\<^sub>2))))
     (let es\<^sub>1 = strip_lets (float_lets e\<^sub>1')
      in reapply_lets es\<^sub>1
          (Let\<^sub>d (inner_expr (float_lets e\<^sub>1')) (multiincr (length es\<^sub>1) (Suc 0) (float_lets e\<^sub>2))))" by simp
  thus ?case by simp
next
  case (ev\<^sub>d_let2 e\<^sub>1 e\<^sub>2)
  hence "Let\<^sub>d (float_lets e\<^sub>1) (float_lets e\<^sub>2) \<leadsto>\<^sub>d subst\<^sub>d 0 (float_lets e\<^sub>1) (float_lets e\<^sub>2)" by simp
  hence "iter (\<leadsto>\<^sub>d) (Let\<^sub>d (float_lets e\<^sub>1) (float_lets e\<^sub>2)) (subst\<^sub>d 0 (float_lets e\<^sub>1) (float_lets e\<^sub>2))"
    by simp
  with ev\<^sub>d_let2 show ?case by (simp add: Let_def)
qed

lemma iter_correct\<^sub>f\<^sub>l [simp]: "iter (\<leadsto>\<^sub>d) e e' \<Longrightarrow> iter (\<leadsto>\<^sub>d) (float_lets e) (float_lets e')"
  by (induction e e' rule: iter.induct) (simp, metis correctness\<^sub>f\<^sub>l iter_append)

end