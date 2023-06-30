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
language, and would force us to work with big-step evaluation for proofs instead of the nicer 
small-step relation. Fortunately, we can solve it another way: if \<open>e\<^sub>1\<close> is not a value, just let-bind 
it too, thereby fixing the evaluation order. Because of our lifting of application left-sides, there 
will be one extra evaluation step substituting it back away in each non-value \<open>App\<^sub>s\<close>, equivalent to 
one extra \<open>Lookup\<^sub>e\<close> in the compiled tree-code. It will be made up for, hopefully, by the savings 
from not having to pop the environments at the end of each function.\<close>

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

lemma multiincr_subst_swap'[simp]: "y \<le> z \<Longrightarrow> 
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

fun is_redex :: "expr\<^sub>d \<Rightarrow> bool" where
  "is_redex (App\<^sub>d e\<^sub>1 e\<^sub>2) = True"
| "is_redex e = False"

lemma is_redex_value [simp]: "value\<^sub>d e \<Longrightarrow> \<not> is_redex e"
  by (induction e) simp_all

lemma is_redex_incr [simp]: "is_redex (incr\<^sub>d x e) = is_redex e"
  by (induction e) simp_all

lemma is_redex_subst [simp]: "value\<^sub>d e' \<Longrightarrow> is_redex (subst\<^sub>d x e' e) = is_redex e"
  by (induction e) simp_all

fun strip_lets :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d list \<times> expr\<^sub>d" where
  "strip_lets (Let\<^sub>d e\<^sub>1 e\<^sub>2) = (case strip_lets e\<^sub>2 of
    (es, e\<^sub>2') \<Rightarrow> (e\<^sub>1 # es, e\<^sub>2'))"
| "strip_lets e = ([], e)"

primrec float_lets :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "float_lets (Var\<^sub>d x) = Var\<^sub>d x"
| "float_lets (Const\<^sub>d n) = Const\<^sub>d n"
| "float_lets (Lam\<^sub>d t e) = Lam\<^sub>d t (float_lets e)"
| "float_lets (App\<^sub>d e\<^sub>1 e\<^sub>2) = (
    let (es\<^sub>1, e\<^sub>1') = strip_lets (float_lets e\<^sub>1) 
    in let (es\<^sub>2, e\<^sub>2') = strip_lets (float_lets e\<^sub>2) 
    in let es\<^sub>1' = if is_redex e\<^sub>1' then es\<^sub>1 else es\<^sub>1 @ [e\<^sub>1']
    in let e\<^sub>1'' = if is_redex e\<^sub>1' then e\<^sub>1' else Var\<^sub>d 0
    in foldr Let\<^sub>d (es\<^sub>1' @ map_with_idx (multiincr (length es\<^sub>1')) es\<^sub>2) 
        (App\<^sub>d (multiincr (length es\<^sub>2) 0 e\<^sub>1'') (multiincr (length es\<^sub>1') (length es\<^sub>2) e\<^sub>2')))"
| "float_lets (Let\<^sub>d e\<^sub>1 e\<^sub>2) = (
    let (es\<^sub>1, e\<^sub>1') = strip_lets (float_lets e\<^sub>1)
    in foldr Let\<^sub>d es\<^sub>1 (Let\<^sub>d e\<^sub>1' (multiincr (length es\<^sub>1) 1 (float_lets e\<^sub>2))))"

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

lemma fold_lets_normalized [simp]: "let_floated (foldr Let\<^sub>d es e) = 
    (list_all let_free es \<and> list_all let_floated es \<and> let_floated e)"
  by (induction es) auto

lemma strip_lets_normalized [simp]: "strip_lets e = (es, e') \<Longrightarrow> 
    let_floated e = (list_all let_free es \<and> list_all let_floated es \<and> let_free e' \<and> let_floated e')"
  by (induction e arbitrary: es) (auto split: prod.splits)

lemma float_lets_normalizes [simp]: "let_floated (float_lets e)"
proof (induction e) 
  case (App\<^sub>d e1 e2)
  obtain es\<^sub>1 e\<^sub>1' where E1: "strip_lets (float_lets e1) = (es\<^sub>1, e\<^sub>1')" by fastforce
  obtain es\<^sub>2 e\<^sub>2' where E2: "strip_lets (float_lets e2) = (es\<^sub>2, e\<^sub>2')" 
    by fastforce
  from App\<^sub>d have "let_floated (float_lets e2)" by simp
  with E2 have "list_all let_free es\<^sub>2 \<and> list_all let_floated es\<^sub>2 \<and> let_free e\<^sub>2' \<and> let_floated e\<^sub>2'" 
    by (metis strip_lets_normalized)
  with App\<^sub>d E1 E2 show ?case by simp
qed (auto split: prod.splits)

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

lemma typing_binding_multiincr [simp]: "\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b es : ts \<Longrightarrow> 
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

lemma typing_strip_lets [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> strip_lets e = (es, e') \<Longrightarrow> 
  \<exists>ts. (\<Gamma> \<turnstile>\<^sub>d\<^sub>b es : ts) \<and> (ts @ \<Gamma> \<turnstile>\<^sub>d e' : t)"
proof (induction \<Gamma> e t arbitrary: es e' rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_var \<Gamma> x t)
  hence "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b es : []) \<and> ([] @ \<Gamma> \<turnstile>\<^sub>d e' : t)" by auto
  thus ?case by auto
next
  case (tc\<^sub>d_const \<Gamma> n)
  hence "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b es : []) \<and> ([] @ \<Gamma> \<turnstile>\<^sub>d e' : Num)" by auto
  thus ?case by auto
next
  case (tc\<^sub>d_lam t\<^sub>1 \<Gamma> e t\<^sub>2)
  hence "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b es : []) \<and> ([] @ \<Gamma> \<turnstile>\<^sub>d e' : Arrow t\<^sub>1 t\<^sub>2)" by auto
  thus ?case by auto
next
  case (tc\<^sub>d_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  hence "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b es : []) \<and> ([] @ \<Gamma> \<turnstile>\<^sub>d e' : t\<^sub>2)" by auto
  thus ?case by auto
next
  case (tc\<^sub>d_let \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
  moreover obtain es\<^sub>2 e\<^sub>2' where E: "strip_lets e\<^sub>2 = (es\<^sub>2, e\<^sub>2')" by fastforce
  ultimately obtain ts where T: "(insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d\<^sub>b es\<^sub>2 : ts) \<and> 
    (ts @ insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e\<^sub>2' : t\<^sub>2)" by fastforce
  hence X: "ts @ t\<^sub>1 # \<Gamma> \<turnstile>\<^sub>d e\<^sub>2' : t\<^sub>2" by (cases \<Gamma>) simp_all
  from tc\<^sub>d_let T have "\<Gamma> \<turnstile>\<^sub>d\<^sub>b e\<^sub>1 # es\<^sub>2 : ts @ [t\<^sub>1]" by simp
  with tc\<^sub>d_let E X show ?case by auto
qed

lemma typing_fold_lets [simp]: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b es : ts \<Longrightarrow> ts @ \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d foldr Let\<^sub>d es e : t"
proof (induction \<Gamma> es ts rule: typing\<^sub>d_bindings.induct)
  case (tc\<^sub>d_bind_cons \<Gamma> e t es ts)
  thus ?case by (induction \<Gamma>) simp_all
qed simp_all 

theorem typing_float_lets [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d float_lets e : t"
proof (induction \<Gamma> e t rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  obtain es\<^sub>1 e\<^sub>1' where E1: "strip_lets (float_lets e\<^sub>1) = (es\<^sub>1, e\<^sub>1')" by fastforce
  with tc\<^sub>d_app obtain ts\<^sub>1 where T1: "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b es\<^sub>1 : ts\<^sub>1) \<and> (ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d e\<^sub>1' : Arrow t\<^sub>1 t\<^sub>2)" by fastforce
  let ?es\<^sub>1 = "if is_redex e\<^sub>1' then es\<^sub>1 else es\<^sub>1 @ [e\<^sub>1']"
  let ?ts\<^sub>1 = "if is_redex e\<^sub>1' then ts\<^sub>1 else Arrow t\<^sub>1 t\<^sub>2 #  ts\<^sub>1"
  let ?e\<^sub>1 = "if is_redex e\<^sub>1' then e\<^sub>1' else Var\<^sub>d 0"
  from tc\<^sub>d_app have "\<Gamma> \<turnstile>\<^sub>d float_lets e\<^sub>2 : t\<^sub>1" by simp
  moreover obtain es\<^sub>2 e\<^sub>2' where E2: "strip_lets (float_lets e\<^sub>2) = (es\<^sub>2, e\<^sub>2')" by fastforce
  ultimately obtain ts\<^sub>2 where T2: "([] @ \<Gamma> \<turnstile>\<^sub>d\<^sub>b es\<^sub>2 : ts\<^sub>2) \<and> (ts\<^sub>2 @ \<Gamma> \<turnstile>\<^sub>d e\<^sub>2' : t\<^sub>1)" by fastforce
  with T1 have L: "length ts\<^sub>1 = length es\<^sub>1 \<and> length ts\<^sub>2 = length es\<^sub>2" by auto
  from T1 have "\<Gamma> \<turnstile>\<^sub>d\<^sub>b es\<^sub>1 @ [e\<^sub>1'] : [Arrow t\<^sub>1 t\<^sub>2] @ ts\<^sub>1"
    by (metis append_Nil typing\<^sub>d_bindings.simps typing_bindings_append)
  with T1 have X: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b ?es\<^sub>1 : ?ts\<^sub>1" by simp
  from T1 have "[] @ ?ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d ?e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by simp
  hence Y: "[] @ ts\<^sub>2 @ ?ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d multiincr (length ts\<^sub>2) (length []) ?e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" 
    by (metis typing_multiincr list.size(3))
  from T2 have Z: "[] @ ?ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d\<^sub>b map_with_idx (\<lambda>k. multiincr (length ?ts\<^sub>1) k) es\<^sub>2 : ts\<^sub>2" 
    using typing_binding_multiincr by fastforce
  from T2 have "ts\<^sub>2 @ ?ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d multiincr (length ?ts\<^sub>1) (length ts\<^sub>2) e\<^sub>2' : t\<^sub>1" by simp
  with E1 E2 L X Y Z show ?case by (simp add: Let_def)
next
  case (tc\<^sub>d_let \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
  then obtain es\<^sub>1 e\<^sub>1' where E: "strip_lets (float_lets e\<^sub>1) = (es\<^sub>1, e\<^sub>1')" by fastforce
  with tc\<^sub>d_let obtain ts\<^sub>1 where T1: "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b es\<^sub>1 : ts\<^sub>1) \<and> (ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d e\<^sub>1' : t\<^sub>1)" by fastforce
  hence L: "length ts\<^sub>1 = length es\<^sub>1" by auto
  from tc\<^sub>d_let have "[t\<^sub>1] @ \<Gamma> \<turnstile>\<^sub>d float_lets e\<^sub>2 : t\<^sub>2" by (induction \<Gamma>) simp_all
  hence "[t\<^sub>1] @ ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d multiincr (length ts\<^sub>1) (length [t\<^sub>1]) (float_lets e\<^sub>2) : t\<^sub>2" 
    using typing_multiincr by fastforce
  with L have "insert_at 0 t\<^sub>1 (ts\<^sub>1 @ \<Gamma>) \<turnstile>\<^sub>d multiincr (length es\<^sub>1) (Suc 0) (float_lets e\<^sub>2) : t\<^sub>2" 
    by (cases "ts\<^sub>1 @ \<Gamma>") simp_all
  with E T1 show ?case by auto
qed simp_all

lemma strip_lets_val [simp]: "value\<^sub>d v \<Longrightarrow> strip_lets v = ([], v)"
  by (induction v) simp_all

lemma foldr_let_val [simp]: "value\<^sub>d (foldr Let\<^sub>d es e) = (es = [] \<and> value\<^sub>d e)"
  by (induction es) simp_all

lemma float_lets_val [simp]: "value\<^sub>d (float_lets e) = value\<^sub>d e"
  by (induction e) (auto split: prod.splits)

lemma strip_lets_foldr [simp]: "strip_lets e = (es, e') \<Longrightarrow> foldr Let\<^sub>d es e' = e"
  by (induction e arbitrary: es e') (auto split: prod.splits)

lemma strip_lets_subst [simp]: "strip_lets e = (es, e') \<Longrightarrow> value\<^sub>d v \<Longrightarrow>
    strip_lets (subst\<^sub>d x v e) = (map_with_idx (\<lambda>k. subst\<^sub>d (k + x) (multiincr k 0 v)) es, 
      subst\<^sub>d (length es + x) (multiincr (length es) 0 v) e')"
  by (induction e arbitrary: es x v) (auto split: prod.splits)

lemma foldr_let_subst [simp]: "subst\<^sub>d x v (foldr Let\<^sub>d es e) = 
  foldr Let\<^sub>d (map_with_idx (\<lambda>k. subst\<^sub>d (k + x) (multiincr k 0 v)) es) 
    (subst\<^sub>d (x + length es) (multiincr (length es) 0 v) e)"
  by (induction es arbitrary: x v) simp_all

lemma strip_lets_incr [simp]: "strip_lets e = (es, e') \<Longrightarrow> 
    strip_lets (incr\<^sub>d x e) = (map_with_idx (\<lambda>k. incr\<^sub>d (k + x)) es, incr\<^sub>d (length es + x) e')"
  by (induction e arbitrary: es x) (auto simp add: comp_def split: prod.splits)

lemma foldr_let_incr [simp]: "incr\<^sub>d x (foldr Let\<^sub>d es e) = 
    foldr Let\<^sub>d (map_with_idx (\<lambda>k. incr\<^sub>d (k + x)) es) (incr\<^sub>d (x + length es) e)"
  by (induction es arbitrary: x) (simp_all add: comp_def)

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
  moreover obtain es\<^sub>1 e\<^sub>1' where "strip_lets (float_lets e1) = (es\<^sub>1, e\<^sub>1')" by fastforce
  moreover obtain es\<^sub>2 e\<^sub>2' where "strip_lets (float_lets e2) = (es\<^sub>2, e\<^sub>2')" by fastforce
  ultimately show ?case by (simp add: Let_def incr_above)
next
  case (Let\<^sub>d e1 e2)
  moreover obtain es\<^sub>1 e\<^sub>1' where "strip_lets (float_lets e1) = (es\<^sub>1, e\<^sub>1')" by fastforce
  ultimately show ?case by (simp add: add.commute)
qed simp_all

lemma float_lets_subst [simp]: "value\<^sub>d v \<Longrightarrow> 
  float_lets (subst\<^sub>d x v e) = subst\<^sub>d x (float_lets v) (float_lets e)"
proof (induction e arbitrary: x v)
  case (App\<^sub>d e1 e2)
  obtain es\<^sub>1 e\<^sub>1' where E1: "strip_lets (float_lets e1) = (es\<^sub>1, e\<^sub>1')" by fastforce
  obtain es\<^sub>2 e\<^sub>2' where E2: "strip_lets (float_lets e2) = (es\<^sub>2, e\<^sub>2')" by fastforce
  show ?case
  proof (cases "is_redex e\<^sub>1'")
    case True                   
    have X: "length es\<^sub>1 + (x + length es\<^sub>2) = length es\<^sub>2 + (x + length es\<^sub>1)" by simp
    have Y: "\<And>k. length es\<^sub>1 + (k + x) = k + (x + length es\<^sub>1)" by simp
    have "\<And>k. multiincr (length es\<^sub>1) k \<circ> subst\<^sub>d (k + x) (multiincr k 0 (float_lets v)) =
      subst\<^sub>d (k + (x + length es\<^sub>1)) (multiincr k 0 (multiincr (length es\<^sub>1) 0 (float_lets v))) \<circ>
        multiincr (length es\<^sub>1) k" by (auto simp add: Y)
    hence "map_with_idx (\<lambda>k. multiincr (length es\<^sub>1) k \<circ> 
      subst\<^sub>d (k + x) (multiincr k 0 (float_lets v))) es\<^sub>2 =
        (map_with_idx (\<lambda>k. subst\<^sub>d (k + (x + length es\<^sub>1)) 
          (multiincr k 0 (multiincr (length es\<^sub>1) 0 (float_lets v))) \<circ> multiincr (length es\<^sub>1) k) es\<^sub>2)" 
      by simp
    with App\<^sub>d E1 E2 True show ?thesis by (simp add: Let_def add.commute X)
  next
    case False
    have X: "length es\<^sub>1 + x = x + length es\<^sub>1" by simp
    have Y: "length es\<^sub>1 + (length es\<^sub>2 + x) = x + length es\<^sub>1 + length es\<^sub>2" by simp
    have Z: "\<And>k. length es\<^sub>1 + (k + x) = k + (x + length es\<^sub>1)" by simp
    have "\<And>k. incr\<^sub>d k \<circ> multiincr (length es\<^sub>1) k \<circ> subst\<^sub>d (k + x) (multiincr k 0 (float_lets v)) =
      subst\<^sub>d (Suc k + (x + length es\<^sub>1)) 
        (multiincr (Suc k) 0 (multiincr (length es\<^sub>1) 0 (float_lets v))) \<circ> incr\<^sub>d k \<circ> 
            multiincr (length es\<^sub>1) k"
      by (auto simp add: incr_multiincr_higher Z)
    hence "map_with_idx (\<lambda>k. incr\<^sub>d k \<circ> multiincr (length es\<^sub>1) k \<circ> 
      subst\<^sub>d (k + x) (multiincr k 0 (float_lets v))) es\<^sub>2 =
        map_with_idx (\<lambda>k. subst\<^sub>d (Suc k + (x + length es\<^sub>1)) 
          (multiincr (Suc k) 0 (multiincr (length es\<^sub>1) 0 (float_lets v))) \<circ> incr\<^sub>d k \<circ> 
            multiincr (length es\<^sub>1) k) es\<^sub>2" by simp
    hence "map_with_idx (\<lambda>k. multiincr (Suc (length es\<^sub>1)) k)
      (map_with_idx (\<lambda>k. subst\<^sub>d (k + x) (multiincr k 0 (float_lets v))) es\<^sub>2) =
        map_with_idx ((\<lambda>k. subst\<^sub>d (k + (x + length es\<^sub>1))
          (multiincr k 0 (multiincr (length es\<^sub>1) 0 (float_lets v)))) \<circ> Suc)
            (map_with_idx (\<lambda>k. multiincr (Suc (length es\<^sub>1)) k) es\<^sub>2)" by simp
    hence "map_with_idx (multiincr (Suc (length es\<^sub>1)))
      (map_with_idx (\<lambda>k. subst\<^sub>d (k + x) (multiincr k 0 (float_lets v))) es\<^sub>2) =
        map_with_idx ((\<lambda>k. subst\<^sub>d (k + (x + length es\<^sub>1))
          (multiincr k 0 (multiincr (length es\<^sub>1) 0 (float_lets v)))) \<circ> Suc)
            (map_with_idx (multiincr (Suc (length es\<^sub>1))) es\<^sub>2)" by blast
    with App\<^sub>d E1 E2 False show ?thesis by (simp add: X Y)
  qed
next
  case (Let\<^sub>d e1 e2)
  obtain es\<^sub>1 e\<^sub>1' where E1: "strip_lets (float_lets e1) = (es\<^sub>1, e\<^sub>1')" by fastforce
  have X: "length es\<^sub>1 + x = x + length es\<^sub>1" by simp
  with Let\<^sub>d E1 show ?case by (simp add: X)
qed simp_all

theorem correctness\<^sub>f\<^sub>l [simp]: "e \<leadsto>\<^sub>d e' \<Longrightarrow> iter (\<leadsto>\<^sub>d) (float_lets e) (float_lets e')"
proof (induction e e' rule: eval\<^sub>d.induct)
  case (ev\<^sub>d_app1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
  hence "iter (\<leadsto>\<^sub>d) (float_lets e\<^sub>1) (float_lets e\<^sub>1')" by simp

  obtain es\<^sub>1 xe\<^sub>1 where E1: "strip_lets (float_lets e\<^sub>1) = (es\<^sub>1, xe\<^sub>1)" by fastforce
  obtain es\<^sub>2 xe\<^sub>2 where E2: "strip_lets (float_lets e\<^sub>2) = (es\<^sub>2, xe\<^sub>2)" by fastforce
  obtain es\<^sub>1' xe\<^sub>1' where E3: "strip_lets (float_lets e\<^sub>1') = (es\<^sub>1', xe\<^sub>1')" by fastforce

  let ?es\<^sub>1 = "if is_redex xe\<^sub>1 then es\<^sub>1 else es\<^sub>1 @ [xe\<^sub>1]"
  let ?es\<^sub>1' = "if is_redex xe\<^sub>1' then es\<^sub>1' else es\<^sub>1' @ [xe\<^sub>1']"


  have "iter (\<leadsto>\<^sub>d)
     (foldr Let\<^sub>d ?es\<^sub>1
              (foldr Let\<^sub>d (map_with_idx (multiincr (length ?es\<^sub>1)) es\<^sub>2)
                (App\<^sub>d (multiincr (length es\<^sub>2) 0 (if is_redex xe\<^sub>1 then xe\<^sub>1 else Var\<^sub>d 0))
                  (multiincr (length ?es\<^sub>1) (length es\<^sub>2) xe\<^sub>2))))
     (foldr Let\<^sub>d ?es\<^sub>1'
              (foldr Let\<^sub>d (map_with_idx (multiincr (length ?es\<^sub>1')) es\<^sub>2)
                (App\<^sub>d (multiincr (length es\<^sub>2) 0 (if is_redex xe\<^sub>1' then xe\<^sub>1' else Var\<^sub>d 0))
                  (multiincr (length ?es\<^sub>1') (length es\<^sub>2) xe\<^sub>2))))" by simpx
  with E1 E2 E3 have "iter (\<leadsto>\<^sub>d) (float_lets (App\<^sub>d e\<^sub>1 e\<^sub>2)) (float_lets (App\<^sub>d e\<^sub>1' e\<^sub>2))" 
    by (simp add: Let_def)
  thus ?case by blast
next
  case (ev\<^sub>d_app2 e\<^sub>1 e\<^sub>2 e\<^sub>2')
  then show ?case by simpx
next
  case (ev\<^sub>d_app3 e\<^sub>2 t e\<^sub>1)
  then show ?case by simp
next
  case (ev\<^sub>d_let1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
  then show ?case by simpx
next
  case (ev\<^sub>d_let2 e\<^sub>1 e\<^sub>2)
  then show ?case by simp
qed

lemma iter_correct\<^sub>f\<^sub>l [simp]: "iter (\<leadsto>\<^sub>d) e e' \<Longrightarrow> iter (\<leadsto>\<^sub>d) (float_lets e) (float_lets e')"
  by (induction e e' rule: iter.induct) (simp, metis correctness\<^sub>f\<^sub>l iter_append)

end