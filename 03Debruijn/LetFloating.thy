theory LetFloating
  imports BigStep
begin

subsection \<open>Let Floating\<close>

text \<open>We perform a small source-level optimization here that will pay off for our tree code. Our 
language is a lexically-scoped one, meaning that the application of a function is evaluated in the 
function's static defining environment rather than its dynamic evaluating environment. This has a 
number of significant consequences - notably alpha conversion and type safety - but what we are 
concerned with now is that it means that every time we _finish_ evaluating a function application, 
we discard the current environment and return to the previous one. Now, consider the effects of a 
let-expression on the environment. When the evaluation of the definition is finished, its value is 
pushed into the environment; when the evaluation of the body is finished, it is popped off. But if 
the let-expression is the last thing being evaluated in a function body, the pop will be followed by 
a return - which means that the pop was unnecessary, since the environment is about to be discarded 
anyways. By collapsing together all \<open>PopEnv\<^sub>e ... PopEnv\<^sub>e, Return\<^sub>e\<close> sequences into just a \<open>Return\<^sub>e\<close>, 
we can save ever executing these \<open>PopEnv\<^sub>e\<close>s separately. But we can do even better.\<close>

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

text \<open>There is one slight catch: naively floating the lets out of the argument of an application 
\<open>App\<^sub>s e\<^sub>1 (Let\<^sub>s e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2)\<close> changes the evaluation order - before, \<open>e\<^sub>1\<close> is evaluated before \<open>e\<^sub>2\<^sub>1\<close>, but 
once the latter has been floated out, it will be evaluated first. This is not necessarily fatal, 
since our language is normalizing and has no side effects, but this would not extend to a richer 
language. Fortunately, we can solve it another way: if \<open>e\<^sub>1\<close> needs evaluation, just let-bind it too, 
thereby fixing the evaluation order. Because of our lifting of application left-sides, there will be
one extra evaluation step substituting it back away in each \<open>App\<^sub>s\<close>, equivalent to one extra 
\<open>Lookup\<^sub>e\<close> in the compiled tree-code. It will be made up for, hopefully, by the savings from not 
having to pop the environments at the end of each function.\<close>

text \<open>This transformation has one even more useful consequence, but it is not yet implemented - see
the "Further Work" section at the end.\<close>

text \<open>We begin by defining our let-floated normal form.\<close>

abbreviation is_var :: "expr\<^sub>d \<Rightarrow> bool" where
  "is_var e \<equiv> (case e of Var\<^sub>d x \<Rightarrow> True | _ \<Rightarrow> False)"

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
| "let_floated (App\<^sub>d e\<^sub>1 e\<^sub>2) = 
    (let_free e\<^sub>1 \<and> let_free e\<^sub>2 \<and> (is_var e\<^sub>1 \<or> value\<^sub>d e\<^sub>1) \<and> let_floated e\<^sub>1 \<and> let_floated e\<^sub>2)"
| "let_floated (Let\<^sub>d e\<^sub>1 e\<^sub>2) = (let_free e\<^sub>1 \<and> let_floated e\<^sub>1 \<and> let_floated e\<^sub>2)"

lemma is_var_val [simp]: "value\<^sub>d e \<Longrightarrow> \<not>is_var e"
  by (induction e) simp_all

lemma is_var_incr [simp]: "is_var (incr\<^sub>d x e) = is_var e"
  by (induction e) simp_all

lemma is_var_subst [simp]: "value\<^sub>d v \<Longrightarrow> is_var (subst\<^sub>d x v e) = (\<exists>y. e = Var\<^sub>d y \<and> x \<noteq> y)"
  by (induction e) simp_all

text \<open>Then, the let-floating transformation itself. We have to define a multiple-increment function
to make sure the variables match properly.\<close>

primrec multiincr :: "nat \<Rightarrow> nat \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "multiincr 0 y = id"
| "multiincr (Suc x) y = incr\<^sub>d y \<circ> multiincr x y"

lemma multiincr_incr_swap' [simp]: "multiincr x y (incr\<^sub>d y e) = incr\<^sub>d y (multiincr x y e)"
  by (induction x) simp_all

lemma multiincr_incr_swap [simp]: "z \<ge> y \<Longrightarrow> 
    multiincr x y (incr\<^sub>d z e) = incr\<^sub>d (z + x) (multiincr x y e)"
  by (induction x) simp_all

lemma multiincr_incr_swap2 [simp]: "z \<le> y \<Longrightarrow> 
    multiincr x (Suc y) (incr\<^sub>d z e) = incr\<^sub>d z (multiincr x y e)"
  by (induction x) simp_all

lemma multiincr_incr_swap_map [simp]: "map_with_idx (Suc y) (multiincr x) (map_with_idx y incr\<^sub>d es) = 
    map_with_idx y (multiincr (Suc x)) es"
  by (induction es arbitrary: y) simp_all

lemma subst_multiincr_lemma [simp]: "(\<lambda>k. subst\<^sub>d (Suc (k + x)) (incr\<^sub>d y (multiincr k y e))) = 
    ((\<lambda>k. subst\<^sub>d (k + x) (multiincr k y e)) \<circ> Suc)"
  by auto

lemma multiincr_plus [simp]: "multiincr n k (multiincr k 0 e) = multiincr k 0 (multiincr n 0 e)"
  by (induction k arbitrary: n) simp_all

lemma multiincr_val [simp]: "value\<^sub>d (multiincr x y e) = value\<^sub>d e"
  by (induction x) simp_all

lemma is_var_multiincr [simp]: "is_var (multiincr x y e) = is_var e"
  by (induction x) simp_all

lemma incr_multiincr_higher: "incr\<^sub>d y (multiincr x y e) = incr\<^sub>d (x + y) (multiincr x y e)"
  by (induction x) simp_all

lemma multiincr_var [simp]: "multiincr x y (Var\<^sub>d z) = Var\<^sub>d (if z < y then z else z + x)"
  by (induction x) (simp_all add: incr_above incr_le)

lemma multiincr_con [simp]: "multiincr x y (Const\<^sub>d n) = Const\<^sub>d n"
  by (induction x) simp_all

lemma multiincr_lam [simp]: "multiincr x y (Lam\<^sub>d t e) = Lam\<^sub>d t (multiincr x (Suc y) e)"
  by (induction x) simp_all

lemma multiincr_app [simp]: "multiincr x y (App\<^sub>d e\<^sub>1 e\<^sub>2) = App\<^sub>d (multiincr x y e\<^sub>1) (multiincr x y e\<^sub>2)"
  by (induction x) simp_all

lemma multiincr_let [simp]: "multiincr x y (Let\<^sub>d e\<^sub>1 e\<^sub>2) = 
    Let\<^sub>d (multiincr x y e\<^sub>1) (multiincr x (Suc y) e\<^sub>2)"
  by (induction x) simp_all

lemma multiincr_subst_swap' [simp]: "y \<le> z \<Longrightarrow> 
    multiincr x y (subst\<^sub>d z e' e) = subst\<^sub>d (x + z) (multiincr x y e') (multiincr x y e)"
  by (induction x) simp_all

lemma multiincr_subst [simp]: "z \<le> y \<Longrightarrow> multiincr x y (subst\<^sub>d z e' e) = 
    subst\<^sub>d z (multiincr x y e') (multiincr x (Suc y) e)"
  by (induction x) simp_all

lemma multiincr_subst_within [simp]: "y \<le> z \<Longrightarrow> z < x + y \<Longrightarrow> 
    subst\<^sub>d z v (multiincr x y e) = multiincr (x - 1) y e"
  by (induction e arbitrary: y z v) (simp_all add: decr_gt')

lemma multiincr_subst_within_lemma [simp]: "
  subst\<^sub>d (Suc x) v (incr\<^sub>d (Suc 0) (multiincr x (Suc 0) e)) = multiincr x (Suc 0) e"
proof -
  have "Suc 0 \<le> Suc x \<and> Suc x < Suc x + Suc 0" by simp
  hence "subst\<^sub>d (Suc x) v (multiincr (Suc x) (Suc 0) e) = multiincr (Suc x - 1) (Suc 0) e" 
    by (metis multiincr_subst_within)
  thus ?thesis by simp
qed

lemma multiincr_between_after' [simp]: "incr\<^sub>d (x + z) (multiincr x z (multiincr y z e)) = 
  incr\<^sub>d (y + x + z) (multiincr x z (multiincr y z e))"
proof (induction e arbitrary: x y z)
  case (Lam\<^sub>d t e)
  hence "incr\<^sub>d (x + Suc z) (multiincr x (Suc z) (multiincr y (Suc z) e)) = 
    incr\<^sub>d (y + x + Suc z) (multiincr x (Suc z) (multiincr y (Suc z) e))" by blast
  thus ?case by simp
next
  case (Let\<^sub>d e1 e2)
  hence "incr\<^sub>d (x + Suc z) (multiincr x (Suc z) (multiincr y (Suc z) e2)) = 
    incr\<^sub>d (y + x + Suc z) (multiincr x (Suc z) (multiincr y (Suc z) e2))" by blast
  with Let\<^sub>d show ?case by simp
qed (simp_all add: incr_above incr_le)

lemma multiincr_between_after [simp]: "incr\<^sub>d x (multiincr x 0 (multiincr y 0 e)) = 
    incr\<^sub>d (y + x) (multiincr x 0 (multiincr y 0 e))"
  by (metis multiincr_between_after' add.right_neutral)

lemma multiincr_subst_cancel [simp]: "subst\<^sub>d (x + y) v (incr\<^sub>d y (multiincr x y e)) = multiincr x y e"
  by (simp add: incr_multiincr_higher)

lemma multiincr_subst_cancel_0 [simp]: "subst\<^sub>d x v (incr\<^sub>d 0 (multiincr x 0 e)) = multiincr x 0 e"
  by (metis add.right_neutral multiincr_subst_cancel)

lemma map_multiincr_subst_cancel [simp]: "
  map_with_idx y (\<lambda>k. subst\<^sub>d (k + x) (v k)) (map_with_idx y (multiincr (Suc x)) es) = 
    map_with_idx y (multiincr x) es"
  by (induction es arbitrary: y) (simp_all add: add.commute incr_multiincr_higher)

lemma multiincr_0 [simp]: "multiincr 0 = (\<lambda>x e. e)"
  by rule auto

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

lemma reapply_nil [simp]: "reapply_lets [] e = e"
  by (simp add: reapply_lets_def)

lemma reapply_cons [simp]: "reapply_lets (e' # es) e = Let\<^sub>d e' (reapply_lets es e)"
  by (simp add: reapply_lets_def)

lemma reapply_append [simp]: "reapply_lets (es @ es') e = reapply_lets es (reapply_lets es' e)"
  by (induction es) simp_all

lemma strip_reapply_lets [simp]: "reapply_lets (strip_lets e) (inner_expr e) = e"
  by (induction e rule: strip_lets.induct) auto

lemma reapply_strip_lets [simp]: "strip_lets (reapply_lets es e) = es @ strip_lets e"
  by (induction es) simp_all

lemma reapply_next_lets [simp]: "inner_expr (reapply_lets es e) = inner_expr e"
  by (induction es) simp_all

primrec float_lets :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "float_lets (Var\<^sub>d x) = Var\<^sub>d x"
| "float_lets (Const\<^sub>d n) = Const\<^sub>d n"
| "float_lets (Lam\<^sub>d t e) = Lam\<^sub>d t (float_lets e)"
| "float_lets (App\<^sub>d e\<^sub>1 e\<^sub>2) = (
    let es\<^sub>1 = strip_lets (float_lets e\<^sub>1)
    in let e\<^sub>1' = inner_expr (float_lets e\<^sub>1)
    in let es\<^sub>2 = strip_lets (float_lets e\<^sub>2) 
    in let e\<^sub>2' = inner_expr (float_lets e\<^sub>2) 
    in if is_var e\<^sub>1' \<or> value\<^sub>d e\<^sub>1'
       then reapply_lets (es\<^sub>1 @ map_with_idx 0 (multiincr (length es\<^sub>1)) es\<^sub>2) 
         (App\<^sub>d (multiincr (length es\<^sub>2) 0 e\<^sub>1') (multiincr (length es\<^sub>1) (length es\<^sub>2) e\<^sub>2'))
       else reapply_lets (es\<^sub>1 @ [e\<^sub>1'] @ map_with_idx 0 (multiincr (Suc (length es\<^sub>1))) es\<^sub>2) 
         (App\<^sub>d (Var\<^sub>d (length es\<^sub>2)) (multiincr (Suc (length es\<^sub>1)) (length es\<^sub>2) e\<^sub>2')))"
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
  by (induction es) auto

lemma float_lets_normalizes [simp]: "let_floated (float_lets e)"
  by (induction e) (simp_all add: Let_def)

lemma let_free_strip_lets [simp]: "let_free e \<Longrightarrow> strip_lets e = []"
  by (induction e) simp_all

lemma let_free_inner_expr [simp]: "let_free e \<Longrightarrow> inner_expr e = e"
  by (induction e) simp_all

lemma float_lets_floated [simp]: "let_floated e \<Longrightarrow> float_lets e = e"
  by (induction e) (simp_all add: Let_def)

theorem float_lets_idempotent [simp]: "float_lets (float_lets e) = float_lets e"
  by simp

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

lemma typing_bindings_eq_length_map [simp]: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b map_with_idx x f es : ts \<Longrightarrow> 
  length es = length ts"
proof (induction es arbitrary: \<Gamma> x ts)
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
  \<Gamma>\<^sub>1 @ t # \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b map_with_idx (length \<Gamma>\<^sub>1) incr\<^sub>d es : ts" 
proof (induction es arbitrary: \<Gamma>\<^sub>1 ts)
  case (Cons e es)
  then obtain ts' t' where T: "(\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d e : t') \<and> (insert_at 0 t' (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) \<turnstile>\<^sub>d\<^sub>b es : ts') \<and> 
    ts = ts' @ [t']" by fastforce
  hence "insert_at 0 t' \<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b es : ts'" by simp
  with Cons have "insert_at 0 t' \<Gamma>\<^sub>1 @ t # \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b 
    map_with_idx (length (insert_at 0 t' \<Gamma>\<^sub>1)) incr\<^sub>d es : ts'" by blast
  hence X: "insert_at 0 t' (\<Gamma>\<^sub>1 @ t # \<Gamma>\<^sub>2) \<turnstile>\<^sub>d\<^sub>b map_with_idx (Suc (length \<Gamma>\<^sub>1)) incr\<^sub>d es : ts'" 
    by (simp add: comp_def)
  from T have "insert_at (length \<Gamma>\<^sub>1) t (\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2) \<turnstile>\<^sub>d incr\<^sub>d (length \<Gamma>\<^sub>1) e : t'"
    by (metis tc\<^sub>d_incr le_add1 length_append)
  with T X show ?case by simp
qed auto

lemma typing_binding_multiincr' [simp]: "\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b es : ts \<Longrightarrow> 
  \<Gamma>\<^sub>1 @ \<Gamma>' @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b map_with_idx (length \<Gamma>\<^sub>1) (multiincr (length \<Gamma>')) es : ts"
proof (induction \<Gamma>')
  case Nil
  thus ?case by simp
next
  case (Cons t \<Gamma>')
  hence "\<Gamma>\<^sub>1 @ t # \<Gamma>' @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b map_with_idx (length \<Gamma>\<^sub>1) (\<lambda>k. multiincr (Suc (length \<Gamma>')) k) es : ts" 
    by simp
  hence "\<Gamma>\<^sub>1 @ t # \<Gamma>' @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d\<^sub>b map_with_idx (length \<Gamma>\<^sub>1) (multiincr (Suc (length \<Gamma>'))) es : ts" 
    by blast
  thus ?case by (simp del: multiincr.simps)
qed

lemma typing_binding_multiincr: "\<Gamma> \<turnstile>\<^sub>d\<^sub>b es : ts \<Longrightarrow> 
  \<Gamma>' @ \<Gamma> \<turnstile>\<^sub>d\<^sub>b map_with_idx 0 (multiincr (length \<Gamma>')) es : ts"
proof -
  assume "\<Gamma> \<turnstile>\<^sub>d\<^sub>b es : ts"
  hence "[] @ \<Gamma>' @ \<Gamma> \<turnstile>\<^sub>d\<^sub>b map_with_idx (length []) (multiincr (length \<Gamma>')) es : ts" 
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
  thus ?case by (induction \<Gamma>) simp_all
qed simp_all

theorem typing_float_lets [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d float_lets e : t"
proof (induction \<Gamma> e t rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  let ?es\<^sub>1 = "strip_lets (float_lets e\<^sub>1)"
  let ?e\<^sub>1 = "inner_expr (float_lets e\<^sub>1)"
  let ?es\<^sub>2 = "strip_lets (float_lets e\<^sub>2)"
  from tc\<^sub>d_app obtain ts\<^sub>1 where T1: "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b ?es\<^sub>1 : ts\<^sub>1) \<and> (ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d ?e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2)" 
    by fastforce
  from tc\<^sub>d_app obtain ts\<^sub>2 where T2: "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b ?es\<^sub>2 : ts\<^sub>2) \<and> 
    (ts\<^sub>2 @ \<Gamma> \<turnstile>\<^sub>d inner_expr (float_lets e\<^sub>2) : t\<^sub>1)" by fastforce
  show ?case
  proof (cases "is_var ?e\<^sub>1 \<or> value\<^sub>d ?e\<^sub>1")
    case True
    from T1 T2 have TS2: "ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d\<^sub>b map_with_idx 0 (multiincr (length ?es\<^sub>1)) ?es\<^sub>2 : ts\<^sub>2" 
      by (metis typing_bindings_eq_length typing_binding_multiincr)
    from T1 T2 have "ts\<^sub>2 @ ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d multiincr (length ?es\<^sub>2) 0 ?e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2"
      by (metis append.left_neutral list.size(3) typing_bindings_eq_length typing_multiincr)
    with T1 T2 TS2 True show ?thesis by (auto simp add: Let_def)
  next
    case False
    from T1 T2 have TS2: "Arrow t\<^sub>1 t\<^sub>2 # ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d\<^sub>b 
      map_with_idx 0 (multiincr (Suc (length ?es\<^sub>1))) ?es\<^sub>2 : ts\<^sub>2" 
        by (metis length_Cons typing_bindings_eq_length typing_binding_multiincr append_Cons)
    from T1 T2 have X: "ts\<^sub>2 @ Arrow t\<^sub>1 t\<^sub>2 # ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d Var\<^sub>d (length ?es\<^sub>2) : Arrow t\<^sub>1 t\<^sub>2" by auto
    from T2 have "ts\<^sub>2 @ Arrow t\<^sub>1 t\<^sub>2 # ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d 
      multiincr (Suc (length ts\<^sub>1)) (length ts\<^sub>2) (inner_expr (float_lets e\<^sub>2)) : t\<^sub>1"
        by (metis append_Cons length_Cons typing_multiincr)
    with T1 T2 have "ts\<^sub>2 @ Arrow t\<^sub>1 t\<^sub>2 # ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d 
      multiincr (Suc (length ?es\<^sub>1)) (length ?es\<^sub>2) (inner_expr (float_lets e\<^sub>2)) : t\<^sub>1" by auto
    with X have "ts\<^sub>2 @ Arrow t\<^sub>1 t\<^sub>2 # ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d 
      App\<^sub>d (Var\<^sub>d (length ?es\<^sub>2)) (incr\<^sub>d (length ?es\<^sub>2) (multiincr (length ?es\<^sub>1) (length ?es\<^sub>2) 
        (inner_expr (float_lets e\<^sub>2)))) : t\<^sub>2" by simp
    with T1 TS2 False show ?thesis by (cases "ts\<^sub>1 @ \<Gamma>") (auto simp add: Let_def)
  qed
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
  by (induction es) simp_all

lemma float_lets_val [simp]: "value\<^sub>d (float_lets e) = value\<^sub>d e"
  by (induction e) (auto simp add: Let_def split: prod.splits)

lemma strip_lets_incr [simp]: "strip_lets (incr\<^sub>d x e) = map_with_idx x incr\<^sub>d (strip_lets e)"
  by (induction e arbitrary: x) (auto simp add: comp_def split: prod.splits)

lemma inner_expr_incr [simp]: "inner_expr (incr\<^sub>d x e) = 
    incr\<^sub>d (length (strip_lets e) + x) (inner_expr e)"
  by (induction e arbitrary: x) (auto simp add: comp_def split: prod.splits)

lemma reapply_let_incr [simp]: "incr\<^sub>d x (reapply_lets es e) = 
    reapply_lets (map_with_idx x incr\<^sub>d es) (incr\<^sub>d (x + length es) e)"
  by (induction es arbitrary: x) (simp_all add: comp_def)

lemma float_lets_lemma [simp]: "z \<le> x \<Longrightarrow> 
  map_with_idx z (multiincr y) (map_with_idx x incr\<^sub>d es) =
    map_with_idx (x + y) incr\<^sub>d (map_with_idx z (multiincr y) es)"
  by (induction es arbitrary: z x) simp_all

lemma float_lets_lemma2 [simp]: "map_with_idx z (multiincr y) 
  (map_with_idx z (\<lambda>k. subst\<^sub>d (k + x) (multiincr k 0 v)) es) = 
    map_with_idx z (\<lambda>k. subst\<^sub>d (k + (x + y)) (multiincr k 0 (multiincr y 0 v))) 
      (map_with_idx z (multiincr y) es)"
  by (induction es arbitrary: z) (simp_all add: add.commute add.left_commute)

lemma float_lets_incr [simp]: "float_lets (incr\<^sub>d x e) = incr\<^sub>d x (float_lets e)"
  by (induction e arbitrary: x) (simp_all add: Let_def incr_above add.commute add.left_commute)

lemma reapply_let_multiincr [simp]: "multiincr x y (reapply_lets es e) = 
    reapply_lets (map_with_idx y (multiincr x) es) (multiincr x (y + length es) e)"
  by (induction es arbitrary: y) simp_all

lemma strip_lets_subst [simp]: "value\<^sub>d v \<Longrightarrow>
    strip_lets (subst\<^sub>d x v e) = map_with_idx 0 (\<lambda>k. subst\<^sub>d (k + x) (multiincr k 0 v)) (strip_lets e)"
  by (induction e arbitrary: x v) (auto split: prod.splits)

lemma inner_expr_subst [simp]: "value\<^sub>d v \<Longrightarrow> inner_expr (subst\<^sub>d x v e) = 
    subst\<^sub>d (length (strip_lets e) + x) (multiincr (length (strip_lets e)) 0 v) (inner_expr e)"
  by (induction e arbitrary: x v) (auto split: prod.splits)

lemma reapply_let_subst [simp]: "subst\<^sub>d x v (reapply_lets es e) = 
  reapply_lets (map_with_idx 0 (\<lambda>k. subst\<^sub>d (k + x) (multiincr k 0 v)) es) 
    (subst\<^sub>d (x + length es) (multiincr (length es) 0 v) e)"
  by (induction es arbitrary: x v) simp_all

lemma float_lets_subst [simp]: "value\<^sub>d v \<Longrightarrow> 
  float_lets (subst\<^sub>d x v e) = subst\<^sub>d x (float_lets v) (float_lets e)"
proof (induction e arbitrary: x v)
  case (App\<^sub>d e1 e2)
  let ?es\<^sub>1 = "strip_lets (float_lets e1)"
  let ?es\<^sub>2 = "strip_lets (float_lets e2)"
  have A: "length ?es\<^sub>1 + (x + length ?es\<^sub>2) = length ?es\<^sub>2 + (x + length ?es\<^sub>1)" by simp
  from App\<^sub>d show ?case 
    by (auto simp add: Let_def add.commute incr_multiincr_higher A split: expr\<^sub>d.splits)
qed (simp_all add: Let_def add.commute)

lemma map_incr_subst_cancel [simp]: "
    map_with_idx x (\<lambda>k. subst\<^sub>d k (e k)) (map_with_idx x incr\<^sub>d es) = es"
  by (induction es arbitrary: x) simp_all

text \<open>And now, the key correctness proof. We are faced with a surprising obstacle: it's simply 
untrue that small-step evaluation preserves let-floatedness! To see why, consider the expression
\<open>Let\<^sub>d (App\<^sub>d (Lam\<^sub>d t (Let\<^sub>d e\<^sub>1 e\<^sub>2)) v\<^sub>3) e\<^sub>4\<close>, which is in let-floated form. One step of evaluation takes
it to \<open>Let\<^sub>d (Let\<^sub>d (subst\<^sub>d 0 v\<^sub>3 e\<^sub>1) (subst\<^sub>d (Suc 0) (incr\<^sub>d 0 v\<^sub>3) e\<^sub>2)) e\<^sub>4\<close>, which is not - it has a let 
nested inside another let's left-hand side. Instead we must fall back on big-step evaluation, which
_is_ preserved.\<close>

lemma eval_strip_lets_let [simp]: "e\<^sub>1 \<Down>\<^sub>d v\<^sub>1 \<Longrightarrow> subst\<^sub>d 0 v\<^sub>1 e\<^sub>2 \<Down>\<^sub>d v\<^sub>2 \<Longrightarrow> 
  reapply_lets (strip_lets e\<^sub>1) (Let\<^sub>d (inner_expr e\<^sub>1) (multiincr (length (strip_lets e\<^sub>1)) (Suc 0) e\<^sub>2)) 
    \<Down>\<^sub>d v\<^sub>2"
proof (induction e\<^sub>1 v\<^sub>1 rule: big_eval\<^sub>d.induct)
  case (bev\<^sub>d_const n)
  hence "Let\<^sub>d (Const\<^sub>d n) e\<^sub>2 \<Down>\<^sub>d v\<^sub>2" by (metis bev\<^sub>d_let big_eval\<^sub>d.bev\<^sub>d_const)
  thus ?case by simp
next
  case (bev\<^sub>d_lam t e)
  hence "Let\<^sub>d (Lam\<^sub>d t e) e\<^sub>2 \<Down>\<^sub>d v\<^sub>2" by (metis bev\<^sub>d_let big_eval\<^sub>d.bev\<^sub>d_lam)
  thus ?case by simp
next
  case (bev\<^sub>d_app e\<^sub>1\<^sub>1 t e\<^sub>1\<^sub>1' e\<^sub>1\<^sub>2 v\<^sub>1\<^sub>2 v)
  hence "Let\<^sub>d (App\<^sub>d e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2) e\<^sub>2 \<Down>\<^sub>d v\<^sub>2" by (metis bev\<^sub>d_let big_eval\<^sub>d.bev\<^sub>d_app)
  thus ?case by simp
next
  case (bev\<^sub>d_let e\<^sub>1\<^sub>1 v\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2 v\<^sub>1\<^sub>2)
  thus ?case by simp
qed

lemma eval_strip_lets_app [simp]: "e\<^sub>2 \<Down>\<^sub>d v\<^sub>2 \<Longrightarrow> e\<^sub>1 \<Down>\<^sub>d Lam\<^sub>d t e\<^sub>1' \<Longrightarrow> subst\<^sub>d 0 v\<^sub>2 e\<^sub>1' \<Down>\<^sub>d v \<Longrightarrow>
  reapply_lets (strip_lets e\<^sub>2) 
    (App\<^sub>d (multiincr (length (strip_lets e\<^sub>2)) 0 e\<^sub>1) (inner_expr e\<^sub>2)) \<Down>\<^sub>d v"
proof (induction e\<^sub>2 v\<^sub>2 rule: big_eval\<^sub>d.induct)
  case (bev\<^sub>d_const n)
  hence "App\<^sub>d e\<^sub>1 (Const\<^sub>d n) \<Down>\<^sub>d v" by (metis bev\<^sub>d_app big_eval\<^sub>d.bev\<^sub>d_const)
  thus ?case by simp
next
  case (bev\<^sub>d_lam tt e)
  hence "App\<^sub>d e\<^sub>1 (Lam\<^sub>d tt e) \<Down>\<^sub>d v" by (metis bev\<^sub>d_app big_eval\<^sub>d.bev\<^sub>d_lam)
  thus ?case by simp
next
  case (bev\<^sub>d_app e\<^sub>2\<^sub>1 tt e\<^sub>2\<^sub>1' e\<^sub>2\<^sub>2 v\<^sub>2\<^sub>2 v\<^sub>2)
  hence "App\<^sub>d e\<^sub>1 (App\<^sub>d e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2) \<Down>\<^sub>d v" by (metis big_eval\<^sub>d.bev\<^sub>d_app)
  thus ?case by simp
next
  case (bev\<^sub>d_let e\<^sub>2\<^sub>1 v\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2 v\<^sub>2\<^sub>2)
  thus ?case by simp
qed

lemma eval_strip_lets_app' [simp]: "e\<^sub>2 \<Down>\<^sub>d v\<^sub>2 \<Longrightarrow> subst\<^sub>d 0 v\<^sub>2 e\<^sub>1 \<Down>\<^sub>d v \<Longrightarrow>
  reapply_lets (strip_lets e\<^sub>2) 
    (App\<^sub>d (Lam\<^sub>d t (multiincr (length (strip_lets e\<^sub>2)) (Suc 0) e\<^sub>1)) (inner_expr e\<^sub>2)) \<Down>\<^sub>d v"
  by (metis eval_strip_lets_app multiincr_lam bev\<^sub>d_lam)

lemma eval_strip_lets_app'' [simp]: "App\<^sub>d e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2 \<Down>\<^sub>d Lam\<^sub>d t e\<^sub>1' \<Longrightarrow> e\<^sub>2 \<Down>\<^sub>d v\<^sub>2 \<Longrightarrow> 
  subst\<^sub>d 0 v\<^sub>2 e\<^sub>1' \<Down>\<^sub>d v \<Longrightarrow> 
    reapply_lets (strip_lets e\<^sub>2) (App\<^sub>d (App\<^sub>d (multiincr (length (strip_lets e\<^sub>2)) 0 e\<^sub>2\<^sub>1) 
      (multiincr (length (strip_lets e\<^sub>2)) 0 e\<^sub>2\<^sub>2)) (inner_expr e\<^sub>2)) \<Down>\<^sub>d v" 
  by (metis eval_strip_lets_app multiincr_app)

lemma eval_strip_lets_app2 [simp]: "e\<^sub>1 \<Down>\<^sub>d Lam\<^sub>d t e\<^sub>1' \<Longrightarrow> e\<^sub>2 \<Down>\<^sub>d v\<^sub>2 \<Longrightarrow> subst\<^sub>d 0 v\<^sub>2 e\<^sub>1' \<Down>\<^sub>d v \<Longrightarrow> 
  reapply_lets (strip_lets e\<^sub>1) 
    (reapply_lets (map_with_idx 0 (multiincr (length (strip_lets e\<^sub>1))) (strip_lets e\<^sub>2))
      (App\<^sub>d (multiincr (length (strip_lets e\<^sub>2)) 0 (inner_expr e\<^sub>1))
        (multiincr (length (strip_lets e\<^sub>1)) (length (strip_lets e\<^sub>2)) (inner_expr e\<^sub>2)))) \<Down>\<^sub>d v"
proof (induction e\<^sub>1 "Lam\<^sub>d t e\<^sub>1'" rule: big_eval\<^sub>d.induct)
  case (bev\<^sub>d_app e\<^sub>2\<^sub>1 tt e\<^sub>2\<^sub>1' e\<^sub>2\<^sub>2 v\<^sub>2\<^sub>2)
  hence "App\<^sub>d e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2 \<Down>\<^sub>d Lam\<^sub>d t e\<^sub>1'" by simp
  with bev\<^sub>d_app have "reapply_lets (strip_lets e\<^sub>2)
    (App\<^sub>d (App\<^sub>d (multiincr (length (strip_lets e\<^sub>2)) 0 e\<^sub>2\<^sub>1) 
      (multiincr (length (strip_lets e\<^sub>2)) 0 e\<^sub>2\<^sub>2)) (inner_expr e\<^sub>2)) \<Down>\<^sub>d v" 
    by (metis eval_strip_lets_app'')
  thus ?case by simp
next
  case (bev\<^sub>d_let e\<^sub>2\<^sub>1 v\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2)
  let ?e\<^sub>2\<^sub>2 = "strip_lets e\<^sub>2\<^sub>2"
  let ?e\<^sub>2 = "strip_lets e\<^sub>2"
  from bev\<^sub>d_let have "reapply_lets (map_with_idx 0 (\<lambda>k. subst\<^sub>d k (multiincr k 0 v\<^sub>2\<^sub>1)) ?e\<^sub>2\<^sub>2)
     (reapply_lets (map_with_idx 0 (multiincr (length ?e\<^sub>2\<^sub>2)) ?e\<^sub>2)
       (App\<^sub>d
         (subst\<^sub>d (length ?e\<^sub>2\<^sub>2 + length ?e\<^sub>2)
           (multiincr (length ?e\<^sub>2) 0 (multiincr (length ?e\<^sub>2\<^sub>2) 0 v\<^sub>2\<^sub>1))
           (multiincr (length ?e\<^sub>2) 0 (inner_expr e\<^sub>2\<^sub>2)))
         (multiincr (length ?e\<^sub>2\<^sub>2) (length ?e\<^sub>2) (inner_expr e\<^sub>2)))) \<Down>\<^sub>d
    v" by (simp add: add.commute)
  with bev\<^sub>d_let show ?case by simp
qed simp_all

theorem correctness\<^sub>f\<^sub>l [simp]: "e \<Down>\<^sub>d e' \<Longrightarrow> float_lets e \<Down>\<^sub>d float_lets e'"
proof (induction e e' rule: big_eval\<^sub>d.induct)
  case (bev\<^sub>d_app e\<^sub>1 t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  let ?es\<^sub>1 = "strip_lets (float_lets e\<^sub>1)"
  let ?e\<^sub>1 = "inner_expr (float_lets e\<^sub>1)"
  let ?es\<^sub>2 = "strip_lets (float_lets e\<^sub>2)"
  let ?e\<^sub>2 = "inner_expr (float_lets e\<^sub>2)"
  from bev\<^sub>d_app show ?case
  proof (cases "is_var ?e\<^sub>1 \<or> value\<^sub>d ?e\<^sub>1")
    case False
    from bev\<^sub>d_app have "subst\<^sub>d 0 (Lam\<^sub>d t (float_lets e\<^sub>1')) (reapply_lets (map_with_idx 0 incr\<^sub>d ?es\<^sub>2) 
      (App\<^sub>d (Var\<^sub>d (length ?es\<^sub>2)) (incr\<^sub>d (length ?es\<^sub>2) ?e\<^sub>2))) \<Down>\<^sub>d float_lets v" by simp
    with bev\<^sub>d_app have "reapply_lets ?es\<^sub>1 (Let\<^sub>d ?e\<^sub>1 (multiincr (length ?es\<^sub>1) (Suc 0) 
      (reapply_lets (map_with_idx 0 incr\<^sub>d ?es\<^sub>2) (App\<^sub>d (Var\<^sub>d (length ?es\<^sub>2)) (incr\<^sub>d (length ?es\<^sub>2) ?e\<^sub>2))))) 
        \<Down>\<^sub>d float_lets v" by (metis eval_strip_lets_let float_lets.simps(3))
    with False show ?thesis by (simp add: Let_def)
  qed (simp_all add: Let_def)
qed (simp_all add: Let_def)

end