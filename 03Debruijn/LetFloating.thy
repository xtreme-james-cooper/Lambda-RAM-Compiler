theory LetFloating
  imports BigStep
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
eagerly-evaluated language, all three subexpressions must be evaluated - but the scope of the \<open>Let\<^sub>s\<close> 
now extends to the end of the expression. Similar transformations can be applied to 
\<open>App\<^sub>s e\<^sub>1 (Let\<^sub>s e\<^sub>2\<^sub>1 e\<^sub>2\<^sub>2)\<close> and \<open>Let\<^sub>s (Let\<^sub>s e\<^sub>1\<^sub>1 e\<^sub>1\<^sub>2) e\<^sub>2\<close>, meaning that we can arrive at a form where every 
lambda-expression is of the shape \<open>Lam\<^sub>s t (Let\<^sub>s e\<^sub>1 (... (Let\<^sub>s e\<^sub>n e) ...))\<close>, n \<ge> 0, and there are no 
\<open>Let\<^sub>s\<close>s in any of the \<open>e\<close>s except under similarly-shaped lambda-expressions. (The top-level program 
could in general not be a lambda-expression, but it will end with a \<open>Return\<^sub>e\<close> as well, so similar 
remarks apply.) This means that _every_ \<open>PopEnv\<^sub>e\<close> will occur right before a \<open>Return\<^sub>e\<close>, and so can be 
eliminated - and we can avoid compiling any code for \<open>PopEnv\<^sub>e\<close> at all.\<close>

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
  "multiincr 0 y e = e"
| "multiincr (Suc x) y e = incr\<^sub>d y (multiincr x y e)"

fun strip_lets :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d list \<times> expr\<^sub>d" where
  "strip_lets (Let\<^sub>d e\<^sub>1 e\<^sub>2) = (case strip_lets e\<^sub>2 of
    (es, e\<^sub>2') \<Rightarrow> (e\<^sub>1 # es, e\<^sub>2'))"
| "strip_lets e = ([], e)"

primrec float_lets :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "float_lets (Var\<^sub>d x) = Var\<^sub>d x"
| "float_lets (Const\<^sub>d n) = Const\<^sub>d n"
| "float_lets (Lam\<^sub>d t e) = Lam\<^sub>d t (float_lets e)"
| "float_lets (App\<^sub>d e\<^sub>1 e\<^sub>2) = (case strip_lets (float_lets e\<^sub>1) of
    (es\<^sub>1, e\<^sub>1') \<Rightarrow> (case strip_lets (multiincr (length es\<^sub>1) 0 (float_lets e\<^sub>2)) of
      (es\<^sub>2, e\<^sub>2') \<Rightarrow> foldr Let\<^sub>d (es\<^sub>1 @ es\<^sub>2) (App\<^sub>d (multiincr (length es\<^sub>2) (length es\<^sub>1) e\<^sub>1') e\<^sub>2')))"
| "float_lets (Let\<^sub>d e\<^sub>1 e\<^sub>2) = (case strip_lets (float_lets e\<^sub>1) of
    (es\<^sub>1, e\<^sub>1') \<Rightarrow> foldr Let\<^sub>d es\<^sub>1 (Let\<^sub>d e\<^sub>1' (multiincr (length es\<^sub>1) 1 (float_lets e\<^sub>2))))"

lemma incr_let_free [simp]: "let_free (incr\<^sub>d x e) = let_free e"
  by (induction e arbitrary: x) simp_all

lemma incr_let_floated [simp]: "let_floated (incr\<^sub>d x e) = let_floated e"
  by (induction e arbitrary: x) simp_all

lemma multiincr_let_free [simp]: "let_free (multiincr x y e) = let_free e"
  by (induction x) simp_all

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
  obtain es\<^sub>2 e\<^sub>2' where E2: "strip_lets (multiincr (length es\<^sub>1) 0 (float_lets e2)) = (es\<^sub>2, e\<^sub>2')" 
    by fastforce
  from App\<^sub>d have "let_floated (multiincr (length es\<^sub>1) 0 (float_lets e2))" by simp
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

lemma typing_multiincr [simp]: "\<Gamma>\<^sub>1 @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d e : t \<Longrightarrow> 
    \<Gamma>\<^sub>1 @ \<Gamma>' @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d multiincr (length \<Gamma>') (length \<Gamma>\<^sub>1) e : t"
proof (induction \<Gamma>')
  case (Cons tt \<Gamma>')
  hence "insert_at (length \<Gamma>\<^sub>1) tt (\<Gamma>\<^sub>1 @ \<Gamma>' @ \<Gamma>\<^sub>2) \<turnstile>\<^sub>d 
    incr\<^sub>d (length \<Gamma>\<^sub>1) (multiincr (length \<Gamma>') (length \<Gamma>\<^sub>1) e) : t" by simp
  hence "\<Gamma>\<^sub>1 @ tt # \<Gamma>' @ \<Gamma>\<^sub>2 \<turnstile>\<^sub>d incr\<^sub>d (length \<Gamma>\<^sub>1) (multiincr (length \<Gamma>') (length \<Gamma>\<^sub>1) e) : t" try by simp
  thus ?case by simp
qed simp_all

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

theorem typing_float_lets [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d float_lets e : t"
proof (induction \<Gamma> e t rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  obtain es\<^sub>1 e\<^sub>1' where E1: "strip_lets (float_lets e\<^sub>1) = (es\<^sub>1, e\<^sub>1')" by fastforce
  with tc\<^sub>d_app obtain ts\<^sub>1 where "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b es\<^sub>1 : ts\<^sub>1) \<and> (ts\<^sub>1 @ \<Gamma> \<turnstile>\<^sub>d e\<^sub>1' : Arrow t\<^sub>1 t\<^sub>2)" by fastforce


  obtain es\<^sub>2 e\<^sub>2' where E2: "strip_lets (multiincr (length es\<^sub>1) 0 (float_lets e\<^sub>2)) = (es\<^sub>2, e\<^sub>2')" by fastforce

  from tc\<^sub>d_app have "\<Gamma> \<turnstile>\<^sub>d float_lets e\<^sub>2 : t\<^sub>1" by simp
  
  
  with tc\<^sub>d_app obtain ts\<^sub>2 where "(\<Gamma> \<turnstile>\<^sub>d\<^sub>b es\<^sub>2 : ts\<^sub>2) \<and> (ts\<^sub>2 @ \<Gamma> \<turnstile>\<^sub>d e\<^sub>2' : t\<^sub>1)" by fastforcex


  from tc\<^sub>d_app have "\<Gamma> \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by simp
  from tc\<^sub>d_app have "\<Gamma> \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" by simp
  from tc\<^sub>d_app have "\<Gamma> \<turnstile>\<^sub>d float_lets e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by simp
  from tc\<^sub>d_app have "\<Gamma> \<turnstile>\<^sub>d float_lets e\<^sub>2 : t\<^sub>1" by simp




  have "\<Gamma> \<turnstile>\<^sub>d foldr Let\<^sub>d es\<^sub>1 (foldr Let\<^sub>d es\<^sub>2 (App\<^sub>d (multiincr (length es\<^sub>2) (length es\<^sub>1) e\<^sub>1') e\<^sub>2')) : t\<^sub>2" by simp
  with E1 E2 show ?case by simp
next
  case (tc\<^sub>d_let \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
  then show ?case by simp
qed simp_all

end