theory Multisubst
  imports DebruijnIndices
begin

subsection \<open>Multiple substitution\<close>

text \<open>We now want to prove termination. But in order to do that, we need one more tool. Multiple
substitution replaces every free variable above an index in an expression with a sequence of closed 
expressions. We will most often be using it with an index of 0, that is, eliminating _all_ free 
variables. \<close>

primrec multisubst' :: "nat \<Rightarrow> expr\<^sub>d list \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "multisubst' x [] e = e"
| "multisubst' x (e' # es) e = multisubst' x es (subst\<^sub>d x e' e)"

abbreviation multisubst :: "expr\<^sub>d list \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "multisubst es e \<equiv> multisubst' 0 es e"

lemma multisubst_no_vars [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> multisubst' x es e = e"
  by (induction es) simp_all

lemma multisubst'_var1 [simp]: "x \<ge> y \<Longrightarrow> lookup vs (x - y) = Some v \<Longrightarrow> 
  (\<And>v es. v \<in> set vs \<Longrightarrow> multisubst' y es v = v) \<Longrightarrow> multisubst' y vs (Var\<^sub>d x) = v"
proof (induction vs x rule: lookup.induct)
  case (3 a as x)
  thus ?case
  proof (cases "y = Suc x")
    case False
    with 3 have "Suc x - y = Suc (x - y)" by simp
    with 3 False show ?thesis by simp
  qed simp_all
qed simp_all

lemma multisubst_var1 [simp]: "lookup vs x = Some v \<Longrightarrow> 
    (\<And>v es. v \<in> set vs \<Longrightarrow> multisubst es v = v) \<Longrightarrow> multisubst vs (Var\<^sub>d x) = v"
  by simp

lemma multisubst_var2 [simp]: "x < y \<Longrightarrow> multisubst' y vs (Var\<^sub>d x) = Var\<^sub>d x"
  by (induction vs) simp_all

lemma multisubst_const [simp]: "multisubst' x es (Const\<^sub>d n) = Const\<^sub>d n"
  by (induction es) simp_all

lemma multisubst_lam [simp]: "multisubst' x es (Lam\<^sub>d t e) = 
    Lam\<^sub>d t (multisubst' (Suc x) (map (incr\<^sub>d 0) es) e)"
  by (induction es arbitrary: e) simp_all

lemma multisubst_app [simp]: "multisubst' x es (App\<^sub>d e\<^sub>1 e\<^sub>2) = 
    App\<^sub>d (multisubst' x es e\<^sub>1) (multisubst' x es e\<^sub>2)"
  by (induction es arbitrary: e\<^sub>1 e\<^sub>2) simp_all

lemma multisubst_let [simp]: "multisubst' x es (Let\<^sub>d e\<^sub>1 e\<^sub>2) = 
    Let\<^sub>d (multisubst' x es e\<^sub>1) (multisubst' (Suc x) (map (incr\<^sub>d 0) es) e\<^sub>2)"
  by (induction es arbitrary: e\<^sub>1 e\<^sub>2) simp_all

lemma multisubst_subst_swap: "y \<le> x \<Longrightarrow> multisubst' x es (subst\<^sub>d y e' e) = 
    subst\<^sub>d y (multisubst' x es e') (multisubst' (Suc x) (map (incr\<^sub>d y) es) e)"
  by (induction es arbitrary: e' e) simp_all

text \<open>Typechecking the sequence of expressions to be multiply-substituted in is simple: they must 
all be closed values, and they must match the typing context type-for-type. \<close>

inductive tc_expr_context :: "ty list \<Rightarrow> expr\<^sub>d list \<Rightarrow> bool" where
  tcp_nil [simp]: "tc_expr_context [] []"
| tcp_cons [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> value\<^sub>d e \<Longrightarrow> tc_expr_context \<Gamma> es \<Longrightarrow> 
    tc_expr_context (t # \<Gamma>) (e # es)"

lemma tc_expr_context_incr [simp]: "tc_expr_context \<Gamma> es \<Longrightarrow> tc_expr_context \<Gamma> (map (incr\<^sub>d x) es)"
  by (induction \<Gamma> es rule: tc_expr_context.induct) simp_all

lemma tc_expr_context_insert [simp]: "tc_expr_context \<Gamma> es \<Longrightarrow> value\<^sub>d e \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> 
  [] \<turnstile>\<^sub>d e : t \<Longrightarrow> tc_expr_context (insert_at x t \<Gamma>) (insert_at x e es)"
proof (induction \<Gamma> es arbitrary: x rule: tc_expr_context.induct)
  case (tcp_cons t' e' \<Gamma> es)
  then show ?case by (induction x) simp_all
qed simp_all

lemma tc_multisubst' [simp]: "tc_expr_context \<Gamma> es \<Longrightarrow> \<Gamma>' @ \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> 
  \<Gamma>' \<turnstile>\<^sub>d multisubst' (length \<Gamma>') es e : t"
proof (induction \<Gamma> es arbitrary: e rule: tc_expr_context.induct)
  case (tcp_cons e' t' \<Gamma> es)
  hence "\<Gamma>' @ \<Gamma> \<turnstile>\<^sub>d e' : t'" by (metis append_Nil tc_postpend)
  with tcp_cons show ?case by simp
qed simp_all

lemma tc_multisubst [simp]: "tc_expr_context \<Gamma> es \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> [] \<turnstile>\<^sub>d multisubst es e : t"
proof -
  assume "\<Gamma> \<turnstile>\<^sub>d e : t" 
  hence "[] @ \<Gamma> \<turnstile>\<^sub>d e : t" by simp
  moreover assume "tc_expr_context \<Gamma> es"
  ultimately show ?thesis using tc_multisubst' by fastforce
qed

lemma multisubst_above [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> multisubst' (length \<Gamma>) es e = e"
  by (induction es) simp_all

lemma multisubst_twice [simp]: "tc_expr_context \<Gamma> es \<Longrightarrow> \<Gamma>' @ \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> 
    multisubst' (length \<Gamma>') es' (multisubst' (length \<Gamma>') es e) = multisubst' (length \<Gamma>') es e"
proof -
  assume "tc_expr_context \<Gamma> es" and "\<Gamma>' @ \<Gamma> \<turnstile>\<^sub>d e : t"
  hence "\<Gamma>' \<turnstile>\<^sub>d multisubst' (length \<Gamma>') es e : t" by simp
  thus ?thesis by simp
qed

lemma incr_multisubst_absorb [simp]: "tc_expr_context \<Gamma> es \<Longrightarrow> \<Gamma>' @ \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> 
  x \<ge> length \<Gamma>' \<Longrightarrow> incr\<^sub>d x (multisubst' (length \<Gamma>') es e) = multisubst' (length \<Gamma>') es e"
proof (induction \<Gamma> es arbitrary: e rule: tc_expr_context.induct)
  case (tcp_cons e' t' \<Gamma> es)
  moreover hence "\<Gamma>' @ \<Gamma> \<turnstile>\<^sub>d e' : t'" by (metis append.left_neutral tc_postpend)
  ultimately show ?case by simp
qed simp_all

end