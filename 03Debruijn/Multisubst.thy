theory Multisubst
  imports DebruijnIndices
begin

subsection \<open>Multiple substitution\<close>

text \<open>We now want to prove termination. But in order to do that, we need one more tool. Multiple
substitution replaces every free variable in an expression with a sequence of closed expressions.\<close>

primrec multisubst :: "expr\<^sub>d list \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "multisubst [] e = e"
| "multisubst (e' # es) e = multisubst es (subst\<^sub>d 0 e' e)"

lemma multisubst_no_vars [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> multisubst es e = e"
  by (induction es) simp_all

text \<open>Explicitly multiple-substituting over constructors is easy in every case but one. Binders 
cause problems for a simple compositional definition, because they increment the substitution index
and \<open>multisubst\<close> only substitutes at 0. We provide a simple solution here and a more precise one, 
using typechecking side conditions, below.\<close>

lemma multisubst_var [simp]: "lookup vs x = Some v \<Longrightarrow> 
    (\<And>v es. v \<in> set vs \<Longrightarrow> multisubst es v = v) \<Longrightarrow> multisubst vs (Var\<^sub>d x) = v"
  by (induction vs x rule: lookup.induct) simp_all

lemma multisubst_const [simp]: "multisubst es (Const\<^sub>d n) = Const\<^sub>d n"
  by (induction es) simp_all

lemma multisubst_lam_simple [simp]: "\<exists>e'. multisubst es (Lam\<^sub>d t e) = Lam\<^sub>d t e'"
  by (induction es arbitrary: e) simp_all

lemma multisubst_app [simp]: "multisubst es (App\<^sub>d e\<^sub>1 e\<^sub>2) = App\<^sub>d (multisubst es e\<^sub>1) (multisubst es e\<^sub>2)"
  by (induction es arbitrary: e\<^sub>1 e\<^sub>2) simp_all

lemma multisubst_lam_to_app [dest]: "App\<^sub>d e\<^sub>1 e\<^sub>2 = multisubst es (Lam\<^sub>d t e) \<Longrightarrow> False"
proof -
  assume "App\<^sub>d e\<^sub>1 e\<^sub>2 = multisubst es (Lam\<^sub>d t e)"
  moreover obtain e' where "multisubst es (Lam\<^sub>d t e) = Lam\<^sub>d t e'" by fastforce
  ultimately show ?thesis by simp
qed

text \<open>Typechecking the sequence of expressions to be multiply-substituted in is simple: they must 
all be closed values, and they must match the typing context type-for-type. \<close>

inductive tc_expr_context :: "ty list \<Rightarrow> expr\<^sub>d list \<Rightarrow> bool" where
  tcp_nil [simp]: "tc_expr_context [] []"
| tcp_cons [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> value\<^sub>d e \<Longrightarrow> tc_expr_context \<Gamma> es \<Longrightarrow> 
    tc_expr_context (t # \<Gamma>) (e # es)"

lemma tc_expr_context_insert [simp]: "tc_expr_context \<Gamma> es \<Longrightarrow> value\<^sub>d e \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> 
  [] \<turnstile>\<^sub>d e : t \<Longrightarrow> tc_expr_context (insert_at x t \<Gamma>) (insert_at x e es)"
proof (induction \<Gamma> es arbitrary: x rule: tc_expr_context.induct)
  case (tcp_cons t' e' \<Gamma> es)
  then show ?case by (induction x) simp_all
qed simp_all

lemma tc_multisubst [simp]: "tc_expr_context \<Gamma> es \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> [] \<turnstile>\<^sub>d multisubst es e : t"
proof (induction \<Gamma> es arbitrary: e rule: tc_expr_context.induct)
  case (tcp_cons e' t' \<Gamma> es)
  moreover hence "insert_at 0 t' \<Gamma> \<turnstile>\<^sub>d e : t" by (induction \<Gamma>) simp_all
  moreover from tcp_cons have "[] \<turnstile>\<^sub>d e' : t'" by simp
  moreover hence "\<Gamma> \<turnstile>\<^sub>d e' : t'" using tc_postpend by fastforce
  ultimately show ?case by simp
qed simp_all

lemma multisubst_lam_complex [simp]: "tc_expr_context \<Gamma> es \<Longrightarrow> insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e : t\<^sub>2 \<Longrightarrow> 
  \<exists>e'. multisubst es (Lam\<^sub>d t\<^sub>1 e) = Lam\<^sub>d t\<^sub>1 e' \<and> ([t\<^sub>1] \<turnstile>\<^sub>d e' : t\<^sub>2) \<and>
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> multisubst es (subst\<^sub>d 0 e\<^sub>2 e) = subst\<^sub>d 0 e\<^sub>2 e')"
proof (induction \<Gamma> es arbitrary: e rule: tc_expr_context.induct)
  case (tcp_cons e' t \<Gamma> es)
  hence "[] \<turnstile>\<^sub>d e' : t" by simp
  hence "\<Gamma> \<turnstile>\<^sub>d e' : t" using tc_postpend by fastforce
  hence "insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d incr\<^sub>d 0 e' : t" by simp
  with tcp_cons show ?case by (cases \<Gamma>) simp_all
qed simp_all

end