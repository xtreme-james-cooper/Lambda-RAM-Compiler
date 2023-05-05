theory Multisubst
  imports Debruijn
begin

inductive tc_pairs :: "ty list \<Rightarrow> dexpr list \<Rightarrow> bool" where
  tcp_nil [simp]: "tc_pairs [] []"
| tcp_cons [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> vald e \<Longrightarrow> tc_pairs \<Gamma> es \<Longrightarrow> tc_pairs (t # \<Gamma>) (e # es)"

primrec multisubst :: "dexpr list \<Rightarrow> dexpr \<Rightarrow> dexpr" where
  "multisubst [] e = e"
| "multisubst (e' # es) e = multisubst es (substd 0 e' e)"

lemma [simp]: "tc_pairs \<Gamma> es \<Longrightarrow> vald e \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> [] \<turnstile>\<^sub>d e : t \<Longrightarrow> 
  tc_pairs (insert_at x t \<Gamma>) (insert_at x e es)"
proof (induction \<Gamma> es arbitrary: x rule: tc_pairs.induct)
  case (tcp_cons t' e' \<Gamma> es)
  then show ?case by (induction x) simp_all
qed simp_all

lemma [simp]: "tc_pairs \<Gamma> es \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> [] \<turnstile>\<^sub>d multisubst es e : t"
proof (induction \<Gamma> es arbitrary: e rule: tc_pairs.induct)
  case (tcp_cons e' t' \<Gamma> es)
  moreover hence "insert_at 0 t' \<Gamma> \<turnstile>\<^sub>d e : t" by (induction \<Gamma>) simp_all
  moreover from tcp_cons have "[] \<turnstile>\<^sub>d e' : t'" by simp
  moreover hence "\<Gamma> \<turnstile>\<^sub>d e' : t'" using tc_postpend by fastforce
  ultimately show ?case by simp
qed simp_all

lemma [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> multisubst es e = e"
  by (induction es) simp_all

lemma multisubst_var [simp]: "lookup vs x = Some v \<Longrightarrow> 
    (\<And>v es. v \<in> set vs \<Longrightarrow> multisubst es v = v) \<Longrightarrow> multisubst vs (DVar x) = v"
  by (induction vs x rule: lookup.induct) simp_all

lemma [simp]: "multisubst es (DConst k) = DConst k"
  by (induction es) simp_all

lemma [simp]: "\<exists>e'. multisubst es (DLam t e) = DLam t e'"
  by (induction es arbitrary: e) simp_all

lemma [simp]: "\<exists>e'. multisubst es (DLam t e) = DLam t e' \<and> 
    (\<forall>e\<^sub>2. (\<forall>ee. substd 0 ee e\<^sub>2 = e\<^sub>2) \<longrightarrow> substd 0 e\<^sub>2 e' = multisubst es (substd 0 e\<^sub>2 e))"
  by (induction es arbitrary: e) simp_all

lemma [simp]: "tc_pairs \<Gamma> es \<Longrightarrow> insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e : t\<^sub>2 \<Longrightarrow> 
  \<exists>e'. multisubst es (DLam t\<^sub>1 e) = DLam t\<^sub>1 e' \<and> ([t\<^sub>1] \<turnstile>\<^sub>d e' : t\<^sub>2) \<and>
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> multisubst (insert_at 0 e\<^sub>2 es) e = substd 0 e\<^sub>2 e')"
proof (induction \<Gamma> es arbitrary: e rule: tc_pairs.induct)
  case (tcp_cons e' t \<Gamma> es)
  hence "[] \<turnstile>\<^sub>d e' : t" by simp
  hence "\<Gamma> \<turnstile>\<^sub>d e' : t" using tc_postpend by fastforce
  hence "insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d incrd 0 e' : t" by simp
  with tcp_cons have "insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d substd (Suc 0) (incrd 0 e') e : t\<^sub>2" 
    by (induction \<Gamma>) simp_all
  with tcp_cons obtain ee' where E: "([t\<^sub>1] \<turnstile>\<^sub>d ee' : t\<^sub>2) \<and> 
    multisubst es (DLam t\<^sub>1 (substd (Suc 0) (incrd 0 e') e)) = DLam t\<^sub>1 ee' \<and> 
      (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> 
        multisubst (insert_at 0 e\<^sub>2 es) (substd (Suc 0) (incrd 0 e') e) = substd 0 e\<^sub>2 ee')" 
    by fastforce
  hence "\<And>e\<^sub>2. [] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1 \<Longrightarrow> 
    multisubst es (substd 0 e\<^sub>2 (substd (Suc 0) (incrd 0 e') e)) = substd 0 e\<^sub>2 ee'" 
      by (induction es) simp_all
  hence "\<And>e\<^sub>2. [] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1 \<Longrightarrow> multisubst es (substd 0 e' (substd 0 e\<^sub>2 e)) = substd 0 e\<^sub>2 ee'"
    by fastforce
  with E show ?case by simp
qed simp_all

lemma [simp]: "multisubst es (DApp e\<^sub>1 e\<^sub>2) = DApp (multisubst es e\<^sub>1) (multisubst es e\<^sub>2)"
  by (induction es arbitrary: e\<^sub>1 e\<^sub>2) simp_all

lemma multisubst_val [simp]: "vald (multisubst es e) \<Longrightarrow> (\<And>e'. e' \<in> set es \<Longrightarrow> vald e') \<Longrightarrow> 
  vald e \<or> (\<exists>x. e = DVar x \<and> x < length es)"
proof (induction es arbitrary: e)
  case (Cons e' es)
  thus ?case
  proof (cases "vald (substd 0 e' e)")
    case True
    with Cons have "vald e \<or> e = DVar 0" by simp
    thus ?thesis by fastforce
  next
    case False
    with Cons obtain x where "substd 0 e' e = DVar x \<and> x < length es" by fastforce
    moreover with Cons have "e = DVar (Suc x)" by fastforce
    ultimately show ?thesis by simp
  qed
qed simp_all

end