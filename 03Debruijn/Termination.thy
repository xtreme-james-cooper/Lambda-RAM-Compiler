theory Termination
  imports Debruijn
begin

abbreviation terminatesd :: "dexpr \<Rightarrow> bool" where
  "terminatesd e \<equiv> (\<exists>e'. vald e' \<and> iter (\<leadsto>\<^sub>d) e e')"

primrec stable :: "ty \<Rightarrow> dexpr \<Rightarrow> bool" where
  "stable Base e = (terminatesd e \<and> [] \<turnstile>\<^sub>d e : Base)"
| "stable (Arrow t\<^sub>1 t\<^sub>2) e = (terminatesd e \<and> ([] \<turnstile>\<^sub>d e : Arrow t\<^sub>1 t\<^sub>2) \<and> 
    (\<forall>e'. stable t\<^sub>1 e' \<longrightarrow> vald e' \<longrightarrow> stable t\<^sub>2 (DApp e e')))"

inductive subst_pairs :: "ty list \<Rightarrow> dexpr list \<Rightarrow> bool" where
  subp_nil [simp]: "subst_pairs [] []"
| subp_cons [simp]: "stable t e \<Longrightarrow> vald e \<Longrightarrow> subst_pairs \<Gamma> es \<Longrightarrow> subst_pairs (t # \<Gamma>) (e # es)"

primrec multisubst :: "dexpr list \<Rightarrow> dexpr \<Rightarrow> dexpr" where
  "multisubst [] e = e"
| "multisubst (e' # es) e = multisubst es (substd 0 e' e)"

lemma [simp]: "stable t e \<Longrightarrow> [] \<turnstile>\<^sub>d e : t"
  by (induction t) simp_all

lemma [simp]: "stable t e \<Longrightarrow> terminatesd e"
  by (induction t) simp_all

lemma [simp]: "subst_pairs \<Gamma> es \<Longrightarrow> stable t e \<Longrightarrow> vald e \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> 
  subst_pairs (insert_at x t \<Gamma>) (insert_at x e es)"
proof (induction \<Gamma> es arbitrary: x rule: subst_pairs.induct)
  case (subp_cons t' e' \<Gamma> es)
  then show ?case by (induction x) simp_all
qed simp_all

lemma [simp]: "subst_pairs \<Gamma> es \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> [] \<turnstile>\<^sub>d multisubst es e : t"
proof (induction \<Gamma> es arbitrary: e rule: subst_pairs.induct)
  case (subp_cons t' e' \<Gamma> es)
  moreover from subp_cons have "insert_at 0 t' \<Gamma> \<turnstile>\<^sub>d e : t" by (induction \<Gamma>) simp_all
  moreover from subp_cons have "[] \<turnstile>\<^sub>d e' : t'" by simp
  moreover hence "\<Gamma> \<turnstile>\<^sub>d e' : t'" using tc_postpend by fastforce
  ultimately show ?case by simp
qed simp_all

lemma [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> multisubst es e = e"
  by (induction es) simp_all

lemma [simp]: "terminatesd (DConst k)"
proof
  show "vald (DConst k) \<and> iter (\<leadsto>\<^sub>d) (DConst k) (DConst k)" by simp
qed

lemma [simp]: "terminatesd (DLam t e)"
proof
  show "vald (DLam t e) \<and> iter (\<leadsto>\<^sub>d) (DLam t e) (DLam t e)" by simp
qed

lemma [simp]: "stable t e \<Longrightarrow> stable t (multisubst es e)"
proof (induction es)
  case (Cons e' es)
  hence "[] \<turnstile>\<^sub>d e : t" by simp
  hence "substd 0 e' e = e" by simp
  with Cons show ?case by simp
qed simp_all

lemma [simp]: "subst_pairs \<Gamma> es \<Longrightarrow> lookup \<Gamma> x = Some t \<Longrightarrow> stable t (multisubst es (DVar x))"
proof (induction \<Gamma> es arbitrary: x rule: subst_pairs.induct)
  case (subp_cons t' e \<Gamma> ves)
  thus ?case by (induction x) simp_all
qed simp_all

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

lemma [simp]: "subst_pairs \<Gamma> es \<Longrightarrow> insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e : t\<^sub>2 \<Longrightarrow> 
  \<exists>e'. multisubst es (DLam t\<^sub>1 e) = DLam t\<^sub>1 e' \<and> ([t\<^sub>1] \<turnstile>\<^sub>d e' : t\<^sub>2) \<and>
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> multisubst (insert_at 0 e\<^sub>2 es) e = substd 0 e\<^sub>2 e')"
proof (induction \<Gamma> es arbitrary: e rule: subst_pairs.induct)
  case (subp_cons t e' \<Gamma> es)
  hence "[] \<turnstile>\<^sub>d e' : t" by simp
  hence "\<Gamma> \<turnstile>\<^sub>d e' : t" using tc_postpend by fastforce
  hence "insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d incrd 0 e' : t" by simp
  with subp_cons have "insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d substd (Suc 0) (incrd 0 e') e : t\<^sub>2" 
    by (induction \<Gamma>) simp_all
  with subp_cons obtain ee' where E: "([t\<^sub>1] \<turnstile>\<^sub>d ee' : t\<^sub>2) \<and> 
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

lemma [simp]: "e \<leadsto>\<^sub>d e' \<Longrightarrow> terminatesd e \<Longrightarrow> terminatesd e'"
proof -
  assume "terminatesd e"
  then obtain v where V: "vald v \<and> iter (\<leadsto>\<^sub>d) e v" by fastforce
  moreover assume "e \<leadsto>\<^sub>d e'"
  ultimately have "vald v \<and> iter (\<leadsto>\<^sub>d) e' v" by (metis evald_backwards)
  thus ?thesis by fastforce
qed

lemma stable_evald: "e \<leadsto>\<^sub>d e' \<Longrightarrow> stable t e \<Longrightarrow> stable t e'"
proof (induction t arbitrary: e e')
  case Base
  then show ?case by simp
next
  case (Arrow t\<^sub>1 t\<^sub>2)
  moreover have "\<And>e\<^sub>2. stable t\<^sub>1 e\<^sub>2 \<Longrightarrow> vald e\<^sub>2 \<Longrightarrow> stable t\<^sub>2 (DApp e' e\<^sub>2)" 
  proof -
    fix e\<^sub>2
    assume "stable t\<^sub>1 e\<^sub>2" and "vald e\<^sub>2"
    with Arrow have X: "stable t\<^sub>2 (DApp e e\<^sub>2)" by simp
    from Arrow have "DApp e e\<^sub>2 \<leadsto>\<^sub>d DApp e' e\<^sub>2" by simp
    with Arrow(2) X show "stable t\<^sub>2 (DApp e' e\<^sub>2)" by simp
  qed 
  ultimately show ?case by simp
qed

lemma stable_persists: "iter (\<leadsto>\<^sub>d) e e' \<Longrightarrow> stable t e \<Longrightarrow> stable t e'"
  by (induction e e' rule: iter.induct) (simp_all add: stable_evald)

lemma stable_evald_back: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> e \<leadsto>\<^sub>d e' \<Longrightarrow> stable t e' \<Longrightarrow> stable t e"
proof (induction t arbitrary: e e')
  case Base
  then show ?case by fastforce
next
  case (Arrow t\<^sub>1 t\<^sub>2)
  from Arrow(5) have "terminatesd e'" by simp
  with Arrow(4) have X: "terminatesd e" by fastforce
  have "\<And>e\<^sub>2. stable t\<^sub>1 e\<^sub>2 \<Longrightarrow> vald e\<^sub>2 \<Longrightarrow> stable t\<^sub>2 (DApp e e\<^sub>2)" 
  proof -
    fix e\<^sub>2
    assume S: "stable t\<^sub>1 e\<^sub>2" and "vald e\<^sub>2"
    with Arrow(5) have Y: "stable t\<^sub>2 (DApp e' e\<^sub>2)" by simp
    from Arrow(3) S have Z: "[] \<turnstile>\<^sub>d DApp e e\<^sub>2 : t\<^sub>2" by simp
    from Arrow(4) have "DApp e e\<^sub>2 \<leadsto>\<^sub>d DApp e' e\<^sub>2" by simp
    with Arrow(2) Y Z show "stable t\<^sub>2 (DApp e e\<^sub>2)" by blast
  qed
  with Arrow(3) X show ?case by simp
qed

lemma stable_persists_back: "iter (\<leadsto>\<^sub>d) e e' \<Longrightarrow> [] \<turnstile>\<^sub>d e : t \<Longrightarrow> stable t e' \<Longrightarrow> stable t e"
proof (induction e e' rule: iter.induct)
  case (iter_step e e' e'')
  thus ?case using stable_evald_back by fastforce
qed simp_all

lemma tc_stable [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> subst_pairs \<Gamma> es \<Longrightarrow> stable t (multisubst es e)"
proof (induction \<Gamma> e t arbitrary: es rule: typecheckd.induct)
  case (tcd_lam t\<^sub>1 \<Gamma> e t\<^sub>2)
  then obtain e' where E: "multisubst es (DLam t\<^sub>1 e) = DLam t\<^sub>1 e' \<and> ([t\<^sub>1] \<turnstile>\<^sub>d e' : t\<^sub>2) \<and> 
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> multisubst (insert_at 0 e\<^sub>2 es) e = substd 0 e\<^sub>2 e')" by fastforce
  moreover have "\<And>e\<^sub>2. stable t\<^sub>1 e\<^sub>2 \<Longrightarrow> vald e\<^sub>2 \<Longrightarrow> stable t\<^sub>2 (DApp (DLam t\<^sub>1 e') e\<^sub>2)"
  proof -
    fix e\<^sub>2
    assume S: "stable t\<^sub>1 e\<^sub>2" and V: "vald e\<^sub>2"
    hence E2: "[] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" by simp
    hence T: "\<exists>t. [] \<turnstile>\<^sub>d e\<^sub>2 : t" by fastforce
    from tcd_lam have "subst_pairs (insert_at 0 t\<^sub>1 \<Gamma>) (insert_at 0 e\<^sub>2 es) \<Longrightarrow> 
      stable t\<^sub>2 (multisubst (insert_at 0 e\<^sub>2 es) e)" by blast
    with tcd_lam S V T E have "stable t\<^sub>2 (substd 0 e\<^sub>2 e')" by simp
    moreover with V have "DApp (DLam t\<^sub>1 e') e\<^sub>2 \<leadsto>\<^sub>d substd 0 e\<^sub>2 e'" by simp
    moreover from E have "[] \<turnstile>\<^sub>d DLam t\<^sub>1 e' : Arrow t\<^sub>1 t\<^sub>2" by simp
    moreover with E2 have "[] \<turnstile>\<^sub>d DApp (DLam t\<^sub>1 e') e\<^sub>2 : t\<^sub>2" by simp
    ultimately show "stable t\<^sub>2 (DApp (DLam t\<^sub>1 e') e\<^sub>2)" by (metis stable_evald_back)
  qed
  ultimately show ?case by simp
next
  case (tcd_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  hence "terminatesd (multisubst es e\<^sub>2)" by fastforce
  then obtain v\<^sub>2 where V2: "vald v\<^sub>2 \<and> iter (\<leadsto>\<^sub>d) (multisubst es e\<^sub>2) v\<^sub>2" by fastforce
  with tcd_app have V2S: "stable t\<^sub>1 v\<^sub>2" by (metis stable_persists)
  from tcd_app have "terminatesd (multisubst es e\<^sub>1)" by fastforce
  then obtain v\<^sub>1 where V1: "vald v\<^sub>1 \<and> iter (\<leadsto>\<^sub>d) (multisubst es e\<^sub>1) v\<^sub>1" by fastforce
  with tcd_app have SV: "stable (Arrow t\<^sub>1 t\<^sub>2) v\<^sub>1" by (metis stable_persists)
  with V2S V2 have "stable t\<^sub>2 (DApp v\<^sub>1 v\<^sub>2)" by simp
  moreover from V1 V2 have "iter (\<leadsto>\<^sub>d) (DApp v\<^sub>1 (multisubst es e\<^sub>2)) (DApp v\<^sub>1 v\<^sub>2)" by simp
  moreover from SV have "[] \<turnstile>\<^sub>d v\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by simp
  moreover with tcd_app have "[] \<turnstile>\<^sub>d DApp v\<^sub>1 (multisubst es e\<^sub>2) : t\<^sub>2" by simp
  ultimately have X: "stable t\<^sub>2 (DApp v\<^sub>1 (multisubst es e\<^sub>2))" by (metis stable_persists_back)
  from V1 have Y: "iter (\<leadsto>\<^sub>d) (DApp (multisubst es e\<^sub>1) (multisubst es e\<^sub>2)) 
    (DApp v\<^sub>1 (multisubst es e\<^sub>2))" by simp
  from tcd_app have "[] \<turnstile>\<^sub>d multisubst es e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by simp
  moreover from tcd_app have "[] \<turnstile>\<^sub>d multisubst es e\<^sub>2 : t\<^sub>1" by simp
  ultimately have "[] \<turnstile>\<^sub>d DApp (multisubst es e\<^sub>1) (multisubst es e\<^sub>2) : t\<^sub>2" by simp
  with X Y have "stable t\<^sub>2 (DApp (multisubst es e\<^sub>1) (multisubst es e\<^sub>2))" 
    by (metis stable_persists_back)
  thus ?case by simp
qed simp_all

theorem tc_terminationd [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> terminatesd e"
proof -
  assume "[] \<turnstile>\<^sub>d e : t" 
  hence "stable t (multisubst [] e)" by (metis subp_nil tc_stable)
  thus ?thesis by simp
qed

end