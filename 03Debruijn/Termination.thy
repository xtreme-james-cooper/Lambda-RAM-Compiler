theory Termination
  imports Multisubst
begin

abbreviation terminatesd :: "dexpr \<Rightarrow> bool" where
  "terminatesd e \<equiv> (\<exists>e'. vald e' \<and> iter (\<leadsto>\<^sub>d) e e')"

primrec stable :: "ty \<Rightarrow> dexpr \<Rightarrow> bool" where
  "stable (TyVar x) e = False" 
| "stable Base e = (terminatesd e \<and> [] \<turnstile>\<^sub>d e : Base)"
| "stable (Arrow t\<^sub>1 t\<^sub>2) e = (terminatesd e \<and> ([] \<turnstile>\<^sub>d e : Arrow t\<^sub>1 t\<^sub>2) \<and> 
    (\<forall>e'. stable t\<^sub>1 e' \<longrightarrow> vald e' \<longrightarrow> stable t\<^sub>2 (DApp e e')))"

lemma stable_typechecks: "stable t e \<Longrightarrow> [] \<turnstile>\<^sub>d e : t"
  by (induction t) simp_all

lemma stable_terminates: "stable t e \<Longrightarrow> terminatesd e"
  by (induction t) simp_all

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
  hence "[] \<turnstile>\<^sub>d e : t" by (metis stable_typechecks)
  hence "substd 0 e' e = e" by simp
  with Cons show ?case by simp
qed simp_all

lemma [simp]: "tc_pairs \<Gamma> es \<Longrightarrow> list_all2 stable \<Gamma> es \<Longrightarrow> lookup \<Gamma> x = Some t \<Longrightarrow> 
  stable t (multisubst es (DVar x))"
proof (induction \<Gamma> es arbitrary: x rule: tc_pairs.induct)
  case (tcp_cons t' e \<Gamma> ves)
  thus ?case by (induction x) simp_all
qed simp_all

lemma [simp]: "e \<leadsto>\<^sub>d e' \<Longrightarrow> terminatesd e = terminatesd e'"
proof 
  assume "terminatesd e"
  then obtain v where V: "vald v \<and> iter (\<leadsto>\<^sub>d) e v" by fastforce
  moreover assume "e \<leadsto>\<^sub>d e'"
  ultimately have "vald v \<and> iter (\<leadsto>\<^sub>d) e' v" by (metis evald_backwards)
  thus "terminatesd e'" by fastforce
next
  assume "terminatesd e'"
  then obtain v where V: "vald v \<and> iter (\<leadsto>\<^sub>d) e' v" by fastforce
  moreover assume "e \<leadsto>\<^sub>d e'"
  ultimately have "vald v \<and> iter (\<leadsto>\<^sub>d) e v" by (metis iter_step)
  thus "terminatesd e" by fastforce
qed

lemma stable_evald: "e \<leadsto>\<^sub>d e' \<Longrightarrow> stable t e \<Longrightarrow> stable t e'"
proof (induction t arbitrary: e e')
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
qed simp_all

lemma stable_persists: "iter (\<leadsto>\<^sub>d) e e' \<Longrightarrow> stable t e \<Longrightarrow> stable t e'"
  by (induction e e' rule: iter.induct) (simp_all add: stable_evald)

lemma stable_evald_back: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> e \<leadsto>\<^sub>d e' \<Longrightarrow> stable t e' \<Longrightarrow> stable t e"
proof (induction t arbitrary: e e')
  case (Arrow t\<^sub>1 t\<^sub>2)
  from Arrow have "terminatesd e'" by simp
  with Arrow have X: "terminatesd e" by fastforce
  have "\<And>e\<^sub>2. stable t\<^sub>1 e\<^sub>2 \<Longrightarrow> vald e\<^sub>2 \<Longrightarrow> stable t\<^sub>2 (DApp e e\<^sub>2)" 
  proof -
    fix e\<^sub>2
    assume S: "stable t\<^sub>1 e\<^sub>2" and "vald e\<^sub>2"
    with Arrow have Y: "stable t\<^sub>2 (DApp e' e\<^sub>2)" by simp
    from S have "[] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1"  by (metis stable_typechecks)
    with Arrow(3) have Z: "[] \<turnstile>\<^sub>d DApp e e\<^sub>2 : t\<^sub>2" by simp
    from Arrow have "DApp e e\<^sub>2 \<leadsto>\<^sub>d DApp e' e\<^sub>2" by simp
    with Arrow Y Z show "stable t\<^sub>2 (DApp e e\<^sub>2)" by blast
  qed
  with Arrow X show ?case by simp
qed simp_all

lemma stable_persists_back: "iter (\<leadsto>\<^sub>d) e e' \<Longrightarrow> [] \<turnstile>\<^sub>d e : t \<Longrightarrow> stable t e' \<Longrightarrow> stable t e"
proof (induction e e' rule: iter.induct)
  case (iter_step e e' e'')
  thus ?case using stable_evald_back by fastforce
qed simp_all

lemma tc_stable [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> tc_pairs \<Gamma> es \<Longrightarrow> list_all2 stable \<Gamma> es \<Longrightarrow> 
  stable t (multisubst es e)"
proof (induction \<Gamma> e t arbitrary: es rule: typecheckd.induct)
  case (tcd_lam t\<^sub>1 \<Gamma> e t\<^sub>2)
  then obtain e' where E: "multisubst es (DLam t\<^sub>1 e) = DLam t\<^sub>1 e' \<and> ([t\<^sub>1] \<turnstile>\<^sub>d e' : t\<^sub>2) \<and> 
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> multisubst (insert_at 0 e\<^sub>2 es) e = substd 0 e\<^sub>2 e')" by fastforce
  moreover have "\<And>e\<^sub>2. stable t\<^sub>1 e\<^sub>2 \<Longrightarrow> vald e\<^sub>2 \<Longrightarrow> stable t\<^sub>2 (DApp (DLam t\<^sub>1 e') e\<^sub>2)"
  proof -
    fix e\<^sub>2
    assume S: "stable t\<^sub>1 e\<^sub>2" and V: "vald e\<^sub>2"
    hence E2: "[] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" by (metis stable_typechecks)
    hence T: "\<exists>t. [] \<turnstile>\<^sub>d e\<^sub>2 : t" by fastforce
    from tcd_lam S have "list_all2 stable (insert_at 0 t\<^sub>1 \<Gamma>) (insert_at 0 e\<^sub>2 es)" by simp
    with tcd_lam have "tc_pairs (insert_at 0 t\<^sub>1 \<Gamma>) (insert_at 0 e\<^sub>2 es) \<Longrightarrow> 
      stable t\<^sub>2 (multisubst (insert_at 0 e\<^sub>2 es) e)" by blast
    with tcd_lam S V T E have "stable t\<^sub>2 (substd 0 e\<^sub>2 e')" by (simp add: stable_typechecks)
    moreover with V have "DApp (DLam t\<^sub>1 e') e\<^sub>2 \<leadsto>\<^sub>d substd 0 e\<^sub>2 e'" by simp
    moreover from E have "[] \<turnstile>\<^sub>d DLam t\<^sub>1 e' : Arrow t\<^sub>1 t\<^sub>2" by simp
    moreover with E2 have "[] \<turnstile>\<^sub>d DApp (DLam t\<^sub>1 e') e\<^sub>2 : t\<^sub>2" by simp
    ultimately show "stable t\<^sub>2 (DApp (DLam t\<^sub>1 e') e\<^sub>2)" by (metis stable_evald_back)
  qed
  ultimately show ?case by simp
next
  case (tcd_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  hence "terminatesd (multisubst es e\<^sub>2)" by (metis stable_terminates)
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
  moreover have "list_all2 stable [] []" by simp
  ultimately show ?thesis by (metis stable_terminates multisubst.simps(1) tcp_nil tc_stable)
qed

end