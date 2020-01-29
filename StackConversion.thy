theory StackConversion
  imports Stack
begin

fun unwind' :: "frame list \<Rightarrow> dexpr \<Rightarrow> dexpr" where
  "unwind' [] e = e"
| "unwind' (FApp1 e\<^sub>2 # s) e = unwind' s (DApp e e\<^sub>2)"
| "unwind' (FApp2 e\<^sub>1 # s) e = unwind' s (DApp e\<^sub>1 e)"
| "unwind' (FReturn # s) e = unwind' s e"

primrec unwind :: "stack_state \<Rightarrow> dexpr" where
  "unwind (SS s e) = unwind' s e"

lemma [simp]: "s : t' \<rightarrow> t \<Longrightarrow> [] \<turnstile>\<^sub>d e : t' \<Longrightarrow> [] \<turnstile>\<^sub>d unwind' s e : t"
  by (induction s t' t arbitrary: e rule: typecheck_stack.induct) simp_all

theorem typesafed [simp]: "\<Sigma> :\<^sub>s t \<Longrightarrow> [] \<turnstile>\<^sub>d unwind \<Sigma> : t"
  by (induction \<Sigma> t rule: typecheck_stack_state.induct) simp_all

lemma [simp]: "s : t' \<rightarrow> t \<Longrightarrow> e \<leadsto>\<^sub>d e' \<Longrightarrow> unwind' s e \<leadsto>\<^sub>d unwind' s e'"
  by (induction s t' t arbitrary: e e' rule: typecheck_stack.induct) simp_all

theorem correctd: "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>s t \<Longrightarrow> iter (\<leadsto>\<^sub>d) (unwind \<Sigma>) (unwind \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: evals.induct)
  case (evs_app3 e\<^sub>2 t\<^sub>1 e\<^sub>1 s)
  then obtain t\<^sub>2 where "s : t\<^sub>2 \<rightarrow> t" by blast
  moreover from evs_app3 have "DApp (DLam t\<^sub>1 e\<^sub>1) e\<^sub>2 \<leadsto>\<^sub>d substd 0 e\<^sub>2 e\<^sub>1" by simp
  ultimately have "unwind' s (DApp (DLam t\<^sub>1 e\<^sub>1) e\<^sub>2) \<leadsto>\<^sub>d unwind' s (substd 0 e\<^sub>2 e\<^sub>1)" by simp
  thus ?case by simp
qed simp_all

primrec all_returns :: "frame list \<Rightarrow> bool" where
  "all_returns [] = True"
| "all_returns (r # rs) = (r = FReturn \<and> all_returns rs)"

lemma unwind_returns [elim]: "all_returns sr \<Longrightarrow> unwind' sr e = e"
  by (induction sr) (simp_all add: all_returns_def)

lemma [dest]: "FApp1 e # sr : t' \<rightarrow> t \<Longrightarrow> all_returns sr \<Longrightarrow> 
    (\<And>t\<^sub>1. t' = Arrow t\<^sub>1 t \<Longrightarrow> [] \<turnstile>\<^sub>d e : t\<^sub>1 \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction sr) fastforce+

lemma [dest]: "FApp2 e # sr : t' \<rightarrow> t \<Longrightarrow> all_returns sr \<Longrightarrow> 
    ([] \<turnstile>\<^sub>d e : Arrow t' t \<Longrightarrow> vald e \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction sr) fastforce+

lemma [dest]: "sr @ s : t' \<rightarrow> t \<Longrightarrow> all_returns sr \<Longrightarrow> (s : t' \<rightarrow> t \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction sr) fastforce+

lemma [dest]: "DApp e\<^sub>1 e\<^sub>2 = unwind' s e \<Longrightarrow> (all_returns s \<and> e = DApp e\<^sub>1 e\<^sub>2) \<or> 
  (\<exists>s' sr. all_returns sr \<and> ((s = s' @ FApp1 e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e) \<or> 
    (s = s' @ FApp2 e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e)))"
proof (induction s e rule: unwind'.induct)
  case (2 e\<^sub>2' s e)
  thus ?case
  proof (cases "all_returns s \<and> DApp e e\<^sub>2' = DApp e\<^sub>1 e\<^sub>2")
    case False
    with 2 obtain s' sr where S: "all_returns sr \<and> ((s = s' @ FApp1 e\<^sub>2 # sr \<and> 
      e\<^sub>1 = unwind' s' (DApp e e\<^sub>2')) \<or> (s = s' @ FApp2 e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' (DApp e e\<^sub>2')))" 
        by fastforce
    thus ?thesis
    proof (cases "s = s' @ FApp1 e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' (DApp e e\<^sub>2')")
      case False
      with S have "all_returns sr \<and> s = s' @ FApp2 e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' (DApp e e\<^sub>2')" by simp
      moreover hence "FApp1 e\<^sub>2' # s' @ FApp2 e\<^sub>1 # sr = (FApp1 e\<^sub>2' # s') @ FApp2 e\<^sub>1 # sr \<and> 
        unwind' s' (DApp e e\<^sub>2') = unwind' (FApp1 e\<^sub>2' # s') e" by simp
      ultimately show ?thesis by blast
    qed fastforce+
  qed fastforce+
next
  case (3 e\<^sub>1' s e)
  thus ?case
  proof (cases "all_returns s \<and> DApp e\<^sub>1' e = DApp e\<^sub>1 e\<^sub>2")
    case False
    with 3 obtain s' sr where S: "all_returns sr \<and> ((s = s' @ FApp1 e\<^sub>2 # sr \<and> 
      e\<^sub>1 = unwind' s' (DApp e\<^sub>1' e)) \<or> (s = s' @ FApp2 e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' (DApp e\<^sub>1' e)))" 
        by fastforce
    thus ?thesis
    proof (cases "s = s' @ FApp1 e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' (DApp e\<^sub>1' e)")
      case False
      with S have "all_returns sr \<and> s = s' @ FApp2 e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' (DApp e\<^sub>1' e)" by simp
      moreover hence "FApp2 e\<^sub>1' # s' @ FApp2 e\<^sub>1 # sr = (FApp2 e\<^sub>1' # s') @ FApp2 e\<^sub>1 # sr \<and> 
        e\<^sub>2 = unwind' (FApp2 e\<^sub>1' # s') e" by simp
      ultimately show ?thesis by blast
    qed fastforce+
  qed fastforce+
next
  case (4 s e)
  thus ?case
  proof (cases "all_returns s \<and> e = DApp e\<^sub>1 e\<^sub>2")
    case False
    with 4 obtain s' sr where S: "all_returns sr \<and> ((s = s' @ FApp1 e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e) \<or> 
      (s = s' @ FApp2 e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e))" by fastforce
    thus ?thesis
    proof (cases "s = s' @ FApp1 e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e")
      case False
      with S have "all_returns sr \<and> s = s' @ FApp2 e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e" by simp
      moreover hence "FReturn # s' @ FApp2 e\<^sub>1 # sr = (FReturn # s') @ FApp2 e\<^sub>1 # sr \<and> 
        e\<^sub>2 = unwind' (FReturn # s') e" by simp
      ultimately show ?thesis by blast
    qed fastforce+
  qed fastforce+
qed simp_all

lemma [simp]: "vald v \<Longrightarrow> v = unwind' s e \<Longrightarrow> all_returns s \<and> e = v"
  by (induction s e rule: unwind'.induct) simp_all

lemma [simp]: "vald v \<Longrightarrow> v = unwind \<Sigma> \<Longrightarrow> \<exists>s. \<Sigma> = SS s v \<and> all_returns s"
  by (induction \<Sigma>) simp_all

lemma [simp]: "all_returns sr \<Longrightarrow> unwind' (s @ FApp1 e\<^sub>2 # sr) e = DApp (unwind' s e) e\<^sub>2"
  by (induction s e rule: unwind'.induct) auto

lemma [simp]: "all_returns sr \<Longrightarrow> unwind' (s @ FApp2 e\<^sub>1 # sr) e = DApp e\<^sub>1 (unwind' s e)"
  by (induction s e rule: unwind'.induct) auto

lemma eval_returns [simp]: "all_returns sr \<Longrightarrow> vald v \<Longrightarrow> iter (\<leadsto>\<^sub>s) (SS (sr @ s) v) (SS s v)"
proof (induction sr)
  case (Cons a sr)
  hence "iter (\<leadsto>\<^sub>s) (SS (sr @ s) v) (SS s v)" by simp
  moreover from Cons have "SS (FReturn # sr @ s) v \<leadsto>\<^sub>s SS (sr @ s) v" by simp
  ultimately have "iter (\<leadsto>\<^sub>s) (SS (FReturn # sr @ s) v) (SS s v)" by simp
  with Cons show ?case by simp
qed simp_all

lemma [simp]: "unwind' s e \<leadsto>\<^sub>d e' \<Longrightarrow> s : t' \<rightarrow> t \<Longrightarrow> [] \<turnstile>\<^sub>d e : tt \<Longrightarrow> 
  \<exists>s' e''. iter (\<leadsto>\<^sub>s) (SS s e) (SS s' e'') \<and> e' = unwind' s' e''"
proof (induction "unwind' s e" e' arbitrary: s e t tt rule: evald.induct)
  case (evd_app1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
  thus ?case
  proof (cases "all_returns s \<and> e = DApp e\<^sub>1 e\<^sub>2")
    case True
    with evd_app1 True obtain t\<^sub>1 where T1: "([] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 tt) \<and> ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1)" by blast
    have "[] : t' \<rightarrow> t'" by simp
    with evd_app1 T1 obtain s' e'' where E: "iter (\<leadsto>\<^sub>s) (SS [] e\<^sub>1) (SS s' e'') \<and> 
      e\<^sub>1' = unwind' s' e''" by fastforce
    hence "iter (\<leadsto>\<^sub>s) (SS ([] @ FApp1 e\<^sub>2 # s) e\<^sub>1) (SS (s' @ FApp1 e\<^sub>2 # s) e'')" by (metis eval_under)
    hence "iter (\<leadsto>\<^sub>s) (SS (FApp1 e\<^sub>2 # s) e\<^sub>1) (SS (s' @ FApp1 e\<^sub>2 # s) e'')" by simp
    hence "iter (\<leadsto>\<^sub>s) (SS s (DApp e\<^sub>1 e\<^sub>2)) (SS (s' @ FApp1 e\<^sub>2 # s) e'')" by (metis evs_app1 iter_step)
    with True E show ?thesis by fastforce
  next
    case False
    with evd_app1 obtain s' sr where S: "all_returns sr \<and> 
      ((s = s' @ FApp1 e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e) \<or> 
        (s = s' @ FApp2 e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e))" by fast
    thus ?thesis
    proof (cases "s = s' @ FApp1 e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e")
      case True
      with evd_app1 obtain t'' where "(s' : t' \<rightarrow> t'') \<and> (FApp1 e\<^sub>2 # sr : t'' \<rightarrow> t)" by fastforce
      with evd_app1 True obtain ss' e'' where S': "iter (\<leadsto>\<^sub>s) (SS s' e) (SS ss' e'') \<and> 
        e\<^sub>1' = unwind' ss' e''" by blast
      hence X: "iter (\<leadsto>\<^sub>s) (SS (s' @ FApp1 e\<^sub>2 # sr) e) (SS (ss' @ FApp1 e\<^sub>2 # sr) e'')" by simp
      from S S' have "DApp e\<^sub>1' e\<^sub>2 = unwind' (ss' @ FApp1 e\<^sub>2 # sr) e''" by simp
      with True X show ?thesis by blast
    next
      case False
      with S have "s = s' @ FApp2 e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e" by simp
      with evd_app1 obtain t\<^sub>1 where "(s' : t' \<rightarrow> t\<^sub>1) \<and> (FApp2 e\<^sub>1 # sr : t\<^sub>1 \<rightarrow> t)" by fastforce
      with S have "([] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t) \<and> vald e\<^sub>1" by fastforce
      with evd_app1 show ?thesis by (metis val_no_evald)
    qed
  qed
next
  case (evd_app2 e\<^sub>1 e\<^sub>2 e\<^sub>2')
  thus ?case
  proof (cases "all_returns s \<and> e = DApp e\<^sub>1 e\<^sub>2")
    case True
    with evd_app2 obtain t\<^sub>1 where T: "([] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 tt) \<and> ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1)" by blast
    from evd_app2 T obtain s' e'' where E: "iter (\<leadsto>\<^sub>s) (SS [] e\<^sub>2) (SS s' e'') \<and> 
      e\<^sub>2' = unwind' s' e''" by (metis unwind'.simps(1) tcs_nil)
    hence "iter (\<leadsto>\<^sub>s) (SS (FApp2 e\<^sub>1 # s) e\<^sub>2) (SS (s' @ FApp2 e\<^sub>1 # s) e'')" 
      by (metis eval_under append_Nil)
    moreover have "SS s (DApp e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>s SS (FApp1 e\<^sub>2 # s) e\<^sub>1" by simp
    moreover from evd_app2 have "SS (FApp1 e\<^sub>2 # s) e\<^sub>1 \<leadsto>\<^sub>s SS (FApp2 e\<^sub>1 # s) e\<^sub>2" by simp
    ultimately have "iter (\<leadsto>\<^sub>s) (SS s (DApp e\<^sub>1 e\<^sub>2)) (SS (s' @ FApp2 e\<^sub>1 # s) e'')" 
      by (metis iter_step)
    with True E show ?thesis by fastforce
  next
    case False
    with evd_app2 obtain s' sr where S: "all_returns sr \<and> 
      ((s = s' @ FApp1 e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e) \<or> 
        (s = s' @ FApp2 e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e))" by blast
    thus ?thesis
    proof (cases "s = s' @ FApp1 e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e")
      case True
      with evd_app2 have S': "all_returns s' \<and> e = e\<^sub>1" by simp 
      with evd_app2 True S obtain t\<^sub>1 where T: "t' = Arrow t\<^sub>1 t \<and> [] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" by blast
      have X: "e\<^sub>2 = unwind' [] e\<^sub>2" by simp
      have "[] : t' \<rightarrow> t'" by simp
      with evd_app2 T X obtain s'' e'' where E: "iter (\<leadsto>\<^sub>s) (SS [] e\<^sub>2) (SS s'' e'') \<and> 
        e\<^sub>2' = unwind' s'' e''" by blast
      hence "iter (\<leadsto>\<^sub>s) (SS (FApp2 e\<^sub>1 # sr) e\<^sub>2) (SS (s'' @ FApp2 e\<^sub>1 # sr) e'')" 
        using eval_under by fastforce
      moreover from evd_app2 have "SS (FApp1 e\<^sub>2 # sr) e\<^sub>1 \<leadsto>\<^sub>s SS (FApp2 e\<^sub>1 # sr) e\<^sub>2" by simp
      moreover from evd_app2 S' have "iter (\<leadsto>\<^sub>s) (SS (s' @ FApp1 e\<^sub>2 # sr) e\<^sub>1) (SS (FApp1 e\<^sub>2 # sr) e\<^sub>1)" 
        by simp
      ultimately have Y: "iter (\<leadsto>\<^sub>s) (SS (s' @ FApp1 e\<^sub>2 # sr) e\<^sub>1) (SS (s'' @ FApp2 e\<^sub>1 # sr) e'')" 
        by (metis iter_step iter_append)
      from S E have "DApp e\<^sub>1 e\<^sub>2' = unwind' (s'' @ FApp2 e\<^sub>1 # sr) e''" by simp
      with True S' Y show ?thesis by metis
    next
      case False
      with S have S': "s = s' @ FApp2 e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e" by simp
      with evd_app2 obtain t\<^sub>1 where "(s' : t' \<rightarrow> t\<^sub>1) \<and> (FApp2 e\<^sub>1 # sr : t\<^sub>1 \<rightarrow> t)" by fastforce
      with evd_app2 S' obtain s'' e'' where E: "iter (\<leadsto>\<^sub>s) (SS s' e) (SS s'' e'') \<and> 
        e\<^sub>2' = unwind' s'' e''" by blast
      hence "iter (\<leadsto>\<^sub>s) (SS (s' @ FApp2 e\<^sub>1 # sr) e) (SS (s'' @ FApp2 e\<^sub>1 # sr) e'')" by simp
      with S S' E show ?thesis by fastforce
    qed
  qed
next
  case (evd_app3 e\<^sub>2 t\<^sub>1 e\<^sub>1)
  thus ?case
  proof (cases "all_returns s \<and> e = DApp (DLam t\<^sub>1 e\<^sub>1) e\<^sub>2")
    case True
    have "SS s (DApp (DLam t\<^sub>1 e\<^sub>1) e\<^sub>2) \<leadsto>\<^sub>s SS (FApp1 e\<^sub>2 # s) (DLam t\<^sub>1 e\<^sub>1)" by simp
    moreover have "SS (FApp1 e\<^sub>2 # s) (DLam t\<^sub>1 e\<^sub>1) \<leadsto>\<^sub>s SS (FApp2 (DLam t\<^sub>1 e\<^sub>1) # s) e\<^sub>2" by simp
    moreover from evd_app3 have "SS (FApp2 (DLam t\<^sub>1 e\<^sub>1) # s) e\<^sub>2 \<leadsto>\<^sub>s SS (FReturn # s) (substd 0 e\<^sub>2 e\<^sub>1)" 
      by simp
    ultimately have X: "iter (\<leadsto>\<^sub>s) (SS s (DApp (DLam t\<^sub>1 e\<^sub>1) e\<^sub>2)) (SS (FReturn # s) (substd 0 e\<^sub>2 e\<^sub>1))" 
      by (metis iter_step iter_refl)
    from True have "substd 0 e\<^sub>2 e\<^sub>1 = unwind' (FReturn # s) (substd 0 e\<^sub>2 e\<^sub>1)"
      using unwind_returns by simp
    with True X show ?thesis by fastforce
  next
    case False
    with evd_app3 obtain s' sr where S: "all_returns sr \<and> 
      ((s = s' @ FApp1 e\<^sub>2 # sr \<and> DLam t\<^sub>1 e\<^sub>1 = unwind' s' e) \<or> 
        (s = s' @ FApp2 (DLam t\<^sub>1 e\<^sub>1) # sr \<and> e\<^sub>2 = unwind' s' e))" by blast
    thus ?thesis
    proof (cases "s = s' @ FApp1 e\<^sub>2 # sr \<and> DLam t\<^sub>1 e\<^sub>1 = unwind' s' e")
      case True
      moreover have "vald (DLam t\<^sub>1 e\<^sub>1)" by simp
      ultimately have S': "all_returns s' \<and> e = DLam t\<^sub>1 e\<^sub>1" by simp
      have "SS (FApp1 e\<^sub>2 # sr) (DLam t\<^sub>1 e\<^sub>1) \<leadsto>\<^sub>s SS (FApp2 (DLam t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2" by simp
      moreover from evd_app3 have "SS (FApp2 (DLam t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2 \<leadsto>\<^sub>s 
        SS (FReturn # sr) (substd 0 e\<^sub>2 e\<^sub>1)" by simp
      moreover from S' have "iter (\<leadsto>\<^sub>s) (SS (s' @ FApp1 e\<^sub>2 # sr) (DLam t\<^sub>1 e\<^sub>1)) 
        (SS (FApp1 e\<^sub>2 # sr) (DLam t\<^sub>1 e\<^sub>1))" by simp
      ultimately have X: "iter (\<leadsto>\<^sub>s) (SS (s' @ FApp1 e\<^sub>2 # sr) (DLam t\<^sub>1 e\<^sub>1)) 
        (SS (FReturn # sr) (substd 0 e\<^sub>2 e\<^sub>1))" by (metis iter_step iter_refl iter_append)
      from S True have "substd 0 e\<^sub>2 e\<^sub>1 = unwind' (FReturn # sr) (substd 0 e\<^sub>2 e\<^sub>1)" 
        using unwind_returns by simp
      with True S' X show ?thesis by fastforce
    next
      case False
      with S evd_app3 have S': "all_returns s' \<and> e = e\<^sub>2" by simp
      from evd_app3 have "SS (FApp2 (DLam t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2 \<leadsto>\<^sub>s SS (FReturn # sr) (substd 0 e\<^sub>2 e\<^sub>1)" 
        by simp
      hence "iter (\<leadsto>\<^sub>s) (SS (FApp2 (DLam t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2) (SS (FReturn # sr) (substd 0 e\<^sub>2 e\<^sub>1))" 
        by (metis iter_step iter_refl)
      moreover from evd_app3 S' have "iter (\<leadsto>\<^sub>s) (SS (s' @ FApp2 (DLam t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2) 
        (SS (FApp2 (DLam t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2)" by simp
      ultimately have X: "iter (\<leadsto>\<^sub>s) (SS (s' @ FApp2 (DLam t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2) 
        (SS (FReturn # sr) (substd 0 e\<^sub>2 e\<^sub>1))" by (metis iter_append)
      from S have "substd 0 e\<^sub>2 e\<^sub>1 = unwind' (FReturn # sr) (substd 0 e\<^sub>2 e\<^sub>1)" 
        using unwind_returns by simp
      with S False S' X show ?thesis by metis
    qed
  qed
qed

theorem completed [simp]: "\<Sigma> :\<^sub>s t \<Longrightarrow> unwind \<Sigma> \<leadsto>\<^sub>d e' \<Longrightarrow> \<exists>\<Sigma>'. iter (\<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<and> e' = unwind \<Sigma>'"
proof (induction \<Sigma> t rule: typecheck_stack_state.induct)
  case (tcs_state s t' t e)
  then obtain s' e'' where "iter (\<leadsto>\<^sub>s) (SS s e) (SS s' e'') \<and> e' = unwind' s' e''" by fastforce
  thus ?case by fastforce
qed

lemma [simp]: "iter (\<leadsto>\<^sub>d) (unwind \<Sigma>) e' \<Longrightarrow> \<Sigma> :\<^sub>s t \<Longrightarrow> \<exists>\<Sigma>'. iter (\<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<and> e' = unwind \<Sigma>'"
proof (induction "unwind \<Sigma>" e' arbitrary: \<Sigma> rule: iter.induct)
  case (iter_step e' e'')
  moreover then obtain \<Sigma>' where S: "iter (\<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<and> e' = unwind \<Sigma>'" by fastforce
  moreover with iter_step have "\<Sigma>' :\<^sub>s t" by fastforce
  ultimately obtain \<Sigma>'' where "iter (\<leadsto>\<^sub>s) \<Sigma>' \<Sigma>'' \<and> e'' = unwind \<Sigma>''" by fastforce
  with S have "iter (\<leadsto>\<^sub>s) \<Sigma> \<Sigma>'' \<and> e'' = unwind \<Sigma>''" by (metis iter_append)
  then show ?case by fastforce
qed force+

lemma [simp]: "iter (\<leadsto>\<^sub>d) e v \<Longrightarrow> [] \<turnstile>\<^sub>d e : t \<Longrightarrow> vald v \<Longrightarrow> iter (\<leadsto>\<^sub>s) (SS [FReturn] e) (SS [] v)"
proof -
  assume "[] \<turnstile>\<^sub>d e : t"
  hence "SS [FReturn] e :\<^sub>s t" by (metis tcs_nil tcs_cons_ret tcs_state)
  moreover assume "iter (\<leadsto>\<^sub>d) e v"
  ultimately obtain \<Sigma>' where S: "iter (\<leadsto>\<^sub>s) (SS [FReturn] e) \<Sigma>' \<and> v = unwind \<Sigma>'" by fastforce
  moreover assume V: "vald v"
  ultimately obtain sr where "\<Sigma>' = SS (sr @ []) v \<and> all_returns sr" by fastforce
  moreover with V have "iter (\<leadsto>\<^sub>s) \<Sigma>' (SS [] v)" by (metis eval_returns)
  with S show "iter (\<leadsto>\<^sub>s) (SS [FReturn] e) (SS [] v)" by (metis iter_append)
qed

end