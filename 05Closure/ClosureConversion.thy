theory ClosureConversion
  imports Closure "../04Stack/Stack" "../03Debruijn/Multisubst"
begin

primrec declosure :: "closure \<Rightarrow> dexpr" where
  "declosure (CConst k) = DConst k"
| "declosure (CLam t cs e) = multisubst (map declosure cs) (DLam t e)"

fun declosure_stack :: "cframe list \<Rightarrow> frame list" where
  "declosure_stack [] = []"
| "declosure_stack (CApp1 cs e # s) = FApp1 (multisubst (map declosure cs) e) # declosure_stack s"
| "declosure_stack (CApp2 c # s) = FApp2 (declosure c) # declosure_stack s"
| "declosure_stack (CReturn cs # s) = FReturn # declosure_stack s"

primrec declosure_state :: "closure_state \<Rightarrow> stack_state" where
  "declosure_state (CSE s cs e) = SS (declosure_stack s) (multisubst (map declosure cs) e)"
| "declosure_state (CSC s c) = SS (declosure_stack s) (declosure c)"

lemma [simp]: "vald (declosure c)"
proof (induction c)
  case (CLam t cs e)
  thus ?case by (induction cs arbitrary: e) simp_all
qed simp_all

lemma [simp]: "c :\<^sub>c\<^sub>l t \<Longrightarrow> [] \<turnstile>\<^sub>d declosure c : t"
  and [simp]: "cs :\<^sub>c\<^sub>l\<^sub>s ts \<Longrightarrow> subst_pairs ts (map declosure cs)" 
proof (induction c t and cs ts rule: typecheck_closure_typecheck_closure_list.inducts)
  case (tcc_lam cs ts t\<^sub>1 e t\<^sub>2)
  then obtain e' where "multisubst (map declosure cs) (DLam t\<^sub>1 e) = DLam t\<^sub>1 e' \<and> ([t\<^sub>1] \<turnstile>\<^sub>d e' : t\<^sub>2) \<and> 
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> multisubst (insert_at 0 e\<^sub>2 (map declosure cs)) e = substd 0 e\<^sub>2 e')" 
      by fastforce
  thus ?case by simp
qed simp_all

lemma [simp]: "s :\<^sub>c t' \<rightarrow> t \<Longrightarrow> declosure_stack s : t' \<rightarrow> t"
proof (induction s t' t rule: typecheck_cstack.induct)
  case (tcc_scons_app1 cs ts e t\<^sub>1 s t\<^sub>2 t)
  hence "subst_pairs ts (map declosure cs)" by simp
  moreover from tcc_scons_app1 have "ts \<turnstile>\<^sub>d e : t\<^sub>1" by simp
  ultimately have "[] \<turnstile>\<^sub>d multisubst (map declosure cs) e : t\<^sub>1" by simp
  with tcc_scons_app1 show ?case by simp
next
  case (tcc_scons_app2 c t\<^sub>1 t\<^sub>2 s t)
  hence "[] \<turnstile>\<^sub>d declosure c : Arrow t\<^sub>1 t\<^sub>2" by simp
  moreover from tcc_scons_app2 have "declosure_stack s : t\<^sub>2 \<rightarrow> t" by simp
  ultimately show ?case by simp
qed simp_all
  
theorem typesafec [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> declosure_state \<Sigma> :\<^sub>s t"
proof (induction \<Sigma> t rule: typecheck_closure_state.induct)
  case (tcc_state_ev s t' t cs ts e)
  hence "subst_pairs ts (map declosure cs)" by simp
  moreover from tcc_state_ev have "ts \<turnstile>\<^sub>d e : t'" by simp
  ultimately have "[] \<turnstile>\<^sub>d multisubst (map declosure cs) e : t'" by simp
  moreover from tcc_state_ev have "declosure_stack s : t' \<rightarrow> t" by simp
  ultimately show ?case by simp
next
  case (tcc_state_ret s t' t c)
  hence "declosure_stack s : t' \<rightarrow> t" by simp
  moreover from tcc_state_ret have "[] \<turnstile>\<^sub>d declosure c : t'" by simp
  ultimately show ?case by simp
qed

lemma multisubst_closure [simp]: "c :\<^sub>c\<^sub>l t \<Longrightarrow> multisubst es (declosure c) = declosure c"
  and [simp]: "cs :\<^sub>c\<^sub>l\<^sub>s ts \<Longrightarrow> v \<in> set (map declosure cs) \<Longrightarrow> multisubst es v = v"
proof (induction c t and cs ts rule: typecheck_closure_typecheck_closure_list.inducts)
  case (tcc_lam cs ts t\<^sub>1 e t\<^sub>2)
  moreover hence "subst_pairs ts (map declosure cs)" by simp
  ultimately obtain e' where E: "multisubst (map declosure cs) (DLam t\<^sub>1 e) = DLam t\<^sub>1 e' \<and> 
    ([t\<^sub>1] \<turnstile>\<^sub>d e' : t\<^sub>2) \<and> (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> 
      multisubst (insert_at 0 e\<^sub>2 (map declosure cs)) e = substd 0 e\<^sub>2 e')" by fastforce
  hence "[] \<turnstile>\<^sub>d DLam t\<^sub>1 e' : Arrow t\<^sub>1 t\<^sub>2" by simp
  hence "multisubst es (DLam t\<^sub>1 e') = DLam t\<^sub>1 e'" by simp
  with E show ?case by simp
qed auto

lemma [simp]: "c :\<^sub>c\<^sub>l t \<Longrightarrow> substd 0 e' (declosure c) = declosure c"
proof -
  assume "c :\<^sub>c\<^sub>l t"
  hence "multisubst [e'] (declosure c) = declosure c" by (metis multisubst_closure)
  thus ?thesis by simp
qed

theorem correctc: "\<Sigma> \<leadsto>\<^sub>c \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow> iter (\<leadsto>\<^sub>s) (declosure_state \<Sigma>) (declosure_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: evalc.induct)
  case (evc_var cs x c s)
  then obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> lookup ts x = Some t'" by fastforce
  hence "\<And>v es. v \<in> set (map declosure cs) \<Longrightarrow> multisubst es v = v" by auto
  moreover from evc_var have "lookup (map declosure cs) x = Some (declosure c)" by simp
  ultimately have "multisubst (map declosure cs) (DVar x) = declosure c" by (metis multisubst_var)
  thus ?case by simp
next
  case (evc_app s cs e\<^sub>1 e\<^sub>2)
  have "SS (declosure_stack s) (DApp (multisubst (map declosure cs) e\<^sub>1) 
    (multisubst (map declosure cs) e\<^sub>2)) \<leadsto>\<^sub>s 
      SS (FApp1 (multisubst (map declosure cs) e\<^sub>2) # declosure_stack s) 
        (multisubst (map declosure cs) e\<^sub>1)" by simp
  hence "iter (\<leadsto>\<^sub>s) (SS (declosure_stack s) (DApp (multisubst (map declosure cs) e\<^sub>1) 
    (multisubst (map declosure cs) e\<^sub>2))) 
      (SS (FApp1 (multisubst (map declosure cs) e\<^sub>2) # declosure_stack s) 
        (multisubst (map declosure cs) e\<^sub>1))" by (metis iter_step iter_refl)
  thus ?case by simp
next
  case (retc_app1 cs e\<^sub>2 s c\<^sub>1)
  have "SS (FApp1 (multisubst (map declosure cs) e\<^sub>2) # declosure_stack s) (declosure c\<^sub>1) \<leadsto>\<^sub>s
    SS (FApp2 (declosure c\<^sub>1) # declosure_stack s) (multisubst (map declosure cs) e\<^sub>2)" by simp
  hence "iter (\<leadsto>\<^sub>s) (SS (FApp1 (multisubst (map declosure cs) e\<^sub>2) # declosure_stack s) 
    (declosure c\<^sub>1)) 
      (SS (FApp2 (declosure c\<^sub>1) # declosure_stack s) (multisubst (map declosure cs) e\<^sub>2))" 
        by (metis iter_step iter_refl)
  thus ?case by simp
next
  case (retc_app2 t\<^sub>1 cs e\<^sub>1 s c\<^sub>2)
  then obtain ts t\<^sub>2 where T: "(cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (insert_at 0 t\<^sub>1 ts \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2) \<and> (s :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> 
    (c\<^sub>2 :\<^sub>c\<^sub>l t\<^sub>1)" by fastforce
  hence "subst_pairs ts (map declosure cs) \<and> insert_at 0 t\<^sub>1 ts \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2" by simp
  then obtain e' where "multisubst (map declosure cs) (DLam t\<^sub>1 e\<^sub>1) = DLam t\<^sub>1 e' \<and> ([t\<^sub>1] \<turnstile>\<^sub>d e' : t\<^sub>2) \<and>
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> multisubst (insert_at 0 e\<^sub>2 (map declosure cs)) e\<^sub>1 = substd 0 e\<^sub>2 e')" 
      by fastforce
  with T have "multisubst (map declosure cs) (DLam t\<^sub>1 e\<^sub>1) = DLam t\<^sub>1 e' \<and> 
    multisubst (insert_at 0 (declosure c\<^sub>2) (map declosure cs)) e\<^sub>1 = substd 0 (declosure c\<^sub>2) e'" 
      by simp
  hence "SS (FApp2 (multisubst (map declosure cs) (DLam t\<^sub>1 e\<^sub>1)) # declosure_stack s) (declosure c\<^sub>2) 
    \<leadsto>\<^sub>s (SS (FReturn # declosure_stack s) 
      (multisubst (map declosure cs) (substd 0 (declosure c\<^sub>2) e\<^sub>1)))" 
    by (induction cs) simp_all
  hence "iter (\<leadsto>\<^sub>s) (SS (FApp2 (multisubst (map declosure cs) (DLam t\<^sub>1 e\<^sub>1)) # declosure_stack s) 
    (declosure c\<^sub>2)) 
      (SS (FReturn # declosure_stack s) 
        (multisubst (map declosure cs) (substd 0 (declosure c\<^sub>2) e\<^sub>1)))" 
    by (metis iter_step iter_refl)
  thus ?case by simp
next
  case (retc_ret cs s c)
  have "SS (FReturn # declosure_stack s) (declosure c) \<leadsto>\<^sub>s SS (declosure_stack s) (declosure c)" 
    by simp
  hence "iter (\<leadsto>\<^sub>s) (SS (FReturn # declosure_stack s) (declosure c)) 
    (SS (declosure_stack s) (declosure c))" by (metis iter_step iter_refl)
  thus ?case by simp
qed simp_all

lemma [simp]: "[] = declosure_stack s \<Longrightarrow> s = []"
  by (induction s rule: declosure_stack.induct) simp_all

lemma [simp]: "FApp1 e # s = declosure_stack s\<^sub>c \<Longrightarrow> \<exists>cs e' s\<^sub>c'. s\<^sub>c = CApp1 cs e' # s\<^sub>c' \<and> 
    e = multisubst (map declosure cs) e' \<and> s = declosure_stack s\<^sub>c'"
  by (induction s\<^sub>c rule: declosure_stack.induct) simp_all

lemma [simp]: "FApp2 e # s = declosure_stack s\<^sub>c \<Longrightarrow> 
    \<exists>c s\<^sub>c'. s\<^sub>c = CApp2 c # s\<^sub>c' \<and> e = declosure c \<and> s = declosure_stack s\<^sub>c'"
  by (induction s\<^sub>c rule: declosure_stack.induct) simp_all

lemma [simp]: "FReturn # s = declosure_stack s\<^sub>c \<Longrightarrow> \<exists>cs s\<^sub>c'. s\<^sub>c = CReturn cs # s\<^sub>c'"
  by (induction s\<^sub>c rule: declosure_stack.induct) simp_all

lemma [simp]: "SS s e = declosure_state \<Sigma> \<Longrightarrow> 
  \<exists>s'. s = declosure_stack s' \<and> ((\<exists>cs e'. \<Sigma> = CSE s' cs e' \<and> e = multisubst (map declosure cs) e') \<or> 
    (\<exists>c. \<Sigma> = CSC s' c \<and> e = declosure c))"
  by (induction \<Sigma>) simp_all

lemma [dest]: "DApp e\<^sub>1 e\<^sub>2 = multisubst (map declosure cs) (DLam t e) \<Longrightarrow> False"
proof -
  assume "DApp e\<^sub>1 e\<^sub>2 = multisubst (map declosure cs) (DLam t e)"
  moreover obtain e' where "multisubst (map declosure cs) (DLam t e) = DLam t e'" by fastforce
  ultimately show ?thesis by simp
qed

lemma [simp]: "DLam t e = declosure c \<Longrightarrow> 
  \<exists>cs e'. c = CLam t cs e' \<and> (\<forall>e\<^sub>2. (\<forall>ee. substd 0 ee e\<^sub>2 = e\<^sub>2) \<longrightarrow> 
    substd 0 e\<^sub>2 e = multisubst (map declosure cs) (substd 0 e\<^sub>2 e'))"
proof (induction c)
  case (CLam tt cs e')
  moreover obtain ee' where "multisubst (map declosure cs) (DLam tt e') = DLam tt ee' \<and> 
    (\<forall>e\<^sub>2. (\<forall>ee. substd 0 ee e\<^sub>2 = e\<^sub>2) \<longrightarrow> 
      substd 0 e\<^sub>2 ee' = multisubst (map declosure cs) (substd 0 e\<^sub>2 e'))" by fastforce
  ultimately show ?case by simp
qed simp_all

lemma [dest]: "DApp e\<^sub>1 e\<^sub>2 = declosure c \<Longrightarrow> False"
  by (induction c) auto

lemma [dest]: "DApp e\<^sub>1 e\<^sub>2 = multisubst (map declosure cs) (declosure c) \<Longrightarrow> False"
proof (induction c)
  case (CLam t cs' e)
  moreover obtain e' where "multisubst (map declosure cs') (DLam t e) = DLam t e'" by fastforce
  ultimately show ?case by auto
qed simp_all 

lemma [dest]: "DApp e\<^sub>1 e\<^sub>2 = multisubst (map declosure cs) (DVar x) \<Longrightarrow> False"
  by (induction cs x rule: lookup.induct) auto

lemma [simp]: "DApp e\<^sub>1 e\<^sub>2 = multisubst (map declosure cs) e \<Longrightarrow> \<exists>e\<^sub>1' e\<^sub>2'. e = DApp e\<^sub>1' e\<^sub>2' \<and>
    e\<^sub>1 = multisubst (map declosure cs) e\<^sub>1' \<and> e\<^sub>2 = multisubst (map declosure cs) e\<^sub>2'"
  by (induction e) auto

lemma [simp]: "lookup cs x = Some c \<Longrightarrow> c :\<^sub>c\<^sub>l t \<Longrightarrow> 
    multisubst (map declosure cs) (DVar x) = declosure c"
  by (induction cs x rule: lookup.induct) simp_all

lemma [simp]: "vald (multisubst (map declosure cs) e) \<Longrightarrow> CSE s cs e :\<^sub>c t \<Longrightarrow>
  \<exists>c. CSE s cs e \<leadsto>\<^sub>c CSC s c \<and> multisubst (map declosure cs) e = declosure c"
proof (induction e)
  case (DVar x)
  then obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (lookup ts x = Some t')" by fastforce
  then obtain c where "lookup cs x = Some c \<and> c :\<^sub>c\<^sub>l t'" by fastforce
  hence "CSE s cs (DVar x) \<leadsto>\<^sub>c CSC s c \<and> multisubst (map declosure cs) (DVar x) = declosure c" 
    by fastforce
  thus ?case by blast
next
  case (DConst k)
  have "CSE s cs (DConst k) \<leadsto>\<^sub>c CSC s (CConst k) \<and> 
    multisubst (map declosure cs) (DConst k) = declosure (CConst k)" by simp
  thus ?case by blast
next
  case (DLam tt e)
  hence "CSE s cs (DLam tt e) \<leadsto>\<^sub>c CSC s (CLam tt cs e) \<and> 
    multisubst (map declosure cs) (DLam tt e) = declosure (CLam tt cs e)" by simp
  thus ?case by blast
qed simp_all

theorem completec [simp]: "declosure_state \<Sigma>\<^sub>c \<leadsto>\<^sub>s \<Sigma>\<^sub>s' \<Longrightarrow> \<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>c'. iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> \<Sigma>\<^sub>s' = declosure_state \<Sigma>\<^sub>c'"
proof (induction "declosure_state \<Sigma>\<^sub>c" \<Sigma>\<^sub>s' rule: evals.induct)
  case (evs_app1 s e\<^sub>1 e\<^sub>2)
  then obtain s' where S: "s = declosure_stack s' \<and> 
    ((\<exists>cs e'. \<Sigma>\<^sub>c = CSE s' cs e' \<and> DApp e\<^sub>1 e\<^sub>2 = multisubst (map declosure cs) e') \<or> 
      (\<exists>c. \<Sigma>\<^sub>c = CSC s' c \<and> DApp e\<^sub>1 e\<^sub>2 = declosure c))" by fastforce
  thus ?case 
  proof (cases "\<exists>cs e'. \<Sigma>\<^sub>c = CSE s' cs e' \<and> DApp e\<^sub>1 e\<^sub>2 = multisubst (map declosure cs) e'")
    case True
    then obtain cs e\<^sub>1' e\<^sub>2' where E: "\<Sigma>\<^sub>c = CSE s' cs (DApp e\<^sub>1' e\<^sub>2') \<and>
      e\<^sub>1 = multisubst (map declosure cs) e\<^sub>1' \<and> e\<^sub>2 = multisubst (map declosure cs) e\<^sub>2'" by fastforce                                                  
    have "CSE s' cs (DApp e\<^sub>1' e\<^sub>2') \<leadsto>\<^sub>c CSE (CApp1 cs e\<^sub>2' # s') cs e\<^sub>1'" by simp
    hence "iter (\<leadsto>\<^sub>c) (CSE s' cs (DApp e\<^sub>1' e\<^sub>2')) (CSE (CApp1 cs e\<^sub>2' # s') cs e\<^sub>1')" 
      by (metis iter_refl iter_step)
    with S E show ?thesis by fastforce
  qed fastforce+
next
  case (evs_app2 e\<^sub>1 e\<^sub>2 s)
  then obtain s\<^sub>c where S: "FApp1 e\<^sub>2 # s = declosure_stack s\<^sub>c \<and> 
    ((\<exists>cs e'. \<Sigma>\<^sub>c = CSE s\<^sub>c cs e' \<and> e\<^sub>1 = multisubst (map declosure cs) e') \<or> 
      (\<exists>c. \<Sigma>\<^sub>c = CSC s\<^sub>c c \<and> e\<^sub>1 = declosure c))" by fastforce
  then obtain cs' e\<^sub>2' s\<^sub>c' where S': "s\<^sub>c = CApp1 cs' e\<^sub>2' # s\<^sub>c' \<and> 
    e\<^sub>2 = multisubst (map declosure cs') e\<^sub>2' \<and> s = declosure_stack s\<^sub>c'" by fastforce
  thus ?case
  proof (cases "\<exists>cs e'. \<Sigma>\<^sub>c = CSE s\<^sub>c cs e' \<and> e\<^sub>1 = multisubst (map declosure cs) e'")
    case True
    with S' obtain cs e' where E: "\<Sigma>\<^sub>c = CSE (CApp1 cs' e\<^sub>2' # s\<^sub>c') cs e' \<and>
      e\<^sub>1 = multisubst (map declosure cs) e'" by fastforce
    with evs_app2 obtain c where C: "
      CSE (CApp1 cs' e\<^sub>2' # s\<^sub>c') cs e' \<leadsto>\<^sub>c CSC (CApp1 cs' e\<^sub>2' # s\<^sub>c') c \<and> 
        multisubst (map declosure cs) e' = declosure c" by fastforce
    moreover have "CSC (CApp1 cs' e\<^sub>2' # s\<^sub>c') c \<leadsto>\<^sub>c CSE (CApp2 c # s\<^sub>c') cs' e\<^sub>2'" by simp
    ultimately have X: "iter (\<leadsto>\<^sub>c) (CSE (CApp1 cs' e\<^sub>2' # s\<^sub>c') cs e') (CSE (CApp2 c # s\<^sub>c') cs' e\<^sub>2')"
      by (metis iter_refl iter_step)
    from E C S' have "SS (FApp2 e\<^sub>1 # s) e\<^sub>2 = declosure_state (CSE (CApp2 c # s\<^sub>c') cs' e\<^sub>2')" by simp
    with E X show ?thesis by blast
  next
    case False
    with S S' obtain c where C: "\<Sigma>\<^sub>c = CSC (CApp1 cs' e\<^sub>2' # s\<^sub>c') c \<and> e\<^sub>1 = declosure c" by fastforce
    have "CSC (CApp1 cs' e\<^sub>2' # s\<^sub>c') c \<leadsto>\<^sub>c CSE (CApp2 c # s\<^sub>c') cs' e\<^sub>2'" by simp
    hence "iter (\<leadsto>\<^sub>c) (CSC (CApp1 cs' e\<^sub>2' # s\<^sub>c') c) (CSE (CApp2 c # s\<^sub>c') cs' e\<^sub>2')" 
      by (metis iter_refl iter_step)
    with C S' show ?thesis by fastforce
  qed
next
  case (evs_app3 e\<^sub>2 t\<^sub>1 e\<^sub>1 s)
  then obtain s\<^sub>c where S: "FApp2 (DLam t\<^sub>1 e\<^sub>1) # s = declosure_stack s\<^sub>c \<and> 
    ((\<exists>cs e'. \<Sigma>\<^sub>c = CSE s\<^sub>c cs e' \<and> e\<^sub>2 = multisubst (map declosure cs) e') \<or> 
      (\<exists>c. \<Sigma>\<^sub>c = CSC s\<^sub>c c \<and> e\<^sub>2 = declosure c))" by fastforce
  then obtain c s\<^sub>c' where S': "s\<^sub>c = CApp2 c # s\<^sub>c' \<and> DLam t\<^sub>1 e\<^sub>1 = declosure c \<and> 
    s = declosure_stack s\<^sub>c'" by fastforce
  then obtain cs' e\<^sub>1' where C: "c = CLam t\<^sub>1 cs' e\<^sub>1' \<and> (\<forall>e\<^sub>2. (\<forall>ee. substd 0 ee e\<^sub>2 = e\<^sub>2) \<longrightarrow> 
    substd 0 e\<^sub>2 e\<^sub>1 = multisubst (map declosure cs') (substd 0 e\<^sub>2 e\<^sub>1'))" by fastforce
  thus ?case
  proof (cases "(\<exists>cs e'. \<Sigma>\<^sub>c = CSE s\<^sub>c cs e' \<and> e\<^sub>2 = multisubst (map declosure cs) e')")
    case True
    with S' obtain cs e' where E: "\<Sigma>\<^sub>c = CSE (CApp2 c # s\<^sub>c') cs e' \<and> 
      e\<^sub>2 = multisubst (map declosure cs) e'" by fastforce
    with evs_app3 obtain c' where C': "CSE (CApp2 c # s\<^sub>c') cs e' \<leadsto>\<^sub>c CSC (CApp2 c # s\<^sub>c') c' \<and> 
      multisubst (map declosure cs) e' = declosure c'" by fastforce
    with E have E2: "e\<^sub>2 = declosure c'" by simp
    have "CSC (CApp2 (CLam t\<^sub>1 cs' e\<^sub>1') # s\<^sub>c') c' \<leadsto>\<^sub>c CSE (CReturn (c' # cs') # s\<^sub>c') (c' # cs') e\<^sub>1'"
      by simp
    with C C' have X: "iter (\<leadsto>\<^sub>c) (CSE (CApp2 c # s\<^sub>c') cs e') 
      (CSE (CReturn (c' # cs') # s\<^sub>c') (c' # cs') e\<^sub>1')" by (metis iter_step iter_refl)
    from evs_app3 E C' have "CSC (CApp2 c # s\<^sub>c') c' :\<^sub>c t" by (metis preservationc)
    then obtain t' where "((CApp2 c # s\<^sub>c') :\<^sub>c t' \<rightarrow> t) \<and> (c' :\<^sub>c\<^sub>l t')" by fastforce
    with E2 have "\<forall>ee. substd 0 ee e\<^sub>2 = e\<^sub>2" by auto
    with C S' E C' have "SS (FReturn # s) (substd 0 e\<^sub>2 e\<^sub>1) = 
      declosure_state (CSE (CReturn (c' # cs') # s\<^sub>c') (c' # cs') e\<^sub>1')" by simp
    with E X show ?thesis by blast
  next
    case False
    with S S' C obtain c\<^sub>2 where E: "\<Sigma>\<^sub>c = CSC (CApp2 (CLam t\<^sub>1 cs' e\<^sub>1') # s\<^sub>c') c\<^sub>2 \<and> e\<^sub>2 = declosure c\<^sub>2" 
      by fastforce
    have X: "CSC (CApp2 (CLam t\<^sub>1 cs' e\<^sub>1') # s\<^sub>c') c\<^sub>2 \<leadsto>\<^sub>c CSE (CReturn (c\<^sub>2 # cs') # s\<^sub>c') (c\<^sub>2 # cs') e\<^sub>1'"
      by simp
    with evs_app3 E have "CSE (CReturn (c\<^sub>2 # cs') # s\<^sub>c') (c\<^sub>2 # cs') e\<^sub>1' :\<^sub>c t" by (metis preservationc)
    then obtain t' ts where "(s\<^sub>c' :\<^sub>c t' \<rightarrow> t) \<and> (c\<^sub>2 # cs' :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (ts \<turnstile>\<^sub>d e\<^sub>1' : t')" by fastforce
    with E have "\<forall>ee. substd 0 ee e\<^sub>2 = e\<^sub>2" by auto
    with S' C E have "SS (FReturn # s) (substd 0 e\<^sub>2 e\<^sub>1) = 
      declosure_state (CSE (CReturn (c\<^sub>2 # cs') # s\<^sub>c') (c\<^sub>2 # cs') e\<^sub>1')" by simp
    with E X show ?thesis by (metis iter_step iter_refl)
  qed
next
  case (evs_ret e s)
  then obtain s\<^sub>c where S: "FReturn # s = declosure_stack s\<^sub>c \<and> 
    ((\<exists>cs e'. \<Sigma>\<^sub>c = CSE s\<^sub>c cs e' \<and> e = multisubst (map declosure cs) e') \<or> 
      (\<exists>c. \<Sigma>\<^sub>c = CSC s\<^sub>c c \<and> e = declosure c))" by fastforce
  then obtain cs s\<^sub>c' where S': "s\<^sub>c = CReturn cs # s\<^sub>c'" by fastforce
  thus ?case
  proof (cases "(\<exists>cs' e'. \<Sigma>\<^sub>c = CSE (CReturn cs # s\<^sub>c') cs' e' \<and> 
      e = multisubst (map declosure cs') e')")
    case True
    then obtain cs' e' where C: "\<Sigma>\<^sub>c = CSE (CReturn cs # s\<^sub>c') cs' e' \<and> 
      e = multisubst (map declosure cs') e'" by fastforce
    with evs_ret obtain c where C': "CSE (CReturn cs # s\<^sub>c') cs' e' \<leadsto>\<^sub>c CSC (CReturn cs # s\<^sub>c') c \<and> 
      multisubst (map declosure cs') e' = declosure c" by fastforce
    moreover have "CSC (CReturn cs # s\<^sub>c') c \<leadsto>\<^sub>c CSC s\<^sub>c' c" by simp
    ultimately have "iter (\<leadsto>\<^sub>c) (CSE (CReturn cs # s\<^sub>c') cs' e') (CSC s\<^sub>c' c)" 
      by (metis iter_refl iter_step)
    with S S' C C' have "iter (\<leadsto>\<^sub>c) (CSE (CReturn cs # s\<^sub>c') cs' e') (CSC s\<^sub>c' c) \<and> 
      SS s e = declosure_state (CSC s\<^sub>c' c)" by simp
    with C show ?thesis by fastforce
  next
    case False
    with S S' obtain c where C: "\<Sigma>\<^sub>c = CSC (CReturn cs # s\<^sub>c') c \<and> e = declosure c" by fastforce
    have "CSC (CReturn cs # s\<^sub>c') c \<leadsto>\<^sub>c CSC s\<^sub>c' c" by simp
    hence "iter (\<leadsto>\<^sub>c) (CSC (CReturn cs # s\<^sub>c') c) (CSC s\<^sub>c' c)" by (metis iter_refl iter_step)
    with S S' C show ?thesis by fastforce
  qed
qed

lemma [simp]: "iter (\<leadsto>\<^sub>s) (declosure_state \<Sigma>\<^sub>c) \<Sigma>\<^sub>s' \<Longrightarrow> \<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>c'. iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> \<Sigma>\<^sub>s' = declosure_state \<Sigma>\<^sub>c'"
proof (induction "declosure_state \<Sigma>\<^sub>c" \<Sigma>\<^sub>s' arbitrary: \<Sigma>\<^sub>c rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>s' \<Sigma>\<^sub>s'')
  moreover then obtain \<Sigma>\<^sub>c' where X: "iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> \<Sigma>\<^sub>s' = declosure_state \<Sigma>\<^sub>c'" by fastforce
  moreover with iter_step have "\<Sigma>\<^sub>c' :\<^sub>c t" by fastforce
  ultimately obtain \<Sigma>\<^sub>c'' where "iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c' \<Sigma>\<^sub>c'' \<and> \<Sigma>\<^sub>s'' = declosure_state \<Sigma>\<^sub>c''" by fastforce
  with X have "iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c'' \<and> \<Sigma>\<^sub>s'' = declosure_state \<Sigma>\<^sub>c''" by (metis iter_append)
  thus ?case by fastforce
qed force+

lemma [simp]: "vald (multisubst (map declosure cs) e) \<Longrightarrow> \<exists>c. CSE s cs e \<leadsto>\<^sub>c CSC s c" 
proof (induction e)
  case (DVar x)
  then obtain c where "lookup cs x = Some c" by (induction cs x rule: lookup.induct) simp_all
  hence "CSE s cs (DVar x) \<leadsto>\<^sub>c CSC s c" by simp
  thus ?case by fastforce
next
  case (DConst k)
  have "CSE s cs (DConst k) \<leadsto>\<^sub>c CSC s (CConst k)" by simp
  thus ?case by fastforce
next
  case (DLam t e)
  have "CSE s cs (DLam t e) \<leadsto>\<^sub>c CSC s (CLam t cs e)" by simp
  thus ?case by fastforce
qed simp_all

lemma [simp]: "\<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow> iter (\<leadsto>\<^sub>s) (declosure_state \<Sigma>\<^sub>c) (SS [] v) \<Longrightarrow> 
  vald v \<Longrightarrow> \<exists>c. iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c (CSC [] c) \<and> declosure c = v"
proof -
  assume VD: "vald v" and TC: "\<Sigma>\<^sub>c :\<^sub>c t" and "iter (\<leadsto>\<^sub>s) (declosure_state \<Sigma>\<^sub>c) (SS [] v)"
  then obtain \<Sigma>\<^sub>c' where E: "iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> SS [] v = declosure_state \<Sigma>\<^sub>c'" by fastforce
  then obtain s' where "[] = declosure_stack s' \<and> 
    ((\<exists>cs e. \<Sigma>\<^sub>c' = CSE s' cs e \<and> v = multisubst (map declosure cs) e) \<or> 
      (\<exists>c. \<Sigma>\<^sub>c' = CSC s' c \<and> v = declosure c))" by fastforce
  moreover hence "s' = []" by simp
  ultimately have S: "(\<exists>cs e. \<Sigma>\<^sub>c' = CSE [] cs e \<and> v = multisubst (map declosure cs) e) \<or> 
    (\<exists>c. \<Sigma>\<^sub>c' = CSC [] c \<and> v = declosure c)" by simp
  with E show ?thesis 
  proof (cases "\<exists>c. \<Sigma>\<^sub>c' = CSC [] c \<and> v = declosure c")
    case False
    with S obtain cs e where V: "\<Sigma>\<^sub>c' = CSE [] cs e \<and> v = multisubst (map declosure cs) e" 
      by fastforce
    with E TC have "CSE [] cs e :\<^sub>c t" by simp
    with V VD obtain c where "CSE [] cs e \<leadsto>\<^sub>c CSC [] c \<and> v = declosure c" by fastforce
    with E V have "iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c (CSC [] c) \<and> declosure c = v" by simp
    thus ?thesis by fastforce
  qed fastforce+
qed

end