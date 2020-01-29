theory TreeCodeConversion
  imports TreeCode Closure
begin

primrec compile' :: "dexpr \<Rightarrow> tree_code list \<Rightarrow> tree_code list" where
  "compile' (DVar x) cd = TLookup x # cd"
| "compile' (DConst k) cd = TPushCon k # cd"
| "compile' (DLam t e) cd = TPushLam (compile' e [TReturn]) # cd"
| "compile' (DApp e\<^sub>1 e\<^sub>2) cd = compile' e\<^sub>1 (compile' e\<^sub>2 (TApply # cd))"

abbreviation compile :: "dexpr \<Rightarrow> tree_code list" where
  "compile e \<equiv> compile' e [TReturn]"

primrec compile_closure :: "closure \<Rightarrow> tclosure" where
  "compile_closure (CConst k) = TConst k"
| "compile_closure (CLam t cs e) = TLam (map compile_closure cs) (compile e)"

fun vals_from_stack :: "cframe list \<Rightarrow> tclosure list" where
  "vals_from_stack [] = []"
| "vals_from_stack (CApp1 cs e # s) = vals_from_stack s"
| "vals_from_stack (CApp2 c # s) = compile_closure c # vals_from_stack s"
| "vals_from_stack (CReturn cs # s) = vals_from_stack s"

fun envs_from_stack :: "cframe list \<Rightarrow> tclosure list list" where
  "envs_from_stack [] = []"
| "envs_from_stack (CApp1 cs e # s) = envs_from_stack s"
| "envs_from_stack (CApp2 c # s) = envs_from_stack s"
| "envs_from_stack (CReturn cs # s) = map compile_closure cs # envs_from_stack s"

fun code_from_stack :: "cframe list \<Rightarrow> tree_code list" where
  "code_from_stack [] = []"
| "code_from_stack (CApp1 cs e # s) = compile' e (TApply # code_from_stack s)"
| "code_from_stack (CApp2 c # s) = TApply # code_from_stack s"
| "code_from_stack (CReturn cs # s) = TReturn # code_from_stack s"

primrec compile_state :: "closure_state \<Rightarrow> tree_code_state" where
  "compile_state (CSE s cs e) = 
    TS (vals_from_stack s) (envs_from_stack s) (compile' e (code_from_stack s))"
| "compile_state (CSC s c) = 
    TS (compile_closure c # vals_from_stack s) (envs_from_stack s) (code_from_stack s)"

primrec unzip :: "dexpr \<Rightarrow> dexpr \<times> dexpr list" where
  "unzip (DVar x) = (DVar x, [])"
| "unzip (DConst k) = (DConst k, [])"
| "unzip (DLam t e) = (DLam t e, [])"
| "unzip (DApp e\<^sub>1 e\<^sub>2) = (case unzip e\<^sub>1 of (e, es) \<Rightarrow> (e, e\<^sub>2 # es))"

primrec zipcompile :: "dexpr list \<Rightarrow> tree_code list \<Rightarrow> tree_code list" where 
  "zipcompile [] acc = acc"
| "zipcompile (e # es) acc = zipcompile es (compile' e (TApply # acc))"

lemma [simp]: "compile' e cd @ cd' = compile' e (cd @ cd')"
  by (induction e arbitrary: cd) simp_all

lemma [simp]: "unzip e = (e', es) \<Longrightarrow> compile' e' (zipcompile es acc) = compile' e acc"
  by (induction e arbitrary: e' es acc) (auto split: prod.splits)

lemma [simp]: "vals_from_stack (map (CApp1 cs) (rev es) @ s) = vals_from_stack s"
  by (induction es arbitrary: s) simp_all

lemma [simp]: "envs_from_stack (map (CApp1 cs) (rev es) @ s) = envs_from_stack s"
  by (induction es arbitrary: s) simp_all

lemma [simp]: "code_from_stack (map (CApp1 cs) (rev es) @ s) = zipcompile es (code_from_stack s)"
  by (induction es arbitrary: s) simp_all

lemma [dest]: "compile' e cd' = TLookup x # cd \<Longrightarrow> 
    (\<And>es. unzip e = (DVar x, es) \<Longrightarrow> cd = zipcompile es cd' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction e arbitrary: cd') fastforce+

lemma [dest]: "compile' e cd' = TPushCon k # cd \<Longrightarrow> 
    (\<And>es. unzip e = (DConst k, es) \<Longrightarrow> cd = zipcompile es cd' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction e arbitrary: cd') fastforce+

lemma compile_to_pushlam' [dest]: "compile' e cd' = TPushLam cd'' # cd \<Longrightarrow> 
  (\<And>es t e'. unzip e = (DLam t e', es) \<Longrightarrow> cd'' = compile e' \<Longrightarrow> 
    cd = zipcompile es cd' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction e arbitrary: cd') fastforce+

lemma [dest]: "compile' e cd' = TApply # cd \<Longrightarrow> P"
  by (induction e arbitrary: cd') simp_all

lemma [dest]: "compile' e cd' = TReturn # cd \<Longrightarrow> P"
  by (induction e arbitrary: cd') simp_all

lemma [dest]: "compile' e cd' = TJump # cd \<Longrightarrow> P"
  by (induction e arbitrary: cd') simp_all

lemma [dest]: "compile_closure c = TConst k \<Longrightarrow> c = CConst k"
  by (induction c) simp_all

lemma compile_lam_closure [dest]: "compile_closure c = TLam env cd \<Longrightarrow> (\<And>t cs e. 
    c = CLam t cs e \<Longrightarrow> env = map compile_closure cs \<Longrightarrow> cd = compile e \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction c) simp_all

lemma tc_latest_environment [simp]: "s @ CApp1 cs e # s' :\<^sub>c t \<rightarrow> t' \<Longrightarrow> 
  latest_environment s' = Some cs"
proof (induction s arbitrary: t)
  case (Cons f s)
  moreover from Cons(2) obtain tt where "s @ CApp1 cs e # s' :\<^sub>c tt \<rightarrow> t'" 
    by (induction "(f # s) @ CApp1 cs e # s'" t t' rule: typecheck_cstack.induct) simp_all
  ultimately show ?case by simp
qed fastforce+

lemma compile_stack_to_lookup [dest]: "code_from_stack s = TLookup x # cd \<Longrightarrow> 
  \<exists>cs e es s'. s = CApp1 cs e # s' \<and> unzip e = (DVar x, es) \<and> 
    cd = zipcompile es (TApply # code_from_stack s')"
  by (induction s rule: code_from_stack.induct) auto

lemma compile_stack_to_pushcon [dest]: "code_from_stack s = TPushCon k # cd \<Longrightarrow> 
  \<exists>cs e es s'. s = CApp1 cs e # s' \<and> unzip e = (DConst k, es) \<and>
    cd = zipcompile es (TApply # code_from_stack s')"
  by (induction s rule: code_from_stack.induct) auto

lemma compile_stack_to_pushlam [dest]: "code_from_stack s = TPushLam cd' # cd \<Longrightarrow> 
  \<exists>cs e es s' t e'. s = CApp1 cs e # s' \<and> unzip e = (DLam t e', es) \<and>
    cd = zipcompile es (TApply # code_from_stack s') \<and> cd' = compile e'"
proof (induction s rule: code_from_stack.induct)
  case (2 cs e s)
  hence "compile' e (TApply # code_from_stack s) = TPushLam cd' # cd" by auto
  moreover then obtain es t e' where "unzip e = (DLam t e', es) \<and> cd' = compile e' \<and> 
    cd = zipcompile es (TApply # code_from_stack s)" by blast
  ultimately show ?case by simp
qed simp_all

lemma compile_stack_to_apply [dest]: "code_from_stack s = TApply # cd \<Longrightarrow> 
    \<exists>s' c. s = CApp2 c # s' \<and> cd = code_from_stack s'"
  by (induction s rule: code_from_stack.induct) auto

lemma compile_stack_to_return [dest]: "code_from_stack s = TReturn # cd \<Longrightarrow> 
    \<exists>cs s'. s = CReturn cs # s' \<and> cd = code_from_stack s'"
  by (induction s rule: code_from_stack.induct) auto
 
lemma compile_stack_to_jump [dest]: "code_from_stack s = TJump # cd \<Longrightarrow> False"
  by (induction s rule: code_from_stack.induct) auto

lemma compile_to_lookup [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> compile_state \<Sigma> = TS vs envs (TLookup x # cd) \<Longrightarrow> 
  (\<exists>s cs e es. \<Sigma> = CSE s cs e \<and> unzip e = (DVar x, es) \<and> cd = zipcompile es (code_from_stack s) \<and>
    vs = vals_from_stack s \<and> envs = envs_from_stack s) \<or> (\<exists>s c cs e es. 
      \<Sigma> = CSC (CApp1 cs e # s) c \<and> unzip e = (DVar x, es) \<and> envs = envs_from_stack s \<and>
        cd = zipcompile es (TApply # code_from_stack s) \<and> 
          vs = compile_closure c # vals_from_stack s)"
  by (induction \<Sigma> t rule: typecheck_closure_state.induct) auto

lemma compile_to_pushcon [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> compile_state \<Sigma> = TS vs envs (TPushCon k # cd) \<Longrightarrow> 
  (\<exists>s cs e es. \<Sigma> = CSE s cs e \<and> unzip e = (DConst k, es) \<and> cd = zipcompile es (code_from_stack s) \<and>
    vs = vals_from_stack s \<and> envs = envs_from_stack s) \<or> (\<exists>s c cs e es. 
      \<Sigma> = CSC (CApp1 cs e # s) c \<and> unzip e = (DConst k, es) \<and> envs = envs_from_stack s \<and>
        cd = zipcompile es (TApply # code_from_stack s) \<and> 
          vs = compile_closure c # vals_from_stack s)"
  by (induction \<Sigma> t rule: typecheck_closure_state.induct) auto

lemma compile_to_pushlam [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> compile_state \<Sigma> = TS vs envs (TPushLam cd' # cd) \<Longrightarrow> 
  (\<exists>s cs e es tt e'. \<Sigma> = CSE s cs e \<and> unzip e = (DLam tt e', es) \<and> 
    cd = zipcompile es (code_from_stack s) \<and> cd' = compile e' \<and> vs = vals_from_stack s \<and> 
      envs = envs_from_stack s) \<or> (\<exists>s c cs e es tt e'. \<Sigma> = CSC (CApp1 cs e # s) c \<and> 
        unzip e = (DLam tt e', es) \<and> cd = zipcompile es (TApply # code_from_stack s) \<and> 
          cd' = compile e' \<and> vs = compile_closure c # vals_from_stack s \<and> 
            envs = envs_from_stack s)"
proof (induction \<Sigma> t rule: typecheck_closure_state.induct)
  case (tcc_state_ev s t' t cs ts e)
  hence "compile' e (code_from_stack s) = TPushLam cd' # cd" by simp
  then obtain es tt e' where "unzip e = (DLam tt e', es) \<and> cd' = compile e'  \<and> 
    cd = zipcompile es (code_from_stack s)" by (metis compile_to_pushlam')
  with tcc_state_ev show ?case by fastforce
next
  case (tcc_state_ret s t' t c)
  moreover then obtain cs e es s' tt e' where "s = CApp1 cs e # s' \<and> unzip e = (DLam tt e', es) \<and>
    cd = zipcompile es (TApply # code_from_stack s') \<and> cd' = compile e'" 
      using compile_stack_to_pushlam by auto
  ultimately show ?case by fastforce
qed

lemma compile_to_apply [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> compile_state \<Sigma> = TS vs envs (TApply # cd) \<Longrightarrow> 
  \<exists>s c c'. \<Sigma> = CSC (CApp2 c' # s) c \<and> cd = code_from_stack s \<and> envs = envs_from_stack s \<and> 
    vs = compile_closure c # compile_closure c' # vals_from_stack s"
  by (induction \<Sigma> t rule: typecheck_closure_state.induct) auto

lemma compile_to_return [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> compile_state \<Sigma> = TS vs envs (TReturn # cd) \<Longrightarrow> 
  \<exists>cs s c. \<Sigma> = CSC (CReturn cs # s) c \<and> cd = code_from_stack s \<and> 
    envs = map compile_closure cs # envs_from_stack s \<and> vs = compile_closure c # vals_from_stack s"
  by (induction \<Sigma> t rule: typecheck_closure_state.induct) auto

lemma compile_to_jump [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> compile_state \<Sigma> = TS vs envs (TJump # cd) \<Longrightarrow> False"
  by (induction \<Sigma> t rule: typecheck_closure_state.induct) (auto split: tree_code_state.splits)

lemma [simp]: "unzip e = (e', es) \<Longrightarrow> 
  iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSE (map (CApp1 cs) (rev es) @ s) cs e')"
proof (induction e arbitrary: s es)
  case (DApp e1 e2)
  then obtain es' where "unzip e1 = (e', es') \<and> es = e2 # es'" by (auto split: prod.splits)
  moreover with DApp have "iter (\<leadsto>\<^sub>c) (CSE (CApp1 cs e2 # s) cs e1) 
    (CSE (map (CApp1 cs) (rev (e2 # es')) @ s) cs e')" by simp
  moreover have "CSE s cs (DApp e1 e2) \<leadsto>\<^sub>c CSE (CApp1 cs e2 # s) cs e1" by simp
  ultimately show ?case by (metis iter_step)
qed simp_all 

theorem correctt [simp]: "compile_state \<Sigma>\<^sub>c \<leadsto>\<^sub>t \<Sigma>\<^sub>t' \<Longrightarrow> \<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>c'. iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> \<Sigma>\<^sub>t' = compile_state \<Sigma>\<^sub>c'"
proof (induction "compile_state \<Sigma>\<^sub>c" \<Sigma>\<^sub>t' rule: evalt.induct)
  case (evt_lookup env x v vs envs cd)
  hence "(\<exists>s cs e es. \<Sigma>\<^sub>c = CSE s cs e \<and> unzip e = (DVar x, es) \<and> 
    cd = zipcompile es (code_from_stack s) \<and> vs = vals_from_stack s \<and> 
      env # envs = envs_from_stack s) \<or> (\<exists>s c cs e es. \<Sigma>\<^sub>c = CSC (CApp1 cs e # s) c \<and> 
        unzip e = (DVar x, es) \<and> env # envs = envs_from_stack s \<and> 
          cd = zipcompile es (TApply # code_from_stack s) \<and> 
            vs = compile_closure c # vals_from_stack s)" using compile_to_lookup by simp
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    then obtain es where E: "unzip e = (DVar x, es) \<and> cd = zipcompile es (code_from_stack s) \<and>
      vs = vals_from_stack s \<and> env # envs = envs_from_stack s" by auto 
    hence "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSE (map (CApp1 cs) (rev es) @ s) cs (DVar x))" by simp


    have "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSC (map (CApp1 cs) (rev es) @ s) yyy) \<and> v = compile_closure yyy" by simp
    with E show ?case by fastforce
  next
    case (CSC s c)
    then obtain s' cs e es where S: "s = CApp1 cs e # s' \<and> 
      unzip e = (DVar x, es) \<and> env # envs = envs_from_stack s' \<and> 
        cd = zipcompile es (TApply # code_from_stack s') \<and> 
          vs = compile_closure c # vals_from_stack s'" by auto


    have "CSC (CApp1 cs e # s') c \<leadsto>\<^sub>c CSE (CApp2 c # s') cs e" by simp


    have "iter (\<leadsto>\<^sub>c) (CSC (CApp1 cs e # s') c) (CSC xxx yyy) \<and> 
      TS (v # vs) (env # envs) cd = compile_state (CSC xxx yyy)" by simp
    with S show ?case by fastforce
  qed
next
  case (evt_pushcon vs envs k cd)
  hence "(\<exists>s cs e es. \<Sigma>\<^sub>c = CSE s cs e \<and> unzip e = (DConst k, es) \<and> 
    cd = zipcompile es (code_from_stack s) \<and> vs = vals_from_stack s \<and> envs = envs_from_stack s) \<or> 
      (\<exists>s c cs e es. \<Sigma>\<^sub>c = CSC (CApp1 cs e # s) c \<and> unzip e = (DConst k, es) \<and> 
        envs = envs_from_stack s \<and> cd = zipcompile es (TApply # code_from_stack s) \<and> 
          vs = compile_closure c # vals_from_stack s)" using compile_to_pushcon by simp
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    then obtain es where E: "unzip e = (DConst k, es) \<and> cd = zipcompile es (code_from_stack s) \<and> 
      vs = vals_from_stack s \<and> envs = envs_from_stack s" by auto
    hence "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSE (map (CApp1 cs) (rev es) @ s) cs (DConst k))" by simp
    moreover have "CSE (map (CApp1 cs) (rev es) @ s) cs (DConst k) \<leadsto>\<^sub>c 
      CSC (map (CApp1 cs) (rev es) @ s) (CConst k)" by simp
    ultimately have "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSC (map (CApp1 cs) (rev es) @ s) (CConst k))" by simp
    with E show ?case by fastforce
  next
    case (CSC s c)
    then obtain s' cs e es where S: "s = CApp1 cs e # s' \<and> unzip e = (DConst k, es) \<and> 
        envs = envs_from_stack s' \<and> cd = zipcompile es (TApply # code_from_stack s') \<and> 
          vs = compile_closure c # vals_from_stack s'" by auto
    hence "iter (\<leadsto>\<^sub>c) (CSE (CApp2 c # s') cs e) 
      (CSE (map (CApp1 cs) (rev es) @ CApp2 c # s') cs (DConst k))" by simp
    moreover have "CSC (CApp1 cs e # s') c \<leadsto>\<^sub>c CSE (CApp2 c # s') cs e" by simp
    moreover have "CSE (map (CApp1 cs) (rev es) @ CApp2 c # s') cs (DConst k) \<leadsto>\<^sub>c 
      CSC (map (CApp1 cs) (rev es) @ CApp2 c # s') (CConst k)" by simp
    ultimately have "iter (\<leadsto>\<^sub>c) (CSC (CApp1 cs e # s') c)
      (CSC (map (CApp1 cs) (rev es) @ CApp2 c # s') (CConst k))" 
        by (metis iter_step iter_step_after)
    with S show ?case by fastforce
  qed
next
  case (evt_pushlam vs env envs cd' cd)
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    moreover hence "compile_state (CSE s cs e) = TS vs (env # envs) (TPushLam cd' # cd)" by simp
    ultimately obtain es tt e' where E: "unzip e = (DLam tt e', es) \<and> 
      cd = zipcompile es (code_from_stack s) \<and> cd' = compile e' \<and> 
        vs = vals_from_stack s \<and> env # envs = envs_from_stack s" using compile_to_pushlam by blast
    hence "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSE (map (CApp1 cs) (rev es) @ s) cs (DLam tt e'))" by simp
    moreover have "CSE (map (CApp1 cs) (rev es) @ s) cs (DLam tt e') \<leadsto>\<^sub>c 
      CSC (map (CApp1 cs) (rev es) @ s) (CLam tt cs e')" by simp
    ultimately have X: "iter (\<leadsto>\<^sub>c) (CSE s cs e) 
      (CSC (map (CApp1 cs) (rev es) @ s) (CLam tt cs e'))" by (metis iter_step_after)
    from E have "env = map compile_closure cs" by simp
    with E X show ?case by fastforce
  next
    case (CSC s c)
    moreover hence "compile_state (CSC s c) = TS vs (env # envs) (TPushLam cd' # cd)" by simp
    ultimately obtain s' cs e es tt e' where S: "s = CApp1 cs e # s' \<and> unzip e = (DLam tt e', es) \<and> 
      cd = zipcompile es (TApply # code_from_stack s') \<and> cd' = compile e' \<and> 
        vs = compile_closure c # vals_from_stack s' \<and> env # envs = envs_from_stack s'" 
      using compile_to_pushlam by blast
    hence "iter (\<leadsto>\<^sub>c) (CSE (CApp2 c # s') cs e) 
      (CSE (map (CApp1 cs) (rev es) @ CApp2 c # s') cs (DLam tt e'))" by simp
    moreover have "CSC (CApp1 cs e # s') c \<leadsto>\<^sub>c CSE (CApp2 c # s') cs e" by simp
    moreover have "CSE (map (CApp1 cs) (rev es) @ CApp2 c # s') cs (DLam tt e') \<leadsto>\<^sub>c 
      CSC (map (CApp1 cs) (rev es) @ CApp2 c # s') (CLam tt cs e')" by simp
    ultimately have X: "iter (\<leadsto>\<^sub>c) (CSC (CApp1 cs e # s') c) 
      (CSC (map (CApp1 cs) (rev es) @ CApp2 c # s') (CLam tt cs e'))" 
        by (metis iter_step iter_step_after)
      from S have "env = map compile_closure cs" by simp
    with S X show ?case by fastforce
  qed
next
  case (evt_apply v env cd' vs envs cd)
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    moreover hence "compile_state (CSE s cs e) = TS (v # TLam env cd' # vs) envs (TApply # cd)"
      by simp
    ultimately show ?case using compile_to_apply by blast
  next
    case (CSC s c)
    moreover hence "compile_state (CSC s c) = TS (v # TLam env cd' # vs) envs (TApply # cd)" by simp
    ultimately obtain s' c' where S: "s = CApp2 c' # s' \<and> cd = code_from_stack s' \<and> 
      envs = envs_from_stack s' \<and> v = compile_closure c \<and> TLam env cd' = compile_closure c' \<and> 
        vs = vals_from_stack s'" using compile_to_apply by blast
    then obtain t cs e where C: "c' = CLam t cs e \<and> env = map compile_closure cs \<and> cd' = compile e" 
      by (metis compile_lam_closure)
    have "CSC (CApp2 (CLam t cs e) # s') c \<leadsto>\<^sub>c CSE (CReturn (c # cs) # s') (c # cs) e" by simp
    hence "iter (\<leadsto>\<^sub>c) (CSC (CApp2 (CLam t cs e) # s') c) (CSE (CReturn (c # cs) # s') (c # cs) e)" 
      by (metis iter_step iter_refl)
    with S C show ?case by fastforce
  qed
next
  case (evt_return vs env envs cd)
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    moreover hence "compile_state (CSE s cs e) = TS vs (env # envs) (TReturn # cd)" by simp
    ultimately show ?case using compile_to_return by blast
  next
    case (CSC s c)
    moreover hence "compile_state (CSC s c) = TS vs (env # envs) (TReturn # cd)" by simp
    ultimately obtain cs s' where S: "s = CReturn cs # s' \<and> cd = code_from_stack s' \<and> 
      env = map compile_closure cs \<and> envs = envs_from_stack s' \<and> 
        vs = compile_closure c # vals_from_stack s'" using compile_to_return by blast
    have "CSC (CReturn cs # s') c \<leadsto>\<^sub>c CSC s' c" by simp
    hence "iter (\<leadsto>\<^sub>c) (CSC (CReturn cs # s') c) (CSC s' c)" by (metis iter_step iter_refl)
    with S show ?case by fastforce
  qed
next
  case (evt_jump v env' cd' vs env envs cd)
  thus ?case by (metis compile_to_jump)
qed

lemma lookup_latest [simp]: "latest_environment s = Some cs \<Longrightarrow> 
    \<exists>envs. envs_from_stack s = map compile_closure cs # envs"
  by (induction s rule: envs_from_stack.induct) simp_all

theorem completet [simp]: "\<Sigma> \<leadsto>\<^sub>c \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow> iter (\<leadsto>\<^sub>t) (compile_state \<Sigma>) (compile_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: evalc.induct)
  case (evc_var cs x c s)
  then obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs \<and> 
    lookup ts x = Some t'" by fastforce
  then obtain envs where "envs_from_stack s = map compile_closure cs # envs" 
    by (metis lookup_latest)
  with evc_var have "TS (vals_from_stack s) (envs_from_stack s) (TLookup x # code_from_stack s) \<leadsto>\<^sub>t 
    TS (compile_closure c # vals_from_stack s) (envs_from_stack s) (code_from_stack s)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS (vals_from_stack s) (envs_from_stack s) (TLookup x # code_from_stack s)) 
    (TS (compile_closure c # vals_from_stack s) (envs_from_stack s) (code_from_stack s))" 
      by (metis iter_step iter_refl)
  thus ?case by simp
next
  case (evc_con s cs k)
  have "TS (vals_from_stack s) (envs_from_stack s) (TPushCon k # code_from_stack s) \<leadsto>\<^sub>t 
    TS (TConst k # vals_from_stack s) (envs_from_stack s) (code_from_stack s)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS (vals_from_stack s) (envs_from_stack s) (TPushCon k # code_from_stack s)) 
    (TS (TConst k # vals_from_stack s) (envs_from_stack s) (code_from_stack s))"
      by (metis iter_step iter_refl)
  thus ?case by simp
next
  case (evc_lam s cs tt e)
  then obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs \<and>
    (ts \<turnstile>\<^sub>d DLam tt e : t')" by fastforce
  then obtain envs where "envs_from_stack s = map compile_closure cs # envs" 
    by (metis lookup_latest)
  hence "TS (vals_from_stack s) (envs_from_stack s) (TPushLam (compile e) # code_from_stack s) \<leadsto>\<^sub>t 
    TS (TLam (map compile_closure cs) (compile e) # vals_from_stack s) (envs_from_stack s) 
      (code_from_stack s)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS (vals_from_stack s) (envs_from_stack s) (TPushLam (compile e) # 
    code_from_stack s)) (TS (TLam (map compile_closure cs) (compile e) #
      vals_from_stack s) (envs_from_stack s) (code_from_stack s))" by (metis iter_step iter_refl)
  thus ?case by simp
next
  case (retc_app2 t cs e\<^sub>1 s c\<^sub>2)
  have "iter (\<leadsto>\<^sub>t) (TS (compile_closure c\<^sub>2 # TLam (map compile_closure cs) 
    (compile e\<^sub>1) # vals_from_stack s) (envs_from_stack s) (TApply # code_from_stack s))
      (TS (vals_from_stack s) ((compile_closure c\<^sub>2 # map compile_closure cs) # envs_from_stack s) 
      (compile e\<^sub>1 @ code_from_stack s))" by (metis evt_apply iter_step iter_refl)
  thus ?case by simp
next
  case (retc_ret cs s c)
  have "TS (compile_closure c # vals_from_stack s) (map compile_closure cs # envs_from_stack s) 
    (TReturn # code_from_stack s) \<leadsto>\<^sub>t TS (compile_closure c # vals_from_stack s) (envs_from_stack s) 
      (code_from_stack s)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS (compile_closure c # vals_from_stack s) 
    (map compile_closure cs # envs_from_stack s) (TReturn # code_from_stack s)) 
      (TS (compile_closure c # vals_from_stack s) (envs_from_stack s) (code_from_stack s))" 
        by (metis iter_step iter_refl)
  thus ?case by simp
qed simp_all

lemma iter_completet [simp]: "iter (\<leadsto>\<^sub>c) \<Sigma> \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow>
  iter (\<leadsto>\<^sub>t) (compile_state \<Sigma>) (compile_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: iter.induct)
  case (iter_step \<Sigma> \<Sigma>' \<Sigma>'')
  hence "iter (\<leadsto>\<^sub>t) (compile_state \<Sigma>) (compile_state \<Sigma>')" by simp
  moreover from iter_step have "iter (\<leadsto>\<^sub>t) (compile_state \<Sigma>') (compile_state \<Sigma>'')" by simp
  ultimately show ?case by (metis iter_append)
qed simp_all

end