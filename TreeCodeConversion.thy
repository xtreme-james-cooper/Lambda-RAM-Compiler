theory TreeCodeConversion
  imports TreeCode Closure
begin

primrec compile :: "dexpr \<Rightarrow> tree_code list" where
  "compile (DVar x) = [TLookup x]"
| "compile (DConst k) = [TPushCon k]"
| "compile (DLam t e) = [TPushLam (compile e)]"
| "compile (DApp e\<^sub>1 e\<^sub>2) = TEnter # compile e\<^sub>1 @ compile e\<^sub>2 @ [TApply]"

primrec compile_closure :: "closure \<Rightarrow> tclosure" where
  "compile_closure (CConst k) = TConst k"
| "compile_closure (CLam t cs e) = TLam (map compile_closure cs) (compile e)"

fun compile_stack :: "cframe list \<Rightarrow> tree_code_state" where
  "compile_stack [] = TS [] [] []"
| "compile_stack (CApp1 cs e # s) = (case compile_stack s of 
      TS vs envs cd \<Rightarrow> TS vs (map compile_closure cs # envs) (compile e @ TApply # cd))"
| "compile_stack (CApp2 c # s) = (case compile_stack s of 
      TS vs envs cd \<Rightarrow> TS (compile_closure c # vs) envs (TApply # cd))"
| "compile_stack (CReturn # s) = compile_stack s"

primrec compile_state :: "closure_state \<Rightarrow> tree_code_state" where
  "compile_state (CSE s cs e) = (case compile_stack s of 
      TS vs envs cd \<Rightarrow> TS vs (map compile_closure cs # envs) (compile e @ cd))"
| "compile_state (CSC s c) = (case compile_stack s of 
      TS vs envs cd \<Rightarrow> TS (compile_closure c # vs) envs cd)"

lemma [dest]: "TLookup x # cd = compile e @ cd' \<Longrightarrow> (e = DVar x \<Longrightarrow> cd' = cd \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction e) simp_all

lemma [dest]: "TPushCon k # cd = compile e @ cd' \<Longrightarrow> (e = DConst k \<Longrightarrow> cd' = cd \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction e) simp_all

lemma [dest]: "TPushLam cd'' # cd = compile e @ cd' \<Longrightarrow> 
    \<exists>t e'. e = DLam t e' \<and> cd'' = compile e' \<and> cd' = cd"
  by (induction e) simp_all

lemma [dest]: "TEnter # cd = compile e @ cd' \<Longrightarrow> 
    \<exists>e\<^sub>1 e\<^sub>2. e = DApp e\<^sub>1 e\<^sub>2 \<and> cd = compile e\<^sub>1 @ compile e\<^sub>2 @ TApply # cd'"
  by (induction e) simp_all

lemma [dest]: "TApply # cd = compile e @ cd' \<Longrightarrow> P"
  by (induction e) simp_all

lemma [dest]: "compile_closure c = TConst k \<Longrightarrow> c = CConst k"
  by (induction c) simp_all

lemma [dest]: "compile_closure c = TLam env cd \<Longrightarrow> 
    \<exists>t cs e. c = CLam t cs e \<and> env = map compile_closure cs \<and> cd = compile e"
  by (induction c) simp_all

primrec all_returnc :: "cframe list \<Rightarrow> bool" where
  "all_returnc [] = True"
| "all_returnc (r # rs) = (r = CReturn \<and> all_returnc rs)"

lemma compile_stack_to_lookup [simp]: "TS vs (env # envs) (TLookup x # cd) = compile_stack s \<Longrightarrow> 
  \<exists>sr cs s' cd'. s = sr @ CApp1 cs (DVar x) # s' \<and> all_returnc sr \<and> 
    compile_stack s' = TS vs envs cd' \<and> env = map compile_closure cs \<and> cd = TApply # cd'"
proof (induction s rule: compile_stack.induct)
  case (2 cs e s)
  then obtain s' where TS: "compile_stack s = TS vs envs s'" by (cases "compile_stack s") simp_all 
  moreover with 2 have "e = DVar x" by auto
  moreover from 2 TS have "env = map compile_closure cs" by simp
  moreover from 2 TS have "cd = TApply # s'" by auto
  ultimately show ?case by fastforce
next
  case (4 s)
  then obtain sr cs s' cd' where "s = sr @ CApp1 cs (DVar x) # s' \<and> all_returnc sr \<and> 
    compile_stack s' = TS vs envs cd' \<and> env = map compile_closure cs \<and> cd = TApply # cd'" 
      by fastforce
  hence "CReturn # s = (CReturn # sr) @ CApp1 cs (DVar x) # s' \<and>
    all_returnc (CReturn # sr) \<and> compile_stack s' = TS vs envs cd' \<and> 
      env = map compile_closure cs \<and> cd = TApply # cd'" by simp
  thus ?case by fastforce
qed (simp_all split: tree_code_state.splits)

lemma compile_stack_to_pushcon [simp]: "TS vs (env # envs) (TPushCon k # cd) = compile_stack s \<Longrightarrow> 
  \<exists>sr cs s' cd'. s = sr @ CApp1 cs (DConst k) # s' \<and> all_returnc sr \<and> 
    compile_stack s' = TS vs envs cd' \<and> env = map compile_closure cs \<and> cd = TApply # cd'"
proof (induction s rule: compile_stack.induct)
  case (2 cs e s)
  then obtain s' where TS: "compile_stack s = TS vs envs s'" by (cases "compile_stack s") simp_all 
  moreover with 2 have "e = DConst k" by auto
  moreover from 2 TS have "env = map compile_closure cs" by simp
  moreover from 2 TS have "cd = TApply # s'" by auto
  ultimately show ?case by fastforce
next
  case (4 s)
  then obtain sr cs s' cd' where "s = sr @ CApp1 cs (DConst k) # s' \<and> all_returnc sr \<and> 
    compile_stack s' = TS vs envs cd' \<and> env = map compile_closure cs \<and> cd = TApply # cd'" 
      by fastforce
  hence "CReturn # s = (CReturn # sr) @ CApp1 cs (DConst k) # s' \<and>
    all_returnc (CReturn # sr) \<and> compile_stack s' = TS vs envs cd' \<and> 
      env = map compile_closure cs \<and> cd = TApply # cd'" by simp
  thus ?case by fastforce
qed (simp_all split: tree_code_state.splits)

lemma compile_stack_to_pushlam [simp]: "TS vs (env # envs) (TPushLam cd' # cd) = compile_stack s \<Longrightarrow> 
  \<exists>sr cs s' cd'' t e. s = sr @ CApp1 cs (DLam t e) # s' \<and> all_returnc sr \<and>  
    compile_stack s' = TS vs envs cd'' \<and> env = map compile_closure cs \<and> cd = TApply # cd'' \<and> 
      compile e = cd'"
proof (induction s rule: compile_stack.induct)
  case (2 cs e s)
  then obtain s' where TS: "compile_stack s = TS vs envs s'" by (cases "compile_stack s") simp_all 
  moreover with 2 obtain t e' where "e = DLam t e' \<and> compile e' = cd'" by auto
  moreover from 2 TS have "env = map compile_closure cs" by simp
  moreover from 2 TS have "cd = TApply # s'" by auto
  ultimately show ?case by fastforce
next
  case (4 s)
  then obtain sr cs s' cd'' t e' where "s = sr @ CApp1 cs (DLam t e') # s' \<and> all_returnc sr \<and> 
    compile_stack s' = TS vs envs cd'' \<and> env = map compile_closure cs \<and> cd = TApply # cd'' \<and> 
      compile e' = cd'" by fastforce
  hence "CReturn # s = (CReturn # sr) @ CApp1 cs (DLam t e') # s' \<and>
    all_returnc (CReturn # sr) \<and> compile_stack s' = TS vs envs cd'' \<and> 
      env = map compile_closure cs \<and> cd = TApply # cd'' \<and> compile e' = cd'" by simp
  thus ?case by fastforce
qed (simp_all split: tree_code_state.splits)

lemma compile_stack_to_enter [simp]: "TS vs (env # envs) (TEnter # cd) = compile_stack s \<Longrightarrow> 
  \<exists>sr s' cd' cs e\<^sub>1 e\<^sub>2. s = sr @ CApp1 cs (DApp e\<^sub>1 e\<^sub>2) # s' \<and> all_returnc sr \<and>  
    compile_stack s' = TS vs envs cd' \<and> env = map compile_closure cs \<and> 
      cd = compile e\<^sub>1 @ compile e\<^sub>2 @ TApply # TApply # cd'" 
proof (induction s rule: compile_stack.induct)
  case (2 cs e s)
  then obtain cd' where TS: "compile_stack s = TS vs envs cd' \<and> env = map compile_closure cs \<and> 
    TEnter # cd = compile e @ TApply # cd'" by (cases "compile_stack s") simp_all
  moreover then obtain e\<^sub>1 e\<^sub>2 where "e = DApp e\<^sub>1 e\<^sub>2 \<and> 
    cd = compile e\<^sub>1 @ compile e\<^sub>2 @ TApply # TApply # cd'" by fastforce
  ultimately show ?case by fastforce
next
  case (4 s)
  from 4 obtain sr s' cd' cs e\<^sub>1 e\<^sub>2 where "s = sr @ CApp1 cs (DApp e\<^sub>1 e\<^sub>2) # s' \<and> all_returnc sr \<and>
    compile_stack s' = TS vs envs cd' \<and> env = map compile_closure cs \<and> 
      cd = compile e\<^sub>1 @ compile e\<^sub>2 @ TApply # TApply # cd'" by fastforce
  moreover hence "CReturn # s = (CReturn # sr) @ CApp1 cs (DApp e\<^sub>1 e\<^sub>2) # s' \<and> 
    all_returnc (CReturn # sr)" by simp
  ultimately show ?case by fastforce
qed (simp_all split: tree_code_state.splits)

lemma compile_stack_to_apply [simp]: "TS vs envs (TApply # cd) = compile_stack s \<Longrightarrow> 
  \<exists>sr s' c vs'. s = sr @ CApp2 c # s' \<and> all_returnc sr \<and> compile_stack s' = TS vs' envs cd \<and> 
    vs = compile_closure c # vs'"
proof (induction s rule: compile_stack.induct)
  case (3 c s)
  then obtain vs' where "compile_stack s = TS vs' envs cd \<and> vs = compile_closure c # vs'" 
    by (cases "compile_stack s") simp_all
  thus ?case by fastforce
next
  case (4 s)
  then obtain sr s' c vs' where "s = sr @ CApp2 c # s' \<and> all_returnc sr \<and> 
    compile_stack s' = TS vs' envs cd \<and> vs = compile_closure c # vs'" by fastforce
  moreover hence "CReturn # s = (CReturn # sr) @ CApp2 c # s' \<and> 
    all_returnc (CReturn # sr)" by simp
  ultimately show ?case by fastforce
qed (auto split: tree_code_state.splits)

lemma compile_to_lookup [simp]: "TS vs (env # envs) (TLookup x # cd) = compile_state \<Sigma> \<Longrightarrow> 
  (\<exists>s cs. compile_stack s = TS vs envs cd \<and> env = map compile_closure cs \<and> \<Sigma> = CSE s cs (DVar x)) \<or> 
    (\<exists>sr s vs' c cs cd'. compile_stack s = TS vs' envs cd' \<and> env = map compile_closure cs \<and> 
      all_returnc sr \<and> cd = TApply # cd' \<and> vs = compile_closure c # vs' \<and> 
        \<Sigma> = CSC (sr @ CApp1 cs (DVar x) # s) c)"
proof (induction \<Sigma>)
  case (CSC s c)
  then obtain vs' where "TS vs' (env # envs) (TLookup x # cd) = compile_stack s \<and> 
    vs = compile_closure c # vs'" by (simp split: tree_code_state.splits)
  thus ?case using compile_stack_to_lookup by metis
qed (auto split: tree_code_state.splits)

lemma compile_to_pushcon [simp]: "TS vs (env # envs) (TPushCon k # cd) = compile_state \<Sigma> \<Longrightarrow> 
  (\<exists>s cs. compile_stack s = TS vs envs cd \<and> env = map compile_closure cs \<and> 
    \<Sigma> = CSE s cs (DConst k)) \<or> (\<exists>sr s vs' c cs cd'. compile_stack s = TS vs' envs cd' \<and> 
      env = map compile_closure cs \<and> all_returnc sr \<and> cd = TApply # cd' \<and> 
        vs = compile_closure c # vs' \<and> \<Sigma> = CSC (sr @ CApp1 cs (DConst k) # s) c)"
proof (induction \<Sigma>)
  case (CSC s c)
  then obtain vs' where "TS vs' (env # envs) (TPushCon k # cd) = compile_stack s \<and> 
    vs = compile_closure c # vs'" by (simp split: tree_code_state.splits)
  thus ?case using compile_stack_to_pushcon by metis
qed (auto split: tree_code_state.splits)

lemma compile_to_pushlam [simp]: "TS vs (env # envs) (TPushLam cd' # cd) = compile_state \<Sigma> \<Longrightarrow> 
  (\<exists>s cs t e. compile_stack s = TS vs envs cd \<and> env = map compile_closure cs \<and> cd' = compile e \<and> 
    \<Sigma> = CSE s cs (DLam t e)) \<or> (\<exists>sr s vs' c cd'' cs t e. compile_stack s = TS vs' envs cd'' \<and> 
      cd = TApply # cd'' \<and> vs = compile_closure c # vs' \<and> env = map compile_closure cs \<and> 
        all_returnc sr \<and> cd' = compile e \<and> \<Sigma> = CSC (sr @ CApp1 cs (DLam t e) # s) c)"
proof (induction \<Sigma>)
  case (CSC s c)
  then obtain vs' where "TS vs' (env # envs) (TPushLam cd' # cd) = compile_stack s \<and> 
    vs = compile_closure c # vs'" by (simp split: tree_code_state.splits)
  thus ?case using compile_stack_to_pushlam by metis
qed (auto split: tree_code_state.splits)

lemma compile_to_enter [simp]: "TS vs (env # envs) (TEnter # cd) = compile_state \<Sigma> \<Longrightarrow> 
  (\<exists>s cs e\<^sub>1 e\<^sub>2 cd'. \<Sigma> = CSE s cs (DApp e\<^sub>1 e\<^sub>2) \<and> compile_stack s = TS vs envs cd' \<and> 
    env = map compile_closure cs \<and> cd = compile e\<^sub>1 @ compile e\<^sub>2 @ TApply # cd') \<or>
      (\<exists>sr s c vs' cd' cs e\<^sub>1 e\<^sub>2. \<Sigma> = CSC (sr @ CApp1 cs (DApp e\<^sub>1 e\<^sub>2) # s) c \<and> 
        vs = compile_closure c # vs' \<and> compile_stack s = TS vs' envs cd' \<and> all_returnc sr \<and>
          env = map compile_closure cs \<and> cd = compile e\<^sub>1 @ compile e\<^sub>2 @ TApply # TApply # cd')" 
proof (induction \<Sigma>) 
  case (CSC s c)
  then obtain vs' where "vs = compile_closure c # vs' \<and> 
    compile_stack s = TS vs' (env # envs) (TEnter # cd)" by (simp split: tree_code_state.splits)
  thus ?case using compile_stack_to_enter by metis
qed (auto split: tree_code_state.splits)

lemma compile_to_apply [simp]: "TS vs envs (TApply # cd) = compile_state \<Sigma> \<Longrightarrow> 
  \<exists>sr s c c' vs'. \<Sigma> = CSC (sr @ CApp2 c' # s) c \<and> all_returnc sr \<and> 
    vs = compile_closure c # compile_closure c' # vs' \<and> compile_stack s = TS vs' envs cd"
proof (induction \<Sigma>)
  case (CSC s c)
  then obtain vs' where "compile_stack s = TS vs' envs (TApply # cd) \<and> vs = compile_closure c # vs'"
    by (simp split: tree_code_state.splits)
  thus ?case by (metis compile_stack_to_apply)
qed (auto split: tree_code_state.splits)

lemma [simp]: "all_returnc rs \<Longrightarrow> iter (\<leadsto>\<^sub>c) (CSC (rs @ s) c) (CSC s c)"
proof (induction rs)
  case (Cons r rs)
  hence "iter (\<leadsto>\<^sub>c) (CSC (rs @ s) c) (CSC s c)" by simp
  moreover have "CSC (CReturn # rs @ s) c \<leadsto>\<^sub>c CSC (rs @ s) c" by simp
  ultimately have "iter (\<leadsto>\<^sub>c) (CSC (CReturn # rs @ s) c) (CSC s c)" by (metis iter_step)
  with Cons show ?case by simp
qed simp_all

theorem correctt [simp]: "compile_state \<Sigma>\<^sub>c \<leadsto>\<^sub>t \<Sigma>\<^sub>t' \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>c'. iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> \<Sigma>\<^sub>t' = compile_state \<Sigma>\<^sub>c'"
proof (induction "compile_state \<Sigma>\<^sub>c" \<Sigma>\<^sub>t' rule: evalt.induct)
  case (evt_lookup env x v vs envs cd)
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    hence E: "compile_stack s = TS vs envs cd \<and> env = map compile_closure cs \<and> e = DVar x" 
      using compile_to_lookup by blast
    with CSE obtain c where C: "lookup cs x = Some c \<and> v = compile_closure c" by fastforce
    hence "CSE s cs (DVar x) \<leadsto>\<^sub>c CSC s c" by simp
    hence "iter (\<leadsto>\<^sub>c) (CSE s cs (DVar x)) (CSC s c)" by simp
    with E C show ?case by fastforce
  next
    case (CSC s c)
    then obtain rs s' vs' cs cd' where C: "compile_stack s' = TS vs' envs cd' \<and> 
      env = map compile_closure cs \<and> cd = TApply # cd' \<and> vs = compile_closure c # vs' \<and> 
        s = rs @ CApp1 cs (DVar x) # s' \<and> all_returnc rs" using compile_to_lookup by blast
    with CSC obtain c' where C': "lookup cs x = Some c' \<and> v = compile_closure c'" by fastforce
    hence "CSE (CApp2 c # s') cs (DVar x) \<leadsto>\<^sub>c CSC (CApp2 c # s') c'" by simp
    moreover have "CSC (CApp1 cs (DVar x) # s') c \<leadsto>\<^sub>c CSE (CApp2 c # s') cs (DVar x)" by simp
    moreover from C have "iter (\<leadsto>\<^sub>c) (CSC (rs @ CApp1 cs (DVar x) # s') c) 
      (CSC (CApp1 cs (DVar x) # s') c)" by fastforce
    ultimately have X: "iter (\<leadsto>\<^sub>c) (CSC (rs @ CApp1 cs (DVar x) # s') c) (CSC (CApp2 c # s') c')" 
      by (metis iter_step iter_refl iter_append)
    from C have "TS (compile_closure c' # compile_closure c # vs') envs (TApply # cd') = 
      compile_state (CSC (CApp2 c # s') c')" by (simp split: tree_code_state.splits)
    with C C' X show ?case by blast
  qed
next
  case (evt_pushcon vs env envs k cd)
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    hence E: "compile_stack s = TS vs envs cd \<and> env = map compile_closure cs \<and> e = DConst k" 
      using compile_to_pushcon by blast
    have "CSE s cs (DConst k) \<leadsto>\<^sub>c CSC s (CConst k)" by simp
    hence "iter (\<leadsto>\<^sub>c) (CSE s cs (DConst k)) (CSC s (CConst k))" by (metis iter_step iter_refl)
    with E show ?case by fastforce
  next
    case (CSC s c)
    then obtain rs s' vs' cs cd' where C: "compile_stack s' = TS vs' envs cd' \<and> 
      env = map compile_closure cs \<and> cd = TApply # cd' \<and> vs = compile_closure c # vs' \<and> 
        s = rs @ CApp1 cs (DConst k) # s' \<and> all_returnc rs" using compile_to_pushcon by blast
    have "CSE (CApp2 c # s') cs (DConst k) \<leadsto>\<^sub>c CSC (CApp2 c # s') (CConst k)" by simp
    moreover have "CSC (CApp1 cs (DConst k) # s') c \<leadsto>\<^sub>c CSE (CApp2 c # s') cs (DConst k)" by simp
    moreover from C have "iter (\<leadsto>\<^sub>c) (CSC (rs @ CApp1 cs (DConst k) # s') c) 
      (CSC (CApp1 cs (DConst k) # s') c)" by fastforce
    ultimately have X: 
      "iter (\<leadsto>\<^sub>c) (CSC (rs @ CApp1 cs (DConst k) # s') c) (CSC (CApp2 c # s') (CConst k))" 
        by (metis iter_step iter_refl iter_append)
    from C have "TS (TConst k # compile_closure c # vs') envs (TApply # cd') = 
      compile_state (CSC (CApp2 c # s') (CConst k))" by (simp split: tree_code_state.splits)
    with C X show ?case by blast
  qed
next
  case (evt_pushlam vs env envs cd' cd)
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e')
    then obtain t e where S: "env = map compile_closure cs \<and> cd' = compile e \<and> 
      compile_stack s = TS vs envs cd \<and> CSE s cs e' = CSE s cs (DLam t e)" 
        using compile_to_pushlam by blast
    have "CSE s cs (DLam t e) \<leadsto>\<^sub>c CSC s (CLam t cs e)" by simp
    hence "iter (\<leadsto>\<^sub>c) (CSE s cs (DLam t e)) (CSC s (CLam t cs e))" by (metis iter_step iter_refl)
    with S show ?case by fastforce
  next
    case (CSC s c)
    then obtain rs s' vs' cd'' cs t e where E: "compile_stack s' = TS vs' envs cd'' \<and> 
      cd = TApply # cd'' \<and> vs = compile_closure c # vs' \<and> env = map compile_closure cs \<and> 
        cd' = compile e \<and> s = rs @ CApp1 cs (DLam t e) # s' \<and> all_returnc rs" 
          using compile_to_pushlam by blast
    have "CSE (CApp2 c # s') cs (DLam t e) \<leadsto>\<^sub>c CSC (CApp2 c # s') (CLam t cs e)" by simp
    moreover have "CSC (CApp1 cs (DLam t e) # s') c \<leadsto>\<^sub>c CSE (CApp2 c # s') cs (DLam t e)" by simp
    moreover from E have "iter (\<leadsto>\<^sub>c) (CSC (rs @ CApp1 cs (DLam t e) # s') c) 
      (CSC (CApp1 cs (DLam t e) # s') c)" by fastforce
    ultimately have
      "iter (\<leadsto>\<^sub>c) (CSC (rs @ CApp1 cs (DLam t e) # s') c) (CSC (CApp2 c # s') (CLam t cs e))" 
        by (metis iter_step iter_refl iter_append)
    with E show ?case by fastforce
  qed
next
  case (evt_enter vs env envs cd)
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    then obtain e\<^sub>1 e\<^sub>2 cd' where E: "e = DApp e\<^sub>1 e\<^sub>2 \<and> compile_stack s = TS vs envs cd' \<and> 
      env = map compile_closure cs \<and> cd = compile e\<^sub>1 @ compile e\<^sub>2 @ TApply # cd'" 
        using compile_to_enter by blast
    have "CSE s cs (DApp e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>c CSE (CApp1 cs e\<^sub>2 # s) cs e\<^sub>1" by simp
    hence "iter (\<leadsto>\<^sub>c) (CSE s cs (DApp e\<^sub>1 e\<^sub>2)) (CSE (CApp1 cs e\<^sub>2 # s) cs e\<^sub>1)" 
      by (metis iter_step iter_refl)
    with E show ?case by fastforce
  next
    case (CSC s c)
    then obtain rs s' vs' cd' cs e\<^sub>1 e\<^sub>2 where S: "s = rs @ CApp1 cs (DApp e\<^sub>1 e\<^sub>2) # s' \<and> 
      vs = compile_closure c # vs' \<and> compile_stack s' = TS vs' envs cd' \<and> all_returnc rs \<and> 
        env = map compile_closure cs \<and> cd = compile e\<^sub>1 @ compile e\<^sub>2 @ TApply # TApply # cd'" 
      using compile_to_enter by blast
    have "CSC (CApp1 cs (DApp e\<^sub>1 e\<^sub>2) # s') c \<leadsto>\<^sub>c CSE (CApp2 c # s') cs (DApp e\<^sub>1 e\<^sub>2)" by simp
    moreover have "CSE (CApp2 c # s') cs (DApp e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>c CSE (CApp1 cs e\<^sub>2 # CApp2 c # s') cs e\<^sub>1" 
      by simp
    moreover from S have "iter (\<leadsto>\<^sub>c) (CSC (rs @ CApp1 cs (DApp e\<^sub>1 e\<^sub>2) # s') c) 
      (CSC (CApp1 cs (DApp e\<^sub>1 e\<^sub>2) # s') c)" by fastforce
    ultimately have "iter (\<leadsto>\<^sub>c) (CSC (rs @ CApp1 cs (DApp e\<^sub>1 e\<^sub>2) # s') c) 
      (CSE (CApp1 cs e\<^sub>2 # CApp2 c # s') cs e\<^sub>1)" by (metis iter_step iter_refl iter_append)
    with S show ?case by fastforce
  qed
next
  case (evt_apply v env cd' vs envs cd)
  then obtain rs s c c' where S: "\<Sigma>\<^sub>c = CSC (rs @ CApp2 c' # s) c \<and> v = compile_closure c \<and> 
    compile_closure c' = TLam env cd' \<and> compile_stack s = TS vs envs cd \<and> all_returnc rs" 
      using compile_to_apply by fastforce
  then obtain t cs e where C: "c' = CLam t cs e \<and> env = map compile_closure cs \<and> cd' = compile e" 
    by fastforce
  have "CSC (CApp2 (CLam t cs e) # s) c \<leadsto>\<^sub>c CSE (CReturn # s) (c # cs) e" by simp
  moreover from S have "iter (\<leadsto>\<^sub>c) (CSC (rs @ CApp2 (CLam t cs e) # s) c) 
    (CSC (CApp2 (CLam t cs e) # s) c)" by fastforce
  ultimately have "iter (\<leadsto>\<^sub>c) (CSC (rs @ CApp2 (CLam t cs e) # s) c) (CSE (CReturn # s) (c # cs) e)" 
    by (metis iter_step iter_refl iter_append)
  with S C show ?case by fastforce
qed

theorem completet [simp]: "\<Sigma> \<leadsto>\<^sub>c \<Sigma>' \<Longrightarrow> iter (\<leadsto>\<^sub>t) (compile_state \<Sigma>) (compile_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: evalc.induct)
  case (evc_var cs x c s)
  obtain vs envs cd where S: "compile_stack s = TS vs envs cd" 
    by (induction s rule: compile_stack.induct) (simp_all split: tree_code_state.splits)
  from evc_var have "TS vs (map compile_closure cs # envs) (TLookup x # cd) \<leadsto>\<^sub>t 
    TS (compile_closure c # vs) envs cd" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS vs (map compile_closure cs # envs) (TLookup x # cd)) 
    (TS (compile_closure c # vs) envs cd)" by (metis iter_step iter_refl)
  with S show ?case by simp
next
  case (evc_con s cs k)
  obtain vs envs cd where S: "compile_stack s = TS vs envs cd" 
    by (induction s rule: compile_stack.induct) (simp_all split: tree_code_state.splits)
  have "TS vs (map compile_closure cs # envs) (TPushCon k # cd) \<leadsto>\<^sub>t TS (TConst k # vs) envs cd" 
    by simp
  hence "iter (\<leadsto>\<^sub>t) (TS vs (map compile_closure cs # envs) (TPushCon k # cd)) 
    (TS (TConst k # vs) envs cd)" by (metis iter_step iter_refl)
  with S show ?case by simp
next
  case (evc_lam s cs t e)
  obtain vs envs cd where S: "compile_stack s = TS vs envs cd" 
    by (induction s rule: compile_stack.induct) (simp_all split: tree_code_state.splits)
  have "TS vs (map compile_closure cs # envs) (TPushLam (compile e) # cd) \<leadsto>\<^sub>t 
    TS (TLam (map compile_closure cs) (compile e) # vs) envs cd" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS vs (map compile_closure cs # envs) (TPushLam (compile e) # cd)) 
      (TS (TLam (map compile_closure cs) (compile e) # vs) envs cd)" by (metis iter_step iter_refl)
  with S show ?case by simp
next
  case (evc_app s cs e\<^sub>1 e\<^sub>2)
  obtain vs envs cd where S: "compile_stack s = TS vs envs cd" 
    by (induction s rule: compile_stack.induct) (simp_all split: tree_code_state.splits)
  have "TS vs (map compile_closure cs # envs) (TEnter # compile e\<^sub>1 @ compile e\<^sub>2 @ TApply # cd) \<leadsto>\<^sub>t
      TS vs (map compile_closure cs # map compile_closure cs # envs) 
        (compile e\<^sub>1 @ compile e\<^sub>2 @ TApply # cd)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS vs (map compile_closure cs # envs) 
    (TEnter # compile e\<^sub>1 @ compile e\<^sub>2 @ TApply # cd))
      (TS vs (map compile_closure cs # map compile_closure cs # envs) 
        (compile e\<^sub>1 @ compile e\<^sub>2 @ TApply # cd))" by (metis iter_step iter_refl)
  with S show ?case by simp
next
  case (retc_app1 cs e\<^sub>2 s c\<^sub>1)
  obtain vs envs cd where "compile_stack s = TS vs envs cd" 
    by (induction s rule: compile_stack.induct) (simp_all split: tree_code_state.splits)
  thus ?case by simp
next
  case (retc_app2 t cs e\<^sub>1 s c\<^sub>2)
  obtain vs envs cd where S: "compile_stack s = TS vs envs cd" 
    by (induction s rule: compile_stack.induct) (simp_all split: tree_code_state.splits)
  have "TS (compile_closure c\<^sub>2 # TLam (map compile_closure cs) (compile e\<^sub>1) # vs) envs (TApply # cd) 
    \<leadsto>\<^sub>t TS vs ((compile_closure c\<^sub>2 # map compile_closure cs) # envs) ((compile e\<^sub>1) @ cd)" 
      by (metis evt_apply)
  hence "iter (\<leadsto>\<^sub>t) (TS (compile_closure c\<^sub>2 # TLam (map compile_closure cs) (compile e\<^sub>1) # vs) envs 
    (TApply # cd))
      (TS vs ((compile_closure c\<^sub>2 # map compile_closure cs) # envs) (compile e\<^sub>1 @ cd))" 
    by (metis iter_step iter_refl)
  with S show ?case by simp
qed simp_all

lemma iter_completet [simp]: "iter (\<leadsto>\<^sub>c) \<Sigma> \<Sigma>' \<Longrightarrow> iter (\<leadsto>\<^sub>t) (compile_state \<Sigma>) (compile_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: iter.induct)
  case (iter_step \<Sigma> \<Sigma>' \<Sigma>'')
  moreover hence "iter (\<leadsto>\<^sub>t) (compile_state \<Sigma>) (compile_state \<Sigma>')" by simp
  ultimately show ?case by (metis iter_append)
qed simp_all

end