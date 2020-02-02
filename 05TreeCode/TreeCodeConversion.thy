theory TreeCodeConversion
  imports TreeCode "../04Closure/Closure"
begin

primrec encode' :: "dexpr \<Rightarrow> tree_code list \<Rightarrow> tree_code list" where
  "encode' (DVar x) cd = TLookup x # cd"
| "encode' (DConst k) cd = TPushCon k # cd"
| "encode' (DLam t e) cd = TPushLam (encode' e []) TReturn # cd"
| "encode' (DApp e\<^sub>1 e\<^sub>2) cd = encode' e\<^sub>1 (encode' e\<^sub>2 (TApply # cd))"

definition encode :: "dexpr \<Rightarrow> tree_code list" where
  "encode e = encode' e []"

primrec encode_closure :: "closure \<Rightarrow> tclosure" where
  "encode_closure (CConst k) = TConst k"
| "encode_closure (CLam t cs e) = TLam (map encode_closure cs) (encode e) TReturn"

fun vals_from_stack :: "cframe list \<Rightarrow> tclosure list" where
  "vals_from_stack [] = []"
| "vals_from_stack (CApp1 cs e # s) = vals_from_stack s"
| "vals_from_stack (CApp2 c # s) = encode_closure c # vals_from_stack s"
| "vals_from_stack (CReturn cs # s) = vals_from_stack s"

fun stack_from_stack :: "cframe list \<Rightarrow> (tclosure list \<times> tree_code list \<times> tree_return) list" where
  "stack_from_stack [] = [([], [], TReturn)]"
| "stack_from_stack (CApp1 cs e # s) = (case hd (stack_from_stack s) of 
    (env, cd, r) \<Rightarrow> (env, encode' e (TApply # cd), r) # tl (stack_from_stack s))"
| "stack_from_stack (CApp2 c # s) = (case hd (stack_from_stack s) of 
    (env, cd, r) \<Rightarrow> (env, TApply # cd, r) # tl (stack_from_stack s))"
| "stack_from_stack (CReturn cs # s) = (map encode_closure cs, [], TReturn) # stack_from_stack s"

primrec encode_state :: "closure_state \<Rightarrow> tree_code_state" where
  "encode_state (CSE s cs e) = (case hd (stack_from_stack s) of 
    (env, cd, r) \<Rightarrow> TS (vals_from_stack s) ((env, encode' e cd, r) # tl (stack_from_stack s)))"
| "encode_state (CSC s c) = 
    TS (encode_closure c # vals_from_stack s) (stack_from_stack s)"

primrec unzip :: "dexpr \<Rightarrow> dexpr \<times> dexpr list" where
  "unzip (DVar x) = (DVar x, [])"
| "unzip (DConst k) = (DConst k, [])"
| "unzip (DLam t e) = (DLam t e, [])"
| "unzip (DApp e\<^sub>1 e\<^sub>2) = (case unzip e\<^sub>1 of (e, es) \<Rightarrow> (e, e\<^sub>2 # es))"

primrec zip_encode :: "dexpr list \<Rightarrow> tree_code list \<Rightarrow> tree_code list" where 
  "zip_encode [] acc = acc"
| "zip_encode (e # es) acc = zip_encode es (encode' e (TApply # acc))"

lemma [simp]: "encode' e cd @ cd' = encode' e (cd @ cd')"
  by (induction e arbitrary: cd) simp_all

lemma [simp]: "unzip e = (e', es) \<Longrightarrow> encode' e' (zip_encode es acc) = encode' e acc"
  by (induction e arbitrary: e' es acc) (auto split: prod.splits)

lemma [simp]: "vals_from_stack (map (CApp1 cs) (rev es) @ s) = vals_from_stack s"
  by (induction es arbitrary: s) simp_all

lemma [simp]: "stack_from_stack s = (env, cd, r) # sfs \<Longrightarrow> 
    stack_from_stack (map (CApp1 cs) (rev es) @ s) = (env, zip_encode es cd, r) # sfs"
  by (induction es arbitrary: s cd) simp_all

lemma [dest]: "encode' e cd' = TLookup x # cd \<Longrightarrow> 
    (\<And>es. unzip e = (DVar x, es) \<Longrightarrow> cd = zip_encode es cd' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction e arbitrary: cd') fastforce+

lemma [dest]: "encode' e cd' = TPushCon k # cd \<Longrightarrow> 
    (\<And>es. unzip e = (DConst k, es) \<Longrightarrow> cd = zip_encode es cd' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction e arbitrary: cd') fastforce+

lemma encode_to_pushlam' [dest]: "encode' e cd' = TPushLam cd'' r # cd \<Longrightarrow> 
  (\<And>es t e'. unzip e = (DLam t e', es) \<Longrightarrow> cd'' = encode e' \<Longrightarrow> r = TReturn \<Longrightarrow> 
    cd = zip_encode es cd' \<Longrightarrow> P) \<Longrightarrow> P"
  using encode_def by (induction e arbitrary: cd') fastforce+

lemma [dest]: "encode' e cd' = TApply # cd \<Longrightarrow> P"
  by (induction e arbitrary: cd') simp_all

lemma [dest]: "encode_closure c = TConst k \<Longrightarrow> c = CConst k"
  by (induction c) simp_all

lemma encode_lam_closure [dest]: "encode_closure c = TLam env cd r \<Longrightarrow> (\<And>t cs e. 
    c = CLam t cs e \<Longrightarrow> env = map encode_closure cs \<Longrightarrow> cd = encode e \<Longrightarrow> r = TReturn \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction c) simp_all

lemma tc_latest_environment [simp]: "s @ CApp1 cs e # s' :\<^sub>c t \<rightarrow> t' \<Longrightarrow> 
  latest_environment s' = Some cs"
proof (induction s arbitrary: t)
  case (Cons f s)
  moreover from Cons(2) obtain tt where "s @ CApp1 cs e # s' :\<^sub>c tt \<rightarrow> t'" 
    by (induction "(f # s) @ CApp1 cs e # s'" t t' rule: typecheck_cstack.induct) simp_all
  ultimately show ?case by simp
qed fastforce+

lemma [simp]: "stack_from_stack s \<noteq> []"
  by (induction s rule: stack_from_stack.induct) (simp_all split: prod.splits)

lemma [simp]: "\<exists>env cd r. hd (stack_from_stack s) = (env, cd, r)"
  by (induction s rule: stack_from_stack.induct) (simp_all split: prod.splits)

lemma encode_stack_to_lookup [dest]: "stack_from_stack s = (env, TLookup x # cd, r) # sfs \<Longrightarrow> 
  \<exists>cs e es s' cd'. s = CApp1 cs e # s' \<and> stack_from_stack s' = (env, cd', r) # sfs \<and> 
    unzip e = (DVar x, es) \<and> cd = zip_encode es (TApply # cd')"
proof (induction s rule: stack_from_stack.induct)
  case (2 cs e s)
  obtain env' cd' r' where "hd (stack_from_stack s) = (env', cd', r')" by fastforce
  moreover with 2 have E: "env' = env \<and> r' = r \<and> encode' e (TApply # cd') = TLookup x # cd \<and> 
    sfs = tl (stack_from_stack s)" by simp
  ultimately have "stack_from_stack s = (env, cd', r) # sfs" 
    by (cases "stack_from_stack s") simp_all
  moreover from E obtain es where "unzip e = (DVar x, es) \<and> cd = zip_encode es (TApply # cd')"
    by blast
  ultimately show ?case by fastforce
qed (simp_all split: prod.splits)

lemma encode_stack_to_pushcon [dest]: "code_from_stack s = TPushCon k # cd \<Longrightarrow> 
  \<exists>cs e es s'. s = CApp1 cs e # s' \<and> unzip e = (DConst k, es) \<and>
    cd = zip_encode es (TApply # code_from_stack s')"
  by (induction s rule: code_from_stack.induct) auto

lemma encode_stack_to_pushlam [dest]: "code_from_stack s = TPushLam cd' # cd \<Longrightarrow> 
  \<exists>cs e es s' t e'. s = CApp1 cs e # s' \<and> unzip e = (DLam t e', es) \<and>
    cd = zip_encode es (TApply # code_from_stack s') \<and> cd' = encode e'"
proof (induction s rule: code_from_stack.induct)
  case (2 cs e s)
  hence "encode' e (TApply # code_from_stack s) = TPushLam cd' # cd" by auto
  moreover then obtain es t e' where "unzip e = (DLam t e', es) \<and> cd' = encode e' \<and> 
    cd = zip_encode es (TApply # code_from_stack s)" by blast
  ultimately show ?case by simp
qed simp_all

lemma encode_stack_to_apply [dest]: "code_from_stack s = TApply # cd \<Longrightarrow> 
    \<exists>s' c. s = CApp2 c # s' \<and> cd = code_from_stack s'"
  by (induction s rule: code_from_stack.induct) auto

lemma encode_stack_to_return [dest]: "code_from_stack s = TReturn # cd \<Longrightarrow> 
    \<exists>cs s'. s = CReturn cs # s' \<and> cd = code_from_stack s'"
  by (induction s rule: code_from_stack.induct) auto
 
lemma encode_stack_to_jump [dest]: "code_from_stack s = TJump # cd \<Longrightarrow> False"
  by (induction s rule: code_from_stack.induct) auto

lemma encode_to_lookup [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> encode_state \<Sigma> = TS vs envs (TLookup x # cd) \<Longrightarrow> 
  (\<exists>s cs e es. \<Sigma> = CSE s cs e \<and> unzip e = (DVar x, es) \<and> cd = zip_encode es (code_from_stack s) \<and>
    vs = vals_from_stack s \<and> envs = envs_from_stack s) \<or> (\<exists>s c cs e es. 
      \<Sigma> = CSC (CApp1 cs e # s) c \<and> unzip e = (DVar x, es) \<and> envs = envs_from_stack s \<and>
        cd = zip_encode es (TApply # code_from_stack s) \<and> 
          vs = encode_closure c # vals_from_stack s)"
  by (induction \<Sigma> t rule: typecheck_closure_state.induct) auto

lemma encode_to_pushcon [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> encode_state \<Sigma> = TS vs envs (TPushCon k # cd) \<Longrightarrow> 
  (\<exists>s cs e es. \<Sigma> = CSE s cs e \<and> unzip e = (DConst k, es) \<and> cd = zip_encode es (code_from_stack s) \<and>
    vs = vals_from_stack s \<and> envs = envs_from_stack s) \<or> (\<exists>s c cs e es. 
      \<Sigma> = CSC (CApp1 cs e # s) c \<and> unzip e = (DConst k, es) \<and> envs = envs_from_stack s \<and>
        cd = zip_encode es (TApply # code_from_stack s) \<and> 
          vs = encode_closure c # vals_from_stack s)"
  by (induction \<Sigma> t rule: typecheck_closure_state.induct) auto

lemma encode_to_pushlam [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> encode_state \<Sigma> = TS vs envs (TPushLam cd' # cd) \<Longrightarrow> 
  (\<exists>s cs e es tt e'. \<Sigma> = CSE s cs e \<and> unzip e = (DLam tt e', es) \<and> 
    cd = zip_encode es (code_from_stack s) \<and> cd' = encode e' \<and> vs = vals_from_stack s \<and> 
      envs = envs_from_stack s) \<or> (\<exists>s c cs e es tt e'. \<Sigma> = CSC (CApp1 cs e # s) c \<and> 
        unzip e = (DLam tt e', es) \<and> cd = zip_encode es (TApply # code_from_stack s) \<and> 
          cd' = encode e' \<and> vs = encode_closure c # vals_from_stack s \<and> 
            envs = envs_from_stack s)"
proof (induction \<Sigma> t rule: typecheck_closure_state.induct)
  case (tcc_state_ev s t' t cs ts e)
  hence "encode' e (code_from_stack s) = TPushLam cd' # cd" by simp
  then obtain es tt e' where "unzip e = (DLam tt e', es) \<and> cd' = encode e'  \<and> 
    cd = zip_encode es (code_from_stack s)" by (metis encode_to_pushlam')
  with tcc_state_ev show ?case by fastforce
next
  case (tcc_state_ret s t' t c)
  moreover then obtain cs e es s' tt e' where "s = CApp1 cs e # s' \<and> unzip e = (DLam tt e', es) \<and>
    cd = zip_encode es (TApply # code_from_stack s') \<and> cd' = encode e'" 
      using encode_stack_to_pushlam by auto
  ultimately show ?case by fastforce
qed

lemma encode_to_apply [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> encode_state \<Sigma> = TS vs envs (TApply # cd) \<Longrightarrow> 
  \<exists>s c c'. \<Sigma> = CSC (CApp2 c' # s) c \<and> cd = code_from_stack s \<and> envs = envs_from_stack s \<and> 
    vs = encode_closure c # encode_closure c' # vals_from_stack s"
  by (induction \<Sigma> t rule: typecheck_closure_state.induct) auto

lemma encode_to_return [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> encode_state \<Sigma> = TS vs envs (TReturn # cd) \<Longrightarrow> 
  \<exists>cs s c. \<Sigma> = CSC (CReturn cs # s) c \<and> cd = code_from_stack s \<and> 
    envs = map encode_closure cs # envs_from_stack s \<and> vs = encode_closure c # vals_from_stack s"
  by (induction \<Sigma> t rule: typecheck_closure_state.induct) auto

lemma encode_to_jump [simp]: "\<Sigma> :\<^sub>c t \<Longrightarrow> encode_state \<Sigma> = TS vs envs (TJump # cd) \<Longrightarrow> False"
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

lemma [simp]: "env # envs = envs_from_stack s \<Longrightarrow> latest_environment s = Some cs \<Longrightarrow> 
    env = map encode_closure cs"
  by (induction s rule: latest_environment.induct) simp_all

theorem correctt [simp]: "encode_state \<Sigma>\<^sub>c \<leadsto>\<^sub>t \<Sigma>\<^sub>t' \<Longrightarrow> \<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>c'. iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> \<Sigma>\<^sub>t' = encode_state \<Sigma>\<^sub>c'"
proof (induction "encode_state \<Sigma>\<^sub>c" \<Sigma>\<^sub>t' rule: evalt.induct)
  case (evt_lookup env x v vs envs cd)
  moreover hence "(\<exists>s cs e es. \<Sigma>\<^sub>c = CSE s cs e \<and> unzip e = (DVar x, es) \<and> 
    cd = zip_encode es (code_from_stack s) \<and> vs = vals_from_stack s \<and> 
      env # envs = envs_from_stack s) \<or> (\<exists>s c cs e es. \<Sigma>\<^sub>c = CSC (CApp1 cs e # s) c \<and> 
        unzip e = (DVar x, es) \<and> env # envs = envs_from_stack s \<and> 
          cd = zip_encode es (TApply # code_from_stack s) \<and> 
            vs = encode_closure c # vals_from_stack s)" using encode_to_lookup by simp
  ultimately show ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    then obtain es where E: "unzip e = (DVar x, es) \<and> cd = zip_encode es (code_from_stack s) \<and>
      vs = vals_from_stack s \<and> env # envs = envs_from_stack s" by auto 
    hence X: "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSE (map (CApp1 cs) (rev es) @ s) cs (DVar x))" by simp
    from CSE obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and>
      latest_environment s = Some cs \<and> (ts \<turnstile>\<^sub>d e : t')" by fastforce
    with E have "env = map encode_closure cs" by fastforce
    with CSE obtain c where C: "lookup cs x = Some c \<and> encode_closure c = v" by fastforce
    with X have "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSC (map (CApp1 cs) (rev es) @ s) c)" by simp
    with E C show ?case by fastforce
  next
    case (CSC s c)
    then obtain s' cs e es where S: "s = CApp1 cs e # s' \<and> 
      unzip e = (DVar x, es) \<and> env # envs = envs_from_stack s' \<and> 
        cd = zip_encode es (TApply # code_from_stack s') \<and> 
          vs = encode_closure c # vals_from_stack s'" by auto
    hence "iter (\<leadsto>\<^sub>c) (CSE (CApp2 c # s') cs e) 
      (CSE (map (CApp1 cs) (rev es) @ CApp2 c # s') cs (DVar x))" by simp
    moreover have "CSC (CApp1 cs e # s') c \<leadsto>\<^sub>c CSE (CApp2 c # s') cs e" by simp
    ultimately have X: "iter (\<leadsto>\<^sub>c) (CSC (CApp1 cs e # s') c) 
      (CSE (map (CApp1 cs) (rev es) @ CApp2 c # s') cs (DVar x))" by (metis iter_step)
    from CSC obtain t' where "(s :\<^sub>c t' \<rightarrow> t) \<and> (c :\<^sub>c\<^sub>l t')" by fastforce
    with S obtain ts t\<^sub>1 t\<^sub>2 where "t' = Arrow t\<^sub>1 t\<^sub>2 \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (ts \<turnstile>\<^sub>d e : t\<^sub>1) \<and> (s' :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> 
      latest_environment s' = Some cs" by fastforce
    with S have "env = map encode_closure cs" by fastforce
    with CSC obtain c' where C: "lookup cs x = Some c' \<and> encode_closure c' = v" by fastforce
    with X have "iter (\<leadsto>\<^sub>c) (CSC (CApp1 cs e # s') c) 
      (CSC (map (CApp1 cs) (rev es) @ CApp2 c # s') c')" by simp
    with S C show ?case by fastforce
  qed
next
  case (evt_pushcon vs envs k cd)
  hence "(\<exists>s cs e es. \<Sigma>\<^sub>c = CSE s cs e \<and> unzip e = (DConst k, es) \<and> 
    cd = zip_encode es (code_from_stack s) \<and> vs = vals_from_stack s \<and> envs = envs_from_stack s) \<or> 
      (\<exists>s c cs e es. \<Sigma>\<^sub>c = CSC (CApp1 cs e # s) c \<and> unzip e = (DConst k, es) \<and> 
        envs = envs_from_stack s \<and> cd = zip_encode es (TApply # code_from_stack s) \<and> 
          vs = encode_closure c # vals_from_stack s)" using encode_to_pushcon by simp
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    then obtain es where E: "unzip e = (DConst k, es) \<and> cd = zip_encode es (code_from_stack s) \<and> 
      vs = vals_from_stack s \<and> envs = envs_from_stack s" by auto
    hence "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSE (map (CApp1 cs) (rev es) @ s) cs (DConst k))" by simp
    moreover have "CSE (map (CApp1 cs) (rev es) @ s) cs (DConst k) \<leadsto>\<^sub>c 
      CSC (map (CApp1 cs) (rev es) @ s) (CConst k)" by simp
    ultimately have "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSC (map (CApp1 cs) (rev es) @ s) (CConst k))" by simp
    with E show ?case by fastforce
  next
    case (CSC s c)
    then obtain s' cs e es where S: "s = CApp1 cs e # s' \<and> unzip e = (DConst k, es) \<and> 
        envs = envs_from_stack s' \<and> cd = zip_encode es (TApply # code_from_stack s') \<and> 
          vs = encode_closure c # vals_from_stack s'" by auto
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
    moreover hence "encode_state (CSE s cs e) = TS vs (env # envs) (TPushLam cd' # cd)" by simp
    ultimately obtain es tt e' where E: "unzip e = (DLam tt e', es) \<and> 
      cd = zip_encode es (code_from_stack s) \<and> cd' = encode e' \<and> 
        vs = vals_from_stack s \<and> env # envs = envs_from_stack s" using encode_to_pushlam by blast
    hence "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSE (map (CApp1 cs) (rev es) @ s) cs (DLam tt e'))" by simp
    moreover have "CSE (map (CApp1 cs) (rev es) @ s) cs (DLam tt e') \<leadsto>\<^sub>c 
      CSC (map (CApp1 cs) (rev es) @ s) (CLam tt cs e')" by simp
    ultimately have "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSC (map (CApp1 cs) (rev es) @ s) (CLam tt cs e'))"
      by (metis iter_step_after)
    with CSE E show ?case by fastforce
  next
    case (CSC s c)
    moreover hence "encode_state (CSC s c) = TS vs (env # envs) (TPushLam cd' # cd)" by simp
    ultimately obtain s' cs e es tt e' where S: "s = CApp1 cs e # s' \<and> unzip e = (DLam tt e', es) \<and> 
      cd = zip_encode es (TApply # code_from_stack s') \<and> cd' = encode e' \<and> 
        vs = encode_closure c # vals_from_stack s' \<and> env # envs = envs_from_stack s'" 
      using encode_to_pushlam by blast
    hence "iter (\<leadsto>\<^sub>c) (CSE (CApp2 c # s') cs e) 
      (CSE (map (CApp1 cs) (rev es) @ CApp2 c # s') cs (DLam tt e'))" by simp
    moreover have "CSC (CApp1 cs e # s') c \<leadsto>\<^sub>c CSE (CApp2 c # s') cs e" by simp
    moreover have "CSE (map (CApp1 cs) (rev es) @ CApp2 c # s') cs (DLam tt e') \<leadsto>\<^sub>c 
      CSC (map (CApp1 cs) (rev es) @ CApp2 c # s') (CLam tt cs e')" by simp
    ultimately have "iter (\<leadsto>\<^sub>c) (CSC (CApp1 cs e # s') c) 
      (CSC (map (CApp1 cs) (rev es) @ CApp2 c # s') (CLam tt cs e'))" 
        by (metis iter_step iter_step_after)
    with CSC S show ?case by fastforce
  qed
next
  case (evt_apply v env cd' vs envs cd)
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    moreover hence "encode_state (CSE s cs e) = TS (v # TLam env cd' # vs) envs (TApply # cd)"
      by simp
    ultimately show ?case using encode_to_apply by blast
  next
    case (CSC s c)
    moreover hence "encode_state (CSC s c) = TS (v # TLam env cd' # vs) envs (TApply # cd)" by simp
    ultimately obtain s' c' where S: "s = CApp2 c' # s' \<and> cd = code_from_stack s' \<and> 
      envs = envs_from_stack s' \<and> v = encode_closure c \<and> TLam env cd' = encode_closure c' \<and> 
        vs = vals_from_stack s'" using encode_to_apply by blast
    then obtain t cs e where C: "c' = CLam t cs e \<and> env = map encode_closure cs \<and> cd' = encode e" 
      by (metis encode_lam_closure)
    have "CSC (CApp2 (CLam t cs e) # s') c \<leadsto>\<^sub>c CSE (CReturn (c # cs) # s') (c # cs) e" by simp
    hence "iter (\<leadsto>\<^sub>c) (CSC (CApp2 (CLam t cs e) # s') c) (CSE (CReturn (c # cs) # s') (c # cs) e)" 
      by (metis iter_step iter_refl)
    with S C show ?case using encode_def by fastforce
  qed
next
  case (evt_return vs env envs cd)
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    moreover hence "encode_state (CSE s cs e) = TS vs (env # envs) (TReturn # cd)" by simp
    ultimately show ?case using encode_to_return by blast
  next
    case (CSC s c)
    moreover hence "encode_state (CSC s c) = TS vs (env # envs) (TReturn # cd)" by simp
    ultimately obtain cs s' where S: "s = CReturn cs # s' \<and> cd = code_from_stack s' \<and> 
      env = map encode_closure cs \<and> envs = envs_from_stack s' \<and> 
        vs = encode_closure c # vals_from_stack s'" using encode_to_return by blast
    have "CSC (CReturn cs # s') c \<leadsto>\<^sub>c CSC s' c" by simp
    hence "iter (\<leadsto>\<^sub>c) (CSC (CReturn cs # s') c) (CSC s' c)" by (metis iter_step iter_refl)
    with S show ?case by fastforce
  qed
next
  case (evt_jump v env' cd' vs env envs cd)
  thus ?case by (metis encode_to_jump)
qed

lemma lookup_latest [simp]: "latest_environment s = Some cs \<Longrightarrow> 
    \<exists>envs. envs_from_stack s = map encode_closure cs # envs"
  by (induction s rule: envs_from_stack.induct) simp_all

theorem completet [simp]: "\<Sigma> \<leadsto>\<^sub>c \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow> iter (\<leadsto>\<^sub>t) (encode_state \<Sigma>) (encode_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: evalc.induct)
  case (evc_var cs x c s)
  then obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs \<and> 
    lookup ts x = Some t'" by fastforce
  then obtain envs where "envs_from_stack s = map encode_closure cs # envs" 
    by (metis lookup_latest)
  with evc_var have "TS (vals_from_stack s) (envs_from_stack s) (TLookup x # code_from_stack s) \<leadsto>\<^sub>t 
    TS (encode_closure c # vals_from_stack s) (envs_from_stack s) (code_from_stack s)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS (vals_from_stack s) (envs_from_stack s) (TLookup x # code_from_stack s)) 
    (TS (encode_closure c # vals_from_stack s) (envs_from_stack s) (code_from_stack s))" 
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
  then obtain envs where "envs_from_stack s = map encode_closure cs # envs" 
    by (metis lookup_latest)
  hence "TS (vals_from_stack s) (envs_from_stack s) (TPushLam (encode e) # code_from_stack s) \<leadsto>\<^sub>t 
    TS (TLam (map encode_closure cs) (encode e) # vals_from_stack s) (envs_from_stack s) 
      (code_from_stack s)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS (vals_from_stack s) (envs_from_stack s) (TPushLam (encode e) # 
    code_from_stack s)) (TS (TLam (map encode_closure cs) (encode e) #
      vals_from_stack s) (envs_from_stack s) (code_from_stack s))" by (metis iter_step iter_refl)
  thus ?case by (simp add: encode_def)
next
  case (retc_app2 t cs e\<^sub>1 s c\<^sub>2)
  have "iter (\<leadsto>\<^sub>t) (TS (encode_closure c\<^sub>2 # TLam (map encode_closure cs) 
    (encode e\<^sub>1) # vals_from_stack s) (envs_from_stack s) (TApply # code_from_stack s))
      (TS (vals_from_stack s) ((encode_closure c\<^sub>2 # map encode_closure cs) # envs_from_stack s) 
      (encode e\<^sub>1 @ code_from_stack s))" by (metis evt_apply iter_step iter_refl)
  thus ?case by (simp add: encode_def)
next
  case (retc_ret cs s c)
  have "TS (encode_closure c # vals_from_stack s) (map encode_closure cs # envs_from_stack s) 
    (TReturn # code_from_stack s) \<leadsto>\<^sub>t TS (encode_closure c # vals_from_stack s) (envs_from_stack s) 
      (code_from_stack s)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS (encode_closure c # vals_from_stack s) 
    (map encode_closure cs # envs_from_stack s) (TReturn # code_from_stack s)) 
      (TS (encode_closure c # vals_from_stack s) (envs_from_stack s) (code_from_stack s))" 
        by (metis iter_step iter_refl)
  thus ?case by simp
qed simp_all

lemma iter_completet [simp]: "iter (\<leadsto>\<^sub>c) \<Sigma> \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow>
  iter (\<leadsto>\<^sub>t) (encode_state \<Sigma>) (encode_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: iter.induct)
  case (iter_step \<Sigma> \<Sigma>' \<Sigma>'')
  hence "iter (\<leadsto>\<^sub>t) (encode_state \<Sigma>) (encode_state \<Sigma>')" by simp
  moreover from iter_step have "iter (\<leadsto>\<^sub>t) (encode_state \<Sigma>') (encode_state \<Sigma>'')" by simp
  ultimately show ?case by (metis iter_append)
qed simp_all

end