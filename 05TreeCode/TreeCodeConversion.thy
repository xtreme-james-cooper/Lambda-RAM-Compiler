theory TreeCodeConversion
  imports TreeCode "../04Closure/Closure"
begin

primrec encode' :: "dexpr \<Rightarrow> nat \<Rightarrow>  tree_code list \<Rightarrow> tree_code list" where
  "encode' (DVar x) d cd = TLookup x # cd"
| "encode' (DConst k) d cd = TPushCon k # cd"
| "encode' (DLam t e) d cd = TPushLam (encode' e (Suc d) []) d # cd"
| "encode' (DApp e\<^sub>1 e\<^sub>2) d cd = encode' e\<^sub>1 d (encode' e\<^sub>2 d (TApply # cd))"

definition encode :: "dexpr \<Rightarrow> tree_code list" where
  "encode e = encode' e 0 []"

primrec encode_closure :: "closure \<Rightarrow> tclosure" where
  "encode_closure (CConst k) = TConst k"
| "encode_closure (CLam t cs e) = TLam (map encode_closure cs) (encode' e (Suc (length cs)) [])"

fun vals_from_stack :: "cframe list \<Rightarrow> tclosure list" where
  "vals_from_stack [] = []"
| "vals_from_stack (CApp1 cs e # s) = vals_from_stack s"
| "vals_from_stack (CApp2 c # s) = encode_closure c # vals_from_stack s"
| "vals_from_stack (CReturn cs # s) = vals_from_stack s"

fun stack_from_stack :: "cframe list \<Rightarrow> tree_stack_frame list" where
  "stack_from_stack [] = []"
| "stack_from_stack (CApp1 cs e # s) = (case stack_from_stack s of
      [] \<Rightarrow> []
    | ((env, cd) # sfs) \<Rightarrow> (env, encode' e (length env) (TApply # cd)) # sfs)"
| "stack_from_stack (CApp2 c # s) = (case stack_from_stack s of
      [] \<Rightarrow> []
    | ((env, cd) # sfs) \<Rightarrow> (env, TApply # cd) # sfs)"
| "stack_from_stack (CReturn cs # s) = (map encode_closure cs, []) # stack_from_stack s"

primrec encode_state :: "closure_state \<Rightarrow> tree_code_state" where
  "encode_state (CSE s cs e) = 
    TS (vals_from_stack s) (case stack_from_stack s of 
        [] \<Rightarrow> []
      | ((env, cd) # sfs) \<Rightarrow> ((env, encode' e (length env) cd) # sfs))"
| "encode_state (CSC s c) = 
    TS (encode_closure c # vals_from_stack s) (stack_from_stack s)"

primrec unzip :: "dexpr \<Rightarrow> dexpr \<times> dexpr list" where
  "unzip (DVar x) = (DVar x, [])"
| "unzip (DConst k) = (DConst k, [])"
| "unzip (DLam t e) = (DLam t e, [])"
| "unzip (DApp e\<^sub>1 e\<^sub>2) = (case unzip e\<^sub>1 of (e, es) \<Rightarrow> (e, e\<^sub>2 # es))"

primrec zip_encode :: "dexpr list \<Rightarrow> nat \<Rightarrow> tree_code list \<Rightarrow> tree_code list" where 
  "zip_encode [] d acc = acc"
| "zip_encode (e # es) d acc = zip_encode es d (encode' e d (TApply # acc))"

lemma [simp]: "encode' e d cd @ cd' = encode' e d (cd @ cd')"
  by (induction e arbitrary: d cd) simp_all

lemma [simp]: "unzip e = (e', es) \<Longrightarrow> encode' e' d (zip_encode es d acc) = encode' e d acc"
  by (induction e arbitrary: e' es d acc) (auto split: prod.splits)

lemma [simp]: "vals_from_stack (map (CApp1 cs) (rev es) @ s) = vals_from_stack s"
  by (induction es arbitrary: s) simp_all

lemma [simp]: "stack_from_stack s = (env, cd) # sfs \<Longrightarrow> 
    stack_from_stack (map (CApp1 cs) (rev es) @ s) = (env, zip_encode es (length env) cd) # sfs"
  by (induction es arbitrary: s cd) simp_all

lemma [dest]: "encode' e d cd' = TLookup x # cd \<Longrightarrow> 
    (\<And>es. unzip e = (DVar x, es) \<Longrightarrow> cd = zip_encode es d cd' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction e arbitrary: cd') fastforce+

lemma [dest]: "encode' e d cd' = TPushCon k # cd \<Longrightarrow> 
    (\<And>es. unzip e = (DConst k, es) \<Longrightarrow> cd = zip_encode es d cd' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction e arbitrary: cd') fastforce+

lemma encode_to_pushlam' [dest]: "encode' e d cd' = TPushLam cd'' d' # cd \<Longrightarrow> 
  (\<And>es t e'. unzip e = (DLam t e', es) \<Longrightarrow> cd'' = encode' e' (Suc d) [] \<Longrightarrow> 
    cd = zip_encode es d cd' \<Longrightarrow> d' = d \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction e arbitrary: cd') fastforce+

lemma [dest]: "encode' e d cd' = TApply # cd \<Longrightarrow> P"
  by (induction e arbitrary: cd') simp_all

lemma [dest]: "encode_closure c = TConst k \<Longrightarrow> c = CConst k"
  by (induction c) simp_all

lemma encode_lam_closure [dest]: "encode_closure c = TLam env cd \<Longrightarrow> (\<And>t cs e. 
  c = CLam t cs e \<Longrightarrow> env = map encode_closure cs \<Longrightarrow> cd = encode' e (Suc (length cs)) [] \<Longrightarrow> P) \<Longrightarrow> 
    P"
  by (induction c) simp_all

lemma tc_latest_environment [simp]: "s @ CApp1 cs e # s' :\<^sub>c t \<rightarrow> t' \<Longrightarrow> 
  latest_environment s' = Some cs"
proof (induction s arbitrary: t)
  case (Cons f s)
  moreover from Cons(2) obtain tt where "s @ CApp1 cs e # s' :\<^sub>c tt \<rightarrow> t'" 
    by (induction "(f # s) @ CApp1 cs e # s'" t t' rule: typecheck_cstack.induct) simp_all
  ultimately show ?case by simp
qed fastforce+

lemma [dest]: "encode' e d cd = [] \<Longrightarrow> P"
  by (induction e arbitrary: cd) simp_all

lemma encode_stack_to_lookup [dest]: "stack_from_stack s = (env, TLookup x # cd) # sfs \<Longrightarrow> 
  \<exists>cs e es s' cd'. s = CApp1 cs e # s' \<and> stack_from_stack s' = (env, cd') # sfs \<and> 
    unzip e = (DVar x, es) \<and> cd = zip_encode es (length env) (TApply # cd')"
proof (induction s rule: stack_from_stack.induct)
  case (2 cs e s)
  then obtain cd' where "stack_from_stack s = (env, cd') # sfs \<and> 
    encode' e (length env) (TApply # cd') = TLookup x # cd" 
      by (cases "stack_from_stack s") (auto split: prod.splits)
  thus ?case by auto
qed (auto split: list.splits)

lemma encode_stack_to_pushcon [dest]: "stack_from_stack s = (env, TPushCon k # cd) # sfs \<Longrightarrow> 
  \<exists>cs e es s' cd'. s = CApp1 cs e # s' \<and> stack_from_stack s' = (env, cd') # sfs \<and> 
    unzip e = (DConst k, es) \<and> cd = zip_encode es (length env) (TApply # cd')"
proof (induction s rule: stack_from_stack.induct)
  case (2 cs e s)
  then obtain cd' where "stack_from_stack s = (env, cd') # sfs \<and> 
    encode' e (length env) (TApply # cd') = TPushCon k # cd" 
      by (cases "stack_from_stack s") (auto split: prod.splits)
  thus ?case by auto
qed (auto split: list.splits)

lemma encode_stack_to_pushlam [dest]: "stack_from_stack s = (env, TPushLam cd' d # cd) # sfs \<Longrightarrow> 
  \<exists>cs e es s' t e' cd''. s = CApp1 cs e # s' \<and> stack_from_stack s' = (env, cd'') # sfs \<and> 
    unzip e = (DLam t e', es) \<and> cd = zip_encode es d (TApply # cd'') \<and> 
      cd' = encode' e' (Suc d) [] \<and> d = length env"
proof (induction s rule: stack_from_stack.induct)
  case (2 cs e s)
  then obtain cd'' where "stack_from_stack s = (env, cd'') # sfs \<and> 
    encode' e d (TApply # cd'') = TPushLam cd' d # cd \<and> d = length env" 
      by (cases "stack_from_stack s") (auto split: prod.splits)
  moreover then obtain t e' es where "unzip e = (DLam t e', es) \<and> cd' = encode' e' (Suc d) [] \<and> 
    cd = zip_encode es d (TApply # cd'')" by (metis encode_to_pushlam')
  ultimately show ?case by fastforce
qed (auto split: list.splits)

lemma encode_stack_to_apply [dest]: "stack_from_stack s = (env, TApply # cd) # sfs \<Longrightarrow> 
    \<exists>s' c. s = CApp2 c # s' \<and> stack_from_stack s' = (env, cd) # sfs"
  by (induction s rule: stack_from_stack.induct) (auto split: list.splits)

lemma encode_stack_to_return [dest]: "stack_from_stack s = (env, []) # sfs \<Longrightarrow> 
  (s = [] \<and> env = [] \<and>  sfs = []) \<or> (\<exists>cs s'. s = CReturn cs # s' \<and> env = map encode_closure cs \<and> 
    sfs = stack_from_stack s')"
  by (induction s rule: stack_from_stack.induct) (auto split: list.splits)

lemma encode_to_lookup [simp]: "encode_state \<Sigma> = TS vs ((env, TLookup x # cd) # sfs) \<Longrightarrow> 
  (\<exists>s cs e es cd'. \<Sigma> = CSE s cs e \<and> unzip e = (DVar x, es) \<and> cd = zip_encode es (length env) cd' \<and>
    stack_from_stack s = ((env, cd') # sfs) \<and> vs = vals_from_stack s) \<or> 
      (\<exists>s c cs e es cd'. \<Sigma> = CSC (CApp1 cs e # s) c \<and> unzip e = (DVar x, es) \<and>
        cd = zip_encode es (length env) (TApply # cd') \<and> stack_from_stack s = ((env, cd') # sfs) \<and>
          vs = encode_closure c # vals_from_stack s)"
proof (induction \<Sigma>)
  case (CSE s cs e)
  moreover then obtain cd' where "stack_from_stack s = (env, cd') # sfs \<and> 
    encode' e (length env) cd' = TLookup x # cd" by (auto split: list.splits)
  ultimately show ?case by auto
qed auto

lemma encode_to_pushcon [simp]: "encode_state \<Sigma> = TS vs ((env, TPushCon k # cd) # sfs) \<Longrightarrow> 
  (\<exists>s cs e es cd'. \<Sigma> = CSE s cs e \<and> unzip e = (DConst k, es) \<and> 
    cd = zip_encode es (length env) cd' \<and> stack_from_stack s = ((env, cd') # sfs) \<and> 
      vs = vals_from_stack s) \<or> (\<exists>s c cs e es cd'. \<Sigma> = CSC (CApp1 cs e # s) c \<and> 
        unzip e = (DConst k, es) \<and> cd = zip_encode es (length env) (TApply # cd') \<and> 
          stack_from_stack s = ((env, cd') # sfs) \<and> vs = encode_closure c # vals_from_stack s)"
proof (induction \<Sigma>)
  case (CSE s cs e)
  moreover then obtain cd' where "stack_from_stack s = (env, cd') # sfs \<and> 
    encode' e (length env) cd' = TPushCon k # cd" by (auto split: list.splits)
  ultimately show ?case by auto
qed auto

lemma encode_to_pushlam [simp]: "encode_state \<Sigma> = TS vs ((env, TPushLam cd' d # cd) # sfs) \<Longrightarrow> 
  (\<exists>s cs e es tt e' cd''. \<Sigma> = CSE s cs e \<and> d = length env \<and> unzip e = (DLam tt e', es) \<and> 
    cd = zip_encode es d cd'' \<and> cd' = encode' e' (Suc d) [] \<and> vs = vals_from_stack s \<and> 
      stack_from_stack s = ((env, cd'') # sfs)) \<or> (\<exists>s c cs e es tt e' cd''. 
        \<Sigma> = CSC (CApp1 cs e # s) c \<and> d = length env \<and> unzip e = (DLam tt e', es) \<and> 
          cd = zip_encode es d (TApply # cd'') \<and> cd' = encode' e' (Suc d) [] \<and> 
            vs = encode_closure c # vals_from_stack s \<and> stack_from_stack s = ((env, cd'') # sfs))"
proof (induction \<Sigma>)
  case (CSE s cs e)
  moreover then obtain cd'' where "stack_from_stack s = (env, cd'') # sfs \<and> d = length env \<and>
    encode' e d cd'' = TPushLam cd' d # cd" by (auto split: list.splits)
  moreover then obtain es tt e' where "unzip e = (DLam tt e', es) \<and> cd' = encode' e' (Suc d) [] \<and> 
    cd = zip_encode es d cd''" by (metis encode_to_pushlam')
  ultimately show ?case by auto
qed auto

lemma encode_to_apply [simp]: "encode_state \<Sigma> = TS vs ((env, TApply # cd) # sfs) \<Longrightarrow> 
  \<exists>s c c'. \<Sigma> = CSC (CApp2 c' # s) c \<and> stack_from_stack s = ((env, cd) # sfs) \<and> 
    vs = encode_closure c # encode_closure c' # vals_from_stack s"
  by (induction \<Sigma>) (auto split: list.splits)

lemma encode_to_return [simp]: "encode_state \<Sigma> = TS vs ((env, []) # sfs) \<Longrightarrow> 
  (\<exists>c. \<Sigma> = CSC [] c \<and> env = [] \<and> sfs = [] \<and> vs = [encode_closure c]) \<or> 
    (\<exists>cs s c. \<Sigma> = CSC (CReturn cs # s) c \<and> sfs = stack_from_stack s \<and>
      env = map encode_closure cs \<and> vs = encode_closure c # vals_from_stack s)"
  by (induction \<Sigma>) (auto split: list.splits)

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

lemma [simp]: "stack_from_stack s = (env, cd) # sfs \<Longrightarrow> latest_environment s = Some cs \<Longrightarrow> 
    env = map encode_closure cs"
  by (induction s arbitrary: cd rule: latest_environment.induct) 
     (simp_all split: list.splits prod.splits)

theorem correctt [simp]: "encode_state \<Sigma>\<^sub>c \<leadsto>\<^sub>t \<Sigma>\<^sub>t' \<Longrightarrow> \<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>c'. iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> \<Sigma>\<^sub>t' = encode_state \<Sigma>\<^sub>c'"
proof (induction "encode_state \<Sigma>\<^sub>c" \<Sigma>\<^sub>t' rule: evalt.induct)
  case (evt_lookup env x v vs cd sfs)
  moreover hence "(\<exists>s cs e es cd'. \<Sigma>\<^sub>c = CSE s cs e \<and> unzip e = (DVar x, es) \<and> 
    cd = zip_encode es (length env) cd' \<and> stack_from_stack s = ((env, cd') # sfs) \<and> 
      vs = vals_from_stack s) \<or> (\<exists>s c cs e es cd'. \<Sigma>\<^sub>c = CSC (CApp1 cs e # s) c \<and> 
        unzip e = (DVar x, es) \<and> cd = zip_encode es (length env) (TApply # cd') \<and> 
          stack_from_stack s = ((env, cd') # sfs) \<and> vs = encode_closure c # vals_from_stack s)" 
    using encode_to_lookup by simp
  ultimately show ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    then obtain es cd' where E: "unzip e = (DVar x, es) \<and> cd = zip_encode es (length env) cd' \<and>
      stack_from_stack s = ((env, cd') # sfs) \<and> vs = vals_from_stack s" by auto 
    hence X: "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSE (map (CApp1 cs) (rev es) @ s) cs (DVar x))" by simp
    from CSE obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and>
      latest_environment s = Some cs \<and> (ts \<turnstile>\<^sub>d e : t')" by fastforce
    with E have "env = map encode_closure cs" by fastforce
    with CSE obtain c where C: "lookup cs x = Some c \<and> encode_closure c = v" by fastforce
    with X have "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSC (map (CApp1 cs) (rev es) @ s) c)" by simp
    with E C show ?case by fastforce
  next
    case (CSC s c)
    then obtain s' cs e es cd' where S: "s = CApp1 cs e # s' \<and> unzip e = (DVar x, es) \<and>
        cd = zip_encode es (length env) (TApply # cd') \<and> stack_from_stack s' = ((env, cd') # sfs) \<and>
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
  case (evt_pushcon vs env k cd sfs)
  hence "(\<exists>s cs e es cd'. \<Sigma>\<^sub>c = CSE s cs e \<and> unzip e = (DConst k, es) \<and> 
    cd = zip_encode es (length env) cd' \<and>stack_from_stack s = ((env, cd') # sfs) \<and> 
      vs = vals_from_stack s) \<or> (\<exists>s c cs e es cd'. \<Sigma>\<^sub>c = CSC (CApp1 cs e # s) c \<and> 
        unzip e = (DConst k, es) \<and> cd = zip_encode es (length env) (TApply # cd') \<and>
          stack_from_stack s = ((env, cd') # sfs) \<and> vs = encode_closure c # vals_from_stack s)" 
    using encode_to_pushcon by simp
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    then obtain es cd' where E: "unzip e = (DConst k, es) \<and> cd = zip_encode es (length env) cd' \<and> 
      stack_from_stack s = ((env, cd') # sfs) \<and> vs = vals_from_stack s" by auto
    hence "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSE (map (CApp1 cs) (rev es) @ s) cs (DConst k))" by simp
    moreover have "CSE (map (CApp1 cs) (rev es) @ s) cs (DConst k) \<leadsto>\<^sub>c 
      CSC (map (CApp1 cs) (rev es) @ s) (CConst k)" by simp
    ultimately have "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSC (map (CApp1 cs) (rev es) @ s) (CConst k))" by simp
    with E show ?case by fastforce
  next
    case (CSC s c)
    then obtain s' cs e es cd' where S: "s = CApp1 cs e # s' \<and> unzip e = (DConst k, es) \<and> 
        cd = zip_encode es (length env) (TApply # cd') \<and> stack_from_stack s' = ((env, cd') # sfs) \<and>
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
  case (evt_pushlam vs env cd' cd sfs)
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (CSE s cs e)
    hence "encode_state (CSE s cs e) = TS vs ((env, TPushLam cd' (length env) # cd) # sfs)" by simp
    then obtain es tt e' cd'' where E: "unzip e = (DLam tt e', es) \<and> 
      cd = zip_encode es (length env) cd'' \<and> cd' = encode' e' (Suc (length env)) [] \<and> 
        vs = vals_from_stack s \<and> stack_from_stack s = ((env, cd'') # sfs)" 
      using encode_to_pushlam by blast
    hence "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSE (map (CApp1 cs) (rev es) @ s) cs (DLam tt e'))" by simp
    moreover have "CSE (map (CApp1 cs) (rev es) @ s) cs (DLam tt e') \<leadsto>\<^sub>c 
      CSC (map (CApp1 cs) (rev es) @ s) (CLam tt cs e')" by simp
    ultimately have X: "iter (\<leadsto>\<^sub>c) (CSE s cs e) (CSC (map (CApp1 cs) (rev es) @ s) (CLam tt cs e'))"
      by (metis iter_step_after)
    from CSE E have "env = map encode_closure cs" by fastforce
    with CSE E X show ?case by fastforce
  next
    case (CSC s c)
    hence "encode_state (CSC s c) = TS vs ((env, TPushLam cd' (length env) # cd) # sfs)" by simp
    then obtain s' cs e es tt e' cd'' where S: "s = CApp1 cs e # s' \<and> 
      unzip e = (DLam tt e', es) \<and> cd = zip_encode es (length env) (TApply # cd'') \<and> 
        cd' = encode' e' (Suc (length env)) [] \<and> vs = encode_closure c # vals_from_stack s' \<and> 
          stack_from_stack s' = ((env, cd'') # sfs)" 
      using encode_to_pushlam by fastforce
    hence "iter (\<leadsto>\<^sub>c) (CSE (CApp2 c # s') cs e) 
      (CSE (map (CApp1 cs) (rev es) @ CApp2 c # s') cs (DLam tt e'))" by simp
    moreover have "CSC (CApp1 cs e # s') c \<leadsto>\<^sub>c CSE (CApp2 c # s') cs e" by simp
    moreover have "CSE (map (CApp1 cs) (rev es) @ CApp2 c # s') cs (DLam tt e') \<leadsto>\<^sub>c 
      CSC (map (CApp1 cs) (rev es) @ CApp2 c # s') (CLam tt cs e')" by simp
    ultimately have X: "iter (\<leadsto>\<^sub>c) (CSC (CApp1 cs e # s') c) 
      (CSC (map (CApp1 cs) (rev es) @ CApp2 c # s') (CLam tt cs e'))" 
        by (metis iter_step iter_step_after)
    from CSC S have "env = map encode_closure cs" by fastforce
    with CSC S X show ?case by fastforce
  qed
next
  case (evt_apply v env' cd' vs env cd sfs)
  hence "encode_state \<Sigma>\<^sub>c = TS (v # TLam env' cd' # vs) ((env, TApply # cd) # sfs)" by simp
  then obtain s c c' where "\<Sigma>\<^sub>c = CSC (CApp2 c' # s) c \<and> 
    stack_from_stack s = ((env, cd) # sfs) \<and> v = encode_closure c \<and> 
      TLam env' cd' = encode_closure c' \<and> vs = vals_from_stack s" using encode_to_apply by blast
  moreover then obtain t cs e where "c' = CLam t cs e \<and> env' = map encode_closure cs \<and> 
    cd' = encode' e (Suc (length cs)) []" by (metis encode_lam_closure)
  moreover have "CSC (CApp2 (CLam t cs e) # s) c \<leadsto>\<^sub>c CSE (CReturn (c # cs) # s) (c # cs) e" by simp
  moreover hence "iter (\<leadsto>\<^sub>c) (CSC (CApp2 (CLam t cs e) # s) c) 
    (CSE (CReturn (c # cs) # s) (c # cs) e)" by (metis iter_one)
  ultimately show ?case using encode_def by fastforce
next
  case (evt_return vs env sfs)
  hence R: "(\<exists>c. \<Sigma>\<^sub>c = CSC [] c \<and> env = [] \<and> sfs = [] \<and> vs = [encode_closure c]) \<or> 
    (\<exists>cs s c. \<Sigma>\<^sub>c = CSC (CReturn cs # s) c \<and> sfs = stack_from_stack s \<and>
      env = map encode_closure cs \<and> vs = encode_closure c # vals_from_stack s)" by simp
  thus ?case
  proof (cases "\<exists>c. \<Sigma>\<^sub>c = CSC [] c \<and> env = [] \<and> sfs = [] \<and> vs = [encode_closure c]")
    case True
    then obtain c where "\<Sigma>\<^sub>c = CSC [] c \<and> env = [] \<and> sfs = [] \<and> vs = [encode_closure c]" 
      by fastforce
    moreover have "iter (\<leadsto>\<^sub>c) (CSC [] c) (CSC [] c)" by simp
    ultimately show ?thesis by fastforce
  next
    case False
    with R obtain cs s c where S: "\<Sigma>\<^sub>c = CSC (CReturn cs # s) c \<and> sfs = stack_from_stack s \<and>
      env = map encode_closure cs \<and> vs = encode_closure c # vals_from_stack s" by fastforce
    have "CSC (CReturn cs # s) c \<leadsto>\<^sub>c CSC s c" by simp
    hence "iter (\<leadsto>\<^sub>c) (CSC (CReturn cs # s) c) (CSC s c)" by (metis iter_one)
    with S show ?thesis by fastforce
  qed
qed

lemma lookup_latest [simp]: "latest_environment s = Some cs \<Longrightarrow> 
    \<exists>cd sfs. stack_from_stack s = (map encode_closure cs, cd) # sfs"
  by (induction s rule: stack_from_stack.induct) (auto split: list.splits)

theorem completet [simp]: "\<Sigma> \<leadsto>\<^sub>c \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow> iter (\<leadsto>\<^sub>t) (encode_state \<Sigma>) (encode_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: evalc.induct)
  case (evc_var cs x c s)
  then obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs \<and> 
    lookup ts x = Some t'" by fastforce
  then obtain cd sfs where S: "stack_from_stack s = (map encode_closure cs, cd) # sfs" 
    by (metis lookup_latest)
  with evc_var have "TS (vals_from_stack s) ((map encode_closure cs, TLookup x # cd) # sfs) \<leadsto>\<^sub>t 
    TS (encode_closure c # vals_from_stack s) ((map encode_closure cs, cd) # sfs)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS (vals_from_stack s) ((map encode_closure cs, TLookup x # cd) # sfs))
    (TS (encode_closure c # vals_from_stack s) ((map encode_closure cs, cd) # sfs))" 
      by (metis iter_one)
    with S show ?case by simp
next
  case (evc_con s cs k)
  then obtain ts where "(s :\<^sub>c Base \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs" 
    by fastforce
  then obtain cd sfs where S: "stack_from_stack s = (map encode_closure cs, cd) # sfs" 
    by (metis lookup_latest)
  have "TS (vals_from_stack s) ((map encode_closure cs, TPushCon k # cd) # sfs) \<leadsto>\<^sub>t 
    TS (TConst k # vals_from_stack s) ((map encode_closure cs, cd) # sfs)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS (vals_from_stack s) ((map encode_closure cs, TPushCon k # cd) # sfs)) 
    (TS (TConst k # vals_from_stack s) ((map encode_closure cs, cd) # sfs))" by (metis iter_one)
  with S show ?case by simp
next
  case (evc_lam s cs tt e)
  then obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs \<and>
    (ts \<turnstile>\<^sub>d DLam tt e : t')" by fastforce
  then obtain cd sfs where S: "stack_from_stack s = (map encode_closure cs, cd) # sfs" 
    by (metis lookup_latest)
  hence "TS (vals_from_stack s) ((map encode_closure cs, 
    TPushLam (encode' e (Suc (length cs)) []) (length cs) # cd) # sfs) \<leadsto>\<^sub>t 
      TS (TLam (map encode_closure cs) (encode' e (Suc (length cs)) []) # vals_from_stack s) 
        ((map encode_closure cs, cd) # sfs)" by (metis evt_pushlam length_map)
  hence "iter (\<leadsto>\<^sub>t) (TS (vals_from_stack s) 
    ((map encode_closure cs, TPushLam (encode' e (Suc (length cs)) []) (length cs) # cd) # sfs)) 
      (TS (TLam (map encode_closure cs) (encode' e (Suc (length cs)) []) # vals_from_stack s)
        ((map encode_closure cs, cd) # sfs))" by (metis iter_one)
  with S show ?case by (simp add: encode_def)
next
  case (evc_app s cs e\<^sub>1 e\<^sub>2)
  then obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs \<and>
    (ts \<turnstile>\<^sub>d DApp e\<^sub>1 e\<^sub>2 : t')" by fastforce
  then obtain cd sfs where S: "stack_from_stack s = (map encode_closure cs, cd) # sfs" 
    by (metis lookup_latest)
  then show ?case by simp
next
  case (retc_app1 cs e\<^sub>2 s c\<^sub>1)
  then obtain ts t\<^sub>1 t\<^sub>2 where "(cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (ts \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<and> (s :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and>
    latest_environment s = Some cs \<and> (c\<^sub>1 :\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2)" by blast
  then obtain cd sfs where "stack_from_stack s = (map encode_closure cs, cd) # sfs" 
    by (metis lookup_latest)
  thus ?case by simp
next
  case (retc_app2 t\<^sub>1 cs e\<^sub>1 s c\<^sub>2)
  then obtain ts t\<^sub>2 cs' where "(cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (insert_at 0 t\<^sub>1 ts \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2) \<and> (s :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> 
    latest_environment s = Some cs' \<and> (c\<^sub>2 :\<^sub>c\<^sub>l t\<^sub>1)" by blast
  then obtain cd sfs where S: "stack_from_stack s = (map encode_closure cs', cd) # sfs" 
    by (metis lookup_latest)
  hence "TS (encode_closure c\<^sub>2 # TLam (map encode_closure cs) (encode' e\<^sub>1 (Suc (length cs)) []) # 
    vals_from_stack s) ((map encode_closure cs', TApply # cd) # sfs) \<leadsto>\<^sub>t
      TS (vals_from_stack s) ((encode_closure c\<^sub>2 # map encode_closure cs, 
        encode' e\<^sub>1 (Suc (length cs)) []) # stack_from_stack s)" by (metis evt_apply)
  hence "iter (\<leadsto>\<^sub>t)
    (TS (encode_closure c\<^sub>2 # TLam (map encode_closure cs) (encode' e\<^sub>1 (Suc (length cs)) []) # 
      vals_from_stack s) ((map encode_closure cs', TApply # cd) # sfs))
        (TS (vals_from_stack s) ((encode_closure c\<^sub>2 # map encode_closure cs, 
          encode' e\<^sub>1 (Suc (length cs)) []) # stack_from_stack s))"
    by (metis iter_one)
  with S show ?case by (simp add: encode_def)
next
  case (retc_ret cs s c)
  have "TS (encode_closure c # vals_from_stack s) 
    ((map encode_closure cs, []) # stack_from_stack s) \<leadsto>\<^sub>t
      TS (encode_closure c # vals_from_stack s) (stack_from_stack s)" by simp
  hence "iter (\<leadsto>\<^sub>t) 
    (TS (encode_closure c # vals_from_stack s) ((map encode_closure cs, []) # stack_from_stack s))
      (TS (encode_closure c # vals_from_stack s) (stack_from_stack s))" by (metis iter_one)
  thus ?case by simp
qed

lemma iter_completet [simp]: "iter (\<leadsto>\<^sub>c) \<Sigma> \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow>
  iter (\<leadsto>\<^sub>t) (encode_state \<Sigma>) (encode_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: iter.induct)
  case (iter_step \<Sigma> \<Sigma>' \<Sigma>'')
  hence "iter (\<leadsto>\<^sub>t) (encode_state \<Sigma>) (encode_state \<Sigma>')" by simp
  moreover from iter_step have "iter (\<leadsto>\<^sub>t) (encode_state \<Sigma>') (encode_state \<Sigma>'')" by simp
  ultimately show ?case by (metis iter_append)
qed simp_all

end