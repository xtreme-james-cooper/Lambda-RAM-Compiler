theory TailCallOptimization
  imports TailCall "../06TreeCode/TreeCode" "../00Utils/Iteration"
begin

fun tco_r :: "tree_code list \<Rightarrow> tco_return" where
  "tco_r [] = TCOReturn"
| "tco_r (TApply # cd) = (case cd of 
      [] \<Rightarrow> TCOJump
    | _ \<Rightarrow> tco_r cd)"
| "tco_r (op # cd) = tco_r cd"

fun tco_cd :: "tree_code list \<Rightarrow> tco_code list" where
  "tco_cd [] = []"
| "tco_cd (TLookup x # cd) = TCOLookup x # tco_cd cd"
| "tco_cd (TPushCon k # cd) = TCOPushCon k # tco_cd cd"
| "tco_cd (TPushLam cd' # cd) = TCOPushLam (tco_cd cd') (tco_r cd') # tco_cd cd"
| "tco_cd (TApply # cd) = (case cd of 
      [] \<Rightarrow> []
    | _ \<Rightarrow> TCOApply # tco_cd cd)"

fun tco_cd_one :: "tree_code \<Rightarrow> tco_code" where
  "tco_cd_one (TLookup x) = TCOLookup x"
| "tco_cd_one (TPushCon k) = TCOPushCon k"
| "tco_cd_one (TPushLam cd') = TCOPushLam (tco_cd cd') (tco_r cd')"
| "tco_cd_one TApply = TCOApply"

definition tco :: "tree_code list \<Rightarrow> tco_code list \<times> tco_return" where
  "tco cd = (tco_cd cd, tco_r cd)"

primrec tco_val :: "tclosure \<Rightarrow> tco_closure" where
  "tco_val (TConst k) = TCOConst k"
| "tco_val (TLam vs cd) = TCOLam (map tco_val vs) (tco_cd cd) (tco_r cd)"

fun tco_stack_frame :: "tree_stack_frame \<Rightarrow> tco_stack_frame" where
  "tco_stack_frame (vs, cd) = (map tco_val vs, tco_cd cd, tco_r cd)"

fun live_frame :: "tco_stack_frame \<Rightarrow> bool" where
  "live_frame (vs, [], TCOReturn) = False"
| "live_frame (vs, [], TCOJump) = True"
| "live_frame (vs, op # cd, r) = True"

primrec dead_frame :: "tree_stack_frame \<Rightarrow> bool" where
  "dead_frame (vs, cd) = (cd = [])"

abbreviation tco_stack :: "tree_stack_frame list \<Rightarrow> tco_stack_frame list" where
  "tco_stack sfs \<equiv> filter live_frame (map tco_stack_frame sfs)"

primrec tco_state :: "tree_code_state \<Rightarrow> tco_code_state" where
  "tco_state (TS vs sfs) = TCOS (map tco_val vs) (tco_stack sfs)"

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> tco_r (op # cd) = tco_r cd"
  by (induction op) (simp_all split: list.splits)

lemma tco_r_append [simp]: "cd' \<noteq> [] \<Longrightarrow> tco_r (cd @ cd') = tco_r cd'"
  by (induction cd) simp_all

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> tco_cd (op # cd) = tco_cd_one op # tco_cd cd"
  by (induction op) (simp_all split: list.splits)

lemma tco_cd_append [simp]: "cd' \<noteq> [] \<Longrightarrow> tco_cd (cd @ cd') = map tco_cd_one cd @ tco_cd cd'"
  by (induction cd) simp_all

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> cd' \<noteq> [] \<Longrightarrow> tco_cd (cd @ cd') \<noteq> []"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "(env, cd, r) # sfs = tco_stack sfs' \<Longrightarrow> \<exists>dsfs env' cd' sfs''. 
  sfs' = dsfs @ (env', cd') # sfs'' \<and> env = map tco_val env' \<and> cd = tco_cd cd' \<and> 
    r = tco_r cd' \<and> list_all dead_frame dsfs \<and> sfs = tco_stack sfs''"
proof (induction sfs')
  case (Cons sf sfs')
  thus ?case
  proof (induction sf)
    case (Pair env' cd')
    thus ?case
    proof (induction cd' rule: tco_cd.induct)
      case 1
      then obtain dsfs env'' cd' sfs'' where X: "sfs' = dsfs @ (env'', cd') # sfs'' \<and> 
        env = map tco_val env'' \<and> cd = tco_cd cd' \<and> r = tco_r cd' \<and> list_all dead_frame dsfs \<and> 
          sfs = tco_stack sfs''" by auto
      hence "\<exists>dsfsx. (env', []) # dsfs @ (env'', cd') # sfs'' = dsfsx @ (env'', cd') # sfs'' \<and> 
          list_all dead_frame dsfsx \<and> sfs = tco_stack sfs''" by simp
      hence "\<exists>dsfsx sfs'''. 
        (env', []) # dsfs @ (env'', cd') # sfs'' = dsfsx @ (env'', cd') # sfs''' \<and> 
          list_all dead_frame dsfsx \<and> sfs = tco_stack sfs'''" by fastforce
      with X show ?case by fastforce
    next
      case (2 x cd')
      hence "env = map tco_val env' \<and> cd = TCOLookup x # tco_cd cd' \<and> r = tco_r cd' \<and> 
        sfs = tco_stack sfs'" by simp
      thus ?case by fastforce
    next
      case (3 k cd')
      hence "env = map tco_val env' \<and> cd = TCOPushCon k # tco_cd cd' \<and> r = tco_r cd' \<and> 
        sfs = tco_stack sfs'" by simp
      thus ?case by fastforce
    next
      case (4 cd\<^sub>l cd')
      hence "env = map tco_val env' \<and> cd = TCOPushLam (tco_cd cd\<^sub>l) (tco_r cd\<^sub>l) # tco_cd cd' \<and> 
        r = tco_r cd' \<and> sfs = tco_stack sfs'" by simp
      thus ?case by fastforce
    next
      case (5 cd')
      thus ?case
      proof (cases cd')
        case Nil
        moreover with 5 have "env = map tco_val env' \<and> cd = [] \<and> r = TCOJump \<and> sfs = tco_stack sfs'" 
          by simp
        ultimately show ?thesis by fastforce
      next
        case (Cons op cd'')
        moreover with 5 have "env = map tco_val env' \<and> cd = TCOApply # tco_cd (op # cd'') \<and> 
          r = tco_r (op # cd'') \<and> sfs = tco_stack sfs'" by simp
        ultimately show ?thesis by fastforce
      qed
    qed
  qed
qed simp_all

lemma [dest]: "TCOS vs ((env, cd, r) # sfs) = tco_state \<Sigma> \<Longrightarrow> \<exists>dsfs vs' env' cd' sfs'. 
  \<Sigma> = TS vs' (dsfs @ (env', cd') # sfs') \<and> vs = map tco_val vs' \<and> env = map tco_val env' \<and> 
    cd = tco_cd cd' \<and> r = tco_r cd' \<and> list_all dead_frame dsfs \<and> sfs = tco_stack sfs'"
  by (induction \<Sigma>) auto

lemma [dest]: "TCOLookup x # cd = tco_cd cd' \<Longrightarrow> \<exists>cd''. cd' = TLookup x # cd'' \<and> cd = tco_cd cd''"
  by (induction cd' rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "TCOPushCon k # cd = tco_cd cd' \<Longrightarrow> \<exists>cd''. cd' = TPushCon k # cd'' \<and> cd = tco_cd cd''"
  by (induction cd' rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "TCOPushLam cd' r # cd = tco_cd cd\<^sub>t \<Longrightarrow> \<exists>cd\<^sub>t' cd\<^sub>t''. cd\<^sub>t = TPushLam cd\<^sub>t'' # cd\<^sub>t' \<and> 
    cd = tco_cd cd\<^sub>t' \<and> r = tco_r cd\<^sub>t'' \<and> cd' = tco_cd cd\<^sub>t''"
  by (induction cd\<^sub>t rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "TCOApply # cd = tco_cd cd' \<Longrightarrow> 
    \<exists>op cd''. cd' = TApply # op # cd'' \<and> cd = tco_cd (op # cd'')"
  by (induction cd' rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "TCOConst k = tco_val v \<Longrightarrow> v = TConst k"
  by (induction v) simp_all

lemma [dest]: "TCOLam env cd r = tco_val v \<Longrightarrow> 
    \<exists>env\<^sub>t cd\<^sub>t. v = TLam env\<^sub>t cd\<^sub>t \<and> env = map tco_val env\<^sub>t \<and> cd = tco_cd cd\<^sub>t \<and> r = tco_r cd\<^sub>t"
  by (induction v) simp_all

lemma [dest]: "TCOReturn = tco_r cd \<Longrightarrow> [] = tco_cd cd \<Longrightarrow> cd = []"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "TCOJump = tco_r cd \<Longrightarrow> [] = tco_cd cd \<Longrightarrow> cd = [TApply]"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

lemma [simp]: "list_all dead_frame dsfs \<Longrightarrow> iter (\<leadsto>\<^sub>t) (TS vs (dsfs @ sfs)) (TS vs sfs)"
proof (induction dsfs)
  case (Cons sf dsfs)
  then obtain vs' where "sf = (vs', [])" by (cases sf) simp_all
  hence "TS vs ((sf # dsfs) @ sfs) \<leadsto>\<^sub>t TS vs (dsfs @ sfs)" by simp
  with Cons show ?case by simp
qed simp_all

lemma [simp]: "\<not> live_frame fr \<Longrightarrow> iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS vs (fr # sfs)) (TCOS vs sfs)"
proof (induction fr rule: live_frame.induct)
  case (1 env)
  hence "TCOS vs ((env, [], TCOReturn) # sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o TCOS vs sfs" by simp
  thus ?case by (metis iter_one)
qed simp_all

lemma [simp]: "tco_cd (op # cd) = [] \<Longrightarrow> tco_r (op # cd) = TCOJump"
  by (induction op) (simp_all split: list.splits)

lemma [simp]: "live_frame (env, cd, TCOJump)"
  by (induction cd) simp_all

lemma tco_never_dead [simp]: "live_frame (env, tco_cd (op # cd), tco_r (op # cd))"
  by (induction op) (simp_all split: list.splits)

theorem completetco [simp]: "tco_state \<Sigma>\<^sub>t \<leadsto>\<^sub>t\<^sub>c\<^sub>o \<Sigma>' \<Longrightarrow> full_state \<Sigma>\<^sub>t \<Longrightarrow> \<exists>\<Sigma>\<^sub>t'. iter (\<leadsto>\<^sub>t) \<Sigma>\<^sub>t \<Sigma>\<^sub>t' \<and> 
  iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) \<Sigma>' (tco_state \<Sigma>\<^sub>t')"
proof (induction "tco_state \<Sigma>\<^sub>t" \<Sigma>' rule: evaltco.induct)
  case (evtco_lookup env x v vs cd r sfs)
  then obtain dsfs vs' env' cd' sfs' where S: 
    "\<Sigma>\<^sub>t = TS vs' (dsfs @ (env', TLookup x # cd') # sfs') \<and> vs = map tco_val vs' \<and> 
      env = map tco_val env' \<and> cd = tco_cd cd' \<and> r = tco_r cd' \<and> list_all dead_frame dsfs \<and> 
        sfs = tco_stack sfs'" by fastforce
  with evtco_lookup obtain v' where V: "lookup env' x = Some v' \<and> v = tco_val v'" by fastforce
  from S have "iter (\<leadsto>\<^sub>t) (TS vs' (dsfs @ (env', TLookup x # cd') # sfs')) 
    (TS vs' ((env', TLookup x # cd') # sfs'))" by simp
  moreover from V have "iter (\<leadsto>\<^sub>t) (TS vs' ((env', TLookup x # cd') # sfs')) 
    (TS (v' # vs') ((env', cd') # sfs'))" by (metis evt_lookup iter_one)
  ultimately have X: "iter (\<leadsto>\<^sub>t) (TS vs' (dsfs @ (env', TLookup x # cd') # sfs')) 
    (TS (v' # vs') ((env', cd') # sfs'))" by (metis iter_append)
  from S V have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (v # map tco_val vs') 
    ((map tco_val env', tco_cd cd', tco_r cd') # tco_stack sfs')) 
      (tco_state (TS (v' # vs') ((env', cd') # sfs')))" by simp
  with S X show ?case by blast
next
  case (evtco_pushcon vs env k cd r sfs)
  then obtain dsfs vs' env' cd' sfs' where S: 
    "\<Sigma>\<^sub>t = TS vs' (dsfs @ (env', TPushCon k # cd') # sfs') \<and> vs = map tco_val vs' \<and> 
      env = map tco_val env' \<and> cd = tco_cd cd' \<and> r = tco_r cd' \<and> list_all dead_frame dsfs \<and> 
        sfs = tco_stack sfs'" by fastforce
  hence "iter (\<leadsto>\<^sub>t) (TS vs' (dsfs @ (env', TPushCon k # cd') # sfs')) 
    (TS vs' ((env', TPushCon k # cd') # sfs'))" by simp
  moreover have "iter (\<leadsto>\<^sub>t) (TS vs' ((env', TPushCon k # cd') # sfs')) 
    (TS (TConst k # vs') ((env', cd') # sfs'))" by (metis evt_pushcon iter_one)
  ultimately have X: "iter (\<leadsto>\<^sub>t) (TS vs' (dsfs @ (env', TPushCon k # cd') # sfs')) 
    (TS (TConst k # vs') ((env', cd') # sfs'))" by simp
  from S have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (TCOConst k # map tco_val vs') 
    ((map tco_val env', tco_cd cd', tco_r cd') # tco_stack sfs')) 
      (tco_state (TS (TConst k # vs') ((env', cd') # sfs')))" by simp
  with S X show ?case by blast
next
  case (evtco_pushlam vs env cd' r' cd r sfs)
  then obtain dsfs vs\<^sub>t env\<^sub>t cd\<^sub>t cd\<^sub>t' sfs\<^sub>t where S: 
    "\<Sigma>\<^sub>t = TS vs\<^sub>t (dsfs @ (env\<^sub>t, TPushLam cd\<^sub>t' # cd\<^sub>t) # sfs\<^sub>t) \<and> vs = map tco_val vs\<^sub>t \<and> 
      env = map tco_val env\<^sub>t \<and> cd = tco_cd cd\<^sub>t \<and> cd' = tco_cd cd\<^sub>t' \<and> r' = tco_r cd\<^sub>t' \<and> 
        r = tco_r cd\<^sub>t \<and> list_all dead_frame dsfs \<and> sfs = tco_stack sfs\<^sub>t" by fastforce
  hence "iter (\<leadsto>\<^sub>t) (TS vs\<^sub>t (dsfs @ (env\<^sub>t, TPushLam cd\<^sub>t' # cd\<^sub>t) # sfs\<^sub>t)) 
    (TS vs\<^sub>t ((env\<^sub>t, TPushLam cd\<^sub>t' # cd\<^sub>t) # sfs\<^sub>t))" by simp
  moreover have "iter (\<leadsto>\<^sub>t) (TS vs\<^sub>t ((env\<^sub>t, TPushLam cd\<^sub>t' # cd\<^sub>t) # sfs\<^sub>t)) 
    (TS (TLam env\<^sub>t cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, cd\<^sub>t) # sfs\<^sub>t))" by (metis evt_pushlam iter_one)
  ultimately have X: "iter (\<leadsto>\<^sub>t) (TS vs\<^sub>t (dsfs @ (env\<^sub>t, TPushLam cd\<^sub>t' # cd\<^sub>t) # sfs\<^sub>t)) 
    (TS (TLam env\<^sub>t cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, cd\<^sub>t) # sfs\<^sub>t))" by simp
  from S have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (TCOLam env cd' r' # map tco_val vs\<^sub>t) 
    ((map tco_val env\<^sub>t, tco_cd cd\<^sub>t, tco_r cd\<^sub>t) # tco_stack sfs\<^sub>t)) 
      (tco_state (TS (TLam env\<^sub>t cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, cd\<^sub>t) # sfs\<^sub>t)))" by simp
  with S X show ?case by blast
next
  case (evtco_apply v env' cd' r' vs env cd r sfs)
  then obtain dsfs v\<^sub>t vl vs\<^sub>t env\<^sub>t cd\<^sub>t'' sfs\<^sub>t where S: 
    "\<Sigma>\<^sub>t = TS (v\<^sub>t # vl # vs\<^sub>t) (dsfs @ (env\<^sub>t, cd\<^sub>t'') # sfs\<^sub>t) \<and> v = tco_val v\<^sub>t \<and> 
      TCOLam env' cd' r' = tco_val vl \<and> vs = map tco_val vs\<^sub>t \<and> env = map tco_val env\<^sub>t \<and> 
        TCOApply # cd = tco_cd cd\<^sub>t'' \<and> r = tco_r cd\<^sub>t'' \<and> list_all dead_frame dsfs \<and> 
          sfs = tco_stack sfs\<^sub>t" by blast
  then obtain op cd\<^sub>t where C: "cd\<^sub>t'' = TApply # op # cd\<^sub>t \<and> cd = tco_cd (op # cd\<^sub>t)" by blast
  from S obtain env\<^sub>t' cd\<^sub>t' where V: "vl = TLam env\<^sub>t' cd\<^sub>t' \<and> env' = map tco_val env\<^sub>t' \<and> 
    cd' = tco_cd cd\<^sub>t' \<and> r' = tco_r cd\<^sub>t'" by blast
  from S have "iter (\<leadsto>\<^sub>t) (TS (v\<^sub>t # TLam env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) (dsfs @ (env\<^sub>t, TApply # op # cd\<^sub>t) # sfs\<^sub>t)) 
    (TS (v\<^sub>t # TLam env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, TApply # op # cd\<^sub>t) # sfs\<^sub>t))" by simp
  moreover have "TS (v\<^sub>t # TLam env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, TApply # op # cd\<^sub>t) # sfs\<^sub>t) \<leadsto>\<^sub>t 
    TS vs\<^sub>t ((v\<^sub>t # env\<^sub>t', cd\<^sub>t') # (env\<^sub>t, op # cd\<^sub>t) # sfs\<^sub>t)" by simp
  ultimately have X: "iter (\<leadsto>\<^sub>t) (TS (v\<^sub>t # TLam env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) 
    (dsfs @ (env\<^sub>t, TApply # op # cd\<^sub>t) # sfs\<^sub>t)) (TS vs\<^sub>t ((v\<^sub>t # env\<^sub>t', cd\<^sub>t') # (env\<^sub>t, op # cd\<^sub>t) # sfs\<^sub>t))" 
      by simp
  from evtco_apply S V have "full_block cd\<^sub>t' 0 = Some (Suc 0)" by simp
  hence "live_frame (tco_val v\<^sub>t # map tco_val env\<^sub>t', tco_cd cd\<^sub>t', tco_r cd\<^sub>t')" 
    by (induction cd\<^sub>t' rule: tco_cd.induct) (simp_all split: list.splits)
  with S have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (map tco_val vs\<^sub>t) ((tco_val v\<^sub>t # map tco_val env\<^sub>t', tco_cd cd\<^sub>t', 
    tco_r cd\<^sub>t') # (map tco_val env\<^sub>t, tco_cd (op # cd\<^sub>t), tco_r (TApply # op # cd\<^sub>t)) # tco_stack sfs\<^sub>t)) 
      (tco_state (TS vs\<^sub>t ((v\<^sub>t # env\<^sub>t', cd\<^sub>t') # (env\<^sub>t, op # cd\<^sub>t) # sfs\<^sub>t)))" by simp
  with S C V X show ?case by blast
next
  case (evtco_return vs env sfs)
  then obtain dsfs vs' env' sfs' where S: "\<Sigma>\<^sub>t = TS vs' (dsfs @ (env', []) # sfs') \<and> 
    vs = map tco_val vs' \<and> env = map tco_val env' \<and> list_all dead_frame dsfs \<and> sfs = tco_stack sfs'" 
      by blast
  hence "iter (\<leadsto>\<^sub>t) (TS vs' (dsfs @ (env', []) # sfs')) (TS vs' ((env', []) # sfs'))" by simp
  moreover have "iter (\<leadsto>\<^sub>t) (TS vs' ((env', []) # sfs')) (TS vs' sfs')" by (simp add: iter_one)
  ultimately have X: "iter (\<leadsto>\<^sub>t) (TS vs' (dsfs @ (env', []) # sfs')) (TS vs' sfs')" by simp
  from S have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS vs sfs) (tco_state (TS vs' sfs'))" by simp
  with S X show ?case by blast
next
  case (evtco_jump v env' cd' r' vs env sfs)
  then obtain dsfs v\<^sub>t vl vs\<^sub>t env\<^sub>t cd\<^sub>t sfs\<^sub>t where S: 
    "\<Sigma>\<^sub>t = TS (v\<^sub>t # vl # vs\<^sub>t) (dsfs @ (env\<^sub>t, cd\<^sub>t) # sfs\<^sub>t) \<and> v = tco_val v\<^sub>t \<and> 
      TCOLam env' cd' r' = tco_val vl \<and> vs = map tco_val vs\<^sub>t \<and> env = map tco_val env\<^sub>t \<and> 
        [] = tco_cd cd\<^sub>t \<and> TCOJump = tco_r cd\<^sub>t \<and> list_all dead_frame dsfs \<and> 
          sfs = tco_stack sfs\<^sub>t" by blast
  then obtain env\<^sub>t' cd\<^sub>t' where V: "vl = TLam env\<^sub>t' cd\<^sub>t' \<and> env' = map tco_val env\<^sub>t' \<and> 
    cd' = tco_cd cd\<^sub>t' \<and> r' = tco_r cd\<^sub>t'" by blast
  from S have C: "cd\<^sub>t = [TApply]" by blast
  with S have "iter (\<leadsto>\<^sub>t) (TS (v\<^sub>t # TLam env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) (dsfs @ (env\<^sub>t, [TApply]) # sfs\<^sub>t)) 
    (TS (v\<^sub>t # TLam env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, [TApply]) # sfs\<^sub>t))" by simp
  moreover have "iter (\<leadsto>\<^sub>t) (TS (v\<^sub>t # TLam env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, [TApply]) # sfs\<^sub>t))
    (TS vs\<^sub>t ((v\<^sub>t # env\<^sub>t', cd\<^sub>t') # (env\<^sub>t, []) # sfs\<^sub>t))" by (simp add: iter_one)
  ultimately have X: "iter (\<leadsto>\<^sub>t) (TS (v\<^sub>t # TLam env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) (dsfs @ (env\<^sub>t, [TApply]) # sfs\<^sub>t)) 
    (TS vs\<^sub>t ((v\<^sub>t # env\<^sub>t', cd\<^sub>t') # (env\<^sub>t, []) # sfs\<^sub>t))" using iter_append by fastforce
  have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (map tco_val vs\<^sub>t) ((tco_val v\<^sub>t # map tco_val env\<^sub>t', tco_cd cd\<^sub>t', tco_r cd\<^sub>t') 
    # tco_stack sfs\<^sub>t)) (tco_state (TS vs\<^sub>t ((v\<^sub>t # env\<^sub>t', cd\<^sub>t') # (env\<^sub>t, []) # sfs\<^sub>t)))" by simp
  with S V C X show ?case by blast
qed

theorem correcttco [simp]: "\<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state \<Sigma>) (tco_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: evalt.induct)
  case (evt_lookup env x v vs cd sfs)
  thus ?case 
  proof (cases cd)
    case Nil
    have "TCOS (tco_val v # map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
      TCOS (tco_val v # map tco_val vs) (tco_stack sfs)" by (metis evtco_return)
    hence "TCOS (tco_val v # map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
      tco_state (TS (v # vs) ((env, []) # sfs))" by simp
    moreover from evt_lookup have "tco_state (TS vs ((env, [TLookup x]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      TCOS (tco_val v # map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs)" by simp
    ultimately have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS vs ((env, [TLookup x]) # sfs)))
      (tco_state (TS (v # vs) ((env, []) # sfs)))" by (metis iter_refl iter_step)
    with Nil show ?thesis by simp
  next
    case (Cons op cd)
    moreover from evt_lookup have "tco_state (TS vs ((env, TLookup x # op # cd) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      tco_state (TS (v # vs) ((env, op # cd) # sfs))" by simp
    ultimately show ?thesis by (metis iter_one)
  qed
next
  case (evt_pushcon vs env k cd sfs)
  thus ?case 
  proof (cases cd)
    case Nil
    have "TCOS (TCOConst k # map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
        TCOS (TCOConst k # map tco_val vs) (tco_stack sfs)" by (metis evtco_return)
    hence "TCOS (TCOConst k # map tco_val vs) 
      ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
        tco_state (TS (TConst k # vs) ((env, []) # sfs))" by simp
    moreover have "tco_state (TS vs ((env, [TPushCon k]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      TCOS (TCOConst k # map tco_val vs) 
        ((map tco_val env, [], TCOReturn) # tco_stack sfs)" by simp
    ultimately have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS vs ((env, [TPushCon k]) # sfs)))
      (tco_state (TS (TConst k # vs) ((env, []) # sfs)))" by (metis iter_refl iter_step)
    with Nil show ?thesis by simp
  next
    case (Cons op cd)
    moreover have "tco_state (TS vs ((env, TPushCon k # op # cd) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      tco_state (TS (TConst k # vs) ((env, op # cd) # sfs))" by simp
    ultimately show ?thesis by (metis iter_one)
  qed
next
  case (evt_pushlam vs env cd' cd sfs)
  thus ?case 
  proof (cases cd)
    case Nil
    have "TCOS (map tco_val vs) ((map tco_val env, 
      [TCOPushLam (tco_cd cd') (tco_r cd')], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o  
        TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r cd') # map tco_val vs) 
          ((map tco_val env, [], TCOReturn) # tco_stack sfs)" by (metis evtco_pushlam)
    hence X: "tco_state (TS vs ((env, [TPushLam cd']) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r cd') # map tco_val vs) 
        ((map tco_val env, [], TCOReturn) # tco_stack sfs)" by simp
    have "TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r cd') # 
      map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r cd') # map tco_val vs) (tco_stack sfs)" 
          by (metis evtco_return)
    hence "TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r cd') # 
      map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        tco_state (TS (TLam env cd' # vs) ((env, []) # sfs))" by simp
    with X have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS vs ((env, [TPushLam cd']) # sfs)))
      (tco_state (TS (TLam env cd' # vs) ((env, []) # sfs)))" by (metis iter_refl iter_step)
    with Nil show ?thesis by simp
  next
    case (Cons op cd)
    have "TCOS (map tco_val vs) ((map tco_val env, TCOPushLam (tco_cd cd') (tco_r cd') # 
      tco_cd (op # cd), tco_r (op # cd)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r cd') # map tco_val vs) 
          ((map tco_val env, tco_cd (op # cd), tco_r (op # cd)) # tco_stack sfs)" 
      by (metis evtco_pushlam)
    hence "tco_state (TS vs ((env, TPushLam cd' # op # cd) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      tco_state (TS (TLam env cd' # vs) ((env, op # cd) # sfs))" by simp
    with Cons show ?thesis by (metis iter_one)
  qed
next
  case (evt_apply v env' cd' vs env cd sfs)
  thus ?case 
  proof (cases cd)
    case Nil note CD = Nil
    thus ?thesis
    proof (cases cd')
      case Nil
      have "TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # tco_stack sfs) 
        \<leadsto>\<^sub>t\<^sub>c\<^sub>o TCOS (map tco_val vs) (tco_stack sfs)" by (metis evtco_return)
      hence "TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # tco_stack sfs) 
        \<leadsto>\<^sub>t\<^sub>c\<^sub>o tco_state (TS vs ((v # env', []) # (env, []) # sfs))" by simp
      hence X: "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # 
        tco_stack sfs)) (tco_state (TS vs ((v # env', []) # (env, []) # sfs)))" by (metis iter_one)
      have "TCOS (tco_val v # TCOLam (map tco_val env') [] TCOReturn # 
        map tco_val vs) ((map tco_val env, [], TCOJump) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
          TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # 
            tco_stack sfs)" by (metis evtco_jump)
      hence "tco_state (TS (v # TLam env' [] # vs) ((env, [TApply]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # tco_stack sfs)" 
          by simp
      with X have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS (v # TLam env' [] # vs) ((env, [TApply]) # sfs)))
        (tco_state (TS vs ((v # env', []) # (env, []) # sfs)))" using iter_step by fast
      with CD Nil show ?thesis by simp
    next
      case (Cons op' cd'')
      have "TCOS (tco_val v # TCOLam (map tco_val env') (tco_cd (op' # cd'')) (tco_r (op' # cd'')) # 
        map tco_val vs) ((map tco_val env, [], TCOJump) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
          TCOS (map tco_val vs) ((tco_val v # map tco_val env', tco_cd (op' # cd''), 
            tco_r (op' # cd'')) # tco_stack sfs)"  by (metis evtco_jump)
      hence "tco_state (TS (v # TLam env' (op' # cd'') # vs) ((env, [TApply]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        tco_state (TS vs ((v # env', op' # cd'') # (env, []) # sfs))" by simp
      with Nil Cons show ?thesis by (metis iter_one)
    qed
  next
    case (Cons op cd) note CD = Cons
    thus ?thesis
    proof (cases cd')
      case Nil
      have "TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # 
        (map tco_val env, tco_cd (op # cd), tco_r (op # cd)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
          TCOS (map tco_val vs) ((map tco_val env, tco_cd (op # cd), 
            tco_r (op # cd)) # tco_stack sfs)" by (metis evtco_return)
      hence "TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # 
        (map tco_val env, tco_cd (op # cd), tco_r (op # cd)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
            tco_state (TS vs ((v # env', []) # (env, op # cd) # sfs))" by simp
      hence X: "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # 
        (map tco_val env, tco_cd (op # cd), tco_r (op # cd)) # tco_stack sfs)) 
          (tco_state (TS vs ((v # env', []) # (env, op # cd) # sfs)))" by (metis iter_one)
      have "tco_state (TS (v # TLam env' [] # vs) ((env, TApply # op # cd) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # 
          (map tco_val env, tco_cd (op # cd), tco_r (op # cd)) # tco_stack sfs)" by simp
      with X have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS (v # TLam env' [] # vs) 
        ((env, TApply # op # cd) # sfs)))
          (tco_state (TS vs ((v # env', []) # (env, op # cd) # sfs)))" 
        using iter_step by fast
      with Cons Nil show ?thesis by simp
    next
      case (Cons op' cd')
      have "tco_state (TS (v # TLam env' (op' # cd') # vs) 
        ((env, TApply # op # cd) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
          tco_state (TS vs ((v # env', (op' # cd')) # (env, op # cd) # sfs))" by simp
      with CD Cons show ?thesis by (metis iter_one)
    qed
  qed
qed simp_all

lemma iter_tco_eval [simp]: "iter (\<leadsto>\<^sub>t) \<Sigma> \<Sigma>' \<Longrightarrow> iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state \<Sigma>) (tco_state \<Sigma>')"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) (simp, metis iter_append correcttco)

end