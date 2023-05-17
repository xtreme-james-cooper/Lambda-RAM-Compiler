theory TailCallOptimization
  imports TailCall "../06TreeCode/TreeCode" "../00Utils/Iteration"
begin

fun tco_r :: "code\<^sub>e list \<Rightarrow> tco_return" where
  "tco_r [] = TCOReturn"
| "tco_r (Apply\<^sub>e # cd) = (case cd of [] \<Rightarrow> TCOJump | _ \<Rightarrow> tco_r cd)"
| "tco_r (op # cd) = tco_r cd"

fun tco_cd :: "code\<^sub>e list \<Rightarrow> tco_code list" where
  "tco_cd [] = []"
| "tco_cd (Lookup\<^sub>e x # cd) = TCOLookup x # tco_cd cd"
| "tco_cd (PushCon\<^sub>e k # cd) = TCOPushCon k # tco_cd cd"
| "tco_cd (PushLam\<^sub>e cd' # cd) = TCOPushLam (tco_cd cd') (tco_r cd') # tco_cd cd"
| "tco_cd (Apply\<^sub>e # cd) = (case cd of [] \<Rightarrow> [] | _ \<Rightarrow> TCOApply # tco_cd cd)"

definition tco :: "code\<^sub>e list \<Rightarrow> tco_code list \<times> tco_return" where
  "tco cd = (tco_cd cd, tco_r cd)"

primrec tco_val :: "closure\<^sub>e \<Rightarrow> tco_closure" where
  "tco_val (Const\<^sub>e k) = TCOConst k"
| "tco_val (Lam\<^sub>e vs cd) = TCOLam (map tco_val vs) (tco_cd cd) (tco_r cd)"

fun tco_stack_frame :: "frame\<^sub>e \<Rightarrow> tco_stack_frame" where
  "tco_stack_frame (vs, cd) = (map tco_val vs, tco_cd cd, tco_r cd)"

fun live_frame :: "tco_stack_frame \<Rightarrow> bool" where
  "live_frame (vs, [], TCOReturn) = False"
| "live_frame (vs, [], TCOJump) = True"
| "live_frame (vs, op # cd, r) = True"

primrec dead_frame :: "frame\<^sub>e \<Rightarrow> bool" where
  "dead_frame (vs, cd) = (cd = [])"

abbreviation tco_stack :: "frame\<^sub>e list \<Rightarrow> tco_stack_frame list" where
  "tco_stack sfs \<equiv> filter live_frame (map tco_stack_frame sfs)"

primrec tco_state :: "state\<^sub>e \<Rightarrow> tco_code_state" where
  "tco_state (S\<^sub>e vs sfs) = TCOS (map tco_val vs) (tco_stack sfs)"

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> tco_r (op # cd) = tco_r cd"
  by (induction op) (simp_all split: list.splits)

lemma tco_r_append [simp]: "cd' \<noteq> [] \<Longrightarrow> tco_r (cd @ cd') = tco_r cd'"
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
  \<Sigma> = S\<^sub>e vs' (dsfs @ (env', cd') # sfs') \<and> vs = map tco_val vs' \<and> env = map tco_val env' \<and> 
    cd = tco_cd cd' \<and> r = tco_r cd' \<and> list_all dead_frame dsfs \<and> sfs = tco_stack sfs'"
  by (induction \<Sigma>) auto

lemma [dest]: "TCOLookup x # cd = tco_cd cd' \<Longrightarrow> \<exists>cd''. cd' = Lookup\<^sub>e x # cd'' \<and> cd = tco_cd cd''"
  by (induction cd' rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "TCOPushCon k # cd = tco_cd cd' \<Longrightarrow> \<exists>cd''. cd' = PushCon\<^sub>e k # cd'' \<and> cd = tco_cd cd''"
  by (induction cd' rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "TCOPushLam cd' r # cd = tco_cd cd\<^sub>t \<Longrightarrow> \<exists>cd\<^sub>t' cd\<^sub>t''. cd\<^sub>t = PushLam\<^sub>e cd\<^sub>t'' # cd\<^sub>t' \<and> 
    cd = tco_cd cd\<^sub>t' \<and> r = tco_r cd\<^sub>t'' \<and> cd' = tco_cd cd\<^sub>t''"
  by (induction cd\<^sub>t rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "TCOApply # cd = tco_cd cd' \<Longrightarrow> 
    \<exists>op cd''. cd' = Apply\<^sub>e # op # cd'' \<and> cd = tco_cd (op # cd'')"
  by (induction cd' rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "TCOConst k = tco_val v \<Longrightarrow> v = Const\<^sub>e k"
  by (induction v) simp_all

lemma [dest]: "TCOLam env cd r = tco_val v \<Longrightarrow> 
    \<exists>env\<^sub>t cd\<^sub>t. v = Lam\<^sub>e env\<^sub>t cd\<^sub>t \<and> env = map tco_val env\<^sub>t \<and> cd = tco_cd cd\<^sub>t \<and> r = tco_r cd\<^sub>t"
  by (induction v) simp_all

lemma [dest]: "TCOReturn = tco_r cd \<Longrightarrow> [] = tco_cd cd \<Longrightarrow> cd = []"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "TCOJump = tco_r cd \<Longrightarrow> [] = tco_cd cd \<Longrightarrow> cd = [Apply\<^sub>e]"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

lemma [simp]: "list_all dead_frame dsfs \<Longrightarrow> iter (\<leadsto>\<^sub>e) (S\<^sub>e vs (dsfs @ sfs)) (S\<^sub>e vs sfs)"
proof (induction dsfs)
  case (Cons sf dsfs)
  then obtain vs' where "sf = (vs', [])" by (cases sf) simp_all
  hence "S\<^sub>e vs ((sf # dsfs) @ sfs) \<leadsto>\<^sub>e S\<^sub>e vs (dsfs @ sfs)" by simp
  with Cons show ?case by simp
qed simp_all

lemma [simp]: "\<not> live_frame fr \<Longrightarrow> iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (TCOS vs (fr # sfs)) (TCOS vs sfs)"
proof (induction fr rule: live_frame.induct)
  case (1 env)
  hence "TCOS vs ((env, [], TCOReturn) # sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o TCOS vs sfs" by simp
  thus ?case by (metis iter_one)
qed simp_all

lemma [simp]: "tco_cd (op # cd) = [] \<Longrightarrow> tco_r (op # cd) = TCOJump"
  by (induction op) (simp_all split: list.splits)

lemma [simp]: "live_frame (env, cd, TCOJump)"
  by (induction cd) simp_all

lemma tco_never_dead [simp]: "live_frame (env, tco_cd (op # cd), tco_r (op # cd))"
  by (induction op) (simp_all split: list.splits)

theorem completetco [simp]: "tco_state \<Sigma>\<^sub>t \<leadsto>\<^sub>e\<^sub>c\<^sub>o \<Sigma>' \<Longrightarrow> \<exists>\<Sigma>\<^sub>t'. iter (\<leadsto>\<^sub>e) \<Sigma>\<^sub>t \<Sigma>\<^sub>t' \<and> 
  iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) \<Sigma>' (tco_state \<Sigma>\<^sub>t')"
proof (induction "tco_state \<Sigma>\<^sub>t" \<Sigma>' rule: evaltco.induct)
  case (evtco_lookup env x v vs cd r sfs)
  then obtain dsfs vs' env' cd' sfs' where S: 
    "\<Sigma>\<^sub>t = S\<^sub>e vs' (dsfs @ (env', Lookup\<^sub>e x # cd') # sfs') \<and> vs = map tco_val vs' \<and> 
      env = map tco_val env' \<and> cd = tco_cd cd' \<and> r = tco_r cd' \<and> list_all dead_frame dsfs \<and> 
        sfs = tco_stack sfs'" by fastforce
  with evtco_lookup obtain v' where V: "lookup env' x = Some v' \<and> v = tco_val v'" by fastforce
  from S have "iter (\<leadsto>\<^sub>e) (S\<^sub>e vs' (dsfs @ (env', Lookup\<^sub>e x # cd') # sfs')) 
    (S\<^sub>e vs' ((env', Lookup\<^sub>e x # cd') # sfs'))" by simp
  moreover from V have "iter (\<leadsto>\<^sub>e) (S\<^sub>e vs' ((env', Lookup\<^sub>e x # cd') # sfs')) 
    (S\<^sub>e (v' # vs') ((env', cd') # sfs'))" by (metis ev\<^sub>e_lookup iter_one)
  ultimately have X: "iter (\<leadsto>\<^sub>e) (S\<^sub>e vs' (dsfs @ (env', Lookup\<^sub>e x # cd') # sfs')) 
    (S\<^sub>e (v' # vs') ((env', cd') # sfs'))" by (metis iter_append)
  from S V have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (TCOS (v # map tco_val vs') 
    ((map tco_val env', tco_cd cd', tco_r cd') # tco_stack sfs')) 
      (tco_state (S\<^sub>e (v' # vs') ((env', cd') # sfs')))" by simp
  with S X show ?case by blast
next
  case (evtco_pushcon vs env k cd r sfs)
  then obtain dsfs vs' env' cd' sfs' where S: 
    "\<Sigma>\<^sub>t = S\<^sub>e vs' (dsfs @ (env', PushCon\<^sub>e k # cd') # sfs') \<and> vs = map tco_val vs' \<and> 
      env = map tco_val env' \<and> cd = tco_cd cd' \<and> r = tco_r cd' \<and> list_all dead_frame dsfs \<and> 
        sfs = tco_stack sfs'" by fastforce
  hence "iter (\<leadsto>\<^sub>e) (S\<^sub>e vs' (dsfs @ (env', PushCon\<^sub>e k # cd') # sfs')) 
    (S\<^sub>e vs' ((env', PushCon\<^sub>e k # cd') # sfs'))" by simp
  moreover have "iter (\<leadsto>\<^sub>e) (S\<^sub>e vs' ((env', PushCon\<^sub>e k # cd') # sfs')) 
    (S\<^sub>e (Const\<^sub>e k # vs') ((env', cd') # sfs'))" by (metis ev\<^sub>e_pushcon iter_one)
  ultimately have X: "iter (\<leadsto>\<^sub>e) (S\<^sub>e vs' (dsfs @ (env', PushCon\<^sub>e k # cd') # sfs')) 
    (S\<^sub>e (Const\<^sub>e k # vs') ((env', cd') # sfs'))" by simp
  from S have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (TCOS (TCOConst k # map tco_val vs') 
    ((map tco_val env', tco_cd cd', tco_r cd') # tco_stack sfs')) 
      (tco_state (S\<^sub>e (Const\<^sub>e k # vs') ((env', cd') # sfs')))" by simp
  with S X show ?case by blast
next
  case (evtco_pushlam vs env cd' r' cd r sfs)
  then obtain dsfs vs\<^sub>t env\<^sub>t cd\<^sub>t cd\<^sub>t' sfs\<^sub>t where S: 
    "\<Sigma>\<^sub>t = S\<^sub>e vs\<^sub>t (dsfs @ (env\<^sub>t, PushLam\<^sub>e cd\<^sub>t' # cd\<^sub>t) # sfs\<^sub>t) \<and> vs = map tco_val vs\<^sub>t \<and> 
      env = map tco_val env\<^sub>t \<and> cd = tco_cd cd\<^sub>t \<and> cd' = tco_cd cd\<^sub>t' \<and> r' = tco_r cd\<^sub>t' \<and> 
        r = tco_r cd\<^sub>t \<and> list_all dead_frame dsfs \<and> sfs = tco_stack sfs\<^sub>t" by fastforce
  hence "iter (\<leadsto>\<^sub>e) (S\<^sub>e vs\<^sub>t (dsfs @ (env\<^sub>t, PushLam\<^sub>e cd\<^sub>t' # cd\<^sub>t) # sfs\<^sub>t)) 
    (S\<^sub>e vs\<^sub>t ((env\<^sub>t, PushLam\<^sub>e cd\<^sub>t' # cd\<^sub>t) # sfs\<^sub>t))" by simp
  moreover have "iter (\<leadsto>\<^sub>e) (S\<^sub>e vs\<^sub>t ((env\<^sub>t, PushLam\<^sub>e cd\<^sub>t' # cd\<^sub>t) # sfs\<^sub>t)) 
    (S\<^sub>e (Lam\<^sub>e env\<^sub>t cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, cd\<^sub>t) # sfs\<^sub>t))" by (metis ev\<^sub>e_pushlam iter_one)
  ultimately have X: "iter (\<leadsto>\<^sub>e) (S\<^sub>e vs\<^sub>t (dsfs @ (env\<^sub>t, PushLam\<^sub>e cd\<^sub>t' # cd\<^sub>t) # sfs\<^sub>t)) 
    (S\<^sub>e (Lam\<^sub>e env\<^sub>t cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, cd\<^sub>t) # sfs\<^sub>t))" by simp
  from S have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (TCOS (TCOLam env cd' r' # map tco_val vs\<^sub>t) 
    ((map tco_val env\<^sub>t, tco_cd cd\<^sub>t, tco_r cd\<^sub>t) # tco_stack sfs\<^sub>t)) 
      (tco_state (S\<^sub>e (Lam\<^sub>e env\<^sub>t cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, cd\<^sub>t) # sfs\<^sub>t)))" by simp
  with S X show ?case by blast
next
  case (evtco_apply v env' cd' r' vs env cd r sfs)
  then obtain dsfs v\<^sub>t vl vs\<^sub>t env\<^sub>t cd\<^sub>t'' sfs\<^sub>t where S: 
    "\<Sigma>\<^sub>t = S\<^sub>e (v\<^sub>t # vl # vs\<^sub>t) (dsfs @ (env\<^sub>t, cd\<^sub>t'') # sfs\<^sub>t) \<and> v = tco_val v\<^sub>t \<and> 
      TCOLam env' cd' r' = tco_val vl \<and> vs = map tco_val vs\<^sub>t \<and> env = map tco_val env\<^sub>t \<and> 
        TCOApply # cd = tco_cd cd\<^sub>t'' \<and> r = tco_r cd\<^sub>t'' \<and> list_all dead_frame dsfs \<and> 
          sfs = tco_stack sfs\<^sub>t" by blast
  then obtain op cd\<^sub>t where C: "cd\<^sub>t'' = Apply\<^sub>e # op # cd\<^sub>t \<and> cd = tco_cd (op # cd\<^sub>t)" by blast
  from S obtain env\<^sub>t' cd\<^sub>t' where V: "vl = Lam\<^sub>e env\<^sub>t' cd\<^sub>t' \<and> env' = map tco_val env\<^sub>t' \<and> 
    cd' = tco_cd cd\<^sub>t' \<and> r' = tco_r cd\<^sub>t'" by blast
  from S have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (v\<^sub>t # Lam\<^sub>e env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) (dsfs @ (env\<^sub>t, Apply\<^sub>e # op # cd\<^sub>t) # sfs\<^sub>t)) 
    (S\<^sub>e (v\<^sub>t # Lam\<^sub>e env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, Apply\<^sub>e # op # cd\<^sub>t) # sfs\<^sub>t))" by simp
  moreover have "S\<^sub>e (v\<^sub>t # Lam\<^sub>e env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, Apply\<^sub>e # op # cd\<^sub>t) # sfs\<^sub>t) \<leadsto>\<^sub>e 
    S\<^sub>e vs\<^sub>t ((v\<^sub>t # env\<^sub>t', cd\<^sub>t') # (env\<^sub>t, op # cd\<^sub>t) # sfs\<^sub>t)" by simp
  ultimately have X: "iter (\<leadsto>\<^sub>e) (S\<^sub>e (v\<^sub>t # Lam\<^sub>e env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) 
    (dsfs @ (env\<^sub>t, Apply\<^sub>e # op # cd\<^sub>t) # sfs\<^sub>t)) (S\<^sub>e vs\<^sub>t ((v\<^sub>t # env\<^sub>t', cd\<^sub>t') # (env\<^sub>t, op # cd\<^sub>t) # sfs\<^sub>t))" 
      by simp
  from S have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (TCOS (map tco_val vs\<^sub>t) ((tco_val v\<^sub>t # map tco_val env\<^sub>t', tco_cd cd\<^sub>t', 
    tco_r cd\<^sub>t') # (map tco_val env\<^sub>t, tco_cd (op # cd\<^sub>t), tco_r (Apply\<^sub>e # op # cd\<^sub>t)) # tco_stack sfs\<^sub>t)) 
      (tco_state (S\<^sub>e vs\<^sub>t ((v\<^sub>t # env\<^sub>t', cd\<^sub>t') # (env\<^sub>t, op # cd\<^sub>t) # sfs\<^sub>t)))" by simp
  with S C V X show ?case by blast
next
  case (evtco_return vs env sfs)
  then obtain dsfs vs' env' sfs' where S: "\<Sigma>\<^sub>t = S\<^sub>e vs' (dsfs @ (env', []) # sfs') \<and> 
    vs = map tco_val vs' \<and> env = map tco_val env' \<and> list_all dead_frame dsfs \<and> sfs = tco_stack sfs'" 
      by blast
  hence "iter (\<leadsto>\<^sub>e) (S\<^sub>e vs' (dsfs @ (env', []) # sfs')) (S\<^sub>e vs' ((env', []) # sfs'))" by simp
  moreover have "iter (\<leadsto>\<^sub>e) (S\<^sub>e vs' ((env', []) # sfs')) (S\<^sub>e vs' sfs')" by (simp add: iter_one)
  ultimately have X: "iter (\<leadsto>\<^sub>e) (S\<^sub>e vs' (dsfs @ (env', []) # sfs')) (S\<^sub>e vs' sfs')" by simp
  from S have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (TCOS vs sfs) (tco_state (S\<^sub>e vs' sfs'))" by simp
  with S X show ?case by blast
next
  case (evtco_jump v env' cd' r' vs env sfs)
  then obtain dsfs v\<^sub>t vl vs\<^sub>t env\<^sub>t cd\<^sub>t sfs\<^sub>t where S: 
    "\<Sigma>\<^sub>t = S\<^sub>e (v\<^sub>t # vl # vs\<^sub>t) (dsfs @ (env\<^sub>t, cd\<^sub>t) # sfs\<^sub>t) \<and> v = tco_val v\<^sub>t \<and> 
      TCOLam env' cd' r' = tco_val vl \<and> vs = map tco_val vs\<^sub>t \<and> env = map tco_val env\<^sub>t \<and> 
        [] = tco_cd cd\<^sub>t \<and> TCOJump = tco_r cd\<^sub>t \<and> list_all dead_frame dsfs \<and> 
          sfs = tco_stack sfs\<^sub>t" by blast
  then obtain env\<^sub>t' cd\<^sub>t' where V: "vl = Lam\<^sub>e env\<^sub>t' cd\<^sub>t' \<and> env' = map tco_val env\<^sub>t' \<and> 
    cd' = tco_cd cd\<^sub>t' \<and> r' = tco_r cd\<^sub>t'" by blast
  from S have C: "cd\<^sub>t = [Apply\<^sub>e]" by blast
  with S have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (v\<^sub>t # Lam\<^sub>e env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) (dsfs @ (env\<^sub>t, [Apply\<^sub>e]) # sfs\<^sub>t)) 
    (S\<^sub>e (v\<^sub>t # Lam\<^sub>e env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, [Apply\<^sub>e]) # sfs\<^sub>t))" by simp
  moreover have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (v\<^sub>t # Lam\<^sub>e env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) ((env\<^sub>t, [Apply\<^sub>e]) # sfs\<^sub>t))
    (S\<^sub>e vs\<^sub>t ((v\<^sub>t # env\<^sub>t', cd\<^sub>t') # (env\<^sub>t, []) # sfs\<^sub>t))" by (simp add: iter_one)
  ultimately have X: "iter (\<leadsto>\<^sub>e) (S\<^sub>e (v\<^sub>t # Lam\<^sub>e env\<^sub>t' cd\<^sub>t' # vs\<^sub>t) (dsfs @ (env\<^sub>t, [Apply\<^sub>e]) # sfs\<^sub>t)) 
    (S\<^sub>e vs\<^sub>t ((v\<^sub>t # env\<^sub>t', cd\<^sub>t') # (env\<^sub>t, []) # sfs\<^sub>t))" using iter_append by fastforce
  have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (TCOS (map tco_val vs\<^sub>t) ((tco_val v\<^sub>t # map tco_val env\<^sub>t', tco_cd cd\<^sub>t', tco_r cd\<^sub>t') 
    # tco_stack sfs\<^sub>t)) (tco_state (S\<^sub>e vs\<^sub>t ((v\<^sub>t # env\<^sub>t', cd\<^sub>t') # (env\<^sub>t, []) # sfs\<^sub>t)))" by simp
  with S V C X show ?case by blast
qed

theorem correcttco [simp]: "\<Sigma> \<leadsto>\<^sub>e \<Sigma>' \<Longrightarrow> iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (tco_state \<Sigma>) (tco_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>e.induct)
  case (ev\<^sub>e_lookup env x v vs cd sfs)
  thus ?case 
  proof (cases cd)
    case Nil
    have "TCOS (tco_val v # map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o 
      TCOS (tco_val v # map tco_val vs) (tco_stack sfs)" by (metis evtco_return)
    hence "TCOS (tco_val v # map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o 
      tco_state (S\<^sub>e (v # vs) ((env, []) # sfs))" by simp
    moreover from ev\<^sub>e_lookup have "tco_state (S\<^sub>e vs ((env, [Lookup\<^sub>e x]) # sfs)) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
      TCOS (tco_val v # map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs)" by simp
    ultimately have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (tco_state (S\<^sub>e vs ((env, [Lookup\<^sub>e x]) # sfs)))
      (tco_state (S\<^sub>e (v # vs) ((env, []) # sfs)))" by (metis iter_refl iter_step)
    with Nil show ?thesis by simp
  next
    case (Cons op cd)
    moreover from ev\<^sub>e_lookup have "tco_state (S\<^sub>e vs ((env, Lookup\<^sub>e x # op # cd) # sfs)) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
      tco_state (S\<^sub>e (v # vs) ((env, op # cd) # sfs))" by simp
    ultimately show ?thesis by (metis iter_one)
  qed
next
  case (ev\<^sub>e_pushcon vs env k cd sfs)
  thus ?case 
  proof (cases cd)
    case Nil
    have "TCOS (TCOConst k # map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o 
        TCOS (TCOConst k # map tco_val vs) (tco_stack sfs)" by (metis evtco_return)
    hence "TCOS (TCOConst k # map tco_val vs) 
      ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o 
        tco_state (S\<^sub>e (Const\<^sub>e k # vs) ((env, []) # sfs))" by simp
    moreover have "tco_state (S\<^sub>e vs ((env, [PushCon\<^sub>e k]) # sfs)) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
      TCOS (TCOConst k # map tco_val vs) 
        ((map tco_val env, [], TCOReturn) # tco_stack sfs)" by simp
    ultimately have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (tco_state (S\<^sub>e vs ((env, [PushCon\<^sub>e k]) # sfs)))
      (tco_state (S\<^sub>e (Const\<^sub>e k # vs) ((env, []) # sfs)))" by (metis iter_refl iter_step)
    with Nil show ?thesis by simp
  next
    case (Cons op cd)
    moreover have "tco_state (S\<^sub>e vs ((env, PushCon\<^sub>e k # op # cd) # sfs)) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
      tco_state (S\<^sub>e (Const\<^sub>e k # vs) ((env, op # cd) # sfs))" by simp
    ultimately show ?thesis by (metis iter_one)
  qed
next
  case (ev\<^sub>e_pushlam vs env cd' cd sfs)
  thus ?case 
  proof (cases cd)
    case Nil
    have "TCOS (map tco_val vs) ((map tco_val env, 
      [TCOPushLam (tco_cd cd') (tco_r cd')], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o  
        TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r cd') # map tco_val vs) 
          ((map tco_val env, [], TCOReturn) # tco_stack sfs)" by (metis evtco_pushlam)
    hence X: "tco_state (S\<^sub>e vs ((env, [PushLam\<^sub>e cd']) # sfs)) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
      TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r cd') # map tco_val vs) 
        ((map tco_val env, [], TCOReturn) # tco_stack sfs)" by simp
    have "TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r cd') # 
      map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
        TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r cd') # map tco_val vs) (tco_stack sfs)" 
          by (metis evtco_return)
    hence "TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r cd') # 
      map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
        tco_state (S\<^sub>e (Lam\<^sub>e env cd' # vs) ((env, []) # sfs))" by simp
    with X have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (tco_state (S\<^sub>e vs ((env, [PushLam\<^sub>e cd']) # sfs)))
      (tco_state (S\<^sub>e (Lam\<^sub>e env cd' # vs) ((env, []) # sfs)))" by (metis iter_refl iter_step)
    with Nil show ?thesis by simp
  next
    case (Cons op cd)
    have "TCOS (map tco_val vs) ((map tco_val env, TCOPushLam (tco_cd cd') (tco_r cd') # 
      tco_cd (op # cd), tco_r (op # cd)) # tco_stack sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
        TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r cd') # map tco_val vs) 
          ((map tco_val env, tco_cd (op # cd), tco_r (op # cd)) # tco_stack sfs)" 
      by (metis evtco_pushlam)
    hence "tco_state (S\<^sub>e vs ((env, PushLam\<^sub>e cd' # op # cd) # sfs)) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
      tco_state (S\<^sub>e (Lam\<^sub>e env cd' # vs) ((env, op # cd) # sfs))" by simp
    with Cons show ?thesis by (metis iter_one)
  qed
next
  case (ev\<^sub>e_apply v env' cd' vs env cd sfs)
  thus ?case 
  proof (cases cd)
    case Nil note CD = Nil
    thus ?thesis
    proof (cases cd')
      case Nil
      have "TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # tco_stack sfs) 
        \<leadsto>\<^sub>e\<^sub>c\<^sub>o TCOS (map tco_val vs) (tco_stack sfs)" by (metis evtco_return)
      hence "TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # tco_stack sfs) 
        \<leadsto>\<^sub>e\<^sub>c\<^sub>o tco_state (S\<^sub>e vs ((v # env', []) # (env, []) # sfs))" by simp
      hence X: "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # 
        tco_stack sfs)) (tco_state (S\<^sub>e vs ((v # env', []) # (env, []) # sfs)))" by (metis iter_one)
      have "TCOS (tco_val v # TCOLam (map tco_val env') [] TCOReturn # 
        map tco_val vs) ((map tco_val env, [], TCOJump) # tco_stack sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
          TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # 
            tco_stack sfs)" by (metis evtco_jump)
      hence "tco_state (S\<^sub>e (v # Lam\<^sub>e env' [] # vs) ((env, [Apply\<^sub>e]) # sfs)) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
        TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # tco_stack sfs)" 
          by simp
      with X have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (tco_state (S\<^sub>e (v # Lam\<^sub>e env' [] # vs) ((env, [Apply\<^sub>e]) # sfs)))
        (tco_state (S\<^sub>e vs ((v # env', []) # (env, []) # sfs)))" using iter_step by fast
      with CD Nil show ?thesis by simp
    next
      case (Cons op' cd'')
      have "TCOS (tco_val v # TCOLam (map tco_val env') (tco_cd (op' # cd'')) (tco_r (op' # cd'')) # 
        map tco_val vs) ((map tco_val env, [], TCOJump) # tco_stack sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
          TCOS (map tco_val vs) ((tco_val v # map tco_val env', tco_cd (op' # cd''), 
            tco_r (op' # cd'')) # tco_stack sfs)"  by (metis evtco_jump)
      hence "tco_state (S\<^sub>e (v # Lam\<^sub>e env' (op' # cd'') # vs) ((env, [Apply\<^sub>e]) # sfs)) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
        tco_state (S\<^sub>e vs ((v # env', op' # cd'') # (env, []) # sfs))" by simp
      with Nil Cons show ?thesis by (metis iter_one)
    qed
  next
    case (Cons op cd) note CD = Cons
    thus ?thesis
    proof (cases cd')
      case Nil
      have "TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # 
        (map tco_val env, tco_cd (op # cd), tco_r (op # cd)) # tco_stack sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
          TCOS (map tco_val vs) ((map tco_val env, tco_cd (op # cd), 
            tco_r (op # cd)) # tco_stack sfs)" by (metis evtco_return)
      hence "TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # 
        (map tco_val env, tco_cd (op # cd), tco_r (op # cd)) # tco_stack sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
            tco_state (S\<^sub>e vs ((v # env', []) # (env, op # cd) # sfs))" by simp
      hence X: "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # 
        (map tco_val env, tco_cd (op # cd), tco_r (op # cd)) # tco_stack sfs)) 
          (tco_state (S\<^sub>e vs ((v # env', []) # (env, op # cd) # sfs)))" by (metis iter_one)
      have "tco_state (S\<^sub>e (v # Lam\<^sub>e env' [] # vs) ((env, Apply\<^sub>e # op # cd) # sfs)) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
        TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn) # 
          (map tco_val env, tco_cd (op # cd), tco_r (op # cd)) # tco_stack sfs)" by simp
      with X have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (tco_state (S\<^sub>e (v # Lam\<^sub>e env' [] # vs) 
        ((env, Apply\<^sub>e # op # cd) # sfs)))
          (tco_state (S\<^sub>e vs ((v # env', []) # (env, op # cd) # sfs)))" 
        using iter_step by fast
      with Cons Nil show ?thesis by simp
    next
      case (Cons op' cd')
      have "tco_state (S\<^sub>e (v # Lam\<^sub>e env' (op' # cd') # vs) 
        ((env, Apply\<^sub>e # op # cd) # sfs)) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
          tco_state (S\<^sub>e vs ((v # env', (op' # cd')) # (env, op # cd) # sfs))" by simp
      with CD Cons show ?thesis by (metis iter_one)
    qed
  qed
qed simp_all

lemma iter_tco_eval [simp]: "iter (\<leadsto>\<^sub>e) \<Sigma> \<Sigma>' \<Longrightarrow> iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (tco_state \<Sigma>) (tco_state \<Sigma>')"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) (simp, metis iter_append correcttco)

end