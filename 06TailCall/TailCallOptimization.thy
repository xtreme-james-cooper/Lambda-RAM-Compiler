theory TailCallOptimization
  imports TailCall "../05TreeCode/TreeCode" "../00Utils/Iteration"
begin

fun tco_r :: "nat \<Rightarrow> tree_code list \<Rightarrow> tco_return" where
  "tco_r d [] = TCOReturn d"
| "tco_r d (TApply # cd) = (case cd of 
      [] \<Rightarrow> TCOJump d
    | _ \<Rightarrow> tco_r d cd)"
| "tco_r d (op # cd) = tco_r d cd"

fun tco_cd :: "tree_code list \<Rightarrow> tco_code list" where
  "tco_cd [] = []"
| "tco_cd (TLookup x # cd) = TCOLookup x # tco_cd cd"
| "tco_cd (TPushCon k # cd) = TCOPushCon k # tco_cd cd"
| "tco_cd (TPushLam cd' d # cd) = TCOPushLam (tco_cd cd') (tco_r (Suc d) cd') d # tco_cd cd"
| "tco_cd (TApply # cd) = (case cd of 
      [] \<Rightarrow> []
    | _ \<Rightarrow> TCOApply # tco_cd cd)"

fun tco_cd_one :: "tree_code \<Rightarrow> tco_code" where
  "tco_cd_one (TLookup x) = TCOLookup x"
| "tco_cd_one (TPushCon k) = TCOPushCon k"
| "tco_cd_one (TPushLam cd' d) = TCOPushLam (tco_cd cd') (tco_r (Suc d) cd') d"
| "tco_cd_one TApply = TCOApply"

definition tco :: "tree_code list \<Rightarrow> tco_code list \<times> tco_return" where
  "tco cd = (tco_cd cd, tco_r 0 cd)"

primrec tco_val :: "tclosure \<Rightarrow> tco_closure" where
  "tco_val (TConst k) = TCOConst k"
| "tco_val (TLam vs cd) = TCOLam (map tco_val vs) (tco_cd cd) (tco_r (Suc (length vs)) cd)"

fun tco_stack_frame :: "tree_stack_frame \<Rightarrow> tco_stack_frame" where
  "tco_stack_frame (vs, cd) = (map tco_val vs, tco_cd cd, tco_r (length vs) cd)"

fun not_dead_frame :: "tco_stack_frame \<Rightarrow> bool" where
  "not_dead_frame (vs, cd, r) = (cd \<noteq> [] \<or> r \<noteq> TCOReturn (length vs))"

primrec dead_frame :: "tree_stack_frame \<Rightarrow> bool" where
  "dead_frame (vs, cd) = (cd = [])"

abbreviation tco_stack :: "tree_stack_frame list \<Rightarrow> tco_stack_frame list" where
  "tco_stack sfs \<equiv> filter not_dead_frame (map tco_stack_frame sfs)"

primrec tco_state :: "tree_code_state \<Rightarrow> tco_code_state" where
  "tco_state (TS vs sfs) = TCOS (map tco_val vs) (tco_stack sfs)"

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> tco_r d (op # cd) = tco_r d cd"
  by (induction op) (simp_all split: list.splits)

lemma tco_r_append [simp]: "cd' \<noteq> [] \<Longrightarrow> tco_r d (cd @ cd') = tco_r d cd'"
  by (induction cd) simp_all

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> tco_cd (op # cd) = tco_cd_one op # tco_cd cd"
  by (induction op) (simp_all split: list.splits)

lemma tco_cd_append [simp]: "cd' \<noteq> [] \<Longrightarrow> tco_cd (cd @ cd') = map tco_cd_one cd @ tco_cd cd'"
  by (induction cd) simp_all

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> cd' \<noteq> [] \<Longrightarrow> tco_cd (cd @ cd') \<noteq> []"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "(env, cd, r) # sfs = tco_stack sfs' \<Longrightarrow> \<exists>dsfs env' cd' sfs''. 
  sfs' = dsfs @ (env', cd') # sfs'' \<and> env = map tco_val env' \<and> cd = tco_cd cd' \<and> 
    r = tco_r (length env) cd' \<and> list_all dead_frame dsfs \<and> sfs = tco_stack sfs''"
proof (induction sfs')
  case (Cons sf sfs')
  thus ?case
  proof (induction sf)
    case (Pair env' cd')
    thus ?case
    proof (induction cd' rule: tco_cd.induct)
      case 1
      then obtain dsfs env'' cd' sfs'' where X: "sfs' = dsfs @ (env'', cd') # sfs'' \<and> 
        env = map tco_val env'' \<and> cd = tco_cd cd' \<and> r = tco_r (length env'') cd' \<and> 
          list_all dead_frame dsfs \<and> sfs = tco_stack sfs''" by auto
      hence "\<exists>dsfsx. (env', []) # dsfs @ (env'', cd') # sfs'' = dsfsx @ (env'', cd') # sfs'' \<and> 
          list_all dead_frame dsfsx \<and> sfs = tco_stack sfs''" by simp
      hence "\<exists>dsfsx sfs'''. 
        (env', []) # dsfs @ (env'', cd') # sfs'' = dsfsx @ (env'', cd') # sfs''' \<and> 
          list_all dead_frame dsfsx \<and> sfs = tco_stack sfs'''" by fastforce
      with X show ?case by fastforce
    next
      case (2 x cd')
      hence "env = map tco_val env' \<and> cd = TCOLookup x # tco_cd cd' \<and> r = tco_r (length env') cd' \<and> 
        sfs = tco_stack sfs'" by simp
      thus ?case by fastforce
    next
      case (3 k cd')
      hence "env = map tco_val env' \<and> cd = TCOPushCon k # tco_cd cd' \<and> 
        r = tco_r (length env') cd' \<and> sfs = tco_stack sfs'" by simp
      thus ?case by fastforce
    next
      case (4 cd\<^sub>l d cd')
      hence "env = map tco_val env' \<and> 
        cd = TCOPushLam (tco_cd cd\<^sub>l) (tco_r (Suc d) cd\<^sub>l) d # tco_cd cd' \<and> 
          r = tco_r (length env') cd' \<and> sfs = tco_stack sfs'" by simp
      thus ?case by fastforce
    next
      case (5 cd')
      thus ?case
      proof (cases cd')
        case Nil
        moreover with 5 have "env = map tco_val env' \<and> cd = [] \<and> r = TCOJump (length env') \<and> 
          sfs = tco_stack sfs'" by simp
        ultimately show ?thesis by fastforce
      next
        case (Cons op cd'')
        moreover with 5 have "env = map tco_val env' \<and> cd = TCOApply # tco_cd (op # cd'') \<and> 
          r = tco_r (length env') (op # cd'') \<and> sfs = tco_stack sfs'" by simp
        ultimately show ?thesis by fastforce
      qed
    qed
  qed
qed simp_all

lemma [dest]: "TCOS vs ((env, cd, r) # sfs) = tco_state \<Sigma> \<Longrightarrow> \<exists>dsfs vs' env' cd' sfs'. 
  \<Sigma> = TS vs' (dsfs @ (env', cd') # sfs') \<and> vs = map tco_val vs' \<and> env = map tco_val env' \<and> 
    cd = tco_cd cd' \<and> r = tco_r (length env) cd' \<and> list_all dead_frame dsfs \<and> sfs = tco_stack sfs'"
  by (induction \<Sigma>) auto

lemma [dest]: "TCOLookup x # cd = tco_cd cd' \<Longrightarrow> \<exists>cd''. cd' = TLookup x # cd'' \<and> cd = tco_cd cd''"
  by (induction cd' rule: tco_cd.induct) (simp_all split: list.splits)

lemma [simp]: "list_all dead_frame dsfs \<Longrightarrow> iter (\<leadsto>\<^sub>t) (TS vs (dsfs @ sfs)) (TS vs sfs)"
proof (induction dsfs)
  case (Cons sf dsfs)
  then obtain vs' where "sf = (vs', [])" by (cases sf) simp_all
  hence "TS vs ((sf # dsfs) @ sfs) \<leadsto>\<^sub>t TS vs (dsfs @ sfs)" by simp
  with Cons show ?case by simp
qed simp_all

lemma [simp]: "\<exists>\<Sigma>\<^sub>t \<Sigma>. iter (\<leadsto>\<^sub>t) (TS vs ((env, cd) # sfs)) \<Sigma>\<^sub>t \<and> 
  iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (map tco_val vs) 
    ((map tco_val env, tco_cd cd, tco_r (length env) cd) # tco_stack sfs)) \<Sigma> \<and> \<Sigma> = tco_state \<Sigma>\<^sub>t" 
proof (induction cd rule: tco_cd.induct)
  case 1
  have "TS vs ((env, []) # sfs) \<leadsto>\<^sub>t TS vs sfs" by simp
  hence X: "iter (\<leadsto>\<^sub>t) (TS vs ((env, []) # sfs)) (TS vs sfs)" by (metis iter_one)
  have "TCOS (map tco_val vs) ((map tco_val env, tco_cd [], tco_r (length env) []) # tco_stack sfs) 
    \<leadsto>\<^sub>t\<^sub>c\<^sub>o TCOS (map tco_val vs) (tco_stack sfs)" by simp
  hence Y: "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) 
    (TCOS (map tco_val vs) ((map tco_val env, tco_cd [], tco_r (length env) []) # tco_stack sfs)) 
      (TCOS (map tco_val vs) (tco_stack sfs))" by (metis iter_one)
  have "TCOS (map tco_val vs) (tco_stack sfs) = tco_state (TS vs sfs)" by simp
  with X Y show ?case by blast
next
  case (2 x cd)


  have X: "iter (\<leadsto>\<^sub>t) (TS vs ((env, TLookup x # cd) # sfs)) \<Sigma>\<^sub>t" by simp
  have Y: "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (map tco_val vs) 
    ((map tco_val env, tco_cd (TLookup x # cd), tco_r (TLookup x # cd)) # tco_stack sfs)) \<Sigma>" by simp
  have "\<Sigma> = tco_state \<Sigma>\<^sub>t" by simp
  with X Y show ?case by blast
next
  case (3 k cd)
  then show ?case by simpx
next
  case (4 cd' cd)
  then show ?case by simpx
next
  case (5 cd)
  then show ?case by simpx
qed 

theorem completetco [simp]: "tco_state \<Sigma>\<^sub>t \<leadsto>\<^sub>t\<^sub>c\<^sub>o \<Sigma>' \<Longrightarrow> \<exists>\<Sigma>\<^sub>t' \<Sigma>''. iter (\<leadsto>\<^sub>t) \<Sigma>\<^sub>t \<Sigma>\<^sub>t' \<and> 
  iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) \<Sigma>' \<Sigma>'' \<and> \<Sigma>'' = tco_state \<Sigma>\<^sub>t'"
proof (induction "tco_state \<Sigma>\<^sub>t" \<Sigma>' rule: evaltco.induct)
  case (evtco_lookup env x v vs cd r sfs)
  then obtain dsfs vs' env' cd' sfs' where S: "\<Sigma>\<^sub>t = TS vs' (dsfs @ (env', cd') # sfs') \<and> 
    vs = map tco_val vs' \<and> env = map tco_val env' \<and> TCOLookup x # cd = tco_cd cd' \<and> 
      r = tco_r (length env) cd' \<and> list_all dead_frame dsfs \<and> sfs = tco_stack sfs'" by blastx
  then obtain cd'' where C: "cd' = TLookup x # cd'' \<and> cd = tco_cd cd''" by blast
  from evtco_lookup S obtain v' where V: "lookup env' x = Some v' \<and> v = tco_val v'" by auto
  hence "TS vs' ((env', TLookup x # cd'') # sfs') \<leadsto>\<^sub>t TS (v' # vs') ((env', cd'') # sfs')" by simp
  moreover from S have "iter (\<leadsto>\<^sub>t) (TS vs' (dsfs @ (env', TLookup x # cd'') # sfs')) 
    (TS vs' ((env', TLookup x # cd'') # sfs'))" by simp
  ultimately have X: "iter (\<leadsto>\<^sub>t) (TS vs' (dsfs @ (env', TLookup x # cd'') # sfs')) 
    (TS (v' # vs') ((env', cd'') # sfs'))" by simp 


  have "iter (\<leadsto>\<^sub>t) (TS vs' (dsfs @ (env', TLookup x # cd'') # sfs')) \<Sigma>\<^sub>t' \<and> 
    iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (v # vs) ((env, cd, r) # sfs)) \<Sigma>'' \<and> \<Sigma>'' = tco_state \<Sigma>\<^sub>t'" by simp
  with S C show ?case by blast
next
case (evtco_pushcon vs env k cd r sfs)
  then show ?case by simp
next
case (evtco_pushlam vs env cd' r' cd r sfs)
  then show ?case by simp
next
  case (evtco_apply v env cd' r' vs cd r sfs)
  then show ?case by simp
next
  case (evtco_return vs env sfs)
  then show ?case by simp
next
  case (evtco_jump v env' cd' r' vs env sfs)
  then show ?case by simp
qed

lemma [simp]: "tco_cd (op # cd) = [] \<Longrightarrow> tco_r d (op # cd) = TCOJump d"
  by (induction op) (simp_all split: list.splits)

lemma tco_never_dead [simp]: "not_dead_frame (vs, tco_cd (op # cd), tco_r (length vs) (op # cd))"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

theorem correcttco [simp]: "\<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state \<Sigma>) (tco_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: evalt.induct)
  case (evt_lookup env x v vs cd sfs)
  thus ?case 
  proof (cases cd)
    case Nil
    have "TCOS (tco_val v # map tco_val vs) 
      ((map tco_val env, [], TCOReturn (length env)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
        TCOS (tco_val v # map tco_val vs) (tco_stack sfs)" by (metis evtco_return length_map)
    hence "TCOS (tco_val v # map tco_val vs) 
      ((map tco_val env, [], TCOReturn (length env)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
        tco_state (TS (v # vs) ((env, []) # sfs))" by simp
    moreover from evt_lookup have "tco_state (TS vs ((env, [TLookup x]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      TCOS (tco_val v # map tco_val vs) 
        ((map tco_val env, [], TCOReturn (length env)) # tco_stack sfs)" by simp
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
    have "TCOS (TCOConst k # map tco_val vs) 
      ((map tco_val env, [], TCOReturn (length env)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
        TCOS (TCOConst k # map tco_val vs) (tco_stack sfs)" by (metis evtco_return length_map)
    hence "TCOS (TCOConst k # map tco_val vs) 
      ((map tco_val env, [], TCOReturn (length env)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
        tco_state (TS (TConst k # vs) ((env, []) # sfs))" by simp
    moreover have "tco_state (TS vs ((env, [TPushCon k]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      TCOS (TCOConst k # map tco_val vs) 
        ((map tco_val env, [], TCOReturn (length env)) # tco_stack sfs)" by simp
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
      [TCOPushLam (tco_cd cd') (tco_r (Suc (length env)) cd') (length env)], 
        TCOReturn (length env)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o  TCOS (TCOLam (map tco_val env) (tco_cd cd') 
          (tco_r (Suc (length env)) cd') # map tco_val vs)
            ((map tco_val env, [], TCOReturn (length env)) # tco_stack sfs)" 
      by (metis evtco_pushlam length_map)
    hence X: "tco_state (TS vs ((env, [TPushLam cd' (length env)]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r (Suc (length env)) cd') # map tco_val vs) 
        ((map tco_val env, [], TCOReturn (length env)) # tco_stack sfs)" by simp
    have "TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r (Suc (length env)) cd') # 
      map tco_val vs) ((map tco_val env, [], TCOReturn (length env)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r (Suc (length env)) cd') # map tco_val vs) 
          (tco_stack sfs)" by (metis evtco_return length_map)
    hence "TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r (Suc (length env)) cd') # 
      map tco_val vs) ((map tco_val env, [], TCOReturn (length env)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        tco_state (TS (TLam env cd' # vs) ((env, []) # sfs))" by simp
    with X have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS vs ((env, [TPushLam cd' (length env)]) # sfs)))
      (tco_state (TS (TLam env cd' # vs) ((env, []) # sfs)))" by (metis iter_refl iter_step)
    with Nil show ?thesis by simp
  next
    case (Cons op cd)
    have "TCOS (map tco_val vs) ((map tco_val env, 
      TCOPushLam (tco_cd cd') (tco_r (Suc (length env)) cd') (length env) # tco_cd (op # cd), 
        tco_r (length env) (op # cd)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
          TCOS (TCOLam (map tco_val env) (tco_cd cd') (tco_r (Suc (length env)) cd') # 
            map tco_val vs) ((map tco_val env, tco_cd (op # cd), tco_r (length env) (op # cd)) # 
              tco_stack sfs)" 
      by (metis evtco_pushlam length_map)
    hence 
      "tco_state (TS vs ((env, TPushLam cd' (length env) # op # cd) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
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
      have "TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], 
        TCOReturn (length (tco_val v # map tco_val env'))) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
          TCOS (map tco_val vs) (tco_stack sfs)" by (metis evtco_return)
      hence "TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], 
        TCOReturn (Suc (length env'))) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
          tco_state (TS vs ((v # env', []) # (env, []) # sfs))" by simp
      hence X: "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (map tco_val vs) 
        ((tco_val v # map tco_val env', [], TCOReturn (Suc (length env'))) # tco_stack sfs))
          (tco_state (TS vs ((v # env', []) # (env, []) # sfs)))" by (metis iter_one)
      have "TCOS (tco_val v # TCOLam (map tco_val env') [] (TCOReturn (Suc (length env'))) # 
        map tco_val vs) ((map tco_val env, [], TCOJump (length env)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
          TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn (Suc (length env'))) # 
            tco_stack sfs)" by (metis evtco_jump length_map)
      hence "tco_state (TS (v # TLam env' [] # vs) ((env, [TApply]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn (Suc (length env'))) # 
          tco_stack sfs)" by simp
      with X have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS (v # TLam env' [] # vs) ((env, [TApply]) # sfs)))
        (tco_state (TS vs ((v # env', []) # (env, []) # sfs)))" using iter_step by fast
      with CD Nil show ?thesis by simp
    next
      case (Cons op' cd'')
      have "TCOS (tco_val v # TCOLam (map tco_val env') (tco_cd (op' # cd'')) 
        (tco_r (Suc (length env')) (op' # cd'')) # map tco_val vs) 
          ((map tco_val env, [], TCOJump (length env)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
            TCOS (map tco_val vs) ((tco_val v # map tco_val env', tco_cd (op' # cd''), 
              tco_r (Suc (length env')) (op' # cd'')) # tco_stack sfs)" 
        by (metis evtco_jump length_map)
      hence "tco_state (TS (v # TLam env' (op' # cd'') # vs) ((env, [TApply]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        tco_state (TS vs ((v # env', op' # cd'') # (env, []) # sfs))" by simp
      with Nil Cons show ?thesis by (metis iter_one)
    qed
  next
    case (Cons op cd) note CD = Cons
    thus ?thesis
    proof (cases cd')
      case Nil
      have "TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], 
        TCOReturn (length (tco_val v # map tco_val env'))) # (map tco_val env, tco_cd (op # cd),
          tco_r (length env) (op # cd)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
            TCOS (map tco_val vs) ((map tco_val env, tco_cd (op # cd), 
              tco_r (length env) (op # cd)) # tco_stack sfs)" by (metis evtco_return)
      hence "TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], 
        TCOReturn (Suc (length env'))) # (map tco_val env, tco_cd (op # cd), 
          tco_r (length env) (op # cd)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
            tco_state (TS vs ((v # env', []) # (env, op # cd) # sfs))" by simp
      hence X: "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], 
        TCOReturn (Suc (length env'))) # (map tco_val env, tco_cd (op # cd), 
          tco_r (length env) (op # cd)) # tco_stack sfs)) 
            (tco_state (TS vs ((v # env', []) # (env, op # cd) # sfs)))" by (metis iter_one)
      have "tco_state (TS (v # TLam env' [] # vs) ((env, TApply # op # cd) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        TCOS (map tco_val vs) ((tco_val v # map tco_val env', [], TCOReturn (Suc (length env'))) # 
          (map tco_val env, tco_cd (op # cd), tco_r (length env) (op # cd)) # tco_stack sfs)" 
            by simp
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