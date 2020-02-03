theory TailCallOptimization
  imports TailCall "../05TreeCode/TreeCode" "../00Utils/Iteration"
begin

fun tco_r :: "tree_code list \<Rightarrow> tco_return" where
  "tco_r [] = TCOReturn"
| "tco_r (TApply # cd) = (case cd of 
      [] \<Rightarrow> TCOJump
    | _ \<Rightarrow> tco_r cd)"
| "tco_r (op # cd) = tco_r cd"

fun tco :: "tree_code list \<Rightarrow> tco_code list" where
  "tco [] = []"
| "tco (TLookup x # cd) = TCOLookup x # tco cd"
| "tco (TPushCon k # cd) = TCOPushCon k # tco cd"
| "tco (TPushLam cd' # cd) = TCOPushLam (tco cd') (tco_r cd') # tco cd"
| "tco (TApply # cd) = (case cd of 
      [] \<Rightarrow> []
    | _ \<Rightarrow> TCOApply # tco cd)"

primrec tco_val :: "tclosure \<Rightarrow> tco_closure" where
  "tco_val (TConst k) = TCOConst k"
| "tco_val (TLam vs cd) = TCOLam (map tco_val vs) (tco cd) (tco_r cd)"

fun tco_stack_frame :: "tree_stack_frame \<Rightarrow> tco_stack_frame" where
  "tco_stack_frame (vs, cd) = (map tco_val vs, tco cd, tco_r cd)"

fun not_dead_frame :: "tco_stack_frame \<Rightarrow> bool" where
  "not_dead_frame (vs, cd, r) = (cd \<noteq> [] \<or> r \<noteq> TCOReturn)"

abbreviation tco_stack :: "tree_stack_frame list \<Rightarrow> tco_stack_frame list" where
  "tco_stack sfs \<equiv> filter not_dead_frame (map tco_stack_frame sfs)"

primrec tco_state :: "tree_code_state \<Rightarrow> tco_code_state" where
  "tco_state (TS vs sfs) = TCOS (map tco_val vs) (tco_stack sfs)"

theorem completetco [simp]: "tco_state \<Sigma> \<leadsto>\<^sub>t\<^sub>c\<^sub>o \<Sigma>' \<Longrightarrow> \<exists>\<Sigma>''. \<Sigma> \<leadsto>\<^sub>t \<Sigma>'' \<and> \<Sigma>' = tco_state \<Sigma>''"
  by simp

lemma [simp]: "tco (op # cd) = [] \<Longrightarrow> tco_r (op # cd) = TCOJump"
  by (induction op) (simp_all split: list.splits)

lemma tco_never_dead [simp]: "not_dead_frame (vs, tco (op # cd), tco_r (op # cd))"
  by (induction cd rule: tco.induct) (simp_all split: list.splits)

theorem correcttco [simp]: "\<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state \<Sigma>) (tco_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: evalt.induct)
  case (evt_lookup env x v vs cd sfs)
  thus ?case 
  proof (cases cd)
    case Nil
    from evt_lookup have "tco_state (TS vs ((env, [TLookup x]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      TCOS (tco_val v # map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs)" by simp
    moreover have "TCOS (tco_val v # map tco_val vs) 
      ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
        tco_state (TS (v # vs) ((env, []) # sfs))" by simp
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
    have "tco_state (TS vs ((env, [TPushCon k]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      TCOS (TCOConst k # map tco_val vs) ((map tco_val env, [], TCOReturn) # tco_stack sfs)" by simp
    moreover have "TCOS (TCOConst k # map tco_val vs) 
      ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
        tco_state (TS (TConst k # vs) ((env, []) # sfs))" by simp
    ultimately have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS vs ((env, [TPushCon k]) # sfs)))
      (tco_state (TS (TConst k # vs) ((env, []) # sfs)))" by (metis iter_refl iter_step)
    with Nil show ?thesis by simp
  next
    case (Cons op cd)
    moreover from evt_lookup have "tco_state (TS vs ((env, TPushCon k # op # cd) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      tco_state (TS (TConst k # vs) ((env, op # cd) # sfs))" by simp
    ultimately show ?thesis by (metis iter_one)
  qed
next
  case (evt_pushlam vs env cd' cd sfs)
  thus ?case 
  proof (cases cd)
    case Nil
    have "tco_state (TS vs ((env, [TPushLam cd']) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      TCOS (TCOLam (map tco_val env) (tco cd') (tco_r cd') # map tco_val vs) 
        ((map tco_val env, [], TCOReturn) # tco_stack sfs)" by simp
    moreover have "TCOS (TCOLam (map tco_val env) (tco cd') (tco_r cd') # map tco_val vs) 
      ((map tco_val env, [], TCOReturn) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        tco_state (TS (TLam env cd' # vs) ((env, []) # sfs))" by simp
    ultimately have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS vs ((env, [TPushLam cd']) # sfs)))
      (tco_state (TS (TLam env cd' # vs) ((env, []) # sfs)))" by (metis iter_refl iter_step)
    with Nil show ?thesis by simp
  next
    case (Cons op cd)
    moreover from evt_lookup have "tco_state (TS vs ((env, TPushLam cd' # op # cd) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      tco_state (TS (TLam env cd' # vs) ((env, op # cd) # sfs))" by simp
    ultimately show ?thesis by (metis iter_one)
  qed
next
  case (evt_apply v env cd' vs cd sfs)
  thus ?case 
  proof (cases cd)
    case Nil note CD = Nil
    thus ?thesis
    proof (cases cd')
      case Nil
      have "TCOS (map tco_val vs) ((tco_val v # map tco_val env, [], TCOReturn) # tco_stack sfs) 
        \<leadsto>\<^sub>t\<^sub>c\<^sub>o tco_state (TS vs ((v # env, []) # (env, []) # sfs))" by simp
      hence "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (map tco_val vs) 
        ((tco_val v # map tco_val env, [], TCOReturn) # tco_stack sfs))
          (tco_state (TS vs ((v # env, []) # (env, []) # sfs)))" by (metis iter_one)
      moreover have "tco_state (TS (v # TLam env [] # vs) ((env, [TApply]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        TCOS (map tco_val vs) ((tco_val v # map tco_val env, [], TCOReturn) # tco_stack sfs)" 
          by simp
      ultimately have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS (v # TLam env [] # vs) ((env, [TApply]) # sfs)))
        (tco_state (TS vs ((v # env, []) # (env, []) # sfs)))" using iter_step by fast
      with CD Nil show ?thesis by simp
    next
      case (Cons op' cd')
      have "tco_state (TS (v # TLam env (op' # cd') # vs) ((env, [TApply]) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        tco_state (TS vs ((v # env, op' # cd') # (env, []) # sfs))" by simp
      with Nil Cons show ?thesis by (metis iter_one)
    qed
  next
    case (Cons op cd) note CD = Cons
    thus ?thesis
    proof (cases cd')
      case Nil
      have "TCOS (map tco_val vs) ((tco_val v # map tco_val env, [], TCOReturn) # 
        (map tco_val env, tco (op # cd), tco_r (op # cd)) # tco_stack sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
          tco_state (TS vs ((v # env, []) # (env, op # cd) # sfs))" by simp
      hence "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (map tco_val vs) ((tco_val v # map tco_val env, [], TCOReturn) # 
        (map tco_val env, tco (op # cd), tco_r (op # cd)) # tco_stack sfs)) 
          (tco_state (TS vs ((v # env, []) # (env, op # cd) # sfs)))" by (metis iter_one)
      moreover have "tco_state (TS (v # TLam env [] # vs) ((env, TApply # op # cd) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        TCOS (map tco_val vs) ((tco_val v # map tco_val env, [], TCOReturn) # 
          (map tco_val env, tco (op # cd), tco_r (op # cd)) # tco_stack sfs)" by simp
      ultimately have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS (v # TLam env [] # vs) 
        ((env, TApply # op # cd) # sfs)))
          (tco_state (TS vs ((v # env, []) # (env, op # cd) # sfs)))" 
        using iter_step by fast
      with Cons Nil show ?thesis by simp
    next
      case (Cons op' cd')
      from evt_lookup have "tco_state (TS (v # TLam env (op' # cd') # vs) 
        ((env, TApply # op # cd) # sfs)) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
          tco_state (TS vs ((v # env, (op' # cd')) # (env, op # cd) # sfs))" by simp
      with CD Cons show ?thesis by (metis iter_one)
    qed
  qed
qed simp_all

lemma iter_tco_eval [simp]: "iter (\<leadsto>\<^sub>t) \<Sigma> \<Sigma>' \<Longrightarrow> iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state \<Sigma>) (tco_state \<Sigma>')"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) (simp, metis iter_append correcttco)

end