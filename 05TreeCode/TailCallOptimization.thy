theory TailCallOptimization
  imports TreeCode "../00Utils/Iteration"
begin

fun tco_r :: "tree_code list \<Rightarrow> tree_return" where
  "tco_r [] = TReturn"
| "tco_r (TApply # cd) = (case cd of 
      [] \<Rightarrow> TJump
    | _ \<Rightarrow> tco_r cd)"
| "tco_r (op # cd) = tco_r cd"

fun tco :: "tree_code list \<Rightarrow> tree_code list" where
  "tco [] = []"
| "tco (TApply # cd) = (case cd of 
      [] \<Rightarrow> []
    | _ \<Rightarrow> TApply # tco cd)"
| "tco (TPushLam cd' r # cd) = TPushLam (tco cd') (tco_r cd') # tco cd"
| "tco (op # cd) = op # tco cd"

primrec tco_val :: "tclosure \<Rightarrow> tclosure" where
  "tco_val (TConst k) = TConst k"
| "tco_val (TLam vs cd r) = TLam (map tco_val vs) (tco cd) (tco_r cd)"

fun tco_stack_frame :: "tree_stack_frame \<Rightarrow> tree_stack_frame" where
  "tco_stack_frame (vs, cd, r) = (map tco_val vs, tco cd, tco_r cd)"

fun not_dead_frame :: "tree_stack_frame \<Rightarrow> bool" where
  "not_dead_frame (vs, cd, r) = (cd \<noteq> [] \<or> r \<noteq> TReturn)"

abbreviation tco_stack :: "tree_stack_frame list \<Rightarrow> tree_stack_frame list" where
  "tco_stack sfs \<equiv> filter not_dead_frame (map tco_stack_frame sfs)"

primrec tco_state :: "tree_code_state \<Rightarrow> tree_code_state" where
  "tco_state (TS vs sfs) = TS (map tco_val vs) (tco_stack sfs)"

fun jump_free_code :: "tree_code list \<Rightarrow> bool" where
  "jump_free_code [] = True"
| "jump_free_code (TPushLam cd' r # cd) = (jump_free_code cd' \<and> r \<noteq> TJump \<and> jump_free_code cd)"
| "jump_free_code (op # cd) = jump_free_code cd"

primrec jump_free_val :: "tclosure \<Rightarrow> bool" where
  "jump_free_val (TConst k) = True"
| "jump_free_val (TLam t cd r) =  (jump_free_code cd \<and> r \<noteq> TJump)"

fun jump_free_frame :: "tree_stack_frame \<Rightarrow> bool" where
  "jump_free_frame (vs, cd, r) =  (list_all jump_free_val vs \<and> jump_free_code cd \<and> r \<noteq> TJump)"

primrec jump_free_state :: "tree_code_state \<Rightarrow> bool" where
  "jump_free_state (TS vs sfs) = (list_all jump_free_val vs \<and> list_all jump_free_frame sfs)"

theorem completetco [simp]: "tco_state \<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> \<exists>\<Sigma>''. \<Sigma> \<leadsto>\<^sub>t \<Sigma>'' \<and> \<Sigma>' = tco_state \<Sigma>''"
  by simp

lemma [simp]: "tco (op # cd) = [] \<Longrightarrow> tco_r (op # cd) = TJump"
  by (induction op) (simp_all split: list.splits)

lemma tco_never_dead [simp]: "not_dead_frame (vs, tco (op # cd), tco_r (op # cd))"
  by (induction cd rule: tco.induct) (simp_all split: list.splits)

lemma jump_free_persists [simp]: "\<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> jump_free_state \<Sigma> \<Longrightarrow> jump_free_state \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: evalt.induct) auto

theorem correcttco [simp]: "\<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> jump_free_state \<Sigma> \<Longrightarrow> 
  iter (\<leadsto>\<^sub>t) (tco_state \<Sigma>) (tco_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: evalt.induct)
  case (evt_lookup env x v vs cd r sfs)
  thus ?case 
  proof (cases cd)
    case Nil
    from evt_lookup have "tco_state (TS vs ((env, [TLookup x], r) # sfs)) \<leadsto>\<^sub>t
      TS (tco_val v # map tco_val vs) ((map tco_val env, [], TReturn) # tco_stack sfs)" by simp
    moreover have "TS (tco_val v # map tco_val vs) ((map tco_val env, [], TReturn) # tco_stack sfs)
      \<leadsto>\<^sub>t tco_state (TS (v # vs) ((env, [], r) # sfs))" by simp
    ultimately have "iter (\<leadsto>\<^sub>t) (tco_state (TS vs ((env, [TLookup x], r) # sfs)))
      (tco_state (TS (v # vs) ((env, [], r) # sfs)))" by (metis iter_refl iter_step)
    with Nil show ?thesis by simp
  next
    case (Cons op cd)
    moreover from evt_lookup have "tco_state (TS vs ((env, TLookup x # op # cd, r) # sfs)) \<leadsto>\<^sub>t
      tco_state (TS (v # vs) ((env, op # cd, r) # sfs))" by simp
    ultimately show ?thesis by (metis iter_one)
  qed
next
  case (evt_pushcon vs env k cd r sfs)
  thus ?case 
  proof (cases cd)
    case Nil
    have "tco_state (TS vs ((env, [TPushCon k], r) # sfs)) \<leadsto>\<^sub>t
      TS (TConst k # map tco_val vs) ((map tco_val env, [], TReturn) # tco_stack sfs)" by simp
    moreover have "TS (TConst k # map tco_val vs) ((map tco_val env, [], TReturn) # tco_stack sfs)
      \<leadsto>\<^sub>t tco_state (TS (TConst k # vs) ((env, [], r) # sfs))" by simp
    ultimately have "iter (\<leadsto>\<^sub>t) (tco_state (TS vs ((env, [TPushCon k], r) # sfs)))
      (tco_state (TS (TConst k # vs) ((env, [], r) # sfs)))" by (metis iter_refl iter_step)
    with Nil show ?thesis by simp
  next
    case (Cons op cd)
    moreover from evt_lookup have "tco_state (TS vs ((env, TPushCon k # op # cd, r) # sfs)) \<leadsto>\<^sub>t
      tco_state (TS (TConst k # vs) ((env, op # cd, r) # sfs))" by simp
    ultimately show ?thesis by (metis iter_one)
  qed
next
  case (evt_pushlam vs env cd' r' cd r sfs)
  thus ?case 
  proof (cases cd)
    case Nil
    have "tco_state (TS vs ((env, [TPushLam cd' r'], r) # sfs)) \<leadsto>\<^sub>t
      TS (TLam (map tco_val env) (tco cd') (tco_r cd') # map tco_val vs) 
        ((map tco_val env, [], TReturn) # tco_stack sfs)" by simp
    moreover have "TS (TLam (map tco_val env) (tco cd') (tco_r cd') # map tco_val vs) 
      ((map tco_val env, [], TReturn) # tco_stack sfs) \<leadsto>\<^sub>t 
        tco_state (TS (TLam env cd' r' # vs) ((env, [], r) # sfs))" by simp
    ultimately have "iter (\<leadsto>\<^sub>t) (tco_state (TS vs ((env, [TPushLam cd' r'], r) # sfs)))
      (tco_state (TS (TLam env cd' r' # vs) ((env, [], r) # sfs)))" by (metis iter_refl iter_step)
    with Nil show ?thesis by simp
  next
    case (Cons op cd)
    moreover from evt_lookup have "tco_state (TS vs ((env, TPushLam cd' r' # op # cd, r) # sfs)) \<leadsto>\<^sub>t
      tco_state (TS (TLam env cd' r' # vs) ((env, op # cd, r) # sfs))" by simp
    ultimately show ?thesis by (metis iter_one)
  qed
next
  case (evt_apply v env cd' r' vs cd r sfs)
  thus ?case 
  proof (cases cd)
    case Nil note CD = Nil
    thus ?thesis
    proof (cases cd')
      case Nil
      have "TS (map tco_val vs) ((tco_val v # map tco_val env, [], TReturn) # tco_stack sfs) \<leadsto>\<^sub>t
          tco_state (TS vs ((v # env, [], r') # (env, [], r) # sfs))" by simp
      hence "iter (\<leadsto>\<^sub>t) (TS (map tco_val vs) 
        ((tco_val v # map tco_val env, [], TReturn) # tco_stack sfs))
          (tco_state (TS vs ((v # env, [], r') # (env, [], r) # sfs)))" by (metis iter_one)
      moreover have "tco_state (TS (v # TLam env [] r' # vs) ((env, [TApply], r) # sfs)) \<leadsto>\<^sub>t
          TS (map tco_val vs) ((tco_val v # map tco_val env, [], TReturn) # tco_stack sfs)" by simp
      ultimately have "iter (\<leadsto>\<^sub>t) (tco_state (TS (v # TLam env [] r' # vs) 
        ((env, [TApply], r) # sfs)))
          (tco_state (TS vs ((v # env, [], r') # (env, [], r) # sfs)))" using iter_step by fast
      with CD Nil show ?thesis by simp
    next
      case (Cons op' cd')
      have "tco_state (TS (v # TLam env (op' # cd') r' # vs) ((env, [TApply], r) # sfs)) \<leadsto>\<^sub>t
        tco_state (TS vs ((v # env, op' # cd', r') # (env, [], r) # sfs))" by simp
      with Nil Cons show ?thesis by (metis iter_one)
    qed
  next
    case (Cons op cd) note CD = Cons
    thus ?thesis
    proof (cases cd')
      case Nil
      have "TS (map tco_val vs) ((tco_val v # map tco_val env, [], TReturn) # 
        (map tco_val env, tco (op # cd), tco_r (op # cd)) # tco_stack sfs) \<leadsto>\<^sub>t
          tco_state (TS vs ((v # env, [], r') # (env, op # cd, r) # sfs))" by simp
      hence "iter (\<leadsto>\<^sub>t) (TS (map tco_val vs) ((tco_val v # map tco_val env, [], TReturn) # 
        (map tco_val env, tco (op # cd), tco_r (op # cd)) # tco_stack sfs)) 
          (tco_state (TS vs ((v # env, [], r') # (env, op # cd, r) # sfs)))" by (metis iter_one)
      moreover have "tco_state (TS (v # TLam env [] r' # vs) ((env, TApply # op # cd, r) # sfs)) \<leadsto>\<^sub>t
        TS (map tco_val vs) ((tco_val v # map tco_val env, [], TReturn) # 
          (map tco_val env, tco (op # cd), tco_r (op # cd)) # tco_stack sfs)" by simp
      ultimately have "iter (\<leadsto>\<^sub>t) (tco_state (TS (v # TLam env [] r' # vs) 
        ((env, TApply # op # cd, r) # sfs)))
          (tco_state (TS vs ((v # env, [], r') # (env, op # cd, r) # sfs)))" 
        using iter_step by fast
      with Cons Nil show ?thesis by simp
    next
      case (Cons op' cd')
      from evt_lookup have "tco_state (TS (v # TLam env (op' # cd') r' # vs) 
        ((env, TApply # op # cd, r) # sfs)) \<leadsto>\<^sub>t
          tco_state (TS vs ((v # env, (op' # cd'), r') # (env, op # cd, r) # sfs))" by simp
      with CD Cons show ?thesis by (metis iter_one)
    qed
  qed
qed simp_all

lemma iter_tco_eval [simp]: "iter (\<leadsto>\<^sub>t) \<Sigma> \<Sigma>' \<Longrightarrow> jump_free_state \<Sigma> \<Longrightarrow> 
    iter (\<leadsto>\<^sub>t) (tco_state \<Sigma>) (tco_state \<Sigma>')"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) (simp, metis iter_append correcttco jump_free_persists)

end