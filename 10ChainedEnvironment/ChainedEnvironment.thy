theory ChainedEnvironment
  imports "../08FlatCode/ByteCode" "../09HeapMemory/Heap"
begin

datatype ceclosure = 
  CEConst nat
  | CELam ptr nat

datatype chained_state = 
  CES "ceclosure heap" "(ptr \<times> ptr) heap" "ptr list" "(ptr \<times> nat) list" (code: "byte_code list")

fun chain_lookup :: "('a \<times> ptr) heap \<Rightarrow> ptr \<Rightarrow> nat \<rightharpoonup> 'a" where
  "chain_lookup h 0 x = None"
| "chain_lookup h (Suc p) 0 = Some (fst (hlookup h p))"
| "chain_lookup h (Suc p) (Suc x) = chain_lookup h (snd (hlookup h p)) x"

inductive evalce :: "chained_state \<Rightarrow> chained_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>c\<^sub>e" 50) where
  evce_lookup [simp]: "cd ! pc = BLookup x \<Longrightarrow> chain_lookup env p x = Some v \<Longrightarrow> 
    CES h env vs ((p, Suc pc) # sfs) cd \<leadsto>\<^sub>c\<^sub>e CES h env (v # vs) ((p, pc) # sfs) cd"
| evce_pushcon [simp]: "cd ! pc = BPushCon k \<Longrightarrow> halloc h (CEConst k) = (h', v) \<Longrightarrow>
    CES h env vs ((p, Suc pc) # sfs) cd \<leadsto>\<^sub>c\<^sub>e CES h' env (v # vs) ((p, pc) # sfs) cd"
| evce_pushlam [simp]: "cd ! pc = BPushLam pc' \<Longrightarrow> 
    halloc h (CELam p pc') = (h', v) \<Longrightarrow> CES h env vs ((p, Suc pc) # sfs) cd \<leadsto>\<^sub>c\<^sub>e 
      CES h' env (v # vs) ((p, pc) # sfs) cd"
| evce_apply [simp]: "cd ! pc = BApply \<Longrightarrow> hlookup h v2 = CELam p' pc' \<Longrightarrow>
    halloc env (v1, p') = (env', p'') \<Longrightarrow> CES h env (v1 # v2 # vs) ((p, Suc pc) # sfs) cd \<leadsto>\<^sub>c\<^sub>e 
      CES h env' vs ((p'', pc') # (p, pc) # sfs) cd"
| evce_return [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    CES h env vs ((p, Suc pc) # sfs) cd \<leadsto>\<^sub>c\<^sub>e CES h env vs sfs cd"
| evce_jump [simp]: "cd ! pc = BJump \<Longrightarrow> hlookup h v2 = CELam p' pc' \<Longrightarrow>
    halloc env (v1, p') = (env', p'') \<Longrightarrow>
      CES h env (v1 # v2 # vs) ((p, Suc pc) # sfs) cd \<leadsto>\<^sub>c\<^sub>e CES h env' vs ((p'', pc') # sfs) cd"

theorem determinismh: "\<Sigma> \<leadsto>\<^sub>c\<^sub>e \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>c\<^sub>e \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalce.induct)
  case (evce_lookup cd pc x env p v h vs sfs)
  from evce_lookup(3, 1, 2) show ?case 
    by (induction "CES h env vs ((p, Suc pc) # sfs) cd" \<Sigma>'' rule: evalce.induct) simp_all 
next
  case (evce_pushcon cd pc k h h' v env vs p sfs)
  from evce_pushcon(3, 1, 2) show ?case 
    by (induction "CES h env vs ((p, Suc pc) # sfs) cd" \<Sigma>'' rule: evalce.induct) simp_all 
next
  case (evce_pushlam cd pc pc' h p h' v env vs sfs)
  from evce_pushlam(3, 1, 2) show ?case 
    by (induction "CES h env vs ((p, Suc pc) # sfs) cd" \<Sigma>'' rule: evalce.induct) simp_all 
next
  case (evce_apply cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  from evce_apply(4, 1, 2, 3) show ?case 
    by (induction "CES h env (v1 # v2 # vs) ((p, Suc pc) # sfs) cd" \<Sigma>'' rule: evalce.induct) 
       simp_all 
next
  case (evce_return cd pc h env vs p sfs)
  from evce_return(2, 1) show ?case 
    by (induction "CES h env vs ((p, Suc pc) # sfs) cd" \<Sigma>'' rule: evalce.induct) simp_all 
next
  case (evce_jump cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  from evce_jump(4, 1, 2, 3) show ?case 
    by (induction "CES h env (v1 # v2 # vs) ((p, Suc pc) # sfs) cd" \<Sigma>'' rule: evalce.induct) 
       simp_all 
qed

lemma [simp]: "\<Sigma> \<leadsto>\<^sub>c\<^sub>e \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: evalce.induct) simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>c\<^sub>e) \<Sigma> \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

end