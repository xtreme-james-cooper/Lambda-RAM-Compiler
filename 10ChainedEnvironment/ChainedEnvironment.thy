theory ChainedEnvironment
  imports "../08FlatCode/ByteCode" "../09HeapMemory/Heap"
begin

datatype ceclosure = 
  CEConst nat
  | CELam ptr nat

datatype chained_state = 
  CES "ceclosure heap" "(ptr \<times> ptr) heap" "ptr list" "(ptr \<times> nat) list"

primrec chain_lookup :: "('a \<times> ptr) heap \<Rightarrow> ptr \<Rightarrow> nat \<Rightarrow> 'a" where
  "chain_lookup h p 0 = (case hlookup h p of (a, b) \<Rightarrow> a)"
| "chain_lookup h p (Suc x) = chain_lookup h (case hlookup h p of (a, b) \<Rightarrow> b) x"

inductive evalce :: "byte_code list \<Rightarrow> chained_state \<Rightarrow> chained_state \<Rightarrow> bool" 
    (infix "\<tturnstile> _ \<leadsto>\<^sub>c\<^sub>e" 50) where
  evce_lookup [simp]: "cd ! pc = BLookup x \<Longrightarrow> 
    cd \<tturnstile> CES h env vs ((p, Suc pc) # sfs) \<leadsto>\<^sub>c\<^sub>e CES h env (chain_lookup env p x # vs) ((p, pc) # sfs)"
| evce_pushcon [simp]: "cd ! pc = BPushCon k \<Longrightarrow> halloc h (CEConst k) = (h', v) \<Longrightarrow>
    cd \<tturnstile> CES h env vs ((p, Suc pc) # sfs) \<leadsto>\<^sub>c\<^sub>e CES h' env (v # vs) ((p, pc) # sfs)"
| evce_pushlam [simp]: "cd ! pc = BPushLam pc' \<Longrightarrow> 
    halloc h (CELam p pc') = (h', v) \<Longrightarrow> 
      cd \<tturnstile> CES h env vs ((p, Suc pc) # sfs) \<leadsto>\<^sub>c\<^sub>e CES h' env (v # vs) ((p, pc) # sfs)"
| evce_apply [simp]: "cd ! pc = BApply \<Longrightarrow> hlookup h v2 = CELam p' pc' \<Longrightarrow>
    halloc env (v1, p') = (env', p'') \<Longrightarrow> 
      cd \<tturnstile> CES h env (v1 # v2 # vs) ((p, Suc pc) # sfs) \<leadsto>\<^sub>c\<^sub>e 
        CES h env' vs ((p'', pc') # (p, pc) # sfs)"
| evce_return [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    cd \<tturnstile> CES h env vs ((p, Suc pc) # sfs) \<leadsto>\<^sub>c\<^sub>e CES h env vs sfs"
| evce_jump [simp]: "cd ! pc = BJump \<Longrightarrow> hlookup h v2 = CELam p' pc' \<Longrightarrow>
    halloc env (v1, p') = (env', p'') \<Longrightarrow>
      cd \<tturnstile> CES h env (v1 # v2 # vs) ((p, Suc pc) # sfs) \<leadsto>\<^sub>c\<^sub>e CES h env' vs ((p'', pc') # sfs)"

theorem determinismh: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>c\<^sub>e \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>c\<^sub>e \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalce.induct)
  case (evce_lookup cd pc x h env vs p sfs)
  from evce_lookup(2, 1) show ?case 
    by (induction cd "CES h env vs ((p, Suc pc) # sfs)" \<Sigma>'' rule: evalce.induct) simp_all 
next
  case (evce_pushcon cd pc k h h' v env vs p sfs)
  from evce_pushcon(3, 1, 2) show ?case 
    by (induction cd "CES h env vs ((p, Suc pc) # sfs)" \<Sigma>'' rule: evalce.induct) simp_all 
next
  case (evce_pushlam cd pc pc' h p h' v env vs sfs)
  from evce_pushlam(3, 1, 2) show ?case 
    by (induction cd "CES h env vs ((p, Suc pc) # sfs)" \<Sigma>'' rule: evalce.induct) simp_all 
next
  case (evce_apply cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  from evce_apply(4, 1, 2, 3) show ?case 
    by (induction cd "CES h env (v1 # v2 # vs) ((p, Suc pc) # sfs)" \<Sigma>'' rule: evalce.induct) 
       simp_all 
next
  case (evce_return cd pc h env vs p sfs)
  from evce_return(2, 1) show ?case 
    by (induction cd "CES h env vs ((p, Suc pc) # sfs)" \<Sigma>'' rule: evalce.induct) simp_all 
next
  case (evce_jump cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  from evce_jump(4, 1, 2, 3) show ?case 
    by (induction cd "CES h env (v1 # v2 # vs) ((p, Suc pc) # sfs)" \<Sigma>'' rule: evalce.induct) 
       simp_all 
qed

end