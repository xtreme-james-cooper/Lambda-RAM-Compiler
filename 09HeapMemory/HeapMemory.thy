theory HeapMemory
  imports "../08ByteCode/ByteCode" Heap
begin

datatype hclosure = 
  HConst nat
  | HLam "ptr list" nat

datatype heap_state = 
  HS "hclosure heap" "ptr list" "(ptr list \<times> nat) list"

inductive evalh :: "byte_code list \<Rightarrow> heap_state \<Rightarrow> heap_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>h" 50) where
  evh_lookup [simp]: "lookup cd pc = Some (BLookup x) \<Longrightarrow> lookup env x = Some v \<Longrightarrow> 
    cd \<tturnstile> HS h vs ((env, Suc pc) # sfs) \<leadsto>\<^sub>h HS h (v # vs) ((env, pc) # sfs)"
| evh_pushcon [simp]: "lookup cd pc = Some (BPushCon k) \<Longrightarrow> halloc h (HConst k) = (h', v) \<Longrightarrow>
    cd \<tturnstile> HS h vs ((env, Suc pc) # sfs) \<leadsto>\<^sub>h HS h' (v # vs) ((env, pc) # sfs)"
| evh_pushlam [simp]: "lookup cd pc = Some (BPushLam pc') \<Longrightarrow> halloc h (HLam env pc') = (h', v) \<Longrightarrow>
    cd \<tturnstile> HS h vs ((env, Suc pc) # sfs) \<leadsto>\<^sub>h HS h' (v # vs) ((env, pc) # sfs)"
| evh_apply [simp]: "lookup cd pc = Some BApply \<Longrightarrow> hlookup h v2 = HLam env' pc' \<Longrightarrow>
    cd \<tturnstile> HS h (v1 # v2 # vs) ((env, Suc pc) # sfs) \<leadsto>\<^sub>h
      HS h vs ((v1 # env', pc') # (env, pc) # sfs)"
| evh_return [simp]: "lookup cd pc = Some BReturn \<Longrightarrow> 
    cd \<tturnstile> HS h vs ((env, Suc pc) # sfs) \<leadsto>\<^sub>h HS h vs sfs"
| evh_jump [simp]: "lookup cd pc = Some BJump \<Longrightarrow> hlookup h v2 = HLam env' pc' \<Longrightarrow>
    cd \<tturnstile> HS h (v1 # v2 # vs) ((env, Suc pc) # sfs) \<leadsto>\<^sub>h HS h vs ((v1 # env', pc') # sfs)"

theorem determinismh: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>h \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>h \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction cd \<Sigma> \<Sigma>' rule: evalh.induct)
  case (evh_lookup cd pc x env v h vs sfs)
  from evh_lookup(3, 1, 2) show ?case 
    by (induction cd "HS h vs ((env, Suc pc) # sfs)" \<Sigma>'' rule: evalh.induct) simp_all 
next
  case (evh_pushcon cd pc k h h' v vs env sfs)
  from evh_pushcon(3, 1, 2) show ?case 
    by (induction cd "HS h vs ((env, Suc pc) # sfs)" \<Sigma>'' rule: evalh.induct) simp_all 
next
  case (evh_pushlam cd pc pc' h env h' v vs sfs)
  from evh_pushlam(3, 1, 2) show ?case 
    by (induction cd "HS h vs ((env, Suc pc) # sfs)" \<Sigma>'' rule: evalh.induct) simp_all 
next
  case (evh_apply cd pc h v2 env' pc' v1 vs env sfs)
  from evh_apply(3, 1, 2) show ?case 
    by (induction cd "HS h (v1 # v2 # vs) ((env, Suc pc) # sfs)" \<Sigma>'' rule: evalh.induct) 
       simp_all 
next
  case (evh_return cd pc h vs env sfs)
  from evh_return(2, 1) show ?case 
    by (induction cd "HS h vs ((env, Suc pc) # sfs)" \<Sigma>'' rule: evalh.induct) simp_all 
next
  case (evh_jump cd pc h v2 env' pc' v1 vs env sfs)
  from evh_jump(3, 1, 2) show ?case 
    by (induction cd "HS h (v1 # v2 # vs) ((env, Suc pc) # sfs)" \<Sigma>'' rule: evalh.induct) 
       simp_all 
qed

end