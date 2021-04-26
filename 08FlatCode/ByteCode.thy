theory ByteCode
  imports "../00Utils/Environment" "../00Utils/Iteration"
begin

datatype byte_code = 
  BLookup nat
  | BPushCon nat
  | BPushLam nat
  | BApply
  | BReturn
  | BJump

datatype bclosure = 
  BConst nat
  | BLam "bclosure list" nat

datatype byte_code_state = 
  BS "bclosure list" "(bclosure list \<times> nat) list"

inductive evalb :: "byte_code list \<Rightarrow> byte_code_state \<Rightarrow> byte_code_state \<Rightarrow> bool" 
    (infix "\<tturnstile> _ \<leadsto>\<^sub>b" 50) where
  evb_lookup [simp]: "cd ! pc = BLookup x \<Longrightarrow> lookup env x = Some v \<Longrightarrow> 
    cd \<tturnstile> BS vs ((env, Suc pc) # sfs) \<leadsto>\<^sub>b BS (v # vs) ((env, pc) # sfs)" 
| evb_pushcon [simp]: "cd ! pc = BPushCon k \<Longrightarrow> 
    cd \<tturnstile> BS vs ((env, Suc pc) # sfs) \<leadsto>\<^sub>b BS (BConst k # vs) ((env, pc) # sfs)"
| evb_pushlam [simp]: "cd ! pc = BPushLam pc' \<Longrightarrow> 
    cd \<tturnstile> BS vs ((env, Suc pc) # sfs) \<leadsto>\<^sub>b BS (BLam env pc' # vs) ((env, pc) # sfs)"
| evb_apply [simp]: "cd ! pc = BApply \<Longrightarrow> 
    cd \<tturnstile> BS (v # BLam env' pc' # vs) ((env, Suc pc) # sfs) \<leadsto>\<^sub>b 
      BS vs ((v # env', pc') # (env, pc) # sfs)"
| evb_return [simp]: "cd ! pc = BReturn \<Longrightarrow> cd \<tturnstile> BS vs ((env, Suc pc) # sfs) \<leadsto>\<^sub>b BS vs sfs"
| evb_jump [simp]: "cd ! pc = BJump \<Longrightarrow> 
    cd \<tturnstile> BS (v # BLam env' pc' # vs) ((env, Suc pc) # sfs) \<leadsto>\<^sub>b BS vs ((v # env', pc') # sfs)"

theorem determinismb: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>b \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>b \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction cd \<Sigma> \<Sigma>' rule: evalb.induct)
  case (evb_lookup cd pc x env v vs sfs)
  from evb_lookup(3, 1, 2) show ?case 
    by (induction cd "BS vs ((env, Suc pc) # sfs)" \<Sigma>'' rule: evalb.induct) simp_all 
next
  case (evb_pushcon cd pc k vs env sfs)
  from evb_pushcon(2, 1) show ?case 
    by (induction cd "BS vs ((env, Suc pc) # sfs)" \<Sigma>'' rule: evalb.induct) simp_all 
next
  case (evb_pushlam cd pc pc' vs env sfs)
  from evb_pushlam(2, 1) show ?case 
    by (induction cd "BS vs ((env, Suc pc) # sfs)" \<Sigma>'' rule: evalb.induct) simp_all 
next
  case (evb_apply cd pc v env' pc' vs env sfs)
  from evb_apply(2, 1) show ?case 
    by (induction cd "BS (v # BLam env' pc' # vs) ((env, Suc pc) # sfs)" \<Sigma>'' rule: evalb.induct) 
       simp_all 
next
  case (evb_return cd pc vs env sfs)
  from evb_return(2, 1) show ?case 
    by (induction cd "BS vs ((env, Suc pc) # sfs)" \<Sigma>'' rule: evalb.induct) simp_all 
next
  case (evb_jump cd pc v env' pc' vs env sfs)
  from evb_jump(2, 1) show ?case 
    by (induction cd "BS (v # BLam env' pc' # vs) ((env, Suc pc) # sfs)" \<Sigma>'' rule: evalb.induct) 
       simp_all 
qed

end