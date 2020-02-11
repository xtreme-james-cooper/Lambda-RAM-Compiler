theory ByteCode
  imports "../00Utils/Environment" "../00Utils/Iteration"
begin

datatype byte_code = 
  BLookup nat
  | BPushCon nat
  | BPushLam nat nat
  | BApply
  | BReturn
  | BJump

datatype bclosure = 
  BConst nat
  | BLam "bclosure list" nat

datatype byte_code_state = 
  BS "bclosure list" "(bclosure list \<times> nat) list" (code: "byte_code list")

inductive evalb :: "byte_code_state \<Rightarrow> byte_code_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>b" 50) where
  evb_lookup [simp]: "cd ! pc = BLookup x \<Longrightarrow> lookup env x = Some v \<Longrightarrow> 
    BS vs ((env, Suc pc) # sfs) cd \<leadsto>\<^sub>b BS (v # vs) ((env, pc) # sfs) cd"
| evb_pushcon [simp]: "cd ! pc = BPushCon k \<Longrightarrow> 
    BS vs ((env, Suc pc) # sfs) cd \<leadsto>\<^sub>b BS (BConst k # vs) ((env, pc) # sfs) cd"
| evb_pushlam [simp]: "cd ! pc = BPushLam pc' (length env) \<Longrightarrow> 
    BS vs ((env, Suc pc) # sfs) cd \<leadsto>\<^sub>b BS (BLam env pc' # vs) ((env, pc) # sfs) cd"
| evb_apply [simp]: "cd ! pc = BApply \<Longrightarrow> 
    BS (v # BLam env' pc' # vs) ((env, Suc pc) # sfs) cd \<leadsto>\<^sub>b 
      BS vs ((v # env', pc') # (env, pc) # sfs) cd"
| evb_return [simp]: "cd ! pc = BReturn \<Longrightarrow> BS vs ((env, Suc pc) # sfs) cd \<leadsto>\<^sub>b BS vs sfs cd"
| evb_jump [simp]: "cd ! pc = BJump \<Longrightarrow> 
    BS (v # BLam env' pc' # vs) ((env, Suc pc) # sfs) cd \<leadsto>\<^sub>b 
      BS vs ((v # env', pc') # sfs) cd"

theorem determinismb: "\<Sigma> \<leadsto>\<^sub>b \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>b \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalb.induct)
  case (evb_lookup cd pc x env v vs sfs)
  from evb_lookup(3, 1, 2) show ?case 
    by (induction "BS vs ((env, Suc pc) # sfs) cd" \<Sigma>'' rule: evalb.induct) simp_all 
next
  case (evb_pushcon cd pc k vs env sfs)
  from evb_pushcon(2, 1) show ?case 
    by (induction "BS vs ((env, Suc pc) # sfs) cd" \<Sigma>'' rule: evalb.induct) simp_all 
next
  case (evb_pushlam cd pc pc' env vs sfs)
  from evb_pushlam(2, 1) show ?case 
    by (induction "BS vs ((env, Suc pc) # sfs) cd" \<Sigma>'' rule: evalb.induct) simp_all 
next
  case (evb_apply cd pc v env' pc' vs env sfs)
  from evb_apply(2, 1) show ?case 
    by (induction "BS (v # BLam env' pc' # vs) ((env, Suc pc) # sfs) cd" \<Sigma>'' rule: evalb.induct) 
       simp_all 
next
  case (evb_return cd pc vs env sfs)
  from evb_return(2, 1) show ?case 
    by (induction "BS vs ((env, Suc pc) # sfs) cd" \<Sigma>'' rule: evalb.induct) simp_all 
next
  case (evb_jump cd pc v env' pc' vs env sfs)
  from evb_jump(2, 1) show ?case 
    by (induction "BS (v # BLam env' pc' # vs) ((env, Suc pc) # sfs) cd" \<Sigma>'' rule: evalb.induct) 
       simp_all 
qed

lemma [simp]: "\<Sigma> \<leadsto>\<^sub>b \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: evalb.induct) simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>b) \<Sigma> \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

end