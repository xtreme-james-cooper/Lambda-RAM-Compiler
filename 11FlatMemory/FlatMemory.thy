theory FlatMemory
  imports "../10HeapMemory/HeapMemory"
begin

datatype flat_state = 
  FS "nat heap" "ptr list" "nat list list" (code: "byte_code list")

fun get_closure :: "nat heap \<Rightarrow> nat \<Rightarrow> hclosure" where
  "get_closure h p = (case hlookup h p of
      0 \<Rightarrow> HConst (hlookup h (Suc p))
    | Suc x \<Rightarrow> HLam (hlookup_list h (Suc (Suc p)) x) (hlookup h (Suc p)))"

inductive evalf :: "flat_state \<Rightarrow> flat_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>f" 50) where
  evf_lookup [simp]: "cd ! pc = BLookup x \<Longrightarrow> lookup env x = Some v \<Longrightarrow> 
    FS h vs ((Suc pc # env) # sfs) cd \<leadsto>\<^sub>f FS h (v # vs) ((pc # env) # sfs) cd"
| evf_pushcon [simp]: "cd ! pc = BPushCon k \<Longrightarrow> halloc_list h [0, k] = (h', v) \<Longrightarrow>
    FS h vs ((Suc pc # env) # sfs) cd \<leadsto>\<^sub>f FS h' (v # vs) ((pc # env) # sfs) cd"
| evf_pushlam [simp]: "cd ! pc = BPushLam pc' (length env) \<Longrightarrow> 
    halloc_list h (Suc (length env) # pc' # env) = (h', v) \<Longrightarrow>
      FS h vs ((Suc pc # env) # sfs) cd \<leadsto>\<^sub>f FS h' (v # vs) ((pc # env) # sfs) cd"
| evf_apply [simp]: "cd ! pc = BApply \<Longrightarrow> get_closure h v2 = HLam env' pc' \<Longrightarrow>
    FS h (v1 # v2 # vs) ((Suc pc # env) # sfs) cd \<leadsto>\<^sub>f
      FS h vs ((pc' # v1 # env') # (pc # env) # sfs) cd"
| evf_return [simp]: "cd ! pc = BReturn (length env) \<Longrightarrow> 
    FS h vs ((Suc pc # env) # sfs) cd \<leadsto>\<^sub>f FS h vs sfs cd"
| evf_jump [simp]: "cd ! pc = BJump (length env) \<Longrightarrow> get_closure h v2 = HLam env' pc' \<Longrightarrow>
    FS h (v1 # v2 # vs) ((Suc pc # env) # sfs) cd \<leadsto>\<^sub>f FS h vs ((pc' # v1 # env') # sfs) cd"

theorem determinismf: "\<Sigma> \<leadsto>\<^sub>f \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>f \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalf.induct)
  case (evf_lookup cd pc x env v h vs sfs)
  from evf_lookup(3, 1, 2) show ?case 
    by (induction "FS h vs ((Suc pc # env) # sfs) cd" \<Sigma>'' rule: evalf.induct) simp_all 
next
  case (evf_pushcon cd pc k h h' v vs env sfs)
  from evf_pushcon(3, 1, 2) show ?case 
    by (induction "FS h vs ((Suc pc # env) # sfs) cd" \<Sigma>'' rule: evalf.induct) simp_all 
next
  case (evf_pushlam cd pc pc' env h h' v vs sfs)
  from evf_pushlam(3, 1, 2) show ?case 
    by (induction "FS h vs ((Suc pc # env) # sfs) cd" \<Sigma>'' rule: evalf.induct) simp_all 
next
  case (evf_apply cd pc h v2 env' pc' v1 vs env sfs)
  from evf_apply(3, 1, 2) show ?case 
    by (induction "FS h (v1 # v2 # vs) ((Suc pc # env) # sfs) cd" \<Sigma>'' rule: evalf.induct) 
       simp_all 
next
  case (evf_return cd pc env h vs sfs)
  from evf_return(2, 1) show ?case 
    by (induction "FS h vs ((Suc pc # env) # sfs) cd" \<Sigma>'' rule: evalf.induct) simp_all 
next
  case (evf_jump cd pc env h v2 env' pc' v1 vs sfs)
  from evf_jump(3, 1, 2) show ?case 
    by (induction "FS h (v1 # v2 # vs) ((Suc pc # env) # sfs) cd" \<Sigma>'' rule: evalf.induct) 
       simp_all 
qed

lemma [simp]: "\<Sigma> \<leadsto>\<^sub>f \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: evalf.induct) simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>f) \<Sigma> \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

end