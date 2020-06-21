theory UnstructuredMemory
  imports "../08HeapMemory/HeapMemory"
begin

datatype unstr_state = 
  US (heap: "nat \<Rightarrow> nat") (heap_pointer: nat) ("values": "nat \<Rightarrow> nat") (value_pointer: nat) 
     (callstack: "nat \<Rightarrow> nat") (callstack_pointer: nat) (code_pointer: nat) (code: "byte_code list")

primrec ulookup_list :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat list" where
  "ulookup_list h x 0 = []"
| "ulookup_list h x (Suc n) = h x # ulookup_list h (Suc x) n"

primrec ualloc_list :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat list \<Rightarrow> (nat \<Rightarrow> nat)" where
  "ualloc_list h hp [] = h"
| "ualloc_list h hp (x # xs) = ualloc_list (h(hp := x)) (Suc hp) xs"

fun uget_closure :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> hclosure" where
  "uget_closure h p = (case h p of
      0 \<Rightarrow> HConst (h (Suc p))
    | Suc x \<Rightarrow> HLam (ulookup_list h (Suc (Suc p)) x) (h (Suc p)))"

inductive evalu :: "unstr_state \<Rightarrow> unstr_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>u" 50) where
  evu_lookup [simp]: "cd ! pc = BLookup x \<Longrightarrow>
    US h hp vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u US h hp (vs(vp := sh (sp - Suc x))) (Suc vp) sh sp pc cd"
| evu_pushcon [simp]: "cd ! pc = BPushCon k \<Longrightarrow> 
    US h hp vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u 
      US (ualloc_list h hp [0, k]) (hp + 2) (vs(vp := hp)) (Suc vp) sh sp pc cd"
| evf_pushlam [simp]: "cd ! pc = BPushLam pc' d \<Longrightarrow> 
   US h hp vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u 
      US (ualloc_list h hp (Suc d # pc' # env)) (hp + d + 2) (vs(vp := hp)) (Suc vp) sh sp pc cd"
| evf_apply [simp]: "cd ! pc = BApply \<Longrightarrow> uget_closure h (vs (vp - 2)) = HLam env' pc' \<Longrightarrow>
    US h hp vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u US h hp vs (vp - 2) 
      (ualloc_list (sh(sp := pc, sp + length env' + 1 := vs (vp - 1))) (Suc sp) env')
        (sp + length env' + 2) pc' cd"
| evf_return [simp]: "cd ! pc = BReturn d \<Longrightarrow> 
    US h hp vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u US h hp vs vp sh (sp - d) (sh(sp - d)) cd"
| evf_jump [simp]: "cd ! pc = BJump d \<Longrightarrow> uget_closure h (vs (vp - 2)) = HLam env' pc' \<Longrightarrow>
    US h hp vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u US h hp vs (vp - 2) 
      (ualloc_list (sh(sp - d + length env' + 1 := vs (vp - 1))) (sp - d + 1) env')
        (sp - d + length env' + 2) pc' cd"

theorem determinismu: "\<Sigma> \<leadsto>\<^sub>u \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>u \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalu.induct)
  case (evu_lookup cd pc x h hp vs vp sh sp)
  from evu_lookup(2, 1) show ?case 
    by (induction "US h hp vs vp sh sp (Suc pc) cd" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_pushcon cd pc k h hp vs vp sh sp)
  from evu_pushcon(2, 1) show ?case 
    by (induction "US h hp vs vp sh sp (Suc pc) cd" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evf_pushlam cd pc pc' d h hp vs vp sh sp env)
  from evf_pushlam(2, 1) show ?case 
    by (induction "US h hp vs vp sh sp (Suc pc) cd" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evf_apply cd pc h vs vp env' pc' hp sh sp)
  from evf_apply(3, 1, 2) show ?case 
    by (induction "US h hp vs vp sh sp (Suc pc) cd" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evf_return cd pc d h hp vs vp sh sp)
  from evf_return(2, 1) show ?case 
    by (induction "US h hp vs vp sh sp (Suc pc) cd" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evf_jump cd pc d h vs vp env' pc' hp sh sp)
  from evf_jump(3, 1, 2) show ?case 
    by (induction "US h hp vs vp sh sp (Suc pc) cd" \<Sigma>'' rule: evalu.induct) simp_all
qed

lemma [simp]: "\<Sigma> \<leadsto>\<^sub>u \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: evalu.induct) simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>u) \<Sigma> \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

end