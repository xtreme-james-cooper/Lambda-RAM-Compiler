theory UnstructuredMemory
  imports "../10ChainedEnvironment/ChainedEnvironment"
begin

datatype unstr_state = 
  US "nat \<Rightarrow> nat" nat nat nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat nat 
     (code: "byte_code list")

inductive evalu :: "unstr_state \<Rightarrow> unstr_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>u" 50) where
  evu_lookup_init [simp]: "cd ! pc = BLookup x \<Longrightarrow> 
    US h hp 0 0 e ep vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u 
      US h hp (Suc x) (sh (sp - 1)) e ep vs vp sh sp (Suc pc) cd"
| evu_lookup_suc [simp]: "cd ! pc = BLookup y \<Longrightarrow> 
    US h hp (Suc (Suc x)) (Suc (Suc p)) e ep vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u 
      US h hp x (h (Suc p)) e ep vs vp sh sp (Suc pc) cd"
| evu_lookup_zero [simp]: "cd ! pc = BLookup x \<Longrightarrow> 
    US h hp (Suc 0) (Suc (Suc p)) e ep vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u 
      US h hp 0 0 e ep (vs(vp := h p)) (Suc vp) sh sp pc cd"
| evu_pushcon [simp]: "cd ! pc = BPushCon k \<Longrightarrow> US h hp x p e ep vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u 
    US (h(hp := 0, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) x p e ep 
      (vs(vp := hp)) (Suc vp) sh sp pc cd"
| evu_pushlam [simp]: "cd ! pc = BPushLam pc' \<Longrightarrow> US h hp x p e ep vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u 
   US (h(hp := 1, Suc hp := (sh (sp - 1)), Suc (Suc hp) := pc')) (3 + hp) x p e ep 
      (vs(vp := hp)) (Suc vp) sh sp pc cd"
| evu_apply [simp]: "cd ! pc = BApply \<Longrightarrow> h (vs (vp - 2)) = 1 \<Longrightarrow> 
    US h hp x p e ep vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u 
      US h hp x p (e(ep := vs (vp - 1), Suc ep := h (Suc (vs (vp - 2))))) (2 + ep) vs (vp - 2) 
        (sh(sp := Suc (Suc ep), Suc sp := h (Suc (Suc (vs (vp - 2)))))) (2 + sp) pc cd"
| evu_return [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    US h hp x p e ep vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u US h hp x p e ep vs vp sh (sp - 1) (sh(sp - 1)) cd"
| evu_jump [simp]: "cd ! pc = BJump \<Longrightarrow> h (vs (vp - 2)) = 1 \<Longrightarrow> 
    US h hp x p e ep vs vp sh sp (Suc pc) cd \<leadsto>\<^sub>u 
      US h hp x p (e(ep := vs (vp - 1), Suc ep := h (Suc (vs (vp - 2))))) (2 + ep) vs (vp - 2) 
        (sh(sp - 2 := Suc (Suc ep), sp - 1 := h (Suc (Suc (vs (vp - 2)))))) sp pc cd"

theorem determinismu: "\<Sigma> \<leadsto>\<^sub>u \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>u \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalu.induct)
  case (evu_lookup_init cd pc x h hp e ep vs vp sh sp)
  from evu_lookup_init(2, 1) show ?case 
    by (induction "US h hp 0 0 e ep vs vp sh sp (Suc pc) cd" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_lookup_suc cd pc y h hp x p e ep vs vp sh sp)
  from evu_lookup_suc(2, 1) show ?case 
    by (induction "US h hp (Suc (Suc x)) (Suc (Suc p)) e ep vs vp sh sp (Suc pc) cd" \<Sigma>'' 
        rule: evalu.induct) 
       simp_all
next
  case (evu_lookup_zero cd pc x h hp p e ep vs vp sh sp)
  from evu_lookup_zero(2, 1) show ?case 
    by (induction "US h hp (Suc 0) (Suc (Suc p)) e ep vs vp sh sp (Suc pc) cd" \<Sigma>'' 
        rule: evalu.induct) 
       simp_all
next
  case (evu_pushcon cd pc k h hp x p e ep vs vp sh sp)
  from evu_pushcon(2, 1) show ?case 
    by (induction "US h hp x p e ep vs vp sh sp (Suc pc) cd" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_pushlam cd pc pc' h hp x p e ep vs vp sh sp)
  from evu_pushlam(2, 1) show ?case 
    by (induction "US h hp x p e ep vs vp sh sp (Suc pc) cd" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_apply cd pc h vs vp hp x p e ep sh sp)
  from evu_apply(3, 1, 2) show ?case    
    by (induction "US h hp x p e ep vs vp sh sp (Suc pc) cd" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_return cd pc h hp x p e ep vs vp sh sp)
  from evu_return(2, 1) show ?case 
    by (induction "US h hp x p e ep vs vp sh sp (Suc pc) cd" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_jump cd pc h vs vp hp x p e ep sh sp)
  from evu_jump(3, 1, 2) show ?case    
    by (induction "US h hp x p e ep vs vp sh sp (Suc pc) cd" \<Sigma>'' rule: evalu.induct) simp_all
qed

lemma [simp]: "\<Sigma> \<leadsto>\<^sub>u \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: evalu.induct) simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>u) \<Sigma> \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

end