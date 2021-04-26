theory UnstructuredMemory
  imports "../10ChainedEnvironment/ChainedEnvironment"
begin

abbreviation nmem :: "nat \<Rightarrow> nat" where
  "nmem x \<equiv> undefined"

datatype unstr_state = 
  US "nat \<Rightarrow> nat" nat nat nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat nat

inductive evalu :: "byte_code list \<Rightarrow> unstr_state \<Rightarrow> unstr_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>u" 50) where
  evu_lookup_init [simp]: "cd ! pc = BLookup x \<Longrightarrow> 
    cd \<tturnstile> US h hp 0 0 e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u 
      US h hp (Suc x) (sh (sp - 1)) e ep vs vp sh sp (Suc pc)"
| evu_lookup_suc [simp]: "cd ! pc = BLookup y \<Longrightarrow> 
    cd \<tturnstile> US h hp (Suc (Suc x)) (Suc (Suc p)) e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u 
      US h hp x (h (Suc p)) e ep vs vp sh sp (Suc pc)"
| evu_lookup_zero [simp]: "cd ! pc = BLookup x \<Longrightarrow> 
    cd \<tturnstile> US h hp (Suc 0) (Suc (Suc p)) e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u 
      US h hp 0 0 e ep (vs(vp := h p)) (Suc vp) sh sp pc"
| evu_pushcon [simp]: "cd ! pc = BPushCon k \<Longrightarrow> 
    cd \<tturnstile> US h hp x p e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u 
      US (h(hp := 0, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) x p e ep 
        (vs(vp := hp)) (Suc vp) sh sp pc"
| evu_pushlam [simp]: "cd ! pc = BPushLam pc' \<Longrightarrow> 
    cd \<tturnstile> US h hp x p e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u 
      US (h(hp := 1, Suc hp := (sh (sp - 1)), Suc (Suc hp) := pc')) (3 + hp) x p e ep 
        (vs(vp := hp)) (Suc vp) sh sp pc"
| evu_apply [simp]: "cd ! pc = BApply \<Longrightarrow> h (vs (vp - 2)) = 1 \<Longrightarrow> 
    cd \<tturnstile> US h hp x p e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u 
      US h hp x p (e(ep := vs (vp - 1), Suc ep := h (Suc (vs (vp - 2))))) (2 + ep) vs (vp - 2) 
        (sh(sp := Suc (Suc ep), Suc sp := h (Suc (Suc (vs (vp - 2)))))) (2 + sp) pc"
| evu_return [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    cd \<tturnstile> US h hp x p e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u US h hp x p e ep vs vp sh (sp - 1) (sh(sp - 1))"
| evu_jump [simp]: "cd ! pc = BJump \<Longrightarrow> h (vs (vp - 2)) = 1 \<Longrightarrow> 
    cd \<tturnstile> US h hp x p e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u 
      US h hp x p (e(ep := vs (vp - 1), Suc ep := h (Suc (vs (vp - 2))))) (2 + ep) vs (vp - 2) 
        (sh(sp - 2 := Suc (Suc ep), sp - 1 := h (Suc (Suc (vs (vp - 2)))))) sp pc"

theorem determinismu: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>u \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>u \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction cd \<Sigma> \<Sigma>' rule: evalu.induct)
  case (evu_lookup_init cd pc x h hp e ep vs vp sh sp)
  from evu_lookup_init(2, 1) show ?case 
    by (induction cd "US h hp 0 0 e ep vs vp sh sp (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_lookup_suc cd pc y h hp x p e ep vs vp sh sp)
  from evu_lookup_suc(2, 1) show ?case 
    by (induction cd "US h hp (Suc (Suc x)) (Suc (Suc p)) e ep vs vp sh sp (Suc pc)" \<Sigma>'' 
        rule: evalu.induct) 
       simp_all
next
  case (evu_lookup_zero cd pc x h hp p e ep vs vp sh sp)
  from evu_lookup_zero(2, 1) show ?case 
    by (induction cd "US h hp (Suc 0) (Suc (Suc p)) e ep vs vp sh sp (Suc pc)" \<Sigma>'' 
        rule: evalu.induct) 
       simp_all
next
  case (evu_pushcon cd pc k h hp x p e ep vs vp sh sp)
  from evu_pushcon(2, 1) show ?case 
    by (induction cd "US h hp x p e ep vs vp sh sp (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_pushlam cd pc pc' h hp x p e ep vs vp sh sp)
  from evu_pushlam(2, 1) show ?case 
    by (induction cd "US h hp x p e ep vs vp sh sp (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_apply cd pc h vs vp hp x p e ep sh sp)
  from evu_apply(3, 1, 2) show ?case    
    by (induction cd "US h hp x p e ep vs vp sh sp (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_return cd pc h hp x p e ep vs vp sh sp)
  from evu_return(2, 1) show ?case 
    by (induction cd "US h hp x p e ep vs vp sh sp (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_jump cd pc h vs vp hp x p e ep sh sp)
  from evu_jump(3, 1, 2) show ?case    
    by (induction cd "US h hp x p e ep vs vp sh sp (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
qed

lemma evalu_clears_regs: "iter (\<tturnstile> cd \<leadsto>\<^sub>u) 
  (US nmem 0 0 0 nmem 0 nmem 0 (nmem(0 := 0)) 1 (length cd)) 
    (US h\<^sub>u hp\<^sub>u x\<^sub>u p\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u 1 sh\<^sub>u sp\<^sub>u 0) \<Longrightarrow> x\<^sub>u = 0 \<and> p\<^sub>u = 0 \<and> sp\<^sub>u = 0" 
  by simp

end