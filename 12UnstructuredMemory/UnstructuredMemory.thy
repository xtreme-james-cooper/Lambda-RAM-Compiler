theory UnstructuredMemory
  imports "../10ChainedEnvironment/ChainedEnvironment"
begin

datatype unstr_state = 
  US "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat nat
  | USF "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat

fun unstr_lookup :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<rightharpoonup> nat" where
  "unstr_lookup h 0 x = None"
| "unstr_lookup h (Suc 0) x = None"
| "unstr_lookup h (Suc (Suc p)) 0 = Some (h p)"
| "unstr_lookup h (Suc (Suc p)) (Suc x) = unstr_lookup h (h (Suc p)) x"

inductive evalu :: "byte_code list \<Rightarrow> unstr_state \<Rightarrow> unstr_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>u" 50) where
  evu_lookup [simp]: "cd ! pc = BLookup x \<Longrightarrow> unstr_lookup e (sh (sp - 1)) x = Some y \<Longrightarrow>
    cd \<tturnstile> US h hp e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u US h hp e ep (vs(vp := y)) (Suc vp) sh sp pc"
| evu_pushcon [simp]: "cd ! pc = BPushCon k \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u 
      US (h(hp := 0, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) e ep 
        (vs(vp := hp)) (Suc vp) sh sp pc"
| evu_pushlam [simp]: "cd ! pc = BPushLam pc' \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u 
      US (h(hp := 1, Suc hp := sh (sp - 1), Suc (Suc hp) := pc')) (3 + hp) e ep 
        (vs(vp := hp)) (Suc vp) sh sp pc"
| evu_apply [simp]: "cd ! pc = BApply \<Longrightarrow> h (vs vp) = Suc x \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs (Suc (Suc vp)) sh sp (Suc pc) \<leadsto>\<^sub>u 
      US h hp (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (2 + ep) vs vp
        (sh(sp := pc, Suc sp := Suc (Suc ep))) (2 + sp) (h (Suc (Suc (vs vp))))"
| evu_return_normal [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u US h hp e ep vs vp sh sp (sh sp)"
| evu_return_end [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh (Suc 0) (Suc pc) \<leadsto>\<^sub>u USF h hp e ep vs vp"
| evu_jump [simp]: "cd ! pc = BJump \<Longrightarrow> h (vs vp) = Suc x \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs (Suc (Suc vp)) sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
      US h hp (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (2 + ep) vs vp
        (sh(sp := Suc (Suc ep))) (Suc sp) (h (Suc (Suc (vs vp))))"

theorem determinismu: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>u \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>u \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction cd \<Sigma> \<Sigma>' rule: evalu.induct)
  case (evu_lookup cd pc x e sh sp y h hp ep vs vp)
  from evu_lookup(3, 1, 2) show ?case 
    by (induction cd "US h hp e ep vs vp sh sp (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
next
next
  case (evu_pushcon cd pc k h hp e ep vs vp sh sp)
  from evu_pushcon(2, 1) show ?case 
    by (induction cd "US h hp e ep vs vp sh sp (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_pushlam cd pc pc' h hp e ep vs vp sh sp)
  from evu_pushlam(2, 1) show ?case 
    by (induction cd "US h hp e ep vs vp sh sp (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_apply cd pc h vs vp x hp e ep sh sp)
  from evu_apply(3, 1, 2) show ?case    
    by (induction cd "US h hp e ep vs (Suc (Suc vp)) sh sp (Suc pc)" \<Sigma>'' rule: evalu.induct) 
       simp_all
next
  case (evu_return_normal cd pc h hp e ep vs vp sh sp)
  from evu_return_normal(2, 1) show ?case 
    by (induction cd "US h hp e ep vs vp sh (Suc (Suc sp)) (Suc pc)" \<Sigma>'' rule: evalu.induct) 
       simp_all
next
  case (evu_return_end cd pc h hp e ep vs vp sh)
  from evu_return_end(2, 1) show ?case 
    by (induction cd "US h hp e ep vs vp sh (Suc 0) (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_jump cd pc h vs vp x hp e ep sh sp)
  from evu_jump(3, 1, 2) show ?case    
    by (induction cd "US h hp e ep vs (Suc (Suc vp)) sh (Suc sp) (Suc pc)" \<Sigma>'' rule: evalu.induct) 
       simp_all
qed

end