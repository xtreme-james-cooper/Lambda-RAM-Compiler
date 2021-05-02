theory Unstructuring
  imports UnstructuredMemory "../11FlatMemory/FlatMemory" "../00Utils/Utils"
begin

fun restructure :: "unstr_state \<Rightarrow> flat_state" where
  "restructure (US h hp e ep vs vp sh sp 0) = 
    FS (H h hp) (H e ep) (listify' vs vp) []"
| "restructure (US h hp e ep vs vp sh sp (Suc pc)) = 
    FS (H h hp) (H e ep) (listify' vs vp) (Suc pc # listify' sh sp)"

theorem completeu [simp]: "cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> cd \<tturnstile> restructure \<Sigma>\<^sub>u \<leadsto>\<^sub>f restructure \<Sigma>\<^sub>u'"
proof (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct)
  case (evu_lookup cd pc x h sh sp y hp e ep vs vp)
  then show ?case by simp
next
  case (evu_pushcon cd pc k h hp e ep vs vp sh sp)
  then show ?case by simp
next
  case (evu_pushlam cd pc pc' h hp e ep vs vp sh sp)
  then show ?case by simp
next
  case (evu_apply cd pc h vs vp hp e ep sh sp)
  then show ?case by simp
next
  case (evu_return cd pc h hp e ep vs vp sh sp)
  then show ?case by simp
next
  case (evu_jump cd pc h vs vp hp e ep sh sp)
  then show ?case by simp
qed

lemma [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> iter (\<tturnstile> cd \<leadsto>\<^sub>f) (restructure \<Sigma>\<^sub>u) (restructure \<Sigma>\<^sub>u')" 
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct) (simp, metis completeu iter_step)

lemma evalu_clears_regs: "iter (\<tturnstile> cd \<leadsto>\<^sub>u) (US nmem 0 nmem 0 nmem 0 (nmem(0 := 0)) 1 (length cd)) 
    (US h\<^sub>u hp\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u 1 sh\<^sub>u sp\<^sub>u 0) \<Longrightarrow> sp\<^sub>u = 0"
  by simp

lemma [dest]: "FS h env vs sfs = restructure \<Sigma> \<Longrightarrow> \<exists>h' hp e ep vs' vp sh sp pc. 
  \<Sigma> = US h' hp e ep vs' vp sh sp pc \<and> h = H h' hp \<and> env = H e ep \<and> vs = listify' vs' vp \<and> 
    ((pc = 0 \<and> sfs = []) \<or> (\<exists>pc'. pc = Suc pc' \<and> sfs = pc # listify' sh sp))"
  by (induction \<Sigma> rule: restructure.induct) simp_all

theorem correctu [simp]: "cd \<tturnstile> restructure \<Sigma>\<^sub>u \<leadsto>\<^sub>f \<Sigma>\<^sub>f' \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>u'. (cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u') \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>u'"
proof (induction "restructure \<Sigma>\<^sub>u" \<Sigma>\<^sub>f' rule: evalf.induct)
  case (evf_lookup cd pc x env p v h vs sfs)
  hence "FS h env vs (Suc pc # p # sfs) = restructure \<Sigma>\<^sub>u" by simp
  then obtain h' hp e ep vs' vp sh sp where S: "
    \<Sigma>\<^sub>u = US h' hp e ep vs' vp sh sp (Suc pc) \<and> h = H h' hp \<and> env = H e ep \<and> 
      vs = listify' vs' vp \<and> p # sfs = listify' sh sp" by fastforce


  from evf_lookup have "cd ! pc = BLookup x" by simp
  from evf_lookup have "flat_lookup env p x = Some v" by simp



  from S have "(cd \<tturnstile> US h' hp e ep vs' vp sh sp (Suc pc) \<leadsto>\<^sub>u US h' hp e ep xvs xvp sh sp (Suc xpc)) \<and> 
    FS h env (v # vs) (pc # p # sfs) = restructure (US h' hp e ep xvs xvp sh sp (Suc xpc))" by simp
  with S show ?case by blast
next
  case (evf_pushcon cd pc k h h' v env vs p sfs)
  then show ?case by simp
next
  case (evf_pushlam cd pc pc' h p h' v env vs sfs)
  then show ?case by simp
next
  case (evf_apply cd pc h v2 p' pc' env v1 env' p2 vs p sfs)
  then show ?case by simp
next
  case (evf_return cd pc h env vs p sfs)
  then show ?case by simp
next
  case (evf_jump cd pc h v2 p' pc' env v1 env' p2 vs p sfs)
  then show ?case by simp
qed

theorem correctu_iter [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>f) (restructure \<Sigma>\<^sub>u) \<Sigma>\<^sub>f' \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>u'. iter (\<tturnstile> cd \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>u'"
  by (induction "restructure \<Sigma>\<^sub>u" \<Sigma>\<^sub>f' arbitrary: \<Sigma>\<^sub>u rule: iter.induct) 
     (force, metis correctu iter_step)

end