theory Unstructuring
  imports UnstructuredMemory "../11FlatMemory/FlatMemory" "../00Utils/Utils"
begin

primrec restructure :: "unstr_state \<Rightarrow> flat_state" where
  "restructure (US h hp e ep vs vp sh sp pc) = 
    FS (H h hp) (H e ep) (listify' vs vp) (pc # listify' sh sp)"
| "restructure (USF h hp e ep vs vp) = 
    FS (H h hp) (H e ep) (listify' vs vp) []"

primrec restructurable :: "unstr_state \<Rightarrow> bool" where
  "restructurable (US h hp e ep vs vp sh sp pc) = (\<exists>sp'. sp = Suc (2 * sp'))"
| "restructurable (USF h hp e ep vs vp) = True"

lemma preserve_restructure [simp]: "cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u \<Longrightarrow> restructurable \<Sigma>\<^sub>u'"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct) (auto, presburger+)

lemma [simp]: "flat_lookup (H h hp) p x = unstr_lookup h p x"
  by (induction h p x rule: unstr_lookup.induct) simp_all

theorem completeu [simp]: "cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u \<Longrightarrow> 
    cd \<tturnstile> restructure \<Sigma>\<^sub>u \<leadsto>\<^sub>f restructure \<Sigma>\<^sub>u'"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct) fastforce+

lemma [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u \<Longrightarrow> 
    iter (\<tturnstile> cd \<leadsto>\<^sub>f) (restructure \<Sigma>\<^sub>u) (restructure \<Sigma>\<^sub>u')" 
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct) (simp, metis completeu iter_step preserve_restructure)

lemma [dest]: "FS h env vs (pc # p # sfs) = restructure \<Sigma> \<Longrightarrow> \<exists>h' hp e ep vs' vp sh sp. 
  \<Sigma> = US h' hp e ep vs' vp sh (Suc sp) pc \<and> h = H h' hp \<and> env = H e ep \<and> vs = listify' vs' vp \<and> 
    p = sh sp \<and> sfs = listify' sh sp"
proof (induction \<Sigma>)
  case (US h' hp e ep vs' vp sh sp pc')
  thus ?case by (cases sp) simp_all
qed simp_all

theorem correctu [simp]: "cd \<tturnstile> restructure \<Sigma>\<^sub>u \<leadsto>\<^sub>f \<Sigma>\<^sub>f' \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>u'. (cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u') \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>u'"
proof (induction "restructure \<Sigma>\<^sub>u" \<Sigma>\<^sub>f' rule: evalf.induct)
  case (evf_lookup cd pc x env p v h vs sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "\<Sigma>\<^sub>u = US h' hp e ep vs' vp sh (Suc sp) (Suc pc) \<and> 
    h = H h' hp \<and> env = H e ep \<and> vs = listify' vs' vp \<and> p = sh sp \<and> sfs = listify' sh sp" 
      by fastforce
  moreover hence "FS h env (v # vs) (pc # p # sfs) = 
    restructure (US h' hp e ep (vs'(vp := v)) (Suc vp) sh (Suc sp) pc)" by simp
  moreover from evf_lookup S have "cd \<tturnstile> US h' hp e ep vs' vp sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
    US h' hp e ep (vs'(vp := v)) (Suc vp) sh (Suc sp) pc" by simp
  ultimately show ?case by blast
next
  case (evf_pushcon cd pc k h h' v env vs p sfs)
  then obtain hh hp e ep vs' vp sh sp where S: "\<Sigma>\<^sub>u = US hh hp e ep vs' vp sh (Suc sp) (Suc pc) \<and> 
    h = H hh hp \<and> env = H e ep \<and> vs = listify' vs' vp \<and> p = sh sp \<and> sfs = listify' sh sp" 
      by fastforce
  with evf_pushcon have "v = hp \<and> 
    h' = H (hh(hp := 0, Suc hp := k, Suc (Suc hp) := 0)) (Suc (Suc (Suc hp)))" by fastforce
  with S have X: "FS h' env (v # vs) (pc # p # sfs) = 
    restructure (US (hh(hp := 0, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) e ep 
      (vs'(vp := hp)) (Suc vp) sh (Suc sp) pc)" by simp
  from evf_pushcon have "cd \<tturnstile> US hh hp e ep vs' vp sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
    US (hh(hp := 0, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) e ep (vs'(vp := hp)) 
      (Suc vp) sh (Suc sp) pc" by simp
  with S X show ?case by blast
next
  case (evf_pushlam cd pc pc' h p h' v env vs sfs)
  then obtain hh hp e ep vs' vp sh sp where S: "\<Sigma>\<^sub>u = US hh hp e ep vs' vp sh (Suc sp) (Suc pc) \<and> 
    h = H hh hp \<and> env = H e ep \<and> vs = listify' vs' vp \<and> p = sh sp \<and> sfs = listify' sh sp" 
      by fastforce
  with evf_pushlam have "v = hp \<and> 
    h' = H (hh(hp := 1, Suc hp := sh sp, Suc (Suc hp) := pc')) (Suc (Suc (Suc hp)))" by fastforce
  with S have X: "FS h' env (v # vs) (pc # p # sfs) = 
    restructure (US (hh(hp := 1, Suc hp := p, Suc (Suc hp) := pc')) (3 + hp) e ep 
      (vs'(vp := hp)) (Suc vp) sh (Suc sp) pc)" by simp
  from evf_pushlam S have "cd \<tturnstile> US hh hp e ep vs' vp sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
    US (hh(hp := 1, Suc hp := sh sp, Suc (Suc hp) := pc')) (3 + hp) e ep (vs'(vp := hp)) 
      (Suc vp) sh (Suc sp) pc" by (metis diff_Suc_1 evu_pushlam)
  with S X show ?case by blast
next
  case (evf_apply cd pc h v2 p' pc' env v1 env' p2 vs p sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "\<Sigma>\<^sub>u = US h' hp e ep vs' vp sh (Suc sp) (Suc pc) \<and> 
    h = H h' hp \<and> env = H e ep \<and> v1 # v2 # vs = listify' vs' vp \<and> p = sh sp \<and> sfs = listify' sh sp" 
      by fastforce

  then show ?case by simp
next
  case (evf_return cd pc h env vs p sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "\<Sigma>\<^sub>u = US h' hp e ep vs' vp sh (Suc sp) (Suc pc) \<and> 
    h = H h' hp \<and> env = H e ep \<and> vs = listify' vs' vp \<and> p = sh sp \<and> sfs = listify' sh sp" 
      by fastforce

  then show ?case by simp
next
  case (evf_jump cd pc h v2 p' pc' env v1 env' p2 vs p sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "\<Sigma>\<^sub>u = US h' hp e ep vs' vp sh (Suc sp) (Suc pc) \<and> 
    h = H h' hp \<and> env = H e ep \<and> v1 # v2 # vs = listify' vs' vp \<and> p = sh sp \<and> sfs = listify' sh sp" 
      by fastforce

  then show ?case by simp
qed

theorem correctu_iter [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>f) (restructure \<Sigma>\<^sub>u) \<Sigma>\<^sub>f' \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>u'. iter (\<tturnstile> cd \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>u'"
  by (induction "restructure \<Sigma>\<^sub>u" \<Sigma>\<^sub>f' arbitrary: \<Sigma>\<^sub>u rule: iter.induct) 
     (force, metis correctu iter_step)

end