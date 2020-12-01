theory Unstructuring
  imports UnstructuredMemory "../11FlatMemory/FlatMemory"
begin

fun restructure :: "unstr_state \<Rightarrow> flat_state" where
  "restructure (US h hp x p e ep vs vp sh sp 0 cd) = 
    FS (H h hp) (H e ep) (listify' vs vp) [] cd"
| "restructure (US h hp x p e ep vs vp sh sp (Suc pc) cd) = 
    FS (H h hp) (H e ep) (listify' vs vp) (Suc pc # listify' sh sp) cd"

theorem completeu [simp]: "\<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> iter (\<leadsto>\<^sub>f) (restructure \<Sigma>\<^sub>u) (restructure \<Sigma>\<^sub>u')"
proof (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct)
  case (evu_lookup_zero cd pc x h hp p e ep vs vp sh sp)
  then show ?case by simp
next
  case (evu_pushcon cd pc k h hp x p e ep vs vp sh sp)
  then show ?case by simp
next
  case (evu_pushlam cd pc pc' h hp x p e ep vs vp sh sp)
  then show ?case by simp
next
  case (evu_apply cd pc h vs vp hp x p e ep sh sp)
  then show ?case by simp
next
  case (evu_return cd pc h hp x p e ep vs vp sh sp)
  then show ?case by simp
next
  case (evu_jump cd pc h vs vp hp x p e ep sh sp)
  then show ?case by simp
qed simp_all

lemma [dest]: "FS h env vs sfs cd = restructure \<Sigma> \<Longrightarrow> \<exists>h' hp x p e ep vs' vp sh sp pc. 
  \<Sigma> = US h' hp x p e ep vs' vp sh sp pc cd \<and> h = H h' hp \<and> env = H e ep \<and> vs = listify' vs' vp \<and> 
    ((pc = 0 \<and> sfs = []) \<or> (\<exists>pc'. pc = Suc pc' \<and> sfs = pc # listify' sh sp))"
  by (induction \<Sigma> rule: restructure.induct) simp_all

theorem correctu [simp]: "restructure \<Sigma>\<^sub>u \<leadsto>\<^sub>f \<Sigma>\<^sub>f' \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>u'. iter (\<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>u'"
proof (induction "restructure \<Sigma>\<^sub>u" \<Sigma>\<^sub>f' rule: evalf.induct)
  case (evf_lookup cd pc x env p v h vs sfs)
  hence "FS h env vs (Suc pc # p # sfs) cd = restructure \<Sigma>\<^sub>u" by simp
  then obtain h' hp xx pp e ep vs' vp sh sp where S: "
    \<Sigma>\<^sub>u = US h' hp xx pp e ep vs' vp sh sp (Suc pc) cd \<and> h = H h' hp \<and> env = H e ep \<and> 
      vs = listify' vs' vp \<and> p # sfs = listify' sh sp" by fastforce


  from evf_lookup have "cd ! pc = BLookup x" by simp
  from evf_lookup have "flat_lookup env p x = Some v" by simp



  have "iter (\<leadsto>\<^sub>u) (US h' hp xx pp e ep vs' vp sh sp (Suc pc) cd) \<Sigma>\<^sub>u' \<and> FS h env (v # vs) (pc # p # sfs) cd = restructure \<Sigma>\<^sub>u'" by simp
  with S show ?case by blast
next
  case (evf_pushcon cd pc k h h' v env vs p sfs)
  then show ?case by simp
next
  case (evf_pushlam cd pc pc' h p h' v env vs sfs)
  then show ?case by simp
next
  case (evf_apply cd pc h v2 p' pc' env v1 env1 p1 env2 p2 vs p sfs)
  then show ?case by simp
next
  case (evf_return cd pc h env vs p sfs)
  then show ?case by simp
next
  case (evf_jump cd pc h v2 p' pc' env v1 env1 p1 env2 p2 vs p sfs)
  then show ?case by simp
qed

theorem correctu_iter [simp]: "iter (\<leadsto>\<^sub>f) (restructure \<Sigma>\<^sub>u) \<Sigma>\<^sub>f' \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>u'. iter (\<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>u'"
  by (induction "restructure \<Sigma>\<^sub>u" \<Sigma>\<^sub>f' arbitrary: \<Sigma>\<^sub>u rule: iter.induct)
     (force, metis correctu iter_append)

end