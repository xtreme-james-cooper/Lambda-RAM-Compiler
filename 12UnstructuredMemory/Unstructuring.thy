theory Unstructuring
  imports UnstructuredMemory "../11FlatMemory/FlatMemory" "../00Utils/Utils" 
begin

primrec restructure :: "unstr_state \<Rightarrow> flat_state" where
  "restructure (US h hp e ep vs vp sh sp pc) = 
    FS (H h hp) (H e ep) (listify' vs vp) (case sp of 
      0 \<Rightarrow> (case pc of 0 \<Rightarrow> [] | Suc pc' \<Rightarrow> Suc pc' # [])  
    | Suc sp' \<Rightarrow> pc # sh sp' # listify' sh sp')"

lemma [simp]: "flat_lookup (H h hp) p x = unstr_lookup h p x"
  by (induction h p x rule: unstr_lookup.induct) simp_all

theorem completeu [simp]: "cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd \<Longrightarrow> 
    cd \<tturnstile> restructure \<Sigma>\<^sub>u \<leadsto>\<^sub>f restructure \<Sigma>\<^sub>u'"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct) (auto split: nat.splits)

lemma [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd \<Longrightarrow> 
    iter (\<tturnstile> cd \<leadsto>\<^sub>f) (restructure \<Sigma>\<^sub>u) (restructure \<Sigma>\<^sub>u')" 
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct) (simp, metis completeu iter_step preserve_restructure)

lemma [dest]: "FS h env vs (pc # p # sfs) = restructure \<Sigma> \<Longrightarrow> \<exists>h' hp e ep vs' vp sh sp. 
  \<Sigma> = US h' hp e ep vs' vp sh (Suc sp) pc \<and> h = H h' hp \<and> env = H e ep \<and> vs = listify' vs' vp \<and> 
    p = sh sp \<and> sfs = listify' sh sp"
proof (induction \<Sigma>)
  case (US h' hp e ep vs' vp sh sp pc')
  thus ?case by (simp_all split: nat.splits)
qed

lemma [dest]: "FS h env vs [] = restructure \<Sigma> \<Longrightarrow> \<exists>h' hp e ep vs' vp sh. 
    \<Sigma> = US h' hp e ep vs' vp sh 0 0 \<and> h = H h' hp \<and> env = H e ep \<and> vs = listify' vs' vp"
  by (induction \<Sigma>) (simp_all split: nat.splits)

theorem correctu [simp]: "cd \<tturnstile> restructure \<Sigma>\<^sub>u \<leadsto>\<^sub>f \<Sigma>\<^sub>f' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd \<Longrightarrow> 
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
    h' = H (hh(hp := 1, Suc hp := k, Suc (Suc hp) := 0)) (Suc (Suc (Suc hp)))" by fastforce
  with S have X: "FS h' env (v # vs) (pc # p # sfs) = 
    restructure (US (hh(hp := 1, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) e ep 
      (vs'(vp := hp)) (Suc vp) sh (Suc sp) pc)" by simp
  from evf_pushcon have "cd \<tturnstile> US hh hp e ep vs' vp sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
    US (hh(hp := 1, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) e ep (vs'(vp := hp)) 
      (Suc vp) sh (Suc sp) pc" by (metis evu_pushcon)
  with S X show ?case by blast
next
  case (evf_pushlam cd pc pc' h p h' v env vs sfs)
  then obtain hh hp e ep vs' vp sh sp where S: "\<Sigma>\<^sub>u = US hh hp e ep vs' vp sh (Suc sp) (Suc pc) \<and> 
    h = H hh hp \<and> env = H e ep \<and> vs = listify' vs' vp \<and> p = sh sp \<and> sfs = listify' sh sp" 
      by fastforce
  with evf_pushlam have "v = hp \<and> 
    h' = H (hh(hp := 0, Suc hp := sh sp, Suc (Suc hp) := pc')) (Suc (Suc (Suc hp)))" by fastforce
  with S have X: "FS h' env (v # vs) (pc # p # sfs) = 
    restructure (US (hh(hp := 0, Suc hp := p, Suc (Suc hp) := pc')) (3 + hp) e ep 
      (vs'(vp := hp)) (Suc vp) sh (Suc sp) pc)" by simp
  from evf_pushlam S have "cd \<tturnstile> US hh hp e ep vs' vp sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
    US (hh(hp := 0, Suc hp := sh sp, Suc (Suc hp) := pc')) (3 + hp) e ep (vs'(vp := hp)) 
      (Suc vp) sh (Suc sp) pc" by (metis diff_Suc_1 evu_pushlam)
  with S X show ?case by blast
next
  case (evf_apply cd pc h v2 p' pc' env v1 env' p2 vs p sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "\<Sigma>\<^sub>u = US h' hp e ep vs' vp sh (Suc sp) (Suc pc) \<and> 
    h = H h' hp \<and> env = H e ep \<and> listify' vs' vp = v1 # v2 # vs \<and> p = sh sp \<and> sfs = listify' sh sp" 
      by fastforce
  then obtain vp' where V: "vp = Suc (Suc vp') \<and> v1 = vs' (Suc vp') \<and> v2 = vs' vp' \<and> 
    vs = listify' vs' vp'" by fastforce
  with evf_apply S have H: "h' (vs' vp') = 0 \<and> p' = h' (Suc (vs' vp')) \<and> 
    pc' = h' (Suc (Suc (vs' vp')))" by (cases "h' (vs' vp')") simp_all
  from evf_apply S have "p2 = ep \<and> env' = H (e(p2 := v1, Suc p2 := p')) (Suc (Suc p2))" by fastforce
  with S V have X: "FS h env' vs (pc' # Suc (Suc p2) # pc # p # sfs) = 
    restructure (US h' hp (e(ep := v1, Suc ep := p')) (2 + ep) vs' vp' 
      (sh(Suc sp := pc, Suc (Suc sp) := Suc (Suc ep))) (2 + Suc sp) pc')" by simp
  from evf_apply V H have "
    cd \<tturnstile> US h' hp e ep vs' (Suc (Suc vp')) sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
      US h' hp (e(ep := v1, Suc ep := p')) (2 + ep) vs' vp'
        (sh(Suc sp := pc, Suc (Suc sp) := Suc (Suc ep))) (2 + Suc sp) pc'"
    by (metis evu_apply)
  with S X V show ?case by blast
next
  case (evf_return cd pc h env vs p sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "\<Sigma>\<^sub>u = US h' hp e ep vs' vp sh (Suc sp) (Suc pc) \<and> 
    h = H h' hp \<and> env = H e ep \<and> vs = listify' vs' vp \<and> p = sh sp \<and> sfs = listify' sh sp" 
      by fastforce
  thus ?case
  proof (cases sp)
    case 0
    with S have X: "FS h env vs sfs = restructure (US h' hp e ep vs' vp sh 0 0)" by simp
    from evf_return have "cd \<tturnstile> US h' hp e ep vs' vp sh (Suc 0) (Suc pc) \<leadsto>\<^sub>u 
      US h' hp e ep vs' vp sh 0 0" by (metis evu_return_end)
    with S 0 X show ?thesis by blast
  next
    case (Suc sp')
    with evf_return S have X: "FS h env vs sfs = restructure (US h' hp e ep vs' vp sh sp' (sh sp'))" 
      by (auto split: nat.splits)
    from evf_return have "cd \<tturnstile> US h' hp e ep vs' vp sh (Suc (Suc sp')) (Suc pc) \<leadsto>\<^sub>u 
      US h' hp e ep vs' vp sh sp' (sh sp')" by (metis evu_return_normal)
    with S Suc X show ?thesis by blast
  qed
next
  case (evf_jump cd pc h v2 p' pc' env v1 env' p2 vs p sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "\<Sigma>\<^sub>u = US h' hp e ep vs' vp sh (Suc sp) (Suc pc) \<and> 
    h = H h' hp \<and> env = H e ep \<and> listify' vs' vp = v1 # v2 # vs \<and> p = sh sp \<and> sfs = listify' sh sp" 
      by fastforce
  then obtain vp' where V: "vp = Suc (Suc vp') \<and> v1 = vs' (Suc vp') \<and> v2 = vs' vp' \<and> 
    vs = listify' vs' vp'" by fastforce
  with evf_jump S have H: "h' (vs' vp') = 0 \<and> p' = h' (Suc (vs' vp')) \<and> 
    pc' = h' (Suc (Suc (vs' vp')))" by (cases "h' (vs' vp')") simp_all
  from evf_jump S have "p2 = ep \<and> env' = H (e(p2 := v1, Suc p2 := p')) (Suc (Suc p2))" by fastforce
  with S V have X: "FS h env' vs (pc' # Suc (Suc p2) # sfs) = 
    restructure (US h' hp (e(ep := v1, Suc ep := p')) (2 + ep) vs' vp' 
      (sh(Suc sp - 1 := Suc (Suc ep))) (Suc sp) pc')" by simp
  from evf_jump V H have "
        cd \<tturnstile> US h' hp e ep vs' (Suc (Suc vp')) sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
    US h' hp (e(ep := v1, Suc ep := p')) (2 + ep) vs' vp'
      (sh(Suc sp - 1 := Suc (Suc ep))) (Suc sp) pc'" by (metis evu_jump)
  with S V X show ?case by blast
qed

theorem correctu_iter [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>f) (restructure \<Sigma>\<^sub>u) \<Sigma>\<^sub>f' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd \<Longrightarrow>
    \<exists>\<Sigma>\<^sub>u'. iter (\<tturnstile> cd \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>u'"
  by (induction "restructure \<Sigma>\<^sub>u" \<Sigma>\<^sub>f' arbitrary: \<Sigma>\<^sub>u rule: iter.induct) 
     (force, metis correctu iter_step preserve_restructure)

lemma [simp]: "restructurable_heap nmem 0 0 x"
  by (simp add: restructurable_heap_def)

lemma [simp]: "restructurable_env nmem 0 0"
  by (simp add: restructurable_env_def)

lemma [simp]: "restructurable_vals nmem 0 0" 
  by (simp add: restructurable_vals_def)

lemma [simp]: "restructurable_stack (nmem(0 := 0)) (Suc 0) 0 x"
  by (simp only: restructurable_stack_def) simp_all

end