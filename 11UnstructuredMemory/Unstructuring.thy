theory Unstructuring
  imports UnstructuredMemory "../10FlatMemory/FlatMemory" "../00Utils/Utils" 
begin

primrec listify_heap :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list" where
  "listify_heap h 0 = []"
| "listify_heap h (Suc x) = h x # listify_heap h x"

lemma [dest]: "listify_heap h x = [] \<Longrightarrow> x = 0"
  by (induction x) simp_all

lemma [dest]: "listify_heap h x = a # as \<Longrightarrow> \<exists>y. x = Suc y \<and> h y = a \<and> listify_heap h y = as"
  by (induction x) simp_all

lemma [simp]: "hp \<le> x \<Longrightarrow> listify_heap (h(x := v)) hp = listify_heap h hp"
  by (induction hp) simp_all

lemma [simp]: "hp \<le> x \<Longrightarrow> listify_heap (h(Suc x := v) \<circ> Suc) hp = listify_heap (h \<circ> Suc) hp"
  by (induction hp) auto

primrec restructure :: "unstr_state \<Rightarrow> state\<^sub>f" where
  "restructure (US h hp e ep vs vp sh sp pc) = 
    S\<^sub>f (H h hp) (H e ep) (listify_heap vs vp) (case sp of 
      0 \<Rightarrow> []  
    | Suc sp' \<Rightarrow> pc # listify_heap (sh \<circ> Suc) sp')"

lemma [simp]: "flat_lookup (H h hp) p x = unstr_lookup h p x"
  by (induction h p x rule: unstr_lookup.induct) simp_all

theorem completeu [simp]: "cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd \<Longrightarrow> 
    cd \<tturnstile> restructure \<Sigma>\<^sub>u \<leadsto>\<^sub>f restructure \<Sigma>\<^sub>u'"
proof (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct)
  case (evu_lookup cd pc x e sh sp y h hp ep vs vp)
  thus ?case by (cases sp) (auto split: nat.splits)
next
  case (evu_pushcon cd pc k h hp e ep vs vp sh sp)
  thus ?case by (cases sp) (auto split: nat.splits)
next
  case (evu_pushlam cd pc pc' h hp e ep vs vp sh sp)
  thus ?case by (cases sp) (auto split: nat.splits)
next
  case (evu_apply \<C> p\<^sub>\<C> h vs vp hp e ep sh sp)
  moreover hence "hlookup (H h hp) (vs vp) = 0" by simp
  moreover have "halloc_list (H e ep) [vs (Suc vp), hlookup (H h hp) (Suc (vs vp))] = 
    (H (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (Suc (Suc ep)), ep)" by simp
  ultimately have "\<And>n. \<C> \<tturnstile> S\<^sub>f (H h hp) (H e ep) (vs (Suc vp) # vs vp # listify_heap vs vp) 
      (Suc p\<^sub>\<C> # sh (Suc n) # listify_heap (sh \<circ> Suc) n) \<leadsto>\<^sub>f 
    S\<^sub>f (H h hp) (H (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (Suc (Suc ep))) 
      (listify_heap vs vp) (hlookup (H h hp) (Suc (Suc (vs vp))) # Suc (Suc ep) # p\<^sub>\<C> # sh (Suc n) # 
        listify_heap (sh \<circ> Suc) n)"
    by (metis ev\<^sub>f_apply)
  with evu_apply show ?case by (cases sp) (auto split: nat.splits)
next
  case (evu_return cd pc h hp e ep vs vp sh sp)
  thus ?case by (cases sp) (auto split: nat.splits)
next
  case (evu_jump \<C> p\<^sub>\<C> h vs vp hp e ep sh sp)
  moreover hence "hlookup (H h hp) (vs vp) = 0" by simp
  moreover have "halloc_list (H e ep) [vs (Suc vp), hlookup (H h hp) (Suc (vs vp))] = 
    (H (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (Suc (Suc ep)), ep)" by simp
  ultimately have "\<And>n. \<C> \<tturnstile> S\<^sub>f (H h hp) (H e ep) (vs (Suc vp) # vs vp # listify_heap vs vp) 
      (Suc p\<^sub>\<C> # sh (Suc n) # listify_heap (sh \<circ> Suc) n) \<leadsto>\<^sub>f 
    S\<^sub>f (H h hp) (H (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (Suc (Suc ep))) 
      (listify_heap vs vp) (hlookup (H h hp) (Suc (Suc (vs vp))) # Suc (Suc ep) # 
        listify_heap (sh \<circ> Suc) n)"
    by (metis ev\<^sub>f_jump)
  with evu_jump show ?case by (cases sp) (auto split: nat.splits)
qed

lemma [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd \<Longrightarrow> 
    iter (\<tturnstile> cd \<leadsto>\<^sub>f) (restructure \<Sigma>\<^sub>u) (restructure \<Sigma>\<^sub>u')" 
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct) (simp, metis completeu iter_step preserve_restructure)

lemma [dest]: "S\<^sub>f h env vs (pc # p # sfs) = restructure \<Sigma> \<Longrightarrow> \<exists>h' hp e ep vs' vp sh sp. 
  \<Sigma> = US h' hp e ep vs' vp sh (Suc (Suc sp)) pc \<and> h = H h' hp \<and> env = H e ep \<and> 
    vs = listify_heap vs' vp \<and> p = sh (Suc sp) \<and> sfs = listify_heap (sh \<circ> Suc) sp"
proof (induction \<Sigma>)
  case (US h' hp e ep vs' vp sh sp pc')
  thus ?case 
  proof (induction sp)
    case (Suc sp')
    thus ?case by (cases sp') (simp_all split: nat.splits, meson comp_apply)
  qed (simp_all split: nat.splits)
qed

lemma [dest]: "S\<^sub>f h env vs [] = restructure \<Sigma> \<Longrightarrow> restructurable \<Sigma> cd \<Longrightarrow> \<exists>h' hp e ep vs' vp sh sp. 
    \<Sigma> = US h' hp e ep vs' vp sh 0 0 \<and> h = H h' hp \<and> env = H e ep \<and> vs = listify_heap vs' vp"
  by (induction \<Sigma>) (simp split: nat.splits)

theorem correctu [simp]: "cd \<tturnstile> restructure \<Sigma>\<^sub>u \<leadsto>\<^sub>f \<Sigma>\<^sub>f' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>u'. (cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u') \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>u'"
proof (induction "restructure \<Sigma>\<^sub>u" \<Sigma>\<^sub>f' rule: eval\<^sub>f.induct)
  case (ev\<^sub>f_lookup cd pc x env p v h vs sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "h = H h' hp \<and> env = H e ep \<and> 
    vs = listify_heap vs' vp \<and> p = sh (Suc sp) \<and> sfs = listify_heap (sh \<circ> Suc) sp \<and> 
      \<Sigma>\<^sub>u = US h' hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc)" by fastforce
  moreover hence "S\<^sub>f h env (v # vs) (pc # p # sfs) = 
    restructure (US h' hp e ep (vs'(vp := v)) (Suc vp) sh (Suc (Suc sp)) pc)" by simp
  moreover from ev\<^sub>f_lookup S have "cd \<tturnstile> US h' hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
    US h' hp e ep (vs'(vp := v)) (Suc vp) sh (Suc (Suc sp)) pc" by simp
  ultimately show ?case by blast
next
  case (ev\<^sub>f_pushcon cd pc k h h' v env vs p sfs)
  then obtain hh hp e ep vs' vp sh sp where S: "h = H hh hp \<and> env = H e ep \<and> 
    vs = listify_heap vs' vp \<and> p = sh (Suc sp) \<and> sfs = listify_heap (sh \<circ> Suc) sp \<and> 
      \<Sigma>\<^sub>u = US hh hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc)" by fastforce
  with ev\<^sub>f_pushcon have "v = hp \<and> 
    h' = H (hh(hp := 1, Suc hp := k, Suc (Suc hp) := 0)) (Suc (Suc (Suc hp)))" by fastforce
  with S have X: "S\<^sub>f h' env (v # vs) (pc # p # sfs) = 
    restructure (US (hh(hp := 1, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) e ep 
      (vs'(vp := hp)) (Suc vp) sh (Suc (Suc sp)) pc)" by simp
  from ev\<^sub>f_pushcon have "cd \<tturnstile> US hh hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
    US (hh(hp := 1, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) e ep (vs'(vp := hp)) 
      (Suc vp) sh (Suc (Suc sp)) pc" by (metis evu_pushcon)
  with S X show ?case by blast
next
  case (ev\<^sub>f_pushlam cd pc pc' h p h' v env vs sfs)
  then obtain hh hp e ep vs' vp sh sp where S: "h = H hh hp \<and> env = H e ep \<and> 
    vs = listify_heap vs' vp \<and> p = sh (Suc sp) \<and> sfs = listify_heap (sh \<circ> Suc) sp \<and> 
      \<Sigma>\<^sub>u = US hh hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc)" by fastforce
  with ev\<^sub>f_pushlam have "v = hp \<and> 
    h' = H (hh(hp := 0, Suc hp := sh (Suc sp), Suc (Suc hp) := pc')) (Suc (Suc (Suc hp)))" 
      by fastforce
  with S have X: "S\<^sub>f h' env (v # vs) (pc # p # sfs) = 
    restructure (US (hh(hp := 0, Suc hp := p, Suc (Suc hp) := pc')) (3 + hp) e ep 
      (vs'(vp := hp)) (Suc vp) sh (Suc (Suc sp)) pc)" by simp
  from ev\<^sub>f_pushlam S have "cd \<tturnstile> US hh hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
    US (hh(hp := 0, Suc hp := sh (Suc sp), Suc (Suc hp) := pc')) (3 + hp) e ep (vs'(vp := hp)) 
      (Suc vp) sh (Suc (Suc sp)) pc" by (metis evu_pushlam)
  with S X show ?case by blast
next
  case (ev\<^sub>f_apply cd pc h v2 env v1 env' p2 vs p sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "h = H h' hp \<and> env = H e ep \<and> p = sh (Suc sp) \<and> 
    sfs = listify_heap (sh \<circ> Suc) sp \<and> listify_heap vs' vp = v1 # v2 # vs \<and> 
      \<Sigma>\<^sub>u = US h' hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc)" by fastforce
  then obtain vp' where V: "vp = Suc (Suc vp') \<and> v1 = vs' (Suc vp') \<and> v2 = vs' vp' \<and> 
    vs = listify_heap vs' vp'" by fastforce
  let ?p' = "h' (Suc (vs' vp'))"
  let ?pc' = "h' (Suc (Suc (vs' vp')))"
  from ev\<^sub>f_apply S V have H: "h' (vs' vp') = 0" by (cases "h' (vs' vp')") simp_all
  from ev\<^sub>f_apply S V have "p2 = ep \<and> env' = H (e(p2 := v1, Suc p2 := ?p')) (Suc (Suc p2))" by auto
  with S V have X: "S\<^sub>f h env' vs (?pc' # Suc (Suc p2) # pc # p # sfs) = 
    restructure (US h' hp (e(ep := v1, Suc ep := ?p')) (2 + ep) vs' vp' 
      (sh(Suc (Suc sp) := pc, Suc (Suc (Suc sp)) := Suc (Suc ep))) (2 + Suc (Suc sp)) ?pc')" by simp
  from ev\<^sub>f_apply V H have "
    cd \<tturnstile> US h' hp e ep vs' (Suc (Suc vp')) sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
      US h' hp (e(ep := v1, Suc ep := ?p')) (2 + ep) vs' vp'
        (sh(Suc (Suc sp) := pc, Suc (Suc (Suc sp)) := Suc (Suc ep))) (2 + Suc (Suc sp)) ?pc'"
    by (metis evu_apply)
  with S X V show ?case by auto
next
  case (ev\<^sub>f_return cd pc h env vs p sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "h = H h' hp \<and> env = H e ep \<and> 
    vs = listify_heap vs' vp \<and> p = sh (Suc sp) \<and> sfs = listify_heap (sh \<circ> Suc) sp \<and> 
      \<Sigma>\<^sub>u = US h' hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc)" by fastforce
  moreover with ev\<^sub>f_return have "S\<^sub>f h env vs sfs = 
    restructure (US h' hp e ep vs' vp sh sp (sh sp))" by (auto split: nat.splits)
  moreover from ev\<^sub>f_return have "cd \<tturnstile> US h' hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
    US h' hp e ep vs' vp sh sp (sh sp)" by (metis evu_return)
  ultimately show ?case by blast
next
  case (ev\<^sub>f_jump cd pc h v2 env v1 env' p2 vs p sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "h = H h' hp \<and> env = H e ep \<and> p = sh (Suc sp) \<and> 
    sfs = listify_heap (sh \<circ> Suc) sp \<and> listify_heap vs' vp = v1 # v2 # vs \<and> 
      \<Sigma>\<^sub>u = US h' hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc)" by fastforce
  then obtain vp' where V: "vp = Suc (Suc vp') \<and> v1 = vs' (Suc vp') \<and> v2 = vs' vp' \<and> 
    vs = listify_heap vs' vp'" by fastforce
  let ?p' = "h' (Suc (vs' vp'))"
  let ?pc' = "h' (Suc (Suc (vs' vp')))"
  from ev\<^sub>f_jump S V have H: "h' (vs' vp') = 0" by (cases "h' (vs' vp')") simp_all
  from ev\<^sub>f_jump S V have "p2 = ep \<and> env' = H (e(p2 := v1, Suc p2 := ?p')) (Suc (Suc p2))" by auto
  with S V have X: "S\<^sub>f h env' vs (?pc' # Suc (Suc p2) # sfs) = 
    restructure (US h' hp (e(ep := v1, Suc ep := ?p')) (2 + ep) vs' vp' 
      (sh(Suc (Suc sp) - 1 := Suc (Suc ep))) (Suc (Suc sp)) ?pc')" by simp
  from ev\<^sub>f_jump V H have "
        cd \<tturnstile> US h' hp e ep vs' (Suc (Suc vp')) sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
    US h' hp (e(ep := v1, Suc ep := ?p')) (2 + ep) vs' vp'
      (sh(Suc (Suc sp) - 1 := Suc (Suc ep))) (Suc (Suc sp)) ?pc'" using evu_jump by fastforce
  with S V X show ?case by auto
qed

theorem correctu_iter [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>f) (restructure \<Sigma>\<^sub>u) \<Sigma>\<^sub>f' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd \<Longrightarrow>
    \<exists>\<Sigma>\<^sub>u'. iter (\<tturnstile> cd \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>u'"
  by (induction "restructure \<Sigma>\<^sub>u" \<Sigma>\<^sub>f' arbitrary: \<Sigma>\<^sub>u rule: iter.induct) 
     (force, metis correctu iter_step preserve_restructure)

end