theory Unstructuring
  imports UnstructuredState "../10FlatMemory/FlatMemory"
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
  "restructure (S\<^sub>u h hp e ep vs vp sh sp pc) = 
    S\<^sub>f (H h hp) (H e ep) (listify_heap vs vp) (case sp of 
      0 \<Rightarrow> []  
    | Suc sp' \<Rightarrow> pc # listify_heap (sh \<circ> Suc) sp')"

lemma [simp]: "flat_lookup (H h hp) p x = unstr_lookup h p x"
  by (induction h p x rule: unstr_lookup.induct) simp_all

primrec restructurable :: "unstr_state \<Rightarrow> bool" where
  "restructurable (S\<^sub>u h hp e ep vs vp sh sp pc) = (even sp \<and> sh 0 = 0 \<and> (sp = 0 \<longrightarrow> pc = 0))"

lemma restructurable_persists [simp]: "cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u \<Longrightarrow> restructurable \<Sigma>\<^sub>u'"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: eval\<^sub>u.induct) simp_all

lemma restructurable_persists_iter [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u \<Longrightarrow> 
    restructurable \<Sigma>\<^sub>u'"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct) simp_all

theorem completeu [simp]: "cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u \<Longrightarrow>
  cd \<tturnstile> restructure \<Sigma>\<^sub>u \<leadsto>\<^sub>f restructure \<Sigma>\<^sub>u'"
proof (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: eval\<^sub>u.induct)
  case (ev\<^sub>u_lookup cd pc x e sh sp y h hp ep vs vp)
  thus ?case by (cases sp) (auto split: nat.splits)
next
  case (ev\<^sub>u_pushcon cd pc k h hp e ep vs vp sh sp)
  thus ?case by (cases sp) (auto split: nat.splits)
next
  case (ev\<^sub>u_pushlam cd pc pc' h hp e ep vs vp sh sp)
  thus ?case by (cases sp) (auto split: nat.splits)
next
  case (ev\<^sub>u_apply \<C> p\<^sub>\<C> h vs vp ep' p\<^sub>\<C>' hp e ep sh sp)
  moreover hence "hlookup (H h hp) (vs vp) = (PEnv, ep')" by simp
  moreover from ev\<^sub>u_apply have "hlookup (H h hp) (Suc (vs vp)) = (PCode, p\<^sub>\<C>')" by simp
  moreover have "halloc_list (H e ep) [vs (Suc vp), ep'] = 
    (H (e(ep := vs (Suc vp), Suc ep := ep')) (Suc (Suc ep)), ep)" by simp
  ultimately have "\<And>n. \<C> \<tturnstile> S\<^sub>f (H h hp) (H e ep) (vs (Suc vp) # vs vp # listify_heap vs vp) 
      (Suc p\<^sub>\<C> # sh (Suc n) # listify_heap (sh \<circ> Suc) n) \<leadsto>\<^sub>f 
    S\<^sub>f (H h hp) (H (e(ep := vs (Suc vp), Suc ep := ep')) (Suc (Suc ep))) 
      (listify_heap vs vp) (p\<^sub>\<C>' # Suc (Suc ep) # p\<^sub>\<C> # sh (Suc n) # listify_heap (sh \<circ> Suc) n)"
    by (metis ev\<^sub>f_apply)
  with ev\<^sub>u_apply show ?case by (cases sp) (auto split: nat.splits)
next
  case (ev\<^sub>u_return cd pc h hp e ep vs vp sh sp)
  thus ?case by (cases sp) (auto split: nat.splits)
next
  case (ev\<^sub>u_jump \<C> p\<^sub>\<C> h vs vp ep' p\<^sub>\<C>' hp e ep sh sp)
  moreover hence "hlookup (H h hp) (vs vp) = (PEnv, ep')" by simp
  moreover from ev\<^sub>u_jump have "hlookup (H h hp) (Suc (vs vp)) = (PCode, p\<^sub>\<C>')" by simp
  moreover have "halloc_list (H e ep) [vs (Suc vp), ep'] = 
    (H (e(ep := vs (Suc vp), Suc ep := ep')) (Suc (Suc ep)), ep)" by simp
  ultimately have "\<And>n. \<C> \<tturnstile> S\<^sub>f (H h hp) (H e ep) (vs (Suc vp) # vs vp # listify_heap vs vp) 
      (Suc p\<^sub>\<C> # sh (Suc n) # listify_heap (sh \<circ> Suc) n) \<leadsto>\<^sub>f 
    S\<^sub>f (H h hp) (H (e(ep := vs (Suc vp), Suc ep := ep')) (Suc (Suc ep))) 
      (listify_heap vs vp) (p\<^sub>\<C>' # Suc (Suc ep) # listify_heap (sh \<circ> Suc) n)"
    by (metis ev\<^sub>f_jump)
  with ev\<^sub>u_jump show ?case by (cases sp) (auto split: nat.splits)
qed

lemma [dest]: "S\<^sub>f h env vs (pc # p # sfs) = restructure \<Sigma> \<Longrightarrow> \<exists>h' hp e ep vs' vp sh sp. 
  \<Sigma> = S\<^sub>u h' hp e ep vs' vp sh (Suc (Suc sp)) pc \<and> h = H h' hp \<and> env = H e ep \<and> 
    vs = listify_heap vs' vp \<and> p = sh (Suc sp) \<and> sfs = listify_heap (sh \<circ> Suc) sp"
proof (induction \<Sigma>)
  case (S\<^sub>u h' hp e ep vs' vp sh sp pc')
  thus ?case 
  proof (induction sp)
    case (Suc sp')
    thus ?case by (cases sp') (simp_all split: nat.splits, meson comp_apply)
  qed (simp_all split: nat.splits)
qed

lemma [dest]: "S\<^sub>f h env vs [] = restructure \<Sigma> \<Longrightarrow> restructurable \<Sigma> \<Longrightarrow> \<exists>h' hp e ep vs' vp sh. 
    \<Sigma> = S\<^sub>u h' hp e ep vs' vp sh 0 0 \<and> h = H h' hp \<and> env = H e ep \<and> vs = listify_heap vs' vp"
  by (induction \<Sigma>) (simp split: nat.splits)

theorem correctu [simp]: "cd \<tturnstile> restructure \<Sigma>\<^sub>u \<leadsto>\<^sub>f \<Sigma>\<^sub>f' \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>u'. (cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u') \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>u'"
proof (induction "restructure \<Sigma>\<^sub>u" \<Sigma>\<^sub>f' rule: eval\<^sub>f.induct)
  case (ev\<^sub>f_lookup cd pc x env p v h vs sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "h = H h' hp \<and> env = H e ep \<and> 
    vs = listify_heap vs' vp \<and> p = sh (Suc sp) \<and> sfs = listify_heap (sh \<circ> Suc) sp \<and> 
      \<Sigma>\<^sub>u = S\<^sub>u h' hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc)" by fastforce
  moreover hence "S\<^sub>f h env (v # vs) (pc # p # sfs) = 
    restructure (S\<^sub>u h' hp e ep (vs'(vp := v)) (Suc vp) sh (Suc (Suc sp)) pc)" by simp
  moreover from ev\<^sub>f_lookup S have "cd \<tturnstile> S\<^sub>u h' hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
    S\<^sub>u h' hp e ep (vs'(vp := v)) (Suc vp) sh (Suc (Suc sp)) pc" by simp
  ultimately show ?case by blast
next
  case (ev\<^sub>f_pushcon cd pc k h h' v env vs p sfs)
  then obtain hh hp e ep vs' vp sh sp where S: "h = H hh hp \<and> env = H e ep \<and> 
    vs = listify_heap vs' vp \<and> p = sh (Suc sp) \<and> sfs = listify_heap (sh \<circ> Suc) sp \<and> 
      \<Sigma>\<^sub>u = S\<^sub>u hh hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc)" by fastforce
  with ev\<^sub>f_pushcon have "v = hp \<and> 
    h' = H (hh(hp := (PConst, k), Suc hp := (PConst, 0))) (Suc (Suc hp))" by fastforce
  with S have X: "S\<^sub>f h' env (v # vs) (pc # p # sfs) = 
    restructure (S\<^sub>u (hh(hp := (PConst, k), Suc hp := (PConst, 0))) 
      (2 + hp) e ep (vs'(vp := hp)) (Suc vp) sh (Suc (Suc sp)) pc)" by simp
  from ev\<^sub>f_pushcon have "cd \<tturnstile> S\<^sub>u hh hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
    S\<^sub>u (hh(hp := (PConst, k), Suc hp := (PConst, 0))) (2 + hp) e ep 
      (vs'(vp := hp)) (Suc vp) sh (Suc (Suc sp)) pc" by (metis ev\<^sub>u_pushcon)
  with S X show ?case by blast
next
  case (ev\<^sub>f_pushlam cd pc pc' h p h' v env vs sfs)
  then obtain hh hp e ep vs' vp sh sp where S: "h = H hh hp \<and> env = H e ep \<and> 
    vs = listify_heap vs' vp \<and> p = sh (Suc sp) \<and> sfs = listify_heap (sh \<circ> Suc) sp \<and> 
      \<Sigma>\<^sub>u = S\<^sub>u hh hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc)" by fastforce
  with ev\<^sub>f_pushlam have "v = hp \<and> 
    h' = H (hh(hp := (PEnv, sh (Suc sp)), Suc hp := (PCode, pc'))) (Suc (Suc hp))" by fastforce
  with S have X: "S\<^sub>f h' env (v # vs) (pc # p # sfs) = 
    restructure (S\<^sub>u (hh(hp := (PEnv, sh (Suc sp)), Suc hp := (PCode, pc'))) (2 + hp) e ep
      (vs'(vp := hp)) (Suc vp) sh (Suc (Suc sp)) pc)" 
        by simp
  from ev\<^sub>f_pushlam S have "cd \<tturnstile> S\<^sub>u hh hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
    S\<^sub>u (hh(hp := (PEnv, sh (Suc sp)), Suc hp := (PCode, pc'))) (2 + hp) 
      e ep (vs'(vp := hp)) (Suc vp) sh (Suc (Suc sp)) pc" by (metis ev\<^sub>u_pushlam)
  with S X show ?case by blast
next
  case (ev\<^sub>f_apply cd pc h v2 p\<^sub>\<Delta>' p\<^sub>\<C>' env v1 env' p2 vs p sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "h = H h' hp \<and> env = H e ep \<and> p = sh (Suc sp) \<and> 
    sfs = listify_heap (sh \<circ> Suc) sp \<and> listify_heap vs' vp = v1 # v2 # vs \<and> 
      \<Sigma>\<^sub>u = S\<^sub>u h' hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc)" by fastforce
  then obtain vp' where V: "vp = Suc (Suc vp') \<and> v1 = vs' (Suc vp') \<and> v2 = vs' vp' \<and> 
    vs = listify_heap vs' vp'" by fastforce
  from ev\<^sub>f_apply S V have H1: "h' (vs' vp') = (PEnv, p\<^sub>\<Delta>')" by simp
  from ev\<^sub>f_apply S V have H2: "h' (Suc (vs' vp')) = (PCode, p\<^sub>\<C>')" by simp
  from ev\<^sub>f_apply S V have "p2 = ep \<and> env' = H (e(p2 := v1, Suc p2 := p\<^sub>\<Delta>')) (Suc (Suc p2))" by auto
  with S V have X: "S\<^sub>f h env' vs (p\<^sub>\<C>' # Suc (Suc p2) # pc # p # sfs) = 
    restructure (S\<^sub>u h' hp (e(ep := v1, Suc ep := p\<^sub>\<Delta>')) (2 + ep) vs' vp' 
      (sh(Suc (Suc sp) := pc, Suc (Suc (Suc sp)) := Suc (Suc ep))) (2 + Suc (Suc sp)) p\<^sub>\<C>')" by simp
  from ev\<^sub>f_apply V H1 H2 have "
    cd \<tturnstile> S\<^sub>u h' hp e ep vs' (Suc (Suc vp')) sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
      S\<^sub>u h' hp (e(ep := v1, Suc ep := p\<^sub>\<Delta>')) (2 + ep) vs' vp'
        (sh(Suc (Suc sp) := pc, Suc (Suc (Suc sp)) := Suc (Suc ep))) (2 + Suc (Suc sp)) p\<^sub>\<C>'"
    by (metis ev\<^sub>u_apply)
  with S X V show ?case by auto
next
  case (ev\<^sub>f_return cd pc h env vs p sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "h = H h' hp \<and> env = H e ep \<and> 
    vs = listify_heap vs' vp \<and> p = sh (Suc sp) \<and> sfs = listify_heap (sh \<circ> Suc) sp \<and> 
      \<Sigma>\<^sub>u = S\<^sub>u h' hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc)" by fastforce
  moreover with ev\<^sub>f_return have "S\<^sub>f h env vs sfs = 
    restructure (S\<^sub>u h' hp e ep vs' vp sh sp (sh sp))" by (auto split: nat.splits)
  moreover from ev\<^sub>f_return have "cd \<tturnstile> S\<^sub>u h' hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
    S\<^sub>u h' hp e ep vs' vp sh sp (sh sp)" by (metis ev\<^sub>u_return)
  ultimately show ?case by blast
next
  case (ev\<^sub>f_jump cd pc h v2 p\<^sub>\<Delta>' p\<^sub>\<C>' env v1 env' p2 vs p sfs)
  then obtain h' hp e ep vs' vp sh sp where S: "h = H h' hp \<and> env = H e ep \<and> p = sh (Suc sp) \<and> 
    sfs = listify_heap (sh \<circ> Suc) sp \<and> listify_heap vs' vp = v1 # v2 # vs \<and> 
      \<Sigma>\<^sub>u = S\<^sub>u h' hp e ep vs' vp sh (Suc (Suc sp)) (Suc pc)" by fastforce
  then obtain vp' where V: "vp = Suc (Suc vp') \<and> v1 = vs' (Suc vp') \<and> v2 = vs' vp' \<and> 
    vs = listify_heap vs' vp'" by fastforce
  from ev\<^sub>f_jump S V have H1: "h' (vs' vp') = (PEnv, p\<^sub>\<Delta>')" by simp
  from ev\<^sub>f_jump S V have H2: "h' (Suc (vs' vp')) = (PCode, p\<^sub>\<C>')" by simp
  from ev\<^sub>f_jump S V have "p2 = ep \<and> env' = H (e(p2 := v1, Suc p2 := p\<^sub>\<Delta>')) (Suc (Suc p2))" by auto
  with S V have X: "S\<^sub>f h env' vs (p\<^sub>\<C>' # Suc (Suc p2) # sfs) = 
    restructure (S\<^sub>u h' hp (e(ep := v1, Suc ep := p\<^sub>\<Delta>')) (2 + ep) vs' vp' 
      (sh(Suc (Suc sp) - 1 := Suc (Suc ep))) (Suc (Suc sp)) p\<^sub>\<C>')" by simp
  from ev\<^sub>f_jump V H1 H2 have "
        cd \<tturnstile> S\<^sub>u h' hp e ep vs' (Suc (Suc vp')) sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
    S\<^sub>u h' hp (e(ep := v1, Suc ep := p\<^sub>\<Delta>')) (2 + ep) vs' vp'
      (sh(Suc (Suc sp) - 1 := Suc (Suc ep))) (Suc (Suc sp)) p\<^sub>\<C>'" using ev\<^sub>u_jump by fastforce
  with S V X show ?case by auto
qed

theorem correctu_iter [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>f) (restructure \<Sigma>\<^sub>u) \<Sigma>\<^sub>f' \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>u'. iter (\<tturnstile> cd \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>u'"
  by (induction "restructure \<Sigma>\<^sub>u" \<Sigma>\<^sub>f' arbitrary: \<Sigma>\<^sub>u rule: iter.induct) 
     (force, metis correctu iter_step)

end