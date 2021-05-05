theory Unstructuring
  imports UnstructuredMemory "../11FlatMemory/FlatMemory" "../00Utils/Utils" 
          "../08FlatCode/CodeFlattening"
begin

primrec restructure :: "unstr_state \<Rightarrow> flat_state" where
  "restructure (US h hp e ep vs vp sh sp pc) = 
    FS (H h hp) (H e ep) (listify' vs vp) (case sp of 
      0 \<Rightarrow> (case pc of 0 \<Rightarrow> [] | Suc pc' \<Rightarrow> Suc pc' # [])  
    | Suc sp' \<Rightarrow> pc # sh sp' # listify' sh sp')"

definition restructurable_heap :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "restructurable_heap h hp ep lcd = (3 dvd hp \<and> (\<forall>x < hp. 3 dvd x \<longrightarrow> h x \<noteq> 0 \<longrightarrow> 
    (even (h (Suc x)) \<and> (h (Suc x)) \<le> ep \<and> h (Suc (Suc x)) \<noteq> 0 \<and> h (Suc (Suc x)) \<le> lcd)))"

definition restructurable_env :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "restructurable_env e ep hp = (even ep \<and>
    (\<forall>x < ep. if even x then 3 dvd e x \<and> e x < hp else even (e x) \<and> e x \<le> ep))"

definition restructurable_vals :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "restructurable_vals vs vp hp = (\<forall>x < vp. 3 dvd vs x \<and> vs x < hp)"

definition restructurable_stack :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "restructurable_stack sh sp ep lcd = 
    (\<forall>x < sp. if odd x then sh x \<noteq> 0 \<and> sh x \<le> lcd else even (sh x) \<and> sh x \<le> ep)"

primrec restructurable :: "unstr_state \<Rightarrow> byte_code list \<Rightarrow> bool" where
  "restructurable (US h hp e ep vs vp sh sp pc) cd = (pc \<le> length cd \<and> 
    length cd \<noteq> 0 \<and> orderly cd 0 \<and> return_terminated cd \<and> restructurable_heap h hp ep (length cd) \<and> 
      restructurable_env e ep hp \<and> restructurable_vals vs vp hp \<and> 
        restructurable_stack sh sp ep (length cd) \<and> (if pc = 0 then sp = 0 else odd sp))"

lemma [simp]: "odd (x::nat) \<Longrightarrow> 0 < x"
  by (cases x) simp_all

lemma [simp]: "return_terminated cd \<Longrightarrow> cd ! 0 \<noteq> BLookup x"
  by (induction cd) auto

lemma [simp]: "return_terminated cd \<Longrightarrow> cd ! 0 \<noteq> BPushCon k"
  by (induction cd) auto

lemma [simp]: "return_terminated cd \<Longrightarrow> cd ! 0 \<noteq> BPushLam pc"
  by (induction cd) auto

lemma [simp]: "return_terminated cd \<Longrightarrow> cd ! 0 \<noteq> BApply"
  by (induction cd) auto

lemma [dest]: "x \<noteq> y \<Longrightarrow> x < Suc y \<Longrightarrow> x < y"
  by presburger

lemma [dest]: "x \<noteq> y \<Longrightarrow> x \<noteq> Suc y \<Longrightarrow> x < Suc (Suc y) \<Longrightarrow> x < y"
  by presburger

lemma [simp]: "3 dvd x \<Longrightarrow> 3 dvd Suc x = False"
  by presburger

lemma [simp]: "3 dvd x \<Longrightarrow> 3 dvd Suc (Suc x) = False"
  by presburger

lemma [elim]: "restructurable_env e ep hp \<Longrightarrow> even ep"
  by (simp add: restructurable_env_def)

lemma [elim]: "restructurable_heap h hp ep lcd \<Longrightarrow> 3 dvd hp"
  by (simp add: restructurable_heap_def)

lemma [simp]: "restructurable_heap h hp ep lcd \<Longrightarrow> 
    restructurable_heap (h(hp := 0, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) ep lcd"
  by (auto simp add: restructurable_heap_def)

lemma [simp]: "restructurable_heap h hp ep lcd \<Longrightarrow> lcd \<noteq> 0 \<Longrightarrow>
  restructurable_heap (h(hp := Suc 0, Suc hp := k, Suc (Suc hp) := pc)) (3 + hp) ep lcd = 
    (even k \<and> k \<le> ep \<and> pc \<noteq> 0 \<and> pc \<le> lcd)"
proof
  let ?f = "\<lambda>x. if x = Suc (Suc hp) then pc else (h(hp := Suc 0, Suc hp := k)) x"
  let ?g = "\<lambda>x. if x = Suc hp then pc else (h(hp := Suc 0, Suc hp := k)) (Suc x)"
  let ?h = "\<lambda>x. if x = hp then pc else (h(hp := Suc 0, Suc hp := k)) (Suc (Suc x))"
  assume H: "restructurable_heap (h(hp := Suc 0, Suc hp := k, Suc (Suc hp) := pc)) (3 + hp) ep lcd"
  moreover hence "\<And>x. x < 3 + hp \<Longrightarrow> 3 dvd x \<Longrightarrow> 0 < ?f x \<and> ?f x \<le> lcd \<Longrightarrow> 
    even (?g x) \<and> ?g x \<le> ep \<and> 0 < ?h x \<and> ?h x \<le> lcd" by (simp add: restructurable_heap_def)
  moreover from H have "3 dvd hp" by (simp add: restructurable_heap_def)
  ultimately have "hp < 3 + hp \<Longrightarrow> 0 < ?f hp \<and> ?f hp \<le> lcd \<Longrightarrow> 
    even (?g hp) \<and> ?g hp \<le> ep \<and> 0 < ?h hp \<and> ?h hp \<le> lcd" by blast
  moreover assume "lcd \<noteq> 0"
  ultimately show "even k \<and> k \<le> ep \<and> pc \<noteq> 0 \<and> pc \<le> lcd" by simp
next
  assume "restructurable_heap h hp ep lcd" and "even k \<and> k \<le> ep \<and> pc \<noteq> 0 \<and> pc \<le> lcd"
  thus "restructurable_heap (h(hp := Suc 0, Suc hp := k, Suc (Suc hp) := pc)) (3 + hp) ep lcd" 
    by (auto simp add: restructurable_heap_def)
qed

lemma [simp]: "restructurable_heap h hp ep lcd \<Longrightarrow> restructurable_heap h hp (Suc (Suc ep)) lcd"
  by (auto simp add: restructurable_heap_def)

lemma [simp]: "restructurable_env e ep hp \<Longrightarrow> restructurable_env e ep (3 + hp)"
  by (auto simp add: restructurable_env_def)

lemma [simp]: "restructurable_env e ep hp \<Longrightarrow> restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> 
  restructurable_heap h hp ep lcd \<Longrightarrow> h (vs vp) = Suc x \<Longrightarrow>
    restructurable_env (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (Suc (Suc ep)) hp"
proof (unfold restructurable_env_def restructurable_vals_def restructurable_heap_def, 
       rule, simp, rule, rule)
  fix y 
  assume "3 dvd hp \<and> (\<forall>x < hp. 3 dvd x \<longrightarrow> h x \<noteq> 0 \<longrightarrow> 
    even (h (Suc x)) \<and> h (Suc x) \<le> ep \<and> h (Suc (Suc x)) \<noteq> 0 \<and> h (Suc (Suc x)) \<le> lcd)"
     and "h (vs vp) = Suc x" and "\<forall>x < Suc (Suc vp). 3 dvd vs x \<and> vs x < hp"
  hence "even (h (Suc (vs vp))) \<and> h (Suc (vs vp)) \<le> ep" by simp
  moreover assume "even ep \<and> 
    (\<forall>x < ep. if even x then 3 dvd e x \<and> e x < hp else even (e x) \<and> e x \<le> ep)"
              and "y < Suc (Suc ep)" and "\<forall>x < Suc (Suc vp). 3 dvd vs x \<and> vs x < hp"
  ultimately show "if even y
        then 3 dvd (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) y \<and> 
          (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) y < hp
        else even ((e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) y) \<and>
          (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) y \<le> Suc (Suc ep)" by auto
qed

lemma [simp]: "restructurable_vals vs vp hp \<Longrightarrow> 
    restructurable_vals (vs(vp := k)) (Suc vp) hp = (k < hp \<and> 3 dvd k)"
  by (auto simp add: restructurable_vals_def)

lemma [simp]: "restructurable_vals vs vp hp \<Longrightarrow> 
    restructurable_vals (vs(vp := k)) (Suc vp) (3 + hp) = (k < 3 + hp \<and> 3 dvd k)"
  by (auto simp add: restructurable_vals_def)

lemma [elim]: "restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> restructurable_vals vs vp hp"
  by (simp add: restructurable_vals_def)

lemma [elim]: "restructurable_stack sh (Suc (Suc sp)) ep lcd \<Longrightarrow> restructurable_stack sh sp ep lcd"
  by (simp add: restructurable_stack_def)

lemma [simp]: "restructurable_stack sh 0 ep lcd"
  by (simp add: restructurable_stack_def)

lemma [simp]: "restructurable_stack sh (Suc (Suc sp)) ep lcd \<Longrightarrow> odd sp \<Longrightarrow> sh sp \<noteq> 0"
  by (simp add: restructurable_stack_def)

lemma [simp]: "restructurable_stack sh (Suc (Suc sp)) ep lcd \<Longrightarrow> odd sp \<Longrightarrow> sh sp \<le> lcd"
  by (simp add: restructurable_stack_def)

lemma [simp]: "restructurable_stack sh sp ep lcd \<Longrightarrow> odd sp \<Longrightarrow> pc \<noteq> 0 \<Longrightarrow> Suc pc \<le> lcd \<Longrightarrow> 
  even ep \<Longrightarrow> 
    restructurable_stack (sh(sp := pc, Suc sp := Suc (Suc ep))) (Suc (Suc sp)) (Suc (Suc ep)) lcd"
  by (unfold restructurable_stack_def) auto

lemma [simp]: "restructurable_stack sh sp ep lcd \<Longrightarrow> odd sp \<Longrightarrow> Suc pc \<le> lcd \<Longrightarrow> 
  restructurable_env e ep hp \<Longrightarrow> return_terminated cd \<Longrightarrow> cd ! pc = BApply \<Longrightarrow> 
    restructurable_stack (sh(sp := pc, Suc sp := Suc (Suc ep))) (Suc (Suc sp)) (Suc (Suc ep)) lcd"
proof -
  assume "return_terminated cd" and "cd ! pc = BApply"
  hence "pc = 0 \<Longrightarrow> False" by simp
  hence "pc \<noteq> 0" by auto
  moreover assume "restructurable_env e ep hp"
  moreover hence "even ep" by auto
  moreover assume "restructurable_stack sh sp ep lcd" and "odd sp" and "Suc pc \<le> lcd"
  ultimately show ?thesis by simp
qed

lemma [simp]: "restructurable_env e ep hp \<Longrightarrow> restructurable_stack sh sp ep lcd \<Longrightarrow> odd sp \<Longrightarrow> 
    restructurable_stack (sh(sp - Suc 0 := Suc (Suc ep))) sp (Suc (Suc ep)) lcd"
  by (unfold restructurable_stack_def) auto

lemma [simp]: "h (vs vp) = Suc y \<Longrightarrow> restructurable_heap h hp ep lcd \<Longrightarrow> 
    restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> 0 < h (Suc (Suc (vs vp)))"
  by (simp add: restructurable_heap_def restructurable_vals_def)

lemma [simp]: "h (vs vp) = Suc y \<Longrightarrow> restructurable_heap h hp ep lcd \<Longrightarrow> 
    restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> h (Suc (Suc (vs vp))) \<le> lcd"
  by (simp add: restructurable_heap_def restructurable_vals_def)

lemma [elim]: "unstr_lookup e p x = Some y \<Longrightarrow> p \<le> ep \<Longrightarrow> even p \<Longrightarrow> restructurable_env e ep hp \<Longrightarrow> 
    y < hp"
proof (induction e p x rule: unstr_lookup.induct)
  case (4 e p x)
  moreover hence "even (e (Suc p)) \<and> e (Suc p) \<le> ep" by (simp add: restructurable_env_def)
  ultimately show ?case by simp
qed (auto simp add: restructurable_env_def)

lemma [elim]: "unstr_lookup e p x = Some y \<Longrightarrow> p \<le> ep \<Longrightarrow> even p \<Longrightarrow> restructurable_env e ep hp \<Longrightarrow> 
    3 dvd y"
proof (induction e p x rule: unstr_lookup.induct) 
  case (4 e p x)
  moreover hence "even (e (Suc p)) \<and> e (Suc p) \<le> ep" by (simp add: restructurable_env_def)
  ultimately show ?case by simp
qed (auto simp add: restructurable_env_def)

lemma [simp]: "odd sp \<Longrightarrow> restructurable_stack sh sp ep lcd \<Longrightarrow> even (sh (sp - Suc 0))" 
  by (unfold restructurable_stack_def) auto

lemma [simp]: "odd sp \<Longrightarrow> restructurable_stack sh sp ep lcd \<Longrightarrow> sh (sp - Suc 0) \<le> ep" 
  by (unfold restructurable_stack_def) auto

lemma [elim]: "unstr_lookup e (sh (sp - Suc 0)) x = Some y \<Longrightarrow> restructurable_stack sh sp ep lcd \<Longrightarrow> 
  restructurable_env e ep hp \<Longrightarrow> odd sp \<Longrightarrow> y < hp"
proof -
  assume "odd sp" and "restructurable_stack sh sp ep lcd"  
  hence "even (sh (sp - Suc 0))" and "sh (sp - Suc 0) \<le> ep" by auto
  moreover assume "unstr_lookup e (sh (sp - Suc 0)) x = Some y" and "restructurable_env e ep hp"
  ultimately show "y < hp" by auto
qed

lemma [elim]: "unstr_lookup e (sh (sp - Suc 0)) x = Some y \<Longrightarrow> restructurable_stack sh sp ep lcd \<Longrightarrow> 
    restructurable_env e ep hp \<Longrightarrow> odd sp \<Longrightarrow> 3 dvd y"
proof -
  assume "odd sp" and "restructurable_stack sh sp ep lcd"  
  hence "sh (sp - Suc 0) \<le> ep \<and> even (sh (sp - Suc 0))" by (unfold restructurable_stack_def) auto
  moreover assume "unstr_lookup e (sh (sp - Suc 0)) x = Some y" and "restructurable_env e ep hp"
  ultimately show "3 dvd y" by auto
qed

lemma [simp]: "h (vs vp) = Suc x \<Longrightarrow> restructurable_heap h hp ep (length cd) \<Longrightarrow> 
    restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> h (Suc (Suc (vs vp))) \<noteq> 0"
  by simp

lemma preserve_restructure [simp]: "cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd \<Longrightarrow> 
    restructurable \<Sigma>\<^sub>u' cd"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct) auto

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
    h = H h' hp \<and> env = H e ep \<and> listify' vs' vp = v1 # v2 # vs \<and> p = sh sp \<and> sfs = listify' sh sp" 
      by fastforce
  then obtain vp' where V: "vp = Suc (Suc vp') \<and> v1 = vs' (Suc vp') \<and> v2 = vs' vp' \<and> 
    vs = listify' vs' vp'" by fastforce
  with evf_apply S obtain x where H: "h' (vs' vp') = Suc x \<and> p' = h' (Suc (vs' vp')) \<and> 
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
  with evf_jump S obtain x where H: "h' (vs' vp') = Suc x \<and> p' = h' (Suc (vs' vp')) \<and> 
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