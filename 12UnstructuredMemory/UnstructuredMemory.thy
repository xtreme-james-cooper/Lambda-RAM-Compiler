theory UnstructuredMemory
  imports "../08FlatCode/CodeFlattening"
begin

datatype unstr_state = 
  US "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat nat

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
      US (h(hp := 1, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) e ep 
        (vs(vp := hp)) (Suc vp) sh sp pc"
| evu_pushlam [simp]: "cd ! pc = BPushLam pc' \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u 
      US (h(hp := 0, Suc hp := sh (sp - 1), Suc (Suc hp) := pc')) (3 + hp) e ep 
        (vs(vp := hp)) (Suc vp) sh sp pc"
| evu_apply [simp]: "cd ! pc = BApply \<Longrightarrow> h (vs vp) = 0 \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs (Suc (Suc vp)) sh sp (Suc pc) \<leadsto>\<^sub>u 
      US h hp (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (2 + ep) vs vp
        (sh(sp := pc, Suc sp := Suc (Suc ep))) (2 + sp) (h (Suc (Suc (vs vp))))"
| evu_return_normal [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u US h hp e ep vs vp sh sp (sh sp)"
| evu_return_end [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh (Suc 0) (Suc pc) \<leadsto>\<^sub>u US h hp e ep vs vp sh 0 0"
| evu_jump [simp]: "cd ! pc = BJump \<Longrightarrow> h (vs vp) = 0 \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs (Suc (Suc vp)) sh sp (Suc pc) \<leadsto>\<^sub>u 
      US h hp (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (2 + ep) vs vp
        (sh(sp - 1 := Suc (Suc ep))) sp (h (Suc (Suc (vs vp))))"

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
  case (evu_apply cd pc h vs vp hp e ep sh sp)
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
    by (induction cd "US h hp e ep vs vp sh (Suc 0) (Suc pc)" \<Sigma>'' rule: evalu.induct) 
       simp_all
next
  case (evu_jump cd pc h vs vp hp e ep sh sp)
  from evu_jump(3, 1, 2) show ?case    
    by (induction cd "US h hp e ep vs (Suc (Suc vp)) sh sp (Suc pc)" \<Sigma>'' rule: evalu.induct) 
       simp_all
qed

definition restructurable_heap :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "restructurable_heap h hp ep lcd = (3 dvd hp \<and> (\<forall>x < hp. 3 dvd x \<longrightarrow> h x = 0 \<longrightarrow> 
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
    restructurable_heap (h(hp := Suc 0, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) ep lcd"
  by (auto simp add: restructurable_heap_def)

lemma [simp]: "restructurable_heap h hp ep lcd \<Longrightarrow> lcd \<noteq> 0 \<Longrightarrow>
  restructurable_heap (h(hp := 0, Suc hp := k, Suc (Suc hp) := pc)) (3 + hp) ep lcd = 
    (even k \<and> k \<le> ep \<and> pc \<noteq> 0 \<and> pc \<le> lcd)"
proof
  let ?f = "\<lambda>x. if x = Suc (Suc hp) then pc else (h(hp := 0, Suc hp := k)) x"
  let ?g = "\<lambda>x. if x = Suc hp then pc else (h(hp := 0, Suc hp := k)) (Suc x)"
  let ?h = "\<lambda>x. if x = hp then pc else (h(hp := 0, Suc hp := k)) (Suc (Suc x))"
  assume H: "restructurable_heap (h(hp := 0, Suc hp := k, Suc (Suc hp) := pc)) (3 + hp) ep lcd"
  moreover hence "\<And>x. x < 3 + hp \<Longrightarrow> 3 dvd x \<Longrightarrow> ?f x = 0 \<Longrightarrow> 
    even (?g x) \<and> ?g x \<le> ep \<and> 0 < ?h x \<and> ?h x \<le> lcd" by (simp add: restructurable_heap_def)
  moreover from H have "3 dvd hp" by (simp add: restructurable_heap_def)
  ultimately have "hp < 3 + hp \<Longrightarrow> ?f hp = 0 \<Longrightarrow> 
    even (?g hp) \<and> ?g hp \<le> ep \<and> 0 < ?h hp \<and> ?h hp \<le> lcd" by blast
  moreover assume "lcd \<noteq> 0"
  ultimately show "even k \<and> k \<le> ep \<and> pc \<noteq> 0 \<and> pc \<le> lcd" by simp
next
  assume "restructurable_heap h hp ep lcd" and "even k \<and> k \<le> ep \<and> pc \<noteq> 0 \<and> pc \<le> lcd"
  thus "restructurable_heap (h(hp := 0, Suc hp := k, Suc (Suc hp) := pc)) (3 + hp) ep lcd" 
    by (auto simp add: restructurable_heap_def)
qed

lemma [simp]: "restructurable_heap h hp ep lcd \<Longrightarrow> restructurable_heap h hp (Suc (Suc ep)) lcd"
  by (auto simp add: restructurable_heap_def)

lemma [simp]: "restructurable_env e ep hp \<Longrightarrow> restructurable_env e ep (3 + hp)"
  by (auto simp add: restructurable_env_def)

lemma [simp]: "restructurable_env e ep hp \<Longrightarrow> restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> 
  restructurable_heap h hp ep lcd \<Longrightarrow> h (vs vp) = 0 \<Longrightarrow>
    restructurable_env (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (Suc (Suc ep)) hp"
proof (unfold restructurable_env_def restructurable_vals_def restructurable_heap_def, 
       rule, simp, rule, rule)
  fix y 
  assume "3 dvd hp \<and> (\<forall>x < hp. 3 dvd x \<longrightarrow> h x = 0 \<longrightarrow> 
    even (h (Suc x)) \<and> h (Suc x) \<le> ep \<and> h (Suc (Suc x)) \<noteq> 0 \<and> h (Suc (Suc x)) \<le> lcd)"
     and "h (vs vp) = 0" and "\<forall>x < Suc (Suc vp). 3 dvd vs x \<and> vs x < hp"
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

lemma [simp]: "h (vs vp) = 0 \<Longrightarrow> restructurable_heap h hp ep lcd \<Longrightarrow> 
    restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> 0 < h (Suc (Suc (vs vp)))"
  by (simp add: restructurable_heap_def restructurable_vals_def)

lemma [simp]: "h (vs vp) = 0 \<Longrightarrow> restructurable_heap h hp ep lcd \<Longrightarrow> 
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

lemma [simp]: "h (vs vp) = 0 \<Longrightarrow> restructurable_heap h hp ep (length cd) \<Longrightarrow> 
    restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> h (Suc (Suc (vs vp))) \<noteq> 0"
  by simp

lemma preserve_restructure [simp]: "cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd \<Longrightarrow> 
    restructurable \<Sigma>\<^sub>u' cd"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct) auto

end