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
  evu_lookup [simp]: "lookup cd pc = Some (BLookup x) \<Longrightarrow> unstr_lookup e (sh sp) x = Some y \<Longrightarrow>
    cd \<tturnstile> US h hp e ep vs vp sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
      US h hp e ep (vs(vp := y)) (Suc vp) sh (Suc sp) pc"
| evu_pushcon [simp]: "lookup cd pc = Some (BPushCon k) \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
      US (h(hp := 1, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp) e ep 
        (vs(vp := hp)) (Suc vp) sh (Suc sp) pc"
| evu_pushlam [simp]: "lookup cd pc = Some (BPushLam pc') \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
      US (h(hp := 0, Suc hp := sh sp, Suc (Suc hp) := pc')) (3 + hp) e ep 
        (vs(vp := hp)) (Suc vp) sh (Suc sp) pc"
| evu_apply [simp]: "lookup cd pc = Some BApply \<Longrightarrow> h (vs vp) = 0 \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs (Suc (Suc vp)) sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
      US h hp (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (2 + ep) vs vp
        (sh(Suc sp := pc, Suc (Suc sp) := Suc (Suc ep))) (2 + Suc sp) (h (Suc (Suc (vs vp))))"
| evu_return [simp]: "lookup cd pc = Some BReturn \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u 
      US h hp e ep vs vp (sh(sp := 0)) sp (sh sp)"
| evu_jump [simp]: "lookup cd pc = Some BJump \<Longrightarrow> h (vs vp) = 0 \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs (Suc (Suc vp)) sh (Suc sp) (Suc pc) \<leadsto>\<^sub>u 
      US h hp (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (2 + ep) vs vp
        (sh(sp := Suc (Suc ep))) (Suc sp) (h (Suc (Suc (vs vp))))"

theorem determinismu: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>u \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>u \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction cd \<Sigma> \<Sigma>' rule: evalu.induct)
  case (evu_lookup cd pc x e sh sp y h hp ep vs vp)
  from evu_lookup(3, 1, 2) show ?case 
    by (induction cd "US h hp e ep vs vp sh (Suc sp) (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
next
next
  case (evu_pushcon cd pc k h hp e ep vs vp sh sp)
  from evu_pushcon(2, 1) show ?case 
    by (induction cd "US h hp e ep vs vp sh (Suc sp) (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_pushlam cd pc pc' h hp e ep vs vp sh sp)
  from evu_pushlam(2, 1) show ?case 
    by (induction cd "US h hp e ep vs vp sh (Suc sp) (Suc pc)" \<Sigma>'' rule: evalu.induct) simp_all
next
  case (evu_apply cd pc h vs vp hp e ep sh sp)
  from evu_apply(3, 1, 2) show ?case    
    by (induction cd "US h hp e ep vs (Suc (Suc vp)) sh (Suc sp) (Suc pc)" \<Sigma>'' rule: evalu.induct) 
       simp_all
next
  case (evu_return cd pc h hp e ep vs vp sh sp)
  from evu_return(2, 1) show ?case 
    by (induction cd "US h hp e ep vs vp sh (Suc (Suc sp)) (Suc pc)" \<Sigma>'' rule: evalu.induct) 
       simp_all
next
  case (evu_jump cd pc h vs vp hp e ep sh sp)
  from evu_jump(3, 1, 2) show ?case    
    by (induction cd "US h hp e ep vs (Suc (Suc vp)) sh (Suc sp) (Suc pc)" \<Sigma>'' rule: evalu.induct) 
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
  "restructurable_stack sh sp ep lcd = (\<forall>x < sp. 
    if x = 0 then sh x = 0 else if even x then sh x \<noteq> 0 \<and> sh x \<le> lcd else even (sh x) \<and> sh x \<le> ep)"

primrec restructurable :: "unstr_state \<Rightarrow> byte_code list \<Rightarrow> bool" where
  "restructurable (US h hp e ep vs vp sh sp pc) cd = (pc \<le> length cd \<and> 
    length cd \<noteq> 0 \<and> orderly cd 0 \<and> return_terminated cd \<and> restructurable_heap h hp ep (length cd) \<and> 
      restructurable_env e ep hp \<and> restructurable_vals vs vp hp \<and> 
        restructurable_stack sh sp ep (length cd) \<and> even sp \<and> (sp = 0 \<longrightarrow> pc = 0))"

lemma [simp]: "odd (x::nat) \<Longrightarrow> 0 < x"
  by (cases x) simp_all

lemma [simp]: "return_terminated cd \<Longrightarrow> lookup cd 0 \<noteq> Some (BLookup x)"
  by (induction cd) auto

lemma [simp]: "return_terminated cd \<Longrightarrow> lookup cd 0 \<noteq> Some (BPushCon k)"
  by (induction cd) auto

lemma [simp]: "return_terminated cd \<Longrightarrow> lookup cd 0 \<noteq> Some (BPushLam pc)"
  by (induction cd) auto

lemma [simp]: "return_terminated cd \<Longrightarrow> lookup cd 0 \<noteq> Some BApply"
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

lemma [elim]: "restructurable_stack sh (Suc (Suc sp)) ep lcd \<Longrightarrow>
    restructurable_stack (sh(sp := 0)) sp ep lcd"
  by (simp add: restructurable_stack_def)

lemma [simp]: "restructurable_stack sh 0 ep lcd"
  by (simp add: restructurable_stack_def)

lemma [elim]: "restructurable_stack sh (Suc sp) ep lcd \<Longrightarrow> sh 0 = 0"
  by (simp add: restructurable_stack_def)

lemma [simp]: "restructurable_stack sh (Suc (Suc sp)) ep lcd \<Longrightarrow> even sp \<Longrightarrow> sh sp \<le> lcd"
proof (unfold restructurable_stack_def)
  assume "\<forall>x<Suc (Suc sp). if x = 0 then sh x = 0 else if even x 
    then sh x \<noteq> 0 \<and> sh x \<le> lcd else even (sh x) \<and> sh x \<le> ep"
     and "even sp"
  hence "if sp = 0 then sh sp = 0 else sh sp \<noteq> 0 \<and> sh sp \<le> lcd" by simp
  thus "sh sp \<le> lcd" by (simp split: if_splits)
qed

lemma [simp]: "0 \<noteq> pc \<Longrightarrow> pc \<le> lcd \<Longrightarrow> even ep \<Longrightarrow> even sp \<Longrightarrow> sp \<noteq> 0 \<Longrightarrow> 
  restructurable_stack sh sp ep lcd \<Longrightarrow>
    restructurable_stack (sh(sp := pc, Suc sp := Suc (Suc ep))) (Suc (Suc sp)) (Suc (Suc ep)) lcd"
proof (unfold restructurable_stack_def)
  let ?sh = "sh(sp := pc, Suc sp := Suc (Suc ep))"
  assume R: "\<forall>x < sp. if x = 0 then sh x = 0 else if even x then sh x \<noteq> 0 \<and> sh x \<le> lcd 
    else even (sh x) \<and> sh x \<le> ep"
  hence "\<And>x. x < sp \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> odd x \<Longrightarrow> even (sh x) \<and> sh x \<le> ep" by simp
  hence X: "\<And>x. odd x \<Longrightarrow> x < sp \<Longrightarrow> sh x \<le> Suc (Suc ep)" by fastforce
  assume "0 \<noteq> pc" and "pc \<le> lcd" and "even ep" and "even sp" and "sp \<noteq> 0"
  with R X show "\<forall>x<Suc (Suc sp). if x = 0 then ?sh x = 0 
    else if even x then ?sh x \<noteq> 0 \<and> ?sh x \<le> lcd else even (?sh x) \<and> ?sh x \<le> Suc (Suc ep)" 
      by auto
qed

lemma [simp]: "restructurable_stack sh sp ep lcd \<Longrightarrow> even sp \<Longrightarrow> Suc pc \<le> lcd \<Longrightarrow> sp \<noteq> 0 \<Longrightarrow>
  restructurable_env e ep hp \<Longrightarrow> return_terminated cd \<Longrightarrow> lookup cd pc = Some BApply \<Longrightarrow> 
    restructurable_stack (sh(sp := pc, Suc sp := Suc (Suc ep))) (Suc (Suc sp)) (Suc (Suc ep)) lcd"
proof -
  assume "return_terminated cd" and "lookup cd pc = Some BApply"
  hence "pc = 0 \<Longrightarrow> False" by simp
  hence "pc \<noteq> 0" by auto
  moreover assume "restructurable_env e ep hp"
  moreover hence "even ep" by auto
  moreover assume "restructurable_stack sh sp ep lcd" and "even sp" and "Suc pc \<le> lcd" and "sp \<noteq> 0"
  ultimately show ?thesis by simp
qed

lemma [simp]: "restructurable_env e ep hp \<Longrightarrow> restructurable_stack sh (Suc sp) ep lcd \<Longrightarrow> 
    odd sp \<Longrightarrow> restructurable_stack (sh(sp := Suc (Suc ep))) (Suc sp) (Suc (Suc ep)) lcd"
proof (unfold restructurable_stack_def)
  assume E: "restructurable_env e ep hp"
  assume O: "odd sp"
  assume R: "\<forall>x < Suc sp. if x = 0 then sh x = 0 else if even x then sh x \<noteq> 0 \<and> sh x \<le> lcd 
    else even (sh x) \<and> sh x \<le> ep"
  hence "\<And>x. x < Suc sp \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> odd x \<Longrightarrow> even (sh x) \<and> sh x \<le> ep" by simp
  hence "\<And>x. odd x \<Longrightarrow> x < Suc sp \<Longrightarrow> sh x \<le> Suc (Suc ep)" by fastforce
  with E R O show "\<forall>x<Suc sp. if x = 0 then (sh(sp := Suc (Suc ep))) x = 0
    else if even x then (sh(sp := Suc (Suc ep))) x \<noteq> 0 \<and> (sh(sp := Suc (Suc ep))) x \<le> lcd
      else even ((sh(sp := Suc (Suc ep))) x) \<and> (sh(sp := Suc (Suc ep))) x \<le> Suc (Suc ep)" 
    by auto
qed

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

lemma [simp]: "odd sp \<Longrightarrow> restructurable_stack sh (Suc sp) ep lcd \<Longrightarrow> even (sh sp)" 
  by (unfold restructurable_stack_def) auto

lemma [simp]: "odd sp \<Longrightarrow> restructurable_stack sh (Suc sp) ep lcd \<Longrightarrow> sh sp \<le> ep" 
  by (unfold restructurable_stack_def) auto

lemma [elim]: "unstr_lookup e (sh sp) x = Some y \<Longrightarrow> restructurable_stack sh (Suc sp) ep lcd \<Longrightarrow> 
  restructurable_env e ep hp \<Longrightarrow> odd sp \<Longrightarrow> y < hp"
proof -
  assume "odd sp" and "restructurable_stack sh (Suc sp) ep lcd"  
  hence "even (sh sp)" and "sh sp \<le> ep" by auto
  moreover assume "unstr_lookup e (sh sp) x = Some y" and "restructurable_env e ep hp"
  ultimately show "y < hp" by auto
qed

lemma [elim]: "unstr_lookup e (sh sp) x = Some y \<Longrightarrow> restructurable_stack sh (Suc sp) ep lcd \<Longrightarrow> 
  restructurable_env e ep hp \<Longrightarrow> odd sp \<Longrightarrow> 3 dvd y"
proof -
  assume "odd sp" and "restructurable_stack sh (Suc sp) ep lcd"  
  hence "sh sp \<le> ep \<and> even (sh sp)" by simp
  moreover assume "unstr_lookup e (sh sp) x = Some y" and "restructurable_env e ep hp"
  ultimately show "3 dvd y" by auto
qed

lemma [simp]: "h (vs vp) = 0 \<Longrightarrow> restructurable_heap h hp ep (length cd) \<Longrightarrow> 
    restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> h (Suc (Suc (vs vp))) \<noteq> 0"
  by simp

lemma preserve_restructure [simp]: "cd \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd \<Longrightarrow> 
    restructurable \<Sigma>\<^sub>u' cd"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct) auto

lemma [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd \<Longrightarrow> restructurable \<Sigma>\<^sub>u' cd"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct) auto

lemma [simp]: "restructurable_heap nmem 0 0 x"
  by (simp add: restructurable_heap_def)

lemma [simp]: "restructurable_env nmem 0 0"
  by (simp add: restructurable_env_def)

lemma [simp]: "restructurable_vals nmem 0 0" 
  by (simp add: restructurable_vals_def)

lemma [simp]: "restructurable_stack (nmem(0 := 0, Suc 0 := 0)) 2 0 lcd"
  by (simp only: restructurable_stack_def) simp_all

end