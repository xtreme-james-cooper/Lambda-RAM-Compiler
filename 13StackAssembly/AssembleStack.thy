theory AssembleStack
  imports StackAssembly "../12UnstructuredMemory/UnstructuredMemory" "../00Utils/Utils"
begin

primrec assemble_stack_len :: "byte_code \<Rightarrow> nat" where
  "assemble_stack_len (BLookup x) = 1"
| "assemble_stack_len (BPushCon k) = 6"
| "assemble_stack_len (BPushLam pc) = 9"
| "assemble_stack_len BApply = 17"
| "assemble_stack_len BReturn = 1"
| "assemble_stack_len BJump = 15"

primrec assemble_stack_op :: "(nat \<Rightarrow> nat) \<Rightarrow> byte_code \<Rightarrow> sassm_code list" where
  "assemble_stack_op mp (BLookup x) = [undefined]"
| "assemble_stack_op mp (BPushCon k) = [
    SAMov (MCon 0),
    SAPush Hp (Con 0), 
    SAPush Hp (Con k), 
    SAPush Hp (Con 1), 
    SAPush Vals Acc, 
    SAMov (Mem Hp)]"
| "assemble_stack_op mp (BPushLam pc) = [
    SAMov (MCon 0),
    SAPush Hp (Con (mp pc)), 
    SAPush Hp Acc, 
    SAPush Hp (Con 0),
    SAGet Stk, 
    SASub 1,
    SAMov (Mem Stk),
    SAPush Vals Acc, 
    SAMov (Mem Hp)]"
| "assemble_stack_op mp BApply = [
    SAJump,
    SAGet Hp,
    SAAdd 1,
    SAUnbackup,
    SAPush Env Acc,
    SAGet Hp,
    SABackup,
    SAAdd 1,
    SAPop Vals,
    SAPush Stk Acc,
    SAAdd 1,
    SAMov (Mem Env),
    SAPush Stk Acc,
    SASub 14,
    SAMov PC,
    SAPush Env Acc,
    SAPop Vals]"
| "assemble_stack_op mp BReturn = [undefined]"
| "assemble_stack_op mp BJump = [
    SAJump,
    SAGet Hp,
    SAAdd 1,
    SAUnbackup,
    SAPush Env Acc,
    SAGet Hp,
    SABackup,
    SAAdd 1,
    SAPop Vals,
    SAPush Stk Acc,
    SAAdd 1,
    SAMov (Mem Env),
    SAPop Stk,
    SAPush Env Acc,
    SAPop Vals]"

(*   evu_lookup [simp]: "cd ! pc = BLookup x \<Longrightarrow> unstr_lookup e (sh (sp - 1)) x = Some y \<Longrightarrow>
    cd \<tturnstile> US h hp e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u US h hp e ep (vs(vp := y)) (Suc vp) sh sp pc"
| evu_return_normal [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh (Suc (Suc sp)) (Suc pc) 0 0 \<leadsto>\<^sub>u 
         US h hp e ep vs vp sh sp             (sh sp)  0 0"
| evu_return_end [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh (Suc 0) (Suc pc) 0 0 \<leadsto>\<^sub>u 
         US h hp e ep vs vp sh 0       0        0 0" *)

abbreviation assemble_extend_map :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "assemble_extend_map mp b lop x \<equiv> (if x < b then mp x else mp x + lop - 1)"

fun assembly_map :: "byte_code list \<Rightarrow> nat \<Rightarrow> nat" where
  "assembly_map [] x = x"
| "assembly_map (op # cd) 0 = 0"
| "assembly_map (op # cd) (Suc x) = assemble_stack_len op + assembly_map cd x"

definition assemble_stack_code :: "byte_code list \<Rightarrow> sassm_code list" where
  "assemble_stack_code cd = concat (map (assemble_stack_op (assembly_map cd)) cd)"

definition assemble_heap :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "assemble_heap mp h x = (if x mod 3 = 2 \<and> h (x - 2) = 0 then mp (h x) else h x)"

definition assemble_stack :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "assemble_stack mp s x = (if even x then s x else mp (s x))"

primrec assemble_state :: "(nat \<Rightarrow> nat) \<Rightarrow> unstr_state \<Rightarrow> sassm_state" where
  "assemble_state mp (US h hp e ep vs vp sh sp pc) = 
    SAS (case_memory (assemble_heap mp h) e vs (assemble_stack mp sh)) 
      (case_memory hp ep vp sp) 0 0 (mp pc)"

abbreviation assm_state :: "byte_code list \<Rightarrow> unstr_state \<Rightarrow> sassm_state" where
  "assm_state cd \<equiv> assemble_state (assembly_map cd)"

lemma [simp]: "length (assemble_stack_op mp op) = assemble_stack_len op"
  by (induction op) simp_all

theorem completesa [simp]: "assemble_stack_code cd\<^sub>b \<tturnstile>\<^sub>s\<^sub>a assm_state cd\<^sub>b \<Sigma>\<^sub>u = Some \<Sigma>\<^sub>s\<^sub>a' \<Longrightarrow> 
  \<exists>n \<Sigma>\<^sub>s\<^sub>a'' \<Sigma>\<^sub>u'. iter_evalsa (assemble_stack_code cd\<^sub>b) n \<Sigma>\<^sub>s\<^sub>a' = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u') \<and> 
    cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u'"
  by simp

lemma [simp]: "cd ! pc = op \<Longrightarrow> pc < length cd \<Longrightarrow> 
  assembly_map cd (Suc pc) = assemble_stack_len op + assembly_map cd pc"
proof (induction cd pc rule: assembly_map.induct)
  case (2 op' cd)
  thus ?case by (cases cd) simp_all
qed simp_all

lemma assemble_code_lookup' [simp]: "cd ! pc = op \<Longrightarrow> pc < length cd \<Longrightarrow> 
  x < assemble_stack_len op \<Longrightarrow> concat (map (assemble_stack_op (assembly_map (cd' @ cd))) cd) ! 
    (x + assembly_map cd pc) = assemble_stack_op (assembly_map (cd' @ cd)) op ! x"
proof (induction cd pc arbitrary: cd' rule: assembly_map.induct)
  case (3 op' cd y)
  hence "concat (map (assemble_stack_op (assembly_map ((cd' @ [op']) @ cd))) cd) ! 
    (x + assembly_map cd y) = assemble_stack_op (assembly_map ((cd' @ [op']) @ cd)) op ! x" 
      by fastforce
  hence "(assemble_stack_op (assembly_map (cd' @ op' # cd)) op' @ 
    concat (map (assemble_stack_op (assembly_map (cd' @ op' # cd))) cd)) !
      (assemble_stack_len op' + x + assembly_map cd y) =
        assemble_stack_op (assembly_map (cd' @ op' # cd)) op ! x" by (simp add: nth_append)
  hence "(assemble_stack_op (assembly_map (cd' @ op' # cd)) op' @ 
    concat (map (assemble_stack_op (assembly_map (cd' @ op' # cd))) cd)) !
      (x + (assemble_stack_len op' + assembly_map cd y)) =
        assemble_stack_op (assembly_map (cd' @ op' # cd)) op ! x" by (metis add.assoc add.commute)
  thus ?case by simp
qed (simp_all add: nth_append)

lemma assemble_code_lookup [simp]: "cd ! pc = op \<Longrightarrow> pc < length cd \<Longrightarrow> 
  x < assemble_stack_len op \<Longrightarrow> 
    assemble_stack_code cd ! (x + assembly_map cd pc) = assemble_stack_op (assembly_map cd) op ! x"
  by (metis assemble_code_lookup' append_Nil assemble_stack_code_def)

lemma [simp]: "cd ! pc = op \<Longrightarrow> pc < length cd \<Longrightarrow> 1 < assemble_stack_len op \<Longrightarrow> 
    assemble_stack_code cd ! (Suc (assembly_map cd pc)) = assemble_stack_op (assembly_map cd) op ! 1"
  using assemble_code_lookup by fastforce

lemma [simp]: "cd ! pc = op \<Longrightarrow> pc < length cd \<Longrightarrow> 0 < assemble_stack_len op \<Longrightarrow> 
    assemble_stack_code cd ! (assembly_map cd pc) = assemble_stack_op (assembly_map cd) op ! 0"
  using assemble_code_lookup by fastforce

lemma [simp]: "m Hp = h \<Longrightarrow> m Env = e \<Longrightarrow> m Vals = vs \<Longrightarrow> m Stk = sh \<Longrightarrow> m = case_memory h e vs sh" 
  by rule (simp split: memory.splits)

lemma assm_hp_lemma1: "3 dvd x \<Longrightarrow> assemble_heap mp h x = h x"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma2: "x mod 3 = 1 \<Longrightarrow> assemble_heap mp h x = h x"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma3: "x mod 3 = 2 \<Longrightarrow> h (x - 2) \<noteq> 0 \<Longrightarrow> assemble_heap mp h x = h x"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma4: "x mod 3 = 2 \<Longrightarrow> h (x - 2) = 0 \<Longrightarrow> assemble_heap mp h x = mp (h x)"
  by (simp add: assemble_heap_def)

lemma assemble_heap_update_lemma [simp]: "3 dvd hp \<Longrightarrow> x \<noteq> hp \<Longrightarrow> x \<noteq> Suc hp \<Longrightarrow> 
  x \<noteq> Suc (Suc hp) \<Longrightarrow> x mod 3 = 2 \<Longrightarrow> 
    (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) (x - 2) = h (x - 2)"
proof (induction x)
  case (Suc x)
  from Suc(2, 3, 4, 5, 6) show ?case 
  proof (induction x)
    case (Suc x)
    from Suc(6) have "3 dvd x" by presburger
    with Suc(2, 3, 4, 5, 6) show ?case by auto
  qed simp_all
qed simp_all

lemma [simp]: "3 dvd hp \<Longrightarrow> x \<noteq> hp \<Longrightarrow> x \<noteq> Suc hp \<Longrightarrow> x \<noteq> Suc (Suc hp) \<Longrightarrow> 
  assemble_heap (assembly_map cd) (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x = 
    assemble_heap (assembly_map cd) h x"
proof (unfold assemble_heap_def, cases "x mod 3 = 2")
  case True
  assume "3 dvd hp" and "x \<noteq> hp" and "x \<noteq> Suc hp" and "x \<noteq> Suc (Suc hp)"
  moreover with True have "(h(hp := a, Suc hp := b, Suc (Suc hp) := c)) (x - 2) = h (x - 2)" 
    by (metis assemble_heap_update_lemma)
  ultimately show "(if x mod 3 = 2 \<and> (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) (x - 2) = 0
    then assembly_map cd ((h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x) 
      else (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x) =
        (if x mod 3 = 2 \<and> h (x - 2) = 0 then assembly_map cd (h x) else h x)" by simp
next
  case False
  assume "x \<noteq> hp" and "x \<noteq> Suc hp" and "x \<noteq> Suc (Suc hp)"
  hence "(x = hp \<longrightarrow> a = h hp) \<and> (x \<noteq> hp \<longrightarrow> (x = Suc hp \<longrightarrow> b = h (Suc hp)) \<and> 
    (x \<noteq> Suc hp \<longrightarrow> x = Suc (Suc hp) \<longrightarrow> c = h (Suc (Suc hp))))" by simp
  with False show "(if x mod 3 = 2 \<and> (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) (x - 2) = 0
    then assembly_map cd ((h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x) 
      else (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x) =
        (if x mod 3 = 2 \<and> h (x - 2) = 0 then assembly_map cd (h x) else h x)" by simp
qed

lemma [simp]: "restructurable_heap h hp ep (length cd) \<Longrightarrow> 
  (assemble_heap (assembly_map cd) h)(hp := Suc a, Suc hp := b, Suc (Suc hp) := c) = 
    assemble_heap (assembly_map cd) (h(hp := Suc a, Suc hp := b, Suc (Suc hp) := c))"
proof
  fix x
  assume "restructurable_heap h hp ep (length cd)"
  hence H: "3 dvd hp" by (simp add: restructurable_heap_def)
  moreover hence "Suc hp mod 3 = 1" by presburger
  moreover hence "Suc (Suc hp) mod 3 = 2" by presburger
  ultimately show "
    ((assemble_heap (assembly_map cd) h)(hp := Suc a, Suc hp := b, Suc (Suc hp) := c)) x =
      assemble_heap (assembly_map cd) (h(hp := Suc a, Suc hp := b, Suc (Suc hp) := c)) x" 
    by (simp add: assm_hp_lemma1 assm_hp_lemma2 assm_hp_lemma3)
qed

lemma [simp]: "restructurable_heap h hp ep (length cd) \<Longrightarrow> 
  (assemble_heap (assembly_map cd) h)(hp := 0, Suc hp := a, Suc (Suc hp) := assembly_map cd b) = 
    assemble_heap (assembly_map cd) (h(hp := 0, Suc hp := a, Suc (Suc hp) := b))"
proof
  fix x
  assume "restructurable_heap h hp ep (length cd)"
  hence H: "3 dvd hp" by (simp add: restructurable_heap_def)
  moreover hence "Suc hp mod 3 = 1" by presburger
  moreover hence "Suc (Suc hp) mod 3 = 2" by presburger
  ultimately show "((assemble_heap (assembly_map cd) h)(hp := 0, Suc hp := a, 
    Suc (Suc hp) := assembly_map cd b)) x =
      assemble_heap (assembly_map cd) (h(hp := 0, Suc hp := a, Suc (Suc hp) := b)) x" 
    by (simp add: assm_hp_lemma1 assm_hp_lemma2 assm_hp_lemma4)
qed

lemma [simp]: "restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> 
    assemble_heap mp h (Suc (vs vp)) = h (Suc (vs vp))"
proof (unfold assemble_heap_def restructurable_vals_def)
  assume "\<forall>x<Suc (Suc vp). 3 dvd vs x \<and> vs x < hp"
  hence "3 dvd vs vp" by simp
  hence "Suc (vs vp) mod 3 = 1" by presburger
  thus "(if Suc (vs vp) mod 3 = 2 \<and> h (Suc (vs vp) - 2) = 0 then mp (h (Suc (vs vp))) 
         else h (Suc (vs vp))) = h (Suc (vs vp))" by simp
qed

lemma [simp]: "restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> h (vs vp) = 0 \<Longrightarrow>
    assemble_heap mp h (Suc (Suc (vs vp))) = mp (h (Suc (Suc (vs vp))))"
proof (unfold assemble_heap_def restructurable_vals_def)
  assume "\<forall>x<Suc (Suc vp). 3 dvd vs x \<and> vs x < hp"
  hence "3 dvd vs vp" by simp
  hence "Suc (Suc (vs vp)) mod 3 = 2" by presburger
  moreover assume "h (vs vp) = 0"
  ultimately show "(if Suc (Suc (vs vp)) mod 3 = 2 \<and> h (Suc (Suc (vs vp)) - 2) = 0 
    then mp (h (Suc (Suc (vs vp)))) else h (Suc (Suc (vs vp)))) = mp (h (Suc (Suc (vs vp))))" 
      by simp
qed

lemma [simp]: "h (vs vp) = Suc x \<Longrightarrow>
    assemble_heap mp h (Suc (Suc (vs vp))) = h (Suc (Suc (vs vp)))"
  by (simp add: assemble_heap_def)

lemma [simp]: "odd sp \<Longrightarrow> assemble_stack (assembly_map cd) sh (sp - Suc 0) = sh (sp - Suc 0)"
  by (simp add: assemble_stack_def)

lemma [simp]: "odd sp \<Longrightarrow> 
  ((assemble_stack (assembly_map cd) sh)(sp := assembly_map cd pc, Suc sp := a)) =
    (assemble_stack (assembly_map cd) (sh(sp := pc, Suc sp := a)))"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "odd (Suc sp) \<Longrightarrow> 
  (assemble_stack (assembly_map cd) sh)(sp := Suc (Suc ep)) = 
    assemble_stack (assembly_map cd) (sh(sp := Suc (Suc ep)))"
  by (auto simp add: assemble_stack_def)

theorem correctsa [simp]: "cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow> 
  \<exists>n. iter_evalsa (assemble_stack_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u')"
proof (induction cd\<^sub>b \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct)
case (evu_lookup cd pc x e sh sp y h hp ep vs vp)
  then show ?case by simp
next
  case (evu_pushcon cd pc k h hp e ep vs vp sh sp)
  moreover hence "assemble_stack_code cd ! (5 + assembly_map cd pc) = SAMov (Mem Hp)" by simp
  moreover from evu_pushcon have "assemble_stack_code cd ! (4 + assembly_map cd pc) =
    SAPush Vals Acc" by simp
  moreover from evu_pushcon have "assemble_stack_code cd ! (3 + assembly_map cd pc) = 
    SAPush Hp (Con 1)" by simp
  moreover from evu_pushcon have "assemble_stack_code cd ! (2 + assembly_map cd pc) = 
    SAPush Hp (Con k)" by (simp del: add_2_eq_Suc) 
  ultimately have "iter_evalsa (assemble_stack_code cd) 6 (SAS (case_memory 
    (assemble_heap (assembly_map cd) h) e vs (assemble_stack (assembly_map cd) sh)) 
      (case_memory hp ep vp sp) 0 0 (assembly_map cd (Suc pc))) = 
        Some (SAS (case_memory (assemble_heap (assembly_map cd) 
          (h(hp := 1, Suc hp := k, Suc (Suc hp) := 0))) e (vs(vp := hp)) 
            (assemble_stack (assembly_map cd) sh)) (case_memory (3 + hp) ep (Suc vp) sp) 0 0 
              (assembly_map cd pc))" 
    by (auto simp add: numeral_def)
  thus ?case by auto
next
  case (evu_pushlam cd pc pc' h hp e ep vs vp sh sp)
  moreover hence "assemble_stack_code cd ! (8 + assembly_map cd pc) = SAMov (Mem Hp)" by simp
  moreover from evu_pushlam have "assemble_stack_code cd ! (7 + assembly_map cd pc) =
    SAPush Vals Acc" by simp
  moreover from evu_pushlam have "assemble_stack_code cd ! (6 + assembly_map cd pc) = 
    SAMov (Mem Stk)" by simp
  moreover from evu_pushlam have "assemble_stack_code cd ! (5 + assembly_map cd pc) = SASub 1" 
    by simp
  moreover from evu_pushlam have "assemble_stack_code cd ! (4 + assembly_map cd pc) = SAGet Stk" 
    by simp
  moreover from evu_pushlam have "assemble_stack_code cd ! (3 + assembly_map cd pc) = 
    SAPush Hp (Con 0)" by simp 
  moreover from evu_pushlam have "assemble_stack_code cd ! (2 + assembly_map cd pc) = 
    SAPush Hp Acc" by (simp del: add_2_eq_Suc) 
  ultimately have "iter_evalsa (assemble_stack_code cd) 9 (SAS (case_memory 
    (assemble_heap (assembly_map cd) h) e vs (assemble_stack (assembly_map cd) sh)) 
      (case_memory hp ep vp sp) 0 0 (assembly_map cd (Suc pc))) = Some (SAS (case_memory 
        (assemble_heap (assembly_map cd) 
          (h(hp := 0, Suc hp := sh (sp - Suc 0), Suc (Suc hp) := pc'))) e (vs(vp := hp)) 
            (assemble_stack (assembly_map cd) sh)) (case_memory (3 + hp) ep (Suc vp) sp) 0 0 
              (assembly_map cd pc))" 
    by (auto simp add: numeral_def)
  thus ?case by auto
next
  case (evu_apply cd pc h vs vp hp e ep sh sp)
  moreover from evu_apply have "assemble_stack_code cd ! (16 + assembly_map cd pc) = SAPop Vals" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (15 + assembly_map cd pc) = SAPush Env Acc" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (14 + assembly_map cd pc) = SAMov PC" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (13 + assembly_map cd pc) = SASub 14" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (12 + assembly_map cd pc) = SAPush Stk Acc" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (11 + assembly_map cd pc) = 
    SAMov (Mem Env)" by simp
  moreover from evu_apply have "assemble_stack_code cd ! (10 + assembly_map cd pc) = SAAdd 1" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (9 + assembly_map cd pc) = SAPush Stk Acc" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (8 + assembly_map cd pc) = SAPop Vals" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (7 + assembly_map cd pc) = SAAdd 1" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (6 + assembly_map cd pc) = SABackup" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (5 + assembly_map cd pc) = SAGet Hp" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (4 + assembly_map cd pc) = SAPush Env Acc" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (3 + assembly_map cd pc) = SAUnbackup" 
    by simp
  moreover from evu_apply have "assemble_stack_code cd ! (2 + assembly_map cd pc) = SAAdd 1" 
    by (simp del: add_2_eq_Suc)
  ultimately have "iter_evalsa (assemble_stack_code cd) 17 (SAS (case_memory 
    (assemble_heap (assembly_map cd) h) e vs (assemble_stack (assembly_map cd) sh)) 
      (case_memory hp ep (Suc (Suc vp)) sp) 0 0 (assembly_map cd (Suc pc))) =
        Some (SAS (case_memory (assemble_heap (assembly_map cd) h) (e(ep := vs (Suc vp), 
          Suc ep := h (Suc (vs vp)))) vs (assemble_stack (assembly_map cd) 
            (sh(sp := pc, Suc sp := Suc (Suc ep))))) (case_memory hp (Suc (Suc ep)) vp 
              (Suc (Suc sp))) 0 0 (assembly_map cd (h (Suc (Suc (vs vp))))))" 
    by (auto simp add: numeral_def)
  thus ?case by auto
next
  case (evu_return_normal cd pc h hp e ep vs vp sh sp)
  then show ?case by simp
next
  case (evu_return_end cd pc h hp e ep vs vp sh)
  then show ?case by simp
next
  case (evu_jump cd pc h vs vp hp e ep sh sp)
  moreover from evu_jump have "assemble_stack_code cd ! (14 + assembly_map cd pc) = SAPop Vals" 
    by simp
  moreover from evu_jump have "assemble_stack_code cd ! (13 + assembly_map cd pc) = SAPush Env Acc" 
    by simp
  moreover from evu_jump have "assemble_stack_code cd ! (12 + assembly_map cd pc) = SAPop Stk" 
    by simp
  moreover from evu_jump have "assemble_stack_code cd ! (11 + assembly_map cd pc) = SAMov (Mem Env)" 
    by simp
  moreover from evu_jump have "assemble_stack_code cd ! (10 + assembly_map cd pc) = SAAdd 1" 
    by simp
  moreover from evu_jump have "assemble_stack_code cd ! (9 + assembly_map cd pc) = SAPush Stk Acc" 
    by simp
  moreover from evu_jump have "assemble_stack_code cd ! (8 + assembly_map cd pc) = SAPop Vals" 
    by simp
  moreover from evu_jump have "assemble_stack_code cd ! (7 + assembly_map cd pc) = SAAdd 1" 
    by simp
  moreover from evu_jump have "assemble_stack_code cd ! (6 + assembly_map cd pc) = SABackup" 
    by simp
  moreover from evu_jump have "assemble_stack_code cd ! (5 + assembly_map cd pc) = SAGet Hp" 
    by simp
  moreover from evu_jump have "assemble_stack_code cd ! (4 + assembly_map cd pc) = SAPush Env Acc" 
    by simp
  moreover from evu_jump have "assemble_stack_code cd ! (3 + assembly_map cd pc) = SAUnbackup" 
    by simp
  moreover from evu_jump have "assemble_stack_code cd ! (2 + assembly_map cd pc) = SAAdd 1" 
    by (simp del: add_2_eq_Suc)
  ultimately have "iter_evalsa (assemble_stack_code cd) 15 (SAS (case_memory 
    (assemble_heap (assembly_map cd) h) e vs (assemble_stack (assembly_map cd) sh))
      (case_memory hp ep (Suc (Suc vp)) sp) 0 0 (assembly_map cd (Suc pc))) = Some (SAS (case_memory 
        (assemble_heap (assembly_map cd) h) (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) vs
          (assemble_stack (assembly_map cd) (sh(sp - Suc 0 := Suc (Suc ep)))))
            (case_memory hp (Suc (Suc ep)) vp sp) 0 0 (assembly_map cd (h (Suc (Suc (vs vp))))))" 
    by (auto simp add: numeral_def split: nat.splits)
  thus ?case by auto
qed

theorem correctsa_iter [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow> 
  \<exists>n. iter_evalsa (assemble_stack_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u')"
proof (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct)
  case (iter_refl \<Sigma>\<^sub>u)
  have "iter_evalsa (assemble_stack_code cd\<^sub>b) 0 (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u)" 
    by simp
  thus ?case by blast
next
  case (iter_step \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Sigma>\<^sub>u'')
  then obtain n where "iter_evalsa (assemble_stack_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = 
    Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u')" by fastforce
  moreover from iter_step obtain m where "
    iter_evalsa (assemble_stack_code cd\<^sub>b) m (assm_state cd\<^sub>b \<Sigma>\<^sub>u') = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u'')" 
      by fastforce
  ultimately have "iter_evalsa (assemble_stack_code cd\<^sub>b) (n + m) (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = 
    Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u'')" by simp
  thus ?case by blast
qed

end