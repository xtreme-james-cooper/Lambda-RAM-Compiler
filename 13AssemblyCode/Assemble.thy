theory Assemble
  imports AssemblyCode "../12UnstructuredMemory/UnstructuredMemory" "../00Utils/Utils"
begin

primrec assemble_op_len :: "byte_code \<Rightarrow> nat" where
  "assemble_op_len (BLookup x) = 8 + 2 * x"
| "assemble_op_len (BPushCon k) = 8"
| "assemble_op_len (BPushLam pc) = 12"
| "assemble_op_len BApply = 22"
| "assemble_op_len BReturn = 4"
| "assemble_op_len BJump = 19"

primrec assemble_op :: "(nat \<Rightarrow> nat) \<Rightarrow> byte_code \<Rightarrow> assm list" where
  "assemble_op mp (BLookup x) = [
    AMov (Con 0),
    AAdd Vals 1,
    APutA Vals,
    AGetA Env (Reg Vals),
    ASubA 2 (Reg Env)] @
    concat (replicate x [
    AGetA Env (Reg Env),
    ASubA 1 (Reg Env)]) @ [
    AGetA Stk (Reg Env),
    ASubA 1 (Reg Stk),
    AMov (Reg Stk)]"
| "assemble_op mp (BPushCon k) = [
    AAdd Hp 1, 
    APutA Hp,
    AAdd Hp 1,  
    APut Hp (Con k),
    AAdd Hp 1,  
    APut Hp (Con 1), 
    AAdd Vals 1,
    APut Vals (Reg Hp)]"
| "assemble_op mp (BPushLam pc) = [
    AAdd Hp 1, 
    APut Hp (Con (mp pc)), 
    AMov (Con 0),
    AAdd Hp 1, 
    APutA Hp,
    AAdd Hp 1, 
    APut Hp (Con 0),
    AGetA Stk (Reg Hp), 
    ASubA 1 (Reg Stk),
    AMov (Reg Stk),
    AAdd Vals 1,
    APut Vals (Reg Hp)]"
| "assemble_op mp BApply = [
    AJmp,
    AGetA Hp PC,
    AAddA 2 (Reg Hp),
    AGet Vals (Reg Hp),
    AAdd Env 1,
    APutA Env,
    AGetA Hp (Reg Env),
    AAddA 1 (Reg Hp),
    AGet Vals (Reg Hp),
    ASub Vals 1,
    AAdd Stk 1,
    APutA Stk,
    AAddA 1 (Reg Env),
    AMov (Reg Env),
    AAdd Stk 1,
    APutA Stk,
    ASubA 17 PC,
    AMov PC,
    AAdd Env 1,
    APutA Env,
    AGet Vals (Reg Env),
    ASub Vals 1]"
| "assemble_op mp BReturn = [
    AJmp,
    APut Stk (Con 0),
    AGet Stk PC,
    ASub Stk 2]"
| "assemble_op mp BJump = [
    AJmp,
    AGetA Hp PC,
    AAddA 2 (Reg Hp),
    AGet Vals (Reg Hp),
    AAdd Env 1,
    APutA Env,
    AGetA Hp (Reg Env),
    AAddA 1 (Reg Hp),
    AGet Vals (Reg Hp),
    ASub Vals 1,
    AAdd Stk 1,
    APutA Stk,
    ASub Stk 1,
    AAddA 1 (Reg Env),
    AMov (Reg Env),
    AAdd Env 1,
    APutA Env,
    AGet Vals (Reg Env),
    ASub Vals 1]"

abbreviation assemble_extend_map :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "assemble_extend_map mp b lop x \<equiv> (if x < b then mp x else mp x + lop - 1)"

fun assembly_map :: "byte_code list \<Rightarrow> nat \<Rightarrow> nat" where
  "assembly_map [] x = 0"
| "assembly_map (op # cd) 0 = 0"
| "assembly_map (op # cd) (Suc x) = assemble_op_len op + assembly_map cd x"

definition assemble_code :: "byte_code list \<Rightarrow> assm list" where
  "assemble_code cd = concat (map (assemble_op (assembly_map cd)) cd)"

definition assemble_heap :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "assemble_heap hp mp h x = (if x < hp \<and> x mod 3 = 2 \<and> h (x - 2) = 0 then mp (h x) else h x)"

definition assemble_stack :: "nat \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "assemble_stack sp mp s x = (if x < sp \<and> even x then mp (s x) else s x)"

primrec assemble_state :: "(nat \<Rightarrow> nat) \<Rightarrow> unstr_state \<Rightarrow> assm_state" where
  "assemble_state mp (US h hp e ep vs vp sh sp pc) = 
    AS (case_register (assemble_heap hp mp h) e vs (assemble_stack sp mp sh)) 
      (case_register hp ep vp sp) 0 (Con 0) (mp pc)"

abbreviation assm_hp :: "nat \<Rightarrow> byte_code list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "assm_hp hp cd \<equiv> assemble_heap hp (assembly_map cd)"

abbreviation assm_stk :: "nat \<Rightarrow> byte_code list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "assm_stk sp cd \<equiv> assemble_stack sp (assembly_map cd)"

abbreviation assm_state :: "byte_code list \<Rightarrow> unstr_state \<Rightarrow> assm_state" where
  "assm_state cd \<equiv> assemble_state (assembly_map cd)"

lemma [simp]: "length (assemble_op mp op) = assemble_op_len op"
  by (induction op) simp_all

lemma [simp]: "length \<circ> assemble_op mp = assemble_op_len"
  by auto

lemma assemble_op_len_Succ: " 0 < assemble_op_len op"
  by (induction op) simp_all

lemma [simp]: "assemble_code [] \<tturnstile>\<^sub>a \<Sigma> = None"
  by (induction \<Sigma>) (simp_all add: assemble_code_def split: nat.splits)

theorem completea [simp]: "assemble_code cd\<^sub>b \<tturnstile>\<^sub>a assm_state cd\<^sub>b \<Sigma>\<^sub>u = Some \<Sigma>\<^sub>a' \<Longrightarrow> 
    \<exists>n \<Sigma>\<^sub>u'. iter_evala (assemble_code cd\<^sub>b) n \<Sigma>\<^sub>a' = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u') \<and> cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u'"
proof (induction \<Sigma>\<^sub>u)
  case (US h hp e ep vs vp sh sp pc)
  thus ?case by simp
qed

lemma [simp]: "assembly_map mp 0 = 0"
  by (induction mp) simp_all

lemma [simp]: "lookup cd pc = Some op \<Longrightarrow> 
  assembly_map cd (Suc pc) = assemble_op_len op + assembly_map cd pc"
proof (induction cd pc rule: assembly_map.induct)
  case (2 op' cd)
  thus ?case by (cases cd) simp_all
qed simp_all

lemma [simp]: "length (assemble_code cd) = list_sum (map assemble_op_len cd)"
  by (induction cd) (simp_all add: assemble_code_def)

lemma [simp]: "assembly_map cd (length cd) = length (assemble_code cd)"
  by (induction cd) (simp_all add: assemble_code_def)

lemma [simp]: "assm_hp hp cd nmem = nmem"
  by (auto simp add: assemble_heap_def)

lemma [simp]: "assm_stk 0 cd m = m"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "lookup (assemble_op mp op @ cd) (assemble_op_len op + x) = lookup cd x"
proof -
  have "lookup (assemble_op mp op @ cd) (length (assemble_op mp op) + x) = lookup cd x" 
    by (metis lookup_append)
  thus ?thesis by simp
qed

lemma assemble_code_lookup' [simp]: "lookup cd pc = Some op \<Longrightarrow> x < assemble_op_len op \<Longrightarrow> 
  lookup (concat (map (assemble_op (assembly_map (cd' @ cd))) cd)) (x + assembly_map cd pc) = 
    lookup (assemble_op (assembly_map (cd' @ cd)) op) x"
proof (induction cd pc arbitrary: cd' rule: assembly_map.induct)
  case (3 op' cd y)
  hence "lookup (concat (map (assemble_op (assembly_map ((cd' @ [op']) @ cd))) cd)) 
    (x + assembly_map cd y) = lookup (assemble_op (assembly_map ((cd' @ [op']) @ cd)) op) x" 
      by fastforce
  hence "lookup (assemble_op (assembly_map (cd' @ op' # cd)) op' @ 
    concat (map (assemble_op (assembly_map (cd' @ op' # cd))) cd))
      (assemble_op_len op' + (x + assembly_map cd y)) =
        lookup (assemble_op (assembly_map (cd' @ op' # cd)) op) x" by simp
  hence "lookup (assemble_op (assembly_map (cd' @ op' # cd)) op' @ 
    concat (map (assemble_op (assembly_map (cd' @ op' # cd))) cd))
      (x + (assemble_op_len op' + assembly_map cd y)) =
        lookup (assemble_op (assembly_map (cd' @ op' # cd)) op) x" by (metis add.assoc add.commute)
  thus ?case by simp
qed simp_all

lemma assemble_code_lookup [simp]: "lookup cd pc = Some op \<Longrightarrow> 
  x < assemble_op_len op \<Longrightarrow> lookup (assemble_code cd) (x + assembly_map cd pc) = 
    lookup (assemble_op (assembly_map cd) op) x"
  by (metis assemble_code_lookup' append_Nil assemble_code_def)

lemma [simp]: "lookup cd pc = Some op \<Longrightarrow> 1 < assemble_op_len op \<Longrightarrow> 
  lookup (assemble_code cd) (Suc (assembly_map cd pc)) = 
    lookup (assemble_op (assembly_map cd) op) 1"
  using assemble_code_lookup by fastforce

lemma [simp]: "lookup cd pc = Some op \<Longrightarrow> 0 < assemble_op_len op \<Longrightarrow> 
    lookup (assemble_code cd) (assembly_map cd pc) = lookup (assemble_op (assembly_map cd) op) 0"
  using assemble_code_lookup by fastforce

lemma [simp]: "m Hp = h \<Longrightarrow> m Env = e \<Longrightarrow> m Vals = vs \<Longrightarrow> m Stk = sh \<Longrightarrow> 
    m = case_register h e vs sh" 
  by rule (simp split: register.splits)

lemma assm_hp_lemma1: "3 dvd x \<Longrightarrow> assemble_heap hp mp h x = h x"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma2: "x mod 3 = 1 \<Longrightarrow> assemble_heap hp mp h x = h x"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma3: "x mod 3 = 2 \<Longrightarrow> h (x - 2) \<noteq> 0 \<Longrightarrow> assemble_heap hp mp h x = h x"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma4: "x mod 3 = 2 \<Longrightarrow> h (x - 2) = 0 \<Longrightarrow> x < hp \<Longrightarrow> 
    assemble_heap hp mp h x = mp (h x)"
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
  assm_hp (Suc (Suc (Suc hp))) cd (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x = 
    assm_hp hp cd h x"
proof (unfold assemble_heap_def, cases "x mod 3 = 2")
  case True
  assume "3 dvd hp" and "x \<noteq> hp" and "x \<noteq> Suc hp" and "x \<noteq> Suc (Suc hp)"
  moreover with True have "(h(hp := a, Suc hp := b, Suc (Suc hp) := c)) (x - 2) = h (x - 2)" 
    by (metis assemble_heap_update_lemma)
  ultimately show "(if x < Suc (Suc (Suc hp)) \<and> x mod 3 = 2 \<and> 
    (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) (x - 2) = 0
      then assembly_map cd ((h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x) 
        else (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x) =
          (if x < hp \<and> x mod 3 = 2 \<and> h (x - 2) = 0 then assembly_map cd (h x) else h x)" by simp
next
  case False
  assume "x \<noteq> hp" and "x \<noteq> Suc hp" and "x \<noteq> Suc (Suc hp)"
  hence "(x = hp \<longrightarrow> a = h hp) \<and> (x \<noteq> hp \<longrightarrow> (x = Suc hp \<longrightarrow> b = h (Suc hp)) \<and> 
    (x \<noteq> Suc hp \<longrightarrow> x = Suc (Suc hp) \<longrightarrow> c = h (Suc (Suc hp))))" by simp
  with False show "(if x < Suc (Suc (Suc hp)) \<and> x mod 3 = 2 \<and> 
    (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) (x - 2) = 0
      then assembly_map cd ((h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x) 
        else (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x) =
          (if x < hp \<and> x mod 3 = 2 \<and> h (x - 2) = 0 then assembly_map cd (h x) else h x)" by simp
qed

lemma [simp]: "restructurable_heap h hp ep (length cd) \<Longrightarrow> 
  (assm_hp hp cd h)(hp := Suc a, Suc hp := b, Suc (Suc hp) := c) = 
    assm_hp (Suc (Suc (Suc hp))) cd (h(hp := Suc a, Suc hp := b, Suc (Suc hp) := c))"
proof
  fix x
  assume "restructurable_heap h hp ep (length cd)"
  hence H: "3 dvd hp" by (simp add: restructurable_heap_def)
  moreover hence "Suc hp mod 3 = 1" by presburger
  moreover hence "Suc (Suc hp) mod 3 = 2" by presburger
  ultimately show "
    ((assm_hp hp cd h)(hp := Suc a, Suc hp := b, Suc (Suc hp) := c)) x =
      assm_hp (Suc (Suc (Suc hp))) cd (h(hp := Suc a, Suc hp := b, Suc (Suc hp) := c)) x" 
    by (simp add: assm_hp_lemma1 assm_hp_lemma2 assm_hp_lemma3)
qed

lemma [simp]: "restructurable_heap h hp ep (length cd) \<Longrightarrow> 
  (assm_hp hp cd h)(hp := 0, Suc hp := a, Suc (Suc hp) := assembly_map cd b) = 
    assm_hp (Suc (Suc (Suc hp))) cd (h(hp := 0, Suc hp := a, Suc (Suc hp) := b))"
proof
  fix x
  assume "restructurable_heap h hp ep (length cd)"
  hence H: "3 dvd hp" by (simp add: restructurable_heap_def)
  moreover hence "Suc hp mod 3 = 1" by presburger
  moreover hence "Suc (Suc hp) mod 3 = 2" by presburger
  ultimately show "((assm_hp hp cd h)(hp := 0, Suc hp := a, 
    Suc (Suc hp) := assembly_map cd b)) x =
      assm_hp (Suc (Suc (Suc hp))) cd (h(hp := 0, Suc hp := a, Suc (Suc hp) := b)) x" 
    by (simp add: assm_hp_lemma1 assm_hp_lemma2 assm_hp_lemma4)
qed

lemma [simp]: "restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> 
    assemble_heap hp mp h (Suc (vs vp)) = h (Suc (vs vp))"
proof (unfold assemble_heap_def restructurable_vals_def)
  assume "\<forall>x<Suc (Suc vp). 3 dvd vs x \<and> vs x < hp"
  hence "3 dvd vs vp" by simp
  hence "Suc (vs vp) mod 3 = 1" by presburger
  thus "(if Suc (vs vp) < hp \<and> Suc (vs vp) mod 3 = 2 \<and> h (Suc (vs vp) - 2) = 0 
         then mp (h (Suc (vs vp))) else h (Suc (vs vp))) = h (Suc (vs vp))" by simp
qed

lemma [simp]: "restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> h (vs vp) = 0 \<Longrightarrow> 
  restructurable_heap h hp ep lcd \<Longrightarrow>
    assemble_heap hp mp h (Suc (Suc (vs vp))) = mp (h (Suc (Suc (vs vp))))"
proof (unfold assemble_heap_def restructurable_vals_def)
  assume "\<forall>x<Suc (Suc vp). 3 dvd vs x \<and> vs x < hp"
  hence "3 dvd vs vp \<and> vs vp < hp" by simp
  moreover assume "restructurable_heap h hp ep lcd"
  moreover hence "3 dvd hp" by auto
  ultimately have "Suc (Suc (vs vp)) mod 3 = 2 \<and> Suc (Suc (vs vp)) < hp" by presburger
  moreover assume "h (vs vp) = 0"
  ultimately show "(if Suc (Suc (vs vp)) < hp \<and> Suc (Suc (vs vp)) mod 3 = 2 \<and> 
    h (Suc (Suc (vs vp)) - 2) = 0 then mp (h (Suc (Suc (vs vp)))) 
      else h (Suc (Suc (vs vp)))) = mp (h (Suc (Suc (vs vp))))" 
        by simp
qed

lemma [simp]: "h (vs vp) = Suc x \<Longrightarrow>
    assemble_heap hp mp h (Suc (Suc (vs vp))) = h (Suc (Suc (vs vp)))"
  by (simp add: assemble_heap_def)

lemma [simp]: "even sp \<Longrightarrow> assm_stk (Suc (Suc sp)) cd sh (Suc sp) = sh (Suc sp)"
  by (simp add: assemble_stack_def)

lemma [simp]: "even sp \<Longrightarrow> ((assm_stk sp cd sh)(sp := assembly_map cd pc, Suc sp := a)) = 
    (assm_stk (Suc (Suc sp)) cd (sh(sp := pc, Suc sp := a)))"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> 
  (assm_stk (Suc sp) cd sh)(Suc sp := assembly_map cd pc, Suc (Suc sp) := k) =
    (assm_stk (Suc (Suc (Suc sp))) cd (sh(Suc sp := pc, Suc (Suc sp) := k)))"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> 
    (assm_stk (Suc sp) cd sh)(sp := k) = assm_stk (Suc sp) cd (sh(sp := k))"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc (Suc sp)) \<Longrightarrow> 
    ((assm_stk (Suc (Suc sp)) cd sh)(sp := 0)) = assm_stk sp cd (sh(sp := 0))"
  by rule (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> assm_stk (Suc sp) cd sh sp = sh sp"
  by (simp add: assemble_stack_def)

lemma [simp]: "even (Suc (Suc sp)) \<Longrightarrow> assm_stk (Suc (Suc sp)) cd sh sp = assembly_map cd (sh sp)"
  by (simp add: assemble_stack_def)

lemma [simp]: "assm_stk 2 cd (sh(0 := 0, Suc 0 := 0)) = (sh(0 := 0, Suc 0 := 0))"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "Suc x \<le> y \<Longrightarrow> lookup (concat (replicate y [a, b])) (2 * x) = Some a"
proof (induction y arbitrary: x)
  case (Suc y)
  thus ?case by (induction x) simp_all
qed simp_all

lemma [simp]: "Suc x \<le> y \<Longrightarrow> lookup (concat (replicate y [a, b])) (Suc (2 * x)) = Some b"
proof (induction y arbitrary: x)
  case (Suc y)
  thus ?case by (induction x) simp_all
qed simp_all

lemma [simp]: "lookup (concat (replicate x [a, b]) @ bs) (2 * x) = lookup bs 0"
  by (induction x) simp_all

lemma [simp]: "lookup (concat (replicate x [a, b]) @ bs) (Suc (2 * x)) = lookup bs 1"
  by (induction x) simp_all

lemma [simp]: "lookup (concat (replicate x [a, b]) @ bs) (Suc (Suc (2 * x))) = lookup bs (Suc 1)"
  by (induction x) simp_all

lemma [simp]: "unstr_lookup e a x = Some v \<Longrightarrow> lookup cd pc = Some (BLookup y) \<Longrightarrow> x \<le> y \<Longrightarrow> 
  pc < length cd \<Longrightarrow> iter_evala (assemble_code cd) (5 + 2 * x) 
    (AS (case_register h e vs sh) (case_register hp ep vp sp) a (Reg Env)
      (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h e (vs(vp := v)) sh)  
        (case_register hp ep (Suc vp) sp) 0 (Con 0) (assembly_map cd pc))"
proof (induction e a x rule: unstr_lookup.induct)
  case (3 e p)
  moreover from 3 have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (ASubA 2 (Reg Env))" by simp
  moreover from 3 have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AGetA Env (Reg Vals))" by simp
  moreover from 3 have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (APutA Vals)" by (simp del: add_2_eq_Suc) (simp add: numeral_def)
  ultimately show ?case by (simp add: numeral_def)
next
  case (4 e p x)
  hence "lookup (assemble_code cd) (6 + 2 * x + assembly_map cd pc) = 
    Some (ASubA (Suc 0) (Reg Env))" by simp
  moreover from 4 have "lookup (assemble_code cd) (5 + 2 * x + assembly_map cd pc) = 
    Some (AGetA Env (Reg Env))" by simp
  ultimately have "iter_evala (assemble_code cd) 2
    (AS (case_register h e vs sh) (case_register hp ep vp sp) (Suc (Suc p)) (Reg Env)
      (7 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h e vs sh) 
        (case_register hp ep vp sp) (e (Suc p)) (Reg Env) (5 + 2 * x + assembly_map cd pc))" 
    by (simp add: numeral_def)
  moreover from 4 have "iter_evala (assemble_code cd) (5 + 2 * x) 
    (AS (case_register h e vs sh) (case_register hp ep vp sp) (e (Suc p)) (Reg Env)
      (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h e (vs(vp := v)) sh) 
        (case_register hp ep (Suc vp) sp) 0 (Con 0) (assembly_map cd pc))" by simp 
  ultimately have "iter_evala (assemble_code cd) (2 + (5 + 2 * x))
    (AS (case_register h e vs sh) (case_register hp ep vp sp) (Suc (Suc p)) (Reg Env)
      (7 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h e (vs(vp := v)) sh)
        (case_register hp ep (Suc vp) sp) 0 (Con 0) (assembly_map cd pc))" 
    using iter_evala_combine by blast
  thus ?case by simp
qed simp_all

theorem correcta [simp]: "cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow> 
  \<exists>n. iter_evala (assemble_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u')"
proof (induction cd\<^sub>b \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct)
  case (evu_lookup cd pc x e sh sp y h hp ep vs vp)
  moreover hence "odd sp" by simp
  moreover from evu_lookup have "lookup (assemble_code cd) (7 + 2 * x + assembly_map cd pc) = 
    Some (AMov (Reg Stk))" by simp
  moreover from evu_lookup have "lookup (assemble_code cd) (6 + 2 * x + assembly_map cd pc) = 
    Some (ASubA 1 (Reg Stk))" by simp
  moreover from evu_lookup have "lookup (assemble_code cd) (5 + 2 * x + assembly_map cd pc) = 
    Some (AGetA Stk (Reg Env))" by simp
  ultimately have "iter_evala (assemble_code cd) 3 
    (AS (case_register (assm_hp hp cd h) e vs (assm_stk (Suc sp) cd sh)) 
      (case_register hp ep vp (Suc sp)) 0 (Con 0) (8 + 2 * x + assembly_map cd pc)) = 
        Some (AS (case_register (assm_hp hp cd h) e vs (assm_stk (Suc sp) cd sh)) 
          (case_register hp ep vp (Suc sp)) (sh sp) (Reg Env) (5 + 2 * x + assembly_map cd pc))" 
    by (simp add: numeral_def)
  moreover from evu_lookup have "iter_evala (assemble_code cd) (5 + 2 * x) 
    (AS (case_register (assm_hp hp cd h) e vs (assm_stk (Suc sp) cd sh)) 
      (case_register hp ep vp (Suc sp)) (sh sp) (Reg Env) (5 + 2 * x + assembly_map cd pc)) = 
        Some (AS (case_register (assm_hp hp cd h) e (vs(vp := y)) (assm_stk (Suc sp) cd sh)) 
          (case_register hp ep (Suc vp) (Suc sp)) 0 (Con 0) (assembly_map cd pc))" by simp
  ultimately have "iter_evala (assemble_code cd) (3 + (5 + 2 * x)) 
    (AS (case_register (assm_hp hp cd h) e vs (assm_stk (Suc sp) cd sh)) 
      (case_register hp ep vp (Suc sp)) 0 (Con 0) (8 + 2 * x + assembly_map cd pc)) = 
        Some (AS (case_register (assm_hp hp cd h) e (vs(vp := y)) (assm_stk (Suc sp) cd sh)) 
          (case_register hp ep (Suc vp) (Suc sp)) 0 (Con 0) (assembly_map cd pc))" 
    using iter_evala_combine by blast
  with evu_lookup show ?case by auto
next
  case (evu_pushcon cd pc k h hp e ep vs vp sh sp)
  moreover from evu_pushcon have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (APut Vals (Reg Hp))" by simp
  moreover from evu_pushcon have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (AAdd Vals 1)" by simp
  moreover from evu_pushcon have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (APut Hp (Con 1))" by simp 
  moreover from evu_pushcon have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AAdd Hp 1)" by simp 
  moreover from evu_pushcon have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (APut Hp (Con k))" by simp 
  moreover from evu_pushcon have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAdd Hp 1)" by (simp del: add_2_eq_Suc) (simp add: numeral_def)
  ultimately have "iter_evala (assemble_code cd) 8 (AS (case_register (assm_hp hp cd h) e vs 
    (assm_stk (Suc sp) cd sh)) (case_register hp ep vp (Suc sp)) 0 (Con 0)
      (assembly_map cd (Suc pc))) = Some (AS (case_register (assm_hp (3 + hp) cd (h(hp := 1,
        Suc hp := k, Suc (Suc hp) := 0))) e (vs(vp := hp)) (assm_stk (Suc sp) cd sh)) 
          (case_register (3 + hp) ep (Suc vp) (Suc sp)) 0 (Con 0) (assembly_map cd pc))" 
    by (auto simp add: numeral_def)
  thus ?case by auto
next
  case (evu_pushlam cd pc pc' h hp e ep vs vp sh sp)
  moreover from evu_pushlam have "lookup (assemble_code cd) (11 + assembly_map cd pc) = 
    Some (APut Vals (Reg Hp))" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (10 + assembly_map cd pc) = 
    Some (AAdd Vals 1)" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (AMov (Reg Stk))" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (ASubA 1 (Reg Stk))" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AGetA Stk (Reg Hp))" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (APut Hp (Con 0))" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd Hp 1)" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (4 + assembly_map cd pc) =
    Some (APutA Hp)" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AAdd Hp 1)" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AMov (Con 0))" by (simp del: add_2_eq_Suc) (simp add: numeral_def)
  ultimately have "iter_evala (assemble_code cd) 12 (AS (case_register (assm_hp hp cd h) e vs 
    (assm_stk (Suc sp) cd sh)) (case_register hp ep vp (Suc sp)) 0 (Con 0)
      (assembly_map cd (Suc pc))) = Some (AS (case_register (assm_hp (3 + hp) cd (h(hp := 0, 
        Suc hp := sh sp, Suc (Suc hp) := pc'))) e (vs(vp := hp)) (assm_stk (Suc sp) cd sh)) 
        (case_register (3 + hp) ep (Suc vp) (Suc sp)) 0 (Con 0) (assembly_map cd pc))" 
    by (auto simp add: numeral_def)
  thus ?case by auto
next
  case (evu_apply cd pc h vs vp hp e ep sh sp)
  moreover from evu_apply have "lookup (assemble_code cd) (21 + assembly_map cd pc) = 
    Some (ASub Vals 1)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (20 + assembly_map cd pc) = 
    Some (AGet Vals (Reg Env))" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (19 + assembly_map cd pc) = 
    Some (APutA Env)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (18 + assembly_map cd pc) = 
    Some (AAdd Env 1)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (17 + assembly_map cd pc) = 
    Some (AMov PC)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (16 + assembly_map cd pc) = 
    Some (ASubA 17 PC)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (15 + assembly_map cd pc) = 
    Some (APutA Stk)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (14 + assembly_map cd pc) = 
    Some (AAdd Stk 1)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (13 + assembly_map cd pc) = 
    Some (AMov (Reg Env))" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (12 + assembly_map cd pc) = 
    Some (AAddA 1 (Reg Env))" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (11 + assembly_map cd pc) = 
    Some (APutA Stk)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (10 + assembly_map cd pc) = 
    Some (AAdd Stk 1)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (ASub Vals 1)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (AGet Vals (Reg Hp))" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AAddA 1 (Reg Hp))" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (AGetA Hp (Reg Env))" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (APutA Env)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AAdd Env 1)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AGet Vals (Reg Hp))" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAddA 2 (Reg Hp))" by (simp del: add_2_eq_Suc) (simp add: numeral_def)
  ultimately have "iter_evala (assemble_code cd) 22 (AS (case_register (assm_hp hp cd h) e vs 
    (assm_stk (Suc sp) cd sh)) (case_register hp ep (Suc (Suc vp)) (Suc sp)) 0 (Con 0)
      (assembly_map cd (Suc pc))) = Some (AS (case_register (assm_hp hp cd h) 
        (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) vs (assm_stk (Suc (Suc (Suc sp))) cd 
          (sh(Suc sp := pc, Suc (Suc sp) := Suc (Suc ep))))) (case_register hp 
            (Suc (Suc ep)) vp (Suc (Suc (Suc sp)))) 0 (Con 0) 
              (assembly_map cd (h (Suc (Suc (vs vp))))))"
    by (auto simp add: numeral_def)
  thus ?case by auto
next
  case (evu_return cd pc h hp e ep vs vp sh sp)
  moreover from evu_return have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (ASub Stk 2)" by simp
  moreover from evu_return have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AGet Stk PC)" by (simp del: add_2_eq_Suc) (simp add: numeral_def)
  ultimately have "iter_evala (assemble_code cd) 4 (AS (case_register (assm_hp hp cd h) e vs 
    (assm_stk (Suc (Suc sp)) cd sh)) (case_register hp ep vp (Suc (Suc sp))) 0 (Con 0)
      (assembly_map cd (Suc pc))) = Some (AS (case_register (assm_hp hp cd h) e vs 
        (assm_stk sp cd (sh(sp := 0)))) (case_register hp ep vp sp) 0 (Con 0)
          (assembly_map cd (sh sp)))"
    by (simp add: numeral_def)
  thus ?case by auto
next
  case (evu_jump cd pc h vs vp hp e ep sh sp)
  moreover from evu_jump have "lookup (assemble_code cd) (18 + assembly_map cd pc) = 
    Some (ASub Vals 1)" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (17 + assembly_map cd pc) = 
    Some (AGet Vals (Reg Env))" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (16 + assembly_map cd pc) = 
    Some (APutA Env)" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (15 + assembly_map cd pc) = 
    Some (AAdd Env 1)" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (14 + assembly_map cd pc) = 
    Some (AMov (Reg Env))" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (13 + assembly_map cd pc) = 
    Some (AAddA 1 (Reg Env))" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (12 + assembly_map cd pc) = 
    Some (ASub Stk 1)" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (11 + assembly_map cd pc) = 
    Some (APutA Stk)" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (10 + assembly_map cd pc) =
    Some (AAdd Stk 1)" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (ASub Vals 1)" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (AGet Vals (Reg Hp))" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AAddA 1 (Reg Hp))" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (AGetA Hp (Reg Env))" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (APutA Env)" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AAdd Env 1)" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AGet Vals (Reg Hp))" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAddA 2 (Reg Hp))" by (simp del: add_2_eq_Suc) (simp add: numeral_def)
  ultimately have "iter_evala (assemble_code cd) 19 (AS (case_register (assm_hp hp cd h) e vs 
    (assm_stk (Suc sp) cd sh)) (case_register hp ep (Suc (Suc vp)) (Suc sp)) 0 (Con 0)
      (assembly_map cd (Suc pc))) = Some (AS (case_register (assm_hp hp cd h) 
        (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) vs (assm_stk (Suc sp) cd 
          (sh(sp := Suc (Suc ep))))) (case_register hp (Suc (Suc ep)) vp (Suc sp)) 0 (Con 0) 
            (assembly_map cd (h (Suc (Suc (vs vp))))))" 
    by (auto simp add: numeral_def)
  thus ?case by auto
qed

lemma [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow> 
  \<exists>n. iter_evala (assemble_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u')"
proof (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct)
  case (iter_refl \<Sigma>\<^sub>u)
  have "iter_evala (assemble_code cd\<^sub>b) 0 (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u)" 
    by simp
  thus ?case by blast
next
  case (iter_step \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Sigma>\<^sub>u'')
  then obtain n where "iter_evala (assemble_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = 
    Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u')" by fastforce
  moreover from iter_step obtain m where "
    iter_evala (assemble_code cd\<^sub>b) m (assm_state cd\<^sub>b \<Sigma>\<^sub>u') = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u'')" 
      by fastforce
  ultimately have "iter_evala (assemble_code cd\<^sub>b) (n + m) (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = 
    Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u'')" by simp
  thus ?case by blast
qed

theorem correcta_iter [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow> 
  iter (\<tturnstile> assemble_code cd\<^sub>b \<leadsto>\<^sub>a) (assm_state cd\<^sub>b \<Sigma>\<^sub>u) (assm_state cd\<^sub>b \<Sigma>\<^sub>u')"
proof -
  assume "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u'" and "restructurable \<Sigma>\<^sub>u cd\<^sub>b"
  hence "\<exists>n. iter_evala (assemble_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u')" 
    by simp
  thus "iter (\<tturnstile> assemble_code cd\<^sub>b \<leadsto>\<^sub>a) (assm_state cd\<^sub>b \<Sigma>\<^sub>u) (assm_state cd\<^sub>b \<Sigma>\<^sub>u')" 
    by (simp add: iter_evala_equiv)
qed

end