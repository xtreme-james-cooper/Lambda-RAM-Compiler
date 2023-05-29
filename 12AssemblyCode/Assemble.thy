theory Assemble
  imports AssemblyCode "../11UnstructuredState/UnstructuredState" "../00Utils/Utils"
begin

primrec assemble_op_len :: "code\<^sub>b \<Rightarrow> nat" where
  "assemble_op_len (Lookup\<^sub>b x) = 7 + 2 * x"
| "assemble_op_len (PushCon\<^sub>b k) = 7"
| "assemble_op_len (PushLam\<^sub>b pc) = 11"
| "assemble_op_len Apply\<^sub>b = 23"
| "assemble_op_len Return\<^sub>b = 5"
| "assemble_op_len Jump\<^sub>b = 20"

primrec assemble_op :: "(nat \<Rightarrow> nat) \<Rightarrow> code\<^sub>b \<Rightarrow> assm list" where
  "assemble_op mp (Lookup\<^sub>b x) = [
    AMov (Con 0),
    AAdd (Reg Vals) 1,
    APut Vals (Acc (Con 0)),
    AGet (Acc (Reg Env)) (Reg Hp),
    ASub (Acc (Reg Env)) 2] @
    concat (replicate x [
    AGet (Acc (Reg Env)) (Reg Env),
    ASub (Acc (Reg Env)) 1]) @ [
    AGet (Acc (Reg Stk)) (Reg Env),
    ASub (Acc (Reg Stk)) 1,
    AMov (Reg Stk)]"
| "assemble_op mp (PushCon\<^sub>b k) = [
    AAdd (Reg Hp) 1, 
    APut Hp (Acc (Con 0)),
    AAdd (Reg Hp) 1,  
    APut Hp (Con k),
    AAdd (Reg Hp) 1,  
    APut Hp (Con 1), 
    AAdd (Reg Vals) 1,
    APut Vals (Reg Hp)]"
| "assemble_op mp (PushLam\<^sub>b pc) = [
    AAdd (Reg Hp) 1, 
    APut Hp (PC (mp pc)), 
    AMov (Con 0),
    AAdd (Reg Hp) 1, 
    APut Hp (Acc (Con 0)),
    AAdd (Reg Hp) 1, 
    APut Hp (Con 0),
    AGet (Acc (Reg Stk)) (Reg Env), 
    ASub (Acc (Reg Stk)) 1,
    AMov (Reg Stk),
    AAdd (Reg Vals) 1,
    APut Vals (Reg Hp)]"
| "assemble_op mp Apply\<^sub>b = [
    AJmp,
    AGet (Acc (Reg Hp)) (PC 0),
    AAdd (Acc (Reg Hp)) 2,
    APut Vals (Con 0),
    AGet (Reg Vals) (Reg Hp),
    AAdd (Reg Env) 1,
    APut Env (Acc (Con 0)),
    AGet (Acc (Reg Hp)) (Reg Env),
    AAdd (Acc (Reg Hp)) 1,
    AGet (Reg Vals) (Reg Hp),
    ASub (Reg Vals) 1,
    AAdd (Reg Stk) 1,
    APut Stk (Acc (Con 0)),
    AAdd (Acc (Reg Env)) 1,
    AMov (Reg Env),
    AAdd (Reg Stk) 1,
    APut Stk (Acc (Con 0)),
    ASub (Acc (PC 0)) 18,
    AMov (PC 0),
    AAdd (Reg Env) 1,
    APut Env (Acc (Con 0)),
    APut Vals (Con 0),
    AGet (Reg Vals) (Reg Hp),
    ASub (Reg Vals) 1]"
| "assemble_op mp Return\<^sub>b = [
    AJmp,
    APut Stk (Con 0),
    AGet (Reg Stk) (PC 0),
    ASub (Reg Stk) 1,
    APut Stk (Con 0),
    ASub (Reg Stk) 1]"
| "assemble_op mp Jump\<^sub>b = [
    AJmp,
    AGet (Acc (Reg Hp)) (PC 0),
    AAdd (Acc (Reg Hp)) 2,
    APut Vals (Con 0),
    AGet (Reg Vals) (Reg Hp),
    AAdd (Reg Env) 1,
    APut Env (Acc (Con 0)),
    AGet (Acc (Reg Hp)) (Reg Env),
    AAdd (Acc (Reg Hp)) 1,
    AGet (Reg Vals) (Reg Hp),
    ASub (Reg Vals) 1,
    AAdd (Reg Stk) 1,
    APut Stk (Acc (Con 0)),
    ASub (Reg Stk) 1,
    AAdd (Acc (Reg Env)) 1,
    AMov (Reg Env),
    AAdd (Reg Env) 1,
    APut Env (Acc (Con 0)),
    APut Vals (Con 0),
    AGet (Reg Vals) (Reg Hp),
    ASub (Reg Vals) 1]"

fun assembly_map :: "code\<^sub>b list \<Rightarrow> nat \<Rightarrow> nat" where
  "assembly_map [] x = 0"
| "assembly_map (op # cd) 0 = 0"
| "assembly_map (op # cd) (Suc x) = Suc (assemble_op_len op + assembly_map cd x)"

definition assemble_code :: "code\<^sub>b list \<Rightarrow> assm list" where
  "assemble_code cd = concat (map (assemble_op (assembly_map cd)) cd)"

definition assemble_heap :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat" where
  "assemble_heap mp h hp x = (if x \<ge> hp then (Con 0, 0) else case x mod 3 of
      0 \<Rightarrow> (Con 0, h x)
    | Suc 0 \<Rightarrow> (if h (x - 1) = 0 then Reg Env else Con 0, h x)
    | Suc (Suc 0) \<Rightarrow> if h (x - 2) = 0 then (PC 0, mp (h x)) else (Con 0, h x))"

definition assemble_env :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat" where
  "assemble_env e ep x = (if x \<ge> ep then (Con 0, 0) else (Reg (if even x then Hp else Env), e x))"

definition assemble_vals :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat" where
  "assemble_vals vs vp x = (if x \<ge> vp then (Con 0, 0) else (Reg Hp, vs x))"

definition assemble_stack :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat" where
  "assemble_stack mp s sp x = (
    if x \<ge> sp then (Con 0, 0) else if even x then (PC 0, mp (s x)) else (Reg Env, s x))"

primrec assemble_state :: "(nat \<Rightarrow> nat) \<Rightarrow> unstr_state \<Rightarrow> assm_state" where
  "assemble_state mp (S\<^sub>u h hp e ep vs vp sh sp pc) = 
    AS (case_register (assemble_heap mp h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assemble_stack mp sh sp)) (case_register hp ep vp sp) 0 (Con 0) (mp pc)"

abbreviation assm_hp :: "code\<^sub>b list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat" where
  "assm_hp cd \<equiv> assemble_heap (assembly_map cd)"

abbreviation assm_stk :: "code\<^sub>b list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat" where
  "assm_stk cd \<equiv> assemble_stack (assembly_map cd)"

abbreviation assm_state :: "code\<^sub>b list \<Rightarrow> unstr_state \<Rightarrow> assm_state" where
  "assm_state cd \<equiv> assemble_state (assembly_map cd)"

lemma length_assemble_op [simp]: "length (assemble_op mp op) = Suc (assemble_op_len op)"
  by (induction op) simp_all

lemma [simp]: "length \<circ> assemble_op mp = Suc \<circ> assemble_op_len"
  by auto

lemma [simp]: "assemble_code [] \<tturnstile>\<^sub>a \<Sigma> = None"
  by (induction \<Sigma>) (simp_all add: assemble_code_def split: nat.splits)

lemma [simp]: "assembly_map cd 0 = 0"
  by (induction cd) simp_all

lemma assembly_map_postpend [simp]: "
    assembly_map (cd @ cd') (length cd) = assembly_map cd (length cd)"
  by (induction cd) simp_all

lemma assm_map_to_suc' [simp]: "assembly_map cd\<^sub>b pc\<^sub>b = Suc pc\<^sub>a \<Longrightarrow> pc\<^sub>b \<le> length cd\<^sub>b \<Longrightarrow> 
  \<exists>pc\<^sub>b' op\<^sub>b cd\<^sub>a' cd\<^sub>a''. pc\<^sub>b = Suc pc\<^sub>b' \<and> lookup cd\<^sub>b pc\<^sub>b' = Some op\<^sub>b \<and> 
    pc\<^sub>a = length cd\<^sub>a' + assemble_op_len op\<^sub>b \<and> 
      concat (map (assemble_op (assembly_map (cd\<^sub>b' @ cd\<^sub>b))) cd\<^sub>b) = 
        cd\<^sub>a' @ assemble_op (assembly_map (cd\<^sub>b' @ cd\<^sub>b)) op\<^sub>b @ cd\<^sub>a''"
proof (induction cd\<^sub>b pc\<^sub>b arbitrary: pc\<^sub>a cd\<^sub>b' rule: assembly_map.induct)
  case (3 op\<^sub>b cd\<^sub>b pc\<^sub>b)
  thus ?case
  proof (induction pc\<^sub>b)
    case (Suc pc\<^sub>b)
    then obtain op\<^sub>b' cd\<^sub>b'' where C: "cd\<^sub>b = op\<^sub>b' # cd\<^sub>b''" by (cases cd\<^sub>b) simp_all
    hence A: "assembly_map cd\<^sub>b (Suc pc\<^sub>b) = Suc (assemble_op_len op\<^sub>b' + assembly_map cd\<^sub>b'' pc\<^sub>b)"
      by simp
    from Suc have "Suc pc\<^sub>b \<le> length cd\<^sub>b" by simp
    with Suc(2) A obtain op\<^sub>b'' cd\<^sub>a' cd\<^sub>a'' where O: "lookup cd\<^sub>b pc\<^sub>b = Some op\<^sub>b'' \<and>
      assemble_op_len op\<^sub>b' + assembly_map cd\<^sub>b'' pc\<^sub>b = length cd\<^sub>a' + assemble_op_len op\<^sub>b'' \<and>
        concat (map (assemble_op (assembly_map ((cd\<^sub>b' @ [op\<^sub>b]) @ cd\<^sub>b))) cd\<^sub>b) =
          cd\<^sub>a' @ assemble_op (assembly_map ((cd\<^sub>b' @ [op\<^sub>b]) @ cd\<^sub>b)) op\<^sub>b'' @ cd\<^sub>a''" by blast
    hence X: "lookup (op\<^sub>b # cd\<^sub>b) (Suc pc\<^sub>b) = Some op\<^sub>b''" by simp
    let ?mp = "assembly_map (cd\<^sub>b' @ op\<^sub>b # cd\<^sub>b)"
    from Suc have "pc\<^sub>a = assemble_op_len op\<^sub>b + assembly_map cd\<^sub>b (Suc pc\<^sub>b)" by simp
    with C O have Y: "pc\<^sub>a = length (assemble_op ?mp op\<^sub>b @ cd\<^sub>a') + assemble_op_len op\<^sub>b''" by simp
    from O have "concat (map (assemble_op ?mp) (op\<^sub>b # cd\<^sub>b)) = 
      (assemble_op ?mp op\<^sub>b @ cd\<^sub>a') @ assemble_op ?mp op\<^sub>b'' @ cd\<^sub>a''" by simp
    with X Y show ?case by blast
  qed simp_all
qed simp_all

lemma assm_map_to_suc [simp]: "assembly_map cd\<^sub>b pc\<^sub>b = Suc pc\<^sub>a \<Longrightarrow> pc\<^sub>b \<le> length cd\<^sub>b \<Longrightarrow> 
  \<exists>pc\<^sub>b' op\<^sub>b cd\<^sub>a' cd\<^sub>a''. pc\<^sub>b = Suc pc\<^sub>b' \<and> lookup cd\<^sub>b pc\<^sub>b' = Some op\<^sub>b \<and> 
    pc\<^sub>a = length cd\<^sub>a' + assemble_op_len op\<^sub>b \<and>
      assemble_code cd\<^sub>b = cd\<^sub>a' @ assemble_op (assembly_map cd\<^sub>b) op\<^sub>b @ cd\<^sub>a''"
proof (unfold assemble_code_def)
  assume "assembly_map cd\<^sub>b pc\<^sub>b = Suc pc\<^sub>a" and "pc\<^sub>b \<le> length cd\<^sub>b"
  hence "\<exists>pc\<^sub>b' op\<^sub>b cd\<^sub>a' cd\<^sub>a''. pc\<^sub>b = Suc pc\<^sub>b' \<and> lookup cd\<^sub>b pc\<^sub>b' = Some op\<^sub>b \<and> 
    pc\<^sub>a = length cd\<^sub>a' + assemble_op_len op\<^sub>b \<and> 
      concat (map (assemble_op (assembly_map ([] @ cd\<^sub>b))) cd\<^sub>b) = 
        cd\<^sub>a' @ assemble_op (assembly_map ([] @ cd\<^sub>b)) op\<^sub>b @ cd\<^sub>a''" by (metis assm_map_to_suc')
  thus "\<exists>pc\<^sub>b' op\<^sub>b cd\<^sub>a' cd\<^sub>a''. pc\<^sub>b = Suc pc\<^sub>b' \<and> lookup cd\<^sub>b pc\<^sub>b' = Some op\<^sub>b \<and> 
    pc\<^sub>a = length cd\<^sub>a' + assemble_op_len op\<^sub>b \<and> concat (map (assemble_op (assembly_map cd\<^sub>b)) cd\<^sub>b) = 
      cd\<^sub>a' @ assemble_op (assembly_map cd\<^sub>b) op\<^sub>b @ cd\<^sub>a''" by simp
qed

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

lemma [simp]: "lookup (assemble_op mp op @ cd) (assemble_op_len op) = 
    Some (last (assemble_op mp op))"
  by (induction op) simp_all

lemma [simp]: "lookup cd pc = Some op \<Longrightarrow> 
  assembly_map cd (Suc pc) = Suc (assemble_op_len op + assembly_map cd pc)"
proof (induction cd pc rule: assembly_map.induct)
  case (2 op' cd)
  thus ?case by (cases cd) simp_all
qed simp_all

lemma length_assemble_code [simp]: "length (assemble_code cd) = 
    sum_list (map (Suc \<circ> assemble_op_len) cd)"
  by (induction cd) (simp_all add: assemble_code_def)

lemma assembly_map_entry_point [simp]: "assembly_map cd (length cd) = length (assemble_code cd)"
  by (induction cd) (simp_all add: assemble_code_def)

lemma [simp]: "lookup (assemble_op mp op @ cd) (Suc (assemble_op_len op + x)) = lookup cd x"
proof -
  have "lookup (assemble_op mp op @ cd) (length (assemble_op mp op) + x) = lookup cd x" 
    by (metis lookup_append_snd)
  thus ?thesis by simp
qed

lemma assemble_code_lookup' [simp]: "lookup cd pc = Some op \<Longrightarrow> x \<le> assemble_op_len op \<Longrightarrow> 
  lookup (concat (map (assemble_op (assembly_map (cd' @ cd))) cd)) (x + assembly_map cd pc) = 
    lookup (assemble_op (assembly_map (cd' @ cd)) op) x"
proof (induction cd pc arbitrary: cd' rule: assembly_map.induct)
  case (3 op' cd y)
  hence "lookup (concat (map (assemble_op (assembly_map ((cd' @ [op']) @ cd))) cd)) 
    (x + assembly_map cd y) = lookup (assemble_op (assembly_map ((cd' @ [op']) @ cd)) op) x" 
      by fastforce
  hence "lookup (assemble_op (assembly_map (cd' @ op' # cd)) op' @ 
    concat (map (assemble_op (assembly_map (cd' @ op' # cd))) cd))
      (Suc (assemble_op_len op' + (x + assembly_map cd y))) =
        lookup (assemble_op (assembly_map (cd' @ op' # cd)) op) x" by simp
  hence "lookup (assemble_op (assembly_map (cd' @ op' # cd)) op' @ 
    concat (map (assemble_op (assembly_map (cd' @ op' # cd))) cd))
      (Suc (x + (assemble_op_len op' + assembly_map cd y))) =
        lookup (assemble_op (assembly_map (cd' @ op' # cd)) op) x" by (metis add.assoc add.commute)
  thus ?case by simp
qed simp_all

lemma assemble_code_lookup [simp]: "lookup cd pc = Some op \<Longrightarrow> 
  x \<le> assemble_op_len op \<Longrightarrow> lookup (assemble_code cd) (x + assembly_map cd pc) = 
    lookup (assemble_op (assembly_map cd) op) x"
  by (metis assemble_code_lookup' append_Nil assemble_code_def)

lemma [simp]: "lookup cd pc = Some op \<Longrightarrow> 1 \<le> assemble_op_len op \<Longrightarrow> 
  lookup (assemble_code cd) (Suc (assembly_map cd pc)) = 
    lookup (assemble_op (assembly_map cd) op) 1"
  using assemble_code_lookup by fastforce

lemma [simp]: "lookup cd pc = Some op \<Longrightarrow> 
    lookup (assemble_code cd) (assembly_map cd pc) = lookup (assemble_op (assembly_map cd) op) 0"
  using assemble_code_lookup by fastforce

lemma [simp]: "m Hp = h \<Longrightarrow> m Env = e \<Longrightarrow> m Vals = vs \<Longrightarrow> m Stk = sh \<Longrightarrow> 
    m = case_register h e vs sh" 
  by rule (simp split: register.splits)

lemma assm_hp_lemma1: "3 dvd x \<Longrightarrow> x < hp \<Longrightarrow> assemble_heap mp h hp x = (Con 0, h x)"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma2: "x mod 3 = 1 \<Longrightarrow> h (x - 1) \<noteq> 0 \<Longrightarrow> x < hp \<Longrightarrow> 
    assemble_heap mp h hp x = (Con 0, h x)"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma3: "x mod 3 = 1 \<Longrightarrow> h (x - 1) = 0 \<Longrightarrow> x < hp \<Longrightarrow>
    assemble_heap mp h hp x = (Reg Env, h x)"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma4: "x mod 3 = 2 \<Longrightarrow> h (x - 2) \<noteq> 0 \<Longrightarrow> x < hp \<Longrightarrow> 
    assemble_heap mp h hp x = (Con 0, h x)"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma5: "x mod 3 = 2 \<Longrightarrow> h (x - 2) = 0 \<Longrightarrow> x < hp \<Longrightarrow> 
    assemble_heap mp h hp x = (PC 0, mp (h x))"
  by (simp add: assemble_heap_def)

lemma [simp]: "x \<noteq> hp \<Longrightarrow> assm_hp cd (h(hp := a)) (Suc hp) x = assm_hp cd h hp x"
  by (induction x rule: x_mod_3_induct) (simp_all add: assemble_heap_def, linarith+)

lemma assemble_heap_update_lemma2 [simp]: "3 dvd hp \<Longrightarrow> x \<noteq> hp \<Longrightarrow> x \<noteq> Suc hp \<Longrightarrow> 
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
  assm_hp cd (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) hp x = assm_hp cd h hp x"
proof (cases "x mod 3")
  case (Suc m) note S = Suc
  assume A: "3 dvd hp" and B: "x \<noteq> hp" and C: "x \<noteq> Suc hp" and D: "x \<noteq> Suc (Suc hp)"
  thus ?thesis 
  proof (cases m)
    case 0
    from Suc C have X1: "x - 1 \<noteq> hp" by simp
    from Suc D have X2: "x - 1 \<noteq> Suc hp" by simp
    from Suc A 0 have X3: "x - 1 \<noteq> Suc (Suc hp)" by presburger
    from B C D X1 X2 X3 have "(if (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) (x - 1) = 0 
      then Reg Env else Con 0, (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x) =
        (if h (x - 1) = 0 then Reg Env else Con 0, h x)" 
      by simp
    with Suc 0 show ?thesis by (simp add: assemble_heap_def)
  next
    case (Suc m')
    with S have M: "x mod 3 = Suc (Suc 0)" by simp
    from D M have X1: "x - 2 \<noteq> hp" by simp
    from A M have X2: "x - 2 \<noteq> Suc hp" by presburger
    from A M have X3: "x - 2 \<noteq> Suc (Suc hp)" by presburger
    from B C D X1 X2 X3 have "(if (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) (x - 2) = 0
         then (PC 0, assembly_map cd ((h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x))
         else (Con 0, (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x)) =
    (if h (x - 2) = 0 then (PC 0, assembly_map cd (h x)) else (Con 0, h x))" by simp
    with M show ?thesis by (simp add: assemble_heap_def)
  qed
qed (simp_all add: assemble_heap_def)

lemma [simp]: "restructurable_heap h hp ep (length cd) \<Longrightarrow> (assm_hp cd h hp)
  (hp := (Con 0, Suc a), Suc hp := (Con 0, b), Suc (Suc hp) := (Con 0, c)) = 
    assm_hp cd (h(hp := Suc a, Suc hp := b, Suc (Suc hp) := c)) (Suc (Suc (Suc hp)))"
proof
  fix x
  assume "restructurable_heap h hp ep (length cd)"
  hence "3 dvd hp" by (simp add: restructurable_heap_def)
  moreover hence "Suc hp mod 3 = 1" by presburger
  moreover hence "Suc (Suc hp) mod 3 = 2" by presburger
  ultimately show "((assm_hp cd h hp)
    (hp := (Con 0, Suc a), Suc hp := (Con 0, b), Suc (Suc hp) := (Con 0, c))) x =
      assm_hp cd (h(hp := Suc a, Suc hp := b, Suc (Suc hp) := c)) (Suc (Suc (Suc hp))) x" 
    by (simp add: assm_hp_lemma1 assm_hp_lemma2 assm_hp_lemma3 assm_hp_lemma4 assm_hp_lemma5)
qed

lemma [simp]: "restructurable_heap h hp ep (length cd) \<Longrightarrow> (assm_hp cd h hp)
  (hp := (Con 0, 0), Suc hp := (Reg Env, a), Suc (Suc hp) := (PC 0, assembly_map cd b)) = 
    assm_hp cd (h(hp := 0, Suc hp := a, Suc (Suc hp) := b)) (Suc (Suc (Suc hp)))"
proof
  fix x
  assume "restructurable_heap h hp ep (length cd)"
  hence H: "3 dvd hp" by (simp add: restructurable_heap_def)
  moreover hence "Suc hp mod 3 = 1" by presburger
  moreover hence "Suc (Suc hp) mod 3 = 2" by presburger
  ultimately show "((assm_hp cd h hp)(hp := (Con 0, 0), Suc hp := (Reg Env, a), 
    Suc (Suc hp) := (PC 0, assembly_map cd b))) x =
      assm_hp cd (h(hp := 0, Suc hp := a, Suc (Suc hp) := b)) (Suc (Suc (Suc hp))) x" 
    by (simp add: assm_hp_lemma1 assm_hp_lemma2 assm_hp_lemma3 assm_hp_lemma4 assm_hp_lemma5)
qed

lemma [simp]: "restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> 
  assemble_heap mp h hp (Suc (vs vp)) = (if h (vs vp) = 0 then Reg Env else Con 0, h (Suc (vs vp)))"
proof (unfold assemble_heap_def restructurable_vals_def)
  assume "3 dvd hp \<and> (\<forall>x<Suc (Suc vp). 3 dvd vs x \<and> vs x < hp)"
  moreover hence X: "3 dvd vs vp \<and> vs vp < hp" by simp
  ultimately have "Suc (vs vp) < hp" by fastforce
  moreover from X have "Suc (vs vp) mod 3 = 1" by presburger
  ultimately show "(if Suc (vs vp) \<ge> hp then (Con 0, 0) else case Suc (vs vp) mod 3 of 
       0 \<Rightarrow> (Con 0, h (Suc (vs vp)))
     | Suc 0 \<Rightarrow> (if h (Suc (vs vp) - 1) = 0 then Reg Env else Con 0, h (Suc (vs vp)))
     | Suc (Suc 0) \<Rightarrow> if h (Suc (vs vp) - 2) = 0 then (PC 0, mp (h (Suc (vs vp)))) 
        else (Con 0, h (Suc (vs vp)))
     | Suc (Suc (Suc x)) \<Rightarrow> undefined) = (if h (vs vp) = 0 then Reg Env else Con 0, h (Suc (vs vp)))" 
    by simp
qed

lemma [simp]: "restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> h (vs vp) = 0 \<Longrightarrow> 
  restructurable_heap h hp ep lcd \<Longrightarrow>
    assemble_heap mp h hp (Suc (Suc (vs vp))) = (PC 0, mp (h (Suc (Suc (vs vp)))))"
proof (unfold assemble_heap_def restructurable_vals_def)
  assume "3 dvd hp \<and> (\<forall>x<Suc (Suc vp). 3 dvd vs x \<and> vs x < hp)"
  hence "3 dvd vs vp \<and> vs vp < hp" by simp
  moreover assume "restructurable_heap h hp ep lcd"
  moreover hence "3 dvd hp" by auto
  ultimately have "Suc (Suc (vs vp)) mod 3 = 2 \<and> Suc (Suc (vs vp)) < hp" by presburger
  moreover assume "h (vs vp) = 0"
  ultimately show "(if (Suc (Suc (vs vp))) \<ge> hp then (Con 0, 0) else case Suc (Suc (vs vp)) mod 3 of 
       0 \<Rightarrow> (Con 0, h (Suc (Suc (vs vp))))
     | Suc 0 \<Rightarrow> (if h (Suc (Suc (vs vp)) - 1) = 0 then Reg Env else Con 0, h (Suc (Suc (vs vp))))
     | Suc (Suc 0) \<Rightarrow>
         if h (Suc (Suc (vs vp)) - 2) = 0 then (PC 0, mp (h (Suc (Suc (vs vp))))) 
        else (Con 0, h (Suc (Suc (vs vp))))
     | Suc (Suc (Suc x)) \<Rightarrow> undefined) = (PC 0, mp (h (Suc (Suc (vs vp)))))" 
    by simp
qed

lemma [simp]: "Suc (Suc (vs vp)) mod 3 \<noteq> Suc (Suc (Suc x))" 
  by simp

lemma [simp]: "h (vs vp) = Suc x \<Longrightarrow> vs vp mod 3 = 0 \<Longrightarrow> Suc (Suc (vs vp)) < hp \<Longrightarrow>
    assemble_heap mp h hp (Suc (Suc (vs vp))) = (Con 0, h (Suc (Suc (vs vp))))"
  by (simp add: assemble_heap_def split: nat.splits) presburger

lemma [simp]: "even sp \<Longrightarrow> assm_stk cd sh (Suc (Suc sp)) (Suc sp) = (Reg Env, sh (Suc sp))"
  by (simp add: assemble_stack_def)

lemma [simp]: "even sp \<Longrightarrow> 
  (assm_stk cd sh sp)(sp := (PC 0, assembly_map cd pc), Suc sp := (Reg Env, a)) = 
    (assm_stk cd (sh(sp := pc, Suc sp := a)) (Suc (Suc sp)))"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> 
  (assm_stk cd sh (Suc sp))(Suc sp := (PC 0, assembly_map cd pc), Suc (Suc sp) := (Reg Env, k)) =
    (assm_stk cd (sh(Suc sp := pc, Suc (Suc sp) := k)) (Suc (Suc (Suc sp))))"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> 
    (assm_stk cd sh sp)(sp := (Reg Env, k)) = assm_stk cd (sh(sp := k)) (Suc sp)"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> 
    (assm_stk cd sh (Suc sp))(sp := (Reg Env, k)) = assm_stk cd (sh(sp := k)) (Suc sp)"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc (Suc sp)) \<Longrightarrow> 
    (assm_stk cd sh sp)(sp := (PC 0, 0)) = assm_stk cd (sh(sp := 0)) (Suc sp)"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> assm_stk cd sh (Suc sp) sp = (Reg Env, sh sp)"
  by (simp add: assemble_stack_def)

lemma [simp]: "even (Suc (Suc sp)) \<Longrightarrow> assm_stk cd sh (Suc sp) sp = 
    (PC 0, assembly_map cd (sh sp))"
  by (simp add: assemble_stack_def)

lemma [simp]: "(assm_stk cd sh (Suc sp))(sp := (Con 0, 0)) = assm_stk cd sh sp"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "(assemble_vals vs vp)(vp := (Reg Hp, y)) = assemble_vals (vs(vp := y)) (Suc vp)"
  by (auto simp add: assemble_vals_def)

lemma [simp]: "(assemble_vals vs (Suc vp))(vp := (Con 0, 0)) = assemble_vals vs vp"
  by rule (simp add: assemble_vals_def)

lemma [simp]: "even ep \<Longrightarrow> (assemble_env e ep)(ep := (Reg Hp, a), Suc ep := (Reg Env, b)) = 
    assemble_env (e(ep := a, Suc ep := b)) (Suc (Suc ep))"
  by (auto simp add: assemble_env_def)

lemma [simp]: "unstr_lookup e a x = Some v \<Longrightarrow> lookup cd pc = Some (Lookup\<^sub>b y) \<Longrightarrow> x \<le> y \<Longrightarrow> 
  pc < length cd \<Longrightarrow> a \<le> ep \<Longrightarrow> restructurable_env e ep hp \<Longrightarrow> iter_evala (assemble_code cd) 
    (5 + 2 * x) (AS (case_register h (assemble_env e ep) vs sh) (case_register hp ep vp sp) a 
      (Reg Env) (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e ep)
        (vs(vp := (Reg Hp, v))) sh) (case_register hp ep (Suc vp) sp) 0 (Con 0) 
          (assembly_map cd pc))"
proof (induction e a x rule: unstr_lookup.induct)
  case (3 e p)
  moreover from 3 have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (ASub (Acc (Reg Env)) 2)" by simp
  moreover from 3 have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AGet (Acc (Reg Env)) (Reg Hp))" by simp
  moreover from 3 have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (APut Vals (Acc (Con 0)))" by (simp del: add_2_eq_Suc)
  ultimately show ?case by (simp add: numeral_def assemble_env_def split: if_splits)
next
  case (4 e p x)
  moreover hence "lookup (assemble_code cd) (6 + 2 * x + assembly_map cd pc) = 
    Some (ASub (Acc (Reg Env)) (Suc 0))" by simp
  moreover from 4 have "lookup (assemble_code cd) (5 + 2 * x + assembly_map cd pc) = 
    Some (AGet (Acc (Reg Env)) (Reg Env))" by simp
  ultimately have X: "iter_evala (assemble_code cd) 2 (AS (case_register h (assemble_env e ep) vs 
    sh) (case_register hp ep vp sp) (Suc (Suc p)) (Reg Env)
      (7 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e ep) vs sh) 
        (case_register hp ep vp sp) (e (Suc p)) (Reg Env) (5 + 2 * x + assembly_map cd pc))" 
    by (simp add: numeral_def assemble_env_def split: if_splits) presburger
  from 4 have "Suc p < ep" and "even p" and "restructurable_env e ep hp" by (auto split: if_splits)
  hence "e (Suc p) < ep" by (auto split: if_splits)
  moreover with 4 have "iter_evala (assemble_code cd) (5 + 2 * x)
    (AS (case_register h (assemble_env e ep) vs sh) (case_register hp ep vp sp) (e (Suc p)) (Reg Env)
      (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e ep) 
        (vs(vp := (Reg Hp, v))) sh) (case_register hp ep (Suc vp) sp) 0 (Con 0) 
          (assembly_map cd pc))" by (simp split: if_splits)
  with X have "iter_evala (assemble_code cd) (2 + (5 + 2 * x))
    (AS (case_register h (assemble_env e ep) vs sh) (case_register hp ep vp sp) (Suc (Suc p)) (
      Reg Env) (7 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e ep) 
        (vs(vp := (Reg Hp, v))) sh) (case_register hp ep (Suc vp) sp) 0 (Con 0) 
          (assembly_map cd pc))" 
    using iter_evala_combine by blast
  thus ?case by simp
qed simp_all

theorem correcta [simp]: "cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow> 
  \<exists>n. iter_evala (assemble_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u')"
proof (induction cd\<^sub>b \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: eval\<^sub>u.induct)
  case (ev\<^sub>u_lookup cd pc x e sh sp y h hp ep vs vp)
  moreover hence "odd sp" by simp
  moreover from ev\<^sub>u_lookup have "lookup (assemble_code cd) (7 + 2 * x + assembly_map cd pc) = 
    Some (AMov (Reg Stk))" by simp
  moreover from ev\<^sub>u_lookup have "lookup (assemble_code cd) (6 + 2 * x + assembly_map cd pc) = 
    Some (ASub (Acc (Reg Stk)) 1)" by simp
  moreover from ev\<^sub>u_lookup have "lookup (assemble_code cd) (5 + 2 * x + assembly_map cd pc) = 
    Some (AGet (Acc (Reg Stk)) (Reg Env))" by simp
  ultimately have X: "iter_evala (assemble_code cd) 3 
    (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp))) (case_register hp ep vp (Suc sp)) 0 (Con 0) 
        (8 + 2 * x + assembly_map cd pc)) = Some (AS (case_register (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc sp))) 
            (case_register hp ep vp (Suc sp)) (sh sp) (Reg Env) (5 + 2 * x + assembly_map cd pc))" 
    by (simp add: numeral_def)
  from ev\<^sub>u_lookup have "sh sp \<le> ep" by auto
  with ev\<^sub>u_lookup have "iter_evala (assemble_code cd) (5 + 2 * x) 
    (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp))) (case_register hp ep vp (Suc sp)) (sh sp) (Reg Env) 
        (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals (vs(vp := y)) (Suc vp)) (assm_stk cd sh (Suc sp))) 
            (case_register hp ep (Suc vp) (Suc sp)) 0 (Con 0) (assembly_map cd pc))" 
    by simp
  with X have "iter_evala (assemble_code cd) (3 + (5 + 2 * x)) 
    (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp))) (case_register hp ep vp (Suc sp)) 0 (Con 0) 
        (8 + 2 * x + assembly_map cd pc)) = Some (AS (case_register (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals (vs(vp := y)) (Suc vp)) (assm_stk cd sh (Suc sp))) 
            (case_register hp ep (Suc vp) (Suc sp)) 0 (Con 0) (assembly_map cd pc))" 
    using iter_evala_combine by blast
  hence "iter_evala (assemble_code cd) (3 + (5 + 2 * x)) 
    (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp))) (case_register hp ep vp (Suc sp)) 0 (Con 0) 
        (8 + (2 * x + assembly_map cd pc))) = Some (AS (case_register (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals (vs(vp := y)) (Suc vp)) (assm_stk cd sh (Suc sp))) 
            (case_register hp ep (Suc vp) (Suc sp)) 0 (Con 0) (assembly_map cd pc))"
    by (simp add: add.assoc)
  with ev\<^sub>u_lookup show ?case by auto
next
  case (ev\<^sub>u_pushcon cd pc k h hp e ep vs vp sh sp)
  moreover from ev\<^sub>u_pushcon have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (APut Vals (Reg Hp))" by simp
  moreover from ev\<^sub>u_pushcon have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (AAdd (Reg Vals) 1)" by simp
  moreover from ev\<^sub>u_pushcon have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (APut Hp (Con 1))" by simp 
  moreover from ev\<^sub>u_pushcon have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AAdd (Reg Hp) 1)" by simp 
  moreover from ev\<^sub>u_pushcon have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (APut Hp (Con k))" by simp 
  moreover from ev\<^sub>u_pushcon have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAdd (Reg Hp) 1)" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 8 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc sp))) 
      (case_register hp ep vp (Suc sp)) 0 (Con 0) (assembly_map cd (Suc pc))) = Some (AS 
        (case_register (assm_hp cd (h(hp := Suc 0, Suc hp := k, Suc (Suc hp) := 0)) (3 + hp)) 
          (assemble_env e ep) (assemble_vals (vs(vp := hp)) (Suc vp)) (assm_stk cd sh (Suc sp))) 
            (case_register (3 + hp) ep (Suc vp) (Suc sp)) 0 (Con 0) (assembly_map cd pc))" 
    by (auto simp add: numeral_def)
  thus ?case by auto
next
  case (ev\<^sub>u_pushlam cd pc pc' h hp e ep vs vp sh sp)
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (11 + assembly_map cd pc) = 
    Some (APut Vals (Reg Hp))" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (10 + assembly_map cd pc) = 
    Some (AAdd (Reg Vals) 1)" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (AMov (Reg Stk))" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (ASub (Acc (Reg Stk)) 1)" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AGet (Acc (Reg Stk)) (Reg Env))" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (APut Hp (Con 0))" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd (Reg Hp) 1)" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (4 + assembly_map cd pc) =
    Some (APut Hp (Acc (Con 0)))" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AAdd (Reg Hp) 1)" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AMov (Con 0))" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 12 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc sp))) 
      (case_register hp ep vp (Suc sp)) 0 (Con 0) (assembly_map cd (Suc pc))) = Some (AS 
        (case_register (assm_hp cd (h(hp := 0, Suc hp := sh sp, Suc (Suc hp) := pc')) (3 + hp)) 
          (assemble_env e ep) (assemble_vals (vs(vp := hp)) (Suc vp)) (assm_stk cd sh (Suc sp))) 
            (case_register (3 + hp) ep (Suc vp) (Suc sp)) 0 (Con 0) (assembly_map cd pc))" 
    by (auto simp add: numeral_def)
  thus ?case by auto
next
  case (ev\<^sub>u_apply cd pc h vs vp hp e ep sh sp)
  moreover hence "even ep" by auto
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (23 + assembly_map cd pc) = 
    Some (ASub (Reg Vals) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (22 + assembly_map cd pc) = 
    Some (AGet (Reg Vals) (Reg Hp))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (21 + assembly_map cd pc) = 
    Some (APut Vals (Con 0))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (20 + assembly_map cd pc) = 
    Some (APut Env (Acc (Con 0)))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (19 + assembly_map cd pc) = 
    Some (AAdd (Reg Env) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (18 + assembly_map cd pc) = 
    Some (AMov (PC 0))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (17 + assembly_map cd pc) = 
    Some (ASub (Acc (PC 0)) 18)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (16 + assembly_map cd pc) = 
    Some (APut Stk (Acc (Con 0)))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (15 + assembly_map cd pc) = 
    Some (AAdd (Reg Stk) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (14 + assembly_map cd pc) = 
    Some (AMov (Reg Env))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (13 + assembly_map cd pc) = 
    Some (AAdd (Acc (Reg Env)) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (12 + assembly_map cd pc) = 
    Some (APut Stk (Acc (Con 0)))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (11 + assembly_map cd pc) = 
    Some (AAdd (Reg Stk) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (10 + assembly_map cd pc) = 
    Some (ASub (Reg Vals) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (AGet (Reg Vals) (Reg Hp))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (AAdd (Acc (Reg Hp)) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AGet (Acc (Reg Hp)) (Reg Env))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (APut Env (Acc (Con 0)))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd (Reg Env) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AGet (Reg Vals) (Reg Hp))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (APut Vals (Con 0))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAdd (Acc (Reg Hp)) 2)" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 24 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs (Suc (Suc vp))) (assm_stk cd sh (Suc sp))) 
      (case_register hp ep (Suc (Suc vp)) (Suc sp)) 0 (Con 0) (assembly_map cd (Suc pc))) = 
        Some (AS (case_register (assm_hp cd h hp) (assemble_env (e(ep := vs (Suc vp), 
          Suc ep := h (Suc (vs vp)))) (Suc (Suc ep))) (assemble_vals vs vp) 
            (assm_stk cd (sh(Suc sp := pc, Suc (Suc sp) := Suc (Suc ep))) (Suc (Suc (Suc sp))))) 
              (case_register hp (Suc (Suc ep)) vp (Suc (Suc (Suc sp)))) 0 (Con 0) 
                (assembly_map cd (h (Suc (Suc (vs vp))))))"
    by (auto simp add: numeral_def assemble_vals_def)
  thus ?case by auto
next
  case (ev\<^sub>u_return cd pc h hp e ep vs vp sh sp)
  moreover from ev\<^sub>u_return have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (ASub (Reg Stk) 1)" by simp
  moreover from ev\<^sub>u_return have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (APut Stk (Con 0))" by simp
  moreover from ev\<^sub>u_return have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (ASub (Reg Stk) 1)" by simp
  moreover from ev\<^sub>u_return have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AGet (Reg Stk) (PC 0))" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 6 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc (Suc sp)))) 
      (case_register hp ep vp (Suc (Suc sp))) 0 (Con 0) (assembly_map cd (Suc pc))) = 
        Some (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
          (assm_stk cd sh sp)) (case_register hp ep vp sp) 0 (Con 0) (assembly_map cd (sh sp)))"
    by (simp add: numeral_def split: prod.splits)
  thus ?case by auto
next
  case (ev\<^sub>u_jump cd pc h vs vp hp e ep sh sp)
  moreover hence "even ep" by auto
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (20 + assembly_map cd pc) = 
    Some (ASub (Reg Vals) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (19 + assembly_map cd pc) = 
    Some (AGet (Reg Vals) (Reg Hp))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (18 + assembly_map cd pc) = 
    Some (APut Vals (Con 0))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (17 + assembly_map cd pc) = 
    Some (APut Env (Acc (Con 0)))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (16 + assembly_map cd pc) = 
    Some (AAdd (Reg Env) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (15 + assembly_map cd pc) = 
    Some (AMov (Reg Env))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (14 + assembly_map cd pc) = 
    Some (AAdd (Acc (Reg Env)) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (13 + assembly_map cd pc) = 
    Some (ASub (Reg Stk) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (12 + assembly_map cd pc) = 
    Some (APut Stk (Acc (Con 0)))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (11 + assembly_map cd pc) =
    Some (AAdd (Reg Stk) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (10 + assembly_map cd pc) = 
    Some (ASub (Reg Vals) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (AGet (Reg Vals) (Reg Hp))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (AAdd (Acc (Reg Hp)) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AGet (Acc (Reg Hp)) (Reg Env))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (APut Env (Acc (Con 0)))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd (Reg Env) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AGet (Reg Vals) (Reg Hp))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (APut Vals (Con 0))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAdd (Acc (Reg Hp)) 2)" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 21 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs (Suc (Suc vp))) (assm_stk cd sh (Suc sp))) 
      (case_register hp ep (Suc (Suc vp)) (Suc sp)) 0 (Con 0) (assembly_map cd (Suc pc))) = 
        Some (AS (case_register (assm_hp cd h hp) (assemble_env (e(ep := vs (Suc vp), 
          Suc ep := h (Suc (vs vp)))) (Suc (Suc ep))) (assemble_vals vs vp) 
            (assm_stk cd (sh(sp := Suc (Suc ep))) (Suc sp))) (case_register hp 
              (Suc (Suc ep)) vp (Suc sp)) 0 (Con 0) (assembly_map cd (h (Suc (Suc (vs vp))))))"
    by (auto simp add: numeral_def assemble_vals_def)
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
    Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u')" by (metis correcta)
  moreover from iter_step obtain m where "
    iter_evala (assemble_code cd\<^sub>b) m (assm_state cd\<^sub>b \<Sigma>\<^sub>u') = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u'')" 
    by (metis preserve_restructure)
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

(* We no longer do the reverse (completeness) direction because it's rather complex to even state 
now *)

lemma [simp]: "assm_hp cd h 0 = (\<lambda>x. (Con 0, 0))"
  by rule (simp add: assemble_heap_def)

lemma [simp]: "assemble_env e 0 = (\<lambda>x. (Con 0, 0))"
  by rule (simp add: assemble_env_def)

lemma [simp]: "assemble_vals vs 0 = (\<lambda>x. (Con 0, 0))"
  by rule (simp add: assemble_vals_def)

lemma [simp]: "assm_stk cd (mp(0 := a, Suc 0 := b)) 2 = 
    (\<lambda>x. (Con 0, 0))(0 := (PC 0, assembly_map cd a), Suc 0 := (Reg Env, b))"
  by rule (simp add: assemble_stack_def)

lemma [simp]: "
  assembly_map (lib @ flatten_code' (length lib) cd @ cd') (length lib + code_list_size cd) = 
    assembly_map (lib @ flatten_code' (length lib) cd) (length (lib @ flatten_code' (length lib) cd))"
        by (metis assembly_map_postpend append.assoc length_append length_flatten')

lemma assembly_map_flatten' [simp]: "properly_terminated\<^sub>e cd \<Longrightarrow>
  assembly_map (lib @ flatten_code' (length lib) cd) (length lib + code_list_size cd) = 
    sum_list (map (Suc \<circ> assemble_op_len) (lib @ flatten_code' (length lib) cd))"
proof (induction "length lib" cd arbitrary: lib rule: flatten_code'.induct)
  case (4 cd' cd)
  let ?lib = "lib @ flatten_code' (length lib) cd'"
  let ?cd = "flatten_code' (length ?lib) cd"
  have X: "assembly_map (?lib @ ?cd @ [PushLam\<^sub>b (length lib + code_list_size cd')]) 
    (length ?lib + code_list_size cd) = assembly_map (?lib @ ?cd) (length (?lib @ ?cd))" 
      by (metis assembly_map_postpend append.assoc length_append length_flatten')
  from 4 have Y: "properly_terminated\<^sub>e cd" by simp
  have "length lib + length (flatten_code' (length lib) cd') = length ?lib" by simp
  with 4 Y have "assembly_map (?lib @ ?cd) (length ?lib + code_list_size cd) =
    sum_list (map (Suc \<circ> assemble_op_len) (?lib @ ?cd))" by blast
  with X show ?case by (simp add: add.assoc) 
qed simp_all

lemma [simp]: "properly_terminated\<^sub>e cd \<Longrightarrow> assembly_map (flatten_code cd) (code_list_size cd) = 
    sum_list (map (Suc \<circ> assemble_op_len) (flatten_code cd))"
proof (unfold flatten_code_def)
  assume "properly_terminated\<^sub>e cd"
  hence "assembly_map ([] @ flatten_code' 0 cd) (length [] + code_list_size cd) = 
    sum_list (map (Suc \<circ> assemble_op_len) ([] @ flatten_code' 0 cd))" 
      by (metis assembly_map_flatten' list.size(3))
  thus "assembly_map (flatten_code' 0 cd) (code_list_size cd) = 
    sum_list (map (Suc \<circ> assemble_op_len) (flatten_code' 0 cd))" by simp
qed

end