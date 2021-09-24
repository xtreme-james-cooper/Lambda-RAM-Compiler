theory Assemble
  imports AssemblyCode "../12UnstructuredMemory/UnstructuredMemory" "../00Utils/Utils"
begin

primrec assemble_op_len :: "byte_code \<Rightarrow> nat" where
  "assemble_op_len (BLookup x) = 7 + 2 * x"
| "assemble_op_len (BPushCon k) = 7"
| "assemble_op_len (BPushLam pc) = 11"
| "assemble_op_len BApply = 21"
| "assemble_op_len BReturn = 2"
| "assemble_op_len BJump = 18"

primrec assemble_op :: "(nat \<Rightarrow> nat) \<Rightarrow> byte_code \<Rightarrow> assm list" where
  "assemble_op mp (BLookup x) = [
    AMov (Con 0),
    AAdd Vals 1,
    APutA Vals,
    AGetA Env (Reg Hp),
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
    APutPC Hp (mp pc), 
    AMov (Con 0),
    AAdd Hp 1, 
    APutA Hp,
    AAdd Hp 1, 
    APut Hp (Con 0),
    AGetA Stk (Reg Env), 
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
    AGet Vals (Reg Hp),
    ASub Vals 1]"
| "assemble_op mp BReturn = [
    AJmp,
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
    AGet Vals (Reg Hp),
    ASub Vals 1]"

fun assembly_map :: "byte_code list \<Rightarrow> nat \<Rightarrow> nat" where
  "assembly_map [] x = 0"
| "assembly_map (op # cd) 0 = 0"
| "assembly_map (op # cd) (Suc x) = Suc (assemble_op_len op + assembly_map cd x)"

definition assemble_code :: "byte_code list \<Rightarrow> assm list" where
  "assemble_code cd = concat (map (assemble_op (assembly_map cd)) cd)"

definition assemble_heap :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat" where
  "assemble_heap mp h x = (case x mod 3 of
      0 \<Rightarrow> (Con 0, h x)
    | Suc 0 \<Rightarrow> (if h (x - 1) = 0 then Reg Env else Con 0, h x)
    | Suc (Suc 0) \<Rightarrow> if h (x - 2) = 0 then (PC, mp (h x)) else (Con 0, h x))"

definition assemble_env :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat" where
  "assemble_env e x = (Reg (if even x then Hp else Env), e x)"

definition assemble_vals :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat" where
  "assemble_vals vs x = (Reg Hp, vs x)"

definition assemble_stack :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat" where
  "assemble_stack mp s x = (if even x then (PC, mp (s x)) else (Reg Env, s x))"

primrec assemble_state :: "(nat \<Rightarrow> nat) \<Rightarrow> unstr_state \<Rightarrow> assm_state" where
  "assemble_state mp (US h hp e ep vs vp sh sp pc) = 
    AS (case_register (assemble_heap mp h) (assemble_env e) (assemble_vals vs) 
      (assemble_stack mp sh)) (case_register hp ep vp sp) 0 (Con 0) (mp pc)"

abbreviation assm_hp :: "byte_code list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat" where
  "assm_hp cd \<equiv> assemble_heap (assembly_map cd)"

abbreviation assm_stk :: "byte_code list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat" where
  "assm_stk cd \<equiv> assemble_stack (assembly_map cd)"

abbreviation assm_state :: "byte_code list \<Rightarrow> unstr_state \<Rightarrow> assm_state" where
  "assm_state cd \<equiv> assemble_state (assembly_map cd)"

lemma [simp]: "length (assemble_op mp op) = Suc (assemble_op_len op)"
  by (induction op) simp_all

lemma [simp]: "length \<circ> assemble_op mp = Suc \<circ> assemble_op_len"
  by auto

lemma [simp]: "assemble_code [] \<tturnstile>\<^sub>a \<Sigma> = None"
  by (induction \<Sigma>) (simp_all add: assemble_code_def split: nat.splits)

lemma [simp]: "assembly_map cd 0 = 0"
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

(*

TODO

theorem completea [simp]: "assemble_code cd\<^sub>b \<tturnstile>\<^sub>a assm_state cd\<^sub>b \<Sigma>\<^sub>u = Some \<Sigma>\<^sub>a' \<Longrightarrow> 
  restructurable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow>
    \<exists>n \<Sigma>\<^sub>u'. iter_evala (assemble_code cd\<^sub>b) n \<Sigma>\<^sub>a' = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u') \<and> cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u'"
proof (induction \<Sigma>\<^sub>u)
  case (US h hp e ep vs vp sh sp pc)
  from US(1) obtain pc' where PCA: "assembly_map cd\<^sub>b pc = Suc pc'" by (simp split: nat.splits)
  moreover from US have "pc \<le> length cd\<^sub>b" by simp
  ultimately obtain pc\<^sub>b' op\<^sub>b cd\<^sub>a' cd\<^sub>a'' where PCB: "pc = Suc pc\<^sub>b' \<and> lookup cd\<^sub>b pc\<^sub>b' = Some op\<^sub>b \<and> 
    pc' = length cd\<^sub>a' + assemble_op_len op\<^sub>b \<and>
      assemble_code cd\<^sub>b = cd\<^sub>a' @ assemble_op (assembly_map cd\<^sub>b) op\<^sub>b @ cd\<^sub>a''" 
        by (metis assm_map_to_suc)


  from US PCA PCB have "Option.bind (lookup (assemble_op (assembly_map cd\<^sub>b) op\<^sub>b @ cd\<^sub>a'') (assemble_op_len op\<^sub>b))
          (assm_step (case_register (assm_hp hp cd\<^sub>b h) e vs (assm_stk sp cd\<^sub>b sh)) (case_register hp ep vp sp) 0
            (Con 0) pc') = Some \<Sigma>\<^sub>a'" by simp


  have "iter_evala (cd\<^sub>a' @ assemble_op (assembly_map cd\<^sub>b) op\<^sub>b @ cd\<^sub>a'') (assemble_op_len op\<^sub>b) \<Sigma>\<^sub>a' = 
    Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u') \<and>
      cd\<^sub>b \<tturnstile> US h hp e ep vs vp sh sp (Suc pc\<^sub>b') \<leadsto>\<^sub>u \<Sigma>\<^sub>u'" by simp
  with PCB show ?case by fastforce
qed

*)

lemma [simp]: "lookup cd pc = Some op \<Longrightarrow> 
  assembly_map cd (Suc pc) = Suc (assemble_op_len op + assembly_map cd pc)"
proof (induction cd pc rule: assembly_map.induct)
  case (2 op' cd)
  thus ?case by (cases cd) simp_all
qed simp_all

lemma [simp]: "length (assemble_code cd) = sum_list (map (Suc \<circ> assemble_op_len) cd)"
  by (induction cd) (simp_all add: assemble_code_def)

lemma [simp]: "assembly_map cd (length cd) = length (assemble_code cd)"
  by (induction cd) (simp_all add: assemble_code_def)

lemma [simp]: "lookup (assemble_op mp op @ cd) (Suc (assemble_op_len op + x)) = lookup cd x"
proof -
  have "lookup (assemble_op mp op @ cd) (length (assemble_op mp op) + x) = lookup cd x" 
    by (metis lookup_append)
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

lemma assm_hp_lemma1: "3 dvd x \<Longrightarrow> assemble_heap mp h x = (Con 0, h x)"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma2: "x mod 3 = 1 \<Longrightarrow> h (x - 1) \<noteq> 0 \<Longrightarrow> assemble_heap mp h x = (Con 0, h x)"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma3: "x mod 3 = 1 \<Longrightarrow> h (x - 1) = 0 \<Longrightarrow>  assemble_heap mp h x = (Reg Env, h x)"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma4: "x mod 3 = 2 \<Longrightarrow> h (x - 2) \<noteq> 0 \<Longrightarrow> assemble_heap mp h x = (Con 0, h x)"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma5: "x mod 3 = 2 \<Longrightarrow> h (x - 2) = 0 \<Longrightarrow> assemble_heap mp h x = (PC, mp (h x))"
  by (simp add: assemble_heap_def)

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
  assm_hp cd (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x = assm_hp cd h x"
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
         then (PC, assembly_map cd ((h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x))
         else (Con 0, (h(hp := a, Suc hp := b, Suc (Suc hp) := c)) x)) =
    (if h (x - 2) = 0 then (PC, assembly_map cd (h x)) else (Con 0, h x))" by simp
    with M show ?thesis by (simp add: assemble_heap_def)
  qed
qed (simp_all add: assemble_heap_def)

lemma [simp]: "restructurable_heap h hp ep (length cd) \<Longrightarrow> (assm_hp cd h)
  (hp := (Con 0, Suc a), Suc hp := (Con 0, b), Suc (Suc hp) := (Con 0, c)) = 
    assm_hp cd (h(hp := Suc a, Suc hp := b, Suc (Suc hp) := c))"
proof
  fix x
  assume "restructurable_heap h hp ep (length cd)"
  hence H: "3 dvd hp" by (simp add: restructurable_heap_def)
  moreover hence "Suc hp mod 3 = 1" by presburger
  moreover hence "Suc (Suc hp) mod 3 = 2" by presburger
  ultimately show "((assm_hp cd h)
    (hp := (Con 0, Suc a), Suc hp := (Con 0, b), Suc (Suc hp) := (Con 0, c))) x =
      assm_hp cd (h(hp := Suc a, Suc hp := b, Suc (Suc hp) := c)) x" 
    by (simp add: assm_hp_lemma1 assm_hp_lemma2 assm_hp_lemma3 assm_hp_lemma4 assm_hp_lemma5)
qed

lemma [simp]: "restructurable_heap h hp ep (length cd) \<Longrightarrow> (assm_hp cd h)
  (hp := (Con 0, 0), Suc hp := (Reg Env, a), Suc (Suc hp) := (PC, assembly_map cd b)) = 
    assm_hp cd (h(hp := 0, Suc hp := a, Suc (Suc hp) := b))"
proof
  fix x
  assume "restructurable_heap h hp ep (length cd)"
  hence H: "3 dvd hp" by (simp add: restructurable_heap_def)
  moreover hence "Suc hp mod 3 = 1" by presburger
  moreover hence "Suc (Suc hp) mod 3 = 2" by presburger
  ultimately show "((assm_hp cd h)(hp := (Con 0, 0), Suc hp := (Reg Env, a), 
    Suc (Suc hp) := (PC, assembly_map cd b))) x =
      assm_hp cd (h(hp := 0, Suc hp := a, Suc (Suc hp) := b)) x" 
    by (simp add: assm_hp_lemma1 assm_hp_lemma2 assm_hp_lemma3 assm_hp_lemma4 assm_hp_lemma5)
qed

lemma [simp]: "restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> 
  assemble_heap mp h (Suc (vs vp)) = (if h (vs vp) = 0 then Reg Env else Con 0, h (Suc (vs vp)))"
proof (unfold assemble_heap_def restructurable_vals_def)
  assume "\<forall>x<Suc (Suc vp). 3 dvd vs x \<and> vs x < hp"
  hence "3 dvd vs vp" by simp
  hence "Suc (vs vp) mod 3 = 1" by presburger
  thus "(case Suc (vs vp) mod 3 of 0 \<Rightarrow> (Con 0, h (Suc (vs vp)))
     | Suc 0 \<Rightarrow> (if h (Suc (vs vp) - 1) = 0 then Reg Env else Con 0, h (Suc (vs vp)))
     | Suc (Suc 0) \<Rightarrow> if h (Suc (vs vp) - 2) = 0 then (PC, mp (h (Suc (vs vp)))) 
        else (Con 0, h (Suc (vs vp)))
     | Suc (Suc (Suc x)) \<Rightarrow> nmem x) =
    (if h (vs vp) = 0 then Reg Env else Con 0, h (Suc (vs vp)))" by simp
qed

lemma [simp]: "restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> h (vs vp) = 0 \<Longrightarrow> 
  restructurable_heap h hp ep lcd \<Longrightarrow>
    assemble_heap mp h (Suc (Suc (vs vp))) = (PC, mp (h (Suc (Suc (vs vp)))))"
proof (unfold assemble_heap_def restructurable_vals_def)
  assume "\<forall>x<Suc (Suc vp). 3 dvd vs x \<and> vs x < hp"
  hence "3 dvd vs vp \<and> vs vp < hp" by simp
  moreover assume "restructurable_heap h hp ep lcd"
  moreover hence "3 dvd hp" by auto
  ultimately have "Suc (Suc (vs vp)) mod 3 = 2 \<and> Suc (Suc (vs vp)) < hp" by presburger
  moreover assume "h (vs vp) = 0"
  ultimately show "(case Suc (Suc (vs vp)) mod 3 of 0 \<Rightarrow> (Con 0, h (Suc (Suc (vs vp))))
     | Suc 0 \<Rightarrow> (if h (Suc (Suc (vs vp)) - 1) = 0 then Reg Env else Con 0, h (Suc (Suc (vs vp))))
     | Suc (Suc 0) \<Rightarrow>
         if h (Suc (Suc (vs vp)) - 2) = 0 then (PC, mp (h (Suc (Suc (vs vp))))) 
        else (Con 0, h (Suc (Suc (vs vp))))
     | Suc (Suc (Suc x)) \<Rightarrow> nmem x) =
    (PC, mp (h (Suc (Suc (vs vp)))))" 
        by simp
    qed

lemma [simp]: "Suc (Suc (vs vp)) mod 3 \<noteq> Suc (Suc (Suc x))" 
  by simp

lemma [simp]: "h (vs vp) = Suc x \<Longrightarrow> vs vp mod 3 = 0 \<Longrightarrow>
    assemble_heap mp h (Suc (Suc (vs vp))) = (Con 0, h (Suc (Suc (vs vp))))"
  by (simp add: assemble_heap_def split: nat.splits) presburger

lemma [simp]: "even sp \<Longrightarrow> assm_stk cd sh (Suc sp) = (Reg Env, sh (Suc sp))"
  by (simp add: assemble_stack_def)

lemma [simp]: "even sp \<Longrightarrow> 
  (assm_stk cd sh)(sp := (PC, assembly_map cd pc), Suc sp := (Reg Env, a)) = 
    (assm_stk cd (sh(sp := pc, Suc sp := a)))"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> 
  (assm_stk cd sh)(Suc sp := (PC, assembly_map cd pc), Suc (Suc sp) := (Reg Env, k)) =
    (assm_stk cd (sh(Suc sp := pc, Suc (Suc sp) := k)))"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> 
    (assm_stk cd sh)(sp := (Reg Env, k)) = assm_stk cd (sh(sp := k))"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc (Suc sp)) \<Longrightarrow> 
    (assm_stk cd sh)(sp := (PC, 0)) = assm_stk cd (sh(sp := 0))"
  by rule (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> assm_stk cd sh sp = (Reg Env, sh sp)"
  by (simp add: assemble_stack_def)

lemma [simp]: "even (Suc (Suc sp)) \<Longrightarrow> assm_stk cd sh sp = 
    (PC, assembly_map cd (sh sp))"
  by (simp add: assemble_stack_def)

lemma [simp]: "(assemble_vals vs)(vp := (Reg Hp, y)) = assemble_vals (vs(vp := y))"
  by (auto simp add: assemble_vals_def)

lemma [simp]: "even ep \<Longrightarrow> (assemble_env e)(ep := (Reg Hp, a), Suc ep := (Reg Env, b)) = 
    assemble_env (e(ep := a, Suc ep := b))"
  by (auto simp add: assemble_env_def)

lemma [simp]: "unstr_lookup e a x = Some v \<Longrightarrow> lookup cd pc = Some (BLookup y) \<Longrightarrow> x \<le> y \<Longrightarrow> 
  pc < length cd \<Longrightarrow> iter_evala (assemble_code cd) (5 + 2 * x) 
    (AS (case_register h (assemble_env e) vs sh) (case_register hp ep vp sp) a (Reg Env)
      (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e)
        (vs(vp := (Reg Hp, v))) sh) (case_register hp ep (Suc vp) sp) 0 (Con 0) 
          (assembly_map cd pc))"
proof (induction e a x rule: unstr_lookup.induct)
  case (3 e p)
  moreover from 3 have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (ASubA 2 (Reg Env))" by simp
  moreover from 3 have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AGetA Env (Reg Hp))" by simp
  moreover from 3 have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (APutA Vals)" by (simp del: add_2_eq_Suc)
  ultimately show ?case by (simp add: numeral_def assemble_env_def split: if_splits)
next
  case (4 e p x)
  moreover hence "lookup (assemble_code cd) (6 + 2 * x + assembly_map cd pc) = 
    Some (ASubA (Suc 0) (Reg Env))" by simp
  moreover from 4 have "lookup (assemble_code cd) (5 + 2 * x + assembly_map cd pc) = 
    Some (AGetA Env (Reg Env))" by simp
  ultimately have "iter_evala (assemble_code cd) 2
    (AS (case_register h (assemble_env e) vs sh) (case_register hp ep vp sp) (Suc (Suc p)) (Reg Env)
      (7 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e) vs sh) 
        (case_register hp ep vp sp) (e (Suc p)) (Reg Env) (5 + 2 * x + assembly_map cd pc))" 
    by (simp add: numeral_def assemble_env_def split: if_splits) presburger
  moreover from 4 have "iter_evala (assemble_code cd) (5 + 2 * x) 
    (AS (case_register h (assemble_env e) vs sh) (case_register hp ep vp sp) (e (Suc p)) (Reg Env)
      (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e) 
        (vs(vp := (Reg Hp, v))) sh) (case_register hp ep (Suc vp) sp) 0 (Con 0) 
          (assembly_map cd pc))" by (simp split: if_splits)
  ultimately have "iter_evala (assemble_code cd) (2 + (5 + 2 * x))
    (AS (case_register h (assemble_env e) vs sh) (case_register hp ep vp sp) (Suc (Suc p)) (Reg Env)
      (7 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e) 
        (vs(vp := (Reg Hp, v))) sh) (case_register hp ep (Suc vp) sp) 0 (Con 0) 
          (assembly_map cd pc))" 
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
    (AS (case_register (assm_hp cd h) (assemble_env e) (assemble_vals vs) 
      (assm_stk cd sh)) (case_register hp ep vp (Suc sp)) 0 (Con 0) 
        (8 + 2 * x + assembly_map cd pc)) = Some (AS (case_register (assm_hp cd h) 
          (assemble_env e) (assemble_vals vs) (assm_stk cd sh)) 
            (case_register hp ep vp (Suc sp)) (sh sp) (Reg Env) (5 + 2 * x + assembly_map cd pc))" 
    by (simp add: numeral_def)
  moreover from evu_lookup have "iter_evala (assemble_code cd) (5 + 2 * x) 
    (AS (case_register (assm_hp cd h) (assemble_env e) (assemble_vals vs) (assm_stk cd sh)) 
      (case_register hp ep vp (Suc sp)) (sh sp) (Reg Env) (5 + 2 * x + assembly_map cd pc)) = 
        Some (AS (case_register (assm_hp cd h) (assemble_env e) (assemble_vals (vs(vp := y))) 
          (assm_stk cd sh)) (case_register hp ep (Suc vp) (Suc sp)) 0 (Con 0) (assembly_map cd pc))" 
    by simp
  ultimately have "iter_evala (assemble_code cd) (3 + (5 + 2 * x)) 
    (AS (case_register (assm_hp cd h) (assemble_env e) (assemble_vals vs) (assm_stk cd sh)) 
      (case_register hp ep vp (Suc sp)) 0 (Con 0) (8 + 2 * x + assembly_map cd pc)) = 
        Some (AS (case_register (assm_hp cd h) (assemble_env e) (assemble_vals (vs(vp := y))) 
          (assm_stk cd sh)) (case_register hp ep (Suc vp) (Suc sp)) 0 (Con 0) (assembly_map cd pc))" 
    using iter_evala_combine by blast
  hence "iter_evala (assemble_code cd) (3 + (5 + 2 * x)) 
    (AS (case_register (assm_hp cd h) (assemble_env e) (assemble_vals vs) (assm_stk cd sh)) 
      (case_register hp ep vp (Suc sp)) 0 (Con 0) (8 + (2 * x + assembly_map cd pc))) = 
        Some (AS (case_register (assm_hp cd h) (assemble_env e) (assemble_vals (vs(vp := y))) 
          (assm_stk cd sh)) (case_register hp ep (Suc vp) (Suc sp)) 0 (Con 0) (assembly_map cd pc))"
    by (metis add.assoc)
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
    Some (AAdd Hp 1)" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 8 (AS (case_register (assm_hp cd h) 
    (assemble_env e) (assemble_vals vs) (assm_stk cd sh)) (case_register hp ep vp (Suc sp)) 0 
      (Con 0) (assembly_map cd (Suc pc))) = Some (AS (case_register (assm_hp cd (h(hp := 1,
        Suc hp := k, Suc (Suc hp) := 0))) (assemble_env e) (assemble_vals (vs(vp := hp))) 
          (assm_stk cd sh)) (case_register (3 + hp) ep (Suc vp) (Suc sp)) 0 (Con 0) 
            (assembly_map cd pc))" 
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
    Some (AGetA Stk (Reg Env))" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (APut Hp (Con 0))" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd Hp 1)" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (4 + assembly_map cd pc) =
    Some (APutA Hp)" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AAdd Hp 1)" by simp
  moreover from evu_pushlam have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AMov (Con 0))" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 12 (AS (case_register (assm_hp cd h) 
    (assemble_env e) (assemble_vals vs) (assm_stk cd sh)) (case_register hp ep vp (Suc sp)) 0 
      (Con 0) (assembly_map cd (Suc pc))) = Some (AS (case_register (assm_hp cd (h(hp := 0, 
        Suc hp := sh sp, Suc (Suc hp) := pc'))) (assemble_env e) (assemble_vals (vs(vp := hp))) 
          (assm_stk cd sh)) (case_register (3 + hp) ep (Suc vp) (Suc sp)) 0 (Con 0) 
            (assembly_map cd pc))" 
    by (auto simp add: numeral_def)
  thus ?case by auto
next
  case (evu_apply cd pc h vs vp hp e ep sh sp)
  moreover hence "even ep" by auto
  moreover from evu_apply have "lookup (assemble_code cd) (21 + assembly_map cd pc) = 
    Some (ASub Vals 1)" by simp
  moreover from evu_apply have "lookup (assemble_code cd) (20 + assembly_map cd pc) = 
    Some (AGet Vals (Reg Hp))" by simp
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
    Some (AAddA 2 (Reg Hp))" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 22 (AS (case_register (assm_hp cd h) 
    (assemble_env e) (assemble_vals vs) (assm_stk cd sh)) (case_register hp ep (Suc (Suc vp)) 
      (Suc sp)) 0 (Con 0) (assembly_map cd (Suc pc))) = Some (AS (case_register (assm_hp cd h) 
        (assemble_env (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp))))) (assemble_vals vs) 
          (assm_stk cd (sh(Suc sp := pc, Suc (Suc sp) := Suc (Suc ep))))) (case_register hp 
            (Suc (Suc ep)) vp (Suc (Suc (Suc sp)))) 0 (Con 0) 
              (assembly_map cd (h (Suc (Suc (vs vp))))))"
    by (auto simp add: numeral_def assemble_vals_def)
  thus ?case by auto
next
  case (evu_return cd pc h hp e ep vs vp sh sp)
  moreover from evu_return have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (ASub Stk 2)" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 3 (AS (case_register (assm_hp cd h) 
    (assemble_env e) (assemble_vals vs) (assm_stk cd sh)) (case_register hp ep vp (Suc (Suc sp))) 0 
      (Con 0) (assembly_map cd (Suc pc))) = Some (AS (case_register (assm_hp cd h) (assemble_env e) 
        (assemble_vals vs) (assm_stk cd sh)) (case_register hp ep vp sp) 0 (Con 0)
          (assembly_map cd (sh sp)))"
    by (simp add: numeral_def)
  thus ?case by auto
next
  case (evu_jump cd pc h vs vp hp e ep sh sp)
  moreover hence "even ep" by auto
  moreover from evu_jump have "lookup (assemble_code cd) (18 + assembly_map cd pc) = 
    Some (ASub Vals 1)" by simp
  moreover from evu_jump have "lookup (assemble_code cd) (17 + assembly_map cd pc) = 
    Some (AGet Vals (Reg Hp))" by simp
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
    Some (AAddA 2 (Reg Hp))" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 19 (AS (case_register (assm_hp cd h) 
    (assemble_env e) (assemble_vals vs) (assm_stk cd sh)) (case_register hp ep (Suc (Suc vp)) 
      (Suc sp)) 0 (Con 0) (assembly_map cd (Suc pc))) = Some (AS (case_register (assm_hp cd h) 
        (assemble_env (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp))))) (assemble_vals vs) 
          (assm_stk cd (sh(sp := Suc (Suc ep))))) (case_register hp (Suc (Suc ep)) vp (Suc sp)) 0 
            (Con 0) (assembly_map cd (h (Suc (Suc (vs vp))))))" 
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

end