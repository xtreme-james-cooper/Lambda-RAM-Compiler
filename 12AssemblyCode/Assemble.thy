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
    APut Vals (Acc (Reg Hp)),
    AGet (Acc (Reg Env)),
    ASub (Acc (Reg Env)) 2] @
    concat (replicate x [
    AGet (Acc (Reg Env)),
    ASub (Acc (Reg Env)) 1]) @ [
    AGet (Acc (Reg Stk)),
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
    APut Hp (Acc (Reg Env)),
    AAdd (Reg Hp) 1, 
    APut Hp (Con 0),
    AGet (Acc (Reg Stk)), 
    ASub (Acc (Reg Stk)) 1,
    AMov (Reg Stk),
    AAdd (Reg Vals) 1,
    APut Vals (Reg Hp)]"
| "assemble_op mp Apply\<^sub>b = [
    AJmp,
    AGet (Acc (Reg Hp)),
    AAdd (Acc (Reg Hp)) 2,
    APut Vals (Con 0),
    AGet (Reg Vals),
    AAdd (Reg Env) 1,
    APut Env (Acc (Reg Env)),
    AGet (Acc (Reg Hp)),
    AAdd (Acc (Reg Hp)) 1,
    AGet (Reg Vals),
    ASub (Reg Vals) 1,
    AAdd (Reg Stk) 1,
    APut Stk (Acc (Reg Env)),
    AAdd (Acc (Reg Env)) 1,
    AMov (Reg Env),
    AAdd (Reg Stk) 1,
    APut Stk (Acc (PC 0)),
    ASub (Acc (PC 0)) 18,
    AMov (PC 0),
    AAdd (Reg Env) 1,
    APut Env (Acc (Reg Hp)),
    APut Vals (Con 0),
    AGet (Reg Vals),
    ASub (Reg Vals) 1]"
| "assemble_op mp Return\<^sub>b = [
    AJmp,
    APut Stk (Con 0),
    AGet (Reg Stk),
    ASub (Reg Stk) 1,
    APut Stk (Con 0),
    ASub (Reg Stk) 1]"
| "assemble_op mp Jump\<^sub>b = [
    AJmp,
    AGet (Acc (Reg Hp)),
    AAdd (Acc (Reg Hp)) 2,
    APut Vals (Con 0),
    AGet (Reg Vals),
    AAdd (Reg Env) 1,
    APut Env (Acc (Reg Env)),
    AGet (Acc (Reg Hp)),
    AAdd (Acc (Reg Hp)) 1,
    AGet (Reg Vals),
    ASub (Reg Vals) 1,
    AAdd (Reg Stk) 1,
    APut Stk (Acc (Reg Env)),
    ASub (Reg Stk) 1,
    AAdd (Acc (Reg Env)) 1,
    AMov (Reg Env),
    AAdd (Reg Env) 1,
    APut Env (Acc (Reg Hp)),
    APut Vals (Con 0),
    AGet (Reg Vals),
    ASub (Reg Vals) 1]"

fun assembly_map :: "code\<^sub>b list \<Rightarrow> nat \<Rightarrow> nat" where
  "assembly_map [] x = 0"
| "assembly_map (op # cd) 0 = 0"
| "assembly_map (op # cd) (Suc x) = Suc (assemble_op_len op + assembly_map cd x)"

definition assemble_code :: "code\<^sub>b list \<Rightarrow> assm list" where
  "assemble_code cd = concat (map (assemble_op (assembly_map cd)) cd)"

definition assemble_heap :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> pointer_tag \<times> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
    register option \<times> nat" where
  "assemble_heap mp h hp x = (if x \<ge> hp then (None, 0) else case x mod 3 of
      0 \<Rightarrow> (None, snd (h x))
    | Suc 0 \<Rightarrow> (if snd (h (x - 1)) = 0 then Some Env else None, snd (h x))
    | Suc (Suc 0) \<Rightarrow> if snd (h (x - 2)) = 0 then (None, mp (snd (h x))) else (None, snd (h x)))"

definition assemble_env :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> register option \<times> nat" where
  "assemble_env e ep x = (if x \<ge> ep then (None, 0) else (Some (if even x then Hp else Env), e x))"

definition assemble_vals :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> register option \<times> nat" where
  "assemble_vals vs vp x = (if x \<ge> vp then (None, 0) else (Some Hp, vs x))"

definition assemble_stack :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> register option \<times> nat" where
  "assemble_stack mp s sp x = (
    if x \<ge> sp then (None, 0) else if even x then (None, mp (s x)) else (Some Env, s x))"

primrec assemble_state :: "(nat \<Rightarrow> nat) \<Rightarrow> unstr_state \<Rightarrow> assm_state" where
  "assemble_state mp (S\<^sub>u h hp e ep vs vp sh sp pc) = 
    AS (case_register (assemble_heap mp h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assemble_stack mp sh sp)) (case_register hp ep vp sp) 0 None (mp pc)"

abbreviation assm_hp :: "code\<^sub>b list \<Rightarrow> (nat \<Rightarrow> pointer_tag \<times> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
    register option \<times> nat" where
  "assm_hp cd \<equiv> assemble_heap (assembly_map cd)"

abbreviation assm_stk :: "code\<^sub>b list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> register option \<times> nat" where
  "assm_stk cd \<equiv> assemble_stack (assembly_map cd)"

abbreviation assm_state :: "code\<^sub>b list \<Rightarrow> unstr_state \<Rightarrow> assm_state" where
  "assm_state cd \<equiv> assemble_state (assembly_map cd)"

lemma length_assemble_op [simp]: "length (assemble_op mp op) = Suc (assemble_op_len op)"
  by (induction op) simp_all

lemma [simp]: "length \<circ> assemble_op mp = Suc \<circ> assemble_op_len"
  by auto

lemma [simp]: "assembly_map cd 0 = 0"
  by (induction cd) simp_all

lemma assembly_map_postpend [simp]: "
    assembly_map (cd @ cd') (length cd) = assembly_map cd (length cd)"
  by (induction cd) simp_all

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

lemma assm_hp_lemma1: "3 dvd x \<Longrightarrow> x < hp \<Longrightarrow> assemble_heap mp h hp x = (None, snd (h x))"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma2: "x mod 3 = 1 \<Longrightarrow> snd (h (x - 1)) \<noteq> 0 \<Longrightarrow> x < hp \<Longrightarrow> 
    assemble_heap mp h hp x = (None, snd (h x))"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma3: "x mod 3 = 1 \<Longrightarrow> snd (h (x - 1)) = 0 \<Longrightarrow> x < hp \<Longrightarrow>
    assemble_heap mp h hp x = (Some Env, snd (h x))"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma4: "x mod 3 = 2 \<Longrightarrow> snd (h (x - 2)) \<noteq> 0 \<Longrightarrow> x < hp \<Longrightarrow> 
    assemble_heap mp h hp x = (None, snd (h x))"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma5: "x mod 3 = 2 \<Longrightarrow> snd (h (x - 2)) = 0 \<Longrightarrow> x < hp \<Longrightarrow> 
    assemble_heap mp h hp x = (None, mp (snd (h x)))"
  by (simp add: assemble_heap_def)

lemma [simp]: "x \<noteq> hp \<Longrightarrow> assm_hp cd (h(hp := a)) (Suc hp) x = assm_hp cd h hp x"
  by (induction x rule: x_mod_3_induct) (simp_all add: assemble_heap_def, linarith+)

lemma [simp]: "restructurable_heap h hp ep (length cd) \<Longrightarrow> (assm_hp cd h hp)
  (hp := (None, Suc a), Suc hp := (None, b), Suc (Suc hp) := (None, c)) = 
    assm_hp cd (h(hp := (PConst, Suc a), Suc hp := (PConst, b), Suc (Suc hp) := (PConst, c))) 
      (Suc (Suc (Suc hp)))"
proof
  fix x
  assume "restructurable_heap h hp ep (length cd)"
  hence "3 dvd hp" by (simp add: restructurable_heap_def)
  moreover hence "Suc hp mod 3 = 1" by presburger
  moreover hence "Suc (Suc hp) mod 3 = 2" by presburger
  ultimately show "((assm_hp cd h hp)
    (hp := (None, Suc a), Suc hp := (None, b), Suc (Suc hp) := (None, c))) x =
      assm_hp cd (h(hp := (PConst, Suc a), Suc hp := (PConst, b), Suc (Suc hp) := (PConst, c))) 
        (Suc (Suc (Suc hp))) x" 
    by (simp add: assm_hp_lemma1 assm_hp_lemma2 assm_hp_lemma3 assm_hp_lemma4 assm_hp_lemma5)
qed

lemma [simp]: "restructurable_heap h hp ep (length cd) \<Longrightarrow> (assm_hp cd h hp)
  (hp := (None, 0), Suc hp := (Some Env, a), Suc (Suc hp) := (None, assembly_map cd b)) = 
    assm_hp cd (h(hp := (PConst, 0), Suc hp := (PEnv, a), Suc (Suc hp) := (PCode, b))) 
      (Suc (Suc (Suc hp)))"
proof
  fix x
  assume "restructurable_heap h hp ep (length cd)"
  hence H: "3 dvd hp" by (simp add: restructurable_heap_def)
  moreover hence "Suc hp mod 3 = 1" by presburger
  moreover hence "Suc (Suc hp) mod 3 = 2" by presburger
  ultimately show "((assm_hp cd h hp)(hp := (None, 0), Suc hp := (Some Env, a), 
    Suc (Suc hp) := (None, assembly_map cd b))) x =
      assm_hp cd (h(hp := (PConst, 0), Suc hp := (PEnv, a), Suc (Suc hp) := (PCode, b))) 
        (Suc (Suc (Suc hp))) x" 
    by (simp add: assm_hp_lemma1 assm_hp_lemma2 assm_hp_lemma3 assm_hp_lemma4 assm_hp_lemma5)
qed

lemma [simp]: "restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> 
  assemble_heap mp h hp (Suc (vs vp)) = 
    (if snd (h (vs vp)) = 0 then Some Env else None, snd (h (Suc (vs vp))))"
proof (unfold assemble_heap_def restructurable_vals_def)
  assume "3 dvd hp \<and> (\<forall>x<Suc (Suc vp). 3 dvd vs x \<and> vs x < hp)"
  moreover hence X: "3 dvd vs vp \<and> vs vp < hp" by simp
  ultimately have "Suc (vs vp) < hp" by fastforce
  moreover from X have "Suc (vs vp) mod 3 = 1" by presburger
  ultimately show "(if Suc (vs vp) \<ge> hp then (None, 0) else case Suc (vs vp) mod 3 of 
       0 \<Rightarrow> (None, snd (h (Suc (vs vp))))
     | Suc 0 \<Rightarrow> (if snd (h (Suc (vs vp) - 1)) = 0 then Some Env else None, snd (h (Suc (vs vp))))
     | Suc (Suc 0) \<Rightarrow> if snd (h (Suc (vs vp) - 2)) = 0 then (None, mp (snd (h (Suc (vs vp))))) 
        else (None, snd (h (Suc (vs vp))))
     | Suc (Suc (Suc x)) \<Rightarrow> undefined) = (if snd (h (vs vp)) = 0 then Some Env 
        else None, snd (h (Suc (vs vp))))" 
    by simp
qed

lemma [simp]: "restructurable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> snd (h (vs vp)) = 0 \<Longrightarrow> 
  restructurable_heap h hp ep lcd \<Longrightarrow>
    assemble_heap mp h hp (Suc (Suc (vs vp))) = (None, mp (snd (h (Suc (Suc (vs vp))))))"
proof (unfold assemble_heap_def restructurable_vals_def)
  assume "3 dvd hp \<and> (\<forall>x<Suc (Suc vp). 3 dvd vs x \<and> vs x < hp)"
  hence "3 dvd vs vp \<and> vs vp < hp" by simp
  moreover assume "restructurable_heap h hp ep lcd"
  moreover hence "3 dvd hp" by auto
  ultimately have "Suc (Suc (vs vp)) mod 3 = 2 \<and> Suc (Suc (vs vp)) < hp" by presburger
  moreover assume "snd (h (vs vp)) = 0"
  ultimately show "(if (Suc (Suc (vs vp))) \<ge> hp then (None, 0) else case Suc (Suc (vs vp)) mod 3 of 
       0 \<Rightarrow> (None, snd (h (Suc (Suc (vs vp)))))
     | Suc 0 \<Rightarrow> (if snd (h (Suc (Suc (vs vp)) - 1)) = 0 then Some Env 
        else None, snd (h (Suc (Suc (vs vp)))))
     | Suc (Suc 0) \<Rightarrow>
         if snd (h (Suc (Suc (vs vp)) - 2)) = 0 then (None, mp (snd (h (Suc (Suc (vs vp))))))
        else (None, snd (h (Suc (Suc (vs vp)))))
     | Suc (Suc (Suc x)) \<Rightarrow> undefined) = (None, mp (snd (h (Suc (Suc (vs vp))))))" 
    by simp
qed

lemma [simp]: "Suc (Suc (vs vp)) mod 3 \<noteq> Suc (Suc (Suc x))" 
  by simp

lemma [simp]: "snd (h (vs vp)) = Suc x \<Longrightarrow> vs vp mod 3 = 0 \<Longrightarrow> Suc (Suc (vs vp)) < hp \<Longrightarrow>
    assemble_heap mp h hp (Suc (Suc (vs vp))) = (None, snd (h (Suc (Suc (vs vp)))))"
  by (simp add: assemble_heap_def split: nat.splits) presburger

lemma [simp]: "even sp \<Longrightarrow> 
  (assm_stk cd sh sp)(sp := (None, assembly_map cd pc), Suc sp := (Some Env, a)) = 
    (assm_stk cd (sh(sp := pc, Suc sp := a)) (Suc (Suc sp)))"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> 
    (assm_stk cd sh (Suc sp))(sp := (Some Env, k)) = assm_stk cd (sh(sp := k)) (Suc sp)"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> assm_stk cd sh (Suc sp) sp = (Some Env, sh sp)"
  by (simp add: assemble_stack_def)

lemma [simp]: "even (Suc (Suc sp)) \<Longrightarrow> assm_stk cd sh (Suc sp) sp = 
    (None, assembly_map cd (sh sp))"
  by (simp add: assemble_stack_def)

lemma [simp]: "(assm_stk cd sh (Suc sp))(sp := (None, 0)) = assm_stk cd sh sp"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "(assemble_vals vs vp)(vp := (Some Hp, y)) = assemble_vals (vs(vp := y)) (Suc vp)"
  by (auto simp add: assemble_vals_def)

lemma [simp]: "(assemble_vals vs (Suc vp))(vp := (None, 0)) = assemble_vals vs vp"
  by rule (simp add: assemble_vals_def)

lemma [simp]: "even ep \<Longrightarrow> (assemble_env e ep)(ep := (Some Hp, a), Suc ep := (Some Env, b)) = 
    assemble_env (e(ep := a, Suc ep := b)) (Suc (Suc ep))"
  by (auto simp add: assemble_env_def)

lemma [simp]: "unstr_lookup e a x = Some v \<Longrightarrow> lookup cd pc = Some (Lookup\<^sub>b y) \<Longrightarrow> x \<le> y \<Longrightarrow> 
  pc < length cd \<Longrightarrow> a \<le> ep \<Longrightarrow> restructurable_env e ep hp \<Longrightarrow> iter_evala (assemble_code cd) 
    (5 + 2 * x) (AS (case_register h (assemble_env e ep) vs sh) (case_register hp ep vp sp) a 
      (Some Env) (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e ep)
        (vs(vp := (Some Hp, v))) sh) (case_register hp ep (Suc vp) sp) 0 None
          (assembly_map cd pc))"
proof (induction e a x rule: unstr_lookup.induct)
  case (3 e p)
  moreover from 3 have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (ASub (Acc (Reg Env)) 2)" by simp
  moreover from 3 have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AGet (Acc (Reg Env)))" by simp
  moreover from 3 have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (APut Vals (Acc (Reg Hp)))" by (simp del: add_2_eq_Suc)
  ultimately show ?case by (simp add: numeral_def assemble_env_def split: if_splits)
next
  case (4 e p x)
  moreover hence "lookup (assemble_code cd) (6 + 2 * x + assembly_map cd pc) = 
    Some (ASub (Acc (Reg Env)) (Suc 0))" by simp
  moreover from 4 have "lookup (assemble_code cd) (5 + 2 * x + assembly_map cd pc) = 
    Some (AGet (Acc (Reg Env)))" by simp
  ultimately have X: "iter_evala (assemble_code cd) 2 (AS (case_register h (assemble_env e ep) vs 
    sh) (case_register hp ep vp sp) (Suc (Suc p)) (Some Env)
      (7 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e ep) vs sh) 
        (case_register hp ep vp sp) (e (Suc p)) (Some Env) (5 + 2 * x + assembly_map cd pc))" 
    by (simp add: numeral_def assemble_env_def split: if_splits) presburger
  from 4 have "Suc p < ep" and "even p" and "restructurable_env e ep hp" by (auto split: if_splits)
  hence "e (Suc p) < ep" by (auto split: if_splits)
  moreover with 4 have "iter_evala (assemble_code cd) (5 + 2 * x)
    (AS (case_register h (assemble_env e ep) vs sh) (case_register hp ep vp sp) (e (Suc p)) (Some Env)
      (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e ep) 
        (vs(vp := (Some Hp, v))) sh) (case_register hp ep (Suc vp) sp) 0 None
          (assembly_map cd pc))" by (simp split: if_splits)
  with X have "iter_evala (assemble_code cd) (2 + (5 + 2 * x))
    (AS (case_register h (assemble_env e ep) vs sh) (case_register hp ep vp sp) (Suc (Suc p)) (
      Some Env) (7 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e ep) 
        (vs(vp := (Some Hp, v))) sh) (case_register hp ep (Suc vp) sp) 0 None
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
    Some (AGet (Acc (Reg Stk)))" by simp
  ultimately have X: "iter_evala (assemble_code cd) 3 
    (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp))) (case_register hp ep vp (Suc sp)) 0 None
        (8 + 2 * x + assembly_map cd pc)) = Some (AS (case_register (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc sp))) 
            (case_register hp ep vp (Suc sp)) (sh sp) (Some Env) (5 + 2 * x + assembly_map cd pc))" 
    by (simp add: numeral_def)
  from ev\<^sub>u_lookup have "sh sp \<le> ep" by auto
  with ev\<^sub>u_lookup have "iter_evala (assemble_code cd) (5 + 2 * x) 
    (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp))) (case_register hp ep vp (Suc sp)) (sh sp) (Some Env) 
        (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals (vs(vp := y)) (Suc vp)) (assm_stk cd sh (Suc sp))) 
            (case_register hp ep (Suc vp) (Suc sp)) 0 None (assembly_map cd pc))" 
    by simp
  with X have "iter_evala (assemble_code cd) (3 + (5 + 2 * x)) 
    (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp))) (case_register hp ep vp (Suc sp)) 0 None
        (8 + 2 * x + assembly_map cd pc)) = Some (AS (case_register (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals (vs(vp := y)) (Suc vp)) (assm_stk cd sh (Suc sp))) 
            (case_register hp ep (Suc vp) (Suc sp)) 0 None (assembly_map cd pc))" 
    using iter_evala_combine by blast
  hence "iter_evala (assemble_code cd) (3 + (5 + 2 * x)) 
    (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp))) (case_register hp ep vp (Suc sp)) 0 None
        (8 + (2 * x + assembly_map cd pc))) = Some (AS (case_register (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals (vs(vp := y)) (Suc vp)) (assm_stk cd sh (Suc sp))) 
            (case_register hp ep (Suc vp) (Suc sp)) 0 None (assembly_map cd pc))"
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
      (case_register hp ep vp (Suc sp)) 0 None (assembly_map cd (Suc pc))) = Some (AS 
        (case_register (assm_hp cd (h(hp := (PConst, Suc 0), Suc hp := (PConst, k), 
          Suc (Suc hp) := (PConst, 0))) (3 + hp)) (assemble_env e ep) (assemble_vals (vs(vp := hp)) 
            (Suc vp)) (assm_stk cd sh (Suc sp))) (case_register (3 + hp) ep (Suc vp) (Suc sp)) 0 
              None (assembly_map cd pc))" 
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
    Some (AGet (Acc (Reg Stk)))" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (APut Hp (Con 0))" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd (Reg Hp) 1)" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (4 + assembly_map cd pc) =
    Some (APut Hp (Acc (Reg Env)))" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AAdd (Reg Hp) 1)" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AMov (Con 0))" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 12 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc sp))) 
      (case_register hp ep vp (Suc sp)) 0 None (assembly_map cd (Suc pc))) = Some (AS 
        (case_register (assm_hp cd (h(hp := (PConst, 0), Suc hp := (PEnv, sh sp), 
          Suc (Suc hp) := (PCode, pc'))) (3 + hp)) (assemble_env e ep) (assemble_vals (vs(vp := hp)) 
            (Suc vp)) (assm_stk cd sh (Suc sp))) (case_register (3 + hp) ep (Suc vp) (Suc sp)) 0 
              None (assembly_map cd pc))" 
    by (auto simp add: numeral_def)
  thus ?case by auto
next
  case (ev\<^sub>u_apply cd pc h vs vp hp e ep sh sp)
  moreover hence "even ep" by auto
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (23 + assembly_map cd pc) = 
    Some (ASub (Reg Vals) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (22 + assembly_map cd pc) = 
    Some (AGet (Reg Vals))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (21 + assembly_map cd pc) = 
    Some (APut Vals (Con 0))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (20 + assembly_map cd pc) = 
    Some (APut Env (Acc (Reg Hp)))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (19 + assembly_map cd pc) = 
    Some (AAdd (Reg Env) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (18 + assembly_map cd pc) = 
    Some (AMov (PC 0))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (17 + assembly_map cd pc) = 
    Some (ASub (Acc (PC 0)) 18)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (16 + assembly_map cd pc) = 
    Some (APut Stk (Acc (PC 0)))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (15 + assembly_map cd pc) = 
    Some (AAdd (Reg Stk) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (14 + assembly_map cd pc) = 
    Some (AMov (Reg Env))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (13 + assembly_map cd pc) = 
    Some (AAdd (Acc (Reg Env)) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (12 + assembly_map cd pc) = 
    Some (APut Stk (Acc (Reg Env)))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (11 + assembly_map cd pc) = 
    Some (AAdd (Reg Stk) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (10 + assembly_map cd pc) = 
    Some (ASub (Reg Vals) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (AGet (Reg Vals))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (AAdd (Acc (Reg Hp)) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AGet (Acc (Reg Hp)))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (APut Env (Acc (Reg Env)))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd (Reg Env) 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AGet (Reg Vals))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (APut Vals (Con 0))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAdd (Acc (Reg Hp)) 2)" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 24 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs (Suc (Suc vp))) (assm_stk cd sh (Suc sp))) 
      (case_register hp ep (Suc (Suc vp)) (Suc sp)) 0 None (assembly_map cd (Suc pc))) = 
        Some (AS (case_register (assm_hp cd h hp) (assemble_env (e(ep := vs (Suc vp), 
          Suc ep := snd (h (Suc (vs vp))))) (Suc (Suc ep))) (assemble_vals vs vp) 
            (assm_stk cd (sh(Suc sp := pc, Suc (Suc sp) := Suc (Suc ep))) (Suc (Suc (Suc sp))))) 
              (case_register hp (Suc (Suc ep)) vp (Suc (Suc (Suc sp)))) 0 None
                (assembly_map cd (snd (h (Suc (Suc (vs vp)))))))"
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
    Some (AGet (Reg Stk))" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 6 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc (Suc sp)))) 
      (case_register hp ep vp (Suc (Suc sp))) 0 None (assembly_map cd (Suc pc))) = 
        Some (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
          (assm_stk cd sh sp)) (case_register hp ep vp sp) 0 None (assembly_map cd (sh sp)))"
    by (simp add: numeral_def split: prod.splits)
  thus ?case by auto
next
  case (ev\<^sub>u_jump cd pc h vs vp hp e ep sh sp)
  moreover hence "even ep" by auto
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (20 + assembly_map cd pc) = 
    Some (ASub (Reg Vals) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (19 + assembly_map cd pc) = 
    Some (AGet (Reg Vals))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (18 + assembly_map cd pc) = 
    Some (APut Vals (Con 0))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (17 + assembly_map cd pc) = 
    Some (APut Env (Acc (Reg Hp)))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (16 + assembly_map cd pc) = 
    Some (AAdd (Reg Env) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (15 + assembly_map cd pc) = 
    Some (AMov (Reg Env))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (14 + assembly_map cd pc) = 
    Some (AAdd (Acc (Reg Env)) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (13 + assembly_map cd pc) = 
    Some (ASub (Reg Stk) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (12 + assembly_map cd pc) = 
    Some (APut Stk (Acc (Reg Env)))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (11 + assembly_map cd pc) =
    Some (AAdd (Reg Stk) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (10 + assembly_map cd pc) = 
    Some (ASub (Reg Vals) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (AGet (Reg Vals))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (AAdd (Acc (Reg Hp)) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AGet (Acc (Reg Hp)))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (APut Env (Acc (Reg Env)))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd (Reg Env) 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AGet (Reg Vals))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (APut Vals (Con 0))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAdd (Acc (Reg Hp)) 2)" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 21 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs (Suc (Suc vp))) (assm_stk cd sh (Suc sp))) 
      (case_register hp ep (Suc (Suc vp)) (Suc sp)) 0 None (assembly_map cd (Suc pc))) = 
        Some (AS (case_register (assm_hp cd h hp) (assemble_env (e(ep := vs (Suc vp), 
          Suc ep := snd (h (Suc (vs vp))))) (Suc (Suc ep))) (assemble_vals vs vp) 
            (assm_stk cd (sh(sp := Suc (Suc ep))) (Suc sp))) (case_register hp 
              (Suc (Suc ep)) vp (Suc sp)) 0 None (assembly_map cd (snd (h (Suc (Suc (vs vp)))))))"
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

theorem correct\<^sub>a_iter [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow> 
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

lemma [simp]: "assm_hp cd h 0 = (\<lambda>x. (None, 0))"
  by rule (simp add: assemble_heap_def)

lemma [simp]: "assemble_env e 0 = (\<lambda>x. (None, 0))"
  by rule (simp add: assemble_env_def)

lemma [simp]: "assemble_vals vs 0 = (\<lambda>x. (None, 0))"
  by rule (simp add: assemble_vals_def)

lemma [simp]: "assm_stk cd (mp(0 := a, Suc 0 := b)) 2 = 
    (\<lambda>x. (None, 0))(0 := (None, assembly_map cd a), Suc 0 := (Some Env, b))"
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