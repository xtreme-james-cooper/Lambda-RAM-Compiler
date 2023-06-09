theory Assemble
  imports AssemblyCode "../11UnstructuredState/UnstructuredState" "../00Utils/Utils"
    "../07ByteCode/CodeFlattening"
begin

primrec assemble_op_len :: "code\<^sub>b \<Rightarrow> nat" where
  "assemble_op_len (Lookup\<^sub>b x) = 7 + 2 * x"
| "assemble_op_len (PushCon\<^sub>b k) = 7"
| "assemble_op_len (PushLam\<^sub>b pc) = 11"
| "assemble_op_len Apply\<^sub>b = 21"
| "assemble_op_len Return\<^sub>b = 5"
| "assemble_op_len Jump\<^sub>b = 20"

primrec assemble_op :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> code\<^sub>b \<Rightarrow> assm list" where
  "assemble_op mp ix (Lookup\<^sub>b x) = [
    APut Acc (Con 0),
    AAdd Vals 1,
    APut Vals (Reg Acc),
    AGet Acc,
    ASub Acc 2] @
    concat (replicate x [
    AGet Acc,
    ASub Acc 1]) @ [
    AGet Acc,
    ASub Acc 1,
    APut Acc (Reg Stk)]"
| "assemble_op mp ix (PushCon\<^sub>b k) = [
    AAdd Hp 1, 
    APut Hp (Reg Acc),
    AAdd Hp 1,  
    APut Hp (Con k),
    AAdd Hp 1,  
    APut Hp (Con 1), 
    AAdd Vals 1,
    APut Vals (Reg Hp)]"
| "assemble_op mp ix (PushLam\<^sub>b pc) = [
    AAdd Hp 1, 
    APut Hp (Con (mp pc)), 
    APut Acc (Con 0),
    AAdd Hp 1, 
    APut Hp (Reg Acc),
    AAdd Hp 1, 
    APut Hp (Con 0),
    AGet Acc, 
    ASub Acc 1,
    APut Acc (Reg Stk),
    AAdd Vals 1,
    APut Vals (Reg Hp)]"
| "assemble_op mp ix Apply\<^sub>b = [
    AJmp,
    AGet Acc,
    AAdd Acc 2,
    APut Vals (Con 0),
    AGet Vals,
    AAdd Env 1,
    APut Env (Reg Acc),
    AGet Acc,
    AAdd Acc 1,
    AGet Vals,
    ASub Vals 1,
    AAdd Stk 1,
    APut Stk (Reg Acc),
    AAdd Acc 1,
    APut Acc (Reg Env),
    AAdd Stk 1,
    APut Stk (Con (mp ix)),
    AAdd Env 1,
    APut Env (Reg Acc),
    APut Vals (Con 0),
    AGet Vals,
    ASub Vals 1]"
| "assemble_op mp ix Return\<^sub>b = [
    AJmp,
    APut Stk (Con 0),
    AGet Stk,
    ASub Stk 1,
    APut Stk (Con 0),
    ASub Stk 1]"
| "assemble_op mp ix Jump\<^sub>b = [
    AJmp,
    AGet Acc,
    AAdd Acc 2,
    APut Vals (Con 0),
    AGet Vals,
    AAdd Env 1,
    APut Env (Reg Acc),
    AGet Acc,
    AAdd Acc 1,
    AGet Vals,
    ASub Vals 1,
    AAdd Stk 1,
    APut Stk (Reg Acc),
    ASub Stk 1,
    AAdd Acc 1,
    APut Acc (Reg Env),
    AAdd Env 1,
    APut Env (Reg Acc),
    APut Vals (Con 0),
    AGet Vals,
    ASub Vals 1]"

fun assembly_map :: "code\<^sub>b list \<Rightarrow> nat \<Rightarrow> nat" where
  "assembly_map [] x = 0"
| "assembly_map (op # cd) 0 = 0"
| "assembly_map (op # cd) (Suc x) = Suc (assemble_op_len op + assembly_map cd x)"

definition assemble_code :: "code\<^sub>b list \<Rightarrow> assm list" where
  "assemble_code cd = concat (map_with_idx (assemble_op (assembly_map cd)) cd)"

definition assemble_heap :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> pointer_tag \<times> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
    register \<times> nat" where
  "assemble_heap mp h hp x = (if x \<ge> hp then (Acc, 0) else case x mod 3 of
      0 \<Rightarrow> (Acc, snd (h x))
    | Suc 0 \<Rightarrow> (if snd (h (x - 1)) = 0 then Env else Acc, snd (h x))
    | Suc (Suc 0) \<Rightarrow> if snd (h (x - 2)) = 0 then (Acc, mp (snd (h x))) else (Acc, snd (h x)))"

definition assemble_env :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> register \<times> nat" where
  "assemble_env e ep x = (if x \<ge> ep then (Acc, 0) else (if even x then Hp else Env, e x))"

definition assemble_vals :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> register \<times> nat" where
  "assemble_vals vs vp x = (if x \<ge> vp then (Acc, 0) else (Hp, vs x))"

definition assemble_stack :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> register \<times> nat" where
  "assemble_stack mp s sp x = (
    if x \<ge> sp then (Acc, 0) else if even x then (Acc, mp (s x)) else (Env, s x))"

primrec assemble_state :: "(nat \<Rightarrow> nat) \<Rightarrow> unstr_state \<Rightarrow> assm_state" where
  "assemble_state mp (S\<^sub>u h hp e ep vs vp sh sp pc) = 
    AS (case_register (assemble_heap mp h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assemble_stack mp sh sp) undefined) (case_register hp ep vp sp 0) Acc (mp pc)"
                                     
abbreviation assm_hp :: "code\<^sub>b list \<Rightarrow> (nat \<Rightarrow> pointer_tag \<times> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> register \<times> nat" 
    where
  "assm_hp cd \<equiv> assemble_heap (assembly_map cd)"

abbreviation assm_stk :: "code\<^sub>b list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> register \<times> nat" where
  "assm_stk cd \<equiv> assemble_stack (assembly_map cd)"

abbreviation assm_state :: "code\<^sub>b list \<Rightarrow> unstr_state \<Rightarrow> assm_state" where
  "assm_state cd \<equiv> assemble_state (assembly_map cd)"

lemma length_assemble_op [simp]: "length (assemble_op mp ix op) = Suc (assemble_op_len op)"
  by (induction op) simp_all

lemma [simp]: "length \<circ> assemble_op mp ix = Suc \<circ> assemble_op_len"
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

lemma [simp]: "lookup (assemble_op mp ix op @ cd) (Suc (assemble_op_len op + x)) = lookup cd x"
proof -
  have "lookup (assemble_op mp ix op @ cd) (length (assemble_op mp ix op) + x) = lookup cd x" 
    by (metis lookup_append_snd)
  thus ?thesis by simp
qed

lemma assemble_code_lookup'' [simp]: "lookup cd pc = Some op \<Longrightarrow> x \<le> assemble_op_len op \<Longrightarrow> 
  lookup (concat (map_with_idx (assemble_op (assembly_map (cd' @ cd)) \<circ> (+) k) cd)) (x + assembly_map cd pc) = 
    lookup (assemble_op (assembly_map (cd' @ cd)) (pc + k) op) x"
proof (induction cd pc arbitrary: cd' k rule: assembly_map.induct)
  case (3 op' cd y)
  moreover hence "lookup cd y = Some op" by simp
  ultimately have "lookup (concat (map_with_idx (assemble_op (assembly_map ((cd' @ [op']) @ cd)) \<circ> 
    (+) (Suc k)) cd)) (x + assembly_map cd y) =
      lookup (assemble_op (assembly_map ((cd' @ [op']) @ cd)) (y + Suc k) op) x" by blast
  hence "lookup (concat (map_with_idx (assemble_op (assembly_map (cd' @ op' # cd)) \<circ> (+) (Suc k)) cd))
    (x + assembly_map cd y) =
      lookup (assemble_op (assembly_map (cd' @ op' # cd)) (Suc (y + k)) op) x" by simp
  moreover have "assemble_op (assembly_map (cd' @ op' # cd)) \<circ> (+) (Suc k) = 
    (\<lambda>z. assemble_op (assembly_map (cd' @ op' # cd)) (Suc (k + z)))" by auto
  ultimately have "lookup (assemble_op (assembly_map (cd' @ op' # cd)) k op' @
      concat (map_with_idx (\<lambda>z. assemble_op (assembly_map (cd' @ op' # cd)) (Suc (k + z))) cd))
     (assemble_op_len op' + (Suc (x + assembly_map cd y))) =
    lookup (assemble_op (assembly_map (cd' @ op' # cd)) (Suc (y + k)) op) x" by simp
  moreover have "assemble_op_len op' + (Suc (x + assembly_map cd y)) = 
    Suc (x + (assemble_op_len op' + assembly_map cd y))" by simp
  ultimately have "lookup (assemble_op (assembly_map (cd' @ op' # cd)) k op' @
      concat (map_with_idx (\<lambda>z. assemble_op (assembly_map (cd' @ op' # cd)) (Suc (k + z))) cd))
     (Suc (x + (assemble_op_len op' + assembly_map cd y))) =
    lookup (assemble_op (assembly_map (cd' @ op' # cd)) (Suc (y + k)) op) x"
    by metis
  thus ?case by simp
qed simp_all

lemma assemble_code_lookup' [simp]: "lookup cd pc = Some op \<Longrightarrow> x \<le> assemble_op_len op \<Longrightarrow> 
  lookup (concat (map_with_idx (assemble_op (assembly_map (cd' @ cd))) cd)) (x + assembly_map cd pc) = 
    lookup (assemble_op (assembly_map (cd' @ cd)) pc op) x"
proof -
  assume "lookup cd pc = Some op" and "x \<le> assemble_op_len op"
  hence "lookup (concat (map_with_idx (assemble_op (assembly_map (cd' @ cd)) \<circ> (+) 0) cd)) (x + assembly_map cd pc) = 
    lookup (assemble_op (assembly_map (cd' @ cd)) (pc + 0) op) x" 
    by (metis assemble_code_lookup'')
  thus ?thesis by simp
qed

lemma assemble_code_lookup [simp]: "lookup cd pc = Some op \<Longrightarrow> 
  x \<le> assemble_op_len op \<Longrightarrow> lookup (assemble_code cd) (x + assembly_map cd pc) = 
    lookup (assemble_op (assembly_map cd) pc op) x"
  by (metis assemble_code_lookup' append_Nil assemble_code_def)

lemma [simp]: "lookup cd pc = Some op \<Longrightarrow> 1 \<le> assemble_op_len op \<Longrightarrow> 
  lookup (assemble_code cd) (Suc (assembly_map cd pc)) = 
    lookup (assemble_op (assembly_map cd) pc op) 1"
  using assemble_code_lookup by fastforce

lemma [simp]: "lookup cd pc = Some op \<Longrightarrow> 
    lookup (assemble_code cd) (assembly_map cd pc) = lookup (assemble_op (assembly_map cd) pc op) 0"
  using assemble_code_lookup by fastforce

lemma assm_hp_lemma1: "3 dvd x \<Longrightarrow> x < hp \<Longrightarrow> assemble_heap mp h hp x = (Acc, snd (h x))"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma2: "x mod 3 = 1 \<Longrightarrow> snd (h (x - 1)) \<noteq> 0 \<Longrightarrow> x < hp \<Longrightarrow> 
    assemble_heap mp h hp x = (Acc, snd (h x))"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma3: "x mod 3 = 1 \<Longrightarrow> snd (h (x - 1)) = 0 \<Longrightarrow> x < hp \<Longrightarrow>
    assemble_heap mp h hp x = (Env, snd (h x))"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma4: "x mod 3 = 2 \<Longrightarrow> snd (h (x - 2)) \<noteq> 0 \<Longrightarrow> x < hp \<Longrightarrow> 
    assemble_heap mp h hp x = (Acc, snd (h x))"
  by (simp add: assemble_heap_def)

lemma assm_hp_lemma5: "x mod 3 = 2 \<Longrightarrow> snd (h (x - 2)) = 0 \<Longrightarrow> x < hp \<Longrightarrow> 
    assemble_heap mp h hp x = (Acc, mp (snd (h x)))"
  by (simp add: assemble_heap_def)

lemma [simp]: "x \<noteq> hp \<Longrightarrow> assm_hp cd (h(hp := a)) (Suc hp) x = assm_hp cd h hp x"
  by (induction x rule: x_mod_3_induct) (simp_all add: assemble_heap_def, linarith+)














definition assembleable_heap :: "(nat \<Rightarrow> pointer_tag \<times> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd = (3 dvd p\<^sub>h \<and> (\<forall>x < p\<^sub>h. 3 dvd x \<longrightarrow> snd (h x) = 0 \<longrightarrow> 
    (even (snd (h (Suc x))) \<and> snd (h (Suc x)) \<le> p\<^sub>\<Delta> \<and> snd (h (Suc (Suc x))) \<noteq> 0 \<and> 
      snd (h (Suc (Suc x))) \<le> lcd)))"

definition assembleable_env :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h = (even p\<^sub>\<Delta> \<and>
    (\<forall>x < p\<^sub>\<Delta>. if even x then 3 dvd \<Delta> x \<and> \<Delta> x < p\<^sub>h else even (\<Delta> x) \<and> \<Delta> x < p\<^sub>\<Delta>))"

definition assembleable_vals :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "assembleable_vals \<V> p\<^sub>\<V> p\<^sub>h = (3 dvd p\<^sub>h \<and> (\<forall>x < p\<^sub>\<V>. 3 dvd \<V> x \<and> \<V> x < p\<^sub>h))"

definition assembleable_stack :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "assembleable_stack s p\<^sub>s p\<^sub>\<Delta> lcd = (\<forall>x < p\<^sub>s. 
    if x = 0 then s x = 0 else if even x then s x \<noteq> 0 \<and> s x \<le> lcd else even (s x) \<and> s x \<le> p\<^sub>\<Delta>)"

primrec assembleable :: "unstr_state \<Rightarrow> code\<^sub>b list \<Rightarrow> bool" where
  "assembleable (S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> p\<^sub>\<V> s p\<^sub>s p\<^sub>\<C>) \<C> = (p\<^sub>\<C> \<le> length \<C> \<and> 
    length \<C> \<noteq> 0 \<and> orderly_code \<C> 0 \<and> properly_terminated\<^sub>b \<C> \<and> assembleable_heap h p\<^sub>h p\<^sub>\<Delta> (length \<C>) \<and> 
      assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<and> assembleable_vals \<V> p\<^sub>\<V> p\<^sub>h \<and> 
        assembleable_stack s p\<^sub>s p\<^sub>\<Delta> (length \<C>) \<and> even p\<^sub>s \<and> (p\<^sub>s = 0 \<longrightarrow> p\<^sub>\<C> = 0))"

lemma [simp]: "properly_terminated\<^sub>b \<C> \<Longrightarrow> lookup \<C> 0 \<noteq> Some (Lookup\<^sub>b x)"
  by (induction \<C>) auto

lemma [simp]: "properly_terminated\<^sub>b \<C> \<Longrightarrow> lookup \<C> 0 \<noteq> Some (PushCon\<^sub>b k)"
  by (induction \<C>) auto

lemma [simp]: "properly_terminated\<^sub>b \<C> \<Longrightarrow> lookup \<C> 0 \<noteq> Some (PushLam\<^sub>b p\<^sub>\<C>)"
  by (induction \<C>) auto

lemma [simp]: "properly_terminated\<^sub>b \<C> \<Longrightarrow> lookup \<C> 0 \<noteq> Some Apply\<^sub>b"
  by (induction \<C>) auto

lemma [dest]: "x \<noteq> y \<Longrightarrow> x < Suc y \<Longrightarrow> x < y"
  by presburger

lemma [dest]: "x \<noteq> y \<Longrightarrow> x \<noteq> Suc y \<Longrightarrow> x < Suc (Suc y) \<Longrightarrow> x < y"
  by presburger

lemma [simp]: "3 dvd x \<Longrightarrow> 3 dvd Suc x = False"
  by presburger

lemma [simp]: "3 dvd x \<Longrightarrow> 3 dvd Suc (Suc x) = False"
  by presburger

lemma [elim]: "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> even p\<^sub>\<Delta>"
  by (simp add: assembleable_env_def)

lemma [elim]: "assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> 3 dvd p\<^sub>h"
  by (simp add: assembleable_heap_def)

lemma [simp]: "assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> 
    assembleable_heap (h(p\<^sub>h := (PConst, Suc 0), Suc p\<^sub>h := (PConst, k), Suc (Suc p\<^sub>h) := (PConst, 0))) 
      (3 + p\<^sub>h) p\<^sub>\<Delta> lcd"
  by (auto simp add: assembleable_heap_def)

lemma [simp]: "assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> lcd \<noteq> 0 \<Longrightarrow>
  assembleable_heap (h(p\<^sub>h := (PConst, 0), Suc p\<^sub>h := (PEnv, k), Suc (Suc p\<^sub>h) := (PCode, p\<^sub>\<C>))) 
    (3 + p\<^sub>h) p\<^sub>\<Delta> lcd = (even k \<and> k \<le> p\<^sub>\<Delta> \<and> p\<^sub>\<C> \<noteq> 0 \<and> p\<^sub>\<C> \<le> lcd)"
proof
  let ?f = "\<lambda>x. if x = Suc (Suc p\<^sub>h) then (PCode, p\<^sub>\<C>) else (h(p\<^sub>h := (PConst, 0), Suc p\<^sub>h := (PEnv, k))) x"
  let ?g = "\<lambda>x. if x = Suc p\<^sub>h then (PCode, p\<^sub>\<C>) else (h(p\<^sub>h := (PConst, 0), Suc p\<^sub>h := (PEnv, k))) (Suc x)"
  let ?h = "\<lambda>x. if x = p\<^sub>h then (PCode, p\<^sub>\<C>) else (h(p\<^sub>h := (PConst, 0), Suc p\<^sub>h := (PEnv, k))) (Suc (Suc x))"
  assume H: "assembleable_heap (h(p\<^sub>h := (PConst, 0), Suc p\<^sub>h := (PEnv, k), 
    Suc (Suc p\<^sub>h) := (PCode, p\<^sub>\<C>))) (3 + p\<^sub>h) p\<^sub>\<Delta> lcd"
  moreover hence "\<And>x. x < 3 + p\<^sub>h \<Longrightarrow> 3 dvd x \<Longrightarrow> snd (?f x) = 0 \<Longrightarrow> 
    even (snd (?g x)) \<and> snd (?g x) \<le> p\<^sub>\<Delta> \<and> 0 < snd (?h x) \<and> snd (?h x) \<le> lcd" 
    by (simp add: assembleable_heap_def)
  moreover from H have "3 dvd p\<^sub>h" by (simp add: assembleable_heap_def)
  ultimately have "p\<^sub>h < 3 + p\<^sub>h \<Longrightarrow> snd (?f p\<^sub>h) = 0 \<Longrightarrow> 
    even (snd (?g p\<^sub>h)) \<and> snd (?g p\<^sub>h) \<le> p\<^sub>\<Delta> \<and> 0 < snd (?h p\<^sub>h) \<and> snd (?h p\<^sub>h) \<le> lcd" by blast
  moreover assume "lcd \<noteq> 0"
  ultimately show "even k \<and> k \<le> p\<^sub>\<Delta> \<and> p\<^sub>\<C> \<noteq> 0 \<and> p\<^sub>\<C> \<le> lcd" by simp
next
  assume "assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd" and "even k \<and> k \<le> p\<^sub>\<Delta> \<and> p\<^sub>\<C> \<noteq> 0 \<and> p\<^sub>\<C> \<le> lcd"
  thus "assembleable_heap (h(p\<^sub>h := (PConst, 0), Suc p\<^sub>h := (PEnv, k), Suc (Suc p\<^sub>h) := (PCode, p\<^sub>\<C>))) 
    (3 + p\<^sub>h) p\<^sub>\<Delta> lcd" by (auto simp add: assembleable_heap_def)
qed

lemma [simp]: "assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> assembleable_heap h p\<^sub>h (Suc (Suc p\<^sub>\<Delta>)) lcd"
  by (auto simp add: assembleable_heap_def)

lemma [simp]: "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> assembleable_env \<Delta> p\<^sub>\<Delta> (3 + p\<^sub>h)"
  by (auto simp add: assembleable_env_def)

lemma [elim]: "p < p\<^sub>\<Delta> \<Longrightarrow> odd p \<Longrightarrow> assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> \<Delta> p < p\<^sub>\<Delta>"
  by (simp add: assembleable_env_def)

lemma [simp]: "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> assembleable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> 
  assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> snd (h (\<V> p\<^sub>\<V>)) = 0 \<Longrightarrow>
    assembleable_env (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := snd (h (Suc (\<V> p\<^sub>\<V>))))) (Suc (Suc p\<^sub>\<Delta>)) p\<^sub>h"
proof (unfold assembleable_env_def assembleable_vals_def assembleable_heap_def, 
       rule, simp, rule, rule)
  fix y 
  assume "3 dvd p\<^sub>h \<and> (\<forall>x < p\<^sub>h. 3 dvd x \<longrightarrow> snd (h x) = 0 \<longrightarrow> 
    even (snd (h (Suc x))) \<and> snd (h (Suc x)) \<le> p\<^sub>\<Delta> \<and> snd (h (Suc (Suc x))) \<noteq> 0 \<and> 
      snd (h (Suc (Suc x))) \<le> lcd)"
     and "snd (h (\<V> p\<^sub>\<V>)) = 0" and "3 dvd p\<^sub>h \<and> (\<forall>x < Suc (Suc p\<^sub>\<V>). 3 dvd \<V> x \<and> \<V> x < p\<^sub>h)"
  hence "even (snd (h (Suc (\<V> p\<^sub>\<V>)))) \<and> snd (h (Suc (\<V> p\<^sub>\<V>))) \<le> p\<^sub>\<Delta>" by simp
  moreover assume "even p\<^sub>\<Delta> \<and> 
    (\<forall>x < p\<^sub>\<Delta>. if even x then 3 dvd \<Delta> x \<and> \<Delta> x < p\<^sub>h else even (\<Delta> x) \<and> \<Delta> x < p\<^sub>\<Delta>)"
              and "y < Suc (Suc p\<^sub>\<Delta>)" and "3 dvd p\<^sub>h \<and> (\<forall>x < Suc (Suc p\<^sub>\<V>). 3 dvd \<V> x \<and> \<V> x < p\<^sub>h)"
  ultimately show "if even y
        then 3 dvd (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := snd (h (Suc (\<V> p\<^sub>\<V>))))) y \<and> 
          (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := snd (h (Suc (\<V> p\<^sub>\<V>))))) y < p\<^sub>h
        else even ((\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := snd (h (Suc (\<V> p\<^sub>\<V>))))) y) \<and>
          (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := snd (h (Suc (\<V> p\<^sub>\<V>))))) y < Suc (Suc p\<^sub>\<Delta>)" by auto
qed

lemma [simp]: "assembleable_vals \<V> p\<^sub>\<V> p\<^sub>h \<Longrightarrow> 
    assembleable_vals (\<V>(p\<^sub>\<V> := k)) (Suc p\<^sub>\<V>) p\<^sub>h = (3 dvd p\<^sub>h \<and> k < p\<^sub>h \<and> 3 dvd k)"
  by (auto simp add: assembleable_vals_def)

lemma [simp]: "assembleable_vals \<V> p\<^sub>\<V> p\<^sub>h \<Longrightarrow> 
    assembleable_vals (\<V>(p\<^sub>\<V> := k)) (Suc p\<^sub>\<V>) (3 + p\<^sub>h) = (3 dvd p\<^sub>h \<and> k < 3 + p\<^sub>h \<and> 3 dvd k)"
  by (auto simp add: assembleable_vals_def)

lemma [elim]: "assembleable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> assembleable_vals \<V> p\<^sub>\<V> p\<^sub>h"
  by (simp add: assembleable_vals_def)

lemma [elim]: "assembleable_stack s (Suc (Suc p\<^sub>s)) p\<^sub>\<Delta> lcd \<Longrightarrow>
    assembleable_stack (s(p\<^sub>s := 0)) p\<^sub>s p\<^sub>\<Delta> lcd"
  by (simp add: assembleable_stack_def)

lemma [simp]: "assembleable_stack s 0 p\<^sub>\<Delta> lcd"
  by (simp add: assembleable_stack_def)

lemma [elim]: "assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> s 0 = 0"
  by (simp add: assembleable_stack_def)

lemma [simp]: "assembleable_stack s (Suc (Suc p\<^sub>s)) p\<^sub>\<Delta> lcd \<Longrightarrow> even p\<^sub>s \<Longrightarrow> s p\<^sub>s \<le> lcd"
proof (unfold assembleable_stack_def)
  assume "\<forall>x<Suc (Suc p\<^sub>s). if x = 0 then s x = 0 else if even x 
    then s x \<noteq> 0 \<and> s x \<le> lcd else even (s x) \<and> s x \<le> p\<^sub>\<Delta>"
     and "even p\<^sub>s"
  hence "if p\<^sub>s = 0 then s p\<^sub>s = 0 else s p\<^sub>s \<noteq> 0 \<and> s p\<^sub>s \<le> lcd" by simp
  thus "s p\<^sub>s \<le> lcd" by (simp split: if_splits)
qed

lemma [simp]: "0 \<noteq> p\<^sub>\<C> \<Longrightarrow> p\<^sub>\<C> \<le> lcd \<Longrightarrow> even p\<^sub>\<Delta> \<Longrightarrow> even p\<^sub>s \<Longrightarrow> p\<^sub>s \<noteq> 0 \<Longrightarrow> 
  assembleable_stack s p\<^sub>s p\<^sub>\<Delta> lcd \<Longrightarrow>
    assembleable_stack (s(p\<^sub>s := p\<^sub>\<C>, Suc p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) (Suc (Suc p\<^sub>s)) (Suc (Suc p\<^sub>\<Delta>)) lcd"
proof (unfold assembleable_stack_def)
  let ?sh = "s(p\<^sub>s := p\<^sub>\<C>, Suc p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))"
  assume R: "\<forall>x < p\<^sub>s. if x = 0 then s x = 0 else if even x then s x \<noteq> 0 \<and> s x \<le> lcd 
    else even (s x) \<and> s x \<le> p\<^sub>\<Delta>"
  hence "\<And>x. x < p\<^sub>s \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> odd x \<Longrightarrow> even (s x) \<and> s x \<le> p\<^sub>\<Delta>" by simp
  hence X: "\<And>x. odd x \<Longrightarrow> x < p\<^sub>s \<Longrightarrow> s x \<le> Suc (Suc p\<^sub>\<Delta>)" by fastforce
  assume "0 \<noteq> p\<^sub>\<C>" and "p\<^sub>\<C> \<le> lcd" and "even p\<^sub>\<Delta>" and "even p\<^sub>s" and "p\<^sub>s \<noteq> 0"
  with R X show "\<forall>x<Suc (Suc p\<^sub>s). if x = 0 then ?sh x = 0 
    else if even x then ?sh x \<noteq> 0 \<and> ?sh x \<le> lcd else even (?sh x) \<and> ?sh x \<le> Suc (Suc p\<^sub>\<Delta>)" 
      by auto
qed

lemma [simp]: "assembleable_stack s p\<^sub>s p\<^sub>\<Delta> lcd \<Longrightarrow> even p\<^sub>s \<Longrightarrow> Suc p\<^sub>\<C> \<le> lcd \<Longrightarrow> p\<^sub>s \<noteq> 0 \<Longrightarrow>
  assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> properly_terminated\<^sub>b \<C> \<Longrightarrow> lookup \<C> p\<^sub>\<C> = Some Apply\<^sub>b \<Longrightarrow> 
    assembleable_stack (s(p\<^sub>s := p\<^sub>\<C>, Suc p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) (Suc (Suc p\<^sub>s)) (Suc (Suc p\<^sub>\<Delta>)) lcd"
proof -
  assume "properly_terminated\<^sub>b \<C>" and "lookup \<C> p\<^sub>\<C> = Some Apply\<^sub>b"
  hence "p\<^sub>\<C> = 0 \<Longrightarrow> False" by simp
  hence "p\<^sub>\<C> \<noteq> 0" by auto
  moreover assume "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h"
  moreover hence "even p\<^sub>\<Delta>" by auto
  moreover assume "assembleable_stack s p\<^sub>s p\<^sub>\<Delta> lcd" and "even p\<^sub>s" and "Suc p\<^sub>\<C> \<le> lcd" and "p\<^sub>s \<noteq> 0"
  ultimately show ?thesis by simp
qed

lemma [simp]: "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> 
    odd p\<^sub>s \<Longrightarrow> assembleable_stack (s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) (Suc p\<^sub>s) (Suc (Suc p\<^sub>\<Delta>)) lcd"
proof (unfold assembleable_stack_def)
  assume E: "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h"
  assume O: "odd p\<^sub>s"
  assume R: "\<forall>x < Suc p\<^sub>s. if x = 0 then s x = 0 else if even x then s x \<noteq> 0 \<and> s x \<le> lcd 
    else even (s x) \<and> s x \<le> p\<^sub>\<Delta>"
  hence "\<And>x. x < Suc p\<^sub>s \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> odd x \<Longrightarrow> even (s x) \<and> s x \<le> p\<^sub>\<Delta>" by simp
  hence "\<And>x. odd x \<Longrightarrow> x < Suc p\<^sub>s \<Longrightarrow> s x \<le> Suc (Suc p\<^sub>\<Delta>)" by fastforce
  with E R O show "\<forall>x<Suc p\<^sub>s. if x = 0 then (s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) x = 0
    else if even x then (s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) x \<noteq> 0 \<and> (s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) x \<le> lcd
      else even ((s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) x) \<and> (s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) x \<le> Suc (Suc p\<^sub>\<Delta>)" 
    by auto
qed

lemma [simp]: "snd (h (\<V> p\<^sub>\<V>)) = 0 \<Longrightarrow> assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> 
    assembleable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> 0 < snd (h (Suc (Suc (\<V> p\<^sub>\<V>))))"
  by (simp add: assembleable_heap_def assembleable_vals_def)

lemma [simp]: "snd (h (\<V> p\<^sub>\<V>)) = 0 \<Longrightarrow> assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> 
    assembleable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> snd (h (Suc (Suc (\<V> p\<^sub>\<V>)))) \<le> lcd"
  by (simp add: assembleable_heap_def assembleable_vals_def)

lemma [elim]: "unstr_lookup \<Delta> p x = Some y \<Longrightarrow> p \<le> p\<^sub>\<Delta> \<Longrightarrow> even p \<Longrightarrow> assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> 
  y < p\<^sub>h"
proof (induction \<Delta> p x rule: unstr_lookup.induct)
  case (4 \<Delta> p x)
  moreover hence "even (\<Delta> (Suc p)) \<and> \<Delta> (Suc p) < p\<^sub>\<Delta>" by (simp add: assembleable_env_def)
  ultimately show ?case by simp
qed (auto simp add: assembleable_env_def)

lemma [elim]: "unstr_lookup \<Delta> p x = Some y \<Longrightarrow> p \<le> p\<^sub>\<Delta> \<Longrightarrow> even p \<Longrightarrow> assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> 
  3 dvd y"
proof (induction \<Delta> p x rule: unstr_lookup.induct) 
  case (4 \<Delta> p x)
  moreover hence "even (\<Delta> (Suc p)) \<and> \<Delta> (Suc p) < p\<^sub>\<Delta>" by (simp add: assembleable_env_def)
  ultimately show ?case by simp
qed (auto simp add: assembleable_env_def)

lemma [simp]: "odd p\<^sub>s \<Longrightarrow> assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> even (s p\<^sub>s)" 
  by (unfold assembleable_stack_def) auto

lemma [simp]: "odd p\<^sub>s \<Longrightarrow> assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> s p\<^sub>s \<le> p\<^sub>\<Delta>" 
  by (unfold assembleable_stack_def) auto

lemma [elim]: "unstr_lookup \<Delta> (s p\<^sub>s) x = Some y \<Longrightarrow> assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> 
  assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> odd p\<^sub>s \<Longrightarrow> y < p\<^sub>h"
proof -
  assume "odd p\<^sub>s" and "assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd"  
  hence "even (s p\<^sub>s)" and "s p\<^sub>s \<le> p\<^sub>\<Delta>" by auto
  moreover assume "unstr_lookup \<Delta> (s p\<^sub>s) x = Some y" and "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h"
  ultimately show "y < p\<^sub>h" by auto
qed

lemma [elim]: "unstr_lookup \<Delta> (s p\<^sub>s) x = Some y \<Longrightarrow> assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> 
  assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> odd p\<^sub>s \<Longrightarrow> 3 dvd y"
proof -
  assume "odd p\<^sub>s" and "assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd"  
  hence "s p\<^sub>s \<le> p\<^sub>\<Delta> \<and> even (s p\<^sub>s)" by simp
  moreover assume "unstr_lookup \<Delta> (s p\<^sub>s) x = Some y" and "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h"
  ultimately show "3 dvd y" by auto
qed

lemma [simp]: "snd (h (\<V> p\<^sub>\<V>)) = 0 \<Longrightarrow> assembleable_heap h p\<^sub>h p\<^sub>\<Delta> (length \<C>) \<Longrightarrow> 
    assembleable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> snd (h (Suc (Suc (\<V> p\<^sub>\<V>)))) \<noteq> 0"
  by simp

lemma [elim]: "assembleable_stack s (Suc (Suc p\<^sub>s)) p\<^sub>\<Delta> lcd \<Longrightarrow> assembleable_stack s p\<^sub>s p\<^sub>\<Delta> lcd"
  by (unfold assembleable_stack_def, rule) simp

lemma preserve_restructure [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> assembleable \<Sigma>\<^sub>u \<C> \<Longrightarrow> 
    assembleable \<Sigma>\<^sub>u' \<C>"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: eval\<^sub>u.induct) auto

lemma [simp]: "iter (\<tturnstile> \<C> \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> assembleable \<Sigma>\<^sub>u \<C> \<Longrightarrow> assembleable \<Sigma>\<^sub>u' \<C>"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct) auto

lemma [simp]: "assembleable_heap nmem 0 0 x"
  by (simp add: assembleable_heap_def)

lemma [simp]: "assembleable_env nmem 0 0"
  by (simp add: assembleable_env_def)

lemma [simp]: "assembleable_vals nmem 0 0" 
  by (simp add: assembleable_vals_def)

lemma [simp]: "assembleable_stack (nmem(0 := 0, Suc 0 := 0)) 2 0 lcd"
  by (simp only: assembleable_stack_def) simp_all








lemma [simp]: "assembleable_heap h hp ep (length cd) \<Longrightarrow> (assm_hp cd h hp)
  (hp := (Acc, Suc a), Suc hp := (Acc, b), Suc (Suc hp) := (Acc, c)) = 
    assm_hp cd (h(hp := (PConst, Suc a), Suc hp := (PConst, b), Suc (Suc hp) := (PConst, c))) 
      (Suc (Suc (Suc hp)))"
proof
  fix x
  assume "assembleable_heap h hp ep (length cd)"
  hence "3 dvd hp" by (simp add: assembleable_heap_def)
  moreover hence "Suc hp mod 3 = 1" by presburger
  moreover hence "Suc (Suc hp) mod 3 = 2" by presburger
  ultimately show "((assm_hp cd h hp)
    (hp := (Acc, Suc a), Suc hp := (Acc, b), Suc (Suc hp) := (Acc, c))) x =
      assm_hp cd (h(hp := (PConst, Suc a), Suc hp := (PConst, b), Suc (Suc hp) := (PConst, c))) 
        (Suc (Suc (Suc hp))) x" 
    by (simp add: assm_hp_lemma1 assm_hp_lemma2 assm_hp_lemma3 assm_hp_lemma4 assm_hp_lemma5)
qed

lemma [simp]: "assembleable_heap h hp ep (length cd) \<Longrightarrow> (assm_hp cd h hp)
  (hp := (Acc, 0), Suc hp := (Env, a), Suc (Suc hp) := (Acc, assembly_map cd b)) = 
    assm_hp cd (h(hp := (PConst, 0), Suc hp := (PEnv, a), Suc (Suc hp) := (PCode, b))) 
      (Suc (Suc (Suc hp)))"
proof
  fix x
  assume "assembleable_heap h hp ep (length cd)"
  hence H: "3 dvd hp" by (simp add: assembleable_heap_def)
  moreover hence "Suc hp mod 3 = 1" by presburger
  moreover hence "Suc (Suc hp) mod 3 = 2" by presburger
  ultimately show "((assm_hp cd h hp)(hp := (Acc, 0), Suc hp := (Env, a), 
    Suc (Suc hp) := (Acc, assembly_map cd b))) x =
      assm_hp cd (h(hp := (PConst, 0), Suc hp := (PEnv, a), Suc (Suc hp) := (PCode, b))) 
        (Suc (Suc (Suc hp))) x" 
    by (simp add: assm_hp_lemma1 assm_hp_lemma2 assm_hp_lemma3 assm_hp_lemma4 assm_hp_lemma5)
qed

lemma [simp]: "assembleable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> 
  assemble_heap mp h hp (Suc (vs vp)) = 
    (if snd (h (vs vp)) = 0 then Env else Acc, snd (h (Suc (vs vp))))"
proof (unfold assemble_heap_def assembleable_vals_def)
  assume "3 dvd hp \<and> (\<forall>x<Suc (Suc vp). 3 dvd vs x \<and> vs x < hp)"
  moreover hence X: "3 dvd vs vp \<and> vs vp < hp" by simp
  ultimately have "Suc (vs vp) < hp" by fastforce
  moreover from X have "Suc (vs vp) mod 3 = 1" by presburger
  ultimately show "(if Suc (vs vp) \<ge> hp then (Acc, 0) else case Suc (vs vp) mod 3 of 
       0 \<Rightarrow> (Acc, snd (h (Suc (vs vp))))
     | Suc 0 \<Rightarrow> (if snd (h (Suc (vs vp) - 1)) = 0 then Env else Acc, snd (h (Suc (vs vp))))
     | Suc (Suc 0) \<Rightarrow> if snd (h (Suc (vs vp) - 2)) = 0 then (Acc, mp (snd (h (Suc (vs vp))))) 
        else (Acc, snd (h (Suc (vs vp))))
     | Suc (Suc (Suc x)) \<Rightarrow> undefined) = (if snd (h (vs vp)) = 0 then Env else Acc, 
        snd (h (Suc (vs vp))))" 
    by simp
qed

lemma [simp]: "assembleable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> snd (h (vs vp)) = 0 \<Longrightarrow> 
  assembleable_heap h hp ep lcd \<Longrightarrow>
    assemble_heap mp h hp (Suc (Suc (vs vp))) = (Acc, mp (snd (h (Suc (Suc (vs vp))))))"
proof (unfold assemble_heap_def assembleable_vals_def)
  assume "3 dvd hp \<and> (\<forall>x<Suc (Suc vp). 3 dvd vs x \<and> vs x < hp)"
  hence "3 dvd vs vp \<and> vs vp < hp" by simp
  moreover assume "assembleable_heap h hp ep lcd"
  moreover hence "3 dvd hp" by auto
  ultimately have "Suc (Suc (vs vp)) mod 3 = 2 \<and> Suc (Suc (vs vp)) < hp" by presburger
  moreover assume "snd (h (vs vp)) = 0"
  ultimately show "(if (Suc (Suc (vs vp))) \<ge> hp then (Acc, 0) else case Suc (Suc (vs vp)) mod 3 of 
       0 \<Rightarrow> (Acc, snd (h (Suc (Suc (vs vp)))))
     | Suc 0 \<Rightarrow> (if snd (h (Suc (Suc (vs vp)) - 1)) = 0 then Env 
        else Acc, snd (h (Suc (Suc (vs vp)))))
     | Suc (Suc 0) \<Rightarrow>
         if snd (h (Suc (Suc (vs vp)) - 2)) = 0 then (Acc, mp (snd (h (Suc (Suc (vs vp))))))
        else (Acc, snd (h (Suc (Suc (vs vp)))))
     | Suc (Suc (Suc x)) \<Rightarrow> undefined) = (Acc, mp (snd (h (Suc (Suc (vs vp))))))" 
    by simp
qed

lemma [simp]: "Suc (Suc (vs vp)) mod 3 \<noteq> Suc (Suc (Suc x))" 
  by simp

lemma [simp]: "snd (h (vs vp)) = Suc x \<Longrightarrow> vs vp mod 3 = 0 \<Longrightarrow> Suc (Suc (vs vp)) < hp \<Longrightarrow>
    assemble_heap mp h hp (Suc (Suc (vs vp))) = (Acc, snd (h (Suc (Suc (vs vp)))))"
  by (simp add: assemble_heap_def split: nat.splits) presburger

lemma [simp]: "even sp \<Longrightarrow> 
  (assm_stk cd sh sp)(sp := (Acc, assembly_map cd pc), Suc sp := (Env, a)) = 
    (assm_stk cd (sh(sp := pc, Suc sp := a)) (Suc (Suc sp)))"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> 
    (assm_stk cd sh (Suc sp))(sp := (Env, k)) = assm_stk cd (sh(sp := k)) (Suc sp)"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "even (Suc sp) \<Longrightarrow> assm_stk cd sh (Suc sp) sp = (Env, sh sp)"
  by (simp add: assemble_stack_def)

lemma [simp]: "even (Suc (Suc sp)) \<Longrightarrow> assm_stk cd sh (Suc sp) sp = 
    (Acc, assembly_map cd (sh sp))"
  by (simp add: assemble_stack_def)

lemma [simp]: "(assm_stk cd sh (Suc sp))(sp := (Acc, 0)) = assm_stk cd sh sp"
  by (auto simp add: assemble_stack_def)

lemma [simp]: "(assemble_vals vs vp)(vp := (Hp, y)) = assemble_vals (vs(vp := y)) (Suc vp)"
  by (auto simp add: assemble_vals_def)

lemma [simp]: "(assemble_vals vs (Suc vp))(vp := (Acc, 0)) = assemble_vals vs vp"
  by rule (simp add: assemble_vals_def)

lemma [simp]: "even ep \<Longrightarrow> (assemble_env e ep)(ep := (Hp, a), Suc ep := (Env, b)) = 
    assemble_env (e(ep := a, Suc ep := b)) (Suc (Suc ep))"
  by (auto simp add: assemble_env_def)

lemma [simp]: "(case_register hp ep vp sp a)(Hp := hp') = case_register hp' ep vp sp a"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp a)(Env := ep') = case_register hp ep' vp sp a"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp a)(Vals := vp') = case_register hp ep vp' sp a"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp a)(Stk := sp') = case_register hp ep vp sp' a"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp a)(Acc := a') = case_register hp ep vp sp a'"
  by rule (simp split: register.splits)

lemma [simp]: "unstr_lookup e a x = Some v \<Longrightarrow> lookup cd pc = Some (Lookup\<^sub>b y) \<Longrightarrow> x \<le> y \<Longrightarrow> 
  pc < length cd \<Longrightarrow> a \<le> ep \<Longrightarrow> assembleable_env e ep hp \<Longrightarrow> iter_evala (assemble_code cd) 
    (5 + 2 * x) (AS (case_register h (assemble_env e ep) vs sh undefined) (case_register hp ep vp sp a) 
      Env (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e ep)
        (vs(vp := (Hp, v))) sh undefined) (case_register hp ep (Suc vp) sp 0) Acc
          (assembly_map cd pc))"
proof (induction e a x rule: unstr_lookup.induct)
  case (3 e p)
  moreover from 3 have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (ASub Acc 2)" by simp
  moreover from 3 have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AGet Acc)" by simp
  moreover from 3 have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (APut Vals (Reg Acc))" by (simp del: add_2_eq_Suc)
  ultimately show ?case 
    by (simp add: numeral_def assemble_env_def split: if_splits)
next
  case (4 e p x)
  moreover hence "lookup (assemble_code cd) (6 + 2 * x + assembly_map cd pc) = 
    Some (ASub Acc (Suc 0))" by simp
  moreover from 4 have "lookup (assemble_code cd) (5 + 2 * x + assembly_map cd pc) = 
    Some (AGet Acc)" by simp
  ultimately have X: "iter_evala (assemble_code cd) 2 (AS (case_register h (assemble_env e ep) vs 
    sh undefined) (case_register hp ep vp sp (Suc (Suc p))) Env
      (7 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e ep) vs sh undefined) 
        (case_register hp ep vp sp (e (Suc p))) Env (5 + 2 * x + assembly_map cd pc))" 
    by (simp add: numeral_def assemble_env_def split: if_splits) presburger
  from 4 have "Suc p < ep" and "even p" and "assembleable_env e ep hp" by (auto split: if_splits)
  hence "e (Suc p) < ep" by (auto split: if_splits)
  moreover with 4 have "iter_evala (assemble_code cd) (5 + 2 * x)
    (AS (case_register h (assemble_env e ep) vs sh undefined) (case_register hp ep vp sp (e (Suc p))) Env
      (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e ep) 
        (vs(vp := (Hp, v))) sh undefined) (case_register hp ep (Suc vp) sp 0) Acc
          (assembly_map cd pc))" by (simp split: if_splits)
  with X have "iter_evala (assemble_code cd) (2 + (5 + 2 * x))
    (AS (case_register h (assemble_env e ep) vs sh undefined) (case_register hp ep vp sp (Suc (Suc p))) (
      Env) (7 + 2 * x + assembly_map cd pc)) = Some (AS (case_register h (assemble_env e ep) 
        (vs(vp := (Hp, v))) sh undefined) (case_register hp ep (Suc vp) sp 0) Acc
          (assembly_map cd pc))" 
    using iter_evala_combine by blast
  thus ?case by simp
qed simp_all

theorem correcta [simp]: "cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> assembleable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow> 
  \<exists>n. iter_evala (assemble_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u')"
proof (induction cd\<^sub>b \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: eval\<^sub>u.induct)
  case (ev\<^sub>u_lookup cd pc x e sh sp y h hp ep vs vp)
  moreover hence "odd sp" by simp
  moreover from ev\<^sub>u_lookup have "lookup (assemble_code cd) (7 + 2 * x + assembly_map cd pc) = 
    Some (APut Acc (Reg Stk))" by simp
  moreover from ev\<^sub>u_lookup have "lookup (assemble_code cd) (6 + 2 * x + assembly_map cd pc) = 
    Some (ASub Acc 1)" by simp
  moreover from ev\<^sub>u_lookup have "lookup (assemble_code cd) (5 + 2 * x + assembly_map cd pc) = 
    Some (AGet Acc)" by simp
  ultimately have X: "iter_evala (assemble_code cd) 3 
    (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp)) undefined) (case_register hp ep vp (Suc sp) 0) Acc
        (8 + 2 * x + assembly_map cd pc)) = Some (AS (case_register (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc sp)) undefined) 
            (case_register hp ep vp (Suc sp) (sh sp)) Env (5 + 2 * x + assembly_map cd pc))" 
    by (simp add: numeral_def)
  from ev\<^sub>u_lookup have "sh sp \<le> ep" by auto
  with ev\<^sub>u_lookup have "iter_evala (assemble_code cd) (5 + 2 * x) 
    (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp)) undefined) (case_register hp ep vp (Suc sp) (sh sp)) Env
        (5 + 2 * x + assembly_map cd pc)) = Some (AS (case_register (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals (vs(vp := y)) (Suc vp)) (assm_stk cd sh (Suc sp)) undefined) 
            (case_register hp ep (Suc vp) (Suc sp) 0) Acc (assembly_map cd pc))" 
    by auto
  with X have "iter_evala (assemble_code cd) (3 + (5 + 2 * x)) 
    (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp)) undefined) (case_register hp ep vp (Suc sp) 0) Acc
        (8 + 2 * x + assembly_map cd pc)) = Some (AS (case_register (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals (vs(vp := y)) (Suc vp)) (assm_stk cd sh (Suc sp)) undefined) 
            (case_register hp ep (Suc vp) (Suc sp) 0) Acc (assembly_map cd pc))" 
    using iter_evala_combine by blast
  hence "iter_evala (assemble_code cd) (3 + (5 + 2 * x)) 
    (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp)) undefined) (case_register hp ep vp (Suc sp) 0) Acc
        (8 + (2 * x + assembly_map cd pc))) = Some (AS (case_register (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals (vs(vp := y)) (Suc vp)) (assm_stk cd sh (Suc sp)) undefined) 
            (case_register hp ep (Suc vp) (Suc sp) 0) Acc (assembly_map cd pc))"
    by (simp add: add.assoc)
  with ev\<^sub>u_lookup show ?case by auto
next
  case (ev\<^sub>u_pushcon cd pc k h hp e ep vs vp sh sp)
  moreover from ev\<^sub>u_pushcon have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (APut Vals (Reg Hp))" by simp
  moreover from ev\<^sub>u_pushcon have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (AAdd Vals 1)" by simp
  moreover from ev\<^sub>u_pushcon have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (APut Hp (Con 1))" by simp 
  moreover from ev\<^sub>u_pushcon have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AAdd Hp 1)" by simp 
  moreover from ev\<^sub>u_pushcon have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (APut Hp (Con k))" by simp 
  moreover from ev\<^sub>u_pushcon have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAdd Hp 1)" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 8 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc sp)) undefined) 
      (case_register hp ep vp (Suc sp) 0) Acc (assembly_map cd (Suc pc))) = Some (AS 
        (case_register (assm_hp cd (h(hp := (PConst, Suc 0), Suc hp := (PConst, k), 
          Suc (Suc hp) := (PConst, 0))) (3 + hp)) (assemble_env e ep) (assemble_vals (vs(vp := hp)) 
            (Suc vp)) (assm_stk cd sh (Suc sp)) undefined) (case_register (3 + hp) ep (Suc vp) (Suc sp) 0) 
              Acc (assembly_map cd pc))" 
    by (auto simp add: numeral_def)
  thus ?case by auto
next
  case (ev\<^sub>u_pushlam cd pc pc' h hp e ep vs vp sh sp)
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (11 + assembly_map cd pc) = 
    Some (APut Vals (Reg Hp))" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (10 + assembly_map cd pc) = 
    Some (AAdd Vals 1)" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (APut Acc (Reg Stk))" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (ASub Acc 1)" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AGet Acc)" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (APut Hp (Con 0))" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd Hp 1)" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (4 + assembly_map cd pc) =
    Some (APut Hp (Reg Acc))" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AAdd Hp 1)" by simp
  moreover from ev\<^sub>u_pushlam have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (APut Acc (Con 0))" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 12 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc sp)) undefined) 
      (case_register hp ep vp (Suc sp) 0) Acc (assembly_map cd (Suc pc))) = Some (AS 
        (case_register (assm_hp cd (h(hp := (PConst, 0), Suc hp := (PEnv, sh sp), 
          Suc (Suc hp) := (PCode, pc'))) (3 + hp)) (assemble_env e ep) (assemble_vals (vs(vp := hp)) 
            (Suc vp)) (assm_stk cd sh (Suc sp)) undefined) (case_register (3 + hp) ep (Suc vp) (Suc sp) 0) 
              Acc (assembly_map cd pc))" 
    by (auto simp add: numeral_def)
  thus ?case by auto
next
  case (ev\<^sub>u_apply cd pc h vs vp hp e ep sh sp)
  moreover hence "even ep" by auto
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (21 + assembly_map cd pc) = 
    Some (ASub Vals 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (20 + assembly_map cd pc) = 
    Some (AGet Vals)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (19 + assembly_map cd pc) = 
    Some (APut Vals (Con 0))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (18 + assembly_map cd pc) = 
    Some (APut Env (Reg Acc))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (17 + assembly_map cd pc) = 
    Some (AAdd Env 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (16 + assembly_map cd pc) = 
    Some (APut Stk (Con (assembly_map cd pc)))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (15 + assembly_map cd pc) = 
    Some (AAdd Stk 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (14 + assembly_map cd pc) = 
    Some (APut Acc (Reg Env))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (13 + assembly_map cd pc) = 
    Some (AAdd Acc 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (12 + assembly_map cd pc) = 
    Some (APut Stk (Reg Acc))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (11 + assembly_map cd pc) = 
    Some (AAdd Stk 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (10 + assembly_map cd pc) = 
    Some (ASub Vals 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (AGet Vals)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (AAdd Acc 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AGet Acc)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (APut Env (Reg Acc))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd Env 1)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AGet Vals)" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (APut Vals (Con 0))" by simp
  moreover from ev\<^sub>u_apply have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAdd Acc 2)" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 22 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs (Suc (Suc vp))) (assm_stk cd sh (Suc sp)) undefined) 
      (case_register hp ep (Suc (Suc vp)) (Suc sp) 0) Acc (assembly_map cd (Suc pc))) = 
        Some (AS (case_register (assm_hp cd h hp) (assemble_env (e(ep := vs (Suc vp), 
          Suc ep := snd (h (Suc (vs vp))))) (Suc (Suc ep))) (assemble_vals vs vp) 
            (assm_stk cd (sh(Suc sp := pc, Suc (Suc sp) := Suc (Suc ep))) (Suc (Suc (Suc sp)))) undefined) 
              (case_register hp (Suc (Suc ep)) vp (Suc (Suc (Suc sp))) 0) Acc
                (assembly_map cd (snd (h (Suc (Suc (vs vp)))))))"
    by (auto simp add: numeral_def assemble_vals_def)
  thus ?case by auto
next
  case (ev\<^sub>u_return cd pc h hp e ep vs vp sh sp)
  moreover from ev\<^sub>u_return have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (ASub Stk 1)" by simp
  moreover from ev\<^sub>u_return have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (APut Stk (Con 0))" by simp
  moreover from ev\<^sub>u_return have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (ASub Stk 1)" by simp
  moreover from ev\<^sub>u_return have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AGet Stk)" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 6 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc (Suc sp))) undefined) 
      (case_register hp ep vp (Suc (Suc sp)) 0) Acc (assembly_map cd (Suc pc))) = 
        Some (AS (case_register (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
          (assm_stk cd sh sp) undefined) (case_register hp ep vp sp 0) Acc (assembly_map cd (sh sp)))"
    by (simp add: numeral_def split: prod.splits)
  thus ?case by auto
next
  case (ev\<^sub>u_jump cd pc h vs vp hp e ep sh sp)
  moreover hence "even ep" by auto
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (20 + assembly_map cd pc) = 
    Some (ASub Vals 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (19 + assembly_map cd pc) = 
    Some (AGet Vals)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (18 + assembly_map cd pc) = 
    Some (APut Vals (Con 0))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (17 + assembly_map cd pc) = 
    Some (APut Env (Reg Acc))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (16 + assembly_map cd pc) = 
    Some (AAdd Env 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (15 + assembly_map cd pc) = 
    Some (APut Acc (Reg Env))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (14 + assembly_map cd pc) = 
    Some (AAdd Acc 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (13 + assembly_map cd pc) = 
    Some (ASub Stk 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (12 + assembly_map cd pc) = 
    Some (APut Stk (Reg Acc))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (11 + assembly_map cd pc) =
    Some (AAdd Stk 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (10 + assembly_map cd pc) = 
    Some (ASub Vals 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (AGet Vals)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (AAdd Acc 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AGet Acc)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (APut Env (Reg Acc))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd Env 1)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AGet Vals)" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (APut Vals (Con 0))" by simp
  moreover from ev\<^sub>u_jump have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAdd Acc 2)" by (simp del: add_2_eq_Suc)
  ultimately have "iter_evala (assemble_code cd) 21 (AS (case_register (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs (Suc (Suc vp))) (assm_stk cd sh (Suc sp)) undefined) 
      (case_register hp ep (Suc (Suc vp)) (Suc sp) 0) Acc (assembly_map cd (Suc pc))) = 
        Some (AS (case_register (assm_hp cd h hp) (assemble_env (e(ep := vs (Suc vp), 
          Suc ep := snd (h (Suc (vs vp))))) (Suc (Suc ep))) (assemble_vals vs vp) 
            (assm_stk cd (sh(sp := Suc (Suc ep))) (Suc sp)) undefined) (case_register hp 
              (Suc (Suc ep)) vp (Suc sp) 0) Acc (assembly_map cd (snd (h (Suc (Suc (vs vp)))))))"
    by (auto simp add: numeral_def assemble_vals_def)
  thus ?case by auto
qed

lemma [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> assembleable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow> 
  \<exists>n. iter_evala (assemble_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u')"
proof (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct)
  case (iter_refl \<Sigma>\<^sub>u)
  have "iter_evala (assemble_code cd\<^sub>b) 0 (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u)" by simp
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

theorem correct\<^sub>a_iter [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> assembleable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow> 
  iter (\<tturnstile> assemble_code cd\<^sub>b \<leadsto>\<^sub>a) (assm_state cd\<^sub>b \<Sigma>\<^sub>u) (assm_state cd\<^sub>b \<Sigma>\<^sub>u')"
proof -
  assume "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u'" and "assembleable \<Sigma>\<^sub>u cd\<^sub>b"
  hence "\<exists>n. iter_evala (assemble_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>u) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>u')" 
    by simp
  thus "iter (\<tturnstile> assemble_code cd\<^sub>b \<leadsto>\<^sub>a) (assm_state cd\<^sub>b \<Sigma>\<^sub>u) (assm_state cd\<^sub>b \<Sigma>\<^sub>u')" 
    by (simp add: iter_evala_equiv)
qed

(* We no longer do the reverse (completeness) direction because it's rather complex to even state 
now *)

lemma [simp]: "assm_hp cd h 0 = (\<lambda>x. (Acc, 0))"
  by rule (simp add: assemble_heap_def)

lemma [simp]: "assemble_env e 0 = (\<lambda>x. (Acc, 0))"
  by rule (simp add: assemble_env_def)

lemma [simp]: "assemble_vals vs 0 = (\<lambda>x. (Acc, 0))"
  by rule (simp add: assemble_vals_def)

lemma [simp]: "assm_stk cd (mp(0 := a, Suc 0 := b)) 2 = 
    (\<lambda>x. (Acc, 0))(0 := (Acc, assembly_map cd a), Suc 0 := (Env, b))"
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