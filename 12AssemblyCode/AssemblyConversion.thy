theory AssemblyConversion
  imports AssemblyCode "../11UnstructuredState/UnstructuredState" "../00Utils/Utils"
    "../07ByteCode/CodeFlattening"
begin

primrec assemble_op_len :: "code\<^sub>b \<Rightarrow> nat" where
  "assemble_op_len (Lookup\<^sub>b x) = 7 + 2 * x"
| "assemble_op_len (PushCon\<^sub>b k) = 5"
| "assemble_op_len (PushLam\<^sub>b pc) = 9"
| "assemble_op_len Apply\<^sub>b = 20"
| "assemble_op_len PushEnv\<^sub>b = 11"
| "assemble_op_len Return\<^sub>b = 5"
| "assemble_op_len Jump\<^sub>b = 19"

primrec assemble_op :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> code\<^sub>b \<Rightarrow> assm list" where
  "assemble_op mp ix (Lookup\<^sub>b x) = [
    AMov (Reg Acc) (Con 0),
    AAdd Vals (Con 1),
    AMov (Mem Vals) (Reg Acc),
    AMov (Reg Acc) (Mem Acc),
    ASub Acc (Con 2)] @
    concat (replicate x [
    AMov (Reg Acc) (Mem Acc),
    ASub Acc (Con 1)]) @ [
    AMov (Reg Acc) (Mem Acc),
    ASub Acc (Con 1),
    AMov (Reg Acc) (Reg Stk)]"
| "assemble_op mp ix (PushCon\<^sub>b k) = [
    AAdd Hp (Con 1), 
    AMov (Mem Hp) (Con 0),
    AAdd Hp (Con 1),  
    AMov (Mem Hp) (Con k),
    AAdd Vals (Con 1),
    AMov (Mem Vals) (Reg Hp)]"
| "assemble_op mp ix (PushLam\<^sub>b pc) = [
    AAdd Hp (Con 1), 
    AMov (Mem Hp) (Con (mp pc)), 
    AMov (Reg Acc) (Con 0),
    AAdd Hp (Con 1), 
    AMov (Mem Hp) (Reg Acc),
    AMov (Reg Acc) (Mem Acc), 
    ASub Acc (Con 1),
    AMov (Reg Acc) (Reg Stk),
    AAdd Vals (Con 1),
    AMov (Mem Vals) (Reg Hp)]"
| "assemble_op mp ix Apply\<^sub>b = [
    AJmp (Reg Acc),
    AMov (Reg Acc) (Mem Acc),
    AAdd Acc (Con 1),
    AMov (Mem Vals) (Con 0),
    AMov (Reg Acc) (Mem Vals),
    AAdd Env (Con 1),
    AMov (Mem Env) (Reg Acc),
    AMov (Reg Acc) (Mem Acc),
    AMov (Reg Acc) (Mem Vals),
    ASub Vals (Con 1),
    AAdd Stk (Con 1),
    AMov (Mem Stk) (Reg Acc),
    AAdd Acc (Con 1),
    AMov (Reg Acc) (Reg Env),
    AAdd Stk (Con 1),
    AMov (Mem Stk) (Con (mp ix)),
    AAdd Env (Con 1),
    AMov (Mem Env) (Reg Acc),
    AMov (Mem Vals) (Con 0),
    AMov (Reg Acc) (Mem Vals),
    ASub Vals (Con 1)]"
| "assemble_op mp ix PushEnv\<^sub>b = [
    AMov (Reg Acc) (Con 0),
    AAdd Stk (Con 1),
    AMov (Mem Stk) (Reg Env),
    AAdd Env (Con 1),
    AMov (Mem Env) (Reg Acc),
    AMov (Reg Acc) (Mem Stk),
    ASub Stk (Con 1),
    AAdd Env (Con 1),
    AMov (Mem Env) (Reg Acc),
    AMov (Mem Vals) (Con 0),
    AMov (Reg Acc) (Mem Vals),
    ASub Vals (Con 1)]"
| "assemble_op mp ix Return\<^sub>b = [
    AJmp (Reg Acc),
    AMov (Mem Stk) (Con 0),
    AMov (Reg Acc) (Mem Stk),
    ASub Stk (Con 1),
    AMov (Mem Stk) (Con 0),
    ASub Stk (Con 1)]"
| "assemble_op mp ix Jump\<^sub>b = [
    AJmp (Reg Acc),
    AMov (Reg Acc) (Mem Acc),
    AAdd Acc (Con 1),
    AMov (Mem Vals) (Con 0),
    AMov (Reg Acc) (Mem Vals),
    AAdd Env (Con 1),
    AMov (Mem Env) (Reg Acc),
    AMov (Reg Acc) (Mem Acc),
    AMov (Reg Acc) (Mem Vals),
    ASub Vals (Con 1),
    AAdd Stk (Con 1),
    AMov (Mem Stk) (Reg Acc),
    ASub Stk (Con 1),
    AAdd Acc (Con 1),
    AMov (Reg Acc) (Reg Env),
    AAdd Env (Con 1),
    AMov (Mem Env) (Reg Acc),
    AMov (Mem Vals) (Con 0),
    AMov (Reg Acc) (Mem Vals),
    ASub Vals (Con 1)]"

fun assembly_map :: "code\<^sub>b list \<Rightarrow> nat \<Rightarrow> nat" where
  "assembly_map [] x = 0"
| "assembly_map (op # cd) 0 = 0"
| "assembly_map (op # cd) (Suc x) = Suc (assemble_op_len op + assembly_map cd x)"

lemma [simp]: "lookup cd x = Some op \<Longrightarrow> (assembly_map cd pc = 0) = (pc = 0)"
  by (induction cd pc rule: assembly_map.induct) simp_all

definition assemble_code :: "code\<^sub>b list \<Rightarrow> assm list" where
  "assemble_code cd = concat (map_with_idx 0 (assemble_op (assembly_map cd)) cd)"

definition assemble_heap :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> pointer_tag \<times> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
    memseg \<times> nat" where
  "assemble_heap mp h hp x = (if x \<ge> hp then (Acc, 0) else case h x of
      (PConst, y) \<Rightarrow> (Acc, y)
    | (PCode, y) \<Rightarrow> (Acc, mp y)
    | (PEnv, y) \<Rightarrow> (Env, y))"

definition assemble_env :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memseg \<times> nat" where
  "assemble_env e ep x = (if x \<ge> ep then (Acc, 0) else (if even x then Hp else Env, e x))"

definition assemble_vals :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memseg \<times> nat" where
  "assemble_vals vs vp x = (if x \<ge> vp then (Acc, 0) else (Hp, vs x))"

definition assemble_stack :: "(nat \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memseg \<times> nat" where
  "assemble_stack mp s sp x = (
    if x \<ge> sp then (Acc, 0) else if even x then (Acc, mp (s x)) else (Env, s x))"

primrec assemble_state :: "(nat \<Rightarrow> nat) \<Rightarrow> state\<^sub>r \<Rightarrow> assm_state" where
  "assemble_state mp (S\<^sub>r h hp e ep vs vp sh sp pc) = 
    S\<^sub>a (case_prod (case_memseg (assemble_heap mp h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assemble_stack mp sh sp) undefined)) 
        (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, sp) (Acc, 0)) (mp pc)"
                                     
abbreviation assm_hp :: "code\<^sub>b list \<Rightarrow> (nat \<Rightarrow> pointer_tag \<times> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memseg \<times> nat" 
    where
  "assm_hp cd \<equiv> assemble_heap (assembly_map cd)"

abbreviation assm_stk :: "code\<^sub>b list \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memseg \<times> nat" where
  "assm_stk cd \<equiv> assemble_stack (assembly_map cd)"

abbreviation assm_state :: "code\<^sub>b list \<Rightarrow> state\<^sub>r \<Rightarrow> assm_state" where
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
  lookup (concat (map_with_idx k (assemble_op (assembly_map (cd' @ cd))) cd)) (x + assembly_map cd pc) = 
    lookup (assemble_op (assembly_map (cd' @ cd)) (pc + k) op) x"
proof (induction cd pc arbitrary: cd' k rule: assembly_map.induct)
  case (3 op' cd y)
  moreover hence "lookup cd y = Some op" by simp
  ultimately have "lookup (concat (map_with_idx (Suc k) (assemble_op (assembly_map ((cd' @ [op']) @ cd))) cd)) (x + assembly_map cd y) =
      lookup (assemble_op (assembly_map ((cd' @ [op']) @ cd)) (y + Suc k) op) x" by blast
  hence "lookup (concat (map_with_idx (Suc k) (assemble_op (assembly_map (cd' @ op' # cd))) cd))
    (x + assembly_map cd y) =
      lookup (assemble_op (assembly_map (cd' @ op' # cd)) (Suc (y + k)) op) x" by simp
  moreover have "assemble_op (assembly_map (cd' @ op' # cd)) \<circ> (+) (Suc k) = 
    (\<lambda>z. assemble_op (assembly_map (cd' @ op' # cd)) (Suc (k + z)))" by auto
  ultimately have "lookup (assemble_op (assembly_map (cd' @ op' # cd)) k op' @
      concat (map_with_idx (Suc k) (assemble_op (assembly_map (cd' @ op' # cd))) cd))
     (assemble_op_len op' + (Suc (x + assembly_map cd y))) =
    lookup (assemble_op (assembly_map (cd' @ op' # cd)) (Suc (y + k)) op) x" by simp
  moreover have "assemble_op_len op' + (Suc (x + assembly_map cd y)) = 
    Suc (x + (assemble_op_len op' + assembly_map cd y))" by simp
  ultimately have "lookup (assemble_op (assembly_map (cd' @ op' # cd)) k op' @
      concat (map_with_idx (Suc k) (assemble_op (assembly_map (cd' @ op' # cd))) cd))
     (Suc (x + (assemble_op_len op' + assembly_map cd y))) =
    lookup (assemble_op (assembly_map (cd' @ op' # cd)) (Suc (y + k)) op) x"
    by metis
  thus ?case by simp
qed simp_all

lemma assemble_code_lookup' [simp]: "lookup cd pc = Some op \<Longrightarrow> x \<le> assemble_op_len op \<Longrightarrow> 
  lookup (concat (map_with_idx 0 (assemble_op (assembly_map (cd' @ cd))) cd)) (x + assembly_map cd pc) = 
    lookup (assemble_op (assembly_map (cd' @ cd)) pc op) x"
proof -
  assume "lookup cd pc = Some op" and "x \<le> assemble_op_len op"
  hence "lookup (concat (map_with_idx 0 (assemble_op (assembly_map (cd' @ cd))) cd)) (x + assembly_map cd pc) = 
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

lemma [simp]: "x \<noteq> hp \<Longrightarrow> assm_hp cd (h(hp := a)) (Suc hp) x = assm_hp cd h hp x"
  by (simp add: assemble_heap_def)












definition assembleable_heap :: "(nat \<Rightarrow> pointer_tag \<times> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd = (even p\<^sub>h \<and>
    (\<forall>x < p\<^sub>h. fst (h x) = PEnv \<longrightarrow> even (snd (h x)) \<and> snd (h x) \<le> p\<^sub>\<Delta>) \<and> 
    (\<forall>x < p\<^sub>h. fst (h x) = PCode \<longrightarrow> snd (h x) \<noteq> 0 \<and> snd (h x) \<le> lcd))"

definition assembleable_env :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h = (even p\<^sub>\<Delta> \<and>
    (\<forall>x < p\<^sub>\<Delta>. even (\<Delta> x) \<and> (if even x then \<Delta> x < p\<^sub>h else \<Delta> x < p\<^sub>\<Delta>)))"

definition assembleable_vals :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "assembleable_vals \<V> p\<^sub>\<V> p\<^sub>h = (even p\<^sub>h \<and> (\<forall>x < p\<^sub>\<V>. even (\<V> x) \<and> \<V> x < p\<^sub>h))"

definition assembleable_stack :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "assembleable_stack s p\<^sub>s p\<^sub>\<Delta> lcd = (\<forall>x < p\<^sub>s. 
    if x = 0 then s x = 0 else if even x then s x \<noteq> 0 \<and> s x \<le> lcd else even (s x) \<and> s x \<le> p\<^sub>\<Delta>)"

primrec assembleable :: "state\<^sub>r \<Rightarrow> code\<^sub>b list \<Rightarrow> bool" where
  "assembleable (S\<^sub>r h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> p\<^sub>\<V> s p\<^sub>s p\<^sub>\<C>) \<C> = (p\<^sub>\<C> \<le> length \<C> \<and> 
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

lemma [elim]: "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> even p\<^sub>\<Delta>"
  by (simp add: assembleable_env_def)

lemma [elim]: "assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> even p\<^sub>h"
  by (simp add: assembleable_heap_def)

lemma [simp]: "assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> 
    assembleable_heap (h(p\<^sub>h := (PConst, k), Suc p\<^sub>h := (PConst, 0))) (Suc (Suc p\<^sub>h)) p\<^sub>\<Delta> lcd"
  by (auto simp add: assembleable_heap_def)

lemma [simp]: "assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> 
  assembleable_heap (h(p\<^sub>h := (PEnv, k), Suc p\<^sub>h := (PCode, p\<^sub>\<C>))) (Suc (Suc p\<^sub>h)) p\<^sub>\<Delta> lcd = 
    (even k \<and> k \<le> p\<^sub>\<Delta> \<and> p\<^sub>\<C> \<noteq> 0 \<and> p\<^sub>\<C> \<le> lcd)"
proof
  let ?f = "\<lambda>x. if x = Suc p\<^sub>h then (PCode, p\<^sub>\<C>) else (h(p\<^sub>h := (PEnv, k))) x"

  assume "assembleable_heap (h(p\<^sub>h := (PEnv, k), Suc p\<^sub>h := (PCode, p\<^sub>\<C>))) (Suc (Suc p\<^sub>h)) p\<^sub>\<Delta> lcd"
  hence X: "even p\<^sub>h \<and>
    (\<forall>x<Suc (Suc p\<^sub>h). fst (?f x) = PEnv \<longrightarrow> even (snd (?f x)) \<and> snd (?f x) \<le> p\<^sub>\<Delta>) \<and>
    (\<forall>x<Suc (Suc p\<^sub>h). fst (?f x) = PCode \<longrightarrow> 0 < snd (?f x) \<and> snd (?f x) \<le> lcd)" 
      by (simp add: assembleable_heap_def)
  hence "p\<^sub>h < Suc (Suc p\<^sub>h) \<Longrightarrow> fst (?f p\<^sub>h) = PEnv \<Longrightarrow> even (snd (?f p\<^sub>h)) \<and> snd (?f p\<^sub>h) \<le> p\<^sub>\<Delta>" by blast
  moreover from X have "Suc p\<^sub>h < Suc (Suc p\<^sub>h) \<Longrightarrow> fst (?f (Suc p\<^sub>h)) = PCode \<Longrightarrow> 
    0 < snd (?f (Suc p\<^sub>h)) \<and> snd (?f (Suc p\<^sub>h)) \<le> lcd" by blast
  ultimately show "even k \<and> k \<le> p\<^sub>\<Delta> \<and> p\<^sub>\<C> \<noteq> 0 \<and> p\<^sub>\<C> \<le> lcd" by simp
next
  assume "assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd" and "even k \<and> k \<le> p\<^sub>\<Delta> \<and> p\<^sub>\<C> \<noteq> 0 \<and> p\<^sub>\<C> \<le> lcd"
  thus "assembleable_heap (h(p\<^sub>h := (PEnv, k), Suc p\<^sub>h := (PCode, p\<^sub>\<C>))) (Suc (Suc p\<^sub>h)) p\<^sub>\<Delta> lcd" 
    by (simp add: assembleable_heap_def)
qed

lemma [simp]: "assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> assembleable_heap h p\<^sub>h (Suc (Suc p\<^sub>\<Delta>)) lcd"
  by (auto simp add: assembleable_heap_def)

lemma [simp]: "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> assembleable_env \<Delta> p\<^sub>\<Delta> (Suc (Suc p\<^sub>h))"
  by (auto simp add: assembleable_env_def)

lemma [elim]: "p < p\<^sub>\<Delta> \<Longrightarrow> odd p \<Longrightarrow> assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> \<Delta> p < p\<^sub>\<Delta>"
  by (simp add: assembleable_env_def)

lemma [simp]: "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> assembleable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> 
  assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> h (\<V> p\<^sub>\<V>) = (PEnv, p\<^sub>\<Delta>') \<Longrightarrow>
    assembleable_env (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := p\<^sub>\<Delta>')) (Suc (Suc p\<^sub>\<Delta>)) p\<^sub>h"
proof (unfold assembleable_env_def assembleable_vals_def assembleable_heap_def, 
       rule, simp, rule, rule)
  fix y 
  assume "even p\<^sub>h \<and> (\<forall>x < Suc (Suc p\<^sub>\<V>). even (\<V> x) \<and> \<V> x < p\<^sub>h)"
  hence "even p\<^sub>h \<and> even (\<V> p\<^sub>\<V>) \<and> \<V> p\<^sub>\<V> < p\<^sub>h" by simp
  moreover assume "even p\<^sub>h \<and>
         (\<forall>x<p\<^sub>h. fst (h x) = PEnv \<longrightarrow> even (snd (h x)) \<and> snd (h x) \<le> p\<^sub>\<Delta>) \<and>
         (\<forall>x<p\<^sub>h. fst (h x) = PCode \<longrightarrow> snd (h x) \<noteq> 0 \<and> snd (h x) \<le> lcd)"
  ultimately have "fst (h (\<V> p\<^sub>\<V>)) = PEnv \<Longrightarrow> 
    even (snd (h (\<V> p\<^sub>\<V>))) \<and> snd (h (\<V> p\<^sub>\<V>)) \<le> p\<^sub>\<Delta>" by fastforce
  moreover assume "h (\<V> p\<^sub>\<V>) = (PEnv, p\<^sub>\<Delta>')" 
    and "even p\<^sub>\<Delta> \<and> (\<forall>x < p\<^sub>\<Delta>. even (\<Delta> x) \<and> (if even x then \<Delta> x < p\<^sub>h else \<Delta> x < p\<^sub>\<Delta>))"
    and "y < Suc (Suc p\<^sub>\<Delta>)" 
    and "even p\<^sub>h \<and> (\<forall>x < Suc (Suc p\<^sub>\<V>). even (\<V> x) \<and> \<V> x < p\<^sub>h)"
  ultimately show "even ((\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := p\<^sub>\<Delta>')) y) \<and> (if even y
    then (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := p\<^sub>\<Delta>')) y < p\<^sub>h
    else (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := p\<^sub>\<Delta>')) y < Suc (Suc p\<^sub>\<Delta>))" by auto
qed

lemma [simp]: "assembleable_vals \<V> p\<^sub>\<V> p\<^sub>h \<Longrightarrow> 
    assembleable_vals (\<V>(p\<^sub>\<V> := k)) (Suc p\<^sub>\<V>) p\<^sub>h = (even p\<^sub>h \<and> k < p\<^sub>h \<and> even k)"
  by (auto simp add: assembleable_vals_def)

lemma [simp]: "assembleable_vals \<V> p\<^sub>\<V> p\<^sub>h \<Longrightarrow> 
    assembleable_vals (\<V>(p\<^sub>\<V> := k)) (Suc p\<^sub>\<V>) (Suc (Suc p\<^sub>h)) = (even p\<^sub>h \<and> k < Suc (Suc p\<^sub>h) \<and> even k)"
  by (auto simp add: assembleable_vals_def)

lemma [elim]: "assembleable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> assembleable_vals \<V> p\<^sub>\<V> p\<^sub>h"
  by (simp add: assembleable_vals_def)

lemma [elim]: "assembleable_vals \<V> (Suc b\<^sub>\<V>) b\<^sub>h \<Longrightarrow> assembleable_vals \<V> b\<^sub>\<V> b\<^sub>h"
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

lemma [elim]: "h (Suc (\<V> p\<^sub>\<V>)) = (PCode, 0) \<Longrightarrow> assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> 
  assembleable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> False"
proof (unfold assembleable_heap_def assembleable_vals_def)
  assume "even p\<^sub>h \<and> (\<forall>x < Suc (Suc p\<^sub>\<V>). even (\<V> x) \<and> \<V> x < p\<^sub>h)"
  hence "even p\<^sub>h \<and> even (\<V> p\<^sub>\<V>) \<and> \<V> p\<^sub>\<V> < p\<^sub>h" by simp
  hence "Suc (\<V> p\<^sub>\<V>) < p\<^sub>h" by fastforce
  moreover assume "even p\<^sub>h \<and>
    (\<forall>x<p\<^sub>h. fst (h x) = PEnv \<longrightarrow> even (snd (h x)) \<and> snd (h x) \<le> p\<^sub>\<Delta>) \<and>
    (\<forall>x<p\<^sub>h. fst (h x) = PCode \<longrightarrow> snd (h x) \<noteq> 0 \<and> snd (h x) \<le> lcd)"
     and "h (Suc (\<V> p\<^sub>\<V>)) = (PCode, 0)"
  ultimately show False by auto
qed

lemma [simp]: "h (Suc (\<V> p\<^sub>\<V>)) = (PCode, p\<^sub>\<C>) \<Longrightarrow> assembleable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> 
    assembleable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> p\<^sub>\<C> \<le> lcd"
proof (unfold assembleable_heap_def assembleable_vals_def)
  assume "even p\<^sub>h \<and> (\<forall>x < Suc (Suc p\<^sub>\<V>). even (\<V> x) \<and> \<V> x < p\<^sub>h)"
  hence "even p\<^sub>h \<and> even (\<V> p\<^sub>\<V>) \<and> \<V> p\<^sub>\<V> < p\<^sub>h" by simp
  hence "Suc (\<V> p\<^sub>\<V>) < p\<^sub>h" by fastforce
  moreover assume "even p\<^sub>h \<and>
    (\<forall>x<p\<^sub>h. fst (h x) = PEnv \<longrightarrow> even (snd (h x)) \<and> snd (h x) \<le> p\<^sub>\<Delta>) \<and>
    (\<forall>x<p\<^sub>h. fst (h x) = PCode \<longrightarrow> snd (h x) \<noteq> 0 \<and> snd (h x) \<le> lcd)"
     and "h (Suc (\<V> p\<^sub>\<V>)) = (PCode, p\<^sub>\<C>)"
  ultimately show "p\<^sub>\<C> \<le> lcd" by auto
qed

lemma [elim]: "unstr_lookup \<Delta> p x = Some y \<Longrightarrow> p \<le> p\<^sub>\<Delta> \<Longrightarrow> even p \<Longrightarrow> assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> 
  y < p\<^sub>h"
proof (induction \<Delta> p x rule: unstr_lookup.induct)
  case (4 \<Delta> p x)
  moreover hence "even (\<Delta> (Suc p)) \<and> \<Delta> (Suc p) < p\<^sub>\<Delta>" by (simp add: assembleable_env_def)
  ultimately show ?case by simp
qed (auto simp add: assembleable_env_def)

lemma [elim]: "unstr_lookup \<Delta> p x = Some y \<Longrightarrow> p \<le> p\<^sub>\<Delta> \<Longrightarrow> even p \<Longrightarrow> assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> 
  even y"
proof (induction \<Delta> p x rule: unstr_lookup.induct) 
  case (4 \<Delta> p x)
  moreover hence "even (\<Delta> (Suc p)) \<and> \<Delta> (Suc p) < p\<^sub>\<Delta>" by (simp add: assembleable_env_def)
  ultimately show ?case by simp
qed (auto simp add: assembleable_env_def)

lemma [simp]: "odd p\<^sub>s \<Longrightarrow> assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> even (s p\<^sub>s)" 
  by (unfold assembleable_stack_def) (auto simp add: odd_pos)

lemma [simp]: "odd p\<^sub>s \<Longrightarrow> assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> s p\<^sub>s \<le> p\<^sub>\<Delta>" 
  by (unfold assembleable_stack_def) (auto simp add: odd_pos)

lemma [elim]: "unstr_lookup \<Delta> (s p\<^sub>s) x = Some y \<Longrightarrow> assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> 
  assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> odd p\<^sub>s \<Longrightarrow> y < p\<^sub>h"
proof -
  assume "odd p\<^sub>s" and "assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd"  
  hence "even (s p\<^sub>s)" and "s p\<^sub>s \<le> p\<^sub>\<Delta>" by auto
  moreover assume "unstr_lookup \<Delta> (s p\<^sub>s) x = Some y" and "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h"
  ultimately show "y < p\<^sub>h" by auto
qed

lemma [elim]: "unstr_lookup \<Delta> (s p\<^sub>s) x = Some y \<Longrightarrow> assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> 
  assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> odd p\<^sub>s \<Longrightarrow> even y"
proof -
  assume "odd p\<^sub>s" and "assembleable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd"  
  hence "s p\<^sub>s \<le> p\<^sub>\<Delta> \<and> even (s p\<^sub>s)" by simp
  moreover assume "unstr_lookup \<Delta> (s p\<^sub>s) x = Some y" and "assembleable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h"
  ultimately show "even y" by auto
qed

lemma [elim]: "assembleable_stack s (Suc (Suc p\<^sub>s)) p\<^sub>\<Delta> lcd \<Longrightarrow> assembleable_stack s p\<^sub>s p\<^sub>\<Delta> lcd"
  by (unfold assembleable_stack_def, rule) simp

lemma [elim]: "assembleable_heap h b\<^sub>h b\<^sub>\<Delta> lcd \<Longrightarrow> assembleable_env \<Delta> b\<^sub>\<Delta> b\<^sub>h \<Longrightarrow> 
  assembleable_vals \<V> (Suc b\<^sub>\<V>) b\<^sub>h \<Longrightarrow> assembleable_stack s (Suc b\<^sub>s) b\<^sub>\<Delta> lcd \<Longrightarrow> odd b\<^sub>s \<Longrightarrow> 
    assembleable_stack (s(b\<^sub>s := b\<^sub>\<Delta>)) (Suc b\<^sub>s) (Suc (Suc b\<^sub>\<Delta>)) lcd"
  by (unfold assembleable_stack_def assembleable_vals_def assembleable_env_def assembleable_heap_def, rule) simp

lemma preserve_restructure [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>r \<leadsto>\<^sub>r \<Sigma>\<^sub>r' \<Longrightarrow> assembleable \<Sigma>\<^sub>r \<C> \<Longrightarrow> 
    assembleable \<Sigma>\<^sub>r' \<C>"
  by (induction \<Sigma>\<^sub>r \<Sigma>\<^sub>r' rule: eval\<^sub>r.induct) auto

lemma [simp]: "iter (\<tturnstile> \<C> \<leadsto>\<^sub>r) \<Sigma>\<^sub>r \<Sigma>\<^sub>r' \<Longrightarrow> assembleable \<Sigma>\<^sub>r \<C> \<Longrightarrow> assembleable \<Sigma>\<^sub>r' \<C>"
  by (induction \<Sigma>\<^sub>r \<Sigma>\<^sub>r' rule: iter.induct) auto

lemma [simp]: "assembleable_heap nmem 0 0 x"
  using assembleable_heap_def by blast

lemma [simp]: "assembleable_env nmem 0 0"
  by (simp add: assembleable_env_def)

lemma [simp]: "assembleable_vals nmem 0 0" 
  by (simp add: assembleable_vals_def)

lemma [simp]: "assembleable_stack (nmem(0 := 0, Suc 0 := 0)) 2 0 lcd"
  by (simp only: assembleable_stack_def) (simp_all add: odd_pos)

lemma [simp]: "assembleable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> vs vp < hp"
proof (unfold assembleable_vals_def)
  assume "even hp \<and> (\<forall>x<Suc (Suc vp). even (vs x) \<and> vs x < hp)"
  hence "even hp \<and> even (vs vp) \<and> vs vp < hp" by simp
  thus ?thesis by fastforce
qed

lemma [simp]: "assembleable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> Suc (vs vp) < hp"
proof (unfold assembleable_vals_def)
  assume "even hp \<and> (\<forall>x<Suc (Suc vp). even (vs x) \<and> vs x < hp)"
  hence "even hp \<and> even (vs vp) \<and> vs vp < hp" by simp
  thus ?thesis by fastforce
qed

lemma [simp]: "(assm_hp cd h hp)(hp := (Acc, a), Suc hp := (Acc, b)) = 
    assm_hp cd (h(hp := (PConst, a), Suc hp := (PConst, b))) (Suc (Suc hp))"
  by (auto simp add: assemble_heap_def)

lemma [simp]: "(assm_hp cd h hp) (hp := (Env, a), Suc hp := (Acc, assembly_map cd b)) = 
    assm_hp cd (h(hp := (PEnv, a), Suc hp := (PCode, b))) (Suc (Suc hp))"
  by (auto simp add: assemble_heap_def)

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

lemma [simp]: "assembleable_vals vs (Suc (Suc vp)) hp \<Longrightarrow> h (vs vp) = (PEnv, ep') \<Longrightarrow> 
  even ep \<Longrightarrow> assm_hp cd h hp (vs vp) = (k, b) \<Longrightarrow> 
    (assemble_env e ep)(ep := (Hp, a), Suc ep := (k, b)) = 
      assemble_env (e(ep := a, Suc ep := ep')) (Suc (Suc ep))"
proof (rule, unfold assemble_env_def)
  fix y
  assume "assembleable_vals vs (Suc (Suc vp)) hp" 
  hence "Suc (vs vp) < hp" by simp
  moreover assume "h (vs vp) = (PEnv, ep')"
     and "assm_hp cd h hp (vs vp) = (k, b)"
  ultimately have "k = Env \<and> b = ep'" by (simp add: assemble_heap_def split: if_splits prod.splits)
  moreover assume "even ep"
  ultimately show "((\<lambda>x. if ep \<le> x then (Acc, 0) else (if even x then Hp else Env, e x)) 
    (ep := (Hp, a), Suc ep := (k, b))) y =
      (if Suc (Suc ep) \<le> y then (Acc, 0)
        else (if even y then Hp else Env, (e(ep := a, Suc ep := ep')) y))" 
    by (simp add: assemble_heap_def split: if_splits prod.splits)
qed

lemma assm_hp_code: "h (Suc (vs vp)) = (PCode, pc) \<Longrightarrow> even ep \<Longrightarrow> 
  assembleable_vals vs (Suc (Suc vp)) hp \<Longrightarrow>
    assm_hp cd h hp (Suc (vs vp)) = (Acc, assembly_map cd pc)"
proof -
  assume "assembleable_vals vs (Suc (Suc vp)) hp"
  hence "Suc (vs vp) < hp" by simp
  thus "h (Suc (vs vp)) = (PCode, pc) \<Longrightarrow> even ep \<Longrightarrow> 
    assm_hp cd h hp (Suc (vs vp)) = (Acc, assembly_map cd pc)"
      by (auto simp add: assemble_heap_def split: prod.splits pointer_tag.splits)
qed

lemma [simp]: "(case_memseg hp ep vp sp a)(Hp := hp') = case_memseg hp' ep vp sp a"
  by rule (simp split: memseg.splits)

lemma [simp]: "(case_memseg hp ep vp sp a)(Env := ep') = case_memseg hp ep' vp sp a"
  by rule (simp split: memseg.splits)

lemma [simp]: "(case_memseg hp ep vp sp a)(Vals := vp') = case_memseg hp ep vp' sp a"
  by rule (simp split: memseg.splits)

lemma [simp]: "(case_memseg hp ep vp sp a)(Stk := sp') = case_memseg hp ep vp sp' a"
  by rule (simp split: memseg.splits)

lemma [simp]: "(case_memseg hp ep vp sp a)(Acc := a') = case_memseg hp ep vp sp a'"
  by rule (simp split: memseg.splits)

lemma [simp]: "unstr_lookup e a x = Some v \<Longrightarrow> lookup cd pc = Some (Lookup\<^sub>b y) \<Longrightarrow> x \<le> y \<Longrightarrow> 
  pc < length cd \<Longrightarrow> a \<le> ep \<Longrightarrow> assembleable_env e ep hp \<Longrightarrow> iter_eval\<^sub>a (assemble_code cd) 
    (5 + 2 * x) (S\<^sub>a (case_prod (case_memseg h (assemble_env e ep) vs sh undefined)) 
      (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, sp) (Env, a)) 
        (5 + 2 * x + assembly_map cd pc)) = Some (S\<^sub>a (case_prod (case_memseg h (assemble_env e ep)
          (vs(vp := (Hp, v))) sh undefined)) (case_memseg (Hp, hp) (Env, ep) (Vals, Suc vp) 
            (Stk, sp) (Acc, 0)) (assembly_map cd pc))"
proof (induction e a x rule: unstr_lookup.induct)
  case (3 e p)
  moreover from 3 have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (ASub Acc (Con 2))" by simp
  moreover from 3 have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Acc))" by simp
  moreover from 3 have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AMov (Mem Vals) (Reg Acc))" by (simp del: add_2_eq_Suc)
  ultimately show ?case 
    by (auto simp add: numeral_def assemble_env_def split: if_splits prod.splits memseg.splits)
next
  case (4 e p x)
  moreover hence "lookup (assemble_code cd) (6 + 2 * x + assembly_map cd pc) = 
    Some (ASub Acc (Con 1))" by simp
  moreover from 4 have "lookup (assemble_code cd) (5 + 2 * x + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Acc))" by simp
  ultimately have X: "iter_eval\<^sub>a (assemble_code cd) 2 (S\<^sub>a (case_prod (case_memseg h (assemble_env e ep) vs 
    sh undefined)) (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, sp) (Env, Suc (Suc p)))
      (7 + 2 * x + assembly_map cd pc)) = Some (S\<^sub>a (case_prod (case_memseg h (assemble_env e ep) vs sh undefined)) 
        (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, sp) (Env, e (Suc p))) (5 + 2 * x + assembly_map cd pc))" 
    by (simp add: numeral_def assemble_env_def split: if_splits) presburger
  from 4 have "Suc p < ep" and "even p" and "assembleable_env e ep hp" by (auto split: if_splits)
  hence "e (Suc p) < ep" by (auto split: if_splits)
  moreover with 4 have "iter_eval\<^sub>a (assemble_code cd) (5 + 2 * x)
    (S\<^sub>a (case_prod (case_memseg h (assemble_env e ep) vs sh undefined)) (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, sp) (Env, e (Suc p)))
      (5 + 2 * x + assembly_map cd pc)) = Some (S\<^sub>a (case_prod (case_memseg h (assemble_env e ep) 
        (vs(vp := (Hp, v))) sh undefined)) (case_memseg (Hp, hp) (Env, ep) (Vals, Suc vp) (Stk, sp) (Acc, 0))
          (assembly_map cd pc))" by (simp split: if_splits)
  with X have "iter_eval\<^sub>a (assemble_code cd) (2 + (5 + 2 * x))
    (S\<^sub>a (case_prod (case_memseg h (assemble_env e ep) vs sh undefined)) (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, sp) (Env, Suc (Suc p))) 
      (7 + 2 * x + assembly_map cd pc)) = Some (S\<^sub>a (case_prod (case_memseg h (assemble_env e ep) 
        (vs(vp := (Hp, v))) sh undefined)) (case_memseg (Hp, hp) (Env, ep) (Vals, Suc vp) (Stk, sp) (Acc, 0))
          (assembly_map cd pc))" 
    using iter_eval\<^sub>a_combine by blast
  thus ?case by simp
qed simp_all

theorem correcta [simp]: "cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>r \<leadsto>\<^sub>r \<Sigma>\<^sub>r' \<Longrightarrow> assembleable \<Sigma>\<^sub>r cd\<^sub>b \<Longrightarrow> 
  \<exists>n. iter_eval\<^sub>a (assemble_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>r) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>r')"
proof (induction cd\<^sub>b \<Sigma>\<^sub>r \<Sigma>\<^sub>r' rule: eval\<^sub>r.induct)
  case (ev\<^sub>r_lookup cd pc x e sh sp y h hp ep vs vp)
  moreover hence "odd sp" by simp
  moreover from ev\<^sub>r_lookup have "lookup (assemble_code cd) (7 + 2 * x + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Reg Stk))" by simp
  moreover from ev\<^sub>r_lookup have "lookup (assemble_code cd) (6 + 2 * x + assembly_map cd pc) = 
    Some (ASub Acc (Con 1))" by simp
  moreover from ev\<^sub>r_lookup have "lookup (assemble_code cd) (5 + 2 * x + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Acc))" by simp
  ultimately have X: "iter_eval\<^sub>a (assemble_code cd) 3 
    (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp)) undefined)) (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, Suc sp) (Acc, 0))
        (8 + 2 * x + assembly_map cd pc)) = Some (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc sp)) undefined)) 
            (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, Suc sp) (Env, sh sp)) (5 + 2 * x + assembly_map cd pc))" 
    by (simp add: numeral_def)
  from ev\<^sub>r_lookup have "sh sp \<le> ep" by auto
  with ev\<^sub>r_lookup have "iter_eval\<^sub>a (assemble_code cd) (5 + 2 * x) 
    (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp)) undefined)) (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, Suc sp) (Env, sh sp))
        (5 + 2 * x + assembly_map cd pc)) = Some (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals (vs(vp := y)) (Suc vp)) (assm_stk cd sh (Suc sp)) undefined)) 
            (case_memseg (Hp, hp) (Env, ep) (Vals, Suc vp) (Stk, Suc sp) (Acc, 0)) (assembly_map cd pc))" 
    by auto
  with X have "iter_eval\<^sub>a (assemble_code cd) (3 + (5 + 2 * x)) 
    (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp)) undefined)) (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, Suc sp) (Acc, 0))
        (8 + 2 * x + assembly_map cd pc)) = Some (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals (vs(vp := y)) (Suc vp)) (assm_stk cd sh (Suc sp)) undefined))
            (case_memseg (Hp, hp) (Env, ep) (Vals, Suc vp) (Stk, Suc sp) (Acc, 0)) (assembly_map cd pc))" 
    using iter_eval\<^sub>a_combine by blast
  hence "iter_eval\<^sub>a (assemble_code cd) (3 + (5 + 2 * x)) 
    (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
      (assm_stk cd sh (Suc sp)) undefined)) (case_memseg(Hp, hp) (Env, ep) (Vals, vp) (Stk, Suc sp) (Acc, 0))
        (8 + (2 * x + assembly_map cd pc))) = Some (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) 
          (assemble_env e ep) (assemble_vals (vs(vp := y)) (Suc vp)) (assm_stk cd sh (Suc sp)) undefined)) 
            (case_memseg (Hp, hp) (Env, ep) (Vals, Suc vp) (Stk, Suc sp) (Acc, 0)) (assembly_map cd pc))"
    by (simp add: add.assoc)
  with ev\<^sub>r_lookup show ?case by auto
next
  case (ev\<^sub>r_pushcon cd pc k h hp e ep vs vp sh sp)
  moreover from ev\<^sub>r_pushcon have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AMov (Mem Vals) (Reg Hp))" by simp
  moreover from ev\<^sub>r_pushcon have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AAdd Vals (Con 1))" by simp
  moreover from ev\<^sub>r_pushcon have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AMov (Mem Hp) (Con k))" by simp 
  moreover from ev\<^sub>r_pushcon have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAdd Hp (Con 1))" by (simp del: add_2_eq_Suc)
  ultimately have "iter_eval\<^sub>a (assemble_code cd) 6 (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc sp)) undefined))
      (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, Suc sp) (Acc, 0)) (assembly_map cd (Suc pc))) = Some (S\<^sub>a 
        (case_prod (case_memseg (assm_hp cd (h(hp := (PConst, k), Suc hp := (PConst, 0))) (2 + hp)) 
          (assemble_env e ep) (assemble_vals (vs(vp := hp)) (Suc vp)) 
            (assm_stk cd sh (Suc sp)) undefined)) (case_memseg (Hp, 2 + hp) (Env, ep) (Vals, Suc vp) (Stk, Suc sp) (Acc, 0)) 
              (assembly_map cd pc))" 
    by (auto simp add: numeral_def assemble_heap_def assemble_vals_def 
             split: prod.splits memseg.splits)
  thus ?case by auto
next
  case (ev\<^sub>r_pushlam cd pc pc' h hp e ep vs vp sh sp)
  moreover from ev\<^sub>r_pushlam have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (AMov (Mem Vals) (Reg Hp))" by simp
  moreover from ev\<^sub>r_pushlam have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (AAdd Vals (Con 1))" by simp
  moreover from ev\<^sub>r_pushlam have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Reg Stk))" by simp
  moreover from ev\<^sub>r_pushlam have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (ASub Acc (Con 1))" by simp
  moreover from ev\<^sub>r_pushlam have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Acc))" by simp
  moreover from ev\<^sub>r_pushlam have "lookup (assemble_code cd) (4 + assembly_map cd pc) =
    Some (AMov (Mem Hp) (Reg Acc))" by simp
  moreover from ev\<^sub>r_pushlam have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AAdd Hp (Con 1))" by simp
  moreover from ev\<^sub>r_pushlam have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Con 0))" by (simp del: add_2_eq_Suc)
  ultimately have "iter_eval\<^sub>a (assemble_code cd) 10 (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc sp)) undefined)) 
      (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, Suc sp) (Acc, 0)) (assembly_map cd (Suc pc))) = Some (S\<^sub>a 
        (case_prod (case_memseg (assm_hp cd (h(hp := (PEnv, sh sp), Suc hp := (PCode, pc'))) (2 + hp)) 
          (assemble_env e ep) (assemble_vals (vs(vp := hp)) (Suc vp)) 
            (assm_stk cd sh (Suc sp)) undefined)) (case_memseg (Hp, 2 + hp) (Env, ep) (Vals, Suc vp) (Stk, Suc sp) (Acc, 0)) 
              (assembly_map cd pc))" 
    by (auto simp add: numeral_def assemble_heap_def assemble_vals_def 
             split: prod.splits memseg.splits)
  thus ?case by auto
next
  case (ev\<^sub>r_apply cd pc h vs vp ep' pc' hp e ep sh sp)
  moreover hence "even ep" by auto
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (20 + assembly_map cd pc) = 
    Some (ASub Vals (Con 1))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (19 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Vals))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (18 + assembly_map cd pc) = 
    Some (AMov (Mem Vals) (Con 0))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (17 + assembly_map cd pc) = 
    Some (AMov (Mem Env) (Reg Acc))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (16 + assembly_map cd pc) = 
    Some (AAdd Env (Con 1))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (15 + assembly_map cd pc) = 
    Some (AMov (Mem Stk) (Con (assembly_map cd pc)))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (14 + assembly_map cd pc) = 
    Some (AAdd Stk (Con 1))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (13 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Reg Env))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (12 + assembly_map cd pc) = 
    Some (AAdd Acc (Con 1))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (11 + assembly_map cd pc) = 
    Some (AMov (Mem Stk) (Reg Acc))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (10 + assembly_map cd pc) = 
    Some (AAdd Stk (Con 1))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (ASub Vals (Con 1))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Vals))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Acc))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (AMov (Mem Env) (Reg Acc))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd Env (Con 1))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Vals))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AMov (Mem Vals) (Con 0))" by simp
  moreover from ev\<^sub>r_apply have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAdd Acc (Con 1))" by (simp del: add_2_eq_Suc)
  moreover from ev\<^sub>r_apply have "assm_hp cd h hp (Suc (vs vp)) = (Acc, assembly_map cd pc')" 
    by (metis assm_hp_code assembleable.simps)
  ultimately have "iter_eval\<^sub>a (assemble_code cd) 21 (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs (Suc (Suc vp))) (assm_stk cd sh (Suc sp)) undefined))
      (case_memseg (Hp, hp) (Env, ep) (Vals, Suc (Suc vp)) (Stk, Suc sp) (Acc, 0)) (assembly_map cd (Suc pc))) = 
        Some (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) (assemble_env (e(ep := vs (Suc vp), 
          Suc ep := ep')) (Suc (Suc ep))) (assemble_vals vs vp) 
            (assm_stk cd (sh(Suc sp := pc, Suc (Suc sp) := Suc (Suc ep))) (Suc (Suc (Suc sp)))) undefined)) 
              (case_memseg (Hp, hp) (Env, Suc (Suc ep)) (Vals, vp) (Stk, Suc (Suc (Suc sp))) (Acc, 0))
                (assembly_map cd pc'))"
    by (auto simp add: numeral_def assemble_vals_def split: prod.splits) 
       (rule,
        auto simp add: assemble_vals_def assemble_heap_def assemble_env_def assemble_stack_def 
             split: prod.splits memseg.splits if_splits)
  thus ?case by auto
next
  case (ev\<^sub>r_pushenv \<C> p\<^sub>\<C> h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> b\<^sub>\<V> s b\<^sub>s)
  moreover from ev\<^sub>r_pushenv have "lookup (assemble_code \<C>) (11 + assembly_map \<C> p\<^sub>\<C>) = 
    Some (ASub Vals (Con 1))" by simp
  moreover from ev\<^sub>r_pushenv have "lookup (assemble_code \<C>) (10 + assembly_map \<C> p\<^sub>\<C>) = 
    Some (AMov (Reg Acc) (Mem Vals))" by simp
  moreover from ev\<^sub>r_pushenv have "lookup (assemble_code \<C>) (9 + assembly_map \<C> p\<^sub>\<C>) = 
    Some (AMov (Mem Vals) (Con 0))" by simp
  moreover from ev\<^sub>r_pushenv have "lookup (assemble_code \<C>) (8 + assembly_map \<C> p\<^sub>\<C>) = 
    Some (AMov (Mem Env) (Reg Acc))" by simp
  moreover from ev\<^sub>r_pushenv have "lookup (assemble_code \<C>) (7 + assembly_map \<C> p\<^sub>\<C>) = 
    Some (AAdd Env (Con 1))" by simp
  moreover from ev\<^sub>r_pushenv have "lookup (assemble_code \<C>) (6 + assembly_map \<C> p\<^sub>\<C>) = 
    Some (ASub Stk (Con 1))" by simp
  moreover from ev\<^sub>r_pushenv have "lookup (assemble_code \<C>) (5 + assembly_map \<C> p\<^sub>\<C>) = 
    Some (AMov (Reg Acc) (Mem Stk))" by simp
  moreover from ev\<^sub>r_pushenv have "lookup (assemble_code \<C>) (4 + assembly_map \<C> p\<^sub>\<C>) = 
    Some (AMov (Mem Env) (Reg Acc))" by simp
  moreover from ev\<^sub>r_pushenv have "lookup (assemble_code \<C>) (3 + assembly_map \<C> p\<^sub>\<C>) = 
    Some (AAdd Env (Con 1))" by simp
  moreover from ev\<^sub>r_pushenv have "lookup (assemble_code \<C>) (2 + assembly_map \<C> p\<^sub>\<C>) = 
    Some (AMov (Mem Stk) (Reg Env))" by (simp del: add_2_eq_Suc)
  ultimately have "iter_eval\<^sub>a (assemble_code \<C>) 12 (S\<^sub>a (case_prod (case_memseg (assm_hp \<C> h b\<^sub>h) 
    (assemble_env \<Delta> b\<^sub>\<Delta>) (assemble_vals \<V> (Suc b\<^sub>\<V>)) (assm_stk \<C> s (Suc b\<^sub>s)) undefined))
      (case_memseg (Hp, b\<^sub>h) (Env, b\<^sub>\<Delta>) (Vals, Suc b\<^sub>\<V>) (Stk, Suc b\<^sub>s) (Acc, 0)) 
        (assembly_map \<C> (Suc p\<^sub>\<C>))) = Some (S\<^sub>a (case_prod (case_memseg (assm_hp \<C> h b\<^sub>h) 
          (assemble_env (\<Delta>(b\<^sub>\<Delta> := \<V> b\<^sub>\<V>, Suc b\<^sub>\<Delta> := s b\<^sub>s)) (Suc (Suc b\<^sub>\<Delta>))) (assemble_vals \<V> b\<^sub>\<V>) 
            (assm_stk \<C> (s(b\<^sub>s := b\<^sub>\<Delta>)) (Suc b\<^sub>s)) undefined)) (case_memseg (Hp, b\<^sub>h) (Env, Suc (Suc b\<^sub>\<Delta>)) 
              (Vals, b\<^sub>\<V>) (Stk, Suc b\<^sub>s) (Acc, 0)) (assembly_map \<C> p\<^sub>\<C>))"
    by (auto simp add: numeral_def assemble_stack_def split: prod.splits memseg.splits)
  thus ?case by auto
next
  case (ev\<^sub>r_return cd pc h hp e ep vs vp sh sp)
  moreover from ev\<^sub>r_return have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (ASub Stk (Con 1))" by simp
  moreover from ev\<^sub>r_return have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AMov (Mem Stk) (Con 0))" by simp
  moreover from ev\<^sub>r_return have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (ASub Stk (Con 1))" by simp
  moreover from ev\<^sub>r_return have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Stk))" by (simp del: add_2_eq_Suc)
  ultimately have "iter_eval\<^sub>a (assemble_code cd) 6 (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs vp) (assm_stk cd sh (Suc (Suc sp))) undefined)) 
      (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, Suc (Suc sp)) (Acc, 0)) (assembly_map cd (Suc pc))) = 
        Some (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) (assemble_env e ep) (assemble_vals vs vp) 
          (assm_stk cd sh sp) undefined)) (case_memseg (Hp, hp) (Env, ep) (Vals, vp) (Stk, sp) (Acc, 0)) (assembly_map cd (sh sp)))"
    by (auto simp add: numeral_def assemble_stack_def split: prod.splits memseg.splits)
  thus ?case by auto
next
  case (ev\<^sub>r_jump cd pc h vs vp ep' pc' hp e ep sh sp)
  moreover hence "even ep" by auto
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (19 + assembly_map cd pc) = 
    Some (ASub Vals (Con 1))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (18 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Vals))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (17 + assembly_map cd pc) = 
    Some (AMov (Mem Vals) (Con 0))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (16 + assembly_map cd pc) = 
    Some (AMov (Mem Env) (Reg Acc))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (15 + assembly_map cd pc) = 
    Some (AAdd Env (Con 1))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (14 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Reg Env))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (13 + assembly_map cd pc) = 
    Some (AAdd Acc (Con 1))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (12 + assembly_map cd pc) = 
    Some (ASub Stk (Con 1))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (11 + assembly_map cd pc) = 
    Some (AMov (Mem Stk) (Reg Acc))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (10 + assembly_map cd pc) =
    Some (AAdd Stk (Con 1))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (9 + assembly_map cd pc) = 
    Some (ASub Vals (Con 1))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (8 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Vals))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (7 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Acc))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (6 + assembly_map cd pc) = 
    Some (AMov (Mem Env) (Reg Acc))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (5 + assembly_map cd pc) = 
    Some (AAdd Env (Con 1))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (4 + assembly_map cd pc) = 
    Some (AMov (Reg Acc) (Mem Vals))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (3 + assembly_map cd pc) = 
    Some (AMov (Mem Vals) (Con 0))" by simp
  moreover from ev\<^sub>r_jump have "lookup (assemble_code cd) (2 + assembly_map cd pc) = 
    Some (AAdd Acc (Con 1))" by (simp del: add_2_eq_Suc)
  moreover from ev\<^sub>r_jump have "assm_hp cd h hp (Suc (vs vp)) = (Acc, assembly_map cd pc')" 
    by (metis assm_hp_code assembleable.simps)
  ultimately have "iter_eval\<^sub>a (assemble_code cd) 20 (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) 
    (assemble_env e ep) (assemble_vals vs (Suc (Suc vp))) (assm_stk cd sh (Suc sp)) undefined))
      (case_memseg (Hp, hp) (Env, ep) (Vals, Suc (Suc vp)) (Stk, Suc sp) (Acc, 0)) (assembly_map cd (Suc pc))) = 
        Some (S\<^sub>a (case_prod (case_memseg (assm_hp cd h hp) (assemble_env (e(ep := vs (Suc vp), 
          Suc ep := ep')) (Suc (Suc ep))) (assemble_vals vs vp) 
            (assm_stk cd (sh(sp := Suc (Suc ep))) (Suc sp)) undefined)) (case_memseg (Hp, hp) 
              (Env, Suc (Suc ep)) (Vals, vp) (Stk, Suc sp) (Acc, 0)) (assembly_map cd pc'))"
    by (auto simp add: numeral_def assemble_vals_def split: prod.splits)
       (rule, auto simp add: assemble_env_def assemble_heap_def assemble_vals_def assemble_stack_def 
                   split: prod.splits memseg.splits)
  thus ?case by auto
qed

lemma [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>r) \<Sigma>\<^sub>r \<Sigma>\<^sub>r' \<Longrightarrow> assembleable \<Sigma>\<^sub>r cd\<^sub>b \<Longrightarrow> 
  \<exists>n. iter_eval\<^sub>a (assemble_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>r) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>r')"
proof (induction \<Sigma>\<^sub>r \<Sigma>\<^sub>r' rule: iter.induct)
  case (iter_refl \<Sigma>\<^sub>r)
  have "iter_eval\<^sub>a (assemble_code cd\<^sub>b) 0 (assm_state cd\<^sub>b \<Sigma>\<^sub>r) = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>r)" by simp
  thus ?case by blast
next
  case (iter_step \<Sigma>\<^sub>r \<Sigma>\<^sub>r' \<Sigma>\<^sub>r'')
  then obtain n where "iter_eval\<^sub>a (assemble_code cd\<^sub>b) n (assm_state cd\<^sub>b \<Sigma>\<^sub>r) = 
    Some (assm_state cd\<^sub>b \<Sigma>\<^sub>r')" by (metis correcta)
  moreover from iter_step obtain m where "
    iter_eval\<^sub>a (assemble_code cd\<^sub>b) m (assm_state cd\<^sub>b \<Sigma>\<^sub>r') = Some (assm_state cd\<^sub>b \<Sigma>\<^sub>r'')" 
    by (metis preserve_restructure)
  ultimately have "iter_eval\<^sub>a (assemble_code cd\<^sub>b) (n + m) (assm_state cd\<^sub>b \<Sigma>\<^sub>r) = 
    Some (assm_state cd\<^sub>b \<Sigma>\<^sub>r'')" by simp
  thus ?case by blast
qed

theorem correct\<^sub>a_iter [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>r) \<Sigma>\<^sub>r \<Sigma>\<^sub>r' \<Longrightarrow> assembleable \<Sigma>\<^sub>r cd\<^sub>b \<Longrightarrow> 
    iter (\<tturnstile> assemble_code cd\<^sub>b \<leadsto>\<^sub>a) (assm_state cd\<^sub>b \<Sigma>\<^sub>r) (assm_state cd\<^sub>b \<Sigma>\<^sub>r')"
  by simp

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
        by (metisx assembly_map_postpend append.assoc length_append length_flatten')

lemma assembly_map_flatten' [simp]: "properly_terminated\<^sub>e cd \<Longrightarrow>
  assembly_map (lib @ flatten_code' (length lib) cd) (length lib + code_list_size cd) = 
    sum_list (map (Suc \<circ> assemble_op_len) (lib @ flatten_code' (length lib) cd))"
proof (induction "length lib" cd arbitrary: lib rule: flatten_code'.induct)
  case (2 x \<C>)
  then show ?case by simp
next
  case (3 n \<C>)
  then show ?case by simp
next
  case (4 \<C>' \<C>)
  case (4 cd' cd)
  let ?lib = "lib @ flatten_code' (length lib) cd'"
  let ?cd = "flatten_code' (length ?lib) cd"
  have X: "assembly_map (?lib @ ?cd @ [PushLam\<^sub>b (length lib + code_list_size cd')]) 
    (length ?lib + code_list_size cd) = assembly_map (?lib @ ?cd) (length (?lib @ ?cd))" 
      by (metisx assembly_map_postpend append.assoc length_append length_flatten')
  from 4 have Y: "properly_terminated\<^sub>e cd" by simp
  have "length lib + length (flatten_code' (length lib) cd') = length ?lib" by simp
  with 4 Y have "assembly_map (?lib @ ?cd) (length ?lib + code_list_size cd) =
    sum_list (map (Suc \<circ> assemble_op_len) (?lib @ ?cd))" by blast
  with X show ?case by (simp add: add.assoc) 
next
  case (5 \<C>)
  then show ?case by simp
next
  case (6 \<C>)
  then show ?case by simp
next
  case (7 \<C>)
  then show ?case by simp
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