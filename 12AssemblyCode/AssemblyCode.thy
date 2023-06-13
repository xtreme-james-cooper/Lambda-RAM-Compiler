theory AssemblyCode
  imports "../00Utils/Iteration" "../00Utils/Environment"
begin

section \<open>Assembly Code\<close>

text \<open>With our transitions reduced to simple function updates and arithmetic operations, we are 
ready to take the final step and move to a low-level, machine-like execution model. For the first 
time, we have choices in our development: we could use a real processor (any of a number of real 
processors, for that matter) or define our own. For simplicity - and because our correctness proof 
relies on a truly unbounded memory, indexed by unbounded naturals, which no real machine has - we 
define a simple machine based in a general way on Nisan and Schocken's tutorial HACK processor [4].\<close>

text \<open>Our processor has five registers, one each for the stack pointers for the value heap, 
environment heap, value stack, and callstack, and one as an accumulator. It also has a special 
register for the code-pointer, and an infinite natural-indexed memory.\<close>

text \<open>For this stage, in order to ease the already quite-involved conversion, we imbue the processor 
with a little more structure. We tag each memory cell and the accumulator register with a memory 
segment, to say what kind of pointer lives in it. (\<open>Acc\<close> stands for non-pointers.) We also keep our 
four memory segments separate in the memory map; this leaves us with an extra segment for \<open>Acc\<close> but
it will remain unused and we will arrange to allocate no space for it in the final memory layout.\<close>

datatype memseg = Hp | Env | Vals | Stk | Acc

datatype assm_state = S\<^sub>a "memseg \<Rightarrow> nat \<Rightarrow> memseg \<times> nat" "memseg \<Rightarrow> nat" memseg nat

text \<open>We have a small, RISC-like (not to say minimalistic) set of operations on the processor. We 
can do simple arithmetic on the registers; we can move values between registers, and load and store 
into memory; and we can jump, to a static address or indirectly to an address in a register. We will
not need all of even this small set of functionality (we never add or subtract a non-constant, or 
make a direct jump, for instance) but we include it to make the processor plausible and for future 
expansion of the source language.\<close>

text \<open>In our assembler, we allow ourselves some liberties with the opcodes. The operate-on-register/
operate-on-constant opcodes are collapsed into a single assembly operation; and the move/load/store 
operations are likewise reduced to a single \<open>AMov\<close> operation with a number of addressing modes.\<close>

datatype addr_mode = Reg memseg | Con nat

datatype move_src = Reg memseg | Con nat | Mem memseg

datatype assm = 
  APut memseg move_src
  | ASub memseg nat
  | AAdd memseg nat
  | AJmp

fun mem_upd :: "(memseg \<Rightarrow> nat \<Rightarrow> memseg \<times> nat) \<Rightarrow> memseg \<Rightarrow> nat \<Rightarrow> memseg \<times> nat \<Rightarrow> 
    memseg \<Rightarrow> nat \<Rightarrow> memseg \<times> nat" where
  "mem_upd mem m mp k m' x = (if m = m' \<and> mp = x then k else mem m' x)"

inductive evala :: "assm list \<Rightarrow> assm_state \<Rightarrow> assm_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>a" 50) where
  eva_movr [simp]: "lookup cd pc = Some (APut Acc (Reg r)) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a mem (ps(Acc := ps r)) r pc"
| eva_mova [simp]: "lookup cd pc = Some (APut Acc (Reg Acc)) \<Longrightarrow> 
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a mem ps act pc"
| eva_movk [simp]: "lookup cd pc = Some (APut Acc (Con k)) \<Longrightarrow> 
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a mem (ps(Acc := k)) Acc pc"
| eva_lod [simp]: "lookup cd pc = Some (APut Acc (Mem r')) \<Longrightarrow> mem r' (ps r') = (t, b) \<Longrightarrow> r' \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a mem (ps(Acc := b)) t pc"
| eva_loda [simp]: "lookup cd pc = Some (APut Acc (Mem Acc)) \<Longrightarrow> mem act (ps Acc) = (t, b) \<Longrightarrow> act \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a mem (ps(Acc := b)) t pc"
| eva_putr [simp]: "lookup cd pc = Some (APut r (Reg r')) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow> r' \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a (mem_upd mem r (ps r) (r', ps r')) ps act pc"
| eva_puta [simp]: "lookup cd pc = Some (APut r (Reg Acc)) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a (mem_upd mem r (ps r) (act, ps Acc)) ps act pc"
| eva_putk [simp]: "lookup cd pc = Some (APut r (Con k)) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a (mem_upd mem r (ps r) (Acc, k)) ps act pc"
| eva_get [simp]: "lookup cd pc = Some (APut r (Mem r')) \<Longrightarrow> mem r' (ps r') = (r, b) \<Longrightarrow> 
      r' \<noteq> Acc \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a mem (ps(r := b)) act pc"
| eva_geta [simp]: "lookup cd pc = Some (APut r (Mem Acc)) \<Longrightarrow> mem act (ps Acc) = (r, b) \<Longrightarrow> 
      r \<noteq> Acc \<Longrightarrow> act \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a mem (ps(r := b)) act pc"
| eva_suba [simp]: "lookup cd pc = Some (ASub Acc k) \<Longrightarrow> ps Acc \<ge> k \<Longrightarrow> act \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a mem (ps(Acc := ps Acc - k)) act pc"
| eva_sub [simp]: "lookup cd pc = Some (ASub r k) \<Longrightarrow> ps r \<ge> k \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a mem (ps(r := ps r - k)) act pc"
| eva_add [simp]: "lookup cd pc = Some (AAdd r k) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a mem (ps(r := ps r + k)) act pc"
| eva_adda [simp]: "lookup cd pc = Some (AAdd Acc k) \<Longrightarrow> act \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a S\<^sub>a mem (ps(Acc := ps Acc + k)) act pc"
| eva_jmp [simp]: "lookup cd pc = Some AJmp \<Longrightarrow> 
    cd \<tturnstile> S\<^sub>a mem ps Acc (Suc pc) \<leadsto>\<^sub>a S\<^sub>a mem (ps(Acc := 0)) Acc (ps Acc)"

abbreviation reg_merge :: "memseg \<Rightarrow> memseg \<Rightarrow> memseg" where
  "reg_merge a b \<equiv> (if a = Acc then b else a)"

fun assm_step :: "(memseg \<Rightarrow> nat \<Rightarrow> memseg \<times> nat) \<Rightarrow> (memseg \<Rightarrow> nat) \<Rightarrow> memseg \<Rightarrow> nat \<Rightarrow> 
    assm \<rightharpoonup> assm_state" where
  "assm_step mem ps act pc (APut Acc (Reg r')) = 
    Some (S\<^sub>a mem (ps(Acc := ps r')) (reg_merge r' act) pc)"
| "assm_step mem ps act pc (APut Acc (Con k)) = 
    Some (S\<^sub>a mem (ps(Acc := k)) Acc pc)"
| "assm_step mem ps act pc (APut Acc (Mem r')) = (case mem (reg_merge r' act) (ps r') of
     (t, b) \<Rightarrow> if r' \<noteq> Acc \<or> act \<noteq> Acc then Some (S\<^sub>a mem (ps(Acc := b)) t pc) else None)"
| "assm_step mem ps act pc (APut r (Reg r')) = 
    Some (S\<^sub>a (mem_upd mem r (ps r) (reg_merge r' act, ps r')) ps act pc)"
| "assm_step mem ps act pc (APut r (Con k)) = 
    Some (S\<^sub>a (mem_upd mem r (ps r) (Acc, k)) ps act pc)"
| "assm_step mem ps act pc (APut r (Mem r')) = (case mem (reg_merge r' act) (ps r') of
     (t, b) \<Rightarrow> if t = r \<and> (r' \<noteq> Acc \<or> act \<noteq> Acc) then Some (S\<^sub>a mem (ps(r := b)) act pc) else None)"
| "assm_step mem ps act pc (ASub r k) = 
    (if ps r < k \<or> (r = Acc \<and> act = Acc) then None 
     else Some (S\<^sub>a mem (ps(r := ps r - k)) act pc))"
| "assm_step mem ps act pc (AAdd r k) = 
    (if r = Acc \<and> act = Acc then None 
     else Some (S\<^sub>a mem (ps(r := ps r + k)) act pc))"
| "assm_step mem ps act pc AJmp = 
    (if act = Acc then Some (S\<^sub>a mem (ps(Acc := 0)) Acc (ps Acc)) else None)"

fun alg_evala :: "assm list \<Rightarrow> assm_state \<rightharpoonup> assm_state" (infix "\<tturnstile>\<^sub>a" 50) where
  "cd \<tturnstile>\<^sub>a S\<^sub>a mem ps act pc = (case pc of
      0 \<Rightarrow> None
    | Suc pc \<Rightarrow> Option.bind (lookup cd pc) (assm_step mem ps act pc))"

primrec iter_evala :: "assm list \<Rightarrow> nat \<Rightarrow> assm_state \<rightharpoonup> assm_state" where
  "iter_evala cd 0 \<Sigma> = Some \<Sigma>"
| "iter_evala cd (Suc x) \<Sigma> = Option.bind (cd \<tturnstile>\<^sub>a \<Sigma>) (iter_evala cd x)"

lemma [simp]: "mem_upd (case_memseg h e vs sh a) Hp x y = case_memseg (h(x := y)) e vs sh a"
proof (rule, rule)
  fix m n
  show "mem_upd (case_memseg h e vs sh a) Hp x y m n = case_memseg (h(x := y)) e vs sh a m n"
    by (induction m) (simp_all split: memseg.splits)
qed

lemma [simp]: "mem_upd (case_memseg h e vs sh a) Env x y = case_memseg h (e(x := y)) vs sh a"
proof (rule, rule)
  fix m n
  show "mem_upd (case_memseg h e vs sh a) Env x y m n = case_memseg h (e(x := y)) vs sh a m n"
    by (induction m) (simp_all split: memseg.splits)
qed

lemma [simp]: "mem_upd (case_memseg h e vs sh a) Vals x y = case_memseg h e (vs(x := y)) sh a"
proof (rule, rule)
  fix m n
  show "mem_upd (case_memseg h e vs sh a) Vals x y m n = case_memseg h e (vs(x := y)) sh a m n"
    by (induction m) (simp_all split: memseg.splits)
qed

lemma [simp]: "mem_upd (case_memseg h e vs sh a) Stk x y = case_memseg h e vs (sh(x := y)) a"
proof (rule, rule)
  fix m n
  show "mem_upd (case_memseg h e vs sh a) Stk x y m n = case_memseg h e vs (sh(x := y)) a m n"
    by (induction m) (simp_all split: memseg.splits)
qed

lemma iter_evala_combine [simp]: "iter_evala cd n \<Sigma> = Some \<Sigma>' \<Longrightarrow> 
  iter_evala cd m \<Sigma>' = Some \<Sigma>'' \<Longrightarrow> iter_evala cd (n + m) \<Sigma> = Some \<Sigma>''"
proof (induction n arbitrary: \<Sigma>)
  case (Suc n)
  then show ?case by (cases "cd \<tturnstile>\<^sub>a \<Sigma>") simp_all
qed simp_all

lemma assm_step_equiv: "(Option.bind (lookup cd pc) (assm_step mem ps act pc) = Some \<Sigma>) \<Longrightarrow>
  (cd \<tturnstile> S\<^sub>a mem ps act (Suc pc) \<leadsto>\<^sub>a \<Sigma>)"
proof (cases "lookup cd pc")
  case (Some op)
  moreover assume "Option.bind (lookup cd pc) (assm_step mem ps act pc) = Some \<Sigma>"
  ultimately show ?thesis 
  proof (induction mem ps act pc op rule: assm_step.induct)
    case (7 mem ps act pc r k)
    then show ?case by (cases r) (auto split: if_splits)
  next
    case (8 mem ps act pc r k)
    then show ?case by (cases r) (auto split: if_splits)
  qed (auto split: if_splits prod.splits option.splits)
qed simp_all

lemma alg_evala_equiv: "(cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>') = (cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>')"
proof
  show "cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>'"
    by (induction \<Sigma>) (auto simp add: assm_step_equiv split: nat.splits)
  show "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>' \<Longrightarrow> cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>'" 
  proof (induction cd \<Sigma> \<Sigma>' rule: evala.induct)
    case (eva_putr cd pc r r' mem ps act)
    thus ?case by (induction r) simp_all
  next
    case (eva_puta cd pc r mem ps act)
    thus ?case by (induction r) simp_all
  next
    case (eva_putk cd pc r k mem ps act)
    thus ?case by (induction r) simp_all
  next
    case (eva_get cd pc r r' mem ps b act)
    thus ?case by (induction r) simp_all
  next
    case (eva_geta cd pc r mem act ps b)
    thus ?case by (induction r) simp_all
  qed simp_all
qed

lemma iter_evala_equiv: "iter (\<tturnstile> cd \<leadsto>\<^sub>a) \<Sigma> \<Sigma>' = (\<exists>n. iter_evala cd n \<Sigma> = Some \<Sigma>')"
proof
  assume "\<exists>n. iter_evala cd n \<Sigma> = Some \<Sigma>'"
  then obtain n where "iter_evala cd n \<Sigma> = Some \<Sigma>'" by fastforce
  thus "iter (\<tturnstile> cd \<leadsto>\<^sub>a) \<Sigma> \<Sigma>'" 
  proof (induction n arbitrary: \<Sigma>)
    case (Suc n)
    thus ?case by (cases "cd \<tturnstile>\<^sub>a \<Sigma>") (simp_all add: alg_evala_equiv)
  qed simp_all
next
  show "iter (\<tturnstile> cd \<leadsto>\<^sub>a) \<Sigma> \<Sigma>' \<Longrightarrow> \<exists>n. iter_evala cd n \<Sigma> = Some \<Sigma>'" 
  proof (induction \<Sigma> \<Sigma>' rule: iter.induct)
    case (iter_refl \<Sigma>)
    have "iter_evala cd 0 \<Sigma> = Some \<Sigma>" by simp
    thus ?case by blast
  next
    case (iter_step \<Sigma> \<Sigma>' \<Sigma>'')
    then obtain n where "iter_evala cd n \<Sigma>' = Some \<Sigma>''" by fastforce
    moreover from iter_step have "cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>'" by (simp add: alg_evala_equiv)
    ultimately have "iter_evala cd (Suc n) \<Sigma> = Some \<Sigma>''" by simp
    thus ?case by blast
  qed
qed

theorem determinisma: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
  by (simp add: alg_evala_equiv)

end