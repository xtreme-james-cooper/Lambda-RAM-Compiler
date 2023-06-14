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
with a little more structure. We tag each memory cell and register with a memory segment, to say 
what kind of pointer lives in it. (\<open>Acc\<close> stands for non-pointers; the tag for all registers except 
\<open>Acc\<close> will be the same as the register itself, but the uniformity of tagging all of them simplifies 
the representation and is helpful to later proofs.) We also keep our four memory segments separate 
in the memory map; this leaves us with an extra segment for \<open>Acc\<close> but it will remain unused and we 
will arrange to allocate no space for it in the final memory layout.\<close>

datatype memseg = Hp | Env | Vals | Stk | Acc

datatype assm_state = S\<^sub>a "memseg \<times> nat \<Rightarrow> memseg \<times> nat" "memseg \<Rightarrow> memseg \<times> nat" nat

text \<open>We have a small, RISC-like (not to say minimalistic) set of operations for the processor. We 
can do simple arithmetic on the registers; we can move values between registers, and load and store 
into memory; and we can jump, to a static address or indirectly to an address in a register. We will
not need all of even this small set of functionality (we never add or subtract a non-constant, or 
make a direct jump, for instance) but we include it to make the processor plausible and for future 
expansion of the source language.\<close>

text \<open>In our assembler, we allow ourselves some liberties with the opcodes. The operate-on-register/
operate-on-constant opcodes are collapsed into a single assembly operation; and the move/load/store 
operations are likewise reduced to a single \<open>AMov\<close> operation with a number of addressing modes. We 
do not syntactically rule out every invalid combination: \<open>AMov (Con 0) (Con 2)\<close> is permitted, for 
instance, even though you obviously cannot assign to the constant 0. Invalid operations, instead,
have no associated transition. There are a few less obvious invalid operations: for instance, in 
keeping with our desire to make a RISC-style processor, you cannot directly add the contents of 
memory to a register; it has to be explicitly loaded into another register with an \<open>AMov\<close> operation 
first.\<close>

datatype addr_mode = Reg memseg | Con nat | Mem memseg

datatype assm = 
  AMov addr_mode addr_mode
  | ASub memseg nat
  | AAdd memseg nat
  | AJmp

abbreviation reg_merge :: "memseg \<Rightarrow> memseg \<Rightarrow> memseg" where
  "reg_merge a b \<equiv> (if a = Acc then b else a)"

fun assm_step :: "(memseg \<times> nat \<Rightarrow> memseg \<times> nat) \<Rightarrow> (memseg \<Rightarrow> memseg \<times> nat) \<Rightarrow> nat \<Rightarrow> 
    assm \<rightharpoonup> assm_state" where
  "assm_step mem ps pc (AMov (Reg r) (Reg r')) = Some (S\<^sub>a mem (ps(r := ps r')) pc)"
| "assm_step mem ps pc (AMov (Reg r) (Con k)) = Some (S\<^sub>a mem (ps(r := (Acc, k))) pc)"
| "assm_step mem ps pc (AMov (Reg r) (Mem r')) = Some (S\<^sub>a mem (ps(r := mem (ps r'))) pc)"
| "assm_step mem ps pc (AMov (Con k) x) = None"
| "assm_step mem ps pc (AMov (Mem r) (Reg r')) = Some (S\<^sub>a (mem(ps r := ps r')) ps pc)"
| "assm_step mem ps pc (AMov (Mem r) (Con k)) = Some (S\<^sub>a (mem(ps r := (Acc, k))) ps pc)"
| "assm_step mem ps pc (AMov (Mem r) (Mem r')) = None"
| "assm_step mem ps pc (ASub r k) = (case ps r of
    (t, v) \<Rightarrow> if v < k then None else Some (S\<^sub>a mem (ps(r := (t, v - k))) pc))"
| "assm_step mem ps pc (AAdd r k) = (case ps r of
    (t, v) \<Rightarrow> Some (S\<^sub>a mem (ps(r := (t, v + k))) pc))"
| "assm_step mem ps pc AJmp = (case ps Acc of
    (t, v) \<Rightarrow> if t = Acc then Some (S\<^sub>a mem (ps(Acc := (Acc, 0))) v) else None)"

primrec eval\<^sub>a :: "assm list \<Rightarrow> assm_state \<rightharpoonup> assm_state" where
  "eval\<^sub>a cd (S\<^sub>a mem ps pc) = (case pc of
      0 \<Rightarrow> None
    | Suc pc' \<Rightarrow> Option.bind (lookup cd pc') (assm_step mem ps pc'))"

primrec iter_eval\<^sub>a :: "assm list \<Rightarrow> nat \<Rightarrow> assm_state \<rightharpoonup> assm_state" where
  "iter_eval\<^sub>a cd 0 \<Sigma> = Some \<Sigma>"
| "iter_eval\<^sub>a cd (Suc x) \<Sigma> = Option.bind (eval\<^sub>a cd \<Sigma>) (iter_eval\<^sub>a cd x)"

abbreviation some_eval\<^sub>a :: "assm list \<Rightarrow> assm_state \<Rightarrow> assm_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>a" 50) where
  "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>' \<equiv> (eval\<^sub>a cd \<Sigma> = Some \<Sigma>')"

lemma iter_evala_combine [simp]: "iter_eval\<^sub>a cd n \<Sigma> = Some \<Sigma>' \<Longrightarrow> 
  iter_eval\<^sub>a cd m \<Sigma>' = Some \<Sigma>'' \<Longrightarrow> iter_eval\<^sub>a cd (n + m) \<Sigma> = Some \<Sigma>''"
proof (induction n arbitrary: \<Sigma>)
  case (Suc n)
  then show ?case by (cases "eval\<^sub>a cd \<Sigma>") simp_all
qed simp_all

lemma iter_evala_equiv [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>a) \<Sigma> \<Sigma>' = (\<exists>n. iter_eval\<^sub>a cd n \<Sigma> = Some \<Sigma>')"
proof 
  show "iter (\<tturnstile> cd \<leadsto>\<^sub>a) \<Sigma> \<Sigma>' \<Longrightarrow> \<exists>n. iter_eval\<^sub>a cd n \<Sigma> = Some \<Sigma>'" 
  proof (induction \<Sigma> \<Sigma>' rule: iter.induct)
    case (iter_refl \<Sigma>)
    have "iter_eval\<^sub>a cd 0 \<Sigma> = Some \<Sigma>" by simp
    thus ?case by blast
  next
    case (iter_step \<Sigma> \<Sigma>' \<Sigma>'')
    moreover then obtain n where "iter_eval\<^sub>a cd n \<Sigma>' = Some \<Sigma>''" by blast
    ultimately have "iter_eval\<^sub>a cd (Suc n) \<Sigma> = Some \<Sigma>''" by simp
    thus ?case by blast
  qed
next
  assume "\<exists>n. iter_eval\<^sub>a cd n \<Sigma> = Some \<Sigma>'"
  then obtain n where "iter_eval\<^sub>a cd n \<Sigma> = Some \<Sigma>'" by blast
  thus "iter (\<tturnstile> cd \<leadsto>\<^sub>a) \<Sigma> \<Sigma>'" 
  proof (induction n arbitrary: \<Sigma>)
    case (Suc n)
    thus ?case by (cases "eval\<^sub>a cd \<Sigma>") simp_all
  qed simp_all
qed

theorem determinisma: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
  by simp

end