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
  | ASub memseg addr_mode
  | AAdd memseg addr_mode
  | AJmp addr_mode

text \<open>The execution of the assembly code is complicated enough - and we will need to execute a lot 
of it in the conversion phase coming up - that for the first time we define reduction by a partial 
function rather than a relation. The steps are mostly straightforward, but note that in addition to
statically-invalid operations like \<open>AMov (Con n) x\<close>, we have some runtime checks as well: for 
instance, that the memory segment pointed to by \<open>r'\<close> in \<open>AMov (Reg r) (Mem r')\<close> is not \<open>Acc\<close> (since 
we never use the \<open>Acc\<close> memory segment). We arrange that, in the actual compiled code, these runtime 
tests always succeed; and so when we get to the final machine code, we will not have to check them.\<close>

fun assm_step :: "(memseg \<times> nat \<Rightarrow> memseg \<times> nat) \<Rightarrow> (memseg \<Rightarrow> memseg \<times> nat) \<Rightarrow> nat \<Rightarrow> assm \<rightharpoonup> 
    assm_state" where
  "assm_step \<mu> \<rho> p\<^sub>\<C> (AMov (Reg r) (Reg r')) = Some (S\<^sub>a \<mu> (\<rho>(r := \<rho> r')) p\<^sub>\<C>)"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (AMov (Reg r) (Con n)) = Some (S\<^sub>a \<mu> (\<rho>(r := (Acc, n))) p\<^sub>\<C>)"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (AMov (Reg r) (Mem r')) = (
    if fst (\<rho> r') \<noteq> Acc then Some (S\<^sub>a \<mu> (\<rho>(r := \<mu> (\<rho> r'))) p\<^sub>\<C>) else None)"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (AMov (Con n) x) = None"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (AMov (Mem r) (Reg r')) = (
    if fst (\<rho> r) \<noteq> Acc then Some (S\<^sub>a (\<mu>(\<rho> r := \<rho> r')) \<rho> p\<^sub>\<C>) else None)"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (AMov (Mem r) (Con n)) = (
    if fst (\<rho> r) \<noteq> Acc then Some (S\<^sub>a (\<mu>(\<rho> r := (Acc, n))) \<rho> p\<^sub>\<C>) else None)"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (AMov (Mem r) (Mem r')) = None"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (ASub r (Reg r')) = (case (\<rho> r, \<rho> r') of
    ((t, v), (t', v')) \<Rightarrow> 
      if v \<ge> v' \<and> t = Acc \<and> t' = Acc then Some (S\<^sub>a \<mu> (\<rho>(r := (t, v - v'))) p\<^sub>\<C>) else None)"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (ASub r (Con n)) = (case \<rho> r of
    (t, v) \<Rightarrow> if v \<ge> n \<and> t \<noteq> Acc then Some (S\<^sub>a \<mu> (\<rho>(r := (t, v - n))) p\<^sub>\<C>) else None)"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (ASub r (Mem r')) = None"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (AAdd r (Reg r')) = (case (\<rho> r, \<rho> r') of
    ((t, v), (t', v')) \<Rightarrow> 
      if t = Acc \<and> t' = Acc then Some (S\<^sub>a \<mu> (\<rho>(r := (t, v + v'))) p\<^sub>\<C>) else None)"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (AAdd r (Con n)) = (case \<rho> r of
    (t, v) \<Rightarrow> if t \<noteq> Acc then Some (S\<^sub>a \<mu> (\<rho>(r := (t, v + n))) p\<^sub>\<C>) else None)"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (AAdd r (Mem r')) = None"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (AJmp (Reg r)) = (case \<rho> r of
    (t, v) \<Rightarrow> if t = Acc then Some (S\<^sub>a \<mu> (\<rho>(r := (Acc, 0))) v) else None)"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (AJmp (Con k)) = Some (S\<^sub>a \<mu> \<rho> k)"
| "assm_step \<mu> \<rho> p\<^sub>\<C> (AJmp (Mem r)) = None"

fun eval\<^sub>a :: "assm list \<Rightarrow> assm_state \<rightharpoonup> assm_state" where
  "eval\<^sub>a \<C> (S\<^sub>a \<mu> \<rho> 0) = None"
| "eval\<^sub>a \<C> (S\<^sub>a \<mu> \<rho> (Suc p\<^sub>\<C>)) = Option.bind (lookup \<C> p\<^sub>\<C>) (assm_step \<mu> \<rho> p\<^sub>\<C>)"

text \<open>We define a relation based on the evaluation function to use as our "standard" evaluation 
relation. With a functional evaluation relation, determinism becomes trivial.\<close>

abbreviation some_eval\<^sub>a :: "assm list \<Rightarrow> assm_state \<Rightarrow> assm_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>a" 50) where
  "\<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>' \<equiv> (eval\<^sub>a \<C> \<Sigma> = Some \<Sigma>')"

theorem determinism\<^sub>a: "\<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>' \<Longrightarrow> \<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
  by simp

text \<open>We also define an iterated form of evaluation, which again will be useful for our assembly 
conversion. It recurses on an operation counter, so it cannot evaluate a block of code indefinitely 
to completion - as is only proper, since our assembly code is Turing-complete and can loop (consider 
\<open>0: AJmp (Con 0)\<close>, for instance). We will only ever need to evaluate fixed amounts of code in our 
conversion correctness proof, so it isn't a problem in practice.\<close>

primrec iter_eval\<^sub>a :: "assm list \<Rightarrow> nat \<Rightarrow> assm_state \<rightharpoonup> assm_state" where
  "iter_eval\<^sub>a \<C> 0 \<Sigma> = Some \<Sigma>"
| "iter_eval\<^sub>a \<C> (Suc x) \<Sigma> = Option.bind (eval\<^sub>a \<C> \<Sigma>) (iter_eval\<^sub>a \<C> x)"

lemma iter_eval\<^sub>a_combine [simp]: "iter_eval\<^sub>a \<C> n \<Sigma> = Some \<Sigma>' \<Longrightarrow> 
  iter_eval\<^sub>a \<C> m \<Sigma>' = Some \<Sigma>'' \<Longrightarrow> iter_eval\<^sub>a \<C> (n + m) \<Sigma> = Some \<Sigma>''"
proof (induction n arbitrary: \<Sigma>)
  case (Suc n)
  then show ?case by (cases "eval\<^sub>a \<C> \<Sigma>") simp_all
qed simp_all

lemma iter_eval\<^sub>a_equiv [simp]: "iter (\<tturnstile> \<C> \<leadsto>\<^sub>a) \<Sigma> \<Sigma>' = (\<exists>n. iter_eval\<^sub>a \<C> n \<Sigma> = Some \<Sigma>')"
proof 
  show "iter (\<tturnstile> \<C> \<leadsto>\<^sub>a) \<Sigma> \<Sigma>' \<Longrightarrow> \<exists>n. iter_eval\<^sub>a \<C> n \<Sigma> = Some \<Sigma>'" 
  proof (induction \<Sigma> \<Sigma>' rule: iter.induct)
    case (iter_refl \<Sigma>)
    have "iter_eval\<^sub>a \<C> 0 \<Sigma> = Some \<Sigma>" by simp
    thus ?case by blast
  next
    case (iter_step \<Sigma> \<Sigma>' \<Sigma>'')
    moreover then obtain n where "iter_eval\<^sub>a \<C> n \<Sigma>' = Some \<Sigma>''" by blast
    ultimately have "iter_eval\<^sub>a \<C> (Suc n) \<Sigma> = Some \<Sigma>''" by simp
    thus ?case by blast
  qed
next
  assume "\<exists>n. iter_eval\<^sub>a \<C> n \<Sigma> = Some \<Sigma>'"
  then obtain n where "iter_eval\<^sub>a \<C> n \<Sigma> = Some \<Sigma>'" by blast
  thus "iter (\<tturnstile> \<C> \<leadsto>\<^sub>a) \<Sigma> \<Sigma>'" 
  proof (induction n arbitrary: \<Sigma>)
    case (Suc n)
    thus ?case by (cases "eval\<^sub>a \<C> \<Sigma>") simp_all
  qed simp_all
qed

end