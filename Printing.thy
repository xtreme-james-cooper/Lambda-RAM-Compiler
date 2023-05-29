theory Printing
  imports "02Typed/Typechecking" "03Debruijn/NameRemoval" "05Closure/ClosureConversion" 
    "06TreeCode/TreeCodeConversion" "06TreeCode/TailCallOptimization" "07ByteCode/CodeFlattening" 
    "08HeapMemory/HeapConversion" "09ChainedEnvironment/Chaining" "10FlatMemory/MemoryFlattening" 
    "12AssemblyCode/Assemble" "13MachineCode/Disassemble" 
begin

datatype print = Number nat | Fun

primrec print_nexpr :: "'a expr\<^sub>s \<Rightarrow> print" where
  "print_nexpr (Var\<^sub>s x) = undefined"
| "print_nexpr (Const\<^sub>s n) = Number n"
| "print_nexpr (Lam\<^sub>s x t e) = Fun"
| "print_nexpr (App\<^sub>s e\<^sub>1 e\<^sub>2) = undefined"

primrec print_dexpr :: "expr\<^sub>d \<Rightarrow> print" where
  "print_dexpr (Var\<^sub>d x) = undefined"
| "print_dexpr (Const\<^sub>d n) = Number n"
| "print_dexpr (Lam\<^sub>d t e) = Fun"
| "print_dexpr (App\<^sub>d e\<^sub>1 e\<^sub>2) = undefined"

primrec print_closure :: "closure\<^sub>c \<Rightarrow> print" where
  "print_closure (Const\<^sub>c n) = Number n"
| "print_closure (Lam\<^sub>c t cs e) = Fun"

primrec print_eclosure :: "closure\<^sub>e \<Rightarrow> print" where
  "print_eclosure (Const\<^sub>e n) = Number n"
| "print_eclosure (Lam\<^sub>e cs cd) = Fun"

primrec print_bclosure :: "closure\<^sub>b \<Rightarrow> print" where
  "print_bclosure (Const\<^sub>b n) = Number n"
| "print_bclosure (Lam\<^sub>b cs pc) = Fun"

primrec print_hclosure :: "closure\<^sub>h \<Rightarrow> print" where
  "print_hclosure (Const\<^sub>h n) = Number n"
| "print_hclosure (Lam\<^sub>h cs pc) = Fun"

primrec print_ceclosure :: "closure\<^sub>v \<Rightarrow> print" where
  "print_ceclosure (Const\<^sub>v n) = Number n"
| "print_ceclosure (Lam\<^sub>v cs pc) = Fun"

fun print_uval :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> print" where
  "print_uval h p = (case h p of
      0 \<Rightarrow> Fun
    | Suc x \<Rightarrow> Number (h (Suc p)))"

fun print_mval :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> print" where
  "print_mval m p = (case m p of
      0 \<Rightarrow> Fun
    | Suc x \<Rightarrow> Number (m (4 + p)))"

primrec print_mach_state :: "mach_state \<Rightarrow> print" where
  "print_mach_state (MS rs mem pc) = print_mval mem (mem 2)"

lemma [simp]: "print_nexpr (erase e) = print_nexpr e" 
  by (induction e) simp_all

lemma [simp]: "print_dexpr (unname e) = print_nexpr e" 
  by (induction e) (simp_all add: unname_def)

lemma print_eqiv_declosure [simp]: "print_closure c = print_dexpr (declosure c)" 
proof (induction c)
  case (Lam\<^sub>c t cs e)
  thus ?case by (induction cs arbitrary: e) simp_all
qed simp_all

lemma [simp]: "print_eclosure (tco_val c) = print_eclosure c"
  by (induction c) simp_all

lemma [simp]: "print_eclosure (encode_closure c) = print_closure c" 
  by (induction c) (simp_all del: print_eqiv_declosure)

lemma [simp]: "print_bclosure c = print_eclosure (unflatten_closure cd c)" 
  by (induction c) simp_all

lemma [simp]: "print_hclosure (hlookup h x) = print_bclosure (unheap_closure h x)"
  by (cases "hlookup h x") simp_all

lemma print_ce [simp]: "hcontains h x \<Longrightarrow> 
    print_ceclosure (hlookup h x) = print_hclosure (hlookup (unchain_heap h env) x)"
  by (cases "hlookup h x") simp_all

lemma print_a [simp]: "3 dvd x \<Longrightarrow> Suc x < hp \<Longrightarrow> 
  print_uval (pseudoreg_map \<circ> assm_hp cd h hp) x = print_uval h x"
proof (induction "h x")
  case (Suc nat)
  hence "h x = Suc nat" by simp
  moreover from Suc have "3 dvd x" and "Suc x < hp" by simp_all
  moreover from Suc have "Suc x mod 3 = 1" by presburger
  ultimately show ?case by (simp add: assm_hp_lemma1 assm_hp_lemma2 split: nat.splits)
qed (simp_all add: assemble_heap_def)

fun get_closure :: "nat heap \<Rightarrow> ptr \<Rightarrow> closure\<^sub>v" where
  "get_closure h p = (case hlookup h p of
      0 \<Rightarrow> Lam\<^sub>v (hlookup h (Suc p)) (hlookup h (Suc (Suc p)))
    | Suc _ \<Rightarrow> Const\<^sub>v (hlookup h (Suc p)))"

primrec flatten_closure' :: "closure\<^sub>v \<Rightarrow> closure\<^sub>v" where
  "flatten_closure' (Const\<^sub>v k) = Const\<^sub>v k"
| "flatten_closure' (Lam\<^sub>v p pc) = Lam\<^sub>v (2 * p) pc"

lemma [simp]: "print_ceclosure (flatten_closure' c) = print_ceclosure c"
  by (induction c) simp_all

lemma [simp]: "hcontains h v \<Longrightarrow> 
    get_closure (flatten_values h) (3 * v) = flatten_closure' (hlookup h v)"
  by (simp split: closure\<^sub>v.splits)

lemma print_u [simp]: "print_uval h p = print_ceclosure (get_closure (H h hp) p)"
  by (cases "h p") simp_all

lemma print_m [simp]: "unmap_mem' p = (a, b) \<Longrightarrow> 
    print_mval (unmap_mem mem) p = print_uval (pseudoreg_map \<circ> mem a) b"
  by (induction p rule: unmap_mem'.induct) 
     (auto simp add: unmap_mem_def numeral_def split: nat.splits)

end