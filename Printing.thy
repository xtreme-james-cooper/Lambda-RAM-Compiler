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

primrec print_uval :: "ty \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> print" where
  "print_uval (Arrow t\<^sub>1 t\<^sub>2) h p = Fun"
| "print_uval Num h p = Number (h p)"

primrec print_mval :: "ty \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> print" where
  "print_mval (Arrow t\<^sub>1 t\<^sub>2) m p = Fun"
| "print_mval Num m p = Number (m p)"

primrec print_mach_state :: "ty \<Rightarrow> mach_state \<Rightarrow> print" where
  "print_mach_state t (MS rs mem pc) = print_mval t mem (mem 2)"

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

primrec closure_ty :: "closure\<^sub>v \<Rightarrow> ty" where
  "closure_ty (Const\<^sub>v n) = Num"
| "closure_ty (Lam\<^sub>v cs pc) = Arrow undefined undefined"

primrec top_level :: "ty \<Rightarrow> ty" where
  "top_level (Arrow t\<^sub>1 t\<^sub>2) = Arrow undefined undefined"
| "top_level Num = Num"

primrec get_closure :: "ty \<Rightarrow> (pointer_tag \<times> nat) heap \<Rightarrow> ptr \<Rightarrow> closure\<^sub>v" where
  "get_closure (Arrow t\<^sub>1 t\<^sub>2) h p = Lam\<^sub>v (snd (hlookup h p)) (snd (hlookup h (Suc p)))"
| "get_closure Num h p = Const\<^sub>v (snd (hlookup h p))"

lemma [dest]: "top_level t = Num \<Longrightarrow> t = Num"
  by (induction t) simp_all

lemma [dest]: "top_level t = Arrow undefined undefined \<Longrightarrow> \<exists>t\<^sub>1 t\<^sub>2. t = Arrow t\<^sub>1 t\<^sub>2"
  by (induction t) simp_all

lemma [simp]: "Map.empty \<turnstile>\<^sub>t v\<^sub>t : t \<Longrightarrow> value\<^sub>s v\<^sub>t \<Longrightarrow> print_ceclosure c = print_nexpr v\<^sub>t \<Longrightarrow> 
  closure_ty c = top_level t"
proof (induction "Map.empty :: var \<rightharpoonup> ty" v\<^sub>t t rule: typing\<^sub>t.induct)
  case (tc\<^sub>t_const n)
  thus ?case by (cases c) simp_all
next
  case (tc\<^sub>t_lam x t\<^sub>1 e t\<^sub>2)
  thus ?case by (cases c) simp_all
qed simp_all

lemma [simp]: "hcontains h v \<Longrightarrow> top_level t = closure_ty (hlookup h v) \<Longrightarrow>
  print_ceclosure (get_closure t (flatten_values h) (2 * v)) = 
    print_ceclosure (hlookup h v)"
  by (cases "hlookup h v") auto

lemma print_u [simp]: "print_uval t (snd \<circ> h) p = print_ceclosure (get_closure t (H h hp) p)"
  by (induction t) simp_all

lemma print_m [simp]: "unmap_mem' p = (a, b) \<Longrightarrow> 
    print_mval t (unmap_mem mem) p = print_uval t (pseudoreg_map \<circ> mem a) b"
  by (induction t) (simp_all add: unmap_mem_def)

primrec hp_tc :: "ty \<Rightarrow> (nat \<Rightarrow> pointer_tag \<times> nat) \<Rightarrow> ptr \<Rightarrow> bool" where
  "hp_tc (Arrow t\<^sub>1 t\<^sub>2) h p = (fst (h p) = PEnv \<and> fst (h (Suc p)) = PCode)"
| "hp_tc Num h p = (fst (h p) = PConst \<and> fst (h (Suc p)) = PConst)"

lemma [simp]: "top_level t = closure_ty (hlookup h\<^sub>c\<^sub>e v\<^sub>h) \<Longrightarrow> flatten_values h\<^sub>c\<^sub>e = H h\<^sub>u hp\<^sub>u \<Longrightarrow> 
  hcontains h\<^sub>c\<^sub>e v\<^sub>h \<Longrightarrow> hp_tc t h\<^sub>u (2 * v\<^sub>h)"
proof (induction h\<^sub>c\<^sub>e)
  case (H h\<^sub>c\<^sub>e hp\<^sub>c\<^sub>e)
  moreover hence "hlookup (H h\<^sub>u hp\<^sub>u) (2 * v\<^sub>h) = 
    (case (h\<^sub>c\<^sub>e v\<^sub>h) of Const\<^sub>v n \<Rightarrow> (PConst, n) | Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C> \<Rightarrow> (PEnv, 2 * p\<^sub>\<Delta>))" 
      by (metis lookup_flat_closure_0 hlookup.simps)
  moreover from H have "hlookup (H h\<^sub>u hp\<^sub>u) (1 + 2 * v\<^sub>h) = 
    (case (hlookup (H h\<^sub>c\<^sub>e hp\<^sub>c\<^sub>e) v\<^sub>h) of Const\<^sub>v n \<Rightarrow> (PConst, 0) | Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C> \<Rightarrow> (PCode, p\<^sub>\<C>))" 
      by (metis plus_1_eq_Suc lookup_flat_closure_1)
  ultimately show ?case by (cases "h\<^sub>c\<^sub>e v\<^sub>h") auto
qed

lemma print_a [simp]: "Suc x < hp \<Longrightarrow> hp_tc t h x \<Longrightarrow>
    print_uval t (pseudoreg_map \<circ> assm_hp cd h hp) x = print_uval t (snd \<circ> h) x"
  by (induction t) (auto simp add: assemble_heap_def split: prod.splits pointer_tag.splits)

lemma flatten_lt_3: "hcontains h x \<Longrightarrow> flatten_values h = H h' hp \<Longrightarrow> Suc (2 * x) < hp"
  by simp

end