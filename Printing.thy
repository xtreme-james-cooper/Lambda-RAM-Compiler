theory Printing
  imports "02Typed/Typechecking" "03Debruijn/NameRemoval" "05Closure/ClosureConversion" 
    "06TreeCode/TreeCodeConversion" "07TailCall/TailCallOptimization" "08FlatCode/CodeFlattening" 
    "09HeapMemory/HeapConversion" "10ChainedEnvironment/Chaining" "11FlatMemory/MemoryFlattening"
    "13AssemblyCode/Assemble" "14MachineCode/Disassemble" 
begin

function string_of_nat :: "nat \<Rightarrow> string" where
  "n < 10 \<Longrightarrow> string_of_nat n = [char_of (48 + n)]"
| "n \<ge> 10 \<Longrightarrow> string_of_nat n = string_of_nat (n div 10) @ [char_of (48 + (n mod 10))]"
  by fastforce+
termination
  by (relation "measure id") simp_all

primrec print_nexpr :: "nexpr \<Rightarrow> string" where
  "print_nexpr (NVar x) = undefined"
| "print_nexpr (NConst k) = string_of_nat k"
| "print_nexpr (NLam x e) = ''<fun>''"
| "print_nexpr (NApp e\<^sub>1 e\<^sub>2) = undefined"

primrec print_texpr :: "texpr \<Rightarrow> string" where
  "print_texpr (texpr.TVar x) = undefined"
| "print_texpr (texpr.TConst k) = string_of_nat k"
| "print_texpr (texpr.TLam x t e) = ''<fun>''"
| "print_texpr (texpr.TApp e\<^sub>1 e\<^sub>2) = undefined"

primrec print_dexpr :: "dexpr \<Rightarrow> string" where
  "print_dexpr (DVar x) = undefined"
| "print_dexpr (DConst k) = string_of_nat k"
| "print_dexpr (DLam t e) = ''<fun>''"
| "print_dexpr (DApp e\<^sub>1 e\<^sub>2) = undefined"

primrec print_closure :: "closure \<Rightarrow> string" where
  "print_closure (CConst k) = string_of_nat k"
| "print_closure (CLam t cs e) = ''<fun>''"

primrec print_tclosure :: "tclosure \<Rightarrow> string" where
  "print_tclosure (TConst k) = string_of_nat k"
| "print_tclosure (TLam cs cd) = ''<fun>''"

primrec print_tco_closure :: "tco_closure \<Rightarrow> string" where
  "print_tco_closure (TCOConst k) = string_of_nat k"
| "print_tco_closure (TCOLam cs cd r) = ''<fun>''"

primrec print_bclosure :: "bclosure \<Rightarrow> string" where
  "print_bclosure (BConst k) = string_of_nat k"
| "print_bclosure (BLam cs pc) = ''<fun>''"

primrec print_hclosure :: "hclosure \<Rightarrow> string" where
  "print_hclosure (HConst k) = string_of_nat k"
| "print_hclosure (HLam cs pc) = ''<fun>''"

primrec print_ceclosure :: "ceclosure \<Rightarrow> string" where
  "print_ceclosure (CEConst k) = string_of_nat k"
| "print_ceclosure (CELam cs pc) = ''<fun>''"

fun print_uval :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> string" where
  "print_uval h p = (case h p of
      0 \<Rightarrow> ''<fun>''
    | Suc x \<Rightarrow> string_of_nat (h (Suc p)))"

fun print_mval :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> string" where
  "print_mval m p = (case m p of
      0 \<Rightarrow> ''<fun>'' 
    | Suc x \<Rightarrow> string_of_nat (m (4 + p)))"

lemma [simp]: "valt e \<Longrightarrow> print_texpr e = print_nexpr (erase e)" 
  by (induction e) (simp_all add: convert_def)

lemma [simp]: "valt e \<Longrightarrow> print_dexpr (convert e) = print_texpr e" 
  by (induction e) (simp_all add: convert_def)

lemma print_eqiv_declosure [simp]: "print_closure c = print_dexpr (declosure c)" 
proof (induction c)
  case (CLam t cs e)
  thus ?case by (induction cs arbitrary: e) simp_all
qed simp_all

lemma [simp]: "print_tco_closure (tco_val c) = print_tclosure c"
  by (induction c) simp_all

lemma [simp]: "print_tclosure (encode_closure c) = print_closure c" 
  by (induction c) (simp_all del: print_eqiv_declosure)

lemma [simp]: "print_bclosure c = print_tco_closure (unflatten_closure cd c)" 
  by (induction c) simp_all

lemma [simp]: "print_hclosure (hlookup h x) = print_bclosure (unheap_closure h x)"
  by (cases "hlookup h x") simp_all

lemma print_ce [simp]: "hcontains h x \<Longrightarrow> 
    print_ceclosure (hlookup h x) = print_hclosure (hlookup (unchain_heap h env) x)"
  by (cases "hlookup h x") simp_all

lemma [simp]: "print_ceclosure (flatten_closure' c) = print_ceclosure c"
  by (induction c) simp_all

lemma print_a [simp]: "3 dvd x \<Longrightarrow> print_uval (snd \<circ> assm_hp cd h) x = print_uval h x"
proof (induction "h x")
  case (Suc nat)
  hence "h x = Suc nat" by simp
  moreover from Suc have "3 dvd x" by simp
  moreover from Suc have "Suc x mod 3 = 1" by presburger
  ultimately show ?case by (simp add: assm_hp_lemma1 assm_hp_lemma2 split: nat.splits)
qed (simp_all add: assemble_heap_def)

lemma print_u [simp]: "print_uval h p = print_ceclosure (get_closure (H h hp) p)"
  by (cases "h p") simp_all

lemma print_m [simp]: "unmap_mem' p = (a, b) \<Longrightarrow> 
    print_mval (unmap_mem mem) p = print_uval (snd \<circ> mem a) b" 
  by simp

end