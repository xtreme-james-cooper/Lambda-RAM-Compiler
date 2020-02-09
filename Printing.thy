theory Printing
  imports "02Debruijn/NameRemoval" "04Closure/ClosureConversion" "05TreeCode/TreeCodeConversion"
    "06TailCall/TailCallOptimization" "07FlatCode/CodeFlattening" 
    "08HeapMemory/HeapConversion" "09FlatMemory/MemoryFlattening"
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
| "print_nexpr (NLam x t e) = ''<fun>''"
| "print_nexpr (NApp e\<^sub>1 e\<^sub>2) = undefined"

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

lemma [simp]: "valn e \<Longrightarrow> print_dexpr (convert e) = print_nexpr e" 
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

lemma [simp]: "print_hclosure (flatten_closure mp v) = print_hclosure v"
  by (induction v) simp_all

end