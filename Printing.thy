theory Printing
  imports NameRemoval ClosureConversion TreeCodeConversion CodeFlattening HeapConversion
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

primrec print_bclosure :: "bclosure \<Rightarrow> string" where
  "print_bclosure (BConst k) = string_of_nat k"
| "print_bclosure (BLam cs pc) = ''<fun>''"

fun print_hclosure :: "hclosure heap \<Rightarrow> ptr \<Rightarrow> string" where
  "print_hclosure h x = (case hlookup h x of 
      HConst k \<Rightarrow> string_of_nat k
    | HLam cs pc \<Rightarrow> ''<fun>'')"

lemma [simp]: "valn e \<Longrightarrow> print_dexpr (convert e) = print_nexpr e" 
  by (induction e) (simp_all add: convert_def)

lemma print_eqiv_declosure [simp]: "print_closure c = print_dexpr (declosure c)" 
proof (induction c)
  case (CLam t cs e)
  thus ?case by (induction cs arbitrary: e) simp_all
qed simp_all

lemma [simp]: "print_tclosure (compile_closure c) = print_closure c" 
  by (induction c) (simp_all del: print_eqiv_declosure)

lemma [simp]: "print_bclosure c = print_tclosure (unflatten_closure cd c)" 
  by (induction c) simp_all

lemma [simp]: "print_hclosure h x = print_bclosure (unheap_closure h x)"
  by (cases "hlookup h x") (auto simp add: unheap_closure.simps)

end