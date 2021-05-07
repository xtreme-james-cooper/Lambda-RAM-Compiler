theory Compiler
  imports Printing "04Stack/StackConversion" "12UnstructuredMemory/Unstructuring" 
    "14AssemblyCode/Assemble" 
begin

abbreviation code_compile :: "texpr \<Rightarrow> mach list" where
  "code_compile \<equiv> disassemble \<circ> fst \<circ> assemble \<circ> flatten_code \<circ> tco \<circ> encode \<circ> convert"

abbreviation compile :: "nexpr \<rightharpoonup> mach list" where 
  "compile \<equiv> map_option (code_compile \<circ> fst) \<circ> typecheck"

primrec tree_code_size :: "tree_code \<Rightarrow> nat"
    and tree_code_size_list :: "tree_code list \<Rightarrow> nat" where
  "tree_code_size (TLookup x) = 0"
| "tree_code_size (TPushCon k) = 0"
| "tree_code_size (TPushLam cd) = tree_code_size_list cd"
| "tree_code_size TApply = 0"
| "tree_code_size_list [] = 1"
| "tree_code_size_list (op # cd) = 
      Suc (if op = TApply \<and> cd = [] then 0 else tree_code_size op + tree_code_size_list cd)"

primrec alg_compile1 :: "var list \<Rightarrow> texpr \<Rightarrow> tree_code list \<Rightarrow> tree_code list" where
  "alg_compile1 \<Phi> (texpr.TVar x) acc = TLookup (the (idx_of \<Phi> x)) # acc"
| "alg_compile1 \<Phi> (texpr.TConst k) acc = TPushCon k # acc"
| "alg_compile1 \<Phi> (texpr.TLam x t e) acc = TPushLam (alg_compile1 (insert_at 0 x \<Phi>) e []) # acc"
| "alg_compile1 \<Phi> (texpr.TApp e\<^sub>1 e\<^sub>2) acc = alg_compile1 \<Phi> e\<^sub>1 (alg_compile1 \<Phi> e\<^sub>2 (TApply # acc))"

function alg_compile2 :: "nat \<Rightarrow> tree_code list \<Rightarrow> byte_code list \<Rightarrow> byte_code list" where
  "alg_compile2 lib [] acc = BReturn # acc"
| "alg_compile2 lib (TLookup x # cd) acc = alg_compile2 lib cd (BLookup x # acc)"
| "alg_compile2 lib (TPushCon k # cd) acc = alg_compile2 lib cd (BPushCon k # acc)"
| "alg_compile2 lib (TPushLam cd' # cd) acc =
    alg_compile2 lib cd' 
      (alg_compile2 (lib + tree_code_size_list cd') cd 
        (BPushLam (lib + tree_code_size_list cd') # acc))"
| "alg_compile2 lib (TApply # []) acc = BJump # acc"
| "alg_compile2 lib (TApply # op # cd) acc = alg_compile2 lib (op # cd) (BApply # acc)"
  by pat_completeness auto
termination
  by (relation "measure (tree_code_size_list \<circ> fst \<circ> snd)") simp_all

definition alg_compile :: "texpr \<Rightarrow> byte_code list" where
  "alg_compile e = alg_compile2 0 (alg_compile1 [] e []) []"

lemma [simp]: "alg_compile1 \<Phi> e acc = encode (convert' \<Phi> e) @ acc"
  by (induction e arbitrary: \<Phi> acc) simp_all

lemma [simp]: "tree_code_size_list cd = code_list_size (tco_cd cd)"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

lemma [simp]: "alg_compile2 lib cd acc = flatten_code' lib (tco_cd cd) (tco_r cd) @ acc"
  by (induction lib cd acc rule: alg_compile2.induct) simp_all

lemma [simp]: "alg_compile = flatten_code \<circ> tco \<circ> encode \<circ> convert"
  by rule (simp add: alg_compile_def convert_def tco_def)

end