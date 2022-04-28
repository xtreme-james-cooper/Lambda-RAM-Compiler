theory Compiler
  imports Printing "04Stack/StackConversion" "12UnstructuredMemory/Unstructuring" 
begin

abbreviation code_compile :: "texpr \<Rightarrow> mach list" where
  "code_compile \<equiv> disassemble \<circ> assemble_code \<circ> flatten_code \<circ> tco \<circ> encode \<circ> convert"

abbreviation compile :: "nexpr \<rightharpoonup> mach list" where 
  "compile \<equiv> map_option (code_compile \<circ> fst) \<circ> typecheck"

primrec quick_convert :: "var set \<Rightarrow> nexpr \<Rightarrow> hexpr \<times> var set" where
  "quick_convert vs (NVar x) = (HVar x, vs)"
| "quick_convert vs (NConst k) = (hexpr.HConst k, vs)"
| "quick_convert vs (NLam x e) = (
    let v = fresh vs
    in let (e', vs') = quick_convert (insert v vs) e
    in (hexpr.HLam x (Var v) e', vs'))"
| "quick_convert vs (NApp e\<^sub>1 e\<^sub>2) = (
    let v = fresh vs
    in let (e\<^sub>1', vs') = quick_convert (insert v vs) e\<^sub>1 
    in let (e\<^sub>2', vs'') = quick_convert vs' e\<^sub>2 
    in (HApp e\<^sub>1' e\<^sub>2', vs''))"

primrec collect_constraints :: "subst \<Rightarrow> var set \<Rightarrow> nexpr \<Rightarrow> uexpr \<times> var set \<times> (uexpr \<times> uexpr) list" 
    where
  "collect_constraints \<Gamma> vs (NVar x) = (case \<Gamma> x of 
      Some t \<Rightarrow> (t, vs, []) 
    | None \<Rightarrow> (Ctor ''Base'' [], vs, fail))"
| "collect_constraints \<Gamma> vs (NConst k) = (Ctor ''Base'' [], vs, [])"
| "collect_constraints \<Gamma> vs (NLam x e) = (
    let v = fresh vs
    in let (t, vs', con) = collect_constraints (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e
    in (Ctor ''Arrow'' [Var v, t], vs', con))"
| "collect_constraints \<Gamma> vs (NApp e\<^sub>1 e\<^sub>2) = (
    let v = fresh vs
    in let (t\<^sub>1, vs', con\<^sub>1) = collect_constraints \<Gamma> (insert v vs) e\<^sub>1 
    in let (t\<^sub>2, vs'', con\<^sub>2) = collect_constraints \<Gamma> vs' e\<^sub>2 
    in (Var v, vs'', con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1, Ctor ''Arrow'' [t\<^sub>2, Var v])]))"

primrec tree_code_size :: "tree_code \<Rightarrow> nat"
    and tree_code_size_list :: "tree_code list \<Rightarrow> nat" where
  "tree_code_size (TLookup x) = 0"
| "tree_code_size (TPushCon k) = 0"
| "tree_code_size (TPushLam cd) = tree_code_size_list cd"
| "tree_code_size TApply = 0"
| "tree_code_size_list [] = 1"
| "tree_code_size_list (op # cd) = 
      Suc (if op = TApply \<and> cd = [] then 0 else tree_code_size op + tree_code_size_list cd)"

primrec alg_compile1 :: "var list \<Rightarrow> nexpr \<Rightarrow> tree_code list \<Rightarrow> tree_code list" where
  "alg_compile1 \<Phi> (NVar x) acc = TLookup (the (idx_of \<Phi> x)) # acc"
| "alg_compile1 \<Phi> (NConst k) acc = TPushCon k # acc"
| "alg_compile1 \<Phi> (NLam x e) acc = TPushLam (alg_compile1 (insert_at 0 x \<Phi>) e []) # acc"
| "alg_compile1 \<Phi> (NApp e\<^sub>1 e\<^sub>2) acc = alg_compile1 \<Phi> e\<^sub>1 (alg_compile1 \<Phi> e\<^sub>2 (TApply # acc))"

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

fun assembly_mapb :: "byte_code list \<Rightarrow> nat \<Rightarrow> nat" where
  "assembly_mapb [] x = 0"
| "assembly_mapb (op # cd) 0 = 0"
| "assembly_mapb (BLookup k # cd) (Suc x) = 8 + 2 * k + assembly_mapb cd x"
| "assembly_mapb (BPushCon k # cd) (Suc x) = 8 + assembly_mapb cd x"
| "assembly_mapb (BPushLam pc # cd) (Suc x) = 12 + assembly_mapb cd x"
| "assembly_mapb (BApply # cd) (Suc x) = 24 + assembly_mapb cd x"
| "assembly_mapb (BReturn # cd) (Suc x) = 6 + assembly_mapb cd x"
| "assembly_mapb (BJump # cd) (Suc x) = 21 + assembly_mapb cd x"

fun alg_assemble :: "(nat \<Rightarrow> nat) \<Rightarrow> byte_code list \<Rightarrow> mach list" where
  "alg_assemble mp [] = []"
| "alg_assemble mp (BLookup x # cd) = 
    [LDI R5 0, ADD R3 4, STO R3 R5, LOD R5 R5, SUB R5 8] @ 
      concat (replicate x [LOD R5 R5, SUB R5 4]) @ 
      [LOD R5 R5, SUB R5 4, MOV R5 R4] @ 
      alg_assemble mp cd"
| "alg_assemble mp (BPushCon k # cd) = 
    [ADD R1 4, STO R1 R5, ADD R1 4, STI R1 k, ADD R1 4, STI R1 1, ADD R3 4, STO R3 R1] @ 
      alg_assemble mp cd"
| "alg_assemble mp (BPushLam pc # cd) = 
    [ADD R1 4, STI R1 (mp pc), LDI R5 0, ADD R1 4, 
      STO R1 R5, ADD R1 4, STI R1 0, LOD R5 R5, SUB R5 4, MOV R5 R4, ADD R3 4, STO R3 R1] @ 
      alg_assemble mp cd"
| "alg_assemble mp (BApply # cd) = 
    [JMP R5, LOD R5 R5, ADD R5 8, STI R3 0, LOD R5 R3, ADD R2 4, STO R2 R5, LOD R5 R5, ADD R5 4, 
      LOD R5 R3, SUB R3 4, ADD R4 4, STO R4 R5, ADD R5 4, MOV R5 R2, ADD R4 4, STO R4 R5, SUB R5 18, 
      MVP R5, ADD R2 4, STO R2 R5, STI R3 0, LOD R5 R3, SUB R3 4] @ 
      alg_assemble mp cd"
| "alg_assemble mp (BReturn # cd) = 
    [JMP R5, STI R4 0, LOD R5 R4, SUB R4 4, STI R4 0, SUB R4 4] @ 
      alg_assemble mp cd"
| "alg_assemble mp (BJump # cd) = 
    [JMP R5, LOD R5 R5, ADD R5 8, STI R3 0, LOD R5 R3, ADD R2 4, STO R2 R5, LOD R5 R5, ADD R5 4, 
      LOD R5 R3, SUB R3 4, ADD R4 4, STO R4 R5, SUB R4 4, ADD R5 4, MOV R5 R2, ADD R2 4, STO R2 R5, 
      STI R3 0, LOD R5 R3, SUB R3 4] @ 
      alg_assemble mp cd"

definition alg_compile3 :: "byte_code list \<Rightarrow> mach list" where
  "alg_compile3 cd = alg_assemble (assembly_mapb cd) cd"

definition alg_compile :: "nexpr \<rightharpoonup> mach list" where
  "alg_compile e = (
    let (t, vs, con) = collect_constraints Map.empty {} e
    in if unify' con \<noteq> None 
       then Some (alg_compile3 (alg_compile2 0 (alg_compile1 [] e []) [])) 
       else None)"

lemma [simp]: "encode (convert' \<Phi> (tsubstt sub e)) = encode (convert' \<Phi> e)"
  by (induction e arbitrary: \<Phi>) simp_all

lemma [simp]: "encode \<circ> convert \<circ> tsubstt sub = encode \<circ> convert"
  by (auto simp add: convert_def)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> quick_convert vs e = (e', vs')"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (simp_all add: Let_def split: option.splits prod.splits)

lemma [simp]: "quick_convert vs e = (e', vs') \<Longrightarrow> 
    alg_compile1 \<Phi> e acc = encode (convert' \<Phi> (solidify e')) @ acc"
  by (induction e arbitrary: \<Phi> acc vs e' vs') (auto simp add: Let_def split: prod.splits)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> 
  alg_compile1 \<Phi> e acc = encode (convert' \<Phi> (solidify e')) @ acc"
proof -
  assume "typecheck' \<Gamma> vs e = (e', t, vs', con)"
  hence "quick_convert vs e = (e', vs')" by simp
  thus ?thesis by simp
qed

lemma [simp]: "tree_code_size_list cd = code_list_size (tco_cd cd)"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

lemma [simp]: "alg_compile2 lib cd acc = flatten_code' lib (tco_cd cd) (tco_r cd) @ acc"
  by (induction lib cd acc rule: alg_compile2.induct) simp_all

lemma [simp]: "alg_assemble mp cd = disassemble (concat (map (assemble_op mp) cd))"
  by (induction mp cd rule: alg_assemble.induct) (simp_all add: disassemble_def)

lemma [simp]: "assembly_mapb cd x = assembly_map cd x"
  by (induction cd x rule: assembly_mapb.induct) simp_all

lemma [simp]: "assembly_mapb cd = assembly_map cd"
  by rule simp

lemma [simp]: "alg_compile3 cd = disassemble (assemble_code cd)"
  by (simp_all add: alg_compile3_def assemble_code_def)

lemma [simp]: "collect_constraints \<Gamma> vs e = snd (typecheck' \<Gamma> vs e)"
  by (induction e arbitrary: \<Gamma> vs) (simp_all add: Let_def split: option.splits prod.splits)

lemma [simp]: "alg_compile = compile"
  by (auto simp add: alg_compile_def Let_def tco_def convert_def split: prod.splits option.splits)

end