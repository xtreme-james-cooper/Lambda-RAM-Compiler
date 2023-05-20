theory Compiler
  imports Printing "04Stack/StackConversion" "11UnstructuredMemory/Unstructuring" 
begin

abbreviation code_compile :: "ty expr\<^sub>s \<Rightarrow> mach list" where
  "code_compile \<equiv> disassemble \<circ> assemble_code \<circ> flatten_code \<circ> tco_code \<circ> encode \<circ> unname"

abbreviation compile :: "unit expr\<^sub>s \<rightharpoonup> mach list \<times> ty" where 
  "compile \<equiv> map_option (apfst code_compile) \<circ> typecheck"

primrec quick_convert :: "var set \<Rightarrow> unit expr\<^sub>s \<Rightarrow> uterm expr\<^sub>s \<times> var set" where
  "quick_convert vs (Var\<^sub>s x) = (Var\<^sub>s x, {})"
| "quick_convert vs (Const\<^sub>s k) = (Const\<^sub>s k, {})"
| "quick_convert vs (Lam\<^sub>s x t e) = (
    let v = fresh vs
    in let (e', vs') = quick_convert (insert v vs) e
    in (Lam\<^sub>s x (Var v) e', insert v vs'))"
| "quick_convert vs (App\<^sub>s e\<^sub>1 e\<^sub>2) = (
    let v = fresh vs
    in let (e\<^sub>1', vs') = quick_convert (insert v vs) e\<^sub>1 
    in let (e\<^sub>2', vs'') = quick_convert (insert v (vs \<union> vs')) e\<^sub>2 
    in (App\<^sub>s e\<^sub>1' e\<^sub>2', insert v (vs' \<union> vs'')))"

primrec collect_constraints :: "subst \<Rightarrow> var set \<Rightarrow> unit expr\<^sub>s \<Rightarrow> uterm \<times> var set \<times> constraint" where
  "collect_constraints \<Gamma> vs (Var\<^sub>s x) = (case \<Gamma> x of 
      Some t \<Rightarrow> (t, {}, []) 
    | None \<Rightarrow> (Num\<^sub>\<tau>, {}, fail))"
| "collect_constraints \<Gamma> vs (Const\<^sub>s k) = (Num\<^sub>\<tau>, {}, [])"
| "collect_constraints \<Gamma> vs (Lam\<^sub>s x u e) = (
    let v = fresh vs
    in let (t, vs', con) = collect_constraints (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e
    in (Arrow\<^sub>\<tau> (Var v) t, insert v vs', con))"
| "collect_constraints \<Gamma> vs (App\<^sub>s e\<^sub>1 e\<^sub>2) = (
    let v = fresh vs
    in let (t\<^sub>1, vs', con\<^sub>1) = collect_constraints \<Gamma> (insert v vs) e\<^sub>1 
    in let (t\<^sub>2, vs'', con\<^sub>2) = collect_constraints \<Gamma> (insert v (vs \<union> vs')) e\<^sub>2 
    in (Var v, insert v (vs' \<union> vs''), con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1, Arrow\<^sub>\<tau> t\<^sub>2 (Var v))]))"

fun tree_code_size :: "code\<^sub>e \<Rightarrow> nat"
and tree_code_size_list :: "code\<^sub>e list \<Rightarrow> nat" where
  "tree_code_size (Lookup\<^sub>e x) = 0"
| "tree_code_size (PushCon\<^sub>e k) = 0"
| "tree_code_size (PushLam\<^sub>e cd) = tree_code_size_list cd"
| "tree_code_size Apply\<^sub>e = 0"
| "tree_code_size Return\<^sub>e = 0"
| "tree_code_size Jump\<^sub>e = 0"
| "tree_code_size_list [] = 0"
| "tree_code_size_list (Apply\<^sub>e # Return\<^sub>e # cd) = Suc (tree_code_size_list cd)"
| "tree_code_size_list (op # cd) = Suc (tree_code_size op + tree_code_size_list cd)"

lemma [simp]: "op \<noteq> Return\<^sub>e \<Longrightarrow> tree_code_size_list (op # cd) < tree_code_size_list (Apply\<^sub>e # op # cd)"
  by (cases op) simp_all

primrec alg_compile1 :: "var list \<Rightarrow> unit expr\<^sub>s \<Rightarrow> code\<^sub>e list \<Rightarrow> code\<^sub>e list" where
  "alg_compile1 \<Phi> (Var\<^sub>s x) acc = Lookup\<^sub>e (the (idx_of \<Phi> x)) # acc"
| "alg_compile1 \<Phi> (Const\<^sub>s k) acc = PushCon\<^sub>e k # acc"
| "alg_compile1 \<Phi> (Lam\<^sub>s x u e) acc = PushLam\<^sub>e (alg_compile1 (insert_at 0 x \<Phi>) e [Return\<^sub>e]) # acc"
| "alg_compile1 \<Phi> (App\<^sub>s e\<^sub>1 e\<^sub>2) acc = alg_compile1 \<Phi> e\<^sub>1 (alg_compile1 \<Phi> e\<^sub>2 (Apply\<^sub>e # acc))"

function alg_compile2 :: "nat \<Rightarrow> code\<^sub>e list \<Rightarrow> code\<^sub>b list \<Rightarrow> code\<^sub>b list" where
  "alg_compile2 lib [] acc = acc"
| "alg_compile2 lib (Lookup\<^sub>e x # cd) acc = alg_compile2 lib cd (Lookup\<^sub>b x # acc)"
| "alg_compile2 lib (PushCon\<^sub>e k # cd) acc = alg_compile2 lib cd (PushCon\<^sub>b k # acc)"
| "alg_compile2 lib (PushLam\<^sub>e cd' # cd) acc =
    alg_compile2 lib cd' 
      (alg_compile2 (lib + tree_code_size_list cd') cd 
        (PushLam\<^sub>b (lib + tree_code_size_list cd') # acc))"
| "alg_compile2 lib (Apply\<^sub>e # []) acc = Apply\<^sub>b # acc"
| "alg_compile2 lib (Apply\<^sub>e # op # cd) acc = (
    if op = Return\<^sub>e 
    then alg_compile2 lib cd (Jump\<^sub>b # acc)
    else alg_compile2 lib (op # cd) (Apply\<^sub>b # acc))"
| "alg_compile2 lib (Return\<^sub>e # cd) acc = alg_compile2 lib cd (Return\<^sub>b # acc)"
| "alg_compile2 lib (Jump\<^sub>e # cd) acc = alg_compile2 lib cd (Jump\<^sub>b # acc)"
  by pat_completeness auto
termination
  by (relation "measure (tree_code_size_list \<circ> fst \<circ> snd)") simp_all

fun assembly_mapb :: "code\<^sub>b list \<Rightarrow> nat \<Rightarrow> nat" where
  "assembly_mapb [] x = 0"
| "assembly_mapb (op # cd) 0 = 0"
| "assembly_mapb (Lookup\<^sub>b k # cd) (Suc x) = 8 + 2 * k + assembly_mapb cd x"
| "assembly_mapb (PushCon\<^sub>b k # cd) (Suc x) = 8 + assembly_mapb cd x"
| "assembly_mapb (PushLam\<^sub>b pc # cd) (Suc x) = 12 + assembly_mapb cd x"
| "assembly_mapb (Apply\<^sub>b # cd) (Suc x) = 24 + assembly_mapb cd x"
| "assembly_mapb (Return\<^sub>b # cd) (Suc x) = 6 + assembly_mapb cd x"
| "assembly_mapb (Jump\<^sub>b # cd) (Suc x) = 21 + assembly_mapb cd x"

fun alg_assemble :: "(nat \<Rightarrow> nat) \<Rightarrow> code\<^sub>b list \<Rightarrow> mach list" where
  "alg_assemble mp [] = []"
| "alg_assemble mp (Lookup\<^sub>b x # cd) = 
    [LDI R5 0, ADD R3 4, STO R3 R5, LOD R5 R5, SUB R5 8] @ 
      concat (replicate x [LOD R5 R5, SUB R5 4]) @ 
      [LOD R5 R5, SUB R5 4, MOV R5 R4] @ 
      alg_assemble mp cd"
| "alg_assemble mp (PushCon\<^sub>b k # cd) = 
    [ADD R1 4, STO R1 R5, ADD R1 4, STI R1 k, ADD R1 4, STI R1 1, ADD R3 4, STO R3 R1] @ 
      alg_assemble mp cd"
| "alg_assemble mp (PushLam\<^sub>b pc # cd) = 
    [ADD R1 4, STI R1 (mp pc), LDI R5 0, ADD R1 4, 
      STO R1 R5, ADD R1 4, STI R1 0, LOD R5 R5, SUB R5 4, MOV R5 R4, ADD R3 4, STO R3 R1] @ 
      alg_assemble mp cd"
| "alg_assemble mp (Apply\<^sub>b # cd) = 
    [JMP R5, LOD R5 R5, ADD R5 8, STI R3 0, LOD R5 R3, ADD R2 4, STO R2 R5, LOD R5 R5, ADD R5 4, 
      LOD R5 R3, SUB R3 4, ADD R4 4, STO R4 R5, ADD R5 4, MOV R5 R2, ADD R4 4, STO R4 R5, SUB R5 18, 
      MVP R5, ADD R2 4, STO R2 R5, STI R3 0, LOD R5 R3, SUB R3 4] @ 
      alg_assemble mp cd"
| "alg_assemble mp (Return\<^sub>b # cd) = 
    [JMP R5, STI R4 0, LOD R5 R4, SUB R4 4, STI R4 0, SUB R4 4] @ 
      alg_assemble mp cd"
| "alg_assemble mp (Jump\<^sub>b # cd) = 
    [JMP R5, LOD R5 R5, ADD R5 8, STI R3 0, LOD R5 R3, ADD R2 4, STO R2 R5, LOD R5 R5, ADD R5 4, 
      LOD R5 R3, SUB R3 4, ADD R4 4, STO R4 R5, SUB R4 4, ADD R5 4, MOV R5 R2, ADD R2 4, STO R2 R5, 
      STI R3 0, LOD R5 R3, SUB R3 4] @ 
      alg_assemble mp cd"

definition alg_compile3 :: "code\<^sub>b list \<Rightarrow> mach list" where
  "alg_compile3 cd = alg_assemble (assembly_mapb cd) cd"

definition alg_compile :: "unit expr\<^sub>s \<rightharpoonup> mach list \<times> ty" where
  "alg_compile e = (
    let (t, vs, con) = collect_constraints Map.empty {} e
    in case unify con of
        None \<Rightarrow> None
      | Some s \<Rightarrow> Some (alg_compile3 (alg_compile2 0 (alg_compile1 [] e [] @ [Return\<^sub>e]) []), 
                        to_type (subst s t)))"

lemma [simp]: "encode' (unname' \<Phi> (map_expr\<^sub>s to_type (map_expr\<^sub>s (subst sub) e))) = 
    encode' (unname' \<Phi> (map_expr\<^sub>s to_type e))"
  by (induction e arbitrary: \<Phi>) simp_all

lemma [simp]: "encode' \<circ> unname \<circ> map_expr\<^sub>s to_type \<circ> map_expr\<^sub>s (subst sub) = 
    encode' \<circ> unname \<circ> map_expr\<^sub>s to_type"
  by (auto simp add: unname_def)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> quick_convert vs e = (e', vs')"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (simp_all add: Let_def split: option.splits prod.splits)

lemma [simp]: "quick_convert vs e = (e', vs') \<Longrightarrow> 
    alg_compile1 \<Phi> e acc = encode' (unname' \<Phi> (map_expr\<^sub>s to_type e')) @ acc"
  by (induction e arbitrary: \<Phi> acc vs e' vs') (auto simp add: Let_def split: prod.splits)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> 
  alg_compile1 \<Phi> e acc = encode' (unname' \<Phi> (map_expr\<^sub>s to_type e')) @ acc"
proof -
  assume "typecheck' \<Gamma> vs e = (e', t, vs', con)"
  hence "quick_convert vs e = (e', vs')" by simp
  thus ?thesis by simp
qed

lemma [simp]: "tree_code_size_list cd = code_list_size (tco_code cd)"
  by (induction cd rule: tco_code.induct) (simp_all split: list.splits)

lemma [simp]: "alg_compile2 lib cd acc = flatten_code' lib (tco_code cd) @ acc"
proof (induction lib cd acc rule: alg_compile2.induct)
  case (6 lib op cd acc)
  thus ?case by (induction op) simp_all
qed simp_all

lemma alg_assemble_simp [simp]: "alg_assemble mp cd = 
    disassemble (concat (map (assemble_op mp) cd))"
  by (induction mp cd rule: alg_assemble.induct) (simp_all add: disassemble_def)

lemma [simp]: "assembly_mapb cd x = assembly_map cd x"
  by (induction cd x rule: assembly_mapb.induct) simp_all

lemma [simp]: "assembly_mapb cd = assembly_map cd"
  by rule simp

lemma alg_compile3_simp [simp]: "alg_compile3 cd = disassemble (assemble_code cd)"
  by (simp_all add: alg_compile3_def assemble_code_def)

lemma [simp]: "collect_constraints \<Gamma> vs e = snd (typecheck' \<Gamma> vs e)"
  by (induction e arbitrary: \<Gamma> vs) (simp_all add: Let_def split: option.splits prod.splits)

lemma alg_compile_simp [simp]: "alg_compile = compile"
  by rule (simp add: alg_compile_def encode_def flatten_code_def unname_def split: prod.splits option.splits)

end