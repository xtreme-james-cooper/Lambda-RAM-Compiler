theory Compiler
  imports Printing "04Stack/StackConversion" "11UnstructuredMemory/Unstructuring" 
begin

primrec tco :: "code\<^sub>e list \<times> return\<^sub>e \<Rightarrow> code\<^sub>e list \<times> return\<^sub>e" where
  "tco (\<C>, r) = (tco_code \<C>, tco_return \<C> r)"

abbreviation code_compile :: "ty expr\<^sub>s \<Rightarrow> mach list" where
  "code_compile \<equiv> disassemble \<circ> assemble_code \<circ> flatten_code \<circ> tco \<circ> encode \<circ> unname"

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

primrec tree_code_size :: "code\<^sub>e \<Rightarrow> nat"
    and tree_code_size_list :: "code\<^sub>e list \<Rightarrow> nat" where
  "tree_code_size (Lookup\<^sub>e x) = 0"
| "tree_code_size (PushCon\<^sub>e k) = 0"
| "tree_code_size (PushLam\<^sub>e cd) = tree_code_size_list cd"
| "tree_code_size Apply\<^sub>e = 0"
| "tree_code_size_list [] = 1"
| "tree_code_size_list (op # cd) = 
      Suc (if op = Apply\<^sub>e \<and> cd = [] then 0 else tree_code_size op + tree_code_size_list cd)"

primrec alg_compile1 :: "var list \<Rightarrow> unit expr\<^sub>s \<Rightarrow> code\<^sub>e list \<Rightarrow> code\<^sub>e list" where
  "alg_compile1 \<Phi> (Var\<^sub>s x) acc = Lookup\<^sub>e (the (idx_of \<Phi> x)) # acc"
| "alg_compile1 \<Phi> (Const\<^sub>s k) acc = PushCon\<^sub>e k # acc"
| "alg_compile1 \<Phi> (Lam\<^sub>s x u e) acc = PushLam\<^sub>e (alg_compile1 (insert_at 0 x \<Phi>) e []) # acc"
| "alg_compile1 \<Phi> (App\<^sub>s e\<^sub>1 e\<^sub>2) acc = alg_compile1 \<Phi> e\<^sub>1 (alg_compile1 \<Phi> e\<^sub>2 (Apply\<^sub>e # acc))"

function alg_compile2 :: "nat \<Rightarrow> code\<^sub>e list \<Rightarrow> byte_code list \<Rightarrow> byte_code list" where
  "alg_compile2 lib [] acc = BReturn # acc"
| "alg_compile2 lib (Lookup\<^sub>e x # cd) acc = alg_compile2 lib cd (BLookup x # acc)"
| "alg_compile2 lib (PushCon\<^sub>e k # cd) acc = alg_compile2 lib cd (BPushCon k # acc)"
| "alg_compile2 lib (PushLam\<^sub>e cd' # cd) acc =
    alg_compile2 lib cd' 
      (alg_compile2 (lib + tree_code_size_list cd') cd 
        (BPushLam (lib + tree_code_size_list cd') # acc))"
| "alg_compile2 lib (Apply\<^sub>e # []) acc = BJump # acc"
| "alg_compile2 lib (Apply\<^sub>e # op # cd) acc = alg_compile2 lib (op # cd) (BApply # acc)"
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

definition alg_compile :: "unit expr\<^sub>s \<rightharpoonup> mach list \<times> ty" where
  "alg_compile e = (
    let (t, vs, con) = collect_constraints Map.empty {} e
    in case unify con of
        None \<Rightarrow> None
      | Some s \<Rightarrow> 
          Some (alg_compile3 (alg_compile2 0 (alg_compile1 [] e []) []), to_type (subst s t)))"

lemma [simp]: "encode (unname' \<Phi> (map_expr\<^sub>s to_type (map_expr\<^sub>s (subst sub) e))) = 
    encode (unname' \<Phi> (map_expr\<^sub>s to_type e))"
  by (induction e arbitrary: \<Phi>) simp_all

lemma [simp]: "encode \<circ> unname \<circ> map_expr\<^sub>s to_type \<circ> map_expr\<^sub>s (subst sub) = 
    encode \<circ> unname \<circ> map_expr\<^sub>s to_type"
  by (auto simp add: unname_def)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> quick_convert vs e = (e', vs')"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (simp_all add: Let_def split: option.splits prod.splits)

lemma [simp]: "quick_convert vs e = (e', vs') \<Longrightarrow> 
    alg_compile1 \<Phi> e acc = encode (unname' \<Phi> (map_expr\<^sub>s to_type e')) @ acc"
  by (induction e arbitrary: \<Phi> acc vs e' vs') (auto simp add: Let_def split: prod.splits)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> 
  alg_compile1 \<Phi> e acc = encode (unname' \<Phi> (map_expr\<^sub>s to_type e')) @ acc"
proof -
  assume "typecheck' \<Gamma> vs e = (e', t, vs', con)"
  hence "quick_convert vs e = (e', vs')" by simp
  thus ?thesis by simp
qed

lemma [simp]: "tree_code_size_list cd = code_list_size (tco_cd cd)"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

lemma [simp]: "alg_compile2 lib cd acc = flatten_code' lib (tco_cd cd) (tco_r cd) @ acc"
  by (induction lib cd acc rule: alg_compile2.induct) simp_all

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
  by rule (simp add: alg_compile_def tco_def unname_def split: prod.splits option.splits)

end