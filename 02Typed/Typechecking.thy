theory Typechecking
  imports Typed "../01Source/Named" "../00Utils/Unification/Unification"
begin

datatype hexpr = 
  HVar var
  | HConst nat
  | HLam var uexpr hexpr
  | HApp hexpr hexpr

primrec hsubst :: "subst \<Rightarrow> hexpr \<Rightarrow> hexpr" where
  "hsubst sub (HVar x) = HVar x"
| "hsubst sub (HConst k) = HConst k"
| "hsubst sub (HLam x t e) = HLam x (subst sub t) (hsubst sub e)"
| "hsubst sub (HApp e\<^sub>1 e\<^sub>2) = HApp (hsubst sub e\<^sub>1) (hsubst sub e\<^sub>2)"

primrec erase :: "texpr \<Rightarrow> nexpr" where
  "erase (TVar x) = NVar x"
| "erase (TConst k) = NConst k"
| "erase (TLam x t e) = NLam x (erase e)"
| "erase (TApp e\<^sub>1 e\<^sub>2) = NApp (erase e\<^sub>1) (erase e\<^sub>2)"

definition env_subst :: "subst \<Rightarrow> subst \<Rightarrow> subst" where
  "env_subst sub \<Gamma> = map_option (subst sub) \<circ> \<Gamma>"

primrec typecheck' :: "subst \<Rightarrow> var set \<Rightarrow> nexpr \<Rightarrow> hexpr \<times> uexpr \<times> var set \<times> (uexpr \<times> uexpr) list" 
    where
  "typecheck' \<Gamma> vs (NVar x) = (case \<Gamma> x of 
      Some t \<Rightarrow> (HVar x, t, vs, []) 
    | None \<Rightarrow> (HVar x, Ctor ''Base'' [], vs, fail))"
| "typecheck' \<Gamma> vs (NConst k) = (HConst k, Ctor ''Base'' [], vs, [])"
| "typecheck' \<Gamma> vs (NLam x e) = (
    let v = fresh vs
    in let (e', t, vs', con) = typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e
    in (HLam x (Var v) e', Ctor ''Arrow'' [Var v, t], vs', con))"
| "typecheck' \<Gamma> vs (NApp e\<^sub>1 e\<^sub>2) = (
    let v = fresh vs
    in let (e\<^sub>1', t\<^sub>1, vs', con\<^sub>1) = typecheck' \<Gamma> (insert v vs) e\<^sub>1 
    in let (e\<^sub>2', t\<^sub>2, vs'', con\<^sub>2) = typecheck' \<Gamma> vs' e\<^sub>2 
    in (HApp e\<^sub>1' e\<^sub>2', Var v, vs'', (t\<^sub>1, Ctor ''Arrow'' [t\<^sub>2, Var v]) # con\<^sub>1 @ con\<^sub>2))"

fun typeify :: "uexpr \<Rightarrow> ty" where
  "typeify (Var v) = TyVar v"
| "typeify (Ctor k []) = (if k = ''Base'' then Base else undefined)"
| "typeify (Ctor k [t\<^sub>1, t\<^sub>2]) = 
    (if k = ''Arrow'' then Arrow (typeify t\<^sub>1) (typeify t\<^sub>2) else undefined)"
| "typeify (Ctor k ts) = undefined"

primrec untypify :: "ty \<Rightarrow> uexpr" where
  "untypify (TyVar v) = Var v"
| "untypify Base = Ctor ''Base'' []"
| "untypify (Arrow t\<^sub>1 t\<^sub>2) = Ctor ''Arrow'' [untypify t\<^sub>1, untypify t\<^sub>2]"

primrec solidify :: "hexpr \<Rightarrow> texpr" where
  "solidify (HVar x) = TVar x"
| "solidify (HConst k) = TConst k"
| "solidify (HLam x t e) = TLam x (typeify t) (solidify e)"
| "solidify (HApp e\<^sub>1 e\<^sub>2) = TApp (solidify e\<^sub>1) (solidify e\<^sub>2)"

fun tsubsts :: "subst \<Rightarrow> ty \<Rightarrow> ty" where
  "tsubsts sub (TyVar y) = (case sub y of Some t \<Rightarrow> typeify t | None \<Rightarrow> TyVar y)"
| "tsubsts sub Base = Base"
| "tsubsts sub (Arrow t\<^sub>1 t\<^sub>2) = Arrow (tsubsts sub t\<^sub>1) (tsubsts sub t\<^sub>2)"

primrec tsubstt :: "subst \<Rightarrow> texpr \<Rightarrow> texpr" where
  "tsubstt sub (TVar x) = TVar x"
| "tsubstt sub (TConst k) = TConst k"
| "tsubstt sub (TLam x t e) = TLam x (tsubsts sub t) (tsubstt sub e)"
| "tsubstt sub (TApp e\<^sub>1 e\<^sub>2) = TApp (tsubstt sub e\<^sub>1) (tsubstt sub e\<^sub>2)"

fun typecheck :: "nexpr \<rightharpoonup> texpr \<times> ty" where
  "typecheck e = (
    let (e', t, vs, con) = typecheck' Map.empty {} e
    in case unify' con of 
        Some sub \<Rightarrow> Some (tsubstt sub (solidify e'), tsubsts sub (typeify t))
      | None \<Rightarrow> None)"

fun valid_ty_uexpr' :: "string \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_ty_uexpr' k 0 = (k = ''Base'')"
| "valid_ty_uexpr' k (Suc 0) = False"
| "valid_ty_uexpr' k (Suc (Suc 0)) = (k = ''Arrow'')"
| "valid_ty_uexpr' k (Suc (Suc (Suc x))) = False"

primrec valid_ty_uexpr :: "uexpr \<Rightarrow> bool" where
  "valid_ty_uexpr (Var v) = True"
| "valid_ty_uexpr (Ctor k ts) = (valid_ty_uexpr' k (length ts) \<and> list_all valid_ty_uexpr ts)"

definition valid_ty_uexprs :: "(uexpr \<times> uexpr) list \<Rightarrow> bool" where
  "valid_ty_uexprs ts = list_all (\<lambda>(t\<^sub>1, t\<^sub>2). valid_ty_uexpr t\<^sub>1 \<and> valid_ty_uexpr t\<^sub>2) ts"
 
definition valid_ty_subst :: "subst \<Rightarrow> bool" where
  "valid_ty_subst \<Gamma> = (\<forall>t \<in> ran \<Gamma>. valid_ty_uexpr t)"

primrec valid_ty_hexpr :: "hexpr \<Rightarrow> bool" where
  "valid_ty_hexpr (HVar x) = True"
| "valid_ty_hexpr (HConst k) = True"
| "valid_ty_hexpr (HLam x t e) = (valid_ty_uexpr t \<and> valid_ty_hexpr e)"
| "valid_ty_hexpr (HApp e\<^sub>1 e\<^sub>2) = (valid_ty_hexpr e\<^sub>1 \<and> valid_ty_hexpr e\<^sub>2)"

lemma typecheck_induct [consumes 1, case_names NVarS NVarN NConst NLam NApp]: "
  typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> 
  (\<And>\<Gamma> vs t x. \<Gamma> x = Some t \<Longrightarrow> P \<Gamma> vs (NVar x) (HVar x) t vs []) \<Longrightarrow> 
  (\<And>\<Gamma> vs x. \<Gamma> x = None \<Longrightarrow> P \<Gamma> vs (NVar x) (HVar x) (Ctor ''Base'' [])  vs fail) \<Longrightarrow> 
  (\<And>\<Gamma> vs k. P \<Gamma> vs (NConst k) (HConst k) (Ctor ''Base'' []) vs []) \<Longrightarrow> 
  (\<And>\<Gamma> vs vs' con x e\<^sub>1 e\<^sub>1' t' v. v = fresh vs \<Longrightarrow> typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>1 = 
    (e\<^sub>1', t', vs', con) \<Longrightarrow> P (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>1 e\<^sub>1' t' vs' con \<Longrightarrow> 
      P \<Gamma> vs (NLam x e\<^sub>1) (HLam x (Var v) e\<^sub>1') (Ctor ''Arrow'' [Var v, t']) vs' con) \<Longrightarrow> 
  (\<And>\<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2. v = fresh vs \<Longrightarrow> 
    typecheck' \<Gamma> (insert v vs) e\<^sub>1 = (e\<^sub>1', t\<^sub>1, vs'', con\<^sub>1) \<Longrightarrow> 
      typecheck' \<Gamma> vs'' e\<^sub>2 = (e\<^sub>2', t\<^sub>2, vs', con\<^sub>2) \<Longrightarrow> P \<Gamma> (insert v vs) e\<^sub>1 e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 \<Longrightarrow> 
        P \<Gamma> vs'' e\<^sub>2 e\<^sub>2' t\<^sub>2 vs' con\<^sub>2 \<Longrightarrow> P \<Gamma> vs (NApp e\<^sub>1 e\<^sub>2) (HApp e\<^sub>1' e\<^sub>2') (Var v) vs' 
          ((t\<^sub>1, Ctor ''Arrow'' [t\<^sub>2, Var v]) # con\<^sub>1 @ con\<^sub>2)) \<Longrightarrow> 
    P \<Gamma> vs e e' t vs' con"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (auto simp add: Let_def split: option.splits prod.splits)

lemma [simp]: "typeify (untypify t) = t"
  by (induction t) simp_all

lemma [simp]: "vars (untypify t) = tvars t"
  by (induction t) simp_all

lemma [simp]: "valid_ty_uexpr t \<Longrightarrow> tvars (typeify t) = vars t"
  by (induction t rule: typeify.induct) simp_all

lemma [simp]: "tsubsts Map.empty e = e"
  by (induction e) simp_all

lemma [simp]: "valid_ty_uexpr t \<Longrightarrow> typeify (subst sub t) = tsubsts sub (typeify t)"
  by (induction t rule: typeify.induct) (simp_all split: option.splits)

lemma valid_empty [simp]: "valid_ty_subst Map.empty"
  by (simp add: valid_ty_subst_def)

lemma [simp]: "valid_ty_uexpr e \<Longrightarrow> typeify (subst sub e) = tsubsts sub (typeify e)"
  by (induction e rule: typeify.induct) (auto split: option.splits)

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> 
    map_option (typeify \<circ> subst sub) (\<Gamma> x) = map_option (tsubsts sub \<circ> typeify) (\<Gamma> x)"
  by (cases "\<Gamma> x") (auto simp add: valid_ty_subst_def ran_def)

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> 
    map_option (typeify \<circ> subst sub) \<circ> \<Gamma> = map_option (tsubsts sub \<circ> typeify) \<circ> \<Gamma>"
  by auto

lemma [simp]: "valid_ty_hexpr e \<Longrightarrow> solidify (hsubst sub e) = tsubstt sub (solidify e)"
  by (induction e) simp_all

lemma [simp]: "erase (solidify (hsubst sub e)) = erase (solidify e)"
  by (induction e) simp_all

lemma [simp]: "erase (tsubstt sub e) = erase e"
  by (induction e) simp_all

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_uexpr t \<Longrightarrow> valid_ty_subst (\<Gamma>(x \<mapsto> t))"
  by (auto simp add: valid_ty_subst_def ran_def)

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_subst \<Gamma>' \<Longrightarrow> valid_ty_subst (\<Gamma>(x := \<Gamma>' y))"
  by (auto simp add: valid_ty_subst_def ran_def)

lemma [simp]: "valid_ty_uexpr (subst s e) \<Longrightarrow> valid_ty_subst s \<Longrightarrow> 
    valid_ty_subst (extend_subst x e s)"
  by (auto simp add: valid_ty_subst_def extend_subst_def ran_def)

lemma [simp]: "valid_ty_uexpr e \<Longrightarrow> valid_ty_uexpr e' \<Longrightarrow> valid_ty_uexpr (subst [x \<mapsto> e'] e)"
  and [simp]: "list_all valid_ty_uexpr es \<Longrightarrow> valid_ty_uexpr e' \<Longrightarrow> 
    list_all valid_ty_uexpr (map (subst [x \<mapsto> e']) es)"
proof (induction e and es rule: vars_varss.induct)
  case (2 k es)
  thus ?case 
  proof (induction es)
    case (Cons a es)
    thus ?case 
    proof (induction es)
      case (Cons b es)
      thus ?case by (induction es) simp_all
    qed simp_all
  qed simp_all
qed simp_all

lemma [simp]: "valid_ty_uexpr e \<Longrightarrow> valid_ty_uexprs ess \<Longrightarrow> valid_ty_uexprs (list_subst x e ess)"
  by (induction ess rule: list_subst.induct) (auto simp add: valid_ty_uexprs_def)

lemma [simp]: "valid_ty_uexpr t \<Longrightarrow> valid_ty_subst sub \<Longrightarrow> valid_ty_uexpr (subst sub t)"
  and [simp]: "list_all valid_ty_uexpr ts \<Longrightarrow> valid_ty_subst sub \<Longrightarrow> 
    list_all valid_ty_uexpr (map (subst sub) ts)"
  by (induction t and ts rule: vars_varss.induct) 
     (auto simp add: valid_ty_subst_def ran_def split: option.splits)

lemma [elim]: "valid_ty_subst \<Gamma> \<Longrightarrow> \<Gamma> x = Some t \<Longrightarrow> valid_ty_uexpr t"
  by (auto simp add: valid_ty_subst_def ran_def)

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_subst sub\<^sub>2 \<Longrightarrow> 
  map_option (typeify \<circ> subst sub\<^sub>1 \<circ> subst sub\<^sub>2) (\<Gamma> x) = 
    map_option (tsubsts sub\<^sub>1 \<circ> tsubsts sub\<^sub>2 \<circ> typeify) (\<Gamma> x)"
proof (cases "\<Gamma> x")
  case (Some e)
  moreover assume "valid_ty_subst \<Gamma>"
  ultimately have E: "valid_ty_uexpr e" by auto
  assume "valid_ty_subst sub\<^sub>2"
  with Some E show ?thesis by simp
qed simp_all

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_subst sub\<^sub>2 \<Longrightarrow> 
  map_option (typeify \<circ> subst sub\<^sub>1 \<circ> subst sub\<^sub>2) \<circ> \<Gamma> = 
    map_option (tsubsts sub\<^sub>1 \<circ> tsubsts sub\<^sub>2 \<circ> typeify) \<circ> \<Gamma>"
  by auto

lemma [elim]: "valid_ty_uexprs ts \<Longrightarrow> unify' ts = Some sub \<Longrightarrow> valid_ty_subst sub"                                  
proof (induction ts arbitrary: sub rule: unify'.induct)
  case (2 k\<^sub>1 es\<^sub>1 k\<^sub>2 es\<^sub>2 ess)
  moreover hence "list_all valid_ty_uexpr es\<^sub>1" by (auto simp add: valid_ty_uexprs_def)
  moreover from 2 have "list_all valid_ty_uexpr es\<^sub>2" by (auto simp add: valid_ty_uexprs_def)
  ultimately show ?case by (simp add: valid_ty_uexprs_def split: if_splits)
next
  case (4 x e ess)
  thus ?case
  proof (cases "e = Var x")
    case False note F = False
    with 4 show ?thesis 
    proof (cases "x \<in> vars e")
      case False
      with 4 F obtain sub' where S: "unify' (list_subst x e ess) = Some sub' \<and> 
        sub = extend_subst x e sub'" by auto
      from 4 have "valid_ty_uexpr e \<and> valid_ty_uexprs ess" by (simp add: valid_ty_uexprs_def)
      hence "valid_ty_uexprs (list_subst x e ess)" by simp
      with 4 F False S show ?thesis by (simp add: valid_ty_uexprs_def)
    qed simp_all
  qed (simp_all add: valid_ty_uexprs_def)
qed (auto simp add: valid_ty_uexprs_def)

lemma [elim]: "valid_ty_uexpr t\<^sub>1 \<Longrightarrow> valid_ty_uexpr t\<^sub>2 \<Longrightarrow> unify t\<^sub>1 t\<^sub>2 = Some sub \<Longrightarrow> 
  valid_ty_subst sub"                                  
proof (unfold unify_def)
  assume "valid_ty_uexpr t\<^sub>1" and "valid_ty_uexpr t\<^sub>2" 
  hence "valid_ty_uexprs [(t\<^sub>1, t\<^sub>2)]" by (simp add: valid_ty_uexprs_def)
  moreover assume "unify' [(t\<^sub>1, t\<^sub>2)] = Some sub"
  ultimately show "valid_ty_subst sub" by auto
qed

lemma [simp]: "valid_ty_subst sub \<Longrightarrow> valid_ty_hexpr e \<Longrightarrow> valid_ty_hexpr (hsubst sub e)"
  by (induction e) simp_all

lemma tc_tsubstt [simp]: "\<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> 
  map_option (tsubsts sub) \<circ> \<Gamma> \<turnstile>\<^sub>n tsubstt sub e : tsubsts sub t"
proof (induction \<Gamma> e t rule: typecheckn.induct)
  case (tcn_lam \<Gamma> x t\<^sub>1 e t\<^sub>2)
  hence "map_option (tsubsts sub) \<circ> \<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n tsubstt sub e : tsubsts sub t\<^sub>2" by blast
  hence "map_option (tsubsts sub) \<circ> \<Gamma> \<turnstile>\<^sub>n tsubstt sub (TLam x t\<^sub>1 e) : tsubsts sub (Arrow t\<^sub>1 t\<^sub>2)" 
    by simp
  thus ?case by blast
qed simp_all

lemma valid_ty_uexpr_structrual [simp]: "structural valid_ty_uexpr"
  by (auto simp add: structural_def)

lemma [simp]: "valid_ty_subst sub \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_subst (env_subst sub \<Gamma>)"
  by (auto simp add: valid_ty_subst_def env_subst_def ran_def)

lemma [simp]: "valid_ty_subst s1 \<Longrightarrow> valid_ty_subst s2 \<Longrightarrow> valid_ty_subst (combine_subst s1 s2)"
proof (unfold valid_ty_subst_def combine_subst_def ran_def, rule)
  fix x
  assume S1: "\<forall>x \<in> {b. \<exists>a. s1 a = Some b}. valid_ty_uexpr x"
  assume S2: "\<forall>x \<in> {b. \<exists>a. s2 a = Some b}. valid_ty_uexpr x"
  assume "x \<in> {b. \<exists>a. (case s2 a of None \<Rightarrow> s1 a | Some e \<Rightarrow> Some (subst s1 e)) = Some b}"
  then obtain y where Y: "(case s2 y of None \<Rightarrow> s1 y | Some e \<Rightarrow> Some (subst s1 e)) = Some x" 
    by auto
  from S1 S2 Y show "valid_ty_uexpr x" 
  proof (cases "s2 y")
    case (Some e)
    from S1 have "valid_ty_subst s1" by (auto simp add: valid_ty_subst_def ran_def)
    with S2 Y Some show ?thesis by auto
  qed auto
qed

lemma [simp]: "hsubst (combine_subst s t) e = hsubst s (hsubst t e)"
  by (induction e) simp_all

lemma [elim]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_uexpr t"
  by (induction rule: typecheck_induct) auto

lemma [elim]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_hexpr e'"
  by (induction rule: typecheck_induct) auto

lemma typecheck_succeeds [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> 
  valid_ty_subst \<Gamma> \<Longrightarrow> unify' con = Some sub' \<Longrightarrow> sub extends sub' \<Longrightarrow>
    map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub e') : typeify (subst sub t)"
proof (induction arbitrary: sub' rule: typecheck_induct)
  case (NVarS \<Gamma> vs t x)
  thus ?case by simp
next
  case (NLam \<Gamma> vs vs' con x e\<^sub>1 e\<^sub>1' t' v)
  hence "valid_ty_subst (\<Gamma>(x \<mapsto> Var v))" by simp
  with NLam have "map_option (typeify \<circ> subst sub) \<circ> \<Gamma>(x \<mapsto> Var v) \<turnstile>\<^sub>n solidify (hsubst sub e\<^sub>1') : 
      typeify (subst sub t')" by blast
  hence "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub (HLam x (Var v) e\<^sub>1')) :
    typeify (subst sub (Ctor ''Arrow'' [Var v, t']))" by simp
  thus ?case by blast
next
  case (NApp \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2)
  then obtain s\<^sub>2 where S2: "unify' (con\<^sub>1 @ con\<^sub>2) = Some s\<^sub>2 \<and> sub' extends s\<^sub>2" by fastforce
  then obtain s\<^sub>3 where S3: "unify' con\<^sub>1 = Some s\<^sub>3 \<and> s\<^sub>2 extends s\<^sub>3" by fastforce
  with NApp S2 have "sub extends s\<^sub>3" by auto
  with NApp S2 S3 have T: "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub e\<^sub>1') : 
    typeify (subst sub t\<^sub>1)" by blast
  from NApp have "sub' unifies\<^sub>l ((t\<^sub>1, Ctor ''Arrow'' [t\<^sub>2, Var v]) # con\<^sub>1 @ con\<^sub>2)" 
    by (metis unify_some) 
  hence "sub' unifies t\<^sub>1 and Ctor ''Arrow'' [t\<^sub>2, Var v]" by simp
  with NApp have X: "sub unifies t\<^sub>1 and Ctor ''Arrow'' [t\<^sub>2, Var v]" by fastforce
  from S2 obtain s\<^sub>4 where S4: "unify' con\<^sub>2 = Some s\<^sub>4 \<and> s\<^sub>2 extends s\<^sub>4" 
    using unify_append_snd by blast
  with NApp S2 have "sub extends s\<^sub>4" by auto
  with NApp S4 have "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub e\<^sub>2') : 
    typeify (subst sub t\<^sub>2)" by blast
  with T X have "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub (HApp e\<^sub>1' e\<^sub>2')) : 
    typeify (subst sub (Var v))" by simp
  thus ?case by blast
qed simp_all

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> Map.empty \<turnstile>\<^sub>n e\<^sub>t : t"
proof -
  assume "typecheck e = Some (e\<^sub>t, t)"
  then obtain e' tt vs con sub where T: "typecheck' Map.empty {} e = (e', tt, vs, con) \<and>
    unify' con = Some sub \<and> e\<^sub>t = tsubstt sub (solidify e') \<and> t = tsubsts sub (typeify tt)" 
      by (auto split: option.splits prod.splits)
  moreover hence "map_option (typeify \<circ> subst sub) \<circ> Map.empty \<turnstile>\<^sub>n solidify (hsubst sub e') : 
    typeify (subst sub tt)" by (metis typecheck_succeeds valid_empty extends_refl)
  moreover from T have "valid_ty_uexpr tt" and "valid_ty_hexpr e'" by auto
  ultimately show "Map.empty \<turnstile>\<^sub>n e\<^sub>t : t" by simp
qed

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> e = erase (solidify e')"
  by (induction rule: typecheck_induct) auto

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> e = erase e\<^sub>t"
  by (auto split: option.splits prod.splits)

lemma [dest]: "erase e\<^sub>t = NVar x \<Longrightarrow> e\<^sub>t = TVar x"
  by (induction e\<^sub>t) simp_all

lemma [dest]: "erase e\<^sub>t = NLam x e \<Longrightarrow> \<exists>t e\<^sub>t'. e\<^sub>t = TLam x t e\<^sub>t' \<and> e = erase e\<^sub>t'"
  by (induction e\<^sub>t) simp_all

lemma [dest]: "erase e\<^sub>t = NApp e\<^sub>1 e\<^sub>2 \<Longrightarrow> \<exists>e\<^sub>1' e\<^sub>2'. e\<^sub>t = TApp e\<^sub>1' e\<^sub>2' \<and> e\<^sub>1 = erase e\<^sub>1'\<and> e\<^sub>2 = erase e\<^sub>2'"
  by (induction e\<^sub>t) simp_all

lemma vars_expand: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> vs \<subseteq> vs'"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (simp_all add: Let_def split: option.splits prod.splits, fastforce+)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> finite vs' = finite vs"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (simp_all add: Let_def split: option.splits prod.splits)

lemma [simp]: "typecheck' (\<Gamma>(x \<mapsto> Var v)) vs e = (e', t, vs', con) \<Longrightarrow> 
  unify' con = None \<Longrightarrow> \<exists>xe' xt xvs' xcon. typecheck' (\<Gamma>(x \<mapsto> t')) vs e = 
    (xe', xt, xvs', xcon) \<and> unify' xcon = None"
proof (induction e arbitrary: \<Gamma> vs e' t vs' con)
  case (NLam y e)
  let ?v = "fresh vs"
  from NLam have "typecheck' (\<Gamma>(x \<mapsto> Var v)) vs (NLam y e) = (e', t, vs', con)" by blast
  then obtain xe' xt where T: "typecheck' (\<Gamma>(x \<mapsto> Var v, y \<mapsto> Var ?v)) (insert ?v vs) e = 
    (xe', xt, vs', con) \<and> e' = HLam y (Var ?v) xe' \<and> t = Ctor ''Arrow'' [Var ?v, xt]" 
      by (auto simp add: Let_def split: prod.splits)
  thus ?case
  proof (cases "x = y")
    case True
    with T have "typecheck' (\<Gamma>(x \<mapsto> t')) vs (NLam y e) = 
      (HLam y (Var ?v) xe', Ctor ''Arrow'' [Var ?v, xt], vs', con)" 
        by (simp add: Let_def split: prod.splits)
    with NLam show ?thesis by blast
  next
    case False
    with T have "typecheck' (\<Gamma>(y \<mapsto> Var ?v, x \<mapsto> Var v)) (insert ?v vs) e = (xe', xt, vs', con)"
      by (simp add: fun_upd_twist)
    with NLam obtain e'' t'' vs'' con' where "unify' con' = None \<and>
      typecheck' (\<Gamma>(y \<mapsto> Var ?v, x \<mapsto> t')) (insert ?v vs) e = (e'', t'', vs'', con')" by blast
    with False have "typecheck' (\<Gamma>(x \<mapsto> t')) vs (NLam y e) = 
      (HLam y (Var ?v) e'', Ctor ''Arrow'' [Var ?v, t''], vs'', con') \<and> unify' con' = None" 
        by (simp add: Let_def fun_upd_twist split: prod.splits)
    thus ?thesis by blast
  qed
next
  case (NApp e1 e2)
  let ?v = "fresh vs"
  obtain e\<^sub>1' t\<^sub>1 vs\<^sub>1 con\<^sub>1 where T1: "(e\<^sub>1', t\<^sub>1, vs\<^sub>1, con\<^sub>1) = 
    typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert ?v vs) e1" 
      by (cases "typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert ?v vs) e1") simp_all
  obtain e\<^sub>2' t\<^sub>2 vs\<^sub>2 con\<^sub>2 where T2: "(e\<^sub>2', t\<^sub>2, vs\<^sub>2, con\<^sub>2) = typecheck' (\<Gamma>(x \<mapsto> Var v)) vs\<^sub>1 e2" 
    by (cases "typecheck' (\<Gamma>(x \<mapsto> Var v)) vs\<^sub>1 e2") simp_all
  from NApp have "typecheck' (\<Gamma>(x \<mapsto> Var v)) vs (NApp e1 e2) = (e', t, vs', con)" by blast
  with T1 T2 have X: "e' = HApp e\<^sub>1' e\<^sub>2' \<and> t = Var ?v \<and> vs' = vs\<^sub>2 \<and> 
    con = (t\<^sub>1, Ctor ''Arrow'' [t\<^sub>2, Var ?v]) # con\<^sub>1 @ con\<^sub>2" 
      by (auto simp add: Let_def split: prod.splits)

  from NApp T1 have "unify' con\<^sub>1 = None \<Longrightarrow>
    \<exists>xe' xt xvs' xcon. typecheck' (\<Gamma>(x \<mapsto> t')) (insert ?v vs) e1 = (xe', xt, xvs', xcon) \<and> unify' xcon = None" by metis
  from NApp have "typecheck' (w\<Gamma>(x \<mapsto> Var v)) wvs e2 = (we', wt, wvs', wcon) \<Longrightarrow>
    unify' wcon = None \<Longrightarrow>
    \<exists>xe' xt xvs' xcon. typecheck' (w\<Gamma>(x \<mapsto> t')) wvs e2 = (xe', xt, xvs', xcon) \<and> unify' xcon = None" by blast
  from NApp have "unify' con = None" by simp







  have "(case typecheck' (\<Gamma>(x \<mapsto> t')) (insert ?v vs) e1 of
        (e\<^sub>1', t\<^sub>1, vs', con\<^sub>1) \<Rightarrow>
          case typecheck' (\<Gamma>(x \<mapsto> t')) vs' e2 of
          (e\<^sub>2', t\<^sub>2, vs'', con\<^sub>2) \<Rightarrow>
            (HApp e\<^sub>1' e\<^sub>2', Var ?v, vs'', (t\<^sub>1, Ctor ''Arrow'' [t\<^sub>2, Var ?v]) # con\<^sub>1 @ con\<^sub>2)) =
    (xe', xt, xvs', xcon) \<and>
    unify' xcon = None" by simp
  hence "typecheck' (\<Gamma>(x \<mapsto> t')) vs (NApp e1 e2) = (xe', xt, xvs', xcon) \<and> unify' xcon = None" 
    by simp
  thus ?case by blast
qed auto

lemma [simp]: "(map_option typeify \<circ> \<Gamma>)(x \<mapsto> t') \<turnstile>\<^sub>n e : t \<Longrightarrow> subst_vars \<Gamma> \<subseteq> vs \<Longrightarrow> v \<in> vs \<Longrightarrow>
  tvarst e \<subseteq> vs \<Longrightarrow> typecheck' (\<Gamma>(x \<mapsto> Var v)) vs (erase e) = (e', tt, vs', con) \<Longrightarrow> 
    unify' con = None \<Longrightarrow> False"
proof (induction "(map_option typeify \<circ> \<Gamma>)(x \<mapsto> t')" e t arbitrary: \<Gamma> vs e' tt vs' con 
       rule: typecheckn.induct)
  case (tcn_lam y t\<^sub>1 e t\<^sub>2)
  let ?v = "fresh vs"
  from tcn_lam obtain e'' tt' where T: "
      typecheck' (\<Gamma>(x \<mapsto> Var v, y \<mapsto> Var ?v)) (insert ?v vs) (erase e) = (e'', tt', vs', con) \<and> 
        e' = HLam y (Var ?v) e'' \<and> tt = Ctor ''Arrow'' [Var ?v, tt']" 
    by (auto simp add: Let_def split: prod.splits)
  thus ?case 
  proof (cases "x = y")
    case True
    from tcn_lam have "(map_option typeify \<circ> \<Gamma>)(x \<mapsto> t', y \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e : t\<^sub>2" by simp 
    from tcn_lam have "subst_vars \<Gamma> \<subseteq> vs" by simp 
    from tcn_lam have "v \<in> vs" by simp 
    from tcn_lam have "unify' con = None" by simp 
    from tcn_lam have "tvars t\<^sub>1 \<subseteq> vs" by simp
    from tcn_lam have "tvarst e \<subseteq> vs" by simp


    then show ?thesis by simp
  next
    case False
    hence X: "(map_option typeify \<circ> \<Gamma>)(x \<mapsto> t', y \<mapsto> t\<^sub>1) = 
      (map_option typeify \<circ> (\<Gamma>(y \<mapsto> untypify t\<^sub>1)))(x \<mapsto> t')" by (simp add: fun_upd_twist)
    from tcn_lam(3, 5) have Y: "subst_vars (\<Gamma>(y \<mapsto> untypify t\<^sub>1)) \<subseteq> insert ?v vs" 
      by (auto simp add: subst_vars_def ran_def)
    from tcn_lam have Z: "v \<in> insert ?v vs" by simp
    from tcn_lam have "tvarst e \<subseteq> insert ?v vs" by auto


    with tcn_lam X Y Z have "typecheck' (\<Gamma>(y \<mapsto> untypify t\<^sub>1, x \<mapsto> Var v)) (insert ?v vs) (erase e) = 
      (xe', xtt, xvs', xcon) \<Longrightarrow> 
      unify' xcon = None \<Longrightarrow> False" by blast 


    from T have "
      typecheck' (\<Gamma>(x \<mapsto> Var v, y \<mapsto> Var ?v)) (insert ?v vs) (erase e) = (e'', tt', vs', con) \<and> 
        e' = HLam y (Var ?v) e'' \<and> tt = Ctor ''Arrow'' [Var ?v, tt']" by simp

    from tcn_lam have "(map_option typeify \<circ> \<Gamma>)(x \<mapsto> t', y \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e : t\<^sub>2" by simp 
    from tcn_lam have "subst_vars \<Gamma> \<subseteq> vs" by simp 
    from tcn_lam have "v \<in> vs" by simp 
    from tcn_lam have "unify' con = None" by simp 
    from tcn_lam have "tvars t\<^sub>1 \<subseteq> vs" by simp
    from tcn_lam have "tvarst e \<subseteq> vs" by simp


    then show ?thesis by simp
  qed
next
  case (tcn_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  thus ?case by simp
qed (simp_all split: if_splits option.splits)

lemma [simp]: "subst_vars \<Gamma> \<subseteq> vs \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> t \<in> ran (map_option typeify \<circ> \<Gamma>) \<Longrightarrow> 
    finite vs \<Longrightarrow> fresh vs \<notin> tvars t"
  by (unfold subst_vars_def valid_ty_subst_def ran_def) fastforce

lemma typecheck_fails' [simp]: "typecheck' \<Gamma> vs e = (e', tt, vs', con) \<Longrightarrow> unify' con = None \<Longrightarrow> 
  finite vs \<Longrightarrow> subst_vars \<Gamma> \<subseteq> vs \<Longrightarrow> tvarst e\<^sub>t \<subseteq> vs \<Longrightarrow> map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>t : t \<Longrightarrow> 
    erase e\<^sub>t = e \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> False"
proof (induction arbitrary: e\<^sub>t t rule: typecheck_induct)
  case (NLam \<Gamma> vs vs' con x e\<^sub>1 e\<^sub>1' t' v)
  then obtain t\<^sub>1 e\<^sub>t' where E: "e\<^sub>t = TLam x t\<^sub>1 e\<^sub>t' \<and> e\<^sub>1 = erase e\<^sub>t'" by auto
  with NLam obtain t\<^sub>2 where T: "((map_option typeify \<circ> \<Gamma>)(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e\<^sub>t' : t\<^sub>2) \<and> t = Arrow t\<^sub>1 t\<^sub>2" 
    by blast
  from NLam have "subst_vars \<Gamma> \<subseteq> vs" by simp
  hence X: "subst_vars (\<Gamma>(x \<mapsto> Var (fresh vs))) \<subseteq> insert (fresh vs) vs" 
    by (auto simp add: subst_vars_def ran_def)
  with NLam E show ?case
  proof (cases "\<exists>tt. (map_option typeify \<circ> \<Gamma>)(x \<mapsto> TyVar (fresh vs)) \<turnstile>\<^sub>n e\<^sub>t' : tt")
    case False

    from False have "\<forall>tt. \<not> (map_option typeify \<circ> \<Gamma>)(x \<mapsto> TyVar (fresh vs)) \<turnstile>\<^sub>n e\<^sub>t' : tt" by simp
    from NLam E have "typecheck' (\<Gamma>(x \<mapsto> Var (fresh vs))) (insert (fresh vs) vs) (erase e\<^sub>t') = 
      (e\<^sub>1', t', vs', con)" by simp
    from NLam have "unify' con = None" by simp
    from NLam have "finite vs" by simp
    from NLam have "subst_vars \<Gamma> \<subseteq> vs" by simp
    from NLam E have "tvars t\<^sub>1 \<subseteq> vs" by simp
    from NLam E have "tvarst e\<^sub>t' \<subseteq> vs" by simp
    from NLam have "valid_ty_subst \<Gamma>" by simp
    from T have "(map_option typeify \<circ> \<Gamma>)(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e\<^sub>t' : t\<^sub>2" by simp


    have False by simp
    thus ?thesis by blast
  qed fastforce+
next
  case (NApp \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2)
  then obtain e\<^sub>1\<^sub>t e\<^sub>2\<^sub>t where E: "e\<^sub>t = TApp e\<^sub>1\<^sub>t e\<^sub>2\<^sub>t \<and> e\<^sub>1 = erase e\<^sub>1\<^sub>t \<and> e\<^sub>2 = erase e\<^sub>2\<^sub>t" by auto
  with NApp obtain t\<^sub>1' where T: "(map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>1\<^sub>t : Arrow t\<^sub>1' t) \<and> 
    (map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>2\<^sub>t : t\<^sub>1')" by blast

  let ?v = "fresh vs"

  from NApp have "typecheck' \<Gamma> (insert ?v vs) e\<^sub>1 = (e\<^sub>1', t\<^sub>1, vs'', con\<^sub>1)" by simp
  from NApp have "typecheck' \<Gamma> vs'' e\<^sub>2 = (e\<^sub>2', t\<^sub>2, vs', con\<^sub>2)" by simp
  from NApp E have "unify' con\<^sub>1 = None \<Longrightarrow>
    tvarst e\<^sub>1\<^sub>t \<subseteq> insert ?v vs \<Longrightarrow>
    map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>1\<^sub>t : xt \<Longrightarrow> False" by blast
  from NApp E have "unify' con\<^sub>2 = None \<Longrightarrow>
    finite vs'' \<Longrightarrow>
    subst_vars \<Gamma> \<subseteq> vs'' \<Longrightarrow>
    tvarst e\<^sub>2\<^sub>t \<subseteq> vs'' \<Longrightarrow> map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>2\<^sub>t : xt \<Longrightarrow> False" by blast
  from NApp have "unify' ((t\<^sub>1, Ctor ''Arrow'' [t\<^sub>2, Var ?v]) # con\<^sub>1 @ con\<^sub>2) = None" by simp
  from NApp have "finite vs" by simp
  from NApp have "subst_vars \<Gamma> \<subseteq> vs" by simp
  from NApp E have "tvarst e\<^sub>1\<^sub>t \<subseteq> vs" by simp
  from NApp E have "tvarst e\<^sub>2\<^sub>t \<subseteq> vs" by simp
  from NApp have "valid_ty_subst \<Gamma>" by simp


  have False by simp
  thus ?case by simp
qed fastforce+

lemma typecheck_fails [simp]: "typecheck e = None \<Longrightarrow> 
  \<nexists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> tvarst e\<^sub>t = {} \<and> e = erase e\<^sub>t"
proof                              
  assume "typecheck e = None"
  then obtain e' tt vs' con where X: "typecheck' Map.empty {} e = (e', tt, vs', con) \<and> 
    unify' con = None" by (auto split: prod.splits option.splits)
  assume "\<exists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> tvarst e\<^sub>t = {} \<and> e = erase e\<^sub>t"
  then obtain e\<^sub>t t where Y: "(map_option typeify \<circ> Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> tvarst e\<^sub>t = {} \<and> 
    e = erase e\<^sub>t" by fastforce
  hence Z: "tvarst e\<^sub>t \<subseteq> {}" by simp
  have W: "subst_vars Map.empty \<subseteq> {}" by simp
  have "valid_ty_subst Map.empty" by simp
  with X Y Z W show "False" by (metis typecheck_fails' finite.emptyI)
qed

lemma [simp]: "valn (erase e) = valt e"
  by (induction e) simp_all

lemma [simp]: "all_vars (erase e) = all_varst e"
  by (induction e) simp_all

lemma [simp]: "erase (subst_vart x y e) = subst_var x y (erase e)"
  by (induction e) simp_all

lemma [simp]: "erase (substt x e' e) = substn x (erase e') (erase e)"
  by (induction x e' e rule: substt.induct) (simp_all add: Let_def)

theorem completeness [simp]: "e \<Down>\<^sub>t v \<Longrightarrow> erase e \<Down> erase v"
  by (induction e v rule: evalt.induct) simp_all

lemma [simp]: "all_varst (tsubstt sub e) = all_varst e"
  by (induction e) simp_all

lemma [simp]: "tsubstt sub (subst_vart y x e) = subst_vart y x (tsubstt sub e)"
  by (induction e) simp_all

lemma [simp]: "tsubstt sub (substt x v e) = substt x (tsubstt sub v) (tsubstt sub e)"
  by (induction x v e rule: substt.induct) (simp_all add: Let_def)

lemma [simp]: "e \<Down>\<^sub>t v \<Longrightarrow> tsubstt sub e \<Down>\<^sub>t tsubstt sub v"
  by (induction e v rule: evalt.induct) simp_all

lemma correctness' [simp]: "e \<Down> v \<Longrightarrow> typecheck' \<Gamma> vs e = (e\<^sub>t, t1, vs1, uni1) \<Longrightarrow> 
  typecheck' \<Gamma> vs v = (v\<^sub>t, t2, vs2, uni2) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> unify' uni1 = Some sub1 \<Longrightarrow>
    unify' uni2 = Some sub2 \<Longrightarrow> tsubsts sub1 (typeify t1) = tsubsts sub2 (typeify t2) \<and> 
      tsubstt sub1 (solidify e\<^sub>t) \<Down>\<^sub>t tsubstt sub2 (solidify v\<^sub>t)"
proof (induction e v arbitrary: vs e\<^sub>t t1 vs1 uni1 sub1 v\<^sub>t t2 vs2 uni2 sub2 rule: evaln.induct)
  case (evn_app e\<^sub>1 x e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  let ?v = "fresh vs"
  let ?v2 = "fresh (insert ?v vs)"
  obtain e\<^sub>1\<^sub>t t\<^sub>1 vs' con\<^sub>1 where E1: "typecheck' \<Gamma> (insert ?v vs) e\<^sub>1 = (e\<^sub>1\<^sub>t, t\<^sub>1, vs', con\<^sub>1)" 
    by (cases "typecheck' \<Gamma> (insert ?v vs) e\<^sub>1") 
  obtain e\<^sub>2\<^sub>t t\<^sub>2 vs'' con\<^sub>2 where E2: "typecheck' \<Gamma> vs' e\<^sub>2 = (e\<^sub>2\<^sub>t, t\<^sub>2, vs'', con\<^sub>2)" 
    by (cases "typecheck' \<Gamma> vs' e\<^sub>2") 
  with evn_app E1 have E: "e\<^sub>t = HApp e\<^sub>1\<^sub>t e\<^sub>2\<^sub>t \<and> t1 = Var ?v \<and> vs1 = vs'' \<and> 
    uni1 = (t\<^sub>1, Ctor ''Arrow'' [t\<^sub>2, Var ?v]) # con\<^sub>1 @ con\<^sub>2" 
      by (auto simp add: Let_def)


  from evn_app have "e\<^sub>1 \<Down> NLam x e\<^sub>1'" by simp
  from evn_app have "e\<^sub>2 \<Down> v\<^sub>2" by simp
  from evn_app have "substn x v\<^sub>2 e\<^sub>1' \<Down> v" by simp

  from evn_app E2 have "typecheck' \<Gamma> vs' v\<^sub>2 = (xv\<^sub>t, xt20, xvs20, xuni2) \<Longrightarrow>
    unify' con\<^sub>2 = Some xsub10 \<Longrightarrow>
    unify' xuni2 = Some xsub20 \<Longrightarrow>
    tsubsts xsub10 (typeify t\<^sub>2) = tsubsts xsub20 (typeify xt20) \<and>
    tsubstt xsub10 (solidify e\<^sub>2\<^sub>t) \<Down>\<^sub>t tsubstt xsub20 (solidify xv\<^sub>t)" by simp
  from evn_app have "typecheck' \<Gamma> xvs (substn x v\<^sub>2 e\<^sub>1') = (xe\<^sub>t, xt10, xvs10, xuni1) \<Longrightarrow>
    typecheck' \<Gamma> xvs v = (xv\<^sub>t, xt20, xvs20, xuni2) \<Longrightarrow>
    valid_ty_subst \<Gamma> \<Longrightarrow>
    unify' xuni1 = Some xsub10 \<Longrightarrow>
    unify' xuni2 = Some xsub20 \<Longrightarrow>
    tsubsts xsub10 (typeify xt10) = tsubsts xsub20 (typeify xt20) \<and>
    tsubstt xsub10 (solidify xe\<^sub>t) \<Down>\<^sub>t tsubstt xsub20 (solidify xv\<^sub>t)" by simp
  from evn_app have "typecheck' \<Gamma> vs v = (v\<^sub>t, t2, vs2, uni2)" by simp
  from evn_app have "valid_ty_subst \<Gamma>" by simp
  from evn_app have "unify' uni1 = Some sub1" by simp
  from evn_app have "unify' uni2 = Some sub2" by simp




  have X: "tsubsts sub1 (typeify (Var ?v)) = tsubsts sub2 (typeify t2)" by simp


  obtain e\<^sub>1\<^sub>t' t\<^sub>1' vsx' con\<^sub>1' where "(e\<^sub>1\<^sub>t', t\<^sub>1', vsx', con\<^sub>1') = 
    typecheck' (\<Gamma>(x \<mapsto> Var ?v2)) (insert ?v2 (insert ?v vs)) e\<^sub>1'" 
      by (cases "typecheck' (\<Gamma>(x \<mapsto> Var ?v2)) (insert ?v2 (insert ?v vs)) e\<^sub>1'") simp_all 
  hence "typecheck' \<Gamma> (insert ?v vs) (NLam x e\<^sub>1') = 
    (HLam x (Var ?v2) e\<^sub>1\<^sub>t', Ctor ''Arrow'' [Var ?v2, t\<^sub>1'], vsx', con\<^sub>1')" 
      by (auto simp add: Let_def split: prod.splits)
  with evn_app E1 have "unify' con\<^sub>1 = Some xsub10 \<Longrightarrow>
    unify' con\<^sub>1' = Some xsub20 \<Longrightarrow>
    tsubsts xsub10 (typeify t\<^sub>1) = tsubsts xsub20 (typeify (Ctor ''Arrow'' [Var ?v2, t\<^sub>1'])) \<and>
    tsubstt xsub10 (solidify e\<^sub>1\<^sub>t) \<Down>\<^sub>t tsubstt xsub20 (solidify (HLam x (Var ?v2) e\<^sub>1\<^sub>t'))" by blast


  have "tsubstt sub1 (solidify e\<^sub>1\<^sub>t) \<Down>\<^sub>t TLam x t xe\<^sub>1' \<Longrightarrow> 
        tsubstt sub1 (solidify e\<^sub>2\<^sub>t) \<Down>\<^sub>t xv\<^sub>2 \<Longrightarrow> 
        substt x xv\<^sub>2 xe\<^sub>1' \<Down>\<^sub>t tsubstt sub2 (solidify v\<^sub>t) \<Longrightarrow> 
        TApp (tsubstt sub1 (solidify e\<^sub>1\<^sub>t)) (tsubstt sub1 (solidify e\<^sub>2\<^sub>t)) \<Down>\<^sub>t tsubstt sub2 (solidify v\<^sub>t)" by simp


  have "TApp (tsubstt sub1 (solidify e\<^sub>1\<^sub>t)) (tsubstt sub1 (solidify e\<^sub>2\<^sub>t)) \<Down>\<^sub>t tsubstt sub2 (solidify v\<^sub>t)" by simp
  with E X show ?case by simp
qed (auto simp add: Let_def split: option.splits prod.splits)

theorem correctness: "e \<Down> v \<Longrightarrow> typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> typecheck v = Some (v\<^sub>t, t) \<Longrightarrow> 
    e\<^sub>t \<Down>\<^sub>t v\<^sub>t"
  by (auto split: option.splits prod.splits)

end