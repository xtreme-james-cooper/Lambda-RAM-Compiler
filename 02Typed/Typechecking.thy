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

primrec typecheck' :: "subst \<Rightarrow> var set \<Rightarrow> nexpr \<rightharpoonup> hexpr \<times> uexpr \<times> var set \<times> subst" where
  "typecheck' \<Gamma> vs (NVar x) = (case \<Gamma> x of 
      Some t \<Rightarrow> Some (HVar x, t, vs, Map.empty) 
    | None \<Rightarrow> None)"
| "typecheck' \<Gamma> vs (NConst k) = Some (HConst k, Ctor ''Base'' [], vs, Map.empty)"
| "typecheck' \<Gamma> vs (NLam x e) = (
    let v = fresh vs
    in case typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e of
        Some (e', t, vs', sub) \<Rightarrow> Some (HLam x (Var v) e', Ctor ''Arrow'' [Var v, t], vs', sub)
      | None \<Rightarrow> None)"
| "typecheck' \<Gamma> vs (NApp e\<^sub>1 e\<^sub>2) = (
    let v = fresh vs
    in case typecheck' \<Gamma> (insert v vs) e\<^sub>1 of 
        Some (e\<^sub>1', t\<^sub>1, vs', sub\<^sub>1) \<Rightarrow> (case typecheck' (env_subst sub\<^sub>1 \<Gamma>) vs' e\<^sub>2 of
            Some (e\<^sub>2', t\<^sub>2, vs'', sub\<^sub>2) \<Rightarrow> (case unify t\<^sub>1 (Ctor ''Arrow'' [t\<^sub>2, Var v]) of
                Some sub\<^sub>3 \<Rightarrow> Some (HApp e\<^sub>1' e\<^sub>2', Var v, vs'', combine_subst sub\<^sub>3 sub\<^sub>2)
              | None \<Rightarrow> None)
          | None \<Rightarrow> None)
      | None \<Rightarrow> None)"

fun typeify :: "uexpr \<Rightarrow> ty" where
  "typeify (Var v) = TyVar v"
| "typeify (Ctor k []) = (if k = ''Base'' then Base else undefined)"
| "typeify (Ctor k [t\<^sub>1, t\<^sub>2]) = 
    (if k = ''Arrow'' then Arrow (typeify t\<^sub>1) (typeify t\<^sub>2) else undefined)"
| "typeify (Ctor k ts) = undefined"

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

primrec solidify :: "hexpr \<Rightarrow> texpr" where
  "solidify (HVar x) = TVar x"
| "solidify (HConst k) = TConst k"
| "solidify (HLam x t e) = TLam x (typeify t) (solidify e)"
| "solidify (HApp e\<^sub>1 e\<^sub>2) = TApp (solidify e\<^sub>1) (solidify e\<^sub>2)"

primrec valid_ty_hexpr :: "hexpr \<Rightarrow> bool" where
  "valid_ty_hexpr (HVar x) = True"
| "valid_ty_hexpr (HConst k) = True"
| "valid_ty_hexpr (HLam x t e) = (valid_ty_uexpr t \<and> valid_ty_hexpr e)"
| "valid_ty_hexpr (HApp e\<^sub>1 e\<^sub>2) = (valid_ty_hexpr e\<^sub>1 \<and> valid_ty_hexpr e\<^sub>2)"

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
  "typecheck e = (case typecheck' Map.empty {} e of
      Some (e', t, vs, sub) \<Rightarrow> Some (tsubstt sub (solidify e'), tsubsts sub (typeify t))
    | None \<Rightarrow> None)"

lemma typecheck_Some [consumes 1, case_names NVar NConst NLam NApp]: "
  typecheck' \<Gamma> vs e = Some (e', t, vs', sub) \<Longrightarrow> 
  (\<And>\<Gamma> vs t x. \<Gamma> x = Some t \<Longrightarrow> P \<Gamma> vs (NVar x) (HVar x) t vs Map.empty) \<Longrightarrow> 
  (\<And>\<Gamma> vs k. P \<Gamma> vs (NConst k) (HConst k) (Ctor ''Base'' []) vs Map.empty) \<Longrightarrow> 
  (\<And>\<Gamma> vs vs' sub x e\<^sub>1 e\<^sub>1' t' v. v = fresh vs \<Longrightarrow> typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>1 = 
    Some (e\<^sub>1', t', vs', sub) \<Longrightarrow> P (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>1 e\<^sub>1' t' vs' sub \<Longrightarrow> 
      P \<Gamma> vs (NLam x e\<^sub>1) (HLam x (Var v) e\<^sub>1') (Ctor ''Arrow'' [Var v, t']) vs' sub) \<Longrightarrow> 
  (\<And>\<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' sub\<^sub>1 e\<^sub>2' t\<^sub>2 sub\<^sub>2 sub\<^sub>3. v = fresh vs \<Longrightarrow> 
    typecheck' \<Gamma> (insert v vs) e\<^sub>1 = Some (e\<^sub>1', t\<^sub>1, vs'', sub\<^sub>1) \<Longrightarrow> 
      typecheck' (env_subst sub\<^sub>1 \<Gamma>) vs'' e\<^sub>2 = Some (e\<^sub>2', t\<^sub>2, vs', sub\<^sub>2) \<Longrightarrow> 
        P \<Gamma> (insert v vs) e\<^sub>1 e\<^sub>1' t\<^sub>1 vs'' sub\<^sub>1 \<Longrightarrow> P (env_subst sub\<^sub>1 \<Gamma>) vs'' e\<^sub>2 e\<^sub>2' t\<^sub>2 vs' sub\<^sub>2 \<Longrightarrow> 
          unify t\<^sub>1 (Ctor ''Arrow'' [t\<^sub>2, Var v]) = Some sub\<^sub>3 \<Longrightarrow> 
            P \<Gamma> vs (NApp e\<^sub>1 e\<^sub>2) (HApp e\<^sub>1' e\<^sub>2') (Var v) vs' (combine_subst sub\<^sub>3 sub\<^sub>2)) \<Longrightarrow> 
              P \<Gamma> vs e e' t vs' sub"
proof (induction e arbitrary: \<Gamma> vs e' t vs' sub)
  case (NLam x e)
  let ?v = "fresh vs"
  from NLam(2) obtain ee' tt where E: "e' = HLam x (Var ?v) ee' \<and> t = Ctor ''Arrow'' [Var ?v, tt] \<and>
    typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e = Some (ee', tt, vs', sub)" 
      by (auto simp add: Let_def split: option.splits)
  with NLam have "P (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e ee' tt vs' sub" by auto
  with NLam E show ?case by metis
qed (auto simp add: Let_def split: option.splits)

lemma typecheck_None [consumes 1, case_names NVar NLam NApp1 NApp2 NApp3]: "
  typecheck' \<Gamma> vs e = None \<Longrightarrow> 
  (\<And>\<Gamma> vs x. \<Gamma> x = None \<Longrightarrow> P \<Gamma> vs (NVar x)) \<Longrightarrow> 
  (\<And>\<Gamma> vs x e\<^sub>1 v. v = fresh vs \<Longrightarrow> typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>1 = None \<Longrightarrow> 
    P (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>1 \<Longrightarrow> P \<Gamma> vs (NLam x e\<^sub>1)) \<Longrightarrow> 
  (\<And>\<Gamma> vs e\<^sub>1 e\<^sub>2 v. v = fresh vs \<Longrightarrow> typecheck' \<Gamma> (insert v vs) e\<^sub>1 = None \<Longrightarrow> P \<Gamma> (insert v vs) e\<^sub>1 \<Longrightarrow> 
    P \<Gamma> vs (NApp e\<^sub>1 e\<^sub>2)) \<Longrightarrow> 
  (\<And>\<Gamma> vs e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' sub\<^sub>1. v = fresh vs \<Longrightarrow> 
    typecheck' \<Gamma> (insert v vs) e\<^sub>1 = Some (e\<^sub>1', t\<^sub>1, vs'', sub\<^sub>1) \<Longrightarrow> 
      typecheck' (env_subst sub\<^sub>1 \<Gamma>) vs'' e\<^sub>2 = None \<Longrightarrow> P (env_subst sub\<^sub>1 \<Gamma>) vs'' e\<^sub>2 \<Longrightarrow> 
        P \<Gamma> vs (NApp e\<^sub>1 e\<^sub>2)) \<Longrightarrow> 
  (\<And>\<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' sub\<^sub>1 e\<^sub>2' t\<^sub>2 sub\<^sub>2. v = fresh vs \<Longrightarrow> 
    typecheck' \<Gamma> (insert v vs) e\<^sub>1 = Some (e\<^sub>1', t\<^sub>1, vs'', sub\<^sub>1) \<Longrightarrow> 
      typecheck' (env_subst sub\<^sub>1 \<Gamma>) vs'' e\<^sub>2 = Some (e\<^sub>2', t\<^sub>2, vs', sub\<^sub>2) \<Longrightarrow> 
        unify t\<^sub>1 (Ctor ''Arrow'' [t\<^sub>2, Var v]) = None \<Longrightarrow> 
          P \<Gamma> vs (NApp e\<^sub>1 e\<^sub>2)) \<Longrightarrow> P \<Gamma> vs e"
proof (induction e arbitrary: \<Gamma> vs)
  case (NLam x e)
  let ?v = "fresh vs"
  from NLam have X: "typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e = None" 
    by (auto simp add: Let_def split: option.splits)
  with NLam have "P (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e" by simp
  with NLam(4) X show ?case by blast
qed (simp_all add: Let_def split: option.splits prod.splits)

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

lemma [simp]: "typecheck' \<Gamma> vs e = Some (e', t, vs', sub) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow>  
  valid_ty_hexpr e' \<and> valid_ty_uexpr t \<and> valid_ty_subst sub"
proof (induction rule: typecheck_Some)
  case (NApp \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' sub\<^sub>1 e\<^sub>2' t\<^sub>2 sub\<^sub>2 sub\<^sub>3)
  hence "valid_ty_uexpr (Ctor ''Arrow'' [t\<^sub>2, Var v])" by simp
  with NApp have X: "valid_ty_subst sub\<^sub>3" by fastforce
  hence "valid_ty_uexpr (case sub\<^sub>3 v of None \<Rightarrow> Var v | Some e \<Rightarrow> e)" 
    by (auto simp add: valid_ty_subst_def ran_def split: option.splits)
  with NApp X show ?case by auto
qed fastforce+

lemma [elim]: "valid_ty_subst \<Gamma> \<Longrightarrow> typecheck' \<Gamma> vs e = Some (e', t, vs', sub) \<Longrightarrow> valid_ty_uexpr t"
  by simp

lemma [elim]: "valid_ty_subst \<Gamma> \<Longrightarrow> typecheck' \<Gamma> vs e = Some (e', t, vs', sub) \<Longrightarrow> 
    valid_ty_hexpr e'"
  by simp

lemma [elim]: "valid_ty_subst \<Gamma> \<Longrightarrow> typecheck' \<Gamma> vs e = Some (e', t, vs', sub) \<Longrightarrow> 
    valid_ty_subst sub"
  by simp

lemma typecheck_succeeds [simp]: "typecheck' \<Gamma> vs e = Some (e', t, vs', sub) \<Longrightarrow> 
  valid_ty_subst \<Gamma> \<Longrightarrow>
    map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub e') : typeify (subst sub t)"
proof (induction rule: typecheck_Some)
  case (NLam \<Gamma> vs vs' sub x e\<^sub>1 e\<^sub>1' t' v)
  hence "valid_ty_subst (\<Gamma>(x \<mapsto> Var v))" by simp
  with NLam have "map_option (typeify \<circ> subst sub) \<circ> \<Gamma>(x \<mapsto> Var v) \<turnstile>\<^sub>n solidify (hsubst sub e\<^sub>1') : 
    typeify (subst sub t')" by blast
  hence "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub (HLam x (Var v) e\<^sub>1')) :
    typeify (subst sub (Ctor ''Arrow'' [Var v, t']))" by simp
  thus ?case by blast
next
  case (NApp \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' sub\<^sub>1 e\<^sub>2' t\<^sub>2 sub\<^sub>2 sub\<^sub>3)
  from NApp have "v = fresh vs" by simp
  from NApp have "typecheck' \<Gamma> (insert v vs) e\<^sub>1 = Some (e\<^sub>1', t\<^sub>1, vs'', sub\<^sub>1)" by simp
  with NApp have E1: "valid_ty_hexpr e\<^sub>1' \<and> valid_ty_subst sub\<^sub>1" by auto
  from NApp have "typecheck' (env_subst sub\<^sub>1 \<Gamma>) vs'' e\<^sub>2 = Some (e\<^sub>2', t\<^sub>2, vs', sub\<^sub>2)" by simp
  with NApp have E2: "valid_ty_hexpr e\<^sub>2' \<and> valid_ty_subst sub\<^sub>2" by auto
  from NApp have "unify t\<^sub>1 (Ctor ''Arrow'' [t\<^sub>2, Var v]) = Some sub\<^sub>3" by simp
  from NApp have "map_option (typeify \<circ> subst sub\<^sub>1) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub\<^sub>1 e\<^sub>1') : typeify (subst sub\<^sub>1 t\<^sub>1)" by blast
  from NApp have "valid_ty_subst \<Gamma>" by simp

  from NApp E1 have "valid_ty_subst (env_subst sub\<^sub>1 \<Gamma>)" by simp
  with NApp have "map_option (typeify \<circ> subst sub\<^sub>2) \<circ> env_subst sub\<^sub>1 \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub\<^sub>2 e\<^sub>2') : typeify (subst sub\<^sub>2 t\<^sub>2)" by blast


  from E1 have X: "map_option (tsubsts sub\<^sub>3 \<circ> tsubsts sub\<^sub>2 \<circ> typeify) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub\<^sub>3 (hsubst sub\<^sub>2 e\<^sub>1')) : 
    Arrow xt\<^sub>1 (typeify (subst sub\<^sub>3 (subst sub\<^sub>2 (Var v))))" by simp
  with NApp E2 have X: "map_option (typeify \<circ> subst sub\<^sub>3 \<circ> subst sub\<^sub>2) \<circ> \<Gamma> \<turnstile>\<^sub>n 
    solidify (hsubst sub\<^sub>3 (hsubst sub\<^sub>2 e\<^sub>1')) : Arrow xt\<^sub>1 (typeify (subst sub\<^sub>3 (subst sub\<^sub>2 (Var v))))" 
      by simp


  from E2 have "map_option (tsubsts sub\<^sub>3 \<circ> tsubsts sub\<^sub>2 \<circ> typeify) \<circ> \<Gamma> \<turnstile>\<^sub>n tsubstt sub\<^sub>3 (tsubstt sub\<^sub>2 (solidify e\<^sub>2')) : xt\<^sub>1" 
    by simp
  with NApp E2 have "map_option (typeify \<circ> subst sub\<^sub>3 \<circ> subst sub\<^sub>2) \<circ> \<Gamma> \<turnstile>\<^sub>n 
    tsubstt sub\<^sub>3 (tsubstt sub\<^sub>2 (solidify e\<^sub>2')) : xt\<^sub>1" by simp
  with X E1 E2 have "map_option (typeify \<circ> subst (combine_subst sub\<^sub>3 sub\<^sub>2)) \<circ> \<Gamma> \<turnstile>\<^sub>n 
    solidify (hsubst (combine_subst sub\<^sub>3 sub\<^sub>2) (HApp e\<^sub>1' e\<^sub>2')) :
      typeify (subst (combine_subst sub\<^sub>3 sub\<^sub>2) (Var v))" by (simp add: comp_assoc)
  thus ?case by blast
qed simp_all

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> Map.empty \<turnstile>\<^sub>n e\<^sub>t : t"
proof -
  assume "typecheck e = Some (e\<^sub>t, t)"
  then obtain e' tt vs sub where T: "typecheck' Map.empty {} e = Some (e', tt, vs, sub) \<and>
    e\<^sub>t = tsubstt sub (solidify e') \<and> t = tsubsts sub (typeify tt)" by (auto split: option.splits)
  moreover hence "map_option (typeify \<circ> subst sub) \<circ> Map.empty \<turnstile>\<^sub>n solidify (hsubst sub e') : 
    typeify (subst sub tt)" by (metis typecheck_succeeds valid_empty)
  moreover from T have "valid_ty_uexpr tt" and "valid_ty_hexpr e'" by auto
  ultimately show "Map.empty \<turnstile>\<^sub>n e\<^sub>t : t" by simp
qed

lemma [simp]: "typecheck' \<Gamma> vs e = Some (e', t, vs', sub) \<Longrightarrow> e = erase (solidify e')"
  by (induction rule: typecheck_Some) auto

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> e = erase e\<^sub>t"
  by (auto split: option.splits)

lemma [dest]: "erase e\<^sub>t = NVar x \<Longrightarrow> e\<^sub>t = TVar x"
  by (induction e\<^sub>t) simp_all

lemma [dest]: "erase e\<^sub>t = NLam x e \<Longrightarrow> \<exists>t e\<^sub>t'. e\<^sub>t = TLam x t e\<^sub>t' \<and> e = erase e\<^sub>t'"
  by (induction e\<^sub>t) simp_all

lemma [dest]: "erase e\<^sub>t = NApp e\<^sub>1 e\<^sub>2 \<Longrightarrow> \<exists>e\<^sub>1' e\<^sub>2'. e\<^sub>t = TApp e\<^sub>1' e\<^sub>2' \<and> e\<^sub>1 = erase e\<^sub>1'\<and> e\<^sub>2 = erase e\<^sub>2'"
  by (induction e\<^sub>t) simp_all

lemma typecheck_fails' [simp]: "typecheck' \<Gamma> vs e = None \<Longrightarrow> map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>t : t \<Longrightarrow> 
  erase e\<^sub>t = e \<Longrightarrow> False"
proof (induction arbitrary: e\<^sub>t t rule: typecheck_None)
  case (NLam \<Gamma> vs x e v)
  then obtain t\<^sub>1 e\<^sub>t' where E: "e\<^sub>t = TLam x t\<^sub>1 e\<^sub>t' \<and> e = erase e\<^sub>t'" by auto
  with NLam obtain t\<^sub>2 where T: "((map_option typeify \<circ> \<Gamma>)(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e\<^sub>t' : t\<^sub>2) \<and> t = Arrow t\<^sub>1 t\<^sub>2" 
    by blast




  from T have "(map_option typeify \<circ> \<Gamma>(x \<mapsto> Var v) \<turnstile>\<^sub>n xe\<^sub>t' : xt) \<and> erase xe\<^sub>t' = e" by simp
  with NLam E show ?case by blast
next
  case (NApp2 \<Gamma> vs e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' sub\<^sub>1)
  thus ?case by simp
next
  case (NApp3 \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' sub\<^sub>1 e\<^sub>2' t\<^sub>2 sub\<^sub>2)
  thus ?case by simp
qed fastforce+

lemma typecheck_fails [simp]: "typecheck e = None \<Longrightarrow> \<nexists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> e = erase e\<^sub>t"
proof 
  assume "typecheck e = None"
  hence X: "typecheck' Map.empty {} e = None" by (auto split: option.splits)
  assume "\<exists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> e = erase e\<^sub>t"
  then obtain e\<^sub>t t where "(map_option typeify \<circ> Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> e = erase e\<^sub>t" by fastforce
  with X show "False" by (metis typecheck_fails')
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

lemma correctness' [simp]: "e \<Down> v \<Longrightarrow> typecheck' \<Gamma> vs e = Some (e\<^sub>t, t1, vs1, sub1) \<Longrightarrow> 
  typecheck' \<Gamma> vs v = Some (v\<^sub>t, t2, vs2, sub2) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> 
    tsubsts sub1 (typeify t1) = tsubsts sub2 (typeify t2) \<and> 
      tsubstt sub1 (solidify e\<^sub>t) \<Down>\<^sub>t tsubstt sub2 (solidify v\<^sub>t)"
proof (induction e v arbitrary: vs e\<^sub>t t1 vs1 sub1 v\<^sub>t t2 vs2 sub2 rule: evaln.induct)
  case (evn_app e\<^sub>1 x e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  let ?v = "fresh vs"
  from evn_app obtain e\<^sub>1'' t\<^sub>1 vs' sub\<^sub>1 e\<^sub>2' t\<^sub>2 sub\<^sub>2 sub\<^sub>3 where E: "e\<^sub>t = HApp e\<^sub>1'' e\<^sub>2' \<and> t1 = Var ?v \<and> 
    typecheck' \<Gamma> (insert ?v vs) e\<^sub>1 = Some (e\<^sub>1'', t\<^sub>1, vs', sub\<^sub>1) \<and> sub1 = combine_subst sub\<^sub>3 sub\<^sub>2 \<and> 
      typecheck' (env_subst sub\<^sub>1 \<Gamma>) vs' e\<^sub>2 = Some (e\<^sub>2', t\<^sub>2, vs1, sub\<^sub>2) \<and> 
        unify t\<^sub>1 (Ctor ''Arrow'' [t\<^sub>2, Var ?v]) = Some sub\<^sub>3" 
    by (auto simp add: Let_def split: option.splits)


  from evn_app have "e\<^sub>1 \<Down> NLam x e\<^sub>1'" by simp
  from evn_app have "e\<^sub>2 \<Down> v\<^sub>2" by simp
  from evn_app have "substn x v\<^sub>2 e\<^sub>1' \<Down> v" by simp
  from evn_app E have "typecheck' \<Gamma> (insert ?v vs) (NLam x e\<^sub>1') = Some (xv\<^sub>t, xt20, xvs20, xsub2) \<Longrightarrow>
    tsubsts sub\<^sub>1 (typeify t\<^sub>1) = tsubsts xsub2 (typeify xt20) \<and> tsubstt sub\<^sub>1 (solidify e\<^sub>1'') \<Down>\<^sub>t tsubstt xsub2 (solidify xv\<^sub>t)" by simp
  from evn_app have "typecheck' \<Gamma> xvs e\<^sub>2 = Some (xe\<^sub>t, xt10, xvs10, xsub1) \<Longrightarrow>
    typecheck' \<Gamma> xvs v\<^sub>2 = Some (xv\<^sub>t, xt20, xvs20, xsub2) \<Longrightarrow>
    tsubsts xsub1 (typeify xt10) = tsubsts xsub2 (typeify xt20) \<and> tsubstt xsub1 (solidify xe\<^sub>t) \<Down>\<^sub>t tsubstt xsub2 (solidify xv\<^sub>t)" by simp
  from evn_app have "typecheck' \<Gamma> xvs (substn x v\<^sub>2 e\<^sub>1') = Some (xe\<^sub>t, xt10, xvs10, xsub1) \<Longrightarrow>
    typecheck' \<Gamma> xvs v = Some (xv\<^sub>t, xt20, xvs20, xsub2) \<Longrightarrow>
    tsubsts xsub1 (typeify xt10) = tsubsts xsub2 (typeify xt20) \<and> tsubstt xsub1 (solidify xe\<^sub>t) \<Down>\<^sub>t tsubstt xsub2 (solidify xv\<^sub>t)" by simp
  from evn_app have "typecheck' \<Gamma> vs v = Some (v\<^sub>t, t2, vs2, sub2)" by simp
  from evn_app have "valid_ty_subst \<Gamma>" by simp


  have "tsubsts sub1 (typeify t1) = tsubsts sub2 (typeify t2) \<and> tsubstt sub1 (solidify e\<^sub>t) \<Down>\<^sub>t tsubstt sub2 (solidify v\<^sub>t)" by simp
  thus ?case by simp
qed (auto simp add: Let_def split: option.splits prod.splits)

theorem correctness: "e \<Down> v \<Longrightarrow> typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> typecheck v = Some (v\<^sub>t, t) \<Longrightarrow> 
    e\<^sub>t \<Down>\<^sub>t v\<^sub>t"
  by (auto split: option.splits prod.splits)

end