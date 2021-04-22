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

primrec typecheck' :: "subst \<Rightarrow> var set \<Rightarrow> nexpr \<rightharpoonup> 
    hexpr \<times> uexpr \<times> var set \<times> (uexpr \<times> uexpr) list" where
  "typecheck' \<Gamma> vs (NVar x) = (case \<Gamma> x of 
      Some t \<Rightarrow> Some (HVar x, t, vs, []) 
    | None \<Rightarrow> None)"
| "typecheck' \<Gamma> vs (NConst k) = Some (HConst k, Ctor ''Base'' [], vs, [])"
| "typecheck' \<Gamma> vs (NLam x e) = (
    let v = fresh vs
    in case typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e of
        Some (e', t, vs', uni) \<Rightarrow> Some (HLam x (Var v) e', Ctor ''Arrow'' [Var v, t], vs', uni)
      | None \<Rightarrow> None)"
| "typecheck' \<Gamma> vs (NApp e\<^sub>1 e\<^sub>2) = (
    let v = fresh vs
    in case typecheck' \<Gamma> (insert v vs) e\<^sub>1 of 
        Some (e\<^sub>1', t\<^sub>1, vs', uni\<^sub>1) \<Rightarrow> (case typecheck' \<Gamma> vs' e\<^sub>2 of
            Some (e\<^sub>2', t\<^sub>2, vs'', uni\<^sub>2) \<Rightarrow> 
              Some (HApp e\<^sub>1' e\<^sub>2', Var v, vs'', (t\<^sub>1, Ctor ''arrow'' [t\<^sub>2, Var v]) # uni\<^sub>1 @ uni\<^sub>2)
          | None \<Rightarrow> None)
      | None \<Rightarrow> None)"

fun typeify :: "uexpr \<Rightarrow> ty" where
  "typeify (Var v) = TyVar v"
| "typeify (Ctor k []) = (if k = ''Base'' then Base else undefined)"
| "typeify (Ctor k [t\<^sub>1, t\<^sub>2]) = 
    (if k = ''Arrow'' then Arrow (typeify t\<^sub>1) (typeify t\<^sub>2) else undefined)"
| "typeify (Ctor k ts) = undefined"

fun valid_ty_uexpr :: "uexpr \<Rightarrow> bool" where
  "valid_ty_uexpr (Var v) = True"
| "valid_ty_uexpr (Ctor k []) = (k = ''Base'')"
| "valid_ty_uexpr (Ctor k [t\<^sub>1, t\<^sub>2]) = (k = ''Arrow'' \<and> valid_ty_uexpr t\<^sub>1 \<and> valid_ty_uexpr t\<^sub>2)"
| "valid_ty_uexpr (Ctor k ts) = False"

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

fun typecheck :: "nexpr \<rightharpoonup> texpr \<times> ty" where
  "typecheck e = (case typecheck' Map.empty {} e of
      Some (e', t, vs, uni) \<Rightarrow> (case unify' uni of 
          Some sub \<Rightarrow> Some (solidify (hsubst sub e'), typeify (subst sub t))
        | None \<Rightarrow> None)
    | None \<Rightarrow> None)"

fun tsubsts :: "subst \<Rightarrow> ty \<Rightarrow> ty" where
  "tsubsts sub (TyVar y) = (case sub y of Some t \<Rightarrow> typeify t | None \<Rightarrow> TyVar y)"
| "tsubsts sub Base = Base"
| "tsubsts sub (Arrow t\<^sub>1 t\<^sub>2) = Arrow (tsubsts sub t\<^sub>1) (tsubsts sub t\<^sub>2)"

primrec tsubstt :: "subst \<Rightarrow> texpr \<Rightarrow> texpr" where
  "tsubstt sub (TVar x) = TVar x"
| "tsubstt sub (TConst k) = TConst k"
| "tsubstt sub (TLam x t e) = TLam x (tsubsts sub t) (tsubstt sub e)"
| "tsubstt sub (TApp e\<^sub>1 e\<^sub>2) = TApp (tsubstt sub e\<^sub>1) (tsubstt sub e\<^sub>2)"

lemma [simp]: "valid_ty_uexpr t \<Longrightarrow> typeify (subst sub t) = tsubsts sub (typeify t)"
  by (induction t rule: typeify.induct) (simp_all split: option.splits)

lemma [simp]: "valid_ty_subst Map.empty"
  by (simp add: valid_ty_subst_def)

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> 
    map_option (typeify \<circ> subst sub) (\<Gamma> x) = map_option (tsubsts sub \<circ> typeify) (\<Gamma> x)"
  by (cases "\<Gamma> x") (auto simp add: valid_ty_subst_def ran_def)

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> 
    map_option (typeify \<circ> subst sub) \<circ> \<Gamma> = map_option (tsubsts sub \<circ> typeify) \<circ> \<Gamma>"
  by auto

lemma [simp]: "valid_ty_hexpr e \<Longrightarrow> solidify (hsubst sub e) = tsubstt sub (solidify e)"
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
  by (induction t rule: valid_ty_uexpr.induct) 
     (auto simp add: valid_ty_subst_def ran_def split: option.splits)

lemma [elim]: "valid_ty_subst \<Gamma> \<Longrightarrow> \<Gamma> x = Some t \<Longrightarrow> valid_ty_uexpr t"
  by (auto simp add: valid_ty_subst_def ran_def)

lemma [elim]: "valid_ty_uexpr (Ctor k es) \<Longrightarrow> list_all valid_ty_uexpr es"
  by (induction "Ctor k es" rule: valid_ty_uexpr.induct) auto

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

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> typecheck' \<Gamma> vs e = Some (e', t, vs', uni) \<Longrightarrow> 
  valid_ty_hexpr e' \<and> valid_ty_uexpr t"
proof (induction e arbitrary: \<Gamma> vs e' t vs' uni)
  case (NLam x e)
  let ?v = "fresh vs"
  from NLam obtain ee' tt where T: "e' = HLam x (Var ?v) ee' \<and> 
    t = Ctor ''Arrow'' [Var ?v, tt] \<and> 
      typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e = Some (ee', tt, vs', uni)" 
    by (auto simp add: Let_def split: option.splits)
  from NLam have "valid_ty_subst (\<Gamma>(x \<mapsto> Var ?v))" by simp
  with NLam T have "valid_ty_uexpr tt \<and> valid_ty_hexpr ee'" by blast
  with NLam have "valid_ty_uexpr (Ctor ''Arrow'' [Var ?v, tt]) \<and> 
    valid_ty_hexpr (HLam x (Var ?v) ee')" by simp
  with T show ?case by blast
qed (auto simp add: Let_def split: option.splits)

lemma [elim]: "valid_ty_subst \<Gamma> \<Longrightarrow> typecheck' \<Gamma> vs e = Some (e', t, vs', uni) \<Longrightarrow> valid_ty_uexpr t"
  by simp

lemma [elim]: "valid_ty_subst \<Gamma> \<Longrightarrow> typecheck' \<Gamma> vs e = Some (e', t, vs', uni) \<Longrightarrow> 
    valid_ty_hexpr e'"
  by simp

lemma typecheck_succeeds [simp]: "typecheck' \<Gamma> vs e = Some (e', t, vs', uni) \<Longrightarrow> 
  unify' uni = Some sub \<Longrightarrow> 
    map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub e') : typeify (subst sub t)"
proof (induction e arbitrary: \<Gamma> vs e' t vs' uni sub)
  case (NVar x)
  hence T: "\<Gamma> x = Some t \<and> e' = HVar x \<and> vs' = vs \<and> uni = []" by (simp split: option.splits)
  moreover with NVar have "sub = Map.empty" by simp
  moreover from T have "map_option (typeify \<circ> subst Map.empty) \<circ> \<Gamma> \<turnstile>\<^sub>n 
    solidify (hsubst Map.empty (HVar x)) : typeify (subst Map.empty t)" by simp
  ultimately show ?case by blast
next
  case (NConst k)
  hence "e' = HConst k \<and> t = Ctor ''Base'' [] \<and> vs' = vs \<and> uni = []" by simp
  hence "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub e') : typeify (subst sub t)" 
    by simp
  thus ?case by blast
next
  case (NLam x e)
  let ?v = "fresh vs"
  from NLam obtain ee' tt where T: "e' = HLam x (Var ?v) ee' \<and> t = Ctor ''Arrow'' [Var ?v, tt] \<and>
    typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e = Some (ee', tt, vs', uni)" 
      by (auto simp add: Let_def split: option.splits)
  thus ?case 
  proof (cases "sub ?v")
    case None
    from NLam T have "map_option (typeify \<circ> subst sub) \<circ> (\<Gamma>(x \<mapsto> Var ?v)) \<turnstile>\<^sub>n 
      solidify (hsubst sub ee') : typeify (subst sub tt)" by blast
    with None have "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n 
      solidify (hsubst sub (HLam x (Var ?v) ee')) : 
        typeify (subst sub (Ctor ''Arrow'' [Var ?v, tt]))" by simp
    with T show ?thesis by blast
  next
    case (Some t')
    from NLam T have "map_option (typeify \<circ> subst sub) \<circ> (\<Gamma>(x \<mapsto> Var ?v)) \<turnstile>\<^sub>n 
      solidify (hsubst sub ee') : typeify (subst sub tt)" by blast
    with Some have "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n 
      solidify (hsubst sub (HLam x (Var ?v) ee')) : 
        typeify (subst sub (Ctor ''Arrow'' [Var ?v, tt]))" by simp
    with T show ?thesis by blast
  qed
next
  case (NApp e\<^sub>1 e\<^sub>2)
  let ?v = "fresh vs"
  from NApp obtain e\<^sub>1' t\<^sub>1 vs'' uni\<^sub>1 e\<^sub>2' t\<^sub>2 uni\<^sub>2 where E: "e' = HApp e\<^sub>1' e\<^sub>2' \<and> t = Var ?v \<and>
    typecheck' \<Gamma> (insert ?v vs) e\<^sub>1 = Some (e\<^sub>1', t\<^sub>1, vs'', uni\<^sub>1) \<and>
      typecheck' \<Gamma> vs'' e\<^sub>2 = Some (e\<^sub>2', t\<^sub>2, vs', uni\<^sub>2) \<and> 
        uni = (t\<^sub>1, Ctor ''arrow'' [t\<^sub>2, Var ?v]) # uni\<^sub>1 @ uni\<^sub>2" 
    by (auto simp add: Let_def split: option.splits)


  from NApp E have "unify' uni\<^sub>1 = Some sub\<^sub>1 \<Longrightarrow> 
    map_option (typeify \<circ> subst sub\<^sub>1) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub\<^sub>1 e\<^sub>1') : typeify (subst sub\<^sub>1 t\<^sub>1)" by blast
  from NApp E have "unify' uni\<^sub>2 = Some sub\<^sub>2 \<Longrightarrow> 
    map_option (typeify \<circ> subst sub\<^sub>2) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub\<^sub>2 e\<^sub>2') : typeify (subst sub\<^sub>2 t\<^sub>2)" by blast

  from NApp have "unify' uni = Some sub" by simp



  have X: "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub e\<^sub>1') : 
    Arrow (typeify (subst sub t\<^sub>1)) (typeify (subst sub t))" by simp




  have "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub e\<^sub>2') : typeify (subst sub t\<^sub>1)" 
    by simp
  with X have "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub (HApp e\<^sub>1' e\<^sub>2')) : 
    typeify (subst sub t)" by simp
  with E show ?case by blast
qed

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> Map.empty \<turnstile>\<^sub>n e\<^sub>t : t"
proof -
  assume "typecheck e = Some (e\<^sub>t, t)"
  then obtain e' tt vs uni sub where "typecheck' Map.empty {} e = Some (e', tt, vs, uni) \<and>
    unify' uni = Some sub \<and> e\<^sub>t = solidify (hsubst sub e') \<and> t = typeify (subst sub tt)" 
      by (auto split: option.splits)
  moreover hence "map_option (typeify \<circ> subst sub) \<circ> Map.empty \<turnstile>\<^sub>n solidify (hsubst sub e') : 
    typeify (subst sub tt)" by (metis typecheck_succeeds)
  ultimately show "Map.empty \<turnstile>\<^sub>n e\<^sub>t : t" by simp
qed

lemma erase_solidify [simp]: "typecheck' \<Gamma> vs e = Some (e', t, vs', uni) \<Longrightarrow> 
    e = erase (solidify e')"
  by (induction e arbitrary: \<Gamma> vs e' t vs' uni) 
     (auto simp add: Let_def split: option.splits)

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> e = erase e\<^sub>t"
proof -
  assume "typecheck e = Some (e\<^sub>t, t)"
  then obtain e' tt vs uni sub where T: "typecheck' Map.empty {} e = Some (e', tt, vs, uni) \<and> 
    unify' uni = Some sub \<and> e\<^sub>t = solidify (hsubst sub e') \<and> t = typeify (subst sub tt)" 
      by (auto split: option.splits)
  hence X: "e = erase (solidify e')" by (metis erase_solidify)
  have "valid_ty_subst Map.empty" by simp
  with T have "valid_ty_hexpr e'" by fastforce
  with T X show ?thesis by simp
qed

lemma [dest]: "erase e\<^sub>t = NVar x \<Longrightarrow> e\<^sub>t = TVar x"
  by (induction e\<^sub>t) simp_all

lemma [dest]: "erase e\<^sub>t = NLam x e \<Longrightarrow> \<exists>t e\<^sub>t'. e\<^sub>t = TLam x t e\<^sub>t' \<and> e = erase e\<^sub>t'"
  by (induction e\<^sub>t) simp_all

lemma typecheck_fails' [simp]: "typecheck' \<Gamma> vs e = None \<Longrightarrow> map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>t : t \<Longrightarrow> 
  erase e\<^sub>t = e \<Longrightarrow> False"
proof (induction e arbitrary: \<Gamma> vs e\<^sub>t t)
  case (NVar x)
  hence "\<Gamma> x = None" by (simp split: option.splits)
  moreover from NVar have "(map_option typeify \<circ> \<Gamma>) x = Some t" by blast
  ultimately show ?case by simp
next
  case (NLam x e)
  let ?v = "fresh vs"
  from NLam have T: "typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e = None" 
    by (auto simp add: Let_def split: option.splits)
  from NLam obtain t\<^sub>1 e\<^sub>t' where E: "e\<^sub>t = TLam x t\<^sub>1 e\<^sub>t' \<and> e = erase e\<^sub>t'" by auto
  with NLam obtain t\<^sub>2 where "t = Arrow t\<^sub>1 t\<^sub>2 \<and> (map_option typeify \<circ> \<Gamma>)(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e\<^sub>t' : t\<^sub>2" by blast
  hence "map_option typeify \<circ> (\<Gamma>(x \<mapsto> Var ?v)) \<turnstile>\<^sub>n e\<^sub>t' : t\<^sub>2" by simp
  with NLam T E show ?case by blast
next
  case (NApp e1 e2)
  thus ?case by simp
qed simp_all

lemma typecheck_fails [simp]: "typecheck e = None \<Longrightarrow> \<nexists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> e = erase e\<^sub>t"
proof (rule, cases "typecheck' Map.empty {} e")
  case None
  assume "\<exists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> e = erase e\<^sub>t"
  then obtain e\<^sub>t tt where "(map_option typeify \<circ> Map.empty \<turnstile>\<^sub>n e\<^sub>t : tt) \<and> e = erase e\<^sub>t" by fastforce
  with None show "False" by (metis typecheck_fails')
next
  case (Some out)
  moreover assume "typecheck e = None"
  ultimately obtain e' t vs uni where X: "typecheck' Map.empty {} e = Some (e', t, vs, uni) \<and> 
    unify' uni = None" by (auto split: option.splits prod.splits)


  assume "\<exists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> e = erase e\<^sub>t"
  then obtain e\<^sub>t tt where "(map_option typeify \<circ> Map.empty \<turnstile>\<^sub>n e\<^sub>t : tt) \<and> e = erase e\<^sub>t" by fastforce


  with Some X show "False" by simp
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

lemma correctness' [simp]: "e \<Down> v \<Longrightarrow> typecheck' \<Gamma> vs e = Some (e\<^sub>t, t1, vs1, uni1) \<Longrightarrow> 
  typecheck' \<Gamma> vs v = Some (v\<^sub>t, t2, vs2, uni2) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> unify' uni1 = Some sub1 \<Longrightarrow> 
    unify' uni2 = Some sub2 \<Longrightarrow> typeify (subst sub1 t1) = typeify (subst sub2 t2) \<Longrightarrow> 
      solidify (hsubst sub1 e\<^sub>t) \<Down>\<^sub>t solidify (hsubst sub2 v\<^sub>t)"
proof (induction e v arbitrary: vs e\<^sub>t t1 vs1 uni1 v\<^sub>t t2 vs2 uni2 sub1 sub2 rule: evaln.induct)
  case (evn_app e\<^sub>1 x e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  let ?v = "fresh vs"
  from evn_app obtain e\<^sub>t\<^sub>1 t\<^sub>1 vs'' uni\<^sub>1 e\<^sub>t\<^sub>2 t\<^sub>2 uni\<^sub>2 where E: "e\<^sub>t = HApp e\<^sub>t\<^sub>1 e\<^sub>t\<^sub>2 \<and> t1 = Var ?v \<and>
    typecheck' \<Gamma> (insert ?v vs) e\<^sub>1 = Some (e\<^sub>t\<^sub>1, t\<^sub>1, vs'', uni\<^sub>1) \<and>
      typecheck' \<Gamma> vs'' e\<^sub>2 = Some (e\<^sub>t\<^sub>2, t\<^sub>2, vs1, uni\<^sub>2) \<and> 
        uni1 = (t\<^sub>1, Ctor ''arrow'' [t\<^sub>2, Var ?v]) # uni\<^sub>1 @ uni\<^sub>2" 
    by (auto simp add: Let_def split: option.splits)

  from evn_app have "e\<^sub>1 \<Down> NLam x e\<^sub>1'" by simp
  from evn_app have "e\<^sub>2 \<Down> v\<^sub>2" by simp
  from evn_app have "substn x v\<^sub>2 e\<^sub>1' \<Down> v" by simp
  from evn_app E have "typecheck' \<Gamma> (insert ?v vs) (NLam x e\<^sub>1') = Some (xv\<^sub>t, xt20, xvs20, xuni20) \<Longrightarrow>
    unify' uni\<^sub>1 = Some xsub1 \<Longrightarrow>
    unify' xuni20 = Some xsub2 \<Longrightarrow>
    typeify (subst xsub1 t\<^sub>1) = typeify (subst xsub2 xt20) \<Longrightarrow> solidify (hsubst xsub1 e\<^sub>t\<^sub>1) \<Down>\<^sub>t solidify (hsubst xsub2 xv\<^sub>t)" by blast
  from evn_app have "typecheck' \<Gamma> xvs e\<^sub>2 = Some (xe\<^sub>t, xt10, xvs10, xuni10) \<Longrightarrow>
    typecheck' \<Gamma> xvs v\<^sub>2 = Some (xv\<^sub>t, xt20, xvs20, xuni20) \<Longrightarrow>
    unify' xuni10 = Some xsub1 \<Longrightarrow>
    unify' xuni20 = Some xsub2 \<Longrightarrow>
    typeify (subst xsub1 xt10) = typeify (subst xsub2 xt20) \<Longrightarrow> solidify (hsubst xsub1 xe\<^sub>t) \<Down>\<^sub>t solidify (hsubst xsub2 xv\<^sub>t)" by simp
  from evn_app have "typecheck' \<Gamma> xvs (substn x v\<^sub>2 e\<^sub>1') = Some (xe\<^sub>t, xt10, xvs10, xuni10) \<Longrightarrow>
    typecheck' \<Gamma> xvs v = Some (xv\<^sub>t, xt20, xvs20, xuni20) \<Longrightarrow>
    unify' xuni10 = Some xsub1 \<Longrightarrow>
    unify' xuni20 = Some xsub2 \<Longrightarrow>
    typeify (subst xsub1 xt10) = typeify (subst xsub2 xt20) \<Longrightarrow> solidify (hsubst xsub1 xe\<^sub>t) \<Down>\<^sub>t solidify (hsubst xsub2 xv\<^sub>t)" by simp
  from evn_app have "typecheck' \<Gamma> vs v = Some (v\<^sub>t, t2, vs2, uni2)" by simp
  from evn_app have "valid_ty_subst \<Gamma>" by simp
  from evn_app have "unify' uni1 = Some sub1" by simp
  from evn_app have "unify' uni2 = Some sub2" by simp
  from evn_app have "typeify (subst sub1 t1) = typeify (subst sub2 t2)" by simp


  have "solidify (hsubst sub1 e\<^sub>t) \<Down>\<^sub>t solidify (hsubst sub2 v\<^sub>t)" by simp
  thus ?case by simp
qed (auto simp add: Let_def split: option.splits prod.splits)

theorem correctness: "e \<Down> v \<Longrightarrow> typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> typecheck v = Some (v\<^sub>t, t) \<Longrightarrow> 
    e\<^sub>t \<Down>\<^sub>t v\<^sub>t"
  by (auto split: option.splits prod.splits)

end