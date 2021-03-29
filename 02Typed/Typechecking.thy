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
    hexpr \<times> uexpr \<times> var set \<times> (var \<rightharpoonup> uexpr)" where
  "typecheck' \<Gamma> vs (NVar x) = (case \<Gamma> x of 
      Some t \<Rightarrow> Some (HVar x, t, vs, \<Gamma>) 
    | None \<Rightarrow> None)"
| "typecheck' \<Gamma> vs (NConst k) = Some (HConst k, Ctor ''Base'' [], vs, \<Gamma>)"
| "typecheck' \<Gamma> vs (NLam x e) = (
    let v = fresh vs
    in case typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e of
        Some (e', t, vs', \<Gamma>') \<Rightarrow> (case \<Gamma>' x of 
          Some t' \<Rightarrow> Some (HLam x t' e', Ctor ''Arrow'' [t', t], vs', (\<Gamma>'(x := \<Gamma> x)))
        | None \<Rightarrow> None)
      | None \<Rightarrow> None)"
| "typecheck' \<Gamma> vs (NApp e\<^sub>1 e\<^sub>2) = (case typecheck' \<Gamma> vs e\<^sub>1 of
      Some (e\<^sub>1', Ctor k [t\<^sub>1, t\<^sub>2], vs', \<Gamma>') \<Rightarrow> (
        if k = ''Arrow'' then case typecheck' \<Gamma>' vs' e\<^sub>2 of
            Some (e\<^sub>2', t\<^sub>3, vs'', \<Gamma>'') \<Rightarrow> (case unify t\<^sub>1 t\<^sub>2 of     
              Some sub \<Rightarrow> Some (HApp (hsubst sub e\<^sub>1') (hsubst sub e\<^sub>2'), subst sub t\<^sub>2, vs'', 
                                map_option (subst sub) \<circ> \<Gamma>'')
            | None \<Rightarrow> None)
          | None \<Rightarrow> None
        else None)
    | _ \<Rightarrow> None)"

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
      Some (e', t, vs, \<Gamma>) \<Rightarrow> Some (solidify e', typeify t)
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

lemma [simp]: "valid_ty_uexpr t \<Longrightarrow> valid_ty_subst sub \<Longrightarrow> valid_ty_uexpr (subst sub t)"
  by (induction t rule: valid_ty_uexpr.induct) 
     (auto simp add: valid_ty_subst_def ran_def split: option.splits)

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_subst sub \<Longrightarrow> 
    valid_ty_subst (map_option (subst sub) \<circ> \<Gamma>)"
  by (auto simp add: valid_ty_subst_def ran_def)

lemma [elim]: "valid_ty_subst \<Gamma> \<Longrightarrow> \<Gamma> x = Some t \<Longrightarrow> valid_ty_uexpr t"
  by (auto simp add: valid_ty_subst_def ran_def)

lemma [elim]: "valid_ty_uexpr t\<^sub>1 \<Longrightarrow> valid_ty_uexpr t\<^sub>2 \<Longrightarrow> unify t\<^sub>1 t\<^sub>2 = Some sub \<Longrightarrow> 
    valid_ty_subst sub"                                  
  by (auto simp add: valid_ty_subst_def)

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

lemma [simp]: "typecheck' \<Gamma> vs e = Some (e', t, vs', \<Gamma>') \<Longrightarrow> dom \<Gamma>' = dom \<Gamma>"
proof (induction e arbitrary: \<Gamma> vs e' t vs' \<Gamma>')
  case (NLam x e)
  let ?v = "fresh vs"
  from NLam obtain ee' tt g\<Gamma>' t' where T: "g\<Gamma>' x = Some t' \<and> e' = HLam x t' ee' \<and> 
    t = Ctor ''Arrow'' [t', tt] \<and> \<Gamma>' = (g\<Gamma>'(x := \<Gamma> x)) \<and>
      typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e = Some (ee', tt, vs', g\<Gamma>')" 
        by (auto simp add: Let_def split: option.splits)
  with NLam have "dom g\<Gamma>' = dom (\<Gamma>(x \<mapsto> Var ?v))" by blast
  hence "dom (g\<Gamma>'(x := \<Gamma> x)) = dom \<Gamma>" by auto
  with T show ?case by blast
next
  case (NApp e1 e2)
  then obtain e\<^sub>1' k t\<^sub>1 t\<^sub>2 vvs' g\<Gamma>' e\<^sub>2' t\<^sub>3 \<Gamma>'' sub where T: "k = ''Arrow'' \<and>
    typecheck' \<Gamma> vs e1 = Some (e\<^sub>1', Ctor k [t\<^sub>1, t\<^sub>2], vvs', g\<Gamma>') \<and> 
      typecheck' g\<Gamma>' vvs' e2 = Some (e\<^sub>2', t\<^sub>3, vs', \<Gamma>'') \<and> unify t\<^sub>1 t\<^sub>2 = Some sub \<and> 
        e' = HApp (hsubst sub e\<^sub>1') (hsubst sub e\<^sub>2') \<and> t = subst sub t\<^sub>2 \<and> 
          \<Gamma>' = map_option (subst sub) \<circ> \<Gamma>''" 
    by (auto split: option.splits uexpr.splits list.splits if_splits)
  with NApp have "dom g\<Gamma>' = dom \<Gamma>" by blast
  moreover from NApp T have "dom \<Gamma>'' = dom g\<Gamma>'" by blast
  ultimately have "dom (map_option (subst sub) \<circ> \<Gamma>'') = dom \<Gamma>" by simp
  with T show ?case by blast
qed (simp_all split: option.splits)

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> typecheck' \<Gamma> vs e = Some (e', t, vs', \<Gamma>') \<Longrightarrow> 
  valid_ty_subst \<Gamma>' \<and> valid_ty_uexpr t \<and> valid_ty_hexpr e'"
proof (induction e arbitrary: \<Gamma> vs e' t vs' \<Gamma>')
  case (NLam x e)
  let ?v = "fresh vs"
  from NLam obtain ee' tt g\<Gamma>' t' where T: "g\<Gamma>' x = Some t' \<and> 
    typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e = Some (ee', tt, vs', g\<Gamma>') \<and> 
      e' = HLam x t' ee' \<and> t = Ctor ''Arrow'' [t', tt] \<and> \<Gamma>' = (g\<Gamma>'(x := \<Gamma> x))" 
    by (auto simp add: Let_def split: option.splits prod.splits)
  from NLam have "valid_ty_subst (\<Gamma>(x \<mapsto> Var ?v))" by simp
  with NLam T have X: "valid_ty_subst g\<Gamma>' \<and> valid_ty_uexpr tt \<and> valid_ty_hexpr ee'" by blast
  with T have "valid_ty_uexpr t'" by auto
  with NLam X have "valid_ty_subst (g\<Gamma>'(x := \<Gamma> x)) \<and> valid_ty_uexpr (Ctor ''Arrow'' [t', tt]) \<and> 
    valid_ty_hexpr (HLam x t' ee')" by simp
  with T show ?case by blast
next
  case (NApp e1 e2)
  from NApp(4) obtain e\<^sub>1' t\<^sub>1 t\<^sub>2 vvs' g\<Gamma>' e\<^sub>2' t\<^sub>3 g\<Gamma>'' sub where T: "unify t\<^sub>1 t\<^sub>2 = Some sub \<and> 
    t = subst sub t\<^sub>2 \<and> e' = HApp (hsubst sub e\<^sub>1') (hsubst sub e\<^sub>2') \<and> 
      \<Gamma>' = map_option (subst sub) \<circ> g\<Gamma>'' \<and> 
        typecheck' \<Gamma> vs e1 = Some (e\<^sub>1', Ctor ''Arrow'' [t\<^sub>1, t\<^sub>2], vvs', g\<Gamma>') \<and>
          typecheck' g\<Gamma>' vvs' e2 = Some (e\<^sub>2', t\<^sub>3, vs', g\<Gamma>'')" 
    by (auto split: option.splits prod.splits uexpr.splits list.splits if_splits)
  moreover with NApp have "valid_ty_subst g\<Gamma>' \<and> valid_ty_uexpr (Ctor ''Arrow'' [t\<^sub>1, t\<^sub>2]) \<and> 
    valid_ty_hexpr e\<^sub>1'" by blast
  moreover with NApp T have "valid_ty_subst g\<Gamma>'' \<and> valid_ty_uexpr t\<^sub>3 \<and> 
    valid_ty_hexpr e\<^sub>2'" by blast
  ultimately have "valid_ty_subst g\<Gamma>'' \<and> valid_ty_subst sub \<and> valid_ty_uexpr t\<^sub>2 \<and> 
    valid_ty_hexpr e\<^sub>1' \<and> valid_ty_hexpr e\<^sub>2'" by auto
  hence "valid_ty_subst (map_option (subst sub) \<circ> g\<Gamma>'') \<and> valid_ty_uexpr (subst sub t\<^sub>2) \<and> 
    valid_ty_hexpr (HApp (hsubst sub e\<^sub>1') (hsubst sub e\<^sub>2'))" by simp
  with T show ?case by blast
qed (auto split: option.splits)

lemma [elim]: "valid_ty_subst \<Gamma> \<Longrightarrow> typecheck' \<Gamma> vs e = Some (e', t, vs', \<Gamma>') \<Longrightarrow> valid_ty_uexpr t"
  by simp

lemma [simp]: "typecheck' \<Gamma> vs e = Some (e', t, vs', \<Gamma>') \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> 
  map_option typeify \<circ> \<Gamma>' \<turnstile>\<^sub>n solidify e' : typeify t"
proof (induction e arbitrary: \<Gamma> vs e' t vs' \<Gamma>')
  case (NLam x e)
  let ?v = "fresh vs"
  from NLam obtain ee' tt g\<Gamma>' t' where T: "g\<Gamma>' x = Some t' \<and> 
    typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e = Some (ee', tt, vs', g\<Gamma>') \<and> 
      e' = HLam x t' ee' \<and> t = Ctor ''Arrow'' [t', tt] \<and> \<Gamma>' = (g\<Gamma>'(x := \<Gamma> x))" 
    by (auto simp add: Let_def split: option.splits prod.splits)
  hence X: "g\<Gamma>' = (\<Gamma>'(x \<mapsto> t'))" by auto
  from NLam have "valid_ty_subst (\<Gamma>(x \<mapsto> Var ?v))" by simp
  with NLam(1) T have "map_option typeify \<circ> g\<Gamma>' \<turnstile>\<^sub>n solidify ee' : typeify tt" by blast
  with X have "map_option typeify \<circ> \<Gamma>' \<turnstile>\<^sub>n solidify (HLam x t' ee') : 
    typeify (Ctor ''Arrow'' [t', tt])" by simp
  with T show ?case by blast
next
  case (NApp e1 e2)
  from NApp(3) obtain e\<^sub>1' t\<^sub>1 t\<^sub>2 vvs' g\<Gamma>' e\<^sub>2' t\<^sub>3 g\<Gamma>'' sub where T: "unify t\<^sub>1 t\<^sub>2 = Some sub \<and> 
    t = subst sub t\<^sub>2 \<and> e' = HApp (hsubst sub e\<^sub>1') (hsubst sub e\<^sub>2') \<and> 
      \<Gamma>' = map_option (subst sub) \<circ> g\<Gamma>'' \<and> 
        typecheck' \<Gamma> vs e1 = Some (e\<^sub>1', Ctor ''Arrow'' [t\<^sub>1, t\<^sub>2], vvs', g\<Gamma>') \<and>
          typecheck' g\<Gamma>' vvs' e2 = Some (e\<^sub>2', t\<^sub>3, vs', g\<Gamma>'')" 
    by (auto split: option.splits prod.splits uexpr.splits list.splits if_splits)
  with NApp(4) have X: "valid_ty_subst g\<Gamma>' \<and> valid_ty_uexpr (Ctor ''Arrow'' [t\<^sub>1, t\<^sub>2]) \<and> 
    valid_ty_hexpr e\<^sub>1'" by fastforce
  with NApp T have Z: "map_option typeify \<circ> g\<Gamma>'' \<turnstile>\<^sub>n solidify e\<^sub>2' : typeify t\<^sub>3" by blast
  from T X have Y: "valid_ty_subst g\<Gamma>'' \<and> valid_ty_uexpr t\<^sub>3 \<and> valid_ty_hexpr e\<^sub>2'" by fastforce


  from NApp T have "map_option typeify \<circ> g\<Gamma>' \<turnstile>\<^sub>n solidify e\<^sub>1' : typeify (Ctor ''Arrow'' [t\<^sub>1, t\<^sub>2])" by blast
  hence "map_option typeify \<circ> g\<Gamma>' \<turnstile>\<^sub>n solidify e\<^sub>1' : Arrow (typeify t\<^sub>1) (typeify t\<^sub>2)" by simp




  have "map_option typeify \<circ> g\<Gamma>'' \<turnstile>\<^sub>n solidify e\<^sub>1' : Arrow (typeify t\<^sub>3) (typeify t\<^sub>2)" by simp
  with Z have "map_option typeify \<circ> g\<Gamma>'' \<turnstile>\<^sub>n TApp (solidify e\<^sub>1') (solidify e\<^sub>2') : typeify t\<^sub>2" by simp
  hence "map_option (tsubsts sub) \<circ> (map_option typeify \<circ> g\<Gamma>'') \<turnstile>\<^sub>n 
    tsubstt sub (TApp (solidify e\<^sub>1') (solidify e\<^sub>2')) : tsubsts sub (typeify t\<^sub>2)" 
      by (metis tc_tsubstt)
  with X Y have "map_option typeify \<circ> (map_option (subst sub) \<circ> g\<Gamma>'') \<turnstile>\<^sub>n 
    solidify (HApp (hsubst sub e\<^sub>1') (hsubst sub e\<^sub>2')) : typeify (subst sub t\<^sub>2)" by simp
  with T show ?case by blast
qed (auto split: option.splits)

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> Map.empty \<turnstile>\<^sub>n e\<^sub>t : t"
proof -
  assume "typecheck e = Some (e\<^sub>t, t)"
  then obtain e' tt vs \<Gamma> where T: "typecheck' Map.empty {} e = Some (e', tt, vs, \<Gamma>) \<and> 
    e\<^sub>t = solidify e' \<and> t = typeify tt" by (auto split: option.splits)
  moreover hence "map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n solidify e' : typeify tt" by auto
  moreover from T have "dom \<Gamma> = dom Map.empty" by force
  ultimately show "Map.empty \<turnstile>\<^sub>n e\<^sub>t : t" by simp
qed

lemma erase_solidify [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> typecheck' \<Gamma> vs e = Some (e', t, vs', \<Gamma>') \<Longrightarrow> 
  e = erase (solidify e')"
proof (induction e arbitrary: \<Gamma> vs e' t vs' \<Gamma>')
  case (NLam x e)
  let ?v = "fresh vs"
  from NLam(3) obtain ee' tt g\<Gamma>' t' where T: "g\<Gamma>' x = Some t' \<and> e' = HLam x t' ee' \<and> 
    t = Ctor ''Arrow'' [t', tt] \<and> \<Gamma>' = g\<Gamma>'(x := \<Gamma> x) \<and> 
      typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e = Some (ee', tt, vs', g\<Gamma>')" 
    by (auto simp add: Let_def split: option.splits)
  from NLam have "valid_ty_subst (\<Gamma>(x \<mapsto> Var ?v))" by simp
  with NLam(1) T have "e = erase (solidify ee')" by blast
  with T show ?case by simp
next
  case (NApp e1 e2)
  from NApp(4) obtain e\<^sub>1' t\<^sub>1 t\<^sub>2 vvs' g\<Gamma>' e\<^sub>2' t\<^sub>3 g\<Gamma>'' sub where T: "unify t\<^sub>1 t\<^sub>2 = Some sub \<and> 
    t = subst sub t\<^sub>2 \<and> e' = HApp (hsubst sub e\<^sub>1') (hsubst sub e\<^sub>2') \<and> 
      \<Gamma>' = map_option (subst sub) \<circ> g\<Gamma>'' \<and> 
        typecheck' \<Gamma> vs e1 = Some (e\<^sub>1', Ctor ''Arrow'' [t\<^sub>1, t\<^sub>2], vvs', g\<Gamma>') \<and>
          typecheck' g\<Gamma>' vvs' e2 = Some (e\<^sub>2', t\<^sub>3, vs', g\<Gamma>'')" 
    by (auto split: option.splits prod.splits uexpr.splits list.splits if_splits)
  moreover with NApp(3) have X: "valid_ty_subst g\<Gamma>' \<and> valid_ty_uexpr (Ctor ''Arrow'' [t\<^sub>1, t\<^sub>2]) \<and> 
    valid_ty_hexpr e\<^sub>1'" by fastforce
  moreover with T have "valid_ty_subst g\<Gamma>'' \<and> valid_ty_uexpr t\<^sub>3 \<and> valid_ty_hexpr e\<^sub>2'" by fastforce
  moreover from NApp T have "e1 = erase (solidify e\<^sub>1')" by blast
  moreover from NApp T X have "e2 = erase (solidify e\<^sub>2')" by blast
  ultimately show ?case by simp
qed (auto simp add: Let_def split: option.splits)

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> e = erase e\<^sub>t"
proof -
  assume "typecheck e = Some (e\<^sub>t, t)"
  then obtain e' tt vs \<Gamma> where T: "typecheck' Map.empty {} e = Some (e', tt, vs, \<Gamma>) \<and> 
    e\<^sub>t = solidify e' \<and> t = typeify tt" by (auto split: option.splits)
  moreover have "valid_ty_subst Map.empty" by simp
  ultimately have "e = erase (solidify e')" by (metis erase_solidify)
  with T show ?thesis by simp
qed

lemma [dest]: "NVar x = erase e\<^sub>t \<Longrightarrow> e\<^sub>t = TVar x"
  by (induction e\<^sub>t) simp_all

lemma [dest]: "NLam x e = erase e\<^sub>t \<Longrightarrow> \<exists>t e\<^sub>t'. e\<^sub>t = TLam x t e\<^sub>t' \<and> e = erase e\<^sub>t'"
  by (induction e\<^sub>t) simp_all

lemma [simp]: "typecheck' \<Gamma> vs e = None \<Longrightarrow> \<nexists>e\<^sub>t t. (map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>t : t) \<and> e = erase e\<^sub>t"
proof (induction e arbitrary: \<Gamma> vs)
  case (NVar x)
  hence X: "\<Gamma> x = None" by (simp split: option.splits)
  have "\<And>e\<^sub>t. NVar x = erase e\<^sub>t \<Longrightarrow> \<nexists>t. map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>t : t"
  proof 
    fix e\<^sub>t
    assume "NVar x = erase e\<^sub>t" 
    hence "e\<^sub>t = TVar x" by blast
    moreover assume "\<exists>t. map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>t : t"
    ultimately obtain t where "(map_option typeify \<circ> \<Gamma>) x = Some t" by blast
    with X show False by simp
  qed
  thus ?case by blast
next
  case (NLam x e)
  let ?v = "fresh vs"
  have "\<And>e\<^sub>t. NLam x e = erase e\<^sub>t \<Longrightarrow> \<nexists>t. map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>t : t"
  proof
    fix e\<^sub>t
    assume "NLam x e = erase e\<^sub>t" 
    then obtain t\<^sub>1 e\<^sub>t' where E: "e\<^sub>t = TLam x t\<^sub>1 e\<^sub>t' \<and> e = erase e\<^sub>t'" by blast
    moreover assume "\<exists>t. map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>t : t"
    ultimately obtain t\<^sub>2 where "(map_option typeify \<circ> \<Gamma>)(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e\<^sub>t' : t\<^sub>2" by blast
    show False
    proof (cases "typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e")
      case None
      with NLam E have "\<And>t. \<not> map_option typeify \<circ> (\<Gamma>(x \<mapsto> Var ?v)) \<turnstile>\<^sub>n e\<^sub>t' : t" by blast
    
    
      show False by blast
    next
      case (Some a)
      with NLam have "\<exists>e' t vs' \<Gamma>'. typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e = Some (e', t, vs', \<Gamma>') \<and> \<Gamma>' x = None" 
        by (auto simp add: Let_def split: option.splits prod.splits)
    
    
      show False by blast
    qed
  qed
  thus ?case by blast
next
  case (NApp e1 e2)
  then show ?case by simp
qed simp_all

lemma typecheck_fails [simp]: "typecheck e = None \<Longrightarrow> \<nexists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> e = erase e\<^sub>t"
  by simp

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

lemma correctness' [simp]: "e \<Down> v \<Longrightarrow> typecheck' \<Gamma> vs e = Some (e\<^sub>t, t1, vs', \<Gamma>') \<Longrightarrow> 
  typecheck' \<Gamma> vs v = Some (v\<^sub>t, t2, vs'', \<Gamma>'') \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> typeify t1 = typeify t2 \<Longrightarrow> 
    solidify e\<^sub>t \<Down>\<^sub>t solidify v\<^sub>t"
proof (induction e v arbitrary: \<Gamma> vs e\<^sub>t t1 vs' \<Gamma>' v\<^sub>t t2 vs'' \<Gamma>'' rule: evaln.induct)
  case (evn_app e\<^sub>1 x e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  from evn_app(7) obtain e\<^sub>1'' t\<^sub>1 t\<^sub>2 vs\<^sub>1' \<Gamma>\<^sub>1' e\<^sub>2' t\<^sub>3 \<Gamma>\<^sub>2' sub where T: "t1 = subst sub t\<^sub>2 \<and> 
    e\<^sub>t = HApp (hsubst sub e\<^sub>1'') (hsubst sub e\<^sub>2') \<and> \<Gamma>' = map_option (subst sub) \<circ> \<Gamma>\<^sub>2' \<and>
      typecheck' \<Gamma> vs e\<^sub>1 = Some (e\<^sub>1'', Ctor ''Arrow'' [t\<^sub>1, t\<^sub>2], vs\<^sub>1', \<Gamma>\<^sub>1') \<and>
        typecheck' \<Gamma>\<^sub>1' vs\<^sub>1' e\<^sub>2 = Some (e\<^sub>2', t\<^sub>3, vs', \<Gamma>\<^sub>2') \<and> unify t\<^sub>1 t\<^sub>2 = Some sub" 
    by (auto split: option.splits if_splits uexpr.splits list.splits)
  with evn_app(9) have X: "valid_ty_subst \<Gamma>\<^sub>1' \<and> valid_ty_uexpr (Ctor ''Arrow'' [t\<^sub>1, t\<^sub>2]) \<and> 
    valid_ty_hexpr e\<^sub>1''" by fastforce
  with T have Y: "valid_ty_subst \<Gamma>\<^sub>2' \<and> valid_ty_uexpr t\<^sub>3 \<and> valid_ty_hexpr e\<^sub>2'" by fastforce


  from evn_app T have "typecheck' \<Gamma> vs (NLam x e\<^sub>1') = Some (xv\<^sub>t, xt2, xvs'', x\<Gamma>'') \<Longrightarrow> 
    Arrow (typeify t\<^sub>1) (typeify t\<^sub>2) = typeify xt2 \<Longrightarrow> solidify e\<^sub>1'' \<Down>\<^sub>t solidify xv\<^sub>t" by auto

  from evn_app T have "typecheck' \<Gamma>\<^sub>1' vs\<^sub>1' v\<^sub>2 = Some (xv\<^sub>t, xt2, xvs'', x\<Gamma>'') \<Longrightarrow> 
    typeify t\<^sub>3 = typeify xt2 \<Longrightarrow> valid_ty_subst \<Gamma>\<^sub>1' \<Longrightarrow> solidify e\<^sub>2' \<Down>\<^sub>t solidify xv\<^sub>t" by blast

  from evn_app have "e\<^sub>1 \<Down> NLam x e\<^sub>1'" by simp
  from evn_app have "e\<^sub>2 \<Down> v\<^sub>2" by simp
  from evn_app have "substn x v\<^sub>2 e\<^sub>1' \<Down> v" by simp




  from evn_app have "typecheck' x\<Gamma> xvs (substn x v\<^sub>2 e\<^sub>1') = Some (xe\<^sub>t, xt1, xvs', x\<Gamma>') \<Longrightarrow>
    typecheck' x\<Gamma> xvs v = Some (xv\<^sub>t, xt2, xvs'', x\<Gamma>'') \<Longrightarrow> valid_ty_subst x\<Gamma> \<Longrightarrow> typeify xt1 = typeify xt2 \<Longrightarrow> 
      solidify xe\<^sub>t \<Down>\<^sub>t solidify xv\<^sub>t" by simp
  from evn_app have "typecheck' \<Gamma> vs v = Some (v\<^sub>t, t2, vs'', \<Gamma>'')" by simp
  from evn_app have "typeify t1 = typeify t2" by simp


  have "tsubstt sub (TApp (solidify e\<^sub>1'') (solidify e\<^sub>2')) \<Down>\<^sub>t solidify v\<^sub>t" by simp
  with T X Y show ?case by simp
qed (auto simp add: Let_def split: option.splits)

theorem correctness: "e \<Down> v \<Longrightarrow> typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> typecheck v = Some (v\<^sub>t, t) \<Longrightarrow> 
    e\<^sub>t \<Down>\<^sub>t v\<^sub>t"
  by (auto split: option.splits)

end