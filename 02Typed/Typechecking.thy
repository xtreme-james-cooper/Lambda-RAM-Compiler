theory Typechecking
  imports Typed "../01Source/SourceLanguage" UnifiableType
begin

datatype hexpr = 
  HVar var
  | HConst nat
  | HLam var uterm hexpr
  | HApp hexpr hexpr

primrec hsubst :: "subst \<Rightarrow> hexpr \<Rightarrow> hexpr" where
  "hsubst sub (HVar x) = HVar x"
| "hsubst sub (HConst k) = HConst k"
| "hsubst sub (HLam x t e) = HLam x (subst sub t) (hsubst sub e)"
| "hsubst sub (HApp e\<^sub>1 e\<^sub>2) = HApp (hsubst sub e\<^sub>1) (hsubst sub e\<^sub>2)"

primrec erase :: "texpr \<Rightarrow> expr\<^sub>s" where
  "erase (TVar x) = Var\<^sub>s x"
| "erase (TConst k) = Const\<^sub>s k"
| "erase (TLam x t e) = Lam\<^sub>s x (erase e)"
| "erase (TApp e\<^sub>1 e\<^sub>2) = App\<^sub>s (erase e\<^sub>1) (erase e\<^sub>2)"

primrec htvars :: "hexpr \<Rightarrow> var set" where
  "htvars (HVar x) = {}"
| "htvars (HConst k) = {}"
| "htvars (HLam x t e) = uvars t \<union> htvars e"
| "htvars (HApp e\<^sub>1 e\<^sub>2) = htvars e\<^sub>1 \<union> htvars e\<^sub>2"

primrec typecheck' :: "subst \<Rightarrow> var set \<Rightarrow> expr\<^sub>s \<Rightarrow> hexpr \<times> uterm \<times> var set \<times> constraint" 
    where
  "typecheck' \<Gamma> vs (Var\<^sub>s x) = (case \<Gamma> x of 
      Some t \<Rightarrow> (HVar x, t, vs, []) 
    | None \<Rightarrow> (HVar x, Ctor ''Num'' [], vs, fail))"
| "typecheck' \<Gamma> vs (Const\<^sub>s k) = (HConst k, Ctor ''Num'' [], vs, [])"
| "typecheck' \<Gamma> vs (Lam\<^sub>s x e) = (
    let v = fresh vs
    in let (e', t, vs', con) = typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e
    in (HLam x (Var v) e', Ctor ''Arrow'' [Var v, t], vs', con))"
| "typecheck' \<Gamma> vs (App\<^sub>s e\<^sub>1 e\<^sub>2) = (
    let v = fresh vs
    in let (e\<^sub>1', t\<^sub>1, vs', con\<^sub>1) = typecheck' \<Gamma> (insert v vs) e\<^sub>1 
    in let (e\<^sub>2', t\<^sub>2, vs'', con\<^sub>2) = typecheck' \<Gamma> vs' e\<^sub>2 
    in (HApp e\<^sub>1' e\<^sub>2', Var v, vs'', con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1, Ctor ''Arrow'' [t\<^sub>2, Var v])]))"

primrec solidify :: "hexpr \<Rightarrow> texpr" where
  "solidify (HVar x) = TVar x"
| "solidify (HConst k) = TConst k"
| "solidify (HLam x t e) = TLam x (typeify t) (solidify e)"
| "solidify (HApp e\<^sub>1 e\<^sub>2) = TApp (solidify e\<^sub>1) (solidify e\<^sub>2)"

primrec liquify :: "texpr \<Rightarrow> hexpr" where
  "liquify (TVar x) = HVar x"
| "liquify (TConst k) = HConst k"
| "liquify (TLam x t e) = HLam x (untypeify t) (liquify e)"
| "liquify (TApp e\<^sub>1 e\<^sub>2) = HApp (liquify e\<^sub>1) (liquify e\<^sub>2)"

primrec tsubstt :: "subst \<Rightarrow> texpr \<Rightarrow> texpr" where
  "tsubstt sub (TVar x) = TVar x"
| "tsubstt sub (TConst k) = TConst k"
| "tsubstt sub (TLam x t e) = TLam x (tsubsts sub t) (tsubstt sub e)"
| "tsubstt sub (TApp e\<^sub>1 e\<^sub>2) = TApp (tsubstt sub e\<^sub>1) (tsubstt sub e\<^sub>2)"

fun typecheck :: "expr\<^sub>s \<rightharpoonup> texpr \<times> ty" where
  "typecheck e = (
    let (e', t, vs, con) = typecheck' Map.empty {} e
    in case unify con of 
        Some sub \<Rightarrow> Some (tsubstt sub (solidify e'), tsubsts sub (typeify t))
      | None \<Rightarrow> None)"

primrec valid_ty_hexpr :: "hexpr \<Rightarrow> bool" where
  "valid_ty_hexpr (HVar x) = True"
| "valid_ty_hexpr (HConst k) = True"
| "valid_ty_hexpr (HLam x t e) = (valid_ty_uexpr t \<and> valid_ty_hexpr e)"
| "valid_ty_hexpr (HApp e\<^sub>1 e\<^sub>2) = (valid_ty_hexpr e\<^sub>1 \<and> valid_ty_hexpr e\<^sub>2)"

lemma typecheck_induct [consumes 1, case_names Var\<^sub>sS Var\<^sub>sN Const\<^sub>s Lam\<^sub>s App\<^sub>s]: "
  typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> 
  (\<And>\<Gamma> vs t x. \<Gamma> x = Some t \<Longrightarrow> P \<Gamma> vs (Var\<^sub>s x) (HVar x) t vs []) \<Longrightarrow> 
  (\<And>\<Gamma> vs x. \<Gamma> x = None \<Longrightarrow> P \<Gamma> vs (Var\<^sub>s x) (HVar x) (Ctor ''Num'' [])  vs fail) \<Longrightarrow> 
  (\<And>\<Gamma> vs k. P \<Gamma> vs (Const\<^sub>s k) (HConst k) (Ctor ''Num'' []) vs []) \<Longrightarrow> 
  (\<And>\<Gamma> vs vs' con x e\<^sub>1 e\<^sub>1' t' v. v = fresh vs \<Longrightarrow> typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>1 = 
    (e\<^sub>1', t', vs', con) \<Longrightarrow> P (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>1 e\<^sub>1' t' vs' con \<Longrightarrow> 
      P \<Gamma> vs (Lam\<^sub>s x e\<^sub>1) (HLam x (Var v) e\<^sub>1') (Ctor ''Arrow'' [Var v, t']) vs' con) \<Longrightarrow> 
  (\<And>\<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2. v = fresh vs \<Longrightarrow> 
    typecheck' \<Gamma> (insert v vs) e\<^sub>1 = (e\<^sub>1', t\<^sub>1, vs'', con\<^sub>1) \<Longrightarrow> 
      typecheck' \<Gamma> vs'' e\<^sub>2 = (e\<^sub>2', t\<^sub>2, vs', con\<^sub>2) \<Longrightarrow> P \<Gamma> (insert v vs) e\<^sub>1 e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 \<Longrightarrow> 
        P \<Gamma> vs'' e\<^sub>2 e\<^sub>2' t\<^sub>2 vs' con\<^sub>2 \<Longrightarrow> P \<Gamma> vs (App\<^sub>s e\<^sub>1 e\<^sub>2) (HApp e\<^sub>1' e\<^sub>2') (Var v) vs' 
          (con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1, Ctor ''Arrow'' [t\<^sub>2, Var v])])) \<Longrightarrow> 
    P \<Gamma> vs e e' t vs' con"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (auto simp add: Let_def split: option.splits prod.splits)

lemma [simp]: "valid_ty_hexpr (liquify e)"
  by (induction e) simp_all

lemma [simp]: "x \<notin> htvars e \<Longrightarrow> hsubst [x \<mapsto> t] e = e"
  by (induction e) simp_all

lemma [simp]: "hsubst (extend_subst x t s) e = hsubst s (hsubst [x \<mapsto> t] e)"
  by (induction e) (simp_all only: hsubst.simps expand_extend_subst comp_def)

lemma [simp]: "valid_ty_hexpr e \<Longrightarrow> solidify (hsubst sub e) = tsubstt sub (solidify e)"
  by (induction e) simp_all

lemma [simp]: "valid_ty_subst sub \<Longrightarrow> liquify (tsubstt sub e) = hsubst sub (liquify e)"
  by (induction e) simp_all

lemma [simp]: "solidify (liquify e) = e"
  by (induction e) simp_all

lemma [simp]: "valid_ty_hexpr e \<Longrightarrow> liquify (solidify e) = e"
  by (induction e) simp_all

lemma [simp]: "valid_ty_hexpr e \<Longrightarrow> tvarst (solidify e) = htvars e"
  by (induction e) simp_all

lemma [simp]: "erase (solidify (hsubst sub e)) = erase (solidify e)"
  by (induction e) simp_all

lemma [simp]: "erase (tsubstt sub e) = erase e"
  by (induction e) simp_all

lemma [simp]: "valid_ty_subst sub \<Longrightarrow> valid_ty_hexpr e \<Longrightarrow> valid_ty_hexpr (hsubst sub e)"
  by (induction e) simp_all

lemma [simp]: "htvars (hsubst sub e) \<subseteq> htvars e - dom sub \<union> subst_vars sub"
proof (induction e)
  case (HLam x t e)
  moreover have "uvars (subst sub t) \<subseteq> uvars t - dom sub \<union> subst_vars sub" by simp
  ultimately show ?case by fastforce
qed auto

lemma [simp]: "dom sub \<inter> htvars e = {} \<Longrightarrow> hsubst sub e = e"
proof (induction e)
  case (HLam x t e)
  moreover hence "dom sub \<inter> uvars t = {}" by auto
  ultimately show ?case by auto
qed auto

lemma [simp]: "dom sub \<inter> tvarst e = {} \<Longrightarrow> tsubstt sub e = e"
proof (induction e)
  case (TLam x t e)
  moreover hence "dom sub \<inter> tvars t = {}" by auto
  ultimately show ?case by auto
qed auto

lemma tc_tsubstt [simp]: "\<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> 
  map_option (tsubsts sub) \<circ> \<Gamma> \<turnstile>\<^sub>n tsubstt sub e : tsubsts sub t"
proof (induction \<Gamma> e t rule: typecheckn.induct)
  case (tcn_lam \<Gamma> x t\<^sub>1 e t\<^sub>2)
  hence "map_option (tsubsts sub) \<circ> \<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n tsubstt sub e : tsubsts sub t\<^sub>2" by blast
  hence "map_option (tsubsts sub) \<circ> \<Gamma> \<turnstile>\<^sub>n tsubstt sub (TLam x t\<^sub>1 e) : tsubsts sub (Arrow t\<^sub>1 t\<^sub>2)" 
    by simp
  thus ?case by blast
qed simp_all

lemma [simp]: "hsubst (combine_subst s t) e = hsubst s (hsubst t e)"
  by (induction e) simp_all

lemma [elim]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_uexpr t"
  by (induction rule: typecheck_induct) auto

lemma [elim]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_hexpr e'"
  by (induction rule: typecheck_induct) auto

lemma typecheck_succeeds [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> 
  valid_ty_subst \<Gamma> \<Longrightarrow> unify con = Some sub' \<Longrightarrow> sub specializes sub' \<Longrightarrow>
    map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub e') : typeify (subst sub t)"
proof (induction arbitrary: sub' rule: typecheck_induct)
  case (Var\<^sub>sS \<Gamma> vs t x)
  thus ?case by simp
next
  case (Lam\<^sub>s \<Gamma> vs vs' con x e\<^sub>1 e\<^sub>1' t' v)
  hence "valid_ty_subst (\<Gamma>(x \<mapsto> Var v))" by simp
  with Lam\<^sub>s have "map_option (typeify \<circ> subst sub) \<circ> \<Gamma>(x \<mapsto> Var v) \<turnstile>\<^sub>n solidify (hsubst sub e\<^sub>1') : 
      typeify (subst sub t')" by blast
  hence "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub (HLam x (Var v) e\<^sub>1')) :
    typeify (subst sub (Ctor ''Arrow'' [Var v, t']))" by simp
  thus ?case by blast
next
  case (App\<^sub>s \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2)
  then obtain s\<^sub>2 where S2: "unify (con\<^sub>1 @ con\<^sub>2) = Some s\<^sub>2 \<and> sub' specializes s\<^sub>2" by fastforce
  then obtain s\<^sub>3 where S3: "unify con\<^sub>1 = Some s\<^sub>3 \<and> s\<^sub>2 specializes s\<^sub>3" by fastforce
  with App\<^sub>s S2 have "sub specializes s\<^sub>3" by auto
  with App\<^sub>s S2 S3 have T: "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub e\<^sub>1') : 
    typeify (subst sub t\<^sub>1)" by blast
  from App\<^sub>s have "sub' unifies\<^sub>\<kappa> (con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1, Ctor ''Arrow'' [t\<^sub>2, Var v])])" 
    by (metis unify_some) 
  hence "sub' unifies t\<^sub>1 and Ctor ''Arrow'' [t\<^sub>2, Var v]" by simp
  with App\<^sub>s have X: "sub unifies t\<^sub>1 and Ctor ''Arrow'' [t\<^sub>2, Var v]" by fastforce
  from S2 obtain s\<^sub>4 where S4: "unify con\<^sub>2 = Some s\<^sub>4 \<and> s\<^sub>2 specializes s\<^sub>4" 
    using unify_append_snd by blast
  with App\<^sub>s S2 have "sub specializes s\<^sub>4" by auto
  with App\<^sub>s S4 have "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub e\<^sub>2') : 
    typeify (subst sub t\<^sub>2)" by blast
  with T X have "map_option (typeify \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>n solidify (hsubst sub (HApp e\<^sub>1' e\<^sub>2')) : 
    typeify (subst sub (Var v))" by simp
  thus ?case by blast
qed simp_all

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> Map.empty \<turnstile>\<^sub>n e\<^sub>t : t"
proof -
  assume "typecheck e = Some (e\<^sub>t, t)"
  then obtain e' tt vs con sub where T: "typecheck' Map.empty {} e = (e', tt, vs, con) \<and>
    unify con = Some sub \<and> e\<^sub>t = tsubstt sub (solidify e') \<and> t = tsubsts sub (typeify tt)" 
      by (auto split: option.splits prod.splits)
  moreover hence "map_option (typeify \<circ> subst sub) \<circ> Map.empty \<turnstile>\<^sub>n solidify (hsubst sub e') : 
    typeify (subst sub tt)" by (metis typecheck_succeeds valid_empty specializes_refl)
  moreover from T have "valid_ty_uexpr tt" and "valid_ty_hexpr e'" by auto
  ultimately show "Map.empty \<turnstile>\<^sub>n e\<^sub>t : t" by simp
qed

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> e = erase (solidify e')"
  by (induction rule: typecheck_induct) auto

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> e = erase e\<^sub>t"
  by (auto split: option.splits prod.splits)

lemma [dest]: "erase e\<^sub>t = Var\<^sub>s x \<Longrightarrow> e\<^sub>t = TVar x"
  by (induction e\<^sub>t) simp_all

lemma [dest]: "erase e\<^sub>t = Lam\<^sub>s x e \<Longrightarrow> \<exists>t e\<^sub>t'. e\<^sub>t = TLam x t e\<^sub>t' \<and> e = erase e\<^sub>t'"
  by (induction e\<^sub>t) simp_all

lemma [dest]: "erase e\<^sub>t = App\<^sub>s e\<^sub>1 e\<^sub>2 \<Longrightarrow> \<exists>e\<^sub>1' e\<^sub>2'. e\<^sub>t = TApp e\<^sub>1' e\<^sub>2' \<and> e\<^sub>1 = erase e\<^sub>1'\<and> e\<^sub>2 = erase e\<^sub>2'"
  by (induction e\<^sub>t) simp_all

lemma vars_expand: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> vs \<subseteq> vs'"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (simp_all add: Let_def split: option.splits prod.splits, fastforce+)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> finite vs' = finite vs"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (simp_all add: Let_def split: option.splits prod.splits)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> finite vs \<Longrightarrow> htvars e' \<subseteq> vs' - vs"
proof (induction rule: typecheck_induct)
  case (Lam\<^sub>s \<Gamma> vs vs' con x e\<^sub>1 e\<^sub>1' t' v)
  moreover hence "insert v vs \<subseteq> vs'" by (metis vars_expand)
  ultimately show ?case by auto
next
  case (App\<^sub>s \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2)
  moreover hence "insert v vs \<subseteq> vs''" by (metis vars_expand)
  moreover from App\<^sub>s have "vs'' \<subseteq> vs'" by (metis vars_expand)
  ultimately show ?case by auto
qed simp_all

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> x \<in> vs \<Longrightarrow> finite vs \<Longrightarrow> x \<notin> htvars e'"
proof -
  assume "typecheck' \<Gamma> vs e = (e', t', vs', con)"
     and "finite vs"
  hence "htvars e' \<subseteq> vs' - vs" by simp
  moreover assume "x \<in> vs" 
  ultimately show "x \<notin> htvars e'" by auto
qed

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> x \<in> vs \<Longrightarrow> finite vs \<Longrightarrow>
  x \<notin> subst_vars \<Gamma> \<Longrightarrow> x \<notin> uvars t'"
proof (induction rule: typecheck_induct)
  case (Lam\<^sub>s \<Gamma> vs vs' con y e\<^sub>1 e\<^sub>1' t' v)
  moreover hence "x \<notin> subst_vars (\<Gamma>(y \<mapsto> Var v))" by (auto simp add: subst_vars_def ran_def)
  ultimately show ?case by simp
qed (auto simp add: subst_vars_def ran_def)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> x \<in> vs \<Longrightarrow> finite vs \<Longrightarrow>
  x \<notin> subst_vars \<Gamma> \<Longrightarrow> x \<notin> constr_vars con"
proof (induction rule: typecheck_induct)
  case (App\<^sub>s \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2)
  moreover hence "x \<in> vs''" using vars_expand by fastforce
  ultimately show ?case by auto
qed fastforce+

lemma [simp]: "typecheck' (\<Gamma>(x \<mapsto> Var y)) vs e = (e', tt, vs', con) \<Longrightarrow> y \<in> vs \<Longrightarrow>
  subst_vars \<Gamma> \<subseteq> vs - {y} \<Longrightarrow> uvars t' \<subseteq> vs - {y} \<Longrightarrow> finite vs \<Longrightarrow> typecheck' (\<Gamma>(x \<mapsto> t')) vs e = 
    (hsubst [y \<mapsto> t'] e', subst [y \<mapsto> t'] tt, vs', constr_subst y t' con)"
proof (induction e arbitrary: \<Gamma> vs e' tt vs' con)
  case (Var\<^sub>s z)
  thus ?case
  proof (cases "x = z")
    case False
    with Var\<^sub>s show ?thesis
    proof (cases "\<Gamma> z")
      case (Some t)
      from Var\<^sub>s have "y \<notin> subst_vars \<Gamma>" by auto
      with Var\<^sub>s False Some have "typecheck' (\<Gamma>(x \<mapsto> t')) vs (Var\<^sub>s z) =
        (hsubst [y \<mapsto> t'] e', subst [y \<mapsto> t'] tt, vs', constr_subst y t' con)" 
          by auto
      thus ?thesis by blast
    qed auto
  qed auto
next
  case (Lam\<^sub>s z e)
  let ?v = "fresh vs"
  from Lam\<^sub>s have F: "fresh vs \<noteq> y" using fresh_is_fresh by blast
  obtain e'' tt' vs'' con' where T: "typecheck' (\<Gamma>(x \<mapsto> Var y, z \<mapsto> Var ?v)) (insert ?v vs) e = 
    (e'', tt', vs'', con')" by (metis prod_cases4)
  show ?case
  proof (cases "x = z")
    case True
    from T Lam\<^sub>s(2) have E: "e' = HLam z (Var ?v) e'' \<and> tt = Ctor ''Arrow'' [Var ?v, tt'] \<and> 
      vs'' = vs' \<and> con' = con" by (simp only: typecheck'.simps Let_def split: prod.splits) simp
    from T True E have T': "typecheck' (\<Gamma>(z \<mapsto> Var ?v)) (insert ?v vs) e = (e'', tt', vs', con)" 
      by simp
    from Lam\<^sub>s(4) F have "y \<notin> subst_vars (\<Gamma>(z \<mapsto> Var ?v))" 
      by (auto simp add: subst_vars_def ran_def)
    with Lam\<^sub>s F E T' True T have "typecheck' (\<Gamma>(x \<mapsto> t')) vs (Lam\<^sub>s z e) =
      (hsubst [y \<mapsto> t'] e', subst [y \<mapsto> t'] tt, vs', constr_subst y t' con)" 
        by (simp add: Let_def split: if_splits prod.splits)
    thus ?thesis by blast
  next
    case False
    from Lam\<^sub>s have "typecheck' (\<Gamma>(x \<mapsto> Var y)) vs (Lam\<^sub>s z e) = (e', tt, vs', con)" by blast
    with T have E: "e' = HLam z (Var ?v) e'' \<and> tt = Ctor ''Arrow'' [Var ?v, tt'] \<and> vs'' = vs' \<and> 
      con' = con" by (simp add: Let_def)
    from E T False have X: "typecheck' (\<Gamma>(z \<mapsto> Var ?v, x \<mapsto> Var y)) (insert ?v vs) e = 
      (e'', tt', vs', con)" by (metis fun_upd_twist)
    have "subst_vars (\<Gamma>(z := None)) \<subseteq> subst_vars \<Gamma>" by simp
    with Lam\<^sub>s(4) F have "subst_vars (\<Gamma>(z \<mapsto> Var ?v)) \<subseteq> insert ?v vs - {y}" by fastforce
    with Lam\<^sub>s X have "typecheck' (\<Gamma>(z \<mapsto> Var ?v, x \<mapsto> t')) (insert ?v vs) e = 
      (hsubst [y \<mapsto> t'] e'', subst [y \<mapsto> t'] tt', vs', constr_subst y t' con)" by blast
    with False have "typecheck' (\<Gamma>(x \<mapsto> t', z \<mapsto> Var ?v)) (insert ?v vs) e = 
      (hsubst [y \<mapsto> t'] e'', subst [y \<mapsto> t'] tt', vs', constr_subst y t' con)" 
        by (metis fun_upd_twist)
    with E F have "typecheck' (\<Gamma>(x \<mapsto> t')) vs (Lam\<^sub>s z e) =
      (hsubst [y \<mapsto> t'] e', subst [y \<mapsto> t'] tt, vs', constr_subst y t' con)" 
        by (simp add: Let_def split: if_splits prod.splits)
    thus ?thesis by blast
  qed
next
  case (App\<^sub>s e1 e2)
  let ?v = "fresh vs"
  obtain e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 where T1: "typecheck' (\<Gamma>(x \<mapsto> Var y)) (insert ?v vs) e1 = 
    (e\<^sub>1', t\<^sub>1, vs'', con\<^sub>1)" by (metis prod_cases4)
  moreover obtain e\<^sub>2' t\<^sub>2 vs''' con\<^sub>2 where T2: "typecheck' (\<Gamma>(x \<mapsto> Var y)) vs'' e2 = 
    (e\<^sub>2', t\<^sub>2, vs''', con\<^sub>2)" by (metis prod_cases4)
  moreover from App\<^sub>s have "typecheck' (\<Gamma>(x \<mapsto> Var y)) vs (App\<^sub>s e1 e2) = (e', tt, vs', con)" by blast
  ultimately have E: "e' = HApp e\<^sub>1' e\<^sub>2' \<and> tt = Var ?v \<and> vs''' = vs' \<and> 
    con = con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1, Ctor ''Arrow'' [t\<^sub>2, Var ?v])]" by (auto simp add: Let_def)
  from T1 have V: "vs \<subseteq> vs''" using vars_expand by blast
  from App\<^sub>s V have A: "y \<in> vs''" by auto
  from App\<^sub>s V have B: "subst_vars \<Gamma> \<subseteq> vs'' - {y}" by auto
  from App\<^sub>s V have C: "uvars t' \<subseteq> vs'' - {y}" by auto
  from App\<^sub>s T1 have D: "finite vs''" by simp
  from App\<^sub>s T1 have T1': "typecheck' (\<Gamma>(x \<mapsto> t')) (insert ?v vs) e1 = 
    (hsubst [y \<mapsto> t'] e\<^sub>1', subst [y \<mapsto> t'] t\<^sub>1, vs'', constr_subst y t' con\<^sub>1)" by blast
  from App\<^sub>s T2 A B C D have T2': "typecheck' (\<Gamma>(x \<mapsto> t')) vs'' e2 = 
    (hsubst [y \<mapsto> t'] e\<^sub>2', subst [y \<mapsto> t'] t\<^sub>2, vs''', constr_subst y t' con\<^sub>2)" by blast
  from App\<^sub>s E T1' T2' have "typecheck' (\<Gamma>(x \<mapsto> t')) vs (App\<^sub>s e1 e2) = 
    (hsubst [y \<mapsto> t'] e', subst [y \<mapsto> t'] tt, vs', constr_subst y t' con)" by (auto simp add: Let_def)
  thus ?case by blast
qed auto

lemma typecheck_fails' [simp]: "map_option typeify \<circ> \<Gamma> \<turnstile>\<^sub>n e\<^sub>t : t \<Longrightarrow> finite vs \<Longrightarrow> 
  subst_vars \<Gamma> \<subseteq> vs \<Longrightarrow> tvarst e\<^sub>t \<subseteq> vs \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> 
    typecheck' \<Gamma> vs (erase e\<^sub>t) = (e', tt, vs', con) \<Longrightarrow> \<exists>s. solidify (hsubst s e') = e\<^sub>t \<and> 
      typeify (subst s tt) = t \<and> dom s = vs' - vs \<and> subst_vars s \<subseteq> tvarst e\<^sub>t \<union> subst_vars \<Gamma> \<and> 
        s unifies\<^sub>\<kappa> con \<and> valid_ty_subst s \<and> idempotent s"
proof (induction "map_option typeify \<circ> \<Gamma>" e\<^sub>t t arbitrary: \<Gamma> vs e' tt vs' con rule: typecheckn.induct)
  case (tcn_lam x t\<^sub>1 e t\<^sub>2)
  let ?v = "fresh vs"
  obtain e'' t' vs'' con' where T: "typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) (erase e) = 
    (e'', t', vs'', con')" by (metis prod_cases4)
  with tcn_lam have E: "e' = HLam x (Var ?v) e'' \<and> tt = Ctor ''Arrow'' [Var ?v, t'] \<and> vs'' = vs' \<and> 
    con' = con" by (simp add: Let_def)
  from tcn_lam have TV: "tvars t\<^sub>1 \<subseteq> insert ?v vs" by auto
  from tcn_lam have "subst_vars \<Gamma> \<subseteq> insert ?v vs" by auto
  with TV have X: "subst_vars (\<Gamma>(x \<mapsto> untypeify t\<^sub>1)) \<subseteq> insert ?v vs" by simp
  have Y: "(map_option typeify \<circ> \<Gamma>)(x \<mapsto> t\<^sub>1) = map_option typeify \<circ> (\<Gamma>(x \<mapsto> untypeify t\<^sub>1))" by simp
  from tcn_lam have Z: "tvarst e \<subseteq> insert ?v vs" by auto
  from tcn_lam have W: "valid_ty_subst (\<Gamma>(x \<mapsto> untypeify t\<^sub>1))" by simp
  from tcn_lam T have TC: "typecheck' (\<Gamma>(x \<mapsto> untypeify t\<^sub>1)) (insert ?v vs) (erase e) = 
    (hsubst [?v \<mapsto> untypeify t\<^sub>1] e'', subst [?v \<mapsto> untypeify t\<^sub>1] t', vs'', 
      constr_subst ?v (untypeify t\<^sub>1) con')" by simp
  from tcn_lam have "finite (insert ?v vs)" by simp
  with tcn_lam X Y Z W TC obtain s where S: "
    solidify (hsubst s (hsubst [?v \<mapsto> untypeify t\<^sub>1] e'')) = e \<and> 
      typeify (subst s (subst [?v \<mapsto> untypeify t\<^sub>1] t')) = t\<^sub>2 \<and>
        s unifies\<^sub>\<kappa> constr_subst ?v (untypeify t\<^sub>1) con' \<and> dom s = vs'' - insert ?v vs \<and> 
          subst_vars s \<subseteq> tvarst e \<union> subst_vars (\<Gamma>(x \<mapsto> untypeify t\<^sub>1)) \<and> valid_ty_subst s \<and> 
            idempotent s" by metis
  from tcn_lam have "subst_vars (\<Gamma>(x \<mapsto> untypeify t\<^sub>1)) \<subseteq> vs" by simp
  moreover from tcn_lam have "?v \<notin> vs" by simp
  ultimately have "?v \<notin> subst_vars (\<Gamma>(x \<mapsto> untypeify t\<^sub>1))" by blast
  with tcn_lam TC have "?v \<notin> constr_vars (constr_subst ?v (untypeify t\<^sub>1) con')" by simp
  hence "?v \<notin> constr_vars con' \<or> ?v \<notin> tvars t\<^sub>1" by (simp split: if_splits)
  from TV S have DV: "dom s \<inter> tvars t\<^sub>1 = {}" by auto
  with E S have A: "solidify (hsubst (extend_subst ?v (untypeify t\<^sub>1) s) e') = TLam x t\<^sub>1 e" by simp
  from tcn_lam have V: "?v \<notin> tvars t\<^sub>1" by auto
  from S have U: "?v \<notin> dom s" by auto
  from S have "subst_vars s \<subseteq> tvarst e \<union> subst_vars (\<Gamma>(x \<mapsto> untypeify t\<^sub>1))" by simp
  moreover from tcn_lam have "tvarst e \<union> subst_vars (\<Gamma>(x \<mapsto> untypeify t\<^sub>1)) \<subseteq> vs \<and> finite vs" by simp
  ultimately have "?v \<notin> subst_vars s" by fastforce
  with S V U have B: "idempotent (extend_subst ?v (untypeify t\<^sub>1) s)" by simp
  from S E have C: "extend_subst ?v (untypeify t\<^sub>1) s unifies\<^sub>\<kappa> con" by simp
  from E TC have "insert ?v vs \<subseteq> vs'" by (metis vars_expand)
  with tcn_lam have "insert ?v (vs' - insert ?v vs) = vs' - vs" by auto
  with S E have D: "dom (extend_subst ?v (untypeify t\<^sub>1) s) = vs' - vs" by simp
  have VS: "uvars (subst s (untypeify t\<^sub>1)) \<subseteq> uvars (untypeify t\<^sub>1) - dom s \<union> subst_vars s" 
    by (metis vars_subst)
  from S have "subst_vars s \<subseteq> tvarst e \<union> subst_vars (\<Gamma>(x := None)) \<union> tvars t\<^sub>1" by auto
  hence "subst_vars s \<subseteq> tvarst e \<union> subst_vars \<Gamma> \<union> tvars t\<^sub>1" by auto
  with U VS have F: "subst_vars (extend_subst ?v (untypeify t\<^sub>1) s) \<subseteq> 
    tvarst (TLam x t\<^sub>1 e) \<union> subst_vars \<Gamma>" by auto
  from DV S E have G: "typeify (subst (extend_subst ?v (untypeify t\<^sub>1) s) tt) = Arrow t\<^sub>1 t\<^sub>2" 
    by (simp add: expand_extend_subst)
  from S have "valid_ty_subst (extend_subst ?v (untypeify t\<^sub>1) s)" by simp
  with A B C D F G show ?case by blast
next
  case (tcn_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  let ?v = "fresh vs"
  obtain e\<^sub>1' t\<^sub>1' vs'' con\<^sub>1 where TC1: "typecheck' \<Gamma> (insert ?v vs) (erase e\<^sub>1) = 
    (e\<^sub>1', t\<^sub>1', vs'', con\<^sub>1)" by (metis prod_cases4)
  obtain e\<^sub>2' t\<^sub>2' vs''' con\<^sub>2 where TC2: "typecheck' \<Gamma> vs'' (erase e\<^sub>2) = (e\<^sub>2', t\<^sub>2', vs''', con\<^sub>2)"
    by (metis prod_cases4)
  with tcn_app TC1 have E: "e' = HApp e\<^sub>1' e\<^sub>2' \<and> tt = Var ?v \<and> vs''' = vs' \<and> 
    con = con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1', Ctor ''Arrow'' [t\<^sub>2', Var ?v])]" by (auto simp add: Let_def)
  from tcn_app have X: "subst_vars \<Gamma> \<subseteq> insert ?v vs" by auto
  from tcn_app have "tvarst e\<^sub>1 \<subseteq> insert ?v vs" by auto
  with tcn_app TC1 X obtain s\<^sub>1 where S1: "solidify (hsubst s\<^sub>1 e\<^sub>1') = e\<^sub>1 \<and> 
    typeify (subst s\<^sub>1 t\<^sub>1') = Arrow t\<^sub>1 t\<^sub>2 \<and> dom s\<^sub>1 = vs'' - insert ?v vs \<and> 
      subst_vars s\<^sub>1 \<subseteq> tvarst e\<^sub>1 \<union> subst_vars \<Gamma> \<and> s\<^sub>1 unifies\<^sub>\<kappa> con\<^sub>1 \<and> valid_ty_subst s\<^sub>1 \<and> 
        idempotent s\<^sub>1" by fastforce
  from TC1 have V1: "insert ?v vs \<subseteq> vs''" by (metis vars_expand)
  from TC2 E have V2: "vs'' \<subseteq> vs'" by (metis vars_expand)
  with tcn_app V1 have Y: "subst_vars \<Gamma> \<subseteq> vs''" by auto
  from tcn_app V1 have "tvarst e\<^sub>2 \<subseteq> vs''" by auto
  with tcn_app TC1 TC2 Y obtain s\<^sub>2 where S2: "solidify (hsubst s\<^sub>2 e\<^sub>2') = e\<^sub>2 \<and> 
    typeify (subst s\<^sub>2 t\<^sub>2') = t\<^sub>1 \<and> dom s\<^sub>2 = vs''' - vs'' \<and> subst_vars s\<^sub>2 \<subseteq> tvarst e\<^sub>2 \<union> subst_vars \<Gamma> \<and> 
      s\<^sub>2 unifies\<^sub>\<kappa> con\<^sub>2 \<and> valid_ty_subst s\<^sub>2 \<and> idempotent s\<^sub>2" by fastforce
  from tcn_app have FV: "?v \<notin> vs" by simp
  from tcn_app S1 S2 have SV: "subst_vars s\<^sub>1 \<subseteq> vs \<union> subst_vars \<Gamma> \<and> 
    subst_vars s\<^sub>2 \<subseteq> vs \<union> subst_vars \<Gamma>" by auto
  with tcn_app have SV: "subst_vars s\<^sub>1 \<subseteq> vs \<and> subst_vars s\<^sub>2 \<subseteq> vs" by auto
  from S1 S2 have DSS: "dom s\<^sub>1 \<inter> dom s\<^sub>2 = {}" by auto
  from tcn_app TC1 S1 have "valid_ty_uexpr t\<^sub>1' \<and> valid_ty_subst s\<^sub>1" by auto
  hence VTS1: "valid_ty_uexpr (subst s\<^sub>1 t\<^sub>1')" by simp
  from tcn_app TC2 S2 have "valid_ty_uexpr t\<^sub>2' \<and> valid_ty_subst s\<^sub>2" by auto
  hence VTS2: "valid_ty_uexpr (subst s\<^sub>2 t\<^sub>2')" by simp
  from tcn_app have "tvars (Arrow t\<^sub>1 t\<^sub>2) \<subseteq> tvarst e\<^sub>1 \<union> \<Union> (tvars ` ran (map_option typeify \<circ> \<Gamma>))" 
    by (metis tcn_tvars)
  with tcn_app have TV2: "tvars t\<^sub>1 \<subseteq> tvarst e\<^sub>1 \<union> subst_vars \<Gamma> \<and> tvars t\<^sub>2 \<subseteq> tvarst e\<^sub>1 \<union> subst_vars \<Gamma>" 
    by (simp add: valid_ty_subst_def subst_vars_def)
  with tcn_app have VT: "tvars t\<^sub>1 \<subseteq> vs \<and> tvars t\<^sub>2 \<subseteq> vs" by auto
  hence VUT: "uvars (untypeify t\<^sub>1) \<subseteq> vs \<and> uvars (untypeify t\<^sub>2) \<subseteq> vs" by simp
  let ?s = "extend_subst ?v (untypeify t\<^sub>2) (combine_subst s\<^sub>1 s\<^sub>2)"
  from S1 have D1: "dom s\<^sub>1 = vs'' - insert ?v vs" by simp
  from S2 E have D2: "dom s\<^sub>2 = vs' - vs''" by simp
  with V1 V2 D1 have D3: "dom (combine_subst s\<^sub>1 s\<^sub>2) = vs' - insert ?v vs" by auto
  with FV V1 V2 have A: "dom ?s = vs' - vs" by auto
  from tcn_app TC1 S1 have VS1: "valid_ty_hexpr e\<^sub>1' \<and> valid_ty_subst s\<^sub>1" by auto
  moreover from S1 have "liquify (solidify (hsubst s\<^sub>1 e\<^sub>1')) = liquify e\<^sub>1" by simp
  ultimately have H1: "hsubst s\<^sub>1 e\<^sub>1' = liquify e\<^sub>1" by simp
  from tcn_app TC2 S2 have VS2: "valid_ty_hexpr e\<^sub>2' \<and> valid_ty_subst s\<^sub>2" by auto
  moreover from S2 have "liquify (solidify (hsubst s\<^sub>2 e\<^sub>2')) = liquify e\<^sub>2" by simp
  ultimately have H2: "hsubst s\<^sub>2 e\<^sub>2' = liquify e\<^sub>2" by simp
  from tcn_app have VG: "?v \<notin> subst_vars \<Gamma>" by auto 
  with tcn_app TC1 have VE1: "?v \<notin> htvars e\<^sub>1'" by simp
  from tcn_app TC1 TC2 V1 VG have VE2: "?v \<notin> htvars e\<^sub>2'" by simp
  from tcn_app TC1 have "htvars e\<^sub>1' \<subseteq> vs'' - insert ?v vs" by simp
  with D2 have HV: "dom s\<^sub>2 \<inter> htvars e\<^sub>1' = {}" by auto
  from tcn_app have "(vs'' - insert ?v vs) \<inter> tvarst e\<^sub>2 = {}" by auto
  with S1 H1 H2 VE1 VE2 HV have "solidify (hsubst ?s e\<^sub>1') = e\<^sub>1 \<and> solidify (hsubst ?s e\<^sub>2') = e\<^sub>2" 
    by simp
  hence B: "solidify (hsubst ?s (HApp e\<^sub>1' e\<^sub>2')) = TApp e\<^sub>1 e\<^sub>2" by simp
  from VT D1 have VS1: "dom s\<^sub>1 \<inter> tvars t\<^sub>2 = {}" by auto
  from V1 VT D2 have VS2: "dom s\<^sub>2 \<inter> tvars t\<^sub>2 = {}" by auto
  with VS1 have C: "typeify (subst ?s (Var ?v)) = t\<^sub>2" by simp
  from S1 S2 have "subst_vars s\<^sub>1 \<subseteq> tvarst e\<^sub>1 \<union> subst_vars \<Gamma> \<union> tvarst e\<^sub>2 \<and> 
    subst_vars s\<^sub>2 - dom s\<^sub>1 \<subseteq> tvarst e\<^sub>1 \<union> subst_vars \<Gamma> \<union> tvarst e\<^sub>2" by blast
  with DSS D3 VS1 VS2 TV2 have D: "subst_vars ?s \<subseteq> tvarst (TApp e\<^sub>1 e\<^sub>2) \<union> subst_vars \<Gamma>" by auto
  from FV SV have VCS: "?v \<notin> subst_vars s\<^sub>1 \<and> ?v \<notin> subst_vars s\<^sub>2" by auto
  from D2 SV V1 have D2S1: "dom s\<^sub>2 \<inter> subst_vars s\<^sub>1 = {}" by auto
  with S1 DSS D3 VCS have UC1: "?s unifies\<^sub>\<kappa> con\<^sub>1" by simp
  from S2 D3 VCS DSS have UC2: "?s unifies\<^sub>\<kappa> con\<^sub>2" by simp
  from S1 have "tvars (typeify (subst s\<^sub>1 t\<^sub>1')) = tvars t\<^sub>1 \<union> tvars t\<^sub>2" by simp
  with VTS1 have VST1: "uvars (subst s\<^sub>1 t\<^sub>1') = tvars t\<^sub>1 \<union> tvars t\<^sub>2" by simp
  with FV VT have "?v \<notin> uvars (subst s\<^sub>1 t\<^sub>1')" by auto
  with S1 VCS have VT1': "?v \<notin> uvars t\<^sub>1'" by auto
  from S2 have "tvars (typeify (subst s\<^sub>2 t\<^sub>2')) = tvars t\<^sub>1" by simp
  with VTS2 have VST2: "uvars (subst s\<^sub>2 t\<^sub>2') = tvars t\<^sub>1" by simp
  with FV VT have "?v \<notin> uvars (subst s\<^sub>2 t\<^sub>2')" by auto
  with V1 D2 S2 VCS have VT2': "?v \<notin> uvars t\<^sub>2'" by auto
  from VST1 VT have "uvars (subst s\<^sub>1 t\<^sub>1') \<subseteq> vs" by simp
  hence "uvars t\<^sub>1' \<subseteq> vs \<union> dom s\<^sub>1" by (metis vars_subst_inv)
  moreover from D2 V1 DSS have "dom s\<^sub>2 \<inter> (vs \<union> dom s\<^sub>1) = {}" by auto
  ultimately have D2V1: "dom s\<^sub>2 \<inter> uvars t\<^sub>1' = {}" by auto
  from VST2 VT have "uvars (subst s\<^sub>2 t\<^sub>2') \<subseteq> vs" by simp
  moreover from D1 V2 DSS have "dom s\<^sub>1 \<inter> (vs \<union> dom s\<^sub>2) = {}" by auto
  ultimately have D1V2: "dom s\<^sub>1 \<inter> uvars (subst s\<^sub>2 t\<^sub>2') = {}" by auto
  from S1 S2 have "untypeify (typeify (subst s\<^sub>1 t\<^sub>1')) = 
    untypeify (typeify (Ctor ''Arrow'' [subst s\<^sub>2 t\<^sub>2', untypeify t\<^sub>2]))" by simp
  with VTS1 VTS2 VT1' VT2' UC1 UC2 VS1 VS2 D2V1 D1V2 have F: 
    "?s unifies\<^sub>\<kappa> con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1', Ctor ''Arrow'' [t\<^sub>2', Var ?v])]" 
      by (simp add: expand_extend_subst)
  from FV VT have "?v \<notin> tvars t\<^sub>2" by auto
  with DSS VCS V1 D1 D2 S1 S2 D2S1 have G: "idempotent ?s" by simp
  from S1 S2 have "valid_ty_subst ?s" by simp
  with E A B C D F G show ?case by blast
qed auto

lemma typecheck_fails [simp]: "typecheck e = None \<Longrightarrow> 
  \<nexists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> tvarst e\<^sub>t = {} \<and> e = erase e\<^sub>t"
proof                              
  assume "typecheck e = None"
  then obtain e' tt vs' con where X: "typecheck' Map.empty {} e = (e', tt, vs', con) \<and> 
    unify con = None" by (auto split: prod.splits option.splits)
  assume "\<exists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> tvarst e\<^sub>t = {} \<and> e = erase e\<^sub>t"
  then obtain e\<^sub>t t where Y: "(map_option typeify \<circ> Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> tvarst e\<^sub>t = {} \<and> 
    e = erase e\<^sub>t" by fastforce
  have Z: "subst_vars Map.empty \<subseteq> {}" by simp
  have "valid_ty_subst Map.empty \<and> finite {}" by simp
  with X Y Z have "\<exists>s. solidify (hsubst s e') = e\<^sub>t \<and> typeify (subst s tt) = t \<and> dom s = vs' - {} \<and> 
    subst_vars s \<subseteq> tvarst e\<^sub>t \<union> subst_vars Map.empty \<and> s unifies\<^sub>\<kappa> con \<and> valid_ty_subst s \<and> 
      idempotent s" using typecheck_fails' by blast
  then obtain s where "s unifies\<^sub>\<kappa> con \<and> idempotent s" by blast
  hence "\<exists>s'. unify con = Some s' \<and> s specializes s'" by simp
  with X show "False" by simp
qed

lemma [simp]: "value (erase e) = valt e"
  by (induction e) simp_all

lemma [simp]: "all_vars (erase e) = all_varst e"
  by (induction e) simp_all

lemma [simp]: "erase (subst_vart x y e) = subst_var x y (erase e)"
  by (induction e) simp_all

lemma [simp]: "erase (substt x e' e) = subst\<^sub>s x (erase e') (erase e)"
  by (induction x e' e rule: substt.induct) (simp_all add: Let_def)

theorem completeness [simp]: "e \<Down>\<^sub>t v \<Longrightarrow> erase e \<Down> erase v"
  by (induction e v rule: evalt.induct) simp_all

end