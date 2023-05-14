theory Typechecking
  imports TypedLanguage UnifiableType
begin

primrec hsubst :: "subst \<Rightarrow> uterm expr\<^sub>s \<Rightarrow> uterm expr\<^sub>s" where
  "hsubst sub (Var\<^sub>s x) = Var\<^sub>s x"
| "hsubst sub (Const\<^sub>s k) = Const\<^sub>s k"
| "hsubst sub (Lam\<^sub>s x t e) = Lam\<^sub>s x (subst sub t) (hsubst sub e)"
| "hsubst sub (App\<^sub>s e\<^sub>1 e\<^sub>2) = App\<^sub>s (hsubst sub e\<^sub>1) (hsubst sub e\<^sub>2)"

primrec erase :: "'a expr\<^sub>s \<Rightarrow> unit expr\<^sub>s" where
  "erase (Var\<^sub>s x) = Var\<^sub>s x"
| "erase (Const\<^sub>s k) = Const\<^sub>s k"
| "erase (Lam\<^sub>s x t e) = Lam\<^sub>s x () (erase e)"
| "erase (App\<^sub>s e\<^sub>1 e\<^sub>2) = App\<^sub>s (erase e\<^sub>1) (erase e\<^sub>2)"

primrec htvars :: "uterm expr\<^sub>s \<Rightarrow> var set" where
  "htvars (Var\<^sub>s x) = {}"
| "htvars (Const\<^sub>s k) = {}"
| "htvars (Lam\<^sub>s x t e) = uvars t \<union> htvars e"
| "htvars (App\<^sub>s e\<^sub>1 e\<^sub>2) = htvars e\<^sub>1 \<union> htvars e\<^sub>2"

primrec typecheck' :: "subst \<Rightarrow> var set \<Rightarrow> 'a expr\<^sub>s \<Rightarrow> uterm expr\<^sub>s \<times> uterm \<times> var set \<times> constraint" 
    where
  "typecheck' \<Gamma> vs (Var\<^sub>s x) = (case \<Gamma> x of 
      Some t \<Rightarrow> (Var\<^sub>s x, t, vs, []) 
    | None \<Rightarrow> (Var\<^sub>s x, Num\<^sub>\<tau>, vs, fail))"
| "typecheck' \<Gamma> vs (Const\<^sub>s k) = (Const\<^sub>s k, Num\<^sub>\<tau>, vs, [])"
| "typecheck' \<Gamma> vs (Lam\<^sub>s x t e) = (
    let v = fresh vs
    in let (e', t, vs', con) = typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e
    in (Lam\<^sub>s x (Var v) e', Arrow\<^sub>\<tau> (Var v) t, vs', con))"
| "typecheck' \<Gamma> vs (App\<^sub>s e\<^sub>1 e\<^sub>2) = (
    let v = fresh vs
    in let (e\<^sub>1', t\<^sub>1, vs', con\<^sub>1) = typecheck' \<Gamma> (insert v vs) e\<^sub>1 
    in let (e\<^sub>2', t\<^sub>2, vs'', con\<^sub>2) = typecheck' \<Gamma> vs' e\<^sub>2 
    in (App\<^sub>s e\<^sub>1' e\<^sub>2', Var v, vs'', con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1, Arrow\<^sub>\<tau> t\<^sub>2 (Var v))]))"

primrec solidify :: "uterm expr\<^sub>s \<Rightarrow> ty expr\<^sub>s" where
  "solidify (Var\<^sub>s x) = Var\<^sub>s x"
| "solidify (Const\<^sub>s k) = Const\<^sub>s k"
| "solidify (Lam\<^sub>s x t e) = Lam\<^sub>s x (to_type t) (solidify e)"
| "solidify (App\<^sub>s e\<^sub>1 e\<^sub>2) = App\<^sub>s (solidify e\<^sub>1) (solidify e\<^sub>2)"

primrec liquify :: "ty expr\<^sub>s \<Rightarrow> uterm expr\<^sub>s" where
  "liquify (Var\<^sub>s x) = Var\<^sub>s x"
| "liquify (Const\<^sub>s k) = Const\<^sub>s k"
| "liquify (Lam\<^sub>s x t e) = Lam\<^sub>s x (to_unifiable t) (liquify e)"
| "liquify (App\<^sub>s e\<^sub>1 e\<^sub>2) = App\<^sub>s (liquify e\<^sub>1) (liquify e\<^sub>2)"

primrec partial_solidify :: "var set \<Rightarrow> uterm expr\<^sub>s \<Rightarrow> uterm expr\<^sub>s" where
  "partial_solidify vs (Var\<^sub>s x) = Var\<^sub>s x"
| "partial_solidify vs (Const\<^sub>s k) = Const\<^sub>s k"
| "partial_solidify vs (Lam\<^sub>s x t e) = Lam\<^sub>s x (eliminate_vars vs t) (partial_solidify vs e)"
| "partial_solidify vs (App\<^sub>s e\<^sub>1 e\<^sub>2) = App\<^sub>s (partial_solidify vs e\<^sub>1) (partial_solidify vs e\<^sub>2)"

fun typecheck :: "'a expr\<^sub>s \<rightharpoonup> ty expr\<^sub>s \<times> ty" where
  "typecheck e = (
    let (e', t, vs, con) = typecheck' Map.empty {} e
    in case unify con of 
        Some sub \<Rightarrow> Some (solidify (hsubst sub e'), to_type (subst sub t))
      | None \<Rightarrow> None)"

primrec valid_ty_hexpr :: "uterm expr\<^sub>s \<Rightarrow> bool" where
  "valid_ty_hexpr (Var\<^sub>s x) = True"
| "valid_ty_hexpr (Const\<^sub>s k) = True"
| "valid_ty_hexpr (Lam\<^sub>s x t e) = (valid_ty_term t \<and> valid_ty_hexpr e)"
| "valid_ty_hexpr (App\<^sub>s e\<^sub>1 e\<^sub>2) = (valid_ty_hexpr e\<^sub>1 \<and> valid_ty_hexpr e\<^sub>2)"

lemma typecheck_induct [consumes 1, case_names Var\<^sub>sS Var\<^sub>sN Const\<^sub>s Lam\<^sub>s App\<^sub>s]: "
  typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> 
  (\<And>\<Gamma> vs t x. \<Gamma> x = Some t \<Longrightarrow> P \<Gamma> vs (Var\<^sub>s x) (Var\<^sub>s x) t vs []) \<Longrightarrow> 
  (\<And>\<Gamma> vs x. \<Gamma> x = None \<Longrightarrow> P \<Gamma> vs (Var\<^sub>s x) (Var\<^sub>s x) Num\<^sub>\<tau> vs fail) \<Longrightarrow> 
  (\<And>\<Gamma> vs k. P \<Gamma> vs (Const\<^sub>s k) (Const\<^sub>s k) Num\<^sub>\<tau> vs []) \<Longrightarrow> 
  (\<And>\<Gamma> vs vs' con x u e\<^sub>1 e\<^sub>1' t' v. v = fresh vs \<Longrightarrow> typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>1 = 
    (e\<^sub>1', t', vs', con) \<Longrightarrow> P (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>1 e\<^sub>1' t' vs' con \<Longrightarrow> 
      P \<Gamma> vs (Lam\<^sub>s x u e\<^sub>1) (Lam\<^sub>s x (Var v) e\<^sub>1') (Arrow\<^sub>\<tau> (Var v) t') vs' con) \<Longrightarrow> 
  (\<And>\<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2. v = fresh vs \<Longrightarrow> 
    typecheck' \<Gamma> (insert v vs) e\<^sub>1 = (e\<^sub>1', t\<^sub>1, vs'', con\<^sub>1) \<Longrightarrow> 
      typecheck' \<Gamma> vs'' e\<^sub>2 = (e\<^sub>2', t\<^sub>2, vs', con\<^sub>2) \<Longrightarrow> P \<Gamma> (insert v vs) e\<^sub>1 e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 \<Longrightarrow> 
        P \<Gamma> vs'' e\<^sub>2 e\<^sub>2' t\<^sub>2 vs' con\<^sub>2 \<Longrightarrow> P \<Gamma> vs (App\<^sub>s e\<^sub>1 e\<^sub>2) (App\<^sub>s e\<^sub>1' e\<^sub>2') (Var v) vs' 
          (con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1, Arrow\<^sub>\<tau> t\<^sub>2 (Var v))])) \<Longrightarrow> 
    P \<Gamma> vs e e' t vs' con"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (auto simp add: Let_def split: option.splits prod.splits)

lemma [simp]: "valid_ty_hexpr (liquify e)"
  by (induction e) simp_all

lemma [simp]: "x \<notin> htvars e \<Longrightarrow> hsubst [x \<mapsto> t] e = e"
  by (induction e) simp_all

lemma [simp]: "hsubst (extend_subst x t s) e = hsubst s (hsubst [x \<mapsto> t] e)"
  by (induction e) (simp_all only: hsubst.simps expand_extend_subst comp_def)

lemma [simp]: "solidify (liquify e) = e"
  by (induction e) simp_all

lemma [simp]: "valid_ty_hexpr e \<Longrightarrow> htvars e = {} \<Longrightarrow> liquify (solidify e) = e"
  by (induction e) simp_all

lemma [simp]: "erase (solidify (hsubst sub e)) = erase (solidify e)"
  by (induction e) simp_all

lemma [simp]: "htvars t = {} \<Longrightarrow> partial_solidify vs t = t"
  by (induction t) simp_all

lemma [simp]: "x \<notin> htvars t \<Longrightarrow> partial_solidify (insert x vs) t = partial_solidify vs t"
  by (induction t) simp_all

lemma [simp]: "valid_ty_subst sub \<Longrightarrow> valid_ty_hexpr e \<Longrightarrow> valid_ty_hexpr (hsubst sub e)"
  by (induction e) simp_all

lemma htvars_hsubst [simp]: "htvars (hsubst sub e) \<subseteq> htvars e - dom sub \<union> subst_vars sub"
proof (induction e)
  case (Lam\<^sub>s x t e)
  moreover have "uvars (subst sub t) \<subseteq> uvars t - dom sub \<union> subst_vars sub" by simp
  ultimately show ?case by fastforce
qed auto

lemma [simp]: "dom sub \<inter> htvars e = {} \<Longrightarrow> hsubst sub e = e"
proof (induction e)
  case (Lam\<^sub>s x t e)
  moreover hence "dom sub \<inter> uvars t = {}" by auto
  ultimately show ?case by auto
qed auto

lemma [simp]: "hsubst (combine_subst s t) e = hsubst s (hsubst t e)"
  by (induction e) simp_all

lemma [elim]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_term t"
  by (induction rule: typecheck_induct) auto

lemma [elim]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_hexpr e'"
  by (induction rule: typecheck_induct) auto

lemma typecheck_succeeds [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> 
  valid_ty_subst \<Gamma> \<Longrightarrow> unify con = Some sub' \<Longrightarrow> sub specializes sub' \<Longrightarrow>
    map_option (to_type \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>t solidify (hsubst sub e') : to_type (subst sub t)"
proof (induction arbitrary: sub' rule: typecheck_induct)
  case (Var\<^sub>sS \<Gamma> vs t x)
  thus ?case by simp
next
  case (Lam\<^sub>s \<Gamma> vs vs' con x u e\<^sub>1 e\<^sub>1' t' v)
  hence "valid_ty_subst (\<Gamma>(x \<mapsto> Var v))" by simp
  with Lam\<^sub>s have "map_option (to_type \<circ> subst sub) \<circ> \<Gamma>(x \<mapsto> Var v) \<turnstile>\<^sub>t solidify (hsubst sub e\<^sub>1') : 
      to_type (subst sub t')" by blast
  hence "map_option (to_type \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>t solidify (hsubst sub (Lam\<^sub>s x (Var v) e\<^sub>1')) :
    to_type (subst sub (Arrow\<^sub>\<tau> (Var v) t'))" by simp
  thus ?case by blast
next
  case (App\<^sub>s \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2)
  then obtain s\<^sub>2 where S2: "unify (con\<^sub>1 @ con\<^sub>2) = Some s\<^sub>2 \<and> sub' specializes s\<^sub>2" by fastforce
  then obtain s\<^sub>3 where S3: "unify con\<^sub>1 = Some s\<^sub>3 \<and> s\<^sub>2 specializes s\<^sub>3" by fastforce
  with App\<^sub>s S2 have "sub specializes s\<^sub>3" by auto
  with App\<^sub>s S2 S3 have T: "map_option (to_type \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>t solidify (hsubst sub e\<^sub>1') : 
    to_type (subst sub t\<^sub>1)" by blast
  from App\<^sub>s have "sub' unifies\<^sub>\<kappa> (con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1, Arrow\<^sub>\<tau> t\<^sub>2 (Var v))])" 
    by (metis unify_some) 
  hence "sub' unifies t\<^sub>1 and Arrow\<^sub>\<tau> t\<^sub>2 (Var v)" by simp
  with App\<^sub>s have X: "sub unifies t\<^sub>1 and Arrow\<^sub>\<tau> t\<^sub>2 (Var v)" by fastforce
  from S2 obtain s\<^sub>4 where S4: "unify con\<^sub>2 = Some s\<^sub>4 \<and> s\<^sub>2 specializes s\<^sub>4" 
    using unify_append_snd by blast
  with App\<^sub>s S2 have "sub specializes s\<^sub>4" by auto
  with App\<^sub>s S4 have "map_option (to_type \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>t solidify (hsubst sub e\<^sub>2') : 
    to_type (subst sub t\<^sub>2)" by blast
  with T X have "map_option (to_type \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>t solidify (hsubst sub (App\<^sub>s e\<^sub>1' e\<^sub>2')) : 
    to_type (subst sub (Var v))" by simp
  thus ?case by blast
qed simp_all

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> Map.empty \<turnstile>\<^sub>t e\<^sub>t : t"
proof -
  assume "typecheck e = Some (e\<^sub>t, t)"
  then obtain e' tt vs con sub where T: "typecheck' Map.empty {} e = (e', tt, vs, con) \<and>
    unify con = Some sub \<and> e\<^sub>t = solidify (hsubst sub e') \<and> t = to_type (subst sub tt)" 
      by (auto split: option.splits prod.splits)
  moreover hence "map_option (to_type \<circ> subst sub) \<circ> Map.empty \<turnstile>\<^sub>t solidify (hsubst sub e') : 
    to_type (subst sub tt)" by (metis typecheck_succeeds valid_empty_subst specializes_refl)
  moreover from T have "valid_ty_term tt" and "valid_ty_hexpr e'" by auto
  ultimately show "Map.empty \<turnstile>\<^sub>t e\<^sub>t : t" by simp
qed

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> e = erase (solidify e')"
  by (induction rule: typecheck_induct) auto

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> e = erase e\<^sub>t"
  by (auto split: option.splits prod.splits)

lemma [dest]: "erase e\<^sub>t = Var\<^sub>s x \<Longrightarrow> e\<^sub>t = Var\<^sub>s x"
  by (induction e\<^sub>t) simp_all

lemma [dest]: "erase e\<^sub>t = Lam\<^sub>s x u e \<Longrightarrow> \<exists>t e\<^sub>t'. e\<^sub>t = Lam\<^sub>s x t e\<^sub>t' \<and> e = erase e\<^sub>t'"
  by (induction e\<^sub>t) simp_all

lemma [dest]: "erase e\<^sub>t = App\<^sub>s e\<^sub>1 e\<^sub>2 \<Longrightarrow> \<exists>e\<^sub>1' e\<^sub>2'. e\<^sub>t = App\<^sub>s e\<^sub>1' e\<^sub>2' \<and> e\<^sub>1 = erase e\<^sub>1'\<and> e\<^sub>2 = erase e\<^sub>2'"
  by (induction e\<^sub>t) simp_all

lemma vars_expand: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> vs \<subseteq> vs'"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (simp_all add: Let_def split: option.splits prod.splits, fastforce+)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> finite vs' = finite vs"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (simp_all add: Let_def split: option.splits prod.splits)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> finite vs \<Longrightarrow> htvars e' \<subseteq> vs' - vs"
proof (induction rule: typecheck_induct)
  case (Lam\<^sub>s \<Gamma> vs vs' con x u e\<^sub>1 e\<^sub>1' t' v)
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

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> finite vs \<Longrightarrow> 
  uvars t' \<subseteq> vs' - vs \<union> subst_vars \<Gamma>"
proof (induction rule: typecheck_induct)
  case (Lam\<^sub>s \<Gamma> vs vs' con x u e\<^sub>1 e\<^sub>1' t' v)
  moreover hence "insert v vs \<subseteq> vs'" by (metis vars_expand)
  ultimately show ?case by auto
next
  case (App\<^sub>s \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2)
  moreover hence "insert v vs \<subseteq> vs''" by (metis vars_expand)
  moreover from App\<^sub>s have "vs'' \<subseteq> vs'" by (metis vars_expand)
  ultimately show ?case by auto
qed auto

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> x \<in> vs \<Longrightarrow> finite vs \<Longrightarrow>
  x \<notin> subst_vars \<Gamma> \<Longrightarrow> x \<notin> uvars t'"
proof -
  assume "typecheck' \<Gamma> vs e = (e', t', vs', con)"
     and "finite vs"
  hence "uvars t' \<subseteq> vs' - vs \<union> subst_vars \<Gamma>" by simp
  moreover assume "x \<in> vs" and "x \<notin> subst_vars \<Gamma>" 
  ultimately show "x \<notin> uvars t'" by auto
qed

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> finite vs \<Longrightarrow> 
  constr_vars con \<subseteq> vs' - vs \<union> subst_vars \<Gamma>"
proof (induction rule: typecheck_induct)
  case (Lam\<^sub>s \<Gamma> vs vs' con x u e\<^sub>1 e\<^sub>1' t' v)
  moreover hence "insert v vs \<subseteq> vs'" by (metis vars_expand)
  ultimately show ?case by auto
next
  case (App\<^sub>s \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2)
  moreover hence V1: "insert v vs \<subseteq> vs''" by (metis vars_expand)
  moreover from App\<^sub>s have V2: "vs'' \<subseteq> vs'" by (metis vars_expand)
  ultimately have V: "v \<in> vs' \<and> v \<notin> vs" by auto
  from App\<^sub>s have "constr_vars con\<^sub>1 \<subseteq> vs'' - insert v vs \<union> subst_vars \<Gamma>" by simp
  with V2 have C1: "constr_vars con\<^sub>1 \<subseteq> vs' - vs \<union> subst_vars \<Gamma>" by auto
  from App\<^sub>s have "constr_vars con\<^sub>2 \<subseteq> vs' - vs'' \<union> subst_vars \<Gamma>" by simp
  with V1 have C2: "constr_vars con\<^sub>2 \<subseteq> vs' - vs \<union> subst_vars \<Gamma>" by auto
  from App\<^sub>s have "uvars t\<^sub>1 \<subseteq> vs'' - insert v vs \<union> subst_vars \<Gamma>" by simp
  with V2 have T1: "uvars t\<^sub>1 \<subseteq> vs' - vs \<union> subst_vars \<Gamma>" by auto
  from App\<^sub>s have "uvars t\<^sub>2 \<subseteq> vs' - vs'' \<union> subst_vars \<Gamma>" by simp
  with V1 have "uvars t\<^sub>2 \<subseteq> vs' - vs \<union> subst_vars \<Gamma>" by auto
  with V C1 C2 T1 show ?case by simp
qed simp_all

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> x \<in> vs \<Longrightarrow> finite vs \<Longrightarrow>
  x \<notin> subst_vars \<Gamma> \<Longrightarrow> x \<notin> constr_vars con"
proof -
  assume "typecheck' \<Gamma> vs e = (e', t', vs', con)"
     and "finite vs"
  hence "constr_vars con \<subseteq> vs' - vs \<union> subst_vars \<Gamma>" by simp
  moreover assume "x \<in> vs" and "x \<notin> subst_vars \<Gamma>" 
  ultimately show "x \<notin> constr_vars con" by auto
qed

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
  case (Lam\<^sub>s z u e)
  let ?v = "fresh vs"
  from Lam\<^sub>s have F: "fresh vs \<noteq> y" using fresh_is_fresh by blast
  obtain e'' tt' vs'' con' where T: "typecheck' (\<Gamma>(x \<mapsto> Var y, z \<mapsto> Var ?v)) (insert ?v vs) e = 
    (e'', tt', vs'', con')" by (metis prod_cases4)
  show ?case
  proof (cases "x = z")
    case True
    from T Lam\<^sub>s(2) have E: "e' = Lam\<^sub>s z (Var ?v) e'' \<and> tt = Arrow\<^sub>\<tau> (Var ?v) tt' \<and> 
      vs'' = vs' \<and> con' = con" by (simp only: typecheck'.simps Let_def split: prod.splits) simp
    from T True E have T': "typecheck' (\<Gamma>(z \<mapsto> Var ?v)) (insert ?v vs) e = (e'', tt', vs', con)" 
      by simp
    from Lam\<^sub>s(4) F have "y \<notin> subst_vars (\<Gamma>(z \<mapsto> Var ?v))" 
      by (auto simp add: subst_vars_def ran_def)
    with Lam\<^sub>s F E T' True T have "typecheck' (\<Gamma>(x \<mapsto> t')) vs (Lam\<^sub>s z u e) =
      (hsubst [y \<mapsto> t'] e', subst [y \<mapsto> t'] tt, vs', constr_subst y t' con)" 
        by (simp add: Let_def split: if_splits prod.splits)
    thus ?thesis by blast
  next
    case False
    from Lam\<^sub>s have "typecheck' (\<Gamma>(x \<mapsto> Var y)) vs (Lam\<^sub>s z u e) = (e', tt, vs', con)" by blast
    with T have E: "e' = Lam\<^sub>s z (Var ?v) e'' \<and> tt = Arrow\<^sub>\<tau> (Var ?v) tt' \<and> vs'' = vs' \<and> 
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
    with E F have "typecheck' (\<Gamma>(x \<mapsto> t')) vs (Lam\<^sub>s z u e) =
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
  ultimately have E: "e' = App\<^sub>s e\<^sub>1' e\<^sub>2' \<and> tt = Var ?v \<and> vs''' = vs' \<and> 
    con = con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1, Arrow\<^sub>\<tau> t\<^sub>2 (Var ?v))]" by (auto simp add: Let_def)
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

lemma typecheck_fails' [simp]: "map_option to_type \<circ> \<Gamma> \<turnstile>\<^sub>t e\<^sub>t : t \<Longrightarrow> finite vs \<Longrightarrow> 
  subst_vars \<Gamma> \<subseteq> vs \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> typecheck' \<Gamma> vs (erase e\<^sub>t) = (e', tt, vs', con) \<Longrightarrow> 
  \<exists>s. partial_solidify vs (hsubst s e') = liquify e\<^sub>t \<and> 
  eliminate_vars vs (subst s tt) = to_unifiable t \<and> dom s = vs' - vs \<and> 
  subst_vars s = {} \<and> s unifies\<^sub>\<kappa> eliminate_vars_constr vs con \<and> valid_ty_subst s \<and> idempotent s"
proof (induction "map_option to_type \<circ> \<Gamma>" e\<^sub>t t arbitrary: \<Gamma> vs e' tt vs' con rule: typing\<^sub>t.induct)
  case (tc\<^sub>t_lam x t\<^sub>1 e t\<^sub>2)
  let ?v = "fresh vs"
  obtain e'' t' vs'' con' where T: "typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) (erase e) = 
    (e'', t', vs'', con')" by (metis prod_cases4)
  with tc\<^sub>t_lam have E: "e' = Lam\<^sub>s x (Var ?v) e'' \<and> tt = Arrow\<^sub>\<tau> (Var ?v) t' \<and> vs'' = vs' \<and> 
    con' = con" by (simp add: Let_def)
  from tc\<^sub>t_lam have "subst_vars \<Gamma> \<subseteq> insert ?v vs" by auto
  hence X: "subst_vars (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1)) \<subseteq> insert ?v vs" by simp
  have Y: "(map_option to_type \<circ> \<Gamma>)(x \<mapsto> t\<^sub>1) = map_option to_type \<circ> (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1))" by simp
  from tc\<^sub>t_lam have Z: "valid_ty_subst (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1))" by simp
  from tc\<^sub>t_lam T have TC: "typecheck' (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1)) (insert ?v vs) (erase e) = 
    (hsubst [?v \<mapsto> to_unifiable t\<^sub>1] e'', subst [?v \<mapsto> to_unifiable t\<^sub>1] t', vs'', 
     constr_subst ?v (to_unifiable t\<^sub>1) con')" by simp
  from tc\<^sub>t_lam have "finite (insert ?v vs)" by simp
  with tc\<^sub>t_lam X Y Z TC obtain s where S: "
    partial_solidify (insert ?v vs) (hsubst s (hsubst [?v \<mapsto> to_unifiable t\<^sub>1] e'')) = liquify e \<and> 
    eliminate_vars (insert ?v vs) (subst s (subst [?v \<mapsto> to_unifiable t\<^sub>1] t')) = to_unifiable t\<^sub>2 \<and>
    s unifies\<^sub>\<kappa> eliminate_vars_constr (insert ?v vs) (constr_subst ?v (to_unifiable t\<^sub>1) con') \<and> 
    dom s = vs'' - insert ?v vs \<and> subst_vars s = {} \<and> valid_ty_subst s \<and> idempotent s" by meson
  from tc\<^sub>t_lam have "subst_vars (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1)) \<subseteq> vs" by simp
  moreover from tc\<^sub>t_lam have FV: "?v \<notin> vs" by simp
  ultimately have "?v \<notin> subst_vars (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1))" by blast
  with tc\<^sub>t_lam TC have VCS: "?v \<notin> constr_vars (constr_subst ?v (to_unifiable t\<^sub>1) con')" by simp
  have "htvars (hsubst [?v \<mapsto> to_unifiable t\<^sub>1] e') \<subseteq> 
    htvars e' - dom [?v \<mapsto> to_unifiable t\<^sub>1] \<union> subst_vars [?v \<mapsto> to_unifiable t\<^sub>1]" 
      by (metis htvars_hsubst)
  hence "htvars (hsubst [?v \<mapsto> to_unifiable t\<^sub>1] e') \<subseteq> htvars e' - {?v}" by simp
  moreover have "htvars (hsubst s (hsubst [?v \<mapsto> to_unifiable t\<^sub>1] e')) \<subseteq> 
    htvars (hsubst [?v \<mapsto> to_unifiable t\<^sub>1] e') - dom s \<union> subst_vars s" by simp
  ultimately have "htvars (hsubst s (hsubst [?v \<mapsto> to_unifiable t\<^sub>1] e')) \<subseteq> 
    htvars e' - {?v} - dom s \<union> subst_vars s" by blast
  with S have "?v \<notin> htvars (hsubst (extend_subst ?v (to_unifiable t\<^sub>1) s) e')" by auto
  with E S VCS have A: "partial_solidify vs (hsubst (extend_subst ?v (to_unifiable t\<^sub>1) s) e') = 
    liquify (Lam\<^sub>s x t\<^sub>1 e)" by simp
  from tc\<^sub>t_lam S have U: "?v \<notin> dom s" by auto
  with S have B: "idempotent (extend_subst ?v (to_unifiable t\<^sub>1) s)" by simp
  from S E FV have "s unifies\<^sub>\<kappa> constr_subst ?v (to_unifiable t\<^sub>1) (eliminate_vars_constr vs con)" 
    by simp
  hence C: "extend_subst ?v (to_unifiable t\<^sub>1) s unifies\<^sub>\<kappa> eliminate_vars_constr vs con" by simp
  from E TC have "insert ?v vs \<subseteq> vs'" by (metis vars_expand)
  with tc\<^sub>t_lam have "insert ?v (vs' - insert ?v vs) = vs' - vs" by auto
  with S E have D: "dom (extend_subst ?v (to_unifiable t\<^sub>1) s) = vs' - vs" by simp
  have VS: "uvars (subst s (to_unifiable t\<^sub>1)) \<subseteq> uvars (to_unifiable t\<^sub>1) - dom s \<union> subst_vars s" 
    by (metis uvars_subst)
  from S U VS have F: "subst_vars (extend_subst ?v (to_unifiable t\<^sub>1) s) = {}" by auto
  from S have AR: "eliminate_vars (insert ?v vs) 
    (subst (map_option (subst [fresh vs \<mapsto> to_unifiable t\<^sub>1]) \<circ> s) 
    (subst [fresh vs \<mapsto> to_unifiable t\<^sub>1] t')) = to_unifiable t\<^sub>2" by (metis subst_absorb_no_ran)
  from U have SV: "s ?v = None" by auto
  have "uvars (subst (extend_subst ?v (to_unifiable t\<^sub>1) s) t') \<subseteq> 
    uvars t' - dom (extend_subst ?v (to_unifiable t\<^sub>1) s) \<union> 
      subst_vars (extend_subst ?v (to_unifiable t\<^sub>1) s)" by (metis uvars_subst)
  with U have "uvars (subst (extend_subst ?v (to_unifiable t\<^sub>1) s) t') \<subseteq> 
    uvars t' - insert ?v (dom s) \<union> uvars (subst s (to_unifiable t\<^sub>1)) \<union> subst_vars s" by simp
  moreover from S have "?v \<notin> 
    uvars t' - insert ?v (dom s) \<union> uvars (subst s (to_unifiable t\<^sub>1)) \<union> subst_vars s" by simp
  ultimately have "?v \<notin> uvars (subst (extend_subst ?v (to_unifiable t\<^sub>1) s) t')" by auto
  with E have "?v \<notin> uvars (subst (extend_subst ?v (to_unifiable t\<^sub>1) s) tt)" by simp
  with S E AR SV have G: "eliminate_vars vs (subst (extend_subst ?v (to_unifiable t\<^sub>1) s) tt) = 
    to_unifiable (Arrow t\<^sub>1 t\<^sub>2)" by (simp add: expand_extend_subst)
  from S have "valid_ty_subst (extend_subst ?v (to_unifiable t\<^sub>1) s)" by simp
  with A B C D F G show ?case by blast
next
  case (tc\<^sub>t_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  let ?v = "fresh vs"
  obtain e\<^sub>1' t\<^sub>1' vs'' con\<^sub>1 where TC1: "typecheck' \<Gamma> (insert ?v vs) (erase e\<^sub>1) = 
    (e\<^sub>1', t\<^sub>1', vs'', con\<^sub>1)" by (metis prod_cases4)
  obtain e\<^sub>2' t\<^sub>2' vs''' con\<^sub>2 where TC2: "typecheck' \<Gamma> vs'' (erase e\<^sub>2) = (e\<^sub>2', t\<^sub>2', vs''', con\<^sub>2)"
    by (metis prod_cases4)
  with tc\<^sub>t_app TC1 have E: "e' = App\<^sub>s e\<^sub>1' e\<^sub>2' \<and> tt = Var ?v \<and> vs''' = vs' \<and> 
    con = con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1', Arrow\<^sub>\<tau> t\<^sub>2' (Var ?v))]" by (auto simp add: Let_def)
  from tc\<^sub>t_app have "subst_vars \<Gamma> \<subseteq> insert ?v vs" by auto
  with tc\<^sub>t_app TC1 obtain s\<^sub>1 where S1: "
    partial_solidify (insert ?v vs) (hsubst s\<^sub>1 e\<^sub>1') = liquify e\<^sub>1 \<and> 
    eliminate_vars (insert ?v vs) (subst s\<^sub>1 t\<^sub>1') = to_unifiable (Arrow t\<^sub>1 t\<^sub>2) \<and> 
    dom s\<^sub>1 = vs'' - insert ?v vs \<and> subst_vars s\<^sub>1 = {} \<and> 
    s\<^sub>1 unifies\<^sub>\<kappa> eliminate_vars_constr (insert ?v vs) con\<^sub>1 \<and> valid_ty_subst s\<^sub>1 \<and> idempotent s\<^sub>1" 
      by fastforce
  from TC1 have V1: "insert ?v vs \<subseteq> vs''" by (metis vars_expand)
  from TC2 E have V2: "vs'' \<subseteq> vs'" by (metis vars_expand)
  with tc\<^sub>t_app V1 have Y: "subst_vars \<Gamma> \<subseteq> vs''" by auto
  with tc\<^sub>t_app TC1 TC2 Y obtain s\<^sub>2 where S2: "partial_solidify vs'' (hsubst s\<^sub>2 e\<^sub>2') = liquify e\<^sub>2 \<and> 
    eliminate_vars vs'' (subst s\<^sub>2 t\<^sub>2') = to_unifiable t\<^sub>1 \<and> dom s\<^sub>2 = vs''' - vs'' \<and> subst_vars s\<^sub>2 = {} \<and> 
    s\<^sub>2 unifies\<^sub>\<kappa> eliminate_vars_constr vs'' con\<^sub>2 \<and> valid_ty_subst s\<^sub>2 \<and> idempotent s\<^sub>2" by fastforce
  from tc\<^sub>t_app have FV: "?v \<notin> vs" by simp
  from S1 S2 have DSS: "dom s\<^sub>1 \<inter> dom s\<^sub>2 = {}" by auto
  from tc\<^sub>t_app TC1 S1 have "valid_ty_term t\<^sub>1' \<and> valid_ty_subst s\<^sub>1" by auto
  hence VTS1: "valid_ty_term (subst s\<^sub>1 t\<^sub>1')" by simp
  from tc\<^sub>t_app TC2 S2 have "valid_ty_term t\<^sub>2' \<and> valid_ty_subst s\<^sub>2" by auto
  hence VTS2: "valid_ty_term (subst s\<^sub>2 t\<^sub>2')" by simp
  let ?s = "extend_subst ?v (to_unifiable t\<^sub>2) (combine_subst s\<^sub>1 s\<^sub>2)"
  from S1 have D1: "dom s\<^sub>1 = vs'' - insert ?v vs" by simp
  from S2 E have D2: "dom s\<^sub>2 = vs' - vs''" by simp
  with V1 V2 D1 have D3: "dom (combine_subst s\<^sub>1 s\<^sub>2) = vs' - insert ?v vs" by auto
  with FV V1 V2 have A: "dom ?s = vs' - vs" by auto
  from tc\<^sub>t_app have VG: "?v \<notin> subst_vars \<Gamma>" by auto 
  with tc\<^sub>t_app TC1 have VE1: "?v \<notin> htvars e\<^sub>1'" by simp
  from tc\<^sub>t_app TC1 TC2 V1 VG have VE2: "?v \<notin> htvars e\<^sub>2'" by simp
  from tc\<^sub>t_app TC1 have "htvars e\<^sub>1' \<subseteq> vs'' - insert ?v vs" by simp
  with D2 have HV: "dom s\<^sub>2 \<inter> htvars e\<^sub>1' = {}" by auto
  from tc\<^sub>t_app E TC1 TC2 have HV2: "htvars e\<^sub>2' \<subseteq> vs' - vs''" by simp
  have "htvars (hsubst s\<^sub>2 e\<^sub>2') \<subseteq> htvars e\<^sub>2' - dom s\<^sub>2 \<union> subst_vars s\<^sub>2" by simp
  with D2 S2 HV2 have HVS2: "htvars (hsubst s\<^sub>2 e\<^sub>2') = {}" by auto
  have "htvars (hsubst s\<^sub>1 e\<^sub>1') \<subseteq> htvars e\<^sub>1' - dom s\<^sub>1 \<union> subst_vars s\<^sub>1" by simp
  with VE1 S1 have "?v \<notin> htvars (hsubst s\<^sub>1 e\<^sub>1')" by blast
  with S1 S2 VE1 VE2 HV HVS2 have "partial_solidify vs (hsubst ?s e\<^sub>1') = liquify e\<^sub>1 \<and>
    partial_solidify vs (hsubst ?s e\<^sub>2') = liquify e\<^sub>2" by simp
  hence B: "partial_solidify vs (hsubst ?s (App\<^sub>s e\<^sub>1' e\<^sub>2')) = liquify (App\<^sub>s e\<^sub>1 e\<^sub>2)" by simp
  have C: "eliminate_vars vs (subst ?s (Var ?v)) = to_unifiable t\<^sub>2" by simp
  from S1 S2 DSS D3 have D: "subst_vars ?s = {}" by auto
  from S1 S2 have VCS: "?v \<notin> subst_vars s\<^sub>1 \<and> ?v \<notin> subst_vars s\<^sub>2" by auto
  from D2 S1 V1 have D2S1: "dom s\<^sub>2 \<inter> subst_vars s\<^sub>1 = {}" by auto
  from tc\<^sub>t_app TC1 VG have "?v \<notin> constr_vars con\<^sub>1" by simp
  with S1 S2 DSS D3 D2S1 have UC1: "?s unifies\<^sub>\<kappa> eliminate_vars_constr vs con\<^sub>1" by simp
  from V1 V2 have VVS': "vs \<subseteq> vs''" by simp
  from tc\<^sub>t_app TC1 TC2 E have "constr_vars con\<^sub>2 \<subseteq> vs' - vs'' \<union> subst_vars \<Gamma>" by simp
  with tc\<^sub>t_app have "constr_vars con\<^sub>2 \<inter> vs'' \<subseteq> vs" by auto
  with S2 VVS' have "s\<^sub>2 unifies\<^sub>\<kappa> eliminate_vars_constr vs con\<^sub>2" 
    by (metis partial_typeify_constr_reduce_subset)
  with S1 S2 DSS D3 have UC2: "?s unifies\<^sub>\<kappa> eliminate_vars_constr vs con\<^sub>2" by simp
  from tc\<^sub>t_app TC1 have UV1: "uvars t\<^sub>1' \<subseteq> vs'' - insert ?v vs \<union> subst_vars \<Gamma>" by simp
  with VG have VT1: "?v \<notin> uvars t\<^sub>1'" by auto
  from tc\<^sub>t_app D2 V1 UV1 have DU1: "dom s\<^sub>2 \<inter> uvars t\<^sub>1' = {}" by auto
  from tc\<^sub>t_app TC1 TC2 E have UV2: "uvars t\<^sub>2' \<subseteq> vs' - vs'' \<union> subst_vars \<Gamma>" by simp
  with VG V1 have VT2: "?v \<notin> uvars t\<^sub>2'" by auto
  have "uvars (subst s\<^sub>1 t\<^sub>1') \<subseteq> uvars t\<^sub>1' - dom s\<^sub>1 \<union> subst_vars s\<^sub>1" by simp
  with S1 D1 UV1 have "uvars (subst s\<^sub>1 t\<^sub>1') \<subseteq> 
    (vs'' - insert ?v vs \<union> subst_vars \<Gamma>) - (vs'' - insert ?v vs) \<union> {}" by auto
  with tc\<^sub>t_app(6) have "uvars (subst s\<^sub>1 t\<^sub>1') \<subseteq> vs'' - insert ?v vs \<union> vs - (vs'' - insert ?v vs)" 
    by auto
  hence US1: "uvars (subst s\<^sub>1 t\<^sub>1') \<subseteq> vs" by auto
  have US2: "uvars (subst s\<^sub>2 t\<^sub>2') \<subseteq> uvars t\<^sub>2' - dom s\<^sub>2 \<union> subst_vars s\<^sub>2" by simp
  with S2 D2 UV2 have "uvars (subst s\<^sub>2 t\<^sub>2') \<subseteq> (vs' - vs'' \<union> subst_vars \<Gamma>) - (vs' - vs'') \<union> {}" 
    by auto
  with tc\<^sub>t_app(6) have "uvars (subst s\<^sub>2 t\<^sub>2') \<subseteq> vs' - vs'' \<union> vs - (vs' - vs'')" by auto
  hence US2: "uvars (subst s\<^sub>2 t\<^sub>2') \<subseteq> vs" by auto
  have "(vs'' - insert ?v vs) \<inter> ((vs' - vs'' \<union> vs) - (vs' - vs'') \<union> vs) = {}" by auto
  with tc\<^sub>t_app have "(vs'' - insert ?v vs) \<inter> ((vs' - vs'' \<union> subst_vars \<Gamma>) - (vs' - vs'') \<union> vs) = {}" 
    by auto
  with S2 D2 UV2 have "(vs'' - insert ?v vs) \<inter> (uvars t\<^sub>2' - dom s\<^sub>2 \<union> subst_vars s\<^sub>2) = {}" by auto
  with D1 US2 have DU2: "dom s\<^sub>1 \<inter> uvars (subst s\<^sub>2 t\<^sub>2') = {}" by fast
  from D1 have DSV1: "dom s\<^sub>1 \<inter> vs = {}" by auto
  from D2 V1 have DSV2: "dom s\<^sub>2 \<inter> vs = {}" by auto
  from S1 obtain tt1 tt2 where SS1: "subst s\<^sub>1 t\<^sub>1' = Arrow\<^sub>\<tau> tt1 tt2 \<and> 
    eliminate_vars (insert ?v vs) tt1 = to_unifiable t\<^sub>1 \<and> 
    eliminate_vars (insert ?v vs) tt2 = to_unifiable t\<^sub>2" by auto
  from US1 SS1 have "uvars tt1 \<subseteq> vs \<and> uvars tt2 \<subseteq> vs" by simp
  with FV SS1 have PT1: "eliminate_vars vs tt1 = to_unifiable t\<^sub>1 \<and> 
    eliminate_vars vs tt2 = to_unifiable t\<^sub>2" by force
  from US2 have "uvars (subst s\<^sub>2 t\<^sub>2') \<inter> vs'' \<subseteq> vs" by auto
  with S2 VVS' have "eliminate_vars vs (subst s\<^sub>2 t\<^sub>2') = to_unifiable t\<^sub>1"
    by (metis partial_typeify_reduce_subset)
  with FV UC1 UC2 S1 S2 DSV1 DSV2 VT1 VT2 DU1 DU2 SS1 PT1 have F: "
    ?s unifies\<^sub>\<kappa> eliminate_vars_constr vs (con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1', Arrow\<^sub>\<tau> t\<^sub>2' (Var ?v))])" 
      by (simp add: expand_extend_subst)
  from DSS VCS V1 D1 D2 S1 S2 D2S1 have G: "idempotent ?s" by simp
  from S1 S2 have "valid_ty_subst ?s" by simp
  with E A B C D F G show ?case by blast
qed auto

lemma typecheck_fails [simp]: "typecheck e = None \<Longrightarrow> \<nexists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>t e\<^sub>t : t) \<and> e = erase e\<^sub>t"
proof                              
  assume "typecheck e = None"
  then obtain e' tt vs' con where X: "typecheck' Map.empty {} e = (e', tt, vs', con) \<and> 
    unify con = None" by (auto split: prod.splits option.splits)
  assume "\<exists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>t e\<^sub>t : t) \<and> e = erase e\<^sub>t"
  then obtain e\<^sub>t t where Y: "(map_option to_type \<circ> Map.empty \<turnstile>\<^sub>t e\<^sub>t : t) \<and> e = erase e\<^sub>t" by fastforce
  have Z: "subst_vars Map.empty \<subseteq> {}" by simp
  have "valid_ty_subst Map.empty \<and> finite {}" by simp
  with X Y Z have "\<exists>s. partial_solidify {} (hsubst s e') = liquify e\<^sub>t \<and> 
    eliminate_vars {} (subst s tt) = to_unifiable t \<and> dom s = vs' - {} \<and> subst_vars s = {} \<and> 
    s unifies\<^sub>\<kappa> eliminate_vars_constr {} con \<and> valid_ty_subst s \<and> idempotent s" 
    using typecheck_fails' by blast
  then obtain s where "s unifies\<^sub>\<kappa> eliminate_vars_constr {} con \<and> idempotent s" by blast
  hence "\<exists>s'. unify con = Some s' \<and> s specializes s'" by simp
  with X show "False" by simp
qed

lemma [simp]: "value\<^sub>s (erase e) = value\<^sub>s e"
  by (induction e) simp_all

lemma [simp]: "all_vars\<^sub>s (erase e) = all_vars\<^sub>s e"
  by (induction e) simp_all

lemma [simp]: "erase (subst_var\<^sub>s x y e) = subst_var\<^sub>s x y (erase e)"
  by (induction e) simp_all

lemma [simp]: "erase (subst\<^sub>s x e' e) = subst\<^sub>s x (erase e') (erase e)"
  by (induction x e' e rule: subst\<^sub>s.induct) (simp_all add: Let_def)

theorem completeness [simp]: "e \<Down> v \<Longrightarrow> erase e \<Down> erase v"
  by (induction e v rule: eval\<^sub>s.induct) simp_all

end