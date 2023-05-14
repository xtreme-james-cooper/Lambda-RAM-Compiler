theory Typechecking
  imports TypedLanguage UnifiableType
begin

subsection \<open>Typechecking\<close>

text \<open>Now, we can finally define typechecking. The main \<open>typecheck'\<close> function is given a typing 
context*, a set of already-used variables, and an expression to check, and returns the expression 
annotated with fresh type variables on each binder, a unifiable term representing the type of the 
expression, a set of additional used variables, and a constraint that must be unified to establish 
the final form of the type of the expression. Rather than explicitly failing if we reach an unbound 
variable, we simply throw an un-unifiable constraint in and fail later.\<close>

text \<open>*The first argument is a \<open>subst\<close> rather than a \<open>var \<rightharpoonup> ty\<close> or \<open>ty list\<close>, but we call it \<Gamma> 
rather than \<sigma> to emphasize its role as a context in which we look up types, not a substitution we 
apply to terms.\<close>

primrec typecheck' :: "subst \<Rightarrow> var set \<Rightarrow> 'a expr\<^sub>s \<Rightarrow> uterm expr\<^sub>s \<times> uterm \<times> var set \<times> constraint" 
    where
  "typecheck' \<Gamma> vs (Var\<^sub>s x) = (case \<Gamma> x of 
      Some \<tau> \<Rightarrow> (Var\<^sub>s x, \<tau>, {}, []) 
    | None \<Rightarrow> (Var\<^sub>s x, Num\<^sub>\<tau>, {}, fail))"
| "typecheck' \<Gamma> vs (Const\<^sub>s n) = (Const\<^sub>s n, Num\<^sub>\<tau>, {}, [])"
| "typecheck' \<Gamma> vs (Lam\<^sub>s x u e) = (
    let v = fresh vs
    in let (e', \<tau>, vs', \<kappa>) = typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e
    in (Lam\<^sub>s x (Var v) e', Arrow\<^sub>\<tau> (Var v) \<tau>, insert v vs', \<kappa>))"
| "typecheck' \<Gamma> vs (App\<^sub>s e\<^sub>1 e\<^sub>2) = (
    let v = fresh vs
    in let (e\<^sub>1', \<tau>\<^sub>1, vs\<^sub>1, \<kappa>\<^sub>1) = typecheck' \<Gamma> (insert v vs) e\<^sub>1 
    in let (e\<^sub>2', \<tau>\<^sub>2, vs\<^sub>2, \<kappa>\<^sub>2) = typecheck' \<Gamma> (insert v (vs \<union> vs\<^sub>1)) e\<^sub>2 
    in (App\<^sub>s e\<^sub>1' e\<^sub>2', Var v, insert v (vs\<^sub>1 \<union> vs\<^sub>2), \<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(\<tau>\<^sub>1, Arrow\<^sub>\<tau> \<tau>\<^sub>2 (Var v))]))"

text \<open>As with the unification algorithm, we create an induction method tailored to \<open>typecheck'\<close>.\<close>

lemma typecheck_induct [consumes 1, case_names Var\<^sub>sS Var\<^sub>sN Const\<^sub>s Lam\<^sub>s App\<^sub>s]: "
  typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> 
  (\<And>\<Gamma> vs t x. \<Gamma> x = Some t \<Longrightarrow> P \<Gamma> vs (Var\<^sub>s x) (Var\<^sub>s x) t {} []) \<Longrightarrow> 
  (\<And>\<Gamma> vs x. \<Gamma> x = None \<Longrightarrow> P \<Gamma> vs (Var\<^sub>s x) (Var\<^sub>s x) Num\<^sub>\<tau> {} fail) \<Longrightarrow> 
  (\<And>\<Gamma> vs k. P \<Gamma> vs (Const\<^sub>s k) (Const\<^sub>s k) Num\<^sub>\<tau> {} []) \<Longrightarrow> 
  (\<And>\<Gamma> vs vs' con x u e\<^sub>1 e\<^sub>1' t' v. v = fresh vs \<Longrightarrow> typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>1 = 
    (e\<^sub>1', t', vs', con) \<Longrightarrow> P (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>1 e\<^sub>1' t' vs' con \<Longrightarrow> 
    P \<Gamma> vs (Lam\<^sub>s x u e\<^sub>1) (Lam\<^sub>s x (Var v) e\<^sub>1') (Arrow\<^sub>\<tau> (Var v) t') (insert v vs') con) \<Longrightarrow> 
  (\<And>\<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2. v = fresh vs \<Longrightarrow> 
    typecheck' \<Gamma> (insert v vs) e\<^sub>1 = (e\<^sub>1', t\<^sub>1, vs', con\<^sub>1) \<Longrightarrow> 
    typecheck' \<Gamma> (insert v (vs \<union> vs')) e\<^sub>2 = (e\<^sub>2', t\<^sub>2, vs'', con\<^sub>2) \<Longrightarrow> 
    P \<Gamma> (insert v vs) e\<^sub>1 e\<^sub>1' t\<^sub>1 vs' con\<^sub>1 \<Longrightarrow> 
    P \<Gamma> (insert v (vs \<union> vs')) e\<^sub>2 e\<^sub>2' t\<^sub>2 vs'' con\<^sub>2 \<Longrightarrow>
    P \<Gamma> vs (App\<^sub>s e\<^sub>1 e\<^sub>2) (App\<^sub>s e\<^sub>1' e\<^sub>2') (Var v) (insert v (vs' \<union> vs'')) 
      (con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1, Arrow\<^sub>\<tau> t\<^sub>2 (Var v))])) \<Longrightarrow> 
  P \<Gamma> vs e e' t vs' con"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (auto simp add: Let_def split: option.splits prod.splits)

text \<open>Full typechecking is now easy. We generate our annotated expression, type term, and 
constraints and then try to unify the constraint; if it fails, we fail, and if it succeeds, we 
can use the unifying substitution to produce the final typed expression and type.\<close>

fun typecheck :: "'a expr\<^sub>s \<rightharpoonup> ty expr\<^sub>s \<times> ty" where
  "typecheck e = (
    let (e', \<tau>, vs, \<kappa>) = typecheck' Map.empty {} e
    in case unify \<kappa> of 
        Some \<sigma> \<Rightarrow> Some (map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) e'), to_type (subst \<sigma> \<tau>))
      | None \<Rightarrow> None)"

abbreviation erase :: "'a expr\<^sub>s \<Rightarrow> unit expr\<^sub>s" where
  "erase \<equiv> map_expr\<^sub>s (\<lambda>x. ())"

primrec tyvars\<^sub>s :: "uterm expr\<^sub>s \<Rightarrow> var set" where
  "tyvars\<^sub>s (Var\<^sub>s x) = {}"
| "tyvars\<^sub>s (Const\<^sub>s k) = {}"
| "tyvars\<^sub>s (Lam\<^sub>s x t e) = uvars t \<union> tyvars\<^sub>s e"
| "tyvars\<^sub>s (App\<^sub>s e\<^sub>1 e\<^sub>2) = tyvars\<^sub>s e\<^sub>1 \<union> tyvars\<^sub>s e\<^sub>2"

primrec valid_ty_expr :: "uterm expr\<^sub>s \<Rightarrow> bool" where
  "valid_ty_expr (Var\<^sub>s x) = True"
| "valid_ty_expr (Const\<^sub>s k) = True"
| "valid_ty_expr (Lam\<^sub>s x t e) = (valid_ty_term t \<and> valid_ty_expr e)"
| "valid_ty_expr (App\<^sub>s e\<^sub>1 e\<^sub>2) = (valid_ty_expr e\<^sub>1 \<and> valid_ty_expr e\<^sub>2)"

lemma [simp]: "valid_ty_expr (map_expr\<^sub>s to_unifiable e)"
  by (induction e) simp_all

lemma [simp]: "x \<notin> tyvars\<^sub>s e \<Longrightarrow> map_expr\<^sub>s (subst [x \<mapsto> t]) e = e"
  by (induction e) simp_all

lemma [simp]: "map_expr\<^sub>s (subst (extend_subst x t s)) e = 
    map_expr\<^sub>s (subst s) (map_expr\<^sub>s (subst [x \<mapsto> t]) e)"
  by (induction e) (simp_all only: expr\<^sub>s.map expand_extend_subst comp_def)

lemma [simp]: "map_expr\<^sub>s to_type (map_expr\<^sub>s to_unifiable e) = e"
  by (induction e) simp_all

lemma [simp]: "valid_ty_expr e \<Longrightarrow> tyvars\<^sub>s e = {} \<Longrightarrow> map_expr\<^sub>s to_unifiable (map_expr\<^sub>s to_type e) = e"
  by (induction e) simp_all

lemma [simp]: "erase (map_expr\<^sub>s to_type (map_expr\<^sub>s (subst sub) e)) = erase (map_expr\<^sub>s to_type e)"
  by (induction e) simp_all

lemma [simp]: "tyvars\<^sub>s t = {} \<Longrightarrow> map_expr\<^sub>s (eliminate_vars vs) t = t"
  by (induction t) simp_all

lemma [simp]: "x \<notin> tyvars\<^sub>s t \<Longrightarrow> map_expr\<^sub>s (eliminate_vars (insert x vs)) t = map_expr\<^sub>s (eliminate_vars vs) t"
  by (induction t) simp_all

lemma [simp]: "valid_ty_subst sub \<Longrightarrow> valid_ty_expr e \<Longrightarrow> valid_ty_expr (map_expr\<^sub>s (subst sub) e)"
  by (induction e) simp_all

lemma htvars_hsubst [simp]: "tyvars\<^sub>s (map_expr\<^sub>s (subst sub) e) \<subseteq> tyvars\<^sub>s e - dom sub \<union> subst_vars sub"
proof (induction e)
  case (Lam\<^sub>s x t e)
  moreover have "uvars (subst sub t) \<subseteq> uvars t - dom sub \<union> subst_vars sub" by simp
  ultimately show ?case by fastforce
qed auto

lemma [simp]: "dom sub \<inter> tyvars\<^sub>s e = {} \<Longrightarrow> map_expr\<^sub>s (subst sub) e = e"
proof (induction e)
  case (Lam\<^sub>s x t e)
  moreover hence "dom sub \<inter> uvars t = {}" by auto
  ultimately show ?case by auto
qed auto

lemma [simp]: "map_expr\<^sub>s (subst (combine_subst s t)) e = map_expr\<^sub>s (subst s) (map_expr\<^sub>s (subst t) e)"
  by (induction e) simp_all

lemma [elim]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_term t"
  by (induction rule: typecheck_induct) auto

lemma [elim]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_expr e'"
  by (induction rule: typecheck_induct) auto

lemma typecheck_succeeds [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> 
  valid_ty_subst \<Gamma> \<Longrightarrow> unify con = Some sub' \<Longrightarrow> sub specializes sub' \<Longrightarrow>
    map_option (to_type \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>t map_expr\<^sub>s to_type (map_expr\<^sub>s (subst sub) e') : to_type (subst sub t)"
proof (induction arbitrary: sub' rule: typecheck_induct)
  case (Var\<^sub>sS \<Gamma> vs t x)
  thus ?case by simp
next
  case (Lam\<^sub>s \<Gamma> vs vs' con x u e\<^sub>1 e\<^sub>1' t' v)
  hence "valid_ty_subst (\<Gamma>(x \<mapsto> Var v))" by simp
  with Lam\<^sub>s have "map_option (to_type \<circ> subst sub) \<circ> \<Gamma>(x \<mapsto> Var v) \<turnstile>\<^sub>t map_expr\<^sub>s to_type (map_expr\<^sub>s (subst sub) e\<^sub>1') : 
      to_type (subst sub t')" by blast
  hence "map_option (to_type \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>t map_expr\<^sub>s to_type (map_expr\<^sub>s (subst sub) (Lam\<^sub>s x (Var v) e\<^sub>1')) :
    to_type (subst sub (Arrow\<^sub>\<tau> (Var v) t'))" by simp
  thus ?case by blast
next
  case (App\<^sub>s \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2)
  then obtain s\<^sub>2 where S2: "unify (con\<^sub>1 @ con\<^sub>2) = Some s\<^sub>2 \<and> sub' specializes s\<^sub>2" by fastforce
  then obtain s\<^sub>3 where S3: "unify con\<^sub>1 = Some s\<^sub>3 \<and> s\<^sub>2 specializes s\<^sub>3" by fastforce
  with App\<^sub>s S2 have "sub specializes s\<^sub>3" by auto
  with App\<^sub>s S2 S3 have T: "map_option (to_type \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>t map_expr\<^sub>s to_type (map_expr\<^sub>s (subst sub) e\<^sub>1') : 
    to_type (subst sub t\<^sub>1)" by blast
  from App\<^sub>s have "sub' unifies\<^sub>\<kappa> (con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1, Arrow\<^sub>\<tau> t\<^sub>2 (Var v))])" 
    by (metis unify_some) 
  hence "sub' unifies t\<^sub>1 and Arrow\<^sub>\<tau> t\<^sub>2 (Var v)" by simp
  with App\<^sub>s have X: "sub unifies t\<^sub>1 and Arrow\<^sub>\<tau> t\<^sub>2 (Var v)" by fastforce
  from S2 obtain s\<^sub>4 where S4: "unify con\<^sub>2 = Some s\<^sub>4 \<and> s\<^sub>2 specializes s\<^sub>4" 
    using unify_append_snd by blast
  with App\<^sub>s S2 have "sub specializes s\<^sub>4" by auto
  with App\<^sub>s S4 have "map_option (to_type \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>t map_expr\<^sub>s to_type (map_expr\<^sub>s (subst sub) e\<^sub>2') : 
    to_type (subst sub t\<^sub>2)" by blast
  with T X have "map_option (to_type \<circ> subst sub) \<circ> \<Gamma> \<turnstile>\<^sub>t map_expr\<^sub>s to_type (map_expr\<^sub>s (subst sub) (App\<^sub>s e\<^sub>1' e\<^sub>2')) : 
    to_type (subst sub (Var v))" by simp
  thus ?case by blast
qed simp_all

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> Map.empty \<turnstile>\<^sub>t e\<^sub>t : t"
proof -
  assume "typecheck e = Some (e\<^sub>t, t)"
  then obtain e' tt vs con sub where T: "typecheck' Map.empty {} e = (e', tt, vs, con) \<and>
    unify con = Some sub \<and> e\<^sub>t = map_expr\<^sub>s to_type (map_expr\<^sub>s (subst sub) e') \<and> t = to_type (subst sub tt)" 
      by (auto split: option.splits prod.splits)
  moreover hence "map_option (to_type \<circ> subst sub) \<circ> Map.empty \<turnstile>\<^sub>t map_expr\<^sub>s to_type (map_expr\<^sub>s (subst sub) e') : 
    to_type (subst sub tt)" by (metis typecheck_succeeds valid_empty_subst specializes_refl)
  moreover from T have "valid_ty_term tt" and "valid_ty_expr e'" by auto
  ultimately show "Map.empty \<turnstile>\<^sub>t e\<^sub>t : t" by simp
qed

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> e = erase (map_expr\<^sub>s to_type e')"
  by (induction rule: typecheck_induct) auto

lemma [simp]: "typecheck e = Some (e\<^sub>t, t) \<Longrightarrow> e = erase e\<^sub>t"
  by (auto split: option.splits prod.splits)

lemma [dest]: "erase e\<^sub>t = Var\<^sub>s x \<Longrightarrow> e\<^sub>t = Var\<^sub>s x"
  by (induction e\<^sub>t) simp_all

lemma [dest]: "erase e\<^sub>t = Lam\<^sub>s x u e \<Longrightarrow> \<exists>t e\<^sub>t'. e\<^sub>t = Lam\<^sub>s x t e\<^sub>t' \<and> e = erase e\<^sub>t'"
  by (induction e\<^sub>t) simp_all

lemma [dest]: "erase e\<^sub>t = App\<^sub>s e\<^sub>1 e\<^sub>2 \<Longrightarrow> \<exists>e\<^sub>1' e\<^sub>2'. e\<^sub>t = App\<^sub>s e\<^sub>1' e\<^sub>2' \<and> e\<^sub>1 = erase e\<^sub>1'\<and> e\<^sub>2 = erase e\<^sub>2'"
  by (induction e\<^sub>t) simp_all

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> finite vs \<Longrightarrow> finite vs'"
  by (induction e arbitrary: \<Gamma> vs e' t vs' con) 
     (auto simp add: Let_def split: option.splits prod.splits)

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t, vs', con) \<Longrightarrow> finite vs \<Longrightarrow> vs \<inter> vs' = {}"
proof (induction e arbitrary: \<Gamma> vs e' t vs' con)
  case (Lam\<^sub>s x u e)
  let ?v = "fresh vs"
  obtain e'' \<tau> vs'' \<kappa> where T: "typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) e = (e'', \<tau>, vs'', \<kappa>)"
    by (metis prod_cases4)
  with Lam\<^sub>s have "e' = Lam\<^sub>s x (Var ?v) e'' \<and> t = Arrow\<^sub>\<tau> (Var ?v) \<tau> \<and> vs' = insert ?v vs'' \<and> 
    con = \<kappa>" by (simp add: Let_def)
  with Lam\<^sub>s T show ?case by fastforce
next
  case (App\<^sub>s e\<^sub>1 e\<^sub>2)
  let ?v = "fresh vs"
  obtain e\<^sub>1' \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 where T1: "typecheck' \<Gamma> (insert ?v vs) e\<^sub>1 = (e\<^sub>1', \<tau>\<^sub>1, vs\<^sub>1, \<kappa>\<^sub>1)"
    by (metis prod_cases4)
  obtain e\<^sub>2' \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2 where T2: "typecheck' \<Gamma> (insert ?v (vs \<union> vs\<^sub>1)) e\<^sub>2 = (e\<^sub>2', \<tau>\<^sub>2, vs\<^sub>2, \<kappa>\<^sub>2)"
    by (metis prod_cases4)
  with App\<^sub>s T1 have "e' = App\<^sub>s e\<^sub>1' e\<^sub>2' \<and> t = Var ?v \<and> vs' = insert ?v (vs\<^sub>1 \<union> vs\<^sub>2) \<and>
    con = \<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(\<tau>\<^sub>1, Arrow\<^sub>\<tau> \<tau>\<^sub>2 (Var ?v))]" by (auto simp add: Let_def)
  with App\<^sub>s T1 T2 show ?case by fastforce
qed (simp_all split: option.splits)
     
lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> finite vs \<Longrightarrow> tyvars\<^sub>s e' \<subseteq> vs'"
  by (induction rule: typecheck_induct) auto

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> x \<in> vs \<Longrightarrow> finite vs \<Longrightarrow> x \<notin> tyvars\<^sub>s e'"
proof -
  assume T: "typecheck' \<Gamma> vs e = (e', t', vs', con)" and F: "finite vs"
  hence "tyvars\<^sub>s e' \<subseteq> vs'" by simp
  moreover from T F have "vs \<inter> vs' = {}" by simp
  moreover assume "x \<in> vs" 
  ultimately show "x \<notin> tyvars\<^sub>s e'" by auto
qed

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> finite vs \<Longrightarrow> 
    uvars t' \<subseteq> vs' \<union> subst_vars \<Gamma>"
  by (induction rule: typecheck_induct) auto

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> x \<in> vs \<Longrightarrow> finite vs \<Longrightarrow>
  x \<notin> subst_vars \<Gamma> \<Longrightarrow> x \<notin> uvars t'"
proof -
  assume T: "typecheck' \<Gamma> vs e = (e', t', vs', con)" and F: "finite vs"
  hence "uvars t' \<subseteq> vs' \<union> subst_vars \<Gamma>" by simp
  moreover from T F have "vs \<inter> vs' = {}" by simp
  moreover assume "x \<in> vs" and "x \<notin> subst_vars \<Gamma>" 
  ultimately show "x \<notin> uvars t'" by auto
qed

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> finite vs \<Longrightarrow> 
  constr_vars con \<subseteq> vs' \<union> subst_vars \<Gamma>"
proof (induction rule: typecheck_induct) 
  case (App\<^sub>s \<Gamma> vs vs' e\<^sub>1 e\<^sub>2 v e\<^sub>1' t\<^sub>1 vs'' con\<^sub>1 e\<^sub>2' t\<^sub>2 con\<^sub>2)
  hence "uvars t\<^sub>1 \<subseteq> vs' \<union> subst_vars \<Gamma>" by simp
  moreover from App\<^sub>s have "uvars t\<^sub>2 \<subseteq> vs'' \<union> subst_vars \<Gamma>" by simp
  ultimately have "uvars t\<^sub>1 \<subseteq> insert v (vs' \<union> vs'' \<union> subst_vars \<Gamma>) \<and> 
    uvars t\<^sub>2 \<subseteq> insert v (vs' \<union> vs'' \<union> subst_vars \<Gamma>)" by auto
  with App\<^sub>s show ?case by auto
qed auto

lemma [simp]: "typecheck' \<Gamma> vs e = (e', t', vs', con) \<Longrightarrow> x \<in> vs \<Longrightarrow> finite vs \<Longrightarrow>
  x \<notin> subst_vars \<Gamma> \<Longrightarrow> x \<notin> constr_vars con"
proof -
  assume T: "typecheck' \<Gamma> vs e = (e', t', vs', con)" and F: "finite vs"
  hence "constr_vars con \<subseteq> vs' \<union> subst_vars \<Gamma>" by simp
  moreover from T F have "vs \<inter> vs' = {}" by simp
  moreover assume "x \<in> vs" and "x \<notin> subst_vars \<Gamma>" 
  ultimately show "x \<notin> constr_vars con" by auto
qed

lemma [simp]: "typecheck' (\<Gamma>(x \<mapsto> Var y)) vs e = (e', tt, vs', con) \<Longrightarrow> y \<in> vs \<Longrightarrow>
  subst_vars \<Gamma> \<subseteq> vs - {y} \<Longrightarrow> uvars t' \<subseteq> vs - {y} \<Longrightarrow> finite vs \<Longrightarrow> typecheck' (\<Gamma>(x \<mapsto> t')) vs e = 
    (map_expr\<^sub>s (subst [y \<mapsto> t']) e', subst [y \<mapsto> t'] tt, vs', constr_subst y t' con)"
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
        (map_expr\<^sub>s (subst [y \<mapsto> t']) e', subst [y \<mapsto> t'] tt, vs', constr_subst y t' con)" 
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
  with Lam\<^sub>s(2) have E: "e' = Lam\<^sub>s z (Var ?v) e'' \<and> tt = Arrow\<^sub>\<tau> (Var ?v) tt' \<and> vs' = insert ?v vs'' \<and> 
    con' = con" by (simp only: typecheck'.simps Let_def split: prod.splits) simp
  show ?case
  proof (cases "x = z")
    case True
    with T E have T': "typecheck' (\<Gamma>(z \<mapsto> Var ?v)) (insert ?v vs) e = (e'', tt', vs'', con)" 
      by simp
    from Lam\<^sub>s(4) F have "y \<notin> subst_vars (\<Gamma>(z \<mapsto> Var ?v))" 
      by (auto simp add: subst_vars_def ran_def)
    with Lam\<^sub>s F E T' True T have "typecheck' (\<Gamma>(x \<mapsto> t')) vs (Lam\<^sub>s z u e) =
      (map_expr\<^sub>s (subst [y \<mapsto> t']) e', subst [y \<mapsto> t'] tt, vs', constr_subst y t' con)" 
        by (simp add: Let_def split: if_splits prod.splits)
    thus ?thesis by blast
  next
    case False
    from Lam\<^sub>s have "typecheck' (\<Gamma>(x \<mapsto> Var y)) vs (Lam\<^sub>s z u e) = (e', tt, vs', con)" by blast
    from E T False have X: "typecheck' (\<Gamma>(z \<mapsto> Var ?v, x \<mapsto> Var y)) (insert ?v vs) e = 
      (e'', tt', vs'', con)" by (metis fun_upd_twist)
    have "subst_vars (\<Gamma>(z := None)) \<subseteq> subst_vars \<Gamma>" by simp
    with Lam\<^sub>s(4) F have "subst_vars (\<Gamma>(z \<mapsto> Var ?v)) \<subseteq> insert ?v vs - {y}" by fastforce
    with Lam\<^sub>s X have "typecheck' (\<Gamma>(z \<mapsto> Var ?v, x \<mapsto> t')) (insert ?v vs) e = 
      (map_expr\<^sub>s (subst [y \<mapsto> t']) e'', subst [y \<mapsto> t'] tt', vs'', constr_subst y t' con)" by blast
    with False have "typecheck' (\<Gamma>(x \<mapsto> t', z \<mapsto> Var ?v)) (insert ?v vs) e = 
      (map_expr\<^sub>s (subst [y \<mapsto> t']) e'', subst [y \<mapsto> t'] tt', vs'', constr_subst y t' con)" 
        by (metis fun_upd_twist)
    with E F have "typecheck' (\<Gamma>(x \<mapsto> t')) vs (Lam\<^sub>s z u e) =
      (map_expr\<^sub>s (subst [y \<mapsto> t']) e', subst [y \<mapsto> t'] tt, vs', constr_subst y t' con)" 
        by (simp add: Let_def split: if_splits prod.splits)
    thus ?thesis by blast
  qed
next
  case (App\<^sub>s e1 e2)
  let ?v = "fresh vs"
  obtain e\<^sub>1' \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 where T1: "typecheck' (\<Gamma>(x \<mapsto> Var y)) (insert ?v vs) e1 = 
    (e\<^sub>1', \<tau>\<^sub>1, vs\<^sub>1, \<kappa>\<^sub>1)" by (metis prod_cases4)
  moreover obtain e\<^sub>2' t\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2 where T2: "
    typecheck' (\<Gamma>(x \<mapsto> Var y)) (insert ?v (vs \<union> vs\<^sub>1)) e2 = (e\<^sub>2', t\<^sub>2, vs\<^sub>2, \<kappa>\<^sub>2)" 
      by (metis prod_cases4)
  moreover from App\<^sub>s have "typecheck' (\<Gamma>(x \<mapsto> Var y)) vs (App\<^sub>s e1 e2) = (e', tt, vs', con)" by blast
  ultimately have E: "e' = App\<^sub>s e\<^sub>1' e\<^sub>2' \<and> tt = Var ?v \<and> vs' = insert ?v (vs\<^sub>1 \<union> vs\<^sub>2) \<and> 
    con = \<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(\<tau>\<^sub>1, Arrow\<^sub>\<tau> t\<^sub>2 (Var ?v))]" by (auto simp add: Let_def)
  moreover from App\<^sub>s T1 have "typecheck' (\<Gamma>(x \<mapsto> t')) (insert ?v vs) e1 =
    (map_expr\<^sub>s (subst [y \<mapsto> t']) e\<^sub>1', subst [y \<mapsto> t'] \<tau>\<^sub>1, vs\<^sub>1, constr_subst y t' \<kappa>\<^sub>1)" by blast
  moreover from App\<^sub>s T1 have "finite (insert ?v (vs \<union> vs\<^sub>1))" by simp
  moreover with App\<^sub>s T2 have "typecheck' (\<Gamma>(x \<mapsto> t')) (insert ?v (vs \<union> vs\<^sub>1)) e2 =
    (map_expr\<^sub>s (subst [y \<mapsto> t']) e\<^sub>2', subst [y \<mapsto> t'] t\<^sub>2, vs\<^sub>2, constr_subst y t' \<kappa>\<^sub>2)" by blast
  moreover from App\<^sub>s have "y \<noteq> ?v" by auto
  ultimately have "typecheck' (\<Gamma>(x \<mapsto> t')) vs (App\<^sub>s e1 e2) =
    (map_expr\<^sub>s (subst [y \<mapsto> t']) e', subst [y \<mapsto> t'] tt, vs', constr_subst y t' con)" 
      by (simp add: Let_def)
  thus ?case by blast
qed auto

lemma typecheck_fails' [simp]: "map_option to_type \<circ> \<Gamma> \<turnstile>\<^sub>t e\<^sub>t : t \<Longrightarrow> finite vs \<Longrightarrow> 
  subst_vars \<Gamma> \<subseteq> vs \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> typecheck' \<Gamma> vs (erase e\<^sub>t) = (e', tt, vs', con) \<Longrightarrow> 
  \<exists>s. map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst s) e') = map_expr\<^sub>s to_unifiable e\<^sub>t \<and> 
  eliminate_vars vs (subst s tt) = to_unifiable t \<and> dom s = vs' \<and> subst_vars s = {} \<and> 
  s unifies\<^sub>\<kappa> eliminate_vars_constr vs con \<and> valid_ty_subst s \<and> idempotent s"
proof (induction "map_option to_type \<circ> \<Gamma>" e\<^sub>t t arbitrary: \<Gamma> vs e' tt vs' con rule: typing\<^sub>t.induct)
  case (tc\<^sub>t_lam x t\<^sub>1 e t\<^sub>2)
  let ?v = "fresh vs"
  obtain e'' t' vs'' con' where T: "typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) (erase e) = 
    (e'', t', vs'', con')" by (metis prod_cases4)
  with tc\<^sub>t_lam have E: "e' = Lam\<^sub>s x (Var ?v) e'' \<and> tt = Arrow\<^sub>\<tau> (Var ?v) t' \<and> vs' = insert ?v vs'' \<and> 
    con' = con" by (simp add: Let_def)
  from tc\<^sub>t_lam have "subst_vars \<Gamma> \<subseteq> insert ?v vs" by auto
  hence X: "subst_vars (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1)) \<subseteq> insert ?v vs" by simp
  have Y: "(map_option to_type \<circ> \<Gamma>)(x \<mapsto> t\<^sub>1) = map_option to_type \<circ> (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1))" by simp
  from tc\<^sub>t_lam have Z: "valid_ty_subst (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1))" by simp
  from tc\<^sub>t_lam T have TC: "typecheck' (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1)) (insert ?v vs) (erase e) = 
    (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e'', subst [?v \<mapsto> to_unifiable t\<^sub>1] t', vs'', 
     constr_subst ?v (to_unifiable t\<^sub>1) con')" by simp
  from tc\<^sub>t_lam have "finite (insert ?v vs)" by simp
  with tc\<^sub>t_lam X Y Z TC obtain s where S: "
    map_expr\<^sub>s (eliminate_vars (insert ?v vs)) (map_expr\<^sub>s (subst s) (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e'')) = map_expr\<^sub>s to_unifiable e \<and> 
    eliminate_vars (insert ?v vs) (subst s (subst [?v \<mapsto> to_unifiable t\<^sub>1] t')) = to_unifiable t\<^sub>2 \<and>
    s unifies\<^sub>\<kappa> eliminate_vars_constr (insert ?v vs) (constr_subst ?v (to_unifiable t\<^sub>1) con') \<and> 
    dom s = vs'' \<and> subst_vars s = {} \<and> valid_ty_subst s \<and> idempotent s" by meson
  from tc\<^sub>t_lam have "subst_vars (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1)) \<subseteq> vs" by simp
  moreover from tc\<^sub>t_lam have FV: "?v \<notin> vs" by simp
  ultimately have "?v \<notin> subst_vars (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1))" by blast
  with tc\<^sub>t_lam TC have VCS: "?v \<notin> constr_vars (constr_subst ?v (to_unifiable t\<^sub>1) con')" by simp
  have "tyvars\<^sub>s (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e') \<subseteq> 
    tyvars\<^sub>s e' - dom [?v \<mapsto> to_unifiable t\<^sub>1] \<union> subst_vars [?v \<mapsto> to_unifiable t\<^sub>1]" 
      by (metis htvars_hsubst)
  hence "tyvars\<^sub>s (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e') \<subseteq> tyvars\<^sub>s e' - {?v}" by simp
  moreover have "tyvars\<^sub>s (map_expr\<^sub>s (subst s) (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e')) \<subseteq> 
    tyvars\<^sub>s (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e') - dom s \<union> subst_vars s" by simp
  ultimately have "tyvars\<^sub>s (map_expr\<^sub>s (subst s) (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e')) \<subseteq> 
    tyvars\<^sub>s e' - {?v} - dom s \<union> subst_vars s" by blast
  with S have "?v \<notin> tyvars\<^sub>s (map_expr\<^sub>s (subst (extend_subst ?v (to_unifiable t\<^sub>1) s)) e')" by auto
  with E S VCS have A: "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst (extend_subst ?v (to_unifiable t\<^sub>1) s)) e') = 
    map_expr\<^sub>s to_unifiable (Lam\<^sub>s x t\<^sub>1 e)" by simp
  from tc\<^sub>t_lam T have "insert ?v vs \<inter> vs'' = {}" by simp
  with S have U: "?v \<notin> dom s" by blast
  with S have B: "idempotent (extend_subst ?v (to_unifiable t\<^sub>1) s)" by simp
  from S E FV have "s unifies\<^sub>\<kappa> constr_subst ?v (to_unifiable t\<^sub>1) (eliminate_vars_constr vs con)" 
    by simp
  hence C: "extend_subst ?v (to_unifiable t\<^sub>1) s unifies\<^sub>\<kappa> eliminate_vars_constr vs con" by simp
  from S E have D: "dom (extend_subst ?v (to_unifiable t\<^sub>1) s) = vs'" by simp
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
  obtain e\<^sub>1' t\<^sub>1' vs\<^sub>1 con\<^sub>1 where TC1: "typecheck' \<Gamma> (insert ?v vs) (erase e\<^sub>1) = 
    (e\<^sub>1', t\<^sub>1', vs\<^sub>1, con\<^sub>1)" by (metis prod_cases4)
  obtain e\<^sub>2' t\<^sub>2' vs\<^sub>2 con\<^sub>2 where TC2: "typecheck' \<Gamma> (insert ?v (vs \<union> vs\<^sub>1)) (erase e\<^sub>2) = 
    (e\<^sub>2', t\<^sub>2', vs\<^sub>2, con\<^sub>2)" by (metis prod_cases4)
  with tc\<^sub>t_app TC1 have E: "e' = App\<^sub>s e\<^sub>1' e\<^sub>2' \<and> tt = Var ?v \<and> vs' = insert ?v (vs\<^sub>1 \<union> vs\<^sub>2) \<and> 
    con = con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1', Arrow\<^sub>\<tau> t\<^sub>2' (Var ?v))]" by (auto simp add: Let_def)
  from tc\<^sub>t_app have "subst_vars \<Gamma> \<subseteq> insert ?v vs" by auto
  with tc\<^sub>t_app TC1 obtain s\<^sub>1 where S1: "
    map_expr\<^sub>s (eliminate_vars (insert ?v vs)) (map_expr\<^sub>s (subst s\<^sub>1) e\<^sub>1') = map_expr\<^sub>s to_unifiable e\<^sub>1 \<and> 
    eliminate_vars (insert ?v vs) (subst s\<^sub>1 t\<^sub>1') = to_unifiable (Arrow t\<^sub>1 t\<^sub>2) \<and> 
    dom s\<^sub>1 = vs\<^sub>1 \<and> subst_vars s\<^sub>1 = {} \<and> 
    s\<^sub>1 unifies\<^sub>\<kappa> eliminate_vars_constr (insert ?v vs) con\<^sub>1 \<and> valid_ty_subst s\<^sub>1 \<and> idempotent s\<^sub>1" 
    by fastforce
  from tc\<^sub>t_app TC1 TC2 have FVS: "finite (insert ?v (vs \<union> vs\<^sub>1))" by simp
  from tc\<^sub>t_app have "subst_vars \<Gamma> \<subseteq> insert ?v (vs \<union> vs\<^sub>1)" by auto
  with tc\<^sub>t_app TC2 FVS obtain s\<^sub>2 where S2: "
    map_expr\<^sub>s (eliminate_vars (insert ?v (vs \<union> vs\<^sub>1))) (map_expr\<^sub>s (subst s\<^sub>2) e\<^sub>2') = 
      map_expr\<^sub>s to_unifiable e\<^sub>2 \<and> 
    eliminate_vars (insert ?v (vs \<union> vs\<^sub>1)) (subst s\<^sub>2 t\<^sub>2') = to_unifiable t\<^sub>1 \<and> dom s\<^sub>2 = vs\<^sub>2 \<and> subst_vars s\<^sub>2 = {} \<and> 
    s\<^sub>2 unifies\<^sub>\<kappa> eliminate_vars_constr (insert ?v (vs \<union> vs\<^sub>1)) con\<^sub>2 \<and> valid_ty_subst s\<^sub>2 \<and> idempotent s\<^sub>2" 
      by presburger
  from tc\<^sub>t_app have FV: "?v \<notin> vs" by simp
  from tc\<^sub>t_app TC1 have VVS1: "insert ?v vs \<inter> vs\<^sub>1 = {}" by simp
  moreover from tc\<^sub>t_app TC1 TC2 have VVS2: "insert ?v (vs \<union> vs\<^sub>1) \<inter> vs\<^sub>2 = {}" by simp
  ultimately have VVS: "?v \<notin> vs\<^sub>1 \<union> vs\<^sub>2" by simp
  from VVS2 S1 S2 have DSS: "dom s\<^sub>1 \<inter> dom s\<^sub>2 = {}" by auto
  from tc\<^sub>t_app TC1 S1 have "valid_ty_term t\<^sub>1' \<and> valid_ty_subst s\<^sub>1" by auto
  hence VTS1: "valid_ty_term (subst s\<^sub>1 t\<^sub>1')" by simp
  from tc\<^sub>t_app TC2 S2 have "valid_ty_term t\<^sub>2' \<and> valid_ty_subst s\<^sub>2" by auto
  hence VTS2: "valid_ty_term (subst s\<^sub>2 t\<^sub>2')" by simp
  let ?s = "extend_subst ?v (to_unifiable t\<^sub>2) (combine_subst s\<^sub>1 s\<^sub>2)"
  from S1 S2 have D3: "dom (combine_subst s\<^sub>1 s\<^sub>2) = vs\<^sub>1 \<union> vs\<^sub>2" by auto
  with FV E have A: "dom ?s = vs'" by simp
  from tc\<^sub>t_app have VG: "?v \<notin> subst_vars \<Gamma>" by auto 
  with tc\<^sub>t_app TC1 have VE1: "?v \<notin> tyvars\<^sub>s e\<^sub>1'" by simp
  from tc\<^sub>t_app TC1 TC2 VG have VE2: "?v \<notin> tyvars\<^sub>s e\<^sub>2'" by simp
  from tc\<^sub>t_app TC1 have "tyvars\<^sub>s e\<^sub>1' \<subseteq> vs\<^sub>1" by simp
  with S1 S2 DSS have HV: "dom s\<^sub>2 \<inter> tyvars\<^sub>s e\<^sub>1' = {}" by blast
  from tc\<^sub>t_app E TC1 TC2 have HV2: "tyvars\<^sub>s e\<^sub>2' \<subseteq> vs\<^sub>2" by simp
  have "tyvars\<^sub>s (map_expr\<^sub>s (subst s\<^sub>2) e\<^sub>2') \<subseteq> tyvars\<^sub>s e\<^sub>2' - dom s\<^sub>2 \<union> subst_vars s\<^sub>2" by simp
  with S2 HV2 have HVS2: "tyvars\<^sub>s (map_expr\<^sub>s (subst s\<^sub>2) e\<^sub>2') = {}" by auto
  have "tyvars\<^sub>s (map_expr\<^sub>s (subst s\<^sub>1) e\<^sub>1') \<subseteq> tyvars\<^sub>s e\<^sub>1' - dom s\<^sub>1 \<union> subst_vars s\<^sub>1" by simp
  with VE1 S1 have "?v \<notin> tyvars\<^sub>s (map_expr\<^sub>s (subst s\<^sub>1) e\<^sub>1')" by blast
  with S1 HV have "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst s\<^sub>1) (map_expr\<^sub>s (subst s\<^sub>2) e\<^sub>1')) = 
    map_expr\<^sub>s to_unifiable e\<^sub>1" by simp
  hence PS1: "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst s\<^sub>1 \<circ> subst s\<^sub>2) e\<^sub>1') = map_expr\<^sub>s to_unifiable e\<^sub>1"
    by (simp add: expr\<^sub>s.map_comp)
  from S2 HVS2 have "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst s\<^sub>1) (map_expr\<^sub>s (subst s\<^sub>2) e\<^sub>2')) = 
    map_expr\<^sub>s to_unifiable e\<^sub>2" by simp
  hence "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst s\<^sub>1 \<circ> subst s\<^sub>2) e\<^sub>2') = map_expr\<^sub>s to_unifiable e\<^sub>2"
    by (simp add: expr\<^sub>s.map_comp)
  with VE1 VE2 PS1 have "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst ?s) e\<^sub>1') = map_expr\<^sub>s to_unifiable e\<^sub>1 \<and>
    map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst ?s) e\<^sub>2') = map_expr\<^sub>s to_unifiable e\<^sub>2" by simp
  hence B: "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst ?s) (App\<^sub>s e\<^sub>1' e\<^sub>2')) = map_expr\<^sub>s to_unifiable (App\<^sub>s e\<^sub>1 e\<^sub>2)" by simp
  have C: "eliminate_vars vs (subst ?s (Var ?v)) = to_unifiable t\<^sub>2" by simp
  from S1 S2 DSS VVS D3 have D: "subst_vars ?s = {}" by simp
  from S1 S2 have VCS: "?v \<notin> subst_vars s\<^sub>1 \<and> ?v \<notin> subst_vars s\<^sub>2" by auto
  from S1 S2 have D2S1: "dom s\<^sub>2 \<inter> subst_vars s\<^sub>1 = {}" by auto
  from tc\<^sub>t_app TC1 VG have "?v \<notin> constr_vars con\<^sub>1" by simp
  with VVS S1 S2 DSS D2S1 have UC1: "?s unifies\<^sub>\<kappa> eliminate_vars_constr vs con\<^sub>1" by simp  
  from tc\<^sub>t_app TC1 TC2 E have "constr_vars con\<^sub>2 \<subseteq> vs\<^sub>2 \<union> subst_vars \<Gamma>" by simp
  with tc\<^sub>t_app VVS2 have CV2: "constr_vars con\<^sub>2 \<inter> vs\<^sub>1 \<subseteq> vs" by auto
  from tc\<^sub>t_app TC1 TC2 VG have "?v \<notin> constr_vars con\<^sub>2" by simp
  with CV2 VVS S1 S2 DSS have UC2: "?s unifies\<^sub>\<kappa> eliminate_vars_constr vs con\<^sub>2" by simp
  from tc\<^sub>t_app TC1 have UV1: "uvars t\<^sub>1' \<subseteq> vs\<^sub>1 \<union> subst_vars \<Gamma>" by simp
  with VG VVS have VT1: "?v \<notin> uvars t\<^sub>1'" by auto
  from DSS VVS2 have "vs\<^sub>2 \<inter> (vs\<^sub>1 \<union> vs) = {}" by blast
  with tc\<^sub>t_app(6) S2 UV1 have DU1: "dom s\<^sub>2 \<inter> uvars t\<^sub>1' = {}" by blast
  from tc\<^sub>t_app TC1 TC2 E have UV2: "uvars t\<^sub>2' \<subseteq> vs\<^sub>2 \<union> subst_vars \<Gamma>" by simp
  with VG VVS have VT2: "?v \<notin> uvars t\<^sub>2'" by auto
  have "uvars (subst s\<^sub>1 t\<^sub>1') \<subseteq> uvars t\<^sub>1' - dom s\<^sub>1 \<union> subst_vars s\<^sub>1" by simp
  with S1 UV1 have "uvars (subst s\<^sub>1 t\<^sub>1') \<subseteq> 
    (vs\<^sub>1 - insert ?v vs \<union> subst_vars \<Gamma>) - (vs\<^sub>1 - insert ?v vs) \<union> {}" by auto
  with tc\<^sub>t_app(6) have "uvars (subst s\<^sub>1 t\<^sub>1') \<subseteq> vs\<^sub>1 - insert ?v vs \<union> vs - (vs\<^sub>1 - insert ?v vs)" 
    by auto
  hence US1: "uvars (subst s\<^sub>1 t\<^sub>1') \<subseteq> vs" by auto
  have "uvars (subst s\<^sub>2 t\<^sub>2') \<subseteq> uvars t\<^sub>2' - dom s\<^sub>2 \<union> subst_vars s\<^sub>2" by simp
  with tc\<^sub>t_app(6) S2 UV2 have US2: "uvars (subst s\<^sub>2 t\<^sub>2') \<subseteq> vs" by blast
  with S1 VVS1 have DU2: "dom s\<^sub>1 \<inter> uvars (subst s\<^sub>2 t\<^sub>2') = {}" by auto
  from S1 VVS1 have DSV1: "dom s\<^sub>1 \<inter> vs = {}" by auto
  from S2 VVS2 have DSV2: "dom s\<^sub>2 \<inter> vs = {}" by auto
  from S1 obtain tt1 tt2 where SS1: "subst s\<^sub>1 t\<^sub>1' = Arrow\<^sub>\<tau> tt1 tt2 \<and> 
    eliminate_vars (insert ?v vs) tt1 = to_unifiable t\<^sub>1 \<and> 
    eliminate_vars (insert ?v vs) tt2 = to_unifiable t\<^sub>2" by auto
  from US1 SS1 have "uvars tt1 \<subseteq> vs \<and> uvars tt2 \<subseteq> vs" by simp
  with FV SS1 have PT1: "eliminate_vars vs tt1 = to_unifiable t\<^sub>1 \<and> 
    eliminate_vars vs tt2 = to_unifiable t\<^sub>2" by force
  from US2 have USV21: "uvars (subst s\<^sub>2 t\<^sub>2') \<inter> vs\<^sub>1 \<subseteq> vs" by auto
  from US2 FV have "?v \<notin> uvars (subst s\<^sub>2 t\<^sub>2')" by auto
  with S2 USV21 have "eliminate_vars vs (subst s\<^sub>2 t\<^sub>2') = to_unifiable t\<^sub>1" by simp
  with FV UC1 UC2 S1 S2 DSV1 DSV2 VT1 VT2 DU1 DU2 SS1 PT1 have F: "
    ?s unifies\<^sub>\<kappa> eliminate_vars_constr vs (con\<^sub>1 @ con\<^sub>2 @ [(t\<^sub>1', Arrow\<^sub>\<tau> t\<^sub>2' (Var ?v))])" 
    by (simp add: expand_extend_subst)
  from S1 S2 DSS VVS D3 have G: "idempotent ?s" by simp
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
  with X Y Z have "\<exists>s. map_expr\<^sub>s (eliminate_vars {}) (map_expr\<^sub>s (subst s) e') = map_expr\<^sub>s to_unifiable e\<^sub>t \<and> 
    eliminate_vars {} (subst s tt) = to_unifiable t \<and> dom s = vs' \<and> subst_vars s = {} \<and> 
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