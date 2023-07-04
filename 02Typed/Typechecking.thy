theory Typechecking
  imports UnifiableType
begin             

subsection \<open>Typechecking\<close>

text \<open>Now, we can finally define typechecking. The main \<open>typecheck'\<close> function is given a typing 
context*, a set of already-used variables, and an expression to check, and returns the expression 
annotated with fresh type variables on each binder, a unifiable term representing the type of the 
expression, a set of additional used variables, and a constraint that must be unified to establish 
the final form of the type of the expression. Rather than explicitly failing if we reach an unbound 
variable, we simply throw an un-unifiable constraint in and fail later.\<close>

text \<open>*The first argument is a \<open>subst\<close>, not a \<open>var \<rightharpoonup> ty\<close> or \<open>ty list\<close>, but we call it \<Gamma> rather than 
\<sigma> to emphasize its role as a context in which we look up types, not a substitution we apply to 
terms.\<close>

primrec typecheck' :: "subst \<Rightarrow> var set \<Rightarrow> 'a expr\<^sub>s \<Rightarrow> uterm expr\<^sub>s \<times> uterm \<times> var set \<times> constraint" 
    where
  "typecheck' \<Gamma> vs (Var\<^sub>s x) = (case \<Gamma> x of 
      Some \<tau> \<Rightarrow> (Var\<^sub>s x, \<tau>, {}, []) 
    | None \<Rightarrow> (Var\<^sub>s x, Num\<^sub>\<tau>, {}, fail))"
| "typecheck' \<Gamma> vs (Const\<^sub>s n) = (Const\<^sub>s n, Num\<^sub>\<tau>, {}, [])"
| "typecheck' \<Gamma> vs (Lam\<^sub>s x u e) = (
    let v = fresh vs
    in let (e\<^sub>u, \<tau>, vs', \<kappa>) = typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e
    in (Lam\<^sub>s x (Var v) e\<^sub>u, Arrow\<^sub>\<tau> (Var v) \<tau>, insert v vs', \<kappa>))"
| "typecheck' \<Gamma> vs (App\<^sub>s e\<^sub>1 e\<^sub>2) = (
    let v = fresh vs
    in let (e\<^sub>u\<^sub>1, \<tau>\<^sub>1, vs\<^sub>1, \<kappa>\<^sub>1) = typecheck' \<Gamma> (insert v vs) e\<^sub>1 
    in let (e\<^sub>u\<^sub>2, \<tau>\<^sub>2, vs\<^sub>2, \<kappa>\<^sub>2) = typecheck' \<Gamma> (insert v (vs \<union> vs\<^sub>1)) e\<^sub>2 
    in (App\<^sub>s e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2, Var v, insert v (vs\<^sub>1 \<union> vs\<^sub>2), \<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(\<tau>\<^sub>1, Arrow\<^sub>\<tau> \<tau>\<^sub>2 (Var v))]))"
| "typecheck' \<Gamma> vs (Let\<^sub>s x e\<^sub>1 e\<^sub>2) = (
    let v = fresh vs
    in let (e\<^sub>u\<^sub>1, \<tau>\<^sub>1, vs\<^sub>1, \<kappa>\<^sub>1) = typecheck' \<Gamma> (insert v vs) e\<^sub>1 
    in let (e\<^sub>u\<^sub>2, \<tau>\<^sub>2, vs\<^sub>2, \<kappa>\<^sub>2) = typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v (vs \<union> vs\<^sub>1)) e\<^sub>2 
    in (Let\<^sub>s x e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2, \<tau>\<^sub>2, insert v (vs\<^sub>1 \<union> vs\<^sub>2), \<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(Var v, \<tau>\<^sub>1)]))"

text \<open>As with the unification algorithm, we create an induction method tailored to \<open>typecheck'\<close>.\<close>

lemma typecheck_induct [consumes 1, case_names Var\<^sub>sS Var\<^sub>sN Const\<^sub>s Lam\<^sub>s App\<^sub>s Let\<^sub>s]: "
  typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> 
  (\<And>\<Gamma> vs x \<tau>. \<Gamma> x = Some \<tau> \<Longrightarrow> P \<Gamma> vs (Var\<^sub>s x) (Var\<^sub>s x) \<tau> {} []) \<Longrightarrow> 
  (\<And>\<Gamma> vs x. \<Gamma> x = None \<Longrightarrow> P \<Gamma> vs (Var\<^sub>s x) (Var\<^sub>s x) Num\<^sub>\<tau> {} fail) \<Longrightarrow> 
  (\<And>\<Gamma> vs n. P \<Gamma> vs (Const\<^sub>s n) (Const\<^sub>s n) Num\<^sub>\<tau> {} []) \<Longrightarrow> 
  (\<And>\<Gamma> vs x u e\<^sub>s v e\<^sub>u \<tau> vs' \<kappa>. v = fresh vs \<Longrightarrow> 
    typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> 
    P (\<Gamma>(x \<mapsto> Var v)) (insert v vs) e\<^sub>s e\<^sub>u \<tau> vs' \<kappa> \<Longrightarrow> 
    P \<Gamma> vs (Lam\<^sub>s x u e\<^sub>s) (Lam\<^sub>s x (Var v) e\<^sub>u) (Arrow\<^sub>\<tau> (Var v) \<tau>) (insert v vs') \<kappa>) \<Longrightarrow> 
  (\<And>\<Gamma> vs e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2 v e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 e\<^sub>u\<^sub>2 \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2. v = fresh vs \<Longrightarrow> 
    typecheck' \<Gamma> (insert v vs) e\<^sub>s\<^sub>1 = (e\<^sub>u\<^sub>1, \<tau>\<^sub>1, vs\<^sub>1, \<kappa>\<^sub>1) \<Longrightarrow> 
    typecheck' \<Gamma> (insert v (vs \<union> vs\<^sub>1)) e\<^sub>s\<^sub>2 = (e\<^sub>u\<^sub>2, \<tau>\<^sub>2, vs\<^sub>2, \<kappa>\<^sub>2) \<Longrightarrow> 
    P \<Gamma> (insert v vs) e\<^sub>s\<^sub>1 e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 \<Longrightarrow> 
    P \<Gamma> (insert v (vs \<union> vs\<^sub>1)) e\<^sub>s\<^sub>2 e\<^sub>u\<^sub>2 \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2 \<Longrightarrow>
    P \<Gamma> vs (App\<^sub>s e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2) (App\<^sub>s e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2) (Var v) (insert v (vs\<^sub>1 \<union> vs\<^sub>2)) 
      (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(\<tau>\<^sub>1, Arrow\<^sub>\<tau> \<tau>\<^sub>2 (Var v))])) \<Longrightarrow> 
  (\<And>\<Gamma> vs e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2 x v e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 e\<^sub>u\<^sub>2 \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2. v = fresh vs \<Longrightarrow> 
    typecheck' \<Gamma> (insert v vs) e\<^sub>s\<^sub>1 = (e\<^sub>u\<^sub>1, \<tau>\<^sub>1, vs\<^sub>1, \<kappa>\<^sub>1) \<Longrightarrow> 
    typecheck' (\<Gamma>(x \<mapsto> Var v)) (insert v (vs \<union> vs\<^sub>1)) e\<^sub>s\<^sub>2 = (e\<^sub>u\<^sub>2, \<tau>\<^sub>2, vs\<^sub>2, \<kappa>\<^sub>2) \<Longrightarrow> 
    P \<Gamma> (insert v vs) e\<^sub>s\<^sub>1 e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 \<Longrightarrow> 
    P (\<Gamma>(x \<mapsto> Var v)) (insert v (vs \<union> vs\<^sub>1)) e\<^sub>s\<^sub>2 e\<^sub>u\<^sub>2 \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2 \<Longrightarrow>
    P \<Gamma> vs (Let\<^sub>s x e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2) (Let\<^sub>s x e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2) \<tau>\<^sub>2 (insert v (vs\<^sub>1 \<union> vs\<^sub>2)) (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(Var v, \<tau>\<^sub>1)])) \<Longrightarrow> 
  P \<Gamma> vs e\<^sub>s e\<^sub>u \<tau> vs' \<kappa>"
  by (induction e\<^sub>s arbitrary: \<Gamma> vs e\<^sub>u \<tau> vs' \<kappa>) 
     (auto simp add: Let_def split: option.splits prod.splits)

lemma typecheck_to_valid_type [elim]: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> 
    valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_term \<tau>"
  by (induction rule: typecheck_induct) auto

lemma typecheck_to_valid_expr [elim]: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> 
    valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_expr e\<^sub>u"
proof (induction rule: typecheck_induct) 
  case (Let\<^sub>s \<Gamma> vs e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2 x v e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 e\<^sub>u\<^sub>2 \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2)
  moreover hence "valid_ty_term \<tau>\<^sub>1" by auto
  ultimately show ?case by simp
qed simp_all

lemma typecheck_erase [simp]: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> erase e\<^sub>u = e\<^sub>s"
  by (induction rule: typecheck_induct) simp_all

lemma typecheck_finite [simp]: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> finite vs \<Longrightarrow> finite vs'"
  by (induction rule: typecheck_induct) simp_all

lemma typecheck_vars_distinct [simp]: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> finite vs \<Longrightarrow> 
    vs \<inter> vs' = {}"
  by (induction rule: typecheck_induct) auto

lemma typecheck_type_vars [simp]: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> finite vs \<Longrightarrow> 
    uvars \<tau> \<subseteq> vs' \<union> subst_vars \<Gamma>"
  by (induction rule: typecheck_induct) auto

lemma typecheck_type_in_old_vars [simp]: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> x \<in> vs \<Longrightarrow> 
  finite vs \<Longrightarrow> x \<notin> subst_vars \<Gamma> \<Longrightarrow> x \<notin> uvars \<tau>"
proof -
  assume T: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>)" and F: "finite vs"
  hence "uvars \<tau> \<subseteq> vs' \<union> subst_vars \<Gamma>" by simp
  moreover from T F have "vs \<inter> vs' = {}" by simp
  moreover assume "x \<in> vs" and "x \<notin> subst_vars \<Gamma>" 
  ultimately show "x \<notin> uvars \<tau>" by auto
qed

text \<open>Full typechecking is now easy. We generate our annotated expression, type term, and 
constraints and then try to unify the constraint; if it fails, we fail, and if it succeeds, we 
can use the unifying substitution to produce the final typed expression and type. As noted earlier, 
we use only simple types in our final output, so \<open>Lam\<^sub>s x () (Var\<^sub>s x)\<close> will be typechecked with the 
type \<open>Arrow Num Num\<close>, for instance. This does not mean that every conceptually-polymorphic function 
can only be applied to numbers, however: the expression 
\<open>App\<^sub>s (Lam\<^sub>s x () (Var\<^sub>s x)) (Lam\<^sub>s x () (Var\<^sub>s x))\<close> will be given the overall type \<open>Arrow Num Num\<close> as 
well, with the first lambda subexpression typed as \<open>Arrow (Arrow Num Num) (Arrow Num Num)\<close>. It is 
only when the final unifiable type term is converted to a proper type that we specialize to \<open>Num\<close>s.\<close>

text \<open>This does, however, lead us to omit an important part of traditional strongly-typed functional 
languages, "let-polymorphism". Specifically, in the expression \<open>Let\<^sub>s x e\<^sub>1 (... x ... x...)\<close>, each 
occurrence of x must have the _same_ simple type, whereas a real language would make x polymorphic 
over \<open>e\<^sub>1\<close>'s free type variables and thus allow it to be _instantiated_ to different simple types as 
needed. We omit this purely for simplicity.\<close>

fun typecheck :: "unit expr\<^sub>s \<rightharpoonup> ty expr\<^sub>s \<times> ty" where
  "typecheck e\<^sub>s = (
    let (e\<^sub>u, \<tau>, vs, \<kappa>) = typecheck' Map.empty {} e\<^sub>s
    in case unify \<kappa> of 
        Some \<sigma> \<Rightarrow> Some (map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) e\<^sub>u), to_type (subst \<sigma> \<tau>))
      | None \<Rightarrow> None)"

text \<open>The typechecking success theorem is simple: a successfully typechecked expression has the type 
indicated, and erases to the original expression. We prove it first for \<open>typecheck'\<close>, then for the 
full typechecker.\<close>

lemma typecheck_success' [simp]: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> 
  unify \<kappa> = Some \<sigma>' \<Longrightarrow> \<sigma> specializes \<sigma>' \<Longrightarrow> finite vs \<Longrightarrow> subst_vars \<Gamma> \<subseteq> vs \<Longrightarrow>
  map_option (to_type \<circ> subst \<sigma>) \<circ> \<Gamma> \<turnstile>\<^sub>t map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) e\<^sub>u) : 
    to_type (subst \<sigma> \<tau>)"
proof (induction arbitrary: \<sigma>' rule: typecheck_induct)
  case (Lam\<^sub>s \<Gamma> vs x u e\<^sub>s v e\<^sub>u \<tau> vs' \<kappa>)
  moreover hence "valid_ty_subst (\<Gamma>(x \<mapsto> Var v))" by simp
  moreover from Lam\<^sub>s have "subst_vars (\<Gamma>(x := None)) \<subseteq> vs" by simp
  moreover hence "subst_vars (\<Gamma>(x \<mapsto> Var v)) \<subseteq> insert v vs" by auto
  ultimately have "map_option (to_type \<circ> subst \<sigma>) \<circ> \<Gamma>(x \<mapsto> Var v) \<turnstile>\<^sub>t 
    map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) e\<^sub>u) : to_type (subst \<sigma> \<tau>)" by blast
  hence "map_option (to_type \<circ> subst \<sigma>) \<circ> \<Gamma> \<turnstile>\<^sub>t 
    map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) (Lam\<^sub>s x (Var v) e\<^sub>u)) : 
    to_type (subst \<sigma> (Arrow\<^sub>\<tau> (Var v) \<tau>))" by simp
  thus ?case by blast
next
  case (App\<^sub>s \<Gamma> vs e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2 v e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 e\<^sub>u\<^sub>2 \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2)
  then obtain \<sigma>\<^sub>2 where S2: "unify (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2) = Some \<sigma>\<^sub>2 \<and> \<sigma>' specializes \<sigma>\<^sub>2" by fastforce
  then obtain \<sigma>\<^sub>3 where S3: "unify \<kappa>\<^sub>1 = Some \<sigma>\<^sub>3 \<and> \<sigma>\<^sub>2 specializes \<sigma>\<^sub>3" by fastforce
  with App\<^sub>s S2 have "\<sigma> specializes \<sigma>\<^sub>3" by auto
  with App\<^sub>s S2 S3 have T: "map_option (to_type \<circ> subst \<sigma>) \<circ> \<Gamma> \<turnstile>\<^sub>t 
    map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) e\<^sub>u\<^sub>1) : to_type (subst \<sigma> \<tau>\<^sub>1)" by blast
  from App\<^sub>s have "\<sigma>' unifies\<^sub>\<kappa> (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(\<tau>\<^sub>1, Arrow\<^sub>\<tau> \<tau>\<^sub>2 (Var v))])" by (metis unify_some) 
  hence "\<sigma>' unifies \<tau>\<^sub>1 and Arrow\<^sub>\<tau> \<tau>\<^sub>2 (Var v)" by simp
  with App\<^sub>s have X: "\<sigma> unifies \<tau>\<^sub>1 and Arrow\<^sub>\<tau> \<tau>\<^sub>2 (Var v)" by fast
  from S2 obtain s\<^sub>4 where S4: "unify \<kappa>\<^sub>2 = Some s\<^sub>4 \<and> \<sigma>\<^sub>2 specializes s\<^sub>4" 
    using unify_append_snd by blast
  with App\<^sub>s S2 have Y: "\<sigma> specializes s\<^sub>4" by auto
  from App\<^sub>s have "finite (insert v (vs \<union> vs\<^sub>1))" by simp
  with App\<^sub>s S4 Y have "map_option (to_type \<circ> subst \<sigma>) \<circ> \<Gamma> \<turnstile>\<^sub>t 
    map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) e\<^sub>u\<^sub>2) : to_type (subst \<sigma> \<tau>\<^sub>2)" by blast
  with T X have "map_option (to_type \<circ> subst \<sigma>) \<circ> \<Gamma> \<turnstile>\<^sub>t 
    map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) (App\<^sub>s e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2)) : to_type (subst \<sigma> (Var v))" by simp
  thus ?case by blast
next
  case (Let\<^sub>s \<Gamma> vs e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2 x v e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 e\<^sub>u\<^sub>2 \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2)
  moreover then obtain \<sigma>\<^sub>1 where "unify \<kappa>\<^sub>1 = Some \<sigma>\<^sub>1 \<and> \<sigma>' specializes \<sigma>\<^sub>1" by fastforce
  moreover with Let\<^sub>s have "\<sigma> specializes \<sigma>\<^sub>1" by auto
  ultimately have X: "map_option (to_type \<circ> subst \<sigma>) \<circ> \<Gamma> \<turnstile>\<^sub>t 
    map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) e\<^sub>u\<^sub>1) : to_type (subst \<sigma> \<tau>\<^sub>1)" by blast
  from Let\<^sub>s obtain \<sigma>\<^sub>2 where S2: "unify (\<kappa>\<^sub>2 @ [(Var v, \<tau>\<^sub>1)]) = Some \<sigma>\<^sub>2 \<and> \<sigma>' specializes \<sigma>\<^sub>2" 
    using unify_append_snd by blast
  then obtain \<sigma>\<^sub>3 where S3: "unify \<kappa>\<^sub>2 = Some \<sigma>\<^sub>3 \<and> \<sigma>\<^sub>2 specializes \<sigma>\<^sub>3" by fastforce
  with Let\<^sub>s S2 have Y: "\<sigma> specializes \<sigma>\<^sub>3" by auto
  from Let\<^sub>s have Z: "valid_ty_subst (\<Gamma>(x \<mapsto> Var v))" by simp
  from Let\<^sub>s have W: "finite (insert v (vs \<union> vs\<^sub>1))" by simp
  from Let\<^sub>s have "subst_vars (\<Gamma>(x \<mapsto> Var v)) \<subseteq> insert v (vs \<union> vs\<^sub>1)" by auto
  with Let\<^sub>s S3 Y Z W have A: "map_option (to_type \<circ> subst \<sigma>) \<circ> \<Gamma>(x \<mapsto> Var v) \<turnstile>\<^sub>t 
    map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) e\<^sub>u\<^sub>2) : to_type (subst \<sigma> \<tau>\<^sub>2)" by blast
  from S2 obtain \<sigma>\<^sub>4 where S4: "unify [(Var v, \<tau>\<^sub>1)] = Some \<sigma>\<^sub>4 \<and> \<sigma>\<^sub>2 specializes \<sigma>\<^sub>4" 
    using unify_append_snd by blast
  from Let\<^sub>s have "v \<notin> subst_vars \<Gamma>" by auto
  with Let\<^sub>s have "v \<notin> uvars \<tau>\<^sub>1" by simp
  with S4 have "\<sigma>\<^sub>4 unifies Var v and \<tau>\<^sub>1" by (auto split: if_splits)
  with Let\<^sub>s S2 S4 have "\<sigma> unifies Var v and \<tau>\<^sub>1" by fastforce
  with X A have "map_option (to_type \<circ> subst \<sigma>) \<circ> \<Gamma> \<turnstile>\<^sub>t 
    map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) (Let\<^sub>s x e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2)) : to_type (subst \<sigma> \<tau>\<^sub>2)" by simp
  thus ?case by blast
qed simp_all

theorem typecheck_success [simp]: "typecheck e\<^sub>s = Some (e\<^sub>t, t) \<Longrightarrow> 
  erase e\<^sub>t = e\<^sub>s \<and> Map.empty \<turnstile>\<^sub>t e\<^sub>t : t"
proof
  assume "typecheck e\<^sub>s = Some (e\<^sub>t, t)"
  then obtain e\<^sub>u \<tau> vs \<kappa> \<sigma> where T: "typecheck' Map.empty {} e\<^sub>s = (e\<^sub>u, \<tau>, vs, \<kappa>) \<and>
    unify \<kappa> = Some \<sigma> \<and> e\<^sub>t = map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) e\<^sub>u) \<and> t = to_type (subst \<sigma> \<tau>)" 
    by (auto split: option.splits prod.splits)
  moreover hence "map_option (to_type \<circ> subst \<sigma>) \<circ> Map.empty \<turnstile>\<^sub>t 
    map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) e\<^sub>u) : to_type (subst \<sigma> \<tau>)" 
      using typecheck_success' by fastforce
  moreover from T have "valid_ty_term \<tau>" and "valid_ty_expr e\<^sub>u" by auto
  ultimately show "Map.empty \<turnstile>\<^sub>t e\<^sub>t : t" by simp
  from T have "erase e\<^sub>u = e\<^sub>s" by (metis typecheck_erase)
  with T show "erase e\<^sub>t = e\<^sub>s" by simp
qed

text \<open>The typechecking failure theorem is just as simple to state - if typechecking fails, then 
there is no possible expression both erases to our initial expression and typechecks - but requires 
much, much more machinery to prove. It is worth considering why. The success theorem could be 
rendered false if our typechecker accepted bogus expressions, but not if it accepted too few: the 
theorem would hold exactly the same if we refused to type any \<open>Lam\<^sub>s\<close> expressions, or for that matter
if we simply failed in every case. The success theorem does not prevent underspecified 
implementations like \<open>typecheck e\<^sub>s = None\<close>. The failure theorem, on the other hand, could be 
rendered false by accepting too few expressions: we must prove that every single failure is a 
genuine failure, and the process of doing so essentially amounts to proving the correctness of the 
whole algorithm. For this reason, although it may not appear so at first glance, the failure theorem 
is the more important of the two.\<close>

lemma typecheck_expr_vars [simp]: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> finite vs \<Longrightarrow> 
    tyvars\<^sub>s e\<^sub>u \<subseteq> vs'"
  by (induction rule: typecheck_induct) auto

lemma typecheck_expr_not_in_old_vars [simp]: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> x \<in> vs \<Longrightarrow> 
  finite vs \<Longrightarrow> x \<notin> tyvars\<^sub>s e\<^sub>u"
proof -
  assume T: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>)" and F: "finite vs"
  hence "tyvars\<^sub>s e\<^sub>u \<subseteq> vs'" by simp
  moreover from T F have "vs \<inter> vs' = {}" by simp
  moreover assume "x \<in> vs" 
  ultimately show "x \<notin> tyvars\<^sub>s e\<^sub>u" by auto
qed

lemma typecheck_constr_vars  [simp]: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> finite vs \<Longrightarrow> 
  constr_vars \<kappa> \<subseteq> vs' \<union> subst_vars \<Gamma>"
proof (induction rule: typecheck_induct) 
  case (App\<^sub>s \<Gamma> vs e\<^sub>1 e\<^sub>2 v e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 e\<^sub>u\<^sub>2 \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2)
  hence "uvars \<tau>\<^sub>1 \<subseteq> vs\<^sub>1 \<union> subst_vars \<Gamma>" by simp
  moreover from App\<^sub>s have "uvars \<tau>\<^sub>2 \<subseteq> vs\<^sub>2 \<union> subst_vars \<Gamma>" by simp
  ultimately have "uvars \<tau>\<^sub>1 \<subseteq> insert v (vs\<^sub>1 \<union> vs\<^sub>2 \<union> subst_vars \<Gamma>) \<and> 
    uvars \<tau>\<^sub>2 \<subseteq> insert v (vs\<^sub>1 \<union> vs\<^sub>2 \<union> subst_vars \<Gamma>)" by auto
  with App\<^sub>s show ?case by auto
next
  case (Let\<^sub>s \<Gamma> vs e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2 x v e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 e\<^sub>u\<^sub>2 \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2)
  moreover hence "finite vs\<^sub>1" by simp
  ultimately have "constr_vars \<kappa>\<^sub>2 \<subseteq> vs\<^sub>2 \<union> subst_vars (\<Gamma>(x \<mapsto> Var v))" by simp
  from Let\<^sub>s have "uvars \<tau>\<^sub>1 \<subseteq> vs\<^sub>1 \<union> subst_vars \<Gamma>" by simp
  hence "uvars \<tau>\<^sub>1 \<subseteq> insert v (vs\<^sub>1 \<union> vs\<^sub>2 \<union> subst_vars \<Gamma>)" by auto
  with Let\<^sub>s show ?case by auto
qed auto

lemma typecheck_constr_in_old_vars [simp]: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> x \<in> vs \<Longrightarrow> 
  finite vs \<Longrightarrow> x \<notin> subst_vars \<Gamma> \<Longrightarrow> x \<notin> constr_vars \<kappa>"
proof -
  assume T: "typecheck' \<Gamma> vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>)" and F: "finite vs"
  hence "constr_vars \<kappa> \<subseteq> vs' \<union> subst_vars \<Gamma>" by simp
  moreover from T F have "vs \<inter> vs' = {}" by simp
  moreover assume "x \<in> vs" and "x \<notin> subst_vars \<Gamma>" 
  ultimately show "x \<notin> constr_vars \<kappa>" by auto
qed

text \<open>Usually our typing context is passed along unchanged, but we add to it when typechecking a 
\<open>Lam\<^sub>s\<close> expression. As a result, we need the following lemma, which allows us to make substitutions 
in the typing context.\<close>

lemma typecheck_subst_in_context [simp]: "typecheck' (\<Gamma>(x \<mapsto> Var y)) vs e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> 
  y \<in> vs \<Longrightarrow> subst_vars \<Gamma> \<subseteq> vs - {y} \<Longrightarrow> uvars \<tau>' \<subseteq> vs - {y} \<Longrightarrow> finite vs \<Longrightarrow> 
  typecheck' (\<Gamma>(x \<mapsto> \<tau>')) vs e\<^sub>s = 
    (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) e\<^sub>u, subst [y \<mapsto> \<tau>'] \<tau>, vs', constr_subst y \<tau>' \<kappa>)"
proof (induction e\<^sub>s arbitrary: \<Gamma> vs e\<^sub>u \<tau> vs' \<kappa>)
  case (Var\<^sub>s z)
  thus ?case
  proof (cases "x = z")
    case False
    with Var\<^sub>s show ?thesis
    proof (cases "\<Gamma> z")
      case (Some t)
      from Var\<^sub>s have "y \<notin> subst_vars \<Gamma>" by auto
      with Var\<^sub>s False Some have "typecheck' (\<Gamma>(x \<mapsto> \<tau>')) vs (Var\<^sub>s z) =
        (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) e\<^sub>u, subst [y \<mapsto> \<tau>'] \<tau>, vs', constr_subst y \<tau>' \<kappa>)" 
          by auto
      thus ?thesis by blast
    qed auto
  qed auto
next
  case (Lam\<^sub>s z u e\<^sub>s)
  let ?v = "fresh vs"
  from Lam\<^sub>s have F: "fresh vs \<noteq> y" using fresh_is_fresh by blast
  obtain e\<^sub>u' \<tau>\<^sub>2 vs'' \<kappa>' where T: "typecheck' (\<Gamma>(x \<mapsto> Var y, z \<mapsto> Var ?v)) (insert ?v vs) e\<^sub>s = 
    (e\<^sub>u', \<tau>\<^sub>2, vs'', \<kappa>')" by (metis prod_cases4)
  with Lam\<^sub>s(2) have E: "e\<^sub>u = Lam\<^sub>s z (Var ?v) e\<^sub>u' \<and> \<tau> = Arrow\<^sub>\<tau> (Var ?v) \<tau>\<^sub>2 \<and> vs' = insert ?v vs'' \<and> 
    \<kappa>' = \<kappa>" by (simp only: typecheck'.simps Let_def split: prod.splits) simp
  show ?case
  proof (cases "x = z")
    case True
    with T E have T': "typecheck' (\<Gamma>(z \<mapsto> Var ?v)) (insert ?v vs) e\<^sub>s = (e\<^sub>u', \<tau>\<^sub>2, vs'', \<kappa>)" by simp
    from Lam\<^sub>s(4) F have "y \<notin> subst_vars (\<Gamma>(z \<mapsto> Var ?v))" by (auto simp add: subst_vars_def ran_def)
    with Lam\<^sub>s F E T' True T have "typecheck' (\<Gamma>(x \<mapsto> \<tau>')) vs (Lam\<^sub>s z u e\<^sub>s) =
      (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) e\<^sub>u, subst [y \<mapsto> \<tau>'] \<tau>, vs', constr_subst y \<tau>' \<kappa>)" 
        by (simp add: Let_def split: if_splits prod.splits)
    thus ?thesis by blast
  next
    case False
    from Lam\<^sub>s have "typecheck' (\<Gamma>(x \<mapsto> Var y)) vs (Lam\<^sub>s z u e\<^sub>s) = (e\<^sub>u, \<tau>, vs', \<kappa>)" by blast
    from E T False have X: "typecheck' (\<Gamma>(z \<mapsto> Var ?v, x \<mapsto> Var y)) (insert ?v vs) e\<^sub>s = 
      (e\<^sub>u', \<tau>\<^sub>2, vs'', \<kappa>)" by (metis fun_upd_twist)
    have "subst_vars (\<Gamma>(z := None)) \<subseteq> subst_vars \<Gamma>" by simp
    with Lam\<^sub>s(4) F have "subst_vars (\<Gamma>(z \<mapsto> Var ?v)) \<subseteq> insert ?v vs - {y}" by fastforce
    with Lam\<^sub>s X have "typecheck' (\<Gamma>(z \<mapsto> Var ?v, x \<mapsto> \<tau>')) (insert ?v vs) e\<^sub>s = 
      (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) e\<^sub>u', subst [y \<mapsto> \<tau>'] \<tau>\<^sub>2, vs'', constr_subst y \<tau>' \<kappa>)" by blast
    with False have "typecheck' (\<Gamma>(x \<mapsto> \<tau>', z \<mapsto> Var ?v)) (insert ?v vs) e\<^sub>s = 
      (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) e\<^sub>u', subst [y \<mapsto> \<tau>'] \<tau>\<^sub>2, vs'', constr_subst y \<tau>' \<kappa>)" 
        by (metis fun_upd_twist)
    with E F have "typecheck' (\<Gamma>(x \<mapsto> \<tau>')) vs (Lam\<^sub>s z u e\<^sub>s) =
      (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) e\<^sub>u, subst [y \<mapsto> \<tau>'] \<tau>, vs', constr_subst y \<tau>' \<kappa>)" 
        by (simp add: Let_def split: if_splits prod.splits)
    thus ?thesis by blast
  qed
next
  case (App\<^sub>s e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2)
  let ?v = "fresh vs"
  obtain e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 where T1: "typecheck' (\<Gamma>(x \<mapsto> Var y)) (insert ?v vs) e\<^sub>s\<^sub>1 = 
    (e\<^sub>u\<^sub>1, \<tau>\<^sub>1, vs\<^sub>1, \<kappa>\<^sub>1)" by (metis prod_cases4)
  moreover obtain e\<^sub>u\<^sub>2 t\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2 where T2: "
    typecheck' (\<Gamma>(x \<mapsto> Var y)) (insert ?v (vs \<union> vs\<^sub>1)) e\<^sub>s\<^sub>2 = (e\<^sub>u\<^sub>2, t\<^sub>2, vs\<^sub>2, \<kappa>\<^sub>2)" 
      by (metis prod_cases4)
  moreover from App\<^sub>s have "typecheck' (\<Gamma>(x \<mapsto> Var y)) vs (App\<^sub>s e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2) = (e\<^sub>u, \<tau>, vs', \<kappa>)" by blast
  ultimately have E: "e\<^sub>u = App\<^sub>s e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2 \<and> \<tau> = Var ?v \<and> vs' = insert ?v (vs\<^sub>1 \<union> vs\<^sub>2) \<and> 
    \<kappa> = \<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(\<tau>\<^sub>1, Arrow\<^sub>\<tau> t\<^sub>2 (Var ?v))]" by (auto simp add: Let_def)
  moreover from App\<^sub>s T1 have "typecheck' (\<Gamma>(x \<mapsto> \<tau>')) (insert ?v vs) e\<^sub>s\<^sub>1 =
    (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) e\<^sub>u\<^sub>1, subst [y \<mapsto> \<tau>'] \<tau>\<^sub>1, vs\<^sub>1, constr_subst y \<tau>' \<kappa>\<^sub>1)" by blast
  moreover from App\<^sub>s T1 have "finite (insert ?v (vs \<union> vs\<^sub>1))" by simp
  moreover with App\<^sub>s T2 have "typecheck' (\<Gamma>(x \<mapsto> \<tau>')) (insert ?v (vs \<union> vs\<^sub>1)) e\<^sub>s\<^sub>2 =
    (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) e\<^sub>u\<^sub>2, subst [y \<mapsto> \<tau>'] t\<^sub>2, vs\<^sub>2, constr_subst y \<tau>' \<kappa>\<^sub>2)" by blast
  moreover from App\<^sub>s have "y \<noteq> ?v" by auto
  ultimately have "typecheck' (\<Gamma>(x \<mapsto> \<tau>')) vs (App\<^sub>s e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2) =
    (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) e\<^sub>u, subst [y \<mapsto> \<tau>'] \<tau>, vs', constr_subst y \<tau>' \<kappa>)" 
      by (simp add: Let_def)
  thus ?case by blast
next
  case (Let\<^sub>s z e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2)
  let ?v = "fresh vs"
  obtain e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 where T1: "typecheck' (\<Gamma>(x \<mapsto> Var y)) (insert ?v vs) e\<^sub>s\<^sub>1 = (e\<^sub>u\<^sub>1, \<tau>\<^sub>1, vs\<^sub>1, \<kappa>\<^sub>1)"
    by (metis prod_cases4)
  with Let\<^sub>s have T1': "typecheck' (\<Gamma>(x \<mapsto> \<tau>')) (insert ?v vs) e\<^sub>s\<^sub>1 =
    (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) e\<^sub>u\<^sub>1, subst [y \<mapsto> \<tau>'] \<tau>\<^sub>1, vs\<^sub>1, constr_subst y \<tau>' \<kappa>\<^sub>1)" by blast
  obtain e\<^sub>u\<^sub>2 \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2 where T2: "typecheck' (\<Gamma>(x \<mapsto> Var y, z \<mapsto> Var ?v)) (insert ?v (vs \<union> vs\<^sub>1)) e\<^sub>s\<^sub>2 =
    (e\<^sub>u\<^sub>2, \<tau>\<^sub>2, vs\<^sub>2, \<kappa>\<^sub>2)" by (metis prod_cases4)
  from Let\<^sub>s have "typecheck' (\<Gamma>(x \<mapsto> Var y)) vs (Let\<^sub>s z e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2) = (e\<^sub>u, \<tau>, vs', \<kappa>)" by blast
  with T1 T2 have E: "e\<^sub>u = Let\<^sub>s z e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2 \<and> \<tau> = \<tau>\<^sub>2 \<and> vs' = insert ?v (vs\<^sub>1 \<union> vs\<^sub>2) \<and> 
    \<kappa> = \<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(Var ?v, \<tau>\<^sub>1)]" by (simp add: Let_def)
  from Let\<^sub>s have V: "?v \<noteq> y" by auto
  thus ?case 
  proof (cases "x = z")
    case True
    from Let\<^sub>s have "subst_vars \<Gamma> \<subseteq> vs - {y}" by simp
    with V have "y \<notin> subst_vars (\<Gamma>(z \<mapsto> Var ?v))" by (auto simp add: subst_vars_def ran_def)
    with Let\<^sub>s T1 T2 True have "y \<notin> tyvars\<^sub>s e\<^sub>u\<^sub>2 \<and> y \<notin> uvars \<tau>\<^sub>2 \<and> y \<notin> constr_vars \<kappa>\<^sub>2" by simp
    with V T1' T2 True have "typecheck' (\<Gamma>(x \<mapsto> \<tau>')) vs (Let\<^sub>s z e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2) =
      (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) (Let\<^sub>s z e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2), subst [y \<mapsto> \<tau>'] \<tau>\<^sub>2, insert ?v (vs\<^sub>1 \<union> vs\<^sub>2), 
        constr_subst y \<tau>' (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(Var ?v, \<tau>\<^sub>1)]))" by (simp add: Let_def)
    with E show ?thesis by blast
  next
    case False
    with T2 have X: "typecheck' (\<Gamma>(z \<mapsto> Var ?v, x \<mapsto> Var y)) (insert ?v (vs \<union> vs\<^sub>1)) e\<^sub>s\<^sub>2 = 
      (e\<^sub>u\<^sub>2, \<tau>\<^sub>2, vs\<^sub>2, \<kappa>\<^sub>2)" by (simp add: fun_upd_twist)
    from Let\<^sub>s have "subst_vars \<Gamma> \<subseteq> insert (fresh vs) (vs \<union> vs\<^sub>1) - {y}" by auto
    with T1 V have Y: "subst_vars (\<Gamma>(z \<mapsto> Var ?v)) \<subseteq> insert ?v (vs \<union> vs\<^sub>1) - {y}" by simp
    from Let\<^sub>s T1 have "finite (insert ?v (vs \<union> vs\<^sub>1))" by simp
    with Let\<^sub>s X Y have "typecheck' (\<Gamma>(z \<mapsto> Var ?v, x \<mapsto> \<tau>')) (insert ?v (vs \<union> vs\<^sub>1)) e\<^sub>s\<^sub>2 =
      (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) e\<^sub>u\<^sub>2, subst [y \<mapsto> \<tau>'] \<tau>\<^sub>2, vs\<^sub>2, constr_subst y \<tau>' \<kappa>\<^sub>2)" by blast
    with False have "typecheck' (\<Gamma>(x \<mapsto> \<tau>', z \<mapsto> Var ?v)) (insert ?v (vs \<union> vs\<^sub>1)) e\<^sub>s\<^sub>2 =
      (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) e\<^sub>u\<^sub>2, subst [y \<mapsto> \<tau>'] \<tau>\<^sub>2, vs\<^sub>2, constr_subst y \<tau>' \<kappa>\<^sub>2)" 
        by (simp add: fun_upd_twist)
    with V T1' have "typecheck' (\<Gamma>(x \<mapsto> \<tau>')) vs (Let\<^sub>s z e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2) =
      (map_expr\<^sub>s (subst [y \<mapsto> \<tau>']) (Let\<^sub>s z e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2), subst [y \<mapsto> \<tau>'] \<tau>\<^sub>2, insert ?v (vs\<^sub>1 \<union> vs\<^sub>2), 
        constr_subst y \<tau>' (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(Var ?v, \<tau>\<^sub>1)]))" by (simp add: Let_def)
    with E show ?thesis by blast
  qed
qed auto

text \<open>Now, the big one. If an expression is well-typed, then there is an (idempotent, well-formed) 
substitution with no free variables and a domain of exactly \<open>typecheck'\<close>'s new variables, that 
solves \<open>typecheck'\<close>'s generated constraints, and unifies the expressions and types. (We finally 
bring in the \<open>eliminate_vars\<close> function, to be careful to map to \<open>Num\<^sub>\<tau>\<close> only the variables that are 
free in the whole expression while unifying; \<open>map_expr\<^sub>s to_type (map_expr\<^sub>s (subst \<sigma>) e\<^sub>u) = e\<^sub>t\<close> and 
\<open>to_type (subst \<sigma> \<tau>) = t\<close> are simpler and look equivalent at first glance, but actually claim too 
much and the induction does not carry on the \<open>App\<^sub>s\<close> case.) This lemma is where the correctness of 
the typechecker is shown: if there is a type, the typechecker will find it.\<close>

lemma typecheck_finds_subst [simp]: "map_option to_type \<circ> \<Gamma> \<turnstile>\<^sub>t e\<^sub>t : t \<Longrightarrow> finite vs \<Longrightarrow> 
  subst_vars \<Gamma> \<subseteq> vs \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> typecheck' \<Gamma> vs (erase e\<^sub>t) = (e\<^sub>u, \<tau>, vs', \<kappa>) \<Longrightarrow> 
  \<exists>\<sigma>. map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst \<sigma>) e\<^sub>u) = map_expr\<^sub>s to_unifiable e\<^sub>t \<and> 
    eliminate_vars vs (subst \<sigma> \<tau>) = to_unifiable t \<and> dom \<sigma> = vs' \<and> subst_vars \<sigma> = {} \<and> 
    \<sigma> unifies\<^sub>\<kappa> eliminate_vars_constr vs \<kappa> \<and> valid_ty_subst \<sigma> \<and> idempotent \<sigma>"
proof (induction "map_option to_type \<circ> \<Gamma>" e\<^sub>t t arbitrary: \<Gamma> vs e\<^sub>u \<tau> vs' \<kappa> rule: typing\<^sub>t.induct)
  case (tc\<^sub>t_lam x t\<^sub>1 e\<^sub>t t\<^sub>2)
  let ?v = "fresh vs"
  obtain e\<^sub>u' \<tau>\<^sub>2 vs'' \<kappa>' where T: "typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v vs) (erase e\<^sub>t) = 
    (e\<^sub>u', \<tau>\<^sub>2, vs'', \<kappa>')" by (metis prod_cases4)
  with tc\<^sub>t_lam have E: "e\<^sub>u = Lam\<^sub>s x (Var ?v) e\<^sub>u' \<and> \<tau> = Arrow\<^sub>\<tau> (Var ?v) \<tau>\<^sub>2 \<and> vs' = insert ?v vs'' \<and> 
    \<kappa>' = \<kappa>" by (simp add: Let_def)
  from tc\<^sub>t_lam have "subst_vars \<Gamma> \<subseteq> insert ?v vs" by auto
  hence X: "subst_vars (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1)) \<subseteq> insert ?v vs" by simp
  have Y: "(map_option to_type \<circ> \<Gamma>)(x \<mapsto> t\<^sub>1) = map_option to_type \<circ> (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1))" 
    by simp
  from tc\<^sub>t_lam have Z: "valid_ty_subst (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1))" by simp
  from tc\<^sub>t_lam T have TC: "typecheck' (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1)) (insert ?v vs) (erase e\<^sub>t) = 
    (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e\<^sub>u', subst [?v \<mapsto> to_unifiable t\<^sub>1] \<tau>\<^sub>2, vs'', 
      constr_subst ?v (to_unifiable t\<^sub>1) \<kappa>')" by simp
  from tc\<^sub>t_lam have "finite (insert ?v vs)" by simp
  with tc\<^sub>t_lam X Y Z TC obtain s where S: "map_expr\<^sub>s (eliminate_vars (insert ?v vs)) 
    (map_expr\<^sub>s (subst s) (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e\<^sub>u')) = 
      map_expr\<^sub>s to_unifiable e\<^sub>t \<and> 
    eliminate_vars (insert ?v vs) (subst s (subst [?v \<mapsto> to_unifiable t\<^sub>1] \<tau>\<^sub>2)) = to_unifiable t\<^sub>2 \<and>
    s unifies\<^sub>\<kappa> eliminate_vars_constr (insert ?v vs) (constr_subst ?v (to_unifiable t\<^sub>1) \<kappa>') \<and> 
    dom s = vs'' \<and> subst_vars s = {} \<and> valid_ty_subst s \<and> idempotent s" by meson
  from tc\<^sub>t_lam have "subst_vars (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1)) \<subseteq> vs" by simp
  moreover from tc\<^sub>t_lam have FV: "?v \<notin> vs" by simp
  ultimately have "?v \<notin> subst_vars (\<Gamma>(x \<mapsto> to_unifiable t\<^sub>1))" by blast
  with tc\<^sub>t_lam TC have VCS: "?v \<notin> constr_vars (constr_subst ?v (to_unifiable t\<^sub>1) \<kappa>')" by simp
  have "tyvars\<^sub>s (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e\<^sub>u) \<subseteq> 
    tyvars\<^sub>s e\<^sub>u - dom [?v \<mapsto> to_unifiable t\<^sub>1] \<union> subst_vars [?v \<mapsto> to_unifiable t\<^sub>1]" 
      by (metis tyvars_subst_expr)
  hence "tyvars\<^sub>s (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e\<^sub>u) \<subseteq> tyvars\<^sub>s e\<^sub>u - {?v}" by simp
  moreover have "tyvars\<^sub>s (map_expr\<^sub>s (subst s) (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e\<^sub>u)) \<subseteq> 
    tyvars\<^sub>s (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e\<^sub>u) - dom s \<union> subst_vars s" 
      by simp
  ultimately have "tyvars\<^sub>s (map_expr\<^sub>s (subst s) (map_expr\<^sub>s (subst [?v \<mapsto> to_unifiable t\<^sub>1]) e\<^sub>u)) \<subseteq> 
    tyvars\<^sub>s e\<^sub>u - {?v} - dom s \<union> subst_vars s" by blast
  with S have "?v \<notin> tyvars\<^sub>s (map_expr\<^sub>s (subst (extend_subst ?v (to_unifiable t\<^sub>1) s)) e\<^sub>u)" by auto
  with E S VCS have A: "map_expr\<^sub>s (eliminate_vars vs) 
    (map_expr\<^sub>s (subst (extend_subst ?v (to_unifiable t\<^sub>1) s)) e\<^sub>u) = 
      map_expr\<^sub>s to_unifiable (Lam\<^sub>s x t\<^sub>1 e\<^sub>t)" by simp
  from tc\<^sub>t_lam T have "insert ?v vs \<inter> vs'' = {}" by simp
  with S have U: "?v \<notin> dom s" by blast
  with S have B: "idempotent (extend_subst ?v (to_unifiable t\<^sub>1) s)" by simp
  from S E FV have "s unifies\<^sub>\<kappa> constr_subst ?v (to_unifiable t\<^sub>1) (eliminate_vars_constr vs \<kappa>)" 
    by simp
  hence C: "extend_subst ?v (to_unifiable t\<^sub>1) s unifies\<^sub>\<kappa> eliminate_vars_constr vs \<kappa>" by simp
  from S E have D: "dom (extend_subst ?v (to_unifiable t\<^sub>1) s) = vs'" by simp
  have VS: "uvars (subst s (to_unifiable t\<^sub>1)) \<subseteq> uvars (to_unifiable t\<^sub>1) - dom s \<union> subst_vars s" 
    by (metis uvars_subst)
  from S U VS have F: "subst_vars (extend_subst ?v (to_unifiable t\<^sub>1) s) = {}" by auto
  from S have AR: "eliminate_vars (insert ?v vs) 
    (subst (map_option (subst [fresh vs \<mapsto> to_unifiable t\<^sub>1]) \<circ> s) 
      (subst [fresh vs \<mapsto> to_unifiable t\<^sub>1] \<tau>\<^sub>2)) = to_unifiable t\<^sub>2" 
    by (metis subst_absorb_no_ran)
  from U have SV: "s ?v = None" by auto
  have "uvars (subst (extend_subst ?v (to_unifiable t\<^sub>1) s) \<tau>\<^sub>2) \<subseteq> 
    uvars \<tau>\<^sub>2 - dom (extend_subst ?v (to_unifiable t\<^sub>1) s) \<union> 
      subst_vars (extend_subst ?v (to_unifiable t\<^sub>1) s)" 
    by (metis uvars_subst)
  with U have "uvars (subst (extend_subst ?v (to_unifiable t\<^sub>1) s) \<tau>\<^sub>2) \<subseteq> 
    uvars \<tau>\<^sub>2 - insert ?v (dom s) \<union> uvars (subst s (to_unifiable t\<^sub>1)) \<union> subst_vars s" by simp
  moreover from S have "?v \<notin> 
    uvars \<tau>\<^sub>2 - insert ?v (dom s) \<union> uvars (subst s (to_unifiable t\<^sub>1)) \<union> subst_vars s" by simp
  ultimately have "?v \<notin> uvars (subst (extend_subst ?v (to_unifiable t\<^sub>1) s) \<tau>\<^sub>2)" by auto
  with E have "?v \<notin> uvars (subst (extend_subst ?v (to_unifiable t\<^sub>1) s) \<tau>)" by simp
  with S E AR SV have G: "eliminate_vars vs (subst (extend_subst ?v (to_unifiable t\<^sub>1) s) \<tau>) = 
    to_unifiable (Arrow t\<^sub>1 t\<^sub>2)" by (simp add: expand_extend_subst)
  from S have "valid_ty_subst (extend_subst ?v (to_unifiable t\<^sub>1) s)" by simp
  with A B C D F G show ?case by blast
next
  case (tc\<^sub>t_app e\<^sub>s\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>s\<^sub>2)
  let ?v = "fresh vs"
  obtain e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 where TC1: "typecheck' \<Gamma> (insert ?v vs) (erase e\<^sub>s\<^sub>1) = (e\<^sub>u\<^sub>1, \<tau>\<^sub>1, vs\<^sub>1, \<kappa>\<^sub>1)" 
    by (metis prod_cases4)
  obtain e\<^sub>u\<^sub>2 \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2 where TC2: "typecheck' \<Gamma> (insert ?v (vs \<union> vs\<^sub>1)) (erase e\<^sub>s\<^sub>2) = (e\<^sub>u\<^sub>2, \<tau>\<^sub>2, vs\<^sub>2, \<kappa>\<^sub>2)" 
    by (metis prod_cases4)
  with tc\<^sub>t_app TC1 have E: "e\<^sub>u = App\<^sub>s e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2 \<and> \<tau> = Var ?v \<and> vs' = insert ?v (vs\<^sub>1 \<union> vs\<^sub>2) \<and> 
    \<kappa> = \<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(\<tau>\<^sub>1, Arrow\<^sub>\<tau> \<tau>\<^sub>2 (Var ?v))]" by (auto simp add: Let_def)
  from tc\<^sub>t_app have "subst_vars \<Gamma> \<subseteq> insert ?v vs" by auto
  with tc\<^sub>t_app TC1 obtain \<sigma>\<^sub>1 where S1: "
    map_expr\<^sub>s (eliminate_vars (insert ?v vs)) (map_expr\<^sub>s (subst \<sigma>\<^sub>1) e\<^sub>u\<^sub>1) = 
      map_expr\<^sub>s to_unifiable e\<^sub>s\<^sub>1 \<and> 
    eliminate_vars (insert ?v vs) (subst \<sigma>\<^sub>1 \<tau>\<^sub>1) = to_unifiable (Arrow t\<^sub>1 t\<^sub>2) \<and> 
    dom \<sigma>\<^sub>1 = vs\<^sub>1 \<and> subst_vars \<sigma>\<^sub>1 = {} \<and> \<sigma>\<^sub>1 unifies\<^sub>\<kappa> eliminate_vars_constr (insert ?v vs) \<kappa>\<^sub>1 \<and> 
    valid_ty_subst \<sigma>\<^sub>1 \<and> idempotent \<sigma>\<^sub>1" 
      by fastforce
  from tc\<^sub>t_app TC1 TC2 have FVS: "finite (insert ?v (vs \<union> vs\<^sub>1))" by simp
  from tc\<^sub>t_app have "subst_vars \<Gamma> \<subseteq> insert ?v (vs \<union> vs\<^sub>1)" by auto
  with tc\<^sub>t_app TC2 FVS obtain \<sigma>\<^sub>2 where S2: "
    map_expr\<^sub>s (eliminate_vars (insert ?v (vs \<union> vs\<^sub>1))) (map_expr\<^sub>s (subst \<sigma>\<^sub>2) e\<^sub>u\<^sub>2) = 
      map_expr\<^sub>s to_unifiable e\<^sub>s\<^sub>2 \<and> 
    eliminate_vars (insert ?v (vs \<union> vs\<^sub>1)) (subst \<sigma>\<^sub>2 \<tau>\<^sub>2) = to_unifiable t\<^sub>1 \<and> dom \<sigma>\<^sub>2 = vs\<^sub>2 \<and> 
    subst_vars \<sigma>\<^sub>2 = {} \<and> \<sigma>\<^sub>2 unifies\<^sub>\<kappa> eliminate_vars_constr (insert ?v (vs \<union> vs\<^sub>1)) \<kappa>\<^sub>2 \<and> 
    valid_ty_subst \<sigma>\<^sub>2 \<and> idempotent \<sigma>\<^sub>2" 
      by presburger
  from tc\<^sub>t_app have FV: "?v \<notin> vs" by simp
  from tc\<^sub>t_app TC1 have VVS1: "insert ?v vs \<inter> vs\<^sub>1 = {}" by simp
  moreover from tc\<^sub>t_app TC1 TC2 have VVS2: "insert ?v (vs \<union> vs\<^sub>1) \<inter> vs\<^sub>2 = {}" by simp
  ultimately have VVS: "?v \<notin> vs\<^sub>1 \<union> vs\<^sub>2" by simp
  from VVS2 S1 S2 have DSS: "dom \<sigma>\<^sub>1 \<inter> dom \<sigma>\<^sub>2 = {}" by auto
  from tc\<^sub>t_app TC1 S1 have "valid_ty_term \<tau>\<^sub>1 \<and> valid_ty_subst \<sigma>\<^sub>1" by auto
  hence VTS1: "valid_ty_term (subst \<sigma>\<^sub>1 \<tau>\<^sub>1)" by simp
  from tc\<^sub>t_app TC2 S2 have "valid_ty_term \<tau>\<^sub>2 \<and> valid_ty_subst \<sigma>\<^sub>2" by auto
  hence VTS2: "valid_ty_term (subst \<sigma>\<^sub>2 \<tau>\<^sub>2)" by simp
  let ?\<sigma> = "extend_subst ?v (to_unifiable t\<^sub>2) (combine_subst \<sigma>\<^sub>1 \<sigma>\<^sub>2)"
  from S1 S2 have D3: "dom (combine_subst \<sigma>\<^sub>1 \<sigma>\<^sub>2) = vs\<^sub>1 \<union> vs\<^sub>2" by auto
  with FV E have A: "dom ?\<sigma> = vs'" by simp
  from tc\<^sub>t_app have VG: "?v \<notin> subst_vars \<Gamma>" by auto 
  with tc\<^sub>t_app TC1 have VE1: "?v \<notin> tyvars\<^sub>s e\<^sub>u\<^sub>1" by simp
  from tc\<^sub>t_app TC1 TC2 VG have VE2: "?v \<notin> tyvars\<^sub>s e\<^sub>u\<^sub>2" by simp
  from tc\<^sub>t_app TC1 have "tyvars\<^sub>s e\<^sub>u\<^sub>1 \<subseteq> vs\<^sub>1" by simp
  with S1 S2 DSS have HV: "dom \<sigma>\<^sub>2 \<inter> tyvars\<^sub>s e\<^sub>u\<^sub>1 = {}" by blast
  from tc\<^sub>t_app E TC1 TC2 have HV2: "tyvars\<^sub>s e\<^sub>u\<^sub>2 \<subseteq> vs\<^sub>2" by simp
  have "tyvars\<^sub>s (map_expr\<^sub>s (subst \<sigma>\<^sub>2) e\<^sub>u\<^sub>2) \<subseteq> tyvars\<^sub>s e\<^sub>u\<^sub>2 - dom \<sigma>\<^sub>2 \<union> subst_vars \<sigma>\<^sub>2" by simp
  with S2 HV2 have HVS2: "tyvars\<^sub>s (map_expr\<^sub>s (subst \<sigma>\<^sub>2) e\<^sub>u\<^sub>2) = {}" by auto
  have "tyvars\<^sub>s (map_expr\<^sub>s (subst \<sigma>\<^sub>1) e\<^sub>u\<^sub>1) \<subseteq> tyvars\<^sub>s e\<^sub>u\<^sub>1 - dom \<sigma>\<^sub>1 \<union> subst_vars \<sigma>\<^sub>1" by simp
  with VE1 S1 have "?v \<notin> tyvars\<^sub>s (map_expr\<^sub>s (subst \<sigma>\<^sub>1) e\<^sub>u\<^sub>1)" by blast
  with S1 HV have "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst \<sigma>\<^sub>1) (map_expr\<^sub>s (subst \<sigma>\<^sub>2) e\<^sub>u\<^sub>1)) = 
    map_expr\<^sub>s to_unifiable e\<^sub>s\<^sub>1" by simp
  hence PS1: "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst \<sigma>\<^sub>1 \<circ> subst \<sigma>\<^sub>2) e\<^sub>u\<^sub>1) = 
    map_expr\<^sub>s to_unifiable e\<^sub>s\<^sub>1" by (simp add: expr\<^sub>s.map_comp)
  from S2 HVS2 have "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst \<sigma>\<^sub>1) (map_expr\<^sub>s (subst \<sigma>\<^sub>2) e\<^sub>u\<^sub>2)) = 
    map_expr\<^sub>s to_unifiable e\<^sub>s\<^sub>2" by simp
  hence "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst \<sigma>\<^sub>1 \<circ> subst \<sigma>\<^sub>2) e\<^sub>u\<^sub>2) = 
    map_expr\<^sub>s to_unifiable e\<^sub>s\<^sub>2" by (simp add: expr\<^sub>s.map_comp)
  with VE1 VE2 PS1 have "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst ?\<sigma>) e\<^sub>u\<^sub>1) = 
      map_expr\<^sub>s to_unifiable e\<^sub>s\<^sub>1 \<and>
    map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst ?\<sigma>) e\<^sub>u\<^sub>2) = map_expr\<^sub>s to_unifiable e\<^sub>s\<^sub>2" by simp
  hence B: "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst ?\<sigma>) (App\<^sub>s e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2)) = 
    map_expr\<^sub>s to_unifiable (App\<^sub>s e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2)" by simp
  have C: "eliminate_vars vs (subst ?\<sigma> (Var ?v)) = to_unifiable t\<^sub>2" by simp
  from S1 S2 DSS VVS D3 have D: "subst_vars ?\<sigma> = {}" by simp
  from S1 S2 have VCS: "?v \<notin> subst_vars \<sigma>\<^sub>1 \<and> ?v \<notin> subst_vars \<sigma>\<^sub>2" by auto
  from S1 S2 have D2S1: "dom \<sigma>\<^sub>2 \<inter> subst_vars \<sigma>\<^sub>1 = {}" by auto
  from tc\<^sub>t_app TC1 VG have "?v \<notin> constr_vars \<kappa>\<^sub>1" by simp
  with VVS S1 S2 DSS D2S1 have UC1: "?\<sigma> unifies\<^sub>\<kappa> eliminate_vars_constr vs \<kappa>\<^sub>1" by simp  
  from tc\<^sub>t_app TC1 TC2 E have "constr_vars \<kappa>\<^sub>2 \<subseteq> vs\<^sub>2 \<union> subst_vars \<Gamma>" by simp
  with tc\<^sub>t_app VVS2 have CV2: "constr_vars \<kappa>\<^sub>2 \<inter> vs\<^sub>1 \<subseteq> vs" by auto
  from tc\<^sub>t_app TC1 TC2 VG have "?v \<notin> constr_vars \<kappa>\<^sub>2" by simp
  with CV2 VVS S1 S2 DSS have UC2: "?\<sigma> unifies\<^sub>\<kappa> eliminate_vars_constr vs \<kappa>\<^sub>2" by simp
  from tc\<^sub>t_app TC1 have UV1: "uvars \<tau>\<^sub>1 \<subseteq> vs\<^sub>1 \<union> subst_vars \<Gamma>" by simp
  with VG VVS have VT1: "?v \<notin> uvars \<tau>\<^sub>1" by auto
  from DSS VVS2 have "vs\<^sub>2 \<inter> (vs\<^sub>1 \<union> vs) = {}" by blast
  with tc\<^sub>t_app(6) S2 UV1 have DU1: "dom \<sigma>\<^sub>2 \<inter> uvars \<tau>\<^sub>1 = {}" by blast
  from tc\<^sub>t_app TC1 TC2 E have UV2: "uvars \<tau>\<^sub>2 \<subseteq> vs\<^sub>2 \<union> subst_vars \<Gamma>" by simp
  with VG VVS have VT2: "?v \<notin> uvars \<tau>\<^sub>2" by auto
  have "uvars (subst \<sigma>\<^sub>1 \<tau>\<^sub>1) \<subseteq> uvars \<tau>\<^sub>1 - dom \<sigma>\<^sub>1 \<union> subst_vars \<sigma>\<^sub>1" by simp
  with S1 UV1 have "uvars (subst \<sigma>\<^sub>1 \<tau>\<^sub>1) \<subseteq> (vs\<^sub>1 - insert ?v vs \<union> subst_vars \<Gamma>) - (vs\<^sub>1 - insert ?v vs)" 
    by auto
  with tc\<^sub>t_app(6) have US1: "uvars (subst \<sigma>\<^sub>1 \<tau>\<^sub>1) \<subseteq> vs" by auto
  have "uvars (subst \<sigma>\<^sub>2 \<tau>\<^sub>2) \<subseteq> uvars \<tau>\<^sub>2 - dom \<sigma>\<^sub>2 \<union> subst_vars \<sigma>\<^sub>2" by simp
  with tc\<^sub>t_app(6) S2 UV2 have US2: "uvars (subst \<sigma>\<^sub>2 \<tau>\<^sub>2) \<subseteq> vs" by blast
  with S1 VVS1 have DU2: "dom \<sigma>\<^sub>1 \<inter> uvars (subst \<sigma>\<^sub>2 \<tau>\<^sub>2) = {}" by auto
  from S1 VVS1 have DSV1: "dom \<sigma>\<^sub>1 \<inter> vs = {}" by auto
  from S2 VVS2 have DSV2: "dom \<sigma>\<^sub>2 \<inter> vs = {}" by auto
  from S1 obtain tt1 tt2 where SS1: "subst \<sigma>\<^sub>1 \<tau>\<^sub>1 = Arrow\<^sub>\<tau> tt1 tt2 \<and> 
    eliminate_vars (insert ?v vs) tt1 = to_unifiable t\<^sub>1 \<and> 
    eliminate_vars (insert ?v vs) tt2 = to_unifiable t\<^sub>2" by auto
  from US1 SS1 have "uvars tt1 \<subseteq> vs \<and> uvars tt2 \<subseteq> vs" by simp
  with FV SS1 have PT1: "eliminate_vars vs tt1 = to_unifiable t\<^sub>1 \<and> 
    eliminate_vars vs tt2 = to_unifiable t\<^sub>2" by force
  from US2 have USV21: "uvars (subst \<sigma>\<^sub>2 \<tau>\<^sub>2) \<inter> vs\<^sub>1 \<subseteq> vs" by auto
  from US2 FV have "?v \<notin> uvars (subst \<sigma>\<^sub>2 \<tau>\<^sub>2)" by auto
  with S2 USV21 have "eliminate_vars vs (subst \<sigma>\<^sub>2 \<tau>\<^sub>2) = to_unifiable t\<^sub>1" by simp
  with FV UC1 UC2 S1 S2 DSV1 DSV2 VT1 VT2 DU1 DU2 SS1 PT1 have F: "
    ?\<sigma> unifies\<^sub>\<kappa> eliminate_vars_constr vs (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(\<tau>\<^sub>1, Arrow\<^sub>\<tau> \<tau>\<^sub>2 (Var ?v))])" 
      by (simp add: expand_extend_subst)
  from S1 S2 DSS VVS D3 have G: "idempotent ?\<sigma>" by simp
  from S1 S2 have "valid_ty_subst ?\<sigma>" by simp
  with E A B C D F G show ?case by blast
next
  case (tc\<^sub>t_let e\<^sub>1 t\<^sub>1 x e\<^sub>2 t\<^sub>2)
  let ?v = "fresh vs"
  obtain e\<^sub>u\<^sub>1 \<tau>\<^sub>1 vs\<^sub>1 \<kappa>\<^sub>1 where TC1: "typecheck' \<Gamma> (insert ?v vs) (erase e\<^sub>1) = (e\<^sub>u\<^sub>1, \<tau>\<^sub>1, vs\<^sub>1, \<kappa>\<^sub>1)" 
    by (metis prod_cases4)
  obtain e\<^sub>u\<^sub>2 \<tau>\<^sub>2 vs\<^sub>2 \<kappa>\<^sub>2 where TC2: "typecheck' (\<Gamma>(x \<mapsto> Var ?v)) (insert ?v (vs \<union> vs\<^sub>1)) (erase e\<^sub>2) =
    (e\<^sub>u\<^sub>2, \<tau>\<^sub>2, vs\<^sub>2, \<kappa>\<^sub>2)" by (metis prod_cases4)
  with tc\<^sub>t_let TC1 have E: "e\<^sub>u = Let\<^sub>s x e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2 \<and> \<tau> = \<tau>\<^sub>2 \<and> vs' = insert ?v (vs\<^sub>1 \<union> vs\<^sub>2) \<and> 
    \<kappa> = \<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(Var ?v, \<tau>\<^sub>1)]" by (simp add: Let_def)
  from tc\<^sub>t_let have "subst_vars \<Gamma> \<subseteq> insert ?v vs" by auto
  with tc\<^sub>t_let TC1 obtain \<sigma>\<^sub>1 where S1: "
    map_expr\<^sub>s (eliminate_vars (insert ?v vs)) (map_expr\<^sub>s (subst \<sigma>\<^sub>1) e\<^sub>u\<^sub>1) = map_expr\<^sub>s to_unifiable e\<^sub>1 \<and>
    eliminate_vars (insert ?v vs) (subst \<sigma>\<^sub>1 \<tau>\<^sub>1) = to_unifiable t\<^sub>1 \<and> dom \<sigma>\<^sub>1 = vs\<^sub>1 \<and>
    subst_vars \<sigma>\<^sub>1 = {} \<and> \<sigma>\<^sub>1 unifies\<^sub>\<kappa> eliminate_vars_constr (insert ?v vs) \<kappa>\<^sub>1 \<and> valid_ty_subst \<sigma>\<^sub>1 \<and> 
    idempotent \<sigma>\<^sub>1" by blast
  from tc\<^sub>t_let have X: "subst_vars \<Gamma> \<subseteq> insert ?v (vs \<union> vs\<^sub>1) - {?v}" by auto
  from tc\<^sub>t_let TC1 have U: "uvars \<tau>\<^sub>1 \<subseteq> vs\<^sub>1 \<union> subst_vars \<Gamma>" by simp
  have "uvars (subst \<sigma>\<^sub>1 \<tau>\<^sub>1) \<subseteq> uvars \<tau>\<^sub>1 - dom \<sigma>\<^sub>1 \<union> subst_vars \<sigma>\<^sub>1" by simp
  with S1 U have U': "uvars (subst \<sigma>\<^sub>1 \<tau>\<^sub>1) \<subseteq> subst_vars \<Gamma>" by blast
  with tc\<^sub>t_let have Y: "uvars (subst \<sigma>\<^sub>1 \<tau>\<^sub>1) \<subseteq> insert ?v (vs \<union> vs\<^sub>1) - {?v}" by auto
  from tc\<^sub>t_let TC1 have "finite (insert ?v (vs \<union> vs\<^sub>1))" by simp
  with TC2 X Y have TC2': "typecheck' (\<Gamma>(x \<mapsto> subst \<sigma>\<^sub>1 \<tau>\<^sub>1)) (insert ?v (vs \<union> vs\<^sub>1)) (erase e\<^sub>2) = 
    (map_expr\<^sub>s (subst [?v \<mapsto> subst \<sigma>\<^sub>1 \<tau>\<^sub>1]) e\<^sub>u\<^sub>2, subst [?v \<mapsto> subst \<sigma>\<^sub>1 \<tau>\<^sub>1] \<tau>\<^sub>2, vs\<^sub>2, 
      constr_subst ?v (subst \<sigma>\<^sub>1 \<tau>\<^sub>1) \<kappa>\<^sub>2)" by simp

  from S1 have T1: "t\<^sub>1 = to_type (eliminate_vars (insert ?v vs) (subst \<sigma>\<^sub>1 \<tau>\<^sub>1))" by simp
  from tc\<^sub>t_let U' have "uvars (subst \<sigma>\<^sub>1 \<tau>\<^sub>1) \<subseteq> insert ?v vs" by auto
  with T1 have A: "(map_option to_type \<circ> \<Gamma>)(x \<mapsto> t\<^sub>1) = map_option to_type \<circ> (\<Gamma>(x \<mapsto> subst \<sigma>\<^sub>1 \<tau>\<^sub>1))" 
    by simp
  from X Y have B: "subst_vars (\<Gamma>(x \<mapsto> subst \<sigma>\<^sub>1 \<tau>\<^sub>1)) \<subseteq> insert ?v (vs \<union> vs\<^sub>1)" 
    by (auto simp add: subst_vars_def ran_def)
  from tc\<^sub>t_let TC1 have "valid_ty_term \<tau>\<^sub>1" by auto
  with S1 have "valid_ty_term (subst \<sigma>\<^sub>1 \<tau>\<^sub>1)" by simp
  with tc\<^sub>t_let have C: "valid_ty_subst (\<Gamma>(x \<mapsto> subst \<sigma>\<^sub>1 \<tau>\<^sub>1))" by simp
  from tc\<^sub>t_let TC1 have "finite (insert ?v (vs \<union> vs\<^sub>1))" by simp
  with tc\<^sub>t_let TC2' A B C obtain \<sigma>\<^sub>2 where S2: "map_expr\<^sub>s (eliminate_vars (insert ?v (vs \<union> vs\<^sub>1))) 
    (map_expr\<^sub>s (subst \<sigma>\<^sub>2) (map_expr\<^sub>s (subst [?v \<mapsto> subst \<sigma>\<^sub>1 \<tau>\<^sub>1]) e\<^sub>u\<^sub>2)) = map_expr\<^sub>s to_unifiable e\<^sub>2 \<and>
    eliminate_vars (insert ?v (vs \<union> vs\<^sub>1)) (subst \<sigma>\<^sub>2 (subst [?v \<mapsto> subst \<sigma>\<^sub>1 \<tau>\<^sub>1] \<tau>\<^sub>2)) = to_unifiable t\<^sub>2 \<and>
    dom \<sigma>\<^sub>2 = vs\<^sub>2 \<and> subst_vars \<sigma>\<^sub>2 = {} \<and> 
    \<sigma>\<^sub>2 unifies\<^sub>\<kappa> eliminate_vars_constr (insert ?v (vs \<union> vs\<^sub>1)) (constr_subst ?v (subst \<sigma>\<^sub>1 \<tau>\<^sub>1) \<kappa>\<^sub>2) \<and> 
    valid_ty_subst \<sigma>\<^sub>2 \<and> idempotent \<sigma>\<^sub>2" by presburger


  from tc\<^sub>t_let have "map_option to_type \<circ> \<Gamma> \<turnstile>\<^sub>t e\<^sub>1 : t\<^sub>1" by simp
  from tc\<^sub>t_let have "(map_option to_type \<circ> \<Gamma>)(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>t e\<^sub>2 : t\<^sub>2" by simp
  from tc\<^sub>t_let have "finite vs" by simp
  from tc\<^sub>t_let have "subst_vars \<Gamma> \<subseteq> vs" by simp
  from tc\<^sub>t_let have "valid_ty_subst \<Gamma>" by simp

  let ?\<sigma> = "extend_subst ?v (to_unifiable t\<^sub>2) (combine_subst \<sigma>\<^sub>1 \<sigma>\<^sub>2)"

  from tc\<^sub>t_let TC1 have "insert ?v vs \<inter> vs\<^sub>1 = {}" by simp
  hence V1: "?v \<notin> vs\<^sub>1" by simp



  have "map_expr\<^sub>s (eliminate_vars vs) (map_expr\<^sub>s (subst ?\<sigma>) (Let\<^sub>s x e\<^sub>u\<^sub>1 e\<^sub>u\<^sub>2)) = 
    map_expr\<^sub>s to_unifiable (Let\<^sub>s x e\<^sub>1 e\<^sub>2) \<and> eliminate_vars vs (subst ?\<sigma> \<tau>\<^sub>2) = to_unifiable t\<^sub>2 \<and> 
    dom ?\<sigma> = insert ?v (vs\<^sub>1 \<union> vs\<^sub>2) \<and> subst_vars ?\<sigma> = {} \<and> 
    ?\<sigma> unifies\<^sub>\<kappa> eliminate_vars_constr vs (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2 @ [(Var ?v, \<tau>\<^sub>1)]) \<and> 
    valid_ty_subst ?\<sigma> \<and> idempotent ?\<sigma>" by simp
  with E show ?case by blast
qed auto

text \<open>With \<open>typecheck_finds_subst\<close> in hand, our failure case is now quite simple:\<close>

theorem typecheck_fails [simp]: "typecheck e\<^sub>s = None \<Longrightarrow> \<nexists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>t e\<^sub>t : t) \<and> e\<^sub>s = erase e\<^sub>t"
proof                              
  assume "typecheck e\<^sub>s = None"
  then obtain e\<^sub>u \<tau> vs' \<kappa> where X: "typecheck' Map.empty {} e\<^sub>s = (e\<^sub>u, \<tau>, vs', \<kappa>) \<and> unify \<kappa> = None" 
    by (auto split: prod.splits option.splits)
  assume "\<exists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>t e\<^sub>t : t) \<and> e\<^sub>s = erase e\<^sub>t"
  then obtain e\<^sub>t t where Y: "(map_option to_type \<circ> Map.empty \<turnstile>\<^sub>t e\<^sub>t : t) \<and> e\<^sub>s = erase e\<^sub>t" by fastforce
  have Z: "subst_vars Map.empty \<subseteq> {}" by simp
  have "valid_ty_subst Map.empty \<and> finite {}" by simp
  with X Y Z have "\<exists>\<sigma>. map_expr\<^sub>s (eliminate_vars {}) (map_expr\<^sub>s (subst \<sigma>) e\<^sub>u) = 
      map_expr\<^sub>s to_unifiable e\<^sub>t \<and> 
    eliminate_vars {} (subst \<sigma> \<tau>) = to_unifiable t \<and> dom \<sigma> = vs' \<and> subst_vars \<sigma> = {} \<and> 
    \<sigma> unifies\<^sub>\<kappa> eliminate_vars_constr {} \<kappa> \<and> valid_ty_subst \<sigma> \<and> idempotent \<sigma>" 
      using typecheck_finds_subst by blast
  then obtain \<sigma> where "\<sigma> unifies\<^sub>\<kappa> eliminate_vars_constr {} \<kappa> \<and> idempotent \<sigma>" by blast
  hence "\<exists>\<sigma>'. unify \<kappa> = Some \<sigma>' \<and> \<sigma> specializes \<sigma>'" by simp
  with X show "False" by simp
qed

end