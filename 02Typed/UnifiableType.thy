theory UnifiableType
  imports TypedLanguage "../00Utils/Unification/Unification"
begin

subsection \<open>Unifiable Types\<close>

text \<open>Before we can define the typechecking algorithm itself, we need to define a conversion between
our actual types and unifiable terms.\<close>

abbreviation Num\<^sub>\<tau> :: "uterm" where
  "Num\<^sub>\<tau> \<equiv> Ctor ''Num'' []"

abbreviation Arrow\<^sub>\<tau> :: "uterm \<Rightarrow> uterm \<Rightarrow> uterm" where
  "Arrow\<^sub>\<tau> \<tau>\<^sub>1 \<tau>\<^sub>2 \<equiv> Ctor ''Arrow'' [\<tau>\<^sub>1, \<tau>\<^sub>2]"

primrec to_unifiable :: "ty \<Rightarrow> uterm" where
  "to_unifiable Num = Num\<^sub>\<tau>"
| "to_unifiable (Arrow t\<^sub>1 t\<^sub>2) = Arrow\<^sub>\<tau> (to_unifiable t\<^sub>1) (to_unifiable t\<^sub>2)"

lemma uvars_of_type [simp]: "uvars (to_unifiable t) = {}"
  by (induction t) simp_all

text \<open>The reverse direction presents some complications. Not every term corresponds to a type; we 
can solve this simply enough with a well-formedness condition \<open>valid_ty_uexpr\<close>. More subtly, a term 
may contain free variables, and a type cannot. We map all term variables, arbitrarily, to the \<open>Num\<close> 
type. Any choice would do as well, of course, but the fact that we have had to make a choice at all 
will lead to some properties becoming more complicated down the line.\<close>

fun to_type :: "uterm \<Rightarrow> ty" where
  "to_type (Var v) = Num"
| "to_type (Ctor \<gamma> []) = (if \<gamma> = ''Num'' then Num else undefined)"
| "to_type (Ctor \<gamma> [\<tau>\<^sub>1, \<tau>\<^sub>2]) = 
    (if \<gamma> = ''Arrow'' then Arrow (to_type \<tau>\<^sub>1) (to_type \<tau>\<^sub>2) else undefined)"
| "to_type (Ctor \<gamma> \<tau>s) = undefined"

fun valid_ty_term' :: "string \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_ty_term' \<gamma> 0 = (\<gamma> = ''Num'')"
| "valid_ty_term' \<gamma> (Suc 0) = False"
| "valid_ty_term' \<gamma> (Suc (Suc 0)) = (\<gamma> = ''Arrow'')"
| "valid_ty_term' \<gamma> (Suc (Suc (Suc x))) = False"

primrec valid_ty_term :: "uterm \<Rightarrow> bool" where
  "valid_ty_term (Var v) = True"
| "valid_ty_term (Ctor \<gamma> \<tau>s) = (valid_ty_term' \<gamma> (length \<tau>s) \<and> list_all valid_ty_term \<tau>s)"

lemma to_unif_to_type [simp]: "to_type (to_unifiable t) = t"
  by (induction t) simp_all

lemma to_type_to_unif [simp]: "valid_ty_term \<tau> \<Longrightarrow> uvars \<tau> = {} \<Longrightarrow> to_unifiable (to_type \<tau>) = \<tau>"
  by (induction \<tau> rule: to_type.induct) simp_all

lemma to_unifiable_valid [simp]: "valid_ty_term (to_unifiable t)"
  by (induction t) simp_all

text \<open>We extend our well-formedness condition to substitutions in the obvious way:\<close>

definition valid_ty_subst :: "subst \<Rightarrow> bool" where
  "valid_ty_subst \<sigma> \<equiv> (\<forall>\<tau> \<in> ran \<sigma>. valid_ty_term \<tau>)"

lemma valid_empty_subst [simp]: "valid_ty_subst Map.empty"
  by (simp add: valid_ty_subst_def)

lemma valid_upd_subst [simp]: "valid_ty_subst \<sigma> \<Longrightarrow> valid_ty_term \<tau> \<Longrightarrow> valid_ty_subst (\<sigma>(x \<mapsto> \<tau>))"
  by (auto simp add: valid_ty_subst_def ran_def)

lemma valid_term_from_subst [elim]: "valid_ty_subst \<sigma> \<Longrightarrow> \<sigma> x = Some \<tau> \<Longrightarrow> valid_ty_term \<tau>"
  by (auto simp add: valid_ty_subst_def ran_def)

lemma valid_substituted_term [simp]: "valid_ty_term \<tau> \<Longrightarrow> valid_ty_subst \<sigma> \<Longrightarrow> 
    valid_ty_term (subst \<sigma> \<tau>)"
  and "list_all valid_ty_term \<tau>s \<Longrightarrow> valid_ty_subst \<sigma> \<Longrightarrow> 
    list_all valid_ty_term (map (subst \<sigma>) \<tau>s)"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) 
     (auto simp add: valid_ty_subst_def ran_def split: option.splits)

lemma valid_extend_subst [simp]: "valid_ty_subst \<sigma> \<Longrightarrow> valid_ty_term \<tau> \<Longrightarrow> 
    valid_ty_subst (extend_subst x \<tau> \<sigma>)"
  by (auto simp add: valid_ty_subst_def extend_subst_def ran_def)

lemma valid_combine_subst [simp]: "valid_ty_subst \<sigma>\<^sub>1 \<Longrightarrow> valid_ty_subst \<sigma>\<^sub>2 \<Longrightarrow> 
  valid_ty_subst (combine_subst \<sigma>\<^sub>1 \<sigma>\<^sub>2)"
proof (unfold valid_ty_subst_def combine_subst_def ran_def, rule)
  fix \<tau>
  assume S1: "\<forall>\<tau>' \<in> {\<tau>''. \<exists>x. \<sigma>\<^sub>1 x = Some \<tau>''}. valid_ty_term \<tau>'"
  assume S2: "\<forall>\<tau>' \<in> {\<tau>''. \<exists>x. \<sigma>\<^sub>2 x = Some \<tau>''}. valid_ty_term \<tau>'"
  assume "\<tau> \<in> {\<tau>''. \<exists>x. (case \<sigma>\<^sub>2 x of None \<Rightarrow> \<sigma>\<^sub>1 x | Some \<tau>' \<Rightarrow> Some (subst \<sigma>\<^sub>1 \<tau>')) = Some \<tau>''}"
  then obtain x where X: "(case \<sigma>\<^sub>2 x of None \<Rightarrow> \<sigma>\<^sub>1 x | Some \<tau>' \<Rightarrow> Some (subst \<sigma>\<^sub>1 \<tau>')) = Some \<tau>" 
    by auto
  from S1 S2 X show "valid_ty_term \<tau>" 
  proof (cases "\<sigma>\<^sub>2 x")
    case (Some \<tau>')
    from S1 have "valid_ty_subst \<sigma>\<^sub>1" by (auto simp add: valid_ty_subst_def ran_def)
    with S2 X Some show ?thesis by auto
  qed auto
qed

text \<open>We also extend it to expressions annotated with unifiable types:\<close>

primrec valid_ty_expr :: "uterm expr\<^sub>s \<Rightarrow> bool" where
  "valid_ty_expr (Var\<^sub>s x) = True"
| "valid_ty_expr (Const\<^sub>s n) = True"
| "valid_ty_expr (Lam\<^sub>s x \<tau> e) = (valid_ty_term \<tau> \<and> valid_ty_expr e)"
| "valid_ty_expr (App\<^sub>s e\<^sub>1 e\<^sub>2) = (valid_ty_expr e\<^sub>1 \<and> valid_ty_expr e\<^sub>2)"
| "valid_ty_expr (Let\<^sub>s x e\<^sub>1 e\<^sub>2) = (valid_ty_expr e\<^sub>1 \<and> valid_ty_expr e\<^sub>2)"

text \<open>Now on to the promised complications. Because the types we produce are not the fully-general 
ones produced by the unification algorithm, we need an operation to replace term variables with 
\<open>Num\<^sub>\<tau>\<close>s. But we still may need to instantiate some of them, to extend a subexpression type 
reconstruction to a larger expression. So we provide a set of variables to eliminate:\<close>

definition eliminate_vars :: "var set \<Rightarrow> uterm \<Rightarrow> uterm" where
  "eliminate_vars vs \<equiv> subst (\<lambda>x. if x \<in> vs then Some Num\<^sub>\<tau> else None)"

lemma eliminate_no_vars [simp]: "eliminate_vars {} \<tau> = \<tau>"
  by (simp add: eliminate_vars_def)

lemma eliminate_unused_var [simp]: "x \<notin> uvars \<tau> \<Longrightarrow> 
    eliminate_vars (insert x vs) \<tau> = eliminate_vars vs \<tau>"
  and "x \<notin> uvarss \<tau>s \<Longrightarrow> map (eliminate_vars (insert x vs)) \<tau>s = map (eliminate_vars vs) \<tau>s"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) (simp_all add: eliminate_vars_def)

lemma eliminate_all_vars [simp]: "uvars \<tau> \<subseteq> vs \<Longrightarrow> valid_ty_term \<tau> \<Longrightarrow> 
    eliminate_vars vs \<tau> = to_unifiable (to_type \<tau>)"
  by (induction \<tau> rule: to_type.induct) (simp_all add: eliminate_vars_def)

lemma eliminate_all_vars_ran [simp]: "subst_vars \<sigma> \<subseteq> vs \<Longrightarrow> valid_ty_subst \<sigma> \<Longrightarrow> \<sigma> x = Some \<tau> \<Longrightarrow> 
    eliminate_vars vs \<tau> = to_unifiable (to_type \<tau>)"
proof -
  assume "valid_ty_subst \<sigma>" and T: "\<sigma> x = Some \<tau>"
  hence X: "valid_ty_term \<tau>" by auto
  assume "subst_vars \<sigma> \<subseteq> vs" 
  with T have "uvars \<tau> \<subseteq> vs" by auto
  with X show ?thesis by simp
qed

lemma eliminate_vars_simp_var [simp]: "eliminate_vars vs (Var x) = (if x \<in> vs then Num\<^sub>\<tau> else Var x)"
  by (simp add: eliminate_vars_def)

lemma eliminate_vars_simp_ctor [simp]: "eliminate_vars vs (Ctor \<gamma> \<tau>s) = 
    Ctor \<gamma> (map (eliminate_vars vs) \<tau>s)"
  by (simp add: eliminate_vars_def)

lemma eliminate_vars_to_arrow [dest]: "eliminate_vars vs \<tau> = Arrow\<^sub>\<tau> \<tau>\<^sub>1 \<tau>\<^sub>2 \<Longrightarrow> \<exists>\<tau>\<^sub>1' \<tau>\<^sub>2'. 
    \<tau> = Arrow\<^sub>\<tau> \<tau>\<^sub>1' \<tau>\<^sub>2' \<and> eliminate_vars vs \<tau>\<^sub>1' = \<tau>\<^sub>1 \<and> eliminate_vars vs \<tau>\<^sub>2' = \<tau>\<^sub>2"
  by (induction \<tau>) (auto simp add: eliminate_vars_def split: if_splits)

lemma eliminate_vars_closed [simp]: "uvars \<tau> = {} \<Longrightarrow> eliminate_vars vs \<tau> = \<tau>"
  and "uvarss \<tau>s = {} \<Longrightarrow> map (eliminate_vars vs) \<tau>s = \<tau>s"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) simp_all

lemma subst_eliminate_vars [simp]: "dom \<sigma> \<inter> vs = {} \<Longrightarrow> subst_vars \<sigma> = {} \<Longrightarrow> 
  subst \<sigma> (eliminate_vars vs \<tau>) = eliminate_vars vs (subst \<sigma> \<tau>)"
proof (induction \<tau>)
  case (Var x)
  thus ?case
  proof (cases "\<sigma> x")
    case (Some \<tau>)
    moreover with Var have "uvars \<tau> = {}" by (auto simp add: subst_vars_def ran_def)
    moreover from Var Some have "x \<notin> vs" by auto
    ultimately show ?thesis by simp
  qed (simp_all add: eliminate_vars_def)
qed simp_all

lemma eliminate_extra_union [simp]: "uvars \<tau> \<inter> vs' \<subseteq> vs \<Longrightarrow> 
    eliminate_vars (vs \<union> vs') \<tau> = eliminate_vars vs \<tau>"
  and "uvarss \<tau>s \<inter> vs' \<subseteq> vs \<Longrightarrow> 
    map (eliminate_vars (vs \<union> vs')) \<tau>s = map (eliminate_vars vs) \<tau>s"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) auto

text \<open>Again, we extend in the obvious way to constraints.\<close>

abbreviation eliminate_vars_constr :: "var set \<Rightarrow> constraint \<Rightarrow> constraint" where
  "eliminate_vars_constr vs \<equiv> map (\<lambda>(\<tau>\<^sub>1, \<tau>\<^sub>2). (eliminate_vars vs \<tau>\<^sub>1, eliminate_vars vs \<tau>\<^sub>2))"

lemma eliminate_unused_var_constr [simp]: "x \<notin> constr_vars \<kappa> \<Longrightarrow> 
    eliminate_vars_constr (insert x vs) \<kappa> = eliminate_vars_constr vs \<kappa>"
  by (induction \<kappa> rule: constr_vars.induct) simp_all

lemma constr_subst_eliminate_vars [simp]: "x \<notin> vs \<Longrightarrow>
  constr_subst x (to_unifiable \<tau>) (eliminate_vars_constr vs \<kappa>) = 
    eliminate_vars_constr vs (constr_subst x (to_unifiable \<tau>) \<kappa>)"
  by (induction x "to_unifiable \<tau>" \<kappa> rule: constr_subst.induct) simp_all

lemma eliminate_extra_union_constr [simp]: "constr_vars \<kappa> \<inter> vs' \<subseteq> vs \<Longrightarrow> 
  eliminate_vars_constr (vs \<union> vs') \<kappa> = eliminate_vars_constr vs \<kappa>"
proof (induction \<kappa> rule: constr_vars.induct)
  case (2 \<tau>\<^sub>1 \<tau>\<^sub>2 \<kappa>)
  moreover hence "uvars \<tau>\<^sub>1 \<inter> vs' \<subseteq> vs \<and> uvars \<tau>\<^sub>2 \<inter> vs' \<subseteq> vs" by auto
  ultimately show ?case by fastforce
qed simp_all

text \<open>Finally, we define a free type-variables operation on expressions annotated with unifiable 
types.\<close>

primrec tyvars\<^sub>s :: "uterm expr\<^sub>s \<Rightarrow> var set" where
  "tyvars\<^sub>s (Var\<^sub>s x) = {}"
| "tyvars\<^sub>s (Const\<^sub>s n) = {}"
| "tyvars\<^sub>s (Lam\<^sub>s x \<tau> e) = uvars \<tau> \<union> tyvars\<^sub>s e"
| "tyvars\<^sub>s (App\<^sub>s e\<^sub>1 e\<^sub>2) = tyvars\<^sub>s e\<^sub>1 \<union> tyvars\<^sub>s e\<^sub>2"
| "tyvars\<^sub>s (Let\<^sub>s x e\<^sub>1 e\<^sub>2) = tyvars\<^sub>s e\<^sub>1 \<union> tyvars\<^sub>s e\<^sub>2"

lemma tyvars_subst_expr [simp]: "tyvars\<^sub>s (map_expr\<^sub>s (subst \<sigma>) e) \<subseteq> 
  tyvars\<^sub>s e - dom \<sigma> \<union> subst_vars \<sigma>"
proof (induction e)
  case (Lam\<^sub>s x \<tau> e)
  moreover have "uvars (subst \<sigma> \<tau>) \<subseteq> uvars \<tau> - dom \<sigma> \<union> subst_vars \<sigma>" by simp
  ultimately show ?case by fastforce
qed auto

lemma eliminate_from_closed_expr [simp]: "tyvars\<^sub>s e = {} \<Longrightarrow> map_expr\<^sub>s (eliminate_vars vs) e = e"
  by (induction e) simp_all

lemma eliminate_unused_var_expr [simp]: "x \<notin> tyvars\<^sub>s e \<Longrightarrow> 
    map_expr\<^sub>s (eliminate_vars (insert x vs)) e = map_expr\<^sub>s (eliminate_vars vs) e"
  by (induction e) simp_all

lemma subst_unused_vars_expr [simp]: "dom \<sigma> \<inter> tyvars\<^sub>s e = {} \<Longrightarrow> map_expr\<^sub>s (subst \<sigma>) e = e"
proof (induction e)
  case (Lam\<^sub>s x \<tau> e)
  moreover hence "dom \<sigma> \<inter> uvars \<tau> = {}" by auto
  ultimately show ?case by auto
qed auto

lemma subst_conbine_subst_expr [simp]: "map_expr\<^sub>s (subst (combine_subst s t)) e = 
    map_expr\<^sub>s (subst s) (map_expr\<^sub>s (subst t) e)"
  by (induction e) simp_all

text \<open>This is also a convenient place to place some other miscellaneous lemmas about term-annotated 
expressions.\<close>

lemma extend_subst_on_expr [simp]: "map_expr\<^sub>s (subst (extend_subst x \<tau> \<sigma>)) e = 
    map_expr\<^sub>s (subst \<sigma>) (map_expr\<^sub>s (subst [x \<mapsto> \<tau>]) e)"
  by (induction e) (simp_all only: expr\<^sub>s.map expand_extend_subst comp_def)

end