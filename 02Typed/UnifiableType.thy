theory UnifiableType
  imports Type "../00Utils/Unification/Unification"
begin

definition env_subst :: "subst \<Rightarrow> subst \<Rightarrow> subst" where
  "env_subst sub \<Gamma> \<equiv> map_option (subst sub) \<circ> \<Gamma>"

fun typeify :: "uterm \<Rightarrow> ty" where
  "typeify (Var v) = Num"
| "typeify (Ctor \<gamma> []) = (if \<gamma> = ''Num'' then Num else undefined)"
| "typeify (Ctor \<gamma> [\<tau>\<^sub>1, \<tau>\<^sub>2]) = 
    (if \<gamma> = ''Arrow'' then Arrow (typeify \<tau>\<^sub>1) (typeify \<tau>\<^sub>2) else undefined)"
| "typeify (Ctor \<gamma> \<tau>s) = undefined"

primrec untypeify :: "ty \<Rightarrow> uterm" where
  "untypeify Num = Ctor ''Num'' []"
| "untypeify (Arrow t\<^sub>1 t\<^sub>2) = Ctor ''Arrow'' [untypeify t\<^sub>1, untypeify t\<^sub>2]"

definition partial_typeify :: "var set \<Rightarrow> uterm \<Rightarrow> uterm" where
  "partial_typeify vs t \<equiv> subst (\<lambda>x. if x \<in> vs then Some (Ctor ''Num'' []) else None) t"

abbreviation partial_typeify_constr :: "var set \<Rightarrow> constraint \<Rightarrow> constraint" where
  "partial_typeify_constr vs k \<equiv> map (\<lambda>(e1, e2). (partial_typeify vs e1, partial_typeify vs e2)) k"

fun valid_ty_uexpr' :: "string \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_ty_uexpr' \<gamma> 0 = (\<gamma> = ''Num'')"
| "valid_ty_uexpr' \<gamma> (Suc 0) = False"
| "valid_ty_uexpr' \<gamma> (Suc (Suc 0)) = (\<gamma> = ''Arrow'')"
| "valid_ty_uexpr' \<gamma> (Suc (Suc (Suc x))) = False"

primrec valid_ty_uexpr :: "uterm \<Rightarrow> bool" where
  "valid_ty_uexpr (Var v) = True"
| "valid_ty_uexpr (Ctor \<gamma> \<tau>s) = (valid_ty_uexpr' \<gamma> (length \<tau>s) \<and> list_all valid_ty_uexpr \<tau>s)"

definition valid_ty_uexprs :: "constraint \<Rightarrow> bool" where
  "valid_ty_uexprs \<tau>s = list_all (\<lambda>(\<tau>\<^sub>1, \<tau>\<^sub>2). valid_ty_uexpr \<tau>\<^sub>1 \<and> valid_ty_uexpr \<tau>\<^sub>2) \<tau>s"
 
definition valid_ty_subst :: "subst \<Rightarrow> bool" where
  "valid_ty_subst \<Gamma> = (\<forall>\<tau> \<in> ran \<Gamma>. valid_ty_uexpr \<tau>)"

lemma [simp]: "typeify (untypeify t) = t"
  by (induction t) simp_all

lemma [simp]: "valid_ty_uexpr t \<Longrightarrow> uvars t = {} \<Longrightarrow> untypeify (typeify t) = t"
  by (induction t rule: typeify.induct) simp_all

lemma [dest]: "typeify e = Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> valid_ty_uexpr e \<Longrightarrow> uvars e = {} \<Longrightarrow> 
    e = Ctor ''Arrow'' [untypeify t\<^sub>1, untypeify t\<^sub>2]"
  by (induction e rule: typeify.induct) auto

lemma [simp]: "uvars (untypeify t) = {}"
  by (induction t) simp_all

lemma [simp]: "valid_ty_uexpr (untypeify t)"
  by (induction t) simp_all

lemma [simp]: "partial_typeify {} t = t"
  by (simp add: partial_typeify_def)

lemma [simp]: "x \<notin> uvars t \<Longrightarrow> partial_typeify (insert x vs) t = partial_typeify vs t"
  and "x \<notin> uvarss ts \<Longrightarrow> map (partial_typeify (insert x vs)) ts = map (partial_typeify vs) ts"
  by (induction t and ts rule: uvars_uvarss.induct) (simp_all add: partial_typeify_def)

lemma partial_typeify_reduce_subset: "uvars t \<inter> vs' \<subseteq> vs \<Longrightarrow> vs \<subseteq> vs' \<Longrightarrow>
    partial_typeify vs' t = partial_typeify vs t"
  and "uvarss ts \<inter> vs' \<subseteq> vs \<Longrightarrow> vs \<subseteq> vs' \<Longrightarrow>
    map (partial_typeify vs') ts = map (partial_typeify vs) ts"
proof (induction t and ts rule: uvars_uvarss.induct)
  case (4 \<tau> \<tau>s)
  moreover hence "uvars \<tau> \<inter> vs' \<subseteq> vs \<and> uvarss \<tau>s \<inter> vs' \<subseteq> vs" by auto
  ultimately show ?case by simp
qed (auto simp add: partial_typeify_def)

lemma [simp]: "partial_typeify vs (untypeify t) = untypeify t"
  by (induction t) (simp_all add: partial_typeify_def)

lemma [simp]: "partial_typeify vs (Var x) = (if x \<in> vs then Ctor ''Num'' [] else Var x)"
  by (simp add: partial_typeify_def)

lemma [simp]: "partial_typeify vs (Ctor \<gamma> ts) = Ctor \<gamma> (map (partial_typeify vs) ts)"
  by (simp add: partial_typeify_def)

lemma [simp]: "uvars t \<subseteq> vs \<Longrightarrow> valid_ty_uexpr t \<Longrightarrow> partial_typeify vs t = untypeify (typeify t)"
  by (induction t rule: typeify.induct) (simp_all add: partial_typeify_def)

lemma [simp]: "uvars t = {} \<Longrightarrow> partial_typeify vs t = t"
  and "uvarss ts = {} \<Longrightarrow> map (partial_typeify vs) ts = ts"
  by (induction t and ts rule: uvars_uvarss.induct) simp_all

lemma [elim]: "valid_ty_subst \<Gamma> \<Longrightarrow> \<Gamma> x = Some t \<Longrightarrow> valid_ty_uexpr t"
  by (auto simp add: valid_ty_subst_def ran_def)

lemma [simp]: "subst_vars \<Gamma> \<subseteq> vs \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> \<Gamma> x = Some t \<Longrightarrow> 
    partial_typeify vs t = untypeify (typeify t)"
proof -
  assume "valid_ty_subst \<Gamma>" and T: "\<Gamma> x = Some t"
  hence X: "valid_ty_uexpr t" by auto
  assume "subst_vars \<Gamma> \<subseteq> vs" 
  with T have "uvars t \<subseteq> vs" by auto
  with X show ?thesis by simp
qed

lemma [dest]: "partial_typeify vs t = Ctor ''Arrow'' [t\<^sub>1, t\<^sub>2] \<Longrightarrow> \<exists>tt1 tt2. 
    t = Ctor ''Arrow'' [tt1, tt2] \<and> partial_typeify vs tt1 = t\<^sub>1 \<and> partial_typeify vs tt2 = t\<^sub>2"
  by (induction t) (auto simp add: partial_typeify_def split: if_splits)

lemma [simp]: "dom s \<inter> vs = {} \<Longrightarrow> subst_vars s = {} \<Longrightarrow> 
  subst s (partial_typeify vs t) = partial_typeify vs (subst s t)"
proof (induction t)
  case (Var x)
  thus ?case
  proof (cases "s x")
    case (Some \<tau>)
    moreover with Var have "uvars \<tau> = {}" by (auto simp add: subst_vars_def ran_def)
    moreover from Var Some have "x \<notin> vs" by auto
    ultimately show ?thesis by simp
  qed (simp_all add: partial_typeify_def)
qed simp_all

lemma [simp]: "x \<notin> constr_vars k \<Longrightarrow> 
    partial_typeify_constr (insert x vs) k = partial_typeify_constr vs k"
  by (induction k rule: constr_vars.induct) simp_all

lemma [simp]: "x \<notin> vs \<Longrightarrow> constr_subst x (untypeify t) (partial_typeify_constr vs con) = 
    partial_typeify_constr vs (constr_subst x (untypeify t) con)"
  by (induction x "untypeify t" con rule: constr_subst.induct) simp_all

lemma partial_typeify_constr_reduce_subset: "constr_vars con \<inter> vs' \<subseteq> vs \<Longrightarrow> vs \<subseteq> vs' \<Longrightarrow>
    partial_typeify_constr vs' con = partial_typeify_constr vs con"
proof (induction con rule: constr_subst.induct)
  case (2 x \<tau> \<tau>\<^sub>1 \<tau>\<^sub>2 \<kappa>)
  moreover hence "constr_vars \<kappa> \<inter> vs' \<subseteq> vs \<and> uvars \<tau>\<^sub>1 \<inter> vs' \<subseteq> vs \<and> uvars \<tau>\<^sub>2 \<inter> vs' \<subseteq> vs" by auto
  ultimately show ?case by (simp add: partial_typeify_reduce_subset)
qed simp_all

lemma valid_empty [simp]: "valid_ty_subst Map.empty"
  by (simp add: valid_ty_subst_def)

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_uexpr t \<Longrightarrow> valid_ty_subst (\<Gamma>(x \<mapsto> t))"
  by (auto simp add: valid_ty_subst_def ran_def)

lemma [simp]: "valid_ty_subst \<Gamma> \<Longrightarrow> valid_ty_subst \<Gamma>' \<Longrightarrow> valid_ty_subst (\<Gamma>(x := \<Gamma>' y))"
  by (auto simp add: valid_ty_subst_def ran_def)

lemma [simp]: "valid_ty_uexpr e \<Longrightarrow> valid_ty_uexpr e' \<Longrightarrow> valid_ty_uexpr (subst [x \<mapsto> e'] e)"
  and [simp]: "list_all valid_ty_uexpr es \<Longrightarrow> valid_ty_uexpr e' \<Longrightarrow> 
    list_all valid_ty_uexpr (map (subst [x \<mapsto> e']) es)"
proof (induction e and es rule: uvars_uvarss.induct)
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

lemma [simp]: "valid_ty_uexpr e \<Longrightarrow> valid_ty_uexprs ess \<Longrightarrow> valid_ty_uexprs (constr_subst x e ess)"
  by (induction ess rule: constr_subst.induct) (auto simp add: valid_ty_uexprs_def)

lemma [simp]: "valid_ty_uexpr t \<Longrightarrow> valid_ty_subst sub \<Longrightarrow> valid_ty_uexpr (subst sub t)"
  and [simp]: "list_all valid_ty_uexpr ts \<Longrightarrow> valid_ty_subst sub \<Longrightarrow> 
    list_all valid_ty_uexpr (map (subst sub) ts)"
  by (induction t and ts rule: uvars_uvarss.induct) 
     (auto simp add: valid_ty_subst_def ran_def split: option.splits)

lemma [simp]: "valid_ty_subst s \<Longrightarrow> valid_ty_uexpr e \<Longrightarrow> valid_ty_subst (extend_subst x e s)"
  by (auto simp add: valid_ty_subst_def extend_subst_def ran_def)

lemma [elim]: "valid_ty_uexprs ts \<Longrightarrow> unify ts = Some sub \<Longrightarrow> valid_ty_subst sub"                                  
proof (induction ts arbitrary: sub rule: unify.induct)
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
    proof (cases "x \<in> uvars e")
      case False
      with 4 F obtain sub' where S: "unify (constr_subst x e ess) = Some sub' \<and> 
        sub = extend_subst x e sub'" by auto
      from 4 have "valid_ty_uexpr e \<and> valid_ty_uexprs ess" by (simp add: valid_ty_uexprs_def)
      hence "valid_ty_uexprs (constr_subst x e ess)" by simp
      with 4 F False S show ?thesis by (simp add: valid_ty_uexprs_def)
    qed simp_all
  qed (simp_all add: valid_ty_uexprs_def)
qed (auto simp add: valid_ty_uexprs_def)

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

lemma [dest]: "typeify \<tau> = Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> valid_ty_uexpr \<tau> \<Longrightarrow>
    \<exists>\<tau>\<^sub>1 \<tau>\<^sub>2. \<tau> = Ctor ''Arrow'' [\<tau>\<^sub>1, \<tau>\<^sub>2] \<and> typeify \<tau>\<^sub>1 = t\<^sub>1 \<and> typeify \<tau>\<^sub>2 = t\<^sub>2"
  by (induction \<tau> rule: typeify.induct) simp_all

end