theory UnifiableType
  imports Type "../00Utils/Unification/Unification"
begin

definition env_subst :: "subst \<Rightarrow> subst \<Rightarrow> subst" where
  "env_subst sub \<Gamma> = map_option (subst sub) \<circ> \<Gamma>"

fun typeify :: "uterm \<Rightarrow> ty" where
  "typeify (Var v) = TyVar v"
| "typeify (Ctor k []) = (if k = ''Num'' then Num else undefined)"
| "typeify (Ctor k [t\<^sub>1, t\<^sub>2]) = 
    (if k = ''Arrow'' then Arrow (typeify t\<^sub>1) (typeify t\<^sub>2) else undefined)"
| "typeify (Ctor k ts) = undefined"

primrec untypeify :: "ty \<Rightarrow> uterm" where
  "untypeify (TyVar v) = Var v"
| "untypeify Num = Ctor ''Num'' []"
| "untypeify (Arrow t\<^sub>1 t\<^sub>2) = Ctor ''Arrow'' [untypeify t\<^sub>1, untypeify t\<^sub>2]"

fun tsubsts :: "subst \<Rightarrow> ty \<Rightarrow> ty" where
  "tsubsts sub (TyVar y) = (case sub y of Some t \<Rightarrow> typeify t | None \<Rightarrow> TyVar y)"
| "tsubsts sub Num = Num"
| "tsubsts sub (Arrow t\<^sub>1 t\<^sub>2) = Arrow (tsubsts sub t\<^sub>1) (tsubsts sub t\<^sub>2)"

fun valid_ty_uexpr' :: "string \<Rightarrow> nat \<Rightarrow> bool" where
  "valid_ty_uexpr' k 0 = (k = ''Num'')"
| "valid_ty_uexpr' k (Suc 0) = False"
| "valid_ty_uexpr' k (Suc (Suc 0)) = (k = ''Arrow'')"
| "valid_ty_uexpr' k (Suc (Suc (Suc x))) = False"

primrec valid_ty_uexpr :: "uterm \<Rightarrow> bool" where
  "valid_ty_uexpr (Var v) = True"
| "valid_ty_uexpr (Ctor k ts) = (valid_ty_uexpr' k (length ts) \<and> list_all valid_ty_uexpr ts)"

definition valid_ty_uexprs :: "constraint \<Rightarrow> bool" where
  "valid_ty_uexprs ts = list_all (\<lambda>(t\<^sub>1, t\<^sub>2). valid_ty_uexpr t\<^sub>1 \<and> valid_ty_uexpr t\<^sub>2) ts"
 
definition valid_ty_subst :: "subst \<Rightarrow> bool" where
  "valid_ty_subst \<Gamma> = (\<forall>t \<in> ran \<Gamma>. valid_ty_uexpr t)"

lemma [simp]: "typeify (untypeify t) = t"
  by (induction t) simp_all

lemma [simp]: "valid_ty_uexpr t \<Longrightarrow> untypeify (typeify t) = t"
  by (induction t rule: typeify.induct) simp_all

lemma [dest]: "typeify e = Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> valid_ty_uexpr e \<Longrightarrow> 
    e = Ctor ''Arrow'' [untypeify t\<^sub>1, untypeify t\<^sub>2]"
  by (induction e rule: typeify.induct) auto

lemma [simp]: "uvars (untypeify t) = tvars t"
  by (induction t) simp_all

lemma [simp]: "valid_ty_uexpr (untypeify t)"
  by (induction t) simp_all

lemma [simp]: "valid_ty_uexpr t \<Longrightarrow> tvars (typeify t) = uvars t"
  by (induction t rule: typeify.induct) simp_all

lemma [simp]: "tsubsts Map.empty e = e"
  by (induction e) simp_all

lemma [simp]: "dom s \<inter> tvars t = {} \<Longrightarrow> tsubsts s t = t"
  by (induction t) (auto split: option.splits)

lemma [simp]: "valid_ty_uexpr t \<Longrightarrow> typeify (subst sub t) = tsubsts sub (typeify t)"
  by (induction t rule: typeify.induct) (simp_all split: option.splits)

lemma [simp]: "valid_ty_subst sub \<Longrightarrow> untypeify (tsubsts sub t) = subst sub (untypeify t)"
  by (induction t) (auto simp add: valid_ty_subst_def ran_def split: option.splits)

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

lemma [simp]: "valid_ty_uexpr e \<Longrightarrow> valid_ty_uexprs ess \<Longrightarrow> valid_ty_uexprs (list_subst x e ess)"
  by (induction ess rule: list_subst.induct) (auto simp add: valid_ty_uexprs_def)

lemma [simp]: "valid_ty_uexpr t \<Longrightarrow> valid_ty_subst sub \<Longrightarrow> valid_ty_uexpr (subst sub t)"
  and [simp]: "list_all valid_ty_uexpr ts \<Longrightarrow> valid_ty_subst sub \<Longrightarrow> 
    list_all valid_ty_uexpr (map (subst sub) ts)"
  by (induction t and ts rule: uvars_uvarss.induct) 
     (auto simp add: valid_ty_subst_def ran_def split: option.splits)

lemma [simp]: "valid_ty_subst s \<Longrightarrow> valid_ty_uexpr e \<Longrightarrow> valid_ty_subst (extend_subst x e s)"
  by (auto simp add: valid_ty_subst_def extend_subst_def ran_def)

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
      with 4 F obtain sub' where S: "unify (list_subst x e ess) = Some sub' \<and> 
        sub = extend_subst x e sub'" by auto
      from 4 have "valid_ty_uexpr e \<and> valid_ty_uexprs ess" by (simp add: valid_ty_uexprs_def)
      hence "valid_ty_uexprs (list_subst x e ess)" by simp
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

lemma [simp]: "subst_vars \<Gamma> \<subseteq> vs \<Longrightarrow> valid_ty_subst \<Gamma> \<Longrightarrow> t \<in> ran (map_option typeify \<circ> \<Gamma>) \<Longrightarrow> 
    finite vs \<Longrightarrow> fresh vs \<notin> tvars t"
  by (unfold subst_vars_def valid_ty_subst_def ran_def) fastforce

end