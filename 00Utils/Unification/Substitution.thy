theory Substitution
  imports UnifiableTerm
begin

subsection \<open>Substitutions\<close>

text \<open>Having defined terms, we now define substitutions over them. A substitution is just a partial 
map from variables to terms:\<close>

type_synonym subst = "var \<rightharpoonup> uterm"

text \<open>Applying a substitution to a term is simply applying the map at each variable in the term:\<close>

fun subst :: "subst \<Rightarrow> uterm \<Rightarrow> uterm" where
  "subst \<sigma> (Var x) = (case \<sigma> x of Some \<tau> \<Rightarrow> \<tau> | None \<Rightarrow> Var x)"
| "subst \<sigma> (Ctor \<gamma> \<tau>s) = Ctor \<gamma> (map (subst \<sigma>) \<tau>s)"

lemma subst_not_in_dom [simp]: "dom \<sigma> \<inter> uvars \<tau> = {} \<Longrightarrow> subst \<sigma> \<tau> = \<tau>"
  and [simp]: "dom \<sigma> \<inter> uvarss \<tau>s = {} \<Longrightarrow> map (subst \<sigma>) \<tau>s = \<tau>s"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) (auto split: option.splits)

lemma subst_empty [simp]: "subst Map.empty = id"
  by auto

lemma uvars_subst_single_member [simp]: "x \<in> uvars \<tau> \<Longrightarrow> 
    uvars (subst [x \<mapsto> \<tau>'] \<tau>) = uvars \<tau> - {x} \<union> uvars \<tau>'"
  and "x \<in> uvarss \<tau>s \<Longrightarrow> uvarss (map (subst [x \<mapsto> \<tau>']) \<tau>s) = uvarss \<tau>s - {x} \<union> uvars \<tau>'"
proof (induction \<tau> and \<tau>s rule: uvars_uvarss.induct)
  case (4 \<tau> \<tau>s)
  hence "uvarss (map (subst [x \<mapsto> \<tau>']) (\<tau> # \<tau>s)) = uvarss (\<tau> # \<tau>s) - {x} \<union> uvars \<tau>'" by fastforce
  thus ?case by blast
qed simp_all

lemma uvars_subst_single [simp]: "uvars (subst [x \<mapsto> \<tau>'] \<tau>) = 
    uvars \<tau> - {x} \<union> (if x \<in> uvars \<tau> then uvars \<tau>' else {})"
  by simp

lemma var_not_substituted [simp]: "x \<in> uvars \<tau> \<Longrightarrow> \<sigma> x = None \<Longrightarrow> x \<in> uvars (subst \<sigma> \<tau>)"
  and "x \<in> uvarss \<tau>s \<Longrightarrow> \<sigma> x = None \<Longrightarrow> x \<in> uvarss (map (subst \<sigma>) \<tau>s)"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) auto

lemma vars_subst_inv [elim]: "uvars (subst \<sigma> \<tau>) \<subseteq> vs \<Longrightarrow> uvars \<tau> \<subseteq> vs \<union> dom \<sigma>"
  and [elim]: "uvarss (map (subst \<sigma>) \<tau>s) \<subseteq> vs \<Longrightarrow> uvarss \<tau>s \<subseteq> vs \<union> dom \<sigma>"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) (auto split: option.splits)

lemma subst_var_to_self' [simp]: "subst [x \<mapsto> Var x] \<tau> = \<tau>"
  and "map (subst [x \<mapsto> Var x]) \<tau>s = \<tau>s"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) simp_all

lemma subst_var_to_self [simp]: "subst [x \<mapsto> Var x] = id"
  by auto

lemma subst_var_swap' [simp]: "subst [y \<mapsto> Var x] (subst [x \<mapsto> Var y] \<tau>) = subst [y \<mapsto> Var x] \<tau>"
  and "map (subst [y \<mapsto> Var x] \<circ> subst [x \<mapsto> Var y]) \<tau>s = map (subst [y \<mapsto> Var x]) \<tau>s"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) simp_all

lemma subst_var_swap [simp]: "subst [y \<mapsto> Var x] \<circ> subst [x \<mapsto> Var y] = subst [y \<mapsto> Var x]"
  by auto

lemma subst_vars_absorb' [simp]: "y \<notin> dom \<sigma> \<Longrightarrow> \<sigma> x = Some (Var y) \<Longrightarrow> 
    subst \<sigma> (subst [x \<mapsto> Var y] \<tau>) = subst \<sigma> \<tau>"
  and "y \<notin> dom \<sigma> \<Longrightarrow> \<sigma> x = Some (Var y) \<Longrightarrow>
    map (subst \<sigma> \<circ> subst [x \<mapsto> Var y]) \<tau>s = map (subst \<sigma>) \<tau>s"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) (auto split: option.splits)

lemma subst_vars_absorb [simp]: "y \<notin> dom \<sigma> \<Longrightarrow> \<sigma> x = Some (Var y) \<Longrightarrow> 
    subst \<sigma> \<circ> subst [x \<mapsto> Var y] = subst \<sigma>"
  by rule simp

lemma subst_upd_not_in_vars [simp]: "x \<notin> uvars \<tau> \<Longrightarrow> subst (\<sigma>(x := y)) \<tau> = subst \<sigma> \<tau>"
  and "x \<notin> uvarss \<tau>s \<Longrightarrow> map (subst (\<sigma>(x := y))) \<tau>s = map (subst \<sigma>) \<tau>s"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) (simp_all split: option.splits)

lemma subst_upd_same_var [simp]: "\<sigma> x = None \<Longrightarrow> subst (\<sigma>(x \<mapsto> Var x)) \<tau> = subst \<sigma> \<tau>"
  by (induction \<tau>) simp_all

lemma subst_to_var [dest]: "subst \<sigma> \<tau> = Var x \<Longrightarrow> 
    (\<tau> = Var x \<and> \<sigma> x = None) \<or> (\<exists>y. \<tau> = Var y \<and> \<sigma> y = Some (Var x))"
  by (induction \<tau>) (auto split: option.splits)

lemma subst_to_ctor [dest]: "subst \<sigma> \<tau> = Ctor \<gamma> \<tau>s \<Longrightarrow> 
    (\<exists>x. \<tau> = Var x \<and> \<sigma> x = Some (Ctor \<gamma> \<tau>s)) \<or> (\<exists>\<tau>s'. \<tau> = Ctor \<gamma> \<tau>s' \<and> map (subst \<sigma>) \<tau>s' = \<tau>s)"
  by (induction \<tau>) (auto split: option.splits)

lemma subst_subst_var [consumes 1, case_names Eq FstOnly SndOnly Both]: 
  "(subst \<sigma> \<circ> subst \<sigma>') (Var x) = Var y \<Longrightarrow> (x = y \<Longrightarrow> P) \<Longrightarrow> 
    (\<sigma> y = None \<Longrightarrow> \<sigma>' x = Some (Var y) \<Longrightarrow> P) \<Longrightarrow> (\<sigma> x = Some (Var y) \<Longrightarrow> \<sigma>' x = None \<Longrightarrow> P) \<Longrightarrow> 
    (\<And>z. \<sigma> z = Some (Var y) \<Longrightarrow> \<sigma>' x = Some (Var z) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto split: option.splits)

lemma structural_preserved_by_subst [simp]: "P \<tau> \<Longrightarrow> \<forall>x\<in>ran \<sigma>. P x \<Longrightarrow> structural P \<Longrightarrow> 
    P (subst \<sigma> \<tau>)"
  and "list_all P \<tau>s \<Longrightarrow> \<forall>x\<in>ran \<sigma>. P x \<Longrightarrow> structural P \<Longrightarrow> list_all P (map (subst \<sigma>) \<tau>s)"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) 
    (auto simp add: structural_def ran_def split: option.splits)

text \<open>Because we only use constraints in the unification algorithm, however, the most common 
substitution on them is for a single variable at a time:\<close>

fun constr_subst :: "var \<Rightarrow> uterm \<Rightarrow> constraint \<Rightarrow> constraint" where
  "constr_subst x \<tau> [] = []"
| "constr_subst x \<tau> ((\<tau>\<^sub>1, \<tau>\<^sub>2) # \<kappa>) = (subst [x \<mapsto> \<tau>] \<tau>\<^sub>1, subst [x \<mapsto> \<tau>] \<tau>\<^sub>2) # constr_subst x \<tau> \<kappa>"

lemma constr_subst_append [simp]: "constr_subst x \<tau> (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2) = 
    constr_subst x \<tau> \<kappa>\<^sub>1 @ constr_subst x \<tau> \<kappa>\<^sub>2"
  by (induction \<kappa>\<^sub>1 rule: constr_subst.induct) simp_all

lemma constr_subst_no_var [simp]: "x \<notin> constr_vars \<kappa> \<Longrightarrow> constr_subst x \<tau> \<kappa> = \<kappa>"
  by (induction x \<tau> \<kappa> rule: constr_subst.induct) simp_all

lemma vars_constr_subst' [simp]: "x \<in> constr_vars \<kappa> \<Longrightarrow> 
  constr_vars (constr_subst x \<tau> \<kappa>) = constr_vars \<kappa> - {x} \<union> uvars \<tau>"
proof (induction \<kappa> rule: constr_vars.induct)
  case (2 e\<^sub>1 e\<^sub>2 \<kappa>)
  thus ?case by (cases "x \<in> constr_vars \<kappa>") auto
qed simp_all

lemma vars_constr_subst [simp]: "constr_vars (constr_subst x \<tau> \<kappa>) = 
    constr_vars \<kappa> - {x} \<union> (if x \<in> constr_vars \<kappa> then uvars \<tau> else {})"
  by simp

lemma structural_preserved_by_constr_subst [simp]: "P \<tau> \<Longrightarrow> structural P \<Longrightarrow> 
    list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) \<kappa> \<Longrightarrow> list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) (constr_subst x \<tau> \<kappa>)"
  by (induction \<kappa> rule: constr_subst.induct) simp_all

text \<open>Using Isabelle's partial functions means we can use the library domain \<open>dom\<close> function 
directly. The range of a substitution, by contrast, is never really directly relevant. Rather, what 
is important is the free variables of the range of a substitution:\<close>

definition subst_vars :: "subst \<Rightarrow> var set" where
  "subst_vars \<sigma> \<equiv> \<Union> (uvars ` ran \<sigma>)"

lemma uvars_subst [simp]: "uvars (subst \<sigma> \<tau>) \<subseteq> uvars \<tau> - dom \<sigma> \<union> subst_vars \<sigma>"
  and "uvarss (map (subst \<sigma>) \<tau>s) \<subseteq> uvarss \<tau>s - dom \<sigma> \<union> subst_vars \<sigma>"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) 
     (auto simp add: subst_vars_def ranI split: option.splits)

lemma ran_empty_subst [simp]: "subst_vars Map.empty = {}"
  by (simp add: subst_vars_def)

lemma ran_single_subst [simp]: "subst_vars [x \<mapsto> \<tau>] = uvars \<tau>"
  by (simp add: subst_vars_def)

lemma ran_narrower_subst [simp]: "subst_vars \<sigma> \<subseteq> vs \<Longrightarrow> subst_vars (\<sigma>(x := None)) \<subseteq> vs"
  by (auto simp add: subst_vars_def ran_def)

lemma ran_subst_upd [simp]: "subst_vars (\<sigma>(x \<mapsto> \<tau>)) = (subst_vars (\<sigma>(x := None)) \<union> uvars \<tau>)"
  by (auto simp add: subst_vars_def ran_def)

lemma ran_subst_upd' [simp]: "subst_vars (\<lambda>a. if a = x then Some \<tau> else \<sigma> a) = 
    (subst_vars (\<sigma>(x := None)) \<union> uvars \<tau>)"
  by (auto simp add: subst_vars_def ran_def)

lemma subst_ran_explicitly [simp]: "\<sigma> x = Some \<tau> \<Longrightarrow> y \<in> uvars \<tau> \<Longrightarrow> y \<in> subst_vars \<sigma>"
  by (auto simp add: subst_vars_def ran_def)

lemma in_ran_subst_narrow2 [simp]: "y \<in> subst_vars (\<sigma>(x := None)) \<Longrightarrow> y \<in> subst_vars \<sigma>"
  by (auto simp add: subst_vars_def ran_def split: if_splits)

lemma in_ran_subst_narrow [simp]: "y \<in> subst_vars (\<Gamma>(x := None)) = 
    (\<exists>z \<tau>. z \<noteq> x \<and> \<Gamma> z = Some \<tau> \<and> y \<in> uvars \<tau>)"
  by (auto simp add: subst_vars_def ran_def split: if_splits)

lemma distinct_from_ran_subst [simp]: "xs \<inter> subst_vars \<sigma> = {} \<Longrightarrow> \<sigma> x = Some \<tau> \<Longrightarrow> xs \<inter> uvars \<tau> = {}"
  by (auto simp add: subst_vars_def ran_def)

lemma subst_not_in_ran [simp]: "x \<notin> subst_vars \<sigma> \<Longrightarrow> \<sigma> y = Some \<tau> \<Longrightarrow> subst [x \<mapsto> \<tau>'] \<tau> = \<tau>"
proof -
  assume "\<sigma> y = Some \<tau>" 
  hence "\<tau> \<in> ran \<sigma>" by (metis ranI)
  moreover assume "x \<notin> subst_vars \<sigma>" 
  ultimately show ?thesis by (simp add: subst_vars_def)
qed

lemma swap_substs_with_fresh_var' [simp]: "x \<notin> dom \<sigma> \<Longrightarrow> x \<notin> subst_vars \<sigma> \<Longrightarrow> 
    subst \<sigma> (subst [x \<mapsto> \<tau>'] \<tau>) = subst [x \<mapsto> subst \<sigma> \<tau>'] (subst \<sigma> \<tau>)"
  by (induction \<tau>) (auto split: option.splits)

lemma swap_substs_with_fresh_var [simp]: "x \<notin> dom \<sigma> \<Longrightarrow> x \<notin> subst_vars \<sigma> \<Longrightarrow> 
    subst \<sigma> \<circ> subst [x \<mapsto> \<tau>] = subst [x \<mapsto> subst \<sigma> \<tau>] \<circ> subst \<sigma>"
  by rule simp

lemma subst_ran_not_in_ran [dest]: "x \<notin> subst_vars \<sigma> \<Longrightarrow> \<sigma> y = Some (Var x) \<Longrightarrow> False"
proof (unfold subst_vars_def)
  assume "\<sigma> y = Some (Var x)"
  hence "x \<in> \<Union> (uvars ` ran \<sigma>)" using uvars.simps ranI by force
  moreover assume "x \<notin> \<Union> (uvars ` ran \<sigma>)" 
  ultimately show "False" by simp
qed

lemma subst_swap_order [simp]: "dom \<sigma> \<inter> dom \<sigma>' = {} \<Longrightarrow> dom \<sigma>' \<inter> subst_vars \<sigma> = {} \<Longrightarrow> 
  subst \<sigma> (subst \<sigma>' \<tau>) = subst (map_option (subst \<sigma>) \<circ> \<sigma>') (subst \<sigma> \<tau>)"
proof (induction \<tau>)
  case (Var x)
  thus ?case
  proof (cases "\<sigma>' x")
    case None note N = None
    thus ?thesis
    proof (cases "\<sigma> x")
      case (Some \<tau>)
      with Var have "dom \<sigma>' \<inter> uvars \<tau> = {}" by simp
      with N Some have "subst \<sigma> (subst \<sigma>' (Var x)) = 
        subst (map_option (subst \<sigma>) \<circ> \<sigma>') (subst \<sigma> (Var x))" by simp
      thus ?thesis by blast
    qed simp_all
  next
    case (Some \<tau>)
    with Var have "\<sigma> x = None" by auto
    with Some show ?thesis by simp
  qed
qed simp_all

lemma subst_absorb_no_ran': "subst_vars \<sigma> = {} \<Longrightarrow> 
    subst (map_option (subst \<sigma>') \<circ> \<sigma>) \<tau> = subst \<sigma> \<tau>"
  by (induction \<tau>) (auto simp add: subst_vars_def ran_def split: option.splits)

lemma subst_absorb_no_ran: "subst_vars \<sigma> = {} \<Longrightarrow> 
    subst (map_option (subst \<sigma>') \<circ> \<sigma>) = subst \<sigma>"
  by (auto simp add: subst_absorb_no_ran')

text \<open>A substitution can be extended an element at a time:\<close>

definition extend_subst :: "var \<Rightarrow> uterm \<Rightarrow> subst \<Rightarrow> subst" where
  "extend_subst x \<tau> \<sigma> \<equiv> (\<sigma>(x \<mapsto> subst \<sigma> \<tau>))"

lemma dom_extend_subst [simp]: "dom (extend_subst x \<tau> \<sigma>) = insert x (dom \<sigma>)"
  by (auto simp add: extend_subst_def)

lemma ran_extend_subst [simp]: "x \<notin> dom \<sigma> \<Longrightarrow>
    subst_vars (extend_subst x \<tau> \<sigma>) = uvars (subst \<sigma> \<tau>) \<union> subst_vars \<sigma>"
  by (auto simp add: extend_subst_def subst_vars_def)

lemma expand_extend_subst': "subst (extend_subst x \<tau>' \<sigma>) \<tau> = subst \<sigma> (subst [x \<mapsto> \<tau>'] \<tau>)"
  by (induction \<tau>) (simp_all add: extend_subst_def)

lemma expand_extend_subst: "subst (extend_subst x \<tau> \<sigma>) = subst \<sigma> \<circ> subst [x \<mapsto> \<tau>]"
  by (auto simp add: expand_extend_subst')

lemma extend_subst_already_substituted [simp]: "\<sigma> x = Some (subst \<sigma> \<tau>) \<Longrightarrow> extend_subst x \<tau> \<sigma> = \<sigma>"
  by (auto simp add: extend_subst_def)

lemma extend_subst_same [simp]: "extend_subst x \<tau> \<sigma> x = Some (subst \<sigma> \<tau>)"
  by (simp add: extend_subst_def) 

lemma extend_subst_var_swap' [simp]: "\<sigma> x = None \<Longrightarrow> \<sigma> y = Some (Var x) \<Longrightarrow> 
    subst (extend_subst x (Var y) \<sigma>) \<tau> = subst \<sigma> \<tau>"
  and "\<sigma> x = None \<Longrightarrow> \<sigma> y = Some (Var x) \<Longrightarrow> 
    map (subst (extend_subst x (Var y) \<sigma>)) \<tau>s = map (subst \<sigma>) \<tau>s"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) (simp_all add: extend_subst_def)

lemma extend_subst_var_swap [simp]: "\<sigma> x = None \<Longrightarrow> \<sigma> y = Some (Var x) \<Longrightarrow> 
    subst (extend_subst x (Var y) \<sigma>) = subst \<sigma>"
  by auto

lemma extend_upd_not_in_vars [simp]: "x \<notin> uvars \<tau> \<Longrightarrow> subst (extend_subst x \<tau>' \<sigma>) \<tau> = subst \<sigma> \<tau>"
  by (simp_all add: extend_subst_def)

lemma extend_subst_narrow [simp]: "\<sigma> x = Some (subst \<sigma> \<tau>) \<Longrightarrow> x \<notin> uvars \<tau> \<Longrightarrow> 
    extend_subst x \<tau> (\<sigma>(x := None)) = \<sigma>"
  by rule (simp add: extend_subst_def)

text \<open>Two substitutions can also be combined directly:\<close>

definition combine_subst :: "subst \<Rightarrow> subst \<Rightarrow> subst" where
  "combine_subst \<sigma>\<^sub>1 \<sigma>\<^sub>2 x \<equiv> (case \<sigma>\<^sub>2 x of None \<Rightarrow> \<sigma>\<^sub>1 x | Some \<tau> \<Rightarrow> Some (subst \<sigma>\<^sub>1 \<tau>))"

lemma dom_combine_subst [simp]: "dom (combine_subst \<sigma> \<sigma>') = dom \<sigma> \<union> dom \<sigma>'"
  by (auto simp add: dom_def combine_subst_def split: option.splits)

lemma ran_combine_subst [simp]: "dom \<sigma> \<inter> dom \<sigma>' = {} \<Longrightarrow> 
  subst_vars (combine_subst \<sigma> \<sigma>') = subst_vars \<sigma> \<union> (subst_vars \<sigma>' - dom \<sigma>)"
proof 
  assume "dom \<sigma> \<inter> dom \<sigma>' = {}"
  hence D: "\<And>y \<tau>. \<sigma> y = Some \<tau> \<Longrightarrow> \<sigma>' y = None" by auto
  show "subst_vars (combine_subst \<sigma> \<sigma>') \<subseteq> subst_vars \<sigma> \<union> (subst_vars \<sigma>' - dom \<sigma>)" 
  proof
    fix x
    assume "x \<in> subst_vars (combine_subst \<sigma> \<sigma>')"
    then obtain \<tau> y where E: "(case \<sigma>' y of None \<Rightarrow> \<sigma> y | Some \<tau>' \<Rightarrow> Some (subst \<sigma> \<tau>')) = Some \<tau> \<and> 
      x \<in> uvars \<tau>" by (auto simp add: subst_vars_def ran_def combine_subst_def)
    thus "x \<in> subst_vars \<sigma> \<union> (subst_vars \<sigma>' - dom \<sigma>)"
    proof (cases "\<sigma>' y")
      case (Some \<tau>')
      with E have "x \<in> uvars (subst \<sigma> \<tau>')" by simp
      hence "x \<in> uvars \<tau>' - dom \<sigma> \<union> subst_vars \<sigma>" using uvars_subst by blast
      with Some show ?thesis by (auto simp add: subst_vars_def ran_def dom_def)
    qed (auto simp add: subst_vars_def ran_def)
  qed
  show "subst_vars \<sigma> \<union> (subst_vars \<sigma>' - dom \<sigma>) \<subseteq> subst_vars (combine_subst \<sigma> \<sigma>')" 
  proof
    fix x
    assume X: "x \<in> subst_vars \<sigma> \<union> (subst_vars \<sigma>' - dom \<sigma>)"
    thus "x \<in> subst_vars (combine_subst \<sigma> \<sigma>')" 
    proof (cases "\<exists>\<tau> y. \<sigma> y = Some \<tau> \<and> x \<in> uvars \<tau>")
      case True
      then obtain \<tau> y where Y: "\<sigma> y = Some \<tau> \<and> x \<in> uvars \<tau>" by auto
      with D have "\<sigma>' y = None" by simp
      with Y have "(case \<sigma>' y of None \<Rightarrow> \<sigma> y | Some \<tau>' \<Rightarrow> Some (subst \<sigma> \<tau>')) = Some \<tau> \<and> 
        x \<in> uvars \<tau>" by simp
      thus ?thesis by (auto simp add: subst_vars_def ran_def combine_subst_def)
    next
      case False
      with X obtain \<tau> y where "\<sigma>' y = Some \<tau> \<and> x \<in> uvars \<tau> \<and> \<sigma> x = None" 
        by (auto simp add: subst_vars_def ran_def dom_def)
      hence "(case \<sigma>' y of None \<Rightarrow> \<sigma> y | Some \<tau>' \<Rightarrow> Some (subst \<sigma> \<tau>')) = Some (subst \<sigma> \<tau>) \<and> 
        x \<in> uvars (subst \<sigma> \<tau>)" by simp
      thus ?thesis by (auto simp add: subst_vars_def ran_def combine_subst_def)
    qed
  qed
qed

lemma combine_subst_expand' [simp]: "subst (combine_subst \<sigma> \<sigma>') \<tau> = subst \<sigma> (subst \<sigma>' \<tau>)"
  by (induction \<tau>) (simp_all add: combine_subst_def split: option.splits)

lemma combine_subst_expand [simp]: "subst (combine_subst \<sigma> \<sigma>') = subst \<sigma> \<circ> subst \<sigma>'"
  by auto

text \<open>The most important thing for a substitution to do is to unify terms and constraints:\<close>

abbreviation unifier :: "subst \<Rightarrow> uterm \<Rightarrow> uterm \<Rightarrow> bool" (infix "unifies _ and" 50) where 
  "\<sigma> unifies \<tau>\<^sub>1 and \<tau>\<^sub>2 \<equiv> subst \<sigma> \<tau>\<^sub>1 = subst \<sigma> \<tau>\<^sub>2"

fun constr_unifier :: "subst \<Rightarrow> constraint \<Rightarrow> bool" (infix "unifies\<^sub>\<kappa>" 50) where 
  "\<sigma> unifies\<^sub>\<kappa> [] = True"
| "\<sigma> unifies\<^sub>\<kappa> ((\<tau>\<^sub>1, \<tau>\<^sub>2) # \<kappa>) = ((\<sigma> unifies \<tau>\<^sub>1 and \<tau>\<^sub>2) \<and> constr_unifier \<sigma> \<kappa>)"

lemma unifies_upd_same [simp]: "\<sigma> x = None \<Longrightarrow> (\<sigma>(x \<mapsto> Var x) unifies\<^sub>\<kappa> \<kappa>) = (\<sigma> unifies\<^sub>\<kappa> \<kappa>)"
  by (induction \<sigma> \<kappa> rule: constr_unifier.induct) simp_all

lemma unifies_extend_var [simp]: "\<sigma> y = Some (Var x) \<Longrightarrow> \<sigma> x = None \<Longrightarrow> 
    extend_subst x (Var y) \<sigma> unifies\<^sub>\<kappa> \<kappa> = (\<sigma> unifies\<^sub>\<kappa> \<kappa>)"
  by (simp add: extend_subst_def)

lemma constr_unifies_append [simp]: "\<sigma> unifies\<^sub>\<kappa> (ess\<^sub>1 @ ess\<^sub>2) = (\<sigma> unifies\<^sub>\<kappa> ess\<^sub>1 \<and> \<sigma> unifies\<^sub>\<kappa> ess\<^sub>2)"
  by (induction \<sigma> ess\<^sub>1 rule: constr_unifier.induct) simp_all

lemma constr_unifies_zip [simp]: "length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> 
  \<sigma> unifies\<^sub>\<kappa> zip es\<^sub>1 es\<^sub>2 = (map (subst \<sigma>) es\<^sub>1 = map (subst \<sigma>) es\<^sub>2)"
proof (induction es\<^sub>1 arbitrary: es\<^sub>2)
  case (Cons e\<^sub>1 es\<^sub>1)
  thus ?case by (induction es\<^sub>2) simp_all
qed simp_all

lemma extend_subst_unifies [simp]: "x \<notin> dom \<sigma> \<Longrightarrow> x \<notin> subst_vars \<sigma> \<Longrightarrow> \<sigma> unifies\<^sub>\<kappa> \<kappa> \<Longrightarrow> 
    extend_subst x \<tau> \<sigma> unifies\<^sub>\<kappa> \<kappa>"
  by (induction \<sigma> \<kappa> rule: constr_unifier.induct) (simp_all add: expand_extend_subst)

lemma constr_subst_unifies [simp]: "\<sigma> unifies\<^sub>\<kappa> constr_subst x \<tau> \<kappa> = (extend_subst x \<tau> \<sigma> unifies\<^sub>\<kappa> \<kappa>)"
  by (induction \<sigma> \<kappa> rule: constr_unifier.induct) (simp_all add: expand_extend_subst)

lemma combine_fst_still_unifies_constr [simp]: "dom \<sigma> \<inter> dom \<sigma>' = {} \<Longrightarrow> 
    dom \<sigma>' \<inter> subst_vars \<sigma> = {} \<Longrightarrow> \<sigma> unifies\<^sub>\<kappa> \<kappa> \<Longrightarrow> combine_subst \<sigma> \<sigma>' unifies\<^sub>\<kappa> \<kappa>"
  by (induction \<sigma> \<kappa> rule: constr_unifier.induct) simp_all

lemma combine_snd_still_unifies_constr [simp]: "\<sigma>' unifies\<^sub>\<kappa> \<kappa> \<Longrightarrow> combine_subst \<sigma> \<sigma>' unifies\<^sub>\<kappa> \<kappa>"
  by (induction \<sigma>' \<kappa> rule: constr_unifier.induct) simp_all

text \<open>The most important class of substitutions is the idempotent ones, that is, ones for which 
repeated application does not change a term further. Equivalently (see \<open>idempotent_is_idempotent\<close>), 
it is the ones whose domain and range are distinct. The key utility of idempotence is that with it, 
we can divide substitutions into compositions of smaller substitutions which in turn will be crucial 
for proving properties of the unification algorithm, particularly that it finds the most general 
unifier. We shall always take care to construct only idempotent substitutions.\<close>

definition idempotent :: "subst \<Rightarrow> bool" where
  "idempotent \<sigma> \<equiv> (dom \<sigma> \<inter> subst_vars \<sigma> = {})"

lemma idempotent_absorb [simp]: "idempotent \<sigma> \<Longrightarrow> subst \<sigma> (subst \<sigma> \<tau>) = subst \<sigma> \<tau>"
proof (induction \<tau>)
  case (Var x)
  hence D: "dom \<sigma> \<inter> \<Union> (uvars ` ran \<sigma>) = {}" by (simp add: idempotent_def subst_vars_def)
  thus ?case
  proof (cases "\<sigma> x")
    case (Some \<tau>)
    with D have "dom \<sigma> \<inter> uvars \<tau> = {}" using ran_def by force
    with Some show ?thesis by simp
  qed simp_all
qed simp_all

lemma idempotent_is_idempotent [simp]: "idempotent \<sigma> \<Longrightarrow> subst \<sigma> \<circ> subst \<sigma> = subst \<sigma>"
  by auto

lemma idempotent_no_id [simp]: "idempotent \<sigma>' \<Longrightarrow> \<sigma>' x \<noteq> Some (Var x)"
proof (rule, unfold idempotent_def)
  assume "\<sigma>' x = Some (Var x)"
  hence "x \<in> dom \<sigma>' \<and> x \<in> subst_vars \<sigma>'" using uvars.simps(1) by fastforce
  moreover assume "dom \<sigma>' \<inter> subst_vars \<sigma>' = {}" 
  ultimately show "False" by auto
qed

lemma empty_idempotent [simp]: "idempotent Map.empty"
  by (simp add: idempotent_def)

lemma idempotent_narrower [simp]: "idempotent \<sigma> \<Longrightarrow> idempotent (\<sigma>(x := None))"
proof (unfold idempotent_def)
  assume "dom \<sigma> \<inter> subst_vars \<sigma> = {}"
  moreover have "subst_vars (\<sigma>(x := None)) \<subseteq> subst_vars \<sigma>" by simp
  ultimately have "dom \<sigma> \<inter> subst_vars (\<sigma>(x := None)) = {}" by blast
  thus "dom (\<sigma>(x := None)) \<inter> subst_vars (\<sigma>(x := None)) = {}" by auto
qed 

lemma extend_subst_idempotent [simp]: "idempotent \<sigma> \<Longrightarrow> x \<notin> uvars \<tau> \<Longrightarrow> x \<notin> dom \<sigma> \<Longrightarrow> 
  x \<notin> subst_vars \<sigma> \<Longrightarrow> idempotent (extend_subst x \<tau> \<sigma>)"
proof (unfold idempotent_def)
  assume D: "dom \<sigma> \<inter> subst_vars \<sigma> = {}"
  assume E: "x \<notin> uvars \<tau>"
  assume S: "x \<notin> dom \<sigma>"
  assume R: "x \<notin> subst_vars \<sigma>"
  have V: "uvars (subst \<sigma> \<tau>) \<subseteq> uvars \<tau> - dom \<sigma> \<union> subst_vars \<sigma>" by simp
  with E R have A: "x \<notin> uvars (subst \<sigma> \<tau>)" by blast
  from D V have "dom \<sigma> \<inter> uvars (subst \<sigma> \<tau>) = {}" by blast
  with A D S R show "dom (extend_subst x \<tau> \<sigma>) \<inter> subst_vars (extend_subst x \<tau> \<sigma>) = {}" by auto
qed

lemma combine_subst_idempotent [simp]: "dom \<sigma> \<inter> dom \<sigma>' = {} \<Longrightarrow> dom \<sigma>' \<inter> subst_vars \<sigma> = {} \<Longrightarrow> 
    idempotent \<sigma> \<Longrightarrow>  idempotent \<sigma>' \<Longrightarrow> idempotent (combine_subst \<sigma> \<sigma>')"
  by (auto simp add: idempotent_def)

lemma dissect_subst [simp]: "\<sigma> x = Some (subst \<sigma> \<tau>) \<Longrightarrow> x \<notin> uvars \<tau> \<Longrightarrow> \<sigma> unifies\<^sub>\<kappa> \<kappa> \<Longrightarrow> 
  idempotent \<sigma> \<Longrightarrow> 
    \<exists>\<sigma>'. \<sigma> = extend_subst x \<tau> \<sigma>' \<and> \<sigma>' unifies\<^sub>\<kappa> constr_subst x \<tau> \<kappa> \<and> idempotent \<sigma>'"
proof (unfold extend_subst_def)
  assume "\<sigma> x = Some (subst \<sigma> \<tau>)" and "x \<notin> uvars \<tau>" and "\<sigma> unifies\<^sub>\<kappa> \<kappa>" and "idempotent \<sigma>"
  hence "\<sigma> = (\<sigma>(x := None))(x \<mapsto> subst (\<sigma>(x := None)) \<tau>) \<and> 
    (\<sigma>(x := None)) unifies\<^sub>\<kappa> constr_subst x \<tau> \<kappa> \<and> idempotent (\<sigma>(x := None))" by auto
  thus "\<exists>\<sigma>'. \<sigma> = \<sigma>'(x \<mapsto> subst \<sigma>' \<tau>) \<and> \<sigma>' unifies\<^sub>\<kappa> constr_subst x \<tau> \<kappa>  \<and> idempotent \<sigma>'" by blast
qed

lemma split_not_in_domain: "x \<notin> dom \<sigma> \<Longrightarrow> subst \<sigma> = subst \<sigma>' \<circ> subst \<sigma>'' \<Longrightarrow> x \<notin> dom \<sigma>'' \<Longrightarrow> 
  idempotent \<sigma>' \<Longrightarrow> x \<notin> dom \<sigma>'"
proof -
  assume "x \<notin> dom \<sigma>" and "x \<notin> dom \<sigma>''"
  hence X: "\<sigma> x = None \<and> \<sigma>'' x = None" by blast
  assume "subst \<sigma> = subst \<sigma>' \<circ> subst \<sigma>''"
  hence Y: "subst \<sigma> (Var x) = subst \<sigma>' (subst \<sigma>'' (Var x))" by simp
  assume "idempotent \<sigma>'"
  hence "\<sigma>' x \<noteq> Some (Var x)" by simp
  with X Y show "x \<notin> dom \<sigma>'" by (auto split: option.splits)
qed

text \<open>We now define what it means for one substitution to specialize another. The specialize 
relation is a preorder, but not a partial order - \<open>specialize_refl\<close>, \<open>specialize_trans\<close>, and 
\<open>specialize_not_antisym\<close> show this.\<close>

definition subst_specialize :: "subst \<Rightarrow> subst \<Rightarrow> bool" (infix "specializes" 50) where
  "\<sigma>' specializes \<sigma> \<equiv> (\<exists>\<sigma>''. subst \<sigma>' = subst \<sigma>'' \<circ> subst \<sigma>)"

lemma anything_specializes_empty [simp]: "\<sigma> specializes Map.empty"
  by (auto simp add: subst_specialize_def)

lemma extend_subst_specializes [simp]: "\<sigma> specializes \<sigma>' \<Longrightarrow> 
  extend_subst x \<tau> \<sigma> specializes extend_subst x \<tau> \<sigma>'"
proof (unfold subst_specialize_def)
  assume "\<exists>\<sigma>''. subst \<sigma> = subst \<sigma>'' \<circ> subst \<sigma>'"
  then obtain \<sigma>'' where "subst \<sigma> = subst \<sigma>'' \<circ> subst \<sigma>'" by blast
  moreover hence "subst (extend_subst x \<tau> \<sigma>) = subst \<sigma>'' \<circ> subst (extend_subst x \<tau> \<sigma>')" 
    by (simp add: expand_extend_subst) auto
  ultimately show "\<exists>\<sigma>''. subst (extend_subst x \<tau> \<sigma>) = subst \<sigma>'' \<circ> subst (extend_subst x \<tau> \<sigma>')" 
    by auto
qed

lemma specializes_refl [simp]: "\<sigma> specializes \<sigma>"
proof (unfold subst_specialize_def)
  have "subst \<sigma> = subst Map.empty \<circ> subst \<sigma>" by simp
  thus "\<exists>\<sigma>''. subst \<sigma> = subst \<sigma>'' \<circ> subst \<sigma>" by blast
qed

lemma specializes_trans [elim]: "\<sigma> specializes \<sigma>' \<Longrightarrow> \<sigma>' specializes \<sigma>'' \<Longrightarrow> \<sigma> specializes \<sigma>''"
proof (unfold subst_specialize_def)
  assume "\<exists>\<sigma>\<^sub>1. subst \<sigma> = subst \<sigma>\<^sub>1 \<circ> subst \<sigma>'"
  then obtain \<sigma>\<^sub>1 where S1: "subst \<sigma> = subst \<sigma>\<^sub>1 \<circ> subst \<sigma>'" by fastforce
  assume "\<exists>\<sigma>\<^sub>2. subst \<sigma>' = subst \<sigma>\<^sub>2 \<circ> subst \<sigma>''" 
  then obtain \<sigma>\<^sub>2 where S2: "subst \<sigma>' = subst \<sigma>\<^sub>2 \<circ> subst \<sigma>''" by fastforce
  have "subst \<sigma>\<^sub>1 \<circ> (subst \<sigma>\<^sub>2 \<circ> subst \<sigma>'') = subst (combine_subst \<sigma>\<^sub>1 \<sigma>\<^sub>2) \<circ> subst \<sigma>''" by fastforce
  with S1 S2 show "\<exists>\<sigma>\<^sub>3. subst \<sigma> = subst \<sigma>\<^sub>3 \<circ> subst \<sigma>''" by metis
qed

lemma specializes_not_antisym: "\<exists>\<sigma> \<sigma>'. \<sigma> specializes \<sigma>' \<and> \<sigma>' specializes \<sigma> \<and> \<sigma> \<noteq> \<sigma>'"
proof (unfold subst_specialize_def)
  let ?x = "V 0" and ?y = "V 1"
  have "\<exists>z. [?x \<mapsto> Var ?y] z \<noteq> [?y \<mapsto> Var ?x] z" by auto
  hence "[?x \<mapsto> Var ?y] \<noteq> [?y \<mapsto> Var ?x]" by metis
  moreover have "\<exists>\<sigma>''. subst [?x \<mapsto> Var ?y] = subst \<sigma>'' \<circ> subst [?y \<mapsto> Var ?x]" 
  proof 
    show "subst [?x \<mapsto> Var ?y] = subst [?x \<mapsto> Var ?y] \<circ> subst [?y \<mapsto> Var ?x]" by simp
  qed
  moreover have "\<exists>\<sigma>''. subst [?y \<mapsto> Var ?x] = subst \<sigma>'' \<circ> subst [?x \<mapsto> Var ?y]" 
  proof 
    show "subst [?y \<mapsto> Var ?x] = subst [?y \<mapsto> Var ?x] \<circ> subst [?x \<mapsto> Var ?y]" by simp
  qed
  ultimately show "\<exists>\<sigma> \<sigma>'. (\<exists>\<sigma>''. subst \<sigma> = subst \<sigma>'' \<circ> subst \<sigma>') \<and> 
    (\<exists>\<sigma>''. subst \<sigma>' = subst \<sigma>'' \<circ> subst \<sigma>) \<and> \<sigma> \<noteq> \<sigma>'" by blast
qed

lemma specializes_still_unifies [elim]: "\<sigma> unifies e\<^sub>1 and e\<^sub>2 \<Longrightarrow> \<sigma>' specializes \<sigma> \<Longrightarrow> 
    \<sigma>' unifies e\<^sub>1 and e\<^sub>2"
  by (auto simp add: subst_specialize_def)

text \<open>Finally, we prove some helper lemmas which will be useful for the "occurs check" in the 
unification algorithm. Essentially, we prove that a variable cannot be unified with a term 
containing that variable - at least not without infinite terms, which we do not allow - and thus we 
can later justify the correctness of the check for this situation.\<close>

lemma occurs_check' [simp]: "x \<in> uvars \<tau> \<Longrightarrow> \<tau> \<noteq> Var x \<Longrightarrow> 
    size (subst \<sigma> (Var x)) < size (subst \<sigma> \<tau>)"
  and [simp]: "x \<in> uvarss \<tau>s \<Longrightarrow> size (subst \<sigma> (Var x)) < size_list (size \<circ> subst \<sigma>) \<tau>s"
proof (induction \<tau> and \<tau>s rule: uvars_uvarss.induct)
  case (4 \<tau> \<tau>s)
  thus ?case by force
qed fastforce+

lemma occurs_check [simp]: "x \<in> uvars \<tau> \<Longrightarrow> \<tau> \<noteq> Var x \<Longrightarrow> \<sigma> unifies Var x and \<tau> \<Longrightarrow> False"
proof -
  assume "x \<in> uvars \<tau>" and "\<tau> \<noteq> Var x" 
  hence "size (subst \<sigma> (Var x)) < size (subst \<sigma> \<tau>)" by (metis occurs_check')
  moreover assume "\<sigma> unifies Var x and \<tau>"
  ultimately show ?thesis by simp
qed

lemma occurs_check2' [simp]: "x \<in> uvars \<tau> \<Longrightarrow> \<tau> \<noteq> Var x \<Longrightarrow> 
    size (subst \<sigma> \<tau>') < size (subst \<sigma> (subst [x \<mapsto> \<tau>'] \<tau>))"
  and [simp]: "x \<in> uvarss \<tau>s \<Longrightarrow> size (subst \<sigma> \<tau>') < size_list (size \<circ> subst \<sigma> \<circ> subst [x \<mapsto> \<tau>']) \<tau>s"
proof (induction \<tau> and \<tau>s rule: uvars_uvarss.induct)
  case (2 \<gamma> \<tau>s)
  hence "size (subst \<sigma> \<tau>') < size_list (size \<circ> subst \<sigma> \<circ> subst [x \<mapsto> \<tau>']) \<tau>s" by fastforce
  hence "size (subst \<sigma> \<tau>') < size (subst \<sigma> (subst [x \<mapsto> \<tau>'] (Ctor \<gamma> \<tau>s)))" 
    by (simp add: fun.map_comp)
  thus ?case by blast
next
  case (4 \<tau> \<tau>s)
  thus ?case by force
qed simp_all

lemma occurs_check2 [simp]: "x \<in> uvars \<tau> \<Longrightarrow> \<tau> \<noteq> Var x \<Longrightarrow> \<sigma> unifies \<tau>' and subst [x \<mapsto> \<tau>'] \<tau> \<Longrightarrow> 
  False"
proof -
  assume "x \<in> uvars \<tau>" and "\<tau> \<noteq> Var x" 
  hence "size (subst \<sigma> \<tau>') < size (subst \<sigma> (subst [x \<mapsto> \<tau>'] \<tau>))" by (metis occurs_check2')
  moreover assume "\<sigma> unifies \<tau>' and subst [x \<mapsto> \<tau>'] \<tau>"
  ultimately show ?thesis by simp
qed

end