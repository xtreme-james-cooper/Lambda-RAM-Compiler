theory Substitution
  imports UnifyExpr
begin

type_synonym subst = "var \<rightharpoonup> uexpr"

fun subst :: "subst \<Rightarrow> uexpr \<Rightarrow> uexpr" where
  "subst s (Var y) = (case s y of Some e \<Rightarrow> e | None \<Rightarrow> Var y)"
| "subst s (Ctor k es) = Ctor k (map (subst s) es)"

definition subst_vars :: "subst \<Rightarrow> var set" where
  "subst_vars s = \<Union> (vars ` ran s)"

fun list_subst :: "var \<Rightarrow> uexpr \<Rightarrow> (uexpr \<times> uexpr) list \<Rightarrow> (uexpr \<times> uexpr) list" where
  "list_subst x e' [] = []"
| "list_subst x e' ((e\<^sub>1, e\<^sub>2) # ess) = (subst [x \<mapsto> e'] e\<^sub>1, subst [x \<mapsto> e'] e\<^sub>2) # list_subst x e' ess"

abbreviation unifier :: "subst \<Rightarrow> uexpr \<Rightarrow> uexpr \<Rightarrow> bool" (infix "unifies _ and" 50) where 
  "unifier s e\<^sub>1 e\<^sub>2 \<equiv> subst s e\<^sub>1 = subst s e\<^sub>2"

fun list_unifier :: "subst \<Rightarrow> (uexpr \<times> uexpr) list \<Rightarrow> bool" (infix "unifies\<^sub>l" 50) where 
  "list_unifier s [] = True"
| "list_unifier s ((e\<^sub>1, e\<^sub>2) # ess) = ((s unifies e\<^sub>1 and e\<^sub>2) \<and> list_unifier s ess)"

definition extend_subst :: "var \<Rightarrow> uexpr \<Rightarrow> subst \<Rightarrow> subst" where
  "extend_subst x e s = (s(x \<mapsto> subst s e))"

definition combine_subst :: "subst \<Rightarrow> subst \<Rightarrow> subst" where
  "combine_subst s\<^sub>1 s\<^sub>2 x = (case s\<^sub>2 x of None \<Rightarrow> s\<^sub>1 x | Some e \<Rightarrow> Some (subst s\<^sub>1 e))"

definition ordered_subst :: "subst \<Rightarrow> bool" where
  "ordered_subst s = (dom s \<inter> subst_vars s = {})"

lemma [simp]: "x \<notin> vars e \<Longrightarrow> subst [x \<mapsto> e'] e = e"
  and [simp]: "x \<notin> varss es \<Longrightarrow> map (subst [x \<mapsto> e']) es = es"
  by (induction e and es rule: vars_varss.induct) simp_all

lemma [simp]: "x \<in> vars e \<Longrightarrow> vars (subst [x \<mapsto> e'] e) = vars e - {x} \<union> vars e'"
  and [simp]: "x \<in> varss es \<Longrightarrow> varss (map (subst [x \<mapsto> e']) es) = varss es - {x} \<union> vars e'"
proof (induction e and es rule: vars_varss.induct)
  case (4 e es)
  hence "varss (map (subst [x \<mapsto> e']) (e # es)) = varss (e # es) - {x} \<union> vars e'" by fastforce
  thus ?case by blast
qed simp_all

lemma [simp]: "vars (subst [x \<mapsto> e'] e) = vars e - {x} \<union> (if x \<in> vars e then vars e' else {})"
  by simp

lemma [simp]: "list_subst x e (es\<^sub>1 @ es\<^sub>2) = list_subst x e es\<^sub>1 @ list_subst x e es\<^sub>2"
  by (induction es\<^sub>1 rule: list_subst.induct) simp_all

lemma [simp]: "list_subst x e (zip es\<^sub>1 es\<^sub>2) = 
    zip (map (subst [x \<mapsto> e]) es\<^sub>1) (map (subst [x \<mapsto> e]) es\<^sub>2)"
proof (induction es\<^sub>1 arbitrary: es\<^sub>2)
  case (Cons e\<^sub>1 es\<^sub>1)
  thus ?case by (induction es\<^sub>2) simp_all
qed simp_all

lemma [simp]: "x \<notin> list_vars ess \<Longrightarrow> list_vars (list_subst x e ess) = list_vars ess"
  by (induction ess rule: list_vars.induct) simp_all

lemma [simp]: "x \<in> list_vars ess \<Longrightarrow> list_vars (list_subst x e ess) = list_vars ess - {x} \<union> vars e"
proof (induction ess rule: list_vars.induct)
  case (2 e\<^sub>1 e\<^sub>2 ess)
  thus ?case by (cases "x \<in> list_vars ess") auto
qed simp_all

lemma [simp]: "list_vars (list_subst x e ess) = 
    list_vars ess - {x} \<union> (if x \<in> list_vars ess then vars e else {})"
  by simp

lemma [simp]: "vars (subst s e) \<subseteq> vars e - dom s \<union> subst_vars s"
  and [simp]: "varss (map (subst s) es) \<subseteq> varss es - dom s \<union> subst_vars s"
  by (induction e and es rule: vars_varss.induct) 
     (auto simp add: subst_vars_def ranI split: option.splits)

lemma [simp]: "subst_vars Map.empty = {}"
  by (simp add: subst_vars_def)

lemma [simp]: "dom (extend_subst x e s) = insert x (dom s)"
  by (auto simp add: extend_subst_def)

lemma [simp]: "ran (extend_subst x e s) = insert (subst s e) (ran (s(x := None)))"
  by (auto simp add: extend_subst_def ran_def)

lemma [simp]: "subst [x \<mapsto> Var x] e = e"
  and [simp]: "map (subst [x \<mapsto> Var x]) es = es"
  by (induction e and es rule: vars_varss.induct) simp_all

lemma [simp]: "subst [x \<mapsto> Var x] = id"
  by auto

lemma [simp]: "subst [y \<mapsto> Var x] (subst [x \<mapsto> Var y] e) = subst [y \<mapsto> Var x] e"
  and [simp]: "map (subst [y \<mapsto> Var x] \<circ> subst [x \<mapsto> Var y]) es = map (subst [y \<mapsto> Var x]) es"
  by (induction e and es rule: vars_varss.induct) simp_all

lemma [simp]: "subst [y \<mapsto> Var x] \<circ> subst [x \<mapsto> Var y] = subst [y \<mapsto> Var x]"
  by auto

lemma expand_extend_subst: "subst (extend_subst x e s) = subst s \<circ> subst [x \<mapsto> e]"
proof
  fix ee
  show "subst (extend_subst x e s) ee = (subst s \<circ> subst [x \<mapsto> e]) ee"
    by (induction ee) (auto simp add: extend_subst_def)
qed

lemma [simp]: "s x = Some (subst s e) \<Longrightarrow> extend_subst x e s = s"
  by (auto simp add: extend_subst_def)

lemma [simp]: "s x = None \<Longrightarrow> s y = Some (Var x) \<Longrightarrow> subst (extend_subst x (Var y) s) e = subst s e"
  and [simp]: "s x = None \<Longrightarrow> s y = Some (Var x) \<Longrightarrow> 
    map (subst (extend_subst x (Var y) s)) es = map (subst s) es"
  by (induction e and es rule: vars_varss.induct) (simp_all add: extend_subst_def)

lemma [simp]: "s x = None \<Longrightarrow> s y = Some (Var x) \<Longrightarrow> subst (extend_subst x (Var y) s) = subst s"
  by auto

lemma [simp]: "x \<notin> subst_vars s \<Longrightarrow> s y = Some e \<Longrightarrow> subst [x \<mapsto> e'] e = e"
proof -
  assume "s y = Some e" 
  hence "e \<in> ran s" by (metis ranI)
  moreover assume "x \<notin> subst_vars s" 
  ultimately show ?thesis by (simp add: subst_vars_def)
qed

lemma [simp]: "x \<notin> dom s \<Longrightarrow> x \<notin> subst_vars s \<Longrightarrow> 
  subst s \<circ> subst [x \<mapsto> e] = subst [x \<mapsto> subst s e] \<circ> subst s"
proof
  fix ee
  assume "x \<notin> dom s" and "x \<notin> subst_vars s"
  thus "(subst s \<circ> subst [x \<mapsto> e]) ee = (subst [x \<mapsto> subst s e] \<circ> subst s) ee"
    by (induction ee) (auto split: option.splits)
qed

lemma [simp]: "x \<notin> dom s \<Longrightarrow> subst_vars (extend_subst x e s) = vars (subst s e) \<union> subst_vars s"
  by (auto simp add: extend_subst_def subst_vars_def)

lemma [simp]: "extend_subst x e s x = Some (subst s e)"
  by (simp add: extend_subst_def) 

lemma [simp]: "ordered_subst Map.empty"
  by (simp add: ordered_subst_def)

lemma [simp]: "ordered_subst s \<Longrightarrow> x \<notin> vars e \<Longrightarrow> x \<notin> dom s \<Longrightarrow> x \<notin> subst_vars s \<Longrightarrow>
  ordered_subst (extend_subst x e s)"
proof (unfold ordered_subst_def)
  assume D: "dom s \<inter> subst_vars s = {}"
  assume E: "x \<notin> vars e"
  assume S: "x \<notin> dom s"
  assume R: "x \<notin> subst_vars s"
  have V: "vars (subst s e) \<subseteq> vars e - dom s \<union> subst_vars s" by simp
  with E R have A: "x \<notin> vars (subst s e)" by blast
  from D V have "dom s \<inter> vars (subst s e) = {}" by blast
  with A D S R show "dom (extend_subst x e s) \<inter> subst_vars (extend_subst x e s) = {}" by auto
qed

lemma [simp]: "vars e \<inter> dom s = {} \<Longrightarrow> subst s e = e"
  and [simp]: "varss es \<inter> dom s = {} \<Longrightarrow> map (subst s) es = es"
  by (induction e and es rule: vars_varss.induct) (auto split: option.splits)

lemma [simp]: "y \<notin> dom s \<Longrightarrow> s x = Some (Var y) \<Longrightarrow> subst s (subst [x \<mapsto> Var y] e) = subst s e"
  and [simp]: "y \<notin> dom s \<Longrightarrow> s x = Some (Var y) \<Longrightarrow>
    map (subst s \<circ> subst [x \<mapsto> Var y]) es = map (subst s) es"
  by (induction e and es rule: vars_varss.induct) (auto split: option.splits)

lemma [simp]: "y \<notin> dom s \<Longrightarrow> s x = Some (Var y) \<Longrightarrow> subst s \<circ> subst [x \<mapsto> Var y] = subst s"
  by (rule, simp)

lemma [simp]: "s unifies\<^sub>l (ess\<^sub>1 @ ess\<^sub>2) = (s unifies\<^sub>l ess\<^sub>1 \<and> s unifies\<^sub>l ess\<^sub>2)"
  by (induction s ess\<^sub>1 rule: list_unifier.induct) simp_all

lemma [simp]: "length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> 
  s unifies\<^sub>l zip es\<^sub>1 es\<^sub>2 = (map (subst s) es\<^sub>1 = map (subst s) es\<^sub>2)"
proof (induction es\<^sub>1 arbitrary: es\<^sub>2)
  case (Cons e\<^sub>1 es\<^sub>1)
  thus ?case by (induction es\<^sub>2) simp_all
qed simp_all

lemma occurs_check' [simp]: "x \<in> vars e \<Longrightarrow> e \<noteq> Var x \<Longrightarrow> size (subst s (Var x)) < size (subst s e)"
  and [simp]: "x \<in> varss es \<Longrightarrow> size (subst s (Var x)) < size_list (size \<circ> subst s) es"
proof (induction e and es rule: vars_varss.induct)
  case (4 e es)
  thus ?case by force
qed fastforce+

lemma occurs_check [simp]: "x \<in> vars e \<Longrightarrow> e \<noteq> Var x \<Longrightarrow> s unifies Var x and e \<Longrightarrow> False"
proof -
  assume "x \<in> vars e" and "e \<noteq> Var x" 
  hence "size (subst s (Var x)) < size (subst s e)" by (metis occurs_check')
  moreover assume "s unifies Var x and e"
  ultimately show ?thesis by simp
qed

lemma [simp]: "x \<in> varss es \<Longrightarrow> s x \<noteq> Some (Ctor k (map (subst s) es))"
proof
  assume "x \<in> varss es"
  hence X: "x \<in> vars (Ctor k es)" by simp
  have Y: "Ctor k es \<noteq> Var x" by simp
  assume "s x = Some (Ctor k (map (subst s) es))"
  hence "s unifies Var x and Ctor k es" by simp
  with X Y show False by (metis occurs_check)
qed

lemma [simp]: "subst s (subst [x \<mapsto> e'] e) = subst (extend_subst x e' s) e"
  by (induction e) (simp_all add: extend_subst_def split: option.splits)

lemma [simp]: "s unifies\<^sub>l list_subst x e ess = (extend_subst x e s unifies\<^sub>l ess)"
  by (induction s ess rule: list_unifier.induct) simp_all

lemma [simp]: "subst Map.empty e = e"
  and [simp]: "map (subst Map.empty) es = es"
  by (induction e and es rule: vars_varss.induct) simp_all

lemma [simp]: "x \<notin> vars e \<Longrightarrow> subst (s(x := y)) e = subst s e"
  and [simp]: "x \<notin> varss es \<Longrightarrow> map (subst (s(x := y))) es = map (subst s) es"
  by (induction e and es rule: vars_varss.induct) (simp_all split: option.splits)

lemma [simp]: "x \<notin> vars e \<Longrightarrow> subst (extend_subst x e' s) e = subst s e"
  by (simp_all add: extend_subst_def)

lemma [simp]: "s x = None \<Longrightarrow> subst (s(x \<mapsto> Var x)) e = subst s e"
  by (induction e) simp_all

lemma [simp]: "s x = None \<Longrightarrow> (s(x \<mapsto> Var x) unifies\<^sub>l ess) = (s unifies\<^sub>l ess)"
  by (induction s ess rule: list_unifier.induct) simp_all

lemma [simp]: "s y = Some (Var x) \<Longrightarrow> s x = None \<Longrightarrow> 
    extend_subst x (Var y) s unifies\<^sub>l ess = (s unifies\<^sub>l ess)"
  by (simp add: extend_subst_def)

lemma [dest]: "subst s e = Var x \<Longrightarrow> 
    (e = Var x \<and> s x = None) \<or> (\<exists>y. e = Var y \<and> s y = Some (Var x))"
  by (induction e) (simp_all split: option.splits)

lemma subst_subst_var [dest, consumes 1, case_names Eq FstOnly SndOnly Both]: 
  "(subst s \<circ> subst t) (Var x) = Var y \<Longrightarrow> (x = y \<Longrightarrow> P) \<Longrightarrow> 
    (s y = None \<Longrightarrow> t x = Some (Var y) \<Longrightarrow> P) \<Longrightarrow> (s x = Some (Var y) \<Longrightarrow> t x = None \<Longrightarrow> P) \<Longrightarrow> 
      (\<And>z. s z = Some (Var y) \<Longrightarrow> t x = Some (Var z) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto split: option.splits)

lemma [simp]: "s x = Some (subst s e) \<Longrightarrow> x \<notin> vars e \<Longrightarrow> extend_subst x e (s(x := None)) = s"
  by rule (simp add: extend_subst_def)

lemma [simp]: "subst_vars (s(x := None)) \<subseteq> subst_vars s"
  by (auto simp add: subst_vars_def) (metis ranI ran_restrictD restrict_complement_singleton_eq)

lemma [simp]: "ordered_subst s \<Longrightarrow> ordered_subst (s(x := None))"
proof (unfold ordered_subst_def)
  assume "dom s \<inter> subst_vars s = {}"
  moreover have "subst_vars (s(x := None)) \<subseteq> subst_vars s" by simp
  ultimately have "dom s \<inter> subst_vars (s(x := None)) = {}" by blast
  thus "dom (s(x := None)) \<inter> subst_vars (s(x := None)) = {}" by auto
qed 

lemma dissect_subst [simp]: "s x = Some (subst s e) \<Longrightarrow> x \<notin> vars e \<Longrightarrow> s unifies\<^sub>l ess \<Longrightarrow> 
  ordered_subst s \<Longrightarrow> 
    \<exists>t. s = extend_subst x e t \<and> t unifies\<^sub>l list_subst x e ess \<and> ordered_subst t"
proof (unfold extend_subst_def)
  assume "s x = Some (subst s e)" and "x \<notin> vars e" and "s unifies\<^sub>l ess" and "ordered_subst s"
  hence "s = (s(x := None))(x \<mapsto> subst (s(x := None)) e) \<and> 
    (s(x := None)) unifies\<^sub>l list_subst x e ess \<and> ordered_subst (s(x := None))" by auto
  thus "\<exists>t. s = t(x \<mapsto> subst t e) \<and> t unifies\<^sub>l list_subst x e ess  \<and> ordered_subst t" by blast
qed

lemma [dest]: "x \<notin> subst_vars s \<Longrightarrow> s y = Some (Var x) \<Longrightarrow> False"
proof (unfold subst_vars_def)
  assume "s y = Some (Var x)"
  hence "x \<in> \<Union> (vars ` ran s)" using vars.simps ranI by force
  moreover assume "x \<notin> \<Union> (vars ` ran s)" 
  ultimately show "False" by simp
qed

lemma [simp]: "s unifies\<^sub>l ess \<Longrightarrow> s x = None \<Longrightarrow> s y = Some (Var x) \<Longrightarrow> 
    s unifies\<^sub>l list_subst x (Var y) ess"
  by (simp add: extend_subst_def)

lemma [simp]: "ordered_subst t \<Longrightarrow> t x \<noteq> Some (Var x)"
proof (rule, unfold ordered_subst_def)
  assume "t x = Some (Var x)"
  hence "x \<in> dom t \<and> x \<in> subst_vars t"
    using vars.simps(1) by fastforce
  moreover assume "dom t \<inter> subst_vars t = {}" 
  ultimately show "False" by auto
qed

lemma split_not_in_domain: "x \<notin> dom s \<Longrightarrow> subst s = subst t \<circ> subst u \<Longrightarrow> x \<notin> dom u \<Longrightarrow> 
  ordered_subst t \<Longrightarrow> x \<notin> dom t"
proof -
  assume "x \<notin> dom s" and "x \<notin> dom u"
  hence X: "s x = None \<and> u x = None" by blast
  assume "subst s = subst t \<circ> subst u"
  hence Y: "subst s (Var x) = subst t (subst u (Var x))" by simp
  assume "ordered_subst t"
  hence "t x \<noteq> Some (Var x)" by simp
  with X Y show "x \<notin> dom t" by (auto split: option.splits)
qed

lemma [simp]: "P e \<Longrightarrow> \<forall>x\<in>ran s. P x \<Longrightarrow> structural P \<Longrightarrow> P (subst s e)"
  and [simp]: "list_all P es \<Longrightarrow> \<forall>x\<in>ran s. P x \<Longrightarrow> structural P \<Longrightarrow> list_all P (map (subst s) es)"
  by (induction e and es rule: vars_varss.induct) 
    (auto simp add: structural_def ran_def split: option.splits)

lemma [simp]: "P e \<Longrightarrow> structural P \<Longrightarrow> list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) ess \<Longrightarrow> 
    list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) (list_subst x e ess)"
  by (induction ess rule: list_subst.induct) simp_all

lemma [simp]: "subst (combine_subst s t) e = subst s (subst t e)"
  by (induction e) (simp_all add: combine_subst_def split: option.splits)

lemma [simp]: "subst (combine_subst s t) = subst s \<circ> subst t"
  by auto

end