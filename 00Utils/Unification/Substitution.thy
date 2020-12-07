theory Substitution
  imports UnifyExpr
begin

type_synonym subst = "string \<rightharpoonup> expr"

fun subst :: "subst \<Rightarrow> expr \<Rightarrow> expr" where
  "subst s (Var y) = (case s y of Some e \<Rightarrow> e | None \<Rightarrow> Var y)"
| "subst s (Ctor k es) = Ctor k (map (subst s) es)"

definition subst_vars :: "subst \<Rightarrow> string set" where
  "subst_vars s = \<Union> (vars ` ran s)"

fun list_subst :: "string \<Rightarrow> expr \<Rightarrow> (expr \<times> expr) list \<Rightarrow> (expr \<times> expr) list" where
  "list_subst x e' [] = []"
| "list_subst x e' ((e\<^sub>1, e\<^sub>2) # ess) = (subst [x \<mapsto> e'] e\<^sub>1, subst [x \<mapsto> e'] e\<^sub>2) # list_subst x e' ess"

abbreviation unifier :: "subst \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> bool" (infix "unifies _ and" 50) where 
  "unifier s e\<^sub>1 e\<^sub>2 \<equiv> subst s e\<^sub>1 = subst s e\<^sub>2"

fun list_unifier :: "subst \<Rightarrow> (expr \<times> expr) list \<Rightarrow> bool" (infix "unifies\<^sub>l" 50) where 
  "list_unifier s [] = True"
| "list_unifier s ((e\<^sub>1, e\<^sub>2) # ess) = ((s unifies e\<^sub>1 and e\<^sub>2) \<and> list_unifier s ess)"

definition extend_subst :: "string \<Rightarrow> expr \<Rightarrow> subst \<Rightarrow> subst" where
  "extend_subst x e s = (s(x \<mapsto> subst s e))"

definition ordered_subst :: "subst \<Rightarrow> bool" where
  "ordered_subst s = (dom s \<inter> subst_vars s = {})"

lemma [simp]: "x \<notin> vars e \<Longrightarrow> vars (subst [x \<mapsto> e'] e) = vars e"
  and [simp]: "x \<notin> varss es \<Longrightarrow> varss (map (subst [x \<mapsto> e']) es) = varss es"
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

lemma [simp]: "x \<notin> dom s \<Longrightarrow> subst_vars (extend_subst x e s) = vars (subst s e) \<union> subst_vars s"
  by (auto simp add: extend_subst_def subst_vars_def)

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

lemma [simp]: "extend_subst x e s x = Some (subst s e)"
  by (simp add: extend_subst_def)

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

lemma var_subst [simp]: "Var x = subst s e \<Longrightarrow> 
    (e = Var x \<and> s x = None) \<or> (\<exists>y. e = Var y \<and> s y = Some (Var x))"
  by (induction e) (simp_all split: option.splits)

lemma [simp]: "s x = Some (subst s e) \<Longrightarrow> x \<notin> vars e \<Longrightarrow> extend_subst x e (s(x := None)) = s"
  by rule (simp add: extend_subst_def)

end