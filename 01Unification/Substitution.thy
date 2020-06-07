theory Substitution
  imports UnifyExpr
begin

type_synonym subst = "string \<rightharpoonup> expr"

fun subst :: "subst \<Rightarrow> expr \<Rightarrow> expr" where
  "subst s (Var y) = (case s y of Some e \<Rightarrow> e | None \<Rightarrow> Var y)"
| "subst s (Ctor k es) = Ctor k (map (subst s) es)"

fun list_subst :: "string \<Rightarrow> expr \<Rightarrow> (expr \<times> expr) list \<Rightarrow> (expr \<times> expr) list" where
  "list_subst x e' [] = []"
| "list_subst x e' ((e\<^sub>1, e\<^sub>2) # ess) = (subst [x \<mapsto> e'] e\<^sub>1, subst [x \<mapsto> e'] e\<^sub>2) # list_subst x e' ess"

abbreviation unifier :: "subst \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> bool" (infix "unifies _ and" 50) where 
  "unifier s e\<^sub>1 e\<^sub>2 \<equiv> subst s e\<^sub>1 = subst s e\<^sub>2"

fun list_unifier :: "subst \<Rightarrow> (expr \<times> expr) list \<Rightarrow> bool" (infix "unifies\<^sub>l" 50) where 
  "list_unifier s [] = True"
| "list_unifier s ((e\<^sub>1, e\<^sub>2) # ess) = ((s unifies e\<^sub>1 and e\<^sub>2) \<and> list_unifier s ess)"

definition extend_subst :: "string \<Rightarrow> expr \<Rightarrow> subst \<Rightarrow> subst" where
  "extend_subst x e s y = (if x = y then Some e else map_option (subst [x \<mapsto> e]) (s y))"

definition ordered_subst :: "subst \<Rightarrow> bool" where
  "ordered_subst s = (dom s \<inter> \<Union> (vars ` ran s) = {})"

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

lemma [simp]: "dom (extend_subst x e s) = insert x (dom s)"
  by (auto simp add: extend_subst_def)

lemma [simp]: "x \<notin> dom s \<Longrightarrow> ran (extend_subst x e s) = insert e (subst [x \<mapsto> e] ` ran s)"
  by (auto simp add: extend_subst_def ran_def)

lemma [simp]: "ordered_subst Map.empty"
  by (simp add: ordered_subst_def)

lemma [simp]: "ordered_subst s \<Longrightarrow> x \<notin> vars e \<Longrightarrow> vars e \<inter> dom s = {} \<Longrightarrow> x \<notin> dom s \<Longrightarrow> 
    ordered_subst (extend_subst x e s)"
  by (auto simp add: ordered_subst_def split: if_splits)

lemma [simp]: "s unifies\<^sub>l (ess\<^sub>1 @ ess\<^sub>2) = (s unifies\<^sub>l ess\<^sub>1 \<and> s unifies\<^sub>l ess\<^sub>2)"
  by (induction s ess\<^sub>1 rule: list_unifier.induct) simp_all

lemma [simp]: "length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> 
  s unifies\<^sub>l zip es\<^sub>1 es\<^sub>2 = (map (subst s) es\<^sub>1 = map (subst s) es\<^sub>2)"
proof (induction es\<^sub>1 arbitrary: es\<^sub>2)
  case (Cons e\<^sub>1 es\<^sub>1)
  thus ?case by (induction es\<^sub>2) simp_all
qed simp_all

lemma unify_subst_one: "s unifies e\<^sub>1 and e\<^sub>2 \<Longrightarrow> s unifies Var x and e' \<Longrightarrow> 
    s unifies subst [x \<mapsto> e'] e\<^sub>1 and subst [x \<mapsto> e'] e\<^sub>2"
proof (induction e\<^sub>1 arbitrary: e\<^sub>2)
  case (Var y)
  thus ?case 
  proof (induction e\<^sub>2)
    case (Var z)
    from Var have "subst s (Var y) = subst s (Var z)" by simp
    from Var have "subst s (Var x) = subst s e'" by simp


    have "subst s (subst [x \<mapsto> e'] (Var y)) = subst s (subst [x \<mapsto> e'] (Var z))" by simp
    thus ?case by simp
  next
    case (Ctor x1a x2)
    thus ?case by simp
  qed
next
  case (Ctor e\<^sub>1 es\<^sub>1)
  thus ?case by simp
qed

lemma [simp]: "x \<notin> vars e \<Longrightarrow> s unifies Var x and e \<Longrightarrow> s unifies\<^sub>l ess \<Longrightarrow> 
  s unifies\<^sub>l list_subst x e ess"
proof (induction x e ess rule: list_subst.induct)
  case (2 x e' e\<^sub>1 e\<^sub>2 ess)
  hence  "s unifies Var x and e'" by simp
  moreover from 2 have "s unifies e\<^sub>1 and e\<^sub>2" by simp
  ultimately have "s unifies subst [x \<mapsto> e'] e\<^sub>1 and subst [x \<mapsto> e'] e\<^sub>2" by (metis unify_subst_one)
  with 2 show ?case by simp
qed simp_all

lemma [simp]: "s x = Some e' \<Longrightarrow> x \<in> vars e \<Longrightarrow> e \<noteq> Var x \<Longrightarrow> size e' < size (subst s e)"
  and [simp]: "s x = Some e' \<Longrightarrow> x \<in> varss es \<Longrightarrow> size e' < size_list (size \<circ> subst s) es"
proof (induction e and es rule: vars_varss.induct)
  case (4 e es)
  then show ?case by force
qed fastforce+

lemma occurs_check [simp]: "x \<in> vars e \<Longrightarrow> e \<noteq> Var x \<Longrightarrow> s x = Some (subst s e) \<Longrightarrow> False"
proof (induction "s x")
  case (Some e')
  from Some(1, 2, 3) have "size e' < size (subst s e)" by simp
  with Some show ?case by simp
qed simp_all


lemma [simp]: "x \<in> varss es \<Longrightarrow> s x \<noteq> Some (Ctor k (map (subst s) es))"
proof (rule)
  assume "x \<in> varss es"
  hence X: "x \<in> vars (Ctor k es)" by simp
  have Y: "Ctor k es \<noteq> Var x" by simp
  assume "s x = Some (Ctor k (map (subst s) es))"
  hence "s x = Some (subst s (Ctor k es))" by simp
  with X Y show False by (metis occurs_check)
qed

end