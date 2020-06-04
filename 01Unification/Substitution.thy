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

end