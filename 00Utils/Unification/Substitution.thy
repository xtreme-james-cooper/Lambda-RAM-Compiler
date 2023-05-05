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

definition subst_extends :: "subst \<Rightarrow> subst \<Rightarrow> bool" (infix "extends" 50) where
  "subst_extends s t = (\<exists>u. subst s = subst u \<circ> subst t)"

lemma [simp]: "subst Map.empty = id"
proof
  fix e
  show "subst Map.empty e = id e" by (induction e) (auto simp add: map_idI)
qed
  
lemma [simp]: "x \<notin> vars e \<Longrightarrow> subst [x \<mapsto> e'] e = e"
  and [simp]: "x \<notin> varss es \<Longrightarrow> map (subst [x \<mapsto> e']) es = es"
  by (induction e and es rule: vars_varss.induct) simp_all

lemma [simp]: "vars e \<subseteq> vs \<Longrightarrow> finite vs \<Longrightarrow> subst [fresh vs \<mapsto> e'] e = e"
proof -
  assume "finite vs"
  hence "fresh vs \<notin> vs" by simp
  moreover assume "vars e \<subseteq> vs" 
  ultimately have "fresh vs \<notin> vars e" by auto
  thus ?thesis by simp
qed

lemma [simp]: "x \<in> vars e \<Longrightarrow> vars (subst [x \<mapsto> e'] e) = vars e - {x} \<union> vars e'"
  and [simp]: "x \<in> varss es \<Longrightarrow> varss (map (subst [x \<mapsto> e']) es) = varss es - {x} \<union> vars e'"
proof (induction e and es rule: vars_varss.induct)
  case (4 e es)
  hence "varss (map (subst [x \<mapsto> e']) (e # es)) = varss (e # es) - {x} \<union> vars e'" by fastforce
  thus ?case by blast
qed simp_all

lemma [simp]: "vars (subst [x \<mapsto> e'] e) = vars e - {x} \<union> (if x \<in> vars e then vars e' else {})"
  by simp

lemma [simp]: "subst [x \<mapsto> e'] (subst [x \<mapsto> e''] e) = subst [x \<mapsto> subst [x \<mapsto> e'] e''] e"
  by (induction e) simp_all

lemma [dest]: "[] = list_subst x e ess \<Longrightarrow> ess = []"
  by (induction x e ess rule: list_subst.induct) simp_all

lemma [dest]: "(e\<^sub>1, e\<^sub>2) # ess' = list_subst x e' ess \<Longrightarrow> \<exists>ee\<^sub>1 ee\<^sub>2 eess. ess = (ee\<^sub>1, ee\<^sub>2) # eess \<and> 
    e\<^sub>1 = subst [x \<mapsto> e'] ee\<^sub>1 \<and> e\<^sub>2 = subst [x \<mapsto> e'] ee\<^sub>2 \<and> ess' = list_subst x e' eess"
  by (induction x e' ess rule: list_subst.induct) simp_all

lemma [simp]: "list_subst x e (es\<^sub>1 @ es\<^sub>2) = list_subst x e es\<^sub>1 @ list_subst x e es\<^sub>2"
  by (induction es\<^sub>1 rule: list_subst.induct) simp_all

lemma [simp]: "list_subst x e (zip es\<^sub>1 es\<^sub>2) = 
    zip (map (subst [x \<mapsto> e]) es\<^sub>1) (map (subst [x \<mapsto> e]) es\<^sub>2)"
proof (induction es\<^sub>1 arbitrary: es\<^sub>2)
  case (Cons e\<^sub>1 es\<^sub>1)
  thus ?case by (induction es\<^sub>2) simp_all
qed simp_all

lemma [simp]: "map prod.swap (list_subst x e ess) = list_subst x e (map prod.swap ess)"
  by (induction ess rule: list_subst.induct) simp_all

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

lemma [simp]: "list_subst x e' (list_subst x e ess) = list_subst x (subst [x \<mapsto> e'] e) ess"
proof (induction x e ess rule: list_subst.induct)
  case (2 x e e\<^sub>1 e\<^sub>2 ess)
  hence "list_subst x e' (list_subst x e ess) = list_subst x (subst [x \<mapsto> e'] e) ess" by blast
  hence "list_subst x e' (list_subst x e ((e\<^sub>1, e\<^sub>2) # ess)) = 
    list_subst x (subst [x \<mapsto> e'] e) ((e\<^sub>1, e\<^sub>2) # ess)" by simp
  thus ?case by blast
qed simp_all

lemma list_subst_no_var [simp]: "x \<notin> list_vars ess \<Longrightarrow> list_subst x e ess = ess"
  by (induction x e ess rule: list_subst.induct) simp_all

lemma subst_merge: "subst (extend_subst x e' s) e = subst s (subst [x \<mapsto> e'] e)"
  by (induction e) (simp_all add: extend_subst_def)

lemma vars_subst [simp]: "vars (subst s e) \<subseteq> vars e - dom s \<union> subst_vars s"
  and [simp]: "varss (map (subst s) es) \<subseteq> varss es - dom s \<union> subst_vars s"
  by (induction e and es rule: vars_varss.induct) 
     (auto simp add: subst_vars_def ranI split: option.splits)

lemma [simp]: "x \<in> vars e \<Longrightarrow> s x = None \<Longrightarrow> x \<in> vars (subst s e)"
  and [simp]: "x \<in> varss es \<Longrightarrow> s x = None \<Longrightarrow> x \<in> varss (map (subst s) es)"
  by (induction e and es rule: vars_varss.induct) auto

lemma [simp]: "subst_vars Map.empty = {}"
  by (simp add: subst_vars_def)

lemma [simp]: "subst_vars s \<subseteq> vs \<Longrightarrow> subst_vars (s(x := None)) \<subseteq> vs"
  by (auto simp add: subst_vars_def ran_def)

lemma [simp]: "s x = Some e \<Longrightarrow> subst_vars s \<subseteq> vs \<Longrightarrow> vars e \<subseteq> vs"
  by (auto simp add: subst_vars_def ran_def)

lemma [simp]: "s x = Some e \<Longrightarrow> y \<in> vars e \<Longrightarrow> y \<in> subst_vars s"
  by (auto simp add: subst_vars_def ran_def)

lemma [simp]: "dom (extend_subst x e s) = insert x (dom s)"
  by (auto simp add: extend_subst_def)

lemma [simp]: "ran (extend_subst x e s) = insert (subst s e) (ran (s(x := None)))"
  by (auto simp add: extend_subst_def ran_def)

lemma [simp]: "dom s \<inter> vars e = {} \<Longrightarrow> subst s e = e"
  and [simp]: "dom s \<inter> varss es = {} \<Longrightarrow> map (subst s) es = es"
  by (induction e and es rule: vars_varss.induct) (auto split: option.splits)

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

lemma [dest]: "subst [x \<mapsto> e'] e = Var y \<Longrightarrow> 
    (e = Var y \<and> (y = x \<longrightarrow> e' = Var y)) \<or> (y \<noteq> x \<and> e = Var x \<and> e' = Var y)"
  by (induction e) (auto split: if_splits)

lemma [dest]: "subst s e = Ctor k es \<Longrightarrow> (\<exists>x. e = Var x \<and> s x = Some (Ctor k es)) \<or> 
    (\<exists>es'. e = Ctor k es' \<and> map (subst s) es' = es)"
  by (induction e) (simp_all split: option.splits)

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
    subst (extend_subst x e' s) e = subst [x \<mapsto> subst s e'] (subst s e)"
  by (induction e) (auto simp add: extend_subst_def split: option.splits)

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

lemma [simp]: "\<exists>s. dom s \<inter> xs = {} \<and> subst_vars s = {} \<and> ordered_subst s"
proof 
  show "dom Map.empty \<inter> xs = {} \<and> subst_vars Map.empty = {} \<and> ordered_subst Map.empty" by simp
qed

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

lemma occurs_check2' [simp]: "x \<in> vars e \<Longrightarrow> e \<noteq> Var x \<Longrightarrow> 
    size (subst s e') < size (subst s (subst [x \<mapsto> e'] e))"
  and [simp]: "x \<in> varss es \<Longrightarrow> size (subst s e') < size_list (size \<circ> subst s \<circ> subst [x \<mapsto> e']) es"
proof (induction e and es rule: vars_varss.induct)
  case (2 k es)
  hence "size (subst s e') < size_list (size \<circ> subst s \<circ> subst [x \<mapsto> e']) es" by fastforce
  hence "size (subst s e') < size (subst s (subst [x \<mapsto> e'] (Ctor k es)))" 
    by (simp add: fun.map_comp)
  thus ?case by blast
next
  case (4 e es)
  thus ?case by force
qed simp_all

lemma occurs_check2 [simp]: "x \<in> vars e \<Longrightarrow> e \<noteq> Var x \<Longrightarrow> s unifies e' and subst [x \<mapsto> e'] e \<Longrightarrow> 
  False"
proof -
  assume "x \<in> vars e" and "e \<noteq> Var x" 
  hence "size (subst s e') < size (subst s (subst [x \<mapsto> e'] e))" by (metis occurs_check2')
  moreover assume "s unifies e' and subst [x \<mapsto> e'] e"
  ultimately show ?thesis by simp
qed

lemma [elim]: "y \<notin> varss (map (subst [x \<mapsto> Var y]) es) \<Longrightarrow> x \<notin> varss es"
  by (induction es) fastforce+

lemma [simp]: "x \<in> varss es \<Longrightarrow> s x \<noteq> Some (Ctor k (map (subst s) es))"
proof
  assume "x \<in> varss es"
  hence X: "x \<in> vars (Ctor k es)" by simp
  have Y: "Ctor k es \<noteq> Var x" by simp
  assume "s x = Some (Ctor k (map (subst s) es))"
  hence "s unifies Var x and Ctor k es" by simp
  with X Y show False by (metis occurs_check)
qed

lemma [simp]: "s unifies\<^sub>l list_subst x e ess = (extend_subst x e s unifies\<^sub>l ess)"
  by (induction s ess rule: list_unifier.induct) (simp_all add: subst_merge)

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
  by (induction e) (auto split: option.splits)

lemma [dest]: "Var x = subst s e \<Longrightarrow> 
    (e = Var x \<and> s x = None) \<or> (\<exists>y. e = Var y \<and> s y = Some (Var x))"
  by (induction e) (auto split: option.splits)

lemma [dest]: "subst s e = Ctor k es \<Longrightarrow> 
    (\<exists>es'. e = Ctor k es' \<and> es = map (subst s) es') \<or> (\<exists>x. e = Var x \<and> s x = Some (Ctor k es))"
  by (induction e) (auto split: option.splits)

lemma [dest]: "Ctor k es = subst s e \<Longrightarrow>
    (\<exists>es'. e = Ctor k es' \<and> es = map (subst s) es') \<or> (\<exists>x. e = Var x \<and> s x = Some (Ctor k es))"
  by (induction e) (auto split: option.splits)

lemma subst_subst_var [dest, consumes 1, case_names Eq FstOnly SndOnly Both]: 
  "(subst s \<circ> subst t) (Var x) = Var y \<Longrightarrow> (x = y \<Longrightarrow> P) \<Longrightarrow> 
    (s y = None \<Longrightarrow> t x = Some (Var y) \<Longrightarrow> P) \<Longrightarrow> (s x = Some (Var y) \<Longrightarrow> t x = None \<Longrightarrow> P) \<Longrightarrow> 
      (\<And>z. s z = Some (Var y) \<Longrightarrow> t x = Some (Var z) \<Longrightarrow> P) \<Longrightarrow> P"
  by (auto split: option.splits)

lemma [simp]: "s x = Some (subst s e) \<Longrightarrow> x \<notin> vars e \<Longrightarrow> extend_subst x e (s(x := None)) = s"
  by rule (simp add: extend_subst_def)

lemma [simp]: "subst_vars (s(x := None)) \<subseteq> subst_vars s"
  by (auto simp add: subst_vars_def) (metis ranI ran_restrictD restrict_complement_singleton_eq)

lemma [simp]: "subst_vars (s(x \<mapsto> e)) = (subst_vars (s(x := None)) \<union> vars e)"
  by (auto simp add: subst_vars_def ran_def)

lemma [simp]: "subst_vars (\<lambda>a. if a = x then Some e else s a) = 
    (subst_vars (s(x := None)) \<union> vars e)"
  by (auto simp add: subst_vars_def ran_def)

lemma [simp]: "y \<in> subst_vars (s(x := None)) \<Longrightarrow> y \<in> subst_vars s"
  by (auto simp add: subst_vars_def ran_def split: if_splits)

lemma [simp]: "y \<in> subst_vars (\<Gamma>(x := None)) = (\<exists>z e. z \<noteq> x \<and> \<Gamma> z = Some e \<and> y \<in> vars e)"
  by (auto simp add: subst_vars_def ran_def split: if_splits)

lemma [simp]: "subst_vars s \<subseteq> as \<Longrightarrow> subst_vars (s(x := None)) \<subseteq> as"
  by (auto simp add: subst_vars_def ran_def)

lemma [simp]: "subst_vars \<Gamma> \<subseteq> vs \<Longrightarrow> x \<notin> vs \<Longrightarrow> \<Gamma> z = Some e \<Longrightarrow> x \<in> vars e \<Longrightarrow> False"
  by (auto simp add: subst_vars_def ran_def)

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

lemma [simp]: "combine_subst Map.empty s = s"
  by rule (simp add: combine_subst_def split: option.splits)

lemma [simp]: "combine_subst s Map.empty = s"
  by rule (simp add: combine_subst_def split: option.splits)

lemma [simp]: "dom (combine_subst s t) = dom s \<union> dom t"
  by (auto simp add: dom_def combine_subst_def split: option.splits)

lemma [simp]: "dom s \<inter> dom t = {} \<Longrightarrow> 
  subst_vars (combine_subst s t) = subst_vars s \<union> (subst_vars t - dom s)"
proof 
  assume "dom s \<inter> dom t = {}"
  hence D: "\<And>y e. s y = Some e \<Longrightarrow> t y = None" by auto
  show "subst_vars (combine_subst s t) \<subseteq> subst_vars s \<union> (subst_vars t - dom s)" 
  proof
    fix x
    assume "x \<in> subst_vars (combine_subst s t)"
    then obtain e y where E: "(case t y of None \<Rightarrow> s y | Some e' \<Rightarrow> Some (subst s e')) = Some e \<and> 
      x \<in> vars e" by (auto simp add: subst_vars_def ran_def combine_subst_def)
    thus "x \<in> subst_vars s \<union> (subst_vars t - dom s)"
    proof (cases "t y")
      case (Some e')
      with E have "x \<in> vars (subst s e')" by simp
      hence "x \<in> vars e' - dom s \<union> subst_vars s" using vars_subst by blast
      with Some show ?thesis by (auto simp add: subst_vars_def ran_def dom_def)
    qed (auto simp add: subst_vars_def ran_def)
  qed
  show "subst_vars s \<union> (subst_vars t - dom s) \<subseteq> subst_vars (combine_subst s t)" 
  proof
    fix x
    assume X: "x \<in> subst_vars s \<union> (subst_vars t - dom s)"
    thus "x \<in> subst_vars (combine_subst s t)" 
    proof (cases "\<exists>e y. s y = Some e \<and> x \<in> vars e")
      case True
      then obtain e y where Y: "s y = Some e \<and> x \<in> vars e" by auto
      with D have "t y = None" by simp
      with Y have "(case t y of None \<Rightarrow> s y | Some e' \<Rightarrow> Some (subst s e')) = Some e \<and> 
        x \<in> vars e" by simp
      thus ?thesis by (auto simp add: subst_vars_def ran_def combine_subst_def)
    next
      case False
      with X obtain e y where "t y = Some e \<and> x \<in> vars e \<and> s x = None" 
        by (auto simp add: subst_vars_def ran_def dom_def)
      hence "(case t y of None \<Rightarrow> s y | Some e' \<Rightarrow> Some (subst s e')) = Some (subst s e) \<and> 
        x \<in> vars (subst s e)" by simp
      thus ?thesis by (auto simp add: subst_vars_def ran_def combine_subst_def)
    qed
  qed
qed

lemma [simp]: "dom s \<inter> dom t = {} \<Longrightarrow> dom t \<inter> subst_vars s = {} \<Longrightarrow> ordered_subst s \<Longrightarrow> 
    ordered_subst t \<Longrightarrow> ordered_subst (combine_subst s t)"
  by (auto simp add: ordered_subst_def)

lemma [simp]: "subst (combine_subst s t) e = subst s (subst t e)"
  by (induction e) (simp_all add: combine_subst_def split: option.splits)

lemma [simp]: "subst (combine_subst s t) = subst s \<circ> subst t"
  by auto

lemma [simp]: "combine_subst s (extend_subst x e t) y = extend_subst x e (combine_subst s t) y"
  by (simp add: combine_subst_def extend_subst_def)

lemma [simp]: "combine_subst s (extend_subst x e t) = extend_subst x e (combine_subst s t)"
  by auto

lemma extends_trans [elim]: "s extends t \<Longrightarrow> t extends u \<Longrightarrow> s extends u"
proof (unfold subst_extends_def)
  assume "\<exists>w. subst s = subst w \<circ> subst t"
  then obtain w where W: "subst s = subst w \<circ> subst t" by fastforce
  assume "\<exists>v. subst t = subst v \<circ> subst u" 
  then obtain v where V: "subst t = subst v \<circ> subst u" by fastforce
  have "subst w \<circ> (subst v \<circ> subst u) = subst (combine_subst w v) \<circ> subst u" by fastforce
  with W V show "\<exists>r. subst s = subst r \<circ> subst u" by metis
qed

lemma [simp]: "s extends Map.empty"
  by (auto simp add: subst_extends_def)

lemma [simp]: "s extends t \<Longrightarrow> extend_subst x e s extends extend_subst x e t"
proof (unfold subst_extends_def)
  assume "\<exists>u. subst s = subst u \<circ> subst t"
  then obtain u where U: "subst s = subst u \<circ> subst t" by blast
  moreover hence "subst (extend_subst x e s) = subst u \<circ> subst (extend_subst x e t)" 
    by (simp add: expand_extend_subst) auto
  ultimately show "\<exists>u. subst (extend_subst x e s) = subst u \<circ> subst (extend_subst x e t)" by auto
qed

lemma extends_refl [simp]: "s extends s"
proof (unfold subst_extends_def)
  have "subst s = subst Map.empty \<circ> subst s" by simp
  thus "\<exists>u. subst s = subst u \<circ> subst s" by blast
qed

lemma [simp]: "t extends u \<Longrightarrow> extend_subst x e u extends s \<Longrightarrow> extend_subst x e t extends s"
proof (unfold subst_extends_def)
  assume "\<exists>b. subst t = subst b \<circ> subst u"
  then obtain b where B: "subst t = subst b \<circ> subst u" by fastforce
  assume "\<exists>c. subst (extend_subst x e u) = subst c \<circ> subst s"
  then obtain c where "subst (extend_subst x e u) = subst c \<circ> subst s" by fastforce
  hence "subst u \<circ> subst [x \<mapsto> e] = subst c \<circ> subst s" by (metis expand_extend_subst)
  hence "subst b \<circ> subst u \<circ> subst [x \<mapsto> e] = subst (combine_subst b c) \<circ> subst s" 
    by (simp add: comp_assoc)
  with B show "\<exists>a. subst (extend_subst x e t) = subst a \<circ> subst s" by (metis expand_extend_subst)
qed

lemma [elim]: "s unifies e\<^sub>1 and e\<^sub>2 \<Longrightarrow> t extends s \<Longrightarrow> t unifies e\<^sub>1 and e\<^sub>2"
  by (auto simp add: subst_extends_def)

lemma [simp]: "xs \<inter> subst_vars s = {} \<Longrightarrow> s x = Some e \<Longrightarrow> xs \<inter> vars e = {}"
  by (auto simp add: subst_vars_def ran_def)

lemma [simp]: "dom s \<inter> dom t = {} \<Longrightarrow> dom t \<inter> subst_vars s = {} \<Longrightarrow> 
    subst s (subst t e) = subst (map_option (subst s) \<circ> t) (subst s e)"
proof (induction e)
  case (Var x)
  thus ?case
  proof (cases "t x")
    case None note N = None
    thus ?thesis
    proof (cases "s x")
      case (Some e)
      with Var have "dom t \<inter> vars e = {}" by simp
      with N Some have "subst s (subst t (Var x)) = 
        subst (map_option (subst s) \<circ> t) (subst s (Var x))" by simp
      thus ?thesis by blast
    qed simp_all
  next
    case (Some e)
    with Var have "s x = None" by auto
    with Some show ?thesis by simp
  qed
qed simp_all

lemma [simp]: "x \<notin> dom s \<Longrightarrow> x \<notin> subst_vars s \<Longrightarrow> s unifies\<^sub>l ess \<Longrightarrow> extend_subst x e s unifies\<^sub>l ess"
  by (induction s ess rule: list_unifier.induct) simp_all

lemma [simp]: "dom s \<inter> dom t = {} \<Longrightarrow> dom t \<inter> subst_vars s = {} \<Longrightarrow> s unifies\<^sub>l ess \<Longrightarrow> 
    combine_subst s t unifies\<^sub>l ess"
  by (induction s ess rule: list_unifier.induct) simp_all

lemma [simp]: "t unifies\<^sub>l ess \<Longrightarrow> combine_subst s t unifies\<^sub>l ess"
  by (induction t ess rule: list_unifier.induct) simp_all

lemma [elim]: "x \<notin> vars (subst s e) \<Longrightarrow> x \<notin> subst_vars s \<Longrightarrow> x \<notin> dom s \<Longrightarrow> x \<notin> vars e"
  and [elim]: "x \<notin> varss (map (subst s) es) \<Longrightarrow> x \<notin> subst_vars s \<Longrightarrow> x \<notin> dom s \<Longrightarrow> x \<notin> varss es"
  by (induction e and es rule: vars_varss.induct) (auto split: option.splits)

lemma vars_subst_inv [elim]: "vars (subst s e) \<subseteq> vs \<Longrightarrow> vars e \<subseteq> vs \<union> dom s"
  and [elim]: "varss (map (subst s) es) \<subseteq> vs \<Longrightarrow> varss es \<subseteq> vs \<union> dom s"
  by (induction e and es rule: vars_varss.induct) (auto split: option.splits)

end