theory Unification
  imports "../00Utils/Utils"
begin

datatype expr = 
  Var string
  | Ctor string "expr list"

type_synonym subst = "string \<rightharpoonup> expr"

primrec subst :: "subst \<Rightarrow> expr \<Rightarrow> expr" where
  "subst s (Var x) = (case s x of Some e \<Rightarrow> e | None \<Rightarrow> Var x)"
| "subst s (Ctor k es) = Ctor k (map (subst s) es)"

definition extend_subst :: "string \<Rightarrow> expr \<Rightarrow> subst \<Rightarrow> subst" where
  "extend_subst x e s y = (if x = y then Some e else map_option (subst [x \<mapsto> e]) (s y))"

definition extension :: "subst \<Rightarrow> subst \<Rightarrow> bool" (infix "extends" 50) where
  "s' extends s = (\<exists>xes. s' = fold (\<lambda>(x, e). extend_subst x e) xes s)"

fun vars :: "expr \<Rightarrow> string set" 
and varss :: "expr list \<Rightarrow> string set" where
  "vars (Var x) = {x}"
| "vars (Ctor k es) = varss es"
| "varss [] = {}"
| "varss (e # es) = vars e \<union> varss es"

primrec ctors :: "expr \<Rightarrow> nat" where
  "ctors (Var x) = 0"
| "ctors (Ctor k es) = Suc (list_sum (map ctors es))"

fun list_subst :: "string \<Rightarrow> expr \<Rightarrow> (expr \<times> expr) list \<Rightarrow> (expr \<times> expr) list" where
  "list_subst x e' [] = []"
| "list_subst x e' ((e\<^sub>1, e\<^sub>2) # ess) = (subst [x \<mapsto> e'] e\<^sub>1, subst [x \<mapsto> e'] e\<^sub>2) # list_subst x e' ess"

fun list_vars :: "(expr \<times> expr) list \<Rightarrow> string set" where
  "list_vars [] = {}"
| "list_vars ((e\<^sub>1, e\<^sub>2) # ess) = vars e\<^sub>1 \<union> vars e\<^sub>2 \<union> list_vars ess"

fun list_ctors :: "(expr \<times> expr) list \<Rightarrow> nat" where
  "list_ctors [] = 0"
| "list_ctors ((e\<^sub>1, e\<^sub>2) # ess) = ctors e\<^sub>1 + ctors e\<^sub>2 + list_ctors ess"

abbreviation unifier :: "subst \<Rightarrow> expr \<Rightarrow> expr \<Rightarrow> bool" (infix "unifies _ and" 50) where 
  "unifier s e\<^sub>1 e\<^sub>2 \<equiv> subst s e\<^sub>1 = subst s e\<^sub>2"

fun list_unifier :: "subst \<Rightarrow> (expr \<times> expr) list \<Rightarrow> bool" (infix "unifies\<^sub>l" 50) where 
  "list_unifier s [] = True"
| "list_unifier s ((e\<^sub>1, e\<^sub>2) # ess) = ((s unifies e\<^sub>1 and e\<^sub>2) \<and> list_unifier s ess)"

function unify' :: "(expr \<times> expr) list \<Rightarrow> subst \<rightharpoonup> subst" where
  "unify' [] s = Some s"
| "unify' ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess) s = (
    if k\<^sub>1 = k\<^sub>2 \<and> length es\<^sub>1 = length es\<^sub>2 then unify' (zip es\<^sub>1 es\<^sub>2 @ ess) s 
    else None)"
| "unify' ((Ctor k es, Var x) # ess) s = (
    if x \<in> varss es then None
    else unify' (list_subst x (Ctor k es) ess) (extend_subst x (Ctor k es) s))"
| "unify' ((Var x, Ctor k es) # ess) s = (
    if x \<in> varss es then None
    else unify' (list_subst x (Ctor k es) ess) (extend_subst x (Ctor k es) s))"
| "unify' ((Var x, Var y) # ess) s = unify' (list_subst x (Var y) ess) (extend_subst x (Var y) s)"
  by pat_completeness auto

definition unify :: "expr \<Rightarrow> expr \<rightharpoonup> subst" where
  "unify e\<^sub>1 e\<^sub>2 = unify' [(e\<^sub>1, e\<^sub>2)] Map.empty"

lemma [simp]: "finite (vars e)"
  and [simp]: "finite (varss es)"
  by (induction e and es rule: vars_varss.induct) simp_all

lemma [simp]: "finite (list_vars ess)"
  by (induction ess rule: list_vars.induct) simp_all

lemma [simp]: "list_vars (ess\<^sub>1 @ ess\<^sub>2) = list_vars ess\<^sub>1 \<union> list_vars ess\<^sub>2"
  by (induction ess\<^sub>1 rule: list_ctors.induct) auto

lemma [simp]: "length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> list_vars (zip es\<^sub>1 es\<^sub>2) = varss es\<^sub>1 \<union> varss es\<^sub>2"
proof (induction es\<^sub>1 arbitrary: es\<^sub>2)
  case (Cons e\<^sub>1 es\<^sub>1)
  thus ?case by (induction es\<^sub>2) auto
qed simp_all

lemma [simp]: "list_ctors (ess\<^sub>1 @ ess\<^sub>2) = list_ctors ess\<^sub>1 + list_ctors ess\<^sub>2"
  by (induction ess\<^sub>1 rule: list_ctors.induct) simp_all

lemma [simp]: "length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> 
  list_ctors (zip es\<^sub>1 es\<^sub>2) = list_sum (map ctors es\<^sub>1) + list_sum (map ctors es\<^sub>2)"
proof (induction es\<^sub>1 arbitrary: es\<^sub>2)
  case (Cons e\<^sub>1 es\<^sub>1)
  thus ?case by (induction es\<^sub>2) simp_all
qed simp_all

lemma [simp]: "subst [x \<mapsto> Var x] e = e"
proof (induction e)
  case (Ctor k es)
  thus ?case by (induction es) simp_all
qed simp_all

lemma [simp]: "list_subst x (Var x) ess = ess"
  by (induction x "Var x" ess rule: list_subst.induct) simp_all

lemma [simp]: "x \<notin> vars e \<Longrightarrow> vars (subst [x \<mapsto> e'] e) = vars e"
  and [simp]: "x \<notin> varss es \<Longrightarrow> varss (map (subst [x \<mapsto> e']) es) = varss es"
  by (induction e and es rule: vars_varss.induct) simp_all

lemma [simp]: "x \<in> vars e \<Longrightarrow> vars (subst [x \<mapsto> e'] e) = vars e - {x} \<union> vars e'"
  and [simp]: "x \<in> varss es \<Longrightarrow> varss (map (subst [x \<mapsto> e']) es) = varss es - {x} \<union> vars e'"
proof (induction e and es rule: vars_varss.induct)
  case (4 e es)
  hence "varss (map (subst [x \<mapsto> e']) (e # es)) = varss (e # es) - {x} \<union> vars e'" 
    by fastforce
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

lemma [simp]: "length (list_subst x e ess) = length ess"
  by (induction x e ess rule: list_subst.induct) simp_all

lemma [simp]: "ctors (subst [x \<mapsto> Var y] e) = ctors e"
proof (induction e)
  case (Ctor k es)
  thus ?case by (induction es) simp_all
qed simp_all

lemma [simp]: "list_ctors (list_subst x (Var y) ess) = list_ctors ess"
  by (induction x "Var y" ess rule: list_subst.induct) simp_all

termination unify'
  by (relation "measures [card \<circ> list_vars \<circ> fst, list_ctors \<circ> fst, length \<circ> fst]") 
     (simp_all add: card_insert_if)

lemma [simp]: "s unifies\<^sub>l (as @ bs) = ((s unifies\<^sub>l as) \<and> (s unifies\<^sub>l bs))"
  by (induction s as rule: list_unifier.induct) simp_all

lemma [simp]: "length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> 
    (s unifies\<^sub>l zip es\<^sub>1 es\<^sub>2) = (map (subst s) es\<^sub>1 = map (subst s) es\<^sub>2)"
proof (induction es\<^sub>1 arbitrary: es\<^sub>2)
  case (Cons e es\<^sub>1)
  thus ?case by (induction es\<^sub>2) simp_all
qed simp_all

lemma unify_none [simp]: "unify' ess s = None \<Longrightarrow> \<nexists>s'. s' extends s \<and> s' unifies\<^sub>l ess"
proof (induction ess s rule: unify'.induct)
  case (2 k\<^sub>1 es\<^sub>1 k\<^sub>2 es\<^sub>2 ess s)
  thus ?case by (cases "k\<^sub>1 = k\<^sub>2 \<and> length es\<^sub>1 = length es\<^sub>2") simp_all
next
  case (3 k es x ess s)
  thus ?case by simp
next
  case (4 x k es ess s)
  thus ?case by simp
next
  case (5 x y ess s)
  from 5 have "\<nexists>s'. s' unifies\<^sub>l list_subst x (Var y) ess" by simp
  from 5 have "unify' (list_subst x (Var y) ess) (extend_subst x (Var y) s) = None" by simp


  have "\<forall>s'. (case s' x of None \<Rightarrow> Var x | Some e \<Rightarrow> e) = (case s' y of None \<Rightarrow> Var y | Some e \<Rightarrow> e) \<longrightarrow> \<not> s' unifies\<^sub>l ess" by simp
  thus ?case by simp
qed simp_all

lemma [simp]: "s extends Map.empty"
  by (unfold extension_def)

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = None \<Longrightarrow> \<nexists>s. s unifies e\<^sub>1 and e\<^sub>2"
proof (unfold unify_def)
  assume "unify' [(e\<^sub>1, e\<^sub>2)] Map.empty = None"
  hence "\<nexists>s'. s' extends Map.empty \<and> s' unifies\<^sub>l [(e\<^sub>1, e\<^sub>2)]" by (metis unify_none)
  thus "\<nexists>s. s unifies e\<^sub>1 and e\<^sub>2" by simp
qed

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = Some s \<Longrightarrow> (s unifies e\<^sub>1 and e\<^sub>2)"
  by simp

end