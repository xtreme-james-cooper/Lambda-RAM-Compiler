theory Unification
  imports Main
begin

primrec list_sum :: "nat list \<Rightarrow> nat" where
  "list_sum [] = 0"
| "list_sum (n # ns) = n + list_sum ns"

lemma [simp]: "length as \<noteq> length bs \<Longrightarrow> map f as \<noteq> map f bs"
proof (induction as arbitrary: bs)
  case Nil
  thus ?case by (induction bs) simp_all
next
  case (Cons a as)
  thus ?case by (induction bs) simp_all
qed


datatype expr = 
  Var string
  | Ctor string "expr list"

type_synonym subst = "string \<rightharpoonup> expr"

primrec subst :: "subst \<Rightarrow> expr \<Rightarrow> expr" where
  "subst s (Var x) = (case s x of Some e \<Rightarrow> e | None \<Rightarrow> Var x)"
| "subst s (Ctor k es) = Ctor k (map (subst s) es)"

definition extend_subst :: "string \<Rightarrow> expr \<Rightarrow> subst \<Rightarrow> subst" where
  "extend_subst x e s y = (if x = y then Some e else map_option (subst [x \<mapsto> e]) (s y))"

primrec vars :: "expr \<Rightarrow> string set" where
  "vars (Var x) = {x}"
| "vars (Ctor k es) = \<Union> (set (map vars es))"

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

function unify' :: "nat \<Rightarrow> (expr \<times> expr) list \<Rightarrow> subst \<rightharpoonup> subst" where
  "unify' n [] s = Some s"
| "unify' n ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess) s = (
    if k\<^sub>1 = k\<^sub>2 \<and> length es\<^sub>1 = length es\<^sub>2 then unify' n (zip es\<^sub>1 es\<^sub>2 @ ess) s 
    else None)"
| "unify' 0 ((Ctor k es, Var x) # ess) s = undefined"
| "unify' (Suc n) ((Ctor k es, Var x) # ess) s = (
    if x \<in> \<Union> (set (map vars es)) then None
    else unify' n (list_subst x (Ctor k es) ess) (extend_subst x (Ctor k es) s))"
| "unify' 0 ((Var x, Ctor k es) # ess) s = undefined"
| "unify' (Suc n) ((Var x, Ctor k es) # ess) s = (
    if x \<in> \<Union> (set (map vars es)) then None
    else unify' n (list_subst x (Ctor k es) ess) (extend_subst x (Ctor k es) s))"
| "unify' 0 ((Var x, Var y) # ess) s = (
    if x = y \<and> x \<notin> list_vars ess then unify' 0 ess s
    else undefined)"
| "unify' (Suc n) ((Var x, Var y) # ess) s = (
    if x = y then unify' (if x \<in> list_vars ess then Suc n else n) ess s
    else unify' n (list_subst x (Var y) ess) (extend_subst x (Var y) s))"
  by pat_completeness auto

definition unify :: "expr \<Rightarrow> expr \<rightharpoonup> subst" where
  "unify e\<^sub>1 e\<^sub>2 = unify' (card (vars e\<^sub>1 \<union> vars e\<^sub>2)) [(e\<^sub>1, e\<^sub>2)] (\<lambda>x. None)"

lemma [simp]: "finite (vars e)"
  by (induction e) simp_all

lemma [simp]: "finite (list_vars ess)"
  by (induction ess rule: list_vars.induct) simp_all

lemma [simp]: "list_vars (ess\<^sub>1 @ ess\<^sub>2) = list_vars ess\<^sub>1 \<union> list_vars ess\<^sub>2"
  by (induction ess\<^sub>1 rule: list_ctors.induct) auto

lemma [simp]: "length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> 
  list_vars (zip es\<^sub>1 es\<^sub>2) = \<Union> (vars ` set es\<^sub>1) \<union> \<Union> (vars ` set es\<^sub>2)"
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

termination unify'
  by (relation "measures [fst, list_ctors \<circ> fst \<circ> snd, length \<circ> fst \<circ> snd]") simp_all

lemma [simp]: "s unifies\<^sub>l (as @ bs) = ((s unifies\<^sub>l as) \<and> (s unifies\<^sub>l bs))"
  by (induction s as rule: list_unifier.induct) simp_all

lemma [simp]: "length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> 
    (s unifies\<^sub>l zip es\<^sub>1 es\<^sub>2) = (map (subst s) es\<^sub>1 = map (subst s) es\<^sub>2)"
proof (induction es\<^sub>1 arbitrary: es\<^sub>2)
  case (Cons e es\<^sub>1)
  thus ?case by (induction es\<^sub>2) simp_all
qed simp_all

lemma [simp]: "x \<notin> vars e \<Longrightarrow> vars (subst [x \<mapsto> e'] e) = vars e"
  by (induction e) simp_all

lemma [simp]: "x \<in> vars e \<Longrightarrow> vars (subst [x \<mapsto> e'] e) = vars e - {x} \<union> vars e'"
proof (induction e)
  case (Ctor k es)
  from Ctor have "xx2a \<in> set es \<Longrightarrow> x \<in> vars xx2a \<Longrightarrow> vars (subst [x \<mapsto> e'] xx2a) = vars xx2a - {x} \<union> vars e'" by simp
  from Ctor have "x \<in> \<Union> (set (map vars es))" by simp



  have "(\<Union>xa\<in>set es. vars (subst [x \<mapsto> e'] xa)) = \<Union> (vars ` set es) - {x} \<union> vars e'" by simp
  hence "vars (subst [x \<mapsto> e'] (Ctor k es)) = vars (Ctor k es) - {x} \<union> vars e'" by simp
  thus ?case by blast
qed simp_all

lemma [simp]: "x \<in> list_vars ess \<Longrightarrow> list_vars (list_subst x e ess) = list_vars ess - {x} \<union> vars e"
proof (induction ess rule: list_vars.induct)
  case (2 e\<^sub>1 e\<^sub>2 ess)

  thus ?case by simp
qed simp_all

lemma [simp]: "x \<notin> list_vars ess \<Longrightarrow> list_vars (list_subst x e ess) = list_vars ess"
  by (induction ess rule: list_vars.induct) simp_all

lemma unify_none [simp]: "unify' (card (list_vars ess)) ess s = None \<Longrightarrow> \<nexists>s'. s' unifies\<^sub>l ess"
proof (induction "card (list_vars ess)" ess s rule: unify'.induct)
  case (2 k\<^sub>1 es\<^sub>1 k\<^sub>2 es\<^sub>2 ess s)
  thus ?case by (cases "k\<^sub>1 = k\<^sub>2 \<and> length es\<^sub>1 = length es\<^sub>2") simp_all
next
  case (4 k es x ess s)
  thus ?case by simp
next
  case (6 n x k es ess s)
  thus ?case by simp
next
  case (8 n x y ess s)
  thus ?case
  proof (cases "x = y")
    case True note T = True
    with 8 show ?thesis 
    proof (cases "x \<in> list_vars ess")
      case True
      from 8 T have X: "card (insert x (list_vars ess)) = Suc n" by simp
      with 8 T True have "unify' (Suc n) ess s = None" by fastforce
      with 8 T True X show ?thesis by (simp add: insert_absorb)
    qed simp_all
  next
    case False
    from 8 False have "n = card (list_vars (list_subst [x \<mapsto> Var y] ess)) \<Longrightarrow>
      unify' (card (list_vars (list_subst [x \<mapsto> Var y] ess))) (list_subst [x \<mapsto> Var y] ess) (extend_subst x (Var y) s) =
      None \<Longrightarrow>
      \<nexists>s'. s' unifies\<^sub>l list_subst [x \<mapsto> Var y] ess" by simp
    from 8 have "card (insert y (insert x (list_vars ess))) = Suc n" by simp
    with 8 False have "unify' n (list_subst [x \<mapsto> Var y] ess) (extend_subst x (Var y) s) = None" by simp



    have "\<And>s'. (case s' x of None \<Rightarrow> Var x | Some e \<Rightarrow> e) = (case s' y of None \<Rightarrow> Var y | Some e \<Rightarrow> e)
       \<Longrightarrow> \<not> s' unifies\<^sub>l ess" by simp
    thus ?thesis by simp
  qed
qed simp_all

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = None \<Longrightarrow> \<nexists>s. s unifies e\<^sub>1 and e\<^sub>2"
proof (unfold unify_def)
  assume "unify' (card (vars e\<^sub>1 \<union> vars e\<^sub>2)) [(e\<^sub>1, e\<^sub>2)] (\<lambda>x. None) = None"
  hence "unify' (card (list_vars [(e\<^sub>1, e\<^sub>2)])) [(e\<^sub>1, e\<^sub>2)] (\<lambda>x. None) = None" by simp
  hence "\<nexists>s'. s' unifies\<^sub>l [(e\<^sub>1, e\<^sub>2)]" by (metis unify_none)
  thus "\<nexists>s. s unifies e\<^sub>1 and e\<^sub>2" by simp
qed

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = Some s \<Longrightarrow> (s unifies e\<^sub>1 and e\<^sub>2)"
  by simp

end