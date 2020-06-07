theory Unification
  imports Substitution
begin

fun unify_induct :: "(expr \<times> expr) list \<Rightarrow> bool" where
  "unify_induct [] = True"
| "unify_induct ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess) = unify_induct ess"
| "unify_induct ((Ctor k es, Var x) # ess) = unify_induct ess"
| "unify_induct ((Var x, Ctor k es) # ess) = unify_induct ess"
| "unify_induct ((Var x, Var y) # ess) = unify_induct ess"

function unify' :: "(expr \<times> expr) list \<Rightarrow> subst \<rightharpoonup> subst" where
  "unify' [] s = Some s"
| "k\<^sub>1 = k\<^sub>2 \<Longrightarrow> length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> unify' ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess) s = 
    unify' (zip es\<^sub>1 es\<^sub>2 @ ess) s"
| "k\<^sub>1 \<noteq> k\<^sub>2 \<or> length es\<^sub>1 \<noteq> length es\<^sub>2 \<Longrightarrow> unify' ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess) s = None"
| "x \<in> varss es \<Longrightarrow> unify' ((Ctor k es, Var x) # ess) s = None"
| "x \<notin> varss es \<Longrightarrow> unify' ((Ctor k es, Var x) # ess) s = 
    unify' (list_subst x (Ctor k es) ess) (extend_subst x (Ctor k es) s)"
| "x \<in> varss es \<Longrightarrow> unify' ((Var x, Ctor k es) # ess) s = None"
| "x \<notin> varss es \<Longrightarrow> unify' ((Var x, Ctor k es) # ess) s = 
    unify' (list_subst x (Ctor k es) ess) (extend_subst x (Ctor k es) s)"
| "x = y \<Longrightarrow> unify' ((Var x, Var y) # ess) s = unify' ess s"
| "x \<noteq> y \<Longrightarrow> unify' ((Var x, Var y) # ess) s = 
    unify' (list_subst x (Var y) ess) (extend_subst x (Var y) s)"
proof -
  fix P 
  fix x :: "(expr \<times> expr) list \<times> subst"
  assume A: "(\<And>s. x = ([], s) \<Longrightarrow> P)" and 
    B: "(\<And>k\<^sub>1 k\<^sub>2 es\<^sub>1 es\<^sub>2 ess s. k\<^sub>1 = k\<^sub>2 \<Longrightarrow> length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> 
      x = ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess, s) \<Longrightarrow> P)" and 
    C: "(\<And>k\<^sub>1 k\<^sub>2 es\<^sub>1 es\<^sub>2 ess s. k\<^sub>1 \<noteq> k\<^sub>2 \<or> length es\<^sub>1 \<noteq> length es\<^sub>2 \<Longrightarrow> 
      x = ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess, s) \<Longrightarrow> P)" and
    D: "(\<And>xa es k ess s. xa \<in> varss es \<Longrightarrow> x = ((Ctor k es, Var xa) # ess, s) \<Longrightarrow> P)" and
    E: "(\<And>xa es k ess s. xa \<notin> varss es \<Longrightarrow> x = ((Ctor k es, Var xa) # ess, s) \<Longrightarrow> P)" and
    F: "(\<And>xa es k ess s. xa \<in> varss es \<Longrightarrow> x = ((Var xa, Ctor k es) # ess, s) \<Longrightarrow> P)" and
    G: "(\<And>xa es k ess s. xa \<notin> varss es \<Longrightarrow> x = ((Var xa, Ctor k es) # ess, s) \<Longrightarrow> P)" and
    H: "(\<And>xa y ess s. xa = y \<Longrightarrow> x = ((Var xa, Var y) # ess, s) \<Longrightarrow> P)" and
    I: "(\<And>xa y ess s. xa \<noteq> y \<Longrightarrow> x = ((Var xa, Var y) # ess, s) \<Longrightarrow> P)"
  show P
  proof (cases x)
    case (Pair ess s)
    with A B C D E F G H I show ?thesis 
    proof (induction ess rule: unify_induct.induct)
      case (2 k\<^sub>1 es\<^sub>1 k\<^sub>2 es\<^sub>2 ess)
      thus ?case by (cases "k\<^sub>1 = k\<^sub>2 \<and> length es\<^sub>1 = length es\<^sub>2") auto
    next
      case (3 k es x ess)
      thus ?case by (cases "x \<in> varss es") simp_all
    next
      case (4 x k es ess)
      thus ?case by (cases "x \<in> varss es") simp_all
    next
      case (5 x y ess)
      thus ?case by (cases "x = y") simp_all
    qed simp_all
  qed
qed auto
termination
  by (relation "measures [card \<circ> list_vars \<circ> fst, list_ctor_count \<circ> fst, length \<circ> fst]") 
     (simp_all add: card_insert_if)

definition unify :: "expr \<Rightarrow> expr \<rightharpoonup> subst" where
  "unify e\<^sub>1 e\<^sub>2 = unify' [(e\<^sub>1, e\<^sub>2)] Map.empty"

lemma unify_ordered [simp]: "ordered_subst s \<Longrightarrow> dom s \<inter> list_vars ess = {} \<Longrightarrow> 
    unify' ess s = Some s' \<Longrightarrow> ordered_subst s'"
proof (induction ess s rule: unify'.induct)
  case (5 x es k ess s)
  moreover hence "vars (Ctor k es) \<inter> dom s = {}" by auto
  moreover from 5 have "dom (extend_subst x (Ctor k es) s) \<inter> 
    list_vars (list_subst x (Ctor k es) ess) = {}" by auto
  ultimately show ?case by simp
next
  case (7 x es k ess s)
  moreover hence "vars (Ctor k es) \<inter> dom s = {}" by auto
  moreover from 7 have "dom (extend_subst x (Ctor k es) s) \<inter> 
    list_vars (list_subst x (Ctor k es) ess) = {}" by auto
  ultimately show ?case by simp
next
  case (9 x y ess s)
  moreover hence "dom (extend_subst x (Var y) s) \<inter> list_vars (list_subst x (Var y) ess) = {}"
    by auto
  ultimately show ?case by simp
qed simp_all

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = Some s \<Longrightarrow> ordered_subst s"
proof (unfold unify_def)
  assume "unify' [(e\<^sub>1, e\<^sub>2)] Map.empty = Some s"
  moreover have "ordered_subst Map.empty" by simp
  moreover have "dom Map.empty \<inter> list_vars [(e\<^sub>1, e\<^sub>2)] = {}" by simp
  ultimately show "ordered_subst s" by (metis unify_ordered)
qed

lemma unify_none [simp]: "unify' ess s = None \<Longrightarrow> \<nexists>s'. s' unifies\<^sub>l ess"
proof (induction ess s rule: unify'.induct)
  case (5 x es k ess s)
  hence "x \<notin> varss es" by simp
  hence "\<And>s'. s' unifies Ctor k es and Var x \<Longrightarrow> s' unifies\<^sub>l ess \<Longrightarrow> 
    s' unifies\<^sub>l list_subst x (Ctor k es) ess" by simp
  moreover from 5 have "\<nexists>s'. s' unifies\<^sub>l list_subst x (Ctor k es) ess" by simp
  ultimately show ?case by auto
next
  case (7 x es k ess s)
  hence "x \<notin> varss es" by simp
  hence "\<And>s'. s' unifies Var x and Ctor k es \<Longrightarrow> s' unifies\<^sub>l ess \<Longrightarrow> 
    s' unifies\<^sub>l list_subst x (Ctor k es) ess" by simp
  moreover from 7 have "\<nexists>s'. s' unifies\<^sub>l list_subst x (Ctor k es) ess" by simp
  ultimately show ?case by auto
next
  case (9 x y ess s)
  hence "x \<noteq> y" by simp
  hence "\<And>s'. s' unifies Var x and Var y \<Longrightarrow> s' unifies\<^sub>l ess \<Longrightarrow> 
    s' unifies\<^sub>l list_subst x (Var y) ess" by simp
  moreover from 9 have "\<nexists>s'. s' unifies\<^sub>l list_subst x (Var y) ess" by simp
  ultimately show ?case by auto
qed (simp_all split: option.splits)

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = None \<Longrightarrow> \<nexists>s. s unifies e\<^sub>1 and e\<^sub>2"
proof (unfold unify_def)
  assume "unify' [(e\<^sub>1, e\<^sub>2)] Map.empty = None"
  hence "\<nexists>s'. s' unifies\<^sub>l [(e\<^sub>1, e\<^sub>2)]" by (metis unify_none)
  thus "\<nexists>s. s unifies e\<^sub>1 and e\<^sub>2" by simp
qed
 
lemma unify_some [simp]: "ordered_subst s \<Longrightarrow> list_vars ess \<inter> dom s = {} \<Longrightarrow> 
  unify' ess s = Some s' \<Longrightarrow> s' unifies\<^sub>l ess"
proof (induction ess s rule: unify'.induct)
  case (5 x es k ess s)
  from 5 have "x \<notin> varss es" by simp
  from 5 have "ordered_subst s" by simp
  from 5 have "x \<notin> dom s" by simp
  from 5 have E: "varss es \<inter> dom s = {}" by auto
  from 5 have F: "dom s \<inter> list_vars ess = {}" by auto
  from 5 have "unify' (list_subst x (Ctor k es) ess) (extend_subst x (Ctor k es) s) = Some s'" by simp



  from 5 E F have "dom (extend_subst x (Ctor k es) s) \<inter> list_vars (list_subst x (Ctor k es) ess) = 
    {}" by auto
  with 5 E have "s' unifies\<^sub>l list_subst x (Ctor k es) ess" by auto



  have "s' x = Some (Ctor k (map (subst s') es)) \<and> s' unifies\<^sub>l ess" by simp
  thus ?case by simp
next
  case (7 x es k ess s)
  thus ?case by simp
next
  case (9 x y ess s)
  thus ?case by simp
qed simp_all

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = Some s \<Longrightarrow> s unifies e\<^sub>1 and e\<^sub>2"
proof (unfold unify_def)
  assume "unify' [(e\<^sub>1, e\<^sub>2)] Map.empty = Some s"
  moreover have "ordered_subst Map.empty" by simp
  moreover have "dom Map.empty \<inter> list_vars [(e\<^sub>1, e\<^sub>2)] = {}" by simp
  ultimately have "s unifies\<^sub>l [(e\<^sub>1, e\<^sub>2)]" by (metis unify_some)
  thus "s unifies e\<^sub>1 and e\<^sub>2" by simp
qed

end