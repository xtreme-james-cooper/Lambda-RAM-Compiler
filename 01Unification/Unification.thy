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
  case (2 k\<^sub>1 k\<^sub>2 es\<^sub>1 es\<^sub>2 ess s)
  then show ?case by simp
next
  case (4 x es k ess s)
  then show ?case by simp
next
  case (5 x es k ess s)
  then show ?case by simp
next
  case (6 x es k ess s)
  then show ?case by simp
next
  case (7 x es k ess s)
  then show ?case by simp
next
  case (9 x y ess s)
  from 9 have "x \<noteq> y" by simp
  from 9 have "\<And>s'. \<not> s' unifies\<^sub>l list_subst x (Var y) ess" by simp
  from 9 have "unify' (list_subst x (Var y) ess) (extend_subst x (Var y) s) = None" by simp


  have "\<And>s'. (\<not> s' unifies Var x and Var y) \<or> \<not> s' unifies\<^sub>l ess" by simp
  then show ?case by simp
qed simp_all

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = None \<Longrightarrow> \<nexists>s. s unifies e\<^sub>1 and e\<^sub>2"
proof (unfold unify_def)
  assume "unify' [(e\<^sub>1, e\<^sub>2)] Map.empty = None"
  hence "\<nexists>s'. s' unifies\<^sub>l [(e\<^sub>1, e\<^sub>2)]" by (metis unify_none)
  thus "\<nexists>s. s unifies e\<^sub>1 and e\<^sub>2" by simp
qed

lemma unify_some [simp]: "ordered_subst s \<Longrightarrow> sdom s \<inter> list_vars ess = {} \<Longrightarrow> 
  unify' ess s = Some s' \<Longrightarrow> s' unifies\<^sub>l ess"
proof (induction ess s rule: unify'.induct)
  case (2 k\<^sub>1 k\<^sub>2 es\<^sub>1 es\<^sub>2 ess s)
  then show ?case by simp
next
  case (5 x es k ess s)
  then show ?case by simp
next
  case (7 x es k ess s)
  then show ?case by simp
next
  case (9 x y ess s)
  hence "unify' (list_subst x (Var y) ess) ((x, Var y) # s) = Some s'" by simp
  then obtain s'' where S: "s' = s'' @ (x, Var y) # s" by fastforce

  with 9 have O: "ordered_subst s'" by (metis unify_ordered)

  from 9 have "sdom s \<inter> list_vars (list_subst x (Var y) ess) = {}" by auto
  with 9 have "s' unifies\<^sub>l list_subst x (Var y) ess" by simp


  from 9 have "x \<noteq> y" by simp
  from 9 have "ordered_subst s" by simp
  from 9 have "x \<notin> sdom s" by simp
  from 9 have "y \<notin> sdom s" by simp
  from 9 have "sdom s \<inter> list_vars ess = {}" by simp


  have "s' unifies\<^sub>l ess" by simp
  with S O show ?case by simp
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