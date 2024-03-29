theory SourceLanguage
  imports "../00Utils/Variable" "../00Utils/Utils"
begin

section \<open>Source Language\<close>

text \<open>We now define our source language. It consists of the untyped lambda calculus, enhanced with 
let-expressions and uninterpreted numbers. There are two main challenges with implementing the 
untyped lambda calculus: the non-termination of evaluation, and capture-avoiding substitution. We 
cannot address the first here, since our language as it stands does in fact admit unnormalizable 
terms like \<open>App\<^sub>s (Lam\<^sub>s x (App\<^sub>s (Var\<^sub>s x) (Var\<^sub>s x))) (Lam\<^sub>s x (App\<^sub>s (Var\<^sub>s x) (Var\<^sub>s x)))\<close>; after 
typechecking, we will lower our sights to the simply-typed subset of our language and be able to 
prove normalization then. As for substitution, for now we take the brute-force approach of renaming 
every binder to a fresh variable every time we substitute past it. We will shortly switch to a 
nameless Debruijn-index representation to make substitution simpler, but we want to keep our source 
language as close to an intuitive, "human-readable" version as possible. After all, changing this 
sort of behaviour to one more easily implemented on a computer is the essence of compilation.\<close>

text \<open>Our concrete datatype is parameterized on an annotation on each lambda binder; this will 
enable us to reuse the same datatype for the typed version.\<close>

(* TODO: products and sums *)

datatype 'a expr\<^sub>s = 
  Var\<^sub>s var
  | Const\<^sub>s nat
  | Lam\<^sub>s var 'a "'a expr\<^sub>s"
  | App\<^sub>s "'a expr\<^sub>s" "'a expr\<^sub>s"
  | Let\<^sub>s var "'a expr\<^sub>s" "'a expr\<^sub>s"

text \<open>Only numbers and lambda-abstractions are values:\<close>

primrec value\<^sub>s :: "'a expr\<^sub>s \<Rightarrow> bool" where
  "value\<^sub>s (Var\<^sub>s x) = False"
| "value\<^sub>s (Const\<^sub>s n) = True" 
| "value\<^sub>s (Lam\<^sub>s x t e) = True" 
| "value\<^sub>s (App\<^sub>s e\<^sub>1 e\<^sub>2) = False" 
| "value\<^sub>s (Let\<^sub>s x e\<^sub>1 e\<^sub>2) = False" 

text \<open>We define free and bound variables in the usual way:\<close>

primrec free_vars\<^sub>s :: "'a expr\<^sub>s \<Rightarrow> var set" where
  "free_vars\<^sub>s (Var\<^sub>s x) = {x}"
| "free_vars\<^sub>s (Const\<^sub>s n) = {}"
| "free_vars\<^sub>s (Lam\<^sub>s x t e) = free_vars\<^sub>s e - {x}"
| "free_vars\<^sub>s (App\<^sub>s e\<^sub>1 e\<^sub>2) = free_vars\<^sub>s e\<^sub>1 \<union> free_vars\<^sub>s e\<^sub>2"
| "free_vars\<^sub>s (Let\<^sub>s x e\<^sub>1 e\<^sub>2) = free_vars\<^sub>s e\<^sub>1 \<union> (free_vars\<^sub>s e\<^sub>2 - {x})"

primrec bound_vars\<^sub>s :: "'a expr\<^sub>s \<Rightarrow> var set" where
  "bound_vars\<^sub>s (Var\<^sub>s x) = {}"
| "bound_vars\<^sub>s (Const\<^sub>s n) = {}"
| "bound_vars\<^sub>s (Lam\<^sub>s x t e) = insert x (bound_vars\<^sub>s e)"
| "bound_vars\<^sub>s (App\<^sub>s e\<^sub>1 e\<^sub>2) = bound_vars\<^sub>s e\<^sub>1 \<union> bound_vars\<^sub>s e\<^sub>2"
| "bound_vars\<^sub>s (Let\<^sub>s x e\<^sub>1 e\<^sub>2) = insert x (bound_vars\<^sub>s e\<^sub>1 \<union> bound_vars\<^sub>s e\<^sub>2)"

definition all_vars\<^sub>s :: "'a expr\<^sub>s \<Rightarrow> var set" where
  "all_vars\<^sub>s e \<equiv> free_vars\<^sub>s e \<union> bound_vars\<^sub>s e"

lemma all_vars_finite [simp]: "finite (all_vars\<^sub>s e)"
  by (induction e) (simp_all add: all_vars\<^sub>s_def)

lemma all_vars_var [simp]: "all_vars\<^sub>s (Var\<^sub>s x) = {x}"
  by (simp add: all_vars\<^sub>s_def)

lemma all_vars_const [simp]: "all_vars\<^sub>s (Const\<^sub>s n) = {}"
  by (simp add: all_vars\<^sub>s_def)

lemma all_vars_lam [simp]: "all_vars\<^sub>s (Lam\<^sub>s x t e) = insert x (all_vars\<^sub>s e)"
  by (auto simp add: all_vars\<^sub>s_def)

lemma all_vars_app [simp]: "all_vars\<^sub>s (App\<^sub>s e\<^sub>1 e\<^sub>2) = all_vars\<^sub>s e\<^sub>1 \<union> all_vars\<^sub>s e\<^sub>2"
  by (auto simp add: all_vars\<^sub>s_def)

lemma all_vars_let [simp]: "all_vars\<^sub>s (Let\<^sub>s x e\<^sub>1 e\<^sub>2) = insert x (all_vars\<^sub>s e\<^sub>1 \<union> all_vars\<^sub>s e\<^sub>2)"
  by (auto simp add: all_vars\<^sub>s_def)

text \<open>Next, we define a limited form of substitution that simply swaps one variable for another. 
Note that this function is unsafe if the replacement variable is bound in the expression; we will 
only ever use it in \<open>subst\<^sub>s\<close>, where we generate a fresh variable for it.\<close>

primrec subst_var\<^sub>s :: "var \<Rightarrow> var \<Rightarrow> 'a expr\<^sub>s \<Rightarrow> 'a expr\<^sub>s" where
  "subst_var\<^sub>s x x' (Var\<^sub>s y) = Var\<^sub>s (if x = y then x' else y)"
| "subst_var\<^sub>s x x' (Const\<^sub>s n) = Const\<^sub>s n"
| "subst_var\<^sub>s x x' (Lam\<^sub>s y t e) = Lam\<^sub>s y t (if x = y then e else subst_var\<^sub>s x x' e)"
| "subst_var\<^sub>s x x' (App\<^sub>s e\<^sub>1 e\<^sub>2) = App\<^sub>s (subst_var\<^sub>s x x' e\<^sub>1) (subst_var\<^sub>s x x' e\<^sub>2)"
| "subst_var\<^sub>s x x' (Let\<^sub>s y e\<^sub>1 e\<^sub>2) = 
    Let\<^sub>s y (subst_var\<^sub>s x x' e\<^sub>1) (if x = y then e\<^sub>2 else subst_var\<^sub>s x x' e\<^sub>2)"

lemma size_subst_var [simp]: "size (subst_var\<^sub>s x x' e) = size e"
  by (induction e) simp_all

lemma free_subst_vars [simp]: "x' \<notin> bound_vars\<^sub>s e \<Longrightarrow> free_vars\<^sub>s (subst_var\<^sub>s x x' e) = 
    free_vars\<^sub>s e - {x} \<union> (if x \<in> free_vars\<^sub>s e then {x'} else {})"
  by (induction e) (auto split: if_splits)

lemma bound_subst_vars [simp]: "bound_vars\<^sub>s (subst_var\<^sub>s x x' e) = bound_vars\<^sub>s e"
  by (induction e) simp_all

text \<open>Finally, our capture-avoiding substitution function. As noted above, we rename every binder 
every time we pass one, using the \<open>subst_var\<close> helper method to avoid an infinite regress. Indeed, we 
still need the \<open>size_subst_var\<close> lemma just to prove termination.\<close> 

fun subst\<^sub>s :: "var \<Rightarrow> 'a expr\<^sub>s \<Rightarrow> 'a expr\<^sub>s \<Rightarrow> 'a expr\<^sub>s" where
  "subst\<^sub>s x e' (Var\<^sub>s y) = (if x = y then e' else Var\<^sub>s y)"
| "subst\<^sub>s x e' (Const\<^sub>s n) = Const\<^sub>s n"
| "subst\<^sub>s x e' (Lam\<^sub>s y t e) = (
    let z = fresh (all_vars\<^sub>s e' \<union> all_vars\<^sub>s e \<union> {x, y})
    in Lam\<^sub>s z t (subst\<^sub>s x e' (subst_var\<^sub>s y z e)))"
| "subst\<^sub>s x e' (App\<^sub>s e\<^sub>1 e\<^sub>2) = App\<^sub>s (subst\<^sub>s x e' e\<^sub>1) (subst\<^sub>s x e' e\<^sub>2)"
| "subst\<^sub>s x e' (Let\<^sub>s y e\<^sub>1 e\<^sub>2) = (
    let z = fresh (all_vars\<^sub>s e' \<union> all_vars\<^sub>s e\<^sub>2 \<union> {x, y})
    in Let\<^sub>s z (subst\<^sub>s x e' e\<^sub>1) (subst\<^sub>s x e' (subst_var\<^sub>s y z e\<^sub>2)))"

lemma free_vars_subst_var [simp]: "free_vars\<^sub>s e \<subseteq> insert x xs \<Longrightarrow> 
 free_vars\<^sub>s (subst_var\<^sub>s x x' e) \<subseteq> insert x' xs"
proof (induction e arbitrary: xs)
  case (Lam\<^sub>s y t e)
  hence "free_vars\<^sub>s e \<subseteq> insert x (insert y xs)" by auto
  with Lam\<^sub>s have "free_vars\<^sub>s (subst_var\<^sub>s x x' e) \<subseteq> insert x' (insert y xs)" by simp
  with Lam\<^sub>s show ?case by auto
next
  case (Let\<^sub>s y e\<^sub>1 e\<^sub>2)
  hence "free_vars\<^sub>s e\<^sub>2 \<subseteq> insert x (insert y xs)" by auto
  with Let\<^sub>s have "free_vars\<^sub>s (subst_var\<^sub>s x x' e\<^sub>2) \<subseteq> insert x' (insert y xs)" by simp
  with Let\<^sub>s show ?case by auto
qed auto

lemma free_vars_subst [simp]: "free_vars\<^sub>s e \<subseteq> insert x xs \<Longrightarrow> free_vars\<^sub>s e' \<subseteq> xs \<Longrightarrow> 
  free_vars\<^sub>s (subst\<^sub>s x e' e) \<subseteq> xs"
proof (induction x e' e arbitrary: xs rule: subst\<^sub>s.induct)
  case (3 x e' y t e)
  let ?z = "fresh (all_vars\<^sub>s e' \<union> all_vars\<^sub>s e \<union> {x, y})"
  from 3 have "free_vars\<^sub>s e \<subseteq> insert y (insert x xs)" by auto
  hence "free_vars\<^sub>s (subst_var\<^sub>s y ?z e) \<subseteq> insert ?z (insert x xs)" by simp
  hence "free_vars\<^sub>s (subst_var\<^sub>s y ?z e) \<subseteq> insert x (insert ?z xs)" by auto
  with 3 show ?case by (auto simp add: Let_def)
next
  case (5 x e' y e\<^sub>1 e\<^sub>2)
  let ?z = "fresh (all_vars\<^sub>s e' \<union> all_vars\<^sub>s e\<^sub>2 \<union> {x, y})"
  from 5 have "free_vars\<^sub>s e\<^sub>2 \<subseteq> insert y (insert x xs)" by auto
  hence "free_vars\<^sub>s (subst_var\<^sub>s y ?z e\<^sub>2) \<subseteq> insert ?z (insert x xs)" by simp
  hence X: "free_vars\<^sub>s (subst_var\<^sub>s y ?z e\<^sub>2) \<subseteq> insert x (insert ?z xs)" by auto
  from 5 have "free_vars\<^sub>s e' \<subseteq> insert ?z xs" by auto
  with 5 X have "free_vars\<^sub>s (subst\<^sub>s x e' (subst_var\<^sub>s y ?z e\<^sub>2)) \<subseteq> insert ?z xs" by auto
  with 5 show ?case by (auto simp add: Let_def)
qed auto

text \<open>Now, we define big-step applicative-order evaluation. It is represented by an inductive 
relation rather than an evaluation function because, of course, some source expressions do not have 
a normal form. However, even once we prove termination for later stages, we will mostly continue to 
use an inductive definition of evaluation simply because it is easier to write and work with.\<close> 

inductive eval\<^sub>s :: "'a expr\<^sub>s \<Rightarrow> 'a expr\<^sub>s \<Rightarrow> bool" (infix "\<Down>\<^sub>s" 50) where
  ev\<^sub>s_const [simp]: "Const\<^sub>s n \<Down>\<^sub>s Const\<^sub>s n"
| ev\<^sub>s_lam [simp]: "Lam\<^sub>s x t e \<Down>\<^sub>s Lam\<^sub>s x t e"
| ev\<^sub>s_app [simp]: "e\<^sub>1 \<Down>\<^sub>s Lam\<^sub>s x t e\<^sub>1' \<Longrightarrow> e\<^sub>2 \<Down>\<^sub>s v\<^sub>2 \<Longrightarrow> subst\<^sub>s x v\<^sub>2 e\<^sub>1' \<Down>\<^sub>s v \<Longrightarrow> App\<^sub>s e\<^sub>1 e\<^sub>2 \<Down>\<^sub>s v"
| ev\<^sub>s_let [simp]: "e\<^sub>1 \<Down>\<^sub>s v\<^sub>1 \<Longrightarrow> subst\<^sub>s x v\<^sub>1 e\<^sub>2 \<Down>\<^sub>s v\<^sub>2 \<Longrightarrow> Let\<^sub>s x e\<^sub>1 e\<^sub>2 \<Down>\<^sub>s v\<^sub>2"

lemma free_vars_eval [simp]: "e \<Down>\<^sub>s v \<Longrightarrow> free_vars\<^sub>s e = {} \<Longrightarrow> free_vars\<^sub>s v = {}"
proof (induction e v rule: eval\<^sub>s.induct)
  case (ev\<^sub>s_app e\<^sub>1 x t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  hence "free_vars\<^sub>s e\<^sub>1' \<subseteq> insert x {} \<and> free_vars\<^sub>s v\<^sub>2 \<subseteq> {}" by simp
  hence "free_vars\<^sub>s (subst\<^sub>s x v\<^sub>2 e\<^sub>1') \<subseteq> {}" by (metis free_vars_subst)
  with ev\<^sub>s_app show ?case by simp
next
  case (ev\<^sub>s_let e\<^sub>1 v\<^sub>1 x e\<^sub>2 v\<^sub>2)
  hence "free_vars\<^sub>s e\<^sub>2 \<subseteq> insert x {} \<and> free_vars\<^sub>s v\<^sub>1 \<subseteq> {}" by simp
  hence "free_vars\<^sub>s (subst\<^sub>s x v\<^sub>1 e\<^sub>2) \<subseteq> {}" by (metis free_vars_subst)
  with ev\<^sub>s_let show ?case by simp
qed simp_all

lemma eval_to_value [simp]: "e \<Down>\<^sub>s v \<Longrightarrow> value\<^sub>s v"
  by (induction e v rule: eval\<^sub>s.induct) simp_all

lemma val_no_eval: "e \<Down>\<^sub>s v \<Longrightarrow> value\<^sub>s e \<Longrightarrow> v = e"
  by (induction e v rule: eval\<^sub>s.induct) simp_all

text \<open>Since our language is untyped, we cannot prove (or even express) the progress and preservation 
theorems. However, we can prove determinism of evaluation:\<close>

theorem determinism\<^sub>s: "e \<Down>\<^sub>s v \<Longrightarrow> e \<Down>\<^sub>s v' \<Longrightarrow> v = v'"
proof (induction e v arbitrary: v' rule: eval\<^sub>s.induct)
  case (ev\<^sub>s_const n)
  thus ?case by (induction rule: eval\<^sub>s.cases) simp_all
next
  case (ev\<^sub>s_lam x e)
  thus ?case by (induction rule: eval\<^sub>s.cases) simp_all
next
  case (ev\<^sub>s_app e\<^sub>1 x e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  from ev\<^sub>s_app(7, 1, 2, 3, 4, 5, 6) show ?case by (induction rule: eval\<^sub>s.cases) blast+
next
  case (ev\<^sub>s_let e\<^sub>1 v\<^sub>1 x e\<^sub>2 v\<^sub>2 t)
  from ev\<^sub>s_let(5, 1, 2, 3, 4) show ?case by (induction rule: eval\<^sub>s.cases) blast+
qed

text \<open>We also define a no-shadowing predicate on our expressions, where no variable is ever bound 
twice in the same scope. This will be useful when we later remove names from the representation.\<close>

primrec no_shadowing\<^sub>s :: "'a expr\<^sub>s \<Rightarrow> bool" where
  "no_shadowing\<^sub>s (Var\<^sub>s x) = True"
| "no_shadowing\<^sub>s (Const\<^sub>s n) = True"
| "no_shadowing\<^sub>s (Lam\<^sub>s x t e) = (no_shadowing\<^sub>s e \<and> x \<notin> bound_vars\<^sub>s e)"
| "no_shadowing\<^sub>s (App\<^sub>s e\<^sub>1 e\<^sub>2) = (no_shadowing\<^sub>s e\<^sub>1 \<and> no_shadowing\<^sub>s e\<^sub>2)"
| "no_shadowing\<^sub>s (Let\<^sub>s x e\<^sub>1 e\<^sub>2) = (no_shadowing\<^sub>s e\<^sub>1 \<and> no_shadowing\<^sub>s e\<^sub>2 \<and> x \<notin> bound_vars\<^sub>s e\<^sub>2)"

lemma now_shadowing_subst_var [simp]: "no_shadowing\<^sub>s (subst_var\<^sub>s x y e) = no_shadowing\<^sub>s e"
  by (induction e) simp_all

text \<open>We define a shadow-removing function on our expressions, that converts one to an 
alpha-equivalent form with no shadowed variables.\<close>

primrec remove_shadows\<^sub>s' :: "var set \<Rightarrow> 'a expr\<^sub>s \<Rightarrow> 'a expr\<^sub>s" where
  "remove_shadows\<^sub>s' vs (Var\<^sub>s y) = Var\<^sub>s y"
| "remove_shadows\<^sub>s' vs (Const\<^sub>s n) = Const\<^sub>s n"
| "remove_shadows\<^sub>s' vs (Lam\<^sub>s x t e) = (
    let e' = remove_shadows\<^sub>s' (insert x vs) e
    in let y = fresh (vs \<union> all_vars\<^sub>s e')
    in Lam\<^sub>s y t (subst_var\<^sub>s x y e'))"
| "remove_shadows\<^sub>s' vs (App\<^sub>s e\<^sub>1 e\<^sub>2) = App\<^sub>s (remove_shadows\<^sub>s' vs e\<^sub>1) (remove_shadows\<^sub>s' vs e\<^sub>2)"
| "remove_shadows\<^sub>s' vs (Let\<^sub>s x e\<^sub>1 e\<^sub>2) = (
    let e\<^sub>2' = remove_shadows\<^sub>s' (insert x vs) e\<^sub>2
    in let y = fresh (vs \<union> all_vars\<^sub>s e\<^sub>2')
    in Let\<^sub>s y (remove_shadows\<^sub>s' vs e\<^sub>1) (subst_var\<^sub>s x y e\<^sub>2'))"

definition remove_shadows\<^sub>s :: "'a expr\<^sub>s \<Rightarrow> 'a expr\<^sub>s" where
  "remove_shadows\<^sub>s e \<equiv> remove_shadows\<^sub>s' {} e"

lemma remove_shadows_no_shadow' [simp]: "finite vs \<Longrightarrow> no_shadowing\<^sub>s (remove_shadows\<^sub>s' vs e)"
proof (induction e arbitrary: vs)
  case (Lam\<^sub>s x t e)
  let ?e = "remove_shadows\<^sub>s' (insert x vs) e"
  let ?x = "fresh (vs \<union> all_vars\<^sub>s ?e)"
  from Lam\<^sub>s have "finite (vs \<union> all_vars\<^sub>s ?e)" by simp
  hence "?x \<notin> vs \<union> all_vars\<^sub>s ?e" by (metis fresh_is_fresh)
  with Lam\<^sub>s show ?case by (simp add: Let_def all_vars\<^sub>s_def)
next
  case (Let\<^sub>s x e\<^sub>1 e\<^sub>2)
  let ?e\<^sub>2 = "remove_shadows\<^sub>s' (insert x vs) e\<^sub>2"
  let ?x = "fresh (vs \<union> all_vars\<^sub>s ?e\<^sub>2)"
  from Let\<^sub>s have "finite (vs \<union> all_vars\<^sub>s ?e\<^sub>2)" by simp
  hence "?x \<notin> vs \<union> all_vars\<^sub>s ?e\<^sub>2" by (metis fresh_is_fresh)
  with Let\<^sub>s show ?case by (simp add: Let_def all_vars\<^sub>s_def)
qed simp_all

lemma remove_shadows_no_shadow [simp]: "no_shadowing\<^sub>s (remove_shadows\<^sub>s e)"
  by (simp add: remove_shadows\<^sub>s_def)

lemma free_vars_remove_shadow [simp]: "finite vs \<Longrightarrow> 
  free_vars\<^sub>s (remove_shadows\<^sub>s' vs e) = free_vars\<^sub>s e"
proof (induction e arbitrary: vs)
  case (Lam\<^sub>s x t e)
  let ?e = "remove_shadows\<^sub>s' (insert x vs) e"
  let ?x = "fresh (vs \<union> all_vars\<^sub>s ?e)"
  from Lam\<^sub>s have "finite (vs \<union> all_vars\<^sub>s ?e)" by simp
  hence "?x \<notin> vs \<union> all_vars\<^sub>s ?e" by (metis fresh_is_fresh)
  with Lam\<^sub>s show ?case by (simp add: Let_def all_vars\<^sub>s_def)
next
  case (Let\<^sub>s x e\<^sub>1 e\<^sub>2)
  let ?e\<^sub>2 = "remove_shadows\<^sub>s' (insert x vs) e\<^sub>2"
  let ?x = "fresh (vs \<union> all_vars\<^sub>s ?e\<^sub>2)"
  from Let\<^sub>s have "finite (vs \<union> all_vars\<^sub>s ?e\<^sub>2)" by simp
  hence "?x \<notin> vs \<union> all_vars\<^sub>s ?e\<^sub>2" by (metis fresh_is_fresh)
  with Let\<^sub>s show ?case by (simp add: Let_def all_vars\<^sub>s_def)
qed simp_all

end