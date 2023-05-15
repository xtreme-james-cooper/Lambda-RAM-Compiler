theory SourceLanguage
  imports "../00Utils/Variable" "../00Utils/Utils"
begin

section \<open>Source Language\<close>

text \<open>We now define our source language. It consists of the untyped lambda calculus, enhanced with 
numbers and arithmetic. There are two main challenges with implementing the untyped lambda calculus: 
the non-termination of evaluation, and capture-avoiding substitution. We cannot address the first 
here, since our language as it stands does in fact admit unnormalizable terms like
\<open>App\<^sub>s (Lam\<^sub>s x (App\<^sub>s (Var\<^sub>s x) (Var\<^sub>s x))) (Lam\<^sub>s x (App\<^sub>s (Var\<^sub>s x) (Var\<^sub>s x)))\<close>; after typechecking, we will 
lower our sights to the simply-typed subset of our language and be able to prove normalization then.
As for substitution, for now we take the brute-force approach of renaming every binder to a fresh 
variable every time we substitute past it. We will shortly switch to a nameless Debruijn-index 
representation to make substitution simpler, but we want to keep our source language as close to an 
intuitive, "human-readable" version as possible. After all, changing this sort of behaviour to one 
more easily implemented on a computer is the essence of compilation.\<close>

text \<open>Our concrete datatype is parameterized on an annotation on each binder; this will enable us to
reuse the same datatype for the typed version.\<close>

(* TODO: products and sums *)

datatype 'a expr\<^sub>s = 
  Var\<^sub>s var
  | Const\<^sub>s nat
  | Lam\<^sub>s var 'a "'a expr\<^sub>s"
  | App\<^sub>s "'a expr\<^sub>s" "'a expr\<^sub>s"

text \<open>Only numbers and lambda-abstractions are values:\<close>

primrec value\<^sub>s :: "'a expr\<^sub>s \<Rightarrow> bool" where
  "value\<^sub>s (Var\<^sub>s x) = False"
| "value\<^sub>s (Const\<^sub>s n) = True" 
| "value\<^sub>s (Lam\<^sub>s x t e) = True" 
| "value\<^sub>s (App\<^sub>s e\<^sub>1 e\<^sub>2) = False" 

text \<open>We define free variables in the usual way:\<close>

primrec free_vars\<^sub>s :: "'a expr\<^sub>s \<Rightarrow> var set" where
  "free_vars\<^sub>s (Var\<^sub>s x) = {x}"
| "free_vars\<^sub>s (Const\<^sub>s k) = {}"
| "free_vars\<^sub>s (Lam\<^sub>s x t e) = free_vars\<^sub>s e - {x}"
| "free_vars\<^sub>s (App\<^sub>s e\<^sub>1 e\<^sub>2) = free_vars\<^sub>s e\<^sub>1 \<union> free_vars\<^sub>s e\<^sub>2"

text \<open>Our capture-avoiding substitution requires some helper methods. First, a function to gather up 
all variables in an expression, even bound ones:\<close>

primrec all_vars\<^sub>s :: "'a expr\<^sub>s \<Rightarrow> var set" where
  "all_vars\<^sub>s (Var\<^sub>s x) = {x}"
| "all_vars\<^sub>s (Const\<^sub>s n) = {}"
| "all_vars\<^sub>s (Lam\<^sub>s x t e) = insert x (all_vars\<^sub>s e)"
| "all_vars\<^sub>s (App\<^sub>s e\<^sub>1 e\<^sub>2) = all_vars\<^sub>s e\<^sub>1 \<union> all_vars\<^sub>s e\<^sub>2"

lemma all_vars_finite [simp]: "finite (all_vars\<^sub>s e)"
  by (induction e) simp_all

text \<open>Next, we define a limited form of substitution that simply swaps one variable for another. 
Note that this function is unsafe if the replacement variable is bound in the expression; we will 
only ever use it in \<open>subst\<^sub>s\<close>, where we generate a fresh variable for it.\<close>

primrec subst_var\<^sub>s :: "var \<Rightarrow> var \<Rightarrow> 'a expr\<^sub>s \<Rightarrow> 'a expr\<^sub>s" where
  "subst_var\<^sub>s x x' (Var\<^sub>s y) = Var\<^sub>s (if x = y then x' else y)"
| "subst_var\<^sub>s x x' (Const\<^sub>s n) = Const\<^sub>s n"
| "subst_var\<^sub>s x x' (Lam\<^sub>s y t e) = Lam\<^sub>s y t (if x = y then e else subst_var\<^sub>s x x' e)"
| "subst_var\<^sub>s x x' (App\<^sub>s e\<^sub>1 e\<^sub>2) = App\<^sub>s (subst_var\<^sub>s x x' e\<^sub>1) (subst_var\<^sub>s x x' e\<^sub>2)"

lemma size_subst_var [simp]: "size (subst_var\<^sub>s x x' e) = size e"
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

lemma free_vars_subst_var [simp]: "free_vars\<^sub>s e \<subseteq> insert x xs \<Longrightarrow> 
 free_vars\<^sub>s (subst_var\<^sub>s x x' e) \<subseteq> insert x' xs"
proof (induction e arbitrary: xs)
  case (Lam\<^sub>s y t e)
  hence "free_vars\<^sub>s e \<subseteq> insert x (insert y xs)" by auto
  with Lam\<^sub>s have "free_vars\<^sub>s (subst_var\<^sub>s x x' e) \<subseteq> insert x' (insert y xs)" by simp
  with Lam\<^sub>s show ?case by auto
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
qed auto

text \<open>Now, we define big-step applicative-order evaluation. It is represented by an inductive 
relation rather than an evaluation function because, of course, some source expressions do not have 
a normal form. However, even once we prove termination for later stages, we will mostly continue to 
use an inductive definition of evaluation simply because it is easier to write and work with.\<close> 

inductive eval\<^sub>s :: "'a expr\<^sub>s \<Rightarrow> 'a expr\<^sub>s \<Rightarrow> bool" (infix "\<Down>\<^sub>s" 50) where
  ev\<^sub>s_const [simp]: "Const\<^sub>s n \<Down>\<^sub>s Const\<^sub>s n"
| ev\<^sub>s_lam [simp]: "Lam\<^sub>s x t e \<Down>\<^sub>s Lam\<^sub>s x t e"
| ev\<^sub>s_app [simp]: "e\<^sub>1 \<Down>\<^sub>s Lam\<^sub>s x t e\<^sub>1' \<Longrightarrow> e\<^sub>2 \<Down>\<^sub>s v\<^sub>2 \<Longrightarrow> subst\<^sub>s x v\<^sub>2 e\<^sub>1' \<Down>\<^sub>s v \<Longrightarrow> App\<^sub>s e\<^sub>1 e\<^sub>2 \<Down>\<^sub>s v"

lemma free_vars_eval [simp]: "e \<Down>\<^sub>s v \<Longrightarrow> free_vars\<^sub>s e = {} \<Longrightarrow> free_vars\<^sub>s v = {}"
proof (induction e v rule: eval\<^sub>s.induct)
  case (ev\<^sub>s_app e\<^sub>1 x t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  hence "free_vars\<^sub>s e\<^sub>1' \<subseteq> insert x {} \<and> free_vars\<^sub>s v\<^sub>2 \<subseteq> {}" by simp
  hence "free_vars\<^sub>s (subst\<^sub>s x v\<^sub>2 e\<^sub>1') \<subseteq> {}" by (metis free_vars_subst)
  with ev\<^sub>s_app show ?case by simp
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
qed

end