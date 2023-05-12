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
representation to make substitution simpler, but we want to keep out source language as close to an 
intuitive, "human-readable" version as possible. After all, changing this sort of behaviour to one 
more easily implemented on a computer is the essence of compilation.\<close>

(* TODO: products and sums *)

datatype expr\<^sub>s = 
  Var\<^sub>s var
  | Const\<^sub>s nat
  | Lam\<^sub>s var expr\<^sub>s
  | App\<^sub>s expr\<^sub>s expr\<^sub>s

text \<open>Only numbers and lambda-abstractions are values:\<close>

primrec "value" :: "expr\<^sub>s \<Rightarrow> bool" where
  "value (Var\<^sub>s x) = False"
| "value (Const\<^sub>s k) = True" 
| "value (Lam\<^sub>s x e) = True" 
| "value (App\<^sub>s e\<^sub>1 e\<^sub>2) = False" 

text \<open>Our capture-avoiding substitution requires some helper methods. First, a function to gather up 
all variables in an expression:\<close>

primrec all_vars :: "expr\<^sub>s \<Rightarrow> var set" where
  "all_vars (Var\<^sub>s x) = {x}"
| "all_vars (Const\<^sub>s k) = {}"
| "all_vars (Lam\<^sub>s x e) = insert x (all_vars e)"
| "all_vars (App\<^sub>s e\<^sub>1 e\<^sub>2) = all_vars e\<^sub>1 \<union> all_vars e\<^sub>2"

lemma all_vars_finite: "finite (all_vars e)"
  by (induction e) simp_all

text \<open>Next, we make a limited form of substitution that simply swaps one variable for another. Note 
that this function is unsafe if the replacement variable is bound in the expression; we will only 
ever use it in \<open>subst\<close>, where we generate a fresh variable for it.\<close>

primrec subst_var :: "var \<Rightarrow> var \<Rightarrow> expr\<^sub>s \<Rightarrow> expr\<^sub>s" where
  "subst_var x x' (Var\<^sub>s y) = Var\<^sub>s (if x = y then x' else y)"
| "subst_var x x' (Const\<^sub>s k) = Const\<^sub>s k"
| "subst_var x x' (Lam\<^sub>s y e) = Lam\<^sub>s y (if x = y then e else subst_var x x' e)"
| "subst_var x x' (App\<^sub>s e\<^sub>1 e\<^sub>2) = App\<^sub>s (subst_var x x' e\<^sub>1) (subst_var x x' e\<^sub>2)"

lemma size_subst_var [simp]: "size (subst_var x x' e) = size e"
  by (induction e) simp_all

text \<open>Finally, our capture-avoiding substitution function. As noted above, we rename every binder 
every time we pass one, using the \<open>subst_var\<close> helper method to avoid an infinite regress. Indeed, we 
still need the \<open>size_subst_var\<close> lemma just to prove termination.\<close> 

fun subst\<^sub>s :: "var \<Rightarrow> expr\<^sub>s \<Rightarrow> expr\<^sub>s \<Rightarrow> expr\<^sub>s" where
  "subst\<^sub>s x e' (Var\<^sub>s y) = (if x = y then e' else Var\<^sub>s y)"
| "subst\<^sub>s x e' (Const\<^sub>s k) = Const\<^sub>s k"
| "subst\<^sub>s x e' (Lam\<^sub>s y e) = (
    let z = fresh (all_vars e' \<union> all_vars e \<union> {x, y})
    in Lam\<^sub>s z (subst\<^sub>s x e' (subst_var y z e)))"
| "subst\<^sub>s x e' (App\<^sub>s e\<^sub>1 e\<^sub>2) = App\<^sub>s (subst\<^sub>s x e' e\<^sub>1) (subst\<^sub>s x e' e\<^sub>2)"

text \<open>Now, we define big-step applicative-order evaluation. It is represented by an inductive 
relation rather than an evaluation function because, of course, some source expressions do not have 
a normal form. However, even once we prove termination for later stages, we will mostly continue to 
use an inductive definition of evaluation simply because it is easier to write and work with.\<close> 

inductive eval\<^sub>s :: "expr\<^sub>s \<Rightarrow> expr\<^sub>s \<Rightarrow> bool" (infix "\<Down>" 50) where
  ev\<^sub>s_const [simp]: "Const\<^sub>s k \<Down> Const\<^sub>s k"
| ev\<^sub>s_lam [simp]: "Lam\<^sub>s x e \<Down> Lam\<^sub>s x e"
| ev\<^sub>s_app [simp]: "e\<^sub>1 \<Down> Lam\<^sub>s x e\<^sub>1' \<Longrightarrow> e\<^sub>2 \<Down> v\<^sub>2 \<Longrightarrow> subst\<^sub>s x v\<^sub>2 e\<^sub>1' \<Down> v \<Longrightarrow> App\<^sub>s e\<^sub>1 e\<^sub>2 \<Down> v"

text \<open>Since our language is untyped, we cannot prove (or even express) the progress and preservation 
theorems. However, we can prove determinism of evaluation:\<close>

theorem determinismn: "e \<Down> v \<Longrightarrow> e \<Down> v' \<Longrightarrow> v = v'"
proof (induction e v arbitrary: v' rule: eval\<^sub>s.induct)
  case (ev\<^sub>s_const k)
  thus ?case by (induction "Const\<^sub>s k" v' rule: eval\<^sub>s.induct) simp_all
next
  case (ev\<^sub>s_lam x e)
  thus ?case by (induction "Lam\<^sub>s x e" v' rule: eval\<^sub>s.induct) simp_all
next
  case (ev\<^sub>s_app e\<^sub>1 x e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  from ev\<^sub>s_app(7, 1, 2, 3, 4, 5, 6) show ?case 
    by (induction "App\<^sub>s e\<^sub>1 e\<^sub>2" v' rule: eval\<^sub>s.induct) blast+
qed

end