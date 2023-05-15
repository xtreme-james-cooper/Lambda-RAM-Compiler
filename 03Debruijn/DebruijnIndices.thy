theory DebruijnIndices
  imports "../02Typed/Type" "../00Utils/Environment" "../00Utils/Iteration"
begin

section \<open>Debruijn Indices\<close>

text \<open>Our next stage is the Debruijn-indexed language. It resembles the typed source language, but
without names on the binders and with natural numbers for variables; these are our indices. Pierce 
[5] covers Debruijn indices well, but the brief version is that it is a nameless representation of 
expressions where a variable points to its binder by counting how many binders lie between them. So,
for example, \<open>\<lambda>x. \<lambda>y. x y (\<lambda>y. x y)\<close> would be represented by \<open>\<lambda>. \<lambda>. 1 0 (\<lambda>. 2 0)\<close>. It is far more
difficult to read, but has the great virtue that name-shadowing and name-collisions are impossible - 
since there are no names - and thus substitution is made much simpler.\<close>

datatype expr\<^sub>d = 
  Var\<^sub>d nat
  | Const\<^sub>d nat
  | Lam\<^sub>d ty expr\<^sub>d
  | App\<^sub>d expr\<^sub>d expr\<^sub>d

text \<open>The typing relation remains similar to the source language typing relation, but notice that 
the context is now a \<open>ty list\<close> examined with \<open>lookup\<close> rather than a \<open>var \<rightharpoonup> ty\<close> partial function, 
and that binding a new variable is just consing to the front of the list - this automatically 
increments all the other in-scope variables.\<close>

inductive typing\<^sub>d :: "ty list \<Rightarrow> expr\<^sub>d \<Rightarrow> ty \<Rightarrow> bool" (infix "\<turnstile>\<^sub>d _ :" 50) where
  tc\<^sub>d_var [simp]: "lookup \<Gamma> x = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d Var\<^sub>d x : t"
| tc\<^sub>d_const [simp]: "\<Gamma> \<turnstile>\<^sub>d Const\<^sub>d n : Num"
| tc\<^sub>d_lam [simp]: "insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d Lam\<^sub>d t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2"
| tc\<^sub>d_app [simp]: "\<Gamma> \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d App\<^sub>d e\<^sub>1 e\<^sub>2 : t\<^sub>2"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>d Var\<^sub>d x : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>d Const\<^sub>d n : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>d Lam\<^sub>d t' e : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>d App\<^sub>d e\<^sub>1 e\<^sub>2 : t"

lemma tc_postpend [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> (\<Gamma> @ \<Gamma>') \<turnstile>\<^sub>d e : t"
  by (induction \<Gamma> e t rule: typing\<^sub>d.induct) simp_all

text \<open>We have the same set of values as in our source language:\<close>

primrec value\<^sub>d :: "expr\<^sub>d \<Rightarrow> bool" where
  "value\<^sub>d (Var\<^sub>d x) = False"
| "value\<^sub>d (Const\<^sub>d n) = True" 
| "value\<^sub>d (Lam\<^sub>d t e) = True" 
| "value\<^sub>d (App\<^sub>d e\<^sub>1 e\<^sub>2) = False" 

lemma canonical_num\<^sub>d [dest]: "\<Gamma> \<turnstile>\<^sub>d e : Num \<Longrightarrow> value\<^sub>d e \<Longrightarrow> \<exists>k. e = Const\<^sub>d k"
  by (induction \<Gamma> e Num rule: typing\<^sub>d.induct) simp_all

lemma canonical_arrow\<^sub>d [dest]: "\<Gamma> \<turnstile>\<^sub>d e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> value\<^sub>d e \<Longrightarrow> 
    \<exists>e'. e = Lam\<^sub>d t\<^sub>1 e' \<and> insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e' : t\<^sub>2"
  by (induction \<Gamma> e "Arrow t\<^sub>1 t\<^sub>2" rule: typing\<^sub>d.induct) simp_all

text \<open>Substitution is much simpler than in our named source language, but not entirely trivial. We 
need one helper function, to increment all the variables in an expression that are larger than some
number.\<close>

primrec incr\<^sub>d :: "nat \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "incr\<^sub>d x (Var\<^sub>d y) = Var\<^sub>d (incr x y)"
| "incr\<^sub>d x (Const\<^sub>d n) = Const\<^sub>d n"
| "incr\<^sub>d x (Lam\<^sub>d t e) = Lam\<^sub>d t (incr\<^sub>d (Suc x) e)"
| "incr\<^sub>d x (App\<^sub>d e\<^sub>1 e\<^sub>2) = App\<^sub>d (incr\<^sub>d x e\<^sub>1) (incr\<^sub>d x e\<^sub>2)"

lemma incr\<^sub>d_swap [simp]: "y \<le> x \<Longrightarrow> incr\<^sub>d y (incr\<^sub>d x e) = incr\<^sub>d (Suc x) (incr\<^sub>d y e)"
  by (induction e arbitrary: x y) simp_all

lemma tc\<^sub>d_incr [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> insert_at x t' \<Gamma> \<turnstile>\<^sub>d incr\<^sub>d x e : t" 
proof (induction \<Gamma> e t arbitrary: x rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  hence "insert_at x t' \<Gamma> \<turnstile>\<^sub>d (incr\<^sub>d x e\<^sub>1) : Arrow t\<^sub>1 t\<^sub>2" by simp
  moreover from tc\<^sub>d_app have "insert_at x t' \<Gamma> \<turnstile>\<^sub>d (incr\<^sub>d x e\<^sub>2) : t\<^sub>1" by simp
  ultimately show ?case by simp
qed fastforce+

lemma incr\<^sub>d_above_bounds [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> x \<ge> length \<Gamma> \<Longrightarrow> incr\<^sub>d x e = e"
proof (induction \<Gamma> e t arbitrary: x rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_var \<Gamma> y t)
  moreover hence "y < length \<Gamma>" by simp
  ultimately have "y < x" by linarith
  thus ?case by (simp add: incr_min)
qed simp_all

text \<open>Now we can define substitution. Unlike in our source language, we have to decrement variables 
that are larger than the substituted variable, because that variable is now gone. In compensation, 
substitution under a binder is now much easier: we simply increment the variable being substituted 
for, and also every variable in \<open>e'\<close>.\<close>

primrec subst\<^sub>d :: "nat \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "subst\<^sub>d x e' (Var\<^sub>d y) = (if x = y then e' else Var\<^sub>d (decr x y))"
| "subst\<^sub>d x e' (Const\<^sub>d n) = Const\<^sub>d n"
| "subst\<^sub>d x e' (Lam\<^sub>d t e) = Lam\<^sub>d t (subst\<^sub>d (Suc x) (incr\<^sub>d 0 e') e)"
| "subst\<^sub>d x e' (App\<^sub>d e\<^sub>1 e\<^sub>2) = App\<^sub>d (subst\<^sub>d x e' e\<^sub>1) (subst\<^sub>d x e' e\<^sub>2)"

lemma incr\<^sub>d_subst_swap [simp]: "y \<le> x \<Longrightarrow> 
    incr\<^sub>d y (subst\<^sub>d x e' e) = subst\<^sub>d (Suc x) (incr\<^sub>d y e') (incr\<^sub>d y e)"
  by (induction e arbitrary: x y e') (simp_all add: incr_le incr_suc_dest)

lemma subst\<^sub>d_incr_cancel [simp]: "subst\<^sub>d x e' (incr\<^sub>d x e) = e"
  by (induction e arbitrary: x e') (simp_all, metis incr_not_eq)

lemma subst\<^sub>d_subst_swap [simp]: "y \<le> x \<Longrightarrow> 
  subst\<^sub>d x e\<^sub>1 (subst\<^sub>d y e\<^sub>2 e) = subst\<^sub>d y (subst\<^sub>d x e\<^sub>1 e\<^sub>2) (subst\<^sub>d (Suc x) (incr\<^sub>d y e\<^sub>1) e)"
proof (induction e arbitrary: x y e\<^sub>1 e\<^sub>2)
  case (Var\<^sub>d z)
  thus ?case 
  proof (cases "y = z")
    case False
    with Var\<^sub>d show ?thesis 
    proof (cases "x = decr y z")
      case True note TXD = True
      with Var\<^sub>d False show ?thesis
      proof (cases "y = decr y z")
        case True
        with False have "z = Suc y" by simp
        with TXD show ?thesis by auto
      qed simp_all
    qed auto
  qed simp_all
qed simp_all

lemma tc\<^sub>d_subst [simp]: "insert_at x t' \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e' : t' \<Longrightarrow> 
  \<Gamma> \<turnstile>\<^sub>d subst\<^sub>d x e' e : t"
proof (induction "insert_at x t' \<Gamma>" e t arbitrary: \<Gamma> x e' rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_var y t)
  moreover have "x \<le> length \<Gamma> \<Longrightarrow> x \<noteq> y \<Longrightarrow> lookup \<Gamma> (decr x y) = lookup (insert_at x t' \<Gamma>) y" 
    by simp
  ultimately show ?case by fastforce
qed fastforce+ 

lemma subst\<^sub>d_above_bounds [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> x \<ge> length \<Gamma> \<Longrightarrow> subst\<^sub>d x e' e = e"
proof (induction \<Gamma> e t arbitrary: x e' rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_var \<Gamma> y t)
  hence "y < length \<Gamma>" by simp
  with tc\<^sub>d_var have "y < x" by linarith
  with tc\<^sub>d_var show ?case by auto
qed simp_all

lemma subst\<^sub>d_to_var [dest]: "subst\<^sub>d 0 e' e = Var\<^sub>d x \<Longrightarrow> value\<^sub>d e' \<Longrightarrow> e = Var\<^sub>d (Suc x)"
proof (induction e)
  case (Var\<^sub>d y)
  thus ?case by (induction y) simp_all
qed simp_all

lemma value\<^sub>d_subst [dest]: "value\<^sub>d (subst\<^sub>d 0 e' e) \<Longrightarrow> value\<^sub>d e' \<Longrightarrow> value\<^sub>d e \<or> e = Var\<^sub>d 0"
  by (induction e) (simp_all split: if_splits)

text \<open>We can now define evaluation. Unlike our source language, but in keeping with future stages, 
we use a small-step evaluation relation. (We will define big-step evaluation for this stage 
subsequently.) This will allow us, for the first time, to prove the full safety property.\<close>

inductive eval\<^sub>d :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d \<Rightarrow> bool" (infix "\<leadsto>\<^sub>d" 50) where
  ev\<^sub>d_app1 [simp]: "e\<^sub>1 \<leadsto>\<^sub>d e\<^sub>1' \<Longrightarrow> App\<^sub>d e\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>d App\<^sub>d e\<^sub>1' e\<^sub>2"
| ev\<^sub>d_app2 [simp]: "value\<^sub>d e\<^sub>1 \<Longrightarrow> e\<^sub>2 \<leadsto>\<^sub>d e\<^sub>2' \<Longrightarrow> App\<^sub>d e\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>d App\<^sub>d e\<^sub>1 e\<^sub>2'"
| ev\<^sub>d_app3 [simp]: "value\<^sub>d e\<^sub>2 \<Longrightarrow> App\<^sub>d (Lam\<^sub>d t e\<^sub>1) e\<^sub>2 \<leadsto>\<^sub>d subst\<^sub>d 0 e\<^sub>2 e\<^sub>1"

lemma val_no_eval\<^sub>d: "e \<leadsto>\<^sub>d e' \<Longrightarrow> value\<^sub>d e \<Longrightarrow> False"
  by (induction e e' rule: eval\<^sub>d.induct) simp_all

text \<open>Our metatheoretic properties, progress, preservation, and determinism, now all follow 
straightforwardly.\<close>

theorem progress\<^sub>d: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> value\<^sub>d e \<or> (\<exists>e'. e \<leadsto>\<^sub>d e')"
proof (induction "[] :: ty list" e t rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  thus ?case 
  proof (cases "value\<^sub>d e\<^sub>1")
    case True note T = True
    thus ?thesis 
    proof (cases "value\<^sub>d e\<^sub>2")
      case True
      with tc\<^sub>d_app T show ?thesis by (metis canonical_arrow\<^sub>d ev\<^sub>d_app3)
    next
      case False
      with tc\<^sub>d_app T show ?thesis by (metis ev\<^sub>d_app2)
    qed
  next
    case False
    with tc\<^sub>d_app show ?thesis by (metis ev\<^sub>d_app1)
  qed
qed simp_all

theorem preservationd [simp]: "e \<leadsto>\<^sub>d e' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e' : t"
  by (induction e e' arbitrary: t rule: eval\<^sub>d.induct) fastforce+

theorem determinism\<^sub>d: "e \<leadsto>\<^sub>d e' \<Longrightarrow> e \<leadsto>\<^sub>d e'' \<Longrightarrow> e' = e''"
proof (induction e e' arbitrary: e'' rule: eval\<^sub>d.induct)
case (ev\<^sub>d_app1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
  from ev\<^sub>d_app1(3, 1, 2) show ?case 
    using val_no_eval\<^sub>d value\<^sub>d.simps(3) by (induction rule: eval\<^sub>d.cases) blast+
next
  case (ev\<^sub>d_app2 e\<^sub>1 e\<^sub>2 e\<^sub>2')
  from ev\<^sub>d_app2(4, 1, 2, 3) show ?case 
     using val_no_eval\<^sub>d by (induction rule: eval\<^sub>d.cases) blast+
next
  case (ev\<^sub>d_app3 e\<^sub>2 t e\<^sub>1)
  from ev\<^sub>d_app3(2, 1) show ?case 
    using val_no_eval\<^sub>d value\<^sub>d.simps(3) by (induction rule: eval\<^sub>d.cases) blast+
qed

end