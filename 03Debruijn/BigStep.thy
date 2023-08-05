theory BigStep
  imports Termination
begin

subsection \<open>Big-step evaluation\<close>

text \<open>Now that termination of well-typed expressions is proven, the big-step semantics are easy. We 
could simply define it as iterated small-step evaluation, but it's easier in the long run to define 
it analogously to the evaluation of our previous stage (since we subsequently need to prove the 
equivalence of evaluation across name-removal, and keeping the evaluation relations similar greatly 
helps with that) and prove the equivalence to small-step evaluation directly.\<close>

inductive big_eval\<^sub>d :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d \<Rightarrow> bool" (infix "\<Down>\<^sub>d" 50) where
  bev\<^sub>d_const [simp]: "Const\<^sub>d n \<Down>\<^sub>d Const\<^sub>d n"
| bev\<^sub>d_lam [simp]: "Lam\<^sub>d t e \<Down>\<^sub>d Lam\<^sub>d t e"
| bev\<^sub>d_app [simp]: "e\<^sub>1 \<Down>\<^sub>d Lam\<^sub>d t e\<^sub>1' \<Longrightarrow> e\<^sub>2 \<Down>\<^sub>d v\<^sub>2 \<Longrightarrow> subst\<^sub>d 0 v\<^sub>2 e\<^sub>1' \<Down>\<^sub>d v \<Longrightarrow> App\<^sub>d e\<^sub>1 e\<^sub>2 \<Down>\<^sub>d v"
| bev\<^sub>d_let [simp]: "e\<^sub>1 \<Down>\<^sub>d v\<^sub>1 \<Longrightarrow> subst\<^sub>d 0 v\<^sub>1 e\<^sub>2 \<Down>\<^sub>d v\<^sub>2 \<Longrightarrow> Let\<^sub>d e\<^sub>1 e\<^sub>2 \<Down>\<^sub>d v\<^sub>2"

inductive_cases [elim]: "Var\<^sub>d x \<Down>\<^sub>d v"
inductive_cases [elim]: "Const\<^sub>d n \<Down>\<^sub>d v"
inductive_cases [elim]: "Lam\<^sub>d t e \<Down>\<^sub>d v"
inductive_cases [elim]: "App\<^sub>d e\<^sub>1 e\<^sub>2 \<Down>\<^sub>d v"
inductive_cases [elim]: "Let\<^sub>d e\<^sub>1 e\<^sub>2 \<Down>\<^sub>d v"

text \<open>It is no surprise that two of our three standard properties, determinism and preservation, are 
simple to prove:\<close>

lemma eval\<^sub>d_to_value [simp]: "e \<Down>\<^sub>d v \<Longrightarrow> value\<^sub>d v"
  by (induction e v rule: big_eval\<^sub>d.induct) simp_all

lemma eval\<^sub>d_of_value [simp]: "value\<^sub>d v \<Longrightarrow> v \<Down>\<^sub>d v"
  by (induction v) simp_all

theorem determinism\<^sub>d\<^sub>b: "e \<Down>\<^sub>d v \<Longrightarrow> e \<Down>\<^sub>d v' \<Longrightarrow> v = v'"
proof (induction e v arbitrary: v' rule: big_eval\<^sub>d.induct)
  case (bev\<^sub>d_const n)
  thus ?case by (induction rule: big_eval\<^sub>d.cases) simp_all
next
  case (bev\<^sub>d_lam t e)
  thus ?case by (induction rule: big_eval\<^sub>d.cases) simp_all
next
  case (bev\<^sub>d_app e\<^sub>1 t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  from bev\<^sub>d_app(7, 1, 2, 3, 4, 5, 6) show ?case by (induction rule: big_eval\<^sub>d.cases) blast+
next
  case (bev\<^sub>d_let e\<^sub>1 v\<^sub>1 e\<^sub>2 v\<^sub>2 t)
  from bev\<^sub>d_let(5, 1, 2, 3, 4) show ?case by (induction rule: big_eval\<^sub>d.cases) blast+
qed

theorem preservation\<^sub>d\<^sub>b: "e \<Down>\<^sub>d v \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d v : t"
  by (induction e v arbitrary: t rule: big_eval\<^sub>d.induct) fastforce+

text \<open>Now, the correctness and completeness properties: every sequence of iterated small-steps 
ending in a value is equivalent to a big-step, and vice versa.\<close>

lemma complete\<^sub>d\<^sub>b' [simp]: "e \<leadsto>\<^sub>d e' \<Longrightarrow> e' \<Down>\<^sub>d v \<Longrightarrow> value\<^sub>d v \<Longrightarrow> e \<Down>\<^sub>d v"
proof (induction e e' arbitrary: v rule: eval\<^sub>d.induct)
  case (ev\<^sub>d_app3 e\<^sub>2 t e\<^sub>1)
  moreover hence "e\<^sub>2 \<Down>\<^sub>d e\<^sub>2" by simp
  ultimately show ?case by (metis bev\<^sub>d_lam bev\<^sub>d_app)
next
  case (ev\<^sub>d_let2 e\<^sub>1 t e\<^sub>2)
  moreover hence "e\<^sub>1 \<Down>\<^sub>d e\<^sub>1" by simp
  ultimately show ?case by simp
qed fastforce+

theorem complete\<^sub>d\<^sub>b: "iter (\<leadsto>\<^sub>d) e v \<Longrightarrow> value\<^sub>d v \<Longrightarrow> e \<Down>\<^sub>d v"
  by (induction e v rule: iter.induct) simp_all

theorem correct\<^sub>d\<^sub>b: "e \<Down>\<^sub>d v \<Longrightarrow> iter (\<leadsto>\<^sub>d) e v"
proof (induction e v rule: big_eval\<^sub>d.induct)
  case (bev\<^sub>d_app e\<^sub>1 t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  hence "iter (\<leadsto>\<^sub>d) (App\<^sub>d e\<^sub>1 e\<^sub>2) (App\<^sub>d (Lam\<^sub>d t e\<^sub>1') e\<^sub>2)" by simp
  moreover from bev\<^sub>d_app have "iter (\<leadsto>\<^sub>d) (App\<^sub>d (Lam\<^sub>d t e\<^sub>1') e\<^sub>2) (App\<^sub>d (Lam\<^sub>d t e\<^sub>1') v\<^sub>2)" by simp
  moreover from bev\<^sub>d_app have "App\<^sub>d (Lam\<^sub>d t e\<^sub>1') v\<^sub>2 \<leadsto>\<^sub>d subst\<^sub>d 0 v\<^sub>2 e\<^sub>1'" by simp
  moreover from bev\<^sub>d_app have "iter (\<leadsto>\<^sub>d) (subst\<^sub>d 0 v\<^sub>2 e\<^sub>1') v" by simp
  ultimately show ?case by (metis iter_append iter_step)
next
  case (bev\<^sub>d_let e\<^sub>1 v\<^sub>1 e\<^sub>2 v\<^sub>2)
  hence "iter (\<leadsto>\<^sub>d) (Let\<^sub>d e\<^sub>1 e\<^sub>2) (Let\<^sub>d v\<^sub>1 e\<^sub>2)" by simp
  moreover from bev\<^sub>d_let have "Let\<^sub>d v\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>d subst\<^sub>d 0 v\<^sub>1 e\<^sub>2" by simp
  moreover from bev\<^sub>d_let have "iter (\<leadsto>\<^sub>d) (subst\<^sub>d 0 v\<^sub>1 e\<^sub>2) v\<^sub>2" by simp
  ultimately show ?case by (metis iter_append iter_step)
qed simp_all

text \<open>Having proved completeness, progress for big-step evaluation is now a simple consequence of 
the termination theorem.\<close>

theorem progress\<^sub>d\<^sub>b [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> \<exists>v. value\<^sub>d v \<and> e \<Down>\<^sub>d v"
proof -
  assume "[] \<turnstile>\<^sub>d e : t"
  then obtain v where "value\<^sub>d v \<and> iter (\<leadsto>\<^sub>d) e v" by fastforce
  thus ?thesis using complete\<^sub>d\<^sub>b by fastforce
qed

end