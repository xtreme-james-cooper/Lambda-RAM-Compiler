theory BigStep
  imports Termination
begin

inductive big_evald :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d \<Rightarrow> bool" (infix "\<Down>\<^sub>d" 50) where
  bevd_const [simp]: "Const\<^sub>d k \<Down>\<^sub>d Const\<^sub>d k"
| bevd_lam [simp]: "Lam\<^sub>d t e \<Down>\<^sub>d Lam\<^sub>d t e"
| bevd_app [simp]: "e\<^sub>1 \<Down>\<^sub>d Lam\<^sub>d t e\<^sub>1' \<Longrightarrow> e\<^sub>2 \<Down>\<^sub>d v\<^sub>2 \<Longrightarrow> subst\<^sub>d 0 v\<^sub>2 e\<^sub>1' \<Down>\<^sub>d v \<Longrightarrow> App\<^sub>d e\<^sub>1 e\<^sub>2 \<Down>\<^sub>d v"

inductive_cases [elim]: "Var\<^sub>d x \<Down>\<^sub>d v"
inductive_cases [elim]: "Const\<^sub>d k \<Down>\<^sub>d v"
inductive_cases [elim]: "Lam\<^sub>d t e \<Down>\<^sub>d v"
inductive_cases [elim]: "App\<^sub>d e\<^sub>1 e\<^sub>2 \<Down>\<^sub>d v"

lemma [simp]: "e \<Down>\<^sub>d v \<Longrightarrow> value\<^sub>d v"
  by (induction e v rule: big_evald.induct) simp_all

theorem deterministimb: "e \<Down>\<^sub>d v \<Longrightarrow> e \<Down>\<^sub>d v' \<Longrightarrow> v = v'"
proof (induction e v arbitrary: v' rule: big_evald.induct)
  case (bevd_const k)
  thus ?case by (induction "Const\<^sub>d k" v' rule: big_evald.induct) simp_all
next
  case (bevd_lam t e)
  thus ?case by (induction "Lam\<^sub>d t e" v' rule: big_evald.induct) simp_all
next
  case (bevd_app e\<^sub>1 t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  from bevd_app(7, 1, 2, 3, 4, 5, 6) show ?case 
    by (induction "App\<^sub>d e\<^sub>1 e\<^sub>2" v' rule: big_evald.induct) blast+
qed

lemma [simp]: "value\<^sub>d v \<Longrightarrow> v \<Down>\<^sub>d v"
  by (induction v) simp_all

lemma completeb' [simp]: "e \<leadsto>\<^sub>d e' \<Longrightarrow> e' \<Down>\<^sub>d v \<Longrightarrow> value\<^sub>d v \<Longrightarrow> e \<Down>\<^sub>d v"
proof (induction e e' arbitrary: v rule: eval\<^sub>d.induct)
  case (ev\<^sub>d_app3 e\<^sub>2 t e\<^sub>1)
  moreover hence "e\<^sub>2 \<Down>\<^sub>d e\<^sub>2" by simp
  ultimately show ?case by (metis bevd_lam bevd_app)
qed fastforce+

theorem completeb [simp]: "iter (\<leadsto>\<^sub>d) e v \<Longrightarrow> value\<^sub>d v \<Longrightarrow> e \<Down>\<^sub>d v"
  by (induction e v rule: iter.induct) simp_all

theorem progressb [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> \<exists>v. value\<^sub>d v \<and> e \<Down>\<^sub>d v"
proof -
  assume "[] \<turnstile>\<^sub>d e : t"
  then obtain v where "value\<^sub>d v \<and> iter (\<leadsto>\<^sub>d) e v" by fastforce
  thus ?thesis by fastforce
qed

theorem correctb: "e \<Down>\<^sub>d v \<Longrightarrow> iter (\<leadsto>\<^sub>d) e v"
proof (induction e v rule: big_evald.induct)
  case (bevd_app e\<^sub>1 t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  hence "iter (\<leadsto>\<^sub>d) (App\<^sub>d e\<^sub>1 e\<^sub>2) (App\<^sub>d (Lam\<^sub>d t e\<^sub>1') e\<^sub>2)" by simp
  moreover from bevd_app have "iter (\<leadsto>\<^sub>d) (App\<^sub>d (Lam\<^sub>d t e\<^sub>1') e\<^sub>2) (App\<^sub>d (Lam\<^sub>d t e\<^sub>1') v\<^sub>2)" by simp
  moreover from bevd_app have "App\<^sub>d (Lam\<^sub>d t e\<^sub>1') v\<^sub>2 \<leadsto>\<^sub>d subst\<^sub>d 0 v\<^sub>2 e\<^sub>1'" by simp
  moreover from bevd_app have "iter (\<leadsto>\<^sub>d) (subst\<^sub>d 0 v\<^sub>2 e\<^sub>1') v" by simp
  ultimately show ?case by (metis iter_append iter_step)
qed simp_all

end