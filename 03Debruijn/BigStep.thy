theory BigStep
  imports Termination
begin

inductive big_evald :: "dexpr \<Rightarrow> dexpr \<Rightarrow> bool" (infix "\<Down>\<^sub>d" 50) where
  bevd_const [simp]: "DConst k \<Down>\<^sub>d DConst k"
| bevd_lam [simp]: "DLam t e \<Down>\<^sub>d DLam t e"
| bevd_app [simp]: "e\<^sub>1 \<Down>\<^sub>d DLam t e\<^sub>1' \<Longrightarrow> e\<^sub>2 \<Down>\<^sub>d v\<^sub>2 \<Longrightarrow> substd 0 v\<^sub>2 e\<^sub>1' \<Down>\<^sub>d v \<Longrightarrow> DApp e\<^sub>1 e\<^sub>2 \<Down>\<^sub>d v"

inductive_cases [elim]: "DVar x \<Down>\<^sub>d v"
inductive_cases [elim]: "DConst k \<Down>\<^sub>d v"
inductive_cases [elim]: "DLam t e \<Down>\<^sub>d v"
inductive_cases [elim]: "DApp e\<^sub>1 e\<^sub>2 \<Down>\<^sub>d v"

lemma [simp]: "e \<Down>\<^sub>d v \<Longrightarrow> vald v"
  by (induction e v rule: big_evald.induct) simp_all

theorem deterministimb: "e \<Down>\<^sub>d v \<Longrightarrow> e \<Down>\<^sub>d v' \<Longrightarrow> v = v'"
proof (induction e v arbitrary: v' rule: big_evald.induct)
  case (bevd_const k)
  thus ?case by (induction "DConst k" v' rule: big_evald.induct) simp_all
next
  case (bevd_lam t e)
  thus ?case by (induction "DLam t e" v' rule: big_evald.induct) simp_all
next
  case (bevd_app e\<^sub>1 t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  from bevd_app(7, 1, 2, 3, 4, 5, 6) show ?case 
    by (induction "DApp e\<^sub>1 e\<^sub>2" v' rule: big_evald.induct) blast+
qed

lemma [simp]: "vald v \<Longrightarrow> v \<Down>\<^sub>d v"
  by (induction v) simp_all

lemma completeb' [simp]: "e \<leadsto>\<^sub>d e' \<Longrightarrow> e' \<Down>\<^sub>d v \<Longrightarrow> vald v \<Longrightarrow> e \<Down>\<^sub>d v"
proof (induction e e' arbitrary: v rule: evald.induct)
  case (evd_app3 e\<^sub>2 t e\<^sub>1)
  moreover hence "e\<^sub>2 \<Down>\<^sub>d e\<^sub>2" by simp
  ultimately show ?case by (metis bevd_lam bevd_app)
qed fastforce+

theorem completeb [simp]: "iter (\<leadsto>\<^sub>d) e v \<Longrightarrow> vald v \<Longrightarrow> e \<Down>\<^sub>d v"
  by (induction e v rule: iter.induct) simp_all

theorem progressb [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> \<exists>v. vald v \<and> e \<Down>\<^sub>d v"
proof -
  assume "[] \<turnstile>\<^sub>d e : t"
  then obtain v where "vald v \<and> iter (\<leadsto>\<^sub>d) e v" by fastforce
  thus ?thesis by fastforce
qed

theorem correctb: "e \<Down>\<^sub>d v \<Longrightarrow> iter (\<leadsto>\<^sub>d) e v"
proof (induction e v rule: big_evald.induct)
  case (bevd_app e\<^sub>1 t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  hence "iter (\<leadsto>\<^sub>d) (DApp e\<^sub>1 e\<^sub>2) (DApp (DLam t e\<^sub>1') e\<^sub>2)" by simp
  moreover from bevd_app have "iter (\<leadsto>\<^sub>d) (DApp (DLam t e\<^sub>1') e\<^sub>2) (DApp (DLam t e\<^sub>1') v\<^sub>2)" by simp
  moreover from bevd_app have "DApp (DLam t e\<^sub>1') v\<^sub>2 \<leadsto>\<^sub>d substd 0 v\<^sub>2 e\<^sub>1'" by simp
  moreover from bevd_app have "iter (\<leadsto>\<^sub>d) (substd 0 v\<^sub>2 e\<^sub>1') v" by simp
  ultimately show ?case by (metis iter_append iter_step)
qed simp_all

end