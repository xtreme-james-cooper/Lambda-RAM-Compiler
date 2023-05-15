theory Termination
  imports Multisubst "../00Utils/Iteration"
begin

subsection \<open>Termination\<close>

text \<open>We are now ready to prove termination of our language. An expression terminates if there is 
some value that iterated small-step evaluation takes it to. (The \<open>val_no_eval\<^sub>d\<close> lemma ensures that 
there are no further evaluation steps once a value is reached.)\<close>

abbreviation terminating :: "expr\<^sub>d \<Rightarrow> bool" where
  "terminating e \<equiv> (\<exists>v. value\<^sub>d v \<and> iter (\<leadsto>\<^sub>d) e v)"

lemma const_terminates [simp]: "terminating (Const\<^sub>d n)"
proof
  show "value\<^sub>d (Const\<^sub>d n) \<and> iter (\<leadsto>\<^sub>d) (Const\<^sub>d n) (Const\<^sub>d n)" by simp
qed

lemma lam_terminates [simp]: "terminating (Lam\<^sub>d t e)"
proof
  show "value\<^sub>d (Lam\<^sub>d t e) \<and> iter (\<leadsto>\<^sub>d) (Lam\<^sub>d t e) (Lam\<^sub>d t e)" by simp
qed

lemma eval\<^sub>d_backwards: "iter (\<leadsto>\<^sub>d) e v \<Longrightarrow> value\<^sub>d v \<Longrightarrow> e \<leadsto>\<^sub>d e' \<Longrightarrow> iter (\<leadsto>\<^sub>d) e' v"
  by (induction e v rule: iter.induct) (metis val_no_eval\<^sub>d, metis determinism\<^sub>d)

lemma eval\<^sub>d_terminates [simp]: "e \<leadsto>\<^sub>d e' \<Longrightarrow> terminating e = terminating e'"
proof 
  assume "terminating e"
  then obtain v where V: "value\<^sub>d v \<and> iter (\<leadsto>\<^sub>d) e v" by fastforce
  moreover assume "e \<leadsto>\<^sub>d e'"
  ultimately have "value\<^sub>d v \<and> iter (\<leadsto>\<^sub>d) e' v" by (metis eval\<^sub>d_backwards)
  thus "terminating e'" by fastforce
next
  assume "terminating e'"
  then obtain v where V: "value\<^sub>d v \<and> iter (\<leadsto>\<^sub>d) e' v" by fastforce
  moreover assume "e \<leadsto>\<^sub>d e'"
  ultimately have "value\<^sub>d v \<and> iter (\<leadsto>\<^sub>d) e v" by (metis iter_step)
  thus "terminating e" by fastforce
qed


lemma eval_under_app_fst [simp]: "iter (\<leadsto>\<^sub>d) e\<^sub>1 e\<^sub>1' \<Longrightarrow> iter (\<leadsto>\<^sub>d) (App\<^sub>d e\<^sub>1 e\<^sub>2) (App\<^sub>d e\<^sub>1' e\<^sub>2)"
proof (induction e\<^sub>1 e\<^sub>1' rule: iter.induct)
  case (iter_step e\<^sub>1 e\<^sub>1' e\<^sub>1'')
  hence "App\<^sub>d e\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>d App\<^sub>d e\<^sub>1' e\<^sub>2" by simp
  moreover from iter_step have "iter (\<leadsto>\<^sub>d) (App\<^sub>d e\<^sub>1' e\<^sub>2) (App\<^sub>d e\<^sub>1'' e\<^sub>2)" by simp
  ultimately show ?case by simp
qed simp_all

lemma eval_under_app_snd [simp]: "iter (\<leadsto>\<^sub>d) e\<^sub>2 e\<^sub>2' \<Longrightarrow> value\<^sub>d e\<^sub>1 \<Longrightarrow> 
  iter (\<leadsto>\<^sub>d) (App\<^sub>d e\<^sub>1 e\<^sub>2) (App\<^sub>d e\<^sub>1 e\<^sub>2')"
proof (induction e\<^sub>2 e\<^sub>2' rule: iter.induct)
  case (iter_step e\<^sub>2 e\<^sub>2' e\<^sub>2'')
  hence "App\<^sub>d e\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>d App\<^sub>d e\<^sub>1 e\<^sub>2'" by simp
  moreover from iter_step have "iter (\<leadsto>\<^sub>d) (App\<^sub>d e\<^sub>1 e\<^sub>2') (App\<^sub>d e\<^sub>1 e\<^sub>2'')" by simp
  ultimately show ?case by simp
qed simp_all

text \<open>Just proving termination by induction over expressions, or even over typing derivations, fails
because knowing that \<open>e\<^sub>1\<close> and \<open>e\<^sub>2\<close> terminate tells us nothing about whether \<open>App\<^sub>d e\<^sub>1 e\<^sub>2\<close> terminates; 
The substitution of \<open>e\<^sub>2\<close> into \<open>e\<^sub>1\<close> can replicate the former to an arbitrary degree. Following Pierce 
[5], we instead prove a stronger property. We define a "stability" property that says an expression 
is well-typed and terminating, and also that function-typed stable expressions remain stable when 
applied to stable arguments. We then prove that every well-typed expression is stable; since all 
stable expressions terminate, all well-typed expressions are terminating.\<close>

primrec stable :: "ty \<Rightarrow> expr\<^sub>d \<Rightarrow> bool" where
  "stable Num e = (terminating e \<and> [] \<turnstile>\<^sub>d e : Num)"
| "stable (Arrow t\<^sub>1 t\<^sub>2) e = (terminating e \<and> ([] \<turnstile>\<^sub>d e : Arrow t\<^sub>1 t\<^sub>2) \<and> 
    (\<forall>e'. stable t\<^sub>1 e' \<longrightarrow> value\<^sub>d e' \<longrightarrow> stable t\<^sub>2 (App\<^sub>d e e')))"

lemma stable_typechecks: "stable t e \<Longrightarrow> [] \<turnstile>\<^sub>d e : t"
  by (induction t) simp_all

lemma stable_terminates: "stable t e \<Longrightarrow> terminating e"
  by (induction t) simp_all

lemma multisubst_var_stable [simp]: "tc_expr_context \<Gamma> es \<Longrightarrow> list_all2 stable \<Gamma> es \<Longrightarrow> 
  lookup \<Gamma> x = Some t \<Longrightarrow> stable t (multisubst es (Var\<^sub>d x))"
proof (induction \<Gamma> es arbitrary: x rule: tc_expr_context.induct)
  case (tcp_cons t' e \<Gamma> ves)
  thus ?case by (cases x) simp_all
qed simp_all

lemma stable_eval\<^sub>d: "e \<leadsto>\<^sub>d e' \<Longrightarrow> stable t e \<Longrightarrow> stable t e'"
proof (induction t arbitrary: e e')
  case (Arrow t\<^sub>1 t\<^sub>2)
  moreover have "\<And>e\<^sub>2. stable t\<^sub>1 e\<^sub>2 \<Longrightarrow> value\<^sub>d e\<^sub>2 \<Longrightarrow> stable t\<^sub>2 (App\<^sub>d e' e\<^sub>2)" 
  proof -
    fix e\<^sub>2
    assume "stable t\<^sub>1 e\<^sub>2" and "value\<^sub>d e\<^sub>2"
    with Arrow have X: "stable t\<^sub>2 (App\<^sub>d e e\<^sub>2)" by simp
    from Arrow have "App\<^sub>d e e\<^sub>2 \<leadsto>\<^sub>d App\<^sub>d e' e\<^sub>2" by simp
    with Arrow(2) X show "stable t\<^sub>2 (App\<^sub>d e' e\<^sub>2)" by simp
  qed 
  ultimately show ?case by simp
qed simp_all

lemma stable_persists: "iter (\<leadsto>\<^sub>d) e e' \<Longrightarrow> stable t e \<Longrightarrow> stable t e'"
  by (induction e e' rule: iter.induct) (simp_all add: stable_eval\<^sub>d)

lemma stable_eval\<^sub>d_back: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> e \<leadsto>\<^sub>d e' \<Longrightarrow> stable t e' \<Longrightarrow> stable t e"
proof (induction t arbitrary: e e')
  case (Arrow t\<^sub>1 t\<^sub>2)
  from Arrow have "terminating e'" by simp
  with Arrow have X: "terminating e" by fastforce
  have "\<And>e\<^sub>2. stable t\<^sub>1 e\<^sub>2 \<Longrightarrow> value\<^sub>d e\<^sub>2 \<Longrightarrow> stable t\<^sub>2 (App\<^sub>d e e\<^sub>2)" 
  proof -
    fix e\<^sub>2
    assume S: "stable t\<^sub>1 e\<^sub>2" and "value\<^sub>d e\<^sub>2"
    with Arrow have Y: "stable t\<^sub>2 (App\<^sub>d e' e\<^sub>2)" by simp
    from S have "[] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1"  by (metis stable_typechecks)
    with Arrow(3) have Z: "[] \<turnstile>\<^sub>d App\<^sub>d e e\<^sub>2 : t\<^sub>2" by simp
    from Arrow have "App\<^sub>d e e\<^sub>2 \<leadsto>\<^sub>d App\<^sub>d e' e\<^sub>2" by simp
    with Arrow Y Z show "stable t\<^sub>2 (App\<^sub>d e e\<^sub>2)" by blast
  qed
  with Arrow X show ?case by simp
qed simp_all

lemma stable_persists_back: "iter (\<leadsto>\<^sub>d) e e' \<Longrightarrow> [] \<turnstile>\<^sub>d e : t \<Longrightarrow> stable t e' \<Longrightarrow> stable t e"
proof (induction e e' rule: iter.induct)
  case (iter_step e e' e'')
  thus ?case using stable_eval\<^sub>d_back by fastforce
qed simp_all

text \<open>We prove the crucial lemma about \<open>multisubst\<close> rather than \<open>subst\<^sub>d\<close> because stability is only 
defined over closed expressions, and we need to substitute for all free variables in an arbitrary 
expression at once to get a closed term.\<close>

lemma tc_stable_multisubst [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> tc_expr_context \<Gamma> es \<Longrightarrow> list_all2 stable \<Gamma> es \<Longrightarrow> 
  stable t (multisubst es e)"
proof (induction \<Gamma> e t arbitrary: es rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_lam t\<^sub>1 \<Gamma> e t\<^sub>2)
  then obtain e' where E: "multisubst es (Lam\<^sub>d t\<^sub>1 e) = Lam\<^sub>d t\<^sub>1 e' \<and> ([t\<^sub>1] \<turnstile>\<^sub>d e' : t\<^sub>2) \<and> 
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> multisubst es (subst\<^sub>d 0 e\<^sub>2 e) = subst\<^sub>d 0 e\<^sub>2 e')" by fastforce
  moreover have "\<And>e\<^sub>2. stable t\<^sub>1 e\<^sub>2 \<Longrightarrow> value\<^sub>d e\<^sub>2 \<Longrightarrow> stable t\<^sub>2 (App\<^sub>d (Lam\<^sub>d t\<^sub>1 e') e\<^sub>2)"
  proof -
    fix e\<^sub>2
    assume S: "stable t\<^sub>1 e\<^sub>2" and V: "value\<^sub>d e\<^sub>2"
    hence E2: "[] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" by (metis stable_typechecks)
    hence T: "\<exists>t. [] \<turnstile>\<^sub>d e\<^sub>2 : t" by fastforce
    from tc\<^sub>d_lam S have "list_all2 stable (insert_at 0 t\<^sub>1 \<Gamma>) (insert_at 0 e\<^sub>2 es)" by simp
    with tc\<^sub>d_lam have "tc_expr_context (insert_at 0 t\<^sub>1 \<Gamma>) (insert_at 0 e\<^sub>2 es) \<Longrightarrow> 
      stable t\<^sub>2 (multisubst (insert_at 0 e\<^sub>2 es) e)" by blast
    hence "tc_expr_context (insert_at 0 t\<^sub>1 \<Gamma>) (insert_at 0 e\<^sub>2 es) \<Longrightarrow> 
      stable t\<^sub>2 (multisubst es (subst\<^sub>d 0 e\<^sub>2 e))" by (cases es) simp_all
    with tc\<^sub>d_lam S V T E have "stable t\<^sub>2 (subst\<^sub>d 0 e\<^sub>2 e')" by (simp add: stable_typechecks)
    moreover with V have "App\<^sub>d (Lam\<^sub>d t\<^sub>1 e') e\<^sub>2 \<leadsto>\<^sub>d subst\<^sub>d 0 e\<^sub>2 e'" by simp
    moreover from E have "[] \<turnstile>\<^sub>d Lam\<^sub>d t\<^sub>1 e' : Arrow t\<^sub>1 t\<^sub>2" by simp
    moreover with E2 have "[] \<turnstile>\<^sub>d App\<^sub>d (Lam\<^sub>d t\<^sub>1 e') e\<^sub>2 : t\<^sub>2" by simp
    ultimately show "stable t\<^sub>2 (App\<^sub>d (Lam\<^sub>d t\<^sub>1 e') e\<^sub>2)" by (metis stable_eval\<^sub>d_back)
  qed
  ultimately show ?case by simp
next
  case (tc\<^sub>d_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  hence "terminating (multisubst es e\<^sub>2)" by (metis stable_terminates)
  then obtain v\<^sub>2 where V2: "value\<^sub>d v\<^sub>2 \<and> iter (\<leadsto>\<^sub>d) (multisubst es e\<^sub>2) v\<^sub>2" by fastforce
  with tc\<^sub>d_app have V2S: "stable t\<^sub>1 v\<^sub>2" by (metis stable_persists)
  from tc\<^sub>d_app have "terminating (multisubst es e\<^sub>1)" by fastforce
  then obtain v\<^sub>1 where V1: "value\<^sub>d v\<^sub>1 \<and> iter (\<leadsto>\<^sub>d) (multisubst es e\<^sub>1) v\<^sub>1" by fastforce
  with tc\<^sub>d_app have SV: "stable (Arrow t\<^sub>1 t\<^sub>2) v\<^sub>1" by (metis stable_persists)
  with V2S V2 have "stable t\<^sub>2 (App\<^sub>d v\<^sub>1 v\<^sub>2)" by simp
  moreover from V1 V2 have "iter (\<leadsto>\<^sub>d) (App\<^sub>d v\<^sub>1 (multisubst es e\<^sub>2)) (App\<^sub>d v\<^sub>1 v\<^sub>2)" by simp
  moreover from SV have "[] \<turnstile>\<^sub>d v\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by simp
  moreover with tc\<^sub>d_app have "[] \<turnstile>\<^sub>d App\<^sub>d v\<^sub>1 (multisubst es e\<^sub>2) : t\<^sub>2" by simp
  ultimately have X: "stable t\<^sub>2 (App\<^sub>d v\<^sub>1 (multisubst es e\<^sub>2))" by (metis stable_persists_back)
  from V1 have Y: "iter (\<leadsto>\<^sub>d) (App\<^sub>d (multisubst es e\<^sub>1) (multisubst es e\<^sub>2)) 
    (App\<^sub>d v\<^sub>1 (multisubst es e\<^sub>2))" by simp
  from tc\<^sub>d_app have "[] \<turnstile>\<^sub>d multisubst es e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by simp
  moreover from tc\<^sub>d_app have "[] \<turnstile>\<^sub>d multisubst es e\<^sub>2 : t\<^sub>1" by simp
  ultimately have "[] \<turnstile>\<^sub>d App\<^sub>d (multisubst es e\<^sub>1) (multisubst es e\<^sub>2) : t\<^sub>2" by simp
  with X Y have "stable t\<^sub>2 (App\<^sub>d (multisubst es e\<^sub>1) (multisubst es e\<^sub>2))" 
    by (metis stable_persists_back)
  thus ?case by simp
qed simp_all

theorem tc_terminationd [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> terminating e"
proof -
  assume "[] \<turnstile>\<^sub>d e : t" 
  moreover have "list_all2 stable [] []" by simp
  ultimately show ?thesis 
    by (metis stable_terminates multisubst.simps(1) tcp_nil tc_stable_multisubst)
qed

end