theory Stack
  imports Debruijn
begin

datatype frame = 
  FApp1 dexpr
  | FApp2 dexpr
  | FReturn

datatype stack_state = SS "frame list" dexpr

inductive typecheck_stack :: "frame list \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" (infix ": _ \<rightarrow>" 50) where
  tcs_nil [simp]: "[] : t \<rightarrow> t"
| tcs_cons_app1 [simp]: "[] \<turnstile>\<^sub>d e : t\<^sub>1 \<Longrightarrow> s : t\<^sub>2 \<rightarrow> t \<Longrightarrow> FApp1 e # s : Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t"
| tcs_cons_app2 [simp]: "[] \<turnstile>\<^sub>d e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> vald e \<Longrightarrow> s : t\<^sub>2 \<rightarrow> t \<Longrightarrow> FApp2 e # s : t\<^sub>1 \<rightarrow> t"
| tcs_cons_ret [simp]: "s : t' \<rightarrow> t \<Longrightarrow> FReturn # s : t' \<rightarrow> t"

inductive_cases [elim]: "[] : t' \<rightarrow> t"
inductive_cases [elim]: "FApp1 e # s : t' \<rightarrow> t"
inductive_cases [elim]: "FApp2 e # s : t' \<rightarrow> t"
inductive_cases [elim]: "FReturn # s : t' \<rightarrow> t"

inductive typecheck_stack_state :: "stack_state \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>s" 50) where
  tcs_state [simp]: "s : t' \<rightarrow> t \<Longrightarrow> [] \<turnstile>\<^sub>d e : t' \<Longrightarrow> SS s e :\<^sub>s t"

inductive_cases [elim]: "SS s e :\<^sub>s t"

inductive evals :: "stack_state \<Rightarrow> stack_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>s" 50) where
  evs_app1 [simp]: "SS s (DApp e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>s SS (FApp1 e\<^sub>2 # s) e\<^sub>1"
| evs_app2 [simp]: "vald e\<^sub>1 \<Longrightarrow> SS (FApp1 e\<^sub>2 # s) e\<^sub>1 \<leadsto>\<^sub>s SS (FApp2 e\<^sub>1 # s) e\<^sub>2"
| evs_app3 [simp]: "vald e\<^sub>2 \<Longrightarrow> SS (FApp2 (DLam t e\<^sub>1) # s) e\<^sub>2 \<leadsto>\<^sub>s SS (FReturn # s) (substd 0 e\<^sub>2 e\<^sub>1)"
| evs_ret [simp]: "vald e \<Longrightarrow> SS (FReturn # s) e \<leadsto>\<^sub>s SS s e"

lemma [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> \<not> vald e \<Longrightarrow> \<exists>\<Sigma>'. SS s e \<leadsto>\<^sub>s \<Sigma>'"
proof (induction "[] :: ty list" e t rule: typecheckd.induct)
  case (tcd_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  have "SS s (DApp e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>s SS (FApp1 e\<^sub>2 # s) e\<^sub>1" by simp
  then show ?case by fastforce
qed simp_all

lemma [simp]: "s : t' \<rightarrow> t \<Longrightarrow> [] \<turnstile>\<^sub>d e : t' \<Longrightarrow> vald e \<Longrightarrow> s = [] \<or> (\<exists>\<Sigma>'. SS s e \<leadsto>\<^sub>s \<Sigma>')"
proof (induction s t' t rule: typecheck_stack.induct)
  case (tcs_cons_app1 e\<^sub>2 t\<^sub>1 s t\<^sub>2 t)
  hence "SS (FApp1 e\<^sub>2 # s) e \<leadsto>\<^sub>s SS (FApp2 e # s) e\<^sub>2" by simp
  thus ?case by fastforce
next
  case (tcs_cons_app2 e\<^sub>1 t\<^sub>1 t\<^sub>2 s t)
  then obtain e\<^sub>1' where "e\<^sub>1 = DLam t\<^sub>1 e\<^sub>1' \<and> insert_at 0 t\<^sub>1 [] \<turnstile>\<^sub>d e\<^sub>1' : t\<^sub>2" by blast
  moreover with tcs_cons_app2 have "SS (FApp2 (DLam t\<^sub>1 e\<^sub>1') # s) e \<leadsto>\<^sub>s 
    SS (FReturn # s) (substd 0 e e\<^sub>1')" by simp
  ultimately show ?case by fastforce
next 
  case (tcs_cons_ret s t')
  hence "SS (FReturn # s) e \<leadsto>\<^sub>s SS s e" by simp
  thus ?case by fastforce
qed simp_all

theorem progresss: "\<Sigma> :\<^sub>s t \<Longrightarrow> (\<exists>e. \<Sigma> = SS [] e \<and> vald e) \<or> (\<exists>\<Sigma>'. \<Sigma> \<leadsto>\<^sub>s \<Sigma>')"
proof (induction \<Sigma> t rule: typecheck_stack_state.induct)
  case (tcs_state s t' t e)
  thus ?case by (cases "vald e") simp_all
qed

theorem preservations [simp]: "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>s t \<Longrightarrow> \<Sigma>' :\<^sub>s t"
proof (induction \<Sigma> \<Sigma>' rule: evals.induct)
  case (evs_app1 s e\<^sub>1 e\<^sub>2)
  then obtain t\<^sub>1 t\<^sub>2 where "s : t\<^sub>2 \<rightarrow> t" and "[] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" and X: "[] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by blast
  hence "FApp1 e\<^sub>2 # s : Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t" by simp
  with X show ?case by simp
next
  case (evs_app2 e\<^sub>1 e\<^sub>2 s)
  then obtain t\<^sub>1 t\<^sub>2 where X: "[] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" and "s : t\<^sub>2 \<rightarrow> t" and "[] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by blast
  with evs_app2 have "FApp2 e\<^sub>1 # s : t\<^sub>1 \<rightarrow> t" by simp
  with X show ?case by simp
next
  case (evs_app3 e\<^sub>2 t\<^sub>1 e\<^sub>1 s)
  then obtain t\<^sub>2 where "[t\<^sub>1] \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2" and X: "s : t\<^sub>2 \<rightarrow> t" and "[] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" by fastforce
  hence "[] \<turnstile>\<^sub>d substd 0 e\<^sub>2 e\<^sub>1 : t\<^sub>2" by simp
  moreover from X have "FReturn # s : t\<^sub>2 \<rightarrow> t" by simp
  ultimately show ?case by simp
qed fastforce+

lemma [simp]: "iter (\<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>s t \<Longrightarrow> \<Sigma>' :\<^sub>s t"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

theorem determinisms: "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>s \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evals.induct)
  case (evs_app1 s e\<^sub>1 e\<^sub>2)
  thus ?case by (induction "SS s (DApp e\<^sub>1 e\<^sub>2)" \<Sigma>'' rule: evals.induct) simp_all
next
  case (evs_app2 e\<^sub>1 e\<^sub>2 s)
  from evs_app2(2, 1) show ?case 
    by (induction "SS (FApp1 e\<^sub>2 # s) e\<^sub>1" \<Sigma>'' rule: evals.induct) auto
next
  case (evs_app3 e\<^sub>2 t e\<^sub>1 s)
  from evs_app3(2, 1) show ?case 
    by (induction "SS (FApp2 (DLam t e\<^sub>1) # s) e\<^sub>2" \<Sigma>'' rule: evals.induct) auto
next 
  case (evs_ret e s)
  from evs_ret(2, 1) show ?case 
    by (induction "SS (FReturn # s) e" \<Sigma>'' rule: evals.induct) auto
qed

lemma [simp]: "SS s e \<leadsto>\<^sub>s SS s' e' \<Longrightarrow> SS (s @ ss) e \<leadsto>\<^sub>s SS (s' @ ss) e'"
  by (induction "SS s e" "SS s' e'" rule: evals.induct) auto

lemma eval_under [simp]: "iter (\<leadsto>\<^sub>s) (SS s e) (SS s' e') \<Longrightarrow> 
  iter (\<leadsto>\<^sub>s) (SS (s @ ss) e) (SS (s' @ ss) e')"
proof (induction "SS s e" "SS s' e'" arbitrary: s e rule: iter.induct)
  case (iter_step \<Sigma>')
  then show ?case 
  proof (induction \<Sigma>' rule: stack_state.induct)
    case (SS s'' e'')
    hence "SS (s @ ss) e \<leadsto>\<^sub>s SS (s'' @ ss) e''" by simp
    moreover from SS have "iter (\<leadsto>\<^sub>s) (SS (s'' @ ss) e'') (SS (s' @ ss) e')" by simp
    ultimately show ?case by simp
  qed
qed simp_all

lemma [simp]: "s @ s' : t' \<rightarrow> t \<Longrightarrow> \<exists>t''. (s : t' \<rightarrow> t'') \<and> (s' : t'' \<rightarrow> t)"
proof (induction s arbitrary: t')
  case (Cons f s)
  thus ?case 
  proof (induction f)
    case (FApp2 e)
    then obtain t\<^sub>2 where X: "([] \<turnstile>\<^sub>d e : Arrow t' t\<^sub>2) \<and> vald e \<and> (s @ s' : t\<^sub>2 \<rightarrow> t)" by auto
    with FApp2 obtain t'' where "(s : t\<^sub>2 \<rightarrow> t'') \<and> (s' : t'' \<rightarrow> t)" by blast
    moreover with X have "FApp2 e # s : t' \<rightarrow> t''" by fastforce
    ultimately show ?case by blast
  qed force+
qed force+

end