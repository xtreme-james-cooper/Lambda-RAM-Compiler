theory Stack
  imports "../03Debruijn/DebruijnIndices"
begin

datatype frame = 
  FApp1 expr\<^sub>d
  | FApp2 expr\<^sub>d
  | FReturn

datatype stack_state = SS bool "frame list" expr\<^sub>d

inductive typecheck_stack :: "frame list \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" (infix ": _ \<rightarrow>" 50) where
  tcs_nil [simp]: "[] : t \<rightarrow> t"
| tcs_cons_app1 [simp]: "[] \<turnstile>\<^sub>d e : t\<^sub>1 \<Longrightarrow> s : t\<^sub>2 \<rightarrow> t \<Longrightarrow> FApp1 e # s : Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t"
| tcs_cons_app2 [simp]: "[] \<turnstile>\<^sub>d e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> value\<^sub>d e \<Longrightarrow> s : t\<^sub>2 \<rightarrow> t \<Longrightarrow> FApp2 e # s : t\<^sub>1 \<rightarrow> t"
| tcs_cons_ret [simp]: "s : t' \<rightarrow> t \<Longrightarrow> FReturn # s : t' \<rightarrow> t"

inductive_cases [elim]: "[] : t' \<rightarrow> t"
inductive_cases [elim]: "FApp1 e # s : t' \<rightarrow> t"
inductive_cases [elim]: "FApp2 e # s : t' \<rightarrow> t"
inductive_cases [elim]: "FReturn # s : t' \<rightarrow> t"

inductive typecheck_stack_state :: "stack_state \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>s" 50) where
  tcs_state [simp]: "s : t' \<rightarrow> t \<Longrightarrow> [] \<turnstile>\<^sub>d e : t' \<Longrightarrow> (b \<Longrightarrow> value\<^sub>d e) \<Longrightarrow> SS b s e :\<^sub>s t"

inductive_cases [elim]: "SS b s e :\<^sub>s t"

inductive evals :: "stack_state \<Rightarrow> stack_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>s" 50) where
  evs_const [simp]: "SS False s (Const\<^sub>d k) \<leadsto>\<^sub>s SS True s (Const\<^sub>d k)"
| evs_lam [simp]: "SS False s (Lam\<^sub>d t e) \<leadsto>\<^sub>s SS True s (Lam\<^sub>d t e)"
| evs_app1 [simp]: "SS False s (App\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>s SS False (FApp1 e\<^sub>2 # s) e\<^sub>1"
| evs_app2 [simp]: "SS True (FApp1 e\<^sub>2 # s) e\<^sub>1 \<leadsto>\<^sub>s SS False (FApp2 e\<^sub>1 # s) e\<^sub>2"
| evs_app3 [simp]: "SS True (FApp2 (Lam\<^sub>d t e\<^sub>1) # s) e\<^sub>2 \<leadsto>\<^sub>s SS False (FReturn # s) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)"
| evs_ret [simp]: "SS True (FReturn # s) e \<leadsto>\<^sub>s SS True s e"

lemma [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> \<exists>\<Sigma>'. SS False s e \<leadsto>\<^sub>s \<Sigma>'"
proof (induction "[] :: ty list" e t rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_const k)
  have "SS False s (Const\<^sub>d k) \<leadsto>\<^sub>s SS True s (Const\<^sub>d k)" by simp
  thus ?case by fastforce
next
  case (tc\<^sub>d_lam t\<^sub>1 e t\<^sub>2)
  have "SS False s (Lam\<^sub>d t\<^sub>1 e) \<leadsto>\<^sub>s SS True s (Lam\<^sub>d t\<^sub>1 e)" by simp
  thus ?case by fastforce
next
  case (tc\<^sub>d_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  have "SS False s (App\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>s SS False (FApp1 e\<^sub>2 # s) e\<^sub>1" by simp
  thus ?case by fastforce
qed simp_all

lemma [simp]: "s : t' \<rightarrow> t \<Longrightarrow> [] \<turnstile>\<^sub>d e : t' \<Longrightarrow> value\<^sub>d e \<Longrightarrow> s = [] \<or> (\<exists>\<Sigma>'. SS True s e \<leadsto>\<^sub>s \<Sigma>')"
proof (induction s t' t rule: typecheck_stack.induct)
  case (tcs_cons_app1 e\<^sub>2 t\<^sub>1 s t\<^sub>2 t)
  hence "SS True (FApp1 e\<^sub>2 # s) e \<leadsto>\<^sub>s SS False (FApp2 e # s) e\<^sub>2" by simp
  thus ?case by fastforce
next
  case (tcs_cons_app2 e\<^sub>1 t\<^sub>1 t\<^sub>2 s t)
  then obtain e\<^sub>1' where "e\<^sub>1 = Lam\<^sub>d t\<^sub>1 e\<^sub>1' \<and> insert_at 0 t\<^sub>1 [] \<turnstile>\<^sub>d e\<^sub>1' : t\<^sub>2" by blast
  moreover with tcs_cons_app2 have "SS True (FApp2 (Lam\<^sub>d t\<^sub>1 e\<^sub>1') # s) e \<leadsto>\<^sub>s 
    SS False (FReturn # s) (subst\<^sub>d 0 e e\<^sub>1')" by simp
  ultimately show ?case by fastforce
next 
  case (tcs_cons_ret s t')
  hence "SS True (FReturn # s) e \<leadsto>\<^sub>s SS True s e" by simp
  thus ?case by fastforce
qed simp_all

theorem progresss: "\<Sigma> :\<^sub>s t \<Longrightarrow> (\<exists>e. \<Sigma> = SS True [] e \<and> value\<^sub>d e) \<or> (\<exists>\<Sigma>'. \<Sigma> \<leadsto>\<^sub>s \<Sigma>')"
proof (induction \<Sigma> t rule: typecheck_stack_state.induct)
  case (tcs_state s t' t e b)
  thus ?case by (cases b) simp_all
qed 

theorem preservations [simp]: "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>s t \<Longrightarrow> \<Sigma>' :\<^sub>s t"
proof (induction \<Sigma> \<Sigma>' rule: evals.induct)
  case (evs_app1 s e\<^sub>1 e\<^sub>2)
  then obtain t\<^sub>1 t\<^sub>2 where "s : t\<^sub>2 \<rightarrow> t" and "[] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" and X: "[] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by blast
  hence "FApp1 e\<^sub>2 # s : Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t" by simp
  with X show ?case by simp
next
  case (evs_app2 e\<^sub>2 s e\<^sub>1)
  then obtain t\<^sub>1 t\<^sub>2 where X: "[] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" and "s : t\<^sub>2 \<rightarrow> t" and "[] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" 
   and "value\<^sub>d e\<^sub>1" by blast
  with evs_app2 have "FApp2 e\<^sub>1 # s : t\<^sub>1 \<rightarrow> t" by simp
  with X show ?case by simp
next
  case (evs_app3 t\<^sub>1 e\<^sub>1 s e\<^sub>2)
  then obtain t\<^sub>2 where "[t\<^sub>1] \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2" and X: "s : t\<^sub>2 \<rightarrow> t" and "[] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" by fastforce
  hence "[] \<turnstile>\<^sub>d subst\<^sub>d 0 e\<^sub>2 e\<^sub>1 : t\<^sub>2" by simp
  moreover from X have "FReturn # s : t\<^sub>2 \<rightarrow> t" by simp
  ultimately show ?case by simp
qed fastforce+

lemma [simp]: "iter (\<leadsto>\<^sub>s) \<Sigma> \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>s t \<Longrightarrow> \<Sigma>' :\<^sub>s t"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

theorem determinisms: "\<Sigma> \<leadsto>\<^sub>s \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>s \<Sigma>'' \<Longrightarrow> \<Sigma> :\<^sub>s t \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evals.induct)
  case (evs_const s k)
  thus ?case by (induction "SS False s (Const\<^sub>d k)" \<Sigma>'' rule: evals.induct) simp_all
next
  case (evs_lam s t e)
  thus ?case by (induction "SS False s (Lam\<^sub>d t e)" \<Sigma>'' rule: evals.induct) simp_all
next
  case (evs_app1 s e\<^sub>1 e\<^sub>2)
  thus ?case by (induction "SS False s (App\<^sub>d e\<^sub>1 e\<^sub>2)" \<Sigma>'' rule: evals.induct) simp_all
next
  case (evs_app2 e\<^sub>2 s e\<^sub>1)
  thus ?case by (induction "SS True (FApp1 e\<^sub>2 # s) e\<^sub>1" \<Sigma>'' rule: evals.induct) simp_all
next
  case (evs_app3 t e\<^sub>1 s e\<^sub>2)
  thus ?case by (induction "SS True (FApp2 (Lam\<^sub>d t e\<^sub>1) # s) e\<^sub>2" \<Sigma>'' rule: evals.induct) simp_all
next 
  case (evs_ret s e)
  thus ?case by (induction "SS True (FReturn # s) e" \<Sigma>'' rule: evals.induct) simp_all
qed

lemma [simp]: "SS b s e \<leadsto>\<^sub>s SS b' s' e' \<Longrightarrow> SS b (s @ ss) e \<leadsto>\<^sub>s SS b' (s' @ ss) e'"
  by (induction "SS b s e" "SS b' s' e'" rule: evals.induct) auto

lemma eval_under [simp]: "iter (\<leadsto>\<^sub>s) (SS b s e) (SS b' s' e') \<Longrightarrow> 
  iter (\<leadsto>\<^sub>s) (SS b (s @ ss) e) (SS b' (s' @ ss) e')"
proof (induction "SS b s e" "SS b' s' e'" arbitrary: b s e rule: iter.induct)
  case (iter_step \<Sigma>')
  then show ?case 
  proof (induction \<Sigma>' rule: stack_state.induct)
    case (SS b'' s'' e'')
    hence "SS b (s @ ss) e \<leadsto>\<^sub>s SS b'' (s'' @ ss) e''" by simp
    moreover from SS have "iter (\<leadsto>\<^sub>s) (SS b'' (s'' @ ss) e'') (SS b' (s' @ ss) e')" by simp
    ultimately show ?case by simp
  qed
qed simp_all

lemma [simp]: "s @ s' : t' \<rightarrow> t \<Longrightarrow> \<exists>t''. (s : t' \<rightarrow> t'') \<and> (s' : t'' \<rightarrow> t)"
proof (induction s arbitrary: t')
  case (Cons f s)
  thus ?case 
  proof (induction f)
    case (FApp2 e)
    then obtain t\<^sub>2 where X: "([] \<turnstile>\<^sub>d e : Arrow t' t\<^sub>2) \<and> value\<^sub>d e \<and> (s @ s' : t\<^sub>2 \<rightarrow> t)" by auto
    with FApp2 obtain t'' where "(s : t\<^sub>2 \<rightarrow> t'') \<and> (s' : t'' \<rightarrow> t)" by blast
    moreover with X have "FApp2 e # s : t' \<rightarrow> t''" by fastforce
    ultimately show ?case by blast
  qed force+
qed force+

lemma [simp]: "value\<^sub>d e \<Longrightarrow> iter (\<leadsto>\<^sub>s) (SS b s e) (SS True s e)"
proof (induction e)
  case (Const\<^sub>d x)
  thus ?case 
  proof (induction b)
    case False
    have "SS False s (Const\<^sub>d x) \<leadsto>\<^sub>s SS True s (Const\<^sub>d x)" by simp
    thus ?case by (metis iter_step iter_refl)
  qed simp_all
next
  case (Lam\<^sub>d t e)
  thus ?case
  proof (induction b)
    case False
    have "SS False s (Lam\<^sub>d t e) \<leadsto>\<^sub>s SS True s (Lam\<^sub>d t e)" by simp
    thus ?case by (metis iter_step iter_refl)
  qed simp_all
qed simp_all

end