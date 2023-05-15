theory StackConversion
  imports Stack
begin

fun unwind' :: "frame\<^sub>k list \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "unwind' [] e = e"
| "unwind' (FApp1\<^sub>k e\<^sub>2 # s) e = unwind' s (App\<^sub>d e e\<^sub>2)"
| "unwind' (FApp2\<^sub>k e\<^sub>1 # s) e = unwind' s (App\<^sub>d e\<^sub>1 e)"
| "unwind' (FReturn\<^sub>k # s) e = unwind' s e"

primrec unwind :: "state\<^sub>k \<Rightarrow> expr\<^sub>d" where
  "unwind (S\<^sub>k b s e) = unwind' s e"

lemma [simp]: "s :\<^sub>k t' \<rightarrow> t \<Longrightarrow> [] \<turnstile>\<^sub>d e : t' \<Longrightarrow> [] \<turnstile>\<^sub>d unwind' s e : t"
  by (induction s t' t arbitrary: e rule: typing_stack\<^sub>k.induct) simp_all

theorem typesafed [simp]: "\<Sigma> :\<^sub>k t \<Longrightarrow> [] \<turnstile>\<^sub>d unwind \<Sigma> : t"
  by (induction \<Sigma> t rule: typing_state\<^sub>k.induct) simp_all

lemma [simp]: "s :\<^sub>k t' \<rightarrow> t \<Longrightarrow> e \<leadsto>\<^sub>d e' \<Longrightarrow> unwind' s e \<leadsto>\<^sub>d unwind' s e'"
  by (induction s t' t arbitrary: e e' rule: typing_stack\<^sub>k.induct) simp_all

theorem correctd: "\<Sigma> \<leadsto>\<^sub>k \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>k t \<Longrightarrow> iter (\<leadsto>\<^sub>d) (unwind \<Sigma>) (unwind \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>k.induct)
  case (ev\<^sub>k_app3 t\<^sub>1 e\<^sub>1 s e\<^sub>2)
  then obtain t\<^sub>2 where "(s :\<^sub>k t\<^sub>2 \<rightarrow> t) \<and> value\<^sub>d e\<^sub>2" by blast
  moreover hence "App\<^sub>d (Lam\<^sub>d t\<^sub>1 e\<^sub>1) e\<^sub>2 \<leadsto>\<^sub>d subst\<^sub>d 0 e\<^sub>2 e\<^sub>1" by simp
  ultimately have "unwind' s (App\<^sub>d (Lam\<^sub>d t\<^sub>1 e\<^sub>1) e\<^sub>2) \<leadsto>\<^sub>d unwind' s (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)" by auto
  thus ?case by simp
qed simp_all

primrec all_returns :: "frame\<^sub>k list \<Rightarrow> bool" where
  "all_returns [] = True"
| "all_returns (r # rs) = (r = FReturn\<^sub>k \<and> all_returns rs)"

lemma unwind_returns [elim]: "all_returns sr \<Longrightarrow> unwind' sr e = e"
  by (induction sr) (simp_all add: all_returns_def)

lemma [dest]: "FApp1\<^sub>k e # sr :\<^sub>k t' \<rightarrow> t \<Longrightarrow> all_returns sr \<Longrightarrow> 
    (\<And>t\<^sub>1. t' = Arrow t\<^sub>1 t \<Longrightarrow> [] \<turnstile>\<^sub>d e : t\<^sub>1 \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction sr) fastforce+

lemma [dest]: "FApp2\<^sub>k e # sr :\<^sub>k t' \<rightarrow> t \<Longrightarrow> all_returns sr \<Longrightarrow> 
    ([] \<turnstile>\<^sub>d e : Arrow t' t \<Longrightarrow> value\<^sub>d e \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction sr) fastforce+

lemma [dest]: "sr @ s :\<^sub>k t' \<rightarrow> t \<Longrightarrow> all_returns sr \<Longrightarrow> (s :\<^sub>k t' \<rightarrow> t \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction sr) fastforce+

lemma [dest]: "App\<^sub>d e\<^sub>1 e\<^sub>2 = unwind' s e \<Longrightarrow> (all_returns s \<and> e = App\<^sub>d e\<^sub>1 e\<^sub>2) \<or> 
  (\<exists>s' sr. all_returns sr \<and> ((s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e) \<or> 
    (s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e)))"
proof (induction s e rule: unwind'.induct)
  case (2 e\<^sub>2' s e)
  thus ?case
  proof (cases "all_returns s \<and> App\<^sub>d e e\<^sub>2' = App\<^sub>d e\<^sub>1 e\<^sub>2")
    case False
    with 2 obtain s' sr where S: "all_returns sr \<and> ((s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> 
      e\<^sub>1 = unwind' s' (App\<^sub>d e e\<^sub>2')) \<or> (s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' (App\<^sub>d e e\<^sub>2')))" 
        by fastforce
    thus ?thesis
    proof (cases "s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' (App\<^sub>d e e\<^sub>2')")
      case False
      with S have "all_returns sr \<and> s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' (App\<^sub>d e e\<^sub>2')" by simp
      moreover hence "FApp1\<^sub>k e\<^sub>2' # s' @ FApp2\<^sub>k e\<^sub>1 # sr = (FApp1\<^sub>k e\<^sub>2' # s') @ FApp2\<^sub>k e\<^sub>1 # sr \<and> 
        unwind' s' (App\<^sub>d e e\<^sub>2') = unwind' (FApp1\<^sub>k e\<^sub>2' # s') e" by simp
      ultimately show ?thesis by blast
    qed fastforce+
  qed fastforce+
next
  case (3 e\<^sub>1' s e)
  thus ?case
  proof (cases "all_returns s \<and> App\<^sub>d e\<^sub>1' e = App\<^sub>d e\<^sub>1 e\<^sub>2")
    case False
    with 3 obtain s' sr where S: "all_returns sr \<and> ((s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> 
      e\<^sub>1 = unwind' s' (App\<^sub>d e\<^sub>1' e)) \<or> (s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' (App\<^sub>d e\<^sub>1' e)))" 
        by fastforce
    thus ?thesis
    proof (cases "s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' (App\<^sub>d e\<^sub>1' e)")
      case False
      with S have "all_returns sr \<and> s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' (App\<^sub>d e\<^sub>1' e)" by simp
      moreover hence "FApp2\<^sub>k e\<^sub>1' # s' @ FApp2\<^sub>k e\<^sub>1 # sr = (FApp2\<^sub>k e\<^sub>1' # s') @ FApp2\<^sub>k e\<^sub>1 # sr \<and> 
        e\<^sub>2 = unwind' (FApp2\<^sub>k e\<^sub>1' # s') e" by simp
      ultimately show ?thesis by blast
    qed fastforce+
  qed fastforce+
next
  case (4 s e)
  thus ?case
  proof (cases "all_returns s \<and> e = App\<^sub>d e\<^sub>1 e\<^sub>2")
    case False
    with 4 obtain s' sr where S: "all_returns sr \<and> ((s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e) \<or> 
      (s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e))" by fastforce
    thus ?thesis
    proof (cases "s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e")
      case False
      with S have "all_returns sr \<and> s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e" by simp
      moreover hence "FReturn\<^sub>k # s' @ FApp2\<^sub>k e\<^sub>1 # sr = (FReturn\<^sub>k # s') @ FApp2\<^sub>k e\<^sub>1 # sr \<and> 
        e\<^sub>2 = unwind' (FReturn\<^sub>k # s') e" by simp
      ultimately show ?thesis by blast
    qed fastforce+
  qed fastforce+
qed simp_all

lemma [simp]: "value\<^sub>d v \<Longrightarrow> v = unwind' s e \<Longrightarrow> all_returns s \<and> e = v"
  by (induction s e rule: unwind'.induct) simp_all

lemma [simp]: "value\<^sub>d v \<Longrightarrow> v = unwind \<Sigma> \<Longrightarrow> \<exists>b s. \<Sigma> = S\<^sub>k b s v \<and> all_returns s"
  by (induction \<Sigma>) simp_all

lemma [simp]: "all_returns sr \<Longrightarrow> unwind' (s @ FApp1\<^sub>k e\<^sub>2 # sr) e = App\<^sub>d (unwind' s e) e\<^sub>2"
  by (induction s e rule: unwind'.induct) auto

lemma [simp]: "all_returns sr \<Longrightarrow> unwind' (s @ FApp2\<^sub>k e\<^sub>1 # sr) e = App\<^sub>d e\<^sub>1 (unwind' s e)"
  by (induction s e rule: unwind'.induct) auto

lemma eval_returns [simp]: "all_returns sr \<Longrightarrow> value\<^sub>d v \<Longrightarrow> iter (\<leadsto>\<^sub>k) (S\<^sub>k b (sr @ s) v) (S\<^sub>k True s v)"
proof (induction sr arbitrary: b)
  case (Cons a sr)
  hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (FReturn\<^sub>k # sr @ s) v) (S\<^sub>k True (FReturn\<^sub>k # sr @ s) v)" by simp
  hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (FReturn\<^sub>k # sr @ s) v) (S\<^sub>k True (sr @ s) v)" by simp
  moreover from Cons have "iter (\<leadsto>\<^sub>k) (S\<^sub>k True (sr @ s) v) (S\<^sub>k True s v)" by simp
  ultimately have "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (FReturn\<^sub>k # sr @ s) v) (S\<^sub>k True s v)" by (metis iter_append)
  with Cons show ?case by simp
qed simp_all

lemma [simp]: "unwind' s e \<leadsto>\<^sub>d e' \<Longrightarrow> s :\<^sub>k t' \<rightarrow> t \<Longrightarrow> [] \<turnstile>\<^sub>d e : tt \<Longrightarrow> (b \<Longrightarrow> value\<^sub>d e) \<Longrightarrow>
  \<exists>b' s' e''. iter (\<leadsto>\<^sub>k) (S\<^sub>k b s e) (S\<^sub>k b' s' e'') \<and> e' = unwind' s' e''"
proof (induction "unwind' s e" e' arbitrary: b s e t tt rule: eval\<^sub>d.induct)
  case (ev\<^sub>d_app1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
  thus ?case
  proof (cases "all_returns s \<and> e = App\<^sub>d e\<^sub>1 e\<^sub>2")
    case True
    with ev\<^sub>d_app1 have B: "\<not>b" by (cases b) simp_all
    from ev\<^sub>d_app1 True obtain t\<^sub>1 where T1: "([] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 tt) \<and> ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1)" by blast
    have "[] :\<^sub>k t' \<rightarrow> t'" by simp
    with ev\<^sub>d_app1 B T1 obtain b' s' e'' where E: "iter (\<leadsto>\<^sub>k) (S\<^sub>k False [] e\<^sub>1) (S\<^sub>k b' s' e'') \<and> 
      e\<^sub>1' = unwind' s' e''" by fastforce
    hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k False ([] @ FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1) (S\<^sub>k b' (s' @ FApp1\<^sub>k e\<^sub>2 # s) e'')" 
      by (metis eval\<^sub>k_under_iter)
    hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k False (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1) (S\<^sub>k b' (s' @ FApp1\<^sub>k e\<^sub>2 # s) e'')" by simp
    hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k False s (App\<^sub>d e\<^sub>1 e\<^sub>2)) (S\<^sub>k b' (s' @ FApp1\<^sub>k e\<^sub>2 # s) e'')" 
      by (metis ev\<^sub>k_app1 iter_step)
    with True B E show ?thesis by fastforce
  next
    case False
    with ev\<^sub>d_app1 obtain s' sr where S: "all_returns sr \<and> 
      ((s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e) \<or> 
        (s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e))" by fast
    thus ?thesis
    proof (cases "s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e")
      case True
      with ev\<^sub>d_app1 obtain t'' where "(s' :\<^sub>k t' \<rightarrow> t'') \<and> (FApp1\<^sub>k e\<^sub>2 # sr :\<^sub>k t'' \<rightarrow> t)" by fastforce
      with ev\<^sub>d_app1 True obtain b' ss' e'' where S': "iter (\<leadsto>\<^sub>k) (S\<^sub>k b s' e) (S\<^sub>k b' ss' e'') \<and> 
        e\<^sub>1' = unwind' ss' e''" by blast
      hence X: "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s' @ FApp1\<^sub>k e\<^sub>2 # sr) e) (S\<^sub>k b' (ss' @ FApp1\<^sub>k e\<^sub>2 # sr) e'')" by simp
      from S S' have "App\<^sub>d e\<^sub>1' e\<^sub>2 = unwind' (ss' @ FApp1\<^sub>k e\<^sub>2 # sr) e''" by simp
      with True X show ?thesis by blast
    next
      case False
      with S have "s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e" by simp
      with ev\<^sub>d_app1 obtain t\<^sub>1 where "(s' :\<^sub>k t' \<rightarrow> t\<^sub>1) \<and> (FApp2\<^sub>k e\<^sub>1 # sr :\<^sub>k t\<^sub>1 \<rightarrow> t)" by fastforce
      with S have "([] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t) \<and> value\<^sub>d e\<^sub>1" by fastforce
      with ev\<^sub>d_app1 show ?thesis by (metis val_no_eval\<^sub>d)
    qed
  qed
next
  case (ev\<^sub>d_app2 e\<^sub>1 e\<^sub>2 e\<^sub>2')
  thus ?case
  proof (cases "all_returns s \<and> e = App\<^sub>d e\<^sub>1 e\<^sub>2")
    case True
    with ev\<^sub>d_app2 have B: "\<not>b" by (cases b) simp_all
    from ev\<^sub>d_app2 True obtain t\<^sub>1 where T: "([] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 tt) \<and> ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1)" by blast
    with ev\<^sub>d_app2 B obtain b' s' e'' where E: "iter (\<leadsto>\<^sub>k) (S\<^sub>k False [] e\<^sub>2) (S\<^sub>k b' s' e'') \<and> 
      e\<^sub>2' = unwind' s' e''" by (metis unwind'.simps(1) tcs\<^sub>k_nil)
    hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k False (FApp2\<^sub>k e\<^sub>1 # s) e\<^sub>2) (S\<^sub>k b' (s' @ FApp2\<^sub>k e\<^sub>1 # s) e'')" 
      by (metis eval\<^sub>k_under_iter append_Nil)
    moreover have "S\<^sub>k False s (App\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>k S\<^sub>k False (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1" by simp
    moreover from ev\<^sub>d_app2 have "iter (\<leadsto>\<^sub>k) (S\<^sub>k False (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1) (S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1)" 
      by simp
    moreover have "S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1 \<leadsto>\<^sub>k S\<^sub>k False (FApp2\<^sub>k e\<^sub>1 # s) e\<^sub>2" by simp
    ultimately have "iter (\<leadsto>\<^sub>k) (S\<^sub>k False s (App\<^sub>d e\<^sub>1 e\<^sub>2)) (S\<^sub>k b' (s' @ FApp2\<^sub>k e\<^sub>1 # s) e'')" 
      by (metis iter_step iter_append)
    with True B E show ?thesis by fastforce
  next
    case False
    with ev\<^sub>d_app2 obtain s' sr where S: "all_returns sr \<and> 
      ((s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e) \<or> 
        (s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e))" by blast
    thus ?thesis
    proof (cases "s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> e\<^sub>1 = unwind' s' e")
      case True
      with ev\<^sub>d_app2 have S': "all_returns s' \<and> e = e\<^sub>1" by simp 
      with ev\<^sub>d_app2 True S obtain t\<^sub>1 where T: "t' = Arrow t\<^sub>1 t \<and> [] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" by blast
      have X: "e\<^sub>2 = unwind' [] e\<^sub>2" by simp
      have E: "[] :\<^sub>k t' \<rightarrow> t'" by simp
      have "False \<Longrightarrow> value\<^sub>d e\<^sub>2" by simp
      with ev\<^sub>d_app2 T X E obtain b'' s'' e'' where E: "iter (\<leadsto>\<^sub>k) (S\<^sub>k False [] e\<^sub>2) (S\<^sub>k b'' s'' e'') \<and> 
        e\<^sub>2' = unwind' s'' e''" by blast
      hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k False (FApp2\<^sub>k e\<^sub>1 # sr) e\<^sub>2) (S\<^sub>k b'' (s'' @ FApp2\<^sub>k e\<^sub>1 # sr) e'')" 
        using eval\<^sub>k_under_iter by fastforce
      moreover from ev\<^sub>d_app2 have "S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # sr) e\<^sub>1 \<leadsto>\<^sub>k S\<^sub>k False (FApp2\<^sub>k e\<^sub>1 # sr) e\<^sub>2" by simp
      moreover from ev\<^sub>d_app2 S' have "iter (\<leadsto>\<^sub>k) (S\<^sub>k True (s' @ FApp1\<^sub>k e\<^sub>2 # sr) e\<^sub>1) 
        (S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # sr) e\<^sub>1)" by simp
      moreover from ev\<^sub>d_app2 S' have "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s' @ FApp1\<^sub>k e\<^sub>2 # sr) e\<^sub>1) 
        (S\<^sub>k True (s' @ FApp1\<^sub>k e\<^sub>2 # sr) e\<^sub>1)" by simp
      ultimately have Y: "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s' @ FApp1\<^sub>k e\<^sub>2 # sr) e\<^sub>1) 
        (S\<^sub>k b'' (s'' @ FApp2\<^sub>k e\<^sub>1 # sr) e'')" by (metis iter_step iter_append)
      from S E have "App\<^sub>d e\<^sub>1 e\<^sub>2' = unwind' (s'' @ FApp2\<^sub>k e\<^sub>1 # sr) e''" by simp
      with True S' Y show ?thesis by auto
    next
      case False
      with S have S': "s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unwind' s' e" by simp
      with ev\<^sub>d_app2 obtain t\<^sub>1 where "(s' :\<^sub>k t' \<rightarrow> t\<^sub>1) \<and> (FApp2\<^sub>k e\<^sub>1 # sr :\<^sub>k t\<^sub>1 \<rightarrow> t)" by fastforce
      with ev\<^sub>d_app2 S' obtain b'' s'' e'' where E: "iter (\<leadsto>\<^sub>k) (S\<^sub>k b s' e) (S\<^sub>k b'' s'' e'') \<and> 
        e\<^sub>2' = unwind' s'' e''" by blast
      hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s' @ FApp2\<^sub>k e\<^sub>1 # sr) e) (S\<^sub>k b'' (s'' @ FApp2\<^sub>k e\<^sub>1 # sr) e'')" by simp
      with S S' E show ?thesis by fastforce
    qed
  qed
next
  case (ev\<^sub>d_app3 e\<^sub>2 t\<^sub>1 e\<^sub>1)
  thus ?case
  proof (cases "all_returns s \<and> e = App\<^sub>d (Lam\<^sub>d t\<^sub>1 e\<^sub>1) e\<^sub>2")
    case True
    with ev\<^sub>d_app3 have B: "\<not>b" by (cases b) simp_all
    have "S\<^sub>k False s (App\<^sub>d (Lam\<^sub>d t\<^sub>1 e\<^sub>1) e\<^sub>2) \<leadsto>\<^sub>k S\<^sub>k False (FApp1\<^sub>k e\<^sub>2 # s) (Lam\<^sub>d t\<^sub>1 e\<^sub>1)" by simp
    moreover have "S\<^sub>k False (FApp1\<^sub>k e\<^sub>2 # s) (Lam\<^sub>d t\<^sub>1 e\<^sub>1) \<leadsto>\<^sub>k S\<^sub>k True  (FApp1\<^sub>k e\<^sub>2 # s) (Lam\<^sub>d t\<^sub>1 e\<^sub>1)" 
      by simp
    moreover have "S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # s) (Lam\<^sub>d t\<^sub>1 e\<^sub>1) \<leadsto>\<^sub>k S\<^sub>k False (FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # s) e\<^sub>2" 
      by simp
    moreover from ev\<^sub>d_app3 have "iter (\<leadsto>\<^sub>k) (S\<^sub>k False (FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # s) e\<^sub>2) 
      (S\<^sub>k True (FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # s) e\<^sub>2)" by simp
    moreover have "S\<^sub>k True (FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # s) e\<^sub>2 \<leadsto>\<^sub>k S\<^sub>k False (FReturn\<^sub>k # s) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)" 
      by simp
    ultimately have X: "iter (\<leadsto>\<^sub>k) (S\<^sub>k False s (App\<^sub>d (Lam\<^sub>d t\<^sub>1 e\<^sub>1) e\<^sub>2)) 
      (S\<^sub>k False (FReturn\<^sub>k # s) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1))" by (metis iter_step iter_refl iter_append)
    from True have "subst\<^sub>d 0 e\<^sub>2 e\<^sub>1 = unwind' (FReturn\<^sub>k # s) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)"
      using unwind_returns by simp
    with True B X show ?thesis by fastforce
  next
    case False
    with ev\<^sub>d_app3 obtain s' sr where S: "all_returns sr \<and> 
      ((s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> Lam\<^sub>d t\<^sub>1 e\<^sub>1 = unwind' s' e) \<or> 
        (s = s' @ FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # sr \<and> e\<^sub>2 = unwind' s' e))" by blast
    thus ?thesis
    proof (cases "s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<and> Lam\<^sub>d t\<^sub>1 e\<^sub>1 = unwind' s' e")
      case True
      moreover have "value\<^sub>d (Lam\<^sub>d t\<^sub>1 e\<^sub>1)" by simp
      ultimately have S': "all_returns s' \<and> e = Lam\<^sub>d t\<^sub>1 e\<^sub>1" by simp
      have "S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # sr) (Lam\<^sub>d t\<^sub>1 e\<^sub>1) \<leadsto>\<^sub>k S\<^sub>k False (FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2" by simp
      moreover from ev\<^sub>d_app3 have "iter (\<leadsto>\<^sub>k) (S\<^sub>k False (FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2) 
        (S\<^sub>k True (FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2)" by simp
      moreover from ev\<^sub>d_app3 have "S\<^sub>k True (FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2 \<leadsto>\<^sub>k 
        S\<^sub>k False (FReturn\<^sub>k # sr) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)" by simp
      moreover from S' have "iter (\<leadsto>\<^sub>k) (S\<^sub>k True (s' @ FApp1\<^sub>k e\<^sub>2 # sr) (Lam\<^sub>d t\<^sub>1 e\<^sub>1)) 
        (S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # sr) (Lam\<^sub>d t\<^sub>1 e\<^sub>1))" by simp
      moreover have "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s' @ FApp1\<^sub>k e\<^sub>2 # sr) (Lam\<^sub>d t\<^sub>1 e\<^sub>1)) 
        (S\<^sub>k True (s' @ FApp1\<^sub>k e\<^sub>2 # sr) (Lam\<^sub>d t\<^sub>1 e\<^sub>1))" by simp
      ultimately have X: "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s' @ FApp1\<^sub>k e\<^sub>2 # sr) (Lam\<^sub>d t\<^sub>1 e\<^sub>1)) 
        (S\<^sub>k False (FReturn\<^sub>k # sr) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1))" by (metis iter_step iter_refl iter_append)
      from S True have "subst\<^sub>d 0 e\<^sub>2 e\<^sub>1 = unwind' (FReturn\<^sub>k # sr) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)" 
        using unwind_returns by simp
      with True S' X show ?thesis by fastforce
    next
      case False
      with S ev\<^sub>d_app3 have S': "all_returns s' \<and> e = e\<^sub>2" by simp
      from ev\<^sub>d_app3 have "S\<^sub>k True (FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2 \<leadsto>\<^sub>k 
        S\<^sub>k False (FReturn\<^sub>k # sr) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)" by simp
      hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k True (FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2) 
        (S\<^sub>k False (FReturn\<^sub>k # sr) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1))" by (metis iter_step iter_refl)
      moreover from ev\<^sub>d_app3 S' have "iter (\<leadsto>\<^sub>k) (S\<^sub>k True (s' @ FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2) 
        (S\<^sub>k True (FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2)" by simp
      moreover from ev\<^sub>d_app3 have "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s' @ FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2) 
        (S\<^sub>k True (s' @ FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2)" by simp
      ultimately have X: "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s' @ FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # sr) e\<^sub>2) 
        (S\<^sub>k False (FReturn\<^sub>k # sr) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1))" by (metis iter_append)
      from S have "subst\<^sub>d 0 e\<^sub>2 e\<^sub>1 = unwind' (FReturn\<^sub>k # sr) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)" 
        using unwind_returns by simp
      with S False S' X show ?thesis by metis
    qed
  qed
qed

theorem completed [simp]: "\<Sigma> :\<^sub>k t \<Longrightarrow> unwind \<Sigma> \<leadsto>\<^sub>d e' \<Longrightarrow> \<exists>\<Sigma>'. iter (\<leadsto>\<^sub>k) \<Sigma> \<Sigma>' \<and> e' = unwind \<Sigma>'"
proof (induction \<Sigma> t rule: typing_state\<^sub>k.induct)
  case (tc_state\<^sub>k s t' t e b)
  then obtain b' s' e'' where "iter (\<leadsto>\<^sub>k) (S\<^sub>k b s e) (S\<^sub>k b' s' e'') \<and> e' = unwind' s' e''" by fastforce
  thus ?case by fastforce
qed

lemma [simp]: "iter (\<leadsto>\<^sub>d) (unwind \<Sigma>) e' \<Longrightarrow> \<Sigma> :\<^sub>k t \<Longrightarrow> \<exists>\<Sigma>'. iter (\<leadsto>\<^sub>k) \<Sigma> \<Sigma>' \<and> e' = unwind \<Sigma>'"
proof (induction "unwind \<Sigma>" e' arbitrary: \<Sigma> rule: iter.induct)
  case (iter_step e' e'')
  moreover then obtain \<Sigma>' where S: "iter (\<leadsto>\<^sub>k) \<Sigma> \<Sigma>' \<and> e' = unwind \<Sigma>'" by fastforce
  moreover with iter_step have "\<Sigma>' :\<^sub>k t" by fastforce
  ultimately obtain \<Sigma>'' where "iter (\<leadsto>\<^sub>k) \<Sigma>' \<Sigma>'' \<and> e'' = unwind \<Sigma>''" by fastforce
  with S have "iter (\<leadsto>\<^sub>k) \<Sigma> \<Sigma>'' \<and> e'' = unwind \<Sigma>''" by (metis iter_append)
  then show ?case by fastforce
qed force+

lemma [simp]: "iter (\<leadsto>\<^sub>d) e v \<Longrightarrow> [] \<turnstile>\<^sub>d e : t \<Longrightarrow> value\<^sub>d v \<Longrightarrow> 
  iter (\<leadsto>\<^sub>k) (S\<^sub>k False [FReturn\<^sub>k] e) (S\<^sub>k True [] v)"
proof -
  assume "[] \<turnstile>\<^sub>d e : t"
  hence "S\<^sub>k False [FReturn\<^sub>k] e :\<^sub>k t" by (metis tcs\<^sub>k_nil tcs\<^sub>k_cons_ret tc_state\<^sub>k)
  moreover assume "iter (\<leadsto>\<^sub>d) e v"
  ultimately obtain \<Sigma>' where S: "iter (\<leadsto>\<^sub>k) (S\<^sub>k False [FReturn\<^sub>k] e) \<Sigma>' \<and> v = unwind \<Sigma>'" by fastforce
  moreover assume V: "value\<^sub>d v"
  ultimately obtain b sr where "\<Sigma>' = S\<^sub>k b (sr @ []) v \<and> all_returns sr" by fastforce
  moreover with V have "iter (\<leadsto>\<^sub>k) \<Sigma>' (S\<^sub>k True [] v)" by (metis eval_returns)
  with S show "iter (\<leadsto>\<^sub>k) (S\<^sub>k False [FReturn\<^sub>k] e) (S\<^sub>k True [] v)" by (metis iter_append)
qed

end