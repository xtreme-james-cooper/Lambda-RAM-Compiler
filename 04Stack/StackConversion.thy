theory StackConversion
  imports Stack
begin

subsection \<open>Stack conversion\<close>

text \<open>Now we define stack conversion. There is no good way to define it in a forward direction, 
since most expressions have more than one possible equivalent stack state, and even picking one 
arbitrarily - the one with an empty stack, say - would fail because the stack evaluation relation 
only has an empty stack at the very beginning and end of evaluation. Instead, we define it 
backwards, which is simple to write, but will give us trouble with our reconstruction lemmas later.\<close>

fun unstack' :: "frame\<^sub>k list \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "unstack' [] e = e"
| "unstack' (FApp1\<^sub>k e\<^sub>2 # s) e = unstack' s (App\<^sub>d e e\<^sub>2)"
| "unstack' (FApp2\<^sub>k e\<^sub>1 # s) e = unstack' s (App\<^sub>d e\<^sub>1 e)"
| "unstack' (FLet\<^sub>k e\<^sub>2 # s) e = unstack' s (Let\<^sub>d e e\<^sub>2)"
| "unstack' (FPop\<^sub>k # s) e = unstack' s e"
| "unstack' (FReturn\<^sub>k # s) e = unstack' s e"

lemma typesafe\<^sub>k' [simp]: "s :\<^sub>k t' \<rightarrow> t \<Longrightarrow> [] \<turnstile>\<^sub>d e : t' \<Longrightarrow> [] \<turnstile>\<^sub>d unstack' s e : t"
  by (induction s t' t arbitrary: e rule: typing_stack\<^sub>k.induct) simp_all

lemma unstack'_eval [simp]: "s :\<^sub>k t' \<rightarrow> t \<Longrightarrow> e \<leadsto>\<^sub>d e' \<Longrightarrow> unstack' s e \<leadsto>\<^sub>d unstack' s e'"
  by (induction s t' t arbitrary: e e' rule: typing_stack\<^sub>k.induct) simp_all

text \<open>Converting a full state is also simple. Once we have that, typesafety and completeness follow 
immediately. Note the use of \<open>iter\<close> in the completeness theorem. Actually, it will only ever be zero 
or one \<open>\<leadsto>\<^sub>d\<close> steps for each \<open>\<leadsto>\<^sub>k\<close> step, since the redex-search steps don't change the unstacked 
expression, and reduction steps are equivalent to a single evaluation step; but as mentioned when we 
defined \<open>iter\<close>, we reuse it for this sort of "zero or one" relation as well.\<close>

primrec unstack :: "state\<^sub>k \<Rightarrow> expr\<^sub>d" where
  "unstack (S\<^sub>k b s e) = unstack' s e"

theorem typesafe\<^sub>k [simp]: "\<Sigma>\<^sub>k :\<^sub>k t \<Longrightarrow> [] \<turnstile>\<^sub>d unstack \<Sigma>\<^sub>k : t"
  by (induction \<Sigma>\<^sub>k t rule: typing_state\<^sub>k.induct) simp_all

theorem complete\<^sub>k: "\<Sigma>\<^sub>k \<leadsto>\<^sub>k \<Sigma>\<^sub>k' \<Longrightarrow> \<Sigma>\<^sub>k :\<^sub>k t \<Longrightarrow> iter (\<leadsto>\<^sub>d) (unstack \<Sigma>\<^sub>k) (unstack \<Sigma>\<^sub>k')"
proof (induction \<Sigma>\<^sub>k \<Sigma>\<^sub>k' rule: eval\<^sub>k.induct)
  case (ev\<^sub>k_app3 t\<^sub>1 e\<^sub>1 s e\<^sub>2)
  then obtain t\<^sub>2 where "(s :\<^sub>k t\<^sub>2 \<rightarrow> t) \<and> value\<^sub>d e\<^sub>2" by blast
  moreover hence "App\<^sub>d (Lam\<^sub>d t\<^sub>1 e\<^sub>1) e\<^sub>2 \<leadsto>\<^sub>d subst\<^sub>d 0 e\<^sub>2 e\<^sub>1" by simp
  ultimately have "unstack' s (App\<^sub>d (Lam\<^sub>d t\<^sub>1 e\<^sub>1) e\<^sub>2) \<leadsto>\<^sub>d unstack' s (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)" by auto
  thus ?case by simp
next
  case (ev\<^sub>k_let2 e\<^sub>2 s e\<^sub>1)
  then obtain t\<^sub>1 t\<^sub>2 where "([t\<^sub>1] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>2) \<and> (s :\<^sub>k t\<^sub>2 \<rightarrow> t) \<and> ([] \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>1) \<and> value\<^sub>d e\<^sub>1"
    by fastforce
  moreover hence "Let\<^sub>d e\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>d subst\<^sub>d 0 e\<^sub>1 e\<^sub>2" by simp
  ultimately have "unstack' s (Let\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>d unstack' s (subst\<^sub>d 0 e\<^sub>1 e\<^sub>2)" by auto
  thus ?case by simp
qed simp_all

text \<open>Correctness is another matter. There are a few problems here, and the biggest of them are the 
environment-management frames \<open>FPop\<^sub>k\<close> and \<open>FReturn\<^sub>k\<close>. A state which unstacks to a given expression 
might have any number of return frames in its stack, anywhere. We define a function to help deal 
with these empty frames.\<close>

primrec all_returns :: "frame\<^sub>k list \<Rightarrow> bool" where
  "all_returns [] = True"
| "all_returns (f # s) = ((f = FReturn\<^sub>k \<or> f = FPop\<^sub>k) \<and> all_returns s)"

lemma unstack_returns [elim]: "all_returns s \<Longrightarrow> unstack' s e = e"
  by (induction s) auto

lemma fapp1_and_returns [dest]: "FApp1\<^sub>k e # s :\<^sub>k t' \<rightarrow> t \<Longrightarrow> all_returns s \<Longrightarrow> 
    (\<And>t\<^sub>1. t' = Arrow t\<^sub>1 t \<Longrightarrow> [] \<turnstile>\<^sub>d e : t\<^sub>1 \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction s) fastforce+

lemma fapp2_and_returns [dest]: "FApp2\<^sub>k e # sr :\<^sub>k t' \<rightarrow> t \<Longrightarrow> all_returns sr \<Longrightarrow> 
    ([] \<turnstile>\<^sub>d e : Arrow t' t \<Longrightarrow> value\<^sub>d e \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction sr) fastforce+

lemma returns_prepended [dest]: "s @ s' :\<^sub>k t' \<rightarrow> t \<Longrightarrow> all_returns s \<Longrightarrow> (s' :\<^sub>k t' \<rightarrow> t \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction s) fastforce+

lemma unstack_to_value' [simp]: "value\<^sub>d v \<Longrightarrow> v = unstack' s e \<Longrightarrow> all_returns s \<and> e = v"
  by (induction s e rule: unstack'.induct) simp_all

lemma unstack_to_value [simp]: "value\<^sub>d v \<Longrightarrow> v = unstack \<Sigma>\<^sub>k \<Longrightarrow> \<exists>b s. \<Sigma>\<^sub>k = S\<^sub>k b s v \<and> all_returns s"
  by (induction \<Sigma>\<^sub>k) simp_all

text \<open>Now we prove our reconstruction lemma for \<open>App\<^sub>d\<close>s. Without returns, this would be somewhat 
simpler - but as mentioned, we need them for future stages.\<close>

lemma unstack_to_app [consumes 1, case_names Empty FApp1\<^sub>k FApp2\<^sub>k]: "App\<^sub>d e\<^sub>1 e\<^sub>2 = unstack' s e \<Longrightarrow> 
    (all_returns s \<Longrightarrow> e = App\<^sub>d e\<^sub>1 e\<^sub>2 \<Longrightarrow> P) \<Longrightarrow> 
    (\<And>s' sr. all_returns sr \<Longrightarrow> s = s' @ FApp1\<^sub>k e\<^sub>2 # sr \<Longrightarrow> e\<^sub>1 = unstack' s' e \<Longrightarrow> P) \<Longrightarrow>
    (\<And>s' sr. all_returns sr \<Longrightarrow> s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<Longrightarrow> e\<^sub>2 = unstack' s' e \<Longrightarrow> P) \<Longrightarrow> 
    P"
  by (induction s e rule: unstack'.induct) fastforce+

lemma unstack_to_let [consumes 1, case_names Empty FLet\<^sub>k]: "Let\<^sub>d e\<^sub>1 e\<^sub>2 = unstack' s e \<Longrightarrow> 
    (all_returns s \<Longrightarrow> e = Let\<^sub>d e\<^sub>1 e\<^sub>2 \<Longrightarrow> P) \<Longrightarrow> 
    (\<And>s' sr. all_returns sr \<Longrightarrow> s = s' @ FLet\<^sub>k e\<^sub>2 # sr \<Longrightarrow> e\<^sub>1 = unstack' s' e \<Longrightarrow> P) \<Longrightarrow>
    P"
  by (induction s e rule: unstack'.induct) fastforce+

lemma unstack_from_app1 [simp]: "all_returns sr \<Longrightarrow> 
    unstack' (s @ FApp1\<^sub>k e\<^sub>2 # sr) e = App\<^sub>d (unstack' s e) e\<^sub>2"
  by (induction s e rule: unstack'.induct) auto

lemma unstack_from_app2 [simp]: "all_returns sr \<Longrightarrow> 
    unstack' (s @ FApp2\<^sub>k e\<^sub>1 # sr) e = App\<^sub>d e\<^sub>1 (unstack' s e)"
  by (induction s e rule: unstack'.induct) auto

lemma eval_return_in_front [simp]: "f = FReturn\<^sub>k \<or> f = FPop\<^sub>k \<Longrightarrow> value\<^sub>d v \<Longrightarrow> 
  iter (\<leadsto>\<^sub>k) (S\<^sub>k b (f # s) v) (S\<^sub>k True s v)"
proof auto
  assume V: "value\<^sub>d v"
  hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (FReturn\<^sub>k # s) v) (S\<^sub>k True (FReturn\<^sub>k # s) v)" by simp
  thus "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (FReturn\<^sub>k # s) v) (S\<^sub>k True s v)" by simp
  from V have "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (FPop\<^sub>k # s) v) (S\<^sub>k True (FPop\<^sub>k # s) v)" by simp
  thus "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (FPop\<^sub>k # s) v) (S\<^sub>k True s v)" by simp
qed

lemma eval_returns_in_front [simp]: "all_returns sr \<Longrightarrow> value\<^sub>d v \<Longrightarrow> 
  iter (\<leadsto>\<^sub>k) (S\<^sub>k b (sr @ s) v) (S\<^sub>k True s v)"
proof (induction sr arbitrary: b)
  case (Cons f sr)
  hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (f # sr @ s) v) (S\<^sub>k True (sr @ s) v)" by simp
  moreover from Cons have "iter (\<leadsto>\<^sub>k) (S\<^sub>k True (sr @ s) v) (S\<^sub>k True s v)" by simp
  ultimately have "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (f # sr @ s) v) (S\<^sub>k True s v)" by (metis iter_append)
  with Cons show ?case by simp
qed simp_all

text \<open>And finally, the main lemma for correctness. Being able to reconstruct the stack state that 
was unstacked to an \<open>App\<^sub>d\<close> is crucial to make this work.\<close>

lemma correctness\<^sub>k' [simp]: "unstack' s e \<leadsto>\<^sub>d e' \<Longrightarrow> s :\<^sub>k t' \<rightarrow> t \<Longrightarrow> [] \<turnstile>\<^sub>d e : tt \<Longrightarrow> 
  b \<longrightarrow> value\<^sub>d e \<Longrightarrow> \<exists>b' s' e''. iter (\<leadsto>\<^sub>k) (S\<^sub>k b s e) (S\<^sub>k b' s' e'') \<and> e' = unstack' s' e''"
proof (induction "unstack' s e" e' arbitrary: b s e t tt rule: eval\<^sub>d.induct)
  case (ev\<^sub>d_app1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
  from ev\<^sub>d_app1(3) show ?case
  proof (induction rule: unstack_to_app)
    case Empty
    with ev\<^sub>d_app1 have B: "\<not>b" by (cases b) simp_all
    from ev\<^sub>d_app1 Empty obtain t\<^sub>1 where T1: "([] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 tt) \<and> ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1)" by blast
    have "[] :\<^sub>k t' \<rightarrow> t'" by simp
    with ev\<^sub>d_app1 B T1 obtain b' s' e'' where E: "iter (\<leadsto>\<^sub>k) (S\<^sub>k False [] e\<^sub>1) (S\<^sub>k b' s' e'') \<and> 
      e\<^sub>1' = unstack' s' e''" by fastforce
    hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k False ([] @ FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1) (S\<^sub>k b' (s' @ FApp1\<^sub>k e\<^sub>2 # s) e'')" 
      by (metis eval\<^sub>k_under_iter)
    hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k False (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1) (S\<^sub>k b' (s' @ FApp1\<^sub>k e\<^sub>2 # s) e'')" by simp
    hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k False s (App\<^sub>d e\<^sub>1 e\<^sub>2)) (S\<^sub>k b' (s' @ FApp1\<^sub>k e\<^sub>2 # s) e'')" 
      by (metis ev\<^sub>k_app1 iter_step)
    with Empty B E show ?thesis by fastforce
  next
    case (FApp1\<^sub>k s' sr)
    with ev\<^sub>d_app1 obtain t'' where "(s' :\<^sub>k t' \<rightarrow> t'') \<and> (FApp1\<^sub>k e\<^sub>2 # sr :\<^sub>k t'' \<rightarrow> t)" by fastforce
    with ev\<^sub>d_app1 FApp1\<^sub>k obtain b' ss' e'' where S': "iter (\<leadsto>\<^sub>k) (S\<^sub>k b s' e) (S\<^sub>k b' ss' e'') \<and> 
      e\<^sub>1' = unstack' ss' e''" by metis
    hence X: "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s' @ FApp1\<^sub>k e\<^sub>2 # sr) e) (S\<^sub>k b' (ss' @ FApp1\<^sub>k e\<^sub>2 # sr) e'')" by simp
    from FApp1\<^sub>k S' have "App\<^sub>d e\<^sub>1' e\<^sub>2 = unstack' (ss' @ FApp1\<^sub>k e\<^sub>2 # sr) e''" by simp
    with FApp1\<^sub>k X show ?case by blast
  next
    case (FApp2\<^sub>k s' sr)
    hence "s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unstack' s' e" by simp
    with ev\<^sub>d_app1 obtain t\<^sub>1 where "(s' :\<^sub>k t' \<rightarrow> t\<^sub>1) \<and> (FApp2\<^sub>k e\<^sub>1 # sr :\<^sub>k t\<^sub>1 \<rightarrow> t)" by fastforce
    with FApp2\<^sub>k have "([] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t) \<and> value\<^sub>d e\<^sub>1" by fastforce
    with ev\<^sub>d_app1 show ?case by (metis val_no_eval\<^sub>d)
  qed
next
  case (ev\<^sub>d_app2 e\<^sub>1 e\<^sub>2 e\<^sub>2')
  from ev\<^sub>d_app2(4) show ?case
  proof (induction rule: unstack_to_app)
    case Empty
    with ev\<^sub>d_app2 have B: "\<not>b" by (cases b) simp_all
    from ev\<^sub>d_app2 Empty obtain t\<^sub>1 where T: "([] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 tt) \<and> ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1)" by blast
    with ev\<^sub>d_app2 B obtain b' s' e'' where E: "iter (\<leadsto>\<^sub>k) (S\<^sub>k False [] e\<^sub>2) (S\<^sub>k b' s' e'') \<and> 
      e\<^sub>2' = unstack' s' e''" by (metis unstack'.simps(1) tcs\<^sub>k_nil)
    hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k False (FApp2\<^sub>k e\<^sub>1 # s) e\<^sub>2) (S\<^sub>k b' (s' @ FApp2\<^sub>k e\<^sub>1 # s) e'')" 
      by (metis eval\<^sub>k_under_iter append_Nil)
    moreover have "S\<^sub>k False s (App\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>k S\<^sub>k False (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1" by simp
    moreover from ev\<^sub>d_app2 have "iter (\<leadsto>\<^sub>k) (S\<^sub>k False (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1) (S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1)" 
      by simp
    moreover have "S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1 \<leadsto>\<^sub>k S\<^sub>k False (FApp2\<^sub>k e\<^sub>1 # s) e\<^sub>2" by simp
    ultimately have "iter (\<leadsto>\<^sub>k) (S\<^sub>k False s (App\<^sub>d e\<^sub>1 e\<^sub>2)) (S\<^sub>k b' (s' @ FApp2\<^sub>k e\<^sub>1 # s) e'')" 
      by (metis iter_step iter_append)
    with Empty B E show ?case by fastforce
  next
    case (FApp1\<^sub>k s' sr)
    with ev\<^sub>d_app2 have S': "all_returns s' \<and> e = e\<^sub>1" by simp 
    with ev\<^sub>d_app2 FApp1\<^sub>k obtain t\<^sub>1 where T: "t' = Arrow t\<^sub>1 t \<and> [] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1" by blast
    have X: "e\<^sub>2 = unstack' [] e\<^sub>2" by simp
    have E: "[] :\<^sub>k t' \<rightarrow> t'" by simp
    have "False \<Longrightarrow> value\<^sub>d e\<^sub>2" by simp
    with ev\<^sub>d_app2 T X E obtain b'' s'' e'' where E: "iter (\<leadsto>\<^sub>k) (S\<^sub>k False [] e\<^sub>2) (S\<^sub>k b'' s'' e'') \<and> 
      e\<^sub>2' = unstack' s'' e''" by blast
    hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k False (FApp2\<^sub>k e\<^sub>1 # sr) e\<^sub>2) (S\<^sub>k b'' (s'' @ FApp2\<^sub>k e\<^sub>1 # sr) e'')" 
      using eval\<^sub>k_under_iter by fastforce
    moreover from ev\<^sub>d_app2 have "S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # sr) e\<^sub>1 \<leadsto>\<^sub>k S\<^sub>k False (FApp2\<^sub>k e\<^sub>1 # sr) e\<^sub>2" by simp
    moreover from ev\<^sub>d_app2 S' have "iter (\<leadsto>\<^sub>k) (S\<^sub>k True (s' @ FApp1\<^sub>k e\<^sub>2 # sr) e\<^sub>1) 
      (S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # sr) e\<^sub>1)" by simp
    moreover from ev\<^sub>d_app2 S' have "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s' @ FApp1\<^sub>k e\<^sub>2 # sr) e\<^sub>1) 
      (S\<^sub>k True (s' @ FApp1\<^sub>k e\<^sub>2 # sr) e\<^sub>1)" by simp
    ultimately have Y: "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s' @ FApp1\<^sub>k e\<^sub>2 # sr) e\<^sub>1) 
      (S\<^sub>k b'' (s'' @ FApp2\<^sub>k e\<^sub>1 # sr) e'')" by (metis iter_step iter_append)
    from FApp1\<^sub>k E have "App\<^sub>d e\<^sub>1 e\<^sub>2' = unstack' (s'' @ FApp2\<^sub>k e\<^sub>1 # sr) e''" by simp
    with FApp1\<^sub>k S' Y show ?case by metis
  next
    case (FApp2\<^sub>k s' sr)
    hence S': "s = s' @ FApp2\<^sub>k e\<^sub>1 # sr \<and> e\<^sub>2 = unstack' s' e" by simp
    with ev\<^sub>d_app2 obtain t\<^sub>1 where "(s' :\<^sub>k t' \<rightarrow> t\<^sub>1) \<and> (FApp2\<^sub>k e\<^sub>1 # sr :\<^sub>k t\<^sub>1 \<rightarrow> t)" by fastforce
    with ev\<^sub>d_app2 S' obtain b'' s'' e'' where E: "iter (\<leadsto>\<^sub>k) (S\<^sub>k b s' e) (S\<^sub>k b'' s'' e'') \<and> 
      e\<^sub>2' = unstack' s'' e''" by blast
    hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s' @ FApp2\<^sub>k e\<^sub>1 # sr) e) (S\<^sub>k b'' (s'' @ FApp2\<^sub>k e\<^sub>1 # sr) e'')" by simp
    with FApp2\<^sub>k S' E show ?case by fastforce
  qed
next
  case (ev\<^sub>d_app3 e\<^sub>2 t\<^sub>1 e\<^sub>1)
  from ev\<^sub>d_app3(2) show ?case
  proof (induction rule: unstack_to_app)
    case Empty
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
    from Empty have "subst\<^sub>d 0 e\<^sub>2 e\<^sub>1 = unstack' (FReturn\<^sub>k # s) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)"
      using unstack_returns by simp
    with Empty B X show ?case by fastforce
  next
    case (FApp1\<^sub>k s' sr)
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
    from FApp1\<^sub>k have "subst\<^sub>d 0 e\<^sub>2 e\<^sub>1 = unstack' (FReturn\<^sub>k # sr) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)" 
      using unstack_returns by simp
    with FApp1\<^sub>k S' X show ?case by fastforce
  next
    case (FApp2\<^sub>k s' sr)
    with ev\<^sub>d_app3 have S': "all_returns s' \<and> e = e\<^sub>2" by simp
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
    from FApp2\<^sub>k have "subst\<^sub>d 0 e\<^sub>2 e\<^sub>1 = unstack' (FReturn\<^sub>k # sr) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)" 
      using unstack_returns by simp
    with FApp2\<^sub>k S' X show ?case by metis
  qed
next
  case (ev\<^sub>d_let1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
  from ev\<^sub>d_let1(3) show ?case
  proof (induction rule: unstack_to_let)
    case Empty
    from ev\<^sub>d_let1 have "e\<^sub>1 \<leadsto>\<^sub>d e\<^sub>1'" by simp
    from ev\<^sub>d_let1 have "e\<^sub>1 = unstack' xs xe \<Longrightarrow>
      xs :\<^sub>k t' \<rightarrow> xt \<Longrightarrow>
      [] \<turnstile>\<^sub>d xe : xtt \<Longrightarrow>
      xb \<longrightarrow> value\<^sub>d xe \<Longrightarrow> \<exists>b' s' e''. iter (\<leadsto>\<^sub>k) (S\<^sub>k xb xs xe) (S\<^sub>k b' s' e'') \<and> e\<^sub>1' = unstack' s' e''" by simp
    from ev\<^sub>d_let1 have "s :\<^sub>k t' \<rightarrow> t" by simp
    from ev\<^sub>d_let1 Empty have "[] \<turnstile>\<^sub>d Let\<^sub>d e\<^sub>1 e\<^sub>2 : tt" by simp
    from ev\<^sub>d_let1 Empty have "\<not>b" by simp
  
  
    have "iter (\<leadsto>\<^sub>k) (S\<^sub>k b s (Let\<^sub>d e\<^sub>1 e\<^sub>2)) (S\<^sub>k b' s' e'') \<and> Let\<^sub>d e\<^sub>1' e\<^sub>2 = unstack' s' e''" by simp
    with Empty show ?case by blast
  next
    case (FLet\<^sub>k s' sr)
    from ev\<^sub>d_let1 have "e\<^sub>1 \<leadsto>\<^sub>d e\<^sub>1'" by simp
    from ev\<^sub>d_let1 have "e\<^sub>1 = unstack' xs xe \<Longrightarrow>
      xs :\<^sub>k t' \<rightarrow> xt \<Longrightarrow>
      [] \<turnstile>\<^sub>d xe : xtt \<Longrightarrow>
      xb \<longrightarrow> value\<^sub>d xe \<Longrightarrow> \<exists>b' s' e''. iter (\<leadsto>\<^sub>k) (S\<^sub>k xb xs xe) (S\<^sub>k b' s' e'') \<and> e\<^sub>1' = unstack' s' e''" by simp
    from ev\<^sub>d_let1 have "s :\<^sub>k t' \<rightarrow> t" by simp
    from ev\<^sub>d_let1 have "[] \<turnstile>\<^sub>d e : tt" by simp
    from ev\<^sub>d_let1 have "b \<longrightarrow> value\<^sub>d e" by simp
  
  
    have "iter (\<leadsto>\<^sub>k) (S\<^sub>k b s e) (S\<^sub>k b' s' e'') \<and> Let\<^sub>d e\<^sub>1' e\<^sub>2 = unstack' s' e''" by simp
    thus ?case by blast
  qed
next
  case (ev\<^sub>d_let2 e\<^sub>1 e\<^sub>2)
  then show ?case by simp
qed

text \<open>Correctness is now simple to state and prove. We also extend the theorem to cover full
evaluation from an initial state to a final one.\<close>

theorem correct\<^sub>k [simp]: "\<Sigma>\<^sub>k :\<^sub>k t \<Longrightarrow> unstack \<Sigma>\<^sub>k \<leadsto>\<^sub>d e' \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>k'. iter (\<leadsto>\<^sub>k) \<Sigma>\<^sub>k \<Sigma>\<^sub>k' \<and> e' = unstack \<Sigma>\<^sub>k'"
proof (induction \<Sigma>\<^sub>k t rule: typing_state\<^sub>k.induct)
  case (tc_state\<^sub>k s t' t e b)
  then obtain b' s' e'' where "iter (\<leadsto>\<^sub>k) (S\<^sub>k b s e) (S\<^sub>k b' s' e'') \<and> e' = unstack' s' e''" 
    by fastforce
  thus ?case by fastforce
qed

lemma correct\<^sub>k_iter [simp]: "iter (\<leadsto>\<^sub>d) (unstack \<Sigma>\<^sub>k) e' \<Longrightarrow> \<Sigma>\<^sub>k :\<^sub>k t \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>k'. iter (\<leadsto>\<^sub>k) \<Sigma>\<^sub>k \<Sigma>\<^sub>k' \<and> e' = unstack \<Sigma>\<^sub>k'"
proof (induction "unstack \<Sigma>\<^sub>k" e' arbitrary: \<Sigma>\<^sub>k rule: iter.induct)
  case (iter_step e' e'')
  moreover then obtain \<Sigma>\<^sub>k' where S: "iter (\<leadsto>\<^sub>k) \<Sigma>\<^sub>k \<Sigma>\<^sub>k' \<and> e' = unstack \<Sigma>\<^sub>k'" by fastforce
  moreover with iter_step have "\<Sigma>\<^sub>k' :\<^sub>k t" by fastforce
  ultimately obtain \<Sigma>\<^sub>k'' where "iter (\<leadsto>\<^sub>k) \<Sigma>\<^sub>k' \<Sigma>\<^sub>k'' \<and> e'' = unstack \<Sigma>\<^sub>k''" by fastforce
  with S have "iter (\<leadsto>\<^sub>k) \<Sigma>\<^sub>k \<Sigma>\<^sub>k'' \<and> e'' = unstack \<Sigma>\<^sub>k''" by (metis iter_append)
  then show ?case by fastforce
qed force+

lemma correct\<^sub>k_full_eval [simp]: "iter (\<leadsto>\<^sub>d) e v \<Longrightarrow> [] \<turnstile>\<^sub>d e : t \<Longrightarrow> value\<^sub>d v \<Longrightarrow> 
  iter (\<leadsto>\<^sub>k) (S\<^sub>k False [FReturn\<^sub>k] e) (S\<^sub>k True [] v)"
proof -
  assume "[] \<turnstile>\<^sub>d e : t"
  hence "S\<^sub>k False [FReturn\<^sub>k] e :\<^sub>k t" by (metis tcs\<^sub>k_nil tcs\<^sub>k_cons_ret tc_state\<^sub>k)
  moreover assume "iter (\<leadsto>\<^sub>d) e v"
  ultimately obtain \<Sigma>\<^sub>k' where S: "iter (\<leadsto>\<^sub>k) (S\<^sub>k False [FReturn\<^sub>k] e) \<Sigma>\<^sub>k' \<and> v = unstack \<Sigma>\<^sub>k'" 
    by fastforce
  moreover assume V: "value\<^sub>d v"
  ultimately obtain b sr where "\<Sigma>\<^sub>k' = S\<^sub>k b (sr @ []) v \<and> all_returns sr" by fastforce
  moreover with V have "iter (\<leadsto>\<^sub>k) \<Sigma>\<^sub>k' (S\<^sub>k True [] v)" by (metis eval_returns_in_front)
  with S show "iter (\<leadsto>\<^sub>k) (S\<^sub>k False [FReturn\<^sub>k] e) (S\<^sub>k True [] v)" by (metis iter_append)
qed

end