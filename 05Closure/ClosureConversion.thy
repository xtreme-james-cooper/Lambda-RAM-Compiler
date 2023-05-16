theory ClosureConversion
  imports Closure "../04Stack/Stack" "../03Debruijn/Multisubst"
begin

subsection \<open>Closure conversion\<close>

text \<open>The basic relationship between closure-values and expressions is simple: the only complicated 
case is closures proper, and by substituting in the entire environment at once using the multisubst 
method we have already helpfully defined, we get an equivalent expression. Once again, however, any 
number of closures could declose to a single expression, so we are forced to run our conversions 
backwards.\<close>

primrec declosure :: "closure\<^sub>c \<Rightarrow> expr\<^sub>d" where
  "declosure (Const\<^sub>c n) = Const\<^sub>d n"
| "declosure (Lam\<^sub>c t \<Delta> e) = multisubst (map declosure \<Delta>) (Lam\<^sub>d t e)"

lemma declosure_always_value [simp]: "value\<^sub>d (declosure c)"
proof (induction c)
  case (Lam\<^sub>c t \<Delta> e)
  thus ?case by (induction \<Delta> arbitrary: e) simp_all
qed simp_all

lemma tc_declosure [simp]: "c :\<^sub>c\<^sub>l t \<Longrightarrow> [] \<turnstile>\<^sub>d declosure c : t"
  and tc_declosure_env [simp]: "\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> tc_expr_context \<Gamma> (map declosure \<Delta>)" 
proof (induction c t and \<Delta> \<Gamma> rule: typing_closure\<^sub>c_typing_environment\<^sub>c.inducts)
  case (tc\<^sub>c_lam \<Delta> \<Gamma> t\<^sub>1 e t\<^sub>2)
  then obtain e' where "multisubst (map declosure \<Delta>) (Lam\<^sub>d t\<^sub>1 e) = Lam\<^sub>d t\<^sub>1 e' \<and> ([t\<^sub>1] \<turnstile>\<^sub>d e' : t\<^sub>2) \<and> 
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> multisubst (map declosure \<Delta>) (subst\<^sub>d 0 e\<^sub>2 e) = subst\<^sub>d 0 e\<^sub>2 e')" 
      by fastforce
  thus ?case by simp
qed simp_all

lemma multisubst_closure [simp]: "c :\<^sub>c\<^sub>l t \<Longrightarrow> multisubst es (declosure c) = declosure c"
  and multisubst_env [simp]: "\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> v \<in> set (map declosure \<Delta>) \<Longrightarrow> multisubst es v = v"
proof (induction c t and \<Delta> \<Gamma> rule: typing_closure\<^sub>c_typing_environment\<^sub>c.inducts)
  case (tc\<^sub>c_lam \<Delta> \<Gamma> t\<^sub>1 e t\<^sub>2)
  moreover hence "tc_expr_context \<Gamma> (map declosure \<Delta>)" by simp
  ultimately obtain e' where E: "multisubst (map declosure \<Delta>) (Lam\<^sub>d t\<^sub>1 e) = Lam\<^sub>d t\<^sub>1 e' \<and> 
    ([t\<^sub>1] \<turnstile>\<^sub>d e' : t\<^sub>2) \<and> (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> 
      multisubst (map declosure \<Delta>) (subst\<^sub>d 0 e\<^sub>2 e) = subst\<^sub>d 0 e\<^sub>2 e')" by fastforce
  hence "[] \<turnstile>\<^sub>d Lam\<^sub>d t\<^sub>1 e' : Arrow t\<^sub>1 t\<^sub>2" by simp
  hence "multisubst es (Lam\<^sub>d t\<^sub>1 e') = Lam\<^sub>d t\<^sub>1 e'" by simp
  with E show ?case by simp
qed auto

text \<open>The stack conversion is an easy extension. We throw away the extra environment on \<open>FReturn\<^sub>c\<close> 
frames.\<close>

fun declosure_stack :: "frame\<^sub>c list \<Rightarrow> frame\<^sub>k list" where
  "declosure_stack [] = []"
| "declosure_stack (FApp1\<^sub>c \<Delta> e # s\<^sub>c) = FApp1\<^sub>k (multisubst (map declosure \<Delta>) e) # declosure_stack s\<^sub>c"
| "declosure_stack (FApp2\<^sub>c c # s\<^sub>c) = FApp2\<^sub>k (declosure c) # declosure_stack s\<^sub>c"
| "declosure_stack (FReturn\<^sub>c \<Delta> # s\<^sub>c) = FReturn\<^sub>k # declosure_stack s\<^sub>c"

lemma tc_declosure_stack [simp]: "s\<^sub>c :\<^sub>c t' \<rightarrow> t \<Longrightarrow> declosure_stack s\<^sub>c :\<^sub>k t' \<rightarrow> t"
proof (induction s\<^sub>c t' t rule: typing_stack\<^sub>c.induct)
  case (tcc_scons_app1 \<Delta> \<Gamma> e t\<^sub>1 s\<^sub>c t\<^sub>2 t)
  hence "tc_expr_context \<Gamma> (map declosure \<Delta>)" by simp
  moreover from tcc_scons_app1 have "\<Gamma> \<turnstile>\<^sub>d e : t\<^sub>1" by simp
  ultimately have "[] \<turnstile>\<^sub>d multisubst (map declosure \<Delta>) e : t\<^sub>1" by simp
  with tcc_scons_app1 show ?case by simp
next
  case (tcc_scons_app2 c t\<^sub>1 t\<^sub>2 s\<^sub>c t)
  hence "[] \<turnstile>\<^sub>d declosure c : Arrow t\<^sub>1 t\<^sub>2" by simp
  moreover from tcc_scons_app2 have "declosure_stack s\<^sub>c :\<^sub>k t\<^sub>2 \<rightarrow> t" by simp
  ultimately show ?case by simp
qed simp_all

text \<open>The state level conversion follows, as does type safety and completeness. Completeness is 
unfortunately complicated by the fact that _almost_ every closure evaluation step has an equivalent
stack evaluation step; but looking up a variable takes a step in this stage, and didn't in the 
previous (all variables were substituted away at the moment of function application), so we must 
again use \<open>iter\<close>.\<close>

primrec declosure_state :: "state\<^sub>c \<Rightarrow> state\<^sub>k" where
  "declosure_state (SE\<^sub>c s\<^sub>c \<Delta> e) = S\<^sub>k False (declosure_stack s\<^sub>c) (multisubst (map declosure \<Delta>) e)"
| "declosure_state (SC\<^sub>c s\<^sub>c c) = S\<^sub>k True (declosure_stack s\<^sub>c) (declosure c)"
  
theorem typesafe\<^sub>c [simp]: "\<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow> declosure_state \<Sigma>\<^sub>c :\<^sub>k t"
proof (induction \<Sigma>\<^sub>c t rule: typecheck_state\<^sub>c.induct)
  case (tcc_state_ev s\<^sub>c t' t \<Delta>\<^sub>c \<Gamma> e)
  hence "tc_expr_context \<Gamma> (map declosure \<Delta>\<^sub>c)" by simp
  moreover from tcc_state_ev have "\<Gamma> \<turnstile>\<^sub>d e : t'" by simp
  ultimately have "[] \<turnstile>\<^sub>d multisubst (map declosure \<Delta>\<^sub>c) e : t'" by simp
  moreover from tcc_state_ev have "declosure_stack s\<^sub>c :\<^sub>k t' \<rightarrow> t" by simp
  ultimately show ?case by simp
next
  case (tcc_state_ret s\<^sub>c t' t c)
  hence "declosure_stack s\<^sub>c :\<^sub>k t' \<rightarrow> t" by simp
  moreover from tcc_state_ret have "[] \<turnstile>\<^sub>d declosure c : t'" by simp
  ultimately show ?case by simp
qed

theorem completeness\<^sub>c: "\<Sigma>\<^sub>c \<leadsto>\<^sub>c \<Sigma>\<^sub>c' \<Longrightarrow> \<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow> 
  iter (\<leadsto>\<^sub>k) (declosure_state \<Sigma>\<^sub>c) (declosure_state \<Sigma>\<^sub>c')"
proof (induction \<Sigma>\<^sub>c \<Sigma>\<^sub>c' rule: eval\<^sub>c.induct)
  case (ev\<^sub>c_var \<Delta> x c s\<^sub>c)
  then obtain t' \<Gamma> where "(s\<^sub>c :\<^sub>c t' \<rightarrow> t) \<and> (\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> lookup \<Gamma> x = Some t'" by fastforce
  hence "\<And>v es. v \<in> set (map declosure \<Delta>) \<Longrightarrow> multisubst es v = v" by auto
  moreover from ev\<^sub>c_var have "lookup (map declosure \<Delta>) x = Some (declosure c)" by simp
  ultimately have "multisubst (map declosure \<Delta>) (Var\<^sub>d x) = declosure c" by (metis multisubst_var)
  thus ?case by simp
next
  case (ev\<^sub>c_lam s\<^sub>c \<Delta> t e)
  obtain e' where "multisubst (map declosure \<Delta>) (Lam\<^sub>d t e) = Lam\<^sub>d t e'" by fastforce
  hence "S\<^sub>k False (declosure_stack s\<^sub>c) (multisubst (map declosure \<Delta>) (Lam\<^sub>d t e)) \<leadsto>\<^sub>k
    S\<^sub>k True (declosure_stack s\<^sub>c) (multisubst (map declosure \<Delta>) (Lam\<^sub>d t e))" by simp
  hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k False (declosure_stack s\<^sub>c) (multisubst (map declosure \<Delta>) (Lam\<^sub>d t e)))
    (S\<^sub>k True (declosure_stack s\<^sub>c) (multisubst (map declosure \<Delta>) (Lam\<^sub>d t e)))" 
      by (metis iter_step iter_refl)
  thus ?case by simp
next
  case (ev\<^sub>c_app s\<^sub>c \<Delta> e\<^sub>1 e\<^sub>2)
  have "S\<^sub>k False (declosure_stack s\<^sub>c) (App\<^sub>d (multisubst (map declosure \<Delta>) e\<^sub>1) 
    (multisubst (map declosure \<Delta>) e\<^sub>2)) \<leadsto>\<^sub>k 
      S\<^sub>k False (FApp1\<^sub>k (multisubst (map declosure \<Delta>) e\<^sub>2) # declosure_stack s\<^sub>c) 
        (multisubst (map declosure \<Delta>) e\<^sub>1)" by simp
  hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k False (declosure_stack s\<^sub>c) (App\<^sub>d (multisubst (map declosure \<Delta>) e\<^sub>1) 
    (multisubst (map declosure \<Delta>) e\<^sub>2))) 
      (S\<^sub>k False (FApp1\<^sub>k (multisubst (map declosure \<Delta>) e\<^sub>2) # declosure_stack s\<^sub>c) 
        (multisubst (map declosure \<Delta>) e\<^sub>1))" by (metis iter_step iter_refl)
  thus ?case by simp
next
  case (ret\<^sub>c_app1 \<Delta> e\<^sub>2 s\<^sub>c c\<^sub>1)
  have "S\<^sub>k True (FApp1\<^sub>k (multisubst (map declosure \<Delta>) e\<^sub>2) # declosure_stack s\<^sub>c) (declosure c\<^sub>1) \<leadsto>\<^sub>k
    S\<^sub>k False (FApp2\<^sub>k (declosure c\<^sub>1) # declosure_stack s\<^sub>c) (multisubst (map declosure \<Delta>) e\<^sub>2)" by simp
  hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k True (FApp1\<^sub>k (multisubst (map declosure \<Delta>) e\<^sub>2) # declosure_stack s\<^sub>c) 
    (declosure c\<^sub>1)) 
      (S\<^sub>k False (FApp2\<^sub>k (declosure c\<^sub>1) # declosure_stack s\<^sub>c) (multisubst (map declosure \<Delta>) e\<^sub>2))" 
        by (metis iter_step iter_refl)
  thus ?case by simp
next
  case (ret\<^sub>c_app2 t\<^sub>1 \<Delta> e\<^sub>1 s\<^sub>c c\<^sub>2)
  then obtain \<Gamma> t\<^sub>2 where T: "(\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> (insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2) \<and> (s\<^sub>c :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> 
    (c\<^sub>2 :\<^sub>c\<^sub>l t\<^sub>1)" by fastforce
  hence "tc_expr_context \<Gamma> (map declosure \<Delta>) \<and> insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2" by simp
  then obtain e' where "multisubst (map declosure \<Delta>) (Lam\<^sub>d t\<^sub>1 e\<^sub>1) = Lam\<^sub>d t\<^sub>1 e' \<and> ([t\<^sub>1] \<turnstile>\<^sub>d e' : t\<^sub>2) \<and>
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> multisubst (map declosure \<Delta>) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1) = subst\<^sub>d 0 e\<^sub>2 e')" 
      by fastforce
  with T have "S\<^sub>k True (FApp2\<^sub>k (multisubst (map declosure \<Delta>) (Lam\<^sub>d t\<^sub>1 e\<^sub>1)) # declosure_stack s\<^sub>c) 
    (declosure c\<^sub>2) \<leadsto>\<^sub>k (S\<^sub>k False (FReturn\<^sub>k # declosure_stack s\<^sub>c) 
      (multisubst (map declosure \<Delta>) (subst\<^sub>d 0 (declosure c\<^sub>2) e\<^sub>1)))" 
    by simp
  hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k True (FApp2\<^sub>k (multisubst (map declosure \<Delta>) (Lam\<^sub>d t\<^sub>1 e\<^sub>1)) # declosure_stack s\<^sub>c) 
    (declosure c\<^sub>2)) 
      (S\<^sub>k False (FReturn\<^sub>k # declosure_stack s\<^sub>c) 
        (multisubst (map declosure \<Delta>) (subst\<^sub>d 0 (declosure c\<^sub>2) e\<^sub>1)))" 
    by (metis iter_step iter_refl)
  thus ?case by simp
next
  case (ret\<^sub>c_ret \<Delta> s\<^sub>c c)
  have "S\<^sub>k True (FReturn\<^sub>k # declosure_stack s\<^sub>c) (declosure c) \<leadsto>\<^sub>k 
    S\<^sub>k True (declosure_stack s\<^sub>c) (declosure c)" by simp
  hence "iter (\<leadsto>\<^sub>k) (S\<^sub>k True (FReturn\<^sub>k # declosure_stack s\<^sub>c) (declosure c)) 
    (S\<^sub>k True (declosure_stack s\<^sub>c) (declosure c))" by (metis iter_step iter_refl)
  thus ?case by simp
qed simp_all

text \<open>Once again, correctness is more difficult, and requires reconstruction lemmas. Unlike last 
time, where a single (albeit complicated) lemma sufficed, closure conversion involves three separate 
levels of conversion, and a correspondingly larger number of lemmas. Fortunately, since there is a 
closer relation between stacks and states, most of them are much simpler to state and prove.\<close>

lemma declose_to_lam [dest]: "Lam\<^sub>d t\<^sub>1 e = declosure c \<Longrightarrow> c :\<^sub>c\<^sub>l Arrow t' t\<^sub>2 \<Longrightarrow>
  \<exists>\<Delta> e'. c = Lam\<^sub>c t\<^sub>1 \<Delta> e' \<and> multisubst (map declosure \<Delta>) (Lam\<^sub>d t\<^sub>1 e') = Lam\<^sub>d t\<^sub>1 e \<and> 
    ([t\<^sub>1] \<turnstile>\<^sub>d e : t\<^sub>2) \<and> t' = t\<^sub>1 \<and>
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> multisubst (map declosure \<Delta>) (subst\<^sub>d 0 e\<^sub>2 e') = subst\<^sub>d 0 e\<^sub>2 e)"
proof (induction c)
  case (Lam\<^sub>c tt \<Delta> e')
  moreover then obtain \<Gamma> where T: "(\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> (insert_at 0 t' \<Gamma> \<turnstile>\<^sub>d e' : t\<^sub>2) \<and> tt = t'" 
    by fastforce
  moreover hence "tc_expr_context \<Gamma> (map declosure \<Delta>)" by simp
  ultimately obtain e'' where "multisubst (map declosure \<Delta>) (Lam\<^sub>d t' e') = Lam\<^sub>d t' e'' \<and> 
    ([t'] \<turnstile>\<^sub>d e'' : t\<^sub>2) \<and>
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t') \<longrightarrow> multisubst (map declosure \<Delta>) (subst\<^sub>d 0 e\<^sub>2 e') = subst\<^sub>d 0 e\<^sub>2 e'')"
      by fastforce
  with Lam\<^sub>c T show ?case by simp
qed simp_all

lemma declose_to_app [dest]: "App\<^sub>d e\<^sub>1 e\<^sub>2 = declosure c \<Longrightarrow> False"
  by (induction c) auto

lemma declose_to_nil [dest]: "[] = declosure_stack s\<^sub>c \<Longrightarrow> s\<^sub>c = []"
  by (induction s\<^sub>c rule: declosure_stack.induct) simp_all

lemma declose_to_fapp1 [dest]: "FApp1\<^sub>k e # s\<^sub>k = declosure_stack s\<^sub>c \<Longrightarrow> 
  \<exists>\<Delta> e' s\<^sub>c'. s\<^sub>c = FApp1\<^sub>c \<Delta> e' # s\<^sub>c' \<and> e = multisubst (map declosure \<Delta>) e' \<and> 
    s\<^sub>k = declosure_stack s\<^sub>c'"
  by (induction s\<^sub>c rule: declosure_stack.induct) simp_all

lemma declose_to_fapp2 [dest]: "FApp2\<^sub>k e # s\<^sub>k = declosure_stack s\<^sub>c \<Longrightarrow> 
    \<exists>c s\<^sub>c'. s\<^sub>c = FApp2\<^sub>c c # s\<^sub>c' \<and> e = declosure c \<and> s\<^sub>k = declosure_stack s\<^sub>c'"
  by (induction s\<^sub>c rule: declosure_stack.induct) simp_all

lemma declose_to_freturn [dest]: "FReturn\<^sub>k # s\<^sub>k = declosure_stack s\<^sub>c \<Longrightarrow> 
    \<exists>\<Delta> s\<^sub>c'. s\<^sub>c = FReturn\<^sub>c \<Delta> # s\<^sub>c' \<and> s\<^sub>k = declosure_stack s\<^sub>c'"
  by (induction s\<^sub>c rule: declosure_stack.induct) simp_all

lemma declose_to_state [dest]: "S\<^sub>k b s\<^sub>k e = declosure_state \<Sigma>\<^sub>c \<Longrightarrow> 
  \<exists>s\<^sub>c. s\<^sub>k = declosure_stack s\<^sub>c \<and> 
    ((\<exists>\<Delta> e'. \<not> b \<and> \<Sigma>\<^sub>c = SE\<^sub>c s\<^sub>c \<Delta> e' \<and> e = multisubst (map declosure \<Delta>) e') \<or> 
    (\<exists>c. b \<and> \<Sigma>\<^sub>c = SC\<^sub>c s\<^sub>c c \<and> e = declosure c))"
  by (induction \<Sigma>\<^sub>c) simp_all

lemma multisubst_closure_to_app [dest]: "App\<^sub>d e\<^sub>1 e\<^sub>2 = multisubst (map declosure \<Delta>) (declosure c) \<Longrightarrow>
  False"
proof (induction c)
  case (Lam\<^sub>c t \<Delta>' e)
  moreover obtain e' where "multisubst (map declosure \<Delta>') (Lam\<^sub>d t e) = Lam\<^sub>d t e'" by fastforce
  ultimately show ?case by auto
qed simp_all 

lemma multisusbt_var_to_app [dest]: "App\<^sub>d e\<^sub>1 e\<^sub>2 = multisubst (map declosure \<Delta>) (Var\<^sub>d x) \<Longrightarrow> False"
  by (induction \<Delta> x rule: lookup.induct) auto

lemma multisusbt_to_app [dest]: "App\<^sub>d e\<^sub>1 e\<^sub>2 = multisubst (map declosure \<Delta>) e \<Longrightarrow> 
  \<exists>e\<^sub>1' e\<^sub>2'. e = App\<^sub>d e\<^sub>1' e\<^sub>2' \<and> e\<^sub>1 = multisubst (map declosure \<Delta>) e\<^sub>1' \<and> 
    e\<^sub>2 = multisubst (map declosure \<Delta>) e\<^sub>2'"
  by (induction e) auto

lemma multisubst_closure_to_con [dest]: "Const\<^sub>d n = multisubst es (declosure c) \<Longrightarrow> c = Const\<^sub>c n"
proof (induction c)
  case (Lam\<^sub>c t \<Delta> e)
  moreover obtain e' where "multisubst (map declosure \<Delta>) (Lam\<^sub>d t e) = Lam\<^sub>d t e'" by fastforce
  moreover obtain e'' where "multisubst es (Lam\<^sub>d t e') = Lam\<^sub>d t e''" by fastforce
  ultimately show ?case by simp
qed simp_all

lemma multisubst_var_to_con [dest]: "Const\<^sub>d n = multisubst (map declosure \<Delta>) (Var\<^sub>d x) \<Longrightarrow> 
    lookup \<Delta> x = Some (Const\<^sub>c n)"
  by (induction \<Delta> x rule: lookup.induct) auto

lemma multisubst_to_con [dest]: "Const\<^sub>d n = multisubst (map declosure \<Delta>) e \<Longrightarrow>
  e = Const\<^sub>d n \<or> (\<exists>x. e = Var\<^sub>d x \<and> lookup \<Delta> x = Some (Const\<^sub>c n))"
proof (induction e)
  case (Lam\<^sub>d t e)
  moreover then obtain e' where "multisubst (map declosure \<Delta>) (Lam\<^sub>d t e) = Lam\<^sub>d t e'" by force
  ultimately show ?case by simp
qed auto

lemma incr_declosure [simp]: "c :\<^sub>c\<^sub>l t \<Longrightarrow> incr\<^sub>d x (declosure c) = declosure c"
  and "\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e : tt \<Longrightarrow> 
    incr\<^sub>d x (multisubst (map declosure \<Delta>) e) = multisubst (map declosure \<Delta>) e"
proof (induction c t and \<Delta> \<Gamma> arbitrary: and e tt 
       rule: typing_closure\<^sub>c_typing_environment\<^sub>c.inducts)
  case (tc\<^sub>c_lam \<Delta> \<Gamma> t\<^sub>1 e t\<^sub>2)
  moreover hence "\<Gamma> \<turnstile>\<^sub>d Lam\<^sub>d t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2" by simp
  ultimately have "incr\<^sub>d x (multisubst (map declosure \<Delta>) (Lam\<^sub>d t\<^sub>1 e)) = 
    multisubst (map declosure \<Delta>) (Lam\<^sub>d t\<^sub>1 e)" by blast
  thus ?case by simp
next
  case (tc\<^sub>c_cons c t \<Delta> \<Gamma>)
  hence "[] \<turnstile>\<^sub>d declosure c : t" by simp
  hence "\<Gamma> \<turnstile>\<^sub>d declosure c : t" using tc_postpend by fastforce
  moreover from tc\<^sub>c_cons have "insert_at 0 t \<Gamma> \<turnstile>\<^sub>d e : tt" by (cases \<Gamma>) simp_all
  ultimately have "\<Gamma> \<turnstile>\<^sub>d subst\<^sub>d 0 (declosure c) e : tt" by simp
  with tc\<^sub>c_cons show ?case by simp
qed simp_all

lemma "c :\<^sub>c\<^sub>l t \<Longrightarrow> True"
  and multisubst_lam_twice [simp]: "\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e : t\<^sub>2 \<Longrightarrow> 
  multisubst (map declosure \<Delta>') (multisubst (map declosure \<Delta>) (Lam\<^sub>d t\<^sub>1 e)) = 
    multisubst (map declosure \<Delta>) (Lam\<^sub>d t\<^sub>1 e)"
proof (induction c t and \<Delta> \<Gamma> arbitrary: and e rule: typing_closure\<^sub>c_typing_environment\<^sub>c.inducts)
  case tc\<^sub>c_nil
  thus ?case by (induction \<Delta>') simp_all
next
  case (tc\<^sub>c_cons c t \<Delta> \<Gamma>)
  hence "[] \<turnstile>\<^sub>d declosure c : t" by simp
  hence "insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d declosure c : t" using tc_postpend by fastforce
  with tc\<^sub>c_cons show ?case by (cases \<Gamma>) simp_all
qed simp_all

lemma multisubst_closure_to_lam [dest]: "c :\<^sub>c\<^sub>l tt \<Longrightarrow> 
  Lam\<^sub>d t e = multisubst (map declosure \<Delta>) (declosure c) \<Longrightarrow> \<exists>\<Delta>' e'. c = Lam\<^sub>c t \<Delta>' e' \<and> 
    multisubst (map declosure \<Delta>') (Lam\<^sub>d t e') = multisubst (map declosure \<Delta>) (declosure c)"
proof (induction c)
  case (Lam\<^sub>c t\<^sub>1 \<Delta>' e')
  then obtain t\<^sub>2 \<Gamma> where T: "tt = Arrow t\<^sub>1 t\<^sub>2 \<and> (\<Delta>' :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> (insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e' : t\<^sub>2)" 
    by fastforce
  hence M: "multisubst (map declosure \<Delta>') (Lam\<^sub>d t\<^sub>1 e') = 
      multisubst (map declosure \<Delta>) (multisubst (map declosure \<Delta>') (Lam\<^sub>d t\<^sub>1 e'))" by fastforce
  obtain e2 where E: "multisubst (map declosure \<Delta>') (Lam\<^sub>d t\<^sub>1 e') = Lam\<^sub>d t\<^sub>1 e2" by fastforce
  obtain e3 where "multisubst (map declosure \<Delta>) (Lam\<^sub>d t\<^sub>1 e2) = Lam\<^sub>d t\<^sub>1 e3" by fastforce
  with Lam\<^sub>c M E show ?case by simp
qed simp_all

lemma multisubst_var_to_lam [dest]: "\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> lookup \<Gamma> x = Some tt \<Longrightarrow> 
  Lam\<^sub>d t e = multisubst (map declosure \<Delta>) (Var\<^sub>d x) \<Longrightarrow> 
    \<exists>\<Delta>' e'. lookup \<Delta> x = Some (Lam\<^sub>c t \<Delta>' e') \<and> 
      multisubst (map declosure \<Delta>') (Lam\<^sub>d t e') = multisubst (map declosure \<Delta>) (Var\<^sub>d x)"
proof (induction \<Delta> x arbitrary: \<Gamma> rule: lookup.induct)
  case (2 c \<Delta>)
  moreover then obtain \<Gamma>' where "\<Gamma> = tt # \<Gamma>' \<and> (c :\<^sub>c\<^sub>l tt) \<and> (\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>')" by auto
  ultimately show ?case by auto
qed fastforce+

lemma multisubst_to_lam [dest]: "\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e : t' \<Longrightarrow> 
  Lam\<^sub>d t e' = multisubst (map declosure \<Delta>) e \<Longrightarrow> 
    (\<exists>e''. e = Lam\<^sub>d t e'') \<or> (\<exists>x \<Delta>' e''. e = Var\<^sub>d x \<and> lookup \<Delta> x = Some (Lam\<^sub>c t \<Delta>' e'') \<and> 
      multisubst (map declosure \<Delta>') (Lam\<^sub>d t e'') = Lam\<^sub>d t e')"
proof (induction e)
  case (Lam\<^sub>d t e)
  moreover then obtain e' where "multisubst (map declosure \<Delta>) (Lam\<^sub>d t e) = Lam\<^sub>d t e'" by fastforce
  ultimately show ?case by simp
qed auto

text \<open>Now we can prove correctness:\<close>

theorem correct\<^sub>c [simp]: "declosure_state \<Sigma>\<^sub>c \<leadsto>\<^sub>k \<Sigma>\<^sub>s' \<Longrightarrow> \<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>c'. iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> \<Sigma>\<^sub>s' = declosure_state \<Sigma>\<^sub>c'"
proof (induction "declosure_state \<Sigma>\<^sub>c" \<Sigma>\<^sub>s' rule: eval\<^sub>k.induct)
  case (ev\<^sub>k_const s n)
  then obtain s' \<Delta> e' where S: "s = declosure_stack s' \<and> \<Sigma>\<^sub>c = SE\<^sub>c s' \<Delta> e' \<and> 
    Const\<^sub>d n = multisubst (map declosure \<Delta>) e'" by fastforce
  thus ?case
  proof (cases "e' = Const\<^sub>d n")
    case True
    have "SE\<^sub>c s' \<Delta> (Const\<^sub>d n) \<leadsto>\<^sub>c SC\<^sub>c s' (Const\<^sub>c n)" by simp
    hence "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s' \<Delta> (Const\<^sub>d n)) (SC\<^sub>c s' (Const\<^sub>c n))" by (metis iter_refl iter_step)
    with S True show ?thesis by fastforce
  next
    case False
    with S obtain x where E: "e' = Var\<^sub>d x \<and> lookup \<Delta> x = Some (Const\<^sub>c n)" by fastforce
    hence "SE\<^sub>c s' \<Delta> (Var\<^sub>d x) \<leadsto>\<^sub>c SC\<^sub>c s' (Const\<^sub>c n)" by simp
    hence X: "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s' \<Delta> (Var\<^sub>d x)) (SC\<^sub>c s' (Const\<^sub>c n))" by simp
    from S have "S\<^sub>k True s (Const\<^sub>d n) = declosure_state (SC\<^sub>c s' (Const\<^sub>c n))" by simp
    with S E X show ?thesis by blast
  qed
next
  case (ev\<^sub>k_lam s tt e)
  then obtain s' \<Delta> e' where S: "s = declosure_stack s' \<and> \<Sigma>\<^sub>c = SE\<^sub>c s' \<Delta> e' \<and> 
    Lam\<^sub>d tt e = multisubst (map declosure \<Delta>) e'" by fastforce
  with ev\<^sub>k_lam obtain t' \<Gamma> where T: "(s' :\<^sub>c t' \<rightarrow> t) \<and> (\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> 
    latest_environment s' = Some \<Delta> \<and> \<Gamma> \<turnstile>\<^sub>d e' : t'" by fastforce
  thus ?case
  proof (cases "\<exists>e''. e' = Lam\<^sub>d tt e''")
    case True
    then obtain e'' where E: "e' = Lam\<^sub>d tt e''" by fastforce
    have "SE\<^sub>c s' \<Delta> (Lam\<^sub>d tt e'') \<leadsto>\<^sub>c SC\<^sub>c s' (Lam\<^sub>c tt \<Delta> e'')" by simp
    hence "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s' \<Delta> (Lam\<^sub>d tt e'')) (SC\<^sub>c s' (Lam\<^sub>c tt \<Delta> e''))" 
      by (metis iter_refl iter_step)
    with S E show ?thesis by fastforce
  next
    case False
    with S T obtain x \<Delta>' e'' where E: "e' = Var\<^sub>d x \<and> lookup \<Delta> x = Some (Lam\<^sub>c tt \<Delta>' e'') \<and> 
      multisubst (map declosure \<Delta>') (Lam\<^sub>d tt e'') = Lam\<^sub>d tt e" by blast
    hence "SE\<^sub>c s' \<Delta> (Var\<^sub>d x) \<leadsto>\<^sub>c SC\<^sub>c s' (Lam\<^sub>c tt \<Delta>' e'')" by simp
    hence X: "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s' \<Delta> (Var\<^sub>d x)) (SC\<^sub>c s' (Lam\<^sub>c tt \<Delta>' e''))" by simp
    from S E have "multisubst (map declosure \<Delta>) e' = multisubst (map declosure \<Delta>') (Lam\<^sub>d tt e'')"
      by metis
    with S have "S\<^sub>k True s (Lam\<^sub>d tt e) = declosure_state (SC\<^sub>c s' (Lam\<^sub>c tt \<Delta>' e''))" by simp
    with S E X show ?thesis by blast
  qed
next
  case (ev\<^sub>k_app1 s e\<^sub>1 e\<^sub>2)
  then obtain s' \<Delta> e' where S: "s = declosure_stack s' \<and> \<Sigma>\<^sub>c = SE\<^sub>c s' \<Delta> e' \<and> 
    App\<^sub>d e\<^sub>1 e\<^sub>2 = multisubst (map declosure \<Delta>) e'" by fastforce
  then obtain e\<^sub>1' e\<^sub>2' where E: "e' = App\<^sub>d e\<^sub>1' e\<^sub>2' \<and>
    e\<^sub>1 = multisubst (map declosure \<Delta>) e\<^sub>1' \<and> e\<^sub>2 = multisubst (map declosure \<Delta>) e\<^sub>2'" by fastforce                                                  
  have "SE\<^sub>c s' \<Delta> (App\<^sub>d e\<^sub>1' e\<^sub>2') \<leadsto>\<^sub>c SE\<^sub>c (FApp1\<^sub>c \<Delta> e\<^sub>2' # s') \<Delta> e\<^sub>1'" by simp
  hence "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s' \<Delta> (App\<^sub>d e\<^sub>1' e\<^sub>2')) (SE\<^sub>c (FApp1\<^sub>c \<Delta> e\<^sub>2' # s') \<Delta> e\<^sub>1')" 
    by (metis iter_refl iter_step)
  with S E show ?case by fastforce
next
  case (ev\<^sub>k_app2 e\<^sub>2 s e\<^sub>1)
  then obtain s\<^sub>c c where S: "FApp1\<^sub>k e\<^sub>2 # s = declosure_stack s\<^sub>c \<and> \<Sigma>\<^sub>c = SC\<^sub>c s\<^sub>c c \<and> e\<^sub>1 = declosure c"
    by auto
  then obtain \<Delta>' e\<^sub>2' s\<^sub>c' where S': "s\<^sub>c = FApp1\<^sub>c \<Delta>' e\<^sub>2' # s\<^sub>c' \<and> 
    e\<^sub>2 = multisubst (map declosure \<Delta>') e\<^sub>2' \<and> s = declosure_stack s\<^sub>c'" by fastforce
  have "SC\<^sub>c (FApp1\<^sub>c \<Delta>' e\<^sub>2' # s\<^sub>c') c \<leadsto>\<^sub>c SE\<^sub>c (FApp2\<^sub>c c # s\<^sub>c') \<Delta>' e\<^sub>2'" by simp
  hence "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FApp1\<^sub>c \<Delta>' e\<^sub>2' # s\<^sub>c') c) (SE\<^sub>c (FApp2\<^sub>c c # s\<^sub>c') \<Delta>' e\<^sub>2')" 
    by (metis iter_refl iter_step)
  with S S' show ?case by fastforce
next
  case (ev\<^sub>k_app3 t\<^sub>1 e\<^sub>1 s e\<^sub>2)
  then obtain s\<^sub>c c\<^sub>2 where S: "FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1) # s = declosure_stack s\<^sub>c \<and> \<Sigma>\<^sub>c = SC\<^sub>c s\<^sub>c c\<^sub>2 \<and> 
    e\<^sub>2 = declosure c\<^sub>2" by auto
  then obtain c s\<^sub>c' where S': "s\<^sub>c = FApp2\<^sub>c c # s\<^sub>c' \<and> Lam\<^sub>d t\<^sub>1 e\<^sub>1 = declosure c \<and> 
    s = declosure_stack s\<^sub>c'" by fastforce
  from ev\<^sub>k_app3 S S' obtain t' t\<^sub>2 \<Delta> where T: "(c :\<^sub>c\<^sub>l Arrow t' t\<^sub>2) \<and> (s\<^sub>c' :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> 
    latest_environment s\<^sub>c' = Some \<Delta> \<and> c\<^sub>2 :\<^sub>c\<^sub>l t'" by fastforce
  with S' obtain \<Delta>' e\<^sub>1' where C: "c = Lam\<^sub>c t\<^sub>1 \<Delta>' e\<^sub>1' \<and> 
    multisubst (map declosure \<Delta>') (Lam\<^sub>d t\<^sub>1 e\<^sub>1') = Lam\<^sub>d t\<^sub>1 e\<^sub>1 \<and> ([t\<^sub>1] \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2) \<and> t' = t\<^sub>1 \<and>
    (\<forall>e\<^sub>2. ([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<longrightarrow> multisubst (map declosure \<Delta>') (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1') = subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)" 
      by (metis declose_to_lam)
  with T S have "subst\<^sub>d 0 e\<^sub>2 e\<^sub>1 = multisubst (map declosure \<Delta>') (subst\<^sub>d 0 (declosure c\<^sub>2) e\<^sub>1')" 
    by simp
  with S S' have X: "S\<^sub>k False (FReturn\<^sub>k # s) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1) = 
    declosure_state (SE\<^sub>c (FReturn\<^sub>c (c\<^sub>2 # \<Delta>') # s\<^sub>c') (c\<^sub>2 # \<Delta>') e\<^sub>1')" by simp
  have "SC\<^sub>c (FApp2\<^sub>c (Lam\<^sub>c t\<^sub>1 \<Delta>' e\<^sub>1') # s\<^sub>c') c\<^sub>2 \<leadsto>\<^sub>c SE\<^sub>c (FReturn\<^sub>c (c\<^sub>2 # \<Delta>') # s\<^sub>c') (c\<^sub>2 # \<Delta>') e\<^sub>1'"
    by simp
  with S S' C X show ?case by (metis iter_step iter_refl)
next
  case (ev\<^sub>k_ret s e)
  then obtain s\<^sub>c c where S: "FReturn\<^sub>k # s = declosure_stack s\<^sub>c \<and> \<Sigma>\<^sub>c = SC\<^sub>c s\<^sub>c c \<and> e = declosure c" 
    by fastforce
  then obtain \<Delta> s\<^sub>c' where S': "s\<^sub>c = FReturn\<^sub>c \<Delta> # s\<^sub>c'" by fastforce
  have "SC\<^sub>c (FReturn\<^sub>c \<Delta> # s\<^sub>c') c \<leadsto>\<^sub>c SC\<^sub>c s\<^sub>c' c" by simp
  hence "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FReturn\<^sub>c \<Delta> # s\<^sub>c') c) (SC\<^sub>c s\<^sub>c' c)" by (metis iter_refl iter_step)
  with S S' show ?case by fastforce
qed

lemma correct\<^sub>c_iter [simp]: "iter (\<leadsto>\<^sub>k) (declosure_state \<Sigma>\<^sub>c) \<Sigma>\<^sub>s' \<Longrightarrow> \<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>c'. iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> \<Sigma>\<^sub>s' = declosure_state \<Sigma>\<^sub>c'"
proof (induction "declosure_state \<Sigma>\<^sub>c" \<Sigma>\<^sub>s' arbitrary: \<Sigma>\<^sub>c rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>s' \<Sigma>\<^sub>s'')
  moreover then obtain \<Sigma>\<^sub>c' where X: "iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> \<Sigma>\<^sub>s' = declosure_state \<Sigma>\<^sub>c'" by fastforce
  moreover with iter_step have "\<Sigma>\<^sub>c' :\<^sub>c t" by fastforce
  ultimately obtain \<Sigma>\<^sub>c'' where "iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c' \<Sigma>\<^sub>c'' \<and> \<Sigma>\<^sub>s'' = declosure_state \<Sigma>\<^sub>c''" by fastforce
  with X have "iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c'' \<and> \<Sigma>\<^sub>s'' = declosure_state \<Sigma>\<^sub>c''" by (metis iter_append)
  thus ?case by fastforce
qed force+

lemma correct\<^sub>c_full_eval [simp]: "\<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow> iter (\<leadsto>\<^sub>k) (declosure_state \<Sigma>\<^sub>c) (S\<^sub>k True [] v) \<Longrightarrow> 
  \<exists>c. iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c (SC\<^sub>c [] c) \<and> declosure c = v"
proof -
  assume TC: "\<Sigma>\<^sub>c :\<^sub>c t" and "iter (\<leadsto>\<^sub>k) (declosure_state \<Sigma>\<^sub>c) (S\<^sub>k True [] v)"
  then obtain \<Sigma>\<^sub>c' where E: "iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> S\<^sub>k True [] v = declosure_state \<Sigma>\<^sub>c'" by fastforce
  then obtain s' c where "[] = declosure_stack s' \<and> \<Sigma>\<^sub>c' = SC\<^sub>c s' c \<and> v = declosure c" by fastforce
  hence "(\<exists>\<Delta> e. \<Sigma>\<^sub>c' = SE\<^sub>c [] \<Delta> e \<and> v = multisubst (map declosure \<Delta>) e) \<or> 
    (\<exists>c. \<Sigma>\<^sub>c' = SC\<^sub>c [] c \<and> v = declosure c)" by auto
  with E show ?thesis by fastforce
qed

end