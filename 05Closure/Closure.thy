theory Closure
  imports "../03Debruijn/LetFloating" "../00Utils/Iteration"
begin

section \<open>Closures\<close>

text \<open>Stack evaluation got rid of one source of recursive tree-walking in our evaluation relation, 
but another remains: substitution itself. In this stage, we eliminate substitution, replacing it 
with lookups into explicit environments. This would be simple, except for lambda-abstractions, which
can be passed around as values, yet contain variables that might have been substituted in for 
somewhere else long ago. Fortunately this is a long-solved problem. The solution is the closure, a 
block of code with a private environment it carries around with it, and which can represent a 
function value: the substituted variables are exactly those in the closure's environment. For us, 
not having defined any code yet, closures will be expressions with attached environments, but the 
idea remains the same.\<close>

text \<open>We call all these distinguished-datatype values "closure-values", even the ones (like 
\<open>Const\<^sub>c\<close>) that manifestly do not need to carry an environment; this is just to give them a name. 
Closure environments, incidentally, are just lists of closure-values, indexed by the variables they 
replace.\<close>

datatype closure\<^sub>c = 
  Const\<^sub>c nat
  | Lam\<^sub>c ty "closure\<^sub>c list" expr\<^sub>d

text \<open>Typing closure-values and environments are for the most part easy. The one key thing to note 
is that in a closure proper, \<open>Lam\<^sub>c t \<Delta> e\<close>, e is almost but not quite a closed expression; it 
represents a function body and so has a single variable not in \<Delta>, to be replaced by its eventual 
argument.\<close>

inductive typing_closure\<^sub>c :: "closure\<^sub>c \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>c\<^sub>l" 50)
      and typing_environment\<^sub>c :: "closure\<^sub>c list \<Rightarrow> ty list \<Rightarrow> bool" (infix ":\<^sub>c\<^sub>l\<^sub>s" 50) where
  tc\<^sub>c_const [simp]: "Const\<^sub>c n :\<^sub>c\<^sub>l Num"
| tc\<^sub>c_lam [simp]: "\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e : t\<^sub>2 \<Longrightarrow> let_floated\<^sub>d e \<Longrightarrow> 
    Lam\<^sub>c t\<^sub>1 \<Delta> e :\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2"
| tc\<^sub>c_nil [simp]: "[] :\<^sub>c\<^sub>l\<^sub>s []"
| tc\<^sub>c_cons [simp]: "c :\<^sub>c\<^sub>l t \<Longrightarrow> \<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> c # \<Delta> :\<^sub>c\<^sub>l\<^sub>s t # \<Gamma>"

inductive_cases [elim]:"Const\<^sub>c n :\<^sub>c\<^sub>l t"
inductive_cases [elim]: "Lam\<^sub>c t\<^sub>1 \<Delta> e :\<^sub>c\<^sub>l t"
inductive_cases [elim]: "[] :\<^sub>c\<^sub>l\<^sub>s \<Gamma>"
inductive_cases [elim]: "c # \<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>"

lemma tc_env_append [simp]: "length \<Delta> = length \<Gamma> \<Longrightarrow> \<Delta> @ \<Delta>' :\<^sub>c\<^sub>l\<^sub>s \<Gamma> @ \<Gamma>' = (\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<and> \<Delta>' :\<^sub>c\<^sub>l\<^sub>s \<Gamma>')"
proof (induction \<Delta> arbitrary: \<Gamma>)
  case Nil
  thus ?case by (induction \<Gamma>) simp_all
next
  case (Cons c \<Delta>)
  thus ?case by (induction \<Gamma>) auto
qed

lemma  "c :\<^sub>c\<^sub>l t \<Longrightarrow> True"
  and lookup_in_env\<^sub>c [simp]: "\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> lookup \<Gamma> x = Some t \<Longrightarrow> \<exists>c. lookup \<Delta> x = Some c \<and> c :\<^sub>c\<^sub>l t"
proof (induction c t and \<Delta> \<Gamma> arbitrary: and x rule: typing_closure\<^sub>c_typing_environment\<^sub>c.inducts)
  case (tc\<^sub>c_cons c t \<Delta> \<Gamma>)
  thus ?case by (cases x) simp_all
qed simp_all

lemma canonical_num\<^sub>c [dest]: "c :\<^sub>c\<^sub>l Num \<Longrightarrow> \<exists>n. c = Const\<^sub>c n"
  by (induction c Num rule: typing_closure\<^sub>c_typing_environment\<^sub>c.inducts(1)) simp_all

lemma canonical_arrow\<^sub>c [dest]: "c :\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> 
    \<exists>\<Delta> \<Gamma> e. c = Lam\<^sub>c t\<^sub>1 \<Delta> e \<and> (\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> (insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e : t\<^sub>2)"
  by (induction c "Arrow t\<^sub>1 t\<^sub>2" rule: typing_closure\<^sub>c_typing_environment\<^sub>c.inducts(1)) auto

text \<open>Our stack frames, meanwhile, have become much more complicated. Because the environment of an 
expression is no longer just implicitly there by substitution, we need to record the current 
environment for the unevaluated expression in \<open>FApp1\<^sub>c\<close>. Because the expression in \<open>FApp2\<^sub>c\<close> is always 
evaluated, we replace it with a closure-value. Finally, in \<open>FReturn\<^sub>c\<close>, we record the environment 
again - this will be necessary in the next stage. We also provide a utility to get the nearest 
enclosing environment: that is, the one recorded by the last \<open>FReturn\<^sub>c\<close> pushed on the stack.\<close>

datatype frame\<^sub>c = 
  FApp1\<^sub>c "closure\<^sub>c list" expr\<^sub>d
  | FApp2\<^sub>c closure\<^sub>c
  | FLet\<^sub>c "closure\<^sub>c list" expr\<^sub>d
  | FReturn\<^sub>c "closure\<^sub>c list"

fun latest_environment\<^sub>c :: "frame\<^sub>c list \<rightharpoonup> closure\<^sub>c list" where
  "latest_environment\<^sub>c [] = None"
| "latest_environment\<^sub>c (FApp1\<^sub>c \<Delta> e # s) = latest_environment\<^sub>c s"
| "latest_environment\<^sub>c (FApp2\<^sub>c c # s) = latest_environment\<^sub>c s"
| "latest_environment\<^sub>c (FLet\<^sub>c \<Delta> e # s) = latest_environment\<^sub>c s"
| "latest_environment\<^sub>c (FReturn\<^sub>c \<Delta> # s) = Some \<Delta>"

fun return_headed\<^sub>c :: "frame\<^sub>c list \<Rightarrow> bool" where
  "return_headed\<^sub>c (FReturn\<^sub>c \<Delta> # s) = True"
| "return_headed\<^sub>c s = False"

lemma return_headed_elim [dest]: "return_headed\<^sub>c s \<Longrightarrow> \<exists>s' \<Delta>. s = FReturn\<^sub>c \<Delta> # s'"
  by (cases s rule: return_headed\<^sub>c.cases) simp_all

text \<open>Typing a stack is about the same as it was last time, given the changes to the frames. But 
there are a couple of points that might seem unnecessary: we check that the latest environment 
matches the stored one in \<open>FApp1\<^sub>c\<close> frames; we have nothing to compare it against in \<open>FApp2\<^sub>c\<close>, but 
check that it at least exists there; and we check that the environment types to something in 
\<open>FReturn\<^sub>c\<close>. None of these are necessary for the safety proofs here, or the correctness proofs when 
converting from the stack stage (we could, with sufficient effort, prove them as theorems), but the 
extra structure guaranteed by these checks will be useful in the next stage.\<close>

inductive typing_stack\<^sub>c :: "frame\<^sub>c list \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>c _ \<rightarrow>" 50) where
  tcc_snil [simp]: "[] :\<^sub>c t \<rightarrow> t"
| tcc_scons_app1 [simp]: "\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e : t\<^sub>1 \<Longrightarrow> let_floated\<^sub>d e \<Longrightarrow> let_free\<^sub>d e \<Longrightarrow> 
    s :\<^sub>c t\<^sub>2 \<rightarrow> t \<Longrightarrow> latest_environment\<^sub>c s = Some \<Delta> \<Longrightarrow> FApp1\<^sub>c \<Delta> e # s :\<^sub>c Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t"
| tcc_scons_app2 [simp]: "c :\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> s :\<^sub>c t\<^sub>2 \<rightarrow> t \<Longrightarrow> latest_environment\<^sub>c s \<noteq> None \<Longrightarrow> 
    FApp2\<^sub>c c # s :\<^sub>c t\<^sub>1 \<rightarrow> t"
| tcc_scons_let [simp]: "latest_environment\<^sub>c s = Some \<Delta> \<Longrightarrow> \<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> 
    insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e : t\<^sub>2 \<Longrightarrow> let_floated\<^sub>d e \<Longrightarrow> s :\<^sub>c t\<^sub>2 \<rightarrow> t \<Longrightarrow> return_headed\<^sub>c s \<Longrightarrow> 
    FLet\<^sub>c \<Delta> e # s :\<^sub>c t\<^sub>1 \<rightarrow> t"
| tcc_scons_ret [simp]: "\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> s :\<^sub>c t' \<rightarrow> t \<Longrightarrow> FReturn\<^sub>c \<Delta> # s :\<^sub>c t' \<rightarrow> t"

inductive_cases [elim]: "[] :\<^sub>c t' \<rightarrow> t"
inductive_cases [elim]: "FApp1\<^sub>c \<Delta> e # s :\<^sub>c t' \<rightarrow> t"
inductive_cases [elim]: "FApp2\<^sub>c c # s :\<^sub>c t' \<rightarrow> t"
inductive_cases [elim]: "FLet\<^sub>c \<Delta> e # s :\<^sub>c t' \<rightarrow> t"
inductive_cases [elim]: "FReturn\<^sub>c \<Delta> # s :\<^sub>c t' \<rightarrow> t"

text \<open>The evaluation state has also been complicated a little. Because expressions and 
closure-values are now two distinct datatypes, the evaluated flag has been replaced by two distinct 
data constructors, one with an expression and environment to be evaluated, the other with a 
closure-value to be returned. Both, of course, retain the call stack.\<close>

datatype state\<^sub>c = 
  SE\<^sub>c "frame\<^sub>c list" "closure\<^sub>c list" expr\<^sub>d
  | SC\<^sub>c "frame\<^sub>c list" closure\<^sub>c

primrec final\<^sub>c :: "state\<^sub>c \<Rightarrow> bool" where
  "final\<^sub>c (SE\<^sub>c s \<Delta> e) = False"
| "final\<^sub>c (SC\<^sub>c s c) = (s = [])"

text \<open>Typechecking the state remains much the same, with again a seemingly-redundant environment
consistency check that will be useful to us later.\<close>

inductive typecheck_state\<^sub>c :: "state\<^sub>c \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>c" 50) where
  tcc_state_ev [simp]: "s :\<^sub>c t' \<rightarrow> t \<Longrightarrow> \<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> latest_environment\<^sub>c s = Some \<Delta> \<Longrightarrow> 
    \<Gamma> \<turnstile>\<^sub>d e : t' \<Longrightarrow> let_floated\<^sub>d e \<Longrightarrow> let_free\<^sub>d e \<or> return_headed\<^sub>c s \<Longrightarrow> SE\<^sub>c s \<Delta> e :\<^sub>c t"
| tcc_state_ret [simp]: "s :\<^sub>c t' \<rightarrow> t \<Longrightarrow> c :\<^sub>c\<^sub>l t' \<Longrightarrow> SC\<^sub>c s c :\<^sub>c t"

inductive_cases [elim]: "SE\<^sub>c s \<Delta> e :\<^sub>c t"
inductive_cases [elim]: "SC\<^sub>c s c :\<^sub>c t"

text \<open>Evaluation now makes use of the environments, shuffling them between the state environment 
slot and the stack frames, and looking up variables in them as appropriate. (Although the state as a 
whole has no free variables, for the first time, the expression under examination might.)\<close>

inductive eval\<^sub>c :: "state\<^sub>c \<Rightarrow> state\<^sub>c \<Rightarrow> bool" (infix "\<leadsto>\<^sub>c" 50) where
  ev\<^sub>c_var [simp]: "lookup \<Delta> x = Some c \<Longrightarrow> SE\<^sub>c s \<Delta> (Var\<^sub>d x) \<leadsto>\<^sub>c SC\<^sub>c s c"
| ev\<^sub>c_con [simp]: "SE\<^sub>c s \<Delta> (Const\<^sub>d n) \<leadsto>\<^sub>c SC\<^sub>c s (Const\<^sub>c n)"
| ev\<^sub>c_lam [simp]: "SE\<^sub>c s \<Delta> (Lam\<^sub>d t e) \<leadsto>\<^sub>c SC\<^sub>c s (Lam\<^sub>c t \<Delta> e)"
| ev\<^sub>c_app [simp]: "SE\<^sub>c s \<Delta> (App\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>c SE\<^sub>c (FApp1\<^sub>c \<Delta> e\<^sub>2 # s) \<Delta> e\<^sub>1"
| ev\<^sub>c_let [simp]: "SE\<^sub>c (FReturn\<^sub>c \<Delta> # s) \<Delta> (Let\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>c SE\<^sub>c (FLet\<^sub>c \<Delta> e\<^sub>2 # FReturn\<^sub>c \<Delta> # s) \<Delta> e\<^sub>1"
| ret\<^sub>c_app1 [simp]: "SC\<^sub>c (FApp1\<^sub>c \<Delta> e\<^sub>2 # s) c\<^sub>1 \<leadsto>\<^sub>c SE\<^sub>c (FApp2\<^sub>c c\<^sub>1 # s) \<Delta> e\<^sub>2"
| ret\<^sub>c_app2 [simp]: "SC\<^sub>c (FApp2\<^sub>c (Lam\<^sub>c t \<Delta> e\<^sub>1) # s) c\<^sub>2 \<leadsto>\<^sub>c SE\<^sub>c (FReturn\<^sub>c (c\<^sub>2 # \<Delta>) # s) (c\<^sub>2 # \<Delta>) e\<^sub>1"
| ret\<^sub>c_let [simp]: "SC\<^sub>c (FLet\<^sub>c \<Delta> e\<^sub>2 # FReturn\<^sub>c \<Delta> # s) c\<^sub>1 \<leadsto>\<^sub>c SE\<^sub>c (FReturn\<^sub>c (c\<^sub>1 # \<Delta>) # s) (c\<^sub>1 # \<Delta>) e\<^sub>2"
| ret\<^sub>c_ret [simp]: "SC\<^sub>c (FReturn\<^sub>c \<Delta> # s) c \<leadsto>\<^sub>c SC\<^sub>c s c"

text \<open>And the safety theorems:\<close>

lemma eval\<^sub>c_from_nonvalue [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> let_free\<^sub>d e \<or> return_headed\<^sub>c s \<Longrightarrow> \<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> 
  latest_environment\<^sub>c s = Some \<Delta> \<Longrightarrow> \<exists>\<Sigma>'. SE\<^sub>c s \<Delta> e \<leadsto>\<^sub>c \<Sigma>'"
proof (induction \<Gamma> e t rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_var \<Gamma> x t)
  then obtain c where "lookup \<Delta> x = Some c \<and> c :\<^sub>c\<^sub>l t" by fastforce
  hence "SE\<^sub>c s \<Delta> (Var\<^sub>d x) \<leadsto>\<^sub>c SC\<^sub>c s c" by simp
  thus ?case by fastforce 
next
  case (tc\<^sub>d_const \<Gamma> n)
  have "SE\<^sub>c s \<Delta> (Const\<^sub>d n) \<leadsto>\<^sub>c SC\<^sub>c s (Const\<^sub>c n)" by simp
  thus ?case by fastforce 
next
  case (tc\<^sub>d_lam t\<^sub>1 \<Gamma> e t\<^sub>2)
  have "SE\<^sub>c s \<Delta> (Lam\<^sub>d t\<^sub>1 e) \<leadsto>\<^sub>c SC\<^sub>c s (Lam\<^sub>c t\<^sub>1 \<Delta> e)" by simp
  thus ?case by fastforce 
next
  case (tc\<^sub>d_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  have "SE\<^sub>c s \<Delta> (App\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>c SE\<^sub>c (FApp1\<^sub>c \<Delta> e\<^sub>2 # s) \<Delta> e\<^sub>1" by simp
  thus ?case by fastforce
next
  case (tc\<^sub>d_let \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
  then obtain s' where "s = FReturn\<^sub>c \<Delta> # s'" by auto
  hence "SE\<^sub>c s \<Delta> (Let\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>c SE\<^sub>c (FLet\<^sub>c \<Delta> e\<^sub>2 # s) \<Delta> e\<^sub>1" by simp
  thus ?case by fastforce
qed

lemma eval\<^sub>c_from_value [simp]: "s :\<^sub>c t' \<rightarrow> t \<Longrightarrow> c :\<^sub>c\<^sub>l t' \<Longrightarrow> s = [] \<or> (\<exists>\<Sigma>'. SC\<^sub>c s c \<leadsto>\<^sub>c \<Sigma>')"
proof (induction s t' t rule: typing_stack\<^sub>c.induct)
  case (tcc_scons_app1 \<Delta> \<Gamma> e\<^sub>2 t\<^sub>1 s t\<^sub>2 t)
  moreover hence "SC\<^sub>c (FApp1\<^sub>c \<Delta> e\<^sub>2 # s) c \<leadsto>\<^sub>c SE\<^sub>c (FApp2\<^sub>c c # s) \<Delta> e\<^sub>2" by simp
  ultimately show ?case by fastforce
next
  case (tcc_scons_app2 c\<^sub>1 t\<^sub>1 t\<^sub>2 s t)
  then obtain \<Delta> ts e where "c\<^sub>1 = Lam\<^sub>c t\<^sub>1 \<Delta> e \<and> (\<Delta> :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (insert_at 0 t\<^sub>1 ts \<turnstile>\<^sub>d e : t\<^sub>2)" 
    by blast
  moreover hence "SC\<^sub>c (FApp2\<^sub>c (Lam\<^sub>c t\<^sub>1 \<Delta> e) # s) c \<leadsto>\<^sub>c SE\<^sub>c (FReturn\<^sub>c (c # \<Delta>) # s) (c # \<Delta>) e" by simp
  ultimately show ?case by fastforce
next
  case (tcc_scons_let s \<Delta> \<Gamma> t\<^sub>1 e t\<^sub>2 t)
  then obtain s' where S: "s = FReturn\<^sub>c \<Delta> # s'" by auto
  moreover have "SC\<^sub>c (FLet\<^sub>c \<Delta> e # FReturn\<^sub>c \<Delta> # s') c \<leadsto>\<^sub>c SE\<^sub>c (FReturn\<^sub>c (c # \<Delta>) # s') (c # \<Delta>) e" 
    by simp
  ultimately show ?case by fastforce
next
  case (tcc_scons_ret \<Delta> \<Gamma> s t' t)
  have "SC\<^sub>c (FReturn\<^sub>c \<Delta> # s) c \<leadsto>\<^sub>c SC\<^sub>c s c" by simp
  thus ?case by fastforce
qed simp_all

theorem progress\<^sub>c: "\<Sigma> :\<^sub>c t \<Longrightarrow> final\<^sub>c \<Sigma> \<or> (\<exists>\<Sigma>'. \<Sigma> \<leadsto>\<^sub>c \<Sigma>')"
  by (induction \<Sigma> t rule: typecheck_state\<^sub>c.induct) simp_all

lemma final_no_eval\<^sub>c [simp]: "\<Sigma> \<leadsto>\<^sub>c \<Sigma>' \<Longrightarrow> final\<^sub>c \<Sigma> \<Longrightarrow> False"
  by (induction \<Sigma> \<Sigma>' rule: eval\<^sub>c.induct) simp_all

theorem preservation\<^sub>c [simp]: "\<Sigma> \<leadsto>\<^sub>c \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow> \<Sigma>' :\<^sub>c t"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>c.induct)
  case (ev\<^sub>c_var \<Delta> x c s)
  then obtain t' \<Gamma> where X: "s :\<^sub>c t' \<rightarrow> t" and "(\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> lookup \<Gamma> x = Some t'" by blast
  then obtain c' where "lookup \<Delta> x = Some c' \<and> c' :\<^sub>c\<^sub>l t'" by fastforce
  with ev\<^sub>c_var X show ?case by simp
next
  case (ev\<^sub>c_app s \<Delta> e\<^sub>1 e\<^sub>2)
  then obtain t\<^sub>1 t\<^sub>2 \<Gamma> where "(s :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> (\<Gamma> \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1)" 
   and X: "(\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> latest_environment\<^sub>c s = Some \<Delta> \<and> (\<Gamma> \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2) \<and> let_free\<^sub>d e\<^sub>1 \<and> 
    let_free\<^sub>d e\<^sub>2 \<and> (is_var\<^sub>d e\<^sub>1 \<or> value\<^sub>d e\<^sub>1) \<and> let_floated\<^sub>d e\<^sub>1 \<and> let_floated\<^sub>d e\<^sub>2" by fastforce
  hence "FApp1\<^sub>c \<Delta> e\<^sub>2 # s :\<^sub>c Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t"  by fastforce
  with X show ?case by fastforce
next
  case (ev\<^sub>c_let \<Delta> s e\<^sub>1 e\<^sub>2)
  then obtain \<Gamma> t\<^sub>2 t\<^sub>1 where "(s :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> (insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>2)" 
    and X: "(\<Gamma> \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>1) \<and> (\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> let_free\<^sub>d e\<^sub>1 \<and> let_floated\<^sub>d e\<^sub>1 \<and> let_floated\<^sub>d e\<^sub>2" 
      by fastforce
  hence "FLet\<^sub>c \<Delta> e\<^sub>2 # FReturn\<^sub>c \<Delta> # s :\<^sub>c t\<^sub>1 \<rightarrow> t" by fastforce
  with X show ?case by fastforce
next
  case (ret\<^sub>c_app1 \<Delta> e\<^sub>2 s c\<^sub>1)
  then obtain \<Gamma> t\<^sub>1 t\<^sub>2 where X: "(\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> latest_environment\<^sub>c s = Some \<Delta> \<and> (\<Gamma> \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<and> 
    let_floated\<^sub>d e\<^sub>2 \<and> let_free\<^sub>d e\<^sub>2" and "(s :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> (c\<^sub>1 :\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2)" by blast
  hence "FApp2\<^sub>c c\<^sub>1 # s :\<^sub>c t\<^sub>1 \<rightarrow> t" by fastforce
  with X show ?case by fastforce
next
  case (ret\<^sub>c_app2 t\<^sub>1 \<Delta> e\<^sub>1 s c\<^sub>2)
  then obtain \<Gamma> t\<^sub>2 where X: "s :\<^sub>c t\<^sub>2 \<rightarrow> t" and Y: "(insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2) \<and> let_floated\<^sub>d e\<^sub>1" 
   and "(\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> (c\<^sub>2 :\<^sub>c\<^sub>l t\<^sub>1)" by blast
  hence Z: "c\<^sub>2 # \<Delta> :\<^sub>c\<^sub>l\<^sub>s insert_at 0 t\<^sub>1 \<Gamma>" by (induction \<Gamma>) simp_all
  with X have "FReturn\<^sub>c (c\<^sub>2 # \<Delta>) # s :\<^sub>c t\<^sub>2 \<rightarrow> t" by simp
  with Y Z show ?case by fastforce
next
  case (ret\<^sub>c_let \<Delta> e\<^sub>2 s c\<^sub>1)
  then obtain t\<^sub>1 where "(FLet\<^sub>c \<Delta> e\<^sub>2 # FReturn\<^sub>c \<Delta> # s :\<^sub>c t\<^sub>1 \<rightarrow> t) \<and> c\<^sub>1 :\<^sub>c\<^sub>l t\<^sub>1" by fastforce
  then obtain \<Gamma> t\<^sub>1 t\<^sub>2 where X: "insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>2" and "\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>" and "c\<^sub>1 :\<^sub>c\<^sub>l t\<^sub>1" 
    and Y: "s :\<^sub>c t\<^sub>2 \<rightarrow> t" and Z: "let_floated\<^sub>d e\<^sub>2" by fastforce
  hence W: "c\<^sub>1 # \<Delta> :\<^sub>c\<^sub>l\<^sub>s insert_at 0 t\<^sub>1 \<Gamma>" by (cases \<Gamma>) simp_all
  with Y have "FReturn\<^sub>c (c\<^sub>1 # \<Delta>) # s :\<^sub>c t\<^sub>2 \<rightarrow> t" by simp
  with X Z W show ?case by fastforce
qed fastforce+

lemma preservation\<^sub>c_iter [simp]: "iter (\<leadsto>\<^sub>c) \<Sigma> \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow> \<Sigma>' :\<^sub>c t"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

theorem determinism\<^sub>c: "\<Sigma> \<leadsto>\<^sub>c \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>c \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>c.induct)
  case (ev\<^sub>c_var \<Delta> x c s)
  from ev\<^sub>c_var(2, 1) show ?case by (induction rule: eval\<^sub>c.cases) simp_all 
next
  case (ev\<^sub>c_con s \<Delta> k)
  thus ?case by (induction rule: eval\<^sub>c.cases) simp_all 
next
  case (ev\<^sub>c_lam s \<Delta> t e)
  thus ?case by (induction rule: eval\<^sub>c.cases) simp_all 
next
  case (ev\<^sub>c_app s \<Delta> e\<^sub>1 e\<^sub>2)
  thus ?case by (induction rule: eval\<^sub>c.cases) simp_all 
next
  case (ev\<^sub>c_let s \<Delta> e\<^sub>1 e\<^sub>2)
  thus ?case by (induction rule: eval\<^sub>c.cases) simp_all 
next
  case (ret\<^sub>c_app1 \<Delta> e\<^sub>2 s c\<^sub>1)
  thus ?case by (induction rule: eval\<^sub>c.cases) simp_all 
next
  case (ret\<^sub>c_app2 t \<Delta> e\<^sub>1 s c\<^sub>2)
  thus ?case by (induction rule: eval\<^sub>c.cases) simp_all 
next
  case (ret\<^sub>c_let \<Delta> e\<^sub>2 s c\<^sub>1)
  thus ?case by (induction rule: eval\<^sub>c.cases) simp_all 
next
  case (ret\<^sub>c_ret \<Delta> s c)
  thus ?case by (induction rule: eval\<^sub>c.cases) simp_all 
qed

end