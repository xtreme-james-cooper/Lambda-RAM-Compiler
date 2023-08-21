theory Stack
  imports "../03Debruijn/LetFloating" "../00Utils/Iteration"
begin

section \<open>Stack Evaluation\<close>

text \<open>Even with the small-step Debruijn-substitution evaluation, we still have a very complex 
evaluation relation, and one that is still not far-removed from the world of semantic definitions. 
(Indeed, Pierce [5] and Harper [6] both use a style much like this for their books, and the very 
early versions of this program began here with what is now stage 3.) For the remainder of this 
paper, we descend through a series of increasingly low-level evaluation states, with correspondingly 
simplified evaluation relations.\<close>

text \<open>The first thing to get rid of is our evaluation premises: we implicitly search the expression 
for the first redex with each step. By making this search explicit via a stack of evaluation frames, 
we can make every evaluation step immediate, acting directly on the expression in the state. We also 
take the opportunity to get rid of explicitly testing expressions for being values.\<close>

text \<open>There are only three things to search through, the left and right subexpressions of an \<open>App\<^sub>d\<close>, 
and the left subexpression of a \<open>Let\<^sub>d\<close>, so there is a frame for each, recording our position in the 
search. The \<open>FReturn\<^sub>k\<close> frame is not strictly necessary for this stage, but recording each time we 
change the implicit evaluation environment will make future stages possible.\<close>

datatype frame\<^sub>k = 
  FApp1\<^sub>k expr\<^sub>d
  | FApp2\<^sub>k expr\<^sub>d
  | FLet\<^sub>k expr\<^sub>d
  | FReturn\<^sub>k

text \<open>Typing a stack is simple. Since the stack represents, in effect, an expression with a hole in 
it for the subexpression under evaluation, it takes a type for that inner expression and returns a 
type for the type of the stack and expression together. Since the stack has no binders and is always
created from a closed expression, we do not need a typing context, either. Note that since we only 
ever search the left side of an \<open>App\<^sub>d\<close> when the right is a value, we enforce that the expression 
stored in a \<open>FApp2\<^sub>k\<close> frame must be a value too; we also retain our let-floating invariants. We are 
also able to guarantee that there is always an \<open>FReturn\<^sub>c\<close> frame above an \<open>FLet\<^sub>c\<close> because all our 
expressions have been let-floated - indeed, this property is precisely what it means to be 
let-floated in a stack context\<close>

fun return_headed\<^sub>k :: "frame\<^sub>k list \<Rightarrow> bool" where
  "return_headed\<^sub>k (FReturn\<^sub>k # s) = True"
| "return_headed\<^sub>k s = False"

lemma return_headed_elim [dest]: "return_headed\<^sub>k s \<Longrightarrow> \<exists>s'. s = FReturn\<^sub>k # s'"
  by (cases s rule: return_headed\<^sub>k.cases) simp_all

lemma return_headed_append [simp]: "return_headed\<^sub>k (s @ s') = 
    (return_headed\<^sub>k s \<or> (s = [] \<and> return_headed\<^sub>k s'))"
  by (cases s rule: return_headed\<^sub>k.cases) simp_all

inductive typing_stack\<^sub>k :: "frame\<^sub>k list \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>k _ \<rightarrow>" 50) where
  tcs\<^sub>k_nil [simp]: "[] :\<^sub>k t \<rightarrow> t"
| tcs\<^sub>k_cons_app1 [simp]: "[] \<turnstile>\<^sub>d e : t\<^sub>1 \<Longrightarrow> let_floated\<^sub>d e \<Longrightarrow> let_free\<^sub>d e \<Longrightarrow> s :\<^sub>k t\<^sub>2 \<rightarrow> t \<Longrightarrow> 
    FApp1\<^sub>k e # s :\<^sub>k Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t"
| tcs\<^sub>k_cons_app2 [simp]: "[] \<turnstile>\<^sub>d e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> let_floated\<^sub>d e \<Longrightarrow> value\<^sub>d e \<Longrightarrow> s :\<^sub>k t\<^sub>2 \<rightarrow> t \<Longrightarrow> 
    FApp2\<^sub>k e # s :\<^sub>k t\<^sub>1 \<rightarrow> t"
| tcs\<^sub>k_cons_let [simp]: "[t\<^sub>1] \<turnstile>\<^sub>d e : t\<^sub>2 \<Longrightarrow> let_floated\<^sub>d e \<Longrightarrow> s :\<^sub>k t\<^sub>2 \<rightarrow> t \<Longrightarrow> return_headed\<^sub>k s \<Longrightarrow>
    FLet\<^sub>k e # s :\<^sub>k t\<^sub>1 \<rightarrow> t"
| tcs\<^sub>k_cons_ret [simp]: "s :\<^sub>k t' \<rightarrow> t \<Longrightarrow> FReturn\<^sub>k # s :\<^sub>k t' \<rightarrow> t"

inductive_cases [elim]: "[] :\<^sub>k t' \<rightarrow> t"
inductive_cases [elim]: "FApp1\<^sub>k e # s :\<^sub>k t' \<rightarrow> t"
inductive_cases [elim]: "FApp2\<^sub>k e # s :\<^sub>k t' \<rightarrow> t"
inductive_cases [elim]: "FLet\<^sub>k e # s :\<^sub>k t' \<rightarrow> t"
inductive_cases [elim]: "FReturn\<^sub>k # s :\<^sub>k t' \<rightarrow> t"

lemma tc_stack\<^sub>k_append [simp]: "s @ s' :\<^sub>k t' \<rightarrow> t \<Longrightarrow> \<not> return_headed\<^sub>k s' \<Longrightarrow> 
  \<exists>t''. (s :\<^sub>k t' \<rightarrow> t'') \<and> (s' :\<^sub>k t'' \<rightarrow> t)"
proof (induction s arbitrary: t')
  case (Cons f s)
  thus ?case 
  proof (induction f)
    case (FApp2\<^sub>k e)
    then obtain t\<^sub>2 where X: "([] \<turnstile>\<^sub>d e : Arrow t' t\<^sub>2) \<and> let_floated\<^sub>d e \<and> let_free\<^sub>d e \<and> value\<^sub>d e \<and> 
      (s @ s' :\<^sub>k t\<^sub>2 \<rightarrow> t)" by auto
    with FApp2\<^sub>k obtain t'' where "(s :\<^sub>k t\<^sub>2 \<rightarrow> t'') \<and> (s' :\<^sub>k t'' \<rightarrow> t)" by blast
    moreover with X have "FApp2\<^sub>k e # s :\<^sub>k t' \<rightarrow> t''" by fastforce
    ultimately show ?case by blast
  next
    case (FLet\<^sub>k e)
    then obtain tt where X: "([t'] \<turnstile>\<^sub>d e : tt) \<and> let_floated\<^sub>d e" and "s @ s' :\<^sub>k tt \<rightarrow> t"
      and S: "return_headed\<^sub>k (s @ s')" by fastforce
    with FLet\<^sub>k obtain t'' where T: "(s :\<^sub>k tt \<rightarrow> t'') \<and> s' :\<^sub>k t'' \<rightarrow> t" by fastforce
    with S FLet\<^sub>k show ?case
    proof (cases s)
      case (Cons f s)
      with S X T Cons have "FLet\<^sub>k e # FReturn\<^sub>k # s :\<^sub>k t' \<rightarrow> t''" by auto
      with S T Cons show ?thesis by auto
    qed simp_all
  qed force+
qed force+

text \<open>The stack evaluation state has three components: the expression being evaluated; the stack 
itself; and a flag for whether or not the expression is known to be a value. We also define the 
concept of a final state, analogous to values for expressions.\<close> 
 
datatype state\<^sub>k = S\<^sub>k bool "frame\<^sub>k list" expr\<^sub>d

primrec final\<^sub>k :: "state\<^sub>k \<Rightarrow> bool" where
  "final\<^sub>k (S\<^sub>k b s e) = (b \<and> s = [])"

text \<open>Typechecking a full state is equally simple. Again, we do not need a typing context because we 
only ever evaluate closed expressions.\<close>

inductive typing_state\<^sub>k :: "state\<^sub>k \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>k" 50) where
  tc_state\<^sub>k [simp]: "s :\<^sub>k t' \<rightarrow> t \<Longrightarrow> [] \<turnstile>\<^sub>d e : t' \<Longrightarrow> let_floated\<^sub>d e \<Longrightarrow> (b \<longrightarrow> value\<^sub>d e) \<Longrightarrow> 
    let_free\<^sub>d e \<or> return_headed\<^sub>k s \<Longrightarrow> S\<^sub>k b s e :\<^sub>k t"

inductive_cases [elim]: "S\<^sub>k b s e :\<^sub>k t"

text \<open>We now define the evaluation relation. As promised, each evaluation step operates directly on 
the state, without any searching or testing of values. We have more steps now, as a result: 
\<open>ev\<^sub>k_app1\<close>, \<open>ev\<^sub>k_app2\<close>, and \<open>ev\<^sub>k_ret\<close> to perform the redex search, and \<open>ev\<^sub>k_const\<close> and \<open>ev\<^sub>k_lam\<close> to 
replace the value tests.\<close>

inductive eval\<^sub>k :: "state\<^sub>k \<Rightarrow> state\<^sub>k \<Rightarrow> bool" (infix "\<leadsto>\<^sub>k" 50) where
  ev\<^sub>k_const [simp]: "S\<^sub>k False s (Const\<^sub>d n) \<leadsto>\<^sub>k S\<^sub>k True s (Const\<^sub>d n)"
| ev\<^sub>k_lam [simp]: "S\<^sub>k False s (Lam\<^sub>d t e) \<leadsto>\<^sub>k S\<^sub>k True s (Lam\<^sub>d t e)"
| ev\<^sub>k_app1 [simp]: "S\<^sub>k False s (App\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>k S\<^sub>k False (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1"
| ev\<^sub>k_app2 [simp]: "S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1 \<leadsto>\<^sub>k S\<^sub>k False (FApp2\<^sub>k e\<^sub>1 # s) e\<^sub>2"
| ev\<^sub>k_app3 [simp]: "S\<^sub>k True (FApp2\<^sub>k (Lam\<^sub>d t e\<^sub>1) # s) e\<^sub>2 \<leadsto>\<^sub>k S\<^sub>k False (FReturn\<^sub>k # s) (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)"
| ev\<^sub>k_let1 [simp]: "S\<^sub>k False (FReturn\<^sub>k # s) (Let\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>k S\<^sub>k False (FLet\<^sub>k e\<^sub>2 # FReturn\<^sub>k # s) e\<^sub>1"
| ev\<^sub>k_let2 [simp]: "S\<^sub>k True (FLet\<^sub>k e\<^sub>2 # FReturn\<^sub>k # s) e\<^sub>1 \<leadsto>\<^sub>k S\<^sub>k False (FReturn\<^sub>k # s) (subst\<^sub>d 0 e\<^sub>1 e\<^sub>2)"
| ev\<^sub>k_ret [simp]: "S\<^sub>k True (FReturn\<^sub>k # s) e \<leadsto>\<^sub>k S\<^sub>k True s e"

lemma eval\<^sub>k_under [simp]: "S\<^sub>k b s e \<leadsto>\<^sub>k S\<^sub>k b' s' e' \<Longrightarrow> S\<^sub>k b (s @ ss) e \<leadsto>\<^sub>k S\<^sub>k b' (s' @ ss) e'"
  by (induction "S\<^sub>k b s e" "S\<^sub>k b' s' e'" rule: eval\<^sub>k.induct) auto

lemma eval\<^sub>k_under_iter [simp]: "iter (\<leadsto>\<^sub>k) (S\<^sub>k b s e) (S\<^sub>k b' s' e') \<Longrightarrow> 
  iter (\<leadsto>\<^sub>k) (S\<^sub>k b (s @ ss) e) (S\<^sub>k b' (s' @ ss) e')"
proof (induction "S\<^sub>k b s e" "S\<^sub>k b' s' e'" arbitrary: b s e rule: iter.induct)
  case (iter_step \<Sigma>')
  then show ?case 
  proof (induction \<Sigma>' rule: state\<^sub>k.induct)
    case (S\<^sub>k b'' s'' e'')
    hence "S\<^sub>k b (s @ ss) e \<leadsto>\<^sub>k S\<^sub>k b'' (s'' @ ss) e''" by simp
    moreover from S\<^sub>k have "iter (\<leadsto>\<^sub>k) (S\<^sub>k b'' (s'' @ ss) e'') (S\<^sub>k b' (s' @ ss) e')" by simp
    ultimately show ?case by simp
  qed
qed simp_all

lemma eval\<^sub>k_value [simp]: "value\<^sub>d e \<Longrightarrow> iter (\<leadsto>\<^sub>k) (S\<^sub>k b s e) (S\<^sub>k True s e)"
proof (induction e)
  case (Const\<^sub>d n)
  thus ?case 
  proof (induction b)
    case False
    have "S\<^sub>k False s (Const\<^sub>d n) \<leadsto>\<^sub>k S\<^sub>k True s (Const\<^sub>d n)" by simp
    thus ?case by (metis iter_step iter_refl)
  qed simp_all
next
  case (Lam\<^sub>d t e)
  thus ?case
  proof (induction b)
    case False
    have "S\<^sub>k False s (Lam\<^sub>d t e) \<leadsto>\<^sub>k S\<^sub>k True s (Lam\<^sub>d t e)" by simp
    thus ?case by (metis iter_step iter_refl)
  qed simp_all
qed simp_all

text \<open>From here, proving the safety theorems is straightforward:\<close>

lemma eval\<^sub>k_from_nonvalue [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> let_floated\<^sub>d e \<Longrightarrow> 
  let_free\<^sub>d e \<or> return_headed\<^sub>k s \<Longrightarrow> \<exists>\<Sigma>'. S\<^sub>k False s e \<leadsto>\<^sub>k \<Sigma>'"
proof (induction "[] :: ty list" e t rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_const n)
  have "S\<^sub>k False s (Const\<^sub>d n) \<leadsto>\<^sub>k S\<^sub>k True s (Const\<^sub>d n)" by simp
  thus ?case by fastforce
next
  case (tc\<^sub>d_lam t\<^sub>1 e t\<^sub>2)
  have "S\<^sub>k False s (Lam\<^sub>d t\<^sub>1 e) \<leadsto>\<^sub>k S\<^sub>k True s (Lam\<^sub>d t\<^sub>1 e)" by simp
  thus ?case by fastforce
next
  case (tc\<^sub>d_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  have "S\<^sub>k False s (App\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>k S\<^sub>k False (FApp1\<^sub>k e\<^sub>2 # s) e\<^sub>1" by simp
  thus ?case by fastforce
next
  case (tc\<^sub>d_let e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
  then obtain s' where "s = FReturn\<^sub>k # s'" by auto
  moreover have "S\<^sub>k False (FReturn\<^sub>k # s') (Let\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>k S\<^sub>k False (FLet\<^sub>k e\<^sub>2 # FReturn\<^sub>k # s') e\<^sub>1" 
    by simp
  ultimately show ?case by fastforce
qed simp_all

lemma eval\<^sub>k_from_value [simp]: "s :\<^sub>k t' \<rightarrow> t \<Longrightarrow> [] \<turnstile>\<^sub>d e : t' \<Longrightarrow> value\<^sub>d e \<Longrightarrow> 
  s = [] \<or> (\<exists>\<Sigma>'. S\<^sub>k True s e \<leadsto>\<^sub>k \<Sigma>')"
proof (induction s t' t rule: typing_stack\<^sub>k.induct)
  case (tcs\<^sub>k_cons_app1 e\<^sub>2 t\<^sub>1 s t\<^sub>2 t)
  hence "S\<^sub>k True (FApp1\<^sub>k e\<^sub>2 # s) e \<leadsto>\<^sub>k S\<^sub>k False (FApp2\<^sub>k e # s) e\<^sub>2" by simp
  thus ?case by fastforce
next
  case (tcs\<^sub>k_cons_app2 e\<^sub>1 t\<^sub>1 t\<^sub>2 s t)
  then obtain e\<^sub>1' where "e\<^sub>1 = Lam\<^sub>d t\<^sub>1 e\<^sub>1' \<and> insert_at 0 t\<^sub>1 [] \<turnstile>\<^sub>d e\<^sub>1' : t\<^sub>2" by blast
  moreover with tcs\<^sub>k_cons_app2 have "S\<^sub>k True (FApp2\<^sub>k (Lam\<^sub>d t\<^sub>1 e\<^sub>1') # s) e \<leadsto>\<^sub>k 
    S\<^sub>k False (FReturn\<^sub>k # s) (subst\<^sub>d 0 e e\<^sub>1')" by simp
  ultimately show ?case by fastforce
next
  case (tcs\<^sub>k_cons_let t\<^sub>1 e\<^sub>2 t\<^sub>2 s t)
  hence "S\<^sub>k True (FLet\<^sub>k e\<^sub>2 # s) e \<leadsto>\<^sub>k S\<^sub>k False s (subst\<^sub>d 0 e e\<^sub>2)" 
    by (cases s rule: return_headed\<^sub>k.cases) simp_all
  then show ?case by fastforce
next 
  case (tcs\<^sub>k_cons_ret s t')
  hence "S\<^sub>k True (FReturn\<^sub>k # s) e \<leadsto>\<^sub>k S\<^sub>k True s e" by simp
  thus ?case by fastforce
qed simp_all

theorem progress\<^sub>k: "\<Sigma> :\<^sub>k t \<Longrightarrow> final\<^sub>k \<Sigma> \<or> (\<exists>\<Sigma>'. \<Sigma> \<leadsto>\<^sub>k \<Sigma>')"
proof (induction \<Sigma> t rule: typing_state\<^sub>k.induct)
  case (tc_state\<^sub>k s t' t e b)
  thus ?case by (cases b) simp_all
qed 

lemma final_no_eval\<^sub>k [simp]: "\<Sigma> \<leadsto>\<^sub>k \<Sigma>' \<Longrightarrow> final\<^sub>k \<Sigma> \<Longrightarrow> False"
  by (induction \<Sigma> \<Sigma>' rule: eval\<^sub>k.induct) simp_all

theorem preservation\<^sub>k [simp]: "\<Sigma> \<leadsto>\<^sub>k \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>k t \<Longrightarrow> \<Sigma>' :\<^sub>k t"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>k.induct)
  case (ev\<^sub>k_app1 s e\<^sub>1 e\<^sub>2)
  then obtain t\<^sub>1 t\<^sub>2 where "s :\<^sub>k t\<^sub>2 \<rightarrow> t" and "([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<and> let_free\<^sub>d e\<^sub>2 \<and> let_floated\<^sub>d e\<^sub>2" 
    and X: "([] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2) \<and> let_free\<^sub>d e\<^sub>1 \<and> let_floated\<^sub>d e\<^sub>1 \<and> (is_var\<^sub>d e\<^sub>1 \<or> value\<^sub>d e\<^sub>1)" 
      by fastforce
  hence "FApp1\<^sub>k e\<^sub>2 # s :\<^sub>k Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t" by simp
  with X show ?case by simp
next
  case (ev\<^sub>k_app2 e\<^sub>2 s e\<^sub>1)
  then obtain t\<^sub>1 t\<^sub>2 where X: "([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<and> let_free\<^sub>d e\<^sub>2 \<and> let_floated\<^sub>d e\<^sub>2" and "s :\<^sub>k t\<^sub>2 \<rightarrow> t" 
   and "([] \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2) \<and> let_free\<^sub>d e\<^sub>1 \<and> let_floated\<^sub>d e\<^sub>1 \<and> value\<^sub>d e\<^sub>1" by fastforce
  with ev\<^sub>k_app2 have "FApp2\<^sub>k e\<^sub>1 # s :\<^sub>k t\<^sub>1 \<rightarrow> t" by fastforce
  with X show ?case by simp
next
  case (ev\<^sub>k_app3 t\<^sub>1 e\<^sub>1 s e\<^sub>2)
  then obtain t\<^sub>2 where "([t\<^sub>1] \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2) \<and> let_floated\<^sub>d e\<^sub>1" and X: "s :\<^sub>k t\<^sub>2 \<rightarrow> t" 
    and "([] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<and> let_floated\<^sub>d e\<^sub>2 \<and> value\<^sub>d e\<^sub>2" by fastforce
  hence "([] \<turnstile>\<^sub>d subst\<^sub>d 0 e\<^sub>2 e\<^sub>1 : t\<^sub>2) \<and> let_floated\<^sub>d (subst\<^sub>d 0 e\<^sub>2 e\<^sub>1)" by fastforce
  moreover from X have "FReturn\<^sub>k # s :\<^sub>k t\<^sub>2 \<rightarrow> t" by simp
  ultimately show ?case by simp
next
  case (ev\<^sub>k_let1 s e\<^sub>1 e\<^sub>2)
  then obtain t\<^sub>1 t\<^sub>2 where "s :\<^sub>k t\<^sub>2 \<rightarrow> t" and X: "([] \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>1) \<and> let_free\<^sub>d e\<^sub>1 \<and> let_floated\<^sub>d e\<^sub>1" 
    and "([t\<^sub>1] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>2) \<and> let_floated\<^sub>d e\<^sub>2" by fastforce
  hence "FLet\<^sub>k e\<^sub>2 # FReturn\<^sub>k # s :\<^sub>k t\<^sub>1 \<rightarrow> t" by fastforce
  with X show ?case by simp
next
  case (ev\<^sub>k_let2 e\<^sub>2 s e\<^sub>1)
  then obtain t\<^sub>1 t\<^sub>2 where "([t\<^sub>1] \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>2) \<and> let_floated\<^sub>d e\<^sub>2" and X: "s :\<^sub>k t\<^sub>2 \<rightarrow> t" 
    and "([] \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>1) \<and> let_floated\<^sub>d e\<^sub>1" and "value\<^sub>d e\<^sub>1" by fastforce
  hence "([] \<turnstile>\<^sub>d subst\<^sub>d 0 e\<^sub>1 e\<^sub>2 : t\<^sub>2) \<and> let_floated\<^sub>d (subst\<^sub>d 0 e\<^sub>1 e\<^sub>2)" by fastforce
  moreover from X have "FReturn\<^sub>k # s :\<^sub>k t\<^sub>2 \<rightarrow> t" by simp
  ultimately show ?case by simp
qed fastforce+

lemma preservation_iter\<^sub>k [simp]: "iter (\<leadsto>\<^sub>k) \<Sigma> \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>k t \<Longrightarrow> \<Sigma>' :\<^sub>k t"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

theorem determinism\<^sub>k: "\<Sigma> \<leadsto>\<^sub>k \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>k \<Sigma>'' \<Longrightarrow> \<Sigma> :\<^sub>k t \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>k.induct)
  case (ev\<^sub>k_const s k)
  thus ?case by (induction rule: eval\<^sub>k.cases) simp_all
next
  case (ev\<^sub>k_lam s t e)
  thus ?case by (induction rule: eval\<^sub>k.cases) simp_all
next
  case (ev\<^sub>k_app1 s e\<^sub>1 e\<^sub>2)
  thus ?case by (induction rule: eval\<^sub>k.cases) simp_all
next
  case (ev\<^sub>k_app2 e\<^sub>2 s e\<^sub>1)
  thus ?case by (induction rule: eval\<^sub>k.cases) simp_all
next
  case (ev\<^sub>k_app3 t e\<^sub>1 s e\<^sub>2)
  thus ?case by (induction rule: eval\<^sub>k.cases) simp_all
next
  case (ev\<^sub>k_let1 s e\<^sub>1 e\<^sub>2)
  thus ?case by (induction rule: eval\<^sub>k.cases) simp_all
next
  case (ev\<^sub>k_let2 e\<^sub>2 s e\<^sub>1)
  thus ?case by (induction rule: eval\<^sub>k.cases) simp_all
next 
  case (ev\<^sub>k_ret s e)
  thus ?case by (induction rule: eval\<^sub>k.cases) simp_all
qed

end