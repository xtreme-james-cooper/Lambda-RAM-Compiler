theory GroupedEnvironments
  imports "../02Typed/Type" "../00Utils/Environment" "../00Utils/Iteration"
begin

section \<open>Grouped Environments\<close>

text \<open>We have now eliminated every expression-walking function in the evaluation process, but there 
is still one recursive function, sort of: \<open>lookup\<close>. \<open>lookup\<close> is implemented as a recursive search 
through a list, but fairly clearly it is equivalent to an indexed lookup which could be done in 
constant time. So we don't have to worry about it.\<close>

text \<open>Or do we? Looking ahead a bit, we will eventually need to represent our environments somehow 
in a concrete machine: probably as contiguous arrays of pointers. This makes our \<open>lookup\<close> operation 
as cheap as it should be, just an array access followed by a pointer lookup. But there is a problem: 
we don't only have one environment. In a simpler block-structured language without function 
closures, we could use a single stack as our environment, pushing and popping new bindings each time 
they go in and out of scope, and accessing variables cheaply. But we have functions that close over 
their declaration environment, and moreover these closures can be duplicated and applied multiple 
times - and thus have their environments extended in different ways. Blindly copying the 
environments every time we need a new closure keeps our lookups cheap, but means that every function 
application takes time linear in the size of the function closure's environment. Alternately, we 
could keep representing environments by a linked list, which can have new bindings cons'd onto the 
end cheaply and repeatedly, but means we _have to_ use the recursive list-search implementation of 
\<open>lookup\<close>, making every variable reference take time proportional to its Debruijn index. Since any 
program is going to have many applications and variables, neither approach seems attractive.\<close>

text \<open>Fortunately, there is a clever third option that combines many of the strengths of both 
representations. Because we have let-floated our bindings, every let-binder is in a list of bindings 
directly below a lambda-binder (or at the outside of the program at the top level). This means that 
every time the lambda-abstraction is instantiated, all the let-bindings must also be instantiated; 
so, without losing any sharing, we can allocate the environment for all the binders together in one 
contiguous block. This permits the cheap pointer-copying environment-sharing of the second method 
above, while reducing the cost of variable lookups to proportional to the number of enclosing 
_functions_ rather than enclosing binders: since we know statically what frame and offset within 
that frame a variable is defined at, we can follow pointers back to that frame and then look up the
index directly. This key optimization makes the whole system adequately efficient, and is 
more-or-less how real language implementations allocate environment memory*.\<close>

text \<open>*We are slightly less efficient than real implementations because in practice most lambda 
abstractions occur in blocks too, and a sequence of lambdas is usually instantiated all at once. 
This allows for the further optimization of allocating environment frames for an entire block of 
lambdas at once, producing a slight loss of sharing on curried applications in exchange for further 
reducing lookup times to proportional to the number of enclosing lambda-_sequences_. Since most 
functions are defined at the top level, this means that lookups are close to constant-time. See our 
further work section.\<close>

text \<open>We are not at the stage of actually representing environments in memory yet, of course. But by 
the time we are, we will have compiled away much of the structure of the expressions, making it much 
more difficult to calculate the frames-and-offsets from Debruijn indexes. So now, just before we 
start compiling our expressions into linear code, we change our abstract environments from single 
lists to lists-of-lists, representing the eventual linked-list-of-frames they will be, and replace 
our variable indexes with frame-offset pairs. (We also precalculate and store the size of the frame 
associated with a lambda-expression and store it for use later as well.)\<close>

datatype expr\<^sub>g = 
  Var\<^sub>g nat nat
  | Const\<^sub>g nat
  | Lam\<^sub>g ty expr\<^sub>g nat
  | App\<^sub>g expr\<^sub>g expr\<^sub>g
  | Let\<^sub>g expr\<^sub>g expr\<^sub>g

text \<open>Typing remains almost unchanged, but we need to adjust the typing context a little: rather 
than just a list, it too is a list of lists to match the new way we look up variables.\<close>

fun let_count :: "expr\<^sub>g \<Rightarrow> nat" where
  "let_count (Let\<^sub>g e\<^sub>1 e\<^sub>2) = Suc (let_count e\<^sub>2)"
| "let_count e = 0"

inductive typing\<^sub>g :: "ty list list \<Rightarrow> expr\<^sub>g \<Rightarrow> ty \<Rightarrow> bool" (infix "\<turnstile>\<^sub>g _ :" 50) where
  tc\<^sub>g_var [simp]: "lookup \<Gamma> x = Some ts \<Longrightarrow> lookup ts y = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>g Var\<^sub>g x y : t"
| tc\<^sub>g_const [simp]: "\<Gamma> \<turnstile>\<^sub>g Const\<^sub>g n : Num"
| tc\<^sub>g_lam [simp]: "insert_at 0 [t\<^sub>1] \<Gamma> \<turnstile>\<^sub>g e : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>g Lam\<^sub>g t\<^sub>1 e (let_count e) : Arrow t\<^sub>1 t\<^sub>2"
| tc\<^sub>g_app [simp]: "\<Gamma> \<turnstile>\<^sub>g e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>g e\<^sub>2 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>g App\<^sub>g e\<^sub>1 e\<^sub>2 : t\<^sub>2"
| tc\<^sub>g_let [simp]: "\<Gamma> \<turnstile>\<^sub>g e\<^sub>1 : t\<^sub>1 \<Longrightarrow> cons_fst t\<^sub>1 \<Gamma> \<turnstile>\<^sub>g e\<^sub>2 : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>g Let\<^sub>g e\<^sub>1 e\<^sub>2 : t\<^sub>2"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>g Var\<^sub>g x y : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>g Const\<^sub>g n : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>g Lam\<^sub>g t' e n : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>g App\<^sub>g e\<^sub>1 e\<^sub>2 : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>g Let\<^sub>g e\<^sub>1 e\<^sub>2 : t"

text \<open>We also redefine our let-floating predicates for our new datatype.\<close>

primrec non_redex\<^sub>g :: "expr\<^sub>g \<Rightarrow> bool" where
  "non_redex\<^sub>g (Var\<^sub>g x y) = True"
| "non_redex\<^sub>g (Const\<^sub>g n) = True"
| "non_redex\<^sub>g (Lam\<^sub>g t e n) = True"
| "non_redex\<^sub>g (App\<^sub>g e\<^sub>1 e\<^sub>2) = False"
| "non_redex\<^sub>g (Let\<^sub>g e\<^sub>1 e\<^sub>2) = False"

primrec let_free\<^sub>g :: "expr\<^sub>g \<Rightarrow> bool" where
  "let_free\<^sub>g (Var\<^sub>g x y) = True"
| "let_free\<^sub>g (Const\<^sub>g n) = True"
| "let_free\<^sub>g (Lam\<^sub>g t e n) = True"
| "let_free\<^sub>g (App\<^sub>g e\<^sub>1 e\<^sub>2) = (let_free\<^sub>g e\<^sub>1 \<and> let_free\<^sub>g e\<^sub>2)"
| "let_free\<^sub>g (Let\<^sub>g e\<^sub>1 e\<^sub>2) = False"

primrec let_floated\<^sub>g :: "expr\<^sub>g \<Rightarrow> bool" where
  "let_floated\<^sub>g (Var\<^sub>g x y) = True"
| "let_floated\<^sub>g (Const\<^sub>g n) = True"
| "let_floated\<^sub>g (Lam\<^sub>g t e n) = let_floated\<^sub>g e"
| "let_floated\<^sub>g (App\<^sub>g e\<^sub>1 e\<^sub>2) = 
    (let_free\<^sub>g e\<^sub>1 \<and> let_free\<^sub>g e\<^sub>2 \<and> non_redex\<^sub>g e\<^sub>1 \<and> let_floated\<^sub>g e\<^sub>1 \<and> let_floated\<^sub>g e\<^sub>2)"
| "let_floated\<^sub>g (Let\<^sub>g e\<^sub>1 e\<^sub>2) = (let_free\<^sub>g e\<^sub>1 \<and> let_floated\<^sub>g e\<^sub>1 \<and> let_floated\<^sub>g e\<^sub>2)"

text \<open>Closures, frames, and states need to be changed similarly.\<close>

datatype closure\<^sub>g = 
  Num\<^sub>g nat
  | Fun\<^sub>g ty "closure\<^sub>g list list" expr\<^sub>g nat

inductive typing_closure\<^sub>g :: "closure\<^sub>g \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>g\<^sub>c\<^sub>l" 50)
      and typing_environment\<^sub>g :: "closure\<^sub>g list list \<Rightarrow> ty list list \<Rightarrow> bool" (infix ":\<^sub>g\<^sub>c\<^sub>l\<^sub>s" 50) where
  tc\<^sub>g_const [simp]: "Num\<^sub>g n :\<^sub>g\<^sub>c\<^sub>l Num"
| tc\<^sub>g_lam [simp]: "\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> insert_at 0 [t\<^sub>1] \<Gamma> \<turnstile>\<^sub>g e : t\<^sub>2 \<Longrightarrow> let_floated\<^sub>g e \<Longrightarrow> 
    Fun\<^sub>g t\<^sub>1 \<Delta> e (let_count e) :\<^sub>g\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2"
| tc\<^sub>g_nil [simp]: "[] :\<^sub>g\<^sub>c\<^sub>l\<^sub>s []"
| tc\<^sub>g_cons_nil [simp]: "\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> [] # \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s [] # \<Gamma>"
| tc\<^sub>g_cons_cons [simp]: "c :\<^sub>g\<^sub>c\<^sub>l t \<Longrightarrow>  cs # \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s ts # \<Gamma> \<Longrightarrow> (c # cs) # \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s (t # ts) # \<Gamma>"

inductive_cases [elim]:"Num\<^sub>g n :\<^sub>g\<^sub>c\<^sub>l t"
inductive_cases [elim]: "Fun\<^sub>g t\<^sub>1 \<Delta> e n :\<^sub>g\<^sub>c\<^sub>l t"
inductive_cases [elim]: "[] :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>"
inductive_cases [elim]: "[] # \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>"
inductive_cases [elim]: "(c # cs) # \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>"

lemma  "c :\<^sub>g\<^sub>c\<^sub>l t \<Longrightarrow> True"
  and lookup_in_env\<^sub>g [simp]: "\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> lookup \<Gamma> x = Some ts \<Longrightarrow> lookup ts y = Some t \<Longrightarrow>
    \<exists>cs c. lookup \<Delta> x = Some cs \<and> lookup cs y = Some c \<and> c :\<^sub>g\<^sub>c\<^sub>l t"
proof (induction c t and \<Delta> \<Gamma> arbitrary: and x ts y rule: typing_closure\<^sub>g_typing_environment\<^sub>g.inducts)
  case (tc\<^sub>g_cons_nil \<Delta> \<Gamma>)
  thus ?case by (cases x) simp_all
next
  case (tc\<^sub>g_cons_cons c t' cs \<Delta> ts' \<Gamma>)
  thus ?case 
  proof (cases x)
    case 0
    with tc\<^sub>g_cons_cons show ?thesis 
    proof (cases y)
      case (Suc y)
      have "lookup (ts' # \<Gamma>) 0 = Some ts'" by simp
      with tc\<^sub>g_cons_cons 0 Suc show ?thesis by fastforce
    qed auto
  next
    case (Suc x)
    with tc\<^sub>g_cons_cons Suc have "lookup (ts' # \<Gamma>) (Suc x) = Some ts" by simp
    with tc\<^sub>g_cons_cons Suc show ?thesis by (cases y) fastforce+
  qed
qed simp_all

lemma "c :\<^sub>g\<^sub>c\<^sub>l t \<Longrightarrow> True"
  and tc_closure_cons_fst [simp]: "\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> c :\<^sub>g\<^sub>c\<^sub>l t \<Longrightarrow> cons_fst c \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s cons_fst t \<Gamma>"
  by (induction c t and \<Delta> \<Gamma> rule: typing_closure\<^sub>g_typing_environment\<^sub>g.inducts) simp_all

lemma env_length_same [simp]: "cs # \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s ts # \<Gamma> \<Longrightarrow> length cs = length ts"
  by (induction cs arbitrary: ts) auto

lemma canonical_num\<^sub>g [dest]: "c :\<^sub>g\<^sub>c\<^sub>l Num \<Longrightarrow> \<exists>n. c = Num\<^sub>g n"
  by (induction c Num rule: typing_closure\<^sub>g_typing_environment\<^sub>g.inducts(1)) simp_all

lemma canonical_arrow\<^sub>g [dest]: "c :\<^sub>g\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> 
    \<exists>\<Delta> \<Gamma> e. c = Fun\<^sub>g t\<^sub>1 \<Delta> e (let_count e) \<and> (\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> (insert_at 0 [t\<^sub>1] \<Gamma> \<turnstile>\<^sub>g e : t\<^sub>2)"
  by (induction c "Arrow t\<^sub>1 t\<^sub>2" rule: typing_closure\<^sub>g_typing_environment\<^sub>g.inducts(1)) auto

datatype frame\<^sub>g = 
  FApp1\<^sub>g "closure\<^sub>g list list" expr\<^sub>g
  | FApp2\<^sub>g closure\<^sub>g
  | FLet\<^sub>g "closure\<^sub>g list list" expr\<^sub>g
  | FReturn\<^sub>g "closure\<^sub>g list list"

fun latest_environment\<^sub>g :: "frame\<^sub>g list \<rightharpoonup> closure\<^sub>g list list" where
  "latest_environment\<^sub>g [] = None"
| "latest_environment\<^sub>g (FApp1\<^sub>g \<Delta> e # s) = latest_environment\<^sub>g s"
| "latest_environment\<^sub>g (FApp2\<^sub>g c # s) = latest_environment\<^sub>g s"
| "latest_environment\<^sub>g (FLet\<^sub>g \<Delta> e # s) = latest_environment\<^sub>g s"
| "latest_environment\<^sub>g (FReturn\<^sub>g \<Delta> # s) = Some \<Delta>"

fun return_headed\<^sub>g :: "frame\<^sub>g list \<Rightarrow> bool" where
  "return_headed\<^sub>g (FReturn\<^sub>g \<Delta> # s) = True"
| "return_headed\<^sub>g s = False"

lemma return_headed_elim [dest]: "return_headed\<^sub>g s \<Longrightarrow> \<exists>s' \<Delta>. s = FReturn\<^sub>g \<Delta> # s'"
  by (cases s rule: return_headed\<^sub>g.cases) simp_all

inductive typing_stack\<^sub>g :: "frame\<^sub>g list \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>g _ \<rightarrow>" 50) where
  tcg_snil [simp]: "[] :\<^sub>g t \<rightarrow> t"
| tcg_scons_app1 [simp]: "\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>g e : t\<^sub>1 \<Longrightarrow> let_floated\<^sub>g e \<Longrightarrow> let_free\<^sub>g e \<Longrightarrow> 
    s :\<^sub>g t\<^sub>2 \<rightarrow> t \<Longrightarrow> latest_environment\<^sub>g s = Some \<Delta> \<Longrightarrow> FApp1\<^sub>g \<Delta> e # s :\<^sub>g Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t"
| tcg_scons_app2 [simp]: "c :\<^sub>g\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> s :\<^sub>g t\<^sub>2 \<rightarrow> t \<Longrightarrow> latest_environment\<^sub>g s \<noteq> None \<Longrightarrow> 
    FApp2\<^sub>g c # s :\<^sub>g t\<^sub>1 \<rightarrow> t"
| tcg_scons_let [simp]: "latest_environment\<^sub>g s = Some \<Delta> \<Longrightarrow> \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow>
    cons_fst t\<^sub>1 \<Gamma> \<turnstile>\<^sub>g e : t\<^sub>2 \<Longrightarrow> let_floated\<^sub>g e \<Longrightarrow> s :\<^sub>g t\<^sub>2 \<rightarrow> t \<Longrightarrow> return_headed\<^sub>g s \<Longrightarrow> 
    FLet\<^sub>g \<Delta> e # s :\<^sub>g t\<^sub>1 \<rightarrow> t"
| tcg_scons_ret [simp]: "\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> s :\<^sub>g t' \<rightarrow> t \<Longrightarrow> FReturn\<^sub>g \<Delta> # s :\<^sub>g t' \<rightarrow> t"

inductive_cases [elim]: "[] :\<^sub>g t' \<rightarrow> t"
inductive_cases [elim]: "FApp1\<^sub>g \<Delta> e # s :\<^sub>g t' \<rightarrow> t"
inductive_cases [elim]: "FApp2\<^sub>g c # s :\<^sub>g t' \<rightarrow> t"
inductive_cases [elim]: "FLet\<^sub>g \<Delta> e # s :\<^sub>g t' \<rightarrow> t"
inductive_cases [elim]: "FPop\<^sub>g c # s :\<^sub>g t' \<rightarrow> t"
inductive_cases [elim]: "FReturn\<^sub>g \<Delta> # s :\<^sub>g t' \<rightarrow> t"

datatype state\<^sub>g = 
  SE\<^sub>g "frame\<^sub>g list" "closure\<^sub>g list list" expr\<^sub>g
  | SC\<^sub>g "frame\<^sub>g list" closure\<^sub>g

primrec final\<^sub>g :: "state\<^sub>g \<Rightarrow> bool" where
  "final\<^sub>g (SE\<^sub>g s \<Delta> e) = False"
| "final\<^sub>g (SC\<^sub>g s c) = (s = [])"

inductive typecheck_state\<^sub>g :: "state\<^sub>g \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>g" 50) where
  tcg_state_ev [simp]: "s :\<^sub>g t' \<rightarrow> t \<Longrightarrow> \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> latest_environment\<^sub>g s = Some \<Delta> \<Longrightarrow> 
    \<Gamma> \<turnstile>\<^sub>g e : t' \<Longrightarrow> let_floated\<^sub>g e \<Longrightarrow> let_free\<^sub>g e \<or> return_headed\<^sub>g s \<Longrightarrow> SE\<^sub>g s \<Delta> e :\<^sub>g t"
| tcg_state_ret [simp]: "s :\<^sub>g t' \<rightarrow> t \<Longrightarrow> c :\<^sub>g\<^sub>c\<^sub>l t' \<Longrightarrow> SC\<^sub>g s c :\<^sub>g t"

inductive_cases [elim]: "SE\<^sub>g s \<Delta> e :\<^sub>g t"
inductive_cases [elim]: "SC\<^sub>g s c :\<^sub>g t"

text \<open>Evaluation, similarly, requires a slightly more complicated lookup than before, but is 
otherwise unchanged.\<close>

inductive eval\<^sub>g :: "state\<^sub>g \<Rightarrow> state\<^sub>g \<Rightarrow> bool" (infix "\<leadsto>\<^sub>g" 50) where
  ev\<^sub>g_var [simp]: "lookup \<Delta> x = Some cs \<Longrightarrow> lookup cs y = Some c \<Longrightarrow> SE\<^sub>g s \<Delta> (Var\<^sub>g x y) \<leadsto>\<^sub>g SC\<^sub>g s c"
| ev\<^sub>g_con [simp]: "SE\<^sub>g s \<Delta> (Const\<^sub>g n) \<leadsto>\<^sub>g SC\<^sub>g s (Num\<^sub>g n)"
| ev\<^sub>g_lam [simp]: "SE\<^sub>g s \<Delta> (Lam\<^sub>g t e n) \<leadsto>\<^sub>g SC\<^sub>g s (Fun\<^sub>g t \<Delta> e n)"
| ev\<^sub>g_app [simp]: "SE\<^sub>g s \<Delta> (App\<^sub>g e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>g SE\<^sub>g (FApp1\<^sub>g \<Delta> e\<^sub>2 # s) \<Delta> e\<^sub>1"
| ev\<^sub>g_let [simp]: "SE\<^sub>g (FReturn\<^sub>g \<Delta> # s) \<Delta> (Let\<^sub>g e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>g SE\<^sub>g (FLet\<^sub>g \<Delta> e\<^sub>2 # FReturn\<^sub>g \<Delta> # s) \<Delta> e\<^sub>1"
| ret\<^sub>g_app1 [simp]: "SC\<^sub>g (FApp1\<^sub>g \<Delta> e\<^sub>2 # s) c\<^sub>1 \<leadsto>\<^sub>g SE\<^sub>g (FApp2\<^sub>g c\<^sub>1 # s) \<Delta> e\<^sub>2"
| ret\<^sub>g_app2 [simp]: "SC\<^sub>g (FApp2\<^sub>g (Fun\<^sub>g t \<Delta> e\<^sub>1 n) # s) c\<^sub>2 \<leadsto>\<^sub>g 
    SE\<^sub>g (FReturn\<^sub>g ([c\<^sub>2] # \<Delta>) # s) ([c\<^sub>2] # \<Delta>) e\<^sub>1"
| ret\<^sub>g_let [simp]: "SC\<^sub>g (FLet\<^sub>g \<Delta> e\<^sub>2 # FReturn\<^sub>g \<Delta> # s) c\<^sub>1 \<leadsto>\<^sub>g 
    SE\<^sub>g (FReturn\<^sub>g (cons_fst c\<^sub>1 \<Delta>) # s) (cons_fst c\<^sub>1 \<Delta>) e\<^sub>2"
| ret\<^sub>g_ret [simp]: "SC\<^sub>g (FReturn\<^sub>g \<Delta> # s) c \<leadsto>\<^sub>g SC\<^sub>g s c"

text \<open>And the safety theorems:\<close>

lemma eval\<^sub>g_from_nonvalue [simp]: "\<Gamma> \<turnstile>\<^sub>g e : t \<Longrightarrow> \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> let_free\<^sub>g e \<or> return_headed\<^sub>g s \<Longrightarrow>
  latest_environment\<^sub>g s = Some \<Delta> \<Longrightarrow> \<exists>\<Sigma>'. SE\<^sub>g s \<Delta> e \<leadsto>\<^sub>g \<Sigma>'"
proof (induction \<Gamma> e t rule: typing\<^sub>g.induct)
  case (tc\<^sub>g_var \<Gamma> x ts y t)
  then obtain cs c where "lookup \<Delta> x = Some cs \<and> lookup cs y = Some c \<and> c :\<^sub>g\<^sub>c\<^sub>l t"
    using lookup_in_env\<^sub>g by blast
  hence "SE\<^sub>g s \<Delta> (Var\<^sub>g x y) \<leadsto>\<^sub>g SC\<^sub>g s c" by simp
  thus ?case by fastforce 
next
  case (tc\<^sub>g_const \<Gamma> n)
  have "SE\<^sub>g s \<Delta> (Const\<^sub>g n) \<leadsto>\<^sub>g SC\<^sub>g s (Num\<^sub>g n)" by simp
  thus ?case by fastforce 
next
  case (tc\<^sub>g_lam t\<^sub>1 \<Gamma> e t\<^sub>2)
  have "SE\<^sub>g s \<Delta> (Lam\<^sub>g t\<^sub>1 e (let_count e)) \<leadsto>\<^sub>g SC\<^sub>g s (Fun\<^sub>g t\<^sub>1 \<Delta> e (let_count e))" by simp
  thus ?case by fastforce 
next
  case (tc\<^sub>g_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  have "SE\<^sub>g s \<Delta> (App\<^sub>g e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>g SE\<^sub>g (FApp1\<^sub>g \<Delta> e\<^sub>2 # s) \<Delta> e\<^sub>1" by simp
  thus ?case by fastforce
next
  case (tc\<^sub>g_let \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
  then obtain s' where "s = FReturn\<^sub>g \<Delta> # s'" by auto
  hence "SE\<^sub>g s \<Delta> (Let\<^sub>g e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>g SE\<^sub>g (FLet\<^sub>g \<Delta> e\<^sub>2 # s) \<Delta> e\<^sub>1" by simp
  thus ?case by fastforce
qed

lemma eval\<^sub>g_from_value [simp]: "s :\<^sub>g t' \<rightarrow> t \<Longrightarrow> c :\<^sub>g\<^sub>c\<^sub>l t' \<Longrightarrow> s = [] \<or> (\<exists>\<Sigma>'. SC\<^sub>g s c \<leadsto>\<^sub>g \<Sigma>')"
proof (induction s t' t rule: typing_stack\<^sub>g.induct)
  case (tcg_scons_app1 \<Delta> \<Gamma> e\<^sub>2 t\<^sub>1 s t\<^sub>2 t)
  moreover hence "SC\<^sub>g (FApp1\<^sub>g \<Delta> e\<^sub>2 # s) c \<leadsto>\<^sub>g SE\<^sub>g (FApp2\<^sub>g c # s) \<Delta> e\<^sub>2" by simp
  ultimately show ?case by fastforce
next
  case (tcg_scons_app2 c\<^sub>1 t\<^sub>1 t\<^sub>2 s t)
  then obtain \<Delta> ts e where "c\<^sub>1 = Fun\<^sub>g t\<^sub>1 \<Delta> e (let_count e) \<and> (\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s ts) \<and> 
    (insert_at 0 [t\<^sub>1] ts \<turnstile>\<^sub>g e : t\<^sub>2)" by blast
  moreover hence "SC\<^sub>g (FApp2\<^sub>g (Fun\<^sub>g t\<^sub>1 \<Delta> e (let_count e)) # s) c \<leadsto>\<^sub>g 
    SE\<^sub>g (FReturn\<^sub>g ([c] # \<Delta>) # s) ([c] # \<Delta>) e" by simp
  ultimately show ?case by fastforce
next
  case (tcg_scons_let s \<Delta> \<Gamma> t\<^sub>1 e t\<^sub>2 t)
  then obtain s' where "s = FReturn\<^sub>g \<Delta> # s'" by auto
  hence "SC\<^sub>g (FLet\<^sub>g \<Delta> e # s) c \<leadsto>\<^sub>g SE\<^sub>g (FReturn\<^sub>g (cons_fst c \<Delta>) # s') (cons_fst c \<Delta>) e" by simp
  thus ?case by fastforce
next
  case (tcg_scons_ret \<Delta> \<Gamma> s t' t)
  have "SC\<^sub>g (FReturn\<^sub>g \<Delta> # s) c \<leadsto>\<^sub>g SC\<^sub>g s c" by simp
  thus ?case by fastforce
qed simp_all

theorem progress\<^sub>g: "\<Sigma> :\<^sub>g t \<Longrightarrow> final\<^sub>g \<Sigma> \<or> (\<exists>\<Sigma>'. \<Sigma> \<leadsto>\<^sub>g \<Sigma>')"
  by (induction \<Sigma> t rule: typecheck_state\<^sub>g.induct) simp_all

lemma final_no_eval\<^sub>g [simp]: "\<Sigma> \<leadsto>\<^sub>g \<Sigma>' \<Longrightarrow> final\<^sub>g \<Sigma> \<Longrightarrow> False"
  by (induction \<Sigma> \<Sigma>' rule: eval\<^sub>g.induct) simp_all

theorem preservation\<^sub>g [simp]: "\<Sigma> \<leadsto>\<^sub>g \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>g t \<Longrightarrow> \<Sigma>' :\<^sub>g t"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>g.induct)
  case (ev\<^sub>g_var \<Delta> x cs y c s)
  then obtain ts t' \<Gamma> where X: "s :\<^sub>g t' \<rightarrow> t" and "(\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> lookup \<Gamma> x = Some ts \<and> 
    lookup ts y = Some t'" by blast
  then obtain cs c' where "lookup \<Delta> x = Some cs \<and> lookup cs y = Some c' \<and> c' :\<^sub>g\<^sub>c\<^sub>l t'"
    using lookup_in_env\<^sub>g by blast
  with ev\<^sub>g_var X show ?case by simp
next
  case (ev\<^sub>g_app s \<Delta> e\<^sub>1 e\<^sub>2)
  then obtain t\<^sub>1 t\<^sub>2 \<Gamma> where "(s :\<^sub>g t\<^sub>2 \<rightarrow> t) \<and> (\<Gamma> \<turnstile>\<^sub>g e\<^sub>2 : t\<^sub>1) \<and> let_floated\<^sub>g e\<^sub>2 \<and> let_free\<^sub>g e\<^sub>2" 
   and X: "(\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> latest_environment\<^sub>g s = Some \<Delta> \<and> (\<Gamma> \<turnstile>\<^sub>g e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2) \<and> 
    let_floated\<^sub>g e\<^sub>1 \<and> let_free\<^sub>g e\<^sub>1" by fastforce
  hence "FApp1\<^sub>g \<Delta> e\<^sub>2 # s :\<^sub>g Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t" by fastforce
  with X show ?case by fastforce
next
  case (ev\<^sub>g_let \<Delta> s e\<^sub>1 e\<^sub>2)
  then obtain \<Gamma> t\<^sub>2 t\<^sub>1 where "(s :\<^sub>g t\<^sub>2 \<rightarrow> t) \<and> (cons_fst t\<^sub>1 \<Gamma> \<turnstile>\<^sub>g e\<^sub>2 : t\<^sub>2) \<and> let_floated\<^sub>g e\<^sub>2" 
    and X: "(\<Gamma> \<turnstile>\<^sub>g e\<^sub>1 : t\<^sub>1) \<and> (\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> let_floated\<^sub>g e\<^sub>1 \<and> let_free\<^sub>g e\<^sub>1" by fastforce
  hence "FLet\<^sub>g \<Delta> e\<^sub>2 # FReturn\<^sub>g \<Delta> # s :\<^sub>g t\<^sub>1 \<rightarrow> t" by fastforce
  with X show ?case by fastforce
next
  case (ret\<^sub>g_app1 \<Delta> e\<^sub>2 s c\<^sub>1)
  then obtain \<Gamma> t\<^sub>1 t\<^sub>2 where X: "(\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> latest_environment\<^sub>g s = Some \<Delta> \<and> (\<Gamma> \<turnstile>\<^sub>g e\<^sub>2 : t\<^sub>1) \<and>
    let_floated\<^sub>g e\<^sub>2 \<and> let_free\<^sub>g e\<^sub>2" 
   and "(s :\<^sub>g t\<^sub>2 \<rightarrow> t) \<and> (c\<^sub>1 :\<^sub>g\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2)" by blast
  hence "FApp2\<^sub>g c\<^sub>1 # s :\<^sub>g t\<^sub>1 \<rightarrow> t" by fastforce
  with X show ?case by fastforce
next
  case (ret\<^sub>g_app2 t\<^sub>1 \<Delta> e\<^sub>1 n s c\<^sub>2)
  then obtain \<Gamma> t\<^sub>2 where X: "s :\<^sub>g t\<^sub>2 \<rightarrow> t" and Y: "(insert_at 0 [t\<^sub>1] \<Gamma> \<turnstile>\<^sub>g e\<^sub>1 : t\<^sub>2) \<and> let_floated\<^sub>g e\<^sub>1" 
   and "(\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> (c\<^sub>2 :\<^sub>g\<^sub>c\<^sub>l t\<^sub>1)" by blast
  hence Z: "[c\<^sub>2] # \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s insert_at 0 [t\<^sub>1] \<Gamma>" by (cases \<Gamma>) simp_all
  with X have "FReturn\<^sub>g ([c\<^sub>2] # \<Delta>) # s :\<^sub>g t\<^sub>2 \<rightarrow> t" by simp
  with Y Z show ?case by fastforce
next
  case (ret\<^sub>g_let \<Delta> e\<^sub>2 s c\<^sub>1)
  then obtain \<Gamma> t\<^sub>1 t\<^sub>2 where X: "(cons_fst t\<^sub>1 \<Gamma> \<turnstile>\<^sub>g e\<^sub>2 : t\<^sub>2) \<and> let_floated\<^sub>g e\<^sub>2" and "\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>" 
    and Z: "c\<^sub>1 :\<^sub>g\<^sub>c\<^sub>l t\<^sub>1" and Y: "s :\<^sub>g t\<^sub>2 \<rightarrow> t" by fastforce
  hence W: "cons_fst c\<^sub>1 \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s cons_fst t\<^sub>1 \<Gamma>" by simp
  with Y have "FReturn\<^sub>g (cons_fst c\<^sub>1 \<Delta>) # s :\<^sub>g t\<^sub>2 \<rightarrow> t" by simp
  with X W show ?case by fastforce
qed fastforce+

lemma preservation\<^sub>g_iter [simp]: "iter (\<leadsto>\<^sub>g) \<Sigma> \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>g t \<Longrightarrow> \<Sigma>' :\<^sub>g t"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

theorem determinism\<^sub>g: "\<Sigma> \<leadsto>\<^sub>g \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>g \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>g.induct)
  case (ev\<^sub>g_var \<Delta> x c s)
  from ev\<^sub>g_var(3, 1, 2) show ?case by (induction rule: eval\<^sub>g.cases) simp_all 
next
  case (ev\<^sub>g_con s \<Delta> k)
  thus ?case by (induction rule: eval\<^sub>g.cases) simp_all 
next
  case (ev\<^sub>g_lam s \<Delta> t e)
  thus ?case by (induction rule: eval\<^sub>g.cases) simp_all 
next
  case (ev\<^sub>g_app s \<Delta> e\<^sub>1 e\<^sub>2)
  thus ?case by (induction rule: eval\<^sub>g.cases) simp_all 
next
  case (ev\<^sub>g_let s \<Delta> e\<^sub>1 e\<^sub>2)
  thus ?case by (induction rule: eval\<^sub>g.cases) simp_all 
next
  case (ret\<^sub>g_app1 \<Delta> e\<^sub>2 s c\<^sub>1)
  thus ?case by (induction rule: eval\<^sub>g.cases) simp_all 
next
  case (ret\<^sub>g_app2 t \<Delta> e\<^sub>1 s c\<^sub>2)
  thus ?case by (induction rule: eval\<^sub>g.cases) simp_all 
next
  case (ret\<^sub>g_let \<Delta> e\<^sub>2 s c\<^sub>1)
  thus ?case by (induction rule: eval\<^sub>g.cases) simp_all 
next
  case (ret\<^sub>g_ret \<Delta> s c)
  thus ?case by (induction rule: eval\<^sub>g.cases) simp_all 
qed

end