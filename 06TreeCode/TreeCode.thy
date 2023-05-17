theory TreeCode
  imports "../00Utils/Environment"
begin

section \<open>Tree Code\<close>

text \<open>Our evaluation relation still works by examining an expression not too different from our 
original source. But we use eager evaluation-order, meaning that for any given expression, it is 
predictable from the shape of the expression exactly what operations must be performed and in what
order. So our next stage is to eliminate all run-time analysis of the expression by performing it 
once at compile time.\<close>

text \<open>Our tree-code contains one constructor per expression constructor. The key difference is that 
application is now an operation without arguments; we have restructured the expression tree into a 
postfix form. Lambda-abstractions keep their sub-codeblock, however (hence the name "tree" code). We 
Will eliminate this too, but not for a few stages yet.\<close>

datatype code\<^sub>e = 
  Lookup\<^sub>e nat
  | PushCon\<^sub>e nat
  | PushLam\<^sub>e "code\<^sub>e list"
  | Apply\<^sub>e

text \<open>Our closure-values remain the same, with just a change from a function body to a function 
codeblock in closures-proper.\<close>

datatype closure\<^sub>e = 
  Const\<^sub>e nat
  | Lam\<^sub>e "closure\<^sub>e list" "code\<^sub>e list"

text \<open>Our state, however, is greatly changed. In particular, the call stack has to be divided in 
two: part of it becomes the call stack proper, with frames containing the call environment and a 
block of yet-to-be-executed code, and the remainder becomes a value stack that \<open>PushX\<close> operations 
push onto and \<open>Apply\<^sub>e\<close> operations pop off.\<close>

type_synonym frame\<^sub>e = "closure\<^sub>e list \<times> code\<^sub>e list"

datatype state\<^sub>e = S\<^sub>e "closure\<^sub>e list" "frame\<^sub>e list"

text \<open>Evaluation is now directed entirely by the code in the topmost callstack frame. \<open>Lookup\<^sub>e\<close> and 
\<open>PushX\<close> push onto the value stack (the former looking up its closure-value from the topmost 
callstack frame's environment); \<open>Apply\<^sub>e\<close> pops two values (the second of which should be a \<open>Lam\<^sub>e\<close>, to 
be applied), and pushes a new callstack frame using the closure's environment and codeblock. When 
the code in a callstack frame is exhausted, we return by popping that frame off the callstack.\<close>

inductive eval\<^sub>e :: "state\<^sub>e \<Rightarrow> state\<^sub>e \<Rightarrow> bool" (infix "\<leadsto>\<^sub>e" 50) where
  ev\<^sub>e_lookup [simp]: "lookup \<Delta> x = Some v \<Longrightarrow> 
    S\<^sub>e \<V> ((\<Delta>, Lookup\<^sub>e x # \<C>) # s) \<leadsto>\<^sub>e S\<^sub>e (v # \<V>) ((\<Delta>, \<C>) # s)"
| ev\<^sub>e_pushcon [simp]: "S\<^sub>e \<V> ((\<Delta>, PushCon\<^sub>e n # \<C>) # s) \<leadsto>\<^sub>e S\<^sub>e (Const\<^sub>e n # \<V>) ((\<Delta>, \<C>) # s)"
| ev\<^sub>e_pushlam [simp]: "S\<^sub>e \<V> ((\<Delta>, PushLam\<^sub>e \<C>' # \<C>) # s) \<leadsto>\<^sub>e S\<^sub>e (Lam\<^sub>e \<Delta> \<C>' # \<V>) ((\<Delta>, \<C>) # s)"
| ev\<^sub>e_apply [simp]: "S\<^sub>e (v # Lam\<^sub>e \<Delta>' \<C>' # \<V>) ((\<Delta>, Apply\<^sub>e # \<C>) # s) \<leadsto>\<^sub>e 
    S\<^sub>e \<V> ((v # \<Delta>', \<C>') # (\<Delta>, \<C>) # s)"
| ev\<^sub>e_return [simp]: "S\<^sub>e \<V> ((\<Delta>, []) # s) \<leadsto>\<^sub>e S\<^sub>e \<V> s"

text \<open>Without typing, our list of safety properties has become quite short: just determinism. We 
could still type our codeblocks, and thence our state; we would need to give each tree-code 
operation a type relating the type of its input value stack to the type of its output value stack, 
and then check that they all compose together properly, but we could do it. However, the typing gets 
more and more labourious as we go on, and here - the moment we finally leave expressions behind for 
good - seems as reasonable a place as any to abandon it. This, of course, leaves us much more 
dependent on the conversion correctness theorems, since they are now our only source of what it
means for a state to be "correct".\<close>

theorem determinism\<^sub>e: "\<Sigma> \<leadsto>\<^sub>e \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>e \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>e.induct)
  case (ev\<^sub>e_lookup env x v \<V> \<C> sfs)
  from ev\<^sub>e_lookup(2, 1) show ?case by (induction rule: eval\<^sub>e.cases) simp_all 
next
  case (ev\<^sub>e_pushcon \<V> env k \<C> sfs)
  thus ?case by  (induction rule: eval\<^sub>e.cases) simp_all 
next
  case (ev\<^sub>e_pushlam \<V> env \<C>' \<C> sfs)
  thus ?case by  (induction rule: eval\<^sub>e.cases) simp_all  
next
  case (ev\<^sub>e_apply v env' \<C>' \<V> env \<C> sfs)
  thus ?case by (induction rule: eval\<^sub>e.cases) simp_all 
next
  case (ev\<^sub>e_return \<V> env sfs)
  thus ?case by (induction rule: eval\<^sub>e.cases) simp_all 
qed

end