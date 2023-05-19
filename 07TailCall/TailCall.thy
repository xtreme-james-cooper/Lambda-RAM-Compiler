theory TailCall
  imports "../00Utils/Environment"
begin

section \<open>Tail Call Optimization\<close>

text \<open>Our previous stage never really returned; it just popped stack frames every time it ran out of 
code to execute. We now add explicit return operations at the end of each code block. This will help 
make it clear where blocks end, once we no longer have the luxury of tree-structured code in the 
next stage - but for now it will also help us enact our one optimization.\<close>

text \<open>We therefore add a second kind of return, \<open>Jump\<^sub>l\<close>, which combines the effect of an \<open>Apply\<^sub>l\<close> and 
a \<open>Return\<^sub>l\<close>.\<close>

datatype return\<^sub>l =
    Return\<^sub>l
    | Jump\<^sub>l

text \<open>The code, closures, stacks, and states remain the same, except that every code block is now 
paired with its return.\<close>

datatype code\<^sub>l = 
  Lookup\<^sub>l nat
  | PushCon\<^sub>l nat
  | PushLam\<^sub>l "code\<^sub>l list" return\<^sub>l
  | Apply\<^sub>l

datatype closure\<^sub>l = 
  Const\<^sub>l nat
  | Lam\<^sub>l "closure\<^sub>l list" "code\<^sub>l list" return\<^sub>l

type_synonym frame\<^sub>l = "closure\<^sub>l list \<times> code\<^sub>l list \<times> return\<^sub>l"

datatype state\<^sub>l = S\<^sub>l "closure\<^sub>l list" "frame\<^sub>l list"

text \<open>The evaluation relation closely matches the previous stage's, with the obvious exception of 
\<open>ev\<^sub>l_jump\<close>. This takes the top two values and applies them together, but unlike \<open>ev\<^sub>l_apply\<close>, it 
replaces the topmost stack frame entirely rather than pushing on top - exactly the tail-call 
optimization we want to express.\<close>

inductive eval\<^sub>l :: "state\<^sub>l \<Rightarrow> state\<^sub>l \<Rightarrow> bool" (infix "\<leadsto>\<^sub>l" 50) where
  ev\<^sub>l_lookup [simp]: "lookup \<Delta> x = Some v \<Longrightarrow> 
    S\<^sub>l \<V> ((\<Delta>, Lookup\<^sub>l x # \<C>, r) # s) \<leadsto>\<^sub>l S\<^sub>l (v # \<V>) ((\<Delta>, \<C>, r) # s)"
| ev\<^sub>l_pushcon [simp]: "S\<^sub>l \<V> ((\<Delta>, PushCon\<^sub>l n # \<C>, r) # s) \<leadsto>\<^sub>l S\<^sub>l (Const\<^sub>l n # \<V>) ((\<Delta>, \<C>, r) # s)"
| ev\<^sub>l_pushlam [simp]: "S\<^sub>l \<V> ((\<Delta>, PushLam\<^sub>l \<C>' r' # \<C>, r) # s) \<leadsto>\<^sub>l 
    S\<^sub>l (Lam\<^sub>l \<Delta> \<C>' r' # \<V>) ((\<Delta>, \<C>, r) # s)"
| ev\<^sub>l_apply [simp]: "S\<^sub>l (v # Lam\<^sub>l \<Delta>' \<C>' r' # \<V>) ((\<Delta>, Apply\<^sub>l # \<C>, r) # s) \<leadsto>\<^sub>l 
    S\<^sub>l \<V> ((v # \<Delta>', \<C>', r') # (\<Delta>, \<C>, r) # s)"
| ev\<^sub>l_return [simp]: "S\<^sub>l \<V> ((\<Delta>, [], Return\<^sub>l) # s) \<leadsto>\<^sub>l S\<^sub>l \<V> s"
| ev\<^sub>l_jump [simp]: "S\<^sub>l (v # Lam\<^sub>l \<Delta>' \<C>' r' # \<V>) ((\<Delta>, [], Jump\<^sub>l) # s) \<leadsto>\<^sub>l S\<^sub>l \<V> ((v # \<Delta>', \<C>', r') # s)"

theorem determinism\<^sub>l: "\<Sigma> \<leadsto>\<^sub>l \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>l \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>l.induct)
  case ev\<^sub>l_lookup
  from ev\<^sub>l_lookup(2, 1) show ?case by (induction rule: eval\<^sub>l.cases) simp_all 
next
  case ev\<^sub>l_pushcon
  thus ?case by (induction rule: eval\<^sub>l.cases) simp_all 
next
  case ev\<^sub>l_pushlam
  thus ?case by (induction rule: eval\<^sub>l.cases) simp_all 
next
  case ev\<^sub>l_apply
  thus ?case by (induction rule: eval\<^sub>l.cases) simp_all 
next
  case ev\<^sub>l_return
  thus ?case by (induction rule: eval\<^sub>l.cases) simp_all 
next
  case ev\<^sub>l_jump
  thus ?case by (induction rule: eval\<^sub>l.cases) simp_all 
qed

end