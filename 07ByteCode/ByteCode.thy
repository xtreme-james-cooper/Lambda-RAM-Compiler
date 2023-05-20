theory ByteCode
  imports "../00Utils/Environment" "../00Utils/Iteration"
begin

section \<open>Byte Code\<close>

text \<open>the last phase compiled to a tree-structured sort of code; but of course real code is not 
tree-structured but linear. We therefore define a new sort of code, similar to tree-code but with 
code-pointers everywhere we previously had recursive codeblocks. (We call it "bytecode" for a 
memorable name and because it could easily be made into such, but we will never actually define a 
representation ourselves.)\<close>

datatype code\<^sub>b = 
  Lookup\<^sub>b nat
  | PushCon\<^sub>b nat
  | PushLam\<^sub>b nat
  | Apply\<^sub>b
  | Return\<^sub>b
  | Jump\<^sub>b

datatype closure\<^sub>b = 
  Const\<^sub>b nat
  | Lam\<^sub>b "closure\<^sub>b list" nat

datatype state\<^sub>b = 
  S\<^sub>b "closure\<^sub>b list" "(closure\<^sub>b list \<times> nat) list"

text \<open>The evaluation relation is rather similar to our previous one, except with code-pointers into
our main bytecode block instead of storing the code in the stack and closures directly. The relation
is now a three-place one, however: the bytecode is separate from the states. We could put it into 
the state directly, but that would be misleading: the state is for data that changes at runtime, 
like the various stacks, but the bytecode never changes. In addition, the next few stages will all 
be finding ways to interpret the same bytecode at a lower and lower level, so keeping the bytecode 
separate will make it clearer that it is not changed from stage to stage.\<close>

text \<open>One unusual feature of the evaluation relation as we have written it is that the bytecode is 
evaluated from right-to-left; that is, the operation at address x+1 will be executed before the 
operation at x. This is mostly to simplify some later operations, in particular \<open>unflatten_code\<close>, 
which relies on the code pointer always decreasing to prove termination.\<close>

inductive eval\<^sub>b :: "code\<^sub>b list \<Rightarrow> state\<^sub>b \<Rightarrow> state\<^sub>b \<Rightarrow> bool" 
    (infix "\<tturnstile> _ \<leadsto>\<^sub>b" 50) where
  ev\<^sub>b_lookup [simp]: "lookup \<C> p = Some (Lookup\<^sub>b x) \<Longrightarrow> lookup \<Delta> x = Some v \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>b \<V> ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>b S\<^sub>b (v # \<V>) ((\<Delta>, p) # s)" 
| ev\<^sub>b_pushcon [simp]: "lookup \<C> p = Some (PushCon\<^sub>b n) \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>b \<V> ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>b S\<^sub>b (Const\<^sub>b n # \<V>) ((\<Delta>, p) # s)"
| ev\<^sub>b_pushlam [simp]: "lookup \<C> p = Some (PushLam\<^sub>b p') \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>b \<V> ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>b S\<^sub>b (Lam\<^sub>b \<Delta> p' # \<V>) ((\<Delta>, p) # s)"
| ev\<^sub>b_apply [simp]: "lookup \<C> p = Some Apply\<^sub>b \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>b (v # Lam\<^sub>b \<Delta>' p' # \<V>) ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>b S\<^sub>b \<V> ((v # \<Delta>', p') # (\<Delta>, p) # s)"
| ev\<^sub>b_return [simp]: "lookup \<C> p = Some Return\<^sub>b \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>b \<V> ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>b S\<^sub>b \<V> s"
| ev\<^sub>b_jump [simp]: "lookup \<C> p = Some Jump\<^sub>b \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>b (v # Lam\<^sub>b \<Delta>' p' # \<V>) ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>b S\<^sub>b \<V> ((v # \<Delta>', p') # s)"

theorem determinismb: "\<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>b \<Sigma>' \<Longrightarrow> \<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>b \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<C> \<Sigma> \<Sigma>' rule: eval\<^sub>b.induct)
  case ev\<^sub>b_lookup
  from ev\<^sub>b_lookup(3, 1, 2) show ?case by (induction rule: eval\<^sub>b.cases) simp_all 
next
  case ev\<^sub>b_pushcon
  from ev\<^sub>b_pushcon(2, 1) show ?case by (induction rule: eval\<^sub>b.cases) simp_all 
next
  case ev\<^sub>b_pushlam
  from ev\<^sub>b_pushlam(2, 1) show ?case by (induction rule: eval\<^sub>b.cases) simp_all 
next
  case ev\<^sub>b_apply
  from ev\<^sub>b_apply(2, 1) show ?case by (induction rule: eval\<^sub>b.cases) simp_all 
next
  case ev\<^sub>b_return
  from ev\<^sub>b_return(2, 1) show ?case by (induction rule: eval\<^sub>b.cases) simp_all 
next
  case ev\<^sub>b_jump
  from ev\<^sub>b_jump(2, 1) show ?case by (induction rule: eval\<^sub>b.cases) simp_all 
qed

text \<open>We also define a properly-terminated predicate, indicating that the code is still structured 
in blocks.\<close>

primrec properly_terminated\<^sub>b :: "code\<^sub>b list \<Rightarrow> bool" where
  "properly_terminated\<^sub>b [] = False"
| "properly_terminated\<^sub>b (op # \<C>) = (op = Return\<^sub>b \<or> op = Jump\<^sub>b)"


end