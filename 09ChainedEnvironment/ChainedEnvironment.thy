theory ChainedEnvironment
  imports "../07ByteCode/ByteCode" "../08HeapMemory/Heap"
begin

section \<open>Chained environments\<close>

text \<open>We still have one place where information is duplicated: our environments themselves. They now 
consist of lists of pointers rather than lists of values, but we still copy the list every time we 
create a new function closure. At first we might think we could resolve this with the same trick we 
used last stage, of storing the environments in the heap (or a new heap) and simply sharing pointers
to them, but in fact this will not work. The problem is that unlike values, which once created never 
change, an environment stored in a closure can be extended - and since a function closure can be 
applied multiple times, extended in different ways.\<close>

text \<open>We actually face a choice here. We could commit to copying the list every time, as a 
contiguous block of data; this would be expensive every time a closure was copied, and mean that 
closures occupy a varying (though compile-time-predictable) amount of space; but, as a consolation,
variable lookup becomes very cheap (just a single pointer indirection). Alternately, we could store 
environments as linked lists, making copying cheap and environments easy to extend in multiple 
directions at once, but at the cost of making variable lookups expensive (a sequence of pointer 
indirections proportional to their Debruijn index). Neither approach seems attractive; in each case,
an operation that "should be" constant-time (or at least "cheap") is instead linear in the number of
bound variables.\<close>

text \<open>Fortunately, there is a clever third option that combines many of the strengths of both 
representations. Because we have let-floated our bindings, every let-binder is in a list of bindings 
directly below a lambda-binder (or at the outside of the expression at the top level). This means 
that every time the lambda-abstraction is instantiated, all the let-bindings must also be 
instantiated; so, without losing any sharing, we can allocate the environment for all the binders 
together in one contiguous block. This permits the cheap pointer-copying environment-sharing of the 
second method above, while reducing the cost of variable lookups to proportional to the number of 
enclosing _functions_ rather than enclosing binders. This key optimization makes the whole system 
adequately efficient, and is more-or-less how real language implementations allocate environment 
memory*.\<close>

text \<open>*We are slightly less efficient than real implementations because in practice most lambda 
abstractions occur in blocks too, and a sequence of lambdas is usually instantiated all at once. 
This allows for the further optimization of allocating environment frames for an entire block of 
lambdas at once, producing a slight loss of sharing on curried applications in exchange for further 
reducing lookup times to proportional to the number of enclosing lambda-_sequences_. Since most 
functions are defined at the top level, this means that lookups are close to constant-time. See our 
further work section.\<close>

text \<open>We will take this last approach. We create a second heap, containing a linked-list (or 
rather, pointer-linked tree) of pointers into our first, value, heap. All environments are now 
pointers into this second heap, which means that our heaps point to each other; we keep them 
separate for simplicity, although much later on we will collapse them into a single memory.\<close>

text \<open>To begin with, we define a lookup function for our linked-tree environments. Since we index 
from the leaves towards the root, we don't actually have to deal with the tree structure; each 
lookup looks like a list. We also distinguish a null pointer, 0, and therefore have to use \<open>Suc p\<close> 
as a pointer to \<open>p\<close>.\<close>

fun chain_lookup :: "('a \<times> ptr) heap \<Rightarrow> ptr \<Rightarrow> nat \<rightharpoonup> 'a" where
  "chain_lookup h 0 x = None"
| "chain_lookup h (Suc p) 0 = Some (fst (hlookup h p))"
| "chain_lookup h (Suc p) (Suc x) = chain_lookup h (snd (hlookup h p)) x"

text \<open>From here, the new evaluation state and relation is simple. The only tricky point is to 
remember that instead of just pushing values on top of the environment in \<open>ev\<^sub>v_apply\<close> or \<open>ev\<^sub>v_jump\<close>,
we must allocate a new cons cell (i.e., a pair) in the environment heap.\<close>

datatype closure\<^sub>v = 
  Const\<^sub>v nat
  | Lam\<^sub>v ptr nat

datatype state\<^sub>v = 
  S\<^sub>v "closure\<^sub>v heap" "(ptr \<times> ptr) heap" "ptr list" "(ptr \<times> nat) list"

inductive eval\<^sub>v :: "code\<^sub>b list \<Rightarrow> state\<^sub>v \<Rightarrow> state\<^sub>v \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>v" 50) where
  ev\<^sub>v_lookup [simp]: "lookup \<C> p\<^sub>\<C> = Some (Lookup\<^sub>b x y z) \<Longrightarrow> chain_lookup \<Delta> p\<^sub>\<Delta> x = Some v \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>v h \<Delta> \<V> ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v S\<^sub>v h \<Delta> (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s)"
| ev\<^sub>v_pushcon [simp]: "lookup \<C> p\<^sub>\<C> = Some (PushCon\<^sub>b n) \<Longrightarrow> halloc h (Const\<^sub>v n) = (h', v) \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>v h \<Delta> \<V> ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v S\<^sub>v h' \<Delta> (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s)"
| ev\<^sub>v_pushlam [simp]: "lookup \<C> p\<^sub>\<C> = Some (PushLam\<^sub>b p\<^sub>\<C>' n) \<Longrightarrow> halloc h (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>') = (h', v) \<Longrightarrow> 
      \<C> \<tturnstile> S\<^sub>v h \<Delta> \<V> ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v S\<^sub>v h' \<Delta> (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s)"
| ev\<^sub>v_apply [simp]: "lookup \<C> p\<^sub>\<C> = Some Apply\<^sub>b \<Longrightarrow> hlookup h v\<^sub>2 = Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>' \<Longrightarrow>
    halloc \<Delta> (v\<^sub>1, p\<^sub>\<Delta>') = (\<Delta>', p\<^sub>\<Delta>'') \<Longrightarrow> 
      \<C> \<tturnstile> S\<^sub>v h \<Delta> (v\<^sub>1 # v\<^sub>2 # \<V>) ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v S\<^sub>v h \<Delta>' \<V> ((Suc p\<^sub>\<Delta>'', p\<^sub>\<C>') # (p\<^sub>\<Delta>, p\<^sub>\<C>) # s)"
| ev\<^sub>v_pushenv [simp]: "lookup \<C> p\<^sub>\<C> = Some PushEnv\<^sub>b \<Longrightarrow> halloc \<Delta> (v, p\<^sub>\<Delta>) = (\<Delta>', p\<^sub>\<Delta>') \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>v h \<Delta> (v # \<V>) ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v S\<^sub>v h \<Delta>' \<V> ((Suc p\<^sub>\<Delta>', p\<^sub>\<C>) # s)"
| ev\<^sub>v_return [simp]: "lookup \<C> p\<^sub>\<C> = Some Return\<^sub>b \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>v h \<Delta> \<V> ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v S\<^sub>v h \<Delta> \<V> s"
| ev\<^sub>v_jump [simp]: "lookup \<C> p\<^sub>\<C> = Some Jump\<^sub>b \<Longrightarrow> hlookup h v\<^sub>2 = Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>' \<Longrightarrow>
    halloc \<Delta> (v\<^sub>1, p\<^sub>\<Delta>') = (\<Delta>', p\<^sub>\<Delta>'') \<Longrightarrow>
      \<C> \<tturnstile> S\<^sub>v h \<Delta> (v\<^sub>1 # v\<^sub>2 # \<V>) ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v S\<^sub>v h \<Delta>' \<V> ((Suc p\<^sub>\<Delta>'', p\<^sub>\<C>') # s)"

theorem determinismh: "\<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>v \<Sigma>' \<Longrightarrow> \<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>v \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>v.induct)
  case ev\<^sub>v_lookup
  from ev\<^sub>v_lookup(3, 1, 2) show ?case by (induction rule: eval\<^sub>v.cases) simp_all 
next
  case ev\<^sub>v_pushcon
  from ev\<^sub>v_pushcon(3, 1, 2) show ?case by (induction rule: eval\<^sub>v.cases) simp_all 
next
  case ev\<^sub>v_pushlam
  from ev\<^sub>v_pushlam(3, 1, 2) show ?case by (induction rule: eval\<^sub>v.cases) simp_all 
next
  case ev\<^sub>v_apply
  from ev\<^sub>v_apply(4, 1, 2, 3) show ?case by (induction rule: eval\<^sub>v.cases) simp_all 
next
  case ev\<^sub>v_pushenv
  from ev\<^sub>v_pushenv(3, 1, 2) show ?case by (induction rule: eval\<^sub>v.cases) simp_all 
next
  case ev\<^sub>v_return
  from ev\<^sub>v_return(2, 1) show ?case by (induction rule: eval\<^sub>v.cases) simp_all 
next
  case ev\<^sub>v_jump
  from ev\<^sub>v_jump(4, 1, 2, 3) show ?case by (induction rule: eval\<^sub>v.cases) simp_all 
qed

end