theory ChainedEnvironment
  imports "../08ByteCode/ByteCode" "../09HeapMemory/Heap"
begin

section \<open>Chained environments\<close>

text \<open>We still have one place where information is duplicated: our environments themselves. They now 
consist of lists of pointers rather than lists of values, but we still copy the list every time we 
create a new function closure.\<close>

text \<open>Fortunately, we have been preparing for this moment for a while now, and everything is in 
position to lay out our environments in memory. We create a second heap, containing a linked-list 
(or rather, pointer-linked tree) of lists of pointers into our first, value, heap. All environments 
are now pointers into this second heap, which means that our heaps point to each other; we keep them 
separate for simplicity, although much later on we will collapse them into a single memory.\<close>

text \<open>To begin with, we define a lookup function for our linked-tree environments. Since we index 
from the leaves towards the root, we don't actually have to deal with the tree structure; each 
lookup looks like a list. We also distinguish a null pointer, 0, and therefore have to use \<open>Suc p\<close> 
as a pointer to \<open>p\<close>.\<close>

fun chain_lookup :: "('a list \<times> ptr) heap \<Rightarrow> ptr \<Rightarrow> nat \<Rightarrow> nat \<rightharpoonup> 'a" where
  "chain_lookup h 0 x y = None"
| "chain_lookup h (Suc p) 0 y = lookup (fst (hlookup h p)) y"
| "chain_lookup h (Suc p) (Suc x) y = chain_lookup h (snd (hlookup h p)) x y"

text \<open>From here, the new evaluation state and relation is simple. The only tricky point is to 
remember that instead of just pushing values on top of the environment in \<open>ev\<^sub>v_apply\<close> or \<open>ev\<^sub>v_jump\<close>,
we must allocate a new cons cell (i.e., a pair) in the environment heap; and in \<open>ev\<^sub>v_pushenv\<close>, we
update the old heap with a new, enlarged memory list.\<close>

datatype closure\<^sub>v = 
  Const\<^sub>v nat
  | Lam\<^sub>v ptr nat

datatype state\<^sub>v = 
  S\<^sub>v "closure\<^sub>v heap" "(ptr list \<times> ptr) heap" "ptr list" "(ptr \<times> nat) list"

inductive eval\<^sub>v :: "code\<^sub>b list \<Rightarrow> state\<^sub>v \<Rightarrow> state\<^sub>v \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>v" 50) where
  ev\<^sub>v_lookup [simp]: "lookup \<C> p\<^sub>\<C> = Some (Lookup\<^sub>b x y) \<Longrightarrow> chain_lookup \<Delta> p\<^sub>\<Delta> x y = Some v \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>v h \<Delta> \<V> ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v S\<^sub>v h \<Delta> (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s)"
| ev\<^sub>v_pushcon [simp]: "lookup \<C> p\<^sub>\<C> = Some (PushCon\<^sub>b n) \<Longrightarrow> halloc h (Const\<^sub>v n) = (h', v) \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>v h \<Delta> \<V> ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v S\<^sub>v h' \<Delta> (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s)"
| ev\<^sub>v_pushlam [simp]: "lookup \<C> p\<^sub>\<C> = Some (PushLam\<^sub>b p\<^sub>\<C>') \<Longrightarrow> halloc h (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>') = (h', v) \<Longrightarrow> 
      \<C> \<tturnstile> S\<^sub>v h \<Delta> \<V> ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v S\<^sub>v h' \<Delta> (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s)"
| ev\<^sub>v_apply [simp]: "lookup \<C> p\<^sub>\<C> = Some Apply\<^sub>b \<Longrightarrow> hlookup h v\<^sub>2 = Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>' \<Longrightarrow>
    halloc \<Delta> ([v\<^sub>1], p\<^sub>\<Delta>') = (\<Delta>', p\<^sub>\<Delta>'') \<Longrightarrow> 
      \<C> \<tturnstile> S\<^sub>v h \<Delta> (v\<^sub>1 # v\<^sub>2 # \<V>) ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v S\<^sub>v h \<Delta>' \<V> ((Suc p\<^sub>\<Delta>'', p\<^sub>\<C>') # (p\<^sub>\<Delta>, p\<^sub>\<C>) # s)"
| ev\<^sub>v_pushenv [simp]: "lookup \<C> p\<^sub>\<C> = Some PushEnv\<^sub>b \<Longrightarrow> hlookup \<Delta> p\<^sub>\<Delta> = (vs, p\<^sub>\<Delta>') \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>v h \<Delta> (v # \<V>) ((Suc p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v 
      S\<^sub>v h (hupdate \<Delta> p\<^sub>\<Delta> (vs @ [v], p\<^sub>\<Delta>')) \<V> ((Suc p\<^sub>\<Delta>, p\<^sub>\<C>) # s)"
| ev\<^sub>v_return [simp]: "lookup \<C> p\<^sub>\<C> = Some Return\<^sub>b \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>v h \<Delta> \<V> ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s) \<leadsto>\<^sub>v S\<^sub>v h \<Delta> \<V> s"
| ev\<^sub>v_jump [simp]: "lookup \<C> p\<^sub>\<C> = Some Jump\<^sub>b \<Longrightarrow> hlookup h v\<^sub>2 = Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>' \<Longrightarrow>
    halloc \<Delta> ([v\<^sub>1], p\<^sub>\<Delta>') = (\<Delta>', p\<^sub>\<Delta>'') \<Longrightarrow>
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