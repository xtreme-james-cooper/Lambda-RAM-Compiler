theory FlatMemory
  imports "../07ByteCode/ByteCode" "../08HeapMemory/Heap" PointerTag
begin

text \<open>The chained memory stage is quite low-level, but it still possesses some structured data: 
pairs in the stack and the environment heap, and tagged closure-values in the value heap. We now 
reduce all of these to contiguous series of numbers. The pairs are just listed, first component 
first; the closures are flattened to sequences of data. A \<open>Const\<^sub>v n\<close> value becomes \<open>[n, 0]\<close>; a 
\<open>Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>\<close> becomes \<open>[p\<^sub>\<Delta>, p\<^sub>\<C>]\<close>. (The padding 0 on the numerical values is just to keep all values 
the same size, greatly easing some of the proofs.) We also tag the code and environment pointers 
because we need to recognize them later, when we move to assembly code and alter all the codeblock 
addresses; besides that, in losing the value constructors and the implicit tag that goes with that, 
we have now discarded our last scrap of source-level type-safety. The \<open>ev\<^sub>f_apply\<close> and \<open>ev\<^sub>f_jump\<close> 
operations assume they've been given a function-closure, and check that they have environment and 
code pointers, but the memory itself no longer records as such that there is a function stored 
there.\<close>

datatype state\<^sub>f = 
  S\<^sub>f "(pointer_tag \<times> nat) heap" "ptr heap" "ptr list" "nat list"

fun flat_lookup :: "ptr heap \<Rightarrow> ptr \<Rightarrow> nat \<rightharpoonup> ptr" where
  "flat_lookup h 0 x = None"
| "flat_lookup h (Suc 0) x = None"
| "flat_lookup h (Suc (Suc p)) 0 = (if even p then Some (hlookup h p) else None)"
| "flat_lookup h (Suc (Suc p)) (Suc x) = (
    if even p then flat_lookup h (hlookup h (Suc p)) x else None)"

inductive eval\<^sub>f :: "code\<^sub>b list \<Rightarrow> state\<^sub>f \<Rightarrow> state\<^sub>f \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>f" 50) where
  ev\<^sub>f_lookup [simp]: "lookup \<C> p\<^sub>\<C> = Some (Lookup\<^sub>b x) \<Longrightarrow> flat_lookup \<Delta> p\<^sub>\<Delta> x = Some v \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>f h \<Delta> \<V> (Suc p\<^sub>\<C> # p\<^sub>\<Delta> # s) \<leadsto>\<^sub>f S\<^sub>f h \<Delta> (v # \<V>) (p\<^sub>\<C> # p\<^sub>\<Delta> # s)"
| ev\<^sub>f_pushcon [simp]: "lookup \<C> p\<^sub>\<C> = Some (PushCon\<^sub>b n) \<Longrightarrow> 
    halloc_list h [(PConst, n), (PConst, 0)] = (h', v) \<Longrightarrow>
      \<C> \<tturnstile> S\<^sub>f h \<Delta> \<V> (Suc p\<^sub>\<C> # p\<^sub>\<Delta> # s) \<leadsto>\<^sub>f S\<^sub>f h' \<Delta> (v # \<V>) (p\<^sub>\<C> # p\<^sub>\<Delta> # s)"
| ev\<^sub>f_pushlam [simp]: "lookup \<C> p\<^sub>\<C> = Some (PushLam\<^sub>b p\<^sub>\<C>') \<Longrightarrow> 
    halloc_list h [(PEnv, p\<^sub>\<Delta>), (PCode, p\<^sub>\<C>')] = (h', v) \<Longrightarrow> 
      \<C> \<tturnstile> S\<^sub>f h \<Delta> \<V> (Suc p\<^sub>\<C> # p\<^sub>\<Delta> # s) \<leadsto>\<^sub>f S\<^sub>f h' \<Delta> (v # \<V>) (p\<^sub>\<C> # p\<^sub>\<Delta> # s)"
| ev\<^sub>f_apply [simp]: "lookup \<C> p\<^sub>\<C> = Some Apply\<^sub>b \<Longrightarrow> hlookup h v\<^sub>2 = (PEnv, p\<^sub>\<Delta>') \<Longrightarrow> 
    hlookup h (Suc v\<^sub>2) = (PCode, p\<^sub>\<C>') \<Longrightarrow> halloc_list \<Delta> [v\<^sub>1, p\<^sub>\<Delta>'] = (\<Delta>', p\<^sub>\<Delta>'') \<Longrightarrow> 
      \<C> \<tturnstile> S\<^sub>f h \<Delta> (v\<^sub>1 # v\<^sub>2 # \<V>) (Suc p\<^sub>\<C> # p\<^sub>\<Delta> # s) \<leadsto>\<^sub>f S\<^sub>f h \<Delta>' \<V> (p\<^sub>\<C>' # Suc (Suc p\<^sub>\<Delta>'') # p\<^sub>\<C> # p\<^sub>\<Delta> # s)"
| ev\<^sub>f_pushenv [simp]: "lookup \<C> p\<^sub>\<C> = Some PushEnv\<^sub>b \<Longrightarrow> halloc_list \<Delta> [v, p\<^sub>\<Delta>] = (\<Delta>', p\<^sub>\<Delta>') \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>f h \<Delta> (v # \<V>) (Suc p\<^sub>\<C> # p\<^sub>\<Delta> # s) \<leadsto>\<^sub>f S\<^sub>f h \<Delta>' \<V> (p\<^sub>\<C> # p\<^sub>\<Delta>' # s)"
| ev\<^sub>f_return [simp]: "lookup \<C> p\<^sub>\<C> = Some Return\<^sub>b \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>f h \<Delta> \<V> (Suc p\<^sub>\<C> # p\<^sub>\<Delta> # s) \<leadsto>\<^sub>f S\<^sub>f h \<Delta> \<V> s"
| ev\<^sub>f_jump [simp]: "lookup \<C> p\<^sub>\<C> = Some Jump\<^sub>b \<Longrightarrow> hlookup h v\<^sub>2 = (PEnv, p\<^sub>\<Delta>') \<Longrightarrow> 
    hlookup h (Suc v\<^sub>2) = (PCode, p\<^sub>\<C>') \<Longrightarrow> halloc_list \<Delta> [v\<^sub>1, p\<^sub>\<Delta>'] = (\<Delta>', p\<^sub>\<Delta>'') \<Longrightarrow> 
      \<C> \<tturnstile> S\<^sub>f h \<Delta> (v\<^sub>1 # v\<^sub>2 # \<V>) (Suc p\<^sub>\<C> # p\<^sub>\<Delta> # s) \<leadsto>\<^sub>f S\<^sub>f h \<Delta>' \<V> (p\<^sub>\<C>' # Suc (Suc p\<^sub>\<Delta>'') # s)"

theorem determinism\<^sub>f: "\<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>f \<Sigma>' \<Longrightarrow> \<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>f \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>f.induct)
  case ev\<^sub>f_lookup
  from ev\<^sub>f_lookup(3, 1, 2) show ?case by (induction rule: eval\<^sub>f.cases) simp_all 
next
  case ev\<^sub>f_pushcon
  from ev\<^sub>f_pushcon(3, 1, 2) show ?case by (induction rule: eval\<^sub>f.cases) simp_all 
next
  case ev\<^sub>f_pushlam
  from ev\<^sub>f_pushlam(3, 1, 2) show ?case by (induction rule: eval\<^sub>f.cases) simp_all  
next
  case ev\<^sub>f_apply
  from ev\<^sub>f_apply(5, 1, 2, 3, 4) show ?case by (induction rule: eval\<^sub>f.cases) simp_all  
next
  case ev\<^sub>f_pushenv
  from ev\<^sub>f_pushenv(3, 1, 2) show ?case by (induction rule: eval\<^sub>f.cases) simp_all  
next
  case ev\<^sub>f_return
  from ev\<^sub>f_return(2, 1) show ?case by (induction rule: eval\<^sub>f.cases) simp_all 
next
  case ev\<^sub>f_jump
  from ev\<^sub>f_jump(5, 1, 2, 3, 4) show ?case by (induction rule: eval\<^sub>f.cases) simp_all 
qed

end