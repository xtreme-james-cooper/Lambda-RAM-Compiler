theory HeapMemory
  imports "../08ByteCode/ByteCode" Heap
begin

subsection \<open>Heap-Memory Values\<close>

text \<open>Now that we have a way of representing heap-allocation, we can get rid of our duplicated 
values. Closure-values replace the environment instance with a list of pointers into the heap, and 
the state as a whole replaces the value stack and the callstack environments with more lists of 
pointers. To make all this work, of course, we also need the actual heap to be stored in the state 
now.\<close>

datatype closure\<^sub>h = 
  Const\<^sub>h nat
  | Lam\<^sub>h "ptr list" nat

datatype state\<^sub>h = 
  S\<^sub>h "closure\<^sub>h heap" "ptr list" "(ptr list \<times> nat) list"

text \<open>Our evaluation relation must now \<open>halloc\<close> values when pushing them, and \<open>hlookup\<close> them when 
popping; but beyond that, things are mostly the same as the previous stage, and we no longer 
duplicate values, only pointers to them.\<close>

inductive eval\<^sub>h :: "code\<^sub>b list \<Rightarrow> state\<^sub>h \<Rightarrow> state\<^sub>h \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>h" 50) where
  ev\<^sub>h_lookup [simp]: "lookup \<C> p = Some (Lookup\<^sub>b x y z) \<Longrightarrow> lookup \<Delta> x = Some v \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>h h \<V> ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>h S\<^sub>h h (v # \<V>) ((\<Delta>, p) # s)"
| ev\<^sub>h_pushcon [simp]: "lookup \<C> p = Some (PushCon\<^sub>b n) \<Longrightarrow> halloc h (Const\<^sub>h n) = (h', v) \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>h h \<V> ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>h S\<^sub>h h' (v # \<V>) ((\<Delta>, p) # s)"
| ev\<^sub>h_pushlam [simp]: "lookup \<C> p = Some (PushLam\<^sub>b p' n) \<Longrightarrow> halloc h (Lam\<^sub>h \<Delta> p') = (h', v) \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>h h \<V> ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>h S\<^sub>h h' (v # \<V>) ((\<Delta>, p) # s)"
| ev\<^sub>h_apply [simp]: "lookup \<C> p = Some Apply\<^sub>b \<Longrightarrow> hlookup h v\<^sub>2 = Lam\<^sub>h \<Delta>' p' \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>h h (v\<^sub>1 # v\<^sub>2 # \<V>) ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>h S\<^sub>h h \<V> ((v\<^sub>1 # \<Delta>', p') # (\<Delta>, p) # s)"
| ev\<^sub>h_pushenv [simp]: "lookup \<C> p = Some PushEnv\<^sub>b \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>h h (v # \<V>) ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>h S\<^sub>h h \<V> ((v # \<Delta>, p) # s)"
| ev\<^sub>h_return [simp]: "lookup \<C> p = Some Return\<^sub>b \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>h h \<V> ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>h S\<^sub>h h \<V> s"
| ev\<^sub>h_jump [simp]: "lookup \<C> p = Some Jump\<^sub>b \<Longrightarrow> hlookup h v\<^sub>2 = Lam\<^sub>h \<Delta>' p' \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>h h (v\<^sub>1 # v\<^sub>2 # \<V>) ((\<Delta>, Suc p) # s) \<leadsto>\<^sub>h S\<^sub>h h \<V> ((v\<^sub>1 # \<Delta>', p') # s)"

theorem determinismh: "\<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>h \<Sigma>' \<Longrightarrow> \<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>h \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<C> \<Sigma> \<Sigma>' rule: eval\<^sub>h.induct)
  case ev\<^sub>h_lookup
  from ev\<^sub>h_lookup(3, 1, 2) show ?case by (induction rule: eval\<^sub>h.cases) simp_all 
next
  case ev\<^sub>h_pushcon
  from ev\<^sub>h_pushcon(3, 1, 2) show ?case by (induction rule: eval\<^sub>h.cases) simp_all 
next
  case ev\<^sub>h_pushlam
  from ev\<^sub>h_pushlam(3, 1, 2) show ?case by (induction rule: eval\<^sub>h.cases) simp_all 
next
  case ev\<^sub>h_apply
  from ev\<^sub>h_apply(3, 1, 2) show ?case by (induction rule: eval\<^sub>h.cases) simp_all 
next
  case ev\<^sub>h_pushenv
  from ev\<^sub>h_pushenv(2, 1) show ?case by (induction rule: eval\<^sub>h.cases) simp_all 
next
  case ev\<^sub>h_return
  from ev\<^sub>h_return(2, 1) show ?case by (induction rule: eval\<^sub>h.cases) simp_all 
next
  case ev\<^sub>h_jump
  from ev\<^sub>h_jump(3, 1, 2) show ?case by (induction rule: eval\<^sub>h.cases) simp_all 
qed

end