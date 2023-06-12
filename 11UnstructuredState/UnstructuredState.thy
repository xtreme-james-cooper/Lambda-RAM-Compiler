theory UnstructuredState
  imports "../07ByteCode/ByteCode" "../10FlatMemory/PointerTag"
begin

section \<open>Unstructured State\<close>

text \<open>We have almost arrived at a state low-level enough to qualify as a real machine. We just need 
to get rid of the heap abstractions - easily done by splitting them up into a \<open>nat \<Rightarrow> nat\<close> memory 
and a free-space pointer - and then the two remaining lists, the value and call stacks. Now that we
are using explicit \<open>nat \<Rightarrow> nat\<close> fields in the state, the value stack is simple to convert: we put it
into a memory map with a stack pointer. (We could not have done this earlier because the heap 
abstraction does not allow deallocation the way a stack needs.) The callstack is almost simple 
enough to do the same way, but we don't want to have to keep doing a memory lookup to get the 
code-pointer, because the code-pointer is referenced in every single operation. Instead, we put the 
tail of the callstack into the memory map, and keep the head (which is the current code pointer) in
its own register.\<close>

datatype unstr_state = 
  S\<^sub>u "nat \<Rightarrow> pointer_tag \<times> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat nat

fun unstr_lookup :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<rightharpoonup> nat" where
  "unstr_lookup h 0 x = None"
| "unstr_lookup h (Suc 0) x = None"
| "unstr_lookup h (Suc (Suc p)) 0 = (if even p then Some (h p) else None)"
| "unstr_lookup h (Suc (Suc p)) (Suc x) = (if even p then unstr_lookup h (h (Suc p)) x else None)"

inductive eval\<^sub>u :: "code\<^sub>b list \<Rightarrow> unstr_state \<Rightarrow> unstr_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>u" 50) where
  ev\<^sub>u_lookup [simp]: "lookup \<C> p\<^sub>\<C> = Some (Lookup\<^sub>b x) \<Longrightarrow> unstr_lookup \<Delta> (s p\<^sub>s) x = Some y \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> p\<^sub>\<V> s (Suc p\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>u S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> (\<V>(p\<^sub>\<V> := y)) (Suc p\<^sub>\<V>) s (Suc p\<^sub>s) p\<^sub>\<C>"
| ev\<^sub>u_pushcon [simp]: "lookup \<C> p\<^sub>\<C> = Some (PushCon\<^sub>b n) \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> p\<^sub>\<V> s (Suc p\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>u 
      S\<^sub>u (h(p\<^sub>h := (PConst, n), Suc p\<^sub>h := (PConst, 0))) (2 + p\<^sub>h) \<Delta> p\<^sub>\<Delta> 
        (\<V>(p\<^sub>\<V> := p\<^sub>h)) (Suc p\<^sub>\<V>) s (Suc p\<^sub>s) p\<^sub>\<C>"
| ev\<^sub>u_pushlam [simp]: "lookup \<C> p\<^sub>\<C> = Some (PushLam\<^sub>b p\<^sub>\<C>') \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> p\<^sub>\<V> s (Suc p\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>u 
      S\<^sub>u (h(p\<^sub>h := (PEnv, s p\<^sub>s), Suc p\<^sub>h := (PCode, p\<^sub>\<C>'))) (2 + p\<^sub>h) \<Delta> p\<^sub>\<Delta> 
        (\<V>(p\<^sub>\<V> := p\<^sub>h)) (Suc p\<^sub>\<V>) s (Suc p\<^sub>s) p\<^sub>\<C>"
| ev\<^sub>u_apply [simp]: "lookup \<C> p\<^sub>\<C> = Some Apply\<^sub>b \<Longrightarrow> h (\<V> p\<^sub>\<V>) = (PEnv, p\<^sub>\<Delta>') \<Longrightarrow> 
    h (Suc (\<V> p\<^sub>\<V>)) = (PCode, p\<^sub>\<C>') \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> (Suc (Suc p\<^sub>\<V>)) s (Suc p\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>u 
      S\<^sub>u h p\<^sub>h (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := p\<^sub>\<Delta>')) (2 + p\<^sub>\<Delta>) \<V> p\<^sub>\<V>
        (s(Suc p\<^sub>s := p\<^sub>\<C>, Suc (Suc p\<^sub>s) := Suc (Suc p\<^sub>\<Delta>))) (2 + Suc p\<^sub>s) p\<^sub>\<C>'"
| ev\<^sub>u_return [simp]: "lookup \<C> p\<^sub>\<C> = Some Return\<^sub>b \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> p\<^sub>\<V> s (Suc (Suc p\<^sub>s)) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>u 
      S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> p\<^sub>\<V> s p\<^sub>s (s p\<^sub>s)"
| ev\<^sub>u_jump [simp]: "lookup \<C> p\<^sub>\<C> = Some Jump\<^sub>b \<Longrightarrow> h (\<V> p\<^sub>\<V>) = (PEnv, p\<^sub>\<Delta>') \<Longrightarrow> 
    h (Suc (\<V> p\<^sub>\<V>)) = (PCode, p\<^sub>\<C>') \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> (Suc (Suc p\<^sub>\<V>)) s (Suc p\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>u 
      S\<^sub>u h p\<^sub>h (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := p\<^sub>\<Delta>')) (2 + p\<^sub>\<Delta>) \<V> p\<^sub>\<V>
        (s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) (Suc p\<^sub>s) p\<^sub>\<C>'"

theorem determinismu: "\<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>u \<Sigma>' \<Longrightarrow> \<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>u \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<C> \<Sigma> \<Sigma>' rule: eval\<^sub>u.induct)
  case ev\<^sub>u_lookup
  from ev\<^sub>u_lookup(3, 1, 2) show ?case by (induction rule: eval\<^sub>u.cases) simp_all
next
next
  case ev\<^sub>u_pushcon
  from ev\<^sub>u_pushcon(2, 1) show ?case by (induction rule: eval\<^sub>u.cases) simp_all
next
  case ev\<^sub>u_pushlam
  from ev\<^sub>u_pushlam(2, 1) show ?case by (induction rule: eval\<^sub>u.cases) simp_all
next
  case ev\<^sub>u_apply
  from ev\<^sub>u_apply(4, 1, 2, 3) show ?case by (induction rule: eval\<^sub>u.cases) simp_all
next
  case ev\<^sub>u_return
  from ev\<^sub>u_return(2, 1) show ?case by (induction rule: eval\<^sub>u.cases) simp_all
next
  case ev\<^sub>u_jump
  from ev\<^sub>u_jump(4, 1, 2, 3) show ?case by (induction rule: eval\<^sub>u.cases) simp_all
qed

end