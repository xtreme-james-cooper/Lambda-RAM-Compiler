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

datatype state\<^sub>r = 
  S\<^sub>r "nat \<Rightarrow> pointer_tag \<times> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat nat

fun unstr_lookup :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<rightharpoonup> nat" where
  "unstr_lookup h 0 x = None"
| "unstr_lookup h (Suc 0) x = None"
| "unstr_lookup h (Suc (Suc p)) 0 = (if even p then Some (h p) else None)"
| "unstr_lookup h (Suc (Suc p)) (Suc x) = (if even p then unstr_lookup h (h (Suc p)) x else None)"

inductive eval\<^sub>r :: "code\<^sub>b list \<Rightarrow> state\<^sub>r \<Rightarrow> state\<^sub>r \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>r" 50) where
  ev\<^sub>r_lookup [simp]: "lookup \<C> p\<^sub>\<C> = Some (Lookup\<^sub>b x) \<Longrightarrow> unstr_lookup \<Delta> (s b\<^sub>s) x = Some y \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>r h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> b\<^sub>\<V> s (Suc b\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r S\<^sub>r h b\<^sub>h \<Delta> b\<^sub>\<Delta> (\<V>(b\<^sub>\<V> := y)) (Suc b\<^sub>\<V>) s (Suc b\<^sub>s) p\<^sub>\<C>"
| ev\<^sub>r_pushcon [simp]: "lookup \<C> p\<^sub>\<C> = Some (PushCon\<^sub>b n) \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>r h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> b\<^sub>\<V> s (Suc b\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r 
      S\<^sub>r (h(b\<^sub>h := (PConst, n), Suc b\<^sub>h := (PConst, 0))) (2 + b\<^sub>h) \<Delta> b\<^sub>\<Delta> (\<V>(b\<^sub>\<V> := b\<^sub>h)) (Suc b\<^sub>\<V>) s 
        (Suc b\<^sub>s) p\<^sub>\<C>"
| ev\<^sub>r_pushlam [simp]: "lookup \<C> p\<^sub>\<C> = Some (PushLam\<^sub>b p\<^sub>\<C>') \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>r h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> b\<^sub>\<V> s (Suc b\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r 
      S\<^sub>r (h(b\<^sub>h := (PEnv, s b\<^sub>s), Suc b\<^sub>h := (PCode, p\<^sub>\<C>'))) (2 + b\<^sub>h) \<Delta> b\<^sub>\<Delta> (\<V>(b\<^sub>\<V> := b\<^sub>h)) (Suc b\<^sub>\<V>) s 
        (Suc b\<^sub>s) p\<^sub>\<C>"
| ev\<^sub>r_apply [simp]: "lookup \<C> p\<^sub>\<C> = Some Apply\<^sub>b \<Longrightarrow> h (\<V> b\<^sub>\<V>) = (PEnv, p\<^sub>\<Delta>) \<Longrightarrow> 
    h (Suc (\<V> b\<^sub>\<V>)) = (PCode, p\<^sub>\<C>') \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>r h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> (Suc (Suc b\<^sub>\<V>)) s (Suc b\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r 
      S\<^sub>r h b\<^sub>h (\<Delta>(b\<^sub>\<Delta> := \<V> (Suc b\<^sub>\<V>), Suc b\<^sub>\<Delta> := p\<^sub>\<Delta>)) (2 + b\<^sub>\<Delta>) \<V> b\<^sub>\<V>
        (s(Suc b\<^sub>s := p\<^sub>\<C>, Suc (Suc b\<^sub>s) := Suc (Suc b\<^sub>\<Delta>))) (2 + Suc b\<^sub>s) p\<^sub>\<C>'"
| ev\<^sub>r_pushenv [simp]: "lookup \<C> p\<^sub>\<C> = Some PushEnv\<^sub>b \<Longrightarrow>
    \<C> \<tturnstile> S\<^sub>r h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> (Suc b\<^sub>\<V>) s (Suc b\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r 
      S\<^sub>r h b\<^sub>h (\<Delta>(b\<^sub>\<Delta> := \<V> b\<^sub>\<V>, Suc b\<^sub>\<Delta> := s b\<^sub>s)) (Suc (Suc b\<^sub>\<Delta>)) \<V> b\<^sub>\<V> 
        (s(b\<^sub>s := b\<^sub>\<Delta>)) (Suc b\<^sub>s) p\<^sub>\<C>"
| ev\<^sub>r_return [simp]: "lookup \<C> p\<^sub>\<C> = Some Return\<^sub>b \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>r h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> b\<^sub>\<V> s (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r S\<^sub>r h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> b\<^sub>\<V> s b\<^sub>s (s b\<^sub>s)"
| ev\<^sub>r_jump [simp]: "lookup \<C> p\<^sub>\<C> = Some Jump\<^sub>b \<Longrightarrow> h (\<V> b\<^sub>\<V>) = (PEnv, p\<^sub>\<Delta>) \<Longrightarrow> 
    h (Suc (\<V> b\<^sub>\<V>)) = (PCode, p\<^sub>\<C>') \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>r h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> (Suc (Suc b\<^sub>\<V>)) s (Suc b\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r 
      S\<^sub>r h b\<^sub>h (\<Delta>(b\<^sub>\<Delta> := \<V> (Suc b\<^sub>\<V>), Suc b\<^sub>\<Delta> := p\<^sub>\<Delta>)) (2 + b\<^sub>\<Delta>) \<V> b\<^sub>\<V> (s(b\<^sub>s := Suc (Suc b\<^sub>\<Delta>))) 
        (Suc b\<^sub>s) p\<^sub>\<C>'"

theorem determinism\<^sub>r: "\<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>r \<Sigma>' \<Longrightarrow> \<C> \<tturnstile> \<Sigma> \<leadsto>\<^sub>r \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<C> \<Sigma> \<Sigma>' rule: eval\<^sub>r.induct)
  case ev\<^sub>r_lookup
  from ev\<^sub>r_lookup(3, 1, 2) show ?case by (induction rule: eval\<^sub>r.cases) simp_all
next
next
  case ev\<^sub>r_pushcon
  from ev\<^sub>r_pushcon(2, 1) show ?case by (induction rule: eval\<^sub>r.cases) simp_all
next
  case ev\<^sub>r_pushlam
  from ev\<^sub>r_pushlam(2, 1) show ?case by (induction rule: eval\<^sub>r.cases) simp_all
next
  case ev\<^sub>r_apply
  from ev\<^sub>r_apply(4, 1, 2, 3) show ?case by (induction rule: eval\<^sub>r.cases) simp_all
next
  case ev\<^sub>r_pushenv
  from ev\<^sub>r_pushenv(2, 1) show ?case by (induction rule: eval\<^sub>r.cases) simp_all
next
  case ev\<^sub>r_return
  from ev\<^sub>r_return(2, 1) show ?case by (induction rule: eval\<^sub>r.cases) simp_all
next
  case ev\<^sub>r_jump
  from ev\<^sub>r_jump(4, 1, 2, 3) show ?case by (induction rule: eval\<^sub>r.cases) simp_all
qed

end