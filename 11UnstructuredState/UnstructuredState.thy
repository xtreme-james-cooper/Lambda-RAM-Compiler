theory UnstructuredState
  imports "../07ByteCode/CodeFlattening"
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
  S\<^sub>u "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat "nat \<Rightarrow> nat" nat nat

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
      S\<^sub>u (h(p\<^sub>h := 1, Suc p\<^sub>h := n, Suc (Suc p\<^sub>h) := 0)) (3 + p\<^sub>h) \<Delta> p\<^sub>\<Delta> 
        (\<V>(p\<^sub>\<V> := p\<^sub>h)) (Suc p\<^sub>\<V>) s (Suc p\<^sub>s) p\<^sub>\<C>"
| ev\<^sub>u_pushlam [simp]: "lookup \<C> p\<^sub>\<C> = Some (PushLam\<^sub>b p\<^sub>\<C>') \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> p\<^sub>\<V> s (Suc p\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>u 
      S\<^sub>u (h(p\<^sub>h := 0, Suc p\<^sub>h := s p\<^sub>s, Suc (Suc p\<^sub>h) := p\<^sub>\<C>')) (3 + p\<^sub>h) \<Delta> p\<^sub>\<Delta> 
        (\<V>(p\<^sub>\<V> := p\<^sub>h)) (Suc p\<^sub>\<V>) s (Suc p\<^sub>s) p\<^sub>\<C>"
| ev\<^sub>u_apply [simp]: "lookup \<C> p\<^sub>\<C> = Some Apply\<^sub>b \<Longrightarrow> h (\<V> p\<^sub>\<V>) = 0 \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> (Suc (Suc p\<^sub>\<V>)) s (Suc p\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>u 
      S\<^sub>u h p\<^sub>h (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := h (Suc (\<V> p\<^sub>\<V>)))) (2 + p\<^sub>\<Delta>) \<V> p\<^sub>\<V>
        (s(Suc p\<^sub>s := p\<^sub>\<C>, Suc (Suc p\<^sub>s) := Suc (Suc p\<^sub>\<Delta>))) (2 + Suc p\<^sub>s) (h (Suc (Suc (\<V> p\<^sub>\<V>))))"
| ev\<^sub>u_return [simp]: "lookup \<C> p\<^sub>\<C> = Some Return\<^sub>b \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> p\<^sub>\<V> s (Suc (Suc p\<^sub>s)) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>u 
      S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> p\<^sub>\<V> s p\<^sub>s (s p\<^sub>s)"
| ev\<^sub>u_jump [simp]: "lookup \<C> p\<^sub>\<C> = Some Jump\<^sub>b \<Longrightarrow> h (\<V> p\<^sub>\<V>) = 0 \<Longrightarrow> 
    \<C> \<tturnstile> S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> (Suc (Suc p\<^sub>\<V>)) s (Suc p\<^sub>s) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>u 
      S\<^sub>u h p\<^sub>h (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := h (Suc (\<V> p\<^sub>\<V>)))) (2 + p\<^sub>\<Delta>) \<V> p\<^sub>\<V>
        (s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) (Suc p\<^sub>s) (h (Suc (Suc (\<V> p\<^sub>\<V>))))"

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
  from ev\<^sub>u_apply(3, 1, 2) show ?case by (induction rule: eval\<^sub>u.cases) simp_all
next
  case ev\<^sub>u_return
  from ev\<^sub>u_return(2, 1) show ?case by (induction rule: eval\<^sub>u.cases) simp_all
next
  case ev\<^sub>u_jump
  from ev\<^sub>u_jump(3, 1, 2) show ?case by (induction rule: eval\<^sub>u.cases) simp_all
qed











definition restructurable_heap :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "restructurable_heap h p\<^sub>h p\<^sub>\<Delta> lcd = (3 dvd p\<^sub>h \<and> (\<forall>x < p\<^sub>h. 3 dvd x \<longrightarrow> h x = 0 \<longrightarrow> 
    (even (h (Suc x)) \<and> h (Suc x) \<le> p\<^sub>\<Delta> \<and> h (Suc (Suc x)) \<noteq> 0 \<and> h (Suc (Suc x)) \<le> lcd)))"

definition restructurable_env :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h = (even p\<^sub>\<Delta> \<and>
    (\<forall>x < p\<^sub>\<Delta>. if even x then 3 dvd \<Delta> x \<and> \<Delta> x < p\<^sub>h else even (\<Delta> x) \<and> \<Delta> x < p\<^sub>\<Delta>))"

definition restructurable_vals :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "restructurable_vals \<V> p\<^sub>\<V> p\<^sub>h = (3 dvd p\<^sub>h \<and> (\<forall>x < p\<^sub>\<V>. 3 dvd \<V> x \<and> \<V> x < p\<^sub>h))"

definition restructurable_stack :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> bool" where
  "restructurable_stack s p\<^sub>s p\<^sub>\<Delta> lcd = (\<forall>x < p\<^sub>s. 
    if x = 0 then s x = 0 else if even x then s x \<noteq> 0 \<and> s x \<le> lcd else even (s x) \<and> s x \<le> p\<^sub>\<Delta>)"

primrec restructurable :: "unstr_state \<Rightarrow> code\<^sub>b list \<Rightarrow> bool" where
  "restructurable (S\<^sub>u h p\<^sub>h \<Delta> p\<^sub>\<Delta> \<V> p\<^sub>\<V> s p\<^sub>s p\<^sub>\<C>) \<C> = (p\<^sub>\<C> \<le> length \<C> \<and> 
    length \<C> \<noteq> 0 \<and> orderly_code \<C> 0 \<and> properly_terminated\<^sub>b \<C> \<and> restructurable_heap h p\<^sub>h p\<^sub>\<Delta> (length \<C>) \<and> 
      restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<and> restructurable_vals \<V> p\<^sub>\<V> p\<^sub>h \<and> 
        restructurable_stack s p\<^sub>s p\<^sub>\<Delta> (length \<C>) \<and> even p\<^sub>s \<and> (p\<^sub>s = 0 \<longrightarrow> p\<^sub>\<C> = 0))"

lemma [simp]: "odd (x::nat) \<Longrightarrow> 0 < x"
  by (cases x) simp_all

lemma [simp]: "properly_terminated\<^sub>b \<C> \<Longrightarrow> lookup \<C> 0 \<noteq> Some (Lookup\<^sub>b x)"
  by (induction \<C>) auto

lemma [simp]: "properly_terminated\<^sub>b \<C> \<Longrightarrow> lookup \<C> 0 \<noteq> Some (PushCon\<^sub>b k)"
  by (induction \<C>) auto

lemma [simp]: "properly_terminated\<^sub>b \<C> \<Longrightarrow> lookup \<C> 0 \<noteq> Some (PushLam\<^sub>b p\<^sub>\<C>)"
  by (induction \<C>) auto

lemma [simp]: "properly_terminated\<^sub>b \<C> \<Longrightarrow> lookup \<C> 0 \<noteq> Some Apply\<^sub>b"
  by (induction \<C>) auto

lemma [dest]: "x \<noteq> y \<Longrightarrow> x < Suc y \<Longrightarrow> x < y"
  by presburger

lemma [dest]: "x \<noteq> y \<Longrightarrow> x \<noteq> Suc y \<Longrightarrow> x < Suc (Suc y) \<Longrightarrow> x < y"
  by presburger

lemma [simp]: "3 dvd x \<Longrightarrow> 3 dvd Suc x = False"
  by presburger

lemma [simp]: "3 dvd x \<Longrightarrow> 3 dvd Suc (Suc x) = False"
  by presburger

lemma [elim]: "restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> even p\<^sub>\<Delta>"
  by (simp add: restructurable_env_def)

lemma [elim]: "restructurable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> 3 dvd p\<^sub>h"
  by (simp add: restructurable_heap_def)

lemma [simp]: "restructurable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> 
    restructurable_heap (h(p\<^sub>h := Suc 0, Suc p\<^sub>h := k, Suc (Suc p\<^sub>h) := 0)) (3 + p\<^sub>h) p\<^sub>\<Delta> lcd"
  by (auto simp add: restructurable_heap_def)

lemma [simp]: "restructurable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> lcd \<noteq> 0 \<Longrightarrow>
  restructurable_heap (h(p\<^sub>h := 0, Suc p\<^sub>h := k, Suc (Suc p\<^sub>h) := p\<^sub>\<C>)) (3 + p\<^sub>h) p\<^sub>\<Delta> lcd = 
    (even k \<and> k \<le> p\<^sub>\<Delta> \<and> p\<^sub>\<C> \<noteq> 0 \<and> p\<^sub>\<C> \<le> lcd)"
proof
  let ?f = "\<lambda>x. if x = Suc (Suc p\<^sub>h) then p\<^sub>\<C> else (h(p\<^sub>h := 0, Suc p\<^sub>h := k)) x"
  let ?g = "\<lambda>x. if x = Suc p\<^sub>h then p\<^sub>\<C> else (h(p\<^sub>h := 0, Suc p\<^sub>h := k)) (Suc x)"
  let ?h = "\<lambda>x. if x = p\<^sub>h then p\<^sub>\<C> else (h(p\<^sub>h := 0, Suc p\<^sub>h := k)) (Suc (Suc x))"
  assume H: "restructurable_heap (h(p\<^sub>h := 0, Suc p\<^sub>h := k, Suc (Suc p\<^sub>h) := p\<^sub>\<C>)) (3 + p\<^sub>h) p\<^sub>\<Delta> lcd"
  moreover hence "\<And>x. x < 3 + p\<^sub>h \<Longrightarrow> 3 dvd x \<Longrightarrow> ?f x = 0 \<Longrightarrow> 
    even (?g x) \<and> ?g x \<le> p\<^sub>\<Delta> \<and> 0 < ?h x \<and> ?h x \<le> lcd" by (simp add: restructurable_heap_def)
  moreover from H have "3 dvd p\<^sub>h" by (simp add: restructurable_heap_def)
  ultimately have "p\<^sub>h < 3 + p\<^sub>h \<Longrightarrow> ?f p\<^sub>h = 0 \<Longrightarrow> 
    even (?g p\<^sub>h) \<and> ?g p\<^sub>h \<le> p\<^sub>\<Delta> \<and> 0 < ?h p\<^sub>h \<and> ?h p\<^sub>h \<le> lcd" by blast
  moreover assume "lcd \<noteq> 0"
  ultimately show "even k \<and> k \<le> p\<^sub>\<Delta> \<and> p\<^sub>\<C> \<noteq> 0 \<and> p\<^sub>\<C> \<le> lcd" by simp
next
  assume "restructurable_heap h p\<^sub>h p\<^sub>\<Delta> lcd" and "even k \<and> k \<le> p\<^sub>\<Delta> \<and> p\<^sub>\<C> \<noteq> 0 \<and> p\<^sub>\<C> \<le> lcd"
  thus "restructurable_heap (h(p\<^sub>h := 0, Suc p\<^sub>h := k, Suc (Suc p\<^sub>h) := p\<^sub>\<C>)) (3 + p\<^sub>h) p\<^sub>\<Delta> lcd" 
    by (auto simp add: restructurable_heap_def)
qed

lemma [simp]: "restructurable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> restructurable_heap h p\<^sub>h (Suc (Suc p\<^sub>\<Delta>)) lcd"
  by (auto simp add: restructurable_heap_def)

lemma [simp]: "restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> restructurable_env \<Delta> p\<^sub>\<Delta> (3 + p\<^sub>h)"
  by (auto simp add: restructurable_env_def)

lemma [elim]: "p < p\<^sub>\<Delta> \<Longrightarrow> odd p \<Longrightarrow> restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> \<Delta> p < p\<^sub>\<Delta>"
  by (simp add: restructurable_env_def)

lemma [simp]: "restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> restructurable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> 
  restructurable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> h (\<V> p\<^sub>\<V>) = 0 \<Longrightarrow>
    restructurable_env (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := h (Suc (\<V> p\<^sub>\<V>)))) (Suc (Suc p\<^sub>\<Delta>)) p\<^sub>h"
proof (unfold restructurable_env_def restructurable_vals_def restructurable_heap_def, 
       rule, simp, rule, rule)
  fix y 
  assume "3 dvd p\<^sub>h \<and> (\<forall>x < p\<^sub>h. 3 dvd x \<longrightarrow> h x = 0 \<longrightarrow> 
    even (h (Suc x)) \<and> h (Suc x) \<le> p\<^sub>\<Delta> \<and> h (Suc (Suc x)) \<noteq> 0 \<and> h (Suc (Suc x)) \<le> lcd)"
     and "h (\<V> p\<^sub>\<V>) = 0" and "3 dvd p\<^sub>h \<and> (\<forall>x < Suc (Suc p\<^sub>\<V>). 3 dvd \<V> x \<and> \<V> x < p\<^sub>h)"
  hence "even (h (Suc (\<V> p\<^sub>\<V>))) \<and> h (Suc (\<V> p\<^sub>\<V>)) \<le> p\<^sub>\<Delta>" by simp
  moreover assume "even p\<^sub>\<Delta> \<and> 
    (\<forall>x < p\<^sub>\<Delta>. if even x then 3 dvd \<Delta> x \<and> \<Delta> x < p\<^sub>h else even (\<Delta> x) \<and> \<Delta> x < p\<^sub>\<Delta>)"
              and "y < Suc (Suc p\<^sub>\<Delta>)" and "3 dvd p\<^sub>h \<and> (\<forall>x < Suc (Suc p\<^sub>\<V>). 3 dvd \<V> x \<and> \<V> x < p\<^sub>h)"
  ultimately show "if even y
        then 3 dvd (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := h (Suc (\<V> p\<^sub>\<V>)))) y \<and> 
          (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := h (Suc (\<V> p\<^sub>\<V>)))) y < p\<^sub>h
        else even ((\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := h (Suc (\<V> p\<^sub>\<V>)))) y) \<and>
          (\<Delta>(p\<^sub>\<Delta> := \<V> (Suc p\<^sub>\<V>), Suc p\<^sub>\<Delta> := h (Suc (\<V> p\<^sub>\<V>)))) y < Suc (Suc p\<^sub>\<Delta>)" by auto
qed

lemma [simp]: "restructurable_vals \<V> p\<^sub>\<V> p\<^sub>h \<Longrightarrow> 
    restructurable_vals (\<V>(p\<^sub>\<V> := k)) (Suc p\<^sub>\<V>) p\<^sub>h = (3 dvd p\<^sub>h \<and> k < p\<^sub>h \<and> 3 dvd k)"
  by (auto simp add: restructurable_vals_def)

lemma [simp]: "restructurable_vals \<V> p\<^sub>\<V> p\<^sub>h \<Longrightarrow> 
    restructurable_vals (\<V>(p\<^sub>\<V> := k)) (Suc p\<^sub>\<V>) (3 + p\<^sub>h) = (3 dvd p\<^sub>h \<and> k < 3 + p\<^sub>h \<and> 3 dvd k)"
  by (auto simp add: restructurable_vals_def)

lemma [elim]: "restructurable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> restructurable_vals \<V> p\<^sub>\<V> p\<^sub>h"
  by (simp add: restructurable_vals_def)

lemma [elim]: "restructurable_stack s (Suc (Suc p\<^sub>s)) p\<^sub>\<Delta> lcd \<Longrightarrow>
    restructurable_stack (s(p\<^sub>s := 0)) p\<^sub>s p\<^sub>\<Delta> lcd"
  by (simp add: restructurable_stack_def)

lemma [simp]: "restructurable_stack s 0 p\<^sub>\<Delta> lcd"
  by (simp add: restructurable_stack_def)

lemma [elim]: "restructurable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> s 0 = 0"
  by (simp add: restructurable_stack_def)

lemma [simp]: "restructurable_stack s (Suc (Suc p\<^sub>s)) p\<^sub>\<Delta> lcd \<Longrightarrow> even p\<^sub>s \<Longrightarrow> s p\<^sub>s \<le> lcd"
proof (unfold restructurable_stack_def)
  assume "\<forall>x<Suc (Suc p\<^sub>s). if x = 0 then s x = 0 else if even x 
    then s x \<noteq> 0 \<and> s x \<le> lcd else even (s x) \<and> s x \<le> p\<^sub>\<Delta>"
     and "even p\<^sub>s"
  hence "if p\<^sub>s = 0 then s p\<^sub>s = 0 else s p\<^sub>s \<noteq> 0 \<and> s p\<^sub>s \<le> lcd" by simp
  thus "s p\<^sub>s \<le> lcd" by (simp split: if_splits)
qed

lemma [simp]: "0 \<noteq> p\<^sub>\<C> \<Longrightarrow> p\<^sub>\<C> \<le> lcd \<Longrightarrow> even p\<^sub>\<Delta> \<Longrightarrow> even p\<^sub>s \<Longrightarrow> p\<^sub>s \<noteq> 0 \<Longrightarrow> 
  restructurable_stack s p\<^sub>s p\<^sub>\<Delta> lcd \<Longrightarrow>
    restructurable_stack (s(p\<^sub>s := p\<^sub>\<C>, Suc p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) (Suc (Suc p\<^sub>s)) (Suc (Suc p\<^sub>\<Delta>)) lcd"
proof (unfold restructurable_stack_def)
  let ?sh = "s(p\<^sub>s := p\<^sub>\<C>, Suc p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))"
  assume R: "\<forall>x < p\<^sub>s. if x = 0 then s x = 0 else if even x then s x \<noteq> 0 \<and> s x \<le> lcd 
    else even (s x) \<and> s x \<le> p\<^sub>\<Delta>"
  hence "\<And>x. x < p\<^sub>s \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> odd x \<Longrightarrow> even (s x) \<and> s x \<le> p\<^sub>\<Delta>" by simp
  hence X: "\<And>x. odd x \<Longrightarrow> x < p\<^sub>s \<Longrightarrow> s x \<le> Suc (Suc p\<^sub>\<Delta>)" by fastforce
  assume "0 \<noteq> p\<^sub>\<C>" and "p\<^sub>\<C> \<le> lcd" and "even p\<^sub>\<Delta>" and "even p\<^sub>s" and "p\<^sub>s \<noteq> 0"
  with R X show "\<forall>x<Suc (Suc p\<^sub>s). if x = 0 then ?sh x = 0 
    else if even x then ?sh x \<noteq> 0 \<and> ?sh x \<le> lcd else even (?sh x) \<and> ?sh x \<le> Suc (Suc p\<^sub>\<Delta>)" 
      by auto
qed

lemma [simp]: "restructurable_stack s p\<^sub>s p\<^sub>\<Delta> lcd \<Longrightarrow> even p\<^sub>s \<Longrightarrow> Suc p\<^sub>\<C> \<le> lcd \<Longrightarrow> p\<^sub>s \<noteq> 0 \<Longrightarrow>
  restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> properly_terminated\<^sub>b \<C> \<Longrightarrow> lookup \<C> p\<^sub>\<C> = Some Apply\<^sub>b \<Longrightarrow> 
    restructurable_stack (s(p\<^sub>s := p\<^sub>\<C>, Suc p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) (Suc (Suc p\<^sub>s)) (Suc (Suc p\<^sub>\<Delta>)) lcd"
proof -
  assume "properly_terminated\<^sub>b \<C>" and "lookup \<C> p\<^sub>\<C> = Some Apply\<^sub>b"
  hence "p\<^sub>\<C> = 0 \<Longrightarrow> False" by simp
  hence "p\<^sub>\<C> \<noteq> 0" by auto
  moreover assume "restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h"
  moreover hence "even p\<^sub>\<Delta>" by auto
  moreover assume "restructurable_stack s p\<^sub>s p\<^sub>\<Delta> lcd" and "even p\<^sub>s" and "Suc p\<^sub>\<C> \<le> lcd" and "p\<^sub>s \<noteq> 0"
  ultimately show ?thesis by simp
qed

lemma [simp]: "restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> restructurable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> 
    odd p\<^sub>s \<Longrightarrow> restructurable_stack (s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) (Suc p\<^sub>s) (Suc (Suc p\<^sub>\<Delta>)) lcd"
proof (unfold restructurable_stack_def)
  assume E: "restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h"
  assume O: "odd p\<^sub>s"
  assume R: "\<forall>x < Suc p\<^sub>s. if x = 0 then s x = 0 else if even x then s x \<noteq> 0 \<and> s x \<le> lcd 
    else even (s x) \<and> s x \<le> p\<^sub>\<Delta>"
  hence "\<And>x. x < Suc p\<^sub>s \<Longrightarrow> x \<noteq> 0 \<Longrightarrow> odd x \<Longrightarrow> even (s x) \<and> s x \<le> p\<^sub>\<Delta>" by simp
  hence "\<And>x. odd x \<Longrightarrow> x < Suc p\<^sub>s \<Longrightarrow> s x \<le> Suc (Suc p\<^sub>\<Delta>)" by fastforce
  with E R O show "\<forall>x<Suc p\<^sub>s. if x = 0 then (s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) x = 0
    else if even x then (s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) x \<noteq> 0 \<and> (s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) x \<le> lcd
      else even ((s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) x) \<and> (s(p\<^sub>s := Suc (Suc p\<^sub>\<Delta>))) x \<le> Suc (Suc p\<^sub>\<Delta>)" 
    by auto
qed

lemma [simp]: "h (\<V> p\<^sub>\<V>) = 0 \<Longrightarrow> restructurable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> 
    restructurable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> 0 < h (Suc (Suc (\<V> p\<^sub>\<V>)))"
  by (simp add: restructurable_heap_def restructurable_vals_def)

lemma [simp]: "h (\<V> p\<^sub>\<V>) = 0 \<Longrightarrow> restructurable_heap h p\<^sub>h p\<^sub>\<Delta> lcd \<Longrightarrow> 
    restructurable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> h (Suc (Suc (\<V> p\<^sub>\<V>))) \<le> lcd"
  by (simp add: restructurable_heap_def restructurable_vals_def)

lemma [elim]: "unstr_lookup \<Delta> p x = Some y \<Longrightarrow> p \<le> p\<^sub>\<Delta> \<Longrightarrow> even p \<Longrightarrow> restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> 
  y < p\<^sub>h"
proof (induction \<Delta> p x rule: unstr_lookup.induct)
  case (4 \<Delta> p x)
  moreover hence "even (\<Delta> (Suc p)) \<and> \<Delta> (Suc p) < p\<^sub>\<Delta>" by (simp add: restructurable_env_def)
  ultimately show ?case by simp
qed (auto simp add: restructurable_env_def)

lemma [elim]: "unstr_lookup \<Delta> p x = Some y \<Longrightarrow> p \<le> p\<^sub>\<Delta> \<Longrightarrow> even p \<Longrightarrow> restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> 
  3 dvd y"
proof (induction \<Delta> p x rule: unstr_lookup.induct) 
  case (4 \<Delta> p x)
  moreover hence "even (\<Delta> (Suc p)) \<and> \<Delta> (Suc p) < p\<^sub>\<Delta>" by (simp add: restructurable_env_def)
  ultimately show ?case by simp
qed (auto simp add: restructurable_env_def)

lemma [simp]: "odd p\<^sub>s \<Longrightarrow> restructurable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> even (s p\<^sub>s)" 
  by (unfold restructurable_stack_def) auto

lemma [simp]: "odd p\<^sub>s \<Longrightarrow> restructurable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> s p\<^sub>s \<le> p\<^sub>\<Delta>" 
  by (unfold restructurable_stack_def) auto

lemma [elim]: "unstr_lookup \<Delta> (s p\<^sub>s) x = Some y \<Longrightarrow> restructurable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> 
  restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> odd p\<^sub>s \<Longrightarrow> y < p\<^sub>h"
proof -
  assume "odd p\<^sub>s" and "restructurable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd"  
  hence "even (s p\<^sub>s)" and "s p\<^sub>s \<le> p\<^sub>\<Delta>" by auto
  moreover assume "unstr_lookup \<Delta> (s p\<^sub>s) x = Some y" and "restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h"
  ultimately show "y < p\<^sub>h" by auto
qed

lemma [elim]: "unstr_lookup \<Delta> (s p\<^sub>s) x = Some y \<Longrightarrow> restructurable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd \<Longrightarrow> 
  restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h \<Longrightarrow> odd p\<^sub>s \<Longrightarrow> 3 dvd y"
proof -
  assume "odd p\<^sub>s" and "restructurable_stack s (Suc p\<^sub>s) p\<^sub>\<Delta> lcd"  
  hence "s p\<^sub>s \<le> p\<^sub>\<Delta> \<and> even (s p\<^sub>s)" by simp
  moreover assume "unstr_lookup \<Delta> (s p\<^sub>s) x = Some y" and "restructurable_env \<Delta> p\<^sub>\<Delta> p\<^sub>h"
  ultimately show "3 dvd y" by auto
qed

lemma [simp]: "h (\<V> p\<^sub>\<V>) = 0 \<Longrightarrow> restructurable_heap h p\<^sub>h p\<^sub>\<Delta> (length \<C>) \<Longrightarrow> 
    restructurable_vals \<V> (Suc (Suc p\<^sub>\<V>)) p\<^sub>h \<Longrightarrow> h (Suc (Suc (\<V> p\<^sub>\<V>))) \<noteq> 0"
  by simp

lemma [elim]: "restructurable_stack s (Suc (Suc p\<^sub>s)) p\<^sub>\<Delta> lcd \<Longrightarrow> restructurable_stack s p\<^sub>s p\<^sub>\<Delta> lcd"
  by (unfold restructurable_stack_def, rule) simp

lemma preserve_restructure [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u \<C> \<Longrightarrow> 
    restructurable \<Sigma>\<^sub>u' \<C>"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: eval\<^sub>u.induct) auto

lemma [simp]: "iter (\<tturnstile> \<C> \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u \<C> \<Longrightarrow> restructurable \<Sigma>\<^sub>u' \<C>"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct) auto

lemma [simp]: "restructurable_heap nmem 0 0 x"
  by (simp add: restructurable_heap_def)

lemma [simp]: "restructurable_env nmem 0 0"
  by (simp add: restructurable_env_def)

lemma [simp]: "restructurable_vals nmem 0 0" 
  by (simp add: restructurable_vals_def)

lemma [simp]: "restructurable_stack (nmem(0 := 0, Suc 0 := 0)) 2 0 lcd"
  by (simp only: restructurable_stack_def) simp_all

end