theory HeapConversion
  imports HeapMemory
begin

subsection \<open>Heap conversion\<close>

text \<open>As usual with evaluation state refinements, many possible heaps correspond to one bytecode 
state. So we must define our conversion functions running backwards; taking care to make sure that 
each function terminates. Unlike the codebase ordered-pointer property, which could be falsified by
looping code or other features we carefully avoid, the ordered-heap property we use here is 
necessarily true even for a more complex language, since no value, no matter what kind, can 
reference values that haven't even been allocated yet.\<close>

fun unheap_closure :: "closure\<^sub>h heap \<Rightarrow> ptr \<Rightarrow> closure\<^sub>b" where
  "unheap_closure h x = (case hlookup h x of 
      Const\<^sub>h n \<Rightarrow> Const\<^sub>b n
    | Lam\<^sub>h \<Delta> p \<Rightarrow> Lam\<^sub>b (if list_all ((>) x) \<Delta> then map (unheap_closure h) \<Delta> else undefined) p)"

abbreviation unheap_stack :: "closure\<^sub>h heap \<Rightarrow> (ptr list \<times> nat) list \<Rightarrow> (closure\<^sub>b list \<times> nat) list" 
    where
  "unheap_stack h s \<equiv> map (\<lambda>(\<Delta>, p). (map (unheap_closure h) \<Delta>, p)) s"

primrec unheap :: "state\<^sub>h \<Rightarrow> state\<^sub>b" where
  "unheap (S\<^sub>h h \<V> s) = S\<^sub>b (map (unheap_closure h) \<V>) (unheap_stack h s)"

primrec bounded_closure :: "closure\<^sub>h heap \<Rightarrow> ptr \<Rightarrow> closure\<^sub>h \<Rightarrow> bool" where
  "bounded_closure h x (Const\<^sub>h n) = True"
| "bounded_closure h x (Lam\<^sub>h \<Delta> p) = (list_all (hcontains h) \<Delta> \<and> list_all ((>) x) \<Delta>)"

lemma halloc_bounded [simp]: "halloc h a = (h', x) \<Longrightarrow> bounded_closure h y c \<Longrightarrow> 
    bounded_closure h' y c"
  by (induction c) simp_all

lemma halloc_heap_bounded [simp]: "heap_all (bounded_closure h) h \<Longrightarrow> halloc h c = (h', v) \<Longrightarrow> 
  bounded_closure h v c \<Longrightarrow> heap_all (bounded_closure h') h'"
proof -
  assume A: "halloc h c = (h', v)" and "heap_all (bounded_closure h) h" and "bounded_closure h v c"
  hence "heap_all (bounded_closure h) h'" by auto
  moreover from A have "\<And>x c. bounded_closure h x c \<Longrightarrow> bounded_closure h' x c" by simp
  ultimately show ?thesis by auto
qed

lemma halloc_unheap_closure [simp]: "halloc h c = (h', v) \<Longrightarrow> hcontains h x \<Longrightarrow> 
  heap_all (bounded_closure h) h \<Longrightarrow> unheap_closure h' x = unheap_closure h x"
proof (induction h x rule: unheap_closure.induct)
  case (1 h x)
  thus ?case
  proof (cases "hlookup h x")
    case (Lam\<^sub>h \<Delta> p)
    with 1 show ?thesis
    proof (cases "list_all ((>) x) \<Delta>")
      case True
      from Lam\<^sub>h 1 have "list_all (hcontains h) \<Delta>" by (metis hlookup_all bounded_closure.simps(2))
      hence S: "\<And>y. y \<in> set \<Delta> \<Longrightarrow> hcontains h y" by auto
      from 1 Lam\<^sub>h True have "\<And>y. y \<in> set \<Delta> \<Longrightarrow> hcontains h y \<Longrightarrow> 
        unheap_closure h' y = unheap_closure h y" by simp
      with S 1(2, 3) Lam\<^sub>h True show ?thesis by simp
    qed simp_all
  qed simp_all
qed

lemma halloc_unheap_env [simp]: "halloc h c = (h', v) \<Longrightarrow> list_all (hcontains h) \<Delta> \<Longrightarrow> 
    heap_all (bounded_closure h) h \<Longrightarrow> map (unheap_closure h') \<Delta> = map (unheap_closure h) \<Delta>"
  by (induction \<Delta>) (simp_all del: unheap_closure.simps)

lemma halloc_unheap_stack [simp]: "halloc h c = (h', v) \<Longrightarrow> 
  list_all (list_all (hcontains h)) (map fst s) \<Longrightarrow> heap_all (bounded_closure h) h \<Longrightarrow> 
    unheap_stack h' s = unheap_stack h s"
  by (induction s) (auto simp del: unheap_closure.simps)

lemma hlookup_lam_bounded [simp]: "hlookup h v = Lam\<^sub>h \<Delta> p \<Longrightarrow> heap_all (bounded_closure h) h \<Longrightarrow> 
    hcontains h v \<Longrightarrow> list_all ((>) v) \<Delta>"
  by (metis hlookup_all bounded_closure.simps(2))

primrec heap_structured :: "state\<^sub>h \<Rightarrow> bool" where
  "heap_structured (S\<^sub>h h \<V> s) = (heap_all (bounded_closure h) h \<and>
    list_all (hcontains h) \<V> \<and> list_all (list_all (hcontains h)) (map fst s))"

lemma eval_heap_structured [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> heap_structured \<Sigma>\<^sub>h'"
proof (induction \<Sigma>\<^sub>h \<Sigma>\<^sub>h' rule: eval\<^sub>h.induct)
  case (ev\<^sub>h_apply \<C> p h v\<^sub>2 \<Delta> p' v\<^sub>1 \<V> s)
  hence "hlookup h v\<^sub>2 = Lam\<^sub>h \<Delta> p' \<and> heap_all (bounded_closure h) h \<and> hcontains h v\<^sub>2" by simp
  hence "bounded_closure h v\<^sub>2 (Lam\<^sub>h \<Delta> p')" by (metis hlookup_all)
  with ev\<^sub>h_apply show ?case by simp
next
  case (ev\<^sub>h_jump \<C> p h v\<^sub>2 \<Delta>' p' v\<^sub>1 \<V> \<Delta> s)
  hence "hlookup h v\<^sub>2 = Lam\<^sub>h \<Delta>' p' \<and> heap_all (bounded_closure h) h \<and> hcontains h v\<^sub>2" by simp
  hence "bounded_closure h v\<^sub>2 (Lam\<^sub>h \<Delta>' p')" by (metis hlookup_all)
  with ev\<^sub>h_jump show ?case by simp
qed fastforce+

text \<open>The completeness proof is our most straightforward yet.\<close>

theorem complete\<^sub>h [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> \<C> \<tturnstile> unheap \<Sigma>\<^sub>h \<leadsto>\<^sub>b unheap \<Sigma>\<^sub>h'"
  by (induction \<Sigma>\<^sub>h \<Sigma>\<^sub>h' rule: eval\<^sub>h.induct) simp_all

text \<open>But even correctness isn't too bad.\<close>

lemma unheap_to_empty [simp]: "S\<^sub>b \<V>\<^sub>b [] = unheap \<Sigma>\<^sub>h \<Longrightarrow> \<exists>h \<V>\<^sub>h. 
  \<Sigma>\<^sub>h = S\<^sub>h h \<V>\<^sub>h [] \<and> \<V>\<^sub>b = map (unheap_closure h) \<V>\<^sub>h"
proof (induction \<Sigma>\<^sub>h)
  case (S\<^sub>h h \<V>\<^sub>h s\<^sub>h)
  thus ?case by (induction s\<^sub>h) (simp_all del: unheap_closure.simps)
qed 

lemma unheap_to_cons [simp]: "S\<^sub>b \<V>\<^sub>b ((\<Delta>, p) # s) = unheap \<Sigma>\<^sub>h \<Longrightarrow> \<exists>h \<V>\<^sub>h \<Delta>\<^sub>h s\<^sub>h. 
  \<Sigma>\<^sub>h = S\<^sub>h h \<V>\<^sub>h ((\<Delta>\<^sub>h, p) # s\<^sub>h) \<and> \<V>\<^sub>b = map (unheap_closure h) \<V>\<^sub>h \<and> 
    \<Delta> = map (unheap_closure h) \<Delta>\<^sub>h \<and> s = unheap_stack h s\<^sub>h"
proof (induction \<Sigma>\<^sub>h)
  case (S\<^sub>h h \<V>\<^sub>h s\<^sub>h)
  thus ?case by (induction s\<^sub>h) (auto simp del: unheap_closure.simps)
qed 

lemma unheap_to_lam [simp]: "unheap_closure h v = Lam\<^sub>b \<Delta>\<^sub>b p \<Longrightarrow> hcontains h v \<Longrightarrow> 
  heap_all (bounded_closure h) h \<Longrightarrow> 
    \<exists>\<Delta>\<^sub>h. hlookup h v = Lam\<^sub>h \<Delta>\<^sub>h p \<and> \<Delta>\<^sub>b = map (unheap_closure h) \<Delta>\<^sub>h"
  by (simp split: closure\<^sub>h.splits if_splits)

theorem correct\<^sub>h [simp]: "\<C> \<tturnstile> unheap \<Sigma>\<^sub>h \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>h'. (\<C> \<tturnstile> \<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h') \<and> \<Sigma>\<^sub>b' = unheap \<Sigma>\<^sub>h'"
proof (induction "unheap \<Sigma>\<^sub>h" \<Sigma>\<^sub>b' rule: eval\<^sub>b.induct)
  case (ev\<^sub>b_lookup \<C> p x \<Delta>\<^sub>b v \<V>\<^sub>b s\<^sub>b)
  then obtain h \<V>\<^sub>h \<Delta>\<^sub>h s\<^sub>h where "\<Sigma>\<^sub>h = S\<^sub>h h \<V>\<^sub>h ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<and> \<V>\<^sub>b = map (unheap_closure h) \<V>\<^sub>h \<and> 
    \<Delta>\<^sub>b = map (unheap_closure h) \<Delta>\<^sub>h \<and> s\<^sub>b = unheap_stack h s\<^sub>h" by fastforce
  moreover with ev\<^sub>b_lookup obtain vv where "lookup \<Delta>\<^sub>h x = Some vv \<and> v = unheap_closure h vv" 
    by fastforce
  moreover with ev\<^sub>b_lookup have "\<C> \<tturnstile> S\<^sub>h h \<V>\<^sub>h ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<leadsto>\<^sub>h S\<^sub>h h (vv # \<V>\<^sub>h) ((\<Delta>\<^sub>h, p) # s\<^sub>h)" 
    by simp
  ultimately show ?case by fastforce
next
  case (ev\<^sub>b_pushcon \<C> p n \<V>\<^sub>b \<Delta>\<^sub>b s\<^sub>b)
  moreover then obtain h \<V>\<^sub>h \<Delta>\<^sub>h s\<^sub>h where "\<Sigma>\<^sub>h = S\<^sub>h h \<V>\<^sub>h ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<and> 
    \<V>\<^sub>b = map (unheap_closure h) \<V>\<^sub>h \<and> \<Delta>\<^sub>b = map (unheap_closure h) \<Delta>\<^sub>h \<and> s\<^sub>b = unheap_stack h s\<^sub>h" 
      by fastforce
  moreover obtain h' v where "halloc h (Const\<^sub>h n) = (h', v)" by fastforce
  moreover with ev\<^sub>b_pushcon have "\<C> \<tturnstile> S\<^sub>h h \<V>\<^sub>h ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<leadsto>\<^sub>h S\<^sub>h h' (v # \<V>\<^sub>h) ((\<Delta>\<^sub>h, p) # s\<^sub>h)" 
    by simp
  ultimately show ?case by fastforce
next
  case (ev\<^sub>b_pushlam \<C> p p' \<V>\<^sub>b \<Delta>\<^sub>b s\<^sub>b)
  moreover then obtain h \<V>\<^sub>h \<Delta>\<^sub>h s\<^sub>h where S: "\<Sigma>\<^sub>h = S\<^sub>h h \<V>\<^sub>h ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<and> 
    \<V>\<^sub>b = map (unheap_closure h) \<V>\<^sub>h \<and> \<Delta>\<^sub>b = map (unheap_closure h) \<Delta>\<^sub>h \<and> s\<^sub>b = unheap_stack h s\<^sub>h" 
      by fastforce
  moreover obtain h' v where "halloc h (Lam\<^sub>h \<Delta>\<^sub>h p') = (h', v)" by fastforce
  moreover with ev\<^sub>b_pushlam S have "\<C> \<tturnstile> S\<^sub>h h \<V>\<^sub>h ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<leadsto>\<^sub>h S\<^sub>h h' (v # \<V>\<^sub>h) ((\<Delta>\<^sub>h, p) # s\<^sub>h)" 
    by simp
  ultimately show ?case by fastforce
next
  case (ev\<^sub>b_apply \<C> p v\<^sub>b \<Delta>\<^sub>b' p' \<V>\<^sub>b \<Delta>\<^sub>b s\<^sub>b)
  then obtain h \<V>\<^sub>h' \<Delta>\<^sub>h s\<^sub>h where S: "\<Sigma>\<^sub>h = S\<^sub>h h \<V>\<^sub>h' ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<and> 
    v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b = map (unheap_closure h) \<V>\<^sub>h' \<and> \<Delta>\<^sub>b = map (unheap_closure h) \<Delta>\<^sub>h \<and> 
      s\<^sub>b = unheap_stack h s\<^sub>h" by fastforce
  moreover then obtain v\<^sub>h\<^sub>1 v\<^sub>h\<^sub>2 \<V>\<^sub>h where "\<V>\<^sub>h' = v\<^sub>h\<^sub>1 # v\<^sub>h\<^sub>2 # \<V>\<^sub>h \<and> v\<^sub>b = unheap_closure h v\<^sub>h\<^sub>1 \<and> 
    Lam\<^sub>b \<Delta>\<^sub>b' p' = unheap_closure h v\<^sub>h\<^sub>2 \<and> \<V>\<^sub>b = map (unheap_closure h) \<V>\<^sub>h" by fastforce
  moreover with ev\<^sub>b_apply S obtain \<Delta>h' where H: "hlookup h v\<^sub>h\<^sub>2 = Lam\<^sub>h \<Delta>h' p' \<and> 
    \<Delta>\<^sub>b' = map (unheap_closure h) \<Delta>h'" by fastforce
  moreover with ev\<^sub>b_apply have "\<C> \<tturnstile> S\<^sub>h h (v\<^sub>h\<^sub>1 # v\<^sub>h\<^sub>2 # \<V>\<^sub>h) ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<leadsto>\<^sub>h 
    S\<^sub>h h \<V>\<^sub>h ((v\<^sub>h\<^sub>1 # \<Delta>h', p') # (\<Delta>\<^sub>h, p) # s\<^sub>h)" by simp
  ultimately show ?case by fastforce
next
  case (ev\<^sub>b_pushenv \<C> p v\<^sub>b \<V>\<^sub>b \<Delta>\<^sub>b s\<^sub>b)
  then obtain h \<V>\<^sub>h' \<Delta>\<^sub>h s\<^sub>h where "\<Sigma>\<^sub>h = S\<^sub>h h \<V>\<^sub>h' ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<and> 
    v\<^sub>b # \<V>\<^sub>b = map (unheap_closure h) \<V>\<^sub>h' \<and> \<Delta>\<^sub>b = map (unheap_closure h) \<Delta>\<^sub>h \<and> s\<^sub>b = unheap_stack h s\<^sub>h" 
      by fastforce
  moreover then obtain v\<^sub>h \<V>\<^sub>h where "\<V>\<^sub>h' = v\<^sub>h # \<V>\<^sub>h \<and> v\<^sub>b = unheap_closure h v\<^sub>h \<and> 
    \<V>\<^sub>b = map (unheap_closure h) \<V>\<^sub>h" by fastforce
  moreover from ev\<^sub>b_pushenv have "\<C> \<tturnstile> S\<^sub>h h (v\<^sub>h # \<V>\<^sub>h) ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<leadsto>\<^sub>h 
    S\<^sub>h h \<V>\<^sub>h ((v\<^sub>h # \<Delta>\<^sub>h, p) # s\<^sub>h)" by simp
  ultimately show ?case by fastforce
next
  case (ev\<^sub>b_return \<C> p \<V>\<^sub>b \<Delta>\<^sub>b s\<^sub>b)
  then obtain h \<V>\<^sub>h \<Delta>\<^sub>h s\<^sub>h where "\<Sigma>\<^sub>h = S\<^sub>h h \<V>\<^sub>h ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<and> \<V>\<^sub>b = map (unheap_closure h) \<V>\<^sub>h \<and> 
    \<Delta>\<^sub>b = map (unheap_closure h) \<Delta>\<^sub>h \<and> s\<^sub>b = unheap_stack h s\<^sub>h" by fastforce
  moreover with ev\<^sub>b_return have "\<C> \<tturnstile> S\<^sub>h h \<V>\<^sub>h ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<leadsto>\<^sub>h S\<^sub>h h \<V>\<^sub>h s\<^sub>h" by simp
  ultimately show ?case by fastforce
next
  case (ev\<^sub>b_jump \<C> p v\<^sub>b \<Delta>\<^sub>b' p' \<V>\<^sub>b \<Delta>\<^sub>b s\<^sub>b)
  then obtain h \<V>\<^sub>h' \<Delta>\<^sub>h s\<^sub>h where S: "\<Sigma>\<^sub>h = S\<^sub>h h \<V>\<^sub>h' ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<and> 
    v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b = map (unheap_closure h) \<V>\<^sub>h' \<and> \<Delta>\<^sub>b = map (unheap_closure h) \<Delta>\<^sub>h \<and> 
      s\<^sub>b = unheap_stack h s\<^sub>h" by fastforce
  moreover from S obtain v\<^sub>h\<^sub>1 v\<^sub>h\<^sub>2 \<V>\<^sub>h where "\<V>\<^sub>h' = v\<^sub>h\<^sub>1 # v\<^sub>h\<^sub>2 # \<V>\<^sub>h \<and> v\<^sub>b = unheap_closure h v\<^sub>h\<^sub>1 \<and> 
    Lam\<^sub>b \<Delta>\<^sub>b' p' = unheap_closure h v\<^sub>h\<^sub>2 \<and> \<V>\<^sub>b = map (unheap_closure h) \<V>\<^sub>h" by fastforce
  moreover with ev\<^sub>b_jump S obtain \<Delta>h' where "hlookup h v\<^sub>h\<^sub>2 = Lam\<^sub>h \<Delta>h' p' \<and> 
    \<Delta>\<^sub>b' = map (unheap_closure h) \<Delta>h'" by fastforce
  moreover with ev\<^sub>b_jump S have "\<C> \<tturnstile> S\<^sub>h h (v\<^sub>h\<^sub>1 # v\<^sub>h\<^sub>2 # \<V>\<^sub>h) ((\<Delta>\<^sub>h, Suc p) # s\<^sub>h) \<leadsto>\<^sub>h 
    S\<^sub>h h \<V>\<^sub>h ((v\<^sub>h\<^sub>1 # \<Delta>h', p') # s\<^sub>h)" by simp
  ultimately show ?case by fastforce
qed

lemma iter_correct\<^sub>h [simp]: "iter (\<tturnstile> \<C> \<leadsto>\<^sub>b) (unheap \<Sigma>\<^sub>h) \<Sigma>\<^sub>b' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>h'. iter (\<tturnstile> \<C> \<leadsto>\<^sub>h) \<Sigma>\<^sub>h \<Sigma>\<^sub>h' \<and> \<Sigma>\<^sub>b' = unheap \<Sigma>\<^sub>h'"
proof (induction "unheap \<Sigma>\<^sub>h" \<Sigma>\<^sub>b' arbitrary: \<Sigma>\<^sub>h rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>b' \<Sigma>\<^sub>b'')
  moreover then obtain \<Sigma>\<^sub>h' where S: "(\<C> \<tturnstile> \<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h') \<and> \<Sigma>\<^sub>b' = unheap \<Sigma>\<^sub>h'" by fastforce
  moreover with iter_step have "heap_structured \<Sigma>\<^sub>h'" by fastforce
  ultimately obtain \<Sigma>\<^sub>h'' where "iter (\<tturnstile> \<C> \<leadsto>\<^sub>h) \<Sigma>\<^sub>h' \<Sigma>\<^sub>h'' \<and> \<Sigma>\<^sub>b'' = unheap \<Sigma>\<^sub>h''" by blast
  with S have "iter (\<tturnstile> \<C> \<leadsto>\<^sub>h) \<Sigma>\<^sub>h \<Sigma>\<^sub>h'' \<and> \<Sigma>\<^sub>b'' = unheap \<Sigma>\<^sub>h''" by fastforce
  thus ?case by fastforce
qed force+

end