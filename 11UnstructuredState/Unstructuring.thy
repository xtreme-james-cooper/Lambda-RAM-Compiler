theory Unstructuring
  imports UnstructuredState "../10FlatMemory/FlatMemory"
begin

subsection \<open>State Unstructuring\<close>

text \<open>The conversion to an unstructured state is almost a complete isomorphism: for every 
(well-formed) flat-memory state, there exists one and only one (well-formed) unstructured state. We 
cannot quite make a pair of inverse functions, however, because the well-formedness condition isn't 
preserved by evaluation. Specifically, the memory map associated with a stack must have some 
specific value (probably \<open>undefined\<close>) for indexes above its stack pointer; but we don't wipe values 
when the stack retreats, we simply leave them behind as garbage. So we can only go one way, from 
unstructured states to flat ones:\<close>

primrec listify_heap :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list" where
  "listify_heap h 0 = []"
| "listify_heap h (Suc x) = h x # listify_heap h x"

lemma listify_to_empty [dest]: "listify_heap h x = [] \<Longrightarrow> x = 0"
  by (induction x) simp_all

lemma listify_to_cons [dest]: "listify_heap h x = a # as \<Longrightarrow> 
    \<exists>y. x = Suc y \<and> h y = a \<and> listify_heap h y = as"
  by (induction x) simp_all

lemma fun_upd_listify [simp]: "b\<^sub>h \<le> x \<Longrightarrow> listify_heap (h(x := v)) b\<^sub>h = listify_heap h b\<^sub>h"
  by (induction b\<^sub>h) simp_all

lemma fun_upd_listify_suc [simp]: "b\<^sub>h \<le> x \<Longrightarrow> 
    listify_heap (h(Suc x := v) \<circ> Suc) b\<^sub>h = listify_heap (h \<circ> Suc) b\<^sub>h"
  by (induction b\<^sub>h) auto

primrec restructure :: "state\<^sub>r \<Rightarrow> state\<^sub>f" where
  "restructure (S\<^sub>r h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> b\<^sub>\<V> s b\<^sub>s p\<^sub>\<C>) = 
    S\<^sub>f (H h b\<^sub>h) (H \<Delta> b\<^sub>\<Delta>) (listify_heap \<V> b\<^sub>\<V>) (case b\<^sub>s of 
      0 \<Rightarrow> []  
    | Suc b\<^sub>s' \<Rightarrow> p\<^sub>\<C> # listify_heap (s \<circ> Suc) b\<^sub>s')"

lemma flat_unstr_lookup [simp]: "flat_lookup (H h b\<^sub>h) p x = unstr_lookup h p x"
  by (induction h p x rule: unstr_lookup.induct) simp_all

text \<open>We also need a well-formedness predicate, to make sure that the stack (the only complicated 
pert of the conversion) is properly set up.\<close>

primrec restructurable :: "state\<^sub>r \<Rightarrow> bool" where
  "restructurable (S\<^sub>r h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> b\<^sub>\<V> s b\<^sub>s p\<^sub>\<C>) = (even b\<^sub>s \<and> s 0 = 0 \<and> (b\<^sub>s = 0 \<longrightarrow> p\<^sub>\<C> = 0))"

lemma restructurable_persists [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>r \<leadsto>\<^sub>r \<Sigma>\<^sub>r' \<Longrightarrow> restructurable \<Sigma>\<^sub>r \<Longrightarrow> restructurable \<Sigma>\<^sub>r'"
  by (induction \<Sigma>\<^sub>r \<Sigma>\<^sub>r' rule: eval\<^sub>r.induct) (auto simp add: odd_pos)

lemma restructurable_persists_iter [simp]: "iter (\<tturnstile> \<C> \<leadsto>\<^sub>r) \<Sigma>\<^sub>r \<Sigma>\<^sub>r' \<Longrightarrow> restructurable \<Sigma>\<^sub>r \<Longrightarrow> 
    restructurable \<Sigma>\<^sub>r'"
  by (induction \<Sigma>\<^sub>r \<Sigma>\<^sub>r' rule: iter.induct) simp_all

text \<open>Completeness is a simple induction, now.\<close>

theorem complete\<^sub>r [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>r \<leadsto>\<^sub>r \<Sigma>\<^sub>r' \<Longrightarrow> restructurable \<Sigma>\<^sub>r \<Longrightarrow> 
  \<C> \<tturnstile> restructure \<Sigma>\<^sub>r \<leadsto>\<^sub>f restructure \<Sigma>\<^sub>r'"
proof (induction \<Sigma>\<^sub>r \<Sigma>\<^sub>r' rule: eval\<^sub>r.induct)
  case (ev\<^sub>r_lookup \<C> p\<^sub>\<C> x z w \<Delta> s b\<^sub>s y h b\<^sub>h b\<^sub>\<Delta> \<V> b\<^sub>\<V>)
  thus ?case by (cases b\<^sub>s) (auto split: nat.splits)
next
  case (ev\<^sub>r_pushcon \<C> p\<^sub>\<C> n h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> b\<^sub>\<V> s b\<^sub>s)
  thus ?case by (cases b\<^sub>s) (auto split: nat.splits)
next
  case (ev\<^sub>r_pushlam \<C> p\<^sub>\<C> p\<^sub>\<C>' n h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> b\<^sub>\<V> s b\<^sub>s)
  thus ?case by (cases b\<^sub>s) (auto split: nat.splits)
next
  case (ev\<^sub>r_apply \<C> p\<^sub>\<C> h \<V> b\<^sub>\<V> p\<^sub>\<Delta> p\<^sub>\<C>' b\<^sub>h \<Delta> b\<^sub>\<Delta> s b\<^sub>s)
  moreover hence "hlookup (H h b\<^sub>h) (\<V> b\<^sub>\<V>) = (PEnv, p\<^sub>\<Delta>)" by simp
  moreover from ev\<^sub>r_apply have "hlookup (H h b\<^sub>h) (Suc (\<V> b\<^sub>\<V>)) = (PCode, p\<^sub>\<C>')" by simp
  moreover have "halloc_list (H \<Delta> b\<^sub>\<Delta>) [\<V> (Suc b\<^sub>\<V>), p\<^sub>\<Delta>] = 
    (H (\<Delta>(b\<^sub>\<Delta> := \<V> (Suc b\<^sub>\<V>), Suc b\<^sub>\<Delta> := p\<^sub>\<Delta>)) (Suc (Suc b\<^sub>\<Delta>)), b\<^sub>\<Delta>)" by simp
  ultimately have "\<And>n. \<C> \<tturnstile> S\<^sub>f (H h b\<^sub>h) (H \<Delta> b\<^sub>\<Delta>) (\<V> (Suc b\<^sub>\<V>) # \<V> b\<^sub>\<V> # listify_heap \<V> b\<^sub>\<V>) 
      (Suc p\<^sub>\<C> # s (Suc n) # listify_heap (s \<circ> Suc) n) \<leadsto>\<^sub>f 
    S\<^sub>f (H h b\<^sub>h) (H (\<Delta>(b\<^sub>\<Delta> := \<V> (Suc b\<^sub>\<V>), Suc b\<^sub>\<Delta> := p\<^sub>\<Delta>)) (Suc (Suc b\<^sub>\<Delta>))) 
      (listify_heap \<V> b\<^sub>\<V>) (p\<^sub>\<C>' # Suc (Suc b\<^sub>\<Delta>) # p\<^sub>\<C> # s (Suc n) # listify_heap (s \<circ> Suc) n)"
    by (metis ev\<^sub>f_apply)
  with ev\<^sub>r_apply show ?case by (cases b\<^sub>s) (auto split: nat.splits)
next
  case (ev\<^sub>r_pushenv \<C> p\<^sub>\<C> h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> b\<^sub>\<V> s b\<^sub>s)
  hence "lookup \<C> p\<^sub>\<C> = Some PushEnv\<^sub>b" by simp
  moreover have "\<And>n. halloc_list (H \<Delta> b\<^sub>\<Delta>) [\<V> b\<^sub>\<V>, s (Suc n)] = 
    (H (\<Delta>(b\<^sub>\<Delta> := \<V> b\<^sub>\<V>, Suc b\<^sub>\<Delta> := s (Suc n))) (Suc (Suc b\<^sub>\<Delta>)), b\<^sub>\<Delta>)" by simp
  ultimately have "\<And>n. \<C> \<tturnstile> S\<^sub>f (H h b\<^sub>h) (H \<Delta> b\<^sub>\<Delta>) (\<V> b\<^sub>\<V> # listify_heap \<V> b\<^sub>\<V>) 
      (Suc p\<^sub>\<C> # s (Suc n) # listify_heap (s \<circ> Suc) n) \<leadsto>\<^sub>f 
    S\<^sub>f (H h b\<^sub>h) (H (\<Delta>(b\<^sub>\<Delta> := \<V> b\<^sub>\<V>, Suc b\<^sub>\<Delta> := s (Suc n))) (Suc (Suc b\<^sub>\<Delta>))) 
      (listify_heap \<V> b\<^sub>\<V>) (p\<^sub>\<C> # Suc (Suc b\<^sub>\<Delta>) # listify_heap (s \<circ> Suc) n)" by (metis ev\<^sub>f_pushenv) 
  with ev\<^sub>r_pushenv show ?case by (cases b\<^sub>s) (auto split: nat.splits)
next
  case (ev\<^sub>r_return \<C> p\<^sub>\<C> h b\<^sub>h \<Delta> b\<^sub>\<Delta> \<V> b\<^sub>\<V> s b\<^sub>s)
  thus ?case by (cases b\<^sub>s) (auto split: nat.splits)
next
  case (ev\<^sub>r_jump \<C> p\<^sub>\<C> h \<V> b\<^sub>\<V> p\<^sub>\<Delta> p\<^sub>\<C>' b\<^sub>h \<Delta> b\<^sub>\<Delta> s b\<^sub>s)
  moreover hence "hlookup (H h b\<^sub>h) (\<V> b\<^sub>\<V>) = (PEnv, p\<^sub>\<Delta>)" by simp
  moreover from ev\<^sub>r_jump have "hlookup (H h b\<^sub>h) (Suc (\<V> b\<^sub>\<V>)) = (PCode, p\<^sub>\<C>')" by simp
  moreover have "halloc_list (H \<Delta> b\<^sub>\<Delta>) [\<V> (Suc b\<^sub>\<V>), p\<^sub>\<Delta>] = 
    (H (\<Delta>(b\<^sub>\<Delta> := \<V> (Suc b\<^sub>\<V>), Suc b\<^sub>\<Delta> := p\<^sub>\<Delta>)) (Suc (Suc b\<^sub>\<Delta>)), b\<^sub>\<Delta>)" by simp
  ultimately have "\<And>n. \<C> \<tturnstile> S\<^sub>f (H h b\<^sub>h) (H \<Delta> b\<^sub>\<Delta>) (\<V> (Suc b\<^sub>\<V>) # \<V> b\<^sub>\<V> # listify_heap \<V> b\<^sub>\<V>) 
      (Suc p\<^sub>\<C> # s (Suc n) # listify_heap (s \<circ> Suc) n) \<leadsto>\<^sub>f 
    S\<^sub>f (H h b\<^sub>h) (H (\<Delta>(b\<^sub>\<Delta> := \<V> (Suc b\<^sub>\<V>), Suc b\<^sub>\<Delta> := p\<^sub>\<Delta>)) (Suc (Suc b\<^sub>\<Delta>))) 
      (listify_heap \<V> b\<^sub>\<V>) (p\<^sub>\<C>' # Suc (Suc b\<^sub>\<Delta>) # listify_heap (s \<circ> Suc) n)"
    by (metis ev\<^sub>f_jump)
  with ev\<^sub>r_jump show ?case by (cases b\<^sub>s) (auto split: nat.splits)
qed

text \<open>However, the simplicity of our conversion means that correctness is also mostly 
straightforward.\<close>

lemma restructure_to_state [dest]: "S\<^sub>f h\<^sub>f \<Delta>\<^sub>f \<V>\<^sub>f (p\<^sub>\<C> # p\<^sub>\<Delta> # s\<^sub>f) = restructure \<Sigma>\<^sub>r \<Longrightarrow> 
  \<exists>h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r b\<^sub>s. \<Sigma>\<^sub>r = S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r (Suc (Suc b\<^sub>s)) p\<^sub>\<C> \<and> h\<^sub>f = H h\<^sub>r b\<^sub>h \<and> 
    \<Delta>\<^sub>f = H \<Delta>\<^sub>r b\<^sub>\<Delta> \<and> \<V>\<^sub>f = listify_heap \<V>\<^sub>r b\<^sub>\<V> \<and> p\<^sub>\<Delta> = s\<^sub>r (Suc b\<^sub>s) \<and> s\<^sub>f = listify_heap (s\<^sub>r \<circ> Suc) b\<^sub>s"
proof (induction \<Sigma>\<^sub>r)
  case (S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r b\<^sub>s p\<^sub>\<C>)
  thus ?case 
  proof (induction b\<^sub>s)
    case (Suc b\<^sub>s)
    thus ?case by (cases b\<^sub>s) (simp_all split: nat.splits, meson comp_apply)
  qed (simp_all split: nat.splits)
qed

lemma restructure_to_final_state [dest]: "S\<^sub>f h\<^sub>f \<Delta>\<^sub>f \<V>\<^sub>f [] = restructure \<Sigma>\<^sub>r \<Longrightarrow> restructurable \<Sigma>\<^sub>r \<Longrightarrow> 
  \<exists>h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r. \<Sigma>\<^sub>r = S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r 0 0 \<and> h\<^sub>f = H h\<^sub>r b\<^sub>h \<and> \<Delta>\<^sub>f = H \<Delta>\<^sub>r b\<^sub>\<Delta> \<and> 
    \<V>\<^sub>f = listify_heap \<V>\<^sub>r b\<^sub>\<V>"
  by (induction \<Sigma>\<^sub>r) (simp split: nat.splits)

theorem correct\<^sub>r [simp]: "\<C> \<tturnstile> restructure \<Sigma>\<^sub>r \<leadsto>\<^sub>f \<Sigma>\<^sub>f' \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>r'. (\<C> \<tturnstile> \<Sigma>\<^sub>r \<leadsto>\<^sub>r \<Sigma>\<^sub>r') \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>r'"
proof (induction "restructure \<Sigma>\<^sub>r" \<Sigma>\<^sub>f' rule: eval\<^sub>f.induct)
  case (ev\<^sub>f_lookup \<C> p\<^sub>\<C> x y z \<Delta>\<^sub>f p\<^sub>\<Delta> v h\<^sub>f \<V>\<^sub>f s\<^sub>f)
  then obtain h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r b\<^sub>s where S: "h\<^sub>f = H h\<^sub>r b\<^sub>h \<and> \<Delta>\<^sub>f = H \<Delta>\<^sub>r b\<^sub>\<Delta> \<and> 
    \<V>\<^sub>f = listify_heap \<V>\<^sub>r b\<^sub>\<V> \<and> p\<^sub>\<Delta> = s\<^sub>r (Suc b\<^sub>s) \<and> s\<^sub>f = listify_heap (s\<^sub>r \<circ> Suc) b\<^sub>s \<and> 
      \<Sigma>\<^sub>r = S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>)" by fastforce
  moreover hence "S\<^sub>f h\<^sub>f \<Delta>\<^sub>f (v # \<V>\<^sub>f) (p\<^sub>\<C> # p\<^sub>\<Delta> # s\<^sub>f) = 
    restructure (S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> (\<V>\<^sub>r(b\<^sub>\<V> := v)) (Suc b\<^sub>\<V>) s\<^sub>r (Suc (Suc b\<^sub>s)) p\<^sub>\<C>)" by simp
  moreover from ev\<^sub>f_lookup S have "\<C> \<tturnstile> S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r 
    S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> (\<V>\<^sub>r(b\<^sub>\<V> := v)) (Suc b\<^sub>\<V>) s\<^sub>r (Suc (Suc b\<^sub>s)) p\<^sub>\<C>" by simp
  ultimately show ?case by blast
next
  case (ev\<^sub>f_pushcon \<C> p\<^sub>\<C> k h\<^sub>f h\<^sub>f' v \<Delta>\<^sub>f \<V>\<^sub>f p\<^sub>\<Delta> s\<^sub>f)
  then obtain h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r b\<^sub>s where S: "h\<^sub>f = H h\<^sub>r b\<^sub>h \<and> \<Delta>\<^sub>f = H \<Delta>\<^sub>r b\<^sub>\<Delta> \<and> 
    \<V>\<^sub>f = listify_heap \<V>\<^sub>r b\<^sub>\<V> \<and> p\<^sub>\<Delta> = s\<^sub>r (Suc b\<^sub>s) \<and> s\<^sub>f = listify_heap (s\<^sub>r \<circ> Suc) b\<^sub>s \<and> 
      \<Sigma>\<^sub>r = S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>)" by fastforce
  with ev\<^sub>f_pushcon have "v = b\<^sub>h \<and> 
    h\<^sub>f' = H (h\<^sub>r(b\<^sub>h := (PConst, k), Suc b\<^sub>h := (PConst, 0))) (Suc (Suc b\<^sub>h))" by fastforce
  with S have X: "S\<^sub>f h\<^sub>f' \<Delta>\<^sub>f (v # \<V>\<^sub>f) (p\<^sub>\<C> # p\<^sub>\<Delta> # s\<^sub>f) = 
    restructure (S\<^sub>r (h\<^sub>r(b\<^sub>h := (PConst, k), Suc b\<^sub>h := (PConst, 0))) 
      (2 + b\<^sub>h) \<Delta>\<^sub>r b\<^sub>\<Delta> (\<V>\<^sub>r(b\<^sub>\<V> := b\<^sub>h)) (Suc b\<^sub>\<V>) s\<^sub>r (Suc (Suc b\<^sub>s)) p\<^sub>\<C>)" by simp
  from ev\<^sub>f_pushcon have "\<C> \<tturnstile> S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r 
    S\<^sub>r (h\<^sub>r(b\<^sub>h := (PConst, k), Suc b\<^sub>h := (PConst, 0))) (2 + b\<^sub>h) \<Delta>\<^sub>r b\<^sub>\<Delta> 
      (\<V>\<^sub>r(b\<^sub>\<V> := b\<^sub>h)) (Suc b\<^sub>\<V>) s\<^sub>r (Suc (Suc b\<^sub>s)) p\<^sub>\<C>" by (metis ev\<^sub>r_pushcon)
  with S X show ?case by blast
next
  case (ev\<^sub>f_pushlam \<C> p\<^sub>\<C> p\<^sub>\<C>' n h\<^sub>f p\<^sub>\<Delta> h\<^sub>f' v \<Delta>\<^sub>f \<V>\<^sub>f s\<^sub>f)
  then obtain h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r b\<^sub>s where S: "h\<^sub>f = H h\<^sub>r b\<^sub>h \<and> \<Delta>\<^sub>f = H \<Delta>\<^sub>r b\<^sub>\<Delta> \<and> 
    \<V>\<^sub>f = listify_heap \<V>\<^sub>r b\<^sub>\<V> \<and> p\<^sub>\<Delta> = s\<^sub>r (Suc b\<^sub>s) \<and> s\<^sub>f = listify_heap (s\<^sub>r \<circ> Suc) b\<^sub>s \<and> 
      \<Sigma>\<^sub>r = S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>)" by fastforce
  with ev\<^sub>f_pushlam have "v = b\<^sub>h \<and> 
    h\<^sub>f' = H (h\<^sub>r(b\<^sub>h := (PEnv, s\<^sub>r (Suc b\<^sub>s)), Suc b\<^sub>h := (PCode, p\<^sub>\<C>'))) (Suc (Suc b\<^sub>h))" by fastforce
  with S have X: "S\<^sub>f h\<^sub>f' \<Delta>\<^sub>f (v # \<V>\<^sub>f) (p\<^sub>\<C> # p\<^sub>\<Delta> # s\<^sub>f) = 
    restructure (S\<^sub>r (h\<^sub>r(b\<^sub>h := (PEnv, s\<^sub>r (Suc b\<^sub>s)), Suc b\<^sub>h := (PCode, p\<^sub>\<C>'))) (2 + b\<^sub>h) \<Delta>\<^sub>r b\<^sub>\<Delta>
      (\<V>\<^sub>r(b\<^sub>\<V> := b\<^sub>h)) (Suc b\<^sub>\<V>) s\<^sub>r (Suc (Suc b\<^sub>s)) p\<^sub>\<C>)" 
        by simp
  from ev\<^sub>f_pushlam S have "\<C> \<tturnstile> S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r 
    S\<^sub>r (h\<^sub>r(b\<^sub>h := (PEnv, s\<^sub>r (Suc b\<^sub>s)), Suc b\<^sub>h := (PCode, p\<^sub>\<C>'))) (2 + b\<^sub>h) 
      \<Delta>\<^sub>r b\<^sub>\<Delta> (\<V>\<^sub>r(b\<^sub>\<V> := b\<^sub>h)) (Suc b\<^sub>\<V>) s\<^sub>r (Suc (Suc b\<^sub>s)) p\<^sub>\<C>" by (metis ev\<^sub>r_pushlam)
  with S X show ?case by blast
next
  case (ev\<^sub>f_apply \<C> p\<^sub>\<C> h\<^sub>f v\<^sub>2 p\<^sub>\<Delta>' p\<^sub>\<C>' \<Delta>\<^sub>f v\<^sub>1 \<Delta>\<^sub>f' p2 \<V>\<^sub>f p\<^sub>\<Delta> s\<^sub>f)
  then obtain h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r b\<^sub>s where S: "h\<^sub>f = H h\<^sub>r b\<^sub>h \<and> \<Delta>\<^sub>f = H \<Delta>\<^sub>r b\<^sub>\<Delta> \<and> p\<^sub>\<Delta> = s\<^sub>r (Suc b\<^sub>s) \<and> 
    s\<^sub>f = listify_heap (s\<^sub>r \<circ> Suc) b\<^sub>s \<and> listify_heap \<V>\<^sub>r b\<^sub>\<V> = v\<^sub>1 # v\<^sub>2 # \<V>\<^sub>f \<and> 
      \<Sigma>\<^sub>r = S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>)" by fastforce
  then obtain vp' where V: "b\<^sub>\<V> = Suc (Suc vp') \<and> v\<^sub>1 = \<V>\<^sub>r (Suc vp') \<and> v\<^sub>2 = \<V>\<^sub>r vp' \<and> 
    \<V>\<^sub>f = listify_heap \<V>\<^sub>r vp'" by fastforce
  from ev\<^sub>f_apply S V have H1: "h\<^sub>r (\<V>\<^sub>r vp') = (PEnv, p\<^sub>\<Delta>')" by simp
  from ev\<^sub>f_apply S V have H2: "h\<^sub>r (Suc (\<V>\<^sub>r vp')) = (PCode, p\<^sub>\<C>')" by simp
  from ev\<^sub>f_apply S V have "p2 = b\<^sub>\<Delta> \<and> \<Delta>\<^sub>f' = H (\<Delta>\<^sub>r(b\<^sub>\<Delta> := v\<^sub>1, Suc b\<^sub>\<Delta> := p\<^sub>\<Delta>')) (Suc (Suc b\<^sub>\<Delta>))" by auto
  with S V have X: "S\<^sub>f h\<^sub>f \<Delta>\<^sub>f' \<V>\<^sub>f (p\<^sub>\<C>' # Suc (Suc b\<^sub>\<Delta>) # p\<^sub>\<C> # p\<^sub>\<Delta> # s\<^sub>f) = 
    restructure (S\<^sub>r h\<^sub>r b\<^sub>h (\<Delta>\<^sub>r(b\<^sub>\<Delta> := v\<^sub>1, Suc b\<^sub>\<Delta> := p\<^sub>\<Delta>')) (2 + b\<^sub>\<Delta>) \<V>\<^sub>r vp' 
      (s\<^sub>r(Suc (Suc b\<^sub>s) := p\<^sub>\<C>, Suc (Suc (Suc b\<^sub>s)) := Suc (Suc b\<^sub>\<Delta>))) (2 + Suc (Suc b\<^sub>s)) p\<^sub>\<C>')" by simp
  from ev\<^sub>f_apply V H1 H2 have "
    \<C> \<tturnstile> S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r (Suc (Suc vp')) s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r 
      S\<^sub>r h\<^sub>r b\<^sub>h (\<Delta>\<^sub>r(b\<^sub>\<Delta> := v\<^sub>1, Suc b\<^sub>\<Delta> := p\<^sub>\<Delta>')) (2 + b\<^sub>\<Delta>) \<V>\<^sub>r vp'
        (s\<^sub>r(Suc (Suc b\<^sub>s) := p\<^sub>\<C>, Suc (Suc (Suc b\<^sub>s)) := Suc (Suc b\<^sub>\<Delta>))) (2 + Suc (Suc b\<^sub>s)) p\<^sub>\<C>'"
    by (metis ev\<^sub>r_apply)
  with ev\<^sub>f_apply S X V show ?case by auto
next
  case (ev\<^sub>f_pushenv \<C> p\<^sub>\<C> \<Delta>\<^sub>f v p\<^sub>\<Delta> \<Delta>' p\<^sub>\<Delta>' h\<^sub>f \<V>\<^sub>f s\<^sub>f)
  moreover then obtain h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V>' s\<^sub>r b\<^sub>s where "
    \<Sigma>\<^sub>r = S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V>' s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>) \<and> h\<^sub>f = H h\<^sub>r b\<^sub>h \<and> \<Delta>\<^sub>f = H \<Delta>\<^sub>r b\<^sub>\<Delta> \<and> 
      listify_heap \<V>\<^sub>r b\<^sub>\<V>' = v # \<V>\<^sub>f \<and> p\<^sub>\<Delta> = s\<^sub>r (Suc b\<^sub>s) \<and> s\<^sub>f = listify_heap (s\<^sub>r \<circ> Suc) b\<^sub>s" by fastforce
  moreover then obtain b\<^sub>\<V> where "b\<^sub>\<V>' = Suc b\<^sub>\<V> \<and> \<V>\<^sub>r b\<^sub>\<V> = v \<and> listify_heap \<V>\<^sub>r b\<^sub>\<V> = \<V>\<^sub>f" by fastforce
  moreover from ev\<^sub>f_pushenv have "\<C> \<tturnstile> S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r (Suc b\<^sub>\<V>) s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r 
    S\<^sub>r h\<^sub>r b\<^sub>h (\<Delta>\<^sub>r(b\<^sub>\<Delta> := \<V>\<^sub>r b\<^sub>\<V>, Suc b\<^sub>\<Delta> := s\<^sub>r (Suc b\<^sub>s))) (Suc (Suc b\<^sub>\<Delta>)) \<V>\<^sub>r b\<^sub>\<V> 
      (s\<^sub>r(Suc b\<^sub>s := Suc (Suc b\<^sub>\<Delta>))) (Suc (Suc b\<^sub>s)) p\<^sub>\<C>" by simp
  ultimately show ?case by auto
next
  case (ev\<^sub>f_return \<C> p\<^sub>\<C> h\<^sub>f \<Delta>\<^sub>f \<V>\<^sub>f p\<^sub>\<Delta> s\<^sub>f)
  then obtain h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r b\<^sub>s where S: "h\<^sub>f = H h\<^sub>r b\<^sub>h \<and> \<Delta>\<^sub>f = H \<Delta>\<^sub>r b\<^sub>\<Delta> \<and> 
    \<V>\<^sub>f = listify_heap \<V>\<^sub>r b\<^sub>\<V> \<and> p\<^sub>\<Delta> = s\<^sub>r (Suc b\<^sub>s) \<and> s\<^sub>f = listify_heap (s\<^sub>r \<circ> Suc) b\<^sub>s \<and> 
      \<Sigma>\<^sub>r = S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>)" by fastforce
  moreover with ev\<^sub>f_return have "S\<^sub>f h\<^sub>f \<Delta>\<^sub>f \<V>\<^sub>f s\<^sub>f = 
    restructure (S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r b\<^sub>s (s\<^sub>r b\<^sub>s))" by (auto split: nat.splits)
  moreover from ev\<^sub>f_return have "\<C> \<tturnstile> S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r 
    S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r b\<^sub>s (s\<^sub>r b\<^sub>s)" by (metis ev\<^sub>r_return)
  ultimately show ?case by blast
next
  case (ev\<^sub>f_jump \<C> p\<^sub>\<C> h\<^sub>f v\<^sub>2 p\<^sub>\<Delta>' p\<^sub>\<C>' \<Delta>\<^sub>f v\<^sub>1 \<Delta>\<^sub>f' p2 \<V>\<^sub>f p\<^sub>\<Delta> s\<^sub>f)
  then obtain h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r b\<^sub>s where S: "h\<^sub>f = H h\<^sub>r b\<^sub>h \<and> \<Delta>\<^sub>f = H \<Delta>\<^sub>r b\<^sub>\<Delta> \<and> p\<^sub>\<Delta> = s\<^sub>r (Suc b\<^sub>s) \<and> 
    s\<^sub>f = listify_heap (s\<^sub>r \<circ> Suc) b\<^sub>s \<and> listify_heap \<V>\<^sub>r b\<^sub>\<V> = v\<^sub>1 # v\<^sub>2 # \<V>\<^sub>f \<and> 
      \<Sigma>\<^sub>r = S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r b\<^sub>\<V> s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>)" by fastforce
  then obtain vp' where V: "b\<^sub>\<V> = Suc (Suc vp') \<and> v\<^sub>1 = \<V>\<^sub>r (Suc vp') \<and> v\<^sub>2 = \<V>\<^sub>r vp' \<and> 
    \<V>\<^sub>f = listify_heap \<V>\<^sub>r vp'" by fastforce
  from ev\<^sub>f_jump S V have H1: "h\<^sub>r (\<V>\<^sub>r vp') = (PEnv, p\<^sub>\<Delta>')" by simp
  from ev\<^sub>f_jump S V have H2: "h\<^sub>r (Suc (\<V>\<^sub>r vp')) = (PCode, p\<^sub>\<C>')" by simp
  from ev\<^sub>f_jump S V have "p2 = b\<^sub>\<Delta> \<and> \<Delta>\<^sub>f' = H (\<Delta>\<^sub>r(b\<^sub>\<Delta> := v\<^sub>1, Suc b\<^sub>\<Delta> := p\<^sub>\<Delta>')) (Suc (Suc b\<^sub>\<Delta>))" by auto
  with S V have X: "S\<^sub>f h\<^sub>f \<Delta>\<^sub>f' \<V>\<^sub>f (p\<^sub>\<C>' # Suc (Suc b\<^sub>\<Delta>) # s\<^sub>f) = 
    restructure (S\<^sub>r h\<^sub>r b\<^sub>h (\<Delta>\<^sub>r(b\<^sub>\<Delta> := v\<^sub>1, Suc b\<^sub>\<Delta> := p\<^sub>\<Delta>')) (2 + b\<^sub>\<Delta>) \<V>\<^sub>r vp' 
      (s\<^sub>r(Suc (Suc b\<^sub>s) - 1 := Suc (Suc b\<^sub>\<Delta>))) (Suc (Suc b\<^sub>s)) p\<^sub>\<C>')" by simp
  from ev\<^sub>f_jump V H1 H2 have "
        \<C> \<tturnstile> S\<^sub>r h\<^sub>r b\<^sub>h \<Delta>\<^sub>r b\<^sub>\<Delta> \<V>\<^sub>r (Suc (Suc vp')) s\<^sub>r (Suc (Suc b\<^sub>s)) (Suc p\<^sub>\<C>) \<leadsto>\<^sub>r 
    S\<^sub>r h\<^sub>r b\<^sub>h (\<Delta>\<^sub>r(b\<^sub>\<Delta> := v\<^sub>1, Suc b\<^sub>\<Delta> := p\<^sub>\<Delta>')) (2 + b\<^sub>\<Delta>) \<V>\<^sub>r vp'
      (s\<^sub>r(Suc (Suc b\<^sub>s) - 1 := Suc (Suc b\<^sub>\<Delta>))) (Suc (Suc b\<^sub>s)) p\<^sub>\<C>'" using ev\<^sub>r_jump by fastforce
  with ev\<^sub>f_jump S V X show ?case by auto
qed

theorem correct\<^sub>r_iter [simp]: "iter (\<tturnstile> \<C> \<leadsto>\<^sub>f) (restructure \<Sigma>\<^sub>r) \<Sigma>\<^sub>f' \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>r'. iter (\<tturnstile> \<C> \<leadsto>\<^sub>r) \<Sigma>\<^sub>r \<Sigma>\<^sub>r' \<and> \<Sigma>\<^sub>f' = restructure \<Sigma>\<^sub>r'"
  by (induction "restructure \<Sigma>\<^sub>r" \<Sigma>\<^sub>f' arbitrary: \<Sigma>\<^sub>r rule: iter.induct) 
     (force, metis correct\<^sub>r iter_step)

end