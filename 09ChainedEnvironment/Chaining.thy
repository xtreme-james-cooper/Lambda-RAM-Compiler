theory Chaining
  imports ChainedEnvironment "../08HeapMemory/HeapMemory"
begin

section \<open>Chaining environments\<close>

text \<open>Restoring environments from linked-list form is a matter of following the pointers down until 
we reach the end. To ensure termination, we only follow pointers to lower in the heap - but since we 
allocate in linear order, this means earlier in the heap, and of course, just as with the value 
stack, each environment can only build on preexisting ones; so we will never encounter a pointer to 
higher up.\<close>

fun unchain_env :: "('a \<times> ptr) heap \<Rightarrow> ptr \<Rightarrow> 'a list" where
  "unchain_env \<Delta> 0 = []"
| "unchain_env \<Delta> (Suc p) = (case hlookup \<Delta> p of 
      (v, p') \<Rightarrow> v # (if p' \<le> p then unchain_env \<Delta> p' else undefined))"

text \<open>We map the transformation through the whole evaluation state.\<close>

primrec unchain_closure :: "(ptr \<times> ptr) heap \<Rightarrow> closure\<^sub>v \<Rightarrow> closure\<^sub>h" where
  "unchain_closure \<Delta> (Const\<^sub>v n) = Const\<^sub>h n"
| "unchain_closure \<Delta> (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>) = Lam\<^sub>h (unchain_env \<Delta> p\<^sub>\<Delta>) p\<^sub>\<C>"

abbreviation unchain_heap :: "closure\<^sub>v heap \<Rightarrow> (ptr \<times> ptr) heap \<Rightarrow> closure\<^sub>h heap" where
  "unchain_heap h \<Delta> \<equiv> hmap (unchain_closure \<Delta>) h"

primrec unchain_frame :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) \<Rightarrow> (ptr list \<times> nat)" where
  "unchain_frame \<Delta> (p\<^sub>\<Delta>, p\<^sub>\<C>) = (unchain_env \<Delta> p\<^sub>\<Delta>, p\<^sub>\<C>)"

abbreviation unchain_stack :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) list \<Rightarrow> (ptr list \<times> nat) list" where
  "unchain_stack \<Delta> s \<equiv> map (unchain_frame \<Delta>) s"

primrec unchain_state :: "state\<^sub>v \<Rightarrow> state\<^sub>h" where
  "unchain_state (S\<^sub>v h \<Delta> \<V> s) = S\<^sub>h (unchain_heap h \<Delta>) \<V> (unchain_stack \<Delta> s)"

lemma halloc_unchain_heap_const [simp]: "halloc h (Const\<^sub>v n) = (h', p) \<Longrightarrow> 
  halloc (unchain_heap h \<Delta>) (Const\<^sub>h n) = (unchain_heap h' \<Delta>, p)"
proof -
  assume "halloc h (Const\<^sub>v n) = (h', p)"
  hence "halloc (hmap (unchain_closure \<Delta>) h) (unchain_closure \<Delta> (Const\<^sub>v n)) = 
    (hmap (unchain_closure \<Delta>) h', p)" by (metis halloc_map)
  thus ?thesis by simp
qed

lemma halloc_unchain_heap_lam [simp]: "halloc h (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>) = (h', v) \<Longrightarrow> 
  halloc (unchain_heap h \<Delta>) (Lam\<^sub>h (unchain_env \<Delta> p\<^sub>\<Delta>) p\<^sub>\<C>) = (unchain_heap h' \<Delta>, v)"
proof -
  assume "halloc h (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>) = (h', v)"
  hence "halloc (hmap (unchain_closure \<Delta>) h) (unchain_closure \<Delta> (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>)) = 
    (hmap (unchain_closure \<Delta>) h', v)" by (metis halloc_map)
  thus ?thesis by simp
qed

text \<open>We define a set of predicates to verify our "no upward pointers" condition.\<close>

abbreviation chain_structured :: "closure\<^sub>v heap \<Rightarrow> (ptr \<times> ptr) heap \<Rightarrow> bool" where
  "chain_structured h \<Delta> \<equiv> heap_all (\<lambda>p (v, p'). p' \<le> p \<and> hcontains h v) \<Delta>"

primrec chained_heap_pointer :: "(ptr \<times> ptr) heap \<Rightarrow> ptr \<Rightarrow> bool" where
  "chained_heap_pointer \<Delta> 0 = True"
| "chained_heap_pointer \<Delta> (Suc p) = hcontains \<Delta> p"

primrec chained_frame :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) \<Rightarrow> bool" where
  "chained_frame \<Delta> (p\<^sub>\<Delta>, p\<^sub>\<C>) = chained_heap_pointer \<Delta> p\<^sub>\<Delta>"

abbreviation chained_stack :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) list \<Rightarrow> bool" where
  "chained_stack \<Delta> s \<equiv> list_all (chained_frame \<Delta>) s"

abbreviation chained_vals :: "closure\<^sub>v heap \<Rightarrow> ptr list \<Rightarrow> bool" where
  "chained_vals h \<V> \<equiv> list_all (hcontains h) \<V>"

primrec chained_closure :: "(ptr \<times> ptr) heap \<Rightarrow> closure\<^sub>v \<Rightarrow> bool" where
  "chained_closure \<Delta> (Const\<^sub>v n) = True"
| "chained_closure \<Delta> (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>) = chained_heap_pointer \<Delta> p\<^sub>\<Delta>"

abbreviation chained_closures :: "(ptr \<times> ptr) heap \<Rightarrow> closure\<^sub>v heap \<Rightarrow> bool" where
  "chained_closures \<Delta> h \<equiv> heap_all (\<lambda>p. chained_closure \<Delta>) h"

primrec chained_state :: "state\<^sub>v \<Rightarrow> bool" where
  "chained_state (S\<^sub>v h \<Delta> \<V> s) = (
    chain_structured h \<Delta> \<and> chained_closures \<Delta> h \<and> chained_vals h \<V> \<and> chained_stack \<Delta> s)"

lemma chained_heap_pointer_unfold [elim]: "hcontains \<Delta> p \<Longrightarrow> p' \<le> p \<Longrightarrow> chained_heap_pointer \<Delta> p'"
  by (induction p') auto

lemma lookup_unchain_env [simp]: "chain_structured h \<Delta> \<Longrightarrow> chained_heap_pointer \<Delta> p \<Longrightarrow>
  lookup (unchain_env \<Delta> p) x = chain_lookup \<Delta> p x"
proof (induction \<Delta> p x rule: chain_lookup.induct)
  case (3 \<Delta> p x)
  obtain v p' where V: "hlookup \<Delta> p = (v, p')" by (cases "hlookup \<Delta> p")
  from 3 have "hcontains \<Delta> p" by auto
  with 3 V have P: "p' \<le> p" using hlookup_all by fast
  with 3 V have "chained_heap_pointer \<Delta> p'" by auto
  with 3(1, 2) V P show ?case by fastforce
qed (simp_all split: prod.splits)

lemma halloc_unchain_env [simp]: "chain_structured h \<Delta> \<Longrightarrow> chained_heap_pointer \<Delta> p \<Longrightarrow> 
  halloc \<Delta> a = (\<Delta>', b) \<Longrightarrow> unchain_env \<Delta>' p = unchain_env \<Delta> p" 
proof (induction \<Delta> p rule: unchain_env.induct)
  case (2 \<Delta> p)
  obtain v p' where V: "hlookup \<Delta> p = (v, p')" by (cases "hlookup \<Delta> p")
  from 2 have H: "hcontains \<Delta> p" by auto
  with 2 V have P: "p' \<le> p" using hlookup_all by fast
  with 2 have "chained_heap_pointer \<Delta> p'" by auto
  with 2 V P have U: "unchain_env \<Delta>' p' = unchain_env \<Delta> p'" by simp
  from 2 V H have "hlookup \<Delta>' p = (v, p')" by simp
  with V P U show ?case by simp
qed simp_all

lemma halloc_unchain_env2 [elim]: "hcontains \<Delta> p \<Longrightarrow> halloc \<Delta> v = (\<Delta>', q) \<Longrightarrow> 
  unchain_env \<Delta>' p = unchain_env \<Delta> p"
proof (induction \<Delta> p rule: unchain_env.induct)
  case (2 \<Delta> p)
  obtain vv p' where V: "hlookup \<Delta> p = (vv, p')" by (cases "hlookup \<Delta> p")
  from 2(2) have "hcontains \<Delta> p" by fast
  with 2(3) V have V': "hlookup \<Delta>' p = (vv, p')" by simp
  from 2(2) V have "p' \<le> p \<Longrightarrow> hcontains \<Delta> p'" by auto
  with 2 V have "p' \<le> p \<Longrightarrow> unchain_env \<Delta>' p' = unchain_env \<Delta> p'" by metis
  with V V' show ?case by simp
qed simp_all

lemma halloc_unchain_env3 [elim]: "chained_heap_pointer \<Delta> a \<Longrightarrow> halloc \<Delta> v = (\<Delta>', p) \<Longrightarrow> 
  unchain_env \<Delta>' a = unchain_env \<Delta> a"
proof (induction a)
  case (Suc p)
  moreover obtain v' p' where "hlookup \<Delta> p = (v', p')" by (cases "hlookup \<Delta> p")
  moreover from Suc have "p' \<le> p \<Longrightarrow> hcontains \<Delta> p'" by auto
  ultimately show ?case by auto
qed simp_all

lemma halloc_unchain_heap [elim]: "chain_structured h \<Delta> \<Longrightarrow> chained_closures \<Delta> h \<Longrightarrow> 
  halloc \<Delta> v = (\<Delta>', p) \<Longrightarrow> unchain_heap h \<Delta>' = unchain_heap h \<Delta>"
proof -
  assume S: "chain_structured h \<Delta>" and C: "chained_closures \<Delta> h" 
    and A: "halloc \<Delta> v = (\<Delta>', p)"
  have "\<And>x. hcontains h x \<Longrightarrow> unchain_closure \<Delta>' (hlookup h x) = 
    unchain_closure \<Delta> (hlookup h x)" 
  proof -
    fix x
    assume X: "hcontains h x"
    show "unchain_closure \<Delta>' (hlookup h x) = unchain_closure \<Delta> (hlookup h x)" 
    proof (cases "hlookup h x")
      case (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>)
      with C X have "chained_closure \<Delta> (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>)" by (metis hlookup_all)
      with S A Lam\<^sub>v show ?thesis by auto
    qed simp_all
  qed
  thus "hmap (unchain_closure \<Delta>') h = hmap (unchain_closure \<Delta>) h" by (metis hmap_eq)
qed

lemma halloc_unchain_stack [elim]: "chained_stack \<Delta> s \<Longrightarrow> halloc \<Delta> v = (\<Delta>', p) \<Longrightarrow> 
    unchain_stack \<Delta>' s = unchain_stack \<Delta> s"
  by (induction s) auto

lemma unfold_unstack_list [simp]: "chain_structured h \<Delta> \<Longrightarrow> chained_heap_pointer \<Delta> p \<Longrightarrow> 
  halloc \<Delta> (v, p) = (\<Delta>', p') \<Longrightarrow> unchain_env \<Delta>' (Suc p') = v # unchain_env \<Delta> p"
proof -
  assume A: "chain_structured h \<Delta>"
  assume B: "chained_heap_pointer \<Delta> p"
  assume C: "halloc \<Delta> (v, p) = (\<Delta>', p')"
  moreover with A B have "unchain_env \<Delta>' p = unchain_env \<Delta> p" by simp
  moreover have "p \<le> p'" 
  proof (cases p)
    case (Suc pp)
    moreover with B C have "pp < p'" by simp
    ultimately show ?thesis by simp
  qed simp_all
  ultimately show ?thesis by simp
qed

lemma halloc_chained_heap_pointer_le [simp]: "chained_heap_pointer \<Delta> p\<^sub>\<Delta> \<Longrightarrow> 
    halloc \<Delta> (v, p\<^sub>\<Delta>) = (\<Delta>', p\<^sub>\<Delta>') \<Longrightarrow> p\<^sub>\<Delta> \<le> p\<^sub>\<Delta>'"
  by (cases p\<^sub>\<Delta>) (simp_all add: Suc_le_eq)

text \<open>Completeness follows:\<close>

theorem complete\<^sub>v [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>v \<leadsto>\<^sub>v \<Sigma>\<^sub>v' \<Longrightarrow> chained_state \<Sigma>\<^sub>v \<Longrightarrow> 
  \<C> \<tturnstile> unchain_state \<Sigma>\<^sub>v \<leadsto>\<^sub>h unchain_state \<Sigma>\<^sub>v'"
proof (induction \<Sigma>\<^sub>v \<Sigma>\<^sub>v' rule: eval\<^sub>v.induct)
  case (ev\<^sub>v_apply \<C> p\<^sub>\<C> h\<^sub>v v\<^sub>2 p\<^sub>\<Delta>' p\<^sub>\<C>' \<Delta>\<^sub>v v\<^sub>1 \<Delta>\<^sub>v' p\<^sub>\<Delta>'' \<V> p\<^sub>\<Delta> s\<^sub>v)
  from ev\<^sub>v_apply have "chained_closures \<Delta>\<^sub>v h\<^sub>v \<and> hcontains h\<^sub>v v\<^sub>2" by simp
  with ev\<^sub>v_apply have "chained_closure \<Delta>\<^sub>v (Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>')" by (metis hlookup_all)
  with ev\<^sub>v_apply have "chain_structured h\<^sub>v \<Delta>\<^sub>v \<and> chained_heap_pointer \<Delta>\<^sub>v p\<^sub>\<Delta>' \<and> 
    halloc \<Delta>\<^sub>v (v\<^sub>1, p\<^sub>\<Delta>') = (\<Delta>\<^sub>v', p\<^sub>\<Delta>'')" by auto
  hence X: "unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>'') = v\<^sub>1 # unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>'" by (metis unfold_unstack_list)
  from ev\<^sub>v_apply have A: "unchain_heap h\<^sub>v \<Delta>\<^sub>v' = unchain_heap h\<^sub>v \<Delta>\<^sub>v" by auto
  from ev\<^sub>v_apply have B: "unchain_env \<Delta>\<^sub>v' p\<^sub>\<Delta> = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by auto
  from ev\<^sub>v_apply have "chained_stack \<Delta>\<^sub>v s\<^sub>v" by simp
  with ev\<^sub>v_apply have C: "unchain_stack \<Delta>\<^sub>v' s\<^sub>v = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by fastforce
  with ev\<^sub>v_apply X A B have "\<C> \<tturnstile> S\<^sub>h (unchain_heap h\<^sub>v \<Delta>\<^sub>v) (v\<^sub>1 # v\<^sub>2 # \<V>) 
    ((unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # unchain_stack \<Delta>\<^sub>v s\<^sub>v) \<leadsto>\<^sub>h
      S\<^sub>h (unchain_heap h\<^sub>v \<Delta>\<^sub>v') \<V> 
        ((unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>''), p\<^sub>\<C>') # (unchain_env \<Delta>\<^sub>v' p\<^sub>\<Delta>, p\<^sub>\<C>) # unchain_stack \<Delta>\<^sub>v' s\<^sub>v)" 
    by (simp add: C)
  thus ?case by simp
next
  case (ev\<^sub>v_pushenv \<C> p\<^sub>\<C> \<Delta>\<^sub>v v p\<^sub>\<Delta> \<Delta>\<^sub>v' p\<^sub>\<Delta>' h\<^sub>v \<V> s\<^sub>v)
  hence X: "unchain_heap h\<^sub>v \<Delta>\<^sub>v' = unchain_heap h\<^sub>v \<Delta>\<^sub>v" by auto
  from ev\<^sub>v_pushenv have "chained_stack \<Delta>\<^sub>v s\<^sub>v" by simp
  with ev\<^sub>v_pushenv have Y: "unchain_stack \<Delta>\<^sub>v' s\<^sub>v = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by fastforce
  from ev\<^sub>v_pushenv have "chain_structured h\<^sub>v \<Delta>\<^sub>v \<and> chained_heap_pointer \<Delta>\<^sub>v p\<^sub>\<Delta> \<and> 
    halloc \<Delta>\<^sub>v (v, p\<^sub>\<Delta>) = (\<Delta>\<^sub>v', p\<^sub>\<Delta>')" by auto
  hence "unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>') = v # unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by (metis unfold_unstack_list)
  with ev\<^sub>v_pushenv X show ?case by (simp add: Y)
next
  case (ev\<^sub>v_jump \<C> p\<^sub>\<C> h\<^sub>v v\<^sub>2 p\<^sub>\<Delta>' p\<^sub>\<C>' \<Delta>\<^sub>v v\<^sub>1 \<Delta>\<^sub>v' p\<^sub>\<Delta>'' \<V> p\<^sub>\<Delta> s\<^sub>v)
  from ev\<^sub>v_jump have "chained_closures \<Delta>\<^sub>v h\<^sub>v \<and> hcontains h\<^sub>v v\<^sub>2" by simp
  with ev\<^sub>v_jump have "chained_closure \<Delta>\<^sub>v (Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>')" by (metis hlookup_all)
  with ev\<^sub>v_jump have "chain_structured h\<^sub>v \<Delta>\<^sub>v \<and> chained_heap_pointer \<Delta>\<^sub>v p\<^sub>\<Delta>' \<and> 
    halloc \<Delta>\<^sub>v (v\<^sub>1, p\<^sub>\<Delta>') = (\<Delta>\<^sub>v', p\<^sub>\<Delta>'')" by auto
  hence X: "unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>'') = v\<^sub>1 # unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>'" by (metis unfold_unstack_list)
  from ev\<^sub>v_jump have A: "unchain_heap h\<^sub>v \<Delta>\<^sub>v' = unchain_heap h\<^sub>v \<Delta>\<^sub>v" by auto
  from ev\<^sub>v_jump have "chained_stack \<Delta>\<^sub>v s\<^sub>v" by simp
  with ev\<^sub>v_jump have B: "unchain_stack \<Delta>\<^sub>v' s\<^sub>v = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by fastforce 
  with ev\<^sub>v_jump X A have "\<C> \<tturnstile> S\<^sub>h (unchain_heap h\<^sub>v \<Delta>\<^sub>v) (v\<^sub>1 # v\<^sub>2 # \<V>) 
    ((unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # unchain_stack \<Delta>\<^sub>v s\<^sub>v) \<leadsto>\<^sub>h
      S\<^sub>h (unchain_heap h\<^sub>v \<Delta>\<^sub>v') \<V> 
        ((unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>''), p\<^sub>\<C>') # unchain_stack \<Delta>\<^sub>v' s\<^sub>v)" by (simp add: B)
  thus ?case by simp
qed auto

text \<open>There are few reconstruction lemmas this stage, but correctness is still somewhat involved.\<close>

lemma unchain_state_reverse [dest]: "S\<^sub>h h\<^sub>h \<V> s\<^sub>h = unchain_state \<Sigma>\<^sub>v \<Longrightarrow> 
    \<exists>h\<^sub>v \<Delta>\<^sub>v s\<^sub>v. \<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V> s\<^sub>v \<and> h\<^sub>h = unchain_heap h\<^sub>v \<Delta>\<^sub>v \<and> s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v"
  by (induction \<Sigma>\<^sub>v) simp_all

lemma unchain_lam_reverse [dest]: "Lam\<^sub>h \<Delta>\<^sub>h p\<^sub>C = unchain_closure \<Delta>\<^sub>v x \<Longrightarrow> 
    \<exists>p\<^sub>\<Delta>. x = Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>C \<and> \<Delta>\<^sub>h = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>"
  by (induction x) simp_all

theorem correct\<^sub>v [simp]: "\<C> \<tturnstile> unchain_state \<Sigma>\<^sub>v \<leadsto>\<^sub>h \<Sigma>\<^sub>h \<Longrightarrow> chained_state \<Sigma>\<^sub>v \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>v'. (\<C> \<tturnstile> \<Sigma>\<^sub>v \<leadsto>\<^sub>v \<Sigma>\<^sub>v') \<and> \<Sigma>\<^sub>h = unchain_state \<Sigma>\<^sub>v'"
proof (induction "unchain_state \<Sigma>\<^sub>v" \<Sigma>\<^sub>h arbitrary: \<Sigma>\<^sub>v rule: eval\<^sub>h.induct)
  case (ev\<^sub>h_lookup \<C> p\<^sub>\<C> x y z \<Delta>\<^sub>h v h\<^sub>h \<V> s\<^sub>h)
  then obtain h\<^sub>v \<Delta>\<^sub>v s\<^sub>v' where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V> s\<^sub>v' \<and> h\<^sub>h = unchain_heap h\<^sub>v \<Delta>\<^sub>v \<and> 
    (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) # s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v'" by fastforce
  then obtain f\<^sub>v s\<^sub>v where SF: "s\<^sub>v' = f\<^sub>v # s\<^sub>v \<and> (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) = unchain_frame \<Delta>\<^sub>v f\<^sub>v \<and> 
    s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by auto
  then obtain p\<^sub>\<Delta> where P: "f\<^sub>v = (p\<^sub>\<Delta>, Suc p\<^sub>\<C>) \<and> \<Delta>\<^sub>h = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by (cases f\<^sub>v) simp_all
  with ev\<^sub>h_lookup S SF have C: "chain_structured h\<^sub>v \<Delta>\<^sub>v" by simp
  with ev\<^sub>h_lookup S SF P have X: "S\<^sub>h h\<^sub>h (v # \<V>) ((\<Delta>\<^sub>h, p\<^sub>\<C>) # s\<^sub>h) = 
    unchain_state (S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v))" by simp
  from ev\<^sub>h_lookup S SF P have "chained_frame \<Delta>\<^sub>v (p\<^sub>\<Delta>, Suc p\<^sub>\<C>)" by simp
  with C have "lookup (unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>) x = chain_lookup \<Delta>\<^sub>v p\<^sub>\<Delta> x" by simp
  with ev\<^sub>h_lookup P C have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V> ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v)" 
    by simp
  with S SF P X show ?case by blast
next
  case (ev\<^sub>h_pushcon \<C> p\<^sub>\<C> n h\<^sub>h h\<^sub>h' v \<V> \<Delta>\<^sub>h s\<^sub>h)
  then obtain h\<^sub>v \<Delta>\<^sub>v s\<^sub>v' where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V> s\<^sub>v' \<and> h\<^sub>h = unchain_heap h\<^sub>v \<Delta>\<^sub>v \<and> 
    (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) # s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v'" by fastforce
  then obtain f\<^sub>v s\<^sub>v where SF: "s\<^sub>v' = f\<^sub>v # s\<^sub>v \<and> (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) = unchain_frame \<Delta>\<^sub>v f\<^sub>v \<and> 
    s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by auto
  then obtain p\<^sub>\<Delta> where P: "f\<^sub>v = (p\<^sub>\<Delta>, Suc p\<^sub>\<C>) \<and> \<Delta>\<^sub>h = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by (cases f\<^sub>v) simp_all
  from ev\<^sub>h_pushcon S have "halloc (hmap (unchain_closure \<Delta>\<^sub>v) h\<^sub>v) (unchain_closure \<Delta>\<^sub>v (Const\<^sub>v n)) = 
    (h\<^sub>h', v)" by simp
  then obtain h\<^sub>v' where H: "halloc h\<^sub>v (Const\<^sub>v n) = (h\<^sub>v', v) \<and> h\<^sub>h' = hmap (unchain_closure \<Delta>\<^sub>v) h\<^sub>v'" 
    by (metis halloc_map_inv)
  hence "h\<^sub>h' = unchain_heap h\<^sub>v' \<Delta>\<^sub>v" by simp
  with SF P have X: "S\<^sub>h h\<^sub>h' (v # \<V>) ((\<Delta>\<^sub>h, p\<^sub>\<C>) # s\<^sub>h) = 
    unchain_state (S\<^sub>v h\<^sub>v' \<Delta>\<^sub>v (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v))" by simp
  from ev\<^sub>h_pushcon H have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V> ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v S\<^sub>v h\<^sub>v' \<Delta>\<^sub>v (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v)" 
    by simp
  with S SF P X show ?case by blast
next
  case (ev\<^sub>h_pushlam \<C> p\<^sub>\<C> p\<^sub>\<C>' n h\<^sub>h \<Delta>\<^sub>h h\<^sub>h' v \<V> s\<^sub>h)
  then obtain h\<^sub>v \<Delta>\<^sub>v s\<^sub>v' where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V> s\<^sub>v' \<and> h\<^sub>h = unchain_heap h\<^sub>v \<Delta>\<^sub>v \<and> 
    (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) # s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v'" by fastforce
  then obtain f\<^sub>v s\<^sub>v where SF: "s\<^sub>v' = f\<^sub>v # s\<^sub>v \<and> (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) = unchain_frame \<Delta>\<^sub>v f\<^sub>v \<and> 
    s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by auto
  then obtain p\<^sub>\<Delta> where P: "f\<^sub>v = (p\<^sub>\<Delta>, Suc p\<^sub>\<C>) \<and> \<Delta>\<^sub>h = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by (cases f\<^sub>v) simp_all
  with ev\<^sub>h_pushlam S have "halloc (hmap (unchain_closure \<Delta>\<^sub>v) h\<^sub>v) 
    (unchain_closure \<Delta>\<^sub>v (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>')) = (h\<^sub>h', v)" by simp
  then obtain h\<^sub>v' where H: "halloc h\<^sub>v (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>') = (h\<^sub>v', v) \<and> 
    h\<^sub>h' = hmap (unchain_closure \<Delta>\<^sub>v) h\<^sub>v'" by (metis halloc_map_inv)
  hence "h\<^sub>h' = unchain_heap h\<^sub>v' \<Delta>\<^sub>v" by simp
  with SF P have X: "S\<^sub>h h\<^sub>h' (v # \<V>) ((\<Delta>\<^sub>h, p\<^sub>\<C>) # s\<^sub>h) = 
    unchain_state (S\<^sub>v h\<^sub>v' \<Delta>\<^sub>v (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v))" by simp
  from ev\<^sub>h_pushlam H have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V> ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>v' \<Delta>\<^sub>v (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v)" by simp
  with S SF P X show ?case by blast
next
  case (ev\<^sub>h_apply \<C> p\<^sub>\<C> h\<^sub>h v\<^sub>2 \<Delta>\<^sub>h' p\<^sub>\<C>' v\<^sub>1 \<V> \<Delta>\<^sub>h s\<^sub>h)
  then obtain h\<^sub>v \<Delta>\<^sub>v s\<^sub>v' where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>1 # v\<^sub>2 # \<V>) s\<^sub>v' \<and> 
    h\<^sub>h = unchain_heap h\<^sub>v \<Delta>\<^sub>v \<and> (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) # s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v'" by fastforce
  then obtain f\<^sub>v s\<^sub>v where SF: "s\<^sub>v' = f\<^sub>v # s\<^sub>v \<and> (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) = unchain_frame \<Delta>\<^sub>v f\<^sub>v \<and> 
    s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by auto
  then obtain p\<^sub>\<Delta> where P: "f\<^sub>v = (p\<^sub>\<Delta>, Suc p\<^sub>\<C>) \<and> \<Delta>\<^sub>h = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by (cases f\<^sub>v) simp_all
  from ev\<^sub>h_apply S have "Lam\<^sub>h \<Delta>\<^sub>h' p\<^sub>\<C>' = unchain_closure \<Delta>\<^sub>v (hlookup h\<^sub>v v\<^sub>2)" by simp
  then obtain p\<^sub>\<Delta>' where P': "hlookup h\<^sub>v v\<^sub>2 = Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>' \<and> \<Delta>\<^sub>h' = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>'" by blast
  obtain \<Delta>\<^sub>v' p\<^sub>\<Delta>'' where H: "halloc \<Delta>\<^sub>v (v\<^sub>1, p\<^sub>\<Delta>') = (\<Delta>\<^sub>v', p\<^sub>\<Delta>'')" 
    by (cases "halloc \<Delta>\<^sub>v (v\<^sub>1, p\<^sub>\<Delta>')") simp_all
  from ev\<^sub>h_apply S SF P have C: "chain_structured h\<^sub>v \<Delta>\<^sub>v \<and> chained_closures \<Delta>\<^sub>v h\<^sub>v \<and>
    hcontains h\<^sub>v v\<^sub>1 \<and> hcontains h\<^sub>v v\<^sub>2 \<and> chained_vals h\<^sub>v \<V> \<and> chained_frame \<Delta>\<^sub>v (p\<^sub>\<Delta>, Suc p\<^sub>\<C>) \<and> 
      chained_stack \<Delta>\<^sub>v s\<^sub>v" by simp
  with H have Y: "unchain_heap h\<^sub>v \<Delta>\<^sub>v' = unchain_heap h\<^sub>v \<Delta>\<^sub>v" by fast
  from H C have "unchain_env \<Delta>\<^sub>v' p\<^sub>\<Delta> = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by fastforce
  with P have W: "\<Delta>\<^sub>h = unchain_env \<Delta>\<^sub>v' p\<^sub>\<Delta>" by metis
  from P' C have "chained_closure \<Delta>\<^sub>v (Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>')" by (metis hlookup_all)
  hence "chained_heap_pointer \<Delta>\<^sub>v p\<^sub>\<Delta>'" by auto
  with H C have "unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>'') = v\<^sub>1 # unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>'" 
    by (metis unfold_unstack_list)
  with H P' have Z: "v\<^sub>1 # \<Delta>\<^sub>h' = unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>'')" by simp
  from H C have "unchain_stack \<Delta>\<^sub>v' s\<^sub>v = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by fast
  with SF have "s\<^sub>h = unchain_stack \<Delta>\<^sub>v' s\<^sub>v" by simp
  with S Y Z W have X: "S\<^sub>h h\<^sub>h \<V> ((v\<^sub>1 # \<Delta>\<^sub>h', p\<^sub>\<C>') # (\<Delta>\<^sub>h, p\<^sub>\<C>) # s\<^sub>h) = 
    unchain_state (S\<^sub>v h\<^sub>v \<Delta>\<^sub>v' \<V> ((Suc p\<^sub>\<Delta>'', p\<^sub>\<C>') # (p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v))" by simp
  from ev\<^sub>h_apply P' H have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>1 # v\<^sub>2 # \<V>) ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v 
      S\<^sub>v h\<^sub>v \<Delta>\<^sub>v' \<V> ((Suc p\<^sub>\<Delta>'', p\<^sub>\<C>') # (p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v)" by simp
  with S SF P X show ?case by blast
next
  case (ev\<^sub>h_pushenv \<C> p\<^sub>\<C> h\<^sub>h v \<V> \<Delta>\<^sub>h s\<^sub>h)
  then obtain h\<^sub>v \<Delta>\<^sub>v s\<^sub>v' where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v # \<V>) s\<^sub>v' \<and> h\<^sub>h = unchain_heap h\<^sub>v \<Delta>\<^sub>v \<and> 
    (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) # s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v'" by fastforce
  then obtain f\<^sub>v s\<^sub>v where SF: "s\<^sub>v' = f\<^sub>v # s\<^sub>v \<and> (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) = unchain_frame \<Delta>\<^sub>v f\<^sub>v \<and> 
    s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by auto
  then obtain p\<^sub>\<Delta> where P: "f\<^sub>v = (p\<^sub>\<Delta>, Suc p\<^sub>\<C>) \<and> \<Delta>\<^sub>h = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by (cases f\<^sub>v) simp_all
  obtain \<Delta>\<^sub>v' p\<^sub>\<Delta>' where H: "halloc \<Delta>\<^sub>v (v, p\<^sub>\<Delta>) = (\<Delta>\<^sub>v', p\<^sub>\<Delta>')" 
    by (cases "halloc \<Delta>\<^sub>v (v, p\<^sub>\<Delta>)") simp_all
  from ev\<^sub>h_pushenv S SF P H have A: "unchain_heap h\<^sub>v \<Delta>\<^sub>v' = unchain_heap h\<^sub>v \<Delta>\<^sub>v" by auto
  from ev\<^sub>h_pushenv S SF P H have B: "unchain_env \<Delta>\<^sub>v' p\<^sub>\<Delta> = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by auto 
  from ev\<^sub>h_pushenv S SF P have "chained_stack \<Delta>\<^sub>v s\<^sub>v" by simp
  with H have C: "unchain_stack \<Delta>\<^sub>v' s\<^sub>v = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by fastforce
  from ev\<^sub>h_pushenv(3) S SF P H have "p\<^sub>\<Delta> \<le> p\<^sub>\<Delta>'" by auto
  with S SF P H A B C have X: "S\<^sub>h h\<^sub>h \<V> ((v # \<Delta>\<^sub>h, p\<^sub>\<C>) # s\<^sub>h) = 
    unchain_state (S\<^sub>v h\<^sub>v \<Delta>\<^sub>v' \<V> ((Suc p\<^sub>\<Delta>', p\<^sub>\<C>) # s\<^sub>v))" by simp
  from ev\<^sub>h_pushenv H have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v # \<V>) ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>v \<Delta>\<^sub>v' \<V> ((Suc p\<^sub>\<Delta>', p\<^sub>\<C>) # s\<^sub>v)" by simp
  with S SF P X show ?case by blast
next
  case (ev\<^sub>h_return \<C> p\<^sub>\<C> h\<^sub>h \<V> \<Delta>\<^sub>h s\<^sub>h)
  then obtain h\<^sub>v \<Delta>\<^sub>v s\<^sub>v' where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V> s\<^sub>v' \<and> h\<^sub>h = unchain_heap h\<^sub>v \<Delta>\<^sub>v \<and> 
    (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) # s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v'" by fastforce
  then obtain f\<^sub>v s\<^sub>v where SF: "s\<^sub>v' = f\<^sub>v # s\<^sub>v \<and> (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) = unchain_frame \<Delta>\<^sub>v f\<^sub>v \<and> 
    s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by auto
  then obtain p\<^sub>\<Delta> where P: "f\<^sub>v = (p\<^sub>\<Delta>, Suc p\<^sub>\<C>) \<and> \<Delta>\<^sub>h = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by (cases f\<^sub>v) simp_all
  from S SF have X: "S\<^sub>h h\<^sub>h \<V> s\<^sub>h = unchain_state (S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V> s\<^sub>v)" by simp
  from ev\<^sub>h_return have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V> ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V> s\<^sub>v" by simp
  with S SF P X show ?case by blast
next
  case (ev\<^sub>h_jump \<C> p\<^sub>\<C> h\<^sub>h v\<^sub>2 \<Delta>\<^sub>h' p\<^sub>\<C>' v\<^sub>1 \<V> \<Delta>\<^sub>h s\<^sub>h)
  then obtain h\<^sub>v \<Delta>\<^sub>v s\<^sub>v' where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>1 # v\<^sub>2 # \<V>) s\<^sub>v' \<and> 
    h\<^sub>h = unchain_heap h\<^sub>v \<Delta>\<^sub>v \<and> (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) # s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v'" by fastforce
  then obtain f\<^sub>v s\<^sub>v where SF: "s\<^sub>v' = f\<^sub>v # s\<^sub>v \<and> (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) = unchain_frame \<Delta>\<^sub>v f\<^sub>v \<and> 
    s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by auto
  then obtain p\<^sub>\<Delta> where P: "f\<^sub>v = (p\<^sub>\<Delta>, Suc p\<^sub>\<C>) \<and> \<Delta>\<^sub>h = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by (cases f\<^sub>v) simp_all
  from ev\<^sub>h_jump S have "Lam\<^sub>h \<Delta>\<^sub>h' p\<^sub>\<C>' = unchain_closure \<Delta>\<^sub>v (hlookup h\<^sub>v v\<^sub>2)" by simp
  then obtain p\<^sub>\<Delta>' where P': "hlookup h\<^sub>v v\<^sub>2 = Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>' \<and> \<Delta>\<^sub>h' = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>'" by blast
  obtain \<Delta>\<^sub>v' p\<^sub>\<Delta>'' where H: "halloc \<Delta>\<^sub>v (v\<^sub>1, p\<^sub>\<Delta>') = (\<Delta>\<^sub>v', p\<^sub>\<Delta>'')" 
    by (cases "halloc \<Delta>\<^sub>v (v\<^sub>1, p\<^sub>\<Delta>')") simp_all
  from ev\<^sub>h_jump S SF P have C: "chain_structured h\<^sub>v \<Delta>\<^sub>v \<and> chained_closures \<Delta>\<^sub>v h\<^sub>v \<and>
    hcontains h\<^sub>v v\<^sub>1 \<and> hcontains h\<^sub>v v\<^sub>2 \<and> chained_vals h\<^sub>v \<V> \<and> chained_heap_pointer \<Delta>\<^sub>v p\<^sub>\<Delta> \<and> 
      chained_stack \<Delta>\<^sub>v s\<^sub>v" by simp
  with H have Y: "unchain_heap h\<^sub>v \<Delta>\<^sub>v' = unchain_heap h\<^sub>v \<Delta>\<^sub>v" by fast
  from P' C have "chained_closure \<Delta>\<^sub>v (Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>')" by (metis hlookup_all)
  hence "chained_heap_pointer \<Delta>\<^sub>v p\<^sub>\<Delta>'" by simp
  with H C have "unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>'') = v\<^sub>1 # unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>'" 
    by (metis unfold_unstack_list)
  with H P' have Z: "v\<^sub>1 # \<Delta>\<^sub>h' = unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>'')" by simp
  from H C have "unchain_stack \<Delta>\<^sub>v' s\<^sub>v = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by fast
  with SF have "s\<^sub>h = unchain_stack \<Delta>\<^sub>v' s\<^sub>v" by simp
  with S Y Z have X: "S\<^sub>h h\<^sub>h \<V> ((v\<^sub>1 # \<Delta>\<^sub>h', p\<^sub>\<C>') # s\<^sub>h) = 
    unchain_state (S\<^sub>v h\<^sub>v \<Delta>\<^sub>v' \<V> ((Suc p\<^sub>\<Delta>'', p\<^sub>\<C>') # s\<^sub>v))" by simp
  from ev\<^sub>h_jump P' H have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>1 # v\<^sub>2 # \<V>) ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v 
      S\<^sub>v h\<^sub>v \<Delta>\<^sub>v' \<V> ((Suc p\<^sub>\<Delta>'', p\<^sub>\<C>') # s\<^sub>v)" by simp
  with S SF P X show ?case by blast
qed

text \<open>However, proving that iterated evaluation is correct, which normally has been a trivial 
corollary, turns out to require a bit more machinery; the \<open>chained_state\<close> property is preserved by 
evaluation, but showing this (\<open>eval_preserves_chained\<close>) takes a few more lemmas, mostly dealing with
allocating into the environment heap.\<close>

lemma halloc_chained_heap_pointer [simp]: "halloc \<Delta> v = (\<Delta>', p) \<Longrightarrow> chained_heap_pointer \<Delta> x \<Longrightarrow> 
    chained_heap_pointer \<Delta>' x"
  by (cases x) simp_all

lemma hallock_chained_closure [simp]: "halloc \<Delta> v = (\<Delta>', p) \<Longrightarrow> chained_closure \<Delta> c \<Longrightarrow> 
    chained_closure \<Delta>' c"
  by (induction c) simp_all

lemma hallock_chained_closures [simp]: "halloc \<Delta> v = (\<Delta>', p) \<Longrightarrow> chained_closures \<Delta> h \<Longrightarrow> 
  chained_closures \<Delta>' h"
proof -
  assume "halloc \<Delta> v = (\<Delta>', p)"
  hence "\<And>y. chained_closure \<Delta> y \<Longrightarrow> chained_closure \<Delta>' y" by simp_all
  moreover assume "chained_closures \<Delta> h"
  ultimately show "chained_closures \<Delta>' h" by (metis heap_all_implication)
qed

lemma halloc_chained_frame [simp]: "halloc \<Delta> (v, p') = (\<Delta>', p) \<Longrightarrow> chained_frame \<Delta> f \<Longrightarrow> 
    chained_frame \<Delta>' f"
  by (induction f) simp_all

lemma hallock_chained_stack [simp]: "halloc \<Delta> (v, p') = (\<Delta>', p) \<Longrightarrow> chained_stack \<Delta> s \<Longrightarrow> 
    chained_stack \<Delta>' s"
  by (induction s) simp_all

lemma chained_hlookup_hcontains [elim]: "chain_structured h \<Delta> \<Longrightarrow> hcontains \<Delta> p \<Longrightarrow> 
  hlookup \<Delta> p = (a, b) \<Longrightarrow> hcontains h a"
proof -
  assume "chain_structured h \<Delta>" and "hcontains \<Delta> p" and "hlookup \<Delta> p = (a, b)"
  hence "(\<lambda>(v, p'). p' \<le> p \<and> hcontains h v) (a, b)" by (metis hlookup_all)
  thus ?thesis by simp
qed

lemma chain_lookup_hcontains [elim]: "chain_structured h \<Delta> \<Longrightarrow> hcontains \<Delta> p \<Longrightarrow> 
  chain_lookup \<Delta> p x = Some v \<Longrightarrow> hcontains h v"
proof (induction \<Delta> p x rule: chain_lookup.induct)
  case (2 \<Delta> p)
  moreover obtain a b where "hlookup \<Delta> p = (a, b)" by (cases "hlookup \<Delta> p")
  ultimately show ?case by auto
next
  case (3 \<Delta> p x)
  obtain a b where A: "hlookup \<Delta> p = (a, b)" by (cases "hlookup \<Delta> p")
  from 3 have "hcontains \<Delta> p" by auto
  with 3 A have "b \<le> p \<and> hcontains h a" using hlookup_all by fast
  with 3 have "hcontains \<Delta> b" by fastforce
  with 3 A show ?case by simp
qed simp_all

lemma chain_lookup_suc_hcontains [elim]: "chain_lookup \<Delta> (Suc p) x = Some v \<Longrightarrow> 
  chain_structured h \<Delta> \<Longrightarrow> hcontains \<Delta> p \<Longrightarrow> hcontains h v"
proof (induction \<Delta> "Suc p" x arbitrary: p rule: chain_lookup.induct)
  case (2 \<Delta> p)
  then obtain b where "hlookup \<Delta> p = (v, b)" by (cases "hlookup \<Delta> p") simp_all
  with 2 have "b \<le> p \<and> hcontains h v" using hlookup_all by fast
  with 2 show ?case by simp
next
  case (3 \<Delta> p x)
  moreover then obtain a b where A: "hlookup \<Delta> p = (a, b)" by (cases "hlookup \<Delta> p")
  moreover with 3 have "b \<le> p \<and> hcontains h a" using hlookup_all by fast
  ultimately show ?case by auto
qed

lemma chain_structured_alloc [simp]: "chained_heap_pointer \<Delta> p\<^sub>\<Delta> \<Longrightarrow> hcontains h v\<^sub>1 \<Longrightarrow> 
  halloc \<Delta> (v\<^sub>1, p\<^sub>\<Delta>) = (\<Delta>', p\<^sub>\<Delta>') \<Longrightarrow> chain_structured h \<Delta> \<Longrightarrow> chain_structured h \<Delta>'"
proof -
  assume X: "chained_heap_pointer \<Delta> p\<^sub>\<Delta>"
  moreover assume A: "halloc \<Delta> (v\<^sub>1, p\<^sub>\<Delta>) = (\<Delta>', p\<^sub>\<Delta>')" and "chain_structured h \<Delta>" 
    and "hcontains h v\<^sub>1"
  moreover have "p\<^sub>\<Delta> \<le> p\<^sub>\<Delta>'"
  proof (cases p\<^sub>\<Delta>)
    case (Suc pp)
    moreover with X A have "pp < p\<^sub>\<Delta>'" by simp
    ultimately show ?thesis by simp
  qed simp_all
  ultimately show ?thesis by auto
qed

lemma chain_structured_alloc_lam [simp]: "hcontains h v\<^sub>2 \<Longrightarrow> hlookup h v\<^sub>2 = Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C> \<Longrightarrow> 
  chained_closures \<Delta> h \<Longrightarrow> hcontains h v\<^sub>1 \<Longrightarrow> halloc \<Delta> (v\<^sub>1, p\<^sub>\<Delta>) = (\<Delta>', p\<^sub>\<Delta>') \<Longrightarrow> 
    chain_structured h \<Delta> \<Longrightarrow> chain_structured h \<Delta>'"
  using hlookup_all by fastforce

lemma chain_structured_unfold [simp]: "chain_structured h \<Delta> \<Longrightarrow> 
  heap_all (\<lambda>p (y, p'). p' \<le> p \<and> (y = x \<or> hcontains h y)) \<Delta>"
proof -
  have "\<And>a b. (\<lambda>p (v, p'). p' \<le> p \<and> hcontains h v) a b \<Longrightarrow> 
    (\<lambda>p (y, p'). p' \<le> p \<and> (y = x \<or> hcontains h y)) a b" by (simp split: prod.splits)
  moreover assume "chain_structured h \<Delta>"
  ultimately show "heap_all (\<lambda>p (y, p'). p' \<le> p \<and> (y = x \<or> hcontains h y)) \<Delta>"
    by (rule heap_all_implication)
qed

lemma eval_preserves_chained [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>v \<leadsto>\<^sub>v \<Sigma>\<^sub>v' \<Longrightarrow> chained_state \<Sigma>\<^sub>v \<Longrightarrow> chained_state \<Sigma>\<^sub>v'"
proof (induction \<Sigma>\<^sub>v \<Sigma>\<^sub>v' rule: eval\<^sub>v.induct)
  case (ev\<^sub>v_lookup \<C> p\<^sub>\<C> x y z \<Delta> p v h \<V> s)
  thus ?case by (cases p) auto
qed auto

lemma preserve_chained [simp]: "iter (\<tturnstile> \<C> \<leadsto>\<^sub>v) \<Sigma>\<^sub>v \<Sigma>\<^sub>v' \<Longrightarrow> chained_state \<Sigma>\<^sub>v \<Longrightarrow> chained_state \<Sigma>\<^sub>v'"
  by (induction \<Sigma>\<^sub>v \<Sigma>\<^sub>v' rule: iter.induct) simp_all

lemma correct\<^sub>v_iter [simp]: "iter (\<tturnstile> \<C> \<leadsto>\<^sub>h) (unchain_state \<Sigma>\<^sub>v) \<Sigma>\<^sub>h \<Longrightarrow> chained_state \<Sigma>\<^sub>v \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>v'. iter (\<tturnstile> \<C> \<leadsto>\<^sub>v) \<Sigma>\<^sub>v \<Sigma>\<^sub>v' \<and> \<Sigma>\<^sub>h = unchain_state \<Sigma>\<^sub>v'"
proof (induction "unchain_state \<Sigma>\<^sub>v" \<Sigma>\<^sub>h arbitrary: \<Sigma>\<^sub>v rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>h' \<Sigma>\<^sub>h'')
  moreover then obtain \<Sigma>\<^sub>v' where S: "(\<C> \<tturnstile> \<Sigma>\<^sub>v \<leadsto>\<^sub>v \<Sigma>\<^sub>v') \<and> \<Sigma>\<^sub>h' = unchain_state \<Sigma>\<^sub>v'" by fastforce
  moreover with iter_step have "chained_state \<Sigma>\<^sub>v'" by (metis eval_preserves_chained)
  ultimately obtain \<Sigma>\<^sub>v'' where "iter (\<tturnstile> \<C> \<leadsto>\<^sub>v) \<Sigma>\<^sub>v' \<Sigma>\<^sub>v'' \<and> \<Sigma>\<^sub>h'' = unchain_state \<Sigma>\<^sub>v''" by blast
  with S have "iter (\<tturnstile> \<C> \<leadsto>\<^sub>v) \<Sigma>\<^sub>v \<Sigma>\<^sub>v'' \<and> \<Sigma>\<^sub>h'' = unchain_state \<Sigma>\<^sub>v''" by fastforce
  then show ?case by fastforce
qed force+

end