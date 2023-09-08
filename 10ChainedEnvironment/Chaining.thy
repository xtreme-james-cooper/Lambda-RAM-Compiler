theory Chaining
  imports ChainedEnvironment "../09HeapMemory/HeapMemory"
begin

section \<open>Chaining environments\<close>

text \<open>Restoring environments from linked-list form is a matter of following the pointers down until 
we reach the end. To ensure termination, we use the environment-size map attached to each 
environment in the callstack and the value heap. (We could also use the fact that each pointer to a 
previously-allocated environment must point lower in the heap, and terminate that way; but the fact 
that the heap is arranged this way must be proved separately, whereas the finiteness of the size map
is statically apparent.)\<close>

fun unchain_env :: "('a list \<times> ptr) heap \<Rightarrow> ptr \<Rightarrow> nat list \<Rightarrow> 'a list list" where
  "unchain_env \<Delta> p [] = []"
| "unchain_env \<Delta> 0 (n # ns) = []"
| "unchain_env \<Delta> (Suc p) (n # ns) = (case hlookup \<Delta> p of 
      (vs, p') \<Rightarrow> take n vs # unchain_env \<Delta> p' ns)"

text \<open>We map the transformation through the whole evaluation state.\<close>

primrec unchain_closure :: "(ptr list \<times> ptr) heap \<Rightarrow> closure\<^sub>v \<Rightarrow> closure\<^sub>h" where
  "unchain_closure \<Delta> (Const\<^sub>v n) = Const\<^sub>h n"
| "unchain_closure \<Delta> (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C> ns) = Lam\<^sub>h (unchain_env \<Delta> p\<^sub>\<Delta> ns) p\<^sub>\<C>"

abbreviation unchain_heap :: "closure\<^sub>v heap \<Rightarrow> (ptr list \<times> ptr) heap \<Rightarrow> closure\<^sub>h heap" where
  "unchain_heap h \<Delta> \<equiv> hmap (unchain_closure \<Delta>) h"

fun unchain_frame :: "(ptr list \<times> ptr) heap \<Rightarrow> (ptr \<times> nat list \<times> nat) \<Rightarrow> (ptr list list \<times> nat)" 
    where
  "unchain_frame \<Delta> (p\<^sub>\<Delta>, ns, p\<^sub>\<C>) = (unchain_env \<Delta> p\<^sub>\<Delta> ns, p\<^sub>\<C>)"

abbreviation unchain_stack :: "(ptr list \<times> ptr) heap \<Rightarrow> (ptr \<times> nat list \<times> nat) list \<Rightarrow> 
    (ptr list list \<times> nat) list" where
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

lemma halloc_unchain_heap_lam [simp]: "halloc h (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C> ns) = (h', v) \<Longrightarrow> 
  halloc (unchain_heap h \<Delta>) (Lam\<^sub>h (unchain_env \<Delta> p\<^sub>\<Delta> ns) p\<^sub>\<C>) = (unchain_heap h' \<Delta>, v)"
proof -
  assume "halloc h (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C> ns) = (h', v)"
  hence "halloc (hmap (unchain_closure \<Delta>) h) (unchain_closure \<Delta> (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C> ns)) = 
    (hmap (unchain_closure \<Delta>) h', v)" by (metis halloc_map)
  thus ?thesis by simp
qed

text \<open>We define a set of predicates to verify that our two heaps point to each other correctly.\<close>

abbreviation chain_structured :: "closure\<^sub>v heap \<Rightarrow> (ptr list \<times> ptr) heap \<Rightarrow> bool" where
  "chain_structured h \<Delta> \<equiv> heap_all (\<lambda>p (vs, p'). p' \<le> p \<and> list_all (hcontains h) vs) \<Delta>"

primrec chained_heap_pointer :: "(ptr list \<times> ptr) heap \<Rightarrow> ptr \<Rightarrow> bool" where
  "chained_heap_pointer \<Delta> 0 = True"
| "chained_heap_pointer \<Delta> (Suc p) = hcontains \<Delta> p"

fun chained_frame :: "(ptr list \<times> ptr) heap \<Rightarrow> (ptr \<times> nat list \<times> nat) \<Rightarrow> bool" where
  "chained_frame \<Delta> (p\<^sub>\<Delta>, ns, p\<^sub>\<C>) = chained_heap_pointer \<Delta> p\<^sub>\<Delta>"

abbreviation chained_stack :: "(ptr list \<times> ptr) heap \<Rightarrow> (ptr \<times> nat list \<times> nat) list \<Rightarrow> bool" where
  "chained_stack \<Delta> s \<equiv> list_all (chained_frame \<Delta>) s"

abbreviation chained_vals :: "closure\<^sub>v heap \<Rightarrow> ptr list \<Rightarrow> bool" where
  "chained_vals h \<V> \<equiv> list_all (hcontains h) \<V>"

primrec chained_closure :: "(ptr list \<times> ptr) heap \<Rightarrow> closure\<^sub>v \<Rightarrow> bool" where
  "chained_closure \<Delta> (Const\<^sub>v n) = True"
| "chained_closure \<Delta> (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C> ns) = chained_heap_pointer \<Delta> p\<^sub>\<Delta>"

abbreviation chained_closures :: "(ptr list \<times> ptr) heap \<Rightarrow> closure\<^sub>v heap \<Rightarrow> bool" where
  "chained_closures \<Delta> h \<equiv> heap_all (\<lambda>p. chained_closure \<Delta>) h"

primrec chained_state :: "state\<^sub>v \<Rightarrow> bool" where
  "chained_state (S\<^sub>v h \<Delta> \<V> s) = (
    chain_structured h \<Delta> \<and> chained_closures \<Delta> h \<and> chained_vals h \<V> \<and> chained_stack \<Delta> s)"

lemma chained_heap_pointer_update [simp]: "chained_heap_pointer (hupdate \<Delta> p' v) p = 
    chained_heap_pointer \<Delta> p"
  by (induction p) simp_all

lemma chained_heap_pointer_unfold [elim]: "hcontains \<Delta> p \<Longrightarrow> p' \<le> p \<Longrightarrow> chained_heap_pointer \<Delta> p'"
  by (induction p') auto

(*
lemma lookup_unchain_env [simp]: "chain_structured h \<Delta> \<Longrightarrow> chained_heap_pointer \<Delta> p \<Longrightarrow>
  Option.bind (lookup (unchain_env \<Delta> p ns) x) (\<lambda>vs. lookup vs y) = chain_lookup \<Delta> p x y"
proof (induction \<Delta> p ns rule: unchain_env.induct)
  case (3 \<Delta> p x)
  obtain v p' where V: "hlookup \<Delta> p = (v, p')" by (cases "hlookup \<Delta> p")
  from 3 have "hcontains \<Delta> p" by auto
  with 3 V have P: "p' \<le> p" using hlookup_all by fast
  with 3 V have "chained_heap_pointer \<Delta> p'" by auto
  with 3(1, 2) V P show ?case by fastforcex
qed (simp_all split: prod.splits)
*)

lemma halloc_unchain_env [simp]: "chain_structured h \<Delta> \<Longrightarrow> chained_heap_pointer \<Delta> p \<Longrightarrow> 
  halloc \<Delta> a = (\<Delta>', b) \<Longrightarrow> unchain_env \<Delta>' p ns = unchain_env \<Delta> p ns" 
proof (induction \<Delta> p ns rule: unchain_env.induct)
  case (3 \<Delta> p n ns)
  obtain vs p' where H: "hlookup \<Delta> p = (vs, p')" by fastforce
  with 3(2, 3) have "p' \<le> p \<and> list_all (hcontains h) vs" using hlookup_all by fastforce
  with 3 have "chained_heap_pointer \<Delta> p'" by auto
  with 3 H show ?case by simp
qed simp_all

lemma halloc_unchain_heap [elim]: "chain_structured h \<Delta> \<Longrightarrow> chained_closures \<Delta> h \<Longrightarrow> 
  halloc \<Delta> v = (\<Delta>', p) \<Longrightarrow> unchain_heap h \<Delta>' = unchain_heap h \<Delta>"
proof (rule hmap_eq)
  fix x
  assume S: "chain_structured h \<Delta>" and C: "chained_closures \<Delta> h" 
    and A: "halloc \<Delta> v = (\<Delta>', p)" and X: "hcontains h x"
  show "unchain_closure \<Delta>' (hlookup h x) = unchain_closure \<Delta> (hlookup h x)" 
  proof (cases "hlookup h x")
    case (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C> ns)
    with C X have "chained_closure \<Delta> (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C> ns)" by (metis hlookup_all)
    with S A Lam\<^sub>v show ?thesis by auto
  qed simp_all
qed

lemma unfold_unstack_list [simp]: "chain_structured h \<Delta> \<Longrightarrow> chained_heap_pointer \<Delta> p \<Longrightarrow> 
  halloc \<Delta> (vs, p) = (\<Delta>', p') \<Longrightarrow> 
    unchain_env \<Delta>' (Suc p') (n # ns) = take n vs # unchain_env \<Delta> p ns"
proof -
  assume A: "chain_structured h \<Delta>"
  assume B: "chained_heap_pointer \<Delta> p"
  assume C: "halloc \<Delta> (vs, p) = (\<Delta>', p')"
  moreover with A B have "unchain_env \<Delta>' p ns = unchain_env \<Delta> p ns" by simp
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
  case (ev\<^sub>v_lookup \<C> p\<^sub>\<C> x y \<Delta> p\<^sub>\<Delta> v h \<V> ns s)
  from ev\<^sub>v_lookup have "lookup \<C> p\<^sub>\<C> = Some (Lookup\<^sub>b x y)" by simp
  from ev\<^sub>v_lookup have "chain_lookup \<Delta> p\<^sub>\<Delta> x y = Some v" by simp
  from ev\<^sub>v_lookup have "chain_structured h \<Delta> \<and> chained_closures \<Delta> h \<and> chained_vals h \<V> \<and> 
    chained_heap_pointer \<Delta> p\<^sub>\<Delta> \<and> chained_stack \<Delta> s" by simp

  from ev\<^sub>v_lookup have "lookup (unchain_env \<Delta> p\<^sub>\<Delta> ns) x = Some vs \<Longrightarrow> 
    lookup vs y = Some v \<Longrightarrow>
        \<C> \<tturnstile> S\<^sub>h (unchain_heap h \<Delta>) \<V> ((unchain_env \<Delta> p\<^sub>\<Delta> ns, Suc p\<^sub>\<C>) # unchain_stack \<Delta> s) \<leadsto>\<^sub>h 
    S\<^sub>h (unchain_heap h \<Delta>) (v # \<V>) ((unchain_env \<Delta> p\<^sub>\<Delta> ns, p\<^sub>\<C>) # unchain_stack \<Delta> s)" by simp

  have "\<C> \<tturnstile> S\<^sub>h (unchain_heap h \<Delta>) \<V> ((unchain_env \<Delta> p\<^sub>\<Delta> ns, Suc p\<^sub>\<C>) # unchain_stack \<Delta> s) \<leadsto>\<^sub>h
    S\<^sub>h (unchain_heap h \<Delta>) (v # \<V>) ((unchain_env \<Delta> p\<^sub>\<Delta> ns, p\<^sub>\<C>) # unchain_stack \<Delta> s)" by simp
  with ev\<^sub>v_lookup show ?case by simp
next
  case (ev\<^sub>v_alloc \<C> p\<^sub>\<C> n \<Delta> p\<^sub>\<Delta> vs p\<^sub>\<Delta>' h \<V> s)
  then show ?case by simp
next
  case (ev\<^sub>v_apply \<C> p\<^sub>\<C> h\<^sub>v v\<^sub>2 p\<^sub>\<Delta>' p\<^sub>\<C>' ns \<Delta>\<^sub>v v\<^sub>1 \<Delta>\<^sub>v' p\<^sub>\<Delta>'' \<V> p\<^sub>\<Delta> s\<^sub>v)
  from ev\<^sub>v_apply have "chained_closures \<Delta>\<^sub>v h\<^sub>v \<and> hcontains h\<^sub>v v\<^sub>2" by simp
  with ev\<^sub>v_apply have "chained_closure \<Delta>\<^sub>v (Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>' ns)" by (metis hlookup_all)
  with ev\<^sub>v_apply have "chain_structured h\<^sub>v \<Delta>\<^sub>v \<and> chained_heap_pointer \<Delta>\<^sub>v p\<^sub>\<Delta>' \<and> 
    halloc \<Delta>\<^sub>v ([v\<^sub>1], p\<^sub>\<Delta>') = (\<Delta>\<^sub>v', p\<^sub>\<Delta>'')" by auto
  hence X: "unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>'') (Suc 0 # ns) = [v\<^sub>1] # unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>' ns" 
    by (metis unfold_unstack_list take_0 take_Suc_Cons)
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
  case (ev\<^sub>v_pushenv \<C> p\<^sub>\<C> n \<Delta>\<^sub>v p\<^sub>\<Delta> vs p\<^sub>\<Delta>' h\<^sub>v v \<V> s\<^sub>v)
  from ev\<^sub>v_pushenv have A: "hlookup \<Delta>\<^sub>v p\<^sub>\<Delta> = (vs, p\<^sub>\<Delta>')" by simp
  from ev\<^sub>v_pushenv have B: "chain_structured h\<^sub>v \<Delta>\<^sub>v" by simp
  from ev\<^sub>v_pushenv have "chained_closures \<Delta>\<^sub>v h\<^sub>v" by simp
  from ev\<^sub>v_pushenv have "hcontains h\<^sub>v v" by simp
  from ev\<^sub>v_pushenv have "chained_vals h\<^sub>v \<V>" by simp
  from ev\<^sub>v_pushenv have C: "hcontains \<Delta>\<^sub>v p\<^sub>\<Delta>" by simp
  from ev\<^sub>v_pushenv have "chained_stack \<Delta>\<^sub>v s\<^sub>v" by simp


  from ev\<^sub>v_pushenv have P: "p\<^sub>\<Delta>' \<le> p\<^sub>\<Delta>" using hlookup_all by fastforce



  have Y: "unchain_stack (hupdate \<Delta>\<^sub>v p\<^sub>\<Delta> (vs @ [v], p\<^sub>\<Delta>')) s\<^sub>v = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by simp
  from ev\<^sub>v_pushenv have "\<C> \<tturnstile> S\<^sub>h (unchain_heap h\<^sub>v \<Delta>\<^sub>v) (v # \<V>) ((vs # unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>', Suc p\<^sub>\<C>) # 
    unchain_stack \<Delta>\<^sub>v s\<^sub>v) \<leadsto>\<^sub>h 
      S\<^sub>h (unchain_heap h\<^sub>v \<Delta>\<^sub>v) \<V> ((snoc_fst v (vs # unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>'), p\<^sub>\<C>) # unchain_stack \<Delta>\<^sub>v s\<^sub>v)" 
    by (metis ev\<^sub>h_pushenv)
  with ev\<^sub>v_pushenv P show ?case by (simp add: Y)
next
  case (ev\<^sub>v_jump \<C> p\<^sub>\<C> h\<^sub>v v\<^sub>2 p\<^sub>\<Delta>' p\<^sub>\<C>' \<Delta>\<^sub>v v\<^sub>1 \<Delta>\<^sub>v' p\<^sub>\<Delta>'' \<V> p\<^sub>\<Delta> s\<^sub>v)
  from ev\<^sub>v_jump have "chained_closures \<Delta>\<^sub>v h\<^sub>v \<and> hcontains h\<^sub>v v\<^sub>2" by simp
  with ev\<^sub>v_jump have "chained_closure \<Delta>\<^sub>v (Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>')" by (metis hlookup_all)
  with ev\<^sub>v_jump have "chain_structured h\<^sub>v \<Delta>\<^sub>v \<and> chained_heap_pointer \<Delta>\<^sub>v p\<^sub>\<Delta>' \<and> 
    halloc \<Delta>\<^sub>v ([v\<^sub>1], p\<^sub>\<Delta>') = (\<Delta>\<^sub>v', p\<^sub>\<Delta>'')" by auto
  hence X: "unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>'') = [v\<^sub>1] # unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>'" by (metis unfold_unstack_list)
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
  case (ev\<^sub>h_lookup \<C> p\<^sub>\<C> x y \<Delta>\<^sub>h vs v h\<^sub>h \<V> s\<^sub>h)
  then obtain h\<^sub>v \<Delta>\<^sub>v s\<^sub>v' where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V> s\<^sub>v' \<and> h\<^sub>h = unchain_heap h\<^sub>v \<Delta>\<^sub>v \<and> 
    (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) # s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v'" by fastforce
  then obtain f\<^sub>v s\<^sub>v where SF: "s\<^sub>v' = f\<^sub>v # s\<^sub>v \<and> (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) = unchain_frame \<Delta>\<^sub>v f\<^sub>v \<and> 
    s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by auto
  then obtain p\<^sub>\<Delta> where P: "f\<^sub>v = (p\<^sub>\<Delta>, Suc p\<^sub>\<C>) \<and> \<Delta>\<^sub>h = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by (cases f\<^sub>v) simp_all
  with ev\<^sub>h_lookup S SF have C: "chain_structured h\<^sub>v \<Delta>\<^sub>v" by simp
  with ev\<^sub>h_lookup S SF P have X: "S\<^sub>h h\<^sub>h (v # \<V>) ((\<Delta>\<^sub>h, p\<^sub>\<C>) # s\<^sub>h) = 
    unchain_state (S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v # \<V>) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v))" by simp
  from ev\<^sub>h_lookup S SF P have "chained_heap_pointer \<Delta>\<^sub>v p\<^sub>\<Delta>" by simp
  with C have "Option.bind (lookup (unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>) x) (\<lambda>vs. lookup vs y) = 
    chain_lookup \<Delta>\<^sub>v p\<^sub>\<Delta> x y" by simp
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
  case (ev\<^sub>h_pushlam \<C> p\<^sub>\<C> p\<^sub>\<C>' h\<^sub>h \<Delta>\<^sub>h h\<^sub>h' v \<V> s\<^sub>h)
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
  case (ev\<^sub>h_alloc \<C> p n h \<V> \<Delta> s)
  then show ?case by simp
next
  case (ev\<^sub>h_apply \<C> p\<^sub>\<C> h\<^sub>h v\<^sub>2 \<Delta>\<^sub>h' p\<^sub>\<C>' v\<^sub>1 \<V> \<Delta>\<^sub>h s\<^sub>h)
  then obtain h\<^sub>v \<Delta>\<^sub>v s\<^sub>v' where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>1 # v\<^sub>2 # \<V>) s\<^sub>v' \<and> 
    h\<^sub>h = unchain_heap h\<^sub>v \<Delta>\<^sub>v \<and> (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) # s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v'" by fastforce
  then obtain f\<^sub>v s\<^sub>v where SF: "s\<^sub>v' = f\<^sub>v # s\<^sub>v \<and> (\<Delta>\<^sub>h, Suc p\<^sub>\<C>) = unchain_frame \<Delta>\<^sub>v f\<^sub>v \<and> 
    s\<^sub>h = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by auto
  then obtain p\<^sub>\<Delta> where P: "f\<^sub>v = (p\<^sub>\<Delta>, Suc p\<^sub>\<C>) \<and> \<Delta>\<^sub>h = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by (cases f\<^sub>v) simp_all
  from ev\<^sub>h_apply S have "Lam\<^sub>h \<Delta>\<^sub>h' p\<^sub>\<C>' = unchain_closure \<Delta>\<^sub>v (hlookup h\<^sub>v v\<^sub>2)" by simp
  then obtain p\<^sub>\<Delta>' where P': "hlookup h\<^sub>v v\<^sub>2 = Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>' \<and> \<Delta>\<^sub>h' = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>'" by blast
  obtain \<Delta>\<^sub>v' p\<^sub>\<Delta>'' where H: "halloc \<Delta>\<^sub>v ([v\<^sub>1], p\<^sub>\<Delta>') = (\<Delta>\<^sub>v', p\<^sub>\<Delta>'')" 
    by (cases "halloc \<Delta>\<^sub>v ([v\<^sub>1], p\<^sub>\<Delta>')") simp_all
  from ev\<^sub>h_apply S SF P have C: "chain_structured h\<^sub>v \<Delta>\<^sub>v \<and> chained_closures \<Delta>\<^sub>v h\<^sub>v \<and>
    hcontains h\<^sub>v v\<^sub>1 \<and> hcontains h\<^sub>v v\<^sub>2 \<and> chained_vals h\<^sub>v \<V> \<and> chained_frame \<Delta>\<^sub>v (p\<^sub>\<Delta>, Suc p\<^sub>\<C>) \<and> 
      chained_stack \<Delta>\<^sub>v s\<^sub>v" by simp
  with H have Y: "unchain_heap h\<^sub>v \<Delta>\<^sub>v' = unchain_heap h\<^sub>v \<Delta>\<^sub>v" by fast
  from H C have "unchain_env \<Delta>\<^sub>v' p\<^sub>\<Delta> = unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>" by fastforce
  with P have W: "\<Delta>\<^sub>h = unchain_env \<Delta>\<^sub>v' p\<^sub>\<Delta>" by metis
  from P' C have "chained_closure \<Delta>\<^sub>v (Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>')" by (metis hlookup_all)
  hence "chained_heap_pointer \<Delta>\<^sub>v p\<^sub>\<Delta>'" by auto
  with H C have "unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>'') = [v\<^sub>1] # unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>'" 
    by (metis unfold_unstack_list)
  with H P' have Z: "[v\<^sub>1] # \<Delta>\<^sub>h' = unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>'')" by simp
  from H C have "unchain_stack \<Delta>\<^sub>v' s\<^sub>v = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by fast
  with SF have "s\<^sub>h = unchain_stack \<Delta>\<^sub>v' s\<^sub>v" by simp
  with S Y Z W have X: "S\<^sub>h h\<^sub>h \<V> (([v\<^sub>1] # \<Delta>\<^sub>h', p\<^sub>\<C>') # (\<Delta>\<^sub>h, p\<^sub>\<C>) # s\<^sub>h) = 
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

  obtain vs p\<^sub>\<Delta>' where H: "hlookup \<Delta>\<^sub>v p\<^sub>\<Delta> = (vs, p\<^sub>\<Delta>')" by fastforce

  from ev\<^sub>h_pushenv H have X: "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v # \<V>) ((Suc p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v 
      S\<^sub>v h\<^sub>v (hupdate \<Delta>\<^sub>v p\<^sub>\<Delta> (vs @ [v], p\<^sub>\<Delta>')) \<V> ((Suc p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v)" by simp

  have Y: "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v # \<V>) ((p\<^sub>\<Delta>, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>v (hupdate \<Delta>\<^sub>v p\<^sub>\<Delta> (vs @ [v], p\<^sub>\<Delta>')) \<V> ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v)" by simp


  have "S\<^sub>h h\<^sub>h \<V> ((snoc_fst v \<Delta>\<^sub>h, p\<^sub>\<C>) # s\<^sub>h) =
    S\<^sub>h (unchain_heap h\<^sub>v (hupdate \<Delta>\<^sub>v p\<^sub>\<Delta> (vs @ [v], p\<^sub>\<Delta>'))) \<V>
     (unchain_stack (hupdate \<Delta>\<^sub>v p\<^sub>\<Delta> (vs @ [v], p\<^sub>\<Delta>')) ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v))" by simp
  have "S\<^sub>h h\<^sub>h \<V> ((snoc_fst v \<Delta>\<^sub>h, p\<^sub>\<C>) # s\<^sub>h) = 
    unchain_state (S\<^sub>v h\<^sub>v (hupdate \<Delta>\<^sub>v p\<^sub>\<Delta> (vs @ [v], p\<^sub>\<Delta>')) \<V> ((p\<^sub>\<Delta>, p\<^sub>\<C>) # s\<^sub>v))" 
      by (simp only: unchain_state.simps)
  with S SF P Y show ?case by blast
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
  obtain \<Delta>\<^sub>v' p\<^sub>\<Delta>'' where H: "halloc \<Delta>\<^sub>v ([v\<^sub>1], p\<^sub>\<Delta>') = (\<Delta>\<^sub>v', p\<^sub>\<Delta>'')" 
    by (cases "halloc \<Delta>\<^sub>v ([v\<^sub>1], p\<^sub>\<Delta>')") simp_all
  from ev\<^sub>h_jump S SF P have C: "chain_structured h\<^sub>v \<Delta>\<^sub>v \<and> chained_closures \<Delta>\<^sub>v h\<^sub>v \<and>
    hcontains h\<^sub>v v\<^sub>1 \<and> hcontains h\<^sub>v v\<^sub>2 \<and> chained_vals h\<^sub>v \<V> \<and> chained_heap_pointer \<Delta>\<^sub>v p\<^sub>\<Delta> \<and> 
      chained_stack \<Delta>\<^sub>v s\<^sub>v" by simp
  with H have Y: "unchain_heap h\<^sub>v \<Delta>\<^sub>v' = unchain_heap h\<^sub>v \<Delta>\<^sub>v" by fast
  from P' C have "chained_closure \<Delta>\<^sub>v (Lam\<^sub>v p\<^sub>\<Delta>' p\<^sub>\<C>')" by (metis hlookup_all)
  hence "chained_heap_pointer \<Delta>\<^sub>v p\<^sub>\<Delta>'" by simp
  with H C have "unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>'') = [v\<^sub>1] # unchain_env \<Delta>\<^sub>v p\<^sub>\<Delta>'" 
    by (metis unfold_unstack_list)
  with H P' have Z: "[v\<^sub>1] # \<Delta>\<^sub>h' = unchain_env \<Delta>\<^sub>v' (Suc p\<^sub>\<Delta>'')" by simp
  from H C have "unchain_stack \<Delta>\<^sub>v' s\<^sub>v = unchain_stack \<Delta>\<^sub>v s\<^sub>v" by fast
  with SF have "s\<^sub>h = unchain_stack \<Delta>\<^sub>v' s\<^sub>v" by simp
  with S Y Z have X: "S\<^sub>h h\<^sub>h \<V> (([v\<^sub>1] # \<Delta>\<^sub>h', p\<^sub>\<C>') # s\<^sub>h) = 
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

lemma halloc_chained_closure [simp]: "halloc \<Delta> v = (\<Delta>', p) \<Longrightarrow> chained_closure \<Delta> c \<Longrightarrow> 
    chained_closure \<Delta>' c"
  by (induction c) simp_all

lemma halloc_chained_closures [simp]: "halloc \<Delta> v = (\<Delta>', p) \<Longrightarrow> chained_closures \<Delta> h \<Longrightarrow> 
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
  hlookup \<Delta> p = (a, b) \<Longrightarrow> list_all (hcontains h) a"
proof -
  assume "chain_structured h \<Delta>" and "hcontains \<Delta> p" and "hlookup \<Delta> p = (a, b)"
  hence "(\<lambda>(vs, p'). p' \<le> p \<and> list_all (hcontains h) vs) (a, b)" by (metis hlookup_all)
  thus ?thesis by simp
qed

lemma chain_lookup_hcontains [elim]: "chain_structured h \<Delta> \<Longrightarrow> hcontains \<Delta> p \<Longrightarrow> 
  chain_lookup \<Delta> p x y = Some v \<Longrightarrow> hcontains h v"
proof (induction \<Delta> p x y rule: chain_lookup.induct)
  case (2 \<Delta> p y)
  obtain vs b where V: "hlookup \<Delta> p = (vs, b)" by fastforce
  from 2 have "hcontains \<Delta> p" by auto
  with 2 V have "b \<le> p \<and> list_all (hcontains h) vs" using hlookup_all by fastforce
  with 2 V show ?case by auto
next
  case (3 \<Delta> p x y)
  obtain a b where A: "hlookup \<Delta> p = (a, b)" by (cases "hlookup \<Delta> p")
  from 3 have "hcontains \<Delta> p" by auto
  with 3 A have "b \<le> p \<and> list_all (hcontains h) a" using hlookup_all by fast
  with 3 have "hcontains \<Delta> b" by fastforce
  with 3 A show ?case by simp
qed simp_all

lemma chain_lookup_suc_hcontains [elim]: "chain_lookup \<Delta> (Suc p) x y = Some v \<Longrightarrow> 
  chain_structured h \<Delta> \<Longrightarrow> hcontains \<Delta> p \<Longrightarrow> hcontains h v"
proof (induction \<Delta> "Suc p" x y arbitrary: p rule: chain_lookup.induct)
  case (2 \<Delta> p y)
  moreover obtain vs b where V: "hlookup \<Delta> p = (vs, b)" by fastforce
  moreover with 2 have "b \<le> p \<and> list_all (hcontains h) vs" using hlookup_all by fastforce
  ultimately show ?case by auto
next
  case (3 \<Delta> p x)
  moreover obtain a b where A: "hlookup \<Delta> p = (a, b)" by fastforce
  moreover with 3 have "b \<le> p \<and> list_all (hcontains h) a" using hlookup_all by fastforce
  ultimately show ?case by auto
qed

lemma chain_structured_alloc [simp]: "chained_heap_pointer \<Delta> p\<^sub>\<Delta> \<Longrightarrow> hcontains h v\<^sub>1 \<Longrightarrow> 
  halloc \<Delta> ([v\<^sub>1], p\<^sub>\<Delta>) = (\<Delta>', p\<^sub>\<Delta>') \<Longrightarrow> chain_structured h \<Delta> \<Longrightarrow> chain_structured h \<Delta>'"
proof -
  assume X: "chained_heap_pointer \<Delta> p\<^sub>\<Delta>"
  moreover assume A: "halloc \<Delta> ([v\<^sub>1], p\<^sub>\<Delta>) = (\<Delta>', p\<^sub>\<Delta>')" and "chain_structured h \<Delta>" 
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
  chained_closures \<Delta> h \<Longrightarrow> hcontains h v\<^sub>1 \<Longrightarrow> halloc \<Delta> ([v\<^sub>1], p\<^sub>\<Delta>) = (\<Delta>', p\<^sub>\<Delta>') \<Longrightarrow> 
    chain_structured h \<Delta> \<Longrightarrow> chain_structured h \<Delta>'"
  using hlookup_all by fastforce

lemma chain_structured_alloc2 [simp]: "halloc h v = (h', p\<^sub>h) \<Longrightarrow> chain_structured h \<Delta> \<Longrightarrow> 
    chain_structured h' \<Delta>"
proof -
  define p where "p = (\<lambda>(x::nat) (vs, y). y \<le> x \<and> list_all (hcontains h) vs)"
  define q where "q = (\<lambda>(x::nat) (vs, y). y \<le> x \<and> list_all (hcontains h') vs)"
  assume H: "halloc h v = (h', p\<^sub>h)" 
  assume "chain_structured h \<Delta>" 
  hence "heap_all p \<Delta>" by (simp add: p_def)
  moreover from H have "\<And>x y. p x y \<Longrightarrow> q x y" by (simp add: p_def q_def split: prod.splits)
  ultimately have "heap_all q \<Delta>" by (metis heap_all_implication)
  thus ?thesis by (simp add: q_def)
qed

lemma chained_closure_update [simp]: "chained_closure (hupdate \<Delta> x v') v = chained_closure \<Delta> v"
  by (induction v) simp_all

lemma chained_frame_update [simp]: "chained_frame (hupdate \<Delta> x v') f = chained_frame \<Delta> f"
  by (induction f) simp_all

lemma eval_preserves_chained [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>v \<leadsto>\<^sub>v \<Sigma>\<^sub>v' \<Longrightarrow> chained_state \<Sigma>\<^sub>v \<Longrightarrow> chained_state \<Sigma>\<^sub>v'"
proof (induction \<Sigma>\<^sub>v \<Sigma>\<^sub>v' rule: eval\<^sub>v.induct)
  case (ev\<^sub>v_lookup \<C> p\<^sub>\<C> x y \<Delta> p\<^sub>\<Delta> v h \<V> s)
  thus ?case by (cases p\<^sub>\<Delta>) auto
next
  case (ev\<^sub>v_alloc \<C> p\<^sub>\<C> n \<Delta> p\<^sub>\<Delta> vs p\<^sub>\<Delta>' h \<V> s)
  then show ?case by simp
next
  case (ev\<^sub>v_pushenv \<C> p\<^sub>\<C> \<Delta> p\<^sub>\<Delta> vs p\<^sub>\<Delta>' h v \<V> s)
  hence P: "p\<^sub>\<Delta>' \<le> p\<^sub>\<Delta> \<and> list_all (hcontains h) vs" using hlookup_all by fastforce
  have "\<And>y. chained_closure \<Delta> y \<Longrightarrow> chained_closure (hupdate \<Delta> p\<^sub>\<Delta> (vs @ [v], p\<^sub>\<Delta>')) y" by simp
  moreover from ev\<^sub>v_pushenv have "heap_all (\<lambda>p. chained_closure \<Delta>) h" by simp
  ultimately have X: "heap_all (\<lambda>p. chained_closure (hupdate \<Delta> p\<^sub>\<Delta> (vs @ [v], p\<^sub>\<Delta>'))) h" 
    using heap_all_implication by metis
  from ev\<^sub>v_pushenv have "list_all (chained_frame (hupdate \<Delta> p\<^sub>\<Delta> (vs @ [v], p\<^sub>\<Delta>'))) s" 
    by (induction s) simp_all
  with ev\<^sub>v_pushenv P X show ?case by simp
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