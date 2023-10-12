theory MemoryFlattening                   
  imports FlatMemory "../09HeapMemory/HeapConversion" "../10ChainedEnvironment/Chaining"
begin

subsection \<open>Memory Flattening\<close>

text \<open>The conversion here can almost go either direction - any (valid) flat state
is equivalent to exactly one chained state, except for the environment size lists stored in the 
stack. Fortunately, to make correctness the simpler proof (and avoid having to define a validity 
predicate), we would have preferred to define the conversion running forward anyways.\<close>

primrec flatten_closure :: "(ptr \<Rightarrow> ptr) \<Rightarrow> closure\<^sub>v \<Rightarrow> (pointer_tag \<times> nat) list" where
  "flatten_closure m (Const\<^sub>v n) = [(PConst, n), (PConst, 0)]"
| "flatten_closure m (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C> ns) = [(PEnv, m p\<^sub>\<Delta>), (PCode, p\<^sub>\<C>)]"

abbreviation flatten_values :: "(ptr \<Rightarrow> ptr) \<Rightarrow> closure\<^sub>v heap \<Rightarrow> (pointer_tag \<times> nat) heap" where
  "flatten_values m h \<equiv> hsplay (flatten_closure m) h"

primrec flatten_env :: "(ptr \<Rightarrow> ptr) \<Rightarrow> (ptr list \<times> ptr) \<Rightarrow> ptr list" where
  "flatten_env m (p\<^sub>h, p\<^sub>\<Delta>) = m p\<^sub>\<Delta> # map ((*) 2) p\<^sub>h"

primrec memory_map :: "(ptr list \<times> ptr) heap \<Rightarrow> ptr \<Rightarrow> ptr" where
  "memory_map \<Delta> 0 = 0"
| "memory_map \<Delta> (Suc x) = Suc (hsplay_map (flatten_env id) \<Delta> x)"

abbreviation flatten_environment :: "(ptr \<Rightarrow> ptr) \<Rightarrow> (ptr list \<times> ptr) heap \<Rightarrow> ptr heap" where
  "flatten_environment m \<Delta> \<equiv> hsplay (flatten_env m) \<Delta>"

abbreviation flatten_vals :: "ptr list \<Rightarrow> ptr list" where
  "flatten_vals \<V> \<equiv> map ((*) 2) \<V>"

fun flatten_frame :: "(ptr \<Rightarrow> ptr) \<Rightarrow> (ptr \<times> nat list \<times> nat) \<Rightarrow> nat list" where
  "flatten_frame m (p\<^sub>\<Delta>, ns, p\<^sub>\<C>) = [p\<^sub>\<C>, m p\<^sub>\<Delta>]"

abbreviation flatten_stack :: "(ptr \<Rightarrow> ptr) \<Rightarrow> (ptr \<times> nat list \<times> nat) list \<Rightarrow> nat list" where
  "flatten_stack m s \<equiv> concat (map (flatten_frame m) s)"

primrec flatten :: "state\<^sub>v \<Rightarrow> state\<^sub>f" where
  "flatten (S\<^sub>v h \<Delta> \<V> s) = 
    S\<^sub>f (flatten_values (memory_map \<Delta>) h) (flatten_environment (memory_map \<Delta>) \<Delta>) (flatten_vals \<V>) 
      (flatten_stack (memory_map \<Delta>) s)"

lemma length_flat_closure [simp]: "length (flatten_closure m c) = 2"
  by (induction c) simp_all

lemma lookup_flat_closure_0 [simp]: "hcontains h v \<Longrightarrow> hlookup (flatten_values m h) (2 * v) = 
  (case hlookup h v of Lam\<^sub>v p\<^sub>\<Delta> _ _ \<Rightarrow> (PEnv, m p\<^sub>\<Delta>) | Const\<^sub>v n \<Rightarrow> (PConst, n))"
proof -
  assume "hcontains h v"
  moreover have "(0::nat) < 2" by simp
  moreover have "\<And>a. length (flatten_closure m a) = 2 \<and> 
    flatten_closure m a ! 0 = (case a of Lam\<^sub>v p\<^sub>\<Delta> _ _ \<Rightarrow> (PEnv, m p\<^sub>\<Delta>) | Const\<^sub>v n \<Rightarrow> (PConst, n))"
      by (simp split: closure\<^sub>v.splits)
  ultimately show ?thesis by (metis (mono_tags, lifting) hlookup_hsplay add.left_neutral)
qed

lemma lookup_flat_closure_1 [simp]: "hcontains h v \<Longrightarrow> hlookup (flatten_values m h) (Suc (2 * v)) = 
  (case hlookup h v of Lam\<^sub>v _ p\<^sub>\<C> _ \<Rightarrow> (PCode, p\<^sub>\<C>) | Const\<^sub>v _ \<Rightarrow> (PConst, 0))"
proof -
  assume "hcontains h v"
  moreover have "(1::nat) < 2" by simp
  moreover have "\<And>a. length (flatten_closure m a) = 2 \<and> 
    flatten_closure m a ! 1 = (case a of Lam\<^sub>v _ p\<^sub>\<C> _ \<Rightarrow> (PCode, p\<^sub>\<C>) | Const\<^sub>v _ \<Rightarrow> (PConst, 0))"
      by (simp split: closure\<^sub>v.splits)
  ultimately show ?thesis by (metis hlookup_hsplay plus_1_eq_Suc Suc_1)
qed

lemma length_flat_env [simp]: "length (flatten_env m e) = Suc (length (fst e))"
  by (induction e) simp_all

lemma flatten_env_0 [simp]: "(flatten_env m e ! 0) = m (snd e)"
  by (induction e) simp_all

lemma memory_map_indifferent [simp]: "hsplay_map (flatten_env (memory_map \<Delta>')) \<Delta> p = 
    hsplay_map (flatten_env id) \<Delta> p"
  by (induction p) simp_all

text \<open>Most of the facts for correctness are simple and self-contained, but the relation between 
\<open>flat_lookup\<close> and \<open>chain_lookup\<close> requires that all pointers followed be contained in the heap. 
Fortunately, we already have this property from the previous stage: \<open>chain_structured\<close> is exactly 
what we need. This does mean we need to use \<open>chained_state\<close> as a well-formedness condition in our 
completeness and correctness theorems, though.\<close>

lemma flat_chained_lookup [simp]: "chained_heap_pointer \<Delta> p \<Longrightarrow> chain_structured h \<Delta> \<Longrightarrow> 
  chain_lookup \<Delta> p x y = Some p' \<Longrightarrow>
    flat_lookup (flatten_environment (memory_map \<Delta>) \<Delta>) (memory_map \<Delta> p) x y = Some (2 * p')"
proof (induction \<Delta> p x y rule: chain_lookup.induct)
  case (2 \<Delta> p y)
  obtain vs pp where V: "hlookup \<Delta> p = (vs, pp)" by fastforce
  with 2 V have X: "Suc y < length (flatten_env (memory_map \<Delta>) (hlookup \<Delta> p))" by auto
  from 2 have Y: "hcontains \<Delta> p" by simp
  have "\<forall>z. 0 < length (flatten_env (memory_map \<Delta>) (hlookup \<Delta> z))" by simp
  with X Y have "hlookup (hsplay (flatten_env (memory_map \<Delta>)) \<Delta>) 
    (Suc y + hsplay_map (flatten_env (memory_map \<Delta>)) \<Delta> p) = 
      flatten_env (memory_map \<Delta>) (hlookup \<Delta> p) ! Suc y" by (metis hlookup_hsplay_map)
  with 2 V show ?case by (auto simp add: add.commute)
next
  case (3 \<Delta> p x y)
  obtain vs pp where V: "hlookup \<Delta> p = (vs, pp)" by fastforce
  from 3 have X: "hcontains \<Delta> p" by simp
  have Y: "0 < length (flatten_env (memory_map \<Delta>) (hlookup \<Delta> p))" by simp
  have "\<forall>z. 0 < length (flatten_env (memory_map \<Delta>) (hlookup \<Delta> z))" by simp
  with X Y have Z: "hlookup (hsplay (flatten_env (memory_map \<Delta>)) \<Delta>) 
    (0 + hsplay_map (flatten_env (memory_map \<Delta>)) \<Delta> p) = 
      flatten_env (memory_map \<Delta>) (hlookup \<Delta> p) ! 0" by (metis hlookup_hsplay_map)
  with V have "hlookup (flatten_environment (memory_map \<Delta>) \<Delta>) (hsplay_map (flatten_env id) \<Delta> p) =
    memory_map \<Delta> pp" by simp
  from 3 V have "pp \<le> p \<and> vs \<noteq> [] \<and> chained_vals h vs" using hlookup_all by fastforce
  with 3 have "chained_heap_pointer \<Delta> pp" by auto
  with 3 V Z show ?case by simp
qed simp_all

lemma flatten_halloc [simp]: "halloc h c = (h', v) \<Longrightarrow> 
    halloc_list (flatten_values m h) (flatten_closure m c) = (flatten_values m h', 2 * v)"
  by simp

lemma halloc_flatten_env [simp]: "halloc \<Delta> (vs, p) = (\<Delta>', p') \<Longrightarrow> 
  halloc_list (flatten_environment (memory_map \<Delta>) \<Delta>) (memory_map \<Delta> p # map ((*) 2) vs) = 
    (flatten_environment (memory_map \<Delta>) \<Delta>', hsplay_map (flatten_env id) \<Delta>' p')" 
proof -
  assume "halloc \<Delta> (vs, p) = (\<Delta>', p')"
  hence "halloc_list (hsplay (flatten_env (memory_map \<Delta>)) \<Delta>) 
    (flatten_env (memory_map \<Delta>) (vs, p)) = 
      (hsplay (flatten_env (memory_map \<Delta>)) \<Delta>', hsplay_map (flatten_env (memory_map \<Delta>)) \<Delta>' p')" 
        by (metis halloc_list_hsplay)
  thus ?thesis by simp
qed

theorem correct\<^sub>f [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>v \<leadsto>\<^sub>v \<Sigma>\<^sub>v' \<Longrightarrow> chained_state \<C> \<Sigma>\<^sub>v \<Longrightarrow> \<C> \<tturnstile> flatten \<Sigma>\<^sub>v \<leadsto>\<^sub>f flatten \<Sigma>\<^sub>v'" 
proof (induction \<Sigma>\<^sub>v \<Sigma>\<^sub>v' rule: eval\<^sub>v.induct)
  case (ev\<^sub>v_pushcon \<C> p\<^sub>\<C> n h h' v \<Delta> \<V> p\<^sub>\<Delta> ns s)
  moreover hence "halloc_list (hsplay (flatten_closure (memory_map \<Delta>)) h) 
    (flatten_closure (memory_map \<Delta>) (Const\<^sub>v n)) = (hsplay (flatten_closure (memory_map \<Delta>)) h', 
      hsplay_map (flatten_closure (memory_map \<Delta>)) h' v)" 
    by (metis halloc_list_hsplay)
  ultimately show ?case by simp
next
  case (ev\<^sub>v_pushlam \<C> p\<^sub>\<C> p\<^sub>\<C>' h p\<^sub>\<Delta> ns h' v \<Delta> \<V> s)
  moreover hence "halloc_list (hsplay (flatten_closure (memory_map \<Delta>)) h) 
    (flatten_closure (memory_map \<Delta>) (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>' ns)) = (hsplay (flatten_closure (memory_map \<Delta>)) h', 
      hsplay_map (flatten_closure (memory_map \<Delta>)) h' v)" 
    by (metis halloc_list_hsplay)
  ultimately show ?case by simp
next
  case (ev\<^sub>v_alloc \<C> p\<^sub>\<C> n \<Delta> p\<^sub>\<Delta> vs p\<^sub>\<Delta>' h \<V> ns s)
  hence "\<C> \<tturnstile> S\<^sub>f (flatten_values (memory_map \<Delta>) h) (flatten_environment (memory_map \<Delta>) \<Delta>) (flatten_vals \<V>) 
         (Suc p\<^sub>\<C> # memory_map \<Delta> p\<^sub>\<Delta> # flatten_stack (memory_map \<Delta>) s) \<leadsto>\<^sub>f 
    S\<^sub>f (flatten_values (memory_map \<Delta>) h) 
      (flatten_environment (memory_map \<Delta>) \<Delta>) 
      (flatten_vals \<V>) 
      (p\<^sub>\<C> # (memory_map \<Delta> p\<^sub>\<Delta> + n) # flatten_stack (memory_map \<Delta>) s)" by simp

  from ev\<^sub>v_alloc have "\<not> hcontains \<Delta> (Suc p\<^sub>\<Delta>)" by simp

  have "\<C> \<tturnstile> S\<^sub>f (flatten_values (memory_map \<Delta>) h) (flatten_environment (memory_map \<Delta>) \<Delta>) (flatten_vals \<V>)
         (Suc p\<^sub>\<C> # memory_map \<Delta> p\<^sub>\<Delta> # flatten_stack (memory_map \<Delta>) s) \<leadsto>\<^sub>f
    S\<^sub>f (flatten_values (memory_map (hupdate \<Delta> p\<^sub>\<Delta> (vs @ replicate n 0, p\<^sub>\<Delta>'))) h)
     (flatten_environment (memory_map (hupdate \<Delta> p\<^sub>\<Delta> (vs @ replicate n 0, p\<^sub>\<Delta>')))
       (hupdate \<Delta> p\<^sub>\<Delta> (vs @ replicate n 0, p\<^sub>\<Delta>')))
     (flatten_vals \<V>)
     (p\<^sub>\<C> #
      memory_map (hupdate \<Delta> p\<^sub>\<Delta> (vs @ replicate n 0, p\<^sub>\<Delta>')) p\<^sub>\<Delta> #
      flatten_stack (memory_map (hupdate \<Delta> p\<^sub>\<Delta> (vs @ replicate n 0, p\<^sub>\<Delta>'))) s)" by simp
  thus ?case by simp
next
  case (ev\<^sub>v_apply \<C> p\<^sub>\<C> h v\<^sub>2 p\<^sub>\<Delta>' p\<^sub>\<C>' ns' \<Delta> v\<^sub>1 \<Delta>' p\<^sub>\<Delta>'' \<V> p\<^sub>\<Delta> ns s)

  from ev\<^sub>v_apply have V2: "hcontains h v\<^sub>2" by simp
  moreover have "\<And>a. length (flatten_closure (memory_map \<Delta>) a) = 2 \<and> 
    flatten_closure (memory_map \<Delta>) a ! 0 = 
      (case a of Lam\<^sub>v p\<^sub>\<Delta> _ _ \<Rightarrow> (PEnv, memory_map \<Delta> p\<^sub>\<Delta>) | Const\<^sub>v n \<Rightarrow> (PConst, n))" 
    by (simp split: closure\<^sub>v.splits)
  ultimately have "hlookup (hsplay (flatten_closure (memory_map \<Delta>)) h) (0 + 2 * v\<^sub>2) = 
    (case hlookup h v\<^sub>2 of Lam\<^sub>v p\<^sub>\<Delta> _ _ \<Rightarrow> (PEnv, memory_map \<Delta> p\<^sub>\<Delta>) | Const\<^sub>v n \<Rightarrow> (PConst, n))"
      using hlookup_hsplay less_2_cases_iff by blast
  with ev\<^sub>v_apply have X: "hlookup (hsplay (flatten_closure (memory_map \<Delta>)) h) (2 * v\<^sub>2) = 
    (PEnv, memory_map \<Delta> p\<^sub>\<Delta>')" by simp

  
  have "\<And>a. length (flatten_closure (memory_map \<Delta>) a) = 2 \<and> 
    flatten_closure (memory_map \<Delta>) a ! Suc 0 = 
      (case a of Lam\<^sub>v _ p\<^sub>\<C> _ \<Rightarrow> (PCode, p\<^sub>\<C>) | Const\<^sub>v _ \<Rightarrow> (PConst, 0))" 
    by (simp split: closure\<^sub>v.splits)
  with V2 have "hlookup (hsplay (flatten_closure (memory_map \<Delta>)) h) (Suc 0 + 2 * v\<^sub>2) = 
    (case hlookup h v\<^sub>2 of Lam\<^sub>v _ p\<^sub>\<C> _ \<Rightarrow> (PCode, p\<^sub>\<C>) | Const\<^sub>v _ \<Rightarrow> (PConst, 0))" 
      using hlookup_hsplay less_2_cases_iff by blast
  with ev\<^sub>v_apply have Y: "hlookup (hsplay (flatten_closure (memory_map \<Delta>)) h) (Suc (2 * v\<^sub>2)) = 
    (PCode, p\<^sub>\<C>')" by simp



  have "halloc_list (flatten_environment (memory_map \<Delta>) \<Delta>) [2 * v\<^sub>1, memory_map \<Delta> p\<^sub>\<Delta>'] = 
      (flatten_environment (memory_map \<Delta>') \<Delta>', hsplay_map (flatten_env id) \<Delta>' p\<^sub>\<Delta>'')" by simp
  with ev\<^sub>v_apply X Y have "
        \<C> \<tturnstile> S\<^sub>f (flatten_values (memory_map \<Delta>) h) (flatten_environment (memory_map \<Delta>) \<Delta>) 
         (2 * v\<^sub>1 # 2 * v\<^sub>2 # flatten_vals \<V>) 
         (Suc p\<^sub>\<C> # memory_map \<Delta> p\<^sub>\<Delta> # flatten_stack (memory_map \<Delta>) s) \<leadsto>\<^sub>f 
    S\<^sub>f (flatten_values (memory_map \<Delta>) h) (flatten_environment (memory_map \<Delta>') \<Delta>') (flatten_vals \<V>) 
      (p\<^sub>\<C>' # Suc (hsplay_map (flatten_env id) \<Delta>' p\<^sub>\<Delta>'') # 
       p\<^sub>\<C> # memory_map \<Delta> p\<^sub>\<Delta> # flatten_stack (memory_map \<Delta>) s)" by simp

  hence "\<C> \<tturnstile> S\<^sub>f (flatten_values (memory_map \<Delta>) h) (flatten_environment (memory_map \<Delta>) \<Delta>)
         (2 * v\<^sub>1 # 2 * v\<^sub>2 # flatten_vals \<V>)
         (Suc p\<^sub>\<C> # memory_map \<Delta> p\<^sub>\<Delta> # flatten_stack (memory_map \<Delta>) s) \<leadsto>\<^sub>f
    S\<^sub>f (flatten_values (memory_map \<Delta>') h) (flatten_environment (memory_map \<Delta>') \<Delta>') (flatten_vals \<V>)
     (p\<^sub>\<C>' # Suc (hsplay_map (flatten_env id) \<Delta>' p\<^sub>\<Delta>'') #
      p\<^sub>\<C> # memory_map \<Delta>' p\<^sub>\<Delta> # flatten_stack (memory_map \<Delta>') s)" by simp
  thus ?case by simp
next
  case (ev\<^sub>v_pushenv \<C> p\<^sub>\<C> n \<Delta> p\<^sub>\<Delta> vs p\<^sub>\<Delta>' h v \<V> ns s)
  thus ?case try0 by simp
next
  case (ev\<^sub>v_jump \<C> p\<^sub>\<C> h v\<^sub>2 p\<^sub>\<Delta>' p\<^sub>\<C>' ns' \<Delta> v\<^sub>1 \<Delta>' p\<^sub>\<Delta>'' \<V> p\<^sub>\<Delta> ns s)
  thus ?case try0 by simp
qed auto

lemma correct\<^sub>f_iter [simp]: "iter (\<tturnstile> \<C> \<leadsto>\<^sub>v) \<Sigma>\<^sub>v \<Sigma>\<^sub>v' \<Longrightarrow> chained_state \<C> \<Sigma>\<^sub>v \<Longrightarrow>
  iter (\<tturnstile> \<C> \<leadsto>\<^sub>f) (flatten \<Sigma>\<^sub>v) (flatten \<Sigma>\<^sub>v')"
proof (induction \<Sigma>\<^sub>v \<Sigma>\<^sub>v' rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>v \<Sigma>\<^sub>v' \<Sigma>\<^sub>v'')
  hence "iter (\<tturnstile> \<C> \<leadsto>\<^sub>f) (flatten \<Sigma>\<^sub>v') (flatten \<Sigma>\<^sub>v'')" by simp
  moreover from iter_step have "\<C> \<tturnstile> flatten \<Sigma>\<^sub>v \<leadsto>\<^sub>f flatten \<Sigma>\<^sub>v'" by simp
  ultimately show ?case by simp
qed simp_all

text \<open>The simplicity of the conversion means our reconstruction lemmas are few and simple too.\<close>

lemma flatten_to_state [dest]: "S\<^sub>f h\<^sub>f \<Delta>\<^sub>f \<V>\<^sub>f s\<^sub>f = flatten \<Sigma>\<^sub>v \<Longrightarrow> 
  \<exists>h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v s\<^sub>v. \<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v s\<^sub>v \<and> h\<^sub>f = flatten_values h\<^sub>v \<and> \<Delta>\<^sub>f = flatten_environment \<Delta>\<^sub>v \<and> 
    \<V>\<^sub>f = flatten_vals \<V>\<^sub>v \<and> s\<^sub>f = flatten_stack s\<^sub>v"
  by (induction \<Sigma>\<^sub>v) simp_all

lemma flatten_to_stack [dest]: "p\<^sub>\<C> # p\<^sub>\<Delta>\<^sub>f # s\<^sub>f = flatten_stack s\<^sub>v \<Longrightarrow> 
  \<exists>p\<^sub>\<Delta>\<^sub>v ns s\<^sub>v'. s\<^sub>v = (p\<^sub>\<Delta>\<^sub>v, ns, p\<^sub>\<C>) # s\<^sub>v' \<and> s\<^sub>f = flatten_stack s\<^sub>v' \<and> p\<^sub>\<Delta>\<^sub>f = 2 * p\<^sub>\<Delta>\<^sub>v"
proof (induction s\<^sub>v)
  case (Cons f\<^sub>v s\<^sub>v)
  thus ?case by (cases f\<^sub>v) simp_all
qed simp_all

lemma halloc_list_flatten_closure [dest]: "
  halloc_list (flatten_values h\<^sub>v) (flatten_closure c) = (h\<^sub>f', v\<^sub>h) \<Longrightarrow> 
    \<exists>h\<^sub>v' v\<^sub>v. h\<^sub>f' = hsplay flatten_closure h\<^sub>v' \<and> v\<^sub>h = 2 * v\<^sub>v \<and> halloc h\<^sub>v c = (h\<^sub>v', v\<^sub>v)"
  by (cases "halloc h\<^sub>v c") simp_all

lemma halloc_list_flatten_environment [dest]: "
  halloc_list (flatten_environment \<Delta>\<^sub>v) (2 * p\<^sub>\<Delta>\<^sub>v # map ((*) 2) vs\<^sub>v) = (\<Delta>\<^sub>f', p\<^sub>\<Delta>\<^sub>f') \<Longrightarrow> 
    \<exists>\<Delta>\<^sub>v' p\<^sub>\<Delta>\<^sub>v'. halloc \<Delta>\<^sub>v (v\<^sub>v, p\<^sub>\<Delta>\<^sub>v) = (\<Delta>\<^sub>v', p\<^sub>\<Delta>\<^sub>v') \<and> \<Delta>\<^sub>f' = flatten_environment \<Delta>\<^sub>v' \<and> p\<^sub>\<Delta>\<^sub>f' = 2 * p\<^sub>\<Delta>\<^sub>v'"
  by (cases "halloc \<Delta>\<^sub>v (v\<^sub>v, p\<^sub>\<Delta>\<^sub>v)") simp_all

text \<open>And we prove completeness. Despite losing the type tags, the pointer tags provide (just) 
enough information to prove this, but in a larger language this might well simply be false. Consider 
a simple sum constructor, Inl v | Inr v, which might be represented by [0, v] or [1, v] depending on 
which constructor was used, and the pair constructor (v1, v2), which would be represented [v1, v2].
Then projecting the second component of a pair would check that the second address was a pointer to 
a nested value - but there would be no way of telling if that came from a product value or a sum 
value, breaking completeness.\<close>

theorem complete\<^sub>f: "\<C> \<tturnstile> flatten \<Sigma>\<^sub>v \<leadsto>\<^sub>f \<Sigma>\<^sub>f' \<Longrightarrow> chained_state \<Sigma>\<^sub>v \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>v'. (\<C> \<tturnstile> \<Sigma>\<^sub>v \<leadsto>\<^sub>v \<Sigma>\<^sub>v') \<and> flatten \<Sigma>\<^sub>v' = \<Sigma>\<^sub>f'" 
proof (induction "flatten \<Sigma>\<^sub>v" \<Sigma>\<^sub>f' rule: eval\<^sub>f.induct)
  case (ev\<^sub>f_lookup \<C> p\<^sub>\<C> x y z \<Delta>\<^sub>f p\<^sub>\<Delta>\<^sub>f v\<^sub>f h\<^sub>f \<V>\<^sub>f s\<^sub>f)
  then obtain h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v p\<^sub>v s\<^sub>v where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v ((p\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<and> 
    h\<^sub>f = flatten_values h\<^sub>v \<and> \<Delta>\<^sub>f = flatten_environment \<Delta>\<^sub>v \<and> \<V>\<^sub>f = flatten_vals \<V>\<^sub>v \<and> 
    s\<^sub>f = flatten_stack s\<^sub>v \<and> p\<^sub>\<Delta>\<^sub>f = 2 * p\<^sub>v" by fastforce
  with ev\<^sub>f_lookup obtain v\<^sub>v where V: "chain_lookup \<Delta>\<^sub>v p\<^sub>v x = Some v\<^sub>v \<and> v\<^sub>f = 2 * v\<^sub>v" by fastforce
  with S have X: "flatten (S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>v # \<V>\<^sub>v) ((p\<^sub>v, p\<^sub>\<C>) # s\<^sub>v)) = S\<^sub>f h\<^sub>f \<Delta>\<^sub>f (v\<^sub>f # \<V>\<^sub>f) (p\<^sub>\<C> # p\<^sub>\<Delta>\<^sub>f # s\<^sub>f)" 
    by simp
  from ev\<^sub>f_lookup V have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v ((p\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>v # \<V>\<^sub>v) ((p\<^sub>v, p\<^sub>\<C>) # s\<^sub>v)" 
    by simp
  with S X show ?case by blast
next
  case (ev\<^sub>f_pushcon \<C> p\<^sub>\<C> n h\<^sub>f h\<^sub>f' v\<^sub>f \<Delta>\<^sub>f \<V>\<^sub>f p\<^sub>\<Delta>\<^sub>f s\<^sub>f)
  then obtain h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v p\<^sub>v s\<^sub>v where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v ((p\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<and> 
    h\<^sub>f = flatten_values h\<^sub>v \<and> \<Delta>\<^sub>f = flatten_environment \<Delta>\<^sub>v \<and> \<V>\<^sub>f = flatten_vals \<V>\<^sub>v \<and> 
    s\<^sub>f = flatten_stack s\<^sub>v \<and> p\<^sub>\<Delta>\<^sub>f = 2 * p\<^sub>v" by fastforce
  with ev\<^sub>f_pushcon have "halloc_list (flatten_values h\<^sub>v) (flatten_closure (Const\<^sub>v n)) = (h\<^sub>f', v\<^sub>f)" 
    by simp
  then obtain h\<^sub>v' v\<^sub>v where H: "h\<^sub>f' = flatten_values h\<^sub>v' \<and> v\<^sub>f = 2 * v\<^sub>v \<and> 
    halloc h\<^sub>v (Const\<^sub>v n) = (h\<^sub>v', v\<^sub>v)" by fastforce
  with S have X: "flatten (S\<^sub>v h\<^sub>v' \<Delta>\<^sub>v (v\<^sub>v # \<V>\<^sub>v) ((p\<^sub>v, p\<^sub>\<C>) # s\<^sub>v)) = S\<^sub>f h\<^sub>f' \<Delta>\<^sub>f (v\<^sub>f # \<V>\<^sub>f) (p\<^sub>\<C> # p\<^sub>\<Delta>\<^sub>f # s\<^sub>f)" 
    by simp
  from ev\<^sub>f_pushcon H have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v ((p\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v S\<^sub>v h\<^sub>v' \<Delta>\<^sub>v (v\<^sub>v # \<V>\<^sub>v) ((p\<^sub>v, p\<^sub>\<C>) # s\<^sub>v)" 
    by simp
  with S X show ?case by blast
next
  case (ev\<^sub>f_pushlam \<C> p\<^sub>\<C> p\<^sub>\<C>' n h\<^sub>f p\<^sub>\<Delta>\<^sub>f h\<^sub>f' v\<^sub>f \<Delta>\<^sub>f \<V>\<^sub>f s\<^sub>f)
  then obtain h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v p\<^sub>v s\<^sub>v where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v ((p\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<and> 
    h\<^sub>f = flatten_values h\<^sub>v \<and> \<Delta>\<^sub>f = flatten_environment \<Delta>\<^sub>v \<and> \<V>\<^sub>f = flatten_vals \<V>\<^sub>v \<and> 
    s\<^sub>f = flatten_stack s\<^sub>v \<and> p\<^sub>\<Delta>\<^sub>f = 2 * p\<^sub>v" by fastforce
  with ev\<^sub>f_pushlam have "halloc_list (flatten_values h\<^sub>v) (flatten_closure (Lam\<^sub>v p\<^sub>v p\<^sub>\<C>')) = (h\<^sub>f', v\<^sub>f)" 
    by simp
  then obtain h\<^sub>v' v\<^sub>v where H: "h\<^sub>f' = flatten_values h\<^sub>v' \<and> v\<^sub>f = 2 * v\<^sub>v \<and> 
    halloc h\<^sub>v (Lam\<^sub>v p\<^sub>v p\<^sub>\<C>') = (h\<^sub>v', v\<^sub>v)" by fastforce
  with S have X: "flatten (S\<^sub>v h\<^sub>v' \<Delta>\<^sub>v (v\<^sub>v # \<V>\<^sub>v) ((p\<^sub>v, p\<^sub>\<C>) # s\<^sub>v)) = S\<^sub>f h\<^sub>f' \<Delta>\<^sub>f (v\<^sub>f # \<V>\<^sub>f) (p\<^sub>\<C> # p\<^sub>\<Delta>\<^sub>f # s\<^sub>f)" 
    by simp
  from ev\<^sub>f_pushlam S H have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v ((p\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>v' \<Delta>\<^sub>v (v\<^sub>v # \<V>\<^sub>v) ((p\<^sub>v, p\<^sub>\<C>) # s\<^sub>v)" by simp
  with S X show ?case by blast
next
  case (ev\<^sub>f_apply \<C> p\<^sub>\<C> h\<^sub>f v\<^sub>2\<^sub>f p\<^sub>\<Delta>\<^sub>f' p\<^sub>\<C>' \<Delta>\<^sub>f v\<^sub>1\<^sub>f \<Delta>\<^sub>f' p\<^sub>\<Delta>\<^sub>f'' \<V>\<^sub>f p\<^sub>\<Delta>\<^sub>f s\<^sub>f)
  then obtain h\<^sub>v \<Delta>\<^sub>v v\<^sub>1\<^sub>v v\<^sub>2\<^sub>v \<V>\<^sub>v p\<^sub>\<Delta>\<^sub>v s\<^sub>v where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>1\<^sub>v # v\<^sub>2\<^sub>v # \<V>\<^sub>v) ((p\<^sub>\<Delta>\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<and> 
    h\<^sub>f = flatten_values h\<^sub>v \<and> \<Delta>\<^sub>f = flatten_environment \<Delta>\<^sub>v \<and> v\<^sub>1\<^sub>f = 2 * v\<^sub>1\<^sub>v \<and> v\<^sub>2\<^sub>f = 2 * v\<^sub>2\<^sub>v \<and> 
    \<V>\<^sub>f = flatten_vals \<V>\<^sub>v \<and> s\<^sub>f = flatten_stack s\<^sub>v \<and> p\<^sub>\<Delta>\<^sub>f = 2 * p\<^sub>\<Delta>\<^sub>v" by fastforce
  with ev\<^sub>f_apply obtain p\<^sub>\<Delta>\<^sub>v' where P: "hlookup h\<^sub>v v\<^sub>2\<^sub>v = Lam\<^sub>v p\<^sub>\<Delta>\<^sub>v' p\<^sub>\<C>' \<and> p\<^sub>\<Delta>\<^sub>f' = 2 * p\<^sub>\<Delta>\<^sub>v'" 
      by (cases "hlookup h\<^sub>v v\<^sub>2\<^sub>v") auto
  obtain \<Delta>\<^sub>v' p\<^sub>\<Delta>\<^sub>v'' where E: "halloc \<Delta>\<^sub>v (v\<^sub>1\<^sub>v, p\<^sub>\<Delta>\<^sub>v') = (\<Delta>\<^sub>v', p\<^sub>\<Delta>\<^sub>v'')" by fastforce
  with ev\<^sub>f_apply S P have X: "flatten (S\<^sub>v h\<^sub>v \<Delta>\<^sub>v' \<V>\<^sub>v ((Suc p\<^sub>\<Delta>\<^sub>v'', p\<^sub>\<C>') # (p\<^sub>\<Delta>\<^sub>v, p\<^sub>\<C>) # s\<^sub>v)) = 
    S\<^sub>f h\<^sub>f \<Delta>\<^sub>f' \<V>\<^sub>f (p\<^sub>\<C>' # Suc (Suc p\<^sub>\<Delta>\<^sub>f'') # p\<^sub>\<C> # p\<^sub>\<Delta>\<^sub>f # s\<^sub>f)" by simp
  from ev\<^sub>f_apply P E have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>1\<^sub>v # v\<^sub>2\<^sub>v # \<V>\<^sub>v) ((p\<^sub>\<Delta>\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>v \<Delta>\<^sub>v' \<V>\<^sub>v ((Suc p\<^sub>\<Delta>\<^sub>v'', p\<^sub>\<C>') # (p\<^sub>\<Delta>\<^sub>v, p\<^sub>\<C>) # s\<^sub>v)" by simp
  with S X show ?case by blast
next
  case (ev\<^sub>f_pushenv \<C> p\<^sub>\<C> \<Delta>\<^sub>f v\<^sub>f p\<^sub>\<Delta>\<^sub>f \<Delta>\<^sub>f' p\<^sub>\<Delta>\<^sub>f' h\<^sub>f \<V>\<^sub>f s\<^sub>f)
  then obtain h\<^sub>v \<Delta>\<^sub>v v\<^sub>v \<V>\<^sub>v p\<^sub>\<Delta>\<^sub>v s\<^sub>v where "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>v # \<V>\<^sub>v) ((p\<^sub>\<Delta>\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<and> 
    h\<^sub>f = flatten_values h\<^sub>v \<and> \<Delta>\<^sub>f = flatten_environment \<Delta>\<^sub>v \<and> v\<^sub>f = 2 * v\<^sub>v \<and> \<V>\<^sub>f = flatten_vals \<V>\<^sub>v \<and> 
      s\<^sub>f = flatten_stack s\<^sub>v \<and> p\<^sub>\<Delta>\<^sub>f = 2 * p\<^sub>\<Delta>\<^sub>v" by fastforce
  moreover with ev\<^sub>f_pushenv obtain \<Delta>\<^sub>v' p\<^sub>\<Delta>\<^sub>v' where "halloc \<Delta>\<^sub>v (v\<^sub>v, p\<^sub>\<Delta>\<^sub>v) = (\<Delta>\<^sub>v', p\<^sub>\<Delta>\<^sub>v') \<and> 
    \<Delta>\<^sub>f' = flatten_environment \<Delta>\<^sub>v' \<and> p\<^sub>\<Delta>\<^sub>f' = 2 * p\<^sub>\<Delta>\<^sub>v'" by fastforce
  moreover with ev\<^sub>f_pushenv have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>v # \<V>\<^sub>v) ((p\<^sub>\<Delta>\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>v \<Delta>\<^sub>v' \<V>\<^sub>v ((Suc p\<^sub>\<Delta>\<^sub>v', p\<^sub>\<C>) # s\<^sub>v)" by simp
  ultimately show ?case by fastforce
next
  case (ev\<^sub>f_return \<C> p\<^sub>\<C> h\<^sub>f \<Delta>\<^sub>f \<V>\<^sub>f p\<^sub>\<Delta>\<^sub>f s\<^sub>f)
  then obtain h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v p\<^sub>\<Delta>\<^sub>v s\<^sub>v where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v ((p\<^sub>\<Delta>\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<and> 
    h\<^sub>f = flatten_values h\<^sub>v \<and> \<Delta>\<^sub>f = flatten_environment \<Delta>\<^sub>v \<and> \<V>\<^sub>f = flatten_vals \<V>\<^sub>v \<and> 
    s\<^sub>f = flatten_stack s\<^sub>v \<and> p\<^sub>\<Delta>\<^sub>f = 2 * p\<^sub>\<Delta>\<^sub>v" by fastforcex
  hence X: "flatten (S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v s\<^sub>v) = S\<^sub>f h\<^sub>f \<Delta>\<^sub>f \<V>\<^sub>f s\<^sub>f" by simp
  from ev\<^sub>f_return have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v ((p\<^sub>\<Delta>\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v S\<^sub>v h\<^sub>v \<Delta>\<^sub>v \<V>\<^sub>v s\<^sub>v" by simp
  with S X show ?case by blast
next
  case (ev\<^sub>f_jump \<C> p\<^sub>\<C> h\<^sub>f v\<^sub>2\<^sub>f p\<^sub>\<Delta>\<^sub>f' p\<^sub>\<C>' \<Delta>\<^sub>f v\<^sub>1\<^sub>f \<Delta>' p\<^sub>\<Delta>\<^sub>f'' \<V>\<^sub>f p\<^sub>\<Delta>\<^sub>f s\<^sub>f)
  then obtain h\<^sub>v \<Delta>\<^sub>v v\<^sub>1\<^sub>v v\<^sub>2\<^sub>v \<V>\<^sub>v p\<^sub>\<Delta>\<^sub>v s\<^sub>v where S: "\<Sigma>\<^sub>v = S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>1\<^sub>v # v\<^sub>2\<^sub>v # \<V>\<^sub>v) ((p\<^sub>\<Delta>\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<and> 
    h\<^sub>f = flatten_values h\<^sub>v \<and> \<Delta>\<^sub>f = flatten_environment \<Delta>\<^sub>v \<and> v\<^sub>1\<^sub>f = 2 * v\<^sub>1\<^sub>v \<and> v\<^sub>2\<^sub>f = 2 * v\<^sub>2\<^sub>v \<and> 
    \<V>\<^sub>f = flatten_vals \<V>\<^sub>v \<and> s\<^sub>f = flatten_stack s\<^sub>v \<and> p\<^sub>\<Delta>\<^sub>f = 2 * p\<^sub>\<Delta>\<^sub>v" by fastforce
  from ev\<^sub>f_jump S obtain p\<^sub>\<Delta>\<^sub>v' where P: "hlookup h\<^sub>v v\<^sub>2\<^sub>v = Lam\<^sub>v p\<^sub>\<Delta>\<^sub>v' p\<^sub>\<C>' \<and> p\<^sub>\<Delta>\<^sub>f' = 2 * p\<^sub>\<Delta>\<^sub>v'" 
    by (cases "hlookup h\<^sub>v v\<^sub>2\<^sub>v") auto
  obtain \<Delta>\<^sub>v' p\<^sub>\<Delta>\<^sub>v'' where E: "halloc \<Delta>\<^sub>v (v\<^sub>1\<^sub>v, p\<^sub>\<Delta>\<^sub>v') = (\<Delta>\<^sub>v', p\<^sub>\<Delta>\<^sub>v'')" by fastforce
  with ev\<^sub>f_jump S P have X: "flatten (S\<^sub>v h\<^sub>v \<Delta>\<^sub>v' \<V>\<^sub>v ((Suc p\<^sub>\<Delta>\<^sub>v'', p\<^sub>\<C>') # s\<^sub>v)) = 
    S\<^sub>f h\<^sub>f \<Delta>' \<V>\<^sub>f (p\<^sub>\<C>' # Suc (Suc p\<^sub>\<Delta>\<^sub>f'') # s\<^sub>f)" by simp
  from ev\<^sub>f_jump P E have "\<C> \<tturnstile> S\<^sub>v h\<^sub>v \<Delta>\<^sub>v (v\<^sub>1\<^sub>v # v\<^sub>2\<^sub>v # \<V>\<^sub>v) ((p\<^sub>\<Delta>\<^sub>v, Suc p\<^sub>\<C>) # s\<^sub>v) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>v \<Delta>\<^sub>v' \<V>\<^sub>v ((Suc p\<^sub>\<Delta>\<^sub>v'', p\<^sub>\<C>') # s\<^sub>v)" by simp
  with S X show ?case by blast
qed

end