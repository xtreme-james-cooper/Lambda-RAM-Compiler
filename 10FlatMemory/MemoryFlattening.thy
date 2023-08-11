theory MemoryFlattening                   
  imports FlatMemory "../08HeapMemory/HeapConversion" "../09ChainedEnvironment/Chaining"
begin

subsection \<open>Memory Flattening\<close>

text \<open>The conversion here is one of the few that could go either direction - any (valid) flat state
is equivalent to exactly one chained state, and vice versa. To make correctness the simpler proof 
(and avoid having to define a validity predicate), we define the conversion running forward.\<close>

primrec flatten_closure :: "closure\<^sub>v \<Rightarrow> (pointer_tag \<times> nat) list" where
  "flatten_closure (Const\<^sub>v n) = [(PConst, n), (PConst, 0)]"
| "flatten_closure (Lam\<^sub>v p\<^sub>\<Delta> p\<^sub>\<C>) = [(PEnv, 2 * p\<^sub>\<Delta>), (PCode, p\<^sub>\<C>)]"

abbreviation flatten_values :: "closure\<^sub>v heap \<Rightarrow> (pointer_tag \<times> nat) heap" where
  "flatten_values h \<equiv> hsplay flatten_closure h"

primrec flatten_env :: "(ptr \<times> ptr) \<Rightarrow> ptr list" where
  "flatten_env (p\<^sub>h, p\<^sub>\<Delta>) = [2 * p\<^sub>h, 2 * p\<^sub>\<Delta>]"

abbreviation flatten_environment :: "(ptr \<times> ptr) heap \<Rightarrow> ptr heap" where
  "flatten_environment h \<equiv> hsplay flatten_env h"

abbreviation flatten_vals :: "ptr list \<Rightarrow> ptr list" where
  "flatten_vals \<V> \<equiv> map ((*) 2) \<V>"

primrec flatten_frame :: "(ptr \<times> nat) \<Rightarrow> nat list" where
  "flatten_frame (p\<^sub>\<Delta>, p\<^sub>\<C>) = [p\<^sub>\<C>, 2 * p\<^sub>\<Delta>]"

abbreviation flatten_stack :: "(ptr \<times> nat) list \<Rightarrow> nat list" where
  "flatten_stack s \<equiv> concat (map flatten_frame s)"

primrec flatten :: "state\<^sub>v \<Rightarrow> state\<^sub>f" where
  "flatten (S\<^sub>v h \<Delta> \<V> s) = 
    S\<^sub>f (flatten_values h) (flatten_environment \<Delta>) (flatten_vals \<V>) (flatten_stack s)"

lemma length_flat_closure [simp]: "length (flatten_closure c) = 2"
  by (induction c) simp_all

lemma lookup_flat_closure_0 [simp]: "hcontains h v \<Longrightarrow> hlookup (flatten_values h) (2 * v) = 
  (case hlookup h v of Lam\<^sub>v p\<^sub>\<Delta> _ \<Rightarrow> (PEnv, 2 * p\<^sub>\<Delta>) | Const\<^sub>v n \<Rightarrow> (PConst, n))"
proof -
  assume "hcontains h v"
  moreover have "(0::nat) < 2" by simp
  moreover have "\<And>a. length (flatten_closure a) = 2 \<and> 
    flatten_closure a ! 0 = (case a of Lam\<^sub>v p\<^sub>\<Delta> _ \<Rightarrow> (PEnv, 2 * p\<^sub>\<Delta>) | Const\<^sub>v n \<Rightarrow> (PConst, n))"
      by (simp split: closure\<^sub>v.splits)
  ultimately show ?thesis by (metis (mono_tags, lifting) hlookup_hsplay add.left_neutral)
qed

lemma lookup_flat_closure_1 [simp]: "hcontains h v \<Longrightarrow> hlookup (flatten_values h) (Suc (2 * v)) = 
  (case hlookup h v of Lam\<^sub>v _ p\<^sub>\<C> \<Rightarrow> (PCode, p\<^sub>\<C>) | Const\<^sub>v _ \<Rightarrow> (PConst, 0))"
proof -
  assume "hcontains h v"
  moreover have "(1::nat) < 2" by simp
  moreover have "\<And>a. length (flatten_closure a) = 2 \<and> 
    flatten_closure a ! 1 = (case a of Lam\<^sub>v _ p\<^sub>\<C> \<Rightarrow> (PCode, p\<^sub>\<C>) | Const\<^sub>v _ \<Rightarrow> (PConst, 0))"
      by (simp split: closure\<^sub>v.splits)
  ultimately show ?thesis by (metis hlookup_hsplay plus_1_eq_Suc Suc_1)
qed

lemma length_flat_env [simp]: "length (flatten_env e) = 2"
  by (induction e) simp_all

lemma flatten_env_0 [simp]: "(flatten_env e ! 0) = 2 * fst e"
  by (induction e) simp_all

text \<open>Most of the facts for correctness are simple and self-contained, but the relation between 
\<open>flat_lookup\<close> and \<open>chain_lookup\<close> requires that all pointers followed be contained in the heap. 
Fortunately, we already have this property from the previous stage: \<open>chain_structured\<close> is exactly 
what we need. This does mean we need to use \<open>chained_state\<close> as a well-formedness condition in our 
completeness and correctness theorems, though.\<close>

lemma flat_lookup_flatten [simp]: "chained_heap_pointer \<Delta> p \<Longrightarrow> chain_structured h \<Delta> \<Longrightarrow>
  flat_lookup (flatten_environment \<Delta>) (2 * p) x = map_option ((*) 2) (chain_lookup \<Delta> p x)"
proof (induction \<Delta> p x rule: chain_lookup.induct)
  case (2 \<Delta> p)
  hence "hcontains \<Delta> p" by auto
  hence "\<And>k g. (\<And>a. flatten_env a ! k = g a) \<Longrightarrow> k < 2 \<Longrightarrow>
    hlookup (hsplay flatten_env \<Delta>) (k + 2 * p) = g (hlookup \<Delta> p)" by simp
  hence "hlookup (hsplay flatten_env \<Delta>) (2 * p) = 2 * fst (hlookup \<Delta> p)" 
    using flatten_env_0 by fastforce
  thus ?case by (simp split: prod.splits)
next
  case (3 \<Delta> p x)
  hence P: "hcontains \<Delta> p" by auto
  hence "\<And>k g. (\<And>a. flatten_env a ! k = g a) \<Longrightarrow> k < 2 \<Longrightarrow>
    hlookup (hsplay flatten_env \<Delta>) (k + 2 * p) = g (hlookup \<Delta> p)" by simp
  moreover have "\<And>a. (flatten_env a ! 1) = 2 * snd a \<and> (1::nat) < 2" by auto
  ultimately have X: "hlookup (hsplay flatten_env \<Delta>) (1 + 2 * p) = 2 * snd (hlookup \<Delta> p)" 
    by meson
  obtain a b where A: "hlookup \<Delta> p = (a, b)" by (cases "hlookup \<Delta> p")
  with 3 P have "b \<le> p" using hlookup_all by fast
  with P have "chained_heap_pointer \<Delta> b" by auto
  with 3 X A show ?case by simp
qed simp_all

lemma flatten_halloc [simp]: "halloc h c = (h', v) \<Longrightarrow> 
    halloc_list (flatten_values h) (flatten_closure c) = (flatten_values h', 2 * v)"
  by simp

lemma halloc_flatten_env [simp]: "halloc \<Delta> (v, p) = (\<Delta>', p') \<Longrightarrow> 
  halloc_list (flatten_environment \<Delta>) [2 * v, 2 * p] = (flatten_environment \<Delta>', 2 * p')" 
proof -
  assume "halloc \<Delta> (v, p) = (\<Delta>', p')"
  moreover have "\<And>x. length (flatten_env x) = 2" by simp
  ultimately have "halloc_list (flatten_environment \<Delta>) (flatten_env (v, p)) = 
    (flatten_environment \<Delta>', 2 * p')" by (metis halloc_list_hsplay)
  thus ?thesis by simp
qed

theorem correct\<^sub>f [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>v \<leadsto>\<^sub>v \<Sigma>\<^sub>v' \<Longrightarrow> chained_state \<Sigma>\<^sub>v \<Longrightarrow> \<C> \<tturnstile> flatten \<Sigma>\<^sub>v \<leadsto>\<^sub>f flatten \<Sigma>\<^sub>v'" 
proof (induction \<Sigma>\<^sub>v \<Sigma>\<^sub>v' rule: eval\<^sub>v.induct)
  case ev\<^sub>v_pushcon
  thus ?case using flatten_halloc by fastforce
next
  case ev\<^sub>v_pushlam
  thus ?case using flatten_halloc by fastforce
next
  case (ev\<^sub>v_apply \<C> p\<^sub>\<C> h v\<^sub>2 p\<^sub>\<Delta>' p\<^sub>\<C>' \<Delta> v\<^sub>1 \<Delta>' p\<^sub>\<Delta>'' \<V> p\<^sub>\<Delta> s)
  moreover hence "halloc_list (flatten_environment \<Delta>) [2 * v\<^sub>1, 2 * p\<^sub>\<Delta>'] = 
    (flatten_environment \<Delta>', 2 * p\<^sub>\<Delta>'')" by simp
  moreover from ev\<^sub>v_apply have "hlookup (flatten_values h) (2 * v\<^sub>2) = (PEnv, 2 * p\<^sub>\<Delta>')" by simp
  moreover from ev\<^sub>v_apply have "hlookup (flatten_values h) (Suc (2 * v\<^sub>2)) = (PCode, p\<^sub>\<C>')" by simp
  ultimately have "\<C> \<tturnstile> S\<^sub>f (flatten_values h) (flatten_environment \<Delta>) 
      (2 * v\<^sub>1 # 2 * v\<^sub>2 # flatten_vals \<V>) (Suc p\<^sub>\<C> # 2 * p\<^sub>\<Delta> # flatten_stack s) \<leadsto>\<^sub>f 
    S\<^sub>f (flatten_values h) (flatten_environment \<Delta>') (flatten_vals \<V>) 
      (p\<^sub>\<C>' # Suc (Suc (2 * p\<^sub>\<Delta>'')) # p\<^sub>\<C> # 2 * p\<^sub>\<Delta> # flatten_stack s)"
    by (metis ev\<^sub>f_apply)
  with ev\<^sub>v_apply show ?case by simp
next
  case (ev\<^sub>v_jump \<C> p\<^sub>\<C> h v\<^sub>2 p\<^sub>\<Delta>' p\<^sub>\<C>' \<Delta> v\<^sub>1 \<Delta>' p\<^sub>\<Delta>'' \<V> p\<^sub>\<Delta> s)
  moreover hence "halloc_list (flatten_environment \<Delta>) [2 * v\<^sub>1, 2 * p\<^sub>\<Delta>'] = 
    (flatten_environment \<Delta>', 2 * p\<^sub>\<Delta>'')" by simp
  moreover from ev\<^sub>v_jump have "hlookup (flatten_values h) (2 * v\<^sub>2) = (PEnv, 2 * p\<^sub>\<Delta>')" by simp
  moreover from ev\<^sub>v_jump have "hlookup (flatten_values h) (Suc (2 * v\<^sub>2)) = (PCode, p\<^sub>\<C>')" by simp
  ultimately have "\<C> \<tturnstile> S\<^sub>f (flatten_values h) (flatten_environment \<Delta>)
      (2 * v\<^sub>1 # 2 * v\<^sub>2 # flatten_vals \<V>) (Suc p\<^sub>\<C> # 2 * p\<^sub>\<Delta> # flatten_stack s) \<leadsto>\<^sub>f 
    S\<^sub>f (flatten_values h) (flatten_environment \<Delta>') (flatten_vals \<V>) 
      (p\<^sub>\<C>' # Suc (Suc (2 * p\<^sub>\<Delta>'')) # flatten_stack s)"
    by (metis ev\<^sub>f_jump)
  with ev\<^sub>v_jump show ?case by simp
qed fastforce+

lemma correct\<^sub>f_iter [simp]: "iter (\<tturnstile> \<C> \<leadsto>\<^sub>v) \<Sigma>\<^sub>v \<Sigma>\<^sub>v' \<Longrightarrow> chained_state \<Sigma>\<^sub>v \<Longrightarrow>
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
  \<exists>p\<^sub>\<Delta>\<^sub>v s\<^sub>v'. s\<^sub>v = (p\<^sub>\<Delta>\<^sub>v, p\<^sub>\<C>) # s\<^sub>v' \<and> s\<^sub>f = flatten_stack s\<^sub>v' \<and> p\<^sub>\<Delta>\<^sub>f = 2 * p\<^sub>\<Delta>\<^sub>v"
proof (induction s\<^sub>v)
  case (Cons f\<^sub>v s\<^sub>v)
  thus ?case by (cases f\<^sub>v) simp_all
qed simp_all

lemma halloc_list_flatten_closure [dest]: "
  halloc_list (flatten_values h\<^sub>v) (flatten_closure c) = (h\<^sub>f', v\<^sub>h) \<Longrightarrow> 
    \<exists>h\<^sub>v' v\<^sub>v. h\<^sub>f' = hsplay flatten_closure h\<^sub>v' \<and> v\<^sub>h = 2 * v\<^sub>v \<and> halloc h\<^sub>v c = (h\<^sub>v', v\<^sub>v)"
  by (cases "halloc h\<^sub>v c") simp_all

lemma halloc_list_flatten_environment [dest]: "
  halloc_list (flatten_environment \<Delta>\<^sub>v) [2 * v\<^sub>v, 2 * p\<^sub>\<Delta>\<^sub>v] = (\<Delta>\<^sub>f', p\<^sub>\<Delta>\<^sub>f') \<Longrightarrow> 
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
    s\<^sub>f = flatten_stack s\<^sub>v \<and> p\<^sub>\<Delta>\<^sub>f = 2 * p\<^sub>\<Delta>\<^sub>v" by fastforce
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