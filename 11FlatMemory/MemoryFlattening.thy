theory MemoryFlattening                   
  imports FlatMemory "../09HeapMemory/HeapConversion"
begin

primrec flatten_closure :: "ceclosure \<Rightarrow> nat list" where
  "flatten_closure (CEConst k) = [0, k, 0]"
| "flatten_closure (CELam p pc) = [1, 2 * p, pc]"

abbreviation flatten_values :: "ceclosure heap \<Rightarrow> nat heap" where
  "flatten_values h \<equiv> hsplay flatten_closure h"

primrec flatten_env :: "(ptr \<times> ptr) \<Rightarrow> ptr list" where
  "flatten_env (a, b) = [b, a]"

abbreviation flatten_environment :: "(ptr \<times> ptr) heap \<Rightarrow> ptr heap" where
  "flatten_environment h \<equiv> hsplay flatten_env h"

primrec flatten_frame :: "(ptr \<times> nat) \<Rightarrow> nat list" where
  "flatten_frame (a, b) = [b, 2 * a]"

abbreviation flatten_stack :: "(ptr \<times> nat) list \<Rightarrow> nat list" where
  "flatten_stack sfs \<equiv> concat (map flatten_frame sfs)"

primrec flatten :: "chained_state \<Rightarrow> flat_state" where
  "flatten (CES h env vs sfs) = 
      FS (flatten_values h) (flatten_environment env) vs (flatten_stack sfs)"

lemma [simp]: "get_closure (flatten_values h) v = hlookup h v"
  by simp

lemma [simp]: "length (flatten_env e) = 2"
  by (induction e) simp_all

lemma [simp]: "fst e = flatten_env e ! 1"
  by (induction e) simp_all

lemma [simp]: "snd e = flatten_env e ! 0"
  by (induction e) simp_all

lemma [simp]: "flat_lookup (flatten_environment env) (2 * p) x = chain_lookup env p x"
  by (induction env p x rule: chain_lookup.induct) simp_all

lemma flatten_halloc [simp]: "halloc h c = (h', v) \<Longrightarrow> 
    halloc_list (flatten_values h) (flatten_closure c) = (flatten_values h', v)"
  by simp

theorem correctf: "cd \<tturnstile> flatten \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>f \<Sigma>\<^sub>f' \<Longrightarrow> \<exists>\<Sigma>\<^sub>c\<^sub>e'. (cd \<tturnstile> \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e') \<and> flatten \<Sigma>\<^sub>c\<^sub>e' = \<Sigma>\<^sub>f'" 
  by simp

theorem completef [simp]: "cd \<tturnstile> \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> cd \<tturnstile> flatten \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>f flatten \<Sigma>\<^sub>c\<^sub>e'" 
proof (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: evalce.induct)
  case (evce_pushcon cd pc k h h' v env vs p sfs)
  moreover hence "halloc_list (flatten_values h) [0, k, 0] = (flatten_values h', v)" 
    using flatten_halloc by fastforce
  ultimately show ?case by simp
next
  case (evce_pushlam cd pc pc' h p h' v env vs sfs)
  moreover hence "halloc_list (flatten_values h) [1, 2 * p, pc'] = (flatten_values h', v)" 
    using flatten_halloc by fastforce
  ultimately show ?case by simp
next
  case (evce_apply cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  then show ?case by simp
next
  case (evce_jump cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  then show ?case by simp
qed simp_all

lemma completef_iter [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>c\<^sub>e) \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> 
  iter (\<tturnstile> cd \<leadsto>\<^sub>f) (flatten \<Sigma>\<^sub>c\<^sub>e) (flatten \<Sigma>\<^sub>c\<^sub>e')"
proof (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Sigma>\<^sub>c\<^sub>e'')
  hence "iter (\<tturnstile> cd \<leadsto>\<^sub>f) (flatten \<Sigma>\<^sub>c\<^sub>e') (flatten \<Sigma>\<^sub>c\<^sub>e'')" by simp
  moreover from iter_step have "cd \<tturnstile> flatten \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>f flatten \<Sigma>\<^sub>c\<^sub>e'" by simp
  ultimately show ?case by simp
qed simp_all

end