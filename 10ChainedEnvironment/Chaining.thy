theory Chaining
  imports ChainedEnvironment "../09HeapMemory/HeapMemory"
begin

definition unstack_list :: "(ptr \<times> ptr) heap \<Rightarrow> ptr \<Rightarrow> ptr list" where
  "unstack_list env p = undefined"

definition unchain_heap :: "ceclosure heap \<Rightarrow> (ptr \<times> ptr) heap \<Rightarrow> hclosure heap" where
  "unchain_heap h env = undefined"

primrec unchain_frame :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) \<Rightarrow> (ptr list \<times> nat)" where
  "unchain_frame env (p, pc) = (unstack_list env p, pc)"

abbreviation unchain_stack :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) list \<Rightarrow> (ptr list \<times> nat) list" where
  "unchain_stack env sfs \<equiv> map (unchain_frame env) sfs"

primrec unchain_state :: "chained_state \<Rightarrow> heap_state" where
  "unchain_state (CES h env vs sfs cd) = HS (unchain_heap h env) vs (unchain_stack env sfs) cd"

lemma [simp]: "lookup (unstack_list env p) x = chain_lookup env p x"
  by simp

lemma [simp]: "halloc h (CEConst k) = (h', p) \<Longrightarrow> 
    halloc (unchain_heap h env) (HConst k) = (unchain_heap h' env, p)"
  by simp

lemma [simp]: "halloc h (CELam p pc) = (h', v) \<Longrightarrow> 
    halloc (unchain_heap h env) (HLam (unstack_list env p) pc) = (unchain_heap h' env, v)"
  by simp

theorem completece [simp]: "unchain_state \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>h \<Sigma>\<^sub>h \<Longrightarrow> \<exists>\<Sigma>\<^sub>c\<^sub>e'. \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<and> \<Sigma>\<^sub>h = unchain_state \<Sigma>\<^sub>c\<^sub>e'"
  by simp

theorem correctce [simp]: "\<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> unchain_state \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>h unchain_state \<Sigma>\<^sub>c\<^sub>e'"
proof (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: evalce.induct)
  case (evce_apply cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  from evce_apply have "cd ! pc = BApply" by simp
  from evce_apply have "hlookup h v2 = CELam p' pc'" by simp
  from evce_apply have "halloc env (v1, p') = (env', p'')" by simp

  from evce_apply have "hlookup (unchain_heap h env) v2 = HLam (unstack_list env p') pc' \<Longrightarrow>
        HS (unchain_heap h env) (v1 # v2 # vs) ((unstack_list env p, Suc pc) # unchain_stack env sfs) cd \<leadsto>\<^sub>h
    HS (unchain_heap h env) vs ((v1 # unstack_list env p', pc') # (unstack_list env p, pc) # unchain_stack env sfs) cd" by simp

  have "HS (unchain_heap h env) (v1 # v2 # vs) ((unstack_list env p, Suc pc) # unchain_stack env sfs) cd \<leadsto>\<^sub>h
    HS (unchain_heap h env') vs ((unstack_list env' p'', pc') # (unstack_list env' p, pc) # unchain_stack env' sfs) cd" by simp
  then show ?case by simp
next
  case (evce_jump cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  then show ?case by simp
qed simp_all

end