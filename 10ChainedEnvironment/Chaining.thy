theory Chaining
  imports ChainedEnvironment "../09HeapMemory/HeapMemory"
begin

abbreviation chain_structured :: "(ptr \<times> ptr) heap \<Rightarrow> bool" where
  "chain_structured h \<equiv> heap_all (\<lambda>p (v, p'). p' \<le> p) h"

primrec chained_frame :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) \<Rightarrow> bool" where
  "chained_frame env (p, pc) = hcontains env p"

abbreviation chained_stack :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) list \<Rightarrow> bool" where
  "chained_stack env sfs \<equiv> list_all (chained_frame env) sfs"

primrec chained_closure :: "(ptr \<times> ptr) heap \<Rightarrow> ceclosure \<Rightarrow> bool" where
  "chained_closure env (CEConst n) = True"
| "chained_closure env (CELam p pc) = hcontains env p"

abbreviation chained_closures :: "(ptr \<times> ptr) heap \<Rightarrow> ceclosure heap \<Rightarrow> bool" where
  "chained_closures env h \<equiv> heap_all (\<lambda>p c. chained_closure env c) h"

primrec chained_state :: "chained_state \<Rightarrow> bool" where
  "chained_state (CES h env vs sfs) = (
    chain_structured env \<and> chained_closures env h \<and> chained_stack env sfs)"

fun unstack_list :: "(ptr \<times> ptr) heap \<Rightarrow> ptr \<Rightarrow> ptr list" where
  "unstack_list env 0 = []"
| "unstack_list env (Suc p) = (case hlookup env p of 
      (v, p') \<Rightarrow> v # (if p' \<le> p then unstack_list env p' else undefined))"

primrec unchain_closure :: "(ptr \<times> ptr) heap \<Rightarrow> ceclosure \<Rightarrow> hclosure" where
  "unchain_closure env (CEConst k) = HConst k"
| "unchain_closure env (CELam p pc) = HLam (unstack_list env p) pc"

definition unchain_heap :: "ceclosure heap \<Rightarrow> (ptr \<times> ptr) heap \<Rightarrow> hclosure heap" where
  "unchain_heap h env = hmap (unchain_closure env) h"

primrec unchain_frame :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) \<Rightarrow> (ptr list \<times> nat)" where
  "unchain_frame env (p, pc) = (unstack_list env p, pc)"

abbreviation unchain_stack :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) list \<Rightarrow> (ptr list \<times> nat) list" where
  "unchain_stack env sfs \<equiv> map (unchain_frame env) sfs"

primrec unchain_state :: "chained_state \<Rightarrow> heap_state" where
  "unchain_state (CES h env vs sfs) = HS (unchain_heap h env) vs (unchain_stack env sfs)"

lemma [simp]: "unchain_heap hempty env = hempty"
  by (simp add: unchain_heap_def)

lemma [simp]: "chain_structured env \<Longrightarrow> hcontains env p \<Longrightarrow>
  lookup (unstack_list env p) x = chain_lookup env p x"
proof (induction env p x rule: chain_lookup.induct)
  case (3 h p x)
  thus ?case
  proof (cases "hlookup h p")
    case (Pair v p')
    moreover from 3 have "hcontains h p" by auto
    moreover from 3 have "chain_structured h" by simp
    ultimately have X: "p' \<le> p" using heap_lookup_all by fastforce
    with 3 have "hcontains h p'" by fastforce
    with 3 Pair X show ?thesis by simp
  qed
qed (simp_all split: prod.splits)

lemma [simp]: "halloc h (CEConst k) = (h', p) \<Longrightarrow> 
  halloc (unchain_heap h env) (HConst k) = (unchain_heap h' env, p)"
proof -
  assume "halloc h (CEConst k) = (h', p)"
  hence "halloc (hmap (unchain_closure env) h) (unchain_closure env (CEConst k)) = 
    (hmap (unchain_closure env) h', p)" by (metis halloc_map)
  thus ?thesis by (simp add: unchain_heap_def)
qed

lemma [simp]: "halloc h (CELam p pc) = (h', v) \<Longrightarrow> 
  halloc (unchain_heap h env) (HLam (unstack_list env p) pc) = (unchain_heap h' env, v)"
proof -
  assume "halloc h (CELam p pc) = (h', v)"
  hence "halloc (hmap (unchain_closure env) h) (unchain_closure env (CELam p pc)) = 
    (hmap (unchain_closure env) h', v)" by (metis halloc_map)
  thus ?thesis by (simp add: unchain_heap_def)
qed

lemma [simp]: "hlookup h x = CEConst k \<Longrightarrow> hcontains h x \<Longrightarrow> 
    hlookup (unchain_heap h env) x = HConst k"
  by (simp add: unchain_heap_def)

lemma [simp]: "hlookup h x = CELam p pc \<Longrightarrow> hcontains h x \<Longrightarrow> 
    hlookup (unchain_heap h env) x = HLam (unstack_list env p) pc"
  by (simp add: unchain_heap_def)

lemma unchain_state_reverse [simp]: "HS h vs sfs = unchain_state \<Sigma> \<Longrightarrow> 
  \<exists>h\<^sub>c\<^sub>e env sfs\<^sub>c\<^sub>e. \<Sigma> = CES h\<^sub>c\<^sub>e env vs sfs\<^sub>c\<^sub>e \<and> h = unchain_heap h\<^sub>c\<^sub>e env \<and> 
    sfs = unchain_stack env sfs\<^sub>c\<^sub>e"
  by (induction \<Sigma>) simp_all

theorem completece [simp]: "cd \<tturnstile> unchain_state \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>h \<Sigma>\<^sub>h \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>c\<^sub>e'. (cd \<tturnstile> \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e') \<and> \<Sigma>\<^sub>h = unchain_state \<Sigma>\<^sub>c\<^sub>e'"
  by simp

lemma [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>h) (unchain_state \<Sigma>\<^sub>c\<^sub>e) \<Sigma>\<^sub>h \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>c\<^sub>e'. iter (\<tturnstile> cd \<leadsto>\<^sub>c\<^sub>e) \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<and> \<Sigma>\<^sub>h = unchain_state \<Sigma>\<^sub>c\<^sub>e'"
proof (induction "unchain_state \<Sigma>\<^sub>c\<^sub>e" \<Sigma>\<^sub>h arbitrary: \<Sigma>\<^sub>c\<^sub>e rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>h' \<Sigma>\<^sub>h'')
  then obtain \<Sigma>\<^sub>c\<^sub>e' where "(cd \<tturnstile> \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e') \<and> \<Sigma>\<^sub>h' = unchain_state \<Sigma>\<^sub>c\<^sub>e'" by fastforce
  moreover with iter_step obtain \<Sigma>\<^sub>c\<^sub>e'' where "iter (\<tturnstile> cd \<leadsto>\<^sub>c\<^sub>e) \<Sigma>\<^sub>c\<^sub>e' \<Sigma>\<^sub>c\<^sub>e'' \<and> 
    \<Sigma>\<^sub>h'' = unchain_state \<Sigma>\<^sub>c\<^sub>e''" by fastforce
  ultimately have "iter (\<tturnstile> cd \<leadsto>\<^sub>c\<^sub>e) \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e'' \<and> \<Sigma>\<^sub>h'' = unchain_state \<Sigma>\<^sub>c\<^sub>e''" by fastforce
  then show ?case by fastforce
qed force+

theorem correctce [simp]: "cd \<tturnstile> \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow> 
  cd \<tturnstile> unchain_state \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>h unchain_state \<Sigma>\<^sub>c\<^sub>e'"
proof (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: evalce.induct)
  case (evce_apply cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  from evce_apply have "cd ! pc = BApply" by simp
  from evce_apply have "hlookup h v2 = CELam p' pc'" by simp
  from evce_apply have "halloc env (v1, p') = (env', p'')" by simp
  from evce_apply have "chain_structured env \<and> hcontains env p \<and> chained_stack env sfs" by simp

  from evce_apply have "hlookup (unchain_heap h env) v2 = HLam (unstack_list env p') pc' \<Longrightarrow>
        cd \<tturnstile> HS (unchain_heap h env) (v1 # v2 # vs) ((unstack_list env p, Suc pc) # unchain_stack env sfs) \<leadsto>\<^sub>h
    HS (unchain_heap h env) vs ((v1 # unstack_list env p', pc') # (unstack_list env p, pc) # unchain_stack env sfs)" by simp

  have "cd \<tturnstile> HS (unchain_heap h env) (v1 # v2 # vs) ((unstack_list env p, Suc pc) # unchain_stack env sfs) \<leadsto>\<^sub>h
    HS (unchain_heap h env') vs ((unstack_list env' p'', pc') # (unstack_list env' p, pc) # unchain_stack env' sfs)" by simp
  then show ?case by simp
next
  case (evce_jump cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  then show ?case by simp
qed simp_all

lemma [simp]: "halloc env (v, p') = (env', p) \<Longrightarrow> p' \<le> p \<Longrightarrow> chain_structured env \<Longrightarrow> 
    chain_structured env'"
  by auto

lemma [simp]: "halloc env (v, p') = (env', p) \<Longrightarrow> chained_frame env f \<Longrightarrow> chained_frame env' f"
  by (induction f) simp_all

lemma [simp]: "halloc env (v, p') = (env', p) \<Longrightarrow> chained_stack env sfs \<Longrightarrow> 
    chained_stack env' sfs"
  by (induction sfs) simp_all

lemma [simp]: "cd \<tturnstile> \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e'"
  apply (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: evalce.induct)
  apply auto
  by simp

lemma [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>c\<^sub>e) \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow> 
  iter (\<tturnstile> cd \<leadsto>\<^sub>h) (unchain_state \<Sigma>\<^sub>c\<^sub>e) (unchain_state \<Sigma>\<^sub>c\<^sub>e')"
proof (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Sigma>\<^sub>c\<^sub>e'')
  hence "iter (\<tturnstile> cd \<leadsto>\<^sub>h) (unchain_state \<Sigma>\<^sub>c\<^sub>e') (unchain_state \<Sigma>\<^sub>c\<^sub>e'')" by simp
  moreover from iter_step have "cd \<tturnstile> unchain_state \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>h unchain_state \<Sigma>\<^sub>c\<^sub>e'" by simp
  ultimately show ?case by simp
qed simp_all

end