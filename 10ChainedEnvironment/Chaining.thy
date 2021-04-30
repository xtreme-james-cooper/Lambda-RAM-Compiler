theory Chaining
  imports ChainedEnvironment "../09HeapMemory/HeapMemory"
begin

abbreviation chain_structured :: "ceclosure heap \<Rightarrow> (ptr \<times> ptr) heap \<Rightarrow> bool" where
  "chain_structured h env \<equiv> heap_all (\<lambda>p (v, p'). p' \<le> p \<and> hcontains h v) env"

fun chained_frame :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) \<Rightarrow> bool" where
  "chained_frame env (0, pc) = True"
| "chained_frame env (Suc p, pc) = hcontains env p"

abbreviation chained_stack :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) list \<Rightarrow> bool" where
  "chained_stack env sfs \<equiv> list_all (chained_frame env) sfs"

abbreviation chained_vals :: "ceclosure heap \<Rightarrow> ptr list \<Rightarrow> bool" where
  "chained_vals h vs \<equiv> list_all (hcontains h) vs"

primrec chained_closure :: "(ptr \<times> ptr) heap \<Rightarrow> ceclosure \<Rightarrow> bool" where
  "chained_closure env (CEConst n) = True"
| "chained_closure env (CELam p pc) = chained_frame env (p, pc)"

abbreviation chained_closures :: "(ptr \<times> ptr) heap \<Rightarrow> ceclosure heap \<Rightarrow> bool" where
  "chained_closures env h \<equiv> heap_all (\<lambda>p. chained_closure env) h"

primrec chained_state :: "chained_state \<Rightarrow> bool" where
  "chained_state (CES h env vs sfs) = (
    chain_structured h env \<and> chained_closures env h \<and> chained_vals h vs \<and> chained_stack env sfs)"

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

definition unchain_stack :: "(ptr \<times> ptr) heap \<Rightarrow> (ptr \<times> nat) list \<Rightarrow> (ptr list \<times> nat) list" where
  "unchain_stack env sfs = map (unchain_frame env) sfs"

primrec unchain_state :: "chained_state \<Rightarrow> heap_state" where
  "unchain_state (CES h env vs sfs) = HS (unchain_heap h env) vs (unchain_stack env sfs)"

lemma [simp]: "unchain_heap hempty env = hempty"
  by (simp add: unchain_heap_def)

lemma [simp]: "chain_structured h env \<Longrightarrow> chained_frame env (p, pc) \<Longrightarrow> halloc env a = (env', b) \<Longrightarrow> 
  unstack_list env' p = unstack_list env p" 
proof (induction env p rule: unstack_list.induct)
  case (2 env p)
  obtain v p' where V: "hlookup env p = (v, p')" by (cases "hlookup env p")
  from 2 have H: "hcontains env p" by auto
  with 2 V have P: "p' \<le> p" using heap_lookup_all by fast
  with H have "chained_frame env (p', pc)" by (cases p') auto
  with 2 V P have U: "unstack_list env' p' = unstack_list env p'" by simp
  from 2 V H have "hlookup env' p = (v, p')" by simp
  with V P U show ?case by simp
qed simp_all

lemma unfold_unstack_list [simp]: "chain_structured h env \<Longrightarrow> chained_frame env (p, pc) \<Longrightarrow> 
  halloc env (v, p) = (env', p') \<Longrightarrow> unstack_list env' (Suc p') = v # unstack_list env p"
proof -
  assume A: "chain_structured h env"
  assume B: "chained_frame env (p, pc)"
  assume C: "halloc env (v, p) = (env', p')"
  moreover with A B have "unstack_list env' p = unstack_list env p" by simp
  moreover have "p \<le> p'" 
  proof (cases p)
    case (Suc pp)
    moreover with B C have "pp < p'" by simp
    ultimately show ?thesis by simp
  qed simp_all
  ultimately show ?thesis by simp
qed

lemma [simp]: "chain_structured h env \<Longrightarrow> chained_frame env (p, pc) \<Longrightarrow>
  lookup (unstack_list env p) x = chain_lookup env p x"
proof (induction env p x rule: chain_lookup.induct)
  case (3 env p x)
  obtain v p' where V: "hlookup env p = (v, p')" by (cases "hlookup env p")
  from 3 have "hcontains env p" by auto
  with 3 V have P: "p' \<le> p" using heap_lookup_all by fast
  with 3(3) have "hcontains env p'" by auto
  hence "chained_frame env (p', pc)" by (cases p') auto
  with 3(1, 2) V P show ?case by fastforce
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

lemma unchain_state_reverse [dest]: "HS h vs sfs = unchain_state \<Sigma> \<Longrightarrow> 
  \<exists>h\<^sub>c\<^sub>e env sfs\<^sub>c\<^sub>e. \<Sigma> = CES h\<^sub>c\<^sub>e env vs sfs\<^sub>c\<^sub>e \<and> h = unchain_heap h\<^sub>c\<^sub>e env \<and> 
    sfs = unchain_stack env sfs\<^sub>c\<^sub>e"
  by (induction \<Sigma>) simp_all

lemma [dest]: "HLam env\<^sub>h pc = unchain_closure env\<^sub>c\<^sub>e x \<Longrightarrow> 
    \<exists>p. x = CELam p pc \<and> env\<^sub>h = unstack_list env\<^sub>c\<^sub>e p"
  by (induction x) simp_all

lemma [elim]: "hcontains env p \<Longrightarrow> halloc env v = (env', q) \<Longrightarrow> 
    unstack_list env' p = unstack_list env p"
proof (induction env p rule: unstack_list.induct)
  case (2 env p)
  obtain vv p' where V: "hlookup env p = (vv, p')" by (cases "hlookup env p")
  from 2(2) have "hcontains env p" by fast
  with 2(3) V have V': "hlookup env' p = (vv, p')" by simp
  from 2(2) V have "p' \<le> p \<Longrightarrow> hcontains env p'" by auto
  with 2 V have "p' \<le> p \<Longrightarrow> unstack_list env' p' = unstack_list env p'" by metis
  with V V' show ?case by simp
qed simp_all

lemma [elim]: "chain_structured h env \<Longrightarrow> chained_closures env h \<Longrightarrow> halloc env v = (env', p) \<Longrightarrow> 
  unchain_heap h env' = unchain_heap h env"
proof (unfold unchain_heap_def)
  assume S: "chain_structured h env" and C: "chained_closures env h" 
    and A: "halloc env v = (env', p)"
  have "\<And>x. hcontains h x \<Longrightarrow> unchain_closure env' (hlookup h x) = 
    unchain_closure env (hlookup h x)" 
  proof -
    fix x
    assume X: "hcontains h x"
    show "unchain_closure env' (hlookup h x) = unchain_closure env (hlookup h x)" 
    proof (cases "hlookup h x")
      case (CELam pp pc)
      with C X have "chained_closure env (CELam pp pc)" by (metis heap_lookup_all)
      with S A CELam show ?thesis by auto
    qed simp_all
  qed
  thus "hmap (unchain_closure env') h = hmap (unchain_closure env) h" by (metis hmap_eq)
qed

lemma [elim]: "chained_frame env a \<Longrightarrow> halloc env v = (env', p) \<Longrightarrow> 
    unchain_frame env' a = unchain_frame env a"
proof (induction env a rule: chained_frame.induct)
  case (2 env p pc)
  moreover obtain v' p' where "hlookup env p = (v', p')" by (cases "hlookup env p")
  moreover from 2 have "p' \<le> p \<Longrightarrow> hcontains env p'" by auto
  ultimately show ?case by auto
qed simp_all

lemma [elim]: "chained_stack env sfs \<Longrightarrow> halloc env v = (env', p) \<Longrightarrow> 
    unchain_stack env' sfs = unchain_stack env sfs"
  by (induction sfs) (auto simp add: unchain_stack_def)

theorem completece [simp]: "cd \<tturnstile> unchain_state \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>h \<Sigma>\<^sub>h \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>c\<^sub>e'. (cd \<tturnstile> \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e') \<and> \<Sigma>\<^sub>h = unchain_state \<Sigma>\<^sub>c\<^sub>e'"
proof (induction "unchain_state \<Sigma>\<^sub>c\<^sub>e" \<Sigma>\<^sub>h arbitrary: \<Sigma>\<^sub>c\<^sub>e rule: evalh.induct)
  case (evh_lookup cd pc x env v h vs sfs)
  then obtain h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e' where S: "\<Sigma>\<^sub>c\<^sub>e = CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs sfs\<^sub>c\<^sub>e' \<and> h = unchain_heap h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e \<and> 
    (env, Suc pc) # sfs = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e'" by fastforce
  then obtain sf\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e where SF: "sfs\<^sub>c\<^sub>e' = sf\<^sub>c\<^sub>e # sfs\<^sub>c\<^sub>e \<and> (env, Suc pc) = unchain_frame env\<^sub>c\<^sub>e sf\<^sub>c\<^sub>e \<and> 
    sfs = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e" by (auto simp add: unchain_stack_def)
  then obtain p where P: "sf\<^sub>c\<^sub>e = (p, Suc pc) \<and> env = unstack_list env\<^sub>c\<^sub>e p" by (cases sf\<^sub>c\<^sub>e) simp_all
  with evh_lookup S SF have C: "chain_structured h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e" by simp
  with evh_lookup S SF P have X: "HS h (v # vs) ((env, pc) # sfs) = 
    unchain_state (CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e (v # vs) ((p, pc) # sfs\<^sub>c\<^sub>e))" by (simp add: unchain_stack_def)
  from evh_lookup S SF P have "chained_frame env\<^sub>c\<^sub>e (p, Suc pc)" by simp
  with C have "lookup (unstack_list env\<^sub>c\<^sub>e p) x = chain_lookup env\<^sub>c\<^sub>e p x" by simp
  with evh_lookup P C have "cd \<tturnstile> CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs ((p, Suc pc) # sfs\<^sub>c\<^sub>e) \<leadsto>\<^sub>c\<^sub>e 
    CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e (v # vs) ((p, pc) # sfs\<^sub>c\<^sub>e)" by simp
  with S SF P X show ?case by blast
next
  case (evh_pushcon cd pc k h h' v vs env sfs)
  then obtain h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e' where S: "\<Sigma>\<^sub>c\<^sub>e = CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs sfs\<^sub>c\<^sub>e' \<and> h = unchain_heap h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e \<and> 
    (env, Suc pc) # sfs = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e'" by fastforce
  then obtain sf\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e where SF: "sfs\<^sub>c\<^sub>e' = sf\<^sub>c\<^sub>e # sfs\<^sub>c\<^sub>e \<and> (env, Suc pc) = unchain_frame env\<^sub>c\<^sub>e sf\<^sub>c\<^sub>e \<and> 
    sfs = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e" by (auto simp add: unchain_stack_def)
  then obtain p where P: "sf\<^sub>c\<^sub>e = (p, Suc pc) \<and> env = unstack_list env\<^sub>c\<^sub>e p" by (cases sf\<^sub>c\<^sub>e) simp_all
  from evh_pushcon S have "halloc (hmap (unchain_closure env\<^sub>c\<^sub>e) h\<^sub>c\<^sub>e) 
    (unchain_closure env\<^sub>c\<^sub>e (CEConst k)) = (h', v)" by (simp add: unchain_heap_def)
  then obtain h\<^sub>c\<^sub>e' where H: "halloc h\<^sub>c\<^sub>e (CEConst k) = (h\<^sub>c\<^sub>e', v) \<and> 
    h' = hmap (unchain_closure env\<^sub>c\<^sub>e) h\<^sub>c\<^sub>e'" by (metis halloc_map_inv)
  hence "h' = unchain_heap h\<^sub>c\<^sub>e' env\<^sub>c\<^sub>e" by (simp add: unchain_heap_def)
  with SF P have X: "HS h' (v # vs) ((env, pc) # sfs) = 
    unchain_state (CES h\<^sub>c\<^sub>e' env\<^sub>c\<^sub>e (v # vs) ((p, pc) # sfs\<^sub>c\<^sub>e))" by (simp add: unchain_stack_def)
  from evh_pushcon H have "cd \<tturnstile> CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs ((p, Suc pc) # sfs\<^sub>c\<^sub>e) \<leadsto>\<^sub>c\<^sub>e 
    CES h\<^sub>c\<^sub>e' env\<^sub>c\<^sub>e (v # vs) ((p, pc) # sfs\<^sub>c\<^sub>e)" by simp
  with S SF P X show ?case by blast
next
  case (evh_pushlam cd pc pc' h env h' v vs sfs)
  then obtain h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e' where S: "\<Sigma>\<^sub>c\<^sub>e = CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs sfs\<^sub>c\<^sub>e' \<and> h = unchain_heap h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e \<and> 
    (env, Suc pc) # sfs = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e'" by fastforce
  then obtain sf\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e where SF: "sfs\<^sub>c\<^sub>e' = sf\<^sub>c\<^sub>e # sfs\<^sub>c\<^sub>e \<and> (env, Suc pc) = unchain_frame env\<^sub>c\<^sub>e sf\<^sub>c\<^sub>e \<and> 
    sfs = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e" by (auto simp add: unchain_stack_def)
  then obtain p where P: "sf\<^sub>c\<^sub>e = (p, Suc pc) \<and> env = unstack_list env\<^sub>c\<^sub>e p" by (cases sf\<^sub>c\<^sub>e) simp_all
  with evh_pushlam S have "halloc (hmap (unchain_closure env\<^sub>c\<^sub>e) h\<^sub>c\<^sub>e) 
    (unchain_closure env\<^sub>c\<^sub>e (CELam p pc')) = (h', v)" by (simp add: unchain_heap_def)
  then obtain h\<^sub>c\<^sub>e' where H: "halloc h\<^sub>c\<^sub>e (CELam p pc') = (h\<^sub>c\<^sub>e', v) \<and> 
    h' = hmap (unchain_closure env\<^sub>c\<^sub>e) h\<^sub>c\<^sub>e'" by (metis halloc_map_inv)
  hence "h' = unchain_heap h\<^sub>c\<^sub>e' env\<^sub>c\<^sub>e" by (simp add: unchain_heap_def)
  with SF P have X: "HS h' (v # vs) ((env, pc) # sfs) = 
    unchain_state (CES h\<^sub>c\<^sub>e' env\<^sub>c\<^sub>e (v # vs) ((p, pc) # sfs\<^sub>c\<^sub>e))" by (simp add: unchain_stack_def)
  from evh_pushlam H have "cd \<tturnstile> CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs ((p, Suc pc) # sfs\<^sub>c\<^sub>e) \<leadsto>\<^sub>c\<^sub>e 
    CES h\<^sub>c\<^sub>e' env\<^sub>c\<^sub>e (v # vs) ((p, pc) # sfs\<^sub>c\<^sub>e)" by simp
  with S SF P X show ?case by blast
next
  case (evh_apply cd pc h v2 env' pc' v1 vs env sfs)
  then obtain h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e' where S: "\<Sigma>\<^sub>c\<^sub>e = CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e (v1 # v2 # vs) sfs\<^sub>c\<^sub>e' \<and> 
    h = unchain_heap h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e \<and> (env, Suc pc) # sfs = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e'" by fastforce
  then obtain sf\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e where SF: "sfs\<^sub>c\<^sub>e' = sf\<^sub>c\<^sub>e # sfs\<^sub>c\<^sub>e \<and> (env, Suc pc) = unchain_frame env\<^sub>c\<^sub>e sf\<^sub>c\<^sub>e \<and> 
    sfs = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e" by (auto simp add: unchain_stack_def)
  then obtain p where P: "sf\<^sub>c\<^sub>e = (p, Suc pc) \<and> env = unstack_list env\<^sub>c\<^sub>e p" by (cases sf\<^sub>c\<^sub>e) simp_all
  from evh_apply S have "HLam env' pc' = unchain_closure env\<^sub>c\<^sub>e (hlookup h\<^sub>c\<^sub>e v2)" 
    by (simp add: unchain_heap_def)
  then obtain p' where P': "hlookup h\<^sub>c\<^sub>e v2 = CELam p' pc' \<and> env' = unstack_list env\<^sub>c\<^sub>e p'" by blast
  obtain env\<^sub>c\<^sub>e' p'' where H: "halloc env\<^sub>c\<^sub>e (v1, p') = (env\<^sub>c\<^sub>e', p'')" 
    by (cases "halloc env\<^sub>c\<^sub>e (v1, p')") simp_all
  from evh_apply S SF P have C: "chain_structured h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e \<and> chained_closures env\<^sub>c\<^sub>e h\<^sub>c\<^sub>e \<and>
    hcontains h\<^sub>c\<^sub>e v1 \<and> hcontains h\<^sub>c\<^sub>e v2 \<and> chained_vals h\<^sub>c\<^sub>e vs \<and> chained_frame env\<^sub>c\<^sub>e (p, Suc pc) \<and> 
      chained_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e" by simp
  with H have Y: "unchain_heap h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e' = unchain_heap h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e" by fast
  from H C have "unstack_list env\<^sub>c\<^sub>e' p = unstack_list env\<^sub>c\<^sub>e p" by fastforce
  with P have W: "env = unstack_list env\<^sub>c\<^sub>e' p" by metis
  from P' C have "chained_closure env\<^sub>c\<^sub>e (CELam p' pc')" by (metis heap_lookup_all)
  hence "chained_frame env\<^sub>c\<^sub>e (p', Suc pc)" by (cases p') auto
  with H C have "unstack_list env\<^sub>c\<^sub>e' (Suc p'') = v1 # unstack_list env\<^sub>c\<^sub>e p'" 
    by (metis unfold_unstack_list)
  with H P' have Z: "v1 # env' = unstack_list env\<^sub>c\<^sub>e' (Suc p'')" by simp
  from H C have "unchain_stack env\<^sub>c\<^sub>e' sfs\<^sub>c\<^sub>e = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e" by fast
  with SF have "sfs = unchain_stack env\<^sub>c\<^sub>e' sfs\<^sub>c\<^sub>e" by simp
  with S Y Z W have X: "HS h vs ((v1 # env', pc') # (env, pc) # sfs) = 
    unchain_state (CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e' vs ((Suc p'', pc') # (p, pc) # sfs\<^sub>c\<^sub>e))" 
      by (simp add: unchain_stack_def)
  from evh_apply P' H have "cd \<tturnstile> CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e (v1 # v2 # vs) ((p, Suc pc) # sfs\<^sub>c\<^sub>e) \<leadsto>\<^sub>c\<^sub>e 
      CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e' vs ((Suc p'', pc') # (p, pc) # sfs\<^sub>c\<^sub>e)" by simp
  with S SF P X show ?case by blast
next
  case (evh_return cd pc h vs env sfs)
  then obtain h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e' where S: "\<Sigma>\<^sub>c\<^sub>e = CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs sfs\<^sub>c\<^sub>e' \<and> h = unchain_heap h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e \<and> 
    (env, Suc pc) # sfs = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e'" by fastforce
  then obtain sf\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e where SF: "sfs\<^sub>c\<^sub>e' = sf\<^sub>c\<^sub>e # sfs\<^sub>c\<^sub>e \<and> (env, Suc pc) = unchain_frame env\<^sub>c\<^sub>e sf\<^sub>c\<^sub>e \<and> 
    sfs = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e" by (auto simp add: unchain_stack_def)
  then obtain p where P: "sf\<^sub>c\<^sub>e = (p, Suc pc) \<and> env = unstack_list env\<^sub>c\<^sub>e p" by (cases sf\<^sub>c\<^sub>e) simp_all
  from S SF have X: "HS h vs sfs = unchain_state (CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs sfs\<^sub>c\<^sub>e)" by simp
  from evh_return have "cd \<tturnstile> CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs ((p, Suc pc) # sfs\<^sub>c\<^sub>e) \<leadsto>\<^sub>c\<^sub>e CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs sfs\<^sub>c\<^sub>e" by simp
  with S SF P X show ?case by blast
next
  case (evh_jump cd pc h v2 env' pc' v1 vs env sfs)
  then obtain h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e' where S: "\<Sigma>\<^sub>c\<^sub>e = CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e (v1 # v2 # vs) sfs\<^sub>c\<^sub>e' \<and> 
    h = unchain_heap h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e \<and> (env, Suc pc) # sfs = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e'" by fastforce
  then obtain sf\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e where SF: "sfs\<^sub>c\<^sub>e' = sf\<^sub>c\<^sub>e # sfs\<^sub>c\<^sub>e \<and> (env, Suc pc) = unchain_frame env\<^sub>c\<^sub>e sf\<^sub>c\<^sub>e \<and> 
    sfs = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e" by (auto simp add: unchain_stack_def)
  then obtain p where P: "sf\<^sub>c\<^sub>e = (p, Suc pc) \<and> env = unstack_list env\<^sub>c\<^sub>e p" by (cases sf\<^sub>c\<^sub>e) simp_all
  from evh_jump S have "HLam env' pc' = unchain_closure env\<^sub>c\<^sub>e (hlookup h\<^sub>c\<^sub>e v2)" 
    by (simp add: unchain_heap_def)
  then obtain p' where P': "hlookup h\<^sub>c\<^sub>e v2 = CELam p' pc' \<and> env' = unstack_list env\<^sub>c\<^sub>e p'" by blast
  obtain env\<^sub>c\<^sub>e' p'' where H: "halloc env\<^sub>c\<^sub>e (v1, p') = (env\<^sub>c\<^sub>e', p'')" 
    by (cases "halloc env\<^sub>c\<^sub>e (v1, p')") simp_all
  from evh_jump S SF P have C: "chain_structured h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e \<and> chained_closures env\<^sub>c\<^sub>e h\<^sub>c\<^sub>e \<and>
    hcontains h\<^sub>c\<^sub>e v1 \<and> hcontains h\<^sub>c\<^sub>e v2 \<and> chained_vals h\<^sub>c\<^sub>e vs \<and> chained_frame env\<^sub>c\<^sub>e (p, Suc pc) \<and> 
      chained_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e" by simp
  with H have Y: "unchain_heap h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e' = unchain_heap h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e" by fast
  from P' C have "chained_closure env\<^sub>c\<^sub>e (CELam p' pc')" by (metis heap_lookup_all)
  hence "chained_frame env\<^sub>c\<^sub>e (p', Suc pc)" by (cases p') auto
  with H C have "unstack_list env\<^sub>c\<^sub>e' (Suc p'') = v1 # unstack_list env\<^sub>c\<^sub>e p'" 
    by (metis unfold_unstack_list)
  with H P' have Z: "v1 # env' = unstack_list env\<^sub>c\<^sub>e' (Suc p'')" by simp
  from H C have "unchain_stack env\<^sub>c\<^sub>e' sfs\<^sub>c\<^sub>e = unchain_stack env\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e" by fast
  with SF have "sfs = unchain_stack env\<^sub>c\<^sub>e' sfs\<^sub>c\<^sub>e" by simp
  with S Y Z have X: "HS h vs ((v1 # env', pc') # sfs) = 
    unchain_state (CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e' vs ((Suc p'', pc') # sfs\<^sub>c\<^sub>e))" by (simp add: unchain_stack_def)
  from evh_jump P' H have "cd \<tturnstile> CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e (v1 # v2 # vs) ((p, Suc pc) # sfs\<^sub>c\<^sub>e) \<leadsto>\<^sub>c\<^sub>e 
      CES h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e' vs ((Suc p'', pc') # sfs\<^sub>c\<^sub>e)" by simp
  with S SF P X show ?case by blast
qed

theorem correctce [simp]: "cd \<tturnstile> \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow> 
  cd \<tturnstile> unchain_state \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>h unchain_state \<Sigma>\<^sub>c\<^sub>e'"
proof (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: evalce.induct)
  case (evce_lookup cd pc x env p v h vs sfs)
  moreover hence "lookup (unstack_list env p) x = chain_lookup env p x" by auto
  ultimately show ?case by (simp add: unchain_stack_def)
next
  case (evce_apply cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  from evce_apply have "chained_closures env h \<and> hcontains h v2" by simp
  with evce_apply have "chained_closure env (CELam p' pc')" by (metis heap_lookup_all)
  with evce_apply have "chain_structured h env \<and> chained_frame env (p', pc) \<and> 
    halloc env (v1, p') = (env', p'')" by (cases p') auto
  hence X: "unstack_list env' (Suc p'') = v1 # unstack_list env p'" by (metis unfold_unstack_list)
  from evce_apply have A: "unchain_heap h env' = unchain_heap h env" by auto
  from evce_apply have B: "unstack_list env' p = unstack_list env p" by auto
  from evce_apply have "unchain_stack env' sfs = unchain_stack env sfs" by auto 
  with evce_apply X A B have "cd \<tturnstile> HS (unchain_heap h env) (v1 # v2 # vs) 
    ((unstack_list env p, Suc pc) # unchain_stack env sfs) \<leadsto>\<^sub>h
      HS (unchain_heap h env') vs 
        ((unstack_list env' (Suc p''), pc') # (unstack_list env' p, pc) # unchain_stack env' sfs)" 
    by simp
  thus ?case by (simp add: unchain_stack_def)
next
  case (evce_jump cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  from evce_jump have "chained_closures env h \<and> hcontains h v2" by simp
  with evce_jump have "chained_closure env (CELam p' pc')" by (metis heap_lookup_all)
  with evce_jump have "chain_structured h env \<and> chained_frame env (p', pc) \<and> 
    halloc env (v1, p') = (env', p'')" by (cases p') auto
  hence X: "unstack_list env' (Suc p'') = v1 # unstack_list env p'" by (metis unfold_unstack_list)
  from evce_jump have A: "unchain_heap h env' = unchain_heap h env" by auto
  from evce_jump have "unchain_stack env' sfs = unchain_stack env sfs" by auto 
  with evce_jump X A have "cd \<tturnstile> HS (unchain_heap h env) (v1 # v2 # vs) 
    ((unstack_list env p, Suc pc) # unchain_stack env sfs) \<leadsto>\<^sub>h
      HS (unchain_heap h env') vs 
        ((unstack_list env' (Suc p''), pc') # unchain_stack env' sfs)" by simp
  thus ?case by (simp add: unchain_stack_def)
qed (simp_all add: unchain_stack_def)

lemma [simp]: "halloc env (v, p') = (env', p) \<Longrightarrow> p' < p \<Longrightarrow> hcontains h v \<Longrightarrow> 
    chain_structured h env \<Longrightarrow> chain_structured h env'"
  by auto

lemma [simp]: "halloc env (v, p') = (env', p) \<Longrightarrow> chained_frame env f \<Longrightarrow> chained_frame env' f"
  by (induction env f rule: chained_frame.induct) simp_all

lemma [simp]: "halloc env (v, p') = (env', p) \<Longrightarrow> chained_stack env sfs \<Longrightarrow> 
    chained_stack env' sfs"
  by (induction sfs) simp_all

lemma [elim]: "chain_structured h env \<Longrightarrow> hcontains env p \<Longrightarrow> hlookup env p = (a, b) \<Longrightarrow> 
    hcontains h a"
proof -
  assume "chain_structured h env" and "hcontains env p" and "hlookup env p = (a, b)"
  hence "(\<lambda>(v, p'). p' \<le> p \<and> hcontains h v) (a, b)" by (metis heap_lookup_all)
  thus ?thesis by simp
qed

lemma [elim]: "chain_structured h env \<Longrightarrow> hcontains env p \<Longrightarrow> chain_lookup env p x = Some v \<Longrightarrow> 
  hcontains h v"
proof (induction env p x rule: chain_lookup.induct)
  case (2 env p)
  moreover obtain a b where "hlookup env p = (a, b)" by (cases "hlookup env p")
  ultimately show ?case by auto
next
  case (3 env p x)
  obtain a b where A: "hlookup env p = (a, b)" by (cases "hlookup env p")
  from 3 have "hcontains env p" by auto
  with 3 A have "b \<le> p \<and> hcontains h a" using heap_lookup_all by fast
  with 3 have "hcontains env b" by fastforce
  with 3 A show ?case by simp
qed simp_all

lemma [elim]: "halloc h v = (h', p) \<Longrightarrow> chain_structured h env \<Longrightarrow> chain_structured h' env"
proof -
  define pp where "pp = (\<lambda>(p::nat) (v, p'). p' \<le> p \<and> hcontains h v)"
  define qq where "qq = (\<lambda>(p::nat) (v, p'). p' \<le> p \<and> hcontains h' v)"
  assume "halloc h v = (h', p)"
  hence A: "\<And>x y. pp x y \<Longrightarrow> qq x y" by (auto simp add: pp_def qq_def split: prod.splits)
  assume "chain_structured h env"
  hence "heap_all pp env" by (simp add: pp_def)
  with A have "heap_all qq env" by (metis heap_all_impl)
  thus "chain_structured h' env" by (simp add: qq_def)
qed

lemma [elim]: "halloc h v = (h', p) \<Longrightarrow> chained_vals h vs \<Longrightarrow> chained_vals h' vs"
  by (induction vs) auto

lemma [elim]: "halloc env v = (env', p) \<Longrightarrow> chained_frame env (a, b) \<Longrightarrow> chained_frame env' (a, b)"
  by (cases a) simp_all

lemma [elim]: "halloc env v = (env', p) \<Longrightarrow> chained_closure env c \<Longrightarrow> chained_closure env' c"
  by (induction c) auto

lemma [elim]: "halloc env v = (env', p) \<Longrightarrow> chained_closures env h \<Longrightarrow> chained_closures env' h"
proof -
  assume "halloc env v = (env', p)"
  hence "\<And>y. chained_closure env y \<Longrightarrow> chained_closure env' y" by auto
  moreover assume "chained_closures env h"
  ultimately show "chained_closures env' h" by (metis heap_all_impl)
qed

lemma [elim]: "hlookup h v2 = CELam p' pc' \<Longrightarrow> chained_closures env h \<Longrightarrow> hcontains h v2 \<Longrightarrow> 
  hcontains h v1 \<Longrightarrow> halloc env (v1, p') = (env', p'') \<Longrightarrow> chain_structured h env \<Longrightarrow> 
    chain_structured h env'"
proof -
  assume "chained_closures env h" and "hlookup h v2 = CELam p' pc'" and "hcontains h v2"
  hence X: "chained_frame env (p', pc')" using heap_lookup_all by fastforce
  moreover assume A: "halloc env (v1, p') = (env', p'')" and "chain_structured h env" 
    and "hcontains h v1"
  moreover have "p' \<le> p''" 
  proof (cases p')
    case (Suc pp)
    moreover with X A have "pp < p''" by simp
    ultimately show ?thesis by simp
  qed simp_all
  ultimately show ?thesis by auto
qed

lemma [elim]: "chain_lookup env (Suc p) x = Some v \<Longrightarrow> chain_structured h env \<Longrightarrow> 
  hcontains env p \<Longrightarrow> hcontains h v"
proof (induction env "Suc p" x arbitrary: p rule: chain_lookup.induct)
  case (2 env p)
  then obtain b where "hlookup env p = (v, b)" by (cases "hlookup env p") simp_all
  with 2 have "b \<le> p \<and> hcontains h v" using heap_lookup_all by fast
  with 2 show ?case by simp
next
  case (3 env p x)
  moreover then obtain a b where A: "hlookup env p = (a, b)" by (cases "hlookup env p")
  moreover with 3 have "b \<le> p \<and> hcontains h a" using heap_lookup_all by fast
  ultimately show ?case by (cases b) auto
qed

lemma [elim]: "halloc h (CELam p pc') = (h', v) \<Longrightarrow> chained_closures env h \<Longrightarrow> 
    chained_frame env (p, pc) \<Longrightarrow> chained_closures env h'"
  by (cases p, auto)

lemma [simp]: "cd \<tturnstile> \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e'"
proof (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: evalce.induct)
case (evce_lookup cd pc x env p v h vs sfs)
  thus ?case by (cases p) auto
next
  case (evce_pushcon cd pc k h h' v env vs p sfs)
  thus ?case by (cases p) auto
next
  case (evce_pushlam cd pc pc' h p h' v env vs sfs)
  thus ?case by (cases p) auto
next
case (evce_apply cd pc h v2 p' pc' env v1 env' p'' vs p sfs)
  thus ?case by (cases p) auto
qed auto

lemma [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>c\<^sub>e) \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow> 
  iter (\<tturnstile> cd \<leadsto>\<^sub>h) (unchain_state \<Sigma>\<^sub>c\<^sub>e) (unchain_state \<Sigma>\<^sub>c\<^sub>e')"
proof (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Sigma>\<^sub>c\<^sub>e'')
  hence "iter (\<tturnstile> cd \<leadsto>\<^sub>h) (unchain_state \<Sigma>\<^sub>c\<^sub>e') (unchain_state \<Sigma>\<^sub>c\<^sub>e'')" by simp
  moreover from iter_step have "cd \<tturnstile> unchain_state \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>h unchain_state \<Sigma>\<^sub>c\<^sub>e'" by simp
  ultimately show ?case by simp
qed simp_all

lemma [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>h) (unchain_state \<Sigma>\<^sub>c\<^sub>e) \<Sigma>\<^sub>h \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>c\<^sub>e'. iter (\<tturnstile> cd \<leadsto>\<^sub>c\<^sub>e) \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<and> \<Sigma>\<^sub>h = unchain_state \<Sigma>\<^sub>c\<^sub>e'"
proof (induction "unchain_state \<Sigma>\<^sub>c\<^sub>e" \<Sigma>\<^sub>h arbitrary: \<Sigma>\<^sub>c\<^sub>e rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>h' \<Sigma>\<^sub>h'')
  then obtain \<Sigma>\<^sub>c\<^sub>e' where "(cd \<tturnstile> \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e') \<and> \<Sigma>\<^sub>h' = unchain_state \<Sigma>\<^sub>c\<^sub>e'" by fastforce
  moreover with iter_step obtain \<Sigma>\<^sub>c\<^sub>e'' where "iter (\<tturnstile> cd \<leadsto>\<^sub>c\<^sub>e) \<Sigma>\<^sub>c\<^sub>e' \<Sigma>\<^sub>c\<^sub>e'' \<and> 
    \<Sigma>\<^sub>h'' = unchain_state \<Sigma>\<^sub>c\<^sub>e''" by fastforce
  ultimately have "iter (\<tturnstile> cd \<leadsto>\<^sub>c\<^sub>e) \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e'' \<and> \<Sigma>\<^sub>h'' = unchain_state \<Sigma>\<^sub>c\<^sub>e''" by fastforce
  then show ?case by fastforce
qed force+

lemma preserve_chained [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>c\<^sub>e) \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow> 
    chained_state \<Sigma>\<^sub>c\<^sub>e'"
  by (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: iter.induct) simp_all

end