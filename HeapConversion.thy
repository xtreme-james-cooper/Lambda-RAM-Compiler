theory HeapConversion
  imports HeapMemory
begin

primrec stack_below :: "ptr \<Rightarrow> ptr list \<Rightarrow> bool" where
  "stack_below x [] = True"
| "stack_below x (v # vs) = (ptr_less x v \<and> stack_below x vs)"

lemma [simp]: "stack_below x ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> ptrSize y < ptrSize x"
  by (induction ys) auto

function unheap_closure :: "hclosure heap \<Rightarrow> ptr \<Rightarrow> bclosure" where
  "unheap_closure h x = (case hlookup h x of 
      HConst k \<Rightarrow> BConst k
    | HLam env pc \<Rightarrow> 
        BLam (if stack_below x env then map (unheap_closure h) env else undefined) pc)"
  by pat_completeness auto
termination by (relation "measure (ptrSize \<circ> snd)") simp_all

primrec unheap :: "heap_state \<Rightarrow> byte_code_state" where
  "unheap (HS h vs envs pcs cd) = 
    BS (map (unheap_closure h) vs) (map (map (unheap_closure h)) envs) pcs cd"

primrec stack_contains :: "hclosure heap \<Rightarrow> ptr list \<Rightarrow> bool" where
  "stack_contains h [] = True"
| "stack_contains h (v # vs) = (hcontains h v \<and> stack_contains h vs)"

primrec env_contains :: "hclosure heap \<Rightarrow> ptr list list \<Rightarrow> bool" where
  "env_contains h [] = True"
| "env_contains h (v # vs) = (stack_contains h v \<and> env_contains h vs)"

primrec bounded_closure :: "hclosure heap \<Rightarrow> ptr \<Rightarrow> hclosure \<Rightarrow> bool" where
  "bounded_closure h x (HConst k) = True"
| "bounded_closure h x (HLam env pc) = (stack_contains h env \<and> stack_below x env)"

primrec heap_structured :: "heap_state \<Rightarrow> bool" where
  "heap_structured (HS h vs envs pcs cd) = (heap_all (bounded_closure h) h \<and>
    stack_contains h vs \<and> env_contains h envs)"

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> stack_contains h vs \<Longrightarrow> stack_contains h' vs"
  by (induction vs) auto

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> env_contains h vs \<Longrightarrow> env_contains h' vs"
  by (induction vs) simp_all

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> bounded_closure h y c \<Longrightarrow> bounded_closure h' y c"
  by (induction c) simp_all

lemma [simp]: "lookup vs x = Some v \<Longrightarrow> stack_contains h vs \<Longrightarrow> hcontains h v"
  by (induction vs x rule: lookup.induct) simp_all

lemma [simp]: "heap_all (bounded_closure h) h \<Longrightarrow> halloc h c = (h', v) \<Longrightarrow> bounded_closure h v c \<Longrightarrow> 
    heap_all (bounded_closure h') h'"
proof -
  assume A: "halloc h c = (h', v)" and "heap_all (bounded_closure h) h" and "bounded_closure h v c"
  hence "heap_all (bounded_closure h) h'" by auto
  moreover from A have "\<And>x c. bounded_closure h x c \<Longrightarrow> bounded_closure h' x c" by simp
  ultimately show ?thesis by auto
qed

lemma [simp]: "halloc h (HConst k) = (h', v) \<Longrightarrow> unheap_closure h' v = BConst k"
  by simp

lemma [simp]: "halloc h c = (h', v) \<Longrightarrow> stack_contains h env \<Longrightarrow> stack_below v env"
  by (induction env) simp_all

lemma [elim]: "stack_contains h env \<Longrightarrow> x \<in> set env \<Longrightarrow> hcontains h x"
  by (induction env) auto

lemma [simp]: "halloc h c = (h', v) \<Longrightarrow> hcontains h x \<Longrightarrow> heap_all (bounded_closure h) h \<Longrightarrow> 
  unheap_closure h' x = unheap_closure h x"
proof (induction h x rule: unheap_closure.induct)
  case (1 h x)
  thus ?case
  proof (cases "hlookup h x")
    case (HLam env p)
    with 1 show ?thesis
    proof (cases "stack_below x env")
      case True
      from HLam 1 have "stack_contains h env" by (metis heap_lookup_all bounded_closure.simps(2))
      hence S: "\<And>y. y \<in> set env \<Longrightarrow> hcontains h y" by auto
      from 1 HLam True have "\<And>y. y \<in> set env \<Longrightarrow> hcontains h y \<Longrightarrow> 
        unheap_closure h' y = unheap_closure h y" by simp
      with S 1(2, 3) HLam True show ?thesis by simp
    qed simp_all
  qed simp_all
qed

lemma [simp]: "halloc h c = (h', v) \<Longrightarrow> stack_contains h env \<Longrightarrow> heap_all (bounded_closure h) h \<Longrightarrow>
    map (unheap_closure h') env = map (unheap_closure h) env"
  by (induction env) (simp_all del: unheap_closure.simps)

lemma [simp]: "halloc h c = (h', v) \<Longrightarrow> env_contains h env \<Longrightarrow> heap_all (bounded_closure h) h \<Longrightarrow>
    map (map (unheap_closure h')) env = map (map (unheap_closure h)) env"
  by (induction env) (simp_all del: unheap_closure.simps)

lemma [simp]: "halloc h (HLam env p) = (h', v) \<Longrightarrow> stack_contains h env \<Longrightarrow> 
    heap_all (bounded_closure h) h \<Longrightarrow> unheap_closure h' v = BLam (map (unheap_closure h) env) p"
  by simp

lemma [simp]: "hlookup h v = HLam env pc \<Longrightarrow> heap_all (bounded_closure h) h \<Longrightarrow> hcontains h v \<Longrightarrow>
    stack_below v env"
  by (metis heap_lookup_all bounded_closure.simps(2))

lemma [simp]: "\<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> heap_structured \<Sigma>\<^sub>h'"
proof (induction \<Sigma>\<^sub>h \<Sigma>\<^sub>h' rule: evalh.induct)
  case (evh_apply cd pc h v2 env pc' v1 vs envs pcs)
  hence "hlookup h v2 = HLam env pc' \<and> heap_all (bounded_closure h) h \<and> hcontains h v2" by simp
  hence "bounded_closure h v2 (HLam env pc')" by (metis heap_lookup_all)
  with evh_apply show ?case by simp
qed fastforce+

theorem correcth [simp]: "\<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> unheap \<Sigma>\<^sub>h \<leadsto>\<^sub>b unheap \<Sigma>\<^sub>h'"
  by (induction \<Sigma>\<^sub>h \<Sigma>\<^sub>h' rule: evalh.induct) simp_all

lemma unheap_backwards [simp]: "BS vs envs pcs cd = unheap \<Sigma>\<^sub>h \<Longrightarrow> \<exists>h vs' envs'. 
  \<Sigma>\<^sub>h = HS h vs' envs' pcs cd \<and> vs = map (unheap_closure h) vs' \<and> 
    envs = map (map (unheap_closure h)) envs'"
  by (induction \<Sigma>\<^sub>h) simp_all

lemma [simp]: "unheap_closure h v = BLam env pc \<Longrightarrow> hcontains h v \<Longrightarrow> 
  heap_all (bounded_closure h) h \<Longrightarrow> 
    \<exists>env'. hlookup h v = HLam env' pc \<and> env = map (unheap_closure h) env'"
  by (simp split: hclosure.splits if_splits)

theorem completeh [simp]: "unheap \<Sigma>\<^sub>h \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>h'. \<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<and> \<Sigma>\<^sub>b' = unheap \<Sigma>\<^sub>h'"
proof (induction "unheap \<Sigma>\<^sub>h" \<Sigma>\<^sub>b' rule: evalb.induct)
  case (evb_lookup cd pc x env v vs envs pcs)
  then obtain h vs' envs'' where "\<Sigma>\<^sub>h = HS h vs' envs'' (Suc pc # pcs) cd \<and> 
    vs = map (unheap_closure h) vs' \<and> env # envs = map (map (unheap_closure h)) envs''" by fastforce
  moreover then obtain env' envs' where "envs'' = env' # envs' \<and> 
    env = map (unheap_closure h) env' \<and> envs = map (map (unheap_closure h)) envs'" by fastforce
  moreover with evb_lookup obtain v' where "lookup env' x = Some v' \<and> v = unheap_closure h v'" 
    by fastforce
  moreover with evb_lookup have "HS h vs' (env' # envs') (Suc pc # pcs) cd \<leadsto>\<^sub>h 
    HS h (v' # vs') envs' (pc # pcs) cd" by simp
  ultimately show ?case by fastforce
next
  case (evb_pushcon cd pc k vs env envs pcs)
  moreover then obtain h vs' envs'' where "\<Sigma>\<^sub>h = HS h vs' envs'' (Suc pc # pcs) cd \<and> 
    vs = map (unheap_closure h) vs' \<and> env # envs = map (map (unheap_closure h)) envs''" by fastforce
  moreover then obtain env' envs' where "envs'' = env' # envs' \<and> 
    env = map (unheap_closure h) env' \<and> envs = map (map (unheap_closure h)) envs'" by fastforce
  moreover obtain h' v where "halloc h (HConst k) = (h', v)" by fastforce
  moreover with evb_pushcon have "HS h vs' (env' # envs') (Suc pc # pcs) cd \<leadsto>\<^sub>h 
    HS h' (v # vs') envs' (pc # pcs) cd" by simp
  ultimately show ?case by fastforce
next
  case (evb_pushlam cd pc pc' vs env envs pcs)
  moreover then obtain h vs' envs'' where "\<Sigma>\<^sub>h = HS h vs' envs'' (Suc pc # pcs) cd \<and> 
    vs = map (unheap_closure h) vs' \<and> env # envs = map (map (unheap_closure h)) envs''" by fastforce
  moreover then obtain env' envs' where "envs'' = env' # envs' \<and> 
    env = map (unheap_closure h) env' \<and> envs = map (map (unheap_closure h)) envs'" by fastforce
  moreover obtain h' v where "halloc h (HLam env' pc') = (h', v)" by fastforce
  moreover with evb_pushlam have "HS h vs' (env' # envs') (Suc pc # pcs) cd \<leadsto>\<^sub>h 
    HS h' (v # vs') envs' (pc # pcs) cd" by simp
  ultimately show ?case by fastforce
next
  case (evb_enter cd pc vs env envs pcs)
  then obtain h vs' envs'' where "\<Sigma>\<^sub>h = HS h vs' envs'' (Suc pc # pcs) cd \<and> 
    vs = map (unheap_closure h) vs' \<and> env # envs = map (map (unheap_closure h)) envs''" by fastforce
  moreover then obtain env' envs' where "envs'' = env' # envs' \<and> 
    env = map (unheap_closure h) env' \<and> envs = map (map (unheap_closure h)) envs'" by fastforce
  moreover from evb_enter have "HS h vs' (env' # envs') (Suc pc # pcs) cd \<leadsto>\<^sub>h 
    HS h vs' (env' # env' # envs') (pc # pcs) cd" by simp
  ultimately show ?case by fastforce
next
  case (evb_apply cd pc v env pc' vs envs pcs)
  then obtain h vs'' envs' where S: "\<Sigma>\<^sub>h = HS h vs'' envs' (Suc pc # pcs) cd \<and> 
    v # BLam env pc' # vs = map (unheap_closure h) vs'' \<and> envs = map (map (unheap_closure h)) envs'" 
      by fastforce
  moreover then obtain v1 v2 vs' where "vs'' = v1 # v2 # vs' \<and> v = unheap_closure h v1 \<and> 
    BLam env pc' = unheap_closure h v2 \<and> vs = map (unheap_closure h) vs'" by fastforce
  moreover with evb_apply S obtain env' where "hlookup h v2 = HLam env' pc' \<and> 
    env = map (unheap_closure h) env'" by fastforce
  moreover with evb_apply have "HS h (v1 # v2 # vs') envs' (Suc pc # pcs) cd \<leadsto>\<^sub>h 
    HS h vs' ((v1 # env') # envs') (pc' # pc # pcs) cd" by simp
  ultimately show ?case by fastforce
next
  case (evb_return cd pc vs envs pcs)
  then obtain h vs' envs' where "\<Sigma>\<^sub>h = HS h vs' envs' (Suc pc # pcs) cd \<and> 
    vs = map (unheap_closure h) vs' \<and> envs = map (map (unheap_closure h)) envs'" by fastforce
  moreover from evb_return have "HS h vs' envs' (Suc pc # pcs) cd \<leadsto>\<^sub>h HS h vs' envs' pcs cd" by simp
  ultimately show ?case by fastforce
qed

lemma [simp]: "iter (\<leadsto>\<^sub>b) (unheap \<Sigma>\<^sub>h) \<Sigma>\<^sub>b' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>h'. iter (\<leadsto>\<^sub>h) \<Sigma>\<^sub>h \<Sigma>\<^sub>h' \<and> \<Sigma>\<^sub>b' = unheap \<Sigma>\<^sub>h'"
proof (induction "unheap \<Sigma>\<^sub>h" \<Sigma>\<^sub>b' arbitrary: \<Sigma>\<^sub>h rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>b' \<Sigma>\<^sub>b'')
  moreover then obtain \<Sigma>\<^sub>h' where S: "\<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<and> \<Sigma>\<^sub>b' = unheap \<Sigma>\<^sub>h'" by fastforce
  moreover with iter_step have "heap_structured \<Sigma>\<^sub>h'" by fastforce
  ultimately obtain \<Sigma>\<^sub>h'' where "iter (\<leadsto>\<^sub>h) \<Sigma>\<^sub>h' \<Sigma>\<^sub>h'' \<and> \<Sigma>\<^sub>b'' = unheap \<Sigma>\<^sub>h''" by fastforce
  with S have "iter (\<leadsto>\<^sub>h) \<Sigma>\<^sub>h \<Sigma>\<^sub>h'' \<and> \<Sigma>\<^sub>b'' = unheap \<Sigma>\<^sub>h''" by fastforce
  thus ?case by fastforce
qed force+

end