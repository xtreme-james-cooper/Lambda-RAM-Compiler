theory HeapConversion
  imports HeapMemory
begin

primrec stack_below :: "ptr \<Rightarrow> ptr list \<Rightarrow> bool" where
  "stack_below x [] = True"
| "stack_below x (v # vs) = (v < x \<and> stack_below x vs)"

lemma [simp]: "stack_below x ys \<Longrightarrow> y \<in> set ys \<Longrightarrow> y < x"
  by (induction ys) auto

fun unheap_closure :: "hclosure heap \<Rightarrow> ptr \<Rightarrow> bclosure" where
  "unheap_closure h x = (case hlookup h x of 
      HConst k \<Rightarrow> BConst k
    | HLam env pc \<Rightarrow> 
        BLam (if stack_below x env then map (unheap_closure h) env else undefined) pc)"

fun unheap_stack :: "hclosure heap \<Rightarrow> (ptr list \<times> nat) list \<Rightarrow> (bclosure list \<times> nat) list" where
  "unheap_stack h [] = []"
| "unheap_stack h ((env, pc) # sfs) = ((map (unheap_closure h) env, pc) # unheap_stack h sfs)"

primrec unheap :: "heap_state \<Rightarrow> byte_code_state" where
  "unheap (HS h vs sfs cd) = 
    BS (map (unheap_closure h) vs) (unheap_stack h sfs) cd"

primrec bounded_closure :: "hclosure heap \<Rightarrow> ptr \<Rightarrow> hclosure \<Rightarrow> bool" where
  "bounded_closure h x (HConst k) = True"
| "bounded_closure h x (HLam env pc) = (stack_contains h env \<and> stack_below x env)"

primrec heap_structured :: "heap_state \<Rightarrow> bool" where
  "heap_structured (HS h vs sfs cd) = (heap_all (bounded_closure h) h \<and>
    stack_contains h vs \<and> env_contains h (map fst sfs))"

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> bounded_closure h y c \<Longrightarrow> bounded_closure h' y c"
  by (induction c) simp_all

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

lemma [simp]: "halloc h c = (h', v) \<Longrightarrow> env_contains h (map fst sfs) \<Longrightarrow> 
    heap_all (bounded_closure h) h \<Longrightarrow> unheap_stack h' sfs = unheap_stack h sfs"
  by (induction sfs rule: unheap_stack.induct) (simp_all del: unheap_closure.simps)

lemma [simp]: "halloc h (HLam env p) = (h', v) \<Longrightarrow> stack_contains h env \<Longrightarrow> 
    heap_all (bounded_closure h) h \<Longrightarrow> unheap_closure h' v = BLam (map (unheap_closure h) env) p"
  by simp

lemma [simp]: "hlookup h v = HLam env pc \<Longrightarrow> heap_all (bounded_closure h) h \<Longrightarrow> hcontains h v \<Longrightarrow>
    stack_below v env"
  by (metis heap_lookup_all bounded_closure.simps(2))

lemma [simp]: "\<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> heap_structured \<Sigma>\<^sub>h'"
proof (induction \<Sigma>\<^sub>h \<Sigma>\<^sub>h' rule: evalh.induct)
  case (evh_apply cd pc h v2 env pc' v1 vs sfs)
  hence "hlookup h v2 = HLam env pc' \<and> heap_all (bounded_closure h) h \<and> hcontains h v2" by simp
  hence "bounded_closure h v2 (HLam env pc')" by (metis heap_lookup_all)
  with evh_apply show ?case by simp
next
  case (evh_jump cd pc h v2 env' pc' v1 vs env sfs)
  hence "hlookup h v2 = HLam env' pc' \<and> heap_all (bounded_closure h) h \<and> hcontains h v2" by simp
  hence "bounded_closure h v2 (HLam env' pc')" by (metis heap_lookup_all)
  with evh_jump show ?case by simp
qed fastforce+

lemma [simp]: "iter (\<leadsto>\<^sub>h) \<Sigma>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> heap_structured \<Sigma>\<^sub>h'"
  by (induction \<Sigma>\<^sub>h \<Sigma>\<^sub>h' rule: iter.induct) simp_all

theorem correcth [simp]: "\<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> unheap \<Sigma>\<^sub>h \<leadsto>\<^sub>b unheap \<Sigma>\<^sub>h'"
  by (induction \<Sigma>\<^sub>h \<Sigma>\<^sub>h' rule: evalh.induct) simp_all

lemma [simp]: "BS vs ((env, pc) # sfs) cd = unheap \<Sigma>\<^sub>h \<Longrightarrow> \<exists>h vs' env' sfs'. 
  \<Sigma>\<^sub>h = HS h vs' ((env', pc) # sfs') cd \<and> vs = map (unheap_closure h) vs' \<and> 
    env = map (unheap_closure h) env' \<and> sfs = unheap_stack h sfs'"
proof (induction \<Sigma>\<^sub>h)
  case (HS h vs' sfs' cd')
  thus ?case by (induction h sfs' rule: unheap_stack.induct) (simp_all del: unheap_closure.simps)
qed 

lemma unheap_empty [simp]: "BS vs [] cd = unheap \<Sigma>\<^sub>h \<Longrightarrow> \<exists>h vs'. 
  \<Sigma>\<^sub>h = HS h vs' [] cd \<and> vs = map (unheap_closure h) vs'"
proof (induction \<Sigma>\<^sub>h)
  case (HS h vs' sfs' cd')
  thus ?case by (induction h sfs' rule: unheap_stack.induct) (simp_all del: unheap_closure.simps)
qed 

lemma [simp]: "unheap_closure h v = BLam env pc \<Longrightarrow> hcontains h v \<Longrightarrow> 
  heap_all (bounded_closure h) h \<Longrightarrow> 
    \<exists>env'. hlookup h v = HLam env' pc \<and> env = map (unheap_closure h) env'"
  by (simp split: hclosure.splits if_splits)

theorem completeh [simp]: "unheap \<Sigma>\<^sub>h \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>h'. \<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<and> \<Sigma>\<^sub>b' = unheap \<Sigma>\<^sub>h'"
proof (induction "unheap \<Sigma>\<^sub>h" \<Sigma>\<^sub>b' rule: evalb.induct)
  case (evb_lookup cd pc x env v vs sfs)
  then obtain h vs' env' sfs' where "\<Sigma>\<^sub>h = HS h vs' ((env', Suc pc) # sfs') cd \<and> 
    vs = map (unheap_closure h) vs' \<and> env = map (unheap_closure h) env' \<and> sfs = unheap_stack h sfs'" 
      by fastforce
  moreover with evb_lookup obtain vv where "lookup env' x = Some vv \<and> v = unheap_closure h vv" 
    by fastforce
  moreover with evb_lookup have "HS h vs' ((env', Suc pc) # sfs') cd \<leadsto>\<^sub>h 
    HS h (vv # vs') ((env', pc) # sfs') cd" by simp
  ultimately show ?case by fastforce
next
  case (evb_pushcon cd pc k vs env sfs)
  moreover then obtain h vs' env' sfs' where "\<Sigma>\<^sub>h = HS h vs' ((env', Suc pc) # sfs') cd \<and> 
    vs = map (unheap_closure h) vs' \<and> env = map (unheap_closure h) env' \<and> sfs = unheap_stack h sfs'" 
      by fastforce
  moreover obtain h' v where "halloc h (HConst k) = (h', v)" by fastforce
  moreover with evb_pushcon have "HS h vs' ((env', Suc pc) # sfs') cd \<leadsto>\<^sub>h 
    HS h' (v # vs') ((env', pc) # sfs') cd" by simp
  ultimately show ?case by fastforce
next
  case (evb_pushlam cd pc pc' vs env sfs)
  moreover then obtain h vs' env' sfs' where S: "\<Sigma>\<^sub>h = HS h vs' ((env', Suc pc) # sfs') cd \<and> 
    vs = map (unheap_closure h) vs' \<and> env = map (unheap_closure h) env' \<and> sfs = unheap_stack h sfs'" 
      by fastforce
  moreover obtain h' v where "halloc h (HLam env' pc') = (h', v)" by fastforce
  moreover with evb_pushlam S have "HS h vs' ((env', Suc pc) # sfs') cd \<leadsto>\<^sub>h 
    HS h' (v # vs') ((env', pc) # sfs') cd" by simp
  ultimately show ?case by fastforce
next
  case (evb_apply cd pc v env' pc' vs env sfs)
  then obtain h vs'' envh sfs' where S: "\<Sigma>\<^sub>h = HS h vs'' ((envh, Suc pc) # sfs') cd \<and> 
    v # BLam env' pc' # vs = map (unheap_closure h) vs'' \<and> env = map (unheap_closure h) envh \<and> 
      sfs = unheap_stack h sfs'" by fastforce
  moreover then obtain v1 v2 vs' where "vs'' = v1 # v2 # vs' \<and> v = unheap_closure h v1 \<and> 
    BLam env' pc' = unheap_closure h v2 \<and> vs = map (unheap_closure h) vs'" by fastforce
  moreover with evb_apply S obtain envh' where H: "hlookup h v2 = HLam envh' pc' \<and> 
    env' = map (unheap_closure h) envh'" by fastforce
  moreover with evb_apply have "HS h (v1 # v2 # vs') ((envh, Suc pc) # sfs') cd \<leadsto>\<^sub>h 
    HS h vs' ((v1 # envh', pc') # (envh, pc) # sfs') cd" by simp
  ultimately show ?case by fastforce
next
  case (evb_return cd pc vs env sfs)
  then obtain h vs' env' sfs' where "\<Sigma>\<^sub>h = HS h vs' ((env', Suc pc) # sfs') cd \<and> 
    vs = map (unheap_closure h) vs' \<and> env = map (unheap_closure h) env' \<and> sfs = unheap_stack h sfs'" 
      by fastforce
  moreover with evb_return have "HS h vs' ((env', Suc pc) # sfs') cd \<leadsto>\<^sub>h HS h vs' sfs' cd" by simp
  ultimately show ?case by fastforce
next
  case (evb_jump cd pc v env' pc' vs env sfs)
  then obtain h vs'' envh sfs' where S: "\<Sigma>\<^sub>h = HS h vs'' ((envh, Suc pc) # sfs') cd \<and> 
    v # BLam env' pc' # vs = map (unheap_closure h) vs'' \<and> env = map (unheap_closure h) envh \<and> 
      sfs = unheap_stack h sfs'" by fastforce
  moreover from S obtain v1 v2 vs' where "vs'' = v1 # v2 # vs' \<and> v = unheap_closure h v1 \<and> 
    BLam env' pc' = unheap_closure h v2 \<and> vs = map (unheap_closure h) vs'" by fastforce
  moreover with evb_jump S obtain envh' where "hlookup h v2 = HLam envh' pc' \<and> 
    env' = map (unheap_closure h) envh'" by fastforce
  moreover with evb_jump S have "HS h (v1 # v2 # vs') ((envh, Suc pc) # sfs') cd \<leadsto>\<^sub>h 
    HS h vs' ((v1 # envh', pc') # sfs') cd" by simp
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