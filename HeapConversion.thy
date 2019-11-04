theory HeapConversion
  imports HeapMemory
begin

function unheap_closure :: "hclosure heap \<Rightarrow> ptr \<Rightarrow> bclosure" where
  [simp del]: "unheap_closure h x = (case hlookup h x of 
      HConst k \<Rightarrow> BConst k
    | HLam env pc \<Rightarrow> 
        BLam (if \<forall>y \<in> set env. ptr_less x y then map (unheap_closure h) env else undefined) pc)"
  by pat_completeness auto
termination by (relation "measure (ptrSize \<circ> snd)") simp_all

primrec unheap :: "heap_state \<Rightarrow> byte_code_state" where
  "unheap (HS h vs envs pcs cd) = 
    BS (map (unheap_closure h) vs) (map (map (unheap_closure h)) envs) pcs cd"

primrec bounded_closure :: "hclosure heap \<Rightarrow> hclosure \<Rightarrow> bool" where
  "bounded_closure h (HConst k) = True"
| "bounded_closure h (HLam env pc) = (\<forall>x \<in> set env. hcontains h x)"

primrec heap_structured :: "heap_state \<Rightarrow> bool" where
  "heap_structured (HS h vs envs pcs cd) = (heap_all (bounded_closure h) h \<and>
    (\<forall>v \<in> set vs. hcontains h v) \<and> (\<forall>env \<in> set envs. \<forall>x \<in> set env. hcontains h x))"

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> bounded_closure h c \<Longrightarrow> bounded_closure h' c"
  by (induction c) auto

lemma [simp]: "heap_all (bounded_closure h) h \<Longrightarrow> halloc h c = (h', v) \<Longrightarrow> bounded_closure h c \<Longrightarrow> 
    heap_all (bounded_closure h') h'"
proof -
  assume A: "halloc h c = (h', v)" and "heap_all (bounded_closure h) h" and "bounded_closure h c"
  hence "heap_all (bounded_closure h) h'" by auto
  moreover from A have "\<And>c. bounded_closure h c \<Longrightarrow> bounded_closure h' c" by simp
  ultimately show ?thesis by auto
qed

lemma [simp]: "\<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> heap_structured \<Sigma>\<^sub>h'"
proof (induction \<Sigma>\<^sub>h \<Sigma>\<^sub>h' rule: evalh.induct)
  case (evh_apply cd pc h v2 env pc' v1 vs envs pcs)
  hence "hlookup h v2 = HLam env pc' \<and> heap_all (bounded_closure h) h \<and> hcontains h v2" by simp
  hence "bounded_closure h (HLam env pc')" by (metis heap_lookup_all)
  with evh_apply show ?case by simp
qed fastforce+

theorem correcth [simp]: "\<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> unheap \<Sigma>\<^sub>h \<leadsto>\<^sub>b unheap \<Sigma>\<^sub>h'"
proof (induction \<Sigma>\<^sub>h \<Sigma>\<^sub>h' rule: evalh.induct)
  case (evh_pushcon cd pc k h h' v vs env envs pcs)
  from evh_pushcon have "cd ! pc = BPushCon k" by simp
  from evh_pushcon have "halloc h (HConst k) = (h', v)" by simp

  from evh_pushcon have "heap_all (bounded_closure h) h" by simp
  from evh_pushcon have "\<forall>v\<in>set vs. hcontains h v" by simp
  from evh_pushcon have "\<forall>x\<in>set env. hcontains h x" by simp
  from evh_pushcon have "\<forall>env\<in>set envs. \<forall>x\<in>set env. hcontains h x" by simp


  from evh_pushcon have 
       "BS (unheap_closure h' v # map (unheap_closure h') vs) (map (map (unheap_closure h')) envs) (pc # pcs) cd = 
    BS (BConst k # (map (unheap_closure h) vs)) (map (map (unheap_closure h)) envs) (pc # pcs) cd" 
    by simp


  have "BS (map (unheap_closure h) vs) (map (unheap_closure h) env # map (map (unheap_closure h)) envs) (Suc pc # pcs) cd \<leadsto>\<^sub>b
    BS (unheap_closure h' v # map (unheap_closure h') vs) (map (map (unheap_closure h')) envs) (pc # pcs) cd" by simp
  then show ?case by simp
next
  case (evh_pushlam cd pc pc' h env h' v vs envs pcs)
  then show ?case by simp
next
  case (evh_apply cd pc h v2 env pc' v1 vs envs pcs)
  then show ?case by simp
qed simp_all

lemma unheap_backwards [simp]: "BS vs envs pcs cd = unheap \<Sigma>\<^sub>h \<Longrightarrow> \<exists>h vs' envs'. 
  \<Sigma>\<^sub>h = HS h vs' envs' pcs cd \<and> vs = map (unheap_closure h) vs' \<and> 
    envs = map (map (unheap_closure h)) envs'"
  by (induction \<Sigma>\<^sub>h) simp_all

theorem completeh [simp]: "unheap \<Sigma>\<^sub>h \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>h'. \<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<and> \<Sigma>\<^sub>b' = unheap \<Sigma>\<^sub>h'"
proof (induction "unheap \<Sigma>\<^sub>h" \<Sigma>\<^sub>b' rule: evalb.induct)
  case (evb_lookup cd pc x env v vs envs pcs)
  thus ?case by simp
next
  case (evb_pushcon cd pc k vs env envs pcs)
  then show ?case by simp
next
  case (evb_pushlam cd pc pc' vs env envs pcs)
  then show ?case by simp
next
  case (evb_enter cd pc vs env envs pcs)
  then show ?case by simp
next
  case (evb_apply cd pc v env pc' vs envs pcs)
  then show ?case by simp
next
  case (evb_return cd pc vs envs pcs)
  then show ?case by simp
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