theory MemoryFlattening
  imports FlatMemory "../08HeapMemory/HeapConversion"
begin

primrec splay_closure :: "(ptr \<Rightarrow> ptr) \<Rightarrow> hclosure \<Rightarrow> nat list" where
  "splay_closure mp (HConst k) = [0, k]"
| "splay_closure mp (HLam env pc) = Suc (length env) # pc # map mp env"

primrec flatten_closure :: "(ptr \<Rightarrow> ptr) \<Rightarrow> hclosure \<Rightarrow> hclosure" where
  "flatten_closure mp (HConst k) = HConst k"
| "flatten_closure mp (HLam env pc) = HLam (map mp env) pc"

primrec flatten_frame :: "(ptr \<Rightarrow> ptr) \<Rightarrow> ptr list \<times> nat \<Rightarrow> nat list" where
  "flatten_frame mp (env, pc) = pc # map mp env"

primrec flatten :: "heap_state \<Rightarrow> flat_state" where
  "flatten (HS h vs sfs cd) = (case hsplay splay_closure h of
      (h', mp) \<Rightarrow> FS h' (map mp vs) (map (flatten_frame mp) sfs) cd)"

theorem correctf: "flatten \<Sigma>\<^sub>h \<leadsto>\<^sub>f \<Sigma>\<^sub>f' \<Longrightarrow> \<exists>\<Sigma>\<^sub>h'. \<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<and> flatten \<Sigma>\<^sub>h' = \<Sigma>\<^sub>f'" 
  by simp

lemma [simp]: "stack_contains h vs \<Longrightarrow> hsplay splay_closure h = (h', mp) \<Longrightarrow> 
  halloc h k = (h'', x) \<Longrightarrow> map (mp(x := y)) vs = map mp vs"
proof (induction vs)
  case (Cons v vs)
  hence "x \<noteq> v" by simp
  hence "v = x \<Longrightarrow> y = mp x" by simp
  with Cons show ?case by simp
qed simp_all

lemma [simp]: "env_contains h envs \<Longrightarrow> hsplay splay_closure h = (h', mp) \<Longrightarrow>
  halloc h k = (h'', x) \<Longrightarrow> 
    map (map (mp(x := y))) envs = map (map mp) envs"
  by (induction envs) (simp_all del: map_eq_conv, fastforce)

lemma [simp]: "halloc_list h\<^sub>1 (splay_closure mp v) = (h\<^sub>2, y) \<Longrightarrow> 
    get_closure h\<^sub>2 y = flatten_closure mp v"
proof (induction v)
  case (HConst x)
  then obtain h' p' where "halloc h\<^sub>1 0 = (h', y) \<and> halloc h' x = (h\<^sub>2, p')" 
    by (simp split: prod.splits)



  hence "(case hlookup h\<^sub>2 y of 0 \<Rightarrow> HConst (hlookup h\<^sub>2 (Suc y))
     | Suc x \<Rightarrow> HLam (hlookup_list h\<^sub>2 (Suc (Suc y)) x) (hlookup h\<^sub>2 (Suc y))) =
    HConst x" by simp
  then show ?case by simp
next
  case (HLam x1a x2)
  then show ?case by (simp split: prod.splits nat.splits)
qed 
qed (simp split: prod.splits)

lemma [simp]: "hsplay' splay_closure h hp = (h', mp) \<Longrightarrow> x < hp \<Longrightarrow> 
    get_closure h' (mp x) = flatten_closure mp (h x)"
proof (induction hp arbitrary: h' mp)
  case (Suc hp)
  then show ?case
  proof (cases "x = hp")
    case True
    obtain h\<^sub>2 mp' where H: "hsplay' splay_closure h hp = (h\<^sub>2, mp')" by fastforce
    obtain h\<^sub>3 y where Y: "halloc_list h\<^sub>2 (splay_closure mp' (h hp)) = (h\<^sub>3, y)" by fastforce 
    with True have "get_closure h\<^sub>3 y = flatten_closure (mp'(hp := y)) (h x)" by simp
    with True have "get_closure h\<^sub>3 ((mp'(hp := y)) x) = flatten_closure (mp'(hp := y)) (h x)"
      by simp
    with Suc H Y show ?thesis by simp
  next
    case False
    obtain h\<^sub>2 mp' where H: "hsplay' splay_closure h hp = (h\<^sub>2, mp')" by fastforce
    obtain h\<^sub>3 y where Y: "halloc_list h\<^sub>2 (splay_closure mp' (h hp)) = (h\<^sub>3, y)" by fastforce 
  
  
    from Suc False H have "get_closure h\<^sub>2 (mp' x) = flatten_closure mp' (h x)" by simp
    from Suc False have "x < hp" by simp
  
  
    from False have "get_closure h\<^sub>3 ((mp'(hp := y)) x) = flatten_closure (mp'(hp := y)) (h x)" by simp
    with Suc H Y show ?thesis by simp
  qed
qed simp_all

lemma get_closure_flatten [simp]: "hsplay splay_closure h = (h', mp) \<Longrightarrow> hcontains h x \<Longrightarrow>
    get_closure h' (mp x) = flatten_closure mp (hlookup h x)"
  by (induction h) (simp_all del: get_closure.simps)

theorem completef [simp]: "\<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> flatten \<Sigma>\<^sub>h \<leadsto>\<^sub>f flatten \<Sigma>\<^sub>h'"
(*
proof (induction \<Sigma>\<^sub>h \<Sigma>\<^sub>h' rule: evalh.induct)
  case (evh_pushcon cd pc k h h' v vs env sfs)
  hence S: "stack_contains h vs \<and> env_contains h env" by simp
  obtain h\<^sub>1 mp where H1: "hsplay splay_closure h = (h\<^sub>1, mp)" by fastforce
  obtain h\<^sub>2 y where H2: "halloc_list h\<^sub>1 [0, k] = (h\<^sub>2, y)" by fastforce
  with evh_pushcon H1 have H3: "hsplay splay_closure h' = (h\<^sub>2, mp(v := y))" by simp
  from evh_pushcon H2 have "FS h\<^sub>1 (map mp vs) (map (map mp) envs) (Suc pc # pcs) cd \<leadsto>\<^sub>f 
    FS h\<^sub>2 (y # map mp vs) (map (map mp) envs) (pc # pcs) cd" by simp
  moreover from evh_pushcon S H1 have "map (mp(v := y)) vs = map mp vs" by fastforce
  moreover from evh_pushcon S H1 have "map (map (mp(v := y))) envs = map (map mp) envs" by fastforce
  ultimately have "FS h\<^sub>1 (map mp vs) (map (map mp) envs) (Suc pc # pcs) cd \<leadsto>\<^sub>f
    FS h\<^sub>2 (y # map (mp(v := y)) vs) (map (map (mp(v := y))) envs) (pc # pcs) cd" by metis
  with H1 H3 show ?case by simp
next
  case (evh_pushlam cd pc pc' h env h' v vs envs pcs)
  hence S: "stack_contains h vs \<and> stack_contains h env \<and> env_contains h envs" by simp
  obtain h\<^sub>1 mp where H1: "hsplay splay_closure h = (h\<^sub>1, mp)" by fastforce
  obtain h\<^sub>2 y where H2: "halloc_list h\<^sub>1 (Suc (length (map mp env)) # pc' # map mp env) = (h\<^sub>2, y)" 
    by fastforce
  with evh_pushlam H1 have H3: "hsplay splay_closure h' = (h\<^sub>2, mp(v := y))" 
    by (simp del: halloc_list.simps)
  from evh_pushlam H2 have "FS h\<^sub>1 (map mp vs) (map mp env # map (map mp) envs) (Suc pc # pcs) cd \<leadsto>\<^sub>f 
    FS h\<^sub>2 (y # map mp vs) (map mp env # map (map mp) envs) (pc # pcs) cd" by simp
  moreover from evh_pushlam S H1 have "map (mp(v := y)) vs = map mp vs" by fastforce
  moreover from evh_pushlam S H1 have "map (mp(v := y)) env = map mp env" by fastforce
  moreover from evh_pushlam S H1 have "map (map (mp(v := y))) envs = map (map mp) envs" by fastforce
  ultimately have "FS h\<^sub>1 (map mp vs) (map mp env # map (map mp) envs) (Suc pc # pcs) cd \<leadsto>\<^sub>f
    FS h\<^sub>2 (y # map (mp(v := y)) vs) (map (mp(v := y)) env # map (map (mp(v := y))) envs) 
      (pc # pcs) cd" by metis
  with H1 H3 show ?case by simp
qed (simp_all del: get_closure.simps split: prod.splits)
*) 
  by simp

lemma completef_iter [simp]: "iter (\<leadsto>\<^sub>h) \<Sigma>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow>
  iter (\<leadsto>\<^sub>f) (flatten \<Sigma>\<^sub>h) (flatten \<Sigma>\<^sub>h')"
proof (induction \<Sigma>\<^sub>h \<Sigma>\<^sub>h' rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>h \<Sigma>\<^sub>h' \<Sigma>\<^sub>h'')
  moreover hence "heap_structured \<Sigma>\<^sub>h'" by simp
  ultimately have "iter (\<leadsto>\<^sub>f) (flatten \<Sigma>\<^sub>h') (flatten \<Sigma>\<^sub>h'')" by simp
  moreover from iter_step have "flatten \<Sigma>\<^sub>h \<leadsto>\<^sub>f flatten \<Sigma>\<^sub>h'" by simp
  ultimately show ?case by simp
qed simp_all

end