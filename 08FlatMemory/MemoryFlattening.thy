theory MemoryFlattening
  imports FlatMemory "../07HeapMemory/HeapConversion"
begin

primrec splay_closure :: "(ptr \<Rightarrow> ptr) \<Rightarrow> hclosure \<Rightarrow> nat list" where
  "splay_closure mp (HConst k) = [0, k]"
| "splay_closure mp (HLam env pc) = Suc (length env) # pc # map mp env"

primrec flatten_closure :: "(ptr \<Rightarrow> ptr) \<Rightarrow> hclosure \<Rightarrow> hclosure" where
  "flatten_closure mp (HConst k) = HConst k"
| "flatten_closure mp (HLam env pc) = HLam (map mp env) pc"

primrec flatten :: "heap_state \<Rightarrow> flat_state" where
  "flatten (HS h vs envs pcs cd) = (case hsplay splay_closure h of
      (h', mp) \<Rightarrow> FS h' (map mp vs) (map (map mp) envs) pcs cd)"

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

lemma [simp]: "hsplay' splay_closure h hp = (h', mp) \<Longrightarrow> x < hp \<Longrightarrow> 
    get_closure h' (mp x) = flatten_closure mp (h x)"
proof (induction hp arbitrary: h' mp)
  case (Suc hp)
  obtain hh' mp' where H: "hsplay' splay_closure h hp = (hh', mp')" by fastforce

  from Suc H have "x < hp \<Longrightarrow> get_closure hh' (mp' x) = flatten_closure mp' (h x)" by simp
  from Suc H have "(case halloc_list hh' (splay_closure mp' (h hp)) of (h'', x) \<Rightarrow> (h'', mp'(hp := x))) =
    (h', mp)" by simp
  from Suc have "x < Suc hp" by simp


  have "get_closure h' (mp x) = flatten_closure mp (h x)" by simp
  thus ?case by simp
qed simp_all

lemma get_closure_flatten [simp]: "hsplay splay_closure h = (h', mp) \<Longrightarrow> hcontains h x \<Longrightarrow>
    get_closure h' (mp x) = flatten_closure mp (hlookup h x)"
  by (induction h) (simp_all del: get_closure.simps)

theorem completef [simp]: "\<Sigma>\<^sub>h \<leadsto>\<^sub>h \<Sigma>\<^sub>h' \<Longrightarrow> heap_structured \<Sigma>\<^sub>h \<Longrightarrow> flatten \<Sigma>\<^sub>h \<leadsto>\<^sub>f flatten \<Sigma>\<^sub>h'"
proof (induction \<Sigma>\<^sub>h \<Sigma>\<^sub>h' rule: evalh.induct)
  case (evh_pushcon cd pc k h h' v vs envs pcs)
  hence S: "stack_contains h vs \<and> env_contains h envs" by simp
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