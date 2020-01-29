theory NameRemoval
  imports "../01Source/Named" Debruijn "../00Utils/AssocList"
begin

fun convert' :: "var list \<Rightarrow> nexpr \<Rightarrow> dexpr" where
  "convert' \<Phi> (NVar x) = DVar (the (idx_of \<Phi> x))"
| "convert' \<Phi> (NConst k) = DConst k"
| "convert' \<Phi> (NLam x t e) = DLam t (convert' (insert_at 0 x \<Phi>) e)"
| "convert' \<Phi> (NApp e\<^sub>1 e\<^sub>2) = DApp (convert' \<Phi> e\<^sub>1) (convert' \<Phi> e\<^sub>2)"

definition convert :: "nexpr \<Rightarrow> dexpr" where
  "convert e = convert' [] e"

lemma [simp]: "map_of \<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> mset (map fst \<Gamma>) = mset \<Phi> \<Longrightarrow> 
  listify \<Gamma> \<Phi> \<turnstile>\<^sub>d convert' \<Phi> e : t"
proof (induction \<Phi> e arbitrary: \<Gamma> t rule: convert'.induct)
  case (3 \<Phi> x t\<^sub>1 e)
  then obtain t\<^sub>2 where "t = Arrow t\<^sub>1 t\<^sub>2 \<and> (map_of \<Gamma>)(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e : t\<^sub>2" by fastforce
  moreover with 3 have 
    "listify ((x, t\<^sub>1) # \<Gamma>) (insert_at 0 x \<Phi>) \<turnstile>\<^sub>d convert' (insert_at 0 x \<Phi>) e : t\<^sub>2" by fastforce
  ultimately show ?case by simp
qed fastforce+

theorem typesafend [simp]: "Map.empty \<turnstile>\<^sub>n e : t \<Longrightarrow> [] \<turnstile>\<^sub>d convert e : t"
proof (unfold convert_def)
  define \<Gamma> where "\<Gamma> = ([] :: (var \<times> ty) list)"
  define \<Phi> where "\<Phi> = ([] :: var list)"
  assume "Map.empty \<turnstile>\<^sub>n e : t"
  hence "map_of \<Gamma> \<turnstile>\<^sub>n e : t" by (simp add: \<Gamma>_def)
  moreover have "mset (map fst \<Gamma>) = mset \<Phi>" by (simp add: \<Gamma>_def \<Phi>_def)
  moreover have "distinct \<Phi>" by (simp add: \<Phi>_def)
  ultimately have "listify \<Gamma> \<Phi> \<turnstile>\<^sub>d convert' \<Phi> e : t" by simp
  thus "[] \<turnstile>\<^sub>d convert' [] e : t" by (simp add: \<Gamma>_def \<Phi>_def)
qed

lemma [simp]: "valn e \<Longrightarrow> vald (convert' \<Phi> e)"
  by (induction e) (simp_all add: Let_def)

lemma [simp]: "y \<notin> all_vars e \<Longrightarrow> x \<le> length \<Phi> \<Longrightarrow> free_vars e \<subseteq> set \<Phi> \<Longrightarrow>
  convert' (insert_at x y \<Phi>) e = incrd x (convert' \<Phi> e)"
proof (induction e arbitrary: x \<Phi>)
  case (NVar z)
  moreover then obtain w where "idx_of \<Phi> z = Some w" by fastforce
  ultimately show ?case by simp
next
  case (NLam z t e)
  moreover hence "free_vars e \<subseteq> set (insert_at 0 z \<Phi>)" by auto
  ultimately show ?case by simp
qed simp_all

lemma [simp]: "x' \<notin> all_vars e \<Longrightarrow> a \<le> length \<Phi> \<Longrightarrow> \<not> (a precedes x in \<Phi>) \<Longrightarrow> 
    convert' (insert_at a x \<Phi>) e = convert' (insert_at a x' \<Phi>) e"
  by (induction e arbitrary: a \<Phi>) (auto simp add: incr_min split: option.splits)

lemma [simp]: "y \<le> length \<Phi> \<Longrightarrow> y precedes x in \<Phi> \<Longrightarrow> y precedes x' in \<Phi> \<Longrightarrow> x' \<notin> all_vars e \<Longrightarrow> 
  free_vars e \<subseteq> insert x (set \<Phi>) \<Longrightarrow> 
    convert' (insert_at y x' \<Phi>) (subst_var x x' e) = convert' (insert_at y x \<Phi>) e"
proof (induction e arbitrary: y \<Phi>)
  case (NLam z t e)
  thus ?case
  proof (cases "x = z")
    case False
    with NLam have X: "Suc y precedes x in insert_at 0 z \<Phi>" by (simp split: option.splits) 
    from NLam have Y: "Suc y precedes x' in insert_at 0 z \<Phi>" by (simp split: option.splits) 
    from NLam have "free_vars e \<subseteq> insert x (set (insert_at 0 z \<Phi>))" by auto
    with NLam False X Y show ?thesis by simp
  qed (simp_all split: option.splits)
qed (auto split: option.splits)

lemma convert_subst [simp]: "y \<le> length \<Phi> \<Longrightarrow> x \<notin> set \<Phi> \<Longrightarrow> free_vars e \<subseteq> insert x (set \<Phi>) \<Longrightarrow>
  free_vars e' \<subseteq> set \<Phi> \<Longrightarrow>
    convert' \<Phi> (substn x e' e) = substd y (convert' \<Phi> e') (convert' (insert_at y x \<Phi>) e)" 
proof (induction x e' e arbitrary: \<Phi> y rule: substn.induct)
  case (1 x e' z)
  thus ?case
  proof (cases "idx_of \<Phi> z")
    case (Some w)
    have "y \<noteq> incr y w" by (metis incr_not_eq)
    with 1 Some show ?thesis by auto
  qed simp_all
next
  case (3 x e' z t e)
  let ?z' = "fresh (all_vars e' \<union> all_vars e \<union> {x, z})"
  have "finite (all_vars e' \<union> all_vars e \<union> {x, z})" by simp
  hence Z: "?z' \<notin> all_vars e' \<union> all_vars e \<union> {x, z}" by (metis fresh_is_fresh)
  from 3 Z have X: "free_vars e' \<subseteq> set (insert_at 0 ?z' \<Phi>)" by auto
  from 3 have "free_vars e \<subseteq> insert z (insert x (set \<Phi>))" by auto
  with Z have "free_vars (subst_var z ?z' e) \<subseteq> insert ?z' (insert x (set \<Phi>))" by auto
  hence "free_vars (subst_var z ?z' e) \<subseteq> insert x (set (insert_at 0 ?z' \<Phi>))" by auto
  with 3 X Z have H: "convert' (insert_at 0 ?z' \<Phi>) (substn x e' (subst_var z ?z' e)) = 
    substd (Suc y) (convert' (insert_at 0 ?z' \<Phi>) e') 
      (convert' (insert_at (Suc y) x (insert_at 0 ?z' \<Phi>)) (subst_var z ?z' e))" by fastforce
  from 3 have "free_vars e \<subseteq> insert z (set (insert_at y x \<Phi>))" by auto
  with Z have "convert' (insert_at 0 ?z' (insert_at y x \<Phi>)) (subst_var z ?z' e) =
    convert' (insert_at 0 z (insert_at y x \<Phi>)) e" by simp
  with 3 Z H show ?case by (simp add: Let_def)
qed simp_all

theorem correctnd: "e \<leadsto>\<^sub>n e' \<Longrightarrow> free_vars e = {} \<Longrightarrow> convert e \<leadsto>\<^sub>d convert e'"
proof (induction e e' rule: evaln.induct)
  case (evn_app3 e\<^sub>2 x t e\<^sub>1)
  hence "DApp (DLam t (convert' [x] e\<^sub>1)) (convert' [] e\<^sub>2) \<leadsto>\<^sub>d 
    substd 0 (convert' [] e\<^sub>2) (convert' (insert_at 0 x []) e\<^sub>1)" by simp
  moreover have "0 \<le> length []" by simp
  moreover have "x \<notin> set []" by simp
  moreover from evn_app3 have "free_vars e\<^sub>1 \<subseteq> insert x (set [])" by simp
  moreover from evn_app3 have "free_vars e\<^sub>2 \<subseteq> set []" by simp
  ultimately have "DApp (DLam t (convert' [x] e\<^sub>1)) (convert' [] e\<^sub>2) \<leadsto>\<^sub>d convert' [] (substn x e\<^sub>2 e\<^sub>1)" 
    by (metis convert_subst)
  then show ?case by (simp add: convert_def)
qed (simp_all add: convert_def)

lemma [simp]: "vald (convert' \<Phi> e) \<Longrightarrow> valn e"
  by (induction e) (simp_all add: Let_def)

lemma convert_val_back: "vald (convert e) \<Longrightarrow> valn e"
  by (simp add: convert_def)

lemma [dest]: "DApp e\<^sub>d\<^sub>1 e\<^sub>d\<^sub>2 = convert e\<^sub>n \<Longrightarrow> 
    \<exists>e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2. e\<^sub>n = NApp e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 \<and> e\<^sub>d\<^sub>1 = convert e\<^sub>n\<^sub>1 \<and> e\<^sub>d\<^sub>2 = convert e\<^sub>n\<^sub>2"
  by (cases e\<^sub>n) (simp_all add: convert_def)

lemma [dest]: "DLam t e\<^sub>d = convert e\<^sub>n \<Longrightarrow> 
    \<exists>x e\<^sub>n'. e\<^sub>n = NLam x t e\<^sub>n' \<and> e\<^sub>d = convert' [x] e\<^sub>n'"
  by (cases e\<^sub>n) (simp_all add: convert_def)

theorem completend [simp]: "convert e\<^sub>n \<leadsto>\<^sub>d e\<^sub>d' \<Longrightarrow> free_vars e\<^sub>n = {} \<Longrightarrow> 
  \<exists>e\<^sub>n'. e\<^sub>n \<leadsto>\<^sub>n e\<^sub>n' \<and> e\<^sub>d' = convert e\<^sub>n'"
proof (induction "convert e\<^sub>n" e\<^sub>d' arbitrary: e\<^sub>n rule: evald.induct)
  case (evd_app1 e\<^sub>d\<^sub>1 e\<^sub>d\<^sub>1' e\<^sub>d\<^sub>2)
  then obtain e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 where N: "e\<^sub>n = NApp e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 \<and> e\<^sub>d\<^sub>1 = convert e\<^sub>n\<^sub>1 \<and> e\<^sub>d\<^sub>2 = convert e\<^sub>n\<^sub>2" by fastforce
  moreover with evd_app1 obtain e\<^sub>n\<^sub>1' where "e\<^sub>n\<^sub>1 \<leadsto>\<^sub>n e\<^sub>n\<^sub>1' \<and> e\<^sub>d\<^sub>1' = convert e\<^sub>n\<^sub>1'" by fastforce
  ultimately have "NApp e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 \<leadsto>\<^sub>n NApp e\<^sub>n\<^sub>1' e\<^sub>n\<^sub>2 \<and> DApp e\<^sub>d\<^sub>1' e\<^sub>d\<^sub>2 = convert (NApp e\<^sub>n\<^sub>1' e\<^sub>n\<^sub>2)" 
    by (simp add: convert_def)
  with N show ?case by fastforce
next
  case (evd_app2 e\<^sub>d\<^sub>1 e\<^sub>d\<^sub>2 e\<^sub>d\<^sub>2')
  moreover then obtain e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 where N: "e\<^sub>n = NApp e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 \<and> e\<^sub>d\<^sub>1 = convert e\<^sub>n\<^sub>1 \<and> e\<^sub>d\<^sub>2 = convert e\<^sub>n\<^sub>2" 
    by fastforce
  moreover with evd_app2 obtain e\<^sub>n\<^sub>2' where "e\<^sub>n\<^sub>2 \<leadsto>\<^sub>n e\<^sub>n\<^sub>2' \<and> e\<^sub>d\<^sub>2' = convert e\<^sub>n\<^sub>2'" by fastforce
  ultimately have "NApp e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 \<leadsto>\<^sub>n NApp e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2' \<and> DApp e\<^sub>d\<^sub>1 e\<^sub>d\<^sub>2' = convert (NApp e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2')" 
    by (simp add: convert_def)
  with N show ?case by fastforce
next
  case (evd_app3 e\<^sub>d\<^sub>2 t e\<^sub>d\<^sub>1)
  moreover then obtain x e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 where N: "e\<^sub>n = NApp (NLam x t e\<^sub>n\<^sub>1) e\<^sub>n\<^sub>2 \<and> e\<^sub>d\<^sub>1 = convert' [x] e\<^sub>n\<^sub>1 \<and> 
    e\<^sub>d\<^sub>2 = convert e\<^sub>n\<^sub>2" by fastforce
  ultimately have "NApp (NLam x t e\<^sub>n\<^sub>1) e\<^sub>n\<^sub>2 \<leadsto>\<^sub>n substn x e\<^sub>n\<^sub>2 e\<^sub>n\<^sub>1 \<and> 
    substd 0 (convert e\<^sub>n\<^sub>2) (convert' [x] e\<^sub>n\<^sub>1) = convert (substn x e\<^sub>n\<^sub>2 e\<^sub>n\<^sub>1)" by (simp add: convert_def)
  with N show ?case by fastforce
qed

lemma [simp]: "iter (\<leadsto>\<^sub>d) (convert e\<^sub>n) e\<^sub>d' \<Longrightarrow> free_vars e\<^sub>n = {} \<Longrightarrow> 
  \<exists>e\<^sub>n'. iter (\<leadsto>\<^sub>n) e\<^sub>n e\<^sub>n' \<and> e\<^sub>d' = convert e\<^sub>n'"
proof (induction "convert e\<^sub>n" e\<^sub>d' arbitrary: e\<^sub>n rule: iter.induct)
  case (iter_step e\<^sub>d' e\<^sub>d'')
  then obtain e\<^sub>n' where "e\<^sub>n \<leadsto>\<^sub>n e\<^sub>n' \<and> e\<^sub>d' = convert e\<^sub>n'" by fastforce
  moreover with iter_step obtain e\<^sub>n'' where "iter (\<leadsto>\<^sub>n) e\<^sub>n' e\<^sub>n'' \<and> e\<^sub>d'' = convert e\<^sub>n''" by fastforce
  ultimately have "iter (\<leadsto>\<^sub>n) e\<^sub>n e\<^sub>n'' \<and> e\<^sub>d'' = convert e\<^sub>n''" by fastforce
  thus ?case by fastforce
qed force+

end