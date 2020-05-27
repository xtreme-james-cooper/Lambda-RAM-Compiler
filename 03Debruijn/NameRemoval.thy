theory NameRemoval
  imports "../02Source/Named" BigStep "../00Utils/AssocList"
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

theorem correctnd [simp]: "e \<Down> v \<Longrightarrow> free_vars e = {} \<Longrightarrow> convert e \<Down>\<^sub>d convert v"
proof (induction e v rule: evaln.induct)
  case (evn_app e\<^sub>1 x t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  hence "e\<^sub>1 \<Down> NLam x t e\<^sub>1'" by simp
  moreover from evn_app have "free_vars e\<^sub>1 = {}" by simp
  ultimately have "free_vars (NLam x t e\<^sub>1') = {}" by (metis free_vars_eval)
  hence X: "free_vars e\<^sub>1' \<subseteq> insert x (set [])" by simp
  moreover from evn_app have Y: "free_vars v\<^sub>2 \<subseteq> set []" by simp
  ultimately have "free_vars (substn x v\<^sub>2 e\<^sub>1') \<subseteq> set []" by (metis free_vars_subst)
  with evn_app X Y show ?case by (simp add: convert_def)
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

theorem completend [simp]: "convert e\<^sub>n \<Down>\<^sub>d v\<^sub>d \<Longrightarrow> free_vars e\<^sub>n = {} \<Longrightarrow> 
  \<exists>v\<^sub>n. e\<^sub>n \<Down> v\<^sub>n \<and> v\<^sub>d = convert v\<^sub>n"
proof (induction "convert e\<^sub>n" v\<^sub>d arbitrary: e\<^sub>n rule: big_evald.induct)
  case (bevd_const k)
  hence "e\<^sub>n \<Down> NConst k \<and> DConst k = convert (NConst k)" by (cases e\<^sub>n) (simp_all add: convert_def)
  thus ?case by fastforce
next
  case (bevd_lam t e)
  then obtain x e' where "e\<^sub>n = NLam x t e' \<and> e = convert' [x] e'" 
    by (cases e\<^sub>n) (simp_all add: convert_def)
  hence "e\<^sub>n \<Down> NLam x t e' \<and> DLam t e = convert (NLam x t e')" by (simp add: convert_def)
  thus ?case by fastforce
next
  case (bevd_app e\<^sub>1 t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  then obtain e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 where E: "e\<^sub>n = NApp e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 \<and> e\<^sub>1 = convert e\<^sub>n\<^sub>1 \<and> e\<^sub>2 = convert e\<^sub>n\<^sub>2" 
    by (cases e\<^sub>n) (simp_all add: convert_def)
  with bevd_app obtain v\<^sub>n\<^sub>1 where V1: "e\<^sub>n\<^sub>1 \<Down> v\<^sub>n\<^sub>1 \<and> DLam t e\<^sub>1' = convert v\<^sub>n\<^sub>1" by fastforce
  then obtain x e\<^sub>n\<^sub>1' where X: "v\<^sub>n\<^sub>1 = NLam x t e\<^sub>n\<^sub>1' \<and> e\<^sub>1' = convert' [x] e\<^sub>n\<^sub>1'"
    by (cases v\<^sub>n\<^sub>1) (simp_all add: convert_def)
  from bevd_app E obtain v\<^sub>n\<^sub>2 where V2: "e\<^sub>n\<^sub>2 \<Down> v\<^sub>n\<^sub>2 \<and> v\<^sub>2 = convert v\<^sub>n\<^sub>2" by fastforce
  from bevd_app E have "free_vars e\<^sub>n\<^sub>1 = {}" by simp
  with V1 X have "free_vars (NLam x t e\<^sub>n\<^sub>1') = {}" by (metis free_vars_eval)
  hence Y: "free_vars e\<^sub>n\<^sub>1' \<subseteq> {x}" by simp
  from bevd_app E have "free_vars e\<^sub>n\<^sub>2 = {}" by simp
  with V2 have Z: "free_vars v\<^sub>n\<^sub>2 = {}" by auto
  with Y have "free_vars (substn x v\<^sub>n\<^sub>2 e\<^sub>n\<^sub>1') = {}" by (metis free_vars_subst subset_empty)
  with bevd_app X V2 Y Z have "\<exists>v\<^sub>n. substn x v\<^sub>n\<^sub>2 e\<^sub>n\<^sub>1' \<Down> v\<^sub>n \<and> v = convert v\<^sub>n" 
    by (simp add: convert_def)
  then obtain v\<^sub>n where "substn x v\<^sub>n\<^sub>2 e\<^sub>n\<^sub>1' \<Down> v\<^sub>n \<and> v = convert v\<^sub>n" by fastforce
  with V1 X V2 have "NApp e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 \<Down> v\<^sub>n \<and> v = convert v\<^sub>n" by fastforce
  with E show ?case by fastforce
qed

(* Now we can finish the deferred progress lemma from 01Source/Named *)

theorem progressn [simp]: "Map.empty \<turnstile>\<^sub>n e : t \<Longrightarrow> \<exists>v. e \<Down> v"
proof -
  assume X: "Map.empty \<turnstile>\<^sub>n e : t"
  hence "[] \<turnstile>\<^sub>d convert e : t" by simp
  then obtain v\<^sub>d where "vald v\<^sub>d \<and> convert e \<Down>\<^sub>d v\<^sub>d" by fastforce
  with X obtain v\<^sub>n where "e \<Down> v\<^sub>n \<and> v\<^sub>d = convert v\<^sub>n" by fastforce
  thus ?thesis by fastforce
qed

end