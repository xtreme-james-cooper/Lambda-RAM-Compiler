theory NameRemoval
  imports "../02Typed/Typechecking" BigStep
begin

subsection \<open>Name-Removal\<close>

text \<open>Now, we  \<close>

primrec convert' :: "var list \<Rightarrow> ty expr\<^sub>s \<Rightarrow> expr\<^sub>d" where
  "convert' \<Phi> (Var\<^sub>s x) = Var\<^sub>d (the (idx_of \<Phi> x))"
| "convert' \<Phi> (Const\<^sub>s k) = Const\<^sub>d k"
| "convert' \<Phi> (Lam\<^sub>s x t e) = Lam\<^sub>d t (convert' (insert_at 0 x \<Phi>) e)"
| "convert' \<Phi> (App\<^sub>s e\<^sub>1 e\<^sub>2) = App\<^sub>d (convert' \<Phi> e\<^sub>1) (convert' \<Phi> e\<^sub>2)"

definition convert :: "ty expr\<^sub>s \<Rightarrow> expr\<^sub>d" where
  "convert e \<equiv> convert' [] e"

lemma [simp]: "value\<^sub>s e \<Longrightarrow> value\<^sub>d (convert' \<Phi> e)"
  by (induction e) (simp_all add: Let_def)

lemma [simp]: "y \<notin> all_vars\<^sub>s e \<Longrightarrow> x \<le> length \<Phi> \<Longrightarrow> free_vars\<^sub>s e \<subseteq> set \<Phi> \<Longrightarrow>
  convert' (insert_at x y \<Phi>) e = incr\<^sub>d x (convert' \<Phi> e)"
proof (induction e arbitrary: x \<Phi>)
  case (Var\<^sub>s z)
  moreover then obtain w where "idx_of \<Phi> z = Some w" by fastforce
  ultimately show ?case by simp
next
  case (Lam\<^sub>s z t e)
  moreover hence "free_vars\<^sub>s e \<subseteq> set (insert_at 0 z \<Phi>)" by auto
  ultimately show ?case by simp
qed simp_all

lemma [simp]: "x' \<notin> all_vars\<^sub>s e \<Longrightarrow> a \<le> length \<Phi> \<Longrightarrow> idx_of \<Phi> x = Some y \<Longrightarrow> a > y \<Longrightarrow> 
    convert' (insert_at a x \<Phi>) e = convert' (insert_at a x' \<Phi>) e"
  by (induction e arbitrary: a \<Phi> y) (auto simp add: incr_min split: option.splits)

abbreviation precede :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" (infix "precedes _ in" 50) where
  "x precedes a in as \<equiv> (case idx_of as a of Some y \<Rightarrow> x \<le> y | None \<Rightarrow> True)"

lemma [simp]: "0 precedes a in as"
  by (simp split: option.splits)

lemma [simp]: "y \<le> length \<Phi> \<Longrightarrow> y precedes x in \<Phi> \<Longrightarrow> y precedes x' in \<Phi> \<Longrightarrow> x' \<notin> all_vars\<^sub>s e \<Longrightarrow> 
  free_vars\<^sub>s e \<subseteq> insert x (set \<Phi>) \<Longrightarrow> 
    convert' (insert_at y x' \<Phi>) (subst_var\<^sub>s x x' e) = convert' (insert_at y x \<Phi>) e"
proof (induction e arbitrary: y \<Phi>)
  case (Lam\<^sub>s z t e)
  thus ?case
  proof (cases "x = z")
    case False
    with Lam\<^sub>s have X: "Suc y precedes x in insert_at 0 z \<Phi>" by (simp split: option.splits) 
    from Lam\<^sub>s have Y: "Suc y precedes x' in insert_at 0 z \<Phi>" by (simp split: option.splits) 
    from Lam\<^sub>s have "free_vars\<^sub>s e \<subseteq> insert x (set (insert_at 0 z \<Phi>))" by auto
    with Lam\<^sub>s False X Y show ?thesis by simp
  qed (simp_all split: option.splits)
qed (auto split: option.splits)

lemma convert_subst [simp]: "y \<le> length \<Phi> \<Longrightarrow> x \<notin> set \<Phi> \<Longrightarrow> free_vars\<^sub>s e \<subseteq> insert x (set \<Phi>) \<Longrightarrow>
  free_vars\<^sub>s e' \<subseteq> set \<Phi> \<Longrightarrow>
    convert' \<Phi> (subst\<^sub>s x e' e) = subst\<^sub>d y (convert' \<Phi> e') (convert' (insert_at y x \<Phi>) e)" 
proof (induction x e' e arbitrary: \<Phi> y rule: subst\<^sub>s.induct)
  case (1 x e' z)
  thus ?case
  proof (cases "idx_of \<Phi> z")
    case (Some w)
    have "y \<noteq> incr y w" by (metis incr_not_eq)
    with 1 Some show ?thesis by auto
  qed simp_all
next
  case (3 x e' z t e)
  let ?z' = "fresh (all_vars\<^sub>s e' \<union> all_vars\<^sub>s e \<union> {x, z})"
  have "finite (all_vars\<^sub>s e' \<union> all_vars\<^sub>s e \<union> {x, z})" by simp
  hence Z: "?z' \<notin> all_vars\<^sub>s e' \<union> all_vars\<^sub>s e \<union> {x, z}" by (metis fresh_is_fresh)
  from 3 Z have X: "free_vars\<^sub>s e' \<subseteq> set (insert_at 0 ?z' \<Phi>)" by auto
  from 3 have "free_vars\<^sub>s e \<subseteq> insert z (insert x (set \<Phi>))" by auto
  with Z have "free_vars\<^sub>s (subst_var\<^sub>s z ?z' e) \<subseteq> insert ?z' (insert x (set \<Phi>))" by auto
  hence "free_vars\<^sub>s (subst_var\<^sub>s z ?z' e) \<subseteq> insert x (set (insert_at 0 ?z' \<Phi>))" by auto
  with 3 X Z have H: "convert' (insert_at 0 ?z' \<Phi>) (subst\<^sub>s x e' (subst_var\<^sub>s z ?z' e)) = 
    subst\<^sub>d (Suc y) (convert' (insert_at 0 ?z' \<Phi>) e') 
      (convert' (insert_at (Suc y) x (insert_at 0 ?z' \<Phi>)) (subst_var\<^sub>s z ?z' e))" by fastforce
  from 3 have "free_vars\<^sub>s e \<subseteq> insert z (set (insert_at y x \<Phi>))" by auto
  with Z have "convert' (insert_at 0 ?z' (insert_at y x \<Phi>)) (subst_var\<^sub>s z ?z' e) =
    convert' (insert_at 0 z (insert_at y x \<Phi>)) e" by simp
  with 3 Z H show ?case by (simp add: Let_def)
qed simp_all

theorem correctnd [simp]: "e \<Down>\<^sub>s v \<Longrightarrow> free_vars\<^sub>s e = {} \<Longrightarrow> convert e \<Down>\<^sub>d convert v"
proof (induction e v rule: eval\<^sub>s.induct)
  case (ev\<^sub>s_app e\<^sub>1 x t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  hence "e\<^sub>1 \<Down>\<^sub>s Lam\<^sub>s x t e\<^sub>1'" by simp
  moreover from ev\<^sub>s_app have "free_vars\<^sub>s e\<^sub>1 = {}" by simp
  ultimately have "free_vars\<^sub>s (Lam\<^sub>s x t e\<^sub>1') = {}" by (metis free_vars_eval)
  hence X: "free_vars\<^sub>s e\<^sub>1' \<subseteq> insert x (set [])" by simp
  moreover from ev\<^sub>s_app have Y: "free_vars\<^sub>s v\<^sub>2 \<subseteq> set []" by simp
  ultimately have "free_vars\<^sub>s (subst\<^sub>s x v\<^sub>2 e\<^sub>1') \<subseteq> set []" by (metis free_vars_subst)
  with ev\<^sub>s_app X Y show ?case by (simp add: convert_def)
qed (simp_all add: convert_def)

lemma [simp]: "value\<^sub>d (convert' \<Phi> e) \<Longrightarrow> value\<^sub>s e"
  by (induction e) (simp_all add: Let_def)

lemma convert_val_back: "value\<^sub>d (convert e) \<Longrightarrow> value\<^sub>s e"
  by (simp add: convert_def)

lemma [dest]: "App\<^sub>d e\<^sub>d\<^sub>1 e\<^sub>d\<^sub>2 = convert e\<^sub>n \<Longrightarrow> 
    \<exists>e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2. e\<^sub>n = App\<^sub>s e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 \<and> e\<^sub>d\<^sub>1 = convert e\<^sub>n\<^sub>1 \<and> e\<^sub>d\<^sub>2 = convert e\<^sub>n\<^sub>2"
  by (cases e\<^sub>n) (simp_all add: convert_def)

lemma [dest]: "Lam\<^sub>d t e\<^sub>d = convert e\<^sub>n \<Longrightarrow> 
    \<exists>x e\<^sub>n'. e\<^sub>n = Lam\<^sub>s x t e\<^sub>n' \<and> e\<^sub>d = convert' [x] e\<^sub>n'"
  by (cases e\<^sub>n) (simp_all add: convert_def)

theorem completend [simp]: "convert e\<^sub>n \<Down>\<^sub>d v\<^sub>d \<Longrightarrow> free_vars\<^sub>s e\<^sub>n = {} \<Longrightarrow> 
  \<exists>v\<^sub>n. e\<^sub>n \<Down>\<^sub>s v\<^sub>n \<and> v\<^sub>d = convert v\<^sub>n"
proof (induction "convert e\<^sub>n" v\<^sub>d arbitrary: e\<^sub>n rule: big_eval\<^sub>d.induct)
  case (bev\<^sub>d_const k)
  hence "e\<^sub>n \<Down>\<^sub>s Const\<^sub>s k \<and> Const\<^sub>d k = convert (Const\<^sub>s k)" by (cases e\<^sub>n) (simp_all add: convert_def)
  thus ?case by fastforce
next
  case (bev\<^sub>d_lam t e)
  then obtain x e' where "e\<^sub>n = Lam\<^sub>s x t e' \<and> e = convert' [x] e'" 
    by (cases e\<^sub>n) (simp_all add: convert_def)
  hence "e\<^sub>n \<Down>\<^sub>s Lam\<^sub>s x t e' \<and> Lam\<^sub>d t e = convert (Lam\<^sub>s x t e')" by (simp add: convert_def)
  thus ?case by fastforce
next
  case (bev\<^sub>d_app e\<^sub>1 t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  then obtain e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 where E: "e\<^sub>n = App\<^sub>s e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 \<and> e\<^sub>1 = convert e\<^sub>n\<^sub>1 \<and> e\<^sub>2 = convert e\<^sub>n\<^sub>2" 
    by (cases e\<^sub>n) (simp_all add: convert_def)
  with bev\<^sub>d_app obtain v\<^sub>n\<^sub>1 where V1: "e\<^sub>n\<^sub>1 \<Down>\<^sub>s v\<^sub>n\<^sub>1 \<and> Lam\<^sub>d t e\<^sub>1' = convert v\<^sub>n\<^sub>1" by fastforce
  then obtain x e\<^sub>n\<^sub>1' where X: "v\<^sub>n\<^sub>1 = Lam\<^sub>s x t e\<^sub>n\<^sub>1' \<and> e\<^sub>1' = convert' [x] e\<^sub>n\<^sub>1'"
    by (cases v\<^sub>n\<^sub>1) (simp_all add: convert_def)
  from bev\<^sub>d_app E obtain v\<^sub>n\<^sub>2 where V2: "e\<^sub>n\<^sub>2 \<Down>\<^sub>s v\<^sub>n\<^sub>2 \<and> v\<^sub>2 = convert v\<^sub>n\<^sub>2" by fastforce
  from bev\<^sub>d_app E have "free_vars\<^sub>s e\<^sub>n\<^sub>1 = {}" by simp
  with V1 X have "free_vars\<^sub>s (Lam\<^sub>s x t e\<^sub>n\<^sub>1') = {}" by (metis free_vars_eval)
  hence Y: "free_vars\<^sub>s e\<^sub>n\<^sub>1' \<subseteq> {x}" by simp
  from bev\<^sub>d_app E have "free_vars\<^sub>s e\<^sub>n\<^sub>2 = {}" by simp
  with V2 have Z: "free_vars\<^sub>s v\<^sub>n\<^sub>2 = {}" by auto
  with Y have "free_vars\<^sub>s (subst\<^sub>s x v\<^sub>n\<^sub>2 e\<^sub>n\<^sub>1') = {}" by (metis free_vars_subst subset_empty)
  with bev\<^sub>d_app X V2 Y Z have "\<exists>v\<^sub>n. subst\<^sub>s x v\<^sub>n\<^sub>2 e\<^sub>n\<^sub>1' \<Down>\<^sub>s v\<^sub>n \<and> v = convert v\<^sub>n" 
    by (simp add: convert_def)
  then obtain v\<^sub>n where "subst\<^sub>s x v\<^sub>n\<^sub>2 e\<^sub>n\<^sub>1' \<Down>\<^sub>s v\<^sub>n \<and> v = convert v\<^sub>n" by fastforce
  with V1 X V2 have "App\<^sub>s e\<^sub>n\<^sub>1 e\<^sub>n\<^sub>2 \<Down>\<^sub>s v\<^sub>n \<and> v = convert v\<^sub>n" by fastforce
  with E show ?case by fastforce
qed


(* typesafety *)

lemma convert_remove_shadows [simp]: "finite vs \<Longrightarrow> free_vars\<^sub>s e \<subseteq> set \<Phi> \<Longrightarrow>
  convert' \<Phi> (remove_shadows\<^sub>s' vs e) = convert' \<Phi> e"
proof (induction e arbitrary: \<Phi> vs)
  case (Lam\<^sub>s x t e)
  let ?e = "remove_shadows\<^sub>s' (insert x vs) e"
  let ?x = "fresh (vs \<union> all_vars\<^sub>s ?e)"
  from Lam\<^sub>s have "finite (vs \<union> all_vars\<^sub>s ?e)" by simp
  hence X: "?x \<notin> vs \<union> all_vars\<^sub>s ?e" by (metis fresh_is_fresh)
  from Lam\<^sub>s have "free_vars\<^sub>s e \<subseteq> insert x (set \<Phi>)" by auto
  with Lam\<^sub>s X show ?case by (simp add: Let_def)
qed simp_all
 
lemma typesafe\<^sub>d' [simp]: "\<Gamma> \<turnstile>\<^sub>t e : t \<Longrightarrow> dom \<Gamma> = set \<Phi> \<Longrightarrow> bound_vars\<^sub>s e \<inter> set \<Phi> = {} \<Longrightarrow> 
  no_shadowing\<^sub>s e \<Longrightarrow> map (the \<circ> \<Gamma>) \<Phi> \<turnstile>\<^sub>d convert' \<Phi> e : t"
proof (induction \<Gamma> e t arbitrary: \<Phi> rule: typing\<^sub>t.induct)
  case (tc\<^sub>t_var \<Gamma> x t)
  hence "x \<in> set \<Phi>" by auto
  with tc\<^sub>t_var show ?case by auto
next
  case (tc\<^sub>t_lam \<Gamma> x t\<^sub>1 e t\<^sub>2)
  moreover hence "dom (\<Gamma>(x \<mapsto> t\<^sub>1)) = set (insert_at 0 x \<Phi>)" by simp
  moreover from tc\<^sub>t_lam have "bound_vars\<^sub>s e \<inter> set (insert_at 0 x \<Phi>) = {}" by simp
  moreover from tc\<^sub>t_lam have "no_shadowing\<^sub>s e" by simp
  ultimately have "map (the \<circ> \<Gamma>(x \<mapsto> t\<^sub>1)) (insert_at 0 x \<Phi>) \<turnstile>\<^sub>d convert' (insert_at 0 x \<Phi>) e : t\<^sub>2" 
    by blast
  with tc\<^sub>t_lam have "map (the \<circ> \<Gamma>) \<Phi> \<turnstile>\<^sub>d convert' \<Phi> (Lam\<^sub>s x t\<^sub>1 e) : Arrow t\<^sub>1 t\<^sub>2" by simp
  thus ?case by blast
next
  case (tc\<^sub>t_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  moreover hence "bound_vars\<^sub>s e\<^sub>1 \<inter> set \<Phi> = {}" by auto
  ultimately have T: "map (the \<circ> \<Gamma>) \<Phi> \<turnstile>\<^sub>d convert' \<Phi> e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by fastforce
  from tc\<^sub>t_app have "bound_vars\<^sub>s e\<^sub>2 \<inter> set \<Phi> = {}" by auto
  with tc\<^sub>t_app have "map (the \<circ> \<Gamma>) \<Phi> \<turnstile>\<^sub>d convert' \<Phi> e\<^sub>2 : t\<^sub>1" by fastforce
  with T have "map (the \<circ> \<Gamma>) \<Phi> \<turnstile>\<^sub>d convert' \<Phi> (App\<^sub>s e\<^sub>1 e\<^sub>2) : t\<^sub>2" by simp
  thus ?case by blast
qed simp_all

theorem typesafend [simp]: "Map.empty \<turnstile>\<^sub>t e : t \<Longrightarrow> [] \<turnstile>\<^sub>d convert e : t"
proof -
  assume T: "Map.empty \<turnstile>\<^sub>t e : t"
  hence "Map.empty \<turnstile>\<^sub>t remove_shadows\<^sub>s e : t" by simp
  moreover have "bound_vars\<^sub>s (remove_shadows\<^sub>s e) \<inter> set [] = {}" by simp
  moreover have "no_shadowing\<^sub>s (remove_shadows\<^sub>s e)" by simp
  ultimately have "[] \<turnstile>\<^sub>d convert' [] (remove_shadows\<^sub>s e) : t" 
    by (metis typesafe\<^sub>d' dom_empty empty_set list.simps(8))
  with T show ?thesis by (simp add: convert_def remove_shadows\<^sub>s_def)
qed

(* Now we can finish the deferred progress lemmas from 01Source/Named and 02Typed/Typed *)

theorem progresst [simp]: "Map.empty \<turnstile>\<^sub>t e : t \<Longrightarrow> \<exists>v. e \<Down>\<^sub>s v"
proof -
  assume X: "Map.empty \<turnstile>\<^sub>t e : t"
  hence "[] \<turnstile>\<^sub>d convert e : t" by simp
  then obtain v\<^sub>d where "value\<^sub>d v\<^sub>d \<and> convert e \<Down>\<^sub>d v\<^sub>d" by fastforce
  with X obtain v\<^sub>n where "e \<Down>\<^sub>s v\<^sub>n \<and> v\<^sub>d = convert v\<^sub>n" by fastforce
  thus ?thesis by fastforce
qed

theorem progressn [simp]: "Map.empty \<turnstile>\<^sub>t e : t \<Longrightarrow> \<exists>v. erase e \<Down>\<^sub>s v"
proof -
  assume X: "Map.empty \<turnstile>\<^sub>t e : t"
  then obtain v\<^sub>t where "e \<Down>\<^sub>s v\<^sub>t" by fastforce
  hence "erase e \<Down>\<^sub>s erase v\<^sub>t" by simp
  thus ?thesis by fastforce
qed

end