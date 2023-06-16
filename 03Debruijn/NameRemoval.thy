theory NameRemoval
  imports "../02Typed/Typechecking" BigStep
begin

subsection \<open>Name-Removal\<close>

text \<open>Now, we define our conversion from named to Debruijn languages. We accumulate a naming context 
of variables, and use their positions in the context to determine their associated index.\<close>

primrec unname' :: "var list \<Rightarrow> ty expr\<^sub>s \<Rightarrow> expr\<^sub>d" where
  "unname' \<Phi> (Var\<^sub>s x) = Var\<^sub>d (the (idx_of \<Phi> x))"
| "unname' \<Phi> (Const\<^sub>s k) = Const\<^sub>d k"
| "unname' \<Phi> (Lam\<^sub>s x t e\<^sub>t) = Lam\<^sub>d t (unname' (insert_at 0 x \<Phi>) e\<^sub>t)"
| "unname' \<Phi> (App\<^sub>s e\<^sub>t\<^sub>1 e\<^sub>t\<^sub>2) = App\<^sub>d (unname' \<Phi> e\<^sub>t\<^sub>1) (unname' \<Phi> e\<^sub>t\<^sub>2)"
| "unname' \<Phi> (Let\<^sub>s x e\<^sub>t\<^sub>1 e\<^sub>t\<^sub>2) = Let\<^sub>d (unname' \<Phi> e\<^sub>t\<^sub>1) (unname' (insert_at 0 x \<Phi>) e\<^sub>t\<^sub>2)"

text \<open>The unnaming operation commutes with the various operations on expressions as we would expect 
it to. In particular, it connects capture-avoiding substitution and the simpler Debruijn 
substitution (see \<open>unname_subst\<close>).\<close>

lemma unname_insert_at [simp]: "y \<notin> all_vars\<^sub>s e\<^sub>t \<Longrightarrow> x \<le> length \<Phi> \<Longrightarrow> free_vars\<^sub>s e\<^sub>t \<subseteq> set \<Phi> \<Longrightarrow>
  unname' (insert_at x y \<Phi>) e\<^sub>t = incr\<^sub>d x (unname' \<Phi> e\<^sub>t)"
proof (induction e\<^sub>t arbitrary: x \<Phi>)
  case (Var\<^sub>s z)
  moreover then obtain w where "idx_of \<Phi> z = Some w" by fastforce
  ultimately show ?case by simp
next
  case (Lam\<^sub>s z t e\<^sub>t)
  moreover hence "free_vars\<^sub>s e\<^sub>t \<subseteq> set (insert_at 0 z \<Phi>)" by auto
  ultimately show ?case by simp
next
  case (Let\<^sub>s z e\<^sub>1\<^sub>t e\<^sub>2\<^sub>t)
  moreover hence "free_vars\<^sub>s e\<^sub>2\<^sub>t \<subseteq> set (insert_at 0 z \<Phi>)" by auto
  ultimately show ?case by simp
qed simp_all

lemma unname_insert_at_irrelevant [simp]: "x' \<notin> all_vars\<^sub>s e\<^sub>t \<Longrightarrow> y \<le> length \<Phi> \<Longrightarrow> 
    \<not>y precedes x in \<Phi> \<Longrightarrow> unname' (insert_at y x \<Phi>) e\<^sub>t = unname' (insert_at y x' \<Phi>) e\<^sub>t"
  by (induction e\<^sub>t arbitrary: y \<Phi>) (auto simp add: incr_min split: option.splits)

lemma unname_subst_var [simp]: "y \<le> length \<Phi> \<Longrightarrow> y precedes x in \<Phi> \<Longrightarrow> y precedes x' in \<Phi> \<Longrightarrow> 
  x' \<notin> all_vars\<^sub>s e\<^sub>t \<Longrightarrow> free_vars\<^sub>s e\<^sub>t \<subseteq> insert x (set \<Phi>) \<Longrightarrow> 
    unname' (insert_at y x' \<Phi>) (subst_var\<^sub>s x x' e\<^sub>t) = unname' (insert_at y x \<Phi>) e\<^sub>t"
proof (induction e\<^sub>t arbitrary: y \<Phi>)
  case (Lam\<^sub>s z t e\<^sub>t)
  thus ?case
  proof (cases "x = z")
    case False
    with Lam\<^sub>s have X: "Suc y precedes x in insert_at 0 z \<Phi>" by (simp split: option.splits) 
    from Lam\<^sub>s have Y: "Suc y precedes x' in insert_at 0 z \<Phi>" by (simp split: option.splits) 
    from Lam\<^sub>s have "free_vars\<^sub>s e\<^sub>t \<subseteq> insert x (set (insert_at 0 z \<Phi>))" by auto
    with Lam\<^sub>s False X Y show ?thesis by simp
  qed (simp_all split: option.splits)
qed (auto split: option.splits)

lemma unname_subst [simp]: "y \<le> length \<Phi> \<Longrightarrow> x \<notin> set \<Phi> \<Longrightarrow> free_vars\<^sub>s e\<^sub>t \<subseteq> insert x (set \<Phi>) \<Longrightarrow>
  free_vars\<^sub>s e\<^sub>t' \<subseteq> set \<Phi> \<Longrightarrow>
    unname' \<Phi> (subst\<^sub>s x e\<^sub>t' e\<^sub>t) = subst\<^sub>d y (unname' \<Phi> e\<^sub>t') (unname' (insert_at y x \<Phi>) e\<^sub>t)" 
proof (induction x e\<^sub>t' e\<^sub>t arbitrary: \<Phi> y rule: subst\<^sub>s.induct)
  case (1 x e\<^sub>t' z)
  thus ?case
  proof (cases "idx_of \<Phi> z")
    case (Some w)
    have "y \<noteq> incr y w" by (metis incr_not_eq)
    with 1 Some show ?thesis by auto
  qed simp_all
next
  case (3 x e\<^sub>t' z t e\<^sub>t)
  let ?z' = "fresh (all_vars\<^sub>s e\<^sub>t' \<union> all_vars\<^sub>s e\<^sub>t \<union> {x, z})"
  have "finite (all_vars\<^sub>s e\<^sub>t' \<union> all_vars\<^sub>s e\<^sub>t \<union> {x, z})" by simp
  hence Z: "?z' \<notin> all_vars\<^sub>s e\<^sub>t' \<union> all_vars\<^sub>s e\<^sub>t \<union> {x, z}" by (metis fresh_is_fresh)
  from 3 Z have X: "free_vars\<^sub>s e\<^sub>t' \<subseteq> set (insert_at 0 ?z' \<Phi>)" by auto
  from 3 have "free_vars\<^sub>s e\<^sub>t \<subseteq> insert z (insert x (set \<Phi>))" by auto
  with Z have "free_vars\<^sub>s (subst_var\<^sub>s z ?z' e\<^sub>t) \<subseteq> insert ?z' (insert x (set \<Phi>))" by auto
  hence "free_vars\<^sub>s (subst_var\<^sub>s z ?z' e\<^sub>t) \<subseteq> insert x (set (insert_at 0 ?z' \<Phi>))" by auto
  with 3 X Z have H: "unname' (insert_at 0 ?z' \<Phi>) (subst\<^sub>s x e\<^sub>t' (subst_var\<^sub>s z ?z' e\<^sub>t)) = 
    subst\<^sub>d (Suc y) (unname' (insert_at 0 ?z' \<Phi>) e\<^sub>t') 
      (unname' (insert_at (Suc y) x (insert_at 0 ?z' \<Phi>)) (subst_var\<^sub>s z ?z' e\<^sub>t))" by fastforce
  from 3 have "free_vars\<^sub>s e\<^sub>t \<subseteq> insert z (set (insert_at y x \<Phi>))" by auto
  with Z have "unname' (insert_at 0 ?z' (insert_at y x \<Phi>)) (subst_var\<^sub>s z ?z' e\<^sub>t) =
    unname' (insert_at 0 z (insert_at y x \<Phi>)) e\<^sub>t" by simp
  with 3 Z H show ?case by (simp add: Let_def)
qed simp_all

text \<open>The unnaming operation ignores alpha-conversion, as we would expect.\<close>

lemma unname_remove_shadows [simp]: "finite vs \<Longrightarrow> free_vars\<^sub>s e\<^sub>t \<subseteq> set \<Phi> \<Longrightarrow>
  unname' \<Phi> (remove_shadows\<^sub>s' vs e\<^sub>t) = unname' \<Phi> e\<^sub>t"
proof (induction e\<^sub>t arbitrary: \<Phi> vs)
  case (Lam\<^sub>s x t e\<^sub>t)
  let ?e = "remove_shadows\<^sub>s' (insert x vs) e\<^sub>t"
  let ?x = "fresh (vs \<union> all_vars\<^sub>s ?e)"
  from Lam\<^sub>s have "finite (vs \<union> all_vars\<^sub>s ?e)" by simp
  hence X: "?x \<notin> vs \<union> all_vars\<^sub>s ?e" by (metis fresh_is_fresh)
  from Lam\<^sub>s have "free_vars\<^sub>s e\<^sub>t \<subseteq> insert x (set \<Phi>)" by auto
  with Lam\<^sub>s X show ?case by (simp add: Let_def)
qed simp_all

text \<open>The unnaming operation is also typesafe. (We need the no-shadowing condition to make the 
induction work, but fortunately \<open>unname_remove_shadows\<close> will let us eliminate it as a top-level 
precondition.)\<close>

lemma typesafe\<^sub>d' [simp]: "\<Gamma> \<turnstile>\<^sub>t e\<^sub>t : t \<Longrightarrow> dom \<Gamma> = set \<Phi> \<Longrightarrow> bound_vars\<^sub>s e\<^sub>t \<inter> set \<Phi> = {} \<Longrightarrow> 
  no_shadowing\<^sub>s e\<^sub>t \<Longrightarrow> map (the \<circ> \<Gamma>) \<Phi> \<turnstile>\<^sub>d unname' \<Phi> e\<^sub>t : t"
proof (induction \<Gamma> e\<^sub>t t arbitrary: \<Phi> rule: typing\<^sub>t.induct)
  case (tc\<^sub>t_var \<Gamma> x t)
  hence "x \<in> set \<Phi>" by auto
  with tc\<^sub>t_var show ?case by auto
next
  case (tc\<^sub>t_lam \<Gamma> x t\<^sub>1 e\<^sub>t t\<^sub>2)
  moreover hence "dom (\<Gamma>(x \<mapsto> t\<^sub>1)) = set (insert_at 0 x \<Phi>)" by simp
  moreover from tc\<^sub>t_lam have "bound_vars\<^sub>s e\<^sub>t \<inter> set (insert_at 0 x \<Phi>) = {}" by simp
  moreover from tc\<^sub>t_lam have "no_shadowing\<^sub>s e\<^sub>t" by simp
  ultimately have "map (the \<circ> \<Gamma>(x \<mapsto> t\<^sub>1)) (insert_at 0 x \<Phi>) \<turnstile>\<^sub>d unname' (insert_at 0 x \<Phi>) e\<^sub>t : t\<^sub>2" 
    by blast
  with tc\<^sub>t_lam have "map (the \<circ> \<Gamma>) \<Phi> \<turnstile>\<^sub>d unname' \<Phi> (Lam\<^sub>s x t\<^sub>1 e\<^sub>t) : Arrow t\<^sub>1 t\<^sub>2" by simp
  thus ?case by blast
next
  case (tc\<^sub>t_app \<Gamma> e\<^sub>t\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>t\<^sub>2)
  moreover hence "bound_vars\<^sub>s e\<^sub>t\<^sub>1 \<inter> set \<Phi> = {}" by auto
  ultimately have T: "map (the \<circ> \<Gamma>) \<Phi> \<turnstile>\<^sub>d unname' \<Phi> e\<^sub>t\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by fastforce
  from tc\<^sub>t_app have "bound_vars\<^sub>s e\<^sub>t\<^sub>2 \<inter> set \<Phi> = {}" by auto
  with tc\<^sub>t_app have "map (the \<circ> \<Gamma>) \<Phi> \<turnstile>\<^sub>d unname' \<Phi> e\<^sub>t\<^sub>2 : t\<^sub>1" by fastforce
  with T have "map (the \<circ> \<Gamma>) \<Phi> \<turnstile>\<^sub>d unname' \<Phi> (App\<^sub>s e\<^sub>t\<^sub>1 e\<^sub>t\<^sub>2) : t\<^sub>2" by simp
  thus ?case by blast
qed simp_all

text \<open>The full unnaming of closed terms operation follows immediately, and we can use it to prove 
our correctness theorems.\<close>

text \<open>Since this is the first full conversion we have done, we will take a moment to explain exactly 
what we prove. There are three theorems for the conversion: typesafety, showing that any well-typed 
abstract state is converted to a well-typed concrete state; correctness proper, showing that if an 
abstract state evaluates to some value, then the concrete version of that state evaluates to the 
concrete version of that value; and completeness, showing that if the concrete version of an state 
evaluates to the concrete version of a value, then the abstract state evaluates to the abstract 
value. (At the moment, our states are just expressions, but they will get more complicated as we 
go on.) As mentioned in the introduction, there are complications, particularly with correctness, 
since our conversion function often runs the other direction, and we have to prove a number of 
reconstruction lemmas to determine what an appropriate abstract state had to have been. (In the 
present stage, \<open>unname_to_app\<close> and \<open>unname_to_lam\<close> are our reconstruction lemmas; since this stage's 
conversion runs "the right direction", they are needed for completeness rather than correctness.) We 
also do not prove all the theorems for all the stages, since the execution model gets less 
structured as we go along: once we reach Tree Code (stage 6) we no longer have a typing judgement, 
so typesafety is lost, and once we reach Assembly (stage 13), the complexity of the reconstruction 
lemmas required becomes so large that we abandon completeness as well. We always prove correctness, 
of course, because composing all our correctness theorems is exactly what gives us our ultimate 
correctness proof.\<close>

definition unname :: "ty expr\<^sub>s \<Rightarrow> expr\<^sub>d" where
  "unname e\<^sub>t \<equiv> unname' [] e\<^sub>t"

theorem typesafe\<^sub>d [simp]: "Map.empty \<turnstile>\<^sub>t e\<^sub>t : t \<Longrightarrow> [] \<turnstile>\<^sub>d unname e\<^sub>t : t"
proof -
  assume T: "Map.empty \<turnstile>\<^sub>t e\<^sub>t : t"
  hence "Map.empty \<turnstile>\<^sub>t remove_shadows\<^sub>s e\<^sub>t : t" by simp
  moreover have "bound_vars\<^sub>s (remove_shadows\<^sub>s e\<^sub>t) \<inter> set [] = {}" by simp
  moreover have "no_shadowing\<^sub>s (remove_shadows\<^sub>s e\<^sub>t)" by simp
  ultimately have "[] \<turnstile>\<^sub>d unname' [] (remove_shadows\<^sub>s e\<^sub>t) : t" 
    by (metis typesafe\<^sub>d' dom_empty empty_set list.simps(8))
  with T show ?thesis by (simp add: unname_def remove_shadows\<^sub>s_def)
qed

theorem correct\<^sub>d [simp]: "e\<^sub>t \<Down>\<^sub>s v\<^sub>s \<Longrightarrow> free_vars\<^sub>s e\<^sub>t = {} \<Longrightarrow> unname e\<^sub>t \<Down>\<^sub>d unname v\<^sub>s"
proof (induction e\<^sub>t v\<^sub>s rule: eval\<^sub>s.induct)
  case (ev\<^sub>s_app e\<^sub>t\<^sub>1 x t e\<^sub>t\<^sub>1' e\<^sub>t\<^sub>2 v\<^sub>s\<^sub>2 v\<^sub>s)
  hence "e\<^sub>t\<^sub>1 \<Down>\<^sub>s Lam\<^sub>s x t e\<^sub>t\<^sub>1'" by simp
  moreover from ev\<^sub>s_app have "free_vars\<^sub>s e\<^sub>t\<^sub>1 = {}" by simp
  ultimately have "free_vars\<^sub>s (Lam\<^sub>s x t e\<^sub>t\<^sub>1') = {}" by (metis free_vars_eval)
  hence X: "free_vars\<^sub>s e\<^sub>t\<^sub>1' \<subseteq> insert x (set [])" by simp
  moreover from ev\<^sub>s_app have Y: "free_vars\<^sub>s v\<^sub>s\<^sub>2 \<subseteq> set []" by simp
  ultimately have "free_vars\<^sub>s (subst\<^sub>s x v\<^sub>s\<^sub>2 e\<^sub>t\<^sub>1') \<subseteq> set []" by (metis free_vars_subst)
  with ev\<^sub>s_app X Y show ?case by (simp add: unname_def)
qed (simp_all add: unname_def)

lemma unname_to_app [dest]: "App\<^sub>d e\<^sub>d\<^sub>1 e\<^sub>d\<^sub>2 = unname e\<^sub>t \<Longrightarrow> 
    \<exists>e\<^sub>t\<^sub>1 e\<^sub>t\<^sub>2. e\<^sub>t = App\<^sub>s e\<^sub>t\<^sub>1 e\<^sub>t\<^sub>2 \<and> e\<^sub>d\<^sub>1 = unname e\<^sub>t\<^sub>1 \<and> e\<^sub>d\<^sub>2 = unname e\<^sub>t\<^sub>2"
  by (cases e\<^sub>t) (simp_all add: unname_def)

lemma unname_to_lam [dest]: "Lam\<^sub>d t e\<^sub>d = unname e\<^sub>t \<Longrightarrow> 
    \<exists>x e\<^sub>t'. e\<^sub>t = Lam\<^sub>s x t e\<^sub>t' \<and> e\<^sub>d = unname' [x] e\<^sub>t'"
  by (cases e\<^sub>t) (simp_all add: unname_def)

theorem complete\<^sub>d [simp]: "unname e\<^sub>t \<Down>\<^sub>d v\<^sub>d \<Longrightarrow> free_vars\<^sub>s e\<^sub>t = {} \<Longrightarrow> \<exists>v\<^sub>t. e\<^sub>t \<Down>\<^sub>s v\<^sub>t \<and> v\<^sub>d = unname v\<^sub>t"
proof (induction "unname e\<^sub>t" v\<^sub>d arbitrary: e\<^sub>t rule: big_eval\<^sub>d.induct)
  case (bev\<^sub>d_const n)
  hence "e\<^sub>t \<Down>\<^sub>s Const\<^sub>s n \<and> Const\<^sub>d n = unname (Const\<^sub>s n)" by (cases e\<^sub>t) (simp_all add: unname_def)
  thus ?case by fastforce
next
  case (bev\<^sub>d_lam t e\<^sub>d)
  then obtain x e' where "e\<^sub>t = Lam\<^sub>s x t e' \<and> e\<^sub>d = unname' [x] e'" 
    by (cases e\<^sub>t) (simp_all add: unname_def)
  hence "e\<^sub>t \<Down>\<^sub>s Lam\<^sub>s x t e' \<and> Lam\<^sub>d t e\<^sub>d = unname (Lam\<^sub>s x t e')" by (simp add: unname_def)
  thus ?case by fastforce
next
  case (bev\<^sub>d_app e\<^sub>d\<^sub>1 t e\<^sub>d\<^sub>1' e\<^sub>d\<^sub>2 v\<^sub>d\<^sub>2 v\<^sub>d)
  then obtain e\<^sub>t\<^sub>1 e\<^sub>t\<^sub>2 where E: "e\<^sub>t = App\<^sub>s e\<^sub>t\<^sub>1 e\<^sub>t\<^sub>2 \<and> e\<^sub>d\<^sub>1 = unname e\<^sub>t\<^sub>1 \<and> e\<^sub>d\<^sub>2 = unname e\<^sub>t\<^sub>2" 
    by (cases e\<^sub>t) (simp_all add: unname_def)
  with bev\<^sub>d_app obtain v\<^sub>t\<^sub>1 where V1: "e\<^sub>t\<^sub>1 \<Down>\<^sub>s v\<^sub>t\<^sub>1 \<and> Lam\<^sub>d t e\<^sub>d\<^sub>1' = unname v\<^sub>t\<^sub>1" by fastforce
  then obtain x e\<^sub>t\<^sub>1' where X: "v\<^sub>t\<^sub>1 = Lam\<^sub>s x t e\<^sub>t\<^sub>1' \<and> e\<^sub>d\<^sub>1' = unname' [x] e\<^sub>t\<^sub>1'"
    by (cases v\<^sub>t\<^sub>1) (simp_all add: unname_def)
  from bev\<^sub>d_app E obtain v\<^sub>t\<^sub>2 where V2: "e\<^sub>t\<^sub>2 \<Down>\<^sub>s v\<^sub>t\<^sub>2 \<and> v\<^sub>d\<^sub>2 = unname v\<^sub>t\<^sub>2" by fastforce
  from bev\<^sub>d_app E have "free_vars\<^sub>s e\<^sub>t\<^sub>1 = {}" by simp
  with V1 X have "free_vars\<^sub>s (Lam\<^sub>s x t e\<^sub>t\<^sub>1') = {}" by (metis free_vars_eval)
  hence Y: "free_vars\<^sub>s e\<^sub>t\<^sub>1' \<subseteq> {x}" by simp
  from bev\<^sub>d_app E have "free_vars\<^sub>s e\<^sub>t\<^sub>2 = {}" by simp
  with V2 have Z: "free_vars\<^sub>s v\<^sub>t\<^sub>2 = {}" by auto
  with Y have "free_vars\<^sub>s (subst\<^sub>s x v\<^sub>t\<^sub>2 e\<^sub>t\<^sub>1') = {}" by (metis free_vars_subst subset_empty)
  with bev\<^sub>d_app X V2 Y Z have "\<exists>v\<^sub>t. subst\<^sub>s x v\<^sub>t\<^sub>2 e\<^sub>t\<^sub>1' \<Down>\<^sub>s v\<^sub>t \<and> v\<^sub>d = unname v\<^sub>t" 
    by (simp add: unname_def)
  then obtain v\<^sub>t where "subst\<^sub>s x v\<^sub>t\<^sub>2 e\<^sub>t\<^sub>1' \<Down>\<^sub>s v\<^sub>t \<and> v\<^sub>d = unname v\<^sub>t" by fastforce
  with V1 X V2 have "App\<^sub>s e\<^sub>t\<^sub>1 e\<^sub>t\<^sub>2 \<Down>\<^sub>s v\<^sub>t \<and> v\<^sub>d = unname v\<^sub>t" by fastforce
  with E show ?case by fastforce
qed

text \<open>Now, finally, we can go back and finish the progress theorems for our typed and source 
languages. This is the only time we will need to backfill like this; subsequent stages will prove 
all their relevant metatheoretic properties at once.\<close>

theorem progress\<^sub>t [simp]: "Map.empty \<turnstile>\<^sub>t e\<^sub>t : t \<Longrightarrow> \<exists>v\<^sub>t. e\<^sub>t \<Down>\<^sub>s v\<^sub>t"
proof -
  assume X: "Map.empty \<turnstile>\<^sub>t e\<^sub>t : t"
  hence "[] \<turnstile>\<^sub>d unname e\<^sub>t : t" by simp
  then obtain v\<^sub>d where "value\<^sub>d v\<^sub>d \<and> unname e\<^sub>t \<Down>\<^sub>d v\<^sub>d" by fastforce
  with X obtain v\<^sub>t where "e\<^sub>t \<Down>\<^sub>s v\<^sub>t \<and> v\<^sub>d = unname v\<^sub>t" by fastforce
  thus ?thesis by fastforce
qed

theorem progress\<^sub>s [simp]: "\<exists>e\<^sub>t t. erase e\<^sub>t = e\<^sub>s \<and> Map.empty \<turnstile>\<^sub>t e\<^sub>t : t \<Longrightarrow> \<exists>v\<^sub>s. e\<^sub>s \<Down>\<^sub>s v\<^sub>s"
proof -
  assume "\<exists>e\<^sub>t t. erase e\<^sub>t = e\<^sub>s \<and> Map.empty \<turnstile>\<^sub>t e\<^sub>t : t"
  then obtain e\<^sub>t t where E: "erase e\<^sub>t = e\<^sub>s \<and> Map.empty \<turnstile>\<^sub>t e\<^sub>t : t" by blast
  then obtain v\<^sub>t where "e\<^sub>t \<Down>\<^sub>s v\<^sub>t" by fastforce
  with E have "e\<^sub>s \<Down>\<^sub>s erase v\<^sub>t" by auto
  thus ?thesis by fastforce
qed

end