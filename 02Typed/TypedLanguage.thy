theory TypedLanguage
  imports Type "../01Source/SourceLanguage"
begin

subsection \<open>Typed Language\<close>

text \<open>Our typed language is almost identical to the untyped source, except there is now a 
type-annotation on every lambda-abstraction. This small change, of course, produces a great 
difference in properties, and will take quite a lot of work to establish in the typechecking pass.\<close>

text \<open>We first define our typing relation. Thanks to the tags on binders (the only difficult part of 
typing the lambda-calculus), we can straightforwardly check that an expression has a given type. In 
fact, we would even write it as an Isabelle function; however, since type-reconstruction is 
performed separately and only once, and the typing judgement is only ever used to prove facts with,
we go with the simpler inductive relation form.\<close>

inductive typing\<^sub>t :: "(var \<rightharpoonup> ty) \<Rightarrow> ty expr\<^sub>s \<Rightarrow> ty \<Rightarrow> bool" (infix "\<turnstile>\<^sub>t _ :" 50) where
  tc\<^sub>t_var [simp]: "\<Gamma> x = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t Var\<^sub>s x : t"
| tc\<^sub>t_const [simp]: "\<Gamma> \<turnstile>\<^sub>t Const\<^sub>s n : Num"
| tc\<^sub>t_lam [simp]: "\<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>t e : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t Lam\<^sub>s x t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2"
| tc\<^sub>t_app [simp]: "\<Gamma> \<turnstile>\<^sub>t e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t e\<^sub>2 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t App\<^sub>s e\<^sub>1 e\<^sub>2 : t\<^sub>2"
| tc\<^sub>t_let [simp]: "\<Gamma> \<turnstile>\<^sub>t e\<^sub>1 : t\<^sub>1 \<Longrightarrow> \<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>t e\<^sub>2 : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t Let\<^sub>s x e\<^sub>1 e\<^sub>2 : t\<^sub>2"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>t Var\<^sub>s x : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>t Const\<^sub>s n : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>t Lam\<^sub>s x t' e : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>t App\<^sub>s e\<^sub>1 e\<^sub>2 : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>t Let\<^sub>s x e\<^sub>1 e\<^sub>2 : t"

lemma free_vars_tc': "\<Gamma> \<turnstile>\<^sub>t e : t \<Longrightarrow> free_vars\<^sub>s e \<subseteq> dom \<Gamma>" 
  by (induction \<Gamma> e t rule: typing\<^sub>t.induct) auto

lemma free_vars_tc [simp]: "Map.empty \<turnstile>\<^sub>t e : t \<Longrightarrow> free_vars\<^sub>s e = {}"
  using free_vars_tc' by fastforce

text \<open>The typing of an expression in a given context is unique:\<close>

theorem uniqueness_of_typing: "\<Gamma> \<turnstile>\<^sub>t e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t e : t' \<Longrightarrow> t = t'"
proof (induction \<Gamma> e t arbitrary: t' rule: typing\<^sub>t.induct)
  case (tc\<^sub>t_var \<Gamma> x t)
  from tc\<^sub>t_var(2, 1) show ?case by (induction rule: typing\<^sub>t.cases) simp_all
next
  case (tc\<^sub>t_const \<Gamma> n)
  thus ?case by (induction rule: typing\<^sub>t.cases) simp_all
next
  case (tc\<^sub>t_lam \<Gamma> x t\<^sub>1 e t\<^sub>2)
  from tc\<^sub>t_lam(3, 1, 2) show ?case by (induction rule: typing\<^sub>t.cases) blast+
next
  case (tc\<^sub>t_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  from tc\<^sub>t_app(5, 1, 2, 3, 4) show ?case by (induction rule: typing\<^sub>t.cases) blast+
next
  case (tc\<^sub>t_let \<Gamma> e\<^sub>1 t\<^sub>1 x e\<^sub>2 t\<^sub>2)
  from tc\<^sub>t_let(5, 1, 2, 3, 4) show ?case by (induction rule: typing\<^sub>t.cases) blast+
qed

text \<open>We can also now prove the canonical-forms lemmas, telling us what shapes a well-typed value
must have.\<close>

lemma canonical_num [dest]: "\<Gamma> \<turnstile>\<^sub>t e : Num \<Longrightarrow> value\<^sub>s e \<Longrightarrow> \<exists>n. e = Const\<^sub>s n"
  by (induction \<Gamma> e Num rule: typing\<^sub>t.induct) simp_all

lemma canonical_arrow\<^sub>t [dest]: "\<Gamma> \<turnstile>\<^sub>t e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> value\<^sub>s e \<Longrightarrow> 
    \<exists>x e'. e = Lam\<^sub>s x t\<^sub>1 e' \<and> \<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>t e' : t\<^sub>2"
  by (induction \<Gamma> e "Arrow t\<^sub>1 t\<^sub>2" rule: typing\<^sub>t.induct) simp_all

text \<open>Finally, we can prove the preservation theorem, one half of the traditional formulation of
language safety. The other half, progress, is true of our language at this point, now that we have 
restricted our sights to the typed subset; but our complex capture-avoiding substitution operation 
would make proving it more painful than necessary. We will return to it once we have moved to a 
Debruijn variable representation.\<close>

lemma tc\<^sub>t_widen_context [simp]: "\<Gamma> \<turnstile>\<^sub>t e : t \<Longrightarrow> x \<notin> all_vars\<^sub>s e \<Longrightarrow> \<Gamma>(x \<mapsto> t') \<turnstile>\<^sub>t e : t"
  by (induction \<Gamma> e t rule: typing\<^sub>t.induct) (auto simp add: fun_upd_twist)

lemma tc\<^sub>t_subst_var [simp]: "\<Gamma>(x \<mapsto> t') \<turnstile>\<^sub>t e : t \<Longrightarrow> x' \<notin> all_vars\<^sub>s e \<Longrightarrow> 
  \<Gamma>(x' \<mapsto> t') \<turnstile>\<^sub>t subst_var\<^sub>s x x' e : t"
proof (induction "\<Gamma>(x \<mapsto> t')" e t arbitrary: \<Gamma> rule: typing\<^sub>t.induct)
  case (tc\<^sub>t_lam y t\<^sub>1 e t\<^sub>2)
  thus ?case
  proof (cases "x = y")
    case False
    moreover with tc\<^sub>t_lam have "\<Gamma>(y \<mapsto> t\<^sub>1, x' \<mapsto> t') \<turnstile>\<^sub>t subst_var\<^sub>s x x' e : t\<^sub>2" 
      by (simp add: fun_upd_twist)
    moreover from tc\<^sub>t_lam have "x' \<noteq> y" by simp
    ultimately show ?thesis by (simp add: fun_upd_twist)
  qed (simp_all add: fun_upd_twist)
next
  case (tc\<^sub>t_let e\<^sub>1 t\<^sub>1 x e\<^sub>2 t\<^sub>2)
  then show ?case by simp
qed fastforce+

lemma tc\<^sub>t_subst [simp]: "\<Gamma>(x \<mapsto> t') \<turnstile>\<^sub>t e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t e' : t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t subst\<^sub>s x e' e : t"
proof (induction x e' e arbitrary: \<Gamma> t rule: subst\<^sub>s.induct)
  case (3 x e' y t\<^sub>1 e)
  then obtain t\<^sub>2 where T: "t = Arrow t\<^sub>1 t\<^sub>2 \<and> \<Gamma>(x \<mapsto> t', y \<mapsto> t\<^sub>1) \<turnstile>\<^sub>t e : t\<^sub>2" by blast
  let ?z = "fresh (all_vars\<^sub>s e' \<union> all_vars\<^sub>s e \<union> {x, y})"
  have "finite (all_vars\<^sub>s e' \<union> all_vars\<^sub>s e \<union> {x, y})" by simp
  hence Z: "?z \<notin> all_vars\<^sub>s e' \<union> all_vars\<^sub>s e \<union> {x, y}" by (metis fresh_is_fresh)
  with T have "\<Gamma>(x \<mapsto> t', ?z \<mapsto> t\<^sub>1) \<turnstile>\<^sub>t subst_var\<^sub>s y ?z e : t\<^sub>2" by simp
  with Z have X: "\<Gamma>(?z \<mapsto> t\<^sub>1, x \<mapsto> t') \<turnstile>\<^sub>t subst_var\<^sub>s y ?z e : t\<^sub>2" by (simp add: fun_upd_twist)
  from 3 Z have "\<Gamma>(?z \<mapsto> t\<^sub>1) \<turnstile>\<^sub>t e' : t'" by simp
  with 3 X have "\<Gamma>(?z \<mapsto> t\<^sub>1) \<turnstile>\<^sub>t subst\<^sub>s x e' (subst_var\<^sub>s y ?z e) : t\<^sub>2" by fastforce
  with T show ?case by (simp add: Let_def)
next
  case (5 x e' y t e\<^sub>1 e\<^sub>2)
  then show ?case by simp
qed fastforce+

theorem preservation\<^sub>t [simp]: "e \<Down>\<^sub>s v \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t v : t"
  by (induction e v arbitrary: t rule: eval\<^sub>s.induct) fastforce+

text \<open>We also prove that the removed-shadow version of an expression typechecks if the original 
did.\<close>

lemma tc_remove_shadows' [simp]: "\<Gamma> \<turnstile>\<^sub>t e : t \<Longrightarrow> finite vs \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t remove_shadows\<^sub>s' vs e : t"
proof (induction \<Gamma> e t arbitrary: vs rule: typing\<^sub>t.induct)
  case (tc\<^sub>t_lam \<Gamma> x t\<^sub>1 e t\<^sub>2)
  let ?e = "remove_shadows\<^sub>s' (insert x vs) e"
  let ?x = "fresh (vs \<union> all_vars\<^sub>s ?e)"
  from tc\<^sub>t_lam have "finite (vs \<union> all_vars\<^sub>s ?e)" by simp
  hence "?x \<notin> vs \<union> all_vars\<^sub>s ?e" by (metis fresh_is_fresh)
  moreover from tc\<^sub>t_lam have "\<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>t ?e : t\<^sub>2" by fastforce
  ultimately show ?case by (simp add: Let_def)
next
  case (tc\<^sub>t_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  hence "\<Gamma> \<turnstile>\<^sub>t remove_shadows\<^sub>s' vs e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2" by simp
  moreover from tc\<^sub>t_app have "\<Gamma> \<turnstile>\<^sub>t remove_shadows\<^sub>s' vs e\<^sub>2 : t\<^sub>1" by simp
  ultimately show ?case by simp
next
  case (tc\<^sub>t_let \<Gamma> e\<^sub>1 t\<^sub>1 x e\<^sub>2 t\<^sub>2)
  then show ?case by simp
qed simp_all

lemma tc_remove_shadows [simp]: "\<Gamma> \<turnstile>\<^sub>t e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t remove_shadows\<^sub>s e : t"
  by (simp add: remove_shadows\<^sub>s_def)

subsection \<open>Type Erasure\<close>

text \<open>We define a type-erasure function to convert back to our untyped language. This will be 
how we show that typechecked expressions have the same shape they started with.\<close>

abbreviation erase :: "'a expr\<^sub>s \<Rightarrow> unit expr\<^sub>s" where
  "erase \<equiv> map_expr\<^sub>s (\<lambda>x. ())"

lemma erase_to_var [dest]: "erase e\<^sub>t = Var\<^sub>s x \<Longrightarrow> e\<^sub>t = Var\<^sub>s x"
  by (induction e\<^sub>t) simp_all

lemma erase_to_const [dest]: "erase e\<^sub>t = Const\<^sub>s n \<Longrightarrow> e\<^sub>t = Const\<^sub>s n"
  by (induction e\<^sub>t) simp_all

lemma erase_to_lam [dest]: "erase e\<^sub>t = Lam\<^sub>s x u e\<^sub>s \<Longrightarrow> \<exists>t e\<^sub>t'. e\<^sub>t = Lam\<^sub>s x t e\<^sub>t' \<and> e\<^sub>s = erase e\<^sub>t'"
  by (induction e\<^sub>t) simp_all

lemma erase_to_app [dest]: "erase e\<^sub>t = App\<^sub>s e\<^sub>s\<^sub>1 e\<^sub>s\<^sub>2 \<Longrightarrow> 
    \<exists>e\<^sub>1' e\<^sub>2'. e\<^sub>t = App\<^sub>s e\<^sub>1' e\<^sub>2' \<and> e\<^sub>s\<^sub>1 = erase e\<^sub>1' \<and> e\<^sub>s\<^sub>2 = erase e\<^sub>2'"
  by (induction e\<^sub>t) simp_all

lemma erase_map [simp]: "erase (map_expr\<^sub>s f e\<^sub>t) = erase e\<^sub>t"
  by (induction e\<^sub>t) simp_all

text \<open>Since evaluation and all its related functions ignore tags, it is no surprise that our first 
completeness theorem is very easy to prove.\<close>

lemma erased_value [simp]: "value\<^sub>s (erase e\<^sub>t) = value\<^sub>s e\<^sub>t"
  by (induction e\<^sub>t) simp_all

lemma erased_vars [simp]: "all_vars\<^sub>s (erase e\<^sub>t) = all_vars\<^sub>s e\<^sub>t"
  by (induction e\<^sub>t) simp_all

lemma erased_subst_var [simp]: "erase (subst_var\<^sub>s x y e\<^sub>t) = subst_var\<^sub>s x y (erase e\<^sub>t)"
  by (induction e\<^sub>t) simp_all

lemma erased_subst [simp]: "erase (subst\<^sub>s x e\<^sub>t' e\<^sub>t) = subst\<^sub>s x (erase e\<^sub>t') (erase e\<^sub>t)"
  by (induction x e\<^sub>t' e\<^sub>t rule: subst\<^sub>s.induct) (simp_all add: Let_def)

theorem completeness [simp]: "e\<^sub>t \<Down>\<^sub>s v\<^sub>t \<Longrightarrow> erase e\<^sub>t \<Down>\<^sub>s erase v\<^sub>t"
  by (induction e\<^sub>t v\<^sub>t rule: eval\<^sub>s.induct) simp_all

end