theory TypedLanguage
  imports Type "../01Source/SourceLanguage"
begin

subsection \<open>Typed Language\<close>

text \<open>Our typed language is almost identical to the untyped source, except there is now a 
type-annotation on every lambda-abstraction. This small change, of course, produces a great 
difference in properties, and will take quite a lot of work to establish in the typechecking pass.\<close>

text \<open>We begin with our typing relation. Thanks to the tags on binders (the only difficult part of 
typing the lambda-calculus), we can straightforwardly check that a term has a given type. In fact, 
we would even write it as an Isabelle function; however, since type-reconstruction is performed 
separately and only once, and the typing judgement is only ever used to prove facts with, we go 
with the simpler inductive relation form.\<close>

inductive typing\<^sub>t :: "(var \<rightharpoonup> ty) \<Rightarrow> ty expr\<^sub>s \<Rightarrow> ty \<Rightarrow> bool" (infix "\<turnstile>\<^sub>t _ :" 50) where
  tc\<^sub>t_var [simp]: "\<Gamma> x = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t Var\<^sub>s x : t"
| tc\<^sub>t_const [simp]: "\<Gamma> \<turnstile>\<^sub>t Const\<^sub>s n : Num"
| tc\<^sub>t_lam [simp]: "\<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>t e : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t Lam\<^sub>s x t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2"
| tc\<^sub>t_app [simp]: "\<Gamma> \<turnstile>\<^sub>t e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t e\<^sub>2 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t App\<^sub>s e\<^sub>1 e\<^sub>2 : t\<^sub>2"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>t Var\<^sub>s x : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>t Const\<^sub>s n : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>t Lam\<^sub>s x t' e : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>t App\<^sub>s e\<^sub>1 e\<^sub>2 : t"

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
  by (induction \<Gamma> e t rule: typing\<^sub>t.induct) (simp_all add: fun_upd_twist)

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
qed fastforce+

theorem preservation\<^sub>t: "e \<Down> v \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>t v : t"
  by (induction e v arbitrary: t rule: eval\<^sub>s.induct) fastforce+

end