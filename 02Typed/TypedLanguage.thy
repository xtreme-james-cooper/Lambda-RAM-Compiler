theory TypedLanguage
  imports Type "../01Source/SourceLanguage"
begin

subsection \<open>Typed Language\<close>

text \<open>Our typed language is almost identical to the untyped source, except there is now a 
type-annotation on every lambda-abstraction. This small change, of course, produces a great 
difference in properties, and will take quite a lot of work to establish in the typechecking pass.\<close>

inductive typecheckn :: "(var \<rightharpoonup> ty) \<Rightarrow> ty expr\<^sub>s \<Rightarrow> ty \<Rightarrow> bool" (infix "\<turnstile>\<^sub>n _ :" 50) where
  tcn_var [simp]: "\<Gamma> x = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n Var\<^sub>s x : t"
| tcn_const [simp]: "\<Gamma> \<turnstile>\<^sub>n Const\<^sub>s k : Num"
| tcn_lam [simp]: "\<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n Lam\<^sub>s x t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2"
| tcn_app [simp]: "\<Gamma> \<turnstile>\<^sub>n e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e\<^sub>2 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n App\<^sub>s e\<^sub>1 e\<^sub>2 : t\<^sub>2"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n Var\<^sub>s x : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n Const\<^sub>s k : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n Lam\<^sub>s x t' e : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n App\<^sub>s e\<^sub>1 e\<^sub>2 : t"

lemma free_vars_tc [simp]: "\<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> free_vars\<^sub>s e \<subseteq> dom \<Gamma>" 
  by (induction \<Gamma> e t rule: typecheckn.induct) auto

lemma [simp]: "Map.empty \<turnstile>\<^sub>n e : t \<Longrightarrow> free_vars\<^sub>s e = {}"
  using free_vars_tc by fastforce

lemma canonical_base\<^sub>s [dest]: "\<Gamma> \<turnstile>\<^sub>n e : Num \<Longrightarrow> value\<^sub>s e \<Longrightarrow> \<exists>k. e = Const\<^sub>s k"
  by (induction \<Gamma> e Num rule: typecheckn.induct) simp_all

lemma canonical_arrow\<^sub>s [dest]: "\<Gamma> \<turnstile>\<^sub>n e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> value\<^sub>s e \<Longrightarrow> 
    \<exists>x e'. e = Lam\<^sub>s x t\<^sub>1 e' \<and> \<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e' : t\<^sub>2"
  by (induction \<Gamma> e "Arrow t\<^sub>1 t\<^sub>2" rule: typecheckn.induct) simp_all

(* Progress not directly provable here, due to lack of proof of termination.
   We prove it in 02Debruijn/NameRemoval *)

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> x \<notin> all_vars\<^sub>s e \<Longrightarrow> \<Gamma>(x \<mapsto> t') \<turnstile>\<^sub>n e : t"
  by (induction \<Gamma> e t rule: typecheckn.induct) (simp_all add: fun_upd_twist)

lemma [simp]: "\<Gamma>(x \<mapsto> t') \<turnstile>\<^sub>n e : t \<Longrightarrow> x' \<notin> all_vars\<^sub>s e \<Longrightarrow> \<Gamma>(x' \<mapsto> t') \<turnstile>\<^sub>n subst_var\<^sub>s x x' e : t"
proof (induction "\<Gamma>(x \<mapsto> t')" e t arbitrary: \<Gamma> rule: typecheckn.induct)
  case (tcn_lam y t\<^sub>1 e t\<^sub>2)
  thus ?case
  proof (cases "x = y")
    case False
    moreover with tcn_lam have "\<Gamma>(y \<mapsto> t\<^sub>1, x' \<mapsto> t') \<turnstile>\<^sub>n subst_var\<^sub>s x x' e : t\<^sub>2" 
      by (simp add: fun_upd_twist)
    moreover from tcn_lam have "x' \<noteq> y" by simp
    ultimately show ?thesis by (simp add: fun_upd_twist)
  qed (simp_all add: fun_upd_twist)
qed fastforce+

lemma [simp]: "\<Gamma>(x \<mapsto> t') \<turnstile>\<^sub>n e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e' : t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n subst\<^sub>s x e' e : t"
proof (induction x e' e arbitrary: \<Gamma> t rule: subst\<^sub>s.induct)
  case (3 x e' y t\<^sub>1 e)
  then obtain t\<^sub>2 where T: "t = Arrow t\<^sub>1 t\<^sub>2 \<and> \<Gamma>(x \<mapsto> t', y \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e : t\<^sub>2" by blast
  let ?z = "fresh (all_vars\<^sub>s e' \<union> all_vars\<^sub>s e \<union> {x, y})"
  have "finite (all_vars\<^sub>s e' \<union> all_vars\<^sub>s e \<union> {x, y})" by simp
  hence Z: "?z \<notin> all_vars\<^sub>s e' \<union> all_vars\<^sub>s e \<union> {x, y}" by (metis fresh_is_fresh)
  with T have "\<Gamma>(x \<mapsto> t', ?z \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n subst_var\<^sub>s y ?z e : t\<^sub>2" by simp
  with Z have X: "\<Gamma>(?z \<mapsto> t\<^sub>1, x \<mapsto> t') \<turnstile>\<^sub>n subst_var\<^sub>s y ?z e : t\<^sub>2" by (simp add: fun_upd_twist)
  from 3 Z have "\<Gamma>(?z \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e' : t'" by simp
  with 3 X have "\<Gamma>(?z \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n subst\<^sub>s x e' (subst_var\<^sub>s y ?z e) : t\<^sub>2" by fastforce
  with T show ?case by (simp add: Let_def)
qed fastforce+

theorem preservationn: "e \<Down> v \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n v : t"
  by (induction e v arbitrary: t rule: eval\<^sub>s.induct) fastforce+

end