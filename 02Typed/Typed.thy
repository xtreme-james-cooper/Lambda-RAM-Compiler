theory Typed
  imports Type "../00Utils/Utils"
begin

datatype texpr = 
  TVar var
  | TConst nat
  | TLam var ty texpr
  | TApp texpr texpr

primrec all_varst :: "texpr \<Rightarrow> var set" where
  "all_varst (TVar x) = {x}"
| "all_varst (TConst k) = {}"
| "all_varst (TLam x t e) = insert x (all_varst e)"
| "all_varst (TApp e\<^sub>1 e\<^sub>2) = all_varst e\<^sub>1 \<union> all_varst e\<^sub>2"

primrec free_varst :: "texpr \<Rightarrow> var set" where
  "free_varst (TVar x) = {x}"
| "free_varst (TConst k) = {}"
| "free_varst (TLam x t e) = free_varst e - {x}"
| "free_varst (TApp e\<^sub>1 e\<^sub>2) = free_varst e\<^sub>1 \<union> free_varst e\<^sub>2"

primrec tvarst :: "texpr \<Rightarrow> var set" where
  "tvarst (TVar x) = {}"
| "tvarst (TConst k) = {}"
| "tvarst (TLam x t e) = tvars t \<union> tvarst e"
| "tvarst (TApp e\<^sub>1 e\<^sub>2) = tvarst e\<^sub>1 \<union> tvarst e\<^sub>2"

inductive typecheckn :: "(var \<rightharpoonup> ty) \<Rightarrow> texpr \<Rightarrow> ty \<Rightarrow> bool" (infix "\<turnstile>\<^sub>n _ :" 50) where
  tcn_var [simp]: "\<Gamma> x = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n TVar x : t"
| tcn_const [simp]: "\<Gamma> \<turnstile>\<^sub>n TConst k : Num"
| tcn_lam [simp]: "\<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n TLam x t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2"
| tcn_app [simp]: "\<Gamma> \<turnstile>\<^sub>n e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e\<^sub>2 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n TApp e\<^sub>1 e\<^sub>2 : t\<^sub>2"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n TVar x : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n TConst k : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n TLam x t' e : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n TApp e\<^sub>1 e\<^sub>2 : t"

primrec valt :: "texpr \<Rightarrow> bool" where
  "valt (TVar x) = False"
| "valt (TConst k) = True" 
| "valt (TLam x t e) = True" 
| "valt (TApp e\<^sub>1 e\<^sub>2) = False" 

primrec subst_vart :: "var \<Rightarrow> var \<Rightarrow> texpr \<Rightarrow> texpr" where
  "subst_vart x x' (TVar y) = TVar (if x = y then x' else y)"
| "subst_vart x x' (TConst k) = TConst k"
| "subst_vart x x' (TLam y t e) = TLam y t (if x = y then e else subst_vart x x' e)"
| "subst_vart x x' (TApp e\<^sub>1 e\<^sub>2) = TApp (subst_vart x x' e\<^sub>1) (subst_vart x x' e\<^sub>2)"

lemma [simp]: "size (subst_vart x x' e) = size e"
  by (induction e) simp_all

fun substt :: "var \<Rightarrow> texpr \<Rightarrow> texpr \<Rightarrow> texpr" where
  "substt x e' (TVar y) = (if x = y then e' else TVar y)"
| "substt x e' (TConst k) = TConst k"
| "substt x e' (TLam y t e) = (
    let z = fresh (all_varst e' \<union> all_varst e \<union> {x, y})
    in TLam z t (substt x e' (subst_vart y z e)))"
| "substt x e' (TApp e\<^sub>1 e\<^sub>2) = TApp (substt x e' e\<^sub>1) (substt x e' e\<^sub>2)"

inductive evalt :: "texpr \<Rightarrow> texpr \<Rightarrow> bool" (infix "\<Down>\<^sub>t" 50) where
  evt_const [simp]: "TConst k \<Down>\<^sub>t TConst k"
| evt_lam [simp]: "TLam x t e \<Down>\<^sub>t TLam x t e"
| evt_app [simp]: "e\<^sub>1 \<Down>\<^sub>t TLam x t e\<^sub>1' \<Longrightarrow> e\<^sub>2 \<Down>\<^sub>t v\<^sub>2 \<Longrightarrow> substt x v\<^sub>2 e\<^sub>1' \<Down>\<^sub>t v \<Longrightarrow> TApp e\<^sub>1 e\<^sub>2 \<Down>\<^sub>t v"

lemma [simp]: "finite (all_varst e)"
  by (induction e) simp_all

lemma [simp]: "free_varst e \<subseteq> insert x xs \<Longrightarrow> free_varst (subst_vart x x' e) \<subseteq> insert x' xs"
proof (induction e arbitrary: xs)
  case (TLam y t e)
  hence "free_varst e \<subseteq> insert x (insert y xs)" by auto
  with TLam have "free_varst (subst_vart x x' e) \<subseteq> insert x' (insert y xs)" by simp
  with TLam show ?case by auto
qed auto

lemma free_vars_substt [simp]: "free_varst e \<subseteq> insert x xs \<Longrightarrow> free_varst e' \<subseteq> xs \<Longrightarrow> 
  free_varst (substt x e' e) \<subseteq> xs"
proof (induction x e' e arbitrary: xs rule: substt.induct)
  case (3 x e' y t e)
  let ?z = "fresh (all_varst e' \<union> all_varst e \<union> {x, y})"
  from 3 have "free_varst e \<subseteq> insert y (insert x xs)" by auto
  hence "free_varst (subst_vart y ?z e) \<subseteq> insert ?z (insert x xs)" by simp
  hence "free_varst (subst_vart y ?z e) \<subseteq> insert x (insert ?z xs)" by auto
  with 3 show ?case by (auto simp add: Let_def)
qed auto

lemma free_vars_evalt [simp]: "e \<Down>\<^sub>t v \<Longrightarrow> free_varst e = {} \<Longrightarrow> free_varst v = {}"
proof (induction e v rule: evalt.induct)
  case (evt_app e\<^sub>1 x t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  hence "free_varst e\<^sub>1' \<subseteq> insert x {} \<and> free_varst v\<^sub>2 \<subseteq> {}" by simp
  hence "free_varst (substt x v\<^sub>2 e\<^sub>1') \<subseteq> {}" by (metis free_vars_substt)
  with evt_app show ?case by simp
qed simp_all

lemma free_vars_subs [simp]: "\<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> free_varst e \<subseteq> dom \<Gamma>" 
  by (induction \<Gamma> e t rule: typecheckn.induct) auto

lemma [simp]: "Map.empty \<turnstile>\<^sub>n e : t \<Longrightarrow> free_varst e = {}"
  using free_vars_subs by fastforce

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> v \<notin> \<Union> (tvars ` ran \<Gamma>) \<Longrightarrow> v \<notin> tvarst e \<Longrightarrow> v \<notin> tvars t"
proof (induction \<Gamma> e t rule: typecheckn.induct)
  case (tcn_lam \<Gamma> x t\<^sub>1 e t\<^sub>2)
  hence "v \<notin> \<Union> (tvars ` ran (\<Gamma>(x \<mapsto> t\<^sub>1)))" by (auto simp add: ran_def)
  with tcn_lam show ?case by fastforce
qed (auto simp add: ran_def)

lemma tcn_tvars [simp]: "\<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> tvars t \<subseteq> tvarst e \<union> \<Union> (tvars ` ran \<Gamma>)"
proof (induction \<Gamma> e t rule: typecheckn.induct)
  case (tcn_lam \<Gamma> x t\<^sub>1 e t\<^sub>2)
  moreover have "\<Union> (tvars ` ran (\<Gamma>(x \<mapsto> t\<^sub>1))) \<subseteq> tvars t\<^sub>1 \<union> \<Union> (tvars ` ran \<Gamma>)" 
    by (auto simp add: ran_def)
  ultimately show ?case by (auto simp add: ran_def)
qed (auto simp add: ran_def)

lemma canonical_basen [dest]: "\<Gamma> \<turnstile>\<^sub>n e : Num \<Longrightarrow> valt e \<Longrightarrow> \<exists>k. e = TConst k"
  by (induction \<Gamma> e Num rule: typecheckn.induct) simp_all

lemma canonical_arrown [dest]: "\<Gamma> \<turnstile>\<^sub>n e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> valt e \<Longrightarrow> 
    \<exists>x e'. e = TLam x t\<^sub>1 e' \<and> \<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e' : t\<^sub>2"
  by (induction \<Gamma> e "Arrow t\<^sub>1 t\<^sub>2" rule: typecheckn.induct) simp_all

(* Progress not directly provable here, due to lack of proof of termination.
   We prove it in 02Debruijn/NameRemoval *)

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> x \<notin> all_varst e \<Longrightarrow> \<Gamma>(x \<mapsto> t') \<turnstile>\<^sub>n e : t"
  by (induction \<Gamma> e t rule: typecheckn.induct) (simp_all add: fun_upd_twist)

lemma [simp]: "\<Gamma>(x \<mapsto> t') \<turnstile>\<^sub>n e : t \<Longrightarrow> x' \<notin> all_varst e \<Longrightarrow> \<Gamma>(x' \<mapsto> t') \<turnstile>\<^sub>n subst_vart x x' e : t"
proof (induction "\<Gamma>(x \<mapsto> t')" e t arbitrary: \<Gamma> rule: typecheckn.induct)
  case (tcn_lam y t\<^sub>1 e t\<^sub>2)
  thus ?case
  proof (cases "x = y")
    case False
    moreover with tcn_lam have "\<Gamma>(y \<mapsto> t\<^sub>1, x' \<mapsto> t') \<turnstile>\<^sub>n subst_vart x x' e : t\<^sub>2" 
      by (simp add: fun_upd_twist)
    moreover from tcn_lam have "x' \<noteq> y" by simp
    ultimately show ?thesis by (simp add: fun_upd_twist)
  qed (simp_all add: fun_upd_twist)
qed fastforce+

lemma [simp]: "\<Gamma>(x \<mapsto> t') \<turnstile>\<^sub>n e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e' : t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n substt x e' e : t"
proof (induction x e' e arbitrary: \<Gamma> t rule: substt.induct)
  case (3 x e' y t\<^sub>1 e)
  then obtain t\<^sub>2 where T: "t = Arrow t\<^sub>1 t\<^sub>2 \<and> \<Gamma>(x \<mapsto> t', y \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e : t\<^sub>2" by blast
  let ?z = "fresh (all_varst e' \<union> all_varst e \<union> {x, y})"
  have "finite (all_varst e' \<union> all_varst e \<union> {x, y})" by simp
  hence Z: "?z \<notin> all_varst e' \<union> all_varst e \<union> {x, y}" by (metis fresh_is_fresh)
  with T have "\<Gamma>(x \<mapsto> t', ?z \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n subst_vart y ?z e : t\<^sub>2" by simp
  with Z have X: "\<Gamma>(?z \<mapsto> t\<^sub>1, x \<mapsto> t') \<turnstile>\<^sub>n subst_vart y ?z e : t\<^sub>2" by (simp add: fun_upd_twist)
  from 3 Z have "\<Gamma>(?z \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e' : t'" by simp
  with 3 X have "\<Gamma>(?z \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n substt x e' (subst_vart y ?z e) : t\<^sub>2" by fastforce
  with T show ?case by (simp add: Let_def)
qed fastforce+

theorem preservationn: "e \<Down>\<^sub>t v \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n v : t"
  by (induction e v arbitrary: t rule: evalt.induct) fastforce+

lemma [simp]: "e \<Down>\<^sub>t v \<Longrightarrow> valt v"
  by (induction e v rule: evalt.induct) simp_all

lemma val_no_evaln: "e \<Down>\<^sub>t v \<Longrightarrow> valt e \<Longrightarrow> v = e"
  by (induction e v rule: evalt.induct) simp_all

theorem determinismn: "e \<Down>\<^sub>t v \<Longrightarrow> e \<Down>\<^sub>t v' \<Longrightarrow> v = v'"
proof (induction e v arbitrary: v' rule: evalt.induct)
  case (evt_const k)
  thus ?case by (induction "TConst k" v' rule: evalt.induct) simp_all
next
  case (evt_lam x t e)
  thus ?case by (induction "TLam x t e" v' rule: evalt.induct) simp_all
next
  case (evt_app e\<^sub>1 x t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  from evt_app(7, 1, 2, 3, 4, 5, 6) show ?case 
    by (induction "TApp e\<^sub>1 e\<^sub>2" v' rule: evalt.induct) blast+
qed

end