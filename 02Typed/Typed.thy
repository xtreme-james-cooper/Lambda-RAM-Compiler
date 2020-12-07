theory Typed
  imports Type "../01Source/Variable" "../00Utils/Utils"
begin

datatype texpr = 
  TVar var
  | TConst nat
  | TLam var ty texpr
  | TApp texpr texpr

primrec all_vars :: "texpr \<Rightarrow> var set" where
  "all_vars (TVar x) = {x}"
| "all_vars (TConst k) = {}"
| "all_vars (TLam x t e) = insert x (all_vars e)"
| "all_vars (TApp e\<^sub>1 e\<^sub>2) = all_vars e\<^sub>1 \<union> all_vars e\<^sub>2"

primrec binders :: "texpr \<Rightarrow> var set" where
  "binders (TVar x) = {}"
| "binders (TConst k) = {}"
| "binders (TLam x t e) = insert x (binders e)"
| "binders (TApp e\<^sub>1 e\<^sub>2) = binders e\<^sub>1 \<union> binders e\<^sub>2"

primrec free_vars :: "texpr \<Rightarrow> var set" where
  "free_vars (TVar x) = {x}"
| "free_vars (TConst k) = {}"
| "free_vars (TLam x t e) = free_vars e - {x}"
| "free_vars (TApp e\<^sub>1 e\<^sub>2) = free_vars e\<^sub>1 \<union> free_vars e\<^sub>2"

inductive typecheckn :: "(var \<rightharpoonup> ty) \<Rightarrow> texpr \<Rightarrow> ty \<Rightarrow> bool" (infix "\<turnstile>\<^sub>n _ :" 50) where
  tcn_var [simp]: "\<Gamma> x = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n TVar x : t"
| tcn_const [simp]: "\<Gamma> \<turnstile>\<^sub>n TConst k : Base"
| tcn_lam [simp]: "\<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n TLam x t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2"
| tcn_app [simp]: "\<Gamma> \<turnstile>\<^sub>n e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e\<^sub>2 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n TApp e\<^sub>1 e\<^sub>2 : t\<^sub>2"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n TVar x : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n TConst k : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n TLam x t' e : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n TApp e\<^sub>1 e\<^sub>2 : t"

primrec valn :: "texpr \<Rightarrow> bool" where
  "valn (TVar x) = False"
| "valn (TConst k) = True" 
| "valn (TLam x t e) = True" 
| "valn (TApp e\<^sub>1 e\<^sub>2) = False" 

primrec subst_var :: "var \<Rightarrow> var \<Rightarrow> texpr \<Rightarrow> texpr" where
  "subst_var x x' (TVar y) = TVar (if x = y then x' else y)"
| "subst_var x x' (TConst k) = TConst k"
| "subst_var x x' (TLam y t e) = TLam y t (if x = y then e else subst_var x x' e)"
| "subst_var x x' (TApp e\<^sub>1 e\<^sub>2) = TApp (subst_var x x' e\<^sub>1) (subst_var x x' e\<^sub>2)"

lemma [simp]: "size (subst_var x x' e) = size e"
  by (induction e) simp_all

fun substn :: "var \<Rightarrow> texpr \<Rightarrow> texpr \<Rightarrow> texpr" where
  "substn x e' (TVar y) = (if x = y then e' else TVar y)"
| "substn x e' (TConst k) = TConst k"
| "substn x e' (TLam y t e) = (
    let z = fresh (all_vars e' \<union> all_vars e \<union> {x, y})
    in TLam z t (substn x e' (subst_var y z e)))"
| "substn x e' (TApp e\<^sub>1 e\<^sub>2) = TApp (substn x e' e\<^sub>1) (substn x e' e\<^sub>2)"

inductive evaln :: "texpr \<Rightarrow> texpr \<Rightarrow> bool" (infix "\<Down>" 50) where
  evn_const [simp]: "TConst k \<Down> TConst k"
| evn_lam [simp]: "TLam x t e \<Down> TLam x t e"
| evn_app [simp]: "e\<^sub>1 \<Down> TLam x t e\<^sub>1' \<Longrightarrow> e\<^sub>2 \<Down> v\<^sub>2 \<Longrightarrow> substn x v\<^sub>2 e\<^sub>1' \<Down> v \<Longrightarrow> TApp e\<^sub>1 e\<^sub>2 \<Down> v"

lemma [simp]: "finite (all_vars e)"
  by (induction e) simp_all

lemma [simp]: "free_vars e \<subseteq> insert x xs \<Longrightarrow> free_vars (subst_var x x' e) \<subseteq> insert x' xs"
proof (induction e arbitrary: xs)
  case (TLam y t e)
  hence "free_vars e \<subseteq> insert x (insert y xs)" by auto
  with TLam have "free_vars (subst_var x x' e) \<subseteq> insert x' (insert y xs)" by simp
  with TLam show ?case by auto
qed auto

lemma free_vars_subst [simp]: "free_vars e \<subseteq> insert x xs \<Longrightarrow> free_vars e' \<subseteq> xs \<Longrightarrow> 
  free_vars (substn x e' e) \<subseteq> xs"
proof (induction x e' e arbitrary: xs rule: substn.induct)
  case (3 x e' y t e)
  let ?z = "fresh (all_vars e' \<union> all_vars e \<union> {x, y})"
  from 3 have "free_vars e \<subseteq> insert y (insert x xs)" by auto
  hence "free_vars (subst_var y ?z e) \<subseteq> insert ?z (insert x xs)" by simp
  hence "free_vars (subst_var y ?z e) \<subseteq> insert x (insert ?z xs)" by auto
  with 3 show ?case by (auto simp add: Let_def)
qed auto

lemma free_vars_eval [simp]: "e \<Down> v \<Longrightarrow> free_vars e = {} \<Longrightarrow> free_vars v = {}"
proof (induction e v rule: evaln.induct)
  case (evn_app e\<^sub>1 x t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  hence "free_vars e\<^sub>1' \<subseteq> insert x {} \<and> free_vars v\<^sub>2 \<subseteq> {}" by simp
  hence "free_vars (substn x v\<^sub>2 e\<^sub>1') \<subseteq> {}" by (metis free_vars_subst)
  with evn_app show ?case by simp
qed simp_all

lemma free_vars_subs [simp]: "\<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> free_vars e \<subseteq> dom \<Gamma>" 
  by (induction \<Gamma> e t rule: typecheckn.induct) auto

lemma [simp]: "Map.empty \<turnstile>\<^sub>n e : t \<Longrightarrow> free_vars e = {}"
  using free_vars_subs by fastforce

lemma canonical_basen [dest]: "\<Gamma> \<turnstile>\<^sub>n e : Base \<Longrightarrow> valn e \<Longrightarrow> \<exists>k. e = TConst k"
  by (induction \<Gamma> e Base rule: typecheckn.induct) simp_all

lemma canonical_arrown [dest]: "\<Gamma> \<turnstile>\<^sub>n e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> valn e \<Longrightarrow> 
    \<exists>x e'. e = TLam x t\<^sub>1 e' \<and> \<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e' : t\<^sub>2"
  by (induction \<Gamma> e "Arrow t\<^sub>1 t\<^sub>2" rule: typecheckn.induct) simp_all

(* Progress not directly provable here, due to lack of proof of termination.
   We prove it in 02Debruijn/NameRemoval *)

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> x \<notin> all_vars e \<Longrightarrow> \<Gamma>(x \<mapsto> t') \<turnstile>\<^sub>n e : t"
  by (induction \<Gamma> e t rule: typecheckn.induct) (simp_all add: fun_upd_twist)

lemma [simp]: "\<Gamma>(x \<mapsto> t') \<turnstile>\<^sub>n e : t \<Longrightarrow> x' \<notin> all_vars e \<Longrightarrow> \<Gamma>(x' \<mapsto> t') \<turnstile>\<^sub>n subst_var x x' e : t"
proof (induction "\<Gamma>(x \<mapsto> t')" e t arbitrary: \<Gamma> rule: typecheckn.induct)
  case (tcn_lam y t\<^sub>1 e t\<^sub>2)
  thus ?case
  proof (cases "x = y")
    case False
    moreover with tcn_lam have "\<Gamma>(y \<mapsto> t\<^sub>1, x' \<mapsto> t') \<turnstile>\<^sub>n subst_var x x' e : t\<^sub>2" 
      by (simp add: fun_upd_twist)
    moreover from tcn_lam have "x' \<noteq> y" by simp
    ultimately show ?thesis by (simp add: fun_upd_twist)
  qed (simp_all add: fun_upd_twist)
qed fastforce+

lemma [simp]: "\<Gamma>(x \<mapsto> t') \<turnstile>\<^sub>n e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e' : t' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n substn x e' e : t"
proof (induction x e' e arbitrary: \<Gamma> t rule: substn.induct)
  case (3 x e' y t\<^sub>1 e)
  then obtain t\<^sub>2 where T: "t = Arrow t\<^sub>1 t\<^sub>2 \<and> \<Gamma>(x \<mapsto> t', y \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e : t\<^sub>2" by blast
  let ?z = "fresh (all_vars e' \<union> all_vars e \<union> {x, y})"
  have "finite (all_vars e' \<union> all_vars e \<union> {x, y})" by simp
  hence Z: "?z \<notin> all_vars e' \<union> all_vars e \<union> {x, y}" by (metis fresh_is_fresh)
  with T have "\<Gamma>(x \<mapsto> t', ?z \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n subst_var y ?z e : t\<^sub>2" by simp
  with Z have X: "\<Gamma>(?z \<mapsto> t\<^sub>1, x \<mapsto> t') \<turnstile>\<^sub>n subst_var y ?z e : t\<^sub>2" by (simp add: fun_upd_twist)
  from 3 Z have "\<Gamma>(?z \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e' : t'" by simp
  with 3 X have "\<Gamma>(?z \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n substn x e' (subst_var y ?z e) : t\<^sub>2" by fastforce
  with T show ?case by (simp add: Let_def)
qed fastforce+

theorem preservationn: "e \<Down> v \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n v : t"
  by (induction e v arbitrary: t rule: evaln.induct) fastforce+

lemma [simp]: "e \<Down> v \<Longrightarrow> valn v"
  by (induction e v rule: evaln.induct) simp_all

lemma val_no_evaln: "e \<Down> v \<Longrightarrow> valn e \<Longrightarrow> v = e"
  by (induction e v rule: evaln.induct) simp_all

theorem determinismn: "e \<Down> v \<Longrightarrow> e \<Down> v' \<Longrightarrow> v = v'"
proof (induction e v arbitrary: v' rule: evaln.induct)
  case (evn_const k)
  thus ?case by (induction "TConst k" v' rule: evaln.induct) simp_all
next
  case (evn_lam x t e)
  thus ?case by (induction "TLam x t e" v' rule: evaln.induct) simp_all
next
  case (evn_app e\<^sub>1 x t e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  from evn_app(7, 1, 2, 3, 4, 5, 6) show ?case 
    by (induction "TApp e\<^sub>1 e\<^sub>2" v' rule: evaln.induct) blast+
qed

end