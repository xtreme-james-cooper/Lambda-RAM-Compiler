theory Named
  imports Variable "../00Utils/Utils"
begin

datatype nexpr = 
  NVar var
  | NConst nat
  | NLam var nexpr
  | NApp nexpr nexpr

primrec all_vars :: "nexpr \<Rightarrow> var set" where
  "all_vars (NVar x) = {x}"
| "all_vars (NConst k) = {}"
| "all_vars (NLam x e) = insert x (all_vars e)"
| "all_vars (NApp e\<^sub>1 e\<^sub>2) = all_vars e\<^sub>1 \<union> all_vars e\<^sub>2"

primrec binders :: "nexpr \<Rightarrow> var set" where
  "binders (NVar x) = {}"
| "binders (NConst k) = {}"
| "binders (NLam x e) = insert x (binders e)"
| "binders (NApp e\<^sub>1 e\<^sub>2) = binders e\<^sub>1 \<union> binders e\<^sub>2"

primrec free_vars :: "nexpr \<Rightarrow> var set" where
  "free_vars (NVar x) = {x}"
| "free_vars (NConst k) = {}"
| "free_vars (NLam x e) = free_vars e - {x}"
| "free_vars (NApp e\<^sub>1 e\<^sub>2) = free_vars e\<^sub>1 \<union> free_vars e\<^sub>2"

primrec valn :: "nexpr \<Rightarrow> bool" where
  "valn (NVar x) = False"
| "valn (NConst k) = True" 
| "valn (NLam x e) = True" 
| "valn (NApp e\<^sub>1 e\<^sub>2) = False" 

primrec subst_var :: "var \<Rightarrow> var \<Rightarrow> nexpr \<Rightarrow> nexpr" where
  "subst_var x x' (NVar y) = NVar (if x = y then x' else y)"
| "subst_var x x' (NConst k) = NConst k"
| "subst_var x x' (NLam y e) = NLam y (if x = y then e else subst_var x x' e)"
| "subst_var x x' (NApp e\<^sub>1 e\<^sub>2) = NApp (subst_var x x' e\<^sub>1) (subst_var x x' e\<^sub>2)"

lemma [simp]: "size (subst_var x x' e) = size e"
  by (induction e) simp_all

fun substn :: "var \<Rightarrow> nexpr \<Rightarrow> nexpr \<Rightarrow> nexpr" where
  "substn x e' (NVar y) = (if x = y then e' else NVar y)"
| "substn x e' (NConst k) = NConst k"
| "substn x e' (NLam y e) = (
    let z = fresh (all_vars e' \<union> all_vars e \<union> {x, y})
    in NLam z (substn x e' (subst_var y z e)))"
| "substn x e' (NApp e\<^sub>1 e\<^sub>2) = NApp (substn x e' e\<^sub>1) (substn x e' e\<^sub>2)"

inductive evaln :: "nexpr \<Rightarrow> nexpr \<Rightarrow> bool" (infix "\<Down>" 50) where
  evn_const [simp]: "NConst k \<Down> NConst k"
| evn_lam [simp]: "NLam x e \<Down> NLam x e"
| evn_app [simp]: "e\<^sub>1 \<Down> NLam x e\<^sub>1' \<Longrightarrow> e\<^sub>2 \<Down> v\<^sub>2 \<Longrightarrow> substn x v\<^sub>2 e\<^sub>1' \<Down> v \<Longrightarrow> NApp e\<^sub>1 e\<^sub>2 \<Down> v"

lemma [simp]: "finite (all_vars e)"
  by (induction e) simp_all

lemma [simp]: "free_vars e \<subseteq> insert x xs \<Longrightarrow> free_vars (subst_var x x' e) \<subseteq> insert x' xs"
proof (induction e arbitrary: xs)
  case (NLam y e)
  hence "free_vars e \<subseteq> insert x (insert y xs)" by auto
  with NLam have "free_vars (subst_var x x' e) \<subseteq> insert x' (insert y xs)" by simp
  with NLam show ?case by auto
qed auto

lemma free_vars_subst [simp]: "free_vars e \<subseteq> insert x xs \<Longrightarrow> free_vars e' \<subseteq> xs \<Longrightarrow> 
  free_vars (substn x e' e) \<subseteq> xs"
proof (induction x e' e arbitrary: xs rule: substn.induct)
  case (3 x e' y e)
  let ?z = "fresh (all_vars e' \<union> all_vars e \<union> {x, y})"
  from 3 have "free_vars e \<subseteq> insert y (insert x xs)" by auto
  hence "free_vars (subst_var y ?z e) \<subseteq> insert ?z (insert x xs)" by simp
  hence "free_vars (subst_var y ?z e) \<subseteq> insert x (insert ?z xs)" by auto
  with 3 show ?case by (auto simp add: Let_def)
qed auto

lemma free_vars_eval [simp]: "e \<Down> v \<Longrightarrow> free_vars e = {} \<Longrightarrow> free_vars v = {}"
proof (induction e v rule: evaln.induct)
  case (evn_app e\<^sub>1 x e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  hence "free_vars e\<^sub>1' \<subseteq> insert x {} \<and> free_vars v\<^sub>2 \<subseteq> {}" by simp
  hence "free_vars (substn x v\<^sub>2 e\<^sub>1') \<subseteq> {}" by (metis free_vars_subst)
  with evn_app show ?case by simp
qed simp_all

(* We, obviously, do not have safety here yet. The relevant proofs are in 02/Named. *)

lemma [simp]: "e \<Down> v \<Longrightarrow> valn v"
  by (induction e v rule: evaln.induct) simp_all

lemma val_no_evaln: "e \<Down> v \<Longrightarrow> valn e \<Longrightarrow> v = e"
  by (induction e v rule: evaln.induct) simp_all

theorem determinismn: "e \<Down> v \<Longrightarrow> e \<Down> v' \<Longrightarrow> v = v'"
proof (induction e v arbitrary: v' rule: evaln.induct)
  case (evn_const k)
  thus ?case by (induction "NConst k" v' rule: evaln.induct) simp_all
next
  case (evn_lam x e)
  thus ?case by (induction "NLam x e" v' rule: evaln.induct) simp_all
next
  case (evn_app e\<^sub>1 x e\<^sub>1' e\<^sub>2 v\<^sub>2 v)
  from evn_app(7, 1, 2, 3, 4, 5, 6) show ?case 
    by (induction "NApp e\<^sub>1 e\<^sub>2" v' rule: evaln.induct) blast+
qed

end