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

(* We, obviously, do not have safety here yet. The relevant proofs are in 03Debruijn/NameRemoval. *)

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