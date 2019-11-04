theory Named
  imports Type Variable Utils
begin

datatype nexpr = 
  NVar var
  | NConst nat
  | NLam var ty nexpr
  | NApp nexpr nexpr

primrec all_vars :: "nexpr \<Rightarrow> var set" where
  "all_vars (NVar x) = {x}"
| "all_vars (NConst k) = {}"
| "all_vars (NLam x t e) = insert x (all_vars e)"
| "all_vars (NApp e\<^sub>1 e\<^sub>2) = all_vars e\<^sub>1 \<union> all_vars e\<^sub>2"

primrec binders :: "nexpr \<Rightarrow> var set" where
  "binders (NVar x) = {}"
| "binders (NConst k) = {}"
| "binders (NLam x t e) = insert x (binders e)"
| "binders (NApp e\<^sub>1 e\<^sub>2) = binders e\<^sub>1 \<union> binders e\<^sub>2"

primrec free_vars :: "nexpr \<Rightarrow> var set" where
  "free_vars (NVar x) = {x}"
| "free_vars (NConst k) = {}"
| "free_vars (NLam x t e) = free_vars e - {x}"
| "free_vars (NApp e\<^sub>1 e\<^sub>2) = free_vars e\<^sub>1 \<union> free_vars e\<^sub>2"

inductive typecheckn :: "(var \<rightharpoonup> ty) \<Rightarrow> nexpr \<Rightarrow> ty \<Rightarrow> bool" (infix "\<turnstile>\<^sub>n _ :" 50) where
  tcn_var [simp]: "\<Gamma> x = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n NVar x : t"
| tcn_const [simp]: "\<Gamma> \<turnstile>\<^sub>n NConst k : Base"
| tcn_lam [simp]: "\<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n NLam x t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2"
| tcn_app [simp]: "\<Gamma> \<turnstile>\<^sub>n e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e\<^sub>2 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n NApp e\<^sub>1 e\<^sub>2 : t\<^sub>2"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n NVar x : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n NConst k : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n NLam x t' e : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>n NApp e\<^sub>1 e\<^sub>2 : t"

primrec valn :: "nexpr \<Rightarrow> bool" where
  "valn (NVar x) = False"
| "valn (NConst k) = True" 
| "valn (NLam x t e) = True" 
| "valn (NApp e\<^sub>1 e\<^sub>2) = False" 

primrec subst_var :: "var \<Rightarrow> var \<Rightarrow> nexpr \<Rightarrow> nexpr" where
  "subst_var x x' (NVar y) = NVar (if x = y then x' else y)"
| "subst_var x x' (NConst k) = NConst k"
| "subst_var x x' (NLam y t e) = NLam y t (if x = y then e else subst_var x x' e)"
| "subst_var x x' (NApp e\<^sub>1 e\<^sub>2) = NApp (subst_var x x' e\<^sub>1) (subst_var x x' e\<^sub>2)"

lemma [simp]: "size (subst_var x x' e) = size e"
  by (induction e) simp_all

fun substn :: "var \<Rightarrow> nexpr \<Rightarrow> nexpr \<Rightarrow> nexpr" where
  "substn x e' (NVar y) = (if x = y then e' else NVar y)"
| "substn x e' (NConst k) = NConst k"
| "substn x e' (NLam y t e) = (
    let z = fresh (all_vars e' \<union> all_vars e \<union> {x, y})
    in NLam z t (substn x e' (subst_var y z e)))"
| "substn x e' (NApp e\<^sub>1 e\<^sub>2) = NApp (substn x e' e\<^sub>1) (substn x e' e\<^sub>2)"

inductive evaln :: "nexpr \<Rightarrow> nexpr \<Rightarrow> bool" (infix "\<leadsto>\<^sub>n" 50) where
  evn_app1 [simp]: "e\<^sub>1 \<leadsto>\<^sub>n e\<^sub>1' \<Longrightarrow> NApp e\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>n NApp e\<^sub>1' e\<^sub>2"
| evn_app2 [simp]: "valn e\<^sub>1 \<Longrightarrow> e\<^sub>2 \<leadsto>\<^sub>n e\<^sub>2' \<Longrightarrow> NApp e\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>n NApp e\<^sub>1 e\<^sub>2'"
| evn_app3 [simp]: "valn e\<^sub>2 \<Longrightarrow> NApp (NLam x t e\<^sub>1) e\<^sub>2 \<leadsto>\<^sub>n substn x e\<^sub>2 e\<^sub>1"

lemma [simp]: "finite (all_vars e)"
  by (induction e) simp_all

lemma [simp]: "free_vars e \<subseteq> insert x xs \<Longrightarrow> free_vars (subst_var x x' e) \<subseteq> insert x' xs"
proof (induction e arbitrary: xs)
  case (NLam y t e)
  hence "free_vars e \<subseteq> insert x (insert y xs)" by auto
  with NLam have "free_vars (subst_var x x' e) \<subseteq> insert x' (insert y xs)" by simp
  with NLam show ?case by auto
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

lemma [simp]: "e \<leadsto>\<^sub>n e' \<Longrightarrow> free_vars e = {} \<Longrightarrow> free_vars e' = {}"
proof (induction e e' rule: evaln.induct)
  case (evn_app3 e\<^sub>2 x t e\<^sub>1)
  hence "free_vars e\<^sub>1 \<subseteq> insert x {} \<and> free_vars e\<^sub>2 \<subseteq> {}" by simp
  hence "free_vars (substn x e\<^sub>2 e\<^sub>1) \<subseteq> {}" by (metis free_vars_subst)
  thus ?case by simp
qed simp_all

lemma free_vars_subs [simp]: "\<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> free_vars e \<subseteq> dom \<Gamma>" 
  by (induction \<Gamma> e t rule: typecheckn.induct) auto

lemma [simp]: "Map.empty \<turnstile>\<^sub>n e : t \<Longrightarrow> free_vars e = {}"
  using free_vars_subs by fastforce

lemma canonical_basen [dest]: "\<Gamma> \<turnstile>\<^sub>n e : Base \<Longrightarrow> valn e \<Longrightarrow> \<exists>k. e = NConst k"
  by (induction \<Gamma> e Base rule: typecheckn.induct) simp_all

lemma canonical_arrown [dest]: "\<Gamma> \<turnstile>\<^sub>n e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> valn e \<Longrightarrow> 
    \<exists>x e'. e = NLam x t\<^sub>1 e' \<and> \<Gamma>(x \<mapsto> t\<^sub>1) \<turnstile>\<^sub>n e' : t\<^sub>2"
  by (induction \<Gamma> e "Arrow t\<^sub>1 t\<^sub>2" rule: typecheckn.induct) simp_all

theorem progressn: "Map.empty \<turnstile>\<^sub>n e : t \<Longrightarrow> valn e \<or> (\<exists>e'. e \<leadsto>\<^sub>n e')"
proof (induction "Map.empty :: var \<rightharpoonup> ty" e t rule: typecheckn.induct)
  case (tcn_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  thus ?case 
  proof (cases "valn e\<^sub>1")
    case True note T = True
    thus ?thesis 
    proof (cases "valn e\<^sub>2")
      case True
      with tcn_app T show ?thesis by (metis canonical_arrown evn_app3)
    next
      case False
      with tcn_app T show ?thesis by (metis evn_app2)
    qed
  next
    case False
    with tcn_app show ?thesis by (metis evn_app1)
  qed
qed simp_all

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

theorem preservationn: "e \<leadsto>\<^sub>n e' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e' : t"
  by (induction e e' arbitrary: t rule: evaln.induct) fastforce+

lemma val_no_evaln: "e \<leadsto>\<^sub>n e' \<Longrightarrow> valn e \<Longrightarrow> False"
  by (induction e e' rule: evaln.induct) simp_all

theorem determinismn: "e \<leadsto>\<^sub>n e' \<Longrightarrow> e \<leadsto>\<^sub>n e'' \<Longrightarrow> e' = e''"
proof (induction e e' arbitrary: e'' rule: evaln.induct)
case (evn_app1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
  from evn_app1(3, 1, 2) show ?case 
    by (induction "NApp e\<^sub>1 e\<^sub>2" e'' rule: evaln.induct) 
       (metis, metis val_no_evaln, metis val_no_evaln valn.simps(3))
next
  case (evn_app2 e\<^sub>1 e\<^sub>2 e\<^sub>2')
  from evn_app2(4, 1, 2, 3) show ?case 
    by (induction "NApp e\<^sub>1 e\<^sub>2" e'' rule: evaln.induct) 
       (metis val_no_evaln, metis, metis val_no_evaln)
next
  case (evn_app3 e\<^sub>2 x t e\<^sub>1)
  from evn_app3(2, 1) show ?case 
    by (induction "NApp (NLam x t e\<^sub>1) e\<^sub>2" e'' rule: evaln.induct) 
       (metis val_no_evaln valn.simps(3), metis val_no_evaln, metis)
qed

end