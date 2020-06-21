theory Debruijn
  imports "../02Source/Type" "../00Utils/Environment" "../00Utils/Iteration"
begin

datatype dexpr = 
  DVar nat
  | DConst nat
  | DLam ty dexpr
  | DApp dexpr dexpr

inductive typecheckd :: "ty list \<Rightarrow> dexpr \<Rightarrow> ty \<Rightarrow> bool" (infix "\<turnstile>\<^sub>d _ :" 50) where
  tcd_var [simp]: "lookup \<Gamma> x = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d DVar x : t"
| tcd_const [simp]: "\<Gamma> \<turnstile>\<^sub>d DConst k : Base"
| tcd_lam [simp]: "insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e : t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d DLam t\<^sub>1 e : Arrow t\<^sub>1 t\<^sub>2"
| tcd_app [simp]: "\<Gamma> \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1 \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d DApp e\<^sub>1 e\<^sub>2 : t\<^sub>2"

inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>d DVar x : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>d DConst k : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>d DLam t' e : t"
inductive_cases [elim]: "\<Gamma> \<turnstile>\<^sub>d DApp e\<^sub>1 e\<^sub>2 : t"

primrec vald :: "dexpr \<Rightarrow> bool" where
  "vald (DVar x) = False"
| "vald (DConst k) = True" 
| "vald (DLam t e) = True" 
| "vald (DApp e\<^sub>1 e\<^sub>2) = False" 

primrec incrd :: "nat \<Rightarrow> dexpr \<Rightarrow> dexpr" where
  "incrd x (DVar y) = DVar (incr x y)"
| "incrd x (DConst k) = DConst k"
| "incrd x (DLam t e) = DLam t (incrd (Suc x) e)"
| "incrd x (DApp e\<^sub>1 e\<^sub>2) = DApp (incrd x e\<^sub>1) (incrd x e\<^sub>2)"

primrec substd :: "nat \<Rightarrow> dexpr \<Rightarrow> dexpr \<Rightarrow> dexpr" where
  "substd x e' (DVar y) = (if x = y then e' else DVar (decr x y))"
| "substd x e' (DConst k) = DConst k"
| "substd x e' (DLam t e) = DLam t (substd (Suc x) (incrd 0 e') e)"
| "substd x e' (DApp e\<^sub>1 e\<^sub>2) = DApp (substd x e' e\<^sub>1) (substd x e' e\<^sub>2)"

inductive evald :: "dexpr \<Rightarrow> dexpr \<Rightarrow> bool" (infix "\<leadsto>\<^sub>d" 50) where
  evd_app1 [simp]: "e\<^sub>1 \<leadsto>\<^sub>d e\<^sub>1' \<Longrightarrow> DApp e\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>d DApp e\<^sub>1' e\<^sub>2"
| evd_app2 [simp]: "vald e\<^sub>1 \<Longrightarrow> e\<^sub>2 \<leadsto>\<^sub>d e\<^sub>2' \<Longrightarrow> DApp e\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>d DApp e\<^sub>1 e\<^sub>2'"
| evd_app3 [simp]: "vald e\<^sub>2 \<Longrightarrow> DApp (DLam t e\<^sub>1) e\<^sub>2 \<leadsto>\<^sub>d substd 0 e\<^sub>2 e\<^sub>1"

lemma tc_postpend [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> (\<Gamma> @ \<Gamma>') \<turnstile>\<^sub>d e : t"
  by (induction \<Gamma> e t rule: typecheckd.induct) simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>d) e\<^sub>1 e\<^sub>1' \<Longrightarrow> iter (\<leadsto>\<^sub>d) (DApp e\<^sub>1 e\<^sub>2) (DApp e\<^sub>1' e\<^sub>2)"
proof (induction e\<^sub>1 e\<^sub>1' rule: iter.induct)
  case (iter_step e\<^sub>1 e\<^sub>1' e\<^sub>1'')
  hence "DApp e\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>d DApp e\<^sub>1' e\<^sub>2" by simp
  moreover from iter_step have "iter (\<leadsto>\<^sub>d) (DApp e\<^sub>1' e\<^sub>2) (DApp e\<^sub>1'' e\<^sub>2)" by simp
  ultimately show ?case by simp
qed simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>d) e\<^sub>2 e\<^sub>2' \<Longrightarrow> vald e\<^sub>1 \<Longrightarrow> iter (\<leadsto>\<^sub>d) (DApp e\<^sub>1 e\<^sub>2) (DApp e\<^sub>1 e\<^sub>2')"
proof (induction e\<^sub>2 e\<^sub>2' rule: iter.induct)
  case (iter_step e\<^sub>2 e\<^sub>2' e\<^sub>2'')
  hence "DApp e\<^sub>1 e\<^sub>2 \<leadsto>\<^sub>d DApp e\<^sub>1 e\<^sub>2'" by simp
  moreover from iter_step have "iter (\<leadsto>\<^sub>d) (DApp e\<^sub>1 e\<^sub>2') (DApp e\<^sub>1 e\<^sub>2'')" by simp
  ultimately show ?case by simp
qed simp_all

lemma [simp]: "y \<le> x \<Longrightarrow> incrd y (incrd x e) = incrd (Suc x) (incrd y e)"
  by (induction e arbitrary: x y) simp_all

lemma [simp]: "vald e \<Longrightarrow> vald (incrd x e)"
  by (induction e) simp_all

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> x \<ge> length \<Gamma> \<Longrightarrow> incrd x e = e"
proof (induction \<Gamma> e t arbitrary: x rule: typecheckd.induct)
  case (tcd_var \<Gamma> y t)
  moreover hence "y < length \<Gamma>" by simp
  ultimately have "y < x" by linarith
  thus ?case by (simp add: incr_min)
qed simp_all

lemma [simp]: "y \<le> x \<Longrightarrow> incrd y (substd x e' e) = substd (Suc x) (incrd y e') (incrd y e)"
  by (induction e arbitrary: x y e') (simp_all add: incr_le incr_lemma)

lemma [simp]: "substd x e' (incrd x e) = e"
  by (induction e arbitrary: x e') (simp_all, metis incr_not_eq)

lemma [simp]: "substd 0 e' e = DVar x \<Longrightarrow> vald e' \<Longrightarrow> e = DVar (Suc x)"
proof (induction e)
  case (DVar y)
  thus ?case by (induction y) simp_all
qed simp_all

lemma [simp]: "vald (substd 0 e' e) \<Longrightarrow> vald e' \<Longrightarrow> vald e \<or> e = DVar 0"
  by (induction e) (simp_all split: if_splits)

lemma [simp]: "y \<le> x \<Longrightarrow> 
  substd x e\<^sub>1 (substd y e\<^sub>2 e) = substd y (substd x e\<^sub>1 e\<^sub>2) (substd (Suc x) (incrd y e\<^sub>1) e)"
proof (induction e arbitrary: x y e\<^sub>1 e\<^sub>2)
  case (DVar z)
  thus ?case 
  proof (cases "y = z")
    case False
    with DVar show ?thesis 
    proof (cases "x = decr y z")
      case True note TXD = True
      with DVar False show ?thesis
      proof (cases "y = decr y z")
        case True
        with False have "z = Suc y" by simp
        with TXD show ?thesis by auto
      qed simp_all
    qed auto
  qed simp_all
qed simp_all

lemma canonical_based [dest]: "\<Gamma> \<turnstile>\<^sub>d e : Base \<Longrightarrow> vald e \<Longrightarrow> \<exists>k. e = DConst k"
  by (induction \<Gamma> e Base rule: typecheckd.induct) simp_all

lemma canonical_arrowd [dest]: "\<Gamma> \<turnstile>\<^sub>d e : Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> vald e \<Longrightarrow> 
    \<exists>e'. e = DLam t\<^sub>1 e' \<and> insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e' : t\<^sub>2"
  by (induction \<Gamma> e "Arrow t\<^sub>1 t\<^sub>2" rule: typecheckd.induct) simp_all

theorem progressd: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> vald e \<or> (\<exists>e'. e \<leadsto>\<^sub>d e')"
proof (induction "[] :: ty list" e t rule: typecheckd.induct)
  case (tcd_app e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  thus ?case 
  proof (cases "vald e\<^sub>1")
    case True note T = True
    thus ?thesis 
    proof (cases "vald e\<^sub>2")
      case True
      with tcd_app T show ?thesis by (metis canonical_arrowd evd_app3)
    next
      case False
      with tcd_app T show ?thesis by (metis evd_app2)
    qed
  next
    case False
    with tcd_app show ?thesis by (metis evd_app1)
  qed
qed simp_all

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> insert_at x t' \<Gamma> \<turnstile>\<^sub>d incrd x e : t" 
proof (induction \<Gamma> e t arbitrary: x rule: typecheckd.induct)
  case (tcd_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  hence "insert_at x t' \<Gamma> \<turnstile>\<^sub>d (incrd x e\<^sub>1) : Arrow t\<^sub>1 t\<^sub>2" by simp
  moreover from tcd_app have "insert_at x t' \<Gamma> \<turnstile>\<^sub>d (incrd x e\<^sub>2) : t\<^sub>1" by simp
  ultimately show ?case by simp
qed fastforce+

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> x \<ge> length \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d incrd x e : t"
proof (induction e arbitrary: \<Gamma> x t)
  case (DVar y)
  hence X: "lookup \<Gamma> y = Some t" by fastforce
  hence "y < length \<Gamma>" by simp
  with DVar have "x > y" by simp
  with X have "lookup \<Gamma> (incr x y) = Some t" using incr_min by (simp, linarith)
  then show ?case by simp
qed fastforce+

lemma [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> x \<ge> length \<Gamma> \<Longrightarrow> substd x e' e = e"
proof (induction \<Gamma> e t arbitrary: x e' rule: typecheckd.induct)
  case (tcd_var \<Gamma> y t)
  hence "y < length \<Gamma>" by simp
  with tcd_var have "y < x" by linarith
  with tcd_var show ?case by auto
qed simp_all

lemma [simp]: "insert_at x t' \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> x \<le> length \<Gamma> \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e' : t' \<Longrightarrow> 
  \<Gamma> \<turnstile>\<^sub>d substd x e' e : t"
proof (induction "insert_at x t' \<Gamma>" e t arbitrary: \<Gamma> x e' rule: typecheckd.induct)
  case (tcd_var y t)
  moreover have "x \<le> length \<Gamma> \<Longrightarrow> x \<noteq> y \<Longrightarrow> lookup \<Gamma> (decr x y) = lookup (insert_at x t' \<Gamma>) y" 
    by simp
  ultimately show ?case by fastforce
qed fastforce+ 

theorem preservationd [simp]: "e \<leadsto>\<^sub>d e' \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>d e' : t"
  by (induction e e' arbitrary: t rule: evald.induct) fastforce+

lemma val_no_evald: "e \<leadsto>\<^sub>d e' \<Longrightarrow> vald e \<Longrightarrow> False"
  by (induction e e' rule: evald.induct) simp_all

theorem determinismd: "e \<leadsto>\<^sub>d e' \<Longrightarrow> e \<leadsto>\<^sub>d e'' \<Longrightarrow> e' = e''"
proof (induction e e' arbitrary: e'' rule: evald.induct)
case (evd_app1 e\<^sub>1 e\<^sub>1' e\<^sub>2)
  from evd_app1(3, 1, 2) show ?case 
    by (induction "DApp e\<^sub>1 e\<^sub>2" e'' rule: evald.induct) 
       (metis, metis val_no_evald, metis val_no_evald vald.simps(3))
next
  case (evd_app2 e\<^sub>1 e\<^sub>2 e\<^sub>2')
  from evd_app2(4, 1, 2, 3) show ?case 
    by (induction "DApp e\<^sub>1 e\<^sub>2" e'' rule: evald.induct) 
       (metis val_no_evald, metis, metis val_no_evald)
next
  case (evd_app3 e\<^sub>2 t e\<^sub>1)
  from evd_app3(2, 1) show ?case 
    by (induction "DApp (DLam t e\<^sub>1) e\<^sub>2" e'' rule: evald.induct) 
       (metis val_no_evald vald.simps(3), metis val_no_evald, metis)
qed

lemma evald_backwards: "iter (\<leadsto>\<^sub>d) e v \<Longrightarrow> vald v \<Longrightarrow> e \<leadsto>\<^sub>d e' \<Longrightarrow> iter (\<leadsto>\<^sub>d) e' v"
  by (induction e v rule: iter.induct) (metis val_no_evald, metis determinismd)

end