theory Closure
  imports "../03Debruijn/DebruijnIndices"
begin

datatype closure = 
  CConst nat
  | CLam ty "closure list" expr\<^sub>d

datatype cframe = 
  CApp1 "closure list" expr\<^sub>d
  | CApp2 closure
  | CReturn "closure list"

datatype closure_state = 
  CSE "cframe list" "closure list"  expr\<^sub>d
  | CSC "cframe list" closure

fun latest_environment :: "cframe list \<rightharpoonup> closure list" where
  "latest_environment [] = None"
| "latest_environment (CApp1 cs e # s) = latest_environment s"
| "latest_environment (CApp2 c # s) = latest_environment s"
| "latest_environment (CReturn cs # s) = Some cs"

inductive typecheck_closure :: "closure \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>c\<^sub>l" 50)
      and typecheck_closure_list :: "closure list \<Rightarrow> ty list \<Rightarrow> bool" (infix ":\<^sub>c\<^sub>l\<^sub>s" 50) where
  tcc_const [simp]: "CConst k :\<^sub>c\<^sub>l Num"
| tcc_lam [simp]: "cs :\<^sub>c\<^sub>l\<^sub>s ts \<Longrightarrow> insert_at 0 t\<^sub>1 ts \<turnstile>\<^sub>d e : t\<^sub>2 \<Longrightarrow> CLam t\<^sub>1 cs e :\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2"
| tcc_nil [simp]: "[] :\<^sub>c\<^sub>l\<^sub>s []"
| tcc_cons [simp]: "c :\<^sub>c\<^sub>l t \<Longrightarrow> cs :\<^sub>c\<^sub>l\<^sub>s ts \<Longrightarrow> c # cs :\<^sub>c\<^sub>l\<^sub>s t # ts"

inductive_cases [elim]:"CConst k :\<^sub>c\<^sub>l t"
inductive_cases [elim]: "CLam t\<^sub>1 cs e :\<^sub>c\<^sub>l t"
inductive_cases [elim]: "[] :\<^sub>c\<^sub>l\<^sub>s ts"
inductive_cases [elim]: "c # cs :\<^sub>c\<^sub>l\<^sub>s ts"

inductive typecheck_cstack :: "cframe list \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>c _ \<rightarrow>" 50) where
  tcc_snil [simp]: "[] :\<^sub>c t \<rightarrow> t"
| tcc_scons_app1 [simp]: "cs :\<^sub>c\<^sub>l\<^sub>s ts \<Longrightarrow> ts \<turnstile>\<^sub>d e : t\<^sub>1 \<Longrightarrow> s :\<^sub>c t\<^sub>2 \<rightarrow> t \<Longrightarrow> 
    latest_environment s = Some cs \<Longrightarrow> CApp1 cs e # s :\<^sub>c Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t"
| tcc_scons_app2 [simp]: "c :\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> s :\<^sub>c t\<^sub>2 \<rightarrow> t \<Longrightarrow> latest_environment s = Some cs \<Longrightarrow> 
    CApp2 c # s :\<^sub>c t\<^sub>1 \<rightarrow> t"
| tcc_scons_ret [simp]: "cs :\<^sub>c\<^sub>l\<^sub>s ts \<Longrightarrow> s :\<^sub>c t' \<rightarrow> t \<Longrightarrow> CReturn cs # s :\<^sub>c t' \<rightarrow> t"

inductive_cases [elim]: "[] :\<^sub>c t' \<rightarrow> t"
inductive_cases [elim]: "CApp1 cs e # s :\<^sub>c t' \<rightarrow> t"
inductive_cases [elim]: "CApp2 c # s :\<^sub>c t' \<rightarrow> t"
inductive_cases [elim]: "CReturn cs # s :\<^sub>c t' \<rightarrow> t"

inductive typecheck_closure_state :: "closure_state \<Rightarrow> ty \<Rightarrow> bool" (infix ":\<^sub>c" 50) where
  tcc_state_ev [simp]: "s :\<^sub>c t' \<rightarrow> t \<Longrightarrow> cs :\<^sub>c\<^sub>l\<^sub>s ts \<Longrightarrow> latest_environment s = Some cs \<Longrightarrow> 
    ts \<turnstile>\<^sub>d e : t' \<Longrightarrow> CSE s cs e :\<^sub>c t"
| tcc_state_ret [simp]: "s :\<^sub>c t' \<rightarrow> t \<Longrightarrow> c :\<^sub>c\<^sub>l t' \<Longrightarrow> CSC s c :\<^sub>c t"

inductive_cases [elim]: "CSE s cs e :\<^sub>c t"
inductive_cases [elim]: "CSC s c :\<^sub>c t"

inductive evalc :: "closure_state \<Rightarrow> closure_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>c" 50) where
  evc_var [simp]: "lookup cs x = Some c \<Longrightarrow> CSE s cs (Var\<^sub>d x) \<leadsto>\<^sub>c CSC s c"
| evc_con [simp]: "CSE s cs (Const\<^sub>d k) \<leadsto>\<^sub>c CSC s (CConst k)"
| evc_lam [simp]: "CSE s cs (Lam\<^sub>d t e) \<leadsto>\<^sub>c CSC s (CLam t cs e)"
| evc_app [simp]: "CSE s cs (App\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>c CSE (CApp1 cs e\<^sub>2 # s) cs e\<^sub>1"
| retc_app1 [simp]: "CSC (CApp1 cs e\<^sub>2 # s) c\<^sub>1 \<leadsto>\<^sub>c CSE (CApp2 c\<^sub>1 # s) cs e\<^sub>2"
| retc_app2 [simp]: "CSC (CApp2 (CLam t cs e\<^sub>1) # s) c\<^sub>2 \<leadsto>\<^sub>c CSE (CReturn (c\<^sub>2 # cs) # s) (c\<^sub>2 # cs) e\<^sub>1"
| retc_ret [simp]: "CSC (CReturn cs # s) c \<leadsto>\<^sub>c CSC s c"

lemma canonical_basec [dest]: "c :\<^sub>c\<^sub>l Num \<Longrightarrow> \<exists>k. c = CConst k"
  by (induction c Num rule: typecheck_closure_typecheck_closure_list.inducts(1)) simp_all

lemma canonical_arrowc [dest]: "c :\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> 
    \<exists>cs ts e. c = CLam t\<^sub>1 cs e \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (insert_at 0 t\<^sub>1 ts \<turnstile>\<^sub>d e : t\<^sub>2)"
  by (induction c "Arrow t\<^sub>1 t\<^sub>2" rule: typecheck_closure_typecheck_closure_list.inducts(1)) auto

lemma  "c :\<^sub>c\<^sub>l t \<Longrightarrow> True"
  and [simp]: "cs :\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> lookup \<Gamma> x = Some t \<Longrightarrow> \<exists>c. lookup cs x = Some c \<and> c :\<^sub>c\<^sub>l t"
proof (induction c t and cs \<Gamma> arbitrary: and x 
       rule: typecheck_closure_typecheck_closure_list.inducts)
  case (tcc_cons c t cs ts)
  thus ?case by (induction x) simp_all
qed simp_all

lemma [simp]: "ts \<turnstile>\<^sub>d e : t \<Longrightarrow> cs :\<^sub>c\<^sub>l\<^sub>s ts \<Longrightarrow> \<exists>\<Sigma>'. CSE s cs e \<leadsto>\<^sub>c \<Sigma>'"
proof (induction ts e t rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_var \<Gamma> x t)
  then obtain c where "lookup cs x = Some c \<and> c :\<^sub>c\<^sub>l t" by fastforce
  hence "CSE s cs (Var\<^sub>d x) \<leadsto>\<^sub>c CSC s c" by simp
  thus ?case by fastforce 
next
  case (tc\<^sub>d_const \<Gamma> k)
  have "CSE s cs (Const\<^sub>d k) \<leadsto>\<^sub>c CSC s (CConst k)" by simp
  thus ?case by fastforce 
next
  case (tc\<^sub>d_lam t\<^sub>1 \<Gamma> e t\<^sub>2)
  have "CSE s cs (Lam\<^sub>d t\<^sub>1 e) \<leadsto>\<^sub>c CSC s (CLam t\<^sub>1 cs e)" by simp
  thus ?case by fastforce 
next
  case (tc\<^sub>d_app \<Gamma> e\<^sub>1 t\<^sub>1 t\<^sub>2 e\<^sub>2)
  have "CSE s cs (App\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>c CSE (CApp1 cs e\<^sub>2 # s) cs e\<^sub>1" by simp
  then show ?case by fastforce
qed

lemma [simp]: "s :\<^sub>c t' \<rightarrow> t \<Longrightarrow> c :\<^sub>c\<^sub>l t' \<Longrightarrow> s = [] \<or> (\<exists>\<Sigma>'. CSC s c \<leadsto>\<^sub>c \<Sigma>')"
proof (induction s t' t rule: typecheck_cstack.induct)
  case (tcc_scons_app1 cs ts e\<^sub>2 t\<^sub>1 s t\<^sub>2 t)
  moreover hence "CSC (CApp1 cs e\<^sub>2 # s) c \<leadsto>\<^sub>c CSE (CApp2 c # s) cs e\<^sub>2" by simp
  ultimately show ?case by fastforce
next
  case (tcc_scons_app2 c\<^sub>1 t\<^sub>1 t\<^sub>2 s t)
  then obtain cs ts e where "c\<^sub>1 = CLam t\<^sub>1 cs e \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (insert_at 0 t\<^sub>1 ts \<turnstile>\<^sub>d e : t\<^sub>2)" 
    by blast
  moreover hence "CSC (CApp2 (CLam t\<^sub>1 cs e) # s) c \<leadsto>\<^sub>c CSE (CReturn (c # cs) # s) (c # cs) e" by simp
  ultimately show ?case by fastforce
next
  case (tcc_scons_ret cs ts s t' t)
  have "CSC (CReturn cs # s) c \<leadsto>\<^sub>c CSC s c" by simp
  thus ?case by fastforce
qed simp_all

theorem progressc: "\<Sigma> :\<^sub>c t \<Longrightarrow> (\<exists>c. \<Sigma> = CSC [] c) \<or> (\<exists>\<Sigma>'. \<Sigma> \<leadsto>\<^sub>c \<Sigma>')"
  by (induction \<Sigma> t rule: typecheck_closure_state.induct) simp_all

theorem preservationc [simp]: "\<Sigma> \<leadsto>\<^sub>c \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow> \<Sigma>' :\<^sub>c t"
proof (induction \<Sigma> \<Sigma>' rule: evalc.induct)
  case (evc_var cs x c s)
  then obtain t' ts where X: "s :\<^sub>c t' \<rightarrow> t" and "(cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> lookup ts x = Some t'" by blast
  then obtain c' where "lookup cs x = Some c' \<and> c' :\<^sub>c\<^sub>l t'" by fastforce
  with evc_var X show ?case by simp
next
  case (evc_app s cs e\<^sub>1 e\<^sub>2)
  then obtain t\<^sub>1 t\<^sub>2 ts where "(s :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> (ts \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1)" 
   and X: "(cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs \<and> (ts \<turnstile>\<^sub>d e\<^sub>1 : Arrow t\<^sub>1 t\<^sub>2)" by blast
  hence "CApp1 cs e\<^sub>2 # s :\<^sub>c Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t"  by fastforce
  with X show ?case by fastforce
next
  case (retc_app1 cs e\<^sub>2 s c\<^sub>1)
  then obtain ts t\<^sub>1 t\<^sub>2 where X: "(cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs \<and> (ts \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1)" 
   and "(s :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> (c\<^sub>1 :\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2)" by blast
  hence "CApp2 c\<^sub>1 # s :\<^sub>c t\<^sub>1 \<rightarrow> t" by fastforce
  with X show ?case by fastforce
next
  case (retc_app2 t\<^sub>1 cs e\<^sub>1 s c\<^sub>2)
  then obtain ts t\<^sub>2 where X: "s :\<^sub>c t\<^sub>2 \<rightarrow> t" and Y: "insert_at 0 t\<^sub>1 ts \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2" 
   and "(cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (c\<^sub>2 :\<^sub>c\<^sub>l t\<^sub>1)" by blast
  hence Z: "c\<^sub>2 # cs :\<^sub>c\<^sub>l\<^sub>s insert_at 0 t\<^sub>1 ts" by (induction ts) simp_all
  with X have "CReturn (c\<^sub>2 # cs) # s :\<^sub>c t\<^sub>2 \<rightarrow> t" by simp
  with Y Z show ?case by fastforce
qed fastforce+

lemma [simp]: "iter (\<leadsto>\<^sub>c) \<Sigma> \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow> \<Sigma>' :\<^sub>c t"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

theorem determinismc: "\<Sigma> \<leadsto>\<^sub>c \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>c \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalc.induct)
  case (evc_var cs x c s)
  from evc_var(2, 1) show ?case by (induction "CSE s cs (Var\<^sub>d x)" \<Sigma>'' rule: evalc.induct) simp_all 
next
  case (evc_con s cs k)
  thus ?case by (induction "CSE s cs (Const\<^sub>d k)" \<Sigma>'' rule: evalc.induct) simp_all 
next
  case (evc_lam s cs t e)
  thus ?case by (induction "CSE s cs (Lam\<^sub>d t e)" \<Sigma>'' rule: evalc.induct) simp_all 
next
  case (evc_app s cs e\<^sub>1 e\<^sub>2)
  thus ?case by (induction "CSE s cs (App\<^sub>d e\<^sub>1 e\<^sub>2)" \<Sigma>'' rule: evalc.induct) simp_all 
next
  case (retc_app1 cs e\<^sub>2 s c\<^sub>1)
  thus ?case by (induction "CSC (CApp1 cs e\<^sub>2 # s) c\<^sub>1" \<Sigma>'' rule: evalc.induct) simp_all 
next
  case (retc_app2 t cs e\<^sub>1 s c\<^sub>2)
  thus ?case by (induction "CSC (CApp2 (CLam t cs e\<^sub>1) # s) c\<^sub>2" \<Sigma>'' rule: evalc.induct) simp_all 
next
  case (retc_ret cs s c)
  thus ?case by (induction "CSC (CReturn cs # s) c" \<Sigma>'' rule: evalc.induct) simp_all 
qed

end