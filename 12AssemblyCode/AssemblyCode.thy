theory AssemblyCode
  imports "../00Utils/Iteration" "../00Utils/Environment"
begin

datatype register = Hp | Env | Vals | Stk

datatype move_src = Reg "register option" | Con nat 

datatype assm = 
  AGet "register option"
  | APut "register option" move_src
  | ASub "register option" nat
  | AAdd "register option" nat
  | AJmp

datatype assm_state = 
  AS "register option \<Rightarrow> nat \<Rightarrow> register option \<times> nat" "register option \<Rightarrow> nat" "register option" nat

primrec registers_case :: "'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> register option \<Rightarrow> 'a" where
  "registers_case hp ep vp sp a (Some r) = case_register hp ep vp sp r"
| "registers_case hp ep vp sp a None = a"

fun mem_upd :: "(register option \<Rightarrow> nat \<Rightarrow> register option \<times> nat) \<Rightarrow> register option \<Rightarrow> nat \<Rightarrow> 
    register option \<times> nat \<Rightarrow> register option \<Rightarrow> nat \<Rightarrow> register option \<times> nat" where
  "mem_upd mem m mp k m' x = (if m = m' \<and> mp = x then k else mem m' x)"

fun assm_step :: "(register option \<Rightarrow> nat \<Rightarrow> register option \<times> nat) \<Rightarrow> (register option \<Rightarrow> nat) \<Rightarrow>
    register option \<Rightarrow> nat \<Rightarrow> assm \<rightharpoonup> assm_state" where
  "assm_step mem ps act pc (AGet (Some r)) = (case mem (Some r) (ps (Some r)) of
      (t, b) \<Rightarrow> Some (AS mem (ps(None := b)) t pc))"
| "assm_step mem ps None pc (AGet None) = None"
| "assm_step mem ps (Some r) pc (AGet None) = (case mem (Some r) (ps None) of
      (t, b) \<Rightarrow> Some (AS mem (ps(None := b)) t pc))"
| "assm_step mem ps act pc (APut None (Reg (Some r))) = 
    Some (AS mem (ps(None := ps (Some r))) (Some r) pc)"
| "assm_step mem ps act pc (APut None (Reg None)) = Some (AS mem ps act pc)"
| "assm_step mem ps act pc (APut None (Con k)) = Some (AS mem (ps(None := k)) None pc)"
| "assm_step mem ps act pc (APut (Some r) (Reg (Some r'))) = 
    Some (AS (mem_upd mem (Some r) (ps (Some r)) (Some r', ps (Some r'))) ps act pc)"
| "assm_step mem ps act pc (APut (Some r) (Reg None)) = 
    Some (AS (mem_upd mem (Some r) (ps (Some r)) (act, ps None)) ps act pc)"
| "assm_step mem ps act pc (APut (Some r) (Con k)) = 
    Some (AS (mem_upd mem (Some r) (ps (Some r)) (None, k)) ps act pc)"
| "assm_step mem ps act pc (ASub (Some r) k) = 
    (if ps (Some r) \<ge> k then Some (AS mem (ps(Some r := ps (Some r) - k)) act pc) else None)"
| "assm_step mem ps None pc (ASub None k) = None"
| "assm_step mem ps (Some r) pc (ASub None k) =
    (if ps None \<ge> k then Some (AS mem (ps(None := ps None - k)) (Some r) pc) else None)"
| "assm_step mem ps act pc (AAdd (Some r) k) = 
    Some (AS mem (ps(Some r := ps (Some r) + k)) act pc)"
| "assm_step mem ps None pc (AAdd None k) = None"
| "assm_step mem ps (Some r) pc (AAdd None k) = Some (AS mem (ps(None := ps None + k)) (Some r) pc)"
| "assm_step mem ps None pc AJmp = Some (AS mem (ps(None := 0)) None (ps None))"
| "assm_step mem ps (Some r) pc AJmp = None"

fun alg_evala :: "assm list \<Rightarrow> assm_state \<rightharpoonup> assm_state" (infix "\<tturnstile>\<^sub>a" 50) where
  "cd \<tturnstile>\<^sub>a AS mem ps act pc = (case pc of
      0 \<Rightarrow> None
    | Suc pc \<Rightarrow> Option.bind (lookup cd pc) (assm_step mem ps act pc))"

primrec iter_evala :: "assm list \<Rightarrow> nat \<Rightarrow> assm_state \<rightharpoonup> assm_state" where
  "iter_evala cd 0 \<Sigma> = Some \<Sigma>"
| "iter_evala cd (Suc x) \<Sigma> = Option.bind (cd \<tturnstile>\<^sub>a \<Sigma>) (iter_evala cd x)"

inductive evala :: "assm list \<Rightarrow> assm_state \<Rightarrow> assm_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>a" 50) where
  eva_movr [simp]: "lookup cd pc = Some (APut None (Reg (Some r))) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(None := ps (Some r))) (Some r) pc"
| eva_mova [simp]: "lookup cd pc = Some (APut None (Reg None)) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem ps act pc"
| eva_movk [simp]: "lookup cd pc = Some (APut None (Con k)) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(None := k)) None pc"
| eva_get [simp]: "lookup cd pc = Some (AGet (Some r)) \<Longrightarrow> mem (Some r) (ps (Some r)) = (t, b) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(None := b)) t pc"
| eva_geta [simp]: "lookup cd pc = Some (AGet None) \<Longrightarrow> mem (Some m) (ps None) = (t, b) \<Longrightarrow>
    cd \<tturnstile> AS mem ps (Some m) (Suc pc) \<leadsto>\<^sub>a AS mem (ps(None := b)) t pc"
| eva_putr [simp]: "lookup cd pc = Some (APut (Some r) (Reg (Some r'))) \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a 
      AS (mem_upd mem (Some r) (ps (Some r)) (Some r', ps (Some r'))) ps act pc"
| eva_puta [simp]: "lookup cd pc = Some (APut (Some r) (Reg None)) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a 
      AS (mem_upd mem (Some r) (ps (Some r)) (act, ps None)) ps act pc"
| eva_putk [simp]: "lookup cd pc = Some (APut (Some r) (Con k)) \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem (Some r) (ps (Some r)) (None, k)) ps act pc"
| eva_suba [simp]: "lookup cd pc = Some (ASub None k) \<Longrightarrow> ps None \<ge> k \<Longrightarrow> 
    cd \<tturnstile> AS mem ps (Some r) (Suc pc) \<leadsto>\<^sub>a AS mem (ps(None := ps None - k)) (Some r) pc"
| eva_sub [simp]: "lookup cd pc = Some (ASub (Some r) k) \<Longrightarrow> ps (Some r) \<ge> k \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Some r := ps (Some r) - k)) act pc"
| eva_add [simp]: "lookup cd pc = Some (AAdd (Some r) k) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Some r := ps (Some r) + k)) act pc"
| eva_adda [simp]: "lookup cd pc = Some (AAdd None k) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps (Some r) (Suc pc) \<leadsto>\<^sub>a AS mem (ps(None := ps None + k)) (Some r) pc"
| eva_jmp [simp]: "lookup cd pc = Some AJmp \<Longrightarrow> 
    cd \<tturnstile> AS mem ps None (Suc pc) \<leadsto>\<^sub>a AS mem (ps(None := 0)) None (ps None)"

lemma [simp]: "mem_upd (registers_case h e vs sh a) (Some Hp) x y = registers_case (h(x := y)) e vs sh a"
proof (rule, rule)
  fix m n
  show "mem_upd (registers_case h e vs sh a) (Some Hp) x y m n =
    registers_case (h(x := y)) e vs sh a m n"
      by (induction m) (simp_all split: register.splits)
qed

lemma [simp]: "mem_upd (registers_case h e vs sh a) (Some Env) x y = registers_case h (e(x := y)) vs sh a"
proof (rule, rule)
  fix m n
  show "mem_upd (registers_case h e vs sh a) (Some Env) x y m n =
    registers_case h (e(x := y)) vs sh a m n"
      by (induction m) (simp_all split: register.splits)
qed

lemma [simp]: "mem_upd (registers_case h e vs sh a) (Some Vals) x y = registers_case h e (vs(x := y)) sh a"
proof (rule, rule)
  fix m n
  show "mem_upd (registers_case h e vs sh a) (Some Vals) x y m n =
    registers_case h e (vs(x := y)) sh a m n"
      by (induction m) (simp_all split: register.splits)
qed

lemma [simp]: "mem_upd (registers_case h e vs sh a) (Some Stk) x y = registers_case h e vs (sh(x := y)) a"
proof (rule, rule)
  fix m n
  show "mem_upd (registers_case h e vs sh a) (Some Stk) x y m n =
    registers_case h e vs (sh(x := y)) a m n"
      by (induction m) (simp_all split: register.splits)
qed

lemma [simp]: "(case_register hp ep vp sp)(Hp := x) = case_register x ep vp sp"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp)(Env := x) = case_register hp x vp sp"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp)(Vals := x) = case_register hp ep x sp"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp)(Stk := x) = case_register hp ep vp x"
  by rule (simp split: register.splits)

lemma iter_evala_combine [simp]: "iter_evala cd n \<Sigma> = Some \<Sigma>' \<Longrightarrow> 
  iter_evala cd m \<Sigma>' = Some \<Sigma>'' \<Longrightarrow> iter_evala cd (n + m) \<Sigma> = Some \<Sigma>''"
proof (induction n arbitrary: \<Sigma>)
  case (Suc n)
  then show ?case by (cases "cd \<tturnstile>\<^sub>a \<Sigma>") simp_all
qed simp_all

lemma assm_step_equiv: "(Option.bind (lookup cd pc) (assm_step mem ps act pc) = Some \<Sigma>) \<Longrightarrow>
  (cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a \<Sigma>)"
proof (cases "lookup cd pc")
  case (Some op)
  moreover assume "Option.bind (lookup cd pc) (assm_step mem ps act pc) = Some \<Sigma>"
  ultimately show ?thesis 
    by (induction mem ps act pc op rule: assm_step.induct) (auto split: if_splits prod.splits)
qed simp_all

lemma alg_evala_equiv: "cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>' = (cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>')"
proof
  show "cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>'"
    by (induction \<Sigma>) (auto simp add: assm_step_equiv split: nat.splits)
  show "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>' \<Longrightarrow> cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>'" 
    by (induction cd \<Sigma> \<Sigma>' rule: evala.induct) simp_all
qed

lemma iter_evala_equiv: "(\<exists>n. iter_evala cd n \<Sigma> = Some \<Sigma>') = iter (\<tturnstile> cd \<leadsto>\<^sub>a) \<Sigma> \<Sigma>'"
proof
  assume "\<exists>n. iter_evala cd n \<Sigma> = Some \<Sigma>'"
  then obtain n where "iter_evala cd n \<Sigma> = Some \<Sigma>'" by fastforce
  thus "iter (\<tturnstile> cd \<leadsto>\<^sub>a) \<Sigma> \<Sigma>'" 
  proof (induction n arbitrary: \<Sigma>)
    case (Suc n)
    thus ?case by (cases "cd \<tturnstile>\<^sub>a \<Sigma>") (simp_all add: alg_evala_equiv)
  qed simp_all
next
  show "iter (\<tturnstile> cd \<leadsto>\<^sub>a) \<Sigma> \<Sigma>' \<Longrightarrow> \<exists>n. iter_evala cd n \<Sigma> = Some \<Sigma>'" 
  proof (induction \<Sigma> \<Sigma>' rule: iter.induct)
    case (iter_refl \<Sigma>)
    have "iter_evala cd 0 \<Sigma> = Some \<Sigma>" by simp
    thus ?case by blast
  next
    case (iter_step \<Sigma> \<Sigma>' \<Sigma>'')
    then obtain n where "iter_evala cd n \<Sigma>' = Some \<Sigma>''" by fastforce
    moreover from iter_step have "cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>'" by (simp add: alg_evala_equiv)
    ultimately have "iter_evala cd (Suc n) \<Sigma> = Some \<Sigma>''" by simp
    thus ?case by blast
  qed
qed

theorem determinisma: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof -
  assume "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>'" 
  hence X: "cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>'" by (simp add: alg_evala_equiv)
  assume "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>''"
  hence "cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>''" by (simp add: alg_evala_equiv)
  with X show "\<Sigma>' = \<Sigma>''" by simp
qed

end