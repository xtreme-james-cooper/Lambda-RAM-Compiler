theory AssemblyCode
  imports "../00Utils/Iteration" "../00Utils/Environment"
begin

datatype register = Hp | Env | Vals | Stk

datatype pseudoreg = Reg register | PC nat | Con nat | Acc pseudoreg

datatype assm = 
  AMov pseudoreg
  | AGet pseudoreg
  | APut register pseudoreg
  | ASub pseudoreg nat
  | AAdd pseudoreg nat
  | AJmp

datatype assm_state = 
  AS "register \<Rightarrow> nat \<Rightarrow> register option \<times> nat" "register \<Rightarrow> nat" nat "register option" nat

fun mem_upd :: "(register \<Rightarrow> nat \<Rightarrow> register option \<times> nat) \<Rightarrow> register \<Rightarrow> nat \<Rightarrow> 
    register option \<times> nat \<Rightarrow> register \<Rightarrow> nat \<Rightarrow> register option \<times> nat" where
  "mem_upd mem m mp k m' x = (if m = m' \<and> mp = x then k else mem m' x)"

fun match_regs :: "register option \<Rightarrow> pseudoreg \<Rightarrow> bool" where
  "match_regs (Some r) (Reg r') = (r = r')"
| "match_regs (Some r) _ = False"
| "match_regs None (Reg r) = False"
| "match_regs None _ = True"

fun assm_step :: "(register \<Rightarrow> nat \<Rightarrow> register option \<times> nat) \<Rightarrow> (register \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> 
    register option \<Rightarrow> nat \<Rightarrow> assm \<rightharpoonup> assm_state" where
  "assm_step mem ps a act pc (AMov (Reg r)) = Some (AS mem ps (ps r) (Some r) pc)"
| "assm_step mem ps a act pc (AMov (PC _)) = Some (AS mem ps pc None pc)"
| "assm_step mem ps a act pc (AMov (Con k)) = Some (AS mem ps k None pc)"
| "assm_step mem ps a act pc (AMov (Acc _)) = None"
| "assm_step mem ps a act pc (AGet (Reg r)) = (case mem r (ps r) of
      (t, b) \<Rightarrow> Some (AS mem ps b t pc))"
| "assm_step mem ps a act pc (AGet (PC _)) = None"
| "assm_step mem ps a act pc (AGet (Con k)) = None"
| "assm_step mem ps a act pc (AGet (Acc (Reg r))) = (case mem r a of
      (t, b) \<Rightarrow> if act = Some r then Some (AS mem ps b t pc) else None)"
| "assm_step mem ps a act pc (AGet (Acc (PC _))) = None"
| "assm_step mem ps a act pc (AGet (Acc (Con k))) = None"
| "assm_step mem ps a act pc (AGet (Acc (Acc r))) = None"
| "assm_step mem ps a act pc (APut r (Reg r')) = 
    Some (AS (mem_upd mem r (ps r) (Some r', ps r')) ps a act pc)"
| "assm_step mem ps a act pc (APut r (PC k)) = 
    Some (AS (mem_upd mem r (ps r) (None, k)) ps a act pc)"
| "assm_step mem ps a act pc (APut r (Con k)) = 
    Some (AS (mem_upd mem r (ps r) (None, k)) ps a act pc)"
| "assm_step mem ps a act pc (APut r (Acc t)) = 
    Some (AS (mem_upd mem r (ps r) (act, a)) ps a act pc)" 
| "assm_step mem ps a act pc (ASub (Reg r) k) = 
    (if ps r \<ge> k then Some (AS mem (ps(r := ps r - k)) a act pc) else None)"
| "assm_step mem ps a act pc (ASub (PC _) k) = None"
| "assm_step mem ps a act pc (ASub (Con m) k) = None"
| "assm_step mem ps a act pc (ASub (Acc t) k) =
    (if match_regs act t \<and> a \<ge> k then Some (AS mem ps (a - k) act pc) else None)"
| "assm_step mem ps a act pc (AAdd (Reg r) k) = Some (AS mem (ps(r := ps r + k)) a act pc)"
| "assm_step mem ps a act pc (AAdd (PC _) k) = None"
| "assm_step mem ps a act pc (AAdd (Con m) k) = None"
| "assm_step mem ps a act pc (AAdd (Acc t) k) =
    (if match_regs act t then Some (AS mem ps (a + k) act pc) else None)"
| "assm_step mem ps a act pc AJmp = 
    (if act = None then Some (AS mem ps 0 None a) else None)"

fun alg_evala :: "assm list \<Rightarrow> assm_state \<rightharpoonup> assm_state" (infix "\<tturnstile>\<^sub>a" 50) where
  "cd \<tturnstile>\<^sub>a AS mem ps a act pc = (case pc of
      0 \<Rightarrow> None
    | Suc pc \<Rightarrow> Option.bind (lookup cd pc) (assm_step mem ps a act pc))"

primrec iter_evala :: "assm list \<Rightarrow> nat \<Rightarrow> assm_state \<rightharpoonup> assm_state" where
  "iter_evala cd 0 \<Sigma> = Some \<Sigma>"
| "iter_evala cd (Suc x) \<Sigma> = Option.bind (cd \<tturnstile>\<^sub>a \<Sigma>) (iter_evala cd x)"

inductive evala :: "assm list \<Rightarrow> assm_state \<Rightarrow> assm_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>a" 50) where
  eva_movr [simp]: "lookup cd pc = Some (AMov (Reg r)) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a AS mem ps (ps r) (Some r) pc"
| eva_movp [simp]: "lookup cd pc = Some (AMov (PC _)) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a AS mem ps pc None pc"
| eva_movk [simp]: "lookup cd pc = Some (AMov (Con k)) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a AS mem ps k None pc"
| eva_get [simp]: "lookup cd pc = Some (AGet (Reg r)) \<Longrightarrow> mem r (ps r) = (t, b) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a AS mem ps b t pc"
| eva_geta [simp]: "lookup cd pc = Some (AGet (Acc (Reg m))) \<Longrightarrow> mem m a = (t, b) \<Longrightarrow>
    cd \<tturnstile> AS mem ps a (Some m) (Suc pc) \<leadsto>\<^sub>a AS mem ps b t pc"
| eva_putr [simp]: "lookup cd pc = Some (APut r (Reg r')) \<Longrightarrow>
    cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem r (ps r) (Some r', ps r')) ps a act pc"
| eva_putk [simp]: "lookup cd pc = Some (APut r (Con k)) \<Longrightarrow>
    cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem r (ps r) (None, k)) ps a act pc"
| eva_putp [simp]: "lookup cd pc = Some (APut r (PC k)) \<Longrightarrow>
    cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem r (ps r) (None, k)) ps a act pc"
| eva_puta [simp]: "lookup cd pc = Some (APut r (Acc t)) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem r (ps r) (act, a)) ps a act pc"
| eva_suba [simp]: "lookup cd pc = Some (ASub (Acc p) k) \<Longrightarrow> a \<ge> k \<Longrightarrow> match_regs act p \<Longrightarrow>
    cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a AS mem ps (a - k) act pc"
| eva_sub [simp]: "lookup cd pc = Some (ASub (Reg r) k) \<Longrightarrow> ps r \<ge> k \<Longrightarrow>
    cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(r := ps r - k)) a act pc"
| eva_add [simp]: "lookup cd pc = Some (AAdd (Reg r) k) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(r := ps r + k)) a act pc"
| eva_adda [simp]: "lookup cd pc = Some (AAdd (Acc p) k) \<Longrightarrow> match_regs act p \<Longrightarrow>
    cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a AS mem ps (a + k) act pc"
| eva_jmp [simp]: "lookup cd pc = Some AJmp \<Longrightarrow> 
    cd \<tturnstile> AS mem ps a None (Suc pc) \<leadsto>\<^sub>a AS mem ps 0 None a"

lemma [simp]: "mem_upd (case_register h e vs sh) Hp x y = case_register (h(x := y)) e vs sh"
  by (rule+) (simp_all split: register.splits)

lemma [simp]: "mem_upd (case_register h e vs sh) Env x y = case_register h (e(x := y)) vs sh"
  by (rule+) (simp_all split: register.splits)

lemma [simp]: "mem_upd (case_register h e vs sh) Vals x y = case_register h e (vs(x := y)) sh"
  by (rule+) (simp_all split: register.splits)

lemma [simp]: "mem_upd (case_register h e vs sh) Stk x y = case_register h e vs (sh(x := y))"
  by (rule+) (simp_all split: register.splits)

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

lemma assm_step_equiv: "(Option.bind (lookup cd pc) (assm_step mem ps a act pc) = Some \<Sigma>) \<Longrightarrow>
  (cd \<tturnstile> AS mem ps a act (Suc pc) \<leadsto>\<^sub>a \<Sigma>)"
proof (cases "lookup cd pc")
  case (Some op)
  moreover assume "Option.bind (lookup cd pc) (assm_step mem ps a act pc) = Some \<Sigma>"
  ultimately show ?thesis 
    by (induction mem ps a act pc op rule: assm_step.induct) (auto split: if_splits prod.splits)
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