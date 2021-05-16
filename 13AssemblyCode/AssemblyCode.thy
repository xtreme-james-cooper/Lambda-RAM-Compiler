theory AssemblyCode
  imports "../00Utils/Iteration"
begin

datatype register = Hp | Env | Vals | Stk | Acc

datatype pseudoreg = Reg register | PC | Con nat

datatype assm = 
  AMov register pseudoreg
  | AGet register register register
  | APut register register pseudoreg
  | ASub register nat
  | AAdd register nat
  | AJmp

datatype assm_state = 
  AS "register \<Rightarrow> nat \<Rightarrow> nat" "register \<Rightarrow> nat" nat

fun mem_upd :: "(register \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> register \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> register \<Rightarrow> nat \<Rightarrow> nat" where
  "mem_upd mem m mp k m' x = (if m = m' \<and> mp = x then k else mem m' x)"

fun alg_evala :: "assm list \<Rightarrow> assm_state \<rightharpoonup> assm_state" (infix "\<tturnstile>\<^sub>a" 50) where
  "cd \<tturnstile>\<^sub>a AS mem ps 0 = None"
| "cd \<tturnstile>\<^sub>a AS mem ps (Suc pc) = Some  (case cd ! pc of
      AMov r' (Reg r) \<Rightarrow> AS mem (ps(r' := ps r)) pc
    | AMov r' PC \<Rightarrow> AS mem (ps(r' := pc)) pc
    | AMov r' (Con k) \<Rightarrow> AS mem (ps(r' := k)) pc
    | AGet r' m r \<Rightarrow> AS mem (ps(r' := mem m (ps r))) pc
    | APut m r' (Reg r) \<Rightarrow> AS (mem_upd mem m (ps r') (ps r)) ps pc
    | APut m r' PC \<Rightarrow> AS (mem_upd mem m (ps r') pc) ps pc
    | APut m r' (Con k) \<Rightarrow> AS (mem_upd mem m (ps r') k) ps pc
    | ASub r k \<Rightarrow> AS mem (ps(r := ps r - k)) pc
    | AAdd r k \<Rightarrow> AS mem (ps(r := ps r + k)) pc
    | AJmp \<Rightarrow> AS mem (ps(Acc := 0)) (ps Acc))"

inductive evala :: "assm list \<Rightarrow> assm_state \<Rightarrow> assm_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>a" 50) where
  eva_movr [simp]: "cd ! pc = AMov r' (Reg r) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps (Suc pc) \<leadsto>\<^sub>a AS mem (ps(r' := ps r)) pc"
| eva_movp [simp]: "cd ! pc = AMov r' PC \<Longrightarrow> 
    cd \<tturnstile> AS mem ps (Suc pc) \<leadsto>\<^sub>a AS mem (ps(r' := pc)) pc"
| eva_movk [simp]: "cd ! pc = AMov r' (Con k) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps (Suc pc) \<leadsto>\<^sub>a AS mem (ps(r' := k)) pc"
| eva_get [simp]: "cd ! pc = AGet r' m r \<Longrightarrow> 
    cd \<tturnstile> AS mem ps (Suc pc) \<leadsto>\<^sub>a AS mem (ps(r' := mem m (ps r))) pc"
| eva_putr [simp]: "cd ! pc = APut m r' (Reg r) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem m (ps r') (ps r)) ps pc"
| eva_putp [simp]: "cd ! pc = APut m r' PC \<Longrightarrow> 
    cd \<tturnstile> AS mem ps (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem m (ps r') pc) ps pc"
| eva_putk [simp]: "cd ! pc = APut m r' (Con k) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem m (ps r') k) ps pc"
| eva_sub [simp]: "cd ! pc = ASub r k \<Longrightarrow> cd \<tturnstile> AS mem ps (Suc pc) \<leadsto>\<^sub>a AS mem (ps(r := ps r - k)) pc"
| eva_add [simp]: "cd ! pc = AAdd r k \<Longrightarrow> cd \<tturnstile> AS mem ps (Suc pc) \<leadsto>\<^sub>a AS mem (ps(r := ps r + k)) pc"
| eva_jmp [simp]: "cd ! pc = AJmp \<Longrightarrow> cd \<tturnstile> AS mem ps (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := 0)) (ps Acc)"

primrec iter_evala :: "assm list \<Rightarrow> nat \<Rightarrow> assm_state \<rightharpoonup> assm_state" where
  "iter_evala cd 0 \<Sigma> = Some \<Sigma>"
| "iter_evala cd (Suc x) \<Sigma> = Option.bind (cd \<tturnstile>\<^sub>a \<Sigma>) (iter_evala cd x)"

lemma [simp]: "mem_upd (case_register h e vs sh a) Hp x y = case_register (h(x := y)) e vs sh a"
  by (rule+) (simp split: register.splits)

lemma [simp]: "mem_upd (case_register h e vs sh a) Env x y = case_register h (e(x := y)) vs sh a"
  by (rule+) (simp split: register.splits)

lemma [simp]: "mem_upd (case_register h e vs sh a) Vals x y = case_register h e (vs(x := y)) sh a"
  by (rule+) (simp split: register.splits)

lemma [simp]: "mem_upd (case_register h e vs sh a) Stk x y = case_register h e vs (sh(x := y)) a"
  by (rule+) (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp a)(Hp := x) = case_register x ep vp sp a"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp a)(Env := x) = case_register hp x vp sp a"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp a)(Vals := x) = case_register hp ep x sp a"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp a)(Stk := x) = case_register hp ep vp x a"
  by rule (simp split: register.splits)

lemma iter_evala_combine [simp]: "iter_evala cd n \<Sigma> = Some \<Sigma>' \<Longrightarrow> 
  iter_evala cd m \<Sigma>' = Some \<Sigma>'' \<Longrightarrow> iter_evala cd (n + m) \<Sigma> = Some \<Sigma>''"
proof (induction n arbitrary: \<Sigma>)
  case (Suc n)
  then show ?case by (cases "cd \<tturnstile>\<^sub>a \<Sigma>") simp_all
qed simp_all

lemma alg_evala_equiv: "cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>' = (cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>')"
proof
  show "cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>'"
    by (induction \<Sigma> rule: alg_evala.induct) (auto split: assm.splits pseudoreg.splits)
  show "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>' \<Longrightarrow> cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>'" by (induction cd \<Sigma> \<Sigma>' rule: evala.induct) simp_all
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

end