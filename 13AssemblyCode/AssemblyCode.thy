theory AssemblyCode
  imports "../00Utils/Iteration" "../00Utils/Environment"
begin

datatype register = Hp | Env | Vals | Stk | Acc

datatype pseudoreg = Reg register | PC | Con nat

datatype assm = 
  AMov pseudoreg
  | AGet register register pseudoreg
  | APut register register pseudoreg
  | ASub register nat pseudoreg
  | AAdd register nat pseudoreg
  | AJmp

datatype assm_state = 
  AS "register \<Rightarrow> nat \<Rightarrow> nat" "register \<Rightarrow> nat" pseudoreg nat

fun mem_upd :: "(register \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> register \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> register \<Rightarrow> nat \<Rightarrow> nat" where
  "mem_upd mem m mp k m' x = (if m = m' \<and> mp = x then k else mem m' x)"

fun alg_evala :: "assm list \<Rightarrow> assm_state \<rightharpoonup> assm_state" (infix "\<tturnstile>\<^sub>a" 50) where
  "cd \<tturnstile>\<^sub>a AS mem ps act 0 = None"
| "cd \<tturnstile>\<^sub>a AS mem ps act (Suc pc) = (case lookup cd pc of
      Some (AMov (Reg Acc)) \<Rightarrow> None
    | Some (AMov (Reg r)) \<Rightarrow> Some (AS mem (ps(Acc := ps r)) (Reg r) pc)
    | Some (AMov PC) \<Rightarrow> Some (AS mem (ps(Acc := pc)) PC pc)
    | Some (AMov (Con k)) \<Rightarrow> Some (AS mem (ps(Acc := k)) (Con 0) pc)
    | Some (AGet Acc r t) \<Rightarrow> None
    | Some (AGet m Acc t) \<Rightarrow> 
        if act = Reg m then Some (AS mem (ps(Acc := mem m (ps Acc))) t pc) else None
    | Some (AGet m r t) \<Rightarrow> 
        if m = r then Some (AS mem (ps(Acc := mem m (ps m))) t pc) else None
    | Some (APut m r' (Reg r)) \<Rightarrow> Some (AS (mem_upd mem m (ps r') (ps r)) ps act pc)
    | Some (APut m r' PC) \<Rightarrow> Some (AS (mem_upd mem m (ps r') pc) ps act pc)
    | Some (APut m r' (Con k)) \<Rightarrow> Some (AS (mem_upd mem m (ps r') k) ps act pc)
    | Some (ASub Acc k t) \<Rightarrow> 
        if act = t then Some (AS mem (ps(Acc := ps Acc - k)) act pc) else None
    | Some (ASub r k t) \<Rightarrow> 
        if t = Reg r then Some (AS mem (ps(r := ps r - k)) act pc) else None
    | Some (AAdd Acc k t) \<Rightarrow>
        if act = t then Some (AS mem (ps(Acc := ps Acc + k)) act pc) else None
    | Some (AAdd r k t) \<Rightarrow>
        if t = Reg r then Some (AS mem (ps(r := ps r + k)) act pc) else None
    | Some AJmp \<Rightarrow> 
        if act = PC then Some (AS mem (ps(Acc := 0)) (Con 0) (ps Acc)) else None
    | None \<Rightarrow> None)"

primrec iter_evala :: "assm list \<Rightarrow> nat \<Rightarrow> assm_state \<rightharpoonup> assm_state" where
  "iter_evala cd 0 \<Sigma> = Some \<Sigma>"
| "iter_evala cd (Suc x) \<Sigma> = Option.bind (cd \<tturnstile>\<^sub>a \<Sigma>) (iter_evala cd x)"

inductive evala :: "assm list \<Rightarrow> assm_state \<Rightarrow> assm_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>a" 50) where
  eva_movr [simp]: "lookup cd pc = Some (AMov (Reg r)) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := ps r)) (Reg r) pc"
| eva_movp [simp]: "lookup cd pc = Some (AMov PC) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := pc)) PC pc"
| eva_movk [simp]: "lookup cd pc = Some (AMov (Con k)) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := k)) (Con 0) pc"
| eva_geta [simp]: "lookup cd pc = Some (AGet m Acc t) \<Longrightarrow> m \<noteq> Acc \<Longrightarrow> 
    cd \<tturnstile> AS mem ps (Reg m) (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := mem m (ps Acc))) t pc"
| eva_get [simp]: "lookup cd pc = Some (AGet r r t) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow> 
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := mem r (ps r))) t pc"
| eva_putr [simp]: "lookup cd pc = Some (APut m r' (Reg r)) \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem m (ps r') (ps r)) ps act pc"
| eva_putp [simp]: "lookup cd pc = Some (APut m r' PC) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem m (ps r') pc) ps act pc"
| eva_putk [simp]: "lookup cd pc = Some (APut m r' (Con k)) \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem m (ps r') k) ps act pc"
| eva_suba [simp]: "lookup cd pc = Some (ASub Acc k act) \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := ps Acc - k)) act pc"
| eva_sub [simp]: "lookup cd pc = Some (ASub r k (Reg r)) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(r := ps r - k)) act pc"
| eva_adda [simp]: "lookup cd pc = Some (AAdd Acc k act) \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := ps Acc + k)) act pc"
| eva_add [simp]: "lookup cd pc = Some (AAdd r k (Reg r)) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(r := ps r + k)) act pc"
| eva_jmp [simp]: "lookup cd pc = Some AJmp \<Longrightarrow> 
    cd \<tturnstile> AS mem ps PC (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := 0)) (Con 0) (ps Acc)"

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

lemma [simp]: "(case_register hp ep vp sp a)(Acc := x) = case_register hp ep vp sp x"
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
    by (induction \<Sigma> rule: alg_evala.induct) 
       (auto split: assm.splits pseudoreg.splits register.splits if_splits option.splits)
  show "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>' \<Longrightarrow> cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>'" 
    by (induction cd \<Sigma> \<Sigma>' rule: evala.induct) (simp_all split: register.splits)
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