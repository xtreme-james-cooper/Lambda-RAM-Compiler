theory AssemblyCode
  imports Main
begin

datatype register = Hp | Env | Vals | Stk | Acc | Acc2

datatype pseudoreg = Reg register | PC | Con nat

datatype assm_code = 
  AMov register pseudoreg
  | AGet register register register
  | APut register register pseudoreg
  | ASub register nat
  | AAdd register nat
  | AJump

datatype assm_state = 
  AS "register \<Rightarrow> nat \<Rightarrow> nat" "register \<Rightarrow> nat" nat

fun mem_upd :: "(register \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> register \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> register \<Rightarrow> nat \<Rightarrow> nat" where
  "mem_upd mem m mp k m' x = (if m = m' \<and> mp = x then k else mem m' x)"

fun evala :: "assm_code list \<Rightarrow> assm_state \<rightharpoonup> assm_state" (infix "\<tturnstile>\<^sub>a" 50) where
  "cd \<tturnstile>\<^sub>a AS mem ps 0 = None"
| "cd \<tturnstile>\<^sub>a AS mem ps (Suc pc) = (case cd ! pc of
      AMov r' (Reg r) \<Rightarrow> Some (AS mem (ps(r' := ps r)) pc)
    | AMov r' PC \<Rightarrow> Some (AS mem (ps(r' := pc)) pc)
    | AMov r' (Con k) \<Rightarrow> Some (AS mem (ps(r' := k)) pc)
    | AGet r' m r \<Rightarrow> Some (AS mem (ps(r' := mem m (ps r))) pc)
    | APut m r' (Reg r) \<Rightarrow> Some (AS (mem_upd mem m (ps r') (ps r)) ps pc)
    | APut m r' PC \<Rightarrow> Some (AS (mem_upd mem m (ps r') pc) ps pc)
    | APut m r' (Con k) \<Rightarrow> Some (AS (mem_upd mem m (ps r') k) ps pc)
    | ASub r k \<Rightarrow> Some (AS mem (ps(r := ps r - k)) pc)
    | AAdd r k \<Rightarrow> Some (AS mem (ps(r := ps r + k)) pc)
    | AJump \<Rightarrow> Some (AS mem (ps(Acc := 0)) (ps Acc)))"

primrec iter_evala :: "assm_code list \<Rightarrow> nat \<Rightarrow> assm_state \<rightharpoonup> assm_state" where
  "iter_evala cd 0 \<Sigma> = Some \<Sigma>"
| "iter_evala cd (Suc x) \<Sigma> = Option.bind (cd \<tturnstile>\<^sub>a \<Sigma>) (iter_evala cd x)"

lemma [simp]: "mem_upd (case_register h e vs sh a b) Hp x y = case_register (h(x := y)) e vs sh a b"
  by (rule+) (simp split: register.splits)

lemma [simp]: "mem_upd (case_register h e vs sh a b) Env x y = 
    case_register h (e(x := y)) vs sh a b"
  by (rule+) (simp split: register.splits)

lemma [simp]: "mem_upd (case_register h e vs sh a b) Vals x y = 
    case_register h e (vs(x := y)) sh a b"
  by (rule+) (simp split: register.splits)

lemma [simp]: "mem_upd (case_register h e vs sh a b) Stk x y = 
    case_register h e vs (sh(x := y)) a b"
  by (rule+) (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp a b)(Hp := x) = case_register x ep vp sp a b"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp a b)(Env := x) = case_register hp x vp sp a b"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp a b)(Vals := x) = case_register hp ep x sp a b"
  by rule (simp split: register.splits)

lemma [simp]: "(case_register hp ep vp sp a b)(Stk := x) = case_register hp ep vp x a b"
  by rule (simp split: register.splits)

lemma iter_evala_combine [simp]: "iter_evala cd n \<Sigma> = Some \<Sigma>' \<Longrightarrow> 
  iter_evala cd m \<Sigma>' = Some \<Sigma>'' \<Longrightarrow> iter_evala cd (n + m) \<Sigma> = Some \<Sigma>''"
proof (induction n arbitrary: \<Sigma>)
  case (Suc n)
  then show ?case by (cases "cd \<tturnstile>\<^sub>a \<Sigma>") simp_all
qed simp_all

end