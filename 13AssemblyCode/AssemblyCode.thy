theory AssemblyCode
  imports Main
begin

datatype memory = Hp | Env | Vals | Stk

datatype pseudoreg = Acc | Acc2 | Con nat
datatype pseudomem = Mem memory | PC | MCon nat

datatype assm_code = 
  APush memory pseudoreg
  | APop memory
  | AMov pseudomem
  | AGet memory
  | ASub nat
  | AAdd nat
  | AJump
  | ABackup
  | AUnbackup

datatype assm_state = 
  AS "memory \<Rightarrow> nat \<Rightarrow> nat" "memory \<Rightarrow> nat" nat nat nat

primrec get_val :: "pseudoreg \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "get_val Acc x y = x"
| "get_val Acc2 x y = y"
| "get_val (Con k) x y = k"

primrec get_mval :: "pseudomem \<Rightarrow> (memory \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "get_mval (Mem m) x y = x m"
| "get_mval PC x y = y"
| "get_mval (MCon k) x y = k"

fun mem_upd :: "(memory \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> memory \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memory \<Rightarrow> nat \<Rightarrow> nat" where
  "mem_upd mem m mp k m' x = (if m = m' \<and> mp = x then k else mem m' x)"

fun evala :: "assm_code list \<Rightarrow> assm_state \<rightharpoonup> assm_state" (infix "\<tturnstile>\<^sub>a" 50) where
  "cd \<tturnstile>\<^sub>a AS mem ps acc acc2 0 = None"
| "cd \<tturnstile>\<^sub>a AS mem ps acc acc2 (Suc pc) = (case cd ! pc of
      APush m r \<Rightarrow> 
        Some (AS (mem_upd mem m (ps m) (get_val r acc pc)) (ps(m := Suc (ps m))) acc acc2 pc)
    | APop m \<Rightarrow> (case ps m of
          Suc p \<Rightarrow> Some (AS mem (ps(m := p)) (mem m p) acc2 pc)
        | 0 \<Rightarrow> None)
    | AMov m \<Rightarrow> Some (AS mem ps (get_mval m ps pc) acc2 pc)
    | AGet m \<Rightarrow> Some (AS mem ps (mem m acc) acc2 pc)
    | ASub k \<Rightarrow> Some (AS mem ps (acc - k) acc2 pc)
    | AAdd k \<Rightarrow> Some (AS mem ps (acc + k) acc2 pc)
    | AJump \<Rightarrow> Some (AS mem ps 0 0 acc)
    | ABackup \<Rightarrow> Some (AS mem ps acc acc pc)
    | AUnbackup \<Rightarrow> Some (AS mem ps acc2 acc2 pc))"

primrec iter_evala :: "assm_code list \<Rightarrow> nat \<Rightarrow> assm_state \<rightharpoonup> assm_state" where
  "iter_evala cd 0 \<Sigma> = Some \<Sigma>"
| "iter_evala cd (Suc x) \<Sigma> = Option.bind (cd \<tturnstile>\<^sub>a \<Sigma>) (iter_evala cd x)"

lemma [simp]: "mem_upd (case_memory h e vs sh) Hp x y = case_memory (h(x := y)) e vs sh"
  by (rule+) (simp split: memory.splits)

lemma [simp]: "mem_upd (case_memory h e vs sh) Env x y = case_memory h (e(x := y)) vs sh"
  by (rule+) (simp split: memory.splits)

lemma [simp]: "mem_upd (case_memory h e vs sh) Vals x y = case_memory h e (vs(x := y)) sh"
  by (rule+) (simp split: memory.splits)

lemma [simp]: "mem_upd (case_memory h e vs sh) Stk x y = case_memory h e vs (sh(x := y))"
  by (rule+) (simp split: memory.splits)

lemma [simp]: "(case_memory hp ep vp sp)(Hp := x) = case_memory x ep vp sp"
  by rule (simp split: memory.splits)

lemma [simp]: "(case_memory hp ep vp sp)(Env := x) = case_memory hp x vp sp"
  by rule (simp split: memory.splits)

lemma [simp]: "(case_memory hp ep vp sp)(Vals := x) = case_memory hp ep x sp"
  by rule (simp split: memory.splits)

lemma [simp]: "(case_memory hp ep vp sp)(Stk := x) = case_memory hp ep vp x"
  by rule (simp split: memory.splits)

lemma iter_evala_combine [simp]: "iter_evala cd n \<Sigma> = Some \<Sigma>' \<Longrightarrow> 
  iter_evala cd m \<Sigma>' = Some \<Sigma>'' \<Longrightarrow> iter_evala cd (n + m) \<Sigma> = Some \<Sigma>''"
proof (induction n arbitrary: \<Sigma>)
  case (Suc n)
  then show ?case by (cases "cd \<tturnstile>\<^sub>a \<Sigma>") simp_all
qed simp_all

end