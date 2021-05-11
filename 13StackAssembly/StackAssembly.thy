theory StackAssembly
  imports Main
begin

datatype memory = Hp | Env | Vals | Stk

datatype pseudoreg = Acc | Acc2 | Con nat
datatype pseudomem = Mem memory | PC | MCon nat

datatype sassm_code = 
  BLookup nat
  | BReturn
  | BJump

  | SAPush memory pseudoreg
  | SAPop memory
  | SAMov pseudomem
  | SAGet memory
  | SASub nat
  | SAAdd nat
  | SAJump
  | SABackup
  | SAUnbackup

datatype sassm_state = 
  SAS "memory \<Rightarrow> nat \<Rightarrow> nat" "memory \<Rightarrow> nat" nat nat nat

fun sassm_lookup :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<rightharpoonup> nat" where
  "sassm_lookup h 0 x = None"
| "sassm_lookup h (Suc 0) x = None"
| "sassm_lookup h (Suc (Suc p)) 0 = Some (h p)"
| "sassm_lookup h (Suc (Suc p)) (Suc x) = sassm_lookup h (h (Suc p)) x"

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

fun evalsa :: "sassm_code list \<Rightarrow> sassm_state \<rightharpoonup> sassm_state" (infix "\<tturnstile>\<^sub>s\<^sub>a" 50) where
  "cd \<tturnstile>\<^sub>s\<^sub>a SAS mem ps acc acc2 0 = None"
| "cd \<tturnstile>\<^sub>s\<^sub>a SAS mem ps acc acc2 (Suc pc) = (case cd ! pc of
      SAPush m r \<Rightarrow> 
        Some (SAS (mem_upd mem m (ps m) (get_val r acc pc)) (ps(m := Suc (ps m))) acc acc2 pc)
    | SAPop m \<Rightarrow> (case ps m of
          Suc p \<Rightarrow> Some (SAS mem (ps(m := p)) (mem m p) acc2 pc)
        | 0 \<Rightarrow> None)
    | SAMov m \<Rightarrow> Some (SAS mem ps (get_mval m ps pc) acc2 pc)
    | SAGet m \<Rightarrow> Some (SAS mem ps (mem m acc) acc2 pc)
    | SASub k \<Rightarrow> Some (SAS mem ps (acc - k) acc2 pc)
    | SAAdd k \<Rightarrow> Some (SAS mem ps (acc + k) acc2 pc)
    | SAJump \<Rightarrow> Some (SAS mem ps 0 0 acc)
    | SABackup \<Rightarrow> Some (SAS mem ps acc acc pc)
    | SAUnbackup \<Rightarrow> Some (SAS mem ps acc2 acc2 pc))"

primrec iter_evalsa :: "sassm_code list \<Rightarrow> nat \<Rightarrow> sassm_state \<rightharpoonup> sassm_state" where
  "iter_evalsa cd 0 \<Sigma> = Some \<Sigma>"
| "iter_evalsa cd (Suc x) \<Sigma> = Option.bind (cd \<tturnstile>\<^sub>s\<^sub>a \<Sigma>) (iter_evalsa cd x)"

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

lemma [simp]: "iter_evalsa cd n \<Sigma> = Some \<Sigma>' \<Longrightarrow> iter_evalsa cd m \<Sigma>' = Some \<Sigma>'' \<Longrightarrow> 
  iter_evalsa cd (n + m) \<Sigma> = Some \<Sigma>''"
proof (induction n arbitrary: \<Sigma>)
  case (Suc n)
  then show ?case by (cases "cd \<tturnstile>\<^sub>s\<^sub>a \<Sigma>") simp_all
qed simp_all

end