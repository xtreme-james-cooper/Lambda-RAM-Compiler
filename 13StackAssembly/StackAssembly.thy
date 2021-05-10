theory StackAssembly
  imports Main
begin

datatype memory = Hp | Env | Vals | Stk

datatype pseudoreg = Acc | Con nat
datatype pseudomem = Mem memory | MCon nat

datatype sassm_code = 
  BLookup nat
  | BApply
  | BReturn
  | BJump

  | SAPush memory pseudoreg
  | SAPop memory
  | SAMov pseudomem
  | SAGet memory
  | SASub nat

datatype sassm_state = 
  SAS "memory \<Rightarrow> nat \<Rightarrow> nat" "memory \<Rightarrow> nat" nat nat

fun sassm_lookup :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<rightharpoonup> nat" where
  "sassm_lookup h 0 x = None"
| "sassm_lookup h (Suc 0) x = None"
| "sassm_lookup h (Suc (Suc p)) 0 = Some (h p)"
| "sassm_lookup h (Suc (Suc p)) (Suc x) = sassm_lookup h (h (Suc p)) x"

primrec get_val :: "pseudoreg \<Rightarrow> nat \<Rightarrow> nat" where
  "get_val Acc x = x"
| "get_val (Con k) x = k"

primrec get_mval :: "pseudomem \<Rightarrow> (memory \<Rightarrow> nat) \<Rightarrow> nat" where
  "get_mval (Mem m) x = x m"
| "get_mval (MCon k) x = k"

fun mem_upd :: "(memory \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> memory \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> memory \<Rightarrow> nat \<Rightarrow> nat" where
  "mem_upd mem m mp k m' x = (if m = m' \<and> mp = x then k else mem m' x)"

inductive evalsa :: "sassm_code list \<Rightarrow> sassm_state \<Rightarrow> sassm_state \<Rightarrow> bool" 
    (infix "\<tturnstile> _ \<leadsto>\<^sub>s\<^sub>a" 50) where
  evsa_push [simp]: "cd ! pc = SAPush m r \<Longrightarrow>
    cd \<tturnstile> SAS mem ps acc (Suc pc) \<leadsto>\<^sub>s\<^sub>a
      SAS (mem_upd mem m (ps m) (get_val r acc)) (ps(m := Suc (ps m))) acc pc"
| evsa_pop [simp]: "cd ! pc = SAPop m \<Longrightarrow> ps m = Suc p \<Longrightarrow>
    cd \<tturnstile> SAS mem ps acc (Suc pc) \<leadsto>\<^sub>s\<^sub>a SAS mem (ps(m := p)) (mem m p) pc"
| evsa_mov [simp]: "cd ! pc = SAMov m \<Longrightarrow>
    cd \<tturnstile> SAS mem ps acc (Suc pc) \<leadsto>\<^sub>s\<^sub>a SAS mem ps (get_mval m ps) pc"
| evsa_get [simp]: "cd ! pc = SAGet m \<Longrightarrow>
    cd \<tturnstile> SAS mem ps acc (Suc pc) \<leadsto>\<^sub>s\<^sub>a SAS mem ps (mem m acc) pc"
| evsa_sub [simp]: "cd ! pc = SASub k \<Longrightarrow>
    cd \<tturnstile> SAS mem ps acc (Suc pc) \<leadsto>\<^sub>s\<^sub>a SAS mem ps (acc - k) pc"

theorem determinismu: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>s\<^sub>a \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>s\<^sub>a \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction cd \<Sigma> \<Sigma>' rule: evalsa.induct)
  case (evsa_push cd pc m r mem ps acc)
  from evsa_push(2, 1) show ?case 
    by (induction cd "SAS mem ps acc (Suc pc)" \<Sigma>'' rule: evalsa.induct) simp_all
next
  case (evsa_pop cd pc m ps p mem acc)
  from evsa_pop(3, 1, 2) show ?case 
    by (induction cd "SAS mem ps acc (Suc pc)" \<Sigma>'' rule: evalsa.induct) simp_all
next
  case (evsa_mov cd pc m mem ps acc)
  from evsa_mov(2, 1) show ?case 
    by (induction cd "SAS mem ps acc (Suc pc)" \<Sigma>'' rule: evalsa.induct) simp_all
next
  case (evsa_get cd pc m mem ps acc)
  from evsa_get(2, 1) show ?case 
    by (induction cd "SAS mem ps acc (Suc pc)" \<Sigma>'' rule: evalsa.induct) simp_all
next
  case (evsa_sub cd pc k mem ps acc)
  from evsa_sub(2, 1) show ?case 
    by (induction cd "SAS mem ps acc (Suc pc)" \<Sigma>'' rule: evalsa.induct) simp_all
qed

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

end