theory StackAssembly
  imports Main
begin

datatype memory = Hp | Env | Vals | Stk

datatype pseudoreg = Acc | Con nat

datatype sassm_code = 
  BLookup nat
  | BApply
  | BReturn
  | BJump

  | SAPush memory pseudoreg
  | SAPop memory
  | SAMov memory
  | SAGet memory

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
    cd \<tturnstile> SAS mem ps acc (Suc pc) \<leadsto>\<^sub>s\<^sub>a SAS mem ps (ps m) pc"
| evsa_get [simp]: "cd ! pc = SAGet m \<Longrightarrow>
    cd \<tturnstile> SAS mem ps acc (Suc pc) \<leadsto>\<^sub>s\<^sub>a SAS mem ps (mem m acc) pc"

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
qed

end