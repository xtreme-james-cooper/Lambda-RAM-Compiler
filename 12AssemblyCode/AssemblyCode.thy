theory AssemblyCode
  imports "../00Utils/Iteration" "../00Utils/Environment"
begin

datatype register = Hp | Env | Vals | Stk | Acc

datatype move_src = Reg register | Con nat 

datatype assm = 
  AGet register
  | APut register move_src
  | ASub register nat
  | AAdd register nat
  | AJmp

datatype assm_state = 
  AS "register \<Rightarrow> nat \<Rightarrow> register \<times> nat" "register \<Rightarrow> nat" register nat

fun mem_upd :: "(register \<Rightarrow> nat \<Rightarrow> register \<times> nat) \<Rightarrow> register \<Rightarrow> nat \<Rightarrow> register \<times> nat \<Rightarrow> 
    register \<Rightarrow> nat \<Rightarrow> register \<times> nat" where
  "mem_upd mem m mp k m' x = (if m = m' \<and> mp = x then k else mem m' x)"

abbreviation reg_merge :: "register \<Rightarrow> register \<Rightarrow> register" where
  "reg_merge a b \<equiv> (if a = Acc then b else a)"

fun assm_step :: "(register \<Rightarrow> nat \<Rightarrow> register \<times> nat) \<Rightarrow> (register \<Rightarrow> nat) \<Rightarrow> register \<Rightarrow> nat \<Rightarrow> 
    assm \<rightharpoonup> assm_state" where
  "assm_step mem ps act pc (AGet r) = 
    (if r = Acc \<and> act = Acc then None
     else case mem (reg_merge r act) (ps r) of
       (t, b) \<Rightarrow> Some (AS mem (ps(Acc := b)) t pc))"
| "assm_step mem ps act pc (APut Acc (Reg r')) = 
    Some (AS mem (ps(Acc := ps r')) (reg_merge r' act) pc)"
| "assm_step mem ps act pc (APut Acc (Con k)) = Some (AS mem (ps(Acc := k)) Acc pc)"
| "assm_step mem ps act pc (APut r (Reg r')) = 
    Some (AS (mem_upd mem r (ps r) (reg_merge r' act, ps r')) ps act pc)"
| "assm_step mem ps act pc (APut r (Con k)) = 
    Some (AS (mem_upd mem r (ps r) (Acc, k)) ps act pc)"
| "assm_step mem ps act pc (ASub r k) = 
    (if ps r < k \<or> (r = Acc \<and> act = Acc) then None 
     else Some (AS mem (ps(r := ps r - k)) act pc))"
| "assm_step mem ps act pc (AAdd r k) = 
    (if r = Acc \<and> act = Acc then None 
     else Some (AS mem (ps(r := ps r + k)) act pc))"
| "assm_step mem ps act pc AJmp = 
    (if act = Acc then Some (AS mem (ps(Acc := 0)) Acc (ps Acc)) else None)"

fun alg_evala :: "assm list \<Rightarrow> assm_state \<rightharpoonup> assm_state" (infix "\<tturnstile>\<^sub>a" 50) where
  "cd \<tturnstile>\<^sub>a AS mem ps act pc = (case pc of
      0 \<Rightarrow> None
    | Suc pc \<Rightarrow> Option.bind (lookup cd pc) (assm_step mem ps act pc))"

primrec iter_evala :: "assm list \<Rightarrow> nat \<Rightarrow> assm_state \<rightharpoonup> assm_state" where
  "iter_evala cd 0 \<Sigma> = Some \<Sigma>"
| "iter_evala cd (Suc x) \<Sigma> = Option.bind (cd \<tturnstile>\<^sub>a \<Sigma>) (iter_evala cd x)"

inductive evala :: "assm list \<Rightarrow> assm_state \<Rightarrow> assm_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>a" 50) where
  eva_movr [simp]: "lookup cd pc = Some (APut Acc (Reg r)) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := ps r)) r pc"
| eva_mova [simp]: "lookup cd pc = Some (APut Acc (Reg Acc)) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem ps act pc"
| eva_movk [simp]: "lookup cd pc = Some (APut Acc (Con k)) \<Longrightarrow> 
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := k)) Acc pc"
| eva_get [simp]: "lookup cd pc = Some (AGet r) \<Longrightarrow> mem r (ps r) = (t, b) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := b)) t pc"
| eva_geta [simp]: "lookup cd pc = Some (AGet Acc) \<Longrightarrow> mem act (ps Acc) = (t, b) \<Longrightarrow> act \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := b)) t pc"
| eva_putr [simp]: "lookup cd pc = Some (APut r (Reg r')) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow> r' \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem r (ps r) (r', ps r')) ps act pc"
| eva_puta [simp]: "lookup cd pc = Some (APut r (Reg Acc)) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem r (ps r) (act, ps Acc)) ps act pc"
| eva_putk [simp]: "lookup cd pc = Some (APut r (Con k)) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS (mem_upd mem r (ps r) (Acc, k)) ps act pc"
| eva_suba [simp]: "lookup cd pc = Some (ASub Acc k) \<Longrightarrow> ps Acc \<ge> k \<Longrightarrow> act \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := ps Acc - k)) act pc"
| eva_sub [simp]: "lookup cd pc = Some (ASub r k) \<Longrightarrow> ps r \<ge> k \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(r := ps r - k)) act pc"
| eva_add [simp]: "lookup cd pc = Some (AAdd r k) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(r := ps r + k)) act pc"
| eva_adda [simp]: "lookup cd pc = Some (AAdd Acc k) \<Longrightarrow> act \<noteq> Acc \<Longrightarrow>
    cd \<tturnstile> AS mem ps act (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := ps Acc + k)) act pc"
| eva_jmp [simp]: "lookup cd pc = Some AJmp \<Longrightarrow> 
    cd \<tturnstile> AS mem ps Acc (Suc pc) \<leadsto>\<^sub>a AS mem (ps(Acc := 0)) Acc (ps Acc)"

lemma [simp]: "mem_upd (case_register h e vs sh a) Hp x y = case_register (h(x := y)) e vs sh a"
proof (rule, rule)
  fix m n
  show "mem_upd (case_register h e vs sh a) Hp x y m n = case_register (h(x := y)) e vs sh a m n"
    by (induction m) (simp_all split: register.splits)
qed

lemma [simp]: "mem_upd (case_register h e vs sh a) Env x y = case_register h (e(x := y)) vs sh a"
proof (rule, rule)
  fix m n
  show "mem_upd (case_register h e vs sh a) Env x y m n = case_register h (e(x := y)) vs sh a m n"
    by (induction m) (simp_all split: register.splits)
qed

lemma [simp]: "mem_upd (case_register h e vs sh a) Vals x y = case_register h e (vs(x := y)) sh a"
proof (rule, rule)
  fix m n
  show "mem_upd (case_register h e vs sh a) Vals x y m n = case_register h e (vs(x := y)) sh a m n"
    by (induction m) (simp_all split: register.splits)
qed

lemma [simp]: "mem_upd (case_register h e vs sh a) Stk x y = case_register h e vs (sh(x := y)) a"
proof (rule, rule)
  fix m n
  show "mem_upd (case_register h e vs sh a) Stk x y m n = case_register h e vs (sh(x := y)) a m n"
    by (induction m) (simp_all split: register.splits)
qed

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
  proof (induction mem ps act pc op rule: assm_step.induct)
    case (6 mem ps act pc r k)
    then show ?case by (cases r) (auto split: if_splits)
  next
    case (7 mem ps act pc r k)
    then show ?case by (cases r) (auto split: if_splits)
  qed (auto split: if_splits prod.splits option.splits)
qed simp_all

lemma alg_evala_equiv: "cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>' = (cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>')"
proof
  show "cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>'"
    by (induction \<Sigma>) (auto simp add: assm_step_equiv split: nat.splits)
  show "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>' \<Longrightarrow> cd \<tturnstile>\<^sub>a \<Sigma> = Some \<Sigma>'" 
  proof (induction cd \<Sigma> \<Sigma>' rule: evala.induct)
    case (eva_putr cd pc r r' mem ps act)
    thus ?case by (induction r) simp_all
  next
    case (eva_puta cd pc r mem ps act)
    thus ?case by (induction r) simp_all
  next
    case (eva_putk cd pc r k mem ps act)
    thus ?case by (induction r) simp_all
  qed simp_all
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