theory Disassemble
  imports MachineCode "../13AssemblyCode/AssemblyCode" "../00Utils/Utils" "../00Utils/Iteration"
begin

primrec register_map :: "register \<Rightarrow> reg" where
  "register_map Hp = R1"
| "register_map Env = R2"
| "register_map Vals = R3"
| "register_map Stk = R4"
| "register_map Acc = R5"

primrec register_offset :: "register \<Rightarrow> nat" where
  "register_offset Hp = 0"
| "register_offset Env = 1"
| "register_offset Vals = 2"
| "register_offset Stk = 3"
| "register_offset Acc = 0"

fun disassemble' :: "assm \<Rightarrow> mach" where
  "disassemble' (AMov (Reg r)) = MOV R5 (register_map r)"
| "disassemble' (AMov PC) = MVP R5"
| "disassemble' (AMov (Con k)) = LDI R5 k"
| "disassemble' (AGet r1 r2 t) = LOD R5 (register_map r2)"
| "disassemble' (APut r1 r2 (Reg r3)) = STO (register_map r1) (register_map r3)"
| "disassemble' (APut r1 r2 PC) = undefined"
| "disassemble' (APut r1 r2 (Con k)) = STI (register_map r1) k"
| "disassemble' (ASub Acc k t) = SUB R5 k"
| "disassemble' (ASub r k t) = SUB (register_map r) (4 * k)"
| "disassemble' (AAdd Acc k t) = ADD R5 k"
| "disassemble' (AAdd r k t) = ADD (register_map r) (4 * k)"
| "disassemble' AJmp = JMP R5"

definition disassemble :: "assm list \<Rightarrow> mach list" where
  "disassemble cd = map disassemble' cd"

fun unmap_mem' :: "nat \<Rightarrow> register \<times> nat" where
  "unmap_mem' 0 = (Hp, 0)" 
| "unmap_mem' (Suc 0) = (Env, 0)"
| "unmap_mem' (Suc (Suc 0)) = (Vals, 0)"
| "unmap_mem' (Suc (Suc (Suc 0))) = (Stk, 0)"
| "unmap_mem' (Suc (Suc (Suc (Suc x)))) = (case unmap_mem' x of (a, b) \<Rightarrow> (a, Suc b))"

definition unmap_mem :: "(register \<Rightarrow> nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "unmap_mem m x = (case unmap_mem' x of (r, p) \<Rightarrow> m r p)"

fun inv_register_map :: "(register \<Rightarrow> nat) \<Rightarrow> pseudoreg \<Rightarrow> reg \<Rightarrow> nat" where
  "inv_register_map rs t R1 = rs Hp * 4"
| "inv_register_map rs t R2 = rs Env * 4 + 1"
| "inv_register_map rs t R3 = rs Vals * 4 + 2"
| "inv_register_map rs t R4 = rs Stk * 4 + 3"
| "inv_register_map rs (Reg r) R5 = rs Acc * 4 + register_offset r"
| "inv_register_map rs PC R5 = rs Acc"
| "inv_register_map rs (Con k) R5 = rs Acc"

primrec disassemble_state :: "assm_state \<Rightarrow> mach_state" where
  "disassemble_state (AS mem rs t pc) = MS (inv_register_map rs t) (unmap_mem mem) pc"

lemma [simp]: "unmap_mem' (4 * k) = (Hp, k)"
  by (induction k) (simp_all add: numeral_def)

lemma [simp]: "unmap_mem' p = (a, b) \<Longrightarrow> unmap_mem' (4 + p) = (a, Suc b)"
  by (simp add: numeral_def)

lemma [simp]: "length (disassemble cd) = length cd"
  by (simp add: disassemble_def)

theorem completem [simp]: "cd\<^sub>m \<tturnstile> \<Sigma>\<^sub>m \<leadsto>\<^sub>m \<Sigma>\<^sub>m' \<Longrightarrow> 
  \<exists>cd\<^sub>a \<Sigma>\<^sub>a \<Sigma>\<^sub>a'. cd\<^sub>m = disassemble cd\<^sub>a \<and> disassemble_state \<Sigma>\<^sub>a = \<Sigma>\<^sub>m \<and> 
    disassemble_state \<Sigma>\<^sub>a' = \<Sigma>\<^sub>m' \<and> cd\<^sub>a \<tturnstile> \<Sigma>\<^sub>a \<leadsto>\<^sub>a \<Sigma>\<^sub>a'"
proof (induction cd\<^sub>m \<Sigma>\<^sub>m \<Sigma>\<^sub>m' rule: evalm.induct)
case (evm_ldi cd pc r k rs mem)
  thus ?case by simp
next
case (evm_lod cd pc r ptr rs mem)
  thus ?case by simp
next
case (evm_sto cd pc ptr r rs mem)
  thus ?case by simp
next
case (evm_sti cd pc ptr k rs mem)
  thus ?case by simp
next
case (evm_mov cd pc r1 r2 rs mem)
  thus ?case by simp
next
  case (evm_mvp cd pc r rs mem)
  thus ?case by simp
next
  case (evm_add cd pc r k rs mem)
  thus ?case by simp
next
  case (evm_sub cd pc r k rs mem)
  thus ?case by simp
next
  case (evm_jmp cd pc r rs mem)
  thus ?case by simp
qed

lemma inv_reg_map_reg: "r \<noteq> Acc \<Longrightarrow> 
  (inv_register_map ps act)(R5 := inv_register_map ps act (register_map r)) = 
    inv_register_map (ps(Acc := ps r)) (Reg r)"
proof
  fix x
  show "r \<noteq> Acc \<Longrightarrow> 
    ((inv_register_map ps act)(R5 := inv_register_map ps act (register_map r))) x = 
      inv_register_map (ps(Acc := ps r)) (Reg r) x"
  proof (induction x)
    case R5
    thus ?case by (induction r) simp_all
  qed simp_all
qed

lemma inv_reg_map_pc: "(inv_register_map ps act)(R5 := pc) = inv_register_map (ps(Acc := pc)) PC"
proof
  fix x
  show "((inv_register_map ps act)(R5 := pc)) x = inv_register_map (ps(Acc := pc)) PC x"
    by (induction x) simp_all
qed

lemma inv_reg_map_con: "(inv_register_map ps act)(R5 := k) = 
  inv_register_map (ps(Acc := k)) (Con 0)"
proof
  fix x
  show "((inv_register_map ps act)(R5 := k)) x = inv_register_map (ps(Acc := k)) (Con 0) x"
    by (induction x) simp_all
qed

lemma [simp]: "unmap_mem' (k * 4) = (Hp, k)"
  by (induction k) (simp_all add: numeral_def)

lemma [simp]: "unmap_mem' (Suc (k * 4)) = (Env, k)"
  by (induction k) (simp_all add: numeral_def)

lemma [simp]: "unmap_mem' (Suc (Suc (k * 4))) = (Vals, k)"
  by (induction k) (simp_all add: numeral_def)

lemma [simp]: "unmap_mem' (k * 4 + 3) = (Stk, k)"
  by (induction k) (simp_all add: numeral_def)

lemma [simp]: "m \<noteq> Acc \<Longrightarrow> unmap_mem' (k * 4 + register_offset m) = (m, k)"
proof (induction k)
  case 0
  thus ?case by (induction m) (simp_all add: numeral_def)
qed (simp_all add: numeral_def)

lemma [simp]: "r \<noteq> Acc \<Longrightarrow> inv_register_map (ps(r := k)) act R5 = inv_register_map ps act R5"
  by (induction act) simp_all

lemma [simp]: "r \<noteq> Acc \<Longrightarrow> inv_register_map (ps(r := ps r + k)) act = 
    ((inv_register_map ps act)(register_map r := inv_register_map ps act (register_map r) + 4 * k))"
proof
  fix x
  show "r \<noteq> Acc \<Longrightarrow> inv_register_map (ps(r := ps r + k)) act x =
    ((inv_register_map ps act)(register_map r := inv_register_map ps act (register_map r) + 4 * k)) 
      x" 
  proof (induction r)
    case Hp
    thus ?case by (induction x) simp_all
  next
    case Env
    thus ?case by (induction x) simp_all
  next
    case Vals
    thus ?case by (induction x) simp_all
  next
    case Stk
    thus ?case by (induction x) simp_all
  next
    case Acc
    thus ?case by (induction x) simp_all
  qed
qed

lemma [simp]: "r \<noteq> Acc \<Longrightarrow> inv_register_map (ps(r := ps r - k)) act = 
    ((inv_register_map ps act)(register_map r := inv_register_map ps act (register_map r) - 4 * k))"
proof
  fix x
  show "r \<noteq> Acc \<Longrightarrow> inv_register_map (ps(r := ps r - k)) act x =
    ((inv_register_map ps act)(register_map r := inv_register_map ps act (register_map r) - 4 * k)) 
      x" 
  proof (induction r)
    case Hp
    thus ?case by (induction x) simp_all
  next
    case Env
    thus ?case by (induction x) simp_all
  next
    case Vals
    thus ?case by (induction x) simp_all
  next
    case Stk
    thus ?case by (induction x) simp_all
  next
    case Acc
    thus ?case by (induction x) simp_all
  qed
qed

lemma [simp]: "m \<noteq> Acc \<Longrightarrow> (r \<noteq> Acc \<Longrightarrow> m = r) \<Longrightarrow>
    unmap_mem mem (inv_register_map ps (Reg m) (register_map r)) = mem m (ps r)"
  by (induction r) (simp_all add: unmap_mem_def split: prod.splits)

lemma [simp]: "m \<noteq> Acc \<Longrightarrow> unmap_mem mem (ps Acc * 4 + register_offset m) = mem m (ps Acc)"
  by (simp add: unmap_mem_def)

theorem correctm [simp]: "cd\<^sub>a \<tturnstile> \<Sigma>\<^sub>a \<leadsto>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow>
  disassemble cd\<^sub>a \<tturnstile> disassemble_state \<Sigma>\<^sub>a \<leadsto>\<^sub>m disassemble_state \<Sigma>\<^sub>a'"
proof (induction cd\<^sub>a \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: evala.induct)
  case (eva_movr cd pc r mem ps act)
  hence "disassemble cd ! pc = MOV R5 (register_map r)" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS ((inv_register_map ps act)(R5 := inv_register_map ps act (register_map r))) 
      (unmap_mem mem) pc" by simp
  with eva_movr show ?case by (simp add: inv_reg_map_reg)
next
  case (eva_movp cd pc mem ps act)
  hence "disassemble cd ! pc = MVP R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS ((inv_register_map ps act)(R5 := pc)) (unmap_mem mem) pc" by simp
  thus ?case by (simp add: inv_reg_map_pc)
next
  case (eva_movk cd pc k mem ps act)
  hence "disassemble cd ! pc = LDI R5 k" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS ((inv_register_map ps act)(R5 := k)) (unmap_mem mem) pc" by simp
  thus ?case by (simp add: inv_reg_map_con)
next
  case (eva_geta cd pc m t mem ps)
  hence "disassemble cd ! pc = LOD R5 R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps (Reg m)) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps (Reg m))(R5 := unmap_mem mem (inv_register_map ps (Reg m) R5))) 
      (unmap_mem mem) pc" by (metis evm_lod)

  with eva_geta have  "disassemble cd \<tturnstile> 
    MS (inv_register_map ps (Reg m)) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
      MS (inv_register_map (ps(Acc := mem m (ps Acc))) t) (unmap_mem mem) pc" by simp
  thus ?case by simp
next
  case (eva_get cd pc r t mem ps act)
  then show ?case try0 by simp
next
  case (eva_putr cd pc m r' r mem ps act)
  then show ?case try0 by simp
next
  case (eva_putp cd pc m r' mem ps act)
  then show ?case try0 by simp
next
  case (eva_putk cd pc m r' k mem ps act)
  then show ?case try0 by simp
next
  case (eva_suba cd pc k mem ps act)
  then show ?case try0 by simp
next
  case (eva_sub cd pc r k mem ps act)
  hence "disassemble cd ! pc = SUB (register_map r) (4 * k)" by simp
  with eva_sub show ?case by simp
next
  case (eva_adda cd pc k mem ps act)
  thus ?case by simp
next
  case (eva_add cd pc r k mem ps act)
  hence "disassemble cd ! pc = ADD (register_map r) (4 * k)" by simp
  with eva_add show ?case by simp
next
  case (eva_jmp cd pc mem ps)
  hence "disassemble cd ! pc = JMP R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps PC) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS ((inv_register_map ps PC)(R5 := 0)) (unmap_mem mem) (inv_register_map ps PC R5)" 
      by (metis evm_jmp)
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps PC) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS (inv_register_map (ps(Acc := 0)) (Con 0)) (unmap_mem mem) (ps Acc)" by simp
  thus ?case by simp
qed

theorem correctm_iter [simp]: "iter (\<tturnstile> cd\<^sub>a \<leadsto>\<^sub>a) \<Sigma>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow> 
    iter (\<tturnstile> disassemble cd\<^sub>a \<leadsto>\<^sub>m) (disassemble_state \<Sigma>\<^sub>a) (disassemble_state \<Sigma>\<^sub>a')"
  by (induction \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: iter.induct) (simp, metis correctm iter_append iter_one)
 
lemma [simp]: "inv_register_map (case_register 0 0 0 2 0) (Con 0) = case_reg 0 1 2 11 0" 
  by (auto split: reg.splits)

lemma [simp]: "inv_register_map (case_register hp ep (Suc 0) 0 0) (Con 0) = 
    case_reg (4 * hp) (Suc (4 * ep)) 6 3 0"
  by (auto split: reg.splits)

lemma [simp]: "unmap_mem' 3 = (Stk, 0)"
  by (simp add: numeral_def)

lemma [dest]: "unmap_mem' x = (Stk, 0) \<Longrightarrow> x = 3"
  by (induction x rule: unmap_mem'.induct) (simp_all split: prod.splits)

lemma [simp]: "unmap_mem' 7 = (Stk, 1)"
  by (simp add: numeral_def)

lemma [dest]: "unmap_mem' x = (Stk, Suc 0) \<Longrightarrow> x = 7"
  by (induction x rule: unmap_mem'.induct) (auto split: prod.splits)

lemma [simp]: "unmap_mem (case_register nmem nmem nmem (nmem(0 := 0, Suc 0 := 0)) nmem) = 
    (nmem(3 := 0, 7 := 0))"
  by rule (auto simp add: unmap_mem_def split: prod.splits register.splits)

lemma [simp]: "unmap_mem (case_register h e v s nmem) 2 = v 0"
  by (simp add: unmap_mem_def numeral_def)

end