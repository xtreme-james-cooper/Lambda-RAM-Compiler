theory Disassemble
  imports MachineCode "../12AssemblyCode/AssemblyCode"
begin

primrec register_map :: "memseg \<Rightarrow> reg" where
  "register_map Hp = R1"
| "register_map Env = R2"
| "register_map Vals = R3"
| "register_map Stk = R4"
| "register_map Acc = R5"

primrec register_offset :: "memseg \<Rightarrow> nat" where
  "register_offset Hp = 0"
| "register_offset Env = 1"
| "register_offset Vals = 2"
| "register_offset Stk = 3"
| "register_offset Acc = 4"

primrec pseudoreg_size :: "move_src \<Rightarrow> nat" where
  "pseudoreg_size (Reg r) = (if r = Acc then 1 else 4)"
| "pseudoreg_size (Con k) = 1"
| "pseudoreg_size (Mem r) = 1"

primrec pseudoreg_map :: "memseg \<times> nat \<Rightarrow> nat" where
  "pseudoreg_map (r, x) = (if r = Acc then x else 4 * x + register_offset r)"

fun disassemble' :: "assm \<Rightarrow> mach" where
  "disassemble' (APut r (Reg r')) = 
    (if r = Acc then MOV R5 (register_map r') else STO (register_map r) (register_map r'))"
| "disassemble' (APut r (Con k)) = (if r = Acc then LDI R5 k else STI (register_map r) k)"
| "disassemble' (APut r (Mem r')) = LOD (register_map r) (register_map r')"
| "disassemble' (ASub r k) = SUB (register_map r) (4 * k)"
| "disassemble' (AAdd r k) = ADD (register_map r) (4 * k)"
| "disassemble' AJmp = JMP R5"

definition disassemble :: "assm list \<Rightarrow> mach list" where
  "disassemble cd = map disassemble' cd"

fun unmap_mem' :: "nat \<Rightarrow> memseg \<times> nat" where
  "unmap_mem' 0 = (Hp, 0)" 
| "unmap_mem' (Suc 0) = (Env, 0)"
| "unmap_mem' (Suc (Suc 0)) = (Vals, 0)"
| "unmap_mem' (Suc (Suc (Suc 0))) = (Stk, 0)"
| "unmap_mem' (Suc (Suc (Suc (Suc x)))) = (case unmap_mem' x of (a, b) \<Rightarrow> (a, Suc b))"

definition unmap_mem :: "(memseg \<Rightarrow> nat \<Rightarrow> memseg \<times> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "unmap_mem m x = (case unmap_mem' x of (r, p) \<Rightarrow> pseudoreg_map (m r p))"

primrec inv_register_map :: "(memseg \<Rightarrow> nat) \<Rightarrow> memseg \<Rightarrow> reg \<Rightarrow> nat" where
  "inv_register_map rs t R1 = rs Hp * 4"
| "inv_register_map rs t R2 = rs Env * 4 + 1"
| "inv_register_map rs t R3 = rs Vals * 4 + 2"
| "inv_register_map rs t R4 = rs Stk * 4 + 3"
| "inv_register_map rs t R5 = pseudoreg_map (t, rs Acc)"

primrec disassemble_state :: "assm_state \<Rightarrow> mach_state" where
  "disassemble_state (S\<^sub>a mem rs t pc) = MS (inv_register_map rs t) (unmap_mem mem) pc"

primrec dissassembleable :: "assm_state \<Rightarrow> nat \<Rightarrow> bool" where
  "dissassembleable (S\<^sub>a mem rs t pc) lcd = (pc < lcd)"

lemma [dest]: "R1 = register_map r \<Longrightarrow> r = Hp"
  by (induction r) simp_all

lemma [dest]: "R2 = register_map r \<Longrightarrow> r = Env"
  by (induction r) simp_all

lemma [dest]: "R3 = register_map r \<Longrightarrow> r = Vals"
  by (induction r) simp_all

lemma [dest]: "R4 = register_map r \<Longrightarrow> r = Stk"
  by (induction r) simp_all

lemma [dest]: "R5 = register_map r \<Longrightarrow> r = Acc"
  by (induction r) simp_all

lemma unmap_times_4 [simp]: "unmap_mem' (4 * k) = (Hp, k)"
  by (induction k) (simp_all add: numeral_def)

lemma [simp]: "unmap_mem' (k * 4) = (Hp, k)"
  by (induction k) (simp_all add: numeral_def)

lemma [simp]: "unmap_mem' (Suc (k * 4)) = (Env, k)"
  by (induction k) (simp_all add: numeral_def)

lemma [simp]: "unmap_mem' (Suc (Suc (k * 4))) = (Vals, k)"
  by (induction k) (simp_all add: numeral_def)

lemma [simp]: "unmap_mem' (k * 4 + 3) = (Stk, k)"
  by (induction k) (simp_all add: numeral_def)

lemma [simp]: "unmap_mem' p = (a, b) \<Longrightarrow> unmap_mem' (4 + p) = (a, Suc b)"
  by (simp add: numeral_def)

lemma [simp]: "length (disassemble cd) = length cd"
  by (simp add: disassemble_def)

lemma [dest]: "unmap_mem' x = (Hp, ps Hp) \<Longrightarrow> x = ps Hp * 4"
  by (induction x arbitrary: ps rule: unmap_mem'.induct) (auto split: prod.splits)

lemma [dest]: "unmap_mem' x = (Env, ps Env) \<Longrightarrow> x = Suc (ps Env * 4)"
  by (induction x arbitrary: ps rule: unmap_mem'.induct) (auto split: prod.splits)

lemma [dest]: "unmap_mem' x = (Vals, ps Vals) \<Longrightarrow> x = Suc (Suc (ps Vals * 4))"
  by (induction x arbitrary: ps rule: unmap_mem'.induct) (auto split: prod.splits)

lemma [dest]: "unmap_mem' x = (Stk, ps Stk) \<Longrightarrow> x = Suc (Suc (Suc (ps Stk * 4)))"
  by (induction x arbitrary: ps rule: unmap_mem'.induct) (auto split: prod.splits)

lemma [dest]: "unmap_mem' x = (Acc, b) \<Longrightarrow> False"
  by (induction x arbitrary: b rule: unmap_mem'.induct) (auto split: prod.splits)

lemma [simp]: "unmap_mem' 2 = (Vals, 0)"
  by (simp add: numeral_def)

lemma [simp]: "unmap_mem' (16 + 16 * x) = (Hp, 4 + 4 * x)"
proof -
  have "unmap_mem' (4 * (4 * Suc x)) = (Hp, 4 * Suc x)" by (metis unmap_times_4)
  thus ?thesis by simp
qed

lemma [simp]: "r \<noteq> Acc \<Longrightarrow> unmap_mem' (inv_register_map ps act (register_map r)) = (r, ps r)"
  by (induction r) simp_all

lemma inv_reg_map_reg: "r \<noteq> Acc \<Longrightarrow>
  (inv_register_map ps act)(R5 := inv_register_map ps act (register_map r)) = 
    inv_register_map (ps(Acc := ps r)) r"
proof
  fix x
  assume "r \<noteq> Acc"
  thus "((inv_register_map ps act)(R5 := inv_register_map ps act (register_map r))) x = 
      inv_register_map (ps(Acc := ps r)) r x"
  proof (induction x)
    case R5
    thus ?case by (induction r) simp_all
  qed simp_all
qed

lemma inv_reg_map_none: "(inv_register_map ps act)(R5 := k) = inv_register_map (ps(Acc := k)) Acc"
proof
  fix x
  show "((inv_register_map ps act)(R5 := k)) x = inv_register_map (ps(Acc := k)) Acc x"
    by (induction x) simp_all
qed

lemma [simp]: "(inv_register_map ps act)
    (R5 := if act = Acc then ps Acc else 4 * ps Acc + register_offset act) = inv_register_map ps act"
  by auto

lemma [simp]: "m \<noteq> Acc \<Longrightarrow> unmap_mem' (4 * k + register_offset m) = (m, k)"
proof (induction k)
  case 0
  thus ?case by (induction m) (simp_all add: numeral_def)
qed (simp_all add: numeral_def)

lemma [simp]: "r \<noteq> Acc \<Longrightarrow> inv_register_map (ps(r := k)) act R5 = inv_register_map ps act R5"
  by (induction act) simp_all

lemma [simp]: "r \<noteq> Acc \<Longrightarrow> inv_register_map (ps(r := ps r + k)) act = 
  ((inv_register_map ps act) (register_map r := inv_register_map ps act (register_map r) + 4 * k))"
proof
  fix x
  assume "r \<noteq> Acc"
  thus "inv_register_map (ps(r := ps r + k)) act x =
    ((inv_register_map ps act) 
      (register_map r := inv_register_map ps act (register_map r) + 4 * k)) x" 
    by (induction x) auto
qed

lemma [simp]: "r \<noteq> Acc \<Longrightarrow> (inv_register_map ps r) (R5 := 4 * ps Acc + register_offset r + 4 * k) = 
  inv_register_map (ps(Acc := ps Acc + k)) r"
proof
  fix x
  assume "r \<noteq> Acc"
  thus "((inv_register_map ps r) (R5 := 4 * ps Acc + register_offset r + 4 * k)) x =
    inv_register_map (ps(Acc := ps Acc + k)) r x" by (induction x) simp_all
qed

lemma [simp]: "ps r \<ge> k \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
  inv_register_map (ps(r := ps r - k)) act = ((inv_register_map ps act)
    (register_map r := inv_register_map ps act (register_map r) - 4 * k))"
proof
  fix x
  assume "ps r \<ge> k" and "r \<noteq> Acc"
  thus "inv_register_map (ps(r := ps r - k)) act x =
    ((inv_register_map ps act) 
      (register_map r := inv_register_map ps act (register_map r) - 4 * k)) x" 
    by (induction x) auto
qed

lemma [simp]: "ps Acc \<ge> k \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
  (inv_register_map ps r) (R5 := 4 * ps Acc + register_offset r - 4 * k) = 
    inv_register_map (ps(Acc := ps Acc - k)) r"
proof
  fix x
  assume "ps Acc \<ge> k" and "r \<noteq> Acc"
  thus "((inv_register_map ps r) (R5 := 4 * ps Acc + register_offset r - 4 * k)) x = 
      inv_register_map (ps(Acc := ps Acc - k)) r x" 
    by (induction x) simp_all
qed

lemma [simp]: "r \<noteq> Acc \<Longrightarrow> unmap_mem mem (inv_register_map ps r (register_map r)) = 
    pseudoreg_map (mem r (ps r))"
  by (induction r) (simp_all add: unmap_mem_def split: prod.splits)

lemma [simp]: "r \<noteq> Acc \<Longrightarrow> mem r (ps r) = (t, b) \<Longrightarrow> 
  (inv_register_map ps act)(R5 := unmap_mem mem (inv_register_map ps act (register_map r))) = 
    inv_register_map (ps(Acc := b)) t"
proof
  fix x
  assume "mem r (ps r) = (t, b)" and "r \<noteq> Acc"
  thus "((inv_register_map ps act)(R5 := 
    unmap_mem mem (inv_register_map ps act (register_map r)))) x = 
      inv_register_map (ps(Acc := b)) t x"
  proof (induction x)
    case R5
    thus ?case by (induction r) (simp_all add: unmap_mem_def)
  qed simp_all
qed

lemma unmap_upd_k: "r \<noteq> Acc \<Longrightarrow> (unmap_mem mem)(inv_register_map ps act (register_map r) := k) = 
    unmap_mem (mem_upd mem r (ps r) (Acc, k))"
  by (rule, induction r) (auto simp add: unmap_mem_def split: prod.splits)

lemma [simp]: "r \<noteq> Acc \<Longrightarrow> r' \<noteq> Acc \<Longrightarrow> ((unmap_mem mem)
  (inv_register_map ps act (register_map r) := inv_register_map ps act (register_map r'))) = 
    unmap_mem (mem_upd mem r (ps r) (r', ps r'))"
proof
  fix x
  assume "r \<noteq> Acc" and "r' \<noteq> Acc"
  thus "((unmap_mem mem)
    (inv_register_map ps act (register_map r) := inv_register_map ps act (register_map r'))) x = 
      unmap_mem (mem_upd mem r (ps r) (r', ps r')) x"
  proof (induction r)
    case Hp
    thus ?case by (induction r') (auto simp add: unmap_mem_def split: prod.splits)
  next
    case Env
    thus ?case by (induction r') (auto simp add: unmap_mem_def split: prod.splits)
  next
    case Vals
    thus ?case by (induction r') (auto simp add: unmap_mem_def split: prod.splits)
  next
    case Stk
    thus ?case by (induction r') (auto simp add: unmap_mem_def split: prod.splits)
  qed simp_all
qed

lemma [simp]: "r \<noteq> Acc \<Longrightarrow> ((unmap_mem mem)(inv_register_map ps act (register_map r) := 
  (if act = Acc then a else 4 * a + register_offset act))) = 
    unmap_mem (mem_upd mem r (ps r) (act, a))"
proof
  fix x
  assume "r \<noteq> Acc"
  thus "((unmap_mem mem)(inv_register_map ps act (register_map r) := 
    (if act = Acc then a else 4 * a + register_offset act))) x = 
      unmap_mem (mem_upd mem r (ps r) (act, a)) x"
        by (induction r) (auto simp add: unmap_mem_def split: prod.splits)
qed

lemma [simp]: "m \<noteq> Acc \<Longrightarrow> mem m (ps Acc) = (t, b) \<Longrightarrow>  
  ((inv_register_map ps m)(R5 := unmap_mem mem (4 * ps Acc + register_offset m))) = 
    inv_register_map (ps(Acc := b)) t"
proof 
  fix x
  assume "mem m (ps Acc) = (t, b)" and "m \<noteq> Acc"
  thus "((inv_register_map ps m)(R5 := unmap_mem mem (4 * ps Acc + register_offset m))) 
    x = inv_register_map (ps(Acc := b)) t x"
      by (induction x) (auto simp add: unmap_mem_def)
qed

lemma [simp]: "mem act (ps Acc) = (r, b) \<Longrightarrow> r \<noteq> Acc \<Longrightarrow> act \<noteq> Acc \<Longrightarrow>
  ((inv_register_map ps act)(register_map r := unmap_mem mem (4 * ps Acc + register_offset act))) =
    (inv_register_map (ps(r := b)) act)"
proof 
  fix x
  assume "mem act (ps Acc) = (r, b)" and "act \<noteq> Acc" and "r \<noteq> Acc"
  thus "((inv_register_map ps act)
    (register_map r := unmap_mem mem (4 * ps Acc + register_offset act))) x =
      (inv_register_map (ps(r := b)) act) x"
    by (induction x) (auto simp add: unmap_mem_def)
qed

lemma [simp]: "mem r' (ps r') = (r, b) \<Longrightarrow> r' \<noteq> Acc \<Longrightarrow> r \<noteq> Acc \<Longrightarrow>
  ((inv_register_map ps act) 
    (register_map r := unmap_mem mem (inv_register_map ps act (register_map r')))) =
      (inv_register_map (ps(r := b)) act)"
proof 
  fix x
  assume "mem r' (ps r') = (r, b)" and "r' \<noteq> Acc" and "r \<noteq> Acc"
  thus "((inv_register_map ps act)
    (register_map r := unmap_mem mem (inv_register_map ps act (register_map r')))) x =
      (inv_register_map (ps(r := b)) act) x"
  proof (induction x)
    case R1
    thus ?case by (induction r) (simp_all add: unmap_mem_def)
  next
    case R2
    thus ?case by (induction r) (simp_all add: unmap_mem_def)
  next
    case R3
    thus ?case by (induction r) (simp_all add: unmap_mem_def)
  next
    case R4
    thus ?case by (induction r) (simp_all add: unmap_mem_def)
  next
    case R5
    thus ?case by (induction r) (simp_all add: unmap_mem_def)
  qed 
qed

lemma [simp]: "(inv_register_map ps act)(R5 := pseudoreg_map (act, ps Acc)) = inv_register_map ps act"
  by auto

lemma lookup_disassemble [simp]: "lookup cd pc = Some op \<Longrightarrow> disassemble cd ! pc = disassemble' op"
proof (induction cd)
  case (Cons op cd)
  thus ?case by (induction pc) (simp_all add: disassemble_def)
qed simp_all

theorem correctm [simp]: "cd\<^sub>a \<tturnstile> \<Sigma>\<^sub>a \<leadsto>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow> 
  disassemble cd\<^sub>a \<tturnstile> disassemble_state \<Sigma>\<^sub>a \<leadsto>\<^sub>m disassemble_state \<Sigma>\<^sub>a'"
proof (induction cd\<^sub>a \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: evala.induct)
  case (eva_movr cd pc r mem ps act)
  moreover hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps act)(R5 := (inv_register_map ps act) (register_map r))) 
      (unmap_mem mem) pc" by simp
  ultimately show ?case by (simp add: inv_reg_map_reg)
next
  case (eva_mova cd pc mem ps act)
  hence "disassemble cd ! pc = MOV R5 R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps act)(R5 := inv_register_map ps act R5)) (unmap_mem mem) pc" 
      by (metis evm_mov)
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS (inv_register_map ps act) (unmap_mem mem) pc" by simp
  thus ?case by simp
next
  case (eva_movk cd pc k mem ps act)
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS ((inv_register_map ps act)(R5 := k)) (unmap_mem mem) pc" by simp
  thus ?case by (simp add: inv_reg_map_none)
next
  case (eva_lod cd pc r' mem ps t b act)
  hence "disassemble cd ! pc = LOD R5 (register_map r')" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps act)(R5 := unmap_mem mem (inv_register_map ps act (register_map r')))) 
      (unmap_mem mem) pc" by (metis evm_lod)
  with eva_lod(2, 3) show ?case by simp
next
  case (eva_loda cd pc mem act ps t b)  
  hence "disassemble cd ! pc = LOD R5 R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps act)(R5 := unmap_mem mem (inv_register_map ps act R5))) 
      (unmap_mem mem) pc" by (metis evm_lod)
  with eva_loda(2, 3) show ?case by simp
next
  case (eva_geta cd pc r mem act ps b) 
  hence "disassemble cd ! pc = LOD (register_map r) R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps act)(register_map r := unmap_mem mem (inv_register_map ps act R5))) 
      (unmap_mem mem) pc" by (metis evm_lod)
  with eva_geta(2, 3, 4) show ?case by simp
next
  case (eva_get cd pc r r' mem ps b act)
  hence "disassemble cd ! pc = LOD (register_map r) (register_map r')" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS ((inv_register_map ps act)(register_map r := (unmap_mem mem) ((inv_register_map ps act) 
      (register_map r')))) (unmap_mem mem) pc" by (metis evm_lod)
  with eva_get(2, 3, 4) show ?case by simp
next
  case (eva_puta cd pc r mem ps act)
  hence "disassemble cd ! pc = STO (register_map r) R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS (inv_register_map ps act) ((unmap_mem mem)(inv_register_map ps act (register_map r) := 
      inv_register_map ps act R5)) pc" by (metis evm_sto)
  with eva_puta show ?case by simp
next
  case (eva_putr cd pc r r' mem ps act)
  hence "disassemble cd ! pc = STO (register_map r) (register_map r')" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS (inv_register_map ps act) ((unmap_mem mem)(inv_register_map ps act (register_map r) := 
      inv_register_map ps act (register_map r'))) pc" by (metis evm_sto)
  with eva_putr show ?case by simp
next
  case (eva_putk cd pc r k mem ps act)
  hence "disassemble cd ! pc = STI (register_map r) k" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS (inv_register_map ps act) 
      ((unmap_mem mem)(inv_register_map ps act (register_map r) := k)) pc" by (metis evm_sti)
  with eva_putk show ?case by (simp add: unmap_upd_k)
next
  case (eva_suba cd pc k ps r mem)
  hence "disassemble cd ! pc = SUB R5 (4 * k)" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps r) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps r)(R5 := inv_register_map ps r R5 - 4 * k)) (unmap_mem mem) pc" 
      by (metis evm_sub)
  with eva_suba show ?case by simp
next
  case (eva_adda cd pc k r mem ps)
  hence "disassemble cd ! pc = ADD R5 (4 * k)" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps r) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps r)(R5 := inv_register_map ps r R5 + 4 * k)) 
      (unmap_mem mem) pc" by (metis evm_add)
  with eva_adda show ?case by simp
next
  case (eva_jmp cd pc mem ps)
  hence "disassemble cd ! pc = JMP R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps Acc) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps Acc)(R5 := 0)) (unmap_mem mem) (inv_register_map ps Acc R5)" 
      try by (metis evm_jmp)
  thus ?case by (simp add: inv_reg_map_none)
qed simp_all

theorem correctm_iter [simp]: "iter (\<tturnstile> cd\<^sub>a \<leadsto>\<^sub>a) \<Sigma>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow> 
    iter (\<tturnstile> disassemble cd\<^sub>a \<leadsto>\<^sub>m) (disassemble_state \<Sigma>\<^sub>a) (disassemble_state \<Sigma>\<^sub>a')"
  by (induction \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: iter.induct) (simp, metis correctm iter_append iter_one)

lemma [simp]: "inv_register_map (case_memseg 0 0 0 2 0) Acc = case_reg 0 1 2 11 0" 
  by (auto split: reg.splits)

lemma [simp]: "inv_register_map (case_memseg hp ep (Suc 0) 0 0) Acc = 
    case_reg (4 * hp) (Suc (4 * ep)) 6 3 0"
  by (auto split: reg.splits)

lemma [dest]: "unmap_mem' x = (r, y) \<Longrightarrow> x = 4 * y + register_offset r"
  by (induction x arbitrary: y rule: unmap_mem'.induct) (simp_all split: prod.splits)

lemma [simp]: "unmap_mem (case_memseg (\<lambda>x. (Acc, 0)) (\<lambda>x. (Acc, 0)) (\<lambda>x. (Acc, 0)) 
  ((\<lambda>x. (Acc, 0)) (0 := (Acc, 0), Suc 0 := (Env, 0))) undefined) = (\<lambda>x. 0)(7 := 1)"
proof (rule, unfold unmap_mem_def)
  fix x
  obtain r p where R: "unmap_mem' x = (r, p)" by fastforce
  moreover hence "x = 4 * p + register_offset r" by auto
  ultimately have "pseudoreg_map ((case r of 
        Stk \<Rightarrow> (\<lambda>x. (Acc, 0))(0 := (Acc, 0), Suc 0 := (Env, 0))
      | Acc \<Rightarrow> undefined 
      | _ \<Rightarrow> (\<lambda>x. (Acc, 0))) p) = ((\<lambda>x. 0)(3 := 0, 7 := 1)) x" 
    by (induction r) (simp_all, presburger+, auto)
  with R show "(case unmap_mem' x of (r, p) \<Rightarrow> 
    pseudoreg_map (case_memseg (\<lambda>x. (Acc, 0)) (\<lambda>x. (Acc, 0)) (\<lambda>x. (Acc, 0))
      ((\<lambda>x. (Acc, 0))(0 := (Acc, 0), Suc 0 := (Env, 0))) undefined r p)) =
        ((\<lambda>x. 0)(7 := 1)) x" by simp
qed

end