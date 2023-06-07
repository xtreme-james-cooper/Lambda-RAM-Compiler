theory Disassemble
  imports MachineCode "../12AssemblyCode/AssemblyCode"
begin

primrec register_map :: "register \<Rightarrow> reg" where
  "register_map Hp = R1"
| "register_map Env = R2"
| "register_map Vals = R3"
| "register_map Stk = R4"

primrec register_offset :: "register \<Rightarrow> nat" where
  "register_offset Hp = 0"
| "register_offset Env = 1"
| "register_offset Vals = 2"
| "register_offset Stk = 3"

fun pseudoreg_size :: "move_src \<Rightarrow> nat" where
  "pseudoreg_size (Reg (Some r)) = 4"
| "pseudoreg_size (Reg None) = 1"
| "pseudoreg_size (Con k) = 1"

fun pseudoreg_map :: "register option \<times> nat \<Rightarrow> nat" where
  "pseudoreg_map (Some r, x) = 4 * x + register_offset r"
| "pseudoreg_map (None, x) = x"

fun disassemble' :: "assm \<Rightarrow> mach" where
  "disassemble' (AGet r) = LOD R5 (case r of Some r \<Rightarrow> register_map r | None \<Rightarrow> R5)"
| "disassemble' (APut (Some r) (Reg r')) = 
    STO (register_map r) (case r' of Some r' \<Rightarrow> register_map r' | None \<Rightarrow> R5)"
| "disassemble' (APut (Some r) (Con k)) = STI (register_map r) k"
| "disassemble' (APut None (Reg r)) = MOV R5 (case r of Some r \<Rightarrow> register_map r | None \<Rightarrow> R5)"
| "disassemble' (APut None (Con k)) = LDI R5 k"
| "disassemble' (ASub r k) = SUB (case r of Some r \<Rightarrow> register_map r | None \<Rightarrow> R5) (4 * k)"
| "disassemble' (AAdd r k) = ADD (case r of Some r \<Rightarrow> register_map r | None \<Rightarrow> R5) (4 * k)"
| "disassemble' AJmp = JMP R5"

definition disassemble :: "assm list \<Rightarrow> mach list" where
  "disassemble cd = map disassemble' cd"

fun unmap_mem' :: "nat \<Rightarrow> register \<times> nat" where
  "unmap_mem' 0 = (Hp, 0)" 
| "unmap_mem' (Suc 0) = (Env, 0)"
| "unmap_mem' (Suc (Suc 0)) = (Vals, 0)"
| "unmap_mem' (Suc (Suc (Suc 0))) = (Stk, 0)"
| "unmap_mem' (Suc (Suc (Suc (Suc x)))) = (case unmap_mem' x of (a, b) \<Rightarrow> (a, Suc b))"

definition unmap_mem :: "(register option \<Rightarrow> nat \<Rightarrow> register option \<times> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "unmap_mem m x = (case unmap_mem' x of (r, p) \<Rightarrow> pseudoreg_map (m (Some r) p))"

primrec inv_register_map :: "(register option \<Rightarrow> nat) \<Rightarrow> register option \<Rightarrow> reg \<Rightarrow> nat" where
  "inv_register_map rs t R1 = rs (Some Hp) * 4"
| "inv_register_map rs t R2 = rs (Some Env) * 4 + 1"
| "inv_register_map rs t R3 = rs (Some Vals) * 4 + 2"
| "inv_register_map rs t R4 = rs (Some Stk) * 4 + 3"
| "inv_register_map rs t R5 = pseudoreg_map (t, rs None)"

primrec disassemble_state :: "assm_state \<Rightarrow> mach_state" where
  "disassemble_state (AS mem rs t pc) = MS (inv_register_map rs t) (unmap_mem mem) pc"

primrec dissassembleable :: "assm_state \<Rightarrow> nat \<Rightarrow> bool" where
  "dissassembleable (AS mem rs t pc) lcd = (pc < lcd)"

lemma [dest]: "R1 = register_map r \<Longrightarrow> r = Hp"
  by (induction r) simp_all

lemma [dest]: "R2 = register_map r \<Longrightarrow> r = Env"
  by (induction r) simp_all

lemma [dest]: "R3 = register_map r \<Longrightarrow> r = Vals"
  by (induction r) simp_all

lemma [dest]: "R4 = register_map r \<Longrightarrow> r = Stk"
  by (induction r) simp_all

lemma [dest]: "R5 = register_map r \<Longrightarrow> False"
  by (induction r) simp_all

lemma unmap_times_4 [simp]: "unmap_mem' (4 * k) = (Hp, k)"
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

lemma [simp]: "unmap_mem' 2 = (Vals, 0)"
  by (simp add: numeral_def)

lemma [simp]: "unmap_mem' (16 + 16 * x) = (Hp, 4 + 4 * x)"
proof -
  have "unmap_mem' (4 * (4 * Suc x)) = (Hp, 4 * Suc x)" by (metis unmap_times_4)
  thus ?thesis by simp
qed

lemma inv_reg_map_reg: "
  (inv_register_map ps act)(R5 := inv_register_map ps act (register_map r)) = 
    inv_register_map (ps(None := ps (Some r))) (Some r)"
proof
  fix x
  show "((inv_register_map ps act)(R5 := inv_register_map ps act (register_map r))) x = 
      inv_register_map (ps(None := ps (Some r))) (Some r) x"
  proof (induction x)
    case R5
    thus ?case by (induction r) simp_all
  qed simp_all
qed

lemma inv_reg_map_none: "(inv_register_map ps act)(R5 := k) = inv_register_map (ps(None := k)) None"
proof
  fix x
  show "((inv_register_map ps act)(R5 := k)) x = inv_register_map (ps(None := k)) None x"
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

lemma [simp]: "unmap_mem' (4 * k + register_offset m) = (m, k)"
proof (induction k)
  case 0
  thus ?case by (induction m) (simp_all add: numeral_def)
qed (simp_all add: numeral_def)

lemma [simp]: "inv_register_map (ps(Some r := k)) act R5 = inv_register_map ps act R5"
  by (induction act) simp_all

lemma [simp]: "inv_register_map (ps(Some r := ps (Some r) + k)) act = 
  ((inv_register_map ps act)
    (register_map r := inv_register_map ps act (register_map r) + 4 * k))"
proof
  fix x
  show "inv_register_map (ps(Some r := ps (Some r) + k)) act x =
    ((inv_register_map ps act)
      (register_map r := inv_register_map ps act (register_map r) + 4 * k)) x" 
    by (induction x) auto
qed

lemma [simp]: "(inv_register_map ps (Some r)) (R5 := 4 * ps None + register_offset r + 4 * k) = 
  inv_register_map (ps(None := ps None + k)) (Some r)"
proof
  fix x
  show "((inv_register_map ps (Some r)) (R5 := 4 * ps None + register_offset r + 4 * k)) x =
    inv_register_map (ps(None := ps None + k)) (Some r) x" by (induction x) simp_all
qed

lemma [simp]: "ps (Some r) \<ge> k \<Longrightarrow>
  inv_register_map (ps(Some r := ps (Some r) - k)) act = ((inv_register_map ps act)
    (register_map r := inv_register_map ps act (register_map r) - 4 * k))"
proof
  fix x
  assume "ps (Some r) \<ge> k"
  thus "inv_register_map (ps(Some r := ps (Some r) - k)) act x =
    ((inv_register_map ps act) 
      (register_map r := inv_register_map ps act (register_map r) - 4 * k)) x" 
    by (induction x) auto
qed

lemma [simp]: "ps None \<ge> k \<Longrightarrow> 
  (inv_register_map ps (Some r)) (R5 := 4 * ps None + register_offset r - 4 * k) = 
    inv_register_map (ps(None := ps None - k)) (Some r)"
proof
  fix x
  assume "ps None \<ge> k"
  thus "((inv_register_map ps (Some r))
    (R5 := 4 * ps None + register_offset r - 4 * k)) x = 
      inv_register_map (ps(None := ps None - k)) (Some r) x" 
    by (induction x) simp_all
qed

lemma [simp]: "unmap_mem mem (inv_register_map ps (Some r) (register_map r)) = 
    pseudoreg_map (mem (Some r) (ps (Some r)))"
  by (induction r) (simp_all add: unmap_mem_def split: prod.splits)

lemma [simp]: "mem (Some r) (ps (Some r)) = (t, b) \<Longrightarrow> 
  (inv_register_map ps act)(R5 := unmap_mem mem (inv_register_map ps act (register_map r))) = 
    inv_register_map (ps(None := b)) t"
proof
  fix x
  assume "mem (Some r) (ps (Some r)) = (t, b)"
  thus "((inv_register_map ps act)(R5 := 
    unmap_mem mem (inv_register_map ps act (register_map r)))) x = 
      inv_register_map (ps(None := b)) t x"
  proof (induction x)
    case R5
    thus ?case by (induction r) (simp_all add: unmap_mem_def)
  qed simp_all
qed

lemma unmap_upd_k: "(unmap_mem mem)(inv_register_map ps act (register_map r) := k) = 
    unmap_mem (mem_upd mem (Some r) (ps (Some r)) (None, k))"
  by (rule, induction r) (auto simp add: unmap_mem_def split: prod.splits)

lemma [simp]: "((unmap_mem mem)
  (inv_register_map ps act (register_map r) := inv_register_map ps act (register_map r'))) = 
    unmap_mem (mem_upd mem (Some r) (ps (Some r)) (Some r', ps (Some r')))"
proof
  fix x
  show "((unmap_mem mem)
    (inv_register_map ps act (register_map r) := inv_register_map ps act (register_map r'))) x = 
      unmap_mem (mem_upd mem (Some r) (ps (Some r)) (Some r', ps (Some r'))) x"
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
  qed
qed

lemma [simp]: "((unmap_mem mem)(inv_register_map ps act (register_map r) := 
    pseudoreg_map (act, a))) = unmap_mem (mem_upd mem (Some r) (ps (Some r)) (act, a))"
proof
  fix x
  show "((unmap_mem mem)(inv_register_map ps act (register_map r) := 
    pseudoreg_map (act, a))) x = unmap_mem (mem_upd mem (Some r) (ps (Some r)) (act, a)) x"
      by (induction r) (auto simp add: unmap_mem_def split: prod.splits)
qed

lemma [simp]: "mem (Some m) (ps None) = (t, b) \<Longrightarrow>  
  ((inv_register_map ps (Some m))(R5 := unmap_mem mem (4 * ps None + register_offset m))) = 
    inv_register_map (ps(None := b)) t"
proof 
  fix x
  assume "mem (Some m) (ps None) = (t, b)"
  thus "((inv_register_map ps (Some m))(R5 := unmap_mem mem (4 * ps None + register_offset m))) 
    x = inv_register_map (ps(None := b)) t x"
      by (induction x) (auto simp add: unmap_mem_def)
qed

lemma [simp]: "(inv_register_map ps act)(R5 := pseudoreg_map (act, ps None)) = inv_register_map ps act"
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
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps act)(R5 := (inv_register_map ps act) (register_map r))) 
      (unmap_mem mem) pc" by simp
  thus ?case by (simp add: inv_reg_map_reg)
next
  case (eva_mova cd pc mem ps act)
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps act)(R5 := (inv_register_map ps act) R5)) 
      (unmap_mem mem) pc" by simp
  thus ?case by simp
next
  case (eva_movk cd pc k mem ps act)
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS ((inv_register_map ps act)(R5 := k)) (unmap_mem mem) pc" by simp
  thus ?case by (simp add: inv_reg_map_none)
next
  case (eva_geta cd pc mem r ps t b) 
  hence "disassemble cd ! pc = LOD R5 R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps (Some r)) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps (Some r))(R5 := unmap_mem mem (inv_register_map ps (Some r) R5))) 
      (unmap_mem mem) pc" by (metis evm_lod)
  with eva_geta(2) show ?case by simp
next
  case (eva_get cd pc r mem ps t b act)
  hence "disassemble cd ! pc = LOD R5 (register_map r)" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS ((inv_register_map ps act)(R5 := (unmap_mem mem) ((inv_register_map ps act) 
      (register_map r)))) (unmap_mem mem) pc" by (metis evm_lod)
  with eva_get(2) show ?case by simp
next
  case (eva_puta cd pc r mem ps act)
  hence "disassemble cd ! pc = STO (register_map r) R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS (inv_register_map ps act) ((unmap_mem mem)(inv_register_map ps act (register_map r) := 
      inv_register_map ps act R5)) pc" by (metis evm_sto)
  thus ?case by simp
next
  case (eva_putr cd pc r r' mem ps act)
  hence "disassemble cd ! pc = STO (register_map r) (register_map r')" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS (inv_register_map ps act) ((unmap_mem mem)(inv_register_map ps act (register_map r) := 
      inv_register_map ps act (register_map r'))) pc" by (metis evm_sto)
  thus ?case by simp
next
  case (eva_putk cd pc r k mem ps act)
  hence "disassemble cd ! pc = STI (register_map r) k" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS (inv_register_map ps act) 
      ((unmap_mem mem)(inv_register_map ps act (register_map r) := k)) pc" by (metis evm_sti)
  thus ?case by (simp add: unmap_upd_k)
next
  case (eva_suba cd pc k ps mem r)
  hence "disassemble cd ! pc = SUB R5 (4 * k)" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps (Some r)) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps (Some r))(R5 := inv_register_map ps (Some r) R5 - 4 * k)) 
      (unmap_mem mem) pc" by (metis evm_sub)
  with eva_suba show ?case by simp
next
  case (eva_adda cd pc k mem ps r)
  hence "disassemble cd ! pc = ADD R5 (4 * k)" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps (Some r)) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps (Some r))(R5 := inv_register_map ps (Some r) R5 + 4 * k)) 
      (unmap_mem mem) pc" by (metis evm_add)
  with eva_adda show ?case by simp
next
  case (eva_jmp cd pc mem ps)
  hence "disassemble cd ! pc = JMP R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps None) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps None)(R5 := 0)) (unmap_mem mem) (inv_register_map ps None R5)" 
      by (metis evm_jmp)
  thus ?case by (simp add: inv_reg_map_none)
qed simp_all

theorem correctm_iter [simp]: "iter (\<tturnstile> cd\<^sub>a \<leadsto>\<^sub>a) \<Sigma>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow> 
    iter (\<tturnstile> disassemble cd\<^sub>a \<leadsto>\<^sub>m) (disassemble_state \<Sigma>\<^sub>a) (disassemble_state \<Sigma>\<^sub>a')"
  by (induction \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: iter.induct) (simp, metis correctm iter_append iter_one)

lemma [simp]: "inv_register_map (registers_case 0 0 0 2 0) None = case_reg 0 1 2 11 0" 
  by (auto split: reg.splits)

lemma [simp]: "inv_register_map (registers_case hp ep (Suc 0) 0 0) None = 
    case_reg (4 * hp) (Suc (4 * ep)) 6 3 0"
  by (auto split: reg.splits)

lemma [dest]: "unmap_mem' x = (r, y) \<Longrightarrow> x = 4 * y + register_offset r"
  by (induction x arbitrary: y rule: unmap_mem'.induct) (simp_all split: prod.splits)

lemma [simp]: "unmap_mem (registers_case (\<lambda>x. (None, 0)) (\<lambda>x. (None, 0)) (\<lambda>x. (None, 0)) 
  ((\<lambda>x. (None, 0)) (0 := (None, 0), Suc 0 := (Some Env, 0))) undefined) = (\<lambda>x. 0)(7 := 1)"
proof (rule, unfold unmap_mem_def)
  fix x
  obtain r p where R: "unmap_mem' x = (r, p)" by fastforce
  moreover hence "x = 4 * p + register_offset r" by auto
  ultimately have "pseudoreg_map ((case r of 
        Stk \<Rightarrow> (\<lambda>x. (None, 0))(0 := (None, 0), Suc 0 := (Some Env, 0)) 
      | _ \<Rightarrow> (\<lambda>x. (None, 0))) p) = ((\<lambda>x. 0)(3 := 0, 7 := 1)) x" 
    by (induction r) (simp_all, presburger+)
  with R show "(case unmap_mem' x of (r, p) \<Rightarrow> 
    pseudoreg_map (registers_case (\<lambda>x. (None, 0)) (\<lambda>x. (None, 0)) (\<lambda>x. (None, 0))
      ((\<lambda>x. (None, 0))(0 := (None, 0), Suc 0 := (Some Env, 0))) undefined (Some r) p)) =
        ((\<lambda>x. 0)(7 := 1)) x" by simp
qed

end