theory Disassemble
  imports MachineCode "../13AssemblyCode/AssemblyCode" "../00Utils/Utils" "../00Utils/Iteration"
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

primrec pseudoreg_size :: "pseudoreg \<Rightarrow> nat" where
  "pseudoreg_size (Reg r) = 4"
| "pseudoreg_size (PC _) = 1"
| "pseudoreg_size (Con k) = 1"
| "pseudoreg_size (Acc _) = 1"

fun pseudoreg_map :: "pseudoreg \<times> nat \<Rightarrow> nat" where
  "pseudoreg_map (Reg r, x) = 4 * x + register_offset r"
| "pseudoreg_map (PC _, x) = x"
| "pseudoreg_map (Con k, x) = x"
| "pseudoreg_map (Acc _, x) = x"

fun disassemble' :: "assm \<Rightarrow> mach" where
  "disassemble' (AMov (Reg r)) = MOV R5 (register_map r)"
| "disassemble' (AMov (PC _)) = MVP R5"
| "disassemble' (AMov (Con k)) = LDI R5 k"
| "disassemble' (AMov (Acc _)) = undefined"
| "disassemble' (AGet (Reg r) t) = LOD R5 (register_map r)"
| "disassemble' (AGet (PC _) t) = undefined"
| "disassemble' (AGet (Con k) t) = undefined"
| "disassemble' (AGet (Acc r) t) = LOD R5 R5"
| "disassemble' (APut r (Reg r')) = STO (register_map r) (register_map r')"
| "disassemble' (APut r (PC k)) = STI (register_map r) k"
| "disassemble' (APut r (Con k)) = STI (register_map r) k"
| "disassemble' (APut r (Acc _)) = STO (register_map r) R5"
| "disassemble' (ASub (Reg r) k) = SUB (register_map r) (4 * k)"
| "disassemble' (ASub (PC _) k) = undefined"
| "disassemble' (ASub (Con m) k) = undefined"
| "disassemble' (ASub (Acc t) k) = SUB R5 (pseudoreg_size t * k)"
| "disassemble' (AAdd (Reg r) k) = ADD (register_map r) (4 * k)"
| "disassemble' (AAdd (PC _) k) = undefined"
| "disassemble' (AAdd (Con m) k) = undefined"
| "disassemble' (AAdd (Acc t) k) = ADD R5 (pseudoreg_size t * k)"
| "disassemble' AJmp = JMP R5"

definition disassemble :: "assm list \<Rightarrow> mach list" where
  "disassemble cd = map disassemble' cd"

fun unmap_mem' :: "nat \<Rightarrow> register \<times> nat" where
  "unmap_mem' 0 = (Hp, 0)" 
| "unmap_mem' (Suc 0) = (Env, 0)"
| "unmap_mem' (Suc (Suc 0)) = (Vals, 0)"
| "unmap_mem' (Suc (Suc (Suc 0))) = (Stk, 0)"
| "unmap_mem' (Suc (Suc (Suc (Suc x)))) = (case unmap_mem' x of (a, b) \<Rightarrow> (a, Suc b))"

definition unmap_mem :: "(register \<Rightarrow> nat \<Rightarrow> pseudoreg \<times> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "unmap_mem m x = (case unmap_mem' x of (r, p) \<Rightarrow> pseudoreg_map (m r p))"

primrec inv_register_map :: "(register \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> pseudoreg \<Rightarrow> reg \<Rightarrow> nat" where
  "inv_register_map rs a t R1 = rs Hp * 4"
| "inv_register_map rs a t R2 = rs Env * 4 + 1"
| "inv_register_map rs a t R3 = rs Vals * 4 + 2"
| "inv_register_map rs a t R4 = rs Stk * 4 + 3"
| "inv_register_map rs a t R5 = pseudoreg_map (t, a)"

primrec disassemble_state :: "assm_state \<Rightarrow> mach_state" where
  "disassemble_state (AS mem rs a t pc) = MS (inv_register_map rs a t) (unmap_mem mem) pc"

primrec dissassembleable :: "assm_state \<Rightarrow> nat \<Rightarrow> bool" where
  "dissassembleable (AS mem rs a t pc) lcd = (pc < lcd)"

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
  (inv_register_map ps a act)(R5 := inv_register_map ps a act (register_map r)) = 
    inv_register_map ps (ps r) (Reg r)"
proof
  fix x
  show "((inv_register_map ps a act)(R5 := inv_register_map ps a act (register_map r))) x = 
      inv_register_map ps (ps r) (Reg r) x"
  proof (induction x)
    case R5
    thus ?case by (induction r) simp_all
  qed simp_all
qed

lemma inv_reg_map_pc: "(inv_register_map ps a act)(R5 := pc) = inv_register_map ps pc (PC 0)"
proof
  fix x
  show "((inv_register_map ps a act)(R5 := pc)) x = inv_register_map ps pc (PC 0) x"
    by (induction x) simp_all
qed

lemma inv_reg_map_con: "(inv_register_map ps a act)(R5 := k) = inv_register_map ps k (Con 0)"
proof
  fix x
  show "((inv_register_map ps a act)(R5 := k)) x = inv_register_map ps k (Con 0) x"
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

lemma [simp]: "inv_register_map (ps(r := k)) a act R5 = inv_register_map ps a act R5"
  by (induction act) simp_all

lemma [simp]: "inv_register_map (ps(r := ps r + k)) a act = 
  ((inv_register_map ps a act)
    (register_map r := inv_register_map ps a act (register_map r) + 4 * k))"
proof
  fix x
  show "inv_register_map (ps(r := ps r + k)) a act x =
    ((inv_register_map ps a act)
      (register_map r := inv_register_map ps a act (register_map r) + 4 * k)) x" 
    by (induction x) auto
qed

lemma [simp]: "(inv_register_map ps a act) (R5 := pseudoreg_map (act, a) + pseudoreg_size act * k) = 
  inv_register_map ps (a + k) act"
proof
  fix x
  show "((inv_register_map ps a act) (R5 := pseudoreg_map (act, a) + pseudoreg_size act * k)) x =
    inv_register_map ps (a + k) act x" 
  proof (induction x)
    case R5
    thus ?case by (induction act) simp_all
  qed simp_all
qed

lemma [simp]: "ps r \<ge> k \<Longrightarrow>
  inv_register_map (ps(r := ps r - k)) a act = ((inv_register_map ps a act)
    (register_map r := inv_register_map ps a act (register_map r) - 4 * k))"
proof
  fix x
  assume "ps r \<ge> k"
  thus "inv_register_map (ps(r := ps r - k)) a act x =
    ((inv_register_map ps a act) 
      (register_map r := inv_register_map ps a act (register_map r) - 4 * k)) x" 
    by (induction x) auto
qed

lemma [simp]: "a \<ge> k \<Longrightarrow> 
  (inv_register_map ps a act) (R5 := pseudoreg_map (act, a) - pseudoreg_size act * k) = 
    inv_register_map ps (a - k) act"
proof
  fix x
  assume "a \<ge> k"
  thus "((inv_register_map ps a act)
    (R5 := pseudoreg_map (act, a) - pseudoreg_size act * k)) x =
      inv_register_map ps (a - k) act x" 
  proof (induction x)
    case R5
    thus ?case by (induction act) simp_all
  qed simp_all
qed

lemma [simp]: "unmap_mem mem (inv_register_map ps a (Reg r) (register_map r)) = 
    pseudoreg_map (mem r (ps r))"
  by (induction r) (simp_all add: unmap_mem_def split: prod.splits)

lemma [simp]: "((inv_register_map ps a (PC 0))(R5 := 0)) = inv_register_map ps 0 (Con 0)"
proof
  fix x
  show "((inv_register_map ps a (PC 0))(R5 := 0)) x = inv_register_map ps 0 (Con 0) x" 
    by (induction x) simp_all
qed

lemma [simp]: "mem r (ps r) = (t, b) \<Longrightarrow> 
  (inv_register_map ps a act)(R5 := unmap_mem mem (inv_register_map ps a act (register_map r))) = 
    inv_register_map ps b t"
proof
  fix x
  assume "mem r (ps r) = (t, b)"
  thus "((inv_register_map ps a act)(R5 := 
    unmap_mem mem (inv_register_map ps a act (register_map r)))) x = inv_register_map ps b t x"
  proof (induction x)
    case R5
    thus ?case by (induction r) (simp_all add: unmap_mem_def)
  qed simp_all
qed

lemma unmap_upd_k: "(unmap_mem mem)(inv_register_map ps a act (register_map r) := k) = 
  unmap_mem (mem_upd mem r (ps r) (Con 0, k))"
proof
  fix x
  show "((unmap_mem mem)(inv_register_map ps a act (register_map r) := k)) x =
      unmap_mem (mem_upd mem r (ps r) (Con 0, k)) x"
    by (induction r) (auto simp add: unmap_mem_def split: prod.splits)
qed

lemma unmap_upd_pc: "(unmap_mem mem)(inv_register_map ps a act (register_map r) := k) = 
  unmap_mem (mem_upd mem r (ps r) (PC 0, k))"
proof
  fix x
  show "((unmap_mem mem)(inv_register_map ps a act (register_map r) := k)) x =
      unmap_mem (mem_upd mem r (ps r) (PC 0, k)) x"
    by (induction r) (auto simp add: unmap_mem_def split: prod.splits)
qed

lemma [simp]: "((unmap_mem mem)
  (inv_register_map ps a act (register_map r) := inv_register_map ps a act (register_map r'))) = 
    unmap_mem (mem_upd mem r (ps r) (Reg r', ps r'))"
proof
  fix x
  show "((unmap_mem mem)
    (inv_register_map ps a act (register_map r) := inv_register_map ps a act (register_map r'))) x = 
      unmap_mem (mem_upd mem r (ps r) (Reg r', ps r')) x"
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

lemma [simp]: "((unmap_mem mem)(inv_register_map ps a act (register_map r) := 
    pseudoreg_map (act, a))) = unmap_mem (mem_upd mem r (ps r) (act, a))"
proof
  fix x
  show "((unmap_mem mem)(inv_register_map ps a act (register_map r) := 
    pseudoreg_map (act, a))) x = unmap_mem (mem_upd mem r (ps r) (act, a)) x"
      by (induction r) (auto simp add: unmap_mem_def split: prod.splits)
qed

lemma [simp]: "mem m a = (t, b) \<Longrightarrow>  
  ((inv_register_map ps a (Reg m))(R5 := unmap_mem mem (4 * a + register_offset m))) = 
    inv_register_map ps b t"
proof 
  fix x
  assume "mem m a = (t, b)"
  thus "((inv_register_map ps a (Reg m))(R5 := unmap_mem mem (4 * a + register_offset m))) 
    x = inv_register_map ps b t x"
      by (induction x) (auto simp add: unmap_mem_def)
qed

lemma [simp]: "lookup cd pc = Some op \<Longrightarrow> disassemble cd ! pc = disassemble' op"
proof (induction cd)
  case (Cons op cd)
  thus ?case by (induction pc) (simp_all add: disassemble_def)
qed simp_all

theorem correctm [simp]: "cd\<^sub>a \<tturnstile> \<Sigma>\<^sub>a \<leadsto>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow> 
  disassemble cd\<^sub>a \<tturnstile> disassemble_state \<Sigma>\<^sub>a \<leadsto>\<^sub>m disassemble_state \<Sigma>\<^sub>a'"
proof (induction cd\<^sub>a \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: evala.induct)
  case (eva_movr cd pc r mem ps a act)
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps a act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps a act)(R5 := (inv_register_map ps a act) (register_map r))) 
      (unmap_mem mem) pc" by simp
  thus ?case by (simp add: inv_reg_map_reg)
next
  case (eva_movp cd pc x mem ps a act)
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps a act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS ((inv_register_map ps a act)(R5 := pc)) (unmap_mem mem) pc" by simp
  thus ?case by (simp add: inv_reg_map_pc)
next
  case (eva_movk cd pc k mem ps a act)
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps a act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS ((inv_register_map ps a act)(R5 := k)) (unmap_mem mem) pc" by simp
  thus ?case by (simp add: inv_reg_map_con)
next
  case (eva_geta cd pc m t mem a b ps) 
  hence "disassemble cd ! pc = LOD R5 R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps a (Reg m)) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps a (Reg m))(R5 := unmap_mem mem (inv_register_map ps a (Reg m) R5))) 
      (unmap_mem mem) pc" by (metis evm_lod)
  with eva_geta(2) show ?case by simp
next
  case (eva_get cd pc r t mem ps b a act)
  hence "disassemble cd ! pc = LOD R5 (register_map r)" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps a act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS ((inv_register_map ps a act)(R5 := (unmap_mem mem) ((inv_register_map ps a act) 
      (register_map r)))) (unmap_mem mem) pc" by (metis evm_lod)
  with eva_get(2) show ?case by simp
next
  case (eva_puta cd pc r x mem ps a act)
  hence "disassemble cd ! pc = STO (register_map r) R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps a act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS (inv_register_map ps a act) ((unmap_mem mem)(inv_register_map ps a act (register_map r) := 
      inv_register_map ps a act R5)) pc" by (metis evm_sto)
  thus ?case by simp
next
  case (eva_putp cd pc r k mem ps a act)
  hence "disassemble cd ! pc = STI (register_map r) k" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps a act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS (inv_register_map ps a act) ((unmap_mem mem)((inv_register_map ps a act) (register_map r) := 
      k)) pc" by (metis evm_sti)
  thus ?case by (simp add: unmap_upd_pc)
next
  case (eva_putr cd pc r r' mem ps a act)
  hence "disassemble cd ! pc = STO (register_map r) (register_map r')" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps a act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS (inv_register_map ps a act) ((unmap_mem mem)(inv_register_map ps a act (register_map r) := 
      inv_register_map ps a act (register_map r'))) pc" by (metis evm_sto)
  thus ?case by simp
next
  case (eva_putk cd pc r k mem ps a act)
  hence "disassemble cd ! pc = STI (register_map r) k" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps a act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m
    MS (inv_register_map ps a act) 
      ((unmap_mem mem)(inv_register_map ps a act (register_map r) := k)) pc" by (metis evm_sti)
  thus ?case by (simp add: unmap_upd_k)
next
  case (eva_suba cd pc act k a mem ps)
  hence "disassemble cd ! pc = SUB R5 (pseudoreg_size act * k)" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps a act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps a act)(R5 := inv_register_map ps a act R5 - pseudoreg_size act * k)) 
      (unmap_mem mem) pc" by (metis evm_sub)
  with eva_suba show ?case by simp
next
  case (eva_adda cd pc act k mem ps a)
  hence "disassemble cd ! pc = ADD R5 (pseudoreg_size act * k)" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps a act) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps a act)(R5 := inv_register_map ps a act R5 + pseudoreg_size act * k)) 
      (unmap_mem mem) pc" by (metis evm_add)
  thus ?case by simp
next
  case (eva_jmp cd pc mem ps a)
  hence "disassemble cd ! pc = JMP R5" by simp
  hence "disassemble cd \<tturnstile> MS (inv_register_map ps a (PC 0)) (unmap_mem mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((inv_register_map ps a (PC 0))(R5 := 0)) (unmap_mem mem) (inv_register_map ps a (PC 0) R5)" 
      by (metis evm_jmp)
  thus ?case by simp
qed simp_all

theorem correctm_iter [simp]: "iter (\<tturnstile> cd\<^sub>a \<leadsto>\<^sub>a) \<Sigma>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow> 
    iter (\<tturnstile> disassemble cd\<^sub>a \<leadsto>\<^sub>m) (disassemble_state \<Sigma>\<^sub>a) (disassemble_state \<Sigma>\<^sub>a')"
  by (induction \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: iter.induct) (simp, metis correctm iter_append iter_one)
 
lemma [simp]: "inv_register_map (case_register 0 0 0 2) 0 (Con 0) = case_reg 0 1 2 11 0" 
  by (auto split: reg.splits)

lemma [simp]: "inv_register_map (case_register hp ep (Suc 0) 0) 0 (Con 0) = 
    case_reg (4 * hp) (Suc (4 * ep)) 6 3 0"
  by (auto split: reg.splits)

lemma [dest]: "unmap_mem' x = (r, y) \<Longrightarrow> x = 4 * y + register_offset r"
  by (induction x arbitrary: y rule: unmap_mem'.induct) (simp_all split: prod.splits)

lemma [simp]: "unmap_mem (case_register (\<lambda>x. (Con 0, 0)) (\<lambda>x. (Con 0, 0)) (\<lambda>x. (Con 0, 0)) 
  ((\<lambda>x. (Con 0, 0))(0 := (PC 0, 0), Suc 0 := (Reg Env, 0)))) = (\<lambda>x. 0)(7 := 1)"
proof (rule, unfold unmap_mem_def)
  fix x
  obtain r p where R: "unmap_mem' x = (r, p)" by fastforce
  moreover hence "x = 4 * p + register_offset r" by auto
  ultimately have "pseudoreg_map ((case r of 
        Stk \<Rightarrow> (\<lambda>x. (Con 0, 0))(0 := (PC 0, 0), Suc 0 := (Reg Env, 0)) 
      | _ \<Rightarrow> (\<lambda>x. (Con 0, 0))) p) = ((\<lambda>x. 0)(3 := 0, 7 := 1)) x" 
    by (induction r) (simp_all, presburger+)
  with R show "(case unmap_mem' x of (r, p) \<Rightarrow> 
    pseudoreg_map ((case r of 
      Stk \<Rightarrow> (\<lambda>x. (Con 0, 0))(0 := (PC 0, 0), Suc 0 := (Reg Env, 0)) | _ \<Rightarrow> (\<lambda>x. (Con 0, 0))) p)) =
        ((\<lambda>x. 0)(7 := 1)) x" by simp
qed

end