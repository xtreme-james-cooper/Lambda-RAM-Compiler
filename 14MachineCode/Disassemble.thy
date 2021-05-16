theory Disassemble
  imports MachineCode "../13AssemblyCode/AssemblyCode" "../00Utils/Utils" "../00Utils/Iteration"
begin

primrec register_map :: "register \<Rightarrow> reg" where
  "register_map Hp = R1"
| "register_map Env = R2"
| "register_map Vals = R3"
| "register_map Stk = R4"
| "register_map Acc = R5"

primrec inv_register_map :: "reg \<Rightarrow> register" where
  "inv_register_map R1 = Hp"
| "inv_register_map R2 = Env"
| "inv_register_map R3 = Vals"
| "inv_register_map R4 = Stk"
| "inv_register_map R5 = Acc"

fun disassemble' :: "assm \<Rightarrow> mach" where
  "disassemble' (AMov r1 (Reg r2)) = MOV (register_map r1) (register_map r2)"
| "disassemble' (AMov r1 PC) = MVP (register_map r1)"
| "disassemble' (AMov r1 (Con k)) = LDI (register_map r1) k"
| "disassemble' (AGet r1 r2 r3) = LOD (register_map r1) (register_map r3)"
| "disassemble' (APut r1 r2 (Reg r3)) = STO (register_map r1) (register_map r3)"
| "disassemble' (APut r1 r2 PC) = undefined"
| "disassemble' (APut r1 r2 (Con k)) = STI (register_map r1) k"
| "disassemble' (ASub r1 k) = SUB (register_map r1) k"
| "disassemble' (AAdd r1 k) = ADD (register_map r1) k"
| "disassemble' AJmp = JMP R5"

definition disassemble :: "assm list \<Rightarrow> mach list" where
  "disassemble cd = map disassemble' cd"

fun unmap_mem :: "nat \<Rightarrow> register \<times> nat" where
  "unmap_mem 0 = (Hp, 0)" 
| "unmap_mem (Suc 0) = (Env, 0)"
| "unmap_mem (Suc (Suc 0)) = (Vals, 0)"
| "unmap_mem (Suc (Suc (Suc 0))) = (Stk, 0)"
| "unmap_mem (Suc (Suc (Suc (Suc x)))) = (case unmap_mem x of (a, b) \<Rightarrow> (a, Suc b))"

primrec disassemble_state :: "assm_state \<Rightarrow> mach_state" where
  "disassemble_state (AS mem rs pc) = MS (rs \<circ> inv_register_map) (uncurry mem \<circ> unmap_mem) pc"

lemma [simp]: "unmap_mem p = (a, b) \<Longrightarrow> uncurry mem (unmap_mem (4 + p)) = mem a (Suc b)"
  by (simp add: numeral_def split: prod.splits)

lemma [simp]: "unmap_mem (4 * x) = (Hp, x)"
  by (induction x rule: unmap_mem.induct) (simp_all add: numeral_def)

lemma [simp]: "length (disassemble cd) = length cd"
  by (simp add: disassemble_def)

theorem completem [simp]: "cd\<^sub>m \<tturnstile> \<Sigma>\<^sub>m \<leadsto>\<^sub>m \<Sigma>\<^sub>m' \<Longrightarrow> 
  \<exists>cd\<^sub>a \<Sigma>\<^sub>a \<Sigma>\<^sub>a'. cd\<^sub>m = disassemble cd\<^sub>a \<and> disassemble_state \<Sigma>\<^sub>a = \<Sigma>\<^sub>m \<and> 
    disassemble_state \<Sigma>\<^sub>a' = \<Sigma>\<^sub>m' \<and> iter (\<tturnstile> cd\<^sub>a \<leadsto>\<^sub>a) \<Sigma>\<^sub>a \<Sigma>\<^sub>a'"
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

lemma [simp]: "inv_register_map (register_map r) = r"
  by (induction r) simp_all

lemma [simp]: "register_map (inv_register_map r) = r"
  by (induction r) simp_all

lemma [simp]: "case_register a b c d e \<circ> inv_register_map = case_reg a b c d e"
proof 
  fix x
  show "(case_register a b c d e \<circ> inv_register_map) x = 
    (case x of R1 \<Rightarrow> a | R2 \<Rightarrow> b | R3 \<Rightarrow> c | R4 \<Rightarrow> d | R5 \<Rightarrow> e)" by (induction x) simp_all
qed

theorem correctm [simp]: "cd\<^sub>a \<tturnstile> \<Sigma>\<^sub>a \<leadsto>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow>
   disassemble cd\<^sub>a \<tturnstile> disassemble_state \<Sigma>\<^sub>a \<leadsto>\<^sub>m disassemble_state \<Sigma>\<^sub>a'"
proof (induction cd\<^sub>a \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: evala.induct)
  case (eva_movr cd pc r' r mem ps)
  thus ?case by simp
next
  case (eva_movp cd pc r' mem ps)
  thus ?case by simp
next
  case (eva_movk cd pc r' k mem ps)
  thus ?case by simp
next
  case (eva_get cd pc r' m r mem ps)
  thus ?case by simp
next
  case (eva_putr cd pc m r' r mem ps)
  thus ?case by simp
next
  case (eva_putp cd pc m r' mem ps)
  thus ?case by simp
next
  case (eva_putk cd pc m r' k mem ps)
  thus ?case by simp
next
  case (eva_sub cd pc r k mem ps)
  thus ?case by simp
next
  case (eva_add cd pc r k mem ps)
  thus ?case by simp
next
  case (eva_jmp cd pc mem ps)
  thus ?case by simp
qed

theorem correctm_iter [simp]: "iter (\<tturnstile> cd\<^sub>a \<leadsto>\<^sub>a) \<Sigma>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow> 
    iter (\<tturnstile> disassemble cd\<^sub>a \<leadsto>\<^sub>m) (disassemble_state \<Sigma>\<^sub>a) (disassemble_state \<Sigma>\<^sub>a')"
  by (induction \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: iter.induct) (simp, metis correctm iter_append iter_one)

lemma [simp]: "unmap_mem x = (Stk, 0) \<Longrightarrow> x = 3"
  by (induction x rule: unmap_mem.induct) (simp_all split: prod.splits)

lemma [simp]: "(uncurry (case_register nmem nmem nmem (nmem(0 := 0, Suc 0 := 0)) nmem) \<circ> 
  unmap_mem) = (nmem(3 := 0, 7 := 0))"
proof
  fix x
  show "(uncurry (case_register nmem nmem nmem (nmem(0 := 0, Suc 0 := 0)) nmem) \<circ> 
    unmap_mem) x = (nmem(3 := 0, 7 := 0)) x"
      by (induction x rule: unmap_mem.induct) 
         (auto simp add: numeral_def split: prod.splits register.splits)
qed

lemma [simp]: "case_reg 0 0 0 2 0 = ((\<lambda>r. 0)(R4 := 2))"
  by (auto split: reg.splits)

end