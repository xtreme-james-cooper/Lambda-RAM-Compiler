theory Disassemble
  imports MachineCode "../13AssemblyCode/AssemblyCode" "../00Utils/Utils" "../00Utils/Iteration"
begin

primrec register_map :: "aregister \<Rightarrow> register" where
  "register_map HP = R1"
| "register_map EP = R2"
| "register_map VP = R3"
| "register_map SP = R4"
| "register_map ACC = R5"
| "register_map ACC2 = R6"

primrec inv_register_map :: "register \<Rightarrow> aregister" where
  "inv_register_map R1 = HP"
| "inv_register_map R2 = EP"
| "inv_register_map R3 = VP"
| "inv_register_map R4 = SP"
| "inv_register_map R5 = ACC"
| "inv_register_map R6 = ACC2"

primrec disassemble' :: "assm \<Rightarrow> mach" where
  "disassemble' (ALdI r k) = LDI (register_map r) k"
| "disassemble' (ALod r1 m r2) = LOD (register_map r1) (register_map r2)"
| "disassemble' (ASto m r1 r2) = STO (register_map r1) (register_map r2)"
| "disassemble' (AMov r1 r2) = MOV (register_map r1) (register_map r2)"
| "disassemble' (AAdd r k) = ADD (register_map r) k"
| "disassemble' (ASub r k) = SUB (register_map r) k"
| "disassemble' (AIJp r) = IJP (register_map r)"
| "disassemble' (AJIZ r k) = JIZ (register_map r) k"
| "disassemble' (AJmp k) = JMP k"
| "disassemble' (AAssert r p) = ASSERT (register_map r) p"

definition disassemble :: "assm list \<Rightarrow> mach list" where
  "disassemble cd = map disassemble' cd"

fun unmap_mem :: "nat \<Rightarrow> memory \<times> nat" where
  "unmap_mem 0 = (Hp, 0)" 
| "unmap_mem (Suc 0) = (Env, 0)"
| "unmap_mem (Suc (Suc 0)) = (Val, 0)"
| "unmap_mem (Suc (Suc (Suc 0))) = (Stk, 0)"
| "unmap_mem (Suc (Suc (Suc (Suc x)))) = (case unmap_mem x of (a, b) \<Rightarrow> (a, Suc b))"

primrec disassemble_state :: "assm_state \<Rightarrow> mach_state" where
  "disassemble_state (AS rs mem pc) = MS (rs \<circ> inv_register_map) (uncurry mem \<circ> unmap_mem) pc"

lemma [simp]: "unmap_mem p = (a, b) \<Longrightarrow> uncurry mem (unmap_mem (4 + p)) = mem a (Suc b)"
  by (simp add: numeral_def split: prod.splits)

lemma [simp]: "unmap_mem (4 * x) = (Hp, x)"
  by (induction x rule: unmap_mem.induct) (simp_all add: numeral_def)

lemma [simp]: "length (disassemble cd) = length cd"
  by (simp add: disassemble_def)

theorem completem [simp]: "cd\<^sub>m \<tturnstile> \<Sigma>\<^sub>m \<leadsto>\<^sub>m \<Sigma>\<^sub>m' \<Longrightarrow> 
  \<exists>cd\<^sub>a \<Sigma>\<^sub>a \<Sigma>\<^sub>a'. cd\<^sub>m = disassemble cd\<^sub>a \<and> disassemble_state \<Sigma>\<^sub>a = \<Sigma>\<^sub>m \<and> 
    disassemble_state \<Sigma>\<^sub>a' = \<Sigma>\<^sub>m' \<and> iter (\<tturnstile> cd\<^sub>a \<leadsto>\<^sub>a) \<Sigma>\<^sub>a \<Sigma>\<^sub>a'"
  by (induction cd\<^sub>m \<Sigma>\<^sub>m \<Sigma>\<^sub>m' rule: evalm.induct) blast

lemma [simp]: "inv_register_map (register_map r) = r"
  by (induction r) simp_all

lemma [simp]: "register_map (inv_register_map r) = r"
  by (induction r) simp_all

lemma [simp]: "((rs \<circ> inv_register_map)(register_map r := k)) = (rs(r := k) \<circ> inv_register_map)"
  by (rule, auto)

lemma [dest]: "inv_register_map r = SP \<Longrightarrow> r = R4"
  by (induction r) simp_all

lemma [simp]: "((\<lambda>r. if r = SP then Suc 0 else 0) \<circ> inv_register_map) = (\<lambda>r. 0)(R4 := Suc 0)"
  by (rule, auto)

lemma [simp]: "uncurry (\<lambda>m. if m = Stk then nmem(0 := 0) else nmem) \<circ> unmap_mem = nmem(3 := 0)"
proof
  fix x
  show "(uncurry (\<lambda>m. if m = Stk then nmem(0 := 0) else nmem) \<circ> unmap_mem) x = (nmem(3 := 0)) x" 
    by (induction x rule: unmap_mem.induct) (simp_all split: prod.splits)
qed

theorem correctm [simp]: "cd\<^sub>a \<tturnstile> \<Sigma>\<^sub>a \<leadsto>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow>
   disassemble cd\<^sub>a \<tturnstile> disassemble_state \<Sigma>\<^sub>a \<leadsto>\<^sub>m disassemble_state \<Sigma>\<^sub>a'"
proof (induction cd\<^sub>a \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: evala.induct)
  case (eva_ldi cd pc r k rs mem)
  hence "disassemble cd ! pc = LDI (register_map r) k" by simp
  hence "disassemble cd \<tturnstile> MS (rs \<circ> inv_register_map) (uncurry mem \<circ> unmap_mem) (Suc pc) \<leadsto>\<^sub>m 
    MS ((rs \<circ> inv_register_map)(register_map r := k)) (uncurry mem \<circ> unmap_mem) pc" 
      by (metis evm_ldi)
  thus ?case by simp
next
  case (eva_lod cd pc r m ptr rs mem)
  thus ?case by simp
next
  case (eva_sto cd pc m ptr r rs mem)
  thus ?case by simp
next
  case (eva_mov cd pc r1 r2 rs mem)
  thus ?case by simp
next
  case (eva_add cd pc r k rs mem)
  thus ?case by simp
next
  case (eva_sub cd pc r k rs mem)
  thus ?case by simp
next
  case (eva_ijp cd pc r rs mem)
  thus ?case by simp
next
  case (eva_jiz_z cd pc r k rs mem)
  thus ?case by simp
next
  case (eva_jiz_s cd pc r pc' rs y mem)
  thus ?case by simp
next
  case (eva_jmp cd pc k rs mem)
  thus ?case by simp
next
  case (eva_assert cd pc r p rs mem)
  thus ?case by simp
qed

theorem correctm_iter [simp]: "iter (\<tturnstile> cd\<^sub>a \<leadsto>\<^sub>a) \<Sigma>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow> 
    iter (\<tturnstile> disassemble cd\<^sub>a \<leadsto>\<^sub>m) (disassemble_state \<Sigma>\<^sub>a) (disassemble_state \<Sigma>\<^sub>a')"
  by (induction \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: iter.induct) (simp, metis correctm iter_append iter_one)

end