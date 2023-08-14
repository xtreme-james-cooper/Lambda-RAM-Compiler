theory Disassemble
  imports MachineCode "../13AssemblyCode/AssemblyCode"
begin

primrec register_map :: "memseg \<Rightarrow> reg" where
  "register_map Hp = R1"
| "register_map Env = R2"
| "register_map Vals = R3"
| "register_map Stk = R4"
| "register_map Acc = R5"

fun disassemble' :: "assm \<Rightarrow> mach" where
  "disassemble' (AMov (Reg r) (Reg r')) = MOV (register_map r) (register_map r')"
| "disassemble' (AMov (Reg r) (Con k)) = LODI (register_map r) k"
| "disassemble' (AMov (Reg r) (Mem r')) = LOD (register_map r) (register_map r')"
| "disassemble' (AMov (Con k) x) = undefined"
| "disassemble' (AMov (Mem r) (Reg r')) = STO (register_map r) (register_map r')"
| "disassemble' (AMov (Mem r) (Con k)) = STOI (register_map r) k"
| "disassemble' (AMov (Mem r) (Mem r')) = undefined"
| "disassemble' (ASub r (Reg r')) = SUB (register_map r) (register_map r')"
| "disassemble' (ASub r (Con k)) = SUBI (register_map r) (4 * k)"
| "disassemble' (ASub r (Mem r')) = undefined"
| "disassemble' (AAdd r (Reg r')) = ADD (register_map r) (register_map r')"
| "disassemble' (AAdd r (Con k)) = ADDI (register_map r) (4 * k)"
| "disassemble' (AAdd r (Mem r')) = undefined"
| "disassemble' (AJmp (Reg r)) = JMP (register_map r)"
| "disassemble' (AJmp (Con k)) = JMPI k"
| "disassemble' (AJmp (Mem r)) = undefined"

definition disassemble :: "assm list \<Rightarrow> mach list" where
  "disassemble cd = map disassemble' cd"

fun unmap_mem' :: "nat \<Rightarrow> memseg \<times> nat" where
  "unmap_mem' 0 = (Hp, 0)" 
| "unmap_mem' (Suc 0) = (Env, 0)"
| "unmap_mem' (Suc (Suc 0)) = (Vals, 0)"
| "unmap_mem' (Suc (Suc (Suc 0))) = (Stk, 0)"
| "unmap_mem' (Suc (Suc (Suc (Suc x)))) = (case unmap_mem' x of (a, b) \<Rightarrow> (a, Suc b))"

primrec register_offset :: "memseg \<Rightarrow> nat" where
  "register_offset Hp = 0"
| "register_offset Env = 1"
| "register_offset Vals = 2"
| "register_offset Stk = 3"
| "register_offset Acc = 4"

primrec pseudoreg_map :: "memseg \<times> nat \<Rightarrow> nat" where
  "pseudoreg_map (r, x) = (if r = Acc then x else 4 * x + register_offset r)"

definition unmap_mem :: "(memseg \<times> nat \<Rightarrow> memseg \<times> nat) \<Rightarrow> nat \<Rightarrow> nat" where
  "unmap_mem m \<equiv> pseudoreg_map \<circ> m \<circ> unmap_mem'"

primrec inv_register_map :: "reg \<Rightarrow> memseg" where
  "inv_register_map R1 = Hp"
| "inv_register_map R2 = Env"
| "inv_register_map R3 = Vals"
| "inv_register_map R4 = Stk"
| "inv_register_map R5 = Acc"

abbreviation dissassemble_regs :: "(memseg \<Rightarrow> memseg \<times> nat) \<Rightarrow> reg \<Rightarrow> nat" where
  "dissassemble_regs rs \<equiv> pseudoreg_map \<circ> rs \<circ> inv_register_map"

primrec disassemble_state :: "assm_state \<Rightarrow> mach_state" where
  "disassemble_state (S\<^sub>a mem rs pc) = MS (dissassemble_regs rs) (unmap_mem mem) pc"

lemma [simp]: "length (disassemble cd) = length cd"
  by (simp add: disassemble_def)

lemma [simp]: "inv_register_map (register_map r) = r"
  by (induction r) simp_all

lemma [simp]: "register_map (inv_register_map r) = r"
  by (induction r) simp_all

lemma [dest]: "inv_register_map r = Acc \<Longrightarrow> r = R5"
  by (induction r) simp_all

lemma [simp]: "unmap_mem' (4 * y) = (Hp, y)" 
  by (induction y) (simp_all add: numeral_def)

lemma [simp]: "unmap_mem' (Suc (4 * y)) = (Env, y)" 
  by (induction y) (simp_all add: numeral_def)

lemma [simp]: "unmap_mem' (Suc (Suc (4 * y))) = (Vals, y)" 
  by (induction y) (simp_all add: numeral_def)

lemma [simp]: "unmap_mem' (4 * y + 3) = (Stk, y)" 
  by (induction y) (simp_all add: numeral_def)

lemma [dest]: "unmap_mem' x = (Acc, y) \<Longrightarrow> False"
  by (induction x arbitrary: y rule: unmap_mem'.induct) (auto split: prod.splits)

lemma [simp]: "pseudoreg_map (unmap_mem' x) = x"
  by (induction x rule: unmap_mem'.induct) (auto split: prod.splits)

lemma [simp]: "x \<noteq> Acc \<Longrightarrow> unmap_mem' (4 * y + register_offset x) = (x, y)"
  by (induction x) simp_all

lemma [simp]: "fst x \<noteq> Acc \<Longrightarrow> unmap_mem' (pseudoreg_map x) = x"
  by (cases x) simp_all

lemma lookup_disassemble [simp]: "lookup cd pc = Some op \<Longrightarrow> disassemble cd ! pc = disassemble' op"
proof (induction cd)
  case (Cons op cd)
  thus ?case by (induction pc) (simp_all add: disassemble_def)
qed simp_all

lemma [simp]: "dissassemble_regs (ps(Acc := (Acc, 0))) = (dissassemble_regs ps)(R5 := 0)"
  by rule auto

lemma [simp]: "dissassemble_regs (ps(r := ps r')) = 
    (dissassemble_regs ps)(register_map r := dissassemble_regs ps (register_map r'))"
  by rule auto

lemma [simp]: "dissassemble_regs (ps(r := (Acc, k))) = (dissassemble_regs ps)(register_map r := k)"
  by rule auto

lemma [simp]: "fst (ps r') \<noteq> Acc \<Longrightarrow> (dissassemble_regs (ps(r := mem (ps r')))) = 
    ((dissassemble_regs ps)
      (register_map r := unmap_mem mem (dissassemble_regs ps (register_map r'))))"
  by rule (auto simp add: unmap_mem_def)

lemma unmap_mem_with_reg [simp]: "fst r \<noteq> Acc \<Longrightarrow> 
    ((unmap_mem mem)(pseudoreg_map r := pseudoreg_map r')) = unmap_mem (mem(r := r'))"
  by rule (auto simp add: unmap_mem_def)

lemma unmap_mem_with_const: "fst r \<noteq> Acc \<Longrightarrow>
    ((unmap_mem mem)(pseudoreg_map r := n)) = unmap_mem (mem(r := (Acc, n)))"
  by rule (auto simp add: unmap_mem_def)

lemma [simp]: "r' \<noteq> Acc \<Longrightarrow> y \<ge> k \<Longrightarrow> 
  ((dissassemble_regs ps)(register_map r := 4 * y + register_offset r' - 4 * k)) = 
    (dissassemble_regs (ps(r := (r', y - k))))"
  by rule auto

lemma [simp]: "r' \<noteq> Acc \<Longrightarrow> 
  ((dissassemble_regs ps)(register_map r := 4 * y + register_offset r' + 4 * k)) = 
    (dissassemble_regs (ps(r := (r', y + k))))"
  by rule auto

lemma [simp]: "ps r = (Acc, v) \<Longrightarrow> ps r' = (Acc, v') \<Longrightarrow> v > v' \<Longrightarrow>
    (dissassemble_regs ps)(register_map r := v - v') = dissassemble_regs (ps(r := (Acc, v - v')))"
  by rule auto

theorem correctm [simp]: "cd\<^sub>a \<tturnstile> \<Sigma>\<^sub>a \<leadsto>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow>
  disassemble cd\<^sub>a \<tturnstile> disassemble_state \<Sigma>\<^sub>a \<leadsto>\<^sub>m disassemble_state \<Sigma>\<^sub>a'"
proof (induction cd\<^sub>a \<Sigma>\<^sub>a rule: eval\<^sub>a.induct)
  case (2 cd\<^sub>a mem ps pc)
  thus ?case 
  proof (cases "lookup cd\<^sub>a pc")
    case (Some op)
    with 2 show ?thesis 
    proof (induction mem ps pc op rule: assm_step.induct)
      case (6 mem ps pc r r')
      thus ?case by (auto simp add: unmap_mem_with_const split: if_splits)
    qed (auto split: prod.splits if_splits)
  qed simp_all
qed simp_all

theorem correctm_iter [simp]: "iter (\<tturnstile> cd\<^sub>a \<leadsto>\<^sub>a) \<Sigma>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow> 
    iter (\<tturnstile> disassemble cd\<^sub>a \<leadsto>\<^sub>m) (disassemble_state \<Sigma>\<^sub>a) (disassemble_state \<Sigma>\<^sub>a')"
  by (induction \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: iter.induct) simp_all

lemma [simp]: "dissassemble_regs (case_memseg (Hp, 0) (Env, 0) (Vals, 0) (Stk, 2) (Acc, 0)) = 
    case_reg 0 (Suc 0) 2 11 0"
  by (auto split: memseg.splits reg.splits)

lemma [simp]: "dissassemble_regs (case_memseg (Hp, x) (Env, y) (Vals, Suc 0) (Stk, 0) (Acc, 0)) =
    case_reg (4 * x) (Suc (4 * y)) 6 3 0"
  by (auto split: memseg.splits reg.splits)

lemma [dest]: "unmap_mem' x = (r, y) \<Longrightarrow> x = 4 * y + register_offset r"
  by (induction x arbitrary: y rule: unmap_mem'.induct) (simp_all split: prod.splits)

lemma [simp]: "unmap_mem (case_prod (case_memseg (\<lambda>x. (Acc, 0)) (\<lambda>x. (Acc, 0)) (\<lambda>x. (Acc, 0)) 
    ((\<lambda>x. (Acc, 0)) (0 := (Acc, 0), Suc 0 := (Env, 0))) undefined)) = (\<lambda>x. 0)(7 := 1)"
  by rule (auto simp add: numeral_def unmap_mem_def split: prod.splits memseg.splits)

end