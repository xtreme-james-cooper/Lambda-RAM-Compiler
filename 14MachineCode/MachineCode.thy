theory MachineCode
  imports Main
begin

datatype register = R1 | R2 | R3 | R4 | R5 | R6

datatype mach = 
    LDI register nat      (* $R := k *)
  | LOD register register (* $R\<^sub>1 := M[$R\<^sub>2] *)
  | STO register register (* M[$R\<^sub>1] := $R\<^sub>2 *)
  | MOV register register (* $R\<^sub>1 := $R\<^sub>2 *)
  | ADD register nat      (* $R := $R + k *)
  | SUB register nat      (* $R := $R - k *)
  | IJP register          (* $PC := $R (indirect jump) *)
  | JIZ register nat      (* $R = 0 \<longrightarrow> $PC = $PC + k, $R \<noteq> 0 \<longrightarrow> NOOP (conditional forward jump) *)
  | JMP nat               (* $PC := $PC - k (backwards jump) *)

  | ASSERT register "nat \<Rightarrow> bool" (* P($R) \<longrightarrow> NOOP, \<not>P($R) \<longrightarrow> abort *)

datatype mach_state = MS "register \<Rightarrow> nat" "nat \<Rightarrow> nat" nat

inductive evalm :: "mach list \<Rightarrow> mach_state \<Rightarrow> mach_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>m" 50) where 
  evm_ldi [simp]: "cd ! pc = LDI r k \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS (rs(r := k)) mem pc"
| evm_lod [simp]: "cd ! pc = LOD r ptr \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS (rs(r := mem (rs ptr))) mem pc"
| evm_sto [simp]: "cd ! pc = STO ptr r \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS rs (mem(rs ptr := rs r)) pc"
| evm_mov [simp]: "cd ! pc = MOV r1 r2 \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS (rs(r1 := rs r2)) mem pc"
| evm_add [simp]: "cd ! pc = ADD r k \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS (rs(r := rs r + k)) mem pc"
| evm_sub [simp]: "cd ! pc = SUB r k \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS (rs(r := rs r - k)) mem pc"
| evm_ijp [simp]: "cd ! pc = IJP r \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS rs mem (rs r)"
| evm_jiz_z [simp]: "cd ! pc = JIZ r k \<Longrightarrow> rs r = 0 \<Longrightarrow>
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS rs mem (pc - k)"
| evm_jiz_s [simp]: "cd ! pc = JIZ r pc' \<Longrightarrow> rs r = Suc y \<Longrightarrow>
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS rs mem pc"
| evm_jmp [simp]: "cd ! pc = JMP k \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS rs mem (pc + k)"
| evm_assert [simp]: "cd ! pc = ASSERT r p \<Longrightarrow> p (rs r) \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS rs mem pc"

theorem determinismm: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>m \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>m \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction cd \<Sigma> \<Sigma>' rule: evalm.induct)
  case (evm_ldi cd pc r k rs mem)
  from evm_ldi(2, 1) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
next
  case (evm_lod cd pc r ptr rs mem)
  from evm_lod(2, 1) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
next
  case (evm_sto cd pc ptr r rs mem)
  from evm_sto(2, 1) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
next
  case (evm_mov cd pc r1 r2 rs mem)
  from evm_mov(2, 1) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
next
  case (evm_add cd pc r k rs mem)
  from evm_add(2, 1) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
next
  case (evm_sub cd pc r k rs mem)
  from evm_sub(2, 1) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
next
  case (evm_ijp cd pc r rs mem)
  from evm_ijp(2, 1) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
next
  case (evm_jiz_z cd pc r pc' rs mem)
  from evm_jiz_z(3, 1, 2) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
next
  case (evm_jiz_s cd pc r pc' rs y mem)
  from evm_jiz_s(3, 1, 2) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
next
  case (evm_jmp cd pc k rs mem)
  from evm_jmp(2, 1) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
next
  case (evm_assert cd pc r p rs mem)
  from evm_assert(3, 1, 2) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
qed

end