theory MachineCode
  imports Main
begin

datatype reg = R1 | R2 | R3 | R4 | R5

datatype mach = 
  LDI reg nat (* $R := k *)
  | LOD reg reg (* $R\<^sub>1 := M[$R\<^sub>2] *)
  | STO reg reg (* M[$R\<^sub>1] := $R\<^sub>2 *)
  | STI reg nat (* M[$R] := k *)
  | MOV reg reg (* $R\<^sub>1 := $R\<^sub>2 *)
  | MVP reg     (* $R := $PC *)
  | ADD reg nat (* $R := $R + k *)
  | SUB reg nat (* $R := $R - k *)
  | JMP reg     (* $PC := $R (indirect jump) *)

datatype mach_state = MS "reg \<Rightarrow> nat" "nat \<Rightarrow> nat" nat

inductive evalm :: "mach list \<Rightarrow> mach_state \<Rightarrow> mach_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>m" 50) where 
  evm_ldi [simp]: "cd ! pc = LDI r k \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS (rs(r := k)) mem pc"
| evm_lod [simp]: "cd ! pc = LOD r ptr \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS (rs(r := mem (rs ptr))) mem pc"
| evm_sto [simp]: "cd ! pc = STO ptr r \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS rs (mem(rs ptr := rs r)) pc"
| evm_sti [simp]: "cd ! pc = STI ptr k \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS rs (mem(rs ptr := k)) pc"
| evm_mov [simp]: "cd ! pc = MOV r1 r2 \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS (rs(r1 := rs r2)) mem pc"
| evm_mvp [simp]: "cd ! pc = MVP r \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS (rs(r := pc)) mem pc"
| evm_add [simp]: "cd ! pc = ADD r k \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS (rs(r := rs r + k)) mem pc"
| evm_sub [simp]: "cd ! pc = SUB r k \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS (rs(r := rs r - k)) mem pc"
| evm_jmp [simp]: "cd ! pc = JMP r \<Longrightarrow> 
    cd \<tturnstile> MS rs mem (Suc pc) \<leadsto>\<^sub>m MS (rs(r := 0)) mem (rs r)"

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
  case (evm_sti cd pc ptr k rs mem)
  from evm_sti(2, 1) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
next
  case (evm_mov cd pc r1 r2 rs mem)
  from evm_mov(2, 1) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
next
  case (evm_mvp cd pc r rs mem)
  from evm_mvp(2, 1) show ?case 
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
  case (evm_jmp cd pc r rs mem)
  from evm_jmp(2, 1) show ?case 
    by (induction cd "MS rs mem (Suc pc)" \<Sigma>'' rule: evalm.induct) simp_all
qed

end