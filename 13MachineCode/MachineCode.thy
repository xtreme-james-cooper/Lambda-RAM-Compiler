theory MachineCode
  imports Main
begin

datatype reg = R1 | R2 | R3 | R4 | R5

datatype mach = 
  MOV reg reg    (* $R\<^sub>1 := $R\<^sub>2 *)
  | LOD reg reg  (* $R\<^sub>1 := M[$R\<^sub>2] *)
  | LODI reg nat (* $R := k *)
  | STO reg reg  (* M[$R\<^sub>1] := $R\<^sub>2 *)
  | STOI reg nat (* M[$R] := k *)
  | ADD reg reg  (* $R\<^sub>1 := $R\<^sub>1 + $R\<^sub>2 *)
  | ADDI reg nat (* $R := $R + k *)
  | SUB reg reg  (* $R\<^sub>1 := $R\<^sub>1 - $R\<^sub>2 *)
  | SUBI reg nat (* $R := $R - k *)
  | JMP reg      (* $PC := $R (indirect jump) *)
  | JMPI nat     (* $PC := k (direct jump) *)

datatype mach_state = MS "reg \<Rightarrow> nat" "nat \<Rightarrow> nat" nat

primrec evalm_step :: "mach \<Rightarrow> (reg \<Rightarrow> nat) \<Rightarrow> (nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> mach_state" where
  "evalm_step (MOV r r') rs mem pc = MS (rs(r := rs r')) mem pc"
| "evalm_step (LOD r r') rs mem pc = MS (rs(r := mem (rs r'))) mem pc"
| "evalm_step (LODI r k) rs mem pc = MS (rs(r := k)) mem pc"
| "evalm_step (STO r r') rs mem pc = MS rs (mem(rs r := rs r')) pc"
| "evalm_step (STOI r k) rs mem pc = MS rs (mem(rs r := k)) pc"
| "evalm_step (ADD r r') rs mem pc = MS (rs(r := rs r + rs r')) mem pc"
| "evalm_step (ADDI r k) rs mem pc = MS (rs(r := rs r + k)) mem pc"
| "evalm_step (SUB r r') rs mem pc = MS (rs(r := rs r - rs r')) mem pc"
| "evalm_step (SUBI r k) rs mem pc = MS (rs(r := rs r - k)) mem pc"
| "evalm_step (JMP r)    rs mem pc = MS (rs(r := 0)) mem (rs r)"
| "evalm_step (JMPI k)   rs mem pc = MS rs mem k"

fun evalm :: "mach list \<Rightarrow> mach_state \<rightharpoonup> mach_state" where 
  "evalm cd (MS rs mem 0) = None"
| "evalm cd (MS rs mem (Suc pc)) = Some (evalm_step (cd ! pc) rs mem pc)"

abbreviation evalm_relation :: "mach list \<Rightarrow> mach_state \<Rightarrow> mach_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>m" 50) where 
  "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>m \<Sigma>' \<equiv> (evalm cd \<Sigma> = Some \<Sigma>')"

theorem determinismm: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>m \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>m \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
  by simp

end