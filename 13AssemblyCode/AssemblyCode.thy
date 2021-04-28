theory AssemblyCode
  imports Main
begin

datatype memory = Hp | Env | Val | Stk

datatype aregister = HP | EP | VP | SP | ACC | ACC2

datatype assm = 
    ALdI aregister nat
  | ALod aregister memory aregister
  | ASto memory aregister aregister
  | AMov aregister aregister
  | AAdd aregister nat
  | ASub aregister nat
  | AIJp aregister (* indirect jump *)
  | AJIZ aregister nat (* forwards jump *)
  | AJmp nat (* backwards jump *)
  | AAssert aregister "nat \<Rightarrow> bool"

datatype assm_state = AS "aregister \<Rightarrow> nat" "memory \<Rightarrow> nat \<Rightarrow> nat" nat

inductive evala :: "assm list \<Rightarrow> assm_state \<Rightarrow> assm_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>a" 50) where 
  eva_ldi [simp]: "cd ! pc = ALdI r k \<Longrightarrow> cd \<tturnstile> AS rs mem (Suc pc) \<leadsto>\<^sub>a AS (rs(r := k)) mem pc"
| eva_lod [simp]: "cd ! pc = ALod r m ptr \<Longrightarrow> 
    cd \<tturnstile> AS rs mem (Suc pc) \<leadsto>\<^sub>a AS (rs(r := mem m (rs ptr))) mem pc"
| eva_sto [simp]: "cd ! pc = ASto m ptr r \<Longrightarrow> 
    cd \<tturnstile> AS rs mem (Suc pc) \<leadsto>\<^sub>a AS rs (mem(m := (mem m)(rs ptr := rs r))) pc"
| eva_mov [simp]: "cd ! pc = AMov r1 r2 \<Longrightarrow> cd \<tturnstile> AS rs mem (Suc pc) \<leadsto>\<^sub>a AS (rs(r1 := rs r2)) mem pc"
| eva_add [simp]: "cd ! pc = AAdd r k \<Longrightarrow> cd \<tturnstile> AS rs mem (Suc pc) \<leadsto>\<^sub>a AS (rs(r := rs r + k)) mem pc"
| eva_sub [simp]: "cd ! pc = ASub r k \<Longrightarrow> cd \<tturnstile> AS rs mem (Suc pc) \<leadsto>\<^sub>a AS (rs(r := rs r - k)) mem pc"
| eva_ijp [simp]: "cd ! pc = AIJp r \<Longrightarrow> cd \<tturnstile> AS rs mem (Suc pc) \<leadsto>\<^sub>a AS rs mem (rs r)"
| eva_jiz_z [simp]: "cd ! pc = AJIZ r k \<Longrightarrow> rs r = 0 \<Longrightarrow>
    cd \<tturnstile> AS rs mem (Suc pc) \<leadsto>\<^sub>a AS rs mem (pc - k)"
| eva_jiz_s [simp]: "cd ! pc = AJIZ r pc' \<Longrightarrow> rs r = Suc y \<Longrightarrow>
    cd \<tturnstile> AS rs mem (Suc pc) \<leadsto>\<^sub>a AS rs mem pc"
| eva_jmp [simp]: "cd ! pc = AJmp k \<Longrightarrow> cd \<tturnstile> AS rs mem (Suc pc) \<leadsto>\<^sub>a AS rs mem (pc + k)"
| eva_assert [simp]: "cd ! pc = AAssert r p \<Longrightarrow> p (rs r) \<Longrightarrow> 
    cd \<tturnstile> AS rs mem (Suc pc) \<leadsto>\<^sub>a AS rs mem pc"

theorem determinisma: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>a \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction cd \<Sigma> \<Sigma>' rule: evala.induct)
  case (eva_ldi cd pc r k rs mem)
  from eva_ldi(2, 1) show ?case 
    by (induction cd "AS rs mem (Suc pc)" \<Sigma>'' rule: evala.induct) simp_all
next
  case (eva_lod cd pc r m ptr rs mem)
  from eva_lod(2, 1) show ?case 
    by (induction cd "AS rs mem (Suc pc)" \<Sigma>'' rule: evala.induct) simp_all
next
  case (eva_sto cd pc m ptr r rs mem)
  from eva_sto(2, 1) show ?case 
    by (induction cd "AS rs mem (Suc pc)" \<Sigma>'' rule: evala.induct) simp_all
next
  case (eva_mov cd pc r1 r2 rs mem)
  from eva_mov(2, 1) show ?case 
    by (induction cd "AS rs mem (Suc pc)" \<Sigma>'' rule: evala.induct) simp_all
next
  case (eva_add cd pc r k rs mem)
  from eva_add(2, 1) show ?case 
    by (induction cd "AS rs mem (Suc pc)" \<Sigma>'' rule: evala.induct) simp_all
next
  case (eva_sub cd pc r k rs mem)
  from eva_sub(2, 1) show ?case 
    by (induction cd "AS rs mem (Suc pc)" \<Sigma>'' rule: evala.induct) simp_all
next
  case (eva_ijp cd pc r rs mem)
  from eva_ijp(2, 1) show ?case 
    by (induction cd "AS rs mem (Suc pc)" \<Sigma>'' rule: evala.induct) simp_all
next
  case (eva_jiz_z cd pc r pc' rs mem)
  from eva_jiz_z(3, 1, 2) show ?case 
    by (induction cd "AS rs mem (Suc pc)" \<Sigma>'' rule: evala.induct) simp_all
next
  case (eva_jiz_s cd pc r pc' rs y mem)
  from eva_jiz_s(3, 1, 2) show ?case 
    by (induction cd "AS rs mem (Suc pc)" \<Sigma>'' rule: evala.induct) simp_all
next
  case (eva_jmp cd pc k rs mem)
  from eva_jmp(2, 1) show ?case 
    by (induction cd "AS rs mem (Suc pc)" \<Sigma>'' rule: evala.induct) simp_all
next
  case (eva_assert cd pc r p rs mem)
  from eva_assert(3, 1, 2) show ?case 
    by (induction cd "AS rs mem (Suc pc)" \<Sigma>'' rule: evala.induct) simp_all
qed

end