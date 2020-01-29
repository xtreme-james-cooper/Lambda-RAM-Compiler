theory HeapMemory
  imports "../06FlatCode/ByteCode" Heap
begin

datatype hclosure = 
  HConst nat
  | HLam "ptr list" nat

datatype heap_state = 
  HS "hclosure heap" "ptr list" "ptr list list" "nat list" (code: "byte_code list")

inductive evalh :: "heap_state \<Rightarrow> heap_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>h" 50) where
  evh_lookup [simp]: "cd ! pc = BLookup x \<Longrightarrow> lookup env x = Some v \<Longrightarrow> 
    HS h vs (env # envs) (Suc pc # pcs) cd \<leadsto>\<^sub>h HS h (v # vs) (env # envs) (pc # pcs) cd"
| evh_pushcon [simp]: "cd ! pc = BPushCon k \<Longrightarrow> halloc h (HConst k) = (h', v) \<Longrightarrow>
    HS h vs envs (Suc pc # pcs) cd \<leadsto>\<^sub>h HS h' (v # vs) envs (pc # pcs) cd"
| evh_pushlam [simp]: "cd ! pc = BPushLam pc' \<Longrightarrow> halloc h (HLam env pc') = (h', v) \<Longrightarrow>
    HS h vs (env # envs) (Suc pc # pcs) cd \<leadsto>\<^sub>h HS h' (v # vs) (env # envs) (pc # pcs) cd"
| evh_apply [simp]: "cd ! pc = BApply \<Longrightarrow> hlookup h v2 = HLam env pc' \<Longrightarrow>
    HS h (v1 # v2 # vs) envs (Suc pc # pcs) cd \<leadsto>\<^sub>h
      HS h vs ((v1 # env) # envs) (pc' # pc # pcs) cd"
| evh_return [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    HS h vs (env # envs) (Suc pc # pcs) cd \<leadsto>\<^sub>h HS h vs envs pcs cd"
| evh_jump [simp]: "cd ! pc = BJump \<Longrightarrow> hlookup h v2 = HLam env' pc' \<Longrightarrow>
    HS h (v1 # v2 # vs) (env # envs) (Suc pc # pcs) cd \<leadsto>\<^sub>h 
      HS h vs ((v1 # env') # envs) (pc' # pcs) cd"

theorem determinismh: "\<Sigma> \<leadsto>\<^sub>h \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>h \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalh.induct)
  case (evh_lookup cd pc x env v h vs envs pcs)
  from evh_lookup(3, 1, 2) show ?case 
    by (induction "HS h vs (env # envs) (Suc pc # pcs) cd" \<Sigma>'' rule: evalh.induct) simp_all 
next
  case (evh_pushcon cd pc k h h' v vs envs pcs)
  from evh_pushcon(3, 1, 2) show ?case 
    by (induction "HS h vs envs (Suc pc # pcs) cd" \<Sigma>'' rule: evalh.induct) simp_all 
next
  case (evh_pushlam cd pc pc' h env h' v vs envs pcs)
  from evh_pushlam(3, 1, 2) show ?case 
    by (induction "HS h vs (env # envs) (Suc pc # pcs) cd" \<Sigma>'' rule: evalh.induct) simp_all 
next
  case (evh_apply cd pc h v2 env pc' v1 vs envs pcs)
  from evh_apply(3, 1, 2) show ?case 
    by (induction "HS h (v1 # v2 # vs) envs (Suc pc # pcs) cd" \<Sigma>'' rule: evalh.induct) 
       simp_all 
next
  case (evh_return cd pc h vs env envs pcs)
  from evh_return(2, 1) show ?case 
    by (induction "HS h vs (env # envs) (Suc pc # pcs) cd" \<Sigma>'' rule: evalh.induct) simp_all 
next
  case (evh_jump cd pc h v2 env' pc' v1 vs env envs pcs)
  from evh_jump(3, 1, 2) show ?case 
    by (induction "HS h (v1 # v2 # vs) (env # envs) (Suc pc # pcs) cd" \<Sigma>'' rule: evalh.induct) 
       simp_all 
qed

lemma [simp]: "\<Sigma> \<leadsto>\<^sub>h \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: evalh.induct) simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>h) \<Sigma> \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

end