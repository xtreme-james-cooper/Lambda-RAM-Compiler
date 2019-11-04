theory ByteCode
  imports Environment Iteration
begin

datatype byte_code = 
  BLookup nat
  | BPushCon nat
  | BPushLam nat
  | BEnter
  | BApply
  | BReturn

datatype bclosure = 
  BConst nat
  | BLam "bclosure list" nat

datatype byte_code_state = 
  BS "bclosure list" "bclosure list list" "nat list" (code: "byte_code list")

inductive evalb :: "byte_code_state \<Rightarrow> byte_code_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>b" 50) where
  evb_lookup [simp]: "cd ! pc = BLookup x \<Longrightarrow> lookup env x = Some v \<Longrightarrow> 
    BS vs (env # envs) (Suc pc # pcs) cd \<leadsto>\<^sub>b BS (v # vs) envs (pc # pcs) cd"
| evb_pushcon [simp]: "cd ! pc = BPushCon k \<Longrightarrow> 
    BS vs (env # envs) (Suc pc # pcs) cd \<leadsto>\<^sub>b BS (BConst k # vs) envs (pc # pcs) cd"
| evb_pushlam [simp]: "cd ! pc = BPushLam pc' \<Longrightarrow> 
    BS vs (env # envs) (Suc pc # pcs) cd \<leadsto>\<^sub>b BS (BLam env pc' # vs) envs (pc # pcs) cd"
| evb_enter [simp]: "cd ! pc = BEnter \<Longrightarrow> 
    BS vs (env # envs) (Suc pc # pcs) cd \<leadsto>\<^sub>b BS vs (env # env # envs) (pc # pcs) cd"
| evb_apply [simp]: "cd ! pc = BApply \<Longrightarrow> 
    BS (v # BLam env pc' # vs) envs (Suc pc # pcs) cd \<leadsto>\<^sub>b 
      BS vs ((v # env) # envs) (pc' # pc # pcs) cd"
| evb_return [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    BS vs envs (Suc pc # pcs) cd \<leadsto>\<^sub>b BS vs envs pcs cd"

theorem determinismb: "\<Sigma> \<leadsto>\<^sub>b \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>b \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalb.induct)
  case (evb_lookup cd pc x env v vs envs pcs)
  from evb_lookup(3, 1, 2) show ?case 
    by (induction "BS vs (env # envs) (Suc pc # pcs) cd" \<Sigma>'' rule: evalb.induct) simp_all 
next
  case (evb_pushcon cd pc k vs env envs pcs)
  from evb_pushcon(2, 1) show ?case 
    by (induction "BS vs (env # envs) (Suc pc # pcs) cd" \<Sigma>'' rule: evalb.induct) simp_all 
next
  case (evb_pushlam cd pc pc' vs env envs pcs)
  from evb_pushlam(2, 1) show ?case 
    by (induction "BS vs (env # envs) (Suc pc # pcs) cd" \<Sigma>'' rule: evalb.induct) simp_all 
next
  case (evb_enter cd pc vs env envs pcs)
  from evb_enter(2, 1) show ?case 
    by (induction "BS vs (env # envs) (Suc pc # pcs) cd" \<Sigma>'' rule: evalb.induct) simp_all 
next
  case (evb_apply cd pc v env pc' vs envs pcs)
  from evb_apply(2, 1) show ?case 
    by (induction "BS (v # BLam env pc' # vs) envs (Suc pc # pcs) cd" \<Sigma>'' rule: evalb.induct) 
       simp_all 
next
  case (evb_return cd pc vs envs pcs)
  from evb_return(2, 1) show ?case 
    by (induction "BS vs envs (Suc pc # pcs) cd" \<Sigma>'' rule: evalb.induct) simp_all 
qed

lemma [simp]: "\<Sigma> \<leadsto>\<^sub>b \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: evalb.induct) simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>b) \<Sigma> \<Sigma>' \<Longrightarrow> code \<Sigma> = code \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: iter.induct) simp_all

end