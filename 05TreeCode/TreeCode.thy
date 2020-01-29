theory TreeCode
  imports "../00Utils/Environment"
begin

datatype tree_code = 
  TLookup nat
  | TPushCon nat
  | TPushLam "tree_code list"
  | TApply
  | TReturn
  | TJump

datatype tclosure = 
  TConst nat
  | TLam "tclosure list" "tree_code list"

datatype tree_code_state = TS "tclosure list" "tclosure list list" "tree_code list"

inductive evalt :: "tree_code_state \<Rightarrow> tree_code_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>t" 50) where
  evt_lookup [simp]: "lookup env x = Some v \<Longrightarrow> 
    TS vs (env # envs) (TLookup x # cd) \<leadsto>\<^sub>t TS (v # vs) (env # envs) cd"
| evt_pushcon [simp]: "TS vs envs (TPushCon k # cd) \<leadsto>\<^sub>t TS (TConst k # vs) envs cd"
| evt_pushlam [simp]: "TS vs (env # envs) (TPushLam cd' # cd) \<leadsto>\<^sub>t 
    TS (TLam env cd' # vs) (env # envs) cd"
| evt_apply [simp]: "TS (v # TLam env cd' # vs) envs (TApply # cd) \<leadsto>\<^sub>t 
    TS vs ((v # env) # envs) (cd' @ cd)"
| evt_return [simp]: "TS vs (env # envs) (TReturn # cd) \<leadsto>\<^sub>t TS vs envs cd"
| evt_jump [simp]: "TS (v # TLam env' cd' # vs) (env # envs) (TJump # cd) \<leadsto>\<^sub>t 
    TS vs ((v # env') # envs) (cd' @ cd)"

theorem determinismt: "\<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>t \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalt.induct)
  case (evt_lookup env x v vs envs cd)
  from evt_lookup(2, 1) show ?case 
    by (induction "TS vs (env # envs) (TLookup x # cd)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_pushcon vs envs k cd)
  thus ?case by (induction "TS vs envs (TPushCon k # cd)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_pushlam vs env envs cd' cd)
  thus ?case by (induction "TS vs (env # envs) (TPushLam cd' # cd)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_apply v env cd' vs envs cd)
  thus ?case 
    by (induction "TS (v # TLam env cd' # vs) envs (TApply # cd)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_return vs env envs cd)
  thus ?case by (induction "TS vs (env # envs) (TReturn # cd)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_jump v env' cd' vs env envs cd)
  thus ?case 
    by (induction "TS (v # TLam env' cd' # vs) (env # envs) (TJump # cd)" \<Sigma>'' rule: evalt.induct) 
       simp_all 
qed

end