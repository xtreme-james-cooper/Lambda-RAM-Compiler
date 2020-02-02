theory TreeCode
  imports "../00Utils/Environment"
begin

datatype tree_return =
    TReturn
  | TJump

datatype tree_code = 
  TLookup nat
  | TPushCon nat
  | TPushLam "tree_code list" tree_return
  | TApply

datatype tclosure = 
  TConst nat
  | TLam "tclosure list" "tree_code list" tree_return

type_synonym tree_stack_frame = "tclosure list \<times> tree_code list \<times> tree_return"

datatype tree_code_state = TS "tclosure list" "tree_stack_frame list"

inductive evalt :: "tree_code_state \<Rightarrow> tree_code_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>t" 50) where
  evt_lookup [simp]: "lookup env x = Some v \<Longrightarrow> 
    TS vs ((env, TLookup x # cd, r) # sfs) \<leadsto>\<^sub>t TS (v # vs) ((env, cd, r) # sfs)"
| evt_pushcon [simp]: "TS vs ((env, TPushCon k # cd, r) # sfs) \<leadsto>\<^sub>t 
    TS (TConst k # vs) ((env, cd, r) # sfs)"
| evt_pushlam [simp]: "TS vs ((env, TPushLam cd' r' # cd, r) # sfs) \<leadsto>\<^sub>t 
    TS (TLam env cd' r' # vs) ((env, cd, r) # sfs)"
| evt_apply [simp]: "TS (v # TLam env cd' r' # vs) ((env, TApply # cd, r) # sfs) \<leadsto>\<^sub>t 
    TS vs ((v # env, cd', r') # (env, cd, r) # sfs)"
| evt_return [simp]: "TS vs ((env, [], TReturn) # sfs) \<leadsto>\<^sub>t TS vs sfs"
| evt_jump [simp]: "TS (v # TLam env' cd' r' # vs) ((env, [], TJump) # sfs) \<leadsto>\<^sub>t 
    TS vs ((v # env', cd', r') # sfs)"

theorem determinismt: "\<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>t \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalt.induct)
  case (evt_lookup env x v vs cd r sfs)
  from evt_lookup(2, 1) show ?case 
    by (induction "TS vs ((env, TLookup x # cd, r) # sfs)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_pushcon vs env k cd r sfs)
  thus ?case 
    by (induction "TS vs ((env, TPushCon k # cd, r) # sfs)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_pushlam vs env cd' r' cd r sfs)
  thus ?case 
    by (induction "TS vs ((env, TPushLam cd' r' # cd, r) # sfs)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_apply v env cd' r' vs cd r sfs)
  thus ?case 
    by (induction "TS (v # TLam env cd' r' # vs) ((env, TApply # cd, r) # sfs)" \<Sigma>'' 
        rule: evalt.induct) 
       simp_all 
next
  case (evt_return vs env sfs)
  thus ?case by (induction "TS vs ((env, [], TReturn) # sfs)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_jump v env' cd' r' vs env sfs)
  thus ?case 
    by (induction "TS (v # TLam env' cd' r' # vs) ((env, [], TJump) # sfs)" \<Sigma>'' rule: evalt.induct) 
       simp_all 
qed

end