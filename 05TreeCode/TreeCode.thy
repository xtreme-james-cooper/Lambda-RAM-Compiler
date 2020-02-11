theory TreeCode
  imports "../00Utils/Environment"
begin

datatype tree_code = 
  TLookup nat
  | TPushCon nat
  | TPushLam "tree_code list" nat
  | TApply

datatype tclosure = 
  TConst nat
  | TLam "tclosure list" "tree_code list"

type_synonym tree_stack_frame = "tclosure list \<times> tree_code list"

datatype tree_code_state = TS "tclosure list" "tree_stack_frame list"

inductive evalt :: "tree_code_state \<Rightarrow> tree_code_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>t" 50) where
  evt_lookup [simp]: "lookup env x = Some v \<Longrightarrow> 
    TS vs ((env, TLookup x # cd) # sfs) \<leadsto>\<^sub>t TS (v # vs) ((env, cd) # sfs)"
| evt_pushcon [simp]: "TS vs ((env, TPushCon k # cd) # sfs) \<leadsto>\<^sub>t TS (TConst k # vs) ((env, cd) # sfs)"
| evt_pushlam [simp]: "TS vs ((env, TPushLam cd' (length env) # cd) # sfs) \<leadsto>\<^sub>t 
    TS (TLam env cd' # vs) ((env, cd) # sfs)"
| evt_apply [simp]: "TS (v # TLam env' cd' # vs) ((env, TApply # cd) # sfs) \<leadsto>\<^sub>t 
    TS vs ((v # env', cd') # (env, cd) # sfs)"
| evt_return [simp]: "TS vs ((env, []) # sfs) \<leadsto>\<^sub>t TS vs sfs"

theorem determinismt: "\<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>t \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalt.induct)
  case (evt_lookup env x v vs cd sfs)
  from evt_lookup(2, 1) show ?case 
    by (induction "TS vs ((env, TLookup x # cd) # sfs)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_pushcon vs env k cd sfs)
  thus ?case 
    by (induction "TS vs ((env, TPushCon k # cd) # sfs)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_pushlam vs env cd' cd sfs)
  thus ?case 
    by (induction "TS vs ((env, TPushLam cd' (length env) # cd) # sfs)" \<Sigma>'' rule: evalt.induct) 
       simp_all 
next
  case (evt_apply v env' cd' vs env cd sfs)
  thus ?case 
    by (induction "TS (v # TLam env' cd' # vs) ((env, TApply # cd) # sfs)" \<Sigma>'' 
        rule: evalt.induct) 
       simp_all 
next
  case (evt_return vs env sfs)
  thus ?case by (induction "TS vs ((env, []) # sfs)" \<Sigma>'' rule: evalt.induct) simp_all 
qed

end