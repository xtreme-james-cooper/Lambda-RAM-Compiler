theory TailCall
  imports "../00Utils/Environment"
begin

datatype tco_return =
    TCOReturn
  | TCOJump

datatype tco_code = 
  TCOLookup nat
  | TCOPushCon nat
  | TCOPushLam "tco_code list" tco_return nat
  | TCOApply

datatype tco_closure = 
  TCOConst nat
  | TCOLam "tco_closure list" "tco_code list" tco_return

type_synonym tco_stack_frame = "tco_closure list \<times> tco_code list \<times> tco_return"

datatype tco_code_state = TCOS "tco_closure list" "tco_stack_frame list"

inductive evaltco :: "tco_code_state \<Rightarrow> tco_code_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>t\<^sub>c\<^sub>o" 50) where
  evtco_lookup [simp]: "lookup env x = Some v \<Longrightarrow> 
    TCOS vs ((env, TCOLookup x # cd, r) # sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o TCOS (v # vs) ((env, cd, r) # sfs)"
| evtco_pushcon [simp]: "TCOS vs ((env, TCOPushCon k # cd, r) # sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
    TCOS (TCOConst k # vs) ((env, cd, r) # sfs)"
| evtco_pushlam [simp]: "TCOS vs ((env, TCOPushLam cd' r' (length env) # cd, r) # sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
    TCOS (TCOLam env cd' r' # vs) ((env, cd, r) # sfs)"
| evtco_apply [simp]: "TCOS (v # TCOLam env' cd' r' # vs) ((env, TCOApply # cd, r) # sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
    TCOS vs ((v # env', cd', r') # (env, cd, r) # sfs)"
| evtco_return [simp]: "TCOS vs ((env, [], TCOReturn) # sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o TCOS vs sfs"
| evtco_jump [simp]: "TCOS (v # TCOLam env' cd' r' # vs) ((env, [], TCOJump) # sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o 
    TCOS vs ((v # env', cd', r') # sfs)"

theorem determinismt: "\<Sigma> \<leadsto>\<^sub>t\<^sub>c\<^sub>o \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>t\<^sub>c\<^sub>o \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evaltco.induct)
  case (evtco_lookup env x v vs cd r sfs)
  from evtco_lookup(2, 1) show ?case 
    by (induction "TCOS vs ((env, TCOLookup x # cd, r) # sfs)" \<Sigma>'' rule: evaltco.induct) simp_all 
next
  case (evtco_pushcon vs env k cd r sfs)
  thus ?case 
    by (induction "TCOS vs ((env, TCOPushCon k # cd, r) # sfs)" \<Sigma>'' rule: evaltco.induct) simp_all 
next
  case (evtco_pushlam vs env cd' r' cd r sfs)
  thus ?case 
    by (induction "TCOS vs ((env, TCOPushLam cd' r' (length env) # cd, r) # sfs)" \<Sigma>'' 
        rule: evaltco.induct) 
       simp_all 
next
  case (evtco_apply v env' cd' r' vs env cd r sfs)
  thus ?case 
    by (induction "TCOS (v # TCOLam env' cd' r' # vs) ((env, TCOApply # cd, r) # sfs)" \<Sigma>'' 
        rule: evaltco.induct) 
       simp_all 
next
  case (evtco_return vs env sfs)
  thus ?case by (induction "TCOS vs ((env, [], TCOReturn) # sfs)" \<Sigma>'' rule: evaltco.induct) simp_all 
next
  case (evtco_jump v env' cd' r' vs env sfs)
  thus ?case 
    by (induction "TCOS (v # TCOLam env' cd' r' # vs) ((env, [], TCOJump) # sfs)" \<Sigma>''
        rule: evaltco.induct) 
       simp_all 
qed

end