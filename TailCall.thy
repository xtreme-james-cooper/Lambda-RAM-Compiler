theory TailCall
  imports Environment
begin

datatype tail_code = 
  TCLookup nat
  | TCPushCon nat
  | TCPushLam "tail_code list"
  | TCApply
  | TCReturn
  | TCTailCall

datatype tcclosure = 
  TCConst nat
  | TCLam "tcclosure list" "tail_code list"

datatype tail_call_state = TCS "tcclosure list" "tcclosure list list" "tail_code list"

inductive evaltc :: "tail_call_state \<Rightarrow> tail_call_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>t\<^sub>c" 50) where
  evtc_lookup [simp]: "lookup env x = Some v \<Longrightarrow> 
    TCS vs (env # envs) (TCLookup x # cd) \<leadsto>\<^sub>t\<^sub>c TCS (v # vs) (env # envs) cd"
| evtc_pushcon [simp]: "TCS vs envs (TCPushCon k # cd) \<leadsto>\<^sub>t\<^sub>c TCS (TCConst k # vs) envs cd"
| evtc_pushlam [simp]: "TCS vs (env # envs) (TCPushLam cd' # cd) \<leadsto>\<^sub>t\<^sub>c 
    TCS (TCLam env cd' # vs) (env # envs) cd"
| evtc_apply [simp]: "TCS (v # TCLam env cd' # vs) envs (TCApply # cd) \<leadsto>\<^sub>t\<^sub>c
    TCS vs ((v # env) # envs) (cd' @ cd)"
| evtc_return [simp]: "TCS vs (env # envs) (TCReturn # cd) \<leadsto>\<^sub>t\<^sub>c
    TCS vs envs cd"
| evtc_tail_call [simp]: "TCS (v # TCLam env cd' # vs) (env' # envs) (TCTailCall # cd) \<leadsto>\<^sub>t\<^sub>c
    TCS vs ((v # env) # envs) (cd' @ cd)"

theorem determinismtc: "\<Sigma> \<leadsto>\<^sub>t\<^sub>c \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>t\<^sub>c \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evaltc.induct)
  case (evtc_lookup env x v vs envs cd)
  from evtc_lookup(2, 1) show ?case 
    by (induction "TCS vs (env # envs) (TCLookup x # cd)" \<Sigma>'' rule: evaltc.induct) simp_all 
next
  case (evtc_pushcon vs envs k cd)
  thus ?case by (induction "TCS vs envs (TCPushCon k # cd)" \<Sigma>'' rule: evaltc.induct) simp_all 
next
  case (evtc_pushlam vs env envs cd' cd)
  thus ?case 
    by (induction "TCS vs (env # envs) (TCPushLam cd' # cd)" \<Sigma>'' rule: evaltc.induct) simp_all 
next
  case (evtc_apply v env cd' vs envs cd)
  thus ?case 
    by (induction "TCS (v # TCLam env cd' # vs) envs (TCApply # cd)" \<Sigma>'' rule: evaltc.induct) 
        simp_all 
next
  case (evtc_return vs env envs cd)
  thus ?case by (induction "TCS vs (env # envs) (TCReturn # cd)" \<Sigma>'' rule: evaltc.induct) simp_all
next
  case (evtc_tail_call v env cd' vs env' envs cd)
  thus ?case 
    by (induction "TCS (v # TCLam env cd' # vs) (env' # envs) (TCTailCall # cd)" \<Sigma>'' 
        rule: evaltc.induct) simp_all
qed

end