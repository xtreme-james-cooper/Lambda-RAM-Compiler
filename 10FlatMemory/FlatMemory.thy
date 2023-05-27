theory FlatMemory
  imports "../09ChainedEnvironment/ChainedEnvironment"
begin

datatype flat_state = 
  FS "nat heap" "ptr heap" "ptr list" "nat list"

fun get_closure :: "nat heap \<Rightarrow> nat \<Rightarrow> closure\<^sub>v" where
  "get_closure h p = (case hlookup h p of
      0 \<Rightarrow> Lam\<^sub>v (hlookup h (Suc p)) (hlookup h (Suc (Suc p)))
    | Suc x \<Rightarrow> Const\<^sub>v (hlookup h (Suc p)))"

fun flat_lookup :: "ptr heap \<Rightarrow> ptr \<Rightarrow> nat \<rightharpoonup> ptr" where
  "flat_lookup h 0 x = None"
| "flat_lookup h (Suc 0) x = None"
| "flat_lookup h (Suc (Suc p)) 0 = (if even p then Some (hlookup h p) else None)"
| "flat_lookup h (Suc (Suc p)) (Suc x) = (
    if even p then flat_lookup h (hlookup h (Suc p)) x else None)"

inductive evalf :: "code\<^sub>b list \<Rightarrow> flat_state \<Rightarrow> flat_state \<Rightarrow> bool" (infix "\<tturnstile> _ \<leadsto>\<^sub>f" 50) where
  evf_lookup [simp]: "lookup cd pc = Some (Lookup\<^sub>b x) \<Longrightarrow> flat_lookup env p x = Some v \<Longrightarrow> 
    cd \<tturnstile> FS h env vs (Suc pc # p # sfs) \<leadsto>\<^sub>f FS h env (v # vs) (pc # p # sfs)"
| evf_pushcon [simp]: "lookup cd pc = Some (PushCon\<^sub>b k) \<Longrightarrow> halloc_list h [1, k, 0] = (h', v) \<Longrightarrow>
    cd \<tturnstile> FS h env vs (Suc pc # p # sfs) \<leadsto>\<^sub>f FS h' env (v # vs) (pc # p # sfs)"
| evf_pushlam [simp]: "lookup cd pc = Some (PushLam\<^sub>b pc') \<Longrightarrow> 
    halloc_list h [0, p, pc'] = (h', v) \<Longrightarrow> 
      cd \<tturnstile> FS h env vs (Suc pc # p # sfs) \<leadsto>\<^sub>f FS h' env (v # vs) (pc # p # sfs)"
| evf_apply [simp]: "lookup cd pc = Some Apply\<^sub>b \<Longrightarrow> get_closure h v2 = Lam\<^sub>v p' pc' \<Longrightarrow>
    halloc_list env [v1, p'] = (env', p2) \<Longrightarrow> 
      cd \<tturnstile> FS h env (v1 # v2 # vs) (Suc pc # p # sfs) \<leadsto>\<^sub>f 
        FS h env' vs (pc' # Suc (Suc p2) # pc # p # sfs)"
| evf_return [simp]: "lookup cd pc = Some Return\<^sub>b \<Longrightarrow> 
    cd \<tturnstile> FS h env vs (Suc pc # p # sfs) \<leadsto>\<^sub>f FS h env vs sfs"
| evf_jump [simp]: "lookup cd pc = Some Jump\<^sub>b \<Longrightarrow> get_closure h v2 = Lam\<^sub>v p' pc' \<Longrightarrow>
    halloc_list env [v1, p'] = (env', p2) \<Longrightarrow> 
      cd \<tturnstile> FS h env (v1 # v2 # vs) (Suc pc # p # sfs) \<leadsto>\<^sub>f FS h env' vs (pc' # Suc (Suc p2) # sfs)"

theorem determinismf: "cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>f \<Sigma>' \<Longrightarrow> cd \<tturnstile> \<Sigma> \<leadsto>\<^sub>f \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalf.induct)
  case (evf_lookup cd pc x env p v h vs sfs)
  from evf_lookup(3, 1, 2) show ?case 
    by (induction cd "FS h env vs (Suc pc # p # sfs)" \<Sigma>'' rule: evalf.induct) simp_all 
next
  case (evf_pushcon cd pc k h h' v env vs p sfs)
  from evf_pushcon(3, 1, 2) show ?case 
    by (induction cd "FS h env vs (Suc pc # p # sfs)" \<Sigma>'' rule: evalf.induct) simp_all 
next
  case (evf_pushlam cd pc pc' h p h' v env vs sfs)
  from evf_pushlam(3, 1, 2) show ?case 
    by (induction cd "FS h env vs (Suc pc # p # sfs)" \<Sigma>'' rule: evalf.induct) simp_all 
next
  case (evf_apply cd pc h v2 p' pc' env v1 env' p2 vs p sfs)
  from evf_apply(4, 1, 2, 3) show ?case 
    by (induction cd "FS h env (v1 # v2 # vs) (Suc pc # p # sfs)" \<Sigma>'' rule: evalf.induct) simp_all 
next
  case (evf_return cd pc h env vs p sfs)
  from evf_return(2, 1) show ?case 
    by (induction cd "FS h env vs (Suc pc # p # sfs)" \<Sigma>'' rule: evalf.induct) simp_all 
next
  case (evf_jump cd pc h v2 p' pc' env v1 env' p2 vs p sfs)
  from evf_jump(4, 1, 2, 3) show ?case 
    by (induction cd "FS h env (v1 # v2 # vs) (Suc pc # p # sfs)" \<Sigma>'' rule: evalf.induct) simp_all 
qed

end