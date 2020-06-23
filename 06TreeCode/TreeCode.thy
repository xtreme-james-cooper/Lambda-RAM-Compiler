theory TreeCode
  imports "../00Utils/Environment"
begin

datatype tree_code = 
  TLookup nat
  | TPushCon nat
  | TPushLam "tree_code list"
  | TApply

datatype tclosure = 
  TConst nat
  | TLam "tclosure list" "tree_code list"

type_synonym tree_stack_frame = "tclosure list \<times> tree_code list"

datatype tree_code_state = TS "tclosure list" "tree_stack_frame list"

fun full_block :: "tree_code list \<Rightarrow> nat \<rightharpoonup> nat" where
  "full_block [] n = Some n"
| "full_block (TLookup x # cd) n = full_block cd (Suc n)"
| "full_block (TPushCon k # cd) n = full_block cd (Suc n)"
| "full_block (TPushLam cd' # cd) n = full_block cd (Suc n)"
| "full_block (TApply # cd) 0 = None"
| "full_block (TApply # cd) (Suc n) = full_block cd n"

primrec full_code_closure :: "tree_code \<Rightarrow> bool" where
  "full_code_closure (TLookup x) = True"
| "full_code_closure (TPushCon k) = True"
| "full_code_closure (TPushLam cd) = (full_block cd 0 = Some 1 \<and> list_all full_code_closure cd)"
| "full_code_closure TApply = True"

primrec full_closure :: "tclosure \<Rightarrow> bool" where
  "full_closure (TConst k) = True"
| "full_closure (TLam env cd) = 
    (list_all full_closure env \<and> full_block cd 0 = Some 1 \<and> list_all full_code_closure cd)"

primrec full_frame :: "tree_stack_frame \<Rightarrow> bool" where
  "full_frame (env, cd) = (list_all full_closure env \<and> list_all full_code_closure cd)"

primrec full_state :: "tree_code_state \<Rightarrow> bool" where
  "full_state (TS env s) = (list_all full_closure env \<and> list_all full_frame s)"

inductive evalt :: "tree_code_state \<Rightarrow> tree_code_state \<Rightarrow> bool" (infix "\<leadsto>\<^sub>t" 50) where
  evt_lookup [simp]: "lookup env x = Some v \<Longrightarrow> 
    TS vs ((env, TLookup x # cd) # sfs) \<leadsto>\<^sub>t TS (v # vs) ((env, cd) # sfs)"
| evt_pushcon [simp]: "TS vs ((env, TPushCon k # cd) # sfs) \<leadsto>\<^sub>t TS (TConst k # vs) ((env, cd) # sfs)"
| evt_pushlam [simp]: "TS vs ((env, TPushLam cd' # cd) # sfs) \<leadsto>\<^sub>t 
    TS (TLam env cd' # vs) ((env, cd) # sfs)"
| evt_apply [simp]: "TS (v # TLam env' cd' # vs) ((env, TApply # cd) # sfs) \<leadsto>\<^sub>t 
    TS vs ((v # env', cd') # (env, cd) # sfs)"
| evt_return [simp]: "TS vs ((env, []) # sfs) \<leadsto>\<^sub>t TS vs sfs"

lemma [simp]: "full_block cd1 n = Some m \<Longrightarrow> full_block cd2 m = Some k \<Longrightarrow> 
    full_block (cd1 @ cd2) n = Some k"
  by (induction cd1 n rule: full_block.induct) simp_all

lemma [simp]: "full_block cd 0 = Some (Suc 0) \<Longrightarrow> cd \<noteq> [] \<and> cd \<noteq> [TApply]"
proof (induction cd)
  case (Cons op cd)
  thus ?case by (induction op) simp_all
qed simp_all
  
lemma preservation [simp]: "\<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> full_state \<Sigma> \<Longrightarrow> full_state \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: evalt.induct) auto

theorem determinismt: "\<Sigma> \<leadsto>\<^sub>t \<Sigma>' \<Longrightarrow> \<Sigma> \<leadsto>\<^sub>t \<Sigma>'' \<Longrightarrow> \<Sigma>' = \<Sigma>''"
proof (induction \<Sigma> \<Sigma>' rule: evalt.induct)
  case (evt_lookup env x v vs cd sfs)
  from evt_lookup(2, 1) show ?case 
    by (induction "TS vs ((env, TLookup x # cd) # sfs)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_pushcon vs env k cd sfs)
  thus ?case by (induction "TS vs ((env, TPushCon k # cd) # sfs)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_pushlam vs env cd' cd sfs)
  thus ?case by (induction "TS vs ((env, TPushLam cd' # cd) # sfs)" \<Sigma>'' rule: evalt.induct) simp_all 
next
  case (evt_apply v env' cd' vs env cd sfs)
  thus ?case 
    by (induction "TS (v # TLam env' cd' # vs) ((env, TApply # cd) # sfs)" \<Sigma>'' rule: evalt.induct) 
       simp_all 
next
  case (evt_return vs env sfs)
  thus ?case by (induction "TS vs ((env, []) # sfs)" \<Sigma>'' rule: evalt.induct) simp_all 
qed

end