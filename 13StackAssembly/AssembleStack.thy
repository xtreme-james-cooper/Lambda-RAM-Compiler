theory AssembleStack
  imports StackAssembly "../12UnstructuredMemory/UnstructuredMemory" "../00Utils/Utils"
begin

primrec assemble_stack_len :: "byte_code \<Rightarrow> nat" where
  "assemble_stack_len (BLookup x) = 1"
| "assemble_stack_len (BPushCon k) = 5"
| "assemble_stack_len (BPushLam pc) = 1"
| "assemble_stack_len BApply = 1"
| "assemble_stack_len BReturn = 1"
| "assemble_stack_len BJump = 1"

primrec assemble_stack_op :: "(nat \<Rightarrow> nat) \<Rightarrow> byte_code \<Rightarrow> sassm_code list" where
  "assemble_stack_op mp (BLookup x) = [undefined]"
| "assemble_stack_op mp (BPushCon k) = [
    SAPush Hp (Con 0), 
    SAPush Hp (Con k), 
    SAPush Hp (Con 0), 
    SAPush Vals Acc, 
    SAMov Hp]"
| "assemble_stack_op mp (BPushLam pc) = [undefined]"
| "assemble_stack_op mp BApply = [undefined]"
| "assemble_stack_op mp BReturn = [undefined]"
| "assemble_stack_op mp BJump = [undefined]"

(*   evu_lookup [simp]: "cd ! pc = BLookup x \<Longrightarrow> unstr_lookup e (sh (sp - 1)) x = Some y \<Longrightarrow>
    cd \<tturnstile> US h hp e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u US h hp e ep (vs(vp := y)) (Suc vp) sh sp pc"
| evu_pushlam [simp]: "cd ! pc = BPushLam pc' \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u 
      US (h(hp := 1, Suc hp := sh (sp - 1), Suc (Suc hp) := pc')) (3 + hp) e ep 
        (vs(vp := hp)) (Suc vp) sh sp pc"
| evu_apply [simp]: "cd ! pc = BApply \<Longrightarrow> h (vs vp) = Suc x \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs (Suc (Suc vp)) sh sp (Suc pc) \<leadsto>\<^sub>u 
      US h hp (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (2 + ep) vs vp
        (sh(sp := pc, Suc sp := Suc (Suc ep))) (2 + sp) (h (Suc (Suc (vs vp))))"
| evu_return_normal [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh (Suc (Suc sp)) (Suc pc) \<leadsto>\<^sub>u US h hp e ep vs vp sh sp (sh sp)"
| evu_return_end [simp]: "cd ! pc = BReturn \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs vp sh (Suc 0) (Suc pc) \<leadsto>\<^sub>u US h hp e ep vs vp sh 0 0"
| evu_jump [simp]: "cd ! pc = BJump \<Longrightarrow> h (vs vp) = Suc x \<Longrightarrow> 
    cd \<tturnstile> US h hp e ep vs (Suc (Suc vp)) sh sp (Suc pc) \<leadsto>\<^sub>u 
      US h hp (e(ep := vs (Suc vp), Suc ep := h (Suc (vs vp)))) (2 + ep) vs vp
        (sh(sp - 1 := Suc (Suc ep))) sp (h (Suc (Suc (vs vp))))" *)

abbreviation assemble_extend_map :: "(nat \<Rightarrow> nat) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat" where
  "assemble_extend_map mp b lop x \<equiv> (if x < b then mp x else mp x + lop - 1)"

fun assembly_map :: "byte_code list \<Rightarrow> nat \<Rightarrow> nat" where
  "assembly_map [] x = x"
| "assembly_map (op # cd) 0 = assemble_stack_len op - 1"
| "assembly_map (op # cd) (Suc x) = assemble_stack_len op + assembly_map cd x"

definition assemble_stack_code :: "byte_code list \<Rightarrow> sassm_code list" where
  "assemble_stack_code cd = concat (map (assemble_stack_op (assembly_map cd)) cd)"

primrec assemble_state :: "(nat \<Rightarrow> nat) \<Rightarrow> unstr_state \<Rightarrow> sassm_state" where
  "assemble_state mp (US h hp e ep vs vp sh sp pc) = 
    SAS (\<lambda>m. case m of Hp \<Rightarrow> h | Env \<Rightarrow> e | Vals \<Rightarrow> vs | Stk \<Rightarrow> sh) 
      (\<lambda>m. case m of Hp \<Rightarrow> hp | Env \<Rightarrow> ep | Vals \<Rightarrow> vp | Stk \<Rightarrow> sp) (SOME x. True) (mp pc)"

lemma [simp]: "assemble_stack_len op = length (assemble_stack_op mp op)"
  by (induction op) simp_all

theorem completesa [simp]: "
  assemble_stack_code cd\<^sub>b \<tturnstile> assemble_state (assembly_map cd\<^sub>b) \<Sigma>\<^sub>u \<leadsto>\<^sub>s\<^sub>a \<Sigma>\<^sub>s\<^sub>a' \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>u'. iter (\<tturnstile> assemble_stack_code cd\<^sub>b \<leadsto>\<^sub>s\<^sub>a) \<Sigma>\<^sub>s\<^sub>a' (assemble_state (assembly_map cd\<^sub>b) \<Sigma>\<^sub>u') \<and> 
      cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u'"
proof (induction "assemble_stack_code cd\<^sub>b" "assemble_state (assembly_map cd\<^sub>b) \<Sigma>\<^sub>u" \<Sigma>\<^sub>s\<^sub>a' 
       rule: evalsa.induct)
  case (evsa_push pc m r mem ps acc)
  thus ?case by simp
next
  case (evsa_pop pc m ps p mem acc)
  thus ?case by simp
next
  case (evsa_mov pc m mem ps acc)
  thus ?case by simp
next
  case (evsa_get pc m mem ps acc)
  thus ?case by simp
qed

theorem correctsa [simp]: "cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> iter (\<tturnstile> assemble_stack_code cd\<^sub>b \<leadsto>\<^sub>s\<^sub>a) 
  (assemble_state (assembly_map cd\<^sub>b) \<Sigma>\<^sub>u) (assemble_state (assembly_map cd\<^sub>b) \<Sigma>\<^sub>u')"
proof (induction cd\<^sub>b \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct)
case (evu_lookup cd pc x e sh sp y h hp ep vs vp)
  then show ?case by simp
next
  case (evu_pushcon cd pc k h hp e ep vs vp sh sp)
  from evu_pushcon have "cd ! pc = BPushCon k" by simp


  have "iter (\<tturnstile> assemble_stack_code cd \<leadsto>\<^sub>s\<^sub>a)
     (SAS (\<lambda>m. case m of Hp \<Rightarrow> h | Env \<Rightarrow> e | Vals \<Rightarrow> vs | Stk \<Rightarrow> sh) (\<lambda>m. case m of Hp \<Rightarrow> hp | Env \<Rightarrow> ep | Vals \<Rightarrow> vp | Stk \<Rightarrow> sp)
       (SOME x. True) (assembly_map cd (Suc pc)))
     (SAS (\<lambda>m. case m of Hp \<Rightarrow> h(hp := 0, Suc hp := k, Suc (Suc hp) := 0) | Env \<Rightarrow> e | Vals \<Rightarrow> vs(vp := hp) | Stk \<Rightarrow> sh)
       (\<lambda>m. case m of Hp \<Rightarrow> 3 + hp | Env \<Rightarrow> ep | Vals \<Rightarrow> Suc vp | Stk \<Rightarrow> sp) (SOME x. True) (assembly_map cd pc))" by simp
  thus ?case by simp
next
  case (evu_pushlam cd pc pc' h hp e ep vs vp sh sp)
  then show ?case by simp
next
  case (evu_apply cd pc h vs vp x hp e ep sh sp)
  then show ?case by simp
next
  case (evu_return_normal cd pc h hp e ep vs vp sh sp)
  then show ?case by simp
next
  case (evu_return_end cd pc h hp e ep vs vp sh)
  then show ?case by simp
next
  case (evu_jump cd pc h vs vp x hp e ep sh sp)
  then show ?case by simp
qed

theorem correctsa_iter [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> 
  assemble_stack_code cd\<^sub>b = (cd\<^sub>s\<^sub>a, mp) \<Longrightarrow> 
    iter (\<tturnstile> cd\<^sub>s\<^sub>a \<leadsto>\<^sub>s\<^sub>a) (assemble_state mp \<Sigma>\<^sub>u) (assemble_state mp \<Sigma>\<^sub>u')"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct) (force, metis correctsa iter_append)

end