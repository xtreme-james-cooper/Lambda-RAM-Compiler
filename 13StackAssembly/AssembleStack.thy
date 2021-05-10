theory AssembleStack
  imports StackAssembly "../12UnstructuredMemory/UnstructuredMemory" "../00Utils/Utils"
begin

primrec assemble_stack_len :: "byte_code \<Rightarrow> nat" where
  "assemble_stack_len (BLookup x) = 1"
| "assemble_stack_len (BPushCon k) = 6"
| "assemble_stack_len (BPushLam pc) = 9"
| "assemble_stack_len BApply = 1"
| "assemble_stack_len BReturn = 1"
| "assemble_stack_len BJump = 1"

primrec assemble_stack_op :: "(nat \<Rightarrow> nat) \<Rightarrow> byte_code \<Rightarrow> sassm_code list" where
  "assemble_stack_op mp (BLookup x) = [undefined]"
| "assemble_stack_op mp (BPushCon k) = [
    SAMov (MCon 0),
    SAPush Hp (Con 0), 
    SAPush Hp (Con k), 
    SAPush Hp (Con 0), 
    SAPush Vals Acc, 
    SAMov (Mem Hp)]"
| "assemble_stack_op mp (BPushLam pc) = [
    SAMov (MCon 0),
    SAPush Hp (Con (mp pc)), 
    SAPush Hp Acc, 
    SAPush Hp (Con 1),
    SAGet Stk, 
    SASub 1,
    SAMov (Mem Stk),
    SAPush Vals Acc, 
    SAMov (Mem Hp)]"
| "assemble_stack_op mp BApply = [undefined]"
| "assemble_stack_op mp BReturn = [undefined]"
| "assemble_stack_op mp BJump = [undefined]"

(*   evu_lookup [simp]: "cd ! pc = BLookup x \<Longrightarrow> unstr_lookup e (sh (sp - 1)) x = Some y \<Longrightarrow>
    cd \<tturnstile> US h hp e ep vs vp sh sp (Suc pc) \<leadsto>\<^sub>u US h hp e ep (vs(vp := y)) (Suc vp) sh sp pc"
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
| "assembly_map (op # cd) 0 = 0"
| "assembly_map (op # cd) (Suc x) = assemble_stack_len op + assembly_map cd x"

definition assemble_stack_code :: "byte_code list \<Rightarrow> sassm_code list" where
  "assemble_stack_code cd = concat (map (assemble_stack_op (assembly_map cd)) cd)"

primrec assemble_state :: "(nat \<Rightarrow> nat) \<Rightarrow> unstr_state \<Rightarrow> sassm_state" where
  "assemble_state mp (US h hp e ep vs vp sh sp pc) = 
    SAS (case_memory h e vs sh) (case_memory hp ep vp sp) 0 (mp pc)"

lemma [simp]: "length (assemble_stack_op mp op) = assemble_stack_len op"
  by (induction op) simp_all

theorem completesa [simp]: "
  assemble_stack_code cd\<^sub>b \<tturnstile> assemble_state (assembly_map cd\<^sub>b) \<Sigma>\<^sub>u \<leadsto>\<^sub>s\<^sub>a \<Sigma>\<^sub>s\<^sub>a' \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>s\<^sub>a'' \<Sigma>\<^sub>u'. iter (\<tturnstile> assemble_stack_code cd\<^sub>b \<leadsto>\<^sub>s\<^sub>a) \<Sigma>\<^sub>s\<^sub>a' (assemble_state (assembly_map cd\<^sub>b) \<Sigma>\<^sub>u') \<and> 
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
next
  case (evsa_sub pc k mem ps acc)
  thus ?case by simp
qed

lemma [simp]: "cd ! pc = op \<Longrightarrow> pc < length cd \<Longrightarrow> 
  assembly_map cd (Suc pc) = assemble_stack_len op + assembly_map cd pc"
proof (induction cd pc rule: assembly_map.induct)
  case (2 op' cd)
  thus ?case by (cases cd) simp_all
qed simp_all

lemma assemble_code_lookup' [simp]: "cd ! pc = op \<Longrightarrow> pc < length cd \<Longrightarrow> 
  x < assemble_stack_len op \<Longrightarrow> concat (map (assemble_stack_op (assembly_map (cd' @ cd))) cd) ! 
    (x + assembly_map cd pc) = assemble_stack_op (assembly_map (cd' @ cd)) op ! x"
proof (induction cd pc arbitrary: cd' rule: assembly_map.induct)
  case (3 op' cd y)
  hence "concat (map (assemble_stack_op (assembly_map ((cd' @ [op']) @ cd))) cd) ! 
    (x + assembly_map cd y) = assemble_stack_op (assembly_map ((cd' @ [op']) @ cd)) op ! x" 
      by fastforce
  hence "(assemble_stack_op (assembly_map (cd' @ op' # cd)) op' @ 
    concat (map (assemble_stack_op (assembly_map (cd' @ op' # cd))) cd)) !
      (assemble_stack_len op' + x + assembly_map cd y) =
        assemble_stack_op (assembly_map (cd' @ op' # cd)) op ! x" by (simp add: nth_append)
  hence "(assemble_stack_op (assembly_map (cd' @ op' # cd)) op' @ 
    concat (map (assemble_stack_op (assembly_map (cd' @ op' # cd))) cd)) !
      (x + (assemble_stack_len op' + assembly_map cd y)) =
        assemble_stack_op (assembly_map (cd' @ op' # cd)) op ! x" by (metis add.assoc add.commute)
  thus ?case by simp
qed (simp_all add: nth_append)

lemma assemble_code_lookup [simp]: "cd ! pc = op \<Longrightarrow> pc < length cd \<Longrightarrow> 
  x < assemble_stack_len op \<Longrightarrow> 
    assemble_stack_code cd ! (x + assembly_map cd pc) = assemble_stack_op (assembly_map cd) op ! x"
  by (metis assemble_code_lookup' append_Nil assemble_stack_code_def)

lemma [simp]: "cd ! pc = op \<Longrightarrow> pc < length cd \<Longrightarrow> 1 < assemble_stack_len op \<Longrightarrow> 
    assemble_stack_code cd ! (Suc (assembly_map cd pc)) = assemble_stack_op (assembly_map cd) op ! 1"
  using assemble_code_lookup by fastforce

lemma [simp]: "cd ! pc = op \<Longrightarrow> pc < length cd \<Longrightarrow> 0 < assemble_stack_len op \<Longrightarrow> 
    assemble_stack_code cd ! (assembly_map cd pc) = assemble_stack_op (assembly_map cd) op ! 0"
  using assemble_code_lookup by fastforce

lemma [simp]: "m Hp = h \<Longrightarrow> m Env = e \<Longrightarrow> m Vals = vs \<Longrightarrow> m Stk = sh \<Longrightarrow> m = case_memory h e vs sh" 
  by rule (simp split: memory.splits)

theorem correctsa [simp]: "cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow> 
  iter (\<tturnstile> assemble_stack_code cd\<^sub>b \<leadsto>\<^sub>s\<^sub>a) (assemble_state (assembly_map cd\<^sub>b) \<Sigma>\<^sub>u) 
    (assemble_state (assembly_map cd\<^sub>b) \<Sigma>\<^sub>u')"
proof (induction cd\<^sub>b \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct)
case (evu_lookup cd pc x e sh sp y h hp ep vs vp)
  then show ?case by simp
next
  case (evu_pushcon cd pc k h hp e ep vs vp sh sp)
  let ?mem = "case_memory h e vs sh"
  let ?ps = "case_memory hp ep vp sp"
  from evu_pushcon have "assemble_stack_code cd ! (5 + assembly_map cd pc) = SAMov (Mem Hp)" by simp
  hence "assemble_stack_code cd ! (Suc (Suc (Suc (Suc (Suc (assembly_map cd pc)))))) = 
    SAMov (Mem Hp)" by (simp add: numeral_def)
  hence A: "assemble_stack_code cd \<tturnstile> 
    SAS ?mem ?ps 0 (Suc (Suc (Suc (Suc (Suc (Suc (assembly_map cd pc))))))) \<leadsto>\<^sub>s\<^sub>a 
      SAS ?mem ?ps hp (Suc (Suc (Suc (Suc (Suc (assembly_map cd pc))))))" 
    by (metis evsa_mov get_mval.simps(1) memory.simps(13))
  from evu_pushcon have "assemble_stack_code cd ! (4 + assembly_map cd pc) = SAPush Vals Acc" 
    by simp
  hence "assemble_stack_code cd ! (Suc (Suc (Suc (Suc (assembly_map cd pc))))) = SAPush Vals Acc" 
    by (simp add: numeral_def)
  hence B: "
    assemble_stack_code cd \<tturnstile> SAS ?mem ?ps hp (Suc (Suc (Suc (Suc (Suc (assembly_map cd pc)))))) \<leadsto>\<^sub>s\<^sub>a
      SAS (mem_upd ?mem Vals vp hp) (?ps(Vals := Suc vp)) hp 
        (Suc (Suc (Suc (Suc (assembly_map cd pc)))))"
    by (metis evsa_push memory.simps(15) get_val.simps(1))
  from evu_pushcon have "assemble_stack_code cd ! (3 + assembly_map cd pc) = SAPush Hp (Con 0)" 
    by simp
  hence "assemble_stack_code cd ! (Suc (Suc (Suc (assembly_map cd pc)))) = SAPush Hp (Con 0)" 
    by (simp add: numeral_def)
  hence C: "assemble_stack_code cd \<tturnstile> SAS (mem_upd ?mem Vals vp hp) (?ps(Vals := Suc vp)) hp 
    (Suc (Suc (Suc (Suc (assembly_map cd pc))))) \<leadsto>\<^sub>s\<^sub>a SAS (mem_upd (mem_upd ?mem Vals vp hp) Hp hp 0) 
      (?ps(Vals := Suc vp, Hp := Suc hp)) hp (Suc (Suc (Suc (assembly_map cd pc))))" 
    by (metis evsa_push get_val.simps(2) fun_upd_apply memory.distinct(3) memory.simps(13))
  from evu_pushcon have "assemble_stack_code cd ! (2 + assembly_map cd pc) = 
    SAPush Hp (Con k)" by (simp del: add_2_eq_Suc)
  hence "assemble_stack_code cd ! (Suc (Suc (assembly_map cd pc))) = SAPush Hp (Con k)" by simp
  hence D: "assemble_stack_code cd \<tturnstile> SAS (mem_upd (mem_upd ?mem Vals vp hp) Hp hp 0) 
    (?ps(Vals := Suc vp, Hp := Suc hp)) hp (Suc (Suc (Suc (assembly_map cd pc)))) \<leadsto>\<^sub>s\<^sub>a 
      SAS (mem_upd (mem_upd (mem_upd ?mem Vals vp hp) Hp hp 0) Hp (Suc hp) k) 
        (?ps(Vals := Suc vp, Hp := Suc (Suc hp))) hp (Suc (Suc (assembly_map cd pc)))" 
    by (metis evsa_push get_val.simps(2) fun_upd_apply fun_upd_upd)
  from evu_pushcon have "assemble_stack_code cd ! Suc (assembly_map cd pc) = SAPush Hp (Con 0)" 
    by simp
  hence E: "assemble_stack_code cd \<tturnstile> SAS (mem_upd (mem_upd (mem_upd ?mem Vals vp hp) Hp hp 0) Hp 
    (Suc hp) k) (?ps(Vals := Suc vp, Hp := Suc (Suc hp))) hp (Suc (Suc (assembly_map cd pc))) \<leadsto>\<^sub>s\<^sub>a
      SAS (mem_upd (mem_upd (mem_upd (mem_upd ?mem Vals vp hp) Hp hp 0) Hp (Suc hp) k) Hp 
        (Suc (Suc hp)) 0) (?ps(Vals := Suc vp, Hp := Suc (Suc (Suc hp)))) hp 
          (Suc (assembly_map cd pc))" 
    by (metis evsa_push get_val.simps(2) fun_upd_apply fun_upd_upd)
  from evu_pushcon have "assemble_stack_code cd ! assembly_map cd pc = SAMov (MCon 0)" by simp
  hence "assemble_stack_code cd \<tturnstile> SAS 
    (mem_upd (mem_upd (mem_upd (mem_upd ?mem Vals vp hp) Hp hp 0) Hp (Suc hp) k) Hp 
      (Suc (Suc hp)) 0) (?ps(Vals := Suc vp, Hp := Suc (Suc (Suc hp)))) hp 
        (Suc (assembly_map cd pc)) \<leadsto>\<^sub>s\<^sub>a SAS 
          (mem_upd (mem_upd (mem_upd (mem_upd ?mem Vals vp hp) Hp hp 0) Hp (Suc hp) k) Hp 
            (Suc (Suc hp)) 0) (?ps(Vals := Suc vp, Hp := Suc (Suc (Suc hp)))) 0 
              (assembly_map cd pc)" 
    by (metis evsa_mov get_mval.simps(2))
  with A B C D E have "iter (\<tturnstile> assemble_stack_code cd \<leadsto>\<^sub>s\<^sub>a) 
    (SAS ?mem ?ps 0 (Suc (Suc (Suc (Suc (Suc (Suc (assembly_map cd pc))))))))
      (SAS (mem_upd (mem_upd (mem_upd (mem_upd ?mem Vals vp hp) Hp hp 0) Hp (Suc hp) k) Hp 
        (Suc (Suc hp)) 0) (?ps(Vals := Suc vp, Hp := Suc (Suc (Suc hp)))) 0 (assembly_map cd pc))"
    by simp
  with evu_pushcon show ?case by (simp add: numeral_def)
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

theorem correctsa_iter [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> restructurable \<Sigma>\<^sub>u cd\<^sub>b \<Longrightarrow> 
  iter (\<tturnstile> assemble_stack_code cd\<^sub>b \<leadsto>\<^sub>s\<^sub>a) 
    (assemble_state (assembly_map cd\<^sub>b) \<Sigma>\<^sub>u) (assemble_state (assembly_map cd\<^sub>b) \<Sigma>\<^sub>u')"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct) (force, metis correctsa iter_append preserve_restructure)

end