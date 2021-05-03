theory Assemble
  imports AssemblyCode "../12UnstructuredMemory/UnstructuredMemory"
begin  

primrec assemble' :: "(nat \<Rightarrow> nat) \<Rightarrow> byte_code \<Rightarrow> assm list" where
  "assemble' mp (BLookup x) = [
      AMov ACC SP,
      ASub ACC 1,
      ALod ACC Stk ACC,
      ALdI AC2 x,
      AAdd AC2 1,
      AJIZ AC2 4,
      ASub AC2 1,
      AAssert ACC ((>) 1),
      ASub ACC 1,
      ALod ACC Hp  ACC,
      AJmp 5,
      AAssert ACC ((>) 1),
      ASub ACC 2,
      ALod ACC Hp  ACC,
      ASto Val VP  ACC,
      AAdd VP  1]"
| "assemble' mp (BPushCon k) = [
      ASto Val VP  HP, 
      AAdd VP  1, 
      ALdI ACC 0, 
      ASto Hp  HP  ACC, 
      AAdd HP  1, 
      ALdI ACC k, 
      ASto Hp  HP  ACC, 
      AAdd HP  1, 
      ALdI ACC 0, 
      ASto Hp  HP  ACC, 
      AAdd HP  1]"
| "assemble' mp (BPushLam pc) = [
      ASto Val VP  HP, 
      AAdd VP  1, 
      ALdI ACC 1, 
      ASto Hp  HP  ACC, 
      AAdd HP  1, 
      AMov ACC SP, 
      ASub ACC 1,
      ALod ACC Stk ACC,
      ASto Hp  HP  ACC, 
      AAdd HP  1, 
      ALdI ACC (mp pc), 
      ASto Hp  HP  ACC, 
      AAdd HP  1]"
| "assemble' mp BApply = [
      ASub VP  1,
      ALod ACC Val VP,
      ASto Env EP  ACC,
      AAdd EP  1,
      ASub VP  1,
      ALod ACC Val VP,
      ALod AC2 Hp  ACC,
      ASub AC2 1,
      AAssert AC2 ((=) 0),
      AAdd ACC 1,
      ALod AC2 Hp  ACC,
      ASto Env EP  AC2,
      AAdd EP  1,
      ASto Stk SP  EP,
      AAdd SP  1,
      AAdd ACC 1,
      ALod ACC Hp  ACC,
      ASto Stk SP  ACC,
      AAdd SP  1]"
| "assemble' mp BReturn = [
      ASub SP  1, 
      ALod ACC Stk SP, 
      AIJp ACC]"
| "assemble' mp BJump = [
      ASub VP  1,
      ALod ACC Val VP,
      ASto Env EP  ACC,
      AAdd EP  1,
      ASub VP  1,
      ALod ACC Val VP,
      ALod AC2 Hp  ACC,
      ASub AC2 1,
      AAssert AC2 ((=) 0),
      AAdd ACC 1,
      ALod AC2 Hp  ACC,
      ASto Env EP  AC2,
      AAdd EP  1,
      ASub SP  1,
      AAdd ACC 1,
      ALod ACC Hp  ACC,
      ASto Stk SP  ACC,
      ASub SP  1,
      ASto Stk SP  EP,
      AAdd SP  2]"

primrec assemble :: "byte_code list \<Rightarrow> assm list \<times> (nat \<Rightarrow> nat)" where
  "assemble [] = ([], id)"
| "assemble (op # cd) = (
    let (cd', mp) = assemble cd
    in let op' = assemble' mp op
    in (op' @ cd', \<lambda>x. case x of 0 \<Rightarrow> 0 | Suc x' \<Rightarrow> mp x' + length op'))"

primrec assemble_state :: "(nat \<Rightarrow> nat) \<Rightarrow> unstr_state \<Rightarrow> assm_state" where
  "assemble_state mp (US h hp e ep vs vp sh sp pc) = AS (\<lambda>r. case r of
      HP \<Rightarrow> hp 
    | EP \<Rightarrow> ep
    | VP \<Rightarrow> vp
    | SP \<Rightarrow> sp
    | ACC \<Rightarrow> 0
    | ACC2 \<Rightarrow> 0) (\<lambda>m. case m of
      Hp \<Rightarrow> h
    | Env \<Rightarrow> e
    | Val \<Rightarrow> vs
    | Stk \<Rightarrow> sh) (mp pc)"

lemma [simp]: "(\<lambda>r. case r of HP \<Rightarrow> 0 | EP \<Rightarrow> 0 | VP \<Rightarrow> 0 | SP \<Rightarrow> Suc 0 | ACC \<Rightarrow> 0 | ACC2 \<Rightarrow> 0) = 
  (\<lambda>r. 0)(SP := Suc 0)"
proof
  fix r
  show "(case r of HP \<Rightarrow> 0 | EP \<Rightarrow> 0 | VP \<Rightarrow> 0 | SP \<Rightarrow> Suc 0 | ACC \<Rightarrow> 0 | ACC2 \<Rightarrow> 0) = 
    ((\<lambda>r. 0)(SP := Suc 0)) r"
      by (cases r) simp_all
  qed

lemma [simp]: "(\<lambda>m. case m of Stk \<Rightarrow> nmem(0 := 0) | _ \<Rightarrow> nmem) = (\<lambda>m. nmem)(Stk := nmem(0 := 0))"
proof
  fix m
  show "(case m of Stk \<Rightarrow> nmem(0 := 0) | _ \<Rightarrow> nmem) = ((\<lambda>m. nmem)(Stk := nmem(0 := 0))) m"
    by (cases m) simp_all
qed

lemma [simp]: "assemble cd = (cd', mp) \<Longrightarrow> mp 0 = 0"
  by (induction cd arbitrary: cd' mp) (auto simp add: Let_def split: prod.splits)

lemma [simp]: "assemble cd = (cd', mp) \<Longrightarrow> mp (length cd) = length cd'"
  by (induction cd arbitrary: cd' mp) (auto simp add: Let_def split: prod.splits)

theorem completea [simp]: "cd\<^sub>a \<tturnstile> \<Sigma>\<^sub>a \<leadsto>\<^sub>a \<Sigma>\<^sub>a' \<Longrightarrow> 
  \<exists>cd\<^sub>b mp \<Sigma>\<^sub>u \<Sigma>\<^sub>u'. assemble cd\<^sub>b = (cd\<^sub>a, mp) \<and> assemble_state mp \<Sigma>\<^sub>u = \<Sigma>\<^sub>a \<and> 
    assemble_state mp \<Sigma>\<^sub>u' = \<Sigma>\<^sub>a' \<and> iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u'"
  by (induction cd\<^sub>a \<Sigma>\<^sub>a \<Sigma>\<^sub>a' rule: evala.induct) blast

theorem correcta [simp]: "cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>u \<leadsto>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> assemble cd\<^sub>b = (cd\<^sub>a, mp) \<Longrightarrow>
    iter (\<tturnstile> cd\<^sub>a \<leadsto>\<^sub>a) (assemble_state mp \<Sigma>\<^sub>u) (assemble_state mp \<Sigma>\<^sub>u')"
  by (induction cd\<^sub>b \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: evalu.induct) blast

theorem correcta_iter [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>u) \<Sigma>\<^sub>u \<Sigma>\<^sub>u' \<Longrightarrow> assemble cd\<^sub>b = (cd\<^sub>a, mp) \<Longrightarrow>
    iter (\<tturnstile> cd\<^sub>a \<leadsto>\<^sub>a) (assemble_state mp \<Sigma>\<^sub>u) (assemble_state mp \<Sigma>\<^sub>u')"
  by (induction \<Sigma>\<^sub>u \<Sigma>\<^sub>u' rule: iter.induct)
     (force, metis correcta iter_append)

end