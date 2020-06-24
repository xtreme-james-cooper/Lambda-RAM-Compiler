theory MemoryFlattening                   
  imports FlatMemory "../09HeapMemory/HeapConversion"
begin

primrec flatten :: "chained_state \<Rightarrow> flat_state" where
  "flatten (CES h env vs sfs cd) = undefined"

theorem correctf: "flatten \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>f \<Sigma>\<^sub>f' \<Longrightarrow> \<exists>\<Sigma>\<^sub>c\<^sub>e'. \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<and> flatten \<Sigma>\<^sub>c\<^sub>e' = \<Sigma>\<^sub>f'" 
  by simp

theorem completef [simp]: "\<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> flatten \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>f flatten \<Sigma>\<^sub>c\<^sub>e'" 
  by simp

lemma completef_iter [simp]: "iter (\<leadsto>\<^sub>c\<^sub>e) \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> iter (\<leadsto>\<^sub>f) (flatten \<Sigma>\<^sub>c\<^sub>e) (flatten \<Sigma>\<^sub>c\<^sub>e')"
proof (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Sigma>\<^sub>c\<^sub>e'')
  hence "iter (\<leadsto>\<^sub>f) (flatten \<Sigma>\<^sub>c\<^sub>e') (flatten \<Sigma>\<^sub>c\<^sub>e'')" by simp
  moreover from iter_step have "flatten \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>f flatten \<Sigma>\<^sub>c\<^sub>e'" by simp
  ultimately show ?case by simp
qed simp_all

end