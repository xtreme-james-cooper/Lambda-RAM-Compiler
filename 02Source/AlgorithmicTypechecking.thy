theory AlgorithmicTypechecking
  imports Named
begin

fun tc_alg :: "(var \<rightharpoonup> ty) \<Rightarrow> nexpr \<rightharpoonup> ty" where
  "tc_alg \<Gamma> (NVar x) = \<Gamma> x"
| "tc_alg \<Gamma> (NConst k) = Some Base"
| "tc_alg \<Gamma> (NLam x t e) = (case tc_alg (\<Gamma>(x \<mapsto> t)) e of 
      Some t\<^sub>2 \<Rightarrow> Some (Arrow t t\<^sub>2)
    | None \<Rightarrow> None)"
| "tc_alg \<Gamma> (NApp e\<^sub>1 e\<^sub>2) = (case tc_alg \<Gamma> e\<^sub>1 of
      Some (Arrow t\<^sub>1 t\<^sub>2) \<Rightarrow> (if tc_alg \<Gamma> e\<^sub>2 = Some t\<^sub>1 then Some t\<^sub>2 else None)
    | Some Base \<Rightarrow> None
    | None \<Rightarrow> None)"

abbreviation typechecks :: "nexpr \<Rightarrow> bool" where
  "typechecks e \<equiv> (tc_alg Map.empty e \<noteq> None)"

lemma [simp]: "(tc_alg \<Gamma> e = Some t) = (\<Gamma> \<turnstile>\<^sub>n e : t)"
proof
  show "tc_alg \<Gamma> e = Some t \<Longrightarrow> \<Gamma> \<turnstile>\<^sub>n e : t"
    by (induction e arbitrary: \<Gamma> t) (simp_all split: option.splits ty.splits if_splits, fastforce+) 
  show "\<Gamma> \<turnstile>\<^sub>n e : t \<Longrightarrow> tc_alg \<Gamma> e = Some t" 
  proof (induction \<Gamma> e t rule: typecheckn.induct)
    case (tcn_lam \<Gamma> x t\<^sub>1 e t\<^sub>2)
    hence "tc_alg (\<Gamma>(x \<mapsto> t\<^sub>1)) e = Some t\<^sub>2" by blast
    thus ?case by simp
  qed simp_all
qed

end