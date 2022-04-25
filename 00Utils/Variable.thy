theory Variable
  imports Main
begin

datatype var = V nat

primrec fresh' :: "var set \<Rightarrow> nat \<Rightarrow> nat" where
  "fresh' xs 0 = 0"
| "fresh' xs (Suc x) = (if V (Suc x) \<in> xs then fresh' (xs - {V (Suc x)}) x else Suc x)"

definition fresh :: "var set \<Rightarrow> var" where
  "fresh xs = V (fresh' xs (card xs))"

abbreviation extend_set :: "var set \<Rightarrow> var set" where
  "extend_set vs \<equiv> insert (fresh vs) vs"

lemma [simp]: "finite xs \<Longrightarrow> fresh' xs x < Suc x"
proof (induction x arbitrary: xs)
  case (Suc x)
  hence "fresh' (xs - {V (Suc x)}) x < Suc x" by simp
  thus ?case by simp
qed simp_all

lemma [simp]: "finite xs \<Longrightarrow> fresh' xs x \<noteq> Suc x"
proof -
  assume "finite xs"
  hence "fresh' xs x < Suc x" by simp
  thus ?thesis by simp
qed

lemma [simp]: "finite xs \<Longrightarrow> x = card xs \<Longrightarrow> V (fresh' xs x) \<notin> xs"
proof (induction x arbitrary: xs)
  case (Suc x)
  moreover hence "finite (xs - {V (Suc x)})" by simp
  moreover from Suc have "V (Suc x) \<in> xs \<Longrightarrow> x = card (xs - {V (Suc x)})" by simp
  ultimately have "V (Suc x) \<in> xs \<Longrightarrow> V (fresh' (xs - {V (Suc x)}) x) \<notin> xs - {V (Suc x)}" by metis
  moreover from Suc(2) have "fresh' (xs - {V (Suc x)}) x \<noteq> Suc x" by simp
  ultimately show ?case by simp
qed simp_all

lemma fresh_is_fresh [simp]: "finite xs \<Longrightarrow> fresh xs \<notin> xs"
  by (simp add: fresh_def)

end