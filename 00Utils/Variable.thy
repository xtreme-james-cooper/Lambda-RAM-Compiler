theory Variable
  imports Utils
begin

subsection \<open>Named Variables\<close>

text \<open>We represent source variables by an opaque datatype and internally by a string. The only 
operations on variables we need are equality and getting a variable distinct from a finite set of 
variables. The key lemma, \<open>fresh_is_fresh\<close>, proves that we in fact have a new variable.\<close>

datatype var = V string

abbreviation varname :: "nat \<Rightarrow> string" where
  "varname x \<equiv> ''v'' @ nat_to_string x"

primrec fresh' :: "var set \<Rightarrow> nat \<Rightarrow> nat" where
  "fresh' xs 0 = 0"
| "fresh' xs (Suc x) = (
    if V (varname (Suc x)) \<in> xs 
    then fresh' (xs - {V (varname (Suc x))}) x 
    else Suc x)"

definition fresh :: "var set \<Rightarrow> var" where
  "fresh xs \<equiv> V (varname (fresh' xs (card xs)))"

lemma fresh_lt_suc [simp]: "finite xs \<Longrightarrow> fresh' xs x < Suc x"
proof (induction x arbitrary: xs)
  case (Suc x)
  hence "fresh' (xs - {V (varname (Suc x))}) x < Suc x" by simp
  thus ?case by simp
qed simp_all

lemma fresh_is_not_suc [simp]: "finite xs \<Longrightarrow> fresh' xs x \<noteq> Suc x"
proof -
  assume "finite xs"
  hence "fresh' xs x < Suc x" by simp
  thus ?thesis by simp
qed

lemma fresh'_is_fresh [simp]: "finite xs \<Longrightarrow> x = card xs \<Longrightarrow> V (varname (fresh' xs x)) \<notin> xs"
proof (induction x arbitrary: xs)
  case (Suc x)
  moreover hence "finite (xs - {V (varname (Suc x))})" by simp
  moreover from Suc have "V (varname (Suc x)) \<in> xs \<Longrightarrow> x = card (xs - {V (varname (Suc x))})" 
    by simp
  ultimately have "V (varname (Suc x)) \<in> xs \<Longrightarrow> 
    V (varname (fresh' (xs - {V (varname (Suc x))}) x)) \<notin> xs - {V (varname (Suc x))}" by metis
  moreover from Suc(2) have "fresh' (xs - {V (varname (Suc x))}) x \<noteq> Suc x" by simp
  ultimately show ?case by simp
qed simp_all

lemma fresh_is_fresh [simp]: "finite xs \<Longrightarrow> fresh xs \<notin> xs"
  by (metis fresh_def fresh'_is_fresh)

end