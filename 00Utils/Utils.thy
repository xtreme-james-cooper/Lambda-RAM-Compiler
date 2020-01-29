theory Utils
  imports "HOL-Library.Multiset"
begin

lemma [simp]: "(as @ bs) ! length as = bs ! 0"
  by (induction as) simp_all

definition remove :: "('a \<rightharpoonup> 'b) \<Rightarrow> 'a \<Rightarrow> ('a \<rightharpoonup> 'b)" where
  "remove f a = f(a := None)"

lemma [simp]: "x \<noteq> y \<Longrightarrow> remove f y x = f x"
  by (simp add: remove_def)

lemma [simp]: "dom (remove f y) = dom f - {y}"
  by (simp add: remove_def)

lemma [simp]: "dom (\<lambda>a. if a = x then Some y else f a) = insert x (dom f)"
  by (auto simp add: dom_if)

lemma [simp]: "map_option Suc opt \<noteq> Some 0"
  by (induction opt) simp_all

lemma [simp]: "image_mset fst (mset ab) = add_mset a s \<Longrightarrow> Some (the (map_of ab a)) = map_of ab a"
proof (induction ab arbitrary: s)
  case (Cons ab abb)
  thus ?case
  proof (induction ab)
    case (Pair aa bb)
    thus ?case
    proof (cases "a = aa")
      case False
      from Pair have "add_mset aa (image_mset fst (mset abb)) - {# aa #} = add_mset a s - {# aa #}" 
        by simp
      with False have "image_mset fst (mset abb) = add_mset a (s - {# aa #})" by simp
      with Pair show ?thesis by simp
    qed simp_all
  qed
qed simp_all

end