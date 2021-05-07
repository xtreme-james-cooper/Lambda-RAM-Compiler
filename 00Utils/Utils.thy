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

lemma [simp]: "ran (f(x \<mapsto> z)) \<subseteq> insert z (ran f)"
  by (auto simp add: ran_def)

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

primrec list_sum :: "nat list \<Rightarrow> nat" where
  "list_sum [] = 0"
| "list_sum (n # ns) = n + list_sum ns"

lemma [simp]: "length as \<noteq> length bs \<Longrightarrow> map f as \<noteq> map f bs"
proof (induction as arbitrary: bs)
  case Nil
  thus ?case by (induction bs) simp_all
next
  case (Cons a as)
  thus ?case by (induction bs) simp_all
qed

lemma [simp]: "finite as \<Longrightarrow> x \<in> as \<Longrightarrow> 0 < card as"
  by (induction "card as") simp_all

lemma [simp]: "finite as \<Longrightarrow> a \<in> as \<Longrightarrow> Suc (card as - Suc 0) = card as"
  by (induction as rule: finite_induct) simp_all

lemma [simp]: "finite as \<Longrightarrow> finite bs \<Longrightarrow> card as < Suc (card (bs \<union> as))"
proof -
  assume "finite as" and "finite bs"
  hence "card as \<le> card (bs \<union> as)" by (simp add: card_mono)
  thus ?thesis by simp
qed

lemma [simp]: "finite as \<Longrightarrow> finite bs \<Longrightarrow> x \<in> as \<Longrightarrow> x \<notin> bs \<Longrightarrow> card bs < card (as \<union> bs)"
proof (induction as arbitrary: bs rule: finite_induct)
  case (insert a as)
  thus ?case by (cases "x = a") (simp_all add: card_insert_if)
qed simp_all

lemma [simp]: "finite as \<Longrightarrow> finite bs \<Longrightarrow> x \<notin> as \<Longrightarrow> x \<in> bs \<Longrightarrow> card (bs - {x} \<union> as) < card (as \<union> bs)"
proof -
  assume "finite as" and "finite bs" and "x \<in> bs"
  moreover hence "card (insert x (as \<union> bs)) = card (as \<union> bs)" by (simp add: card_insert_if)
  moreover assume "x \<notin> as"
  ultimately show ?thesis by (simp add: Un_Diff card.insert_remove sup_commute)
qed

lemma [simp]: "map_option f \<circ> map_option g \<circ> h = map_option (f \<circ> g) \<circ> h"
  by (rule, auto, metis option.map_comp)

lemma [simp]: "map_option f \<circ> (map_option g \<circ> h) = map_option (f \<circ> g) \<circ> h"
  by (rule, auto, metis option.map_comp)

lemma [simp]: "length as = length bs \<Longrightarrow> 
  list_all (\<lambda>(a, b). P a \<and> Q b) (zip as bs) = (list_all P as \<and> list_all Q bs)"
proof (induction as arbitrary: bs)
  case (Cons a as)
  thus ?case by (induction bs) auto
qed simp_all

primrec uncurry :: "('a \<Rightarrow> 'b \<Rightarrow> 'c) \<Rightarrow> 'a \<times> 'b \<Rightarrow> 'c" where
  "uncurry f (a, b) = f a b"

abbreviation nmem :: "nat \<Rightarrow> nat" where
  "nmem x \<equiv> undefined"

lemma [simp]: "(a # as @ bs) ! length as = (a # as) ! length as"
  by (induction as arbitrary: a) simp_all

lemma [simp]: "0 < x \<Longrightarrow> x \<le> length as \<Longrightarrow> (as @ bs) ! (length as - x) = as ! (length as - x)"
proof (induction as arbitrary: x bs rule: rev_induct)
  case (snoc a as)
  thus ?case 
  proof (induction x)
    case (Suc x)
    thus ?case by (induction x) simp_all
  qed simp_all
qed simp_all

end