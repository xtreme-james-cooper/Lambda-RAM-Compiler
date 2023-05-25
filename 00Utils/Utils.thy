theory Utils
  imports Main
begin

section \<open>Utilities\<close>

text \<open>We begin with a small collection of utility functions.\<close>

subsection \<open>Utilities\<close>

text \<open>In this section we have a number of miscellaneous functions and lemmas about the standard 
library that do not fit anywhere else. This can be skimmed or skipped on a first read.\<close>

lemma dom_expanded_fun_upd [simp]: "dom (\<lambda>a. if a = x then Some y else f a) = insert x (dom f)"
  by (auto simp add: dom_if)

lemma ran_of_map_option [simp]: "ran (map_option f \<circ> g) = f ` ran g"
  by (auto simp add: ran_def)

lemma length_concat_map [simp]: "length (concat (map f as)) = sum_list (map (length \<circ> f) as)"
  by (induction as) simp_all

lemma length_neq_map_neq [simp]: "length as \<noteq> length bs \<Longrightarrow> map f as \<noteq> map f bs"
proof (induction as arbitrary: bs)
  case Nil
  thus ?case by (induction bs) simp_all
next
  case (Cons a as)
  thus ?case by (induction bs) simp_all
qed

lemma finite_card_union' [simp]: "finite as \<Longrightarrow> finite bs \<Longrightarrow> card as < Suc (card (bs \<union> as))"
proof -
  assume "finite as" and "finite bs"
  hence "card as \<le> card (bs \<union> as)" by (simp add: card_mono)
  thus ?thesis by simp
qed

lemma finite_card_union [simp]: "finite as \<Longrightarrow> finite bs \<Longrightarrow> x \<in> as \<Longrightarrow> x \<notin> bs \<Longrightarrow> 
  card bs < card (as \<union> bs)"
proof (induction as arbitrary: bs rule: finite_induct)
  case (insert a as)
  thus ?case by (cases "x = a") (simp_all add: card_insert_if)
qed simp_all

lemma finite_card_union_remove [simp]: "finite as \<Longrightarrow> finite bs \<Longrightarrow> x \<notin> as \<Longrightarrow> x \<in> bs \<Longrightarrow> 
  card (bs - {x} \<union> as) < card (as \<union> bs)"
proof -
  assume "finite as" and "finite bs" and "x \<in> bs"
  moreover hence "card (insert x (as \<union> bs)) = card (as \<union> bs)" by (simp add: card_insert_if)
  moreover assume "x \<notin> as"
  ultimately show ?thesis by (simp add: Un_Diff card.insert_remove sup_commute)
qed

lemma list_all_zip [simp]: "length as = length bs \<Longrightarrow> 
  list_all (\<lambda>(a, b). P a \<and> Q b) (zip as bs) = (list_all P as \<and> list_all Q bs)"
proof (induction as arbitrary: bs)
  case (Cons a as)
  thus ?case by (induction bs) auto
qed simp_all

lemma length_concat_replicate [simp]: "length (concat (replicate x as)) = length as * x"
  by (induction x) simp_all

lemma map_concat_replicate [simp]: "map f (concat (replicate x as)) = 
    concat (replicate x (map f as))"
  by (induction x) simp_all

lemma suc_mult_lt_lemma [simp]: "x < y \<Longrightarrow> 1 < k \<Longrightarrow> Suc (k * x) < k * y"
  by (metis One_nat_def Suc_lessE Suc_lessI Suc_mult_less_cancel1 Suc_times_mod_eq 
            mod_mult_self1_is_0 nat.simps(3))

lemma x_mod_3_induct [case_names 0 1 2]: "((x::nat) mod 3 = 0 \<Longrightarrow> P x) \<Longrightarrow> (x mod 3 = 1 \<Longrightarrow> P x) \<Longrightarrow> 
    (x mod 3 = 2 \<Longrightarrow> P x) \<Longrightarrow> P x"
  by linarith

lemma upd_the [simp]: "the \<circ> (f(x \<mapsto> a)) = (the \<circ> f)(x := a)"
  by auto

lemma splay_lemma [simp]: "(k::nat) < m \<Longrightarrow> x < n \<Longrightarrow> k + m * x < m * n"
proof (induction x arbitrary: n)
  case 0
  thus ?case by (induction n) simp_all
next
  case (Suc x)
  thus ?case by (induction n) simp_all
qed

lemma list_all_elem [elim]: "list_all f env \<Longrightarrow> x \<in> set env \<Longrightarrow> f x"
  by (induction env) auto

end