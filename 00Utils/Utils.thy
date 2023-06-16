theory Utils
  imports Main
begin

section \<open>Utilities\<close>

text \<open>We begin with a small collection of utility functions.\<close>

subsection \<open>Utilities\<close>

text \<open>In this section we have a number of miscellaneous functions and lemmas about the standard 
library that do not fit anywhere else. This can be skimmed or skipped on a first read.\<close>

primrec map_with_idx :: "(nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_with_idx f [] = []"
| "map_with_idx f (a # as) = f 0 a # map_with_idx (f \<circ> Suc) as"

lemma len_conc_map_ix_lemma' [simp]: "((\<lambda>x. f (ix + x)) \<circ> Suc) = (\<lambda>x. f (Suc (ix + x)))"
  by auto

lemma len_conc_map_ix_lemma [simp]: "((\<lambda>ix a. length (f ix a)) \<circ> Suc) = 
    (\<lambda>ix a. length (f (Suc ix) a))"
  by auto

lemma length_concat_map_with_idx [simp]: "length (concat (map_with_idx f as)) = 
    sum_list (map_with_idx (\<lambda>ix a. length (f ix a)) as)"
  by (induction as arbitrary: f) simp_all

fun nat_to_string' :: "nat \<Rightarrow> char" where
  "nat_to_string' 0 = CHR 48"
| "nat_to_string' (Suc 0) = CHR 49"
| "nat_to_string' (Suc (Suc 0)) = CHR 50"
| "nat_to_string' (Suc (Suc (Suc 0))) = CHR 51"
| "nat_to_string' (Suc (Suc (Suc (Suc 0)))) = CHR 52"
| "nat_to_string' (Suc (Suc (Suc (Suc (Suc 0))))) = CHR 53"
| "nat_to_string' (Suc (Suc (Suc (Suc (Suc (Suc 0)))))) = CHR 54"
| "nat_to_string' (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0))))))) = CHR 55"
| "nat_to_string' (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc 0)))))))) = CHR 56"
| "nat_to_string' (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc (Suc x))))))))) = CHR 57"

fun nat_to_string :: "nat \<Rightarrow> string" where
  "nat_to_string x = 
    (if x < 10 then [nat_to_string' x] else nat_to_string (x div 10) @ [nat_to_string' (x mod 10)])"

declare nat_to_string.simps [simp del]

lemma nat_to_string'_inj [simp]: "x < 10 \<Longrightarrow> y < 10 \<Longrightarrow> 
  (nat_to_string' x = nat_to_string' y) = (x = y)"
proof (induction x rule: nat_to_string'.induct)
  case 1
  thus ?case by (induction y rule: nat_to_string'.induct) simp_all
next
  case 2
  thus ?case by (induction y rule: nat_to_string'.induct) simp_all
next
  case 3
  thus ?case by (induction y rule: nat_to_string'.induct) simp_all
next
  case 4
  thus ?case by (induction y rule: nat_to_string'.induct) simp_all
next
  case 5
  thus ?case by (induction y rule: nat_to_string'.induct) simp_all
next
  case 6
  thus ?case by (induction y rule: nat_to_string'.induct) simp_all
next
  case 7
  thus ?case by (induction y rule: nat_to_string'.induct) simp_all
next
  case 8
  thus ?case by (induction y rule: nat_to_string'.induct) simp_all
next
  case 9
  thus ?case by (induction y rule: nat_to_string'.induct) simp_all
next
  case (10 x)
  thus ?case by (induction y rule: nat_to_string'.induct) simp_all
qed

lemma nat_to_string_not_empty [simp]: "nat_to_string x \<noteq> []"
  by (induction x rule: nat_to_string.induct) (simp_all add: nat_to_string.simps)

lemma nat_to_string_not_empty2 [simp]: "[] \<noteq> nat_to_string x"
  by (metis nat_to_string_not_empty)

lemma div10_mod10_eq [simp]: "((x::nat) div 10 = y div 10 \<and> x mod 10 = y mod 10) = (x = y)"
proof
  assume "x div 10 = y div 10 \<and> x mod 10 = y mod 10"
  hence "x div 10 * 10 + x mod 10 = y div 10 * 10 + y mod 10" by simp
  thus "x = y" by simp
qed simp_all

lemma nat_to_string_inj [simp]: "(nat_to_string x = nat_to_string y) = (x = y)"
  by (induction x arbitrary: y rule: nat_to_string.induct, induction y rule: nat_to_string.induct)
     (simp_all add: nat_to_string.simps)

lemma dom_expanded_fun_upd [simp]: "dom (\<lambda>a. if a = x then Some y else f a) = insert x (dom f)"
  by (auto simp add: dom_if)

lemma ran_of_map_option [simp]: "ran (map_option f \<circ> g) = f ` ran g"
  by (auto simp add: ran_def)

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

lemma snd_pair [simp]: "(a, b) = f x \<Longrightarrow> snd (f x) = b"
  by (metis snd_conv)

lemma plus_zero [simp]: "(+) (0::nat) = id"
  by auto

lemma suc_even [simp]: "Suc (Suc 0) dvd Suc x \<Longrightarrow> odd x"
  by presburger

lemma even_down [simp]: "Suc (Suc 0) dvd Suc (Suc x) = (Suc (Suc 0) dvd x)"
  by presburger

end