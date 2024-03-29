theory Utils
  imports Main
begin

section \<open>Utilities\<close>

text \<open>We begin with a small collection of utility functions.\<close>

subsection \<open>Utilities\<close>

text \<open>In this section we have a number of miscellaneous functions and lemmas about the standard 
library that do not fit anywhere else. This can be skimmed or skipped on a first read.\<close>

primrec map_with_idx :: "nat \<Rightarrow> (nat \<Rightarrow> 'a \<Rightarrow> 'b) \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_with_idx x f [] = []"
| "map_with_idx x f (a # as) = f x a # map_with_idx (Suc x) f as"

lemma map_with_idx_id [simp]: "map_with_idx x (\<lambda>a b. b) as = as"
  by (induction as arbitrary: x) (simp_all add: comp_def)

lemma map_with_idx_const [simp]: "map_with_idx x (\<lambda>k. f) as = map f as"
  by (induction as arbitrary: x) (simp_all add: comp_def)

lemma length_map_with_idx [simp]: "length (map_with_idx x f as) = length as"
  by (induction as arbitrary: x) simp_all

lemma map_with_idx_append [simp]: "map_with_idx x f (as @ bs) = 
    map_with_idx x f as @ map_with_idx (x + length as) f bs"
  by (induction as arbitrary: x) (simp_all add: comp_def)

lemma length_concat_map_with_idx [simp]: "length (concat (map_with_idx x f as)) = 
    sum_list (map_with_idx x (\<lambda>ix a. length (f ix a)) as)"
  by (induction as arbitrary: x) simp_all

lemma map_with_idx_comp' [simp]: "map_with_idx x (\<lambda>k. f k \<circ> g k) as = 
    map_with_idx x f (map_with_idx x g as)"
  by (induction as arbitrary: x) (simp_all add: comp_def)

lemma map_with_idx_comp [simp]: "map_with_idx x (\<lambda>k. f k \<circ> g k) = 
    map_with_idx x f \<circ> map_with_idx x g"
  by auto

lemma map_with_idx_comp2' [simp]: "map_with_idx x (\<lambda>k. f \<circ> g k) as = map f (map_with_idx x g as)"
  by (induction as arbitrary: x) (simp_all add: comp_def)

lemma map_with_idx_comp2 [simp]: "map_with_idx x (\<lambda>k. f \<circ> g k) = map f \<circ> map_with_idx x g"
  by auto

lemma map_with_idx_suc [simp]: "map_with_idx x (f \<circ> Suc) as = map_with_idx (Suc x) f as"
  by (induction as arbitrary: x) simp_all

lemma list_all_map_with_idx [simp]: "(\<And>k a. p (f k a) = p a) \<Longrightarrow> 
    list_all p (map_with_idx x f as) = list_all p as"
  by (induction as arbitrary: x) simp_all

primrec snoc_fst :: "'a \<Rightarrow> 'a list list \<Rightarrow> 'a list list" where
  "snoc_fst b [] = []"
| "snoc_fst b (bs # bss) = (bs @ [b]) # bss"

lemma snoc_fst_nil [simp]: "(snoc_fst a as = []) = (as = [])"
  by (cases as) simp_all

lemma snoc_fst_nil2 [simp]: "([] = snoc_fst a as) = (as = [])"
  by (cases as) simp_all

lemma snoc_fst_inj [simp]: "as \<noteq> [] \<Longrightarrow> (snoc_fst a as = snoc_fst b bs) = (a = b \<and> as = bs)"
proof (induction as arbitrary: bs)
  case (Cons a as)
  thus ?case by (induction bs) auto
qed simp_all

lemma map_snoc_fst [simp]: "map (map f) (snoc_fst a as) = snoc_fst (f a) (map (map f) as)"
  by (induction as) simp_all

lemma length_hd_snoc_fst [simp]: "as \<noteq> [] \<Longrightarrow> length (hd (snoc_fst a as)) = Suc (length (hd as))"
  by (induction as) simp_all

lemma list_all_snoc_fst [simp]: "list_all (list_all p) (snoc_fst a as) = 
    ((as = [] \<or> p a) \<and> list_all (list_all p) as)"
  by (induction as) auto

lemma snoc_fst_take [simp]: "n < length as \<Longrightarrow> take (Suc n) (as[n := a]) = take n as @ [a]"
  by (induction as arbitrary: n) (simp_all split: nat.splits)

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

lemma list_all_elem [elim]: "list_all p as \<Longrightarrow> a \<in> set as \<Longrightarrow> p a"
  by (induction as) auto

lemma list_all_elem2 [elim]: "list_all (list_all p) bss \<Longrightarrow> bs \<in> set bss \<Longrightarrow> b \<in> set bs \<Longrightarrow> p b"
  by (induction bss) auto

lemma map_not_null [simp]: "(\<noteq>) [] \<circ> map f = (\<noteq>) []"
  by auto

lemma snd_pair [simp]: "(a, b) = f x \<Longrightarrow> snd (f x) = b"
  by (metis snd_conv)

lemma plus_zero [simp]: "(+) (0::nat) = id"
  by auto

lemma plus_one [simp]: "(+) (Suc 0) = Suc"
  by auto

lemma suc_comp_plus [simp]: "Suc \<circ> (+) x = (+) (Suc x)"
  by auto

lemma apfst_suc [simp]: "(\<lambda>(y, z). (y, if y = 0 then Suc z else z)) \<circ> apfst Suc = apfst Suc"
  by auto

lemma suc_even [simp]: "Suc (Suc 0) dvd Suc x \<Longrightarrow> odd x"
  by presburger

lemma even_down [simp]: "Suc (Suc 0) dvd Suc (Suc x) = (Suc (Suc 0) dvd x)"
  by presburger

lemma dvd_2_suc [dest]: "Suc (Suc 0) dvd Suc x \<Longrightarrow> Suc (Suc 0) dvd x \<Longrightarrow> False"
  by presburger

end