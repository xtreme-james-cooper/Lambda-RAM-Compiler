theory Environment
  imports "HOL-Library.Multiset"
begin

fun lookup :: "'a list \<Rightarrow> nat \<rightharpoonup> 'a" where
  "lookup [] x = None"
| "lookup (a # as) 0 = Some a"
| "lookup (a # as) (Suc x) = lookup as x"

fun insert_at :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert_at 0 a' [] = a' # []"
| "insert_at 0 a' (a # as) = a' # a # as"
| "insert_at (Suc x) a' [] = undefined"
| "insert_at (Suc x) a' (a # as) = a # insert_at x a' as"

fun idx_of :: "'a list \<Rightarrow> 'a \<rightharpoonup> nat" where
  "idx_of [] a' = None"
| "idx_of (a # as) a' = (if a = a' then Some 0 else map_option Suc (idx_of as a'))"

fun incr :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "incr 0 y = Suc y"
| "incr (Suc x) 0 = 0"
| "incr (Suc x) (Suc y) = Suc (incr x y)"

fun decr :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "decr x 0 = 0"
| "decr 0 (Suc y) = y"
| "decr (Suc x) (Suc y) = Suc (decr x y)"

abbreviation precede :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> bool" (infix "precedes _ in" 50) where
  "x precedes a in as \<equiv> (case idx_of as a of Some y \<Rightarrow> x \<le> y | None \<Rightarrow> True)"

lemma [simp]: "incr 0 = Suc"
  by auto

lemma [simp]: "decr x (incr x y) = y"
  by (induction x y rule: incr.induct) simp_all

lemma incr_not_eq [simp]: "incr x y \<noteq> x"
  by (induction x y rule: incr.induct) simp_all

lemma incr_min: "y < x \<Longrightarrow> incr x y = min x y"
  by (induction x y rule: incr.induct) simp_all

lemma [simp]: "y \<le> x \<Longrightarrow> decr x y = y"
  by (induction x y rule: decr.induct) simp_all

lemma [simp]: "y \<ge> x \<Longrightarrow> decr x (Suc y) = y"
  by (induction x y rule: decr.induct) simp_all

lemma [simp]: "x \<noteq> y \<Longrightarrow> decr y x = y \<Longrightarrow> x = Suc y"
  by (induction y x rule: decr.induct) simp_all

lemma [simp]: "y < decr y x \<Longrightarrow> Suc (decr y x) = x"
  by (induction y x rule: decr.induct) simp_all

lemma [simp]: "y \<le> x \<Longrightarrow> incr y (incr x z) = incr (Suc x) (incr y z)"
proof (induction x z arbitrary: y rule: incr.induct)
  case (2 x)
  thus ?case by (induction y) simp_all
next
  case (3 x z)
  thus ?case by (induction y) simp_all
qed simp_all

lemma [simp]: "y \<le> x \<Longrightarrow> incr y (decr x z) = decr (Suc x) (incr y z)"
proof (induction y z arbitrary: x rule: incr.induct)
  case (3 y z)
  thus ?case by (induction x) simp_all
qed simp_all

lemma [simp]: "y \<le> x \<Longrightarrow> decr x (decr y z) = decr y (decr (Suc x) z)"
proof (induction y z arbitrary: x rule: decr.induct)
  case (3 y z)
  then show ?case by (induction x) simp_all
qed simp_all

lemma incr_le: "y \<le> x \<Longrightarrow> incr y x = Suc x"
  by (induction y x rule: incr.induct) simp_all

lemma incr_lemma': "Suc y \<le> incr y x \<Longrightarrow> incr y x = Suc x"
  by (induction y x rule: incr.induct) simp_all

lemma incr_lemma: "y \<le> z \<Longrightarrow> Suc z = incr y x \<Longrightarrow> z = x"
proof (induction y x rule: incr.induct)
  case (3 y x)
  then show ?case by simp (metis incr_lemma')
qed simp_all

lemma [simp]: "y \<le> x \<Longrightarrow> y \<noteq> z \<Longrightarrow> x \<noteq> decr y z \<Longrightarrow> Suc x \<noteq> z \<Longrightarrow> y \<noteq> decr (Suc x) z"
proof (induction y z arbitrary: x rule: decr.induct)
  case (3 y z)
  then show ?case by (induction x) simp_all
qed simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> length (insert_at x a as) = Suc (length as)"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> mset (insert_at x a as) = add_mset a (mset as)"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "x \<ge> length as \<Longrightarrow> lookup as x = None"
  by (induction as x rule: lookup.induct) simp_all

lemma [simp]: "lookup as x = Some a \<Longrightarrow> x < length as"
  by (induction as x rule: lookup.induct) simp_all

lemma [simp]: "x < length as \<Longrightarrow> \<exists>a. lookup as x = Some a"
  by (induction as x rule: lookup.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> lookup (insert_at x a as) x = Some a"
  by (induction x a as rule: insert_at.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> lookup (insert_at x a as) (incr x y) = lookup as y"
proof (induction x a as arbitrary: y rule: insert_at.induct)
  case (4 x a' a as)
  then show ?case by (induction y) simp_all
qed simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> x \<noteq> y \<Longrightarrow> lookup as (decr x y) = lookup (insert_at x a as) y"
proof (induction x a as arbitrary: y rule: insert_at.induct)
  case (1 a')
  then show ?case by (induction y) simp_all
next
  case (2 a' a as)
  then show ?case by (induction y) simp_all
next
  case (4 x a' a as)
  then show ?case by (induction y) simp_all
qed simp_all

lemma [simp]: "lookup (map f as) x = map_option f (lookup as x)"
  by (induction as x rule: lookup.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> y \<le> x \<Longrightarrow> 
    insert_at y a (insert_at x b as) = insert_at (Suc x) b (insert_at y a as)"
proof (induction x b as arbitrary: y rule: insert_at.induct)
  case (4 x a' a as)
  then show ?case by (induction y) simp_all
qed simp_all

lemma [simp]: "lookup as x = Some a \<Longrightarrow> lookup (as @ bs) x = Some a"
  by (induction as x rule: lookup.induct) simp_all

lemma [simp]: "x \<le> length as \<Longrightarrow> insert_at x a as @ bs = insert_at x a (as @ bs)"
proof (induction x a as rule: insert_at.induct)
  case (1 a')
  then show ?case by (induction bs) simp_all
qed simp_all

lemma [simp]: "x \<in> set as \<Longrightarrow> \<exists>y. idx_of as x = Some y"
  by (induction as x rule: idx_of.induct) auto

lemma [simp]: "idx_of as x = Some y \<Longrightarrow> x \<in> set as"
  by (induction as x arbitrary: y rule: idx_of.induct) (auto split: if_splits)

lemma [simp]: "idx_of as x = None \<Longrightarrow> x \<notin> set as"
  by (induction as x rule: idx_of.induct) (simp_all split: if_splits)

lemma [simp]: "a \<noteq> b \<Longrightarrow> (\<exists>x. idx_of (remove1 b as) a = Some x) = (\<exists>x. idx_of as a = Some x)"
  by (induction as) (simp_all split: if_splits)

lemma [simp]: "x \<le> length as \<Longrightarrow> set (insert_at x a as) = insert a (set as)"
  by (induction x a as rule: insert_at.induct) auto

lemma [simp]: "x \<le> length as \<Longrightarrow> distinct (insert_at x a as) = (a \<notin> set as \<and> distinct as)"
  by (induction x a as rule: insert_at.induct) auto

lemma [simp]: "x \<le> length as \<Longrightarrow> idx_of (insert_at x a as) b = 
  (case idx_of as b of 
    None \<Rightarrow> (if a = b then Some x else None) 
  | Some y \<Rightarrow> Some (if a = b then min x y else incr x y))"
proof (induction x a as rule: insert_at.induct)
  case (4 x a' a as)
  thus ?case by (cases "idx_of as b") auto
qed (simp_all split: option.splits)

lemma [simp]: "0 precedes a in as"
  by (simp split: option.splits)

lemma [simp]: "lookup as x = Some a \<Longrightarrow> a \<in> set as"
  by (induction as x rule: lookup.induct) simp_all

end