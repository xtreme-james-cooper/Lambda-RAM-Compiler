theory Environment
  imports "HOL-Library.Multiset"
begin

subsection \<open>Environments\<close>

text \<open>We represent environments (mostly for typing contexts, but also for evaluation once the 
concept of an "evaluation environment" becomes relevant) by simple lists. We could be more abstract 
- wrapping the type in a data constructor - or less so - treating them as a synonym for `nat \<rightharpoonup> 'a` 
- but the list representation is a good practical middle option.\<close>

text \<open>The fundamental operation on environments is the indexed lookup. It behaves much like the 
standard library's !! operation, but is a partial function rather than one with undefined domain 
elements; this really only moves the proof requirements around, from preconditions to outputs, but
we found this arrangement convenient.\<close>

fun lookup :: "'a list \<Rightarrow> nat \<rightharpoonup> 'a" where
  "lookup [] x = None"
| "lookup (a # as) 0 = Some a"
| "lookup (a # as) (Suc x) = lookup as x"

lemma lookup_in_bounds [simp]: "x < length as \<Longrightarrow> lookup as x \<noteq> None"
  by (induction as x rule: lookup.induct) simp_all

lemma lookup_some_in_bounds [simp]: "lookup as x = Some a \<Longrightarrow> x < length as"
  by (induction as x rule: lookup.induct) simp_all

lemma lookup_some_in_bounds_suc [simp]: "lookup as (Suc x) = Some a \<Longrightarrow> x < length as"
  by (induction as x rule: lookup.induct) simp_all

lemma lookup_map [simp]: "lookup (map f as) x = map_option f (lookup as x)"
  by (induction as x rule: lookup.induct) simp_all

lemma lookup_append_fst [simp]: "x < length as \<Longrightarrow> lookup (as @ bs) x = lookup as x"
  by (induction as x rule: lookup.induct) simp_all

lemma lookup_append_length [simp]: "lookup (as @ bs) (length as) = lookup bs 0"
  by (induction as) simp_all

lemma lookup_append_snd [simp]: "lookup (as @ bs) (length as + n) = lookup bs n"
  by (induction as) simp_all

lemma lookup_has_prop [elim]: "list_all p as \<Longrightarrow> lookup as x = Some a \<Longrightarrow> p a"
  by (induction as x rule: lookup.induct) simp_all

lemma lookup_idx_equiv [simp]: "lookup as x = Some a \<Longrightarrow> as ! x = a"
  by (induction as x rule: lookup.induct) simp_all

text \<open>Before we can talk about the other major function on environments, insert_at, we must define 
some helper functions on nats, incr and decr. If y is an index into an environment and x is the 
index at which the environment is being expanded (respectively, contracted) at, then incr x y and 
decr x y represent the modified index which will point to the same element in the environment. 
Because an element is being eliminated, decr has a side-condition that its two arguments be 
unequal.\<close>

(* 

TODO: proper diagram here
           ,---------
          /
---------' ,---------
          /
---------' ,---------
          /
---------+-----------

---------------------

---------------------
   x        incr 2 x


--------,          
         \ 
--------, `---------
         \
--------, `---------
         \
----------+---------

--------------------

--------------------
   x        decr 2 x

*)

fun incr :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "incr 0 y = Suc y"
| "incr (Suc x) 0 = 0"
| "incr (Suc x) (Suc y) = Suc (incr x y)"

fun decr :: "nat \<Rightarrow> nat \<Rightarrow> nat" where
  "decr x 0 = 0"
| "decr 0 (Suc y) = y"
| "decr (Suc x) (Suc y) = Suc (decr x y)"

lemma incr_not_eq [simp]: "incr x y \<noteq> x"
  by (induction x y rule: incr.induct) simp_all

lemma incr_min: "y < x \<Longrightarrow> incr x y = min x y"
  by (induction x y rule: incr.induct) simp_all

lemma incr_le: "y \<le> x \<Longrightarrow> incr y x = Suc x"
  by (induction y x rule: incr.induct) simp_all

lemma incr_suc_dest_lemma: "Suc y \<le> incr y x \<Longrightarrow> incr y x = Suc x"
  by (induction y x rule: incr.induct) simp_all

lemma incr_suc_dest: "y \<le> z \<Longrightarrow> Suc z = incr y x \<Longrightarrow> z = x"
proof (induction y x rule: incr.induct)
  case (3 y x)
  then show ?case by simp (metis incr_suc_dest_lemma)
qed simp_all

lemma decr_le [simp]: "y \<le> x \<Longrightarrow> decr x y = y"
  by (induction x y rule: decr.induct) simp_all

lemma decr_gt [simp]: "y \<ge> x \<Longrightarrow> decr x (Suc y) = y"
  by (induction x y rule: decr.induct) simp_all

lemma decr_eq_idx [simp]: "x \<noteq> y \<Longrightarrow> decr y x = y \<Longrightarrow> x = Suc y"
  by (induction y x rule: decr.induct) simp_all

lemma suc_decr [simp]: "y < decr y x \<Longrightarrow> Suc (decr y x) = x"
  by (induction y x rule: decr.induct) simp_all

lemma decr_lemma_for_debruijn [simp]: "y \<le> x \<Longrightarrow> y \<noteq> z \<Longrightarrow> x \<noteq> decr y z \<Longrightarrow> Suc x \<noteq> z \<Longrightarrow> 
  y \<noteq> decr (Suc x) z"
proof (induction y z arbitrary: x rule: decr.induct)
  case (3 y z)
  then show ?case by (induction x) simp_all
qed simp_all

text \<open>This is also our introduction to swap lemmas: we prove a series of automatic simplification 
rules that reorder an arbitrary sequence of incrs and decrs into a sequence of incrs ordered by 
strictly increasing indices, followed by a sequence of decrs with strictly decreasing indices. This 
canonical form will make later proofs much simpler, and we will freely reuse the concept for later 
environments.\<close>

lemma incr_swap [simp]: "y \<le> x \<Longrightarrow> incr y (incr x z) = incr (Suc x) (incr y z)"
proof (induction x z arbitrary: y rule: incr.induct)
  case (2 x)
  thus ?case by (induction y) simp_all
next
  case (3 x z)
  thus ?case by (induction y) simp_all
qed simp_all

lemma decr_swap [simp]: "y \<le> x \<Longrightarrow> decr x (decr y z) = decr y (decr (Suc x) z)"
proof (induction y z arbitrary: x rule: decr.induct)
  case (3 y z)
  then show ?case by (induction x) simp_all
qed simp_all

lemma decr_incr_absorb [simp]: "decr x (incr x y) = y"
  by (induction x y rule: incr.induct) simp_all

lemma incr_decr_swap [simp]: "y \<le> x \<Longrightarrow> incr y (decr x z) = decr (Suc x) (incr y z)"
proof (induction y z arbitrary: x rule: incr.induct)
  case (3 y z)
  thus ?case by (induction x) simp_all
qed simp_all

text \<open>We can now define insert_at, which extends an environment at a given index. We treat extending 
environments in terms of this function, rather than simply by consing elements to the front, because
moving under binders can rearrange the environment, and the insert_at function can represent this 
cleanly.\<close>

fun insert_at :: "nat \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "insert_at 0 a' [] = a' # []"
| "insert_at 0 a' (a # as) = a' # a # as"
| "insert_at (Suc x) a' [] = undefined"
| "insert_at (Suc x) a' (a # as) = a # insert_at x a' as"

lemma insert_at_length [simp]: "x \<le> length as \<Longrightarrow> length (insert_at x a as) = Suc (length as)"
  by (induction x a as rule: insert_at.induct) simp_all

lemma insert_at_mset [simp]: "x \<le> length as \<Longrightarrow> mset (insert_at x a as) = add_mset a (mset as)"
  by (induction x a as rule: insert_at.induct) simp_all

lemma insert_at_set [simp]: "x \<le> length as \<Longrightarrow> set (insert_at x a as) = insert a (set as)"
  by (induction x a as rule: insert_at.induct) auto

lemma insert_at_append [simp]: "x \<le> length as \<Longrightarrow> insert_at x a as @ bs = insert_at x a (as @ bs)"
proof (induction x a as rule: insert_at.induct)
  case (1 a')
  then show ?case by (induction bs) simp_all
qed simp_all

lemma insert_at_list_all [simp]: "list_all2 p as bs \<Longrightarrow> p a b \<Longrightarrow> x \<le> length as \<Longrightarrow> 
  list_all2 p (insert_at x a as) (insert_at x b bs)"
proof (induction x a as arbitrary: bs rule: insert_at.induct)
  case (2 a' a as)
  thus ?case by (induction bs) simp_all
next
  case (4 x a' a as)
  thus ?case by (induction bs) simp_all
qed simp_all

text \<open>Note that, although insert_at is not defined in terms of incr and decr, the interaction of 
lookup and insert_at fundamentally depends on them.\<close>

lemma lookup_insert_at_same [simp]: "x \<le> length as \<Longrightarrow> lookup (insert_at x a as) x = Some a"
  by (induction x a as rule: insert_at.induct) simp_all

lemma lookup_insert_at_incr [simp]: "x \<le> length as \<Longrightarrow> 
  lookup (insert_at x a as) (incr x y) = lookup as y"
proof (induction x a as arbitrary: y rule: insert_at.induct)
  case (4 x a' a as)
  then show ?case by (induction y) simp_all
qed simp_all

lemma lookup_at_decr [simp]: "x \<le> length as \<Longrightarrow> x \<noteq> y \<Longrightarrow> 
  lookup as (decr x y) = lookup (insert_at x a as) y"
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

text \<open>insert_at gets its own swap lemma: the canonical order is smallest index to largest.\<close>

lemma insert_at_swap [simp]: "x \<le> length as \<Longrightarrow> y \<le> x \<Longrightarrow> 
    insert_at y a (insert_at x b as) = insert_at (Suc x) b (insert_at y a as)"
proof (induction x b as arbitrary: y rule: insert_at.induct)
  case (4 x a' a as)
  then show ?case by (induction y) simp_all
qed simp_all

text \<open>We now define idx_of, a partial inverse of lookup that returns the first index of a given item 
in an environment.\<close>

fun idx_of :: "'a list \<Rightarrow> 'a \<rightharpoonup> nat" where
  "idx_of [] a' = None"
| "idx_of (a # as) a' = (if a = a' then Some 0 else map_option Suc (idx_of as a'))"

lemma idx_of_defined [simp]: "x \<in> set as \<Longrightarrow> \<exists>y. idx_of as x = Some y"
  by (induction as x rule: idx_of.induct) auto

lemma idx_of_member [simp]: "idx_of as x = Some y \<Longrightarrow> x \<in> set as"
  by (induction as x arbitrary: y rule: idx_of.induct) (auto split: if_splits)

lemma idx_of_not_member [simp]: "idx_of as x = None \<Longrightarrow> x \<notin> set as"
  by (induction as x rule: idx_of.induct) (simp_all split: if_splits)

lemma idx_of_remove [simp]: "a \<noteq> b \<Longrightarrow> 
    (\<exists>x. idx_of (remove1 b as) a = Some x) = (\<exists>x. idx_of as a = Some x)"
  by (induction as) (simp_all split: if_splits)

lemma idx_of_insert_at [simp]: "x \<le> length as \<Longrightarrow> idx_of (insert_at x a as) b = 
  (case idx_of as b of 
    None \<Rightarrow> (if a = b then Some x else None) 
  | Some y \<Rightarrow> Some (if a = b then min x y else incr x y))"
proof (induction x a as rule: insert_at.induct)
  case (4 x a' a as)
  thus ?case by (cases "idx_of as b") auto
qed (simp_all split: option.splits)

text \<open>Finally, some numeral simplification rules. These will be used in the assembly code pass, 
where lookups into long blocks of assembly code are common.\<close>

lemma lookup_2 [simp]: "lookup (a # b # c # d) 2 = Some c" 
  by (simp add: numeral_def)
lemma lookup_3 [simp]: "lookup (a # b # c # d # e) 3 = Some d" 
  by (simp add: numeral_def)
lemma lookup_4 [simp]: "lookup (a # b # c # d # e # f) 4 = Some e" 
  by (simp add: numeral_def)
lemma lookup_5 [simp]: "lookup (a # b # c # d # e # f # g) 5 = Some f" 
  by (simp add: numeral_def)
lemma lookup_6 [simp]: "lookup (a # b # c # d # e # f # g # h) 6 = Some g" 
  by (simp add: numeral_def)
lemma lookup_7 [simp]: "lookup (a # b # c # d # e # f # g # h # i) 7 = Some h" 
  by (simp add: numeral_def)
lemma lookup_8 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j) 8 = Some i" 
  by (simp add: numeral_def)
lemma lookup_9 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k) 9 = Some j" 
  by (simp add: numeral_def)
lemma lookup_10 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l) 10 = Some k" 
  by (simp add: numeral_def)
lemma lookup_11 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m) 11 = Some l" 
  by (simp add: numeral_def)
lemma lookup_12 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m # n) 12 = Some m" 
  by (simp add: numeral_def)
lemma lookup_13 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m # n # p) 13 = 
  Some n" by (simp add: numeral_def)
lemma lookup_14 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m # n # p # q) 14 = 
  Some p" by (simp add: numeral_def)
lemma lookup_15 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m # n # p # q # r) 
  15 = Some q" by (simp add: numeral_def)
lemma lookup_16 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m # n # p # q # r # 
  s) 16 = Some r" by (simp add: numeral_def)
lemma lookup_17 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m # n # p # q # r # 
  s # t) 17 = Some s" by (simp add: numeral_def)
lemma lookup_18 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m # n # p # q # r # 
  s # t # u) 18 = Some t" by (simp add: numeral_def)
lemma lookup_19 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m # n # p # q # r # 
  s # t # u # v) 19 = Some u" by (simp add: numeral_def)
lemma lookup_20 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m # n # p # q # r # 
  s # t # u # v # w) 20 = Some v" by (simp add: numeral_def)
lemma lookup_21 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m # n # p # q # r # 
  s # t # u # v # w # x) 21 = Some w" by (simp add: numeral_def)
lemma lookup_22 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m # n # p # q # r # 
  s # t # u # v # w # x # y) 22 = Some x" by (simp add: numeral_def)
lemma lookup_23 [simp]: "lookup (a # b # c # d # e # f # g # h # i # j # k # l # m # n # p # q # r # 
  s # t # u # v # w # x # y # z) 23 = Some y" by (simp add: numeral_def)

lemma lookup_5_plus_x [simp]: "lookup (a # b # c # d # e # f) (5 + x) = lookup f x" 
  by (simp add: numeral_def)
lemma lookup_6_plus_x [simp]: "lookup (a # b # c # d # e # f) (6 + x) = lookup f (Suc x)" 
  by (simp add: numeral_def)
lemma lookup_7_plus_x [simp]: "lookup (a # b # c # d # e # f) (7 + x) = lookup f (Suc (Suc x))" 
  by (simp add: numeral_def)

end