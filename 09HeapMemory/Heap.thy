theory Heap
  imports "../00Utils/Environment"
begin

section \<open>Heap Memory\<close>

text \<open>Having reached a more concrete code representation with our bytecode, we can continue making 
our evaluation state more concrete too. The most obvious inefficiency in our bytecode interpreter is
that values and environments are copied around willy-nilly; but before we can address that, we need
to build a new abstraction to store our values in.\<close>

subsection \<open>Heaps\<close>

text \<open>We have so far represented stacks as lists. Heaps are random-access, but we only ever add to 
them at one end, so we could represent heaps the same way, with allocation being an append to the 
end of the list. But it will be more useful to us to build a more direct representation of heaps, as 
a \<open>nat \<Rightarrow> 'a\<close> mapping with a marker indicating the first (smallest) unallocated address.\<close>

datatype 'a heap = H "nat \<Rightarrow> 'a" nat

definition hempty :: "'a heap" where
  "hempty \<equiv> H (\<lambda>x. undefined) 0"

text \<open>We also define a type of pointers into the heap, although we do not make it abstract as we 
need to be able to manipulate them as numbers.\<close>

type_synonym ptr = nat

text \<open>As with environments, the main use of a heap is to look up a reference within it. Unlike an 
environment or stack, a heap is random-access.\<close>

primrec hlookup :: "'a heap \<Rightarrow> ptr \<Rightarrow> 'a" where
  "hlookup (H h hp) x = h x"

text \<open>Unlike environments, the adding-to-heap operation is relatively complicated. It must not only
update the heap's internal map and the upper boundary marker, but it must return a pointer to the 
newly allocated storage for the item.\<close>

primrec halloc :: "'a heap \<Rightarrow> 'a \<Rightarrow> 'a heap \<times> ptr" where
  "halloc (H h hp) a = (H (h(hp := a)) (Suc hp), hp)"

lemma hlookup_alloc [simp]: "halloc h a = (h', x) \<Longrightarrow> 
    hlookup h' y = (if x = y then a else hlookup h y)"
  by (induction h) (auto split: if_splits)

text \<open>We also have a valid-pointer predicate (it's straightforward, because we never deallocate 
memory).\<close>

primrec hcontains :: "'a heap \<Rightarrow> ptr \<Rightarrow> bool" where
  "hcontains (H h hp) x = (x < hp)"

lemma hcontains_suc [elim]: "hcontains h (Suc x) \<Longrightarrow> hcontains h x"
  by (induction h)  simp_all

lemma hcontains_lte [elim]: "hcontains h x \<Longrightarrow> y \<le> x \<Longrightarrow> hcontains h y"
  by (induction h)  simp_all

lemma halloc_contains [simp]: "halloc h a = (h', y) \<Longrightarrow> hcontains h' x = (x = y \<or> hcontains h x)"
  by (induction h) auto

lemma halloc_lookup [simp]: "halloc h a = (h', x) \<Longrightarrow> hcontains h y \<Longrightarrow> 
    hlookup h' y = hlookup h y"
  by (induction h) (auto split: if_splits)

lemma halloc_contains_lt [simp]: "halloc h a = (h', x) \<Longrightarrow> hcontains h y \<Longrightarrow> y < x"
  by (induction h) auto

lemma halloc_list_all_contains [simp]: "halloc h a = (h', x) \<Longrightarrow> list_all (hcontains h) vs \<Longrightarrow> 
    list_all (hcontains h') vs"
  by (induction vs) auto

lemma halloc_list_list_all_contains [simp]: "halloc h a = (h', x) \<Longrightarrow> 
    list_all (list_all (hcontains h)) vs \<Longrightarrow> list_all (list_all (hcontains h')) vs"
  by (induction vs) simp_all

lemma halloc_list_list_list_all_contains [simp]: "halloc h a = (h', x) \<Longrightarrow> 
  list_all (list_all (list_all (hcontains h))) vs \<Longrightarrow> 
    list_all (list_all (list_all (hcontains h'))) vs"
  by (induction vs) simp_all

lemma halloc_env_bounded [simp]: "halloc h c = (h', v) \<Longrightarrow> list_all (hcontains h) env \<Longrightarrow> 
    list_all ((>) v) env"
  by (induction env) simp_all

lemma halloc_env_bounded2 [simp]: "halloc h c = (h', v) \<Longrightarrow> 
    list_all (list_all (hcontains h)) env \<Longrightarrow> list_all (list_all ((>) v)) env"
  by (induction env) simp_all

text \<open>We also define some utility functions. We cannot use the autogenerated \<open>map_heap\<close> and 
\<open>pred_heap\<close> because they do not respect the upper bound. \<open>hmap_empty\<close>, for instance, would be false
unless the function f had \<open>f undefined = undefined\<close>.\<close>

primrec hmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a heap \<Rightarrow> 'b heap" where
  "hmap f (H h hp) = H (\<lambda>x. if x < hp then f (h x) else undefined) hp"

lemma hmap_empty [simp]: "hmap f hempty = hempty"
  by (simp add: hempty_def)

lemma halloc_map [simp]: "halloc h a = (h', v) \<Longrightarrow> halloc (hmap f h) (f a) = (hmap f h', v)"
  by (induction h) auto+

lemma halloc_map_inv [simp]: "halloc (hmap f h) (f a) = (h', v) \<Longrightarrow> 
    \<exists>h''. halloc h a = (h'', v) \<and> h' = hmap f h''"
  by (induction h) auto

lemma hlookup_map [simp]: "hcontains h x \<Longrightarrow> hlookup (hmap f h) x = f (hlookup h x)"
  by (induction h) simp_all

lemma hmap_eq: "(\<And>x. hcontains h x \<Longrightarrow> f (hlookup h x) = g (hlookup h x)) \<Longrightarrow> hmap f h = hmap g h"
  by (induction h) auto

primrec heap_all :: "(ptr \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a heap \<Rightarrow> bool" where
  "heap_all p (H h hp) = (\<forall>x < hp. p x (h x))"

lemma heap_all_empty [simp]: "heap_all f hempty"
  by (simp add: hempty_def)

lemma halloc_all [elim]: "heap_all p h \<Longrightarrow> halloc h a = (h', x) \<Longrightarrow> p x a \<Longrightarrow> heap_all p h'"
  by (induction h) auto

lemma hlookup_all: "hlookup h x = a \<Longrightarrow> heap_all p h \<Longrightarrow> hcontains h x \<Longrightarrow> p x a"
  by (induction h) auto

lemma heap_all_implication [elim]: "(\<And>x y. p x y \<Longrightarrow> q x y) \<Longrightarrow> heap_all p h \<Longrightarrow> heap_all q h"
  by (induction h) simp_all

text \<open>For later passes, we will also need some more complex ways of interacting with the heap: 
allocating an entire list of items at once, for instance.\<close>

fun halloc_list' :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "halloc_list' h hp [] = h"
| "halloc_list' h hp (x # xs) = halloc_list' (h(hp := x)) (Suc hp) xs"

primrec halloc_list :: "'a heap \<Rightarrow> 'a list \<Rightarrow> 'a heap \<times> ptr" where
  "halloc_list (H h hp) as = (H (halloc_list' h hp as) (hp + length as), hp)"

lemma halloc_list_lookup' [simp]: "y < hp \<Longrightarrow> halloc_list' h hp as y = h y" 
  by (induction as arbitrary: h hp) simp_all

lemma halloc_list_lookup [simp]: "halloc_list h as = (h', x) \<Longrightarrow> hcontains h y \<Longrightarrow> 
    hlookup h' y = hlookup h y" 
  by (induction h) auto

lemma halloc_list_lookup_idx' [simp]: "k < length as \<Longrightarrow> halloc_list' h hp as (k + hp) = as ! k"
proof (induction as arbitrary: h hp k)
  case (Cons a as)
  thus ?case 
  proof (induction k)
    case (Suc k)
    hence "halloc_list' (h(hp := a)) (Suc hp) as (k + (Suc hp)) = as ! k"
      by (metis length_Cons not_less_eq)
    thus ?case by simp
  qed simp_all
qed simp_all

lemma halloc_list_lookup_idx [simp]: "halloc_list h as = (h', p) \<Longrightarrow> k < length as \<Longrightarrow> 
    hlookup h' (k + p) = as ! k"
  by (induction h) (auto split: prod.splits)

text \<open>We also have a function for flatmapping a heap of structured data into a heap of 
less-structured data. The workings of the function are complex, having to manage two heaps 
allocating at different rates, but the key properties (\<open>hlookup_hsplay\<close> and \<open>halloc_list_hsplay\<close>) 
are fairly simple.\<close>

function hsplay' :: "('a \<Rightarrow> 'b list) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
    (nat \<Rightarrow> 'b) \<times> nat" where
  "hp\<^sub>a \<le> n \<Longrightarrow> hsplay' f h\<^sub>a hp\<^sub>a h\<^sub>b hp\<^sub>b n = (h\<^sub>b, hp\<^sub>b)"
| "hp\<^sub>a > n \<Longrightarrow> hsplay' f h\<^sub>a hp\<^sub>a h\<^sub>b hp\<^sub>b n = 
    hsplay' f h\<^sub>a hp\<^sub>a (halloc_list' h\<^sub>b hp\<^sub>b (f (h\<^sub>a n))) (hp\<^sub>b + length (f (h\<^sub>a n))) (Suc n)"
  by atomize_elim auto
termination
  by (relation "measure (\<lambda>(_, _, hp\<^sub>a, _, _, n). hp\<^sub>a - n)") simp_all

primrec hsplay :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a heap \<Rightarrow> 'b heap" where
  "hsplay f (H h hp) = (case hsplay' f h hp (\<lambda>x. undefined) 0 0 of (h', hp') \<Rightarrow> H h' hp')"

lemma hsplay_empty [simp]: "hsplay f hempty = hempty"
  by (simp add: hempty_def)

lemma hlookup_hsplay' [simp]: "(\<And>a. length (f a) = m \<and> f a ! k = g a) \<Longrightarrow> p < hpa \<Longrightarrow> k < m \<Longrightarrow>
  (\<And>x. x < n \<Longrightarrow> hb (k + m * x) = g (ha x)) \<Longrightarrow> hpb = m * n \<Longrightarrow>
    hsplay' f ha hpa hb hpb n = (h', hp') \<Longrightarrow> h' (k + m * p) = g (ha p)"
proof (induction f ha hpa hb hpb n rule: hsplay'.induct)
  case (2 hpa n f ha hb hpb)
  hence "\<And>x. x < Suc n \<Longrightarrow> halloc_list' hb hpb (f (ha n)) (k + m * x) = g (ha x)" 
  proof -
    fix x
    assume X: "x < Suc n"
    with 2 show "?thesis x" 
    proof (cases "x < n")
      case False
      with X have "x = n" by simp
      with 2 show ?thesis by simp
    qed simp_all
  qed
  with 2 show ?case by simp
qed simp_all

lemma hlookup_hsplay [simp]: "(\<And>a. length (f a) = m \<and> f a ! k = g a) \<Longrightarrow> hcontains h p \<Longrightarrow> k < m \<Longrightarrow>
  hlookup (hsplay f h) (k + m * p) = g (hlookup h p)"
proof (induction h)
  case (H h hp)
  moreover obtain h' hp' where "hsplay' f h hp (\<lambda>x. undefined) 0 0 = (h', hp')" by fastforce
  moreover with H have "p < hp \<Longrightarrow> 0 = m * 0 \<Longrightarrow> h' (k + m * p) = g (h p)" 
    using hlookup_hsplay' by blast
  ultimately show ?case by simp
qed

lemma halloc_list_hsplay' [simp]: "n \<le> hpa \<Longrightarrow> hsplay' f ha hpa hb hpb n = (h, hp) \<Longrightarrow> 
  hsplay' f (ha(hpa := a)) (Suc hpa) hb hpb n = (h', hp') \<Longrightarrow> 
    h' = halloc_list' h hp (f a) \<and> hp' = hp + length (f a)"
  by (induction f ha hpa hb hpb n rule: hsplay'.induct) simp_all

lemma hsplay'_index [simp]: "hsplay' f ha hpa hb hpb n = (h, hp) \<Longrightarrow> (\<And>x. length (f x) = k) \<Longrightarrow> 
    hp = hpb + k * (hpa - n)"
proof (induction f ha hpa hb hpb n rule: hsplay'.induct)
  case (2 hpa n f ha hb hpb)
  moreover have "n < hpa \<Longrightarrow> k + k * (hpa - Suc n) = k * (hpa - n)"
    by (metis Suc_diff_Suc mult_Suc_right)
  ultimately show ?case by simp
qed simp_all

lemma halloc_list_hsplay [simp]: "halloc h a = (h', p) \<Longrightarrow> (\<And>x. length (f x) = k) \<Longrightarrow> 
  halloc_list (hsplay f h) (f a) = (hsplay f h', k * p)"
proof (induction h)
  case (H h hp)
  hence "hp = p" by simp
  moreover with H have "h' = H (h(p := a)) (Suc p)" by simp
  moreover obtain hh' hp' where HH: "hsplay' f h p (\<lambda>x. undefined) 0 0 = (hh', hp')" by fastforce
  moreover obtain hh'' hp'' where HH': "hsplay' f (h(p := a)) (Suc p) (\<lambda>x. undefined) 0 0 = 
    (hh'', hp'')" by fastforce
  moreover with HH have "hh'' = halloc_list' hh' hp' (f a) \<and> hp'' = hp' + length (f a)" 
    using halloc_list_hsplay' by fast
  moreover from H HH have "hp' = 0 + k * (p - 0)" by (metis hsplay'_index)
  ultimately show ?case by fastforce
qed

lemma hsplay_contains_lemma2 [simp]: "hsplay' f h hp m mp n = (h', hp') \<Longrightarrow> mp = k * n \<Longrightarrow> 
    (\<And>a. length (f a) = k) \<Longrightarrow> n \<le> hp \<Longrightarrow> hp' = k * hp"
  by (induction f h hp m mp n rule: hsplay'.induct) simp_all

lemma hsplay_contains_lemma [simp]: "hcontains h x \<Longrightarrow> hsplay f h = H h' hp' \<Longrightarrow> 
  (\<And>a. length (f a) = k) \<Longrightarrow> 1 < k \<Longrightarrow> Suc (k * x) < hp'"
proof (induction h)
  case (H h hp)
  moreover hence "hp' = k * hp" by (simp split: prod.splits)
  ultimately show ?case by simp
qed 

end