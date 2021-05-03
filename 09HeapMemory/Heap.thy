theory Heap
  imports "../00Utils/Environment"
begin

type_synonym ptr = nat

datatype 'a heap = H "nat \<Rightarrow> 'a" nat

definition hempty :: "'a heap" where
  "hempty = H (\<lambda>x. undefined) 0"
 
primrec halloc :: "'a heap \<Rightarrow> 'a \<Rightarrow> 'a heap \<times> ptr" where
  "halloc (H h hp) a = (H (h(hp := a)) (Suc hp), hp)"

primrec hlookup :: "'a heap \<Rightarrow> ptr \<Rightarrow> 'a" where
  "hlookup (H h hp) x = h x"

primrec hcontains :: "'a heap \<Rightarrow> ptr \<Rightarrow> bool" where
  "hcontains (H h hp) x = (x < hp)"

primrec heap_all :: "(ptr \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a heap \<Rightarrow> bool" where
  "heap_all p (H h hp) = (\<forall>x < hp. p x (h x))"

primrec hmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a heap \<Rightarrow> 'b heap" where
  "hmap f (H h hp) = H (\<lambda>x. if x < hp then f (h x) else undefined) hp"

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> hlookup h' y = (if x = y then a else hlookup h y)"
  by (induction h) (auto split: if_splits)

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> hcontains h y \<Longrightarrow> hlookup h' y = hlookup h y"
  by (induction h) (auto split: if_splits)

lemma [elim]: "hcontains h (Suc x) \<Longrightarrow> hcontains h x"
  by (induction h)  simp_all

lemma [elim]: "hcontains h x \<Longrightarrow> y \<le> x \<Longrightarrow> hcontains h y"
  by (induction h)  simp_all

lemma [simp]: "hcontains h x \<Longrightarrow> halloc h a = (h', y) \<Longrightarrow> hcontains h' x"
  by (induction h) auto

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> hcontains h' x"
  by (induction h) auto

lemma heap_lookup_all: "hlookup h x = a \<Longrightarrow> heap_all p h \<Longrightarrow> hcontains h x \<Longrightarrow> p x a"
  by (induction h) auto

lemma [elim]: "heap_all p h \<Longrightarrow> halloc h a = (h', x) \<Longrightarrow> p x a \<Longrightarrow> heap_all p h'"
  by (induction h) auto

lemma heap_all_impl [elim]: "(\<And>x y. p x y \<Longrightarrow> q x y) \<Longrightarrow> heap_all p h \<Longrightarrow> heap_all q h"
  by (induction h) simp_all

lemma [simp]: "heap_all f hempty"
  by (simp add: hempty_def)

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> hcontains h y \<Longrightarrow> y < x"
  by (induction h) auto

lemma [simp]: "halloc h a = (h', v) \<Longrightarrow> hcontains h x \<Longrightarrow> v \<noteq> x"
  by (induction h) auto

lemma [simp]: "hmap f hempty = hempty"
  by (simp add: hempty_def)

lemma halloc_map [simp]: "halloc h a = (h', v) \<Longrightarrow> halloc (hmap f h) (f a) = (hmap f h', v)"
  by (induction h) auto+

lemma halloc_map_inv [simp]: "halloc (hmap f h) (f a) = (h', v) \<Longrightarrow> 
    \<exists>h''. halloc h a = (h'', v) \<and> h' = hmap f h''"
  by (induction h) auto

lemma [simp]: "hcontains h x \<Longrightarrow> hlookup (hmap f h) x = f (hlookup h x)"
  by (induction h) simp_all

lemma hmap_eq: "(\<And>x. hcontains h x \<Longrightarrow> f (hlookup h x) = g (hlookup h x)) \<Longrightarrow> hmap f h = hmap g h"
proof (induction h)
  case (H h hp)
  have "(\<lambda>x. if x < hp then f (h x) else undefined) = (\<lambda>x. if x < hp then g (h x) else undefined)" 
  proof 
    fix x
    from H show "(if x < hp then f (h x) else undefined) = (if x < hp then g (h x) else undefined)"
      by (simp split: if_splits)
  qed
  thus ?case by simp
qed

primrec stack_contains :: "'a heap \<Rightarrow> ptr list \<Rightarrow> bool" where
  "stack_contains h [] = True"
| "stack_contains h (v # vs) = (hcontains h v \<and> stack_contains h vs)"

primrec env_contains :: "'a heap \<Rightarrow> ptr list list \<Rightarrow> bool" where
  "env_contains h [] = True"
| "env_contains h (v # vs) = (stack_contains h v \<and> env_contains h vs)"

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> stack_contains h vs \<Longrightarrow> stack_contains h' vs"
  by (induction vs) auto

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> env_contains h vs \<Longrightarrow> env_contains h' vs"
  by (induction vs) simp_all

lemma [simp]: "lookup vs x = Some v \<Longrightarrow> stack_contains h vs \<Longrightarrow> hcontains h v"
  by (induction vs x rule: lookup.induct) simp_all

lemma [elim]: "stack_contains h env \<Longrightarrow> x \<in> set env \<Longrightarrow> hcontains h x"
  by (induction env) auto

fun halloc_list' :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list \<Rightarrow> (nat \<Rightarrow> 'a)" where
  "halloc_list' h hp [] = h"
| "halloc_list' h hp (x # xs) = halloc_list' (h(hp := x)) (Suc hp) xs"

primrec halloc_list :: "'a heap \<Rightarrow> 'a list \<Rightarrow> 'a heap \<times> ptr" where
  "halloc_list (H h hp) as = (H (halloc_list' h hp as) (hp + length as), hp)"

function hsplay' :: "('a \<Rightarrow> 'b list) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> (nat \<Rightarrow> 'b) \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 
    (nat \<Rightarrow> 'b) \<times> nat" where
  "hpa \<le> n \<Longrightarrow> hsplay' f ha hpa hb hpb n = (hb, hpb)"
| "hpa > n \<Longrightarrow> hsplay' f ha hpa hb hpb n = 
    hsplay' f ha hpa (halloc_list' hb hpb (f (ha n))) (hpb + length (f (ha n))) (Suc n)"
  by atomize_elim auto
termination
  by (relation "measure (\<lambda>(_, _, hpa, _, _, n). hpa - n)") simp_all

primrec hsplay :: "('a \<Rightarrow> 'b list) \<Rightarrow> 'a heap \<Rightarrow> 'b heap" where
  "hsplay f (H h hp) = (case hsplay' f h hp (\<lambda>x. undefined) 0 0 of (h', hp') \<Rightarrow> H h' hp')"

lemma [simp]: "y < hp \<Longrightarrow> halloc_list' h hp as y = h y" 
  by (induction as arbitrary: h hp) simp_all

lemma [simp]: "halloc_list h as = (h', x) \<Longrightarrow> hcontains h y \<Longrightarrow> hlookup h' y = hlookup h y" 
  by (induction h) auto

lemma [simp]: "k < length as \<Longrightarrow> halloc_list' h hp as (k + hp) = as ! k"
proof (induction as arbitrary: h hp k)
  case (Cons a as)
  thus ?case 
  proof (induction k)
    case (Suc k)
    hence "halloc_list' (h(hp := a)) (Suc hp) as (k + (Suc hp)) = as ! k" by fastforce
    thus ?case by simp
  qed simp_all
qed simp_all

lemma [simp]: "halloc_list h as = (h', p) \<Longrightarrow> k < length as \<Longrightarrow> 
    hlookup h' (k + p) = as ! k"
  by (induction h) (auto split: prod.splits)

lemma [simp]: "(k::nat) < m \<Longrightarrow> x < n \<Longrightarrow> k + m * x < m * n"
proof (induction x arbitrary: n)
  case 0
  thus ?case by (induction n) simp_all
next
  case (Suc x)
  thus ?case by (induction n) simp_all
qed

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

lemma [simp]: "hsplay f hempty = hempty"
  by (simp add: hempty_def)

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

primrec listify' :: "(nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'a list" where
  "listify' h 0 = []"
| "listify' h (Suc x) = h x # listify' h x"

primrec listify :: "'a heap \<Rightarrow> 'a list" where
  "listify (H h hp) = listify' h hp"

lemma [dest]: "listify' h x = [] \<Longrightarrow> x = 0"
  by (induction x) simp_all

lemma [dest]: "listify' h x = a # as \<Longrightarrow> \<exists>y. x = Suc y \<and> h y = a \<and> listify' h y = as"
  by (induction x) simp_all

lemma [simp]: "hp \<le> x \<Longrightarrow> listify' (h(x := v)) hp = listify' h hp"
  by (induction hp) simp_all

end