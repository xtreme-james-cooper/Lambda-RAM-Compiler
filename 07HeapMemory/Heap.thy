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
  "hmap f (H h hp) = H (f \<circ> h) hp"

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> hlookup h' y = (if x = y then a else hlookup h y) "
  by (induction h) (auto split: if_splits)

lemma [simp]: "hcontains h x \<Longrightarrow> halloc h a = (h', y) \<Longrightarrow> hcontains h' x"
  by (induction h) auto

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> hcontains h' x"
  by (induction h) auto

lemma heap_lookup_all: "hlookup h x = a \<Longrightarrow> heap_all p h \<Longrightarrow> hcontains h x \<Longrightarrow> p x a"
  by (induction h) auto

lemma [elim]: "heap_all p h \<Longrightarrow> halloc h a = (h', x) \<Longrightarrow> p x a \<Longrightarrow> heap_all p h'"
  by (induction h) auto

lemma [elim]: "(\<And>x y. p x y \<Longrightarrow> q x y) \<Longrightarrow> heap_all p h \<Longrightarrow> heap_all q h"
  by (induction h) simp_all

lemma [simp]: "heap_all f hempty"
  by (simp add: hempty_def)

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> hcontains h y \<Longrightarrow> y < x"
  by (induction h) auto

lemma [simp]: "halloc h a = (h', v) \<Longrightarrow> hcontains h x \<Longrightarrow> v \<noteq> x"
  by (induction h) auto

lemma halloc_map [simp]: "halloc h a = (h', v) \<Longrightarrow> halloc (hmap f h) (f a) = (hmap f h', v)"
  by (induction h) auto+

lemma [simp]: "hlookup (hmap f h) x = f (hlookup h x)"
  by (induction h) simp_all

primrec halloc_list :: "'a heap \<Rightarrow> 'a list \<Rightarrow> 'a heap \<times> ptr" where
  "halloc_list h [] = (h, undefined)"
| "halloc_list h (x # xs) = (case halloc h x of
      (h', p) \<Rightarrow> (case halloc_list h' xs of
          (h'', p') \<Rightarrow> (h'', p)))"

primrec hlookup_list :: "nat heap \<Rightarrow> ptr \<Rightarrow> nat \<Rightarrow> nat list" where
  "hlookup_list h x 0 = []"
| "hlookup_list h x (Suc n) = hlookup h x # hlookup_list h (Suc x) n"

primrec hsplay' :: "((ptr \<Rightarrow> ptr) \<Rightarrow> 'a \<Rightarrow> 'b list) \<Rightarrow> (nat \<Rightarrow> 'a) \<Rightarrow> nat \<Rightarrow> 'b heap \<times> (ptr \<Rightarrow> ptr)" 
    where
  "hsplay' f h 0 = (hempty, \<lambda>x. undefined)"
| "hsplay' f h (Suc hp) = (case hsplay' f h hp of
      (h', mp) \<Rightarrow> (case halloc_list h' (f mp (h hp)) of
          (h'', x) \<Rightarrow> (h'', mp(hp := x))))"

fun hsplay :: "((ptr \<Rightarrow> ptr) \<Rightarrow> 'a \<Rightarrow> 'b list) \<Rightarrow> 'a heap \<Rightarrow> 'b heap \<times> (ptr \<Rightarrow> ptr)" where
  "hsplay f (H h hp) = hsplay' f h hp"

lemma [simp]: "hsplay f hempty = (hempty, \<lambda>x. undefined)"
  by (simp add: hempty_def)

lemma [simp]: "x \<ge> hp \<Longrightarrow> hsplay' f (h(x := v)) hp = hsplay' f h hp"
  by (induction hp) simp_all

lemma [simp]: "halloc h v = (h', x) \<Longrightarrow> hsplay f h = (h\<^sub>1, mp) \<Longrightarrow> 
    halloc_list h\<^sub>1 (f mp v) = (h\<^sub>2, y) \<Longrightarrow> hsplay f h' = (h\<^sub>2, mp(x := y))"
  by (induction h) fastforce

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

end