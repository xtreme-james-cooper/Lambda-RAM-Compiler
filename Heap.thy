theory Heap
  imports Main
begin

datatype ptr = P nat

primrec ptrSize :: "ptr \<Rightarrow> nat" where
  "ptrSize (P x) = x"

fun ptr_less :: "ptr \<Rightarrow> ptr \<Rightarrow> bool" where
  "ptr_less x y = (ptrSize x > ptrSize y)"

datatype 'a heap = H "nat \<Rightarrow> 'a" nat

definition hempty :: "'a heap" where
  "hempty = H (\<lambda>x. undefined) 0"
 
primrec halloc :: "'a heap \<Rightarrow> 'a \<Rightarrow> 'a heap \<times> ptr" where
  "halloc (H h hp) a = (H (h(hp := a)) (Suc hp), P hp)"

fun hlookup :: "'a heap \<Rightarrow> ptr \<Rightarrow> 'a" where
  "hlookup (H h hp) (P x) = h x"

fun hcontains :: "'a heap \<Rightarrow> ptr \<Rightarrow> bool" where
  "hcontains (H h hp) (P x) = (x < hp)"

primrec heap_all :: "(ptr \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a heap \<Rightarrow> bool" where
  "heap_all p (H h hp) = (\<forall>x < hp. p (P x) (h x))"

primrec hmap :: "('a \<Rightarrow> 'b) \<Rightarrow> 'a heap \<Rightarrow> 'b heap" where
  "hmap f (H h hp) = H (f \<circ> h) hp"

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> hlookup h' y = (if x = y then a else hlookup h y) "
  by (induction h y rule: hlookup.induct) (auto split: if_splits)

lemma [simp]: "hcontains h x \<Longrightarrow> halloc h a = (h', y) \<Longrightarrow> hcontains h' x"
  by (induction h x rule: hcontains.induct) auto

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> hcontains h' x"
  by (induction h x rule: hcontains.induct) auto

lemma heap_lookup_all: "hlookup h x = a \<Longrightarrow> heap_all p h \<Longrightarrow> hcontains h x \<Longrightarrow> p x a"
  by (induction h x rule: hcontains.induct) auto

lemma [elim]: "heap_all p h \<Longrightarrow> halloc h a = (h', x) \<Longrightarrow> p x a \<Longrightarrow> heap_all p h'"
  by (induction h) auto

lemma [elim]: "(\<And>x y. p x y \<Longrightarrow> q x y) \<Longrightarrow> heap_all p h \<Longrightarrow> heap_all q h"
  by (induction h) simp_all

lemma [simp]: "heap_all f hempty"
  by (simp add: hempty_def)

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> hcontains h y \<Longrightarrow> ptrSize y < ptrSize x"
  by (induction h y rule: hcontains.induct) auto

lemma [simp]: "halloc h a = (h', v) \<Longrightarrow> hcontains h x \<Longrightarrow> v \<noteq> x"
  by (induction h x rule: hcontains.induct) auto

lemma [simp]: "halloc h a = (h', v) \<Longrightarrow> halloc (hmap f h) (f a) = (hmap f h', v)"
  by (induction h) auto+

end