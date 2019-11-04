theory Heap
  imports Main
begin

datatype ptr = P nat

primrec ptrSize :: "ptr \<Rightarrow> nat" where
  "ptrSize (P x) = x"

fun ptr_less :: "ptr \<Rightarrow> ptr \<Rightarrow> bool" where
  "ptr_less x y = (ptrSize x > ptrSize y)"

datatype 'a heap = H "ptr \<Rightarrow> 'a" nat

definition hempty :: "'a heap" where
  "hempty = H (\<lambda>x. undefined) 0"
 
primrec halloc :: "'a heap \<Rightarrow> 'a \<Rightarrow> 'a heap \<times> ptr" where
  "halloc (H h hp) a = (H (h(P hp := a)) (Suc hp), P hp)"

primrec hlookup :: "'a heap \<Rightarrow> ptr \<Rightarrow> 'a" where
  "hlookup (H h hp) x = h x"

fun hcontains :: "'a heap \<Rightarrow> ptr \<Rightarrow> bool" where
  "hcontains (H h hp) (P x) = (x < hp)"

primrec heap_all :: "('a \<Rightarrow> bool) \<Rightarrow> 'a heap \<Rightarrow> bool" where
  "heap_all p (H h hp) = (\<forall>x < hp. p (h (P x)))"

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> hlookup h' y = (if x = y then a else hlookup h y) "
  by (induction h) auto

lemma [simp]: "hcontains h x \<Longrightarrow> halloc h a = (h', y) \<Longrightarrow> hcontains h' x"
  by (induction h x rule: hcontains.induct) auto

lemma [simp]: "halloc h a = (h', x) \<Longrightarrow> hcontains h' x"
  by (induction h x rule: hcontains.induct) auto

lemma heap_lookup_all: "hlookup h x = a \<Longrightarrow> heap_all p h \<Longrightarrow> hcontains h x \<Longrightarrow> p a"
  by (induction h x rule: hcontains.induct) auto

lemma [elim]: "heap_all p h \<Longrightarrow> halloc h a = (h', x) \<Longrightarrow> p a \<Longrightarrow> heap_all p h'"
  by (induction h) auto

lemma [elim]: "(\<And>x. p x \<Longrightarrow> q x) \<Longrightarrow> heap_all p h \<Longrightarrow> heap_all q h"
  by (induction h) simp_all

lemma [simp]: "heap_all f hempty"
  by (simp add: hempty_def)

end