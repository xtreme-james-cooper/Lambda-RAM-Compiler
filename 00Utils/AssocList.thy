theory AssocList
  imports Utils Environment
begin

subsection \<open>Association Lists\<close>

text \<open>Our final utility is an association list method, for use in the name-removal phase.
The \<open>map_by_assoc_list\<close> function maps an environment through an association list, but each 
association can only be used once. We need this flexibility (instead of just using the standard 
library's \<open>map_of\<close> function) because the source language permits name-shadowing.\<close>

fun remove_first :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b) list" where
  "remove_first [] a' = []"
| "remove_first ((a, b) # ab) a' = (if a = a' then ab else (a, b) # remove_first ab a')"

primrec map_by_assoc_list :: "('a \<times> 'b) list \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_by_assoc_list ab [] = []"
| "map_by_assoc_list ab (a # as) = the (map_of ab a) # map_by_assoc_list (remove_first ab a) as"

lemma map_remove_fst [simp]: "map fst (remove_first as a) = remove1 a (map fst as)"
  by (induction as a rule: remove_first.induct) simp_all

lemma map_of_remove_fst [simp]: "a \<noteq> b \<Longrightarrow> map_of (remove_first as b) a = map_of as a"
  by (induction as b rule: remove_first.induct) simp_all

lemma map_by_assoc_insert [simp]: "map_by_assoc_list ((a, b) # ab) (insert_at 0 a as) = 
    insert_at 0 b (map_by_assoc_list ab as)"
  by (induction as) simp_all

lemma lookup_by_assoc_list [simp]: "mset (map fst ab) = mset as \<Longrightarrow> idx_of as a = Some x \<Longrightarrow>
  lookup (map_by_assoc_list ab as) x = map_of ab a" 
proof (induction as arbitrary: ab x)
  case (Cons a' as)
  thus ?case
  proof (induction x)
    case 0
    moreover hence "a' = a \<or> (a' \<noteq> a \<and> map_option Suc (idx_of as a) = Some 0)" by fastforce
    ultimately show ?case by simp
  next
    case (Suc x)
    moreover hence "a' \<noteq> a" by fastforce
    moreover with Suc have "idx_of as a = Some x" by fastforce
    moreover from Suc have "mset (map fst (remove_first ab a')) = mset as" by simp
    ultimately show ?case by fastforce
  qed
qed simp_all

end