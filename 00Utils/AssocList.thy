theory AssocList
  imports Utils Environment
begin

fun remove_first :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> ('a \<times> 'b) list" where
  "remove_first [] a' = []"
| "remove_first ((a, b) # ab) a' = (if a = a' then ab else (a, b) # remove_first ab a')"

primrec map_by_assoc_list :: "('a \<times> 'b) list \<Rightarrow> 'a list \<Rightarrow> 'b list" where
  "map_by_assoc_list ab [] = []"
| "map_by_assoc_list ab (a # as) = the (map_of ab a) # map_by_assoc_list (remove_first ab a) as"

lemma [simp]: "map fst (remove_first as a) = remove1 a (map fst as)"
  by (induction as a rule: remove_first.induct) simp_all

lemma [simp]: "a \<noteq> b \<Longrightarrow> map_of (remove_first as b) a = map_of as a"
  by (induction as b rule: remove_first.induct) simp_all

lemma [simp]: "map_by_assoc_list ((a, b) # ab) (insert_at 0 a as) = 
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

lemma [simp]: "map_of ab a = Some b \<Longrightarrow> mset (map fst ab) = mset as \<Longrightarrow> idx_of as a \<noteq> None"
proof (induction ab arbitrary: as)
  case (Cons a' ab)
  thus ?case 
  proof (induction a')
    case (Pair a' b')
    thus ?case
    proof (induction as)
      case (Cons a'' as)
      thus ?case
      proof (cases "a = a''")
        case False note F'' = False
        thus ?thesis
        proof (cases "a = a'")
          case True
          from Cons have "add_mset a' (mset (map fst ab)) - {# a'' #} = 
            add_mset a'' (mset as) - {# a'' #}" by simp
          with True False have "add_mset a (mset (map fst ab) - {# a'' #}) = mset as" by simp
          moreover have "a \<in># add_mset a (mset (map fst ab) - {# a'' #})" by simp
          ultimately show ?thesis by simp
        next
          case False note F' = False
          with Cons show ?thesis
          proof (cases "a' = a''")
            case False
            from Cons have "add_mset a' (mset (map fst ab)) - {# a' #} = 
              add_mset a'' (mset as) - {# a' #}" by simp
            with False have "mset (map fst ab) = mset (a'' # (remove1 a' as))" by simp
            with Cons F' have "idx_of (a'' # (remove1 a' as)) a \<noteq> None" by fastforce
            with F'' F' show ?thesis by simp
          qed simp_all
        qed
      qed simp_all
    qed simp_all
  qed
qed simp_all

end