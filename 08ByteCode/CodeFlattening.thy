theory CodeFlattening
  imports ByteCode "../07TreeCode/TreeCode"
begin

subsection \<open>Code Flattening\<close>

text \<open>Flattening code is mostly just a map from tree-code operations to bytecode ones; but whenever 
we reach a nested codeblock, we pull it out and convert it first. As a result, all code-pointers in
the flattened codeblock point towards lower addresses. The first argument is the first free address;
each nested codeblock is put there and then the argument is updated to its new, further-along 
position.\<close>

fun flatten_code' :: "nat \<Rightarrow> code\<^sub>e list \<Rightarrow> code\<^sub>b list" where
  "flatten_code' p [] = []"
| "flatten_code' p (Lookup\<^sub>e x y # \<C>) = flatten_code' p \<C> @ [Lookup\<^sub>b x y]"
| "flatten_code' p (PushCon\<^sub>e n # \<C>) = flatten_code' p \<C> @ [PushCon\<^sub>b n]"
| "flatten_code' p (PushLam\<^sub>e \<C>' n # \<C>) = (
    let \<C>\<^sub>b' = flatten_code' p \<C>' @ [Alloc\<^sub>b n]
    in \<C>\<^sub>b' @ flatten_code' (p + length \<C>\<^sub>b') \<C> @ [PushLam\<^sub>b (p + length \<C>\<^sub>b')])"
| "flatten_code' p (Apply\<^sub>e # \<C>) = flatten_code' p \<C> @ [Apply\<^sub>b]"
| "flatten_code' p (PushEnv\<^sub>e n # \<C>) = flatten_code' p \<C> @ [PushEnv\<^sub>b n]"
| "flatten_code' p (Return\<^sub>e # \<C>) = flatten_code' p \<C> @ [Return\<^sub>b]"
| "flatten_code' p (Jump\<^sub>e # \<C>) = flatten_code' p \<C> @ [Jump\<^sub>b]"

definition flatten_code :: "code\<^sub>e list \<Rightarrow> code\<^sub>b list" where
  "flatten_code \<C> \<equiv> flatten_code' 0 \<C>"

lemma properly_terminated_flatten' [simp]: "properly_terminated\<^sub>e \<C> \<Longrightarrow> 
    properly_terminated\<^sub>b (flatten_code' p \<C> @ \<C>')"
  by (induction p \<C> arbitrary: \<C>' rule: flatten_code'.induct) 
     (auto simp add: Let_def split: if_splits)

lemma properly_terminated_flatten [simp]: "properly_terminated\<^sub>e \<C> \<Longrightarrow> 
  properly_terminated\<^sub>b (flatten_code \<C>)"
proof (unfold flatten_code_def)
  assume "properly_terminated\<^sub>e \<C>"
  hence "properly_terminated\<^sub>b (flatten_code' 0 \<C> @ [])" by (metis properly_terminated_flatten')
  thus "properly_terminated\<^sub>b (flatten_code' 0 \<C>)" by simp
qed

text \<open>We also define a function to directly calculate the length of a flattened piece of code. (The
reason we do not use \<open>length (flatten_code' p \<C>)\<close> is that the p argument is irrelevant to the 
length.)\<close>

primrec code_size :: "code\<^sub>e \<Rightarrow> nat"
    and code_list_size :: "code\<^sub>e list \<Rightarrow> nat" where
  "code_size (Lookup\<^sub>e x y) = 1"
| "code_size (PushCon\<^sub>e n) = 1"
| "code_size (PushLam\<^sub>e \<C> n) = Suc (Suc (code_list_size \<C>))"
| "code_size Apply\<^sub>e = 1"
| "code_size (PushEnv\<^sub>e n) = 1"
| "code_size Return\<^sub>e = 1"
| "code_size Jump\<^sub>e = 1"
| "code_list_size [] = 0"
| "code_list_size (op # \<C>) = code_size op + code_list_size \<C>"

lemma length_flatten' [simp]: "length (flatten_code' p \<C>) = code_list_size \<C>"
  by (induction p \<C> rule: flatten_code'.induct) simp_all

lemma length_flatten [simp]: "length (flatten_code \<C>) = code_list_size \<C>"
  by (simp add: flatten_code_def)

lemma code_size_nz [simp]: "0 < code_size op"
  by (induction op) simp_all

lemma code_list_size_empty [simp]: "(code_list_size \<C> = 0) = (\<C> = [])"
  by (induction \<C>) simp_all

lemma index_into_append [simp]: "
    lookup (flatten_code' m \<C> @ \<C>') (code_list_size \<C> + n) = lookup \<C>' n"
  by (metis length_flatten' lookup_append_snd)

lemma index_into_flatten [simp]: "lookup (flatten_code' n \<C> @ op # \<C>') (code_list_size \<C>) = Some op"
proof -
  have "lookup (flatten_code' n \<C> @ op # \<C>') (code_list_size \<C> + 0) = lookup (op # \<C>') 0" 
    by (metis index_into_append)
  thus ?thesis by simp
qed

text \<open>One might think that, like previous compilation passes, we could simply map \<open>flatten_code\<close> up
the levels of the state and produce a compiled state. Unfortunately, we cannot. Once evaluation 
begins, the code stored in the tree-code stack could come from all over the codebase, and there is 
no guarantee that \<open>flatten_code\<close> would assign the right internal addresses. The structure of the 
code would be the same, of course, but rather than get bogged down in trying to define an 
"alpha-equivalence for code pointers" we cut to the chase and define a code-unflattening function. 
Note the importance for termination of each nested code pointer being less than the address of its 
operation.\<close>

primrec alloc_size :: "code\<^sub>b list \<Rightarrow> nat \<Rightarrow> nat" where
  "alloc_size \<C> 0 = undefined"
| "alloc_size \<C> (Suc p) = (case lookup \<C> p of
      Some (Alloc\<^sub>b n) \<Rightarrow> n
    | _ \<Rightarrow> undefined)"

fun unflatten_code :: "code\<^sub>b list \<Rightarrow> nat \<Rightarrow> code\<^sub>e list" where
  "unflatten_code \<C> 0 = []"
| "unflatten_code \<C> (Suc p) = (case lookup \<C> p of
      Some (Lookup\<^sub>b x y) \<Rightarrow> Lookup\<^sub>e x y # unflatten_code \<C> p
    | Some (PushCon\<^sub>b n) \<Rightarrow>  PushCon\<^sub>e n # unflatten_code \<C> p
    | Some (PushLam\<^sub>b p') \<Rightarrow> (
        if p' \<le> p then PushLam\<^sub>e (unflatten_code \<C> p') (alloc_size \<C> p') # unflatten_code \<C> p 
        else undefined) 
    | Some (Alloc\<^sub>b n) \<Rightarrow> unflatten_code \<C> p
    | Some Apply\<^sub>b \<Rightarrow> Apply\<^sub>e # unflatten_code \<C> p
    | Some (PushEnv\<^sub>b n) \<Rightarrow> PushEnv\<^sub>e n # unflatten_code \<C> p
    | Some Return\<^sub>b \<Rightarrow> [Return\<^sub>e]
    | Some Jump\<^sub>b \<Rightarrow> [Jump\<^sub>e]
    | None \<Rightarrow> undefined)"

primrec unflatten_closure :: "code\<^sub>b list \<Rightarrow> closure\<^sub>b \<Rightarrow> closure\<^sub>e" where
  "unflatten_closure \<C> (Const\<^sub>b n) = Const\<^sub>e n"
| "unflatten_closure \<C> (Lam\<^sub>b \<Delta> p) = 
    Lam\<^sub>e (map (map (unflatten_closure \<C>)) \<Delta>) (unflatten_code \<C> p) (alloc_size \<C> p)"

abbreviation unflatten_values :: "code\<^sub>b list \<Rightarrow> closure\<^sub>b list \<Rightarrow> closure\<^sub>e list" where
  "unflatten_values \<C> \<V> \<equiv> map (unflatten_closure \<C>) \<V>"

primrec unflatten_frame :: "code\<^sub>b list \<Rightarrow> (closure\<^sub>b list list \<times> nat) \<Rightarrow> frame\<^sub>e" where
  "unflatten_frame \<C> (\<Delta>, p) = (map (unflatten_values \<C>) \<Delta>, unflatten_code \<C> p)"

abbreviation unflatten_stack :: "code\<^sub>b list \<Rightarrow> (closure\<^sub>b list list \<times> nat) list \<Rightarrow> frame\<^sub>e list" where
  "unflatten_stack \<C> s \<equiv> map (unflatten_frame \<C>) s"

primrec unflatten_state :: "code\<^sub>b list \<Rightarrow> state\<^sub>b \<Rightarrow> state\<^sub>e" where
  "unflatten_state \<C> (S\<^sub>b \<V> s) = S\<^sub>e (unflatten_values \<C> \<V>) (unflatten_stack \<C> s)"

lemma unflatten_alloc_front [simp]: "p \<le> length \<C> \<Longrightarrow> alloc_size (\<C> @ \<C>') p = alloc_size \<C> p"
  by (induction p) simp_all

lemma unflatten_front [simp]: "p \<le> length \<C> \<Longrightarrow> unflatten_code (\<C> @ \<C>') p = unflatten_code \<C> p"
  by (induction \<C> p rule: unflatten_code.induct) (simp_all split: option.splits code\<^sub>b.splits) 

lemma unflatten_flatten' [simp]: "properly_terminated\<^sub>e \<C> \<Longrightarrow> 
  unflatten_code (\<C>' @ flatten_code' (length \<C>') \<C> @ \<C>'') (length \<C>' + code_list_size \<C>) = \<C>"
proof (induction "length \<C>'" \<C> arbitrary: \<C>' \<C>'' rule: flatten_code'.induct)
  case (4 \<C>\<^sub>2 n \<C>\<^sub>1)
  let ?pc = "Suc (length \<C>' + code_list_size \<C>\<^sub>2)"
  let ?code' = "\<C>' @ flatten_code' (length \<C>') \<C>\<^sub>2 @ [Alloc\<^sub>b n]"
  let ?code = "?code' @ flatten_code' ?pc \<C>\<^sub>1 @ PushLam\<^sub>b ?pc # \<C>''"
  have X: "length \<C>' + length (flatten_code' (length \<C>') \<C>\<^sub>2 @ [Alloc\<^sub>b n]) = length ?code'" by simp
  from 4 have "properly_terminated\<^sub>e \<C>\<^sub>1" by simp
  with 4 X have "unflatten_code (?code' @ flatten_code' (length ?code') \<C>\<^sub>1 @
    PushLam\<^sub>b (Suc (length \<C>' + length (flatten_code' (length \<C>') \<C>\<^sub>2))) # \<C>'')
      (length ?code' + code_list_size \<C>\<^sub>1) = \<C>\<^sub>1" by blast
  with 4 have X: "unflatten_code ?code (?pc + code_list_size \<C>\<^sub>1) = \<C>\<^sub>1" by simp
  from 4 have "properly_terminated\<^sub>e \<C>\<^sub>2" by simp
  with 4 have "unflatten_code ?code' (length \<C>' + code_list_size \<C>\<^sub>2) = \<C>\<^sub>2" by blast
  hence "unflatten_code ?code' ?pc = \<C>\<^sub>2" by simp
  moreover from 4 have "?pc \<le> length ?code'" by simp
  ultimately have Y: "unflatten_code ?code ?pc = \<C>\<^sub>2" by (metis unflatten_front)
  have "lookup (Alloc\<^sub>b n # flatten_code' ?pc \<C>\<^sub>1 @ PushLam\<^sub>b ?pc # \<C>'') (Suc (code_list_size \<C>\<^sub>1)) =
    Some (PushLam\<^sub>b (Suc (length \<C>' + code_list_size \<C>\<^sub>2)))" by simp
  hence "lookup (\<C>' @ flatten_code' (length \<C>') \<C>\<^sub>2 @ Alloc\<^sub>b n # flatten_code' ?pc \<C>\<^sub>1 @ 
    PushLam\<^sub>b ?pc # \<C>'') (length \<C>' + (code_list_size \<C>\<^sub>2 + Suc (code_list_size \<C>\<^sub>1))) =
      Some (PushLam\<^sub>b (Suc (length \<C>' + code_list_size \<C>\<^sub>2)))"
    by (metis lookup_append_snd index_into_append)
  with X Y show ?case by (simp add: add.assoc)
qed simp_all

lemma unflatten_flatten [simp]: "properly_terminated\<^sub>e \<C> \<Longrightarrow> 
  unflatten_code (flatten_code \<C>) (code_list_size \<C>) = \<C>"
proof -
  assume "properly_terminated\<^sub>e \<C>"
  hence "unflatten_code ([] @ flatten_code' (length []) \<C> @ []) 
    (length [] + code_list_size \<C>) = \<C>" by (metis unflatten_flatten' list.size(3))
  thus ?thesis by (simp add: flatten_code_def)
qed

text \<open>We have noted already that all the pointers in the codebase should go towards smaller 
addresses. We now define some predicates to assert this formally:\<close>

fun orderly_op :: "nat \<Rightarrow> code\<^sub>b \<Rightarrow> bool" where
  "orderly_op n (PushLam\<^sub>b p) = (0 < p \<and> p \<le> n)"
| "orderly_op n _ = True"

primrec orderly_code :: "code\<^sub>b list \<Rightarrow> nat \<Rightarrow> bool" where
  "orderly_code [] n = True"
| "orderly_code (op # cd) n = (orderly_op n op \<and> orderly_code cd (Suc n))"

primrec orderly_closure :: "nat \<Rightarrow> closure\<^sub>b \<Rightarrow> bool" where
  "orderly_closure n (Const\<^sub>b m) = True"
| "orderly_closure n (Lam\<^sub>b \<Delta> p) = (0 < p \<and> p \<le> n \<and> list_all (list_all (orderly_closure n)) \<Delta>)"

fun orderly_stack :: "(closure\<^sub>b list list \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "orderly_stack [] n = True"
| "orderly_stack ((\<Delta>, 0) # s) n = False"
| "orderly_stack ((\<Delta>, Suc p) # s) n = 
    (p < n \<and> \<Delta> \<noteq> [] \<and> list_all (list_all (orderly_closure n)) \<Delta> \<and> orderly_stack s n)"

primrec orderly_state :: "code\<^sub>b list \<Rightarrow> state\<^sub>b \<Rightarrow> bool" where
  "orderly_state \<C> (S\<^sub>b \<V> s) = (orderly_code \<C> 0 \<and> properly_terminated\<^sub>b \<C> \<and> block_structured\<^sub>b \<C> \<and>
    orderly_stack s (length \<C>) \<and> list_all (orderly_closure (length \<C>)) \<V>)"

lemma orderly_append [simp]: "orderly_code (\<C> @ \<C>') n = 
      (orderly_code \<C> n \<and> orderly_code \<C>' (length \<C> + n))"
  by (induction \<C> arbitrary: n) simp_all

lemma orderly_flatten' [simp]: "p \<le> n \<Longrightarrow> properly_terminated\<^sub>e \<C> \<Longrightarrow> 
    orderly_code (flatten_code' p \<C>) n"
  by (induction p \<C> arbitrary: n rule: flatten_code'.induct) auto

lemma orderly_flatten [simp]: "properly_terminated\<^sub>e \<C> \<Longrightarrow> orderly_code (flatten_code \<C>) 0"
  by (simp add: flatten_code_def)

lemma orderly_empty_frame [simp]: "x > 0 \<Longrightarrow> orderly_stack [([[]], x)] x"
  by (cases x) simp_all

lemma orderly_length_flatten [simp]: "\<C> \<noteq> [] \<Longrightarrow> 
    orderly_stack [([[]], length (flatten_code \<C>))] (length (flatten_code \<C>))"
  by (induction \<C>) simp_all

lemma orderly_code_size [simp]: "\<C> \<noteq> [] \<Longrightarrow> 
    orderly_stack [([[]], code_list_size \<C>)] (code_list_size \<C>)"
proof -
  assume "\<C> \<noteq> []"
  moreover hence "orderly_stack [([[]], length (flatten_code \<C>))] (length (flatten_code \<C>))" 
    by (metis orderly_length_flatten)
  ultimately show ?thesis by simp
qed

lemma pushlam_ordered' [simp]: "lookup \<C> x = Some (PushLam\<^sub>b p) \<Longrightarrow> orderly_code \<C> n \<Longrightarrow> 
    x < length \<C> \<Longrightarrow> 0 < p \<and> p \<le> length \<C> + n"
  by (induction \<C> x arbitrary: n rule: lookup.induct) fastforce+

lemma pushlam_ordered [simp]: "lookup \<C> x = Some (PushLam\<^sub>b p) \<Longrightarrow> orderly_code \<C> 0 \<Longrightarrow> 
    x < length \<C> \<Longrightarrow> 0 < p \<and> p \<le> length \<C>"
  using pushlam_ordered' by fastforce

lemma orderly_lam' [simp]: "lookup \<C> p = Some (PushLam\<^sub>b p') \<Longrightarrow> orderly_code \<C> n \<Longrightarrow> p' \<le> p + n"
  by (induction \<C> p arbitrary: n rule: lookup.induct) fastforce+

lemma orderly_lam [simp]: "lookup \<C> p = Some (PushLam\<^sub>b p') \<Longrightarrow> orderly_code \<C> 0 \<Longrightarrow> p' \<le> p"
  using orderly_lam' by fastforce

text \<open>Evaluation preserves the property of being orderly:\<close>

lemma eval_preserves_orderly [simp]: "\<C>\<^sub>b \<tturnstile> \<Sigma>\<^sub>b \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state \<C>\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow> 
  orderly_state \<C>\<^sub>b \<Sigma>\<^sub>b'"
proof (induction \<C>\<^sub>b \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: eval\<^sub>b.induct)
  case (ev\<^sub>b_lookup cd pc x y env vs v \<V> s)
  thus ?case by (cases pc, cases cd) auto
next
  case (ev\<^sub>b_pushcon cd pc k vs env s)
  thus ?case by (cases pc, cases cd) simp_all
next
  case (ev\<^sub>b_pushlam cd pc pc' vs env s)
  thus ?case 
  proof (cases pc)
    case 0
    with ev\<^sub>b_pushlam show ?thesis by (cases cd) simp_all
  qed simp_all
next
  case (ev\<^sub>b_alloc \<C> pc n \<V> \<Delta> s)
  thus ?case by (cases pc, cases \<C>) simp_all
next
  case (ev\<^sub>b_apply cd pc v env' pc' vs env s)
  thus ?case by (cases pc', simp, cases pc, cases cd) simp_all
next
  case (ev\<^sub>b_pushenv cd pc v vs env s)
  thus ?case by (cases pc, cases cd) simp_all
next
  case (ev\<^sub>b_jump cd pc v env' pc' vs env s)
  thus ?case by (cases pc') simp_all
qed simp_all

lemma iter_eval_preserves_orderly [simp]: "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state \<C>\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow> 
    orderly_state \<C>\<^sub>b \<Sigma>\<^sub>b'"
  by (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: iter.induct) simp_all

text \<open>Because we use an unflattening function rather than a flattening one, completeness is 
straightforward:\<close>

theorem complete\<^sub>b [simp]: "\<C> \<tturnstile> \<Sigma>\<^sub>b \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state \<C> \<Sigma>\<^sub>b \<Longrightarrow> 
  iter (\<leadsto>\<^sub>e) (unflatten_state \<C> \<Sigma>\<^sub>b) (unflatten_state \<C> \<Sigma>\<^sub>b')"
proof (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: eval\<^sub>b.induct)
  case (ev\<^sub>b_lookup \<C> p x y \<Delta> vs v \<V> s)
  hence "S\<^sub>e (unflatten_values \<C> \<V>) ((map (unflatten_values \<C>) \<Delta>, unflatten_code \<C> (Suc p)) # 
    unflatten_stack \<C> s) \<leadsto>\<^sub>e
    S\<^sub>e (unflatten_closure \<C> v # unflatten_values \<C> \<V>) ((map (unflatten_values \<C>) \<Delta>, 
    unflatten_code \<C> p) # unflatten_stack \<C> s)" by simp
  thus ?case by simp
next
  case (ev\<^sub>b_pushcon \<C> p k \<V> \<Delta> s)
  hence "S\<^sub>e (unflatten_values \<C> \<V>) ((map (unflatten_values \<C>) \<Delta>, unflatten_code \<C> (Suc p)) # 
    unflatten_stack \<C> s) \<leadsto>\<^sub>e
    S\<^sub>e (Const\<^sub>e k # unflatten_values \<C> \<V>) ((map (unflatten_values \<C>) \<Delta>, unflatten_code \<C> p) # 
    unflatten_stack \<C> s)" by simp
  thus ?case by simp
next
  case (ev\<^sub>b_pushlam \<C> p p' \<V> \<Delta> s)
  moreover hence X: "p' \<le> p" by auto
  moreover have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (unflatten_values \<C> \<V>) ((map (unflatten_values \<C>) \<Delta>, 
    PushLam\<^sub>e (unflatten_code \<C> p') (alloc_size \<C> p') # unflatten_code \<C> p) # unflatten_stack \<C> s))
    (S\<^sub>e (Lam\<^sub>e (map (unflatten_values \<C>) \<Delta>) (unflatten_code \<C> p') (alloc_size \<C> p') # 
    unflatten_values \<C> \<V>) ((map (unflatten_values \<C>) \<Delta>, unflatten_code \<C> p) # unflatten_stack \<C> s))" 
      by (metis ev\<^sub>e_pushlam iter_one)
  ultimately show ?case by simp
next
  case (ev\<^sub>b_apply \<C> p v \<Delta>' p' \<V> \<Delta> s)
  hence "S\<^sub>e (unflatten_closure \<C> v # Lam\<^sub>e (map (unflatten_values \<C>) \<Delta>') (unflatten_code \<C> p') 
    (alloc_size \<C> p') # unflatten_values \<C> \<V>) 
    ((map (unflatten_values \<C>) \<Delta>, unflatten_code \<C> (Suc p)) # unflatten_stack \<C> s) \<leadsto>\<^sub>e
    S\<^sub>e (unflatten_values \<C> \<V>) (([unflatten_closure \<C> v] # map (unflatten_values \<C>) \<Delta>', 
    unflatten_code \<C> p') # (map (unflatten_values \<C>) \<Delta>, unflatten_code \<C> p) # unflatten_stack \<C> s)" 
      by simp
  thus ?case by simp
next
  case (ev\<^sub>b_pushenv \<C> p n v \<V> \<Delta> s)
  have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (unflatten_closure \<C> v # unflatten_values \<C> \<V>)
    ((map (unflatten_values \<C> )\<Delta>, PushEnv\<^sub>e n # unflatten_code \<C> p) # unflatten_stack \<C> s))
    (S\<^sub>e (unflatten_values \<C> \<V>) ((snoc_fst (unflatten_closure \<C> v) (map (unflatten_values \<C>) \<Delta>), 
      unflatten_code \<C> p) # unflatten_stack \<C> s))" by (metis ev\<^sub>e_pushenv iter_one)
  with ev\<^sub>b_pushenv show ?case by simp
next
  case (ev\<^sub>b_return \<C> p \<V> \<Delta> s)
  moreover have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (unflatten_values \<C> \<V>) ((map (unflatten_values \<C>) \<Delta>, [Return\<^sub>e]) # 
    unflatten_stack \<C> s))
    (S\<^sub>e (unflatten_values \<C> \<V>) (unflatten_stack \<C> s))" by (metis ev\<^sub>e_return iter_one)
  ultimately show ?case by simp
next
  case (ev\<^sub>b_jump \<C> p v \<Delta>' p' \<V> \<Delta> s)
  have "S\<^sub>e (unflatten_closure \<C> v # Lam\<^sub>e (map (unflatten_values \<C>) \<Delta>') (unflatten_code \<C> p') 
    (alloc_size \<C> p') # unflatten_values \<C> \<V>) ((map (unflatten_values \<C>) \<Delta>, [Jump\<^sub>e]) # 
    unflatten_stack \<C> s) \<leadsto>\<^sub>e S\<^sub>e (unflatten_values \<C> \<V>) (([unflatten_closure \<C> v] # 
    map (unflatten_values \<C>) \<Delta>', unflatten_code \<C> p') # unflatten_stack \<C> s)" by (metis ev\<^sub>e_jump)
  with ev\<^sub>b_jump have "S\<^sub>e (unflatten_closure \<C> v # Lam\<^sub>e (map (unflatten_values \<C>) \<Delta>') 
    (unflatten_code \<C> p') (alloc_size \<C> p') # unflatten_values \<C> \<V>)
    ((map (unflatten_values \<C>) \<Delta>, unflatten_code \<C> (Suc p)) # unflatten_stack \<C> s) \<leadsto>\<^sub>e
    S\<^sub>e (unflatten_values \<C> \<V>) (([unflatten_closure \<C> v] # map (unflatten_values \<C>) \<Delta>', 
    unflatten_code \<C> p') # unflatten_stack \<C> s)" by simp
  hence "iter (\<leadsto>\<^sub>e) (S\<^sub>e (unflatten_closure \<C> v # Lam\<^sub>e (map (unflatten_values \<C>) \<Delta>') 
    (unflatten_code \<C> p') (alloc_size \<C> p') # unflatten_values \<C> \<V>)
    ((map (unflatten_values \<C>) \<Delta>, unflatten_code \<C> (Suc p)) # unflatten_stack \<C> s))
    (S\<^sub>e (unflatten_values \<C> \<V>) (([unflatten_closure \<C> v] # map (unflatten_values \<C>) \<Delta>', 
    unflatten_code \<C> p') # unflatten_stack \<C> s))" 
      by (metis iter_one)
  thus ?case by simp
qed simp_all

text \<open>But it means correctness needs the usual supply of reconstruction lemmas. A particular hassle
is the addition of the \<open>Alloc\<^sub>b\<close> opcodes: we don't have to go as far as we did in stage 4, since we
can only ever have one \<open>Alloc\<^sub>b\<close> in a row, but it still complicates the lemmas.\<close>

lemma terminated_to_lookup [dest]: "properly_terminated\<^sub>b \<C>\<^sub>b \<Longrightarrow> lookup \<C>\<^sub>b 0 = Some (PushLam\<^sub>b p) \<Longrightarrow> 
    False"
  by (induction \<C>\<^sub>b) simp_all

lemma unflatten_to_lookup [dest]: "Lookup\<^sub>e x y # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<Longrightarrow> 
  orderly_code \<C>\<^sub>b 0 \<Longrightarrow> p < length \<C>\<^sub>b \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow> 
    (lookup \<C>\<^sub>b p = Some (Lookup\<^sub>b x y) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
    (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some (Lookup\<^sub>b x y) \<and> 
      \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')"
  by (cases p) (auto split: option.splits code\<^sub>b.splits)

lemma unflatten_to_pushcon [dest]: "PushCon\<^sub>e n # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<Longrightarrow> 
  orderly_code \<C>\<^sub>b 0 \<Longrightarrow> p < length \<C>\<^sub>b \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow> 
    (lookup \<C>\<^sub>b p = Some (PushCon\<^sub>b n) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
    (\<exists>p' m. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b m) \<and> lookup \<C>\<^sub>b p' = Some (PushCon\<^sub>b n) \<and> 
      \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')"
  by (cases p) (auto split: option.splits code\<^sub>b.splits)

lemma unflatten_to_pushlam [dest]: "PushLam\<^sub>e \<C>\<^sub>e' n # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<Longrightarrow> 
  orderly_code \<C>\<^sub>b 0 \<Longrightarrow> p < length \<C>\<^sub>b \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow>
    \<exists>p'. \<C>\<^sub>e' = unflatten_code \<C>\<^sub>b p' \<and> n = alloc_size \<C>\<^sub>b p' \<and>
      ((lookup \<C>\<^sub>b p = Some (PushLam\<^sub>b p') \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or> 
      (\<exists>p'' m. p = Suc p'' \<and> lookup \<C>\<^sub>b (Suc p'') = Some (Alloc\<^sub>b m) \<and> 
        lookup \<C>\<^sub>b p'' = Some (PushLam\<^sub>b p') \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p''))"
  by (cases p) (auto split: option.splits code\<^sub>b.splits)

lemma unflatten_to_apply [dest]: "Apply\<^sub>e # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<Longrightarrow> orderly_code \<C>\<^sub>b 0 \<Longrightarrow> 
    p < length \<C>\<^sub>b \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow> 
      (lookup \<C>\<^sub>b p = Some Apply\<^sub>b \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
      (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some Apply\<^sub>b \<and> 
        \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')"
  by (cases p) (auto split: option.splits code\<^sub>b.splits)

lemma unflatten_to_pushenv [dest]: "PushEnv\<^sub>e n # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<Longrightarrow>
     orderly_code \<C>\<^sub>b 0 \<Longrightarrow> p < length \<C>\<^sub>b \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow> 
      (lookup \<C>\<^sub>b p = Some (PushEnv\<^sub>b n) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or> 
      (\<exists>p' m. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b m) \<and> lookup \<C>\<^sub>b p' = Some (PushEnv\<^sub>b n) \<and> 
        \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')"
  by (cases p) (auto split: option.splits code\<^sub>b.splits)

lemma unflatten_to_return [dest]: "Return\<^sub>e # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<Longrightarrow> 
    orderly_code \<C>\<^sub>b 0 \<Longrightarrow> p < length \<C>\<^sub>b \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow> 
      (lookup \<C>\<^sub>b p = Some Return\<^sub>b \<or> 
      (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some Return\<^sub>b)) \<and> 
        \<C>\<^sub>e = []"
  by (cases p) (auto split: option.splits code\<^sub>b.splits)

lemma unflatten_to_jump [dest]: "Jump\<^sub>e # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<Longrightarrow> 
    orderly_code \<C>\<^sub>b 0 \<Longrightarrow> p < length \<C>\<^sub>b \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow> 
      (lookup \<C>\<^sub>b p = Some Jump\<^sub>b \<and> \<C>\<^sub>e = []) \<or>
      (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some Jump\<^sub>b \<and> 
        \<C>\<^sub>e = [])"
  by (cases p) (auto split: option.splits code\<^sub>b.splits)

lemma unflatten_stack_to_lookup [dest]: "(\<Delta>\<^sub>e, Lookup\<^sub>e x y # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b \<Longrightarrow> 
  orderly_code \<C>\<^sub>b 0 \<Longrightarrow> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow> \<exists>\<Delta>\<^sub>b p s\<^sub>b'. 
    s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> 
    ((lookup \<C>\<^sub>b p = Some (Lookup\<^sub>b x y) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
    (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some (Lookup\<^sub>b x y) \<and> 
      \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')) \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'"
proof (induction s\<^sub>b "length \<C>\<^sub>b" rule: orderly_stack.induct)
  case (3 \<Delta>\<^sub>b p s\<^sub>b')
  hence "Lookup\<^sub>e x y # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<and> orderly_code \<C>\<^sub>b 0 \<and> p < length \<C>\<^sub>b" by simp
  with 3 have "(lookup \<C>\<^sub>b p = Some (Lookup\<^sub>b x y) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
    (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some (Lookup\<^sub>b x y) \<and> 
      \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')" by blast
  with 3 show ?case by simp
qed simp_all

lemma unflatten_stack_to_pushcon [dest]: "(\<Delta>\<^sub>e, PushCon\<^sub>e n # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b \<Longrightarrow> 
  orderly_code \<C>\<^sub>b 0 \<Longrightarrow> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow> \<exists>\<Delta>\<^sub>b p s\<^sub>b'. 
    s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> 
    ((lookup \<C>\<^sub>b p = Some (PushCon\<^sub>b n) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
    (\<exists>p' m. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b m) \<and> lookup \<C>\<^sub>b p' = Some (PushCon\<^sub>b n) \<and> 
      \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')) \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'"
proof (induction s\<^sub>b "length \<C>\<^sub>b" rule: orderly_stack.induct)
  case (3 \<Delta>\<^sub>b p s\<^sub>b')
  hence "PushCon\<^sub>e n # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<and> orderly_code \<C>\<^sub>b 0 \<and> p < length \<C>\<^sub>b" by simp
  with 3 have "(lookup \<C>\<^sub>b p = Some (PushCon\<^sub>b n) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
    (\<exists>p' m. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b m) \<and> lookup \<C>\<^sub>b p' = Some (PushCon\<^sub>b n) \<and> 
      \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')" by blast
  with 3 show ?case by simp
qed simp_all

lemma unflatten_stack_to_pushlam [dest]: "(\<Delta>\<^sub>e, PushLam\<^sub>e \<C>\<^sub>e' n # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b \<Longrightarrow> 
  orderly_code \<C>\<^sub>b 0 \<Longrightarrow> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow> \<exists>\<Delta>\<^sub>b p s\<^sub>b' p'. 
  s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> \<C>\<^sub>e' = unflatten_code \<C>\<^sub>b p' \<and> 
    n = alloc_size \<C>\<^sub>b p' \<and> ((lookup \<C>\<^sub>b p = Some (PushLam\<^sub>b p') \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or> 
    (\<exists>p'' m. p = Suc p'' \<and> lookup \<C>\<^sub>b (Suc p'') = Some (Alloc\<^sub>b m) \<and> 
      lookup \<C>\<^sub>b p'' = Some (PushLam\<^sub>b p') \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p'')) \<and> 
  s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'"
proof (induction s\<^sub>b "length \<C>\<^sub>b" rule: orderly_stack.induct)
  case (3 \<Delta>\<^sub>b p s\<^sub>b')
  hence "PushLam\<^sub>e \<C>\<^sub>e' n # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<and> orderly_code \<C>\<^sub>b 0 \<and> p < length \<C>\<^sub>b" 
    by simp
  with 3 obtain p' where P: "\<C>\<^sub>e' = unflatten_code \<C>\<^sub>b p' \<and> n = alloc_size \<C>\<^sub>b p' \<and>
    ((lookup \<C>\<^sub>b p = Some (PushLam\<^sub>b p') \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or> 
    (\<exists>p'' m. p = Suc p'' \<and> lookup \<C>\<^sub>b (Suc p'') = Some (Alloc\<^sub>b m) \<and> 
      lookup \<C>\<^sub>b p'' = Some (PushLam\<^sub>b p') \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p''))" by blast
  from 3 have "\<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'" by simp
  with 3 P show ?case by blast
qed simp_all

lemma unflatten_stack_to_apply [dest]: "(\<Delta>\<^sub>e, Apply\<^sub>e # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b \<Longrightarrow> 
  orderly_code \<C>\<^sub>b 0 \<Longrightarrow> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow> \<exists>\<Delta>\<^sub>b p s\<^sub>b'. 
    s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> 
      ((lookup \<C>\<^sub>b p = Some Apply\<^sub>b \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
      (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some Apply\<^sub>b \<and> 
        \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')) \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'"
proof (induction s\<^sub>b "length \<C>\<^sub>b" rule: orderly_stack.induct)
  case (3 \<Delta>\<^sub>b p s\<^sub>b')
  hence "Apply\<^sub>e # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<and> orderly_code \<C>\<^sub>b 0 \<and> p < length \<C>\<^sub>b" by simp
  with 3 have "(lookup \<C>\<^sub>b p = Some Apply\<^sub>b \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
      (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some Apply\<^sub>b \<and> 
        \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')" by blast
  with 3 show ?case by simp
qed simp_all

lemma unflatten_stack_to_pushenv [dest]: "(\<Delta>\<^sub>e, PushEnv\<^sub>e n # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b \<Longrightarrow> 
  orderly_code \<C>\<^sub>b 0 \<Longrightarrow> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow>  \<exists>\<Delta>\<^sub>b p s\<^sub>b'. 
    s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> 
      ((lookup \<C>\<^sub>b p = Some (PushEnv\<^sub>b n) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
      (\<exists>p' m. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b m) \<and> lookup \<C>\<^sub>b p' = Some (PushEnv\<^sub>b n) \<and> 
        \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')) \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'"
proof (induction s\<^sub>b "length \<C>\<^sub>b" rule: orderly_stack.induct)
  case (3 \<Delta>\<^sub>b p s\<^sub>b')
  hence "PushEnv\<^sub>e n # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<and> orderly_code \<C>\<^sub>b 0 \<and> p < length \<C>\<^sub>b" by simp
  with 3 have "(lookup \<C>\<^sub>b p = Some (PushEnv\<^sub>b n) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
      (\<exists>p' m. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b m) \<and> lookup \<C>\<^sub>b p' = Some (PushEnv\<^sub>b n) \<and> 
        \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')" by blast
  with 3 show ?case by simp
qed simp_all

lemma unflatten_stack_to_return [dest]: "(\<Delta>\<^sub>e, Return\<^sub>e # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b \<Longrightarrow> 
  orderly_code \<C>\<^sub>b 0 \<Longrightarrow> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow> \<exists>\<Delta>\<^sub>b p s\<^sub>b'. 
    s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> 
      (lookup \<C>\<^sub>b p = Some Return\<^sub>b \<or> 
      (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some Return\<^sub>b)) \<and> 
        \<C>\<^sub>e = [] \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'"
proof (induction s\<^sub>b "length \<C>\<^sub>b" rule: orderly_stack.induct)
  case (3 \<Delta>\<^sub>b p s\<^sub>b')
  hence "Return\<^sub>e # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<and> orderly_code \<C>\<^sub>b 0 \<and> p < length \<C>\<^sub>b" by simp
  with 3 have "(lookup \<C>\<^sub>b p = Some Return\<^sub>b \<or> 
      (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some Return\<^sub>b)) \<and> 
        \<C>\<^sub>e = []" by blast
  with 3 show ?case by simp
qed simp_all

lemma unflatten_stack_to_jump [dest]: "(\<Delta>\<^sub>e, Jump\<^sub>e # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b \<Longrightarrow> 
  orderly_code \<C>\<^sub>b 0 \<Longrightarrow> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<Longrightarrow> block_structured\<^sub>b \<C>\<^sub>b \<Longrightarrow> \<exists>\<Delta>\<^sub>b p s\<^sub>b'. 
    s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> (lookup \<C>\<^sub>b p = Some Jump\<^sub>b \<or> 
      (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some Jump\<^sub>b)) \<and> 
        \<C>\<^sub>e = [] \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'"
proof (induction s\<^sub>b "length \<C>\<^sub>b" rule: orderly_stack.induct)
  case (3 \<Delta>\<^sub>b p s\<^sub>b')
  hence "Jump\<^sub>e # \<C>\<^sub>e = unflatten_code \<C>\<^sub>b (Suc p) \<and> orderly_code \<C>\<^sub>b 0 \<and> p < length \<C>\<^sub>b" by simp
  with 3 have "(lookup \<C>\<^sub>b p = Some Jump\<^sub>b \<or> 
      (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some Jump\<^sub>b)) \<and> 
        \<C>\<^sub>e = []" by blast
  with 3 show ?case by simp
qed simp_all

lemma unflatten_to_lam [dest]: "Lam\<^sub>e \<Delta>\<^sub>e \<C>\<^sub>e n = unflatten_closure \<C>\<^sub>b v\<^sub>b \<Longrightarrow> 
    \<exists>\<Delta>\<^sub>b p. v\<^sub>b = Lam\<^sub>b \<Delta>\<^sub>b p \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p \<and> 
      n = alloc_size \<C>\<^sub>b p"
  by (induction v\<^sub>b) simp_all

lemma unflatten_state [dest]: "S\<^sub>e \<V>\<^sub>e s\<^sub>e = unflatten_state \<C> \<Sigma>\<^sub>b \<Longrightarrow> \<exists>\<V>\<^sub>b s\<^sub>b. 
    \<Sigma>\<^sub>b = S\<^sub>b \<V>\<^sub>b s\<^sub>b \<and> \<V>\<^sub>e = unflatten_values \<C> \<V>\<^sub>b \<and> s\<^sub>e = unflatten_stack \<C> s\<^sub>b"
  by (induction \<Sigma>\<^sub>b) simp_all

theorem correct\<^sub>b [simp]: "unflatten_state \<C>\<^sub>b \<Sigma>\<^sub>b \<leadsto>\<^sub>e \<Sigma>\<^sub>e' \<Longrightarrow> orderly_state \<C>\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>b'. iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state \<C>\<^sub>b \<Sigma>\<^sub>b' = \<Sigma>\<^sub>e'"
proof (induction "unflatten_state \<C>\<^sub>b \<Sigma>\<^sub>b" \<Sigma>\<^sub>e' rule: eval\<^sub>e.induct)
  case (ev\<^sub>e_lookup \<Delta>\<^sub>e x vs y v \<V>\<^sub>e \<C>\<^sub>e s\<^sub>e)
  then obtain \<V>\<^sub>b s\<^sub>b where B: "\<Sigma>\<^sub>b = S\<^sub>b \<V>\<^sub>b s\<^sub>b \<and> \<V>\<^sub>e = unflatten_values \<C>\<^sub>b \<V>\<^sub>b \<and> 
    (\<Delta>\<^sub>e, Lookup\<^sub>e x y # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b" by fastforce
  with ev\<^sub>e_lookup have "orderly_code \<C>\<^sub>b 0 \<and> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<and> block_structured\<^sub>b \<C>\<^sub>b" 
    by simp
  with B obtain \<Delta>\<^sub>b p s\<^sub>b' where S: "s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> 
    \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> ((lookup \<C>\<^sub>b p = Some (Lookup\<^sub>b x y) \<and> 
    \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or> (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b p = Some (Alloc\<^sub>b n) \<and> 
    lookup \<C>\<^sub>b p' = Some (Lookup\<^sub>b x y) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')) \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'" 
      by (metis unflatten_stack_to_lookup)
  with ev\<^sub>e_lookup obtain vs' where VS: "lookup \<Delta>\<^sub>b x = Some vs' \<and> 
    map (unflatten_closure \<C>\<^sub>b) vs' = vs" by fastforce
  with ev\<^sub>e_lookup obtain v' where V: "lookup vs' y = Some v' \<and> unflatten_closure \<C>\<^sub>b v' = v" 
    by fastforce
  show ?case
  proof (cases "lookup \<C>\<^sub>b p = Some (Lookup\<^sub>b x y) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p")
    case True
    with S VS V have "\<C>\<^sub>b \<tturnstile> S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b') \<leadsto>\<^sub>b S\<^sub>b (v' # \<V>\<^sub>b) ((\<Delta>\<^sub>b, p) # s\<^sub>b')" by simp
    hence "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b')) (S\<^sub>b (v' # \<V>\<^sub>b) ((\<Delta>\<^sub>b, p) # s\<^sub>b'))" by simp
    with B S VS V True show ?thesis by fastforce
  next
    case False
    with S obtain p' n where P: "p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> 
      lookup \<C>\<^sub>b p' = Some (Lookup\<^sub>b x y) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p'" by blast
    with VS V have "\<C>\<^sub>b \<tturnstile> S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p') # s\<^sub>b') \<leadsto>\<^sub>b S\<^sub>b (v' # \<V>\<^sub>b) ((\<Delta>\<^sub>b, p') # s\<^sub>b')" by simp
    moreover from P have "\<C>\<^sub>b \<tturnstile> S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc (Suc p')) # s\<^sub>b') \<leadsto>\<^sub>b S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p') # s\<^sub>b')" 
      by simp
    ultimately have "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc (Suc p')) # s\<^sub>b')) 
      (S\<^sub>b (v' # \<V>\<^sub>b) ((\<Delta>\<^sub>b, p') # s\<^sub>b'))" by (metis iter_step iter_refl)
    with B S VS V False P show ?thesis by fastforce
  qed
next
  case (ev\<^sub>e_pushcon \<V>\<^sub>e \<Delta>\<^sub>e n \<C>\<^sub>e s\<^sub>e)
  then obtain \<V>\<^sub>b s\<^sub>b where B: "\<Sigma>\<^sub>b = S\<^sub>b \<V>\<^sub>b s\<^sub>b \<and> \<V>\<^sub>e = unflatten_values \<C>\<^sub>b \<V>\<^sub>b \<and> 
    (\<Delta>\<^sub>e, PushCon\<^sub>e n # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b" by fastforce
  with ev\<^sub>e_pushcon have "orderly_code \<C>\<^sub>b 0 \<and> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<and> block_structured\<^sub>b \<C>\<^sub>b" 
    by simp
  with B obtain \<Delta>\<^sub>b p s\<^sub>b' where S: "s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> 
    ((lookup \<C>\<^sub>b p = Some (PushCon\<^sub>b n) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
    (\<exists>p' m. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b m) \<and> lookup \<C>\<^sub>b p' = Some (PushCon\<^sub>b n) \<and> 
      \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')) \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'" by (metis unflatten_stack_to_pushcon)
  show ?case
  proof (cases "lookup \<C>\<^sub>b p = Some (PushCon\<^sub>b n) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p")
    case True
    with S have "\<C>\<^sub>b \<tturnstile> S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b') \<leadsto>\<^sub>b S\<^sub>b (Const\<^sub>b n # \<V>\<^sub>b) ((\<Delta>\<^sub>b, p) # s\<^sub>b')" by simp
    hence "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b')) (S\<^sub>b (Const\<^sub>b n # \<V>\<^sub>b) ((\<Delta>\<^sub>b, p) # s\<^sub>b'))" by simp
    with B S True show ?thesis by fastforce
  next
    case False
    with S obtain p' m where P: "p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b m) \<and> 
      lookup \<C>\<^sub>b p' = Some (PushCon\<^sub>b n) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p'" by blast
    with S have "\<C>\<^sub>b \<tturnstile> S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc (Suc p')) # s\<^sub>b') \<leadsto>\<^sub>b S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p') # s\<^sub>b')" by simp
    moreover from S P have "\<C>\<^sub>b \<tturnstile> S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p') # s\<^sub>b') \<leadsto>\<^sub>b S\<^sub>b (Const\<^sub>b n # \<V>\<^sub>b) ((\<Delta>\<^sub>b, p') # s\<^sub>b')" 
      by simp
    ultimately have "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc (Suc p')) # s\<^sub>b')) 
      (S\<^sub>b (Const\<^sub>b n # \<V>\<^sub>b) ((\<Delta>\<^sub>b, p') # s\<^sub>b'))" by (metis iter_step iter_refl)
    with B S False P show ?thesis by fastforce
  qed
next
  case (ev\<^sub>e_pushlam \<V>\<^sub>e \<Delta>\<^sub>e \<C>\<^sub>e' n \<C>\<^sub>e s\<^sub>e)
  then obtain \<V>\<^sub>b s\<^sub>b where B: "\<Sigma>\<^sub>b = S\<^sub>b \<V>\<^sub>b s\<^sub>b \<and> \<V>\<^sub>e = unflatten_values \<C>\<^sub>b \<V>\<^sub>b \<and> 
    (\<Delta>\<^sub>e, PushLam\<^sub>e \<C>\<^sub>e' n # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b" by fastforce
  with ev\<^sub>e_pushlam have "orderly_code \<C>\<^sub>b 0 \<and> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<and> block_structured\<^sub>b \<C>\<^sub>b" 
    by simp
  with B obtain \<Delta>\<^sub>b p s\<^sub>b' p' where S: "s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> 
    \<C>\<^sub>e' = unflatten_code \<C>\<^sub>b p' \<and> n = alloc_size \<C>\<^sub>b p' \<and> ((lookup \<C>\<^sub>b p = Some (PushLam\<^sub>b p') \<and> 
    \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or> (\<exists>p'' m. p = Suc p'' \<and> lookup \<C>\<^sub>b (Suc p'') = Some (Alloc\<^sub>b m) \<and> 
      lookup \<C>\<^sub>b p'' = Some (PushLam\<^sub>b p') \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p'')) \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'"
    using unflatten_stack_to_pushlam by metis
  show ?case
  proof (cases "lookup \<C>\<^sub>b p = Some (PushLam\<^sub>b p') \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p")
    case True
    with S have "\<C>\<^sub>b \<tturnstile> S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b') \<leadsto>\<^sub>b S\<^sub>b (Lam\<^sub>b \<Delta>\<^sub>b p' # \<V>\<^sub>b) ((\<Delta>\<^sub>b, p) # s\<^sub>b')" by simp
    hence "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b')) (S\<^sub>b (Lam\<^sub>b \<Delta>\<^sub>b p' # \<V>\<^sub>b) ((\<Delta>\<^sub>b, p) # s\<^sub>b'))" 
      by simp
    with B S True show ?thesis by fastforce
  next
    case False
    with S obtain p'' m where P: "p = Suc p'' \<and> lookup \<C>\<^sub>b (Suc p'') = Some (Alloc\<^sub>b m) \<and> 
      lookup \<C>\<^sub>b p'' = Some (PushLam\<^sub>b p') \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p''" by blast
    with S have "\<C>\<^sub>b \<tturnstile> S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc (Suc p'')) # s\<^sub>b') \<leadsto>\<^sub>b S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p'') # s\<^sub>b')" by simp
    moreover from S P have "\<C>\<^sub>b \<tturnstile> S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p'') # s\<^sub>b') \<leadsto>\<^sub>b 
      S\<^sub>b (Lam\<^sub>b \<Delta>\<^sub>b p' # \<V>\<^sub>b) ((\<Delta>\<^sub>b, p'') # s\<^sub>b')" by simp
    ultimately have "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc (Suc p'')) # s\<^sub>b')) 
      (S\<^sub>b (Lam\<^sub>b \<Delta>\<^sub>b p' # \<V>\<^sub>b) ((\<Delta>\<^sub>b, p'') # s\<^sub>b'))" by (metis iter_step iter_refl)
    with B S False P show ?thesis by auto
  qed
next
  case (ev\<^sub>e_apply v\<^sub>e \<Delta>\<^sub>e' \<C>\<^sub>e' n \<V>\<^sub>e \<Delta>\<^sub>e \<C>\<^sub>e s\<^sub>e)
  then obtain \<V>\<^sub>b s\<^sub>b where B: "\<Sigma>\<^sub>b = S\<^sub>b \<V>\<^sub>b s\<^sub>b \<and> v\<^sub>e # Lam\<^sub>e \<Delta>\<^sub>e' \<C>\<^sub>e' n # \<V>\<^sub>e = unflatten_values \<C>\<^sub>b \<V>\<^sub>b \<and> 
    (\<Delta>\<^sub>e, Apply\<^sub>e # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b" by force
  with ev\<^sub>e_apply have "orderly_code \<C>\<^sub>b 0 \<and> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<and> block_structured\<^sub>b \<C>\<^sub>b" 
    by simp
  with B obtain \<Delta>\<^sub>b p s\<^sub>b' where S: "s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> 
      ((lookup \<C>\<^sub>b p = Some Apply\<^sub>b \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
      (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some Apply\<^sub>b \<and> 
        \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')) \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'" 
    by (metis unflatten_stack_to_apply)
  from B obtain v\<^sub>b \<Delta>\<^sub>b' p' \<V>\<^sub>b' where V: "\<V>\<^sub>b = v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b' \<and> 
    v\<^sub>e = unflatten_closure \<C>\<^sub>b v\<^sub>b \<and> \<Delta>\<^sub>e' = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b' \<and> 
      \<C>\<^sub>e' = unflatten_code \<C>\<^sub>b p' \<and> n = alloc_size \<C>\<^sub>b p' \<and> \<V>\<^sub>e = unflatten_values \<C>\<^sub>b \<V>\<^sub>b'" by fastforce
  show ?case
  proof (cases "lookup \<C>\<^sub>b p = Some Apply\<^sub>b \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p")
    case True
    with S have "\<C>\<^sub>b \<tturnstile> S\<^sub>b (v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b') \<leadsto>\<^sub>b
      S\<^sub>b \<V>\<^sub>b' (([v\<^sub>b] # \<Delta>\<^sub>b', p') # (\<Delta>\<^sub>b, p) # s\<^sub>b')" by simp
    hence "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b (v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b')) 
      (S\<^sub>b \<V>\<^sub>b' (([v\<^sub>b] # \<Delta>\<^sub>b', p') # (\<Delta>\<^sub>b, p) # s\<^sub>b'))" by simp
    with B S V True show ?thesis by fastforce
  next
    case False
    with S obtain p'' m where P: "p = Suc p'' \<and> lookup \<C>\<^sub>b (Suc p'') = Some (Alloc\<^sub>b m) \<and> 
      lookup \<C>\<^sub>b p'' = Some Apply\<^sub>b \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p''" by blast
    with S have "\<C>\<^sub>b \<tturnstile> S\<^sub>b (v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc (Suc p'')) # s\<^sub>b') \<leadsto>\<^sub>b 
      S\<^sub>b (v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc p'') # s\<^sub>b')" by simp
    moreover from S P have "\<C>\<^sub>b \<tturnstile> S\<^sub>b (v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc p'') # s\<^sub>b') \<leadsto>\<^sub>b 
      S\<^sub>b \<V>\<^sub>b' (([v\<^sub>b] # \<Delta>\<^sub>b', p') # (\<Delta>\<^sub>b, p'') # s\<^sub>b')" by simp
    ultimately have "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b (v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc (Suc p'')) # s\<^sub>b')) 
      (S\<^sub>b \<V>\<^sub>b' (([v\<^sub>b] # \<Delta>\<^sub>b', p') # (\<Delta>\<^sub>b, p'') # s\<^sub>b'))" by (metis iter_step iter_refl)
    with B S V False P show ?thesis by fastforce
  qed
next
  case (ev\<^sub>e_pushenv v\<^sub>e \<V>\<^sub>e \<Delta>\<^sub>e n \<C>\<^sub>e s\<^sub>e)
  then obtain \<V>\<^sub>b s\<^sub>b where B: "\<Sigma>\<^sub>b = S\<^sub>b \<V>\<^sub>b s\<^sub>b \<and> v\<^sub>e # \<V>\<^sub>e = unflatten_values \<C>\<^sub>b \<V>\<^sub>b \<and> 
    ((\<Delta>\<^sub>e, PushEnv\<^sub>e n # \<C>\<^sub>e) # s\<^sub>e) = unflatten_stack \<C>\<^sub>b s\<^sub>b" by fastforce
  with ev\<^sub>e_pushenv have "orderly_code \<C>\<^sub>b 0 \<and> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<and> block_structured\<^sub>b \<C>\<^sub>b" 
    by simp
  with B obtain \<Delta>\<^sub>b p s\<^sub>b' where S: "s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> 
      ((lookup \<C>\<^sub>b p = Some (PushEnv\<^sub>b n) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p) \<or>
      (\<exists>p' m. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b m) \<and> lookup \<C>\<^sub>b p' = Some (PushEnv\<^sub>b n) \<and> 
        \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p')) \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'" 
    by (metis unflatten_stack_to_pushenv)
  from B obtain v\<^sub>b \<V>\<^sub>b' where V: "\<V>\<^sub>b = v\<^sub>b # \<V>\<^sub>b' \<and> v\<^sub>e = unflatten_closure \<C>\<^sub>b v\<^sub>b \<and> 
    \<V>\<^sub>e = unflatten_values \<C>\<^sub>b \<V>\<^sub>b'" by fastforce
  show ?case
  proof (cases "lookup \<C>\<^sub>b p = Some (PushEnv\<^sub>b n) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p")
    case True
    with S have "\<C>\<^sub>b \<tturnstile> S\<^sub>b (v\<^sub>b # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b') \<leadsto>\<^sub>b S\<^sub>b \<V>\<^sub>b' ((snoc_fst v\<^sub>b \<Delta>\<^sub>b, p) # s\<^sub>b')" 
      by simp
    hence "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b (v\<^sub>b # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b')) (S\<^sub>b \<V>\<^sub>b' ((snoc_fst v\<^sub>b \<Delta>\<^sub>b, p) # s\<^sub>b'))" 
      by simp
    with B S V True show ?thesis by fastforce
  next
    case False
    with S obtain p'' m where P: "p = Suc p'' \<and> lookup \<C>\<^sub>b (Suc p'') = Some (Alloc\<^sub>b m) \<and> 
      lookup \<C>\<^sub>b p'' = Some (PushEnv\<^sub>b n) \<and> \<C>\<^sub>e = unflatten_code \<C>\<^sub>b p''" by blast
    with S have "\<C>\<^sub>b \<tturnstile> S\<^sub>b (v\<^sub>b # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc (Suc p'')) # s\<^sub>b') \<leadsto>\<^sub>b 
      S\<^sub>b (v\<^sub>b # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc p'') # s\<^sub>b')" by simp
    moreover from S P have "\<C>\<^sub>b \<tturnstile> S\<^sub>b (v\<^sub>b # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc p'') # s\<^sub>b') \<leadsto>\<^sub>b 
      S\<^sub>b \<V>\<^sub>b' ((snoc_fst v\<^sub>b \<Delta>\<^sub>b, p'') # s\<^sub>b')" by simp
    ultimately have "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b (v\<^sub>b # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc (Suc p'')) # s\<^sub>b')) 
      (S\<^sub>b \<V>\<^sub>b' ((snoc_fst v\<^sub>b \<Delta>\<^sub>b, p'') # s\<^sub>b'))" by (metis iter_step iter_refl)
    with B S V False P show ?thesis by fastforce
  qed
next
  case (ev\<^sub>e_return \<V>\<^sub>e \<Delta>\<^sub>e \<C>\<^sub>e s\<^sub>e)
  then obtain \<V>\<^sub>b s\<^sub>b where B: "\<Sigma>\<^sub>b = S\<^sub>b \<V>\<^sub>b s\<^sub>b \<and> \<V>\<^sub>e = unflatten_values \<C>\<^sub>b \<V>\<^sub>b \<and> 
    (\<Delta>\<^sub>e, Return\<^sub>e # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b" by fastforce
  with ev\<^sub>e_return have "orderly_code \<C>\<^sub>b 0 \<and> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<and> block_structured\<^sub>b \<C>\<^sub>b" 
    by simp
  with B obtain \<Delta>\<^sub>b p s\<^sub>b' where S: "s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> 
      (lookup \<C>\<^sub>b p = Some Return\<^sub>b \<or> 
      (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> lookup \<C>\<^sub>b p' = Some Return\<^sub>b)) \<and> 
        \<C>\<^sub>e = [] \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'" 
    by (metis unflatten_stack_to_return)
  show ?case
  proof (cases "lookup \<C>\<^sub>b p = Some Return\<^sub>b")
    case True
    with S have "\<C>\<^sub>b \<tturnstile> S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b') \<leadsto>\<^sub>b S\<^sub>b \<V>\<^sub>b s\<^sub>b'" by simp
    hence "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b')) (S\<^sub>b \<V>\<^sub>b s\<^sub>b')" by simp
    with B S True show ?thesis by fastforce
  next
    case False
    with S obtain p' n where P: "p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> 
      lookup \<C>\<^sub>b p' = Some Return\<^sub>b" by blast
    with S have "\<C>\<^sub>b \<tturnstile> S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc (Suc p')) # s\<^sub>b') \<leadsto>\<^sub>b S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p') # s\<^sub>b')" by simp
    moreover from S P have "\<C>\<^sub>b \<tturnstile> S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc p') # s\<^sub>b') \<leadsto>\<^sub>b S\<^sub>b \<V>\<^sub>b s\<^sub>b'" by simp
    ultimately have "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b \<V>\<^sub>b ((\<Delta>\<^sub>b, Suc (Suc p')) # s\<^sub>b')) (S\<^sub>b \<V>\<^sub>b s\<^sub>b')" 
      by (metis iter_step iter_refl)
    with B S False P show ?thesis by fastforce
  qed
next
  case (ev\<^sub>e_jump v \<Delta>\<^sub>e' \<C>\<^sub>e' n \<V>\<^sub>e \<Delta>\<^sub>e \<C>\<^sub>e s\<^sub>e)
  then obtain \<V>\<^sub>b s\<^sub>b where B: "\<Sigma>\<^sub>b = S\<^sub>b \<V>\<^sub>b s\<^sub>b \<and> 
    v # Lam\<^sub>e \<Delta>\<^sub>e' \<C>\<^sub>e' n # \<V>\<^sub>e = unflatten_values \<C>\<^sub>b \<V>\<^sub>b \<and> 
      (\<Delta>\<^sub>e, Jump\<^sub>e # \<C>\<^sub>e) # s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b" by force
  with ev\<^sub>e_jump have "orderly_code \<C>\<^sub>b 0 \<and> orderly_stack s\<^sub>b (length \<C>\<^sub>b) \<and> block_structured\<^sub>b \<C>\<^sub>b" 
    by simp
  with B obtain \<Delta>\<^sub>b p s\<^sub>b' where S: "s\<^sub>b = (\<Delta>\<^sub>b, Suc p) # s\<^sub>b' \<and> \<Delta>\<^sub>e = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b \<and> 
    (lookup \<C>\<^sub>b p = Some Jump\<^sub>b \<or> (\<exists>p' n. p = Suc p' \<and> lookup \<C>\<^sub>b (Suc p') = Some (Alloc\<^sub>b n) \<and> 
      lookup \<C>\<^sub>b p' = Some Jump\<^sub>b)) \<and> \<C>\<^sub>e = [] \<and> s\<^sub>e = unflatten_stack \<C>\<^sub>b s\<^sub>b'" 
    by (metis unflatten_stack_to_jump)
  from B obtain v\<^sub>b \<Delta>\<^sub>b' p' \<V>\<^sub>b' where V: "\<V>\<^sub>b = v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b' \<and> 
    v = unflatten_closure \<C>\<^sub>b v\<^sub>b \<and> \<Delta>\<^sub>e' = map (unflatten_values \<C>\<^sub>b) \<Delta>\<^sub>b' \<and> \<C>\<^sub>e' = unflatten_code \<C>\<^sub>b p' \<and>
      n = alloc_size \<C>\<^sub>b p' \<and> \<V>\<^sub>e = unflatten_values \<C>\<^sub>b \<V>\<^sub>b'" by fastforce
  show ?case
  proof (cases "lookup \<C>\<^sub>b p = Some Jump\<^sub>b")
    case True
    with S have "\<C>\<^sub>b \<tturnstile> S\<^sub>b (v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b') \<leadsto>\<^sub>b
      S\<^sub>b \<V>\<^sub>b' (([v\<^sub>b] # \<Delta>\<^sub>b', p') # s\<^sub>b')" by simp
    hence "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b (v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc p) # s\<^sub>b')) 
      (S\<^sub>b \<V>\<^sub>b' (([v\<^sub>b] # \<Delta>\<^sub>b', p') # s\<^sub>b'))" by simp
    with B S V True show ?thesis by fastforce
  next
    case False
    with S obtain p'' m where P: "p = Suc p'' \<and> lookup \<C>\<^sub>b (Suc p'') = Some (Alloc\<^sub>b m) \<and> 
      lookup \<C>\<^sub>b p'' = Some Jump\<^sub>b" by blast
    with S have "\<C>\<^sub>b \<tturnstile> S\<^sub>b (v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc (Suc p'')) # s\<^sub>b') \<leadsto>\<^sub>b 
      S\<^sub>b (v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc p'') # s\<^sub>b')" by simp
    moreover from S P have "\<C>\<^sub>b \<tturnstile> S\<^sub>b (v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc p'') # s\<^sub>b') \<leadsto>\<^sub>b 
      S\<^sub>b \<V>\<^sub>b' (([v\<^sub>b] # \<Delta>\<^sub>b', p') # s\<^sub>b')" by simp
    ultimately have "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b (v\<^sub>b # Lam\<^sub>b \<Delta>\<^sub>b' p' # \<V>\<^sub>b') ((\<Delta>\<^sub>b, Suc (Suc p'')) # s\<^sub>b')) 
      (S\<^sub>b \<V>\<^sub>b' (([v\<^sub>b] # \<Delta>\<^sub>b', p') # s\<^sub>b'))" by (metis iter_step iter_refl)
    with B S V False P show ?thesis by fastforce
  qed
qed

lemma iter_correct\<^sub>b [simp]: "iter (\<leadsto>\<^sub>e) (unflatten_state \<C>\<^sub>b \<Sigma>\<^sub>b) \<Sigma>\<^sub>e' \<Longrightarrow> orderly_state \<C>\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>b'. iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state \<C>\<^sub>b \<Sigma>\<^sub>b' = \<Sigma>\<^sub>e'"
proof (induction "unflatten_state \<C>\<^sub>b \<Sigma>\<^sub>b" \<Sigma>\<^sub>e' arbitrary: \<Sigma>\<^sub>b rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>e' \<Sigma>\<^sub>e'')
  moreover then obtain \<Sigma>\<^sub>b' where S: "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state \<C>\<^sub>b \<Sigma>\<^sub>b' = \<Sigma>\<^sub>e'" 
    by fastforce
  moreover with iter_step have "orderly_state \<C>\<^sub>b \<Sigma>\<^sub>b'" by fastforce
  ultimately obtain \<Sigma>\<^sub>b'' where "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b' \<Sigma>\<^sub>b'' \<and> unflatten_state \<C>\<^sub>b \<Sigma>\<^sub>b'' = \<Sigma>\<^sub>e''" 
    by fastforce
  with S show ?case by (metis iter_append)
qed force+

lemma unfl_terminal [simp]: "unflatten_state \<C>\<^sub>b \<Sigma> = S\<^sub>e [c] [] \<Longrightarrow>
  \<exists>v. \<Sigma> = S\<^sub>b [v] [] \<and> c = unflatten_closure \<C>\<^sub>b v"
proof -
  assume "unflatten_state \<C>\<^sub>b \<Sigma> = S\<^sub>e [c] []"
  then obtain \<V>\<^sub>b s where S: "\<Sigma> = S\<^sub>b \<V>\<^sub>b s \<and> [c] = unflatten_values \<C>\<^sub>b \<V>\<^sub>b \<and> [] = unflatten_stack \<C>\<^sub>b s" 
    by (metis unflatten_state)
  moreover then obtain v where "\<V>\<^sub>b = [v] \<and> c = unflatten_closure \<C>\<^sub>b v" by blast
  ultimately show ?thesis by simp
qed

lemma eval\<^sub>b_end [simp]: "iter (\<leadsto>\<^sub>e) (unflatten_state \<C>\<^sub>b \<Sigma>\<^sub>b) (S\<^sub>e [c] []) \<Longrightarrow> 
  orderly_state \<C>\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow> 
    \<exists>v. iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b (S\<^sub>b [v] []) \<and> c = unflatten_closure \<C>\<^sub>b v"
proof -
  assume "iter (\<leadsto>\<^sub>e) (unflatten_state \<C>\<^sub>b \<Sigma>\<^sub>b) (S\<^sub>e [c] [])"
  moreover assume O: "orderly_state \<C>\<^sub>b \<Sigma>\<^sub>b"
  ultimately obtain \<Sigma>\<^sub>b' where E: "iter (\<tturnstile> \<C>\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state \<C>\<^sub>b \<Sigma>\<^sub>b' = S\<^sub>e [c] []" 
    by fastforce
  moreover with O have "orderly_state \<C>\<^sub>b \<Sigma>\<^sub>b'" by fastforce
  moreover with E obtain v where "\<Sigma>\<^sub>b' = S\<^sub>b [v] [] \<and> c = unflatten_closure \<C>\<^sub>b v" 
    by (metis unfl_terminal)
  ultimately show ?thesis by blast
qed

end