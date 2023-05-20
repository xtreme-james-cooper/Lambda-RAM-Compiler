theory CodeFlattening
  imports ByteCode "../06TreeCode/TreeCode"
begin

subsection \<open>Code Flattening\<close>

text \<open>Flattening code is mostly just a map from tree-code operations to bytecode ones; but whenever 
we reach a nested codeblock, we pull it out and convert it first. As a result, all code-pointers in
the flattened codeblock point towards lower addresses. The first argument is the first free address;
each nested codeblock is put there and then the argument is updated to its new, further-along 
position.\<close>

fun flatten_code' :: "nat \<Rightarrow> code\<^sub>e list \<Rightarrow> code\<^sub>b list" where
  "flatten_code' p [] = []"
| "flatten_code' p (Lookup\<^sub>e x # \<C>) = flatten_code' p \<C> @ [Lookup\<^sub>b x]"
| "flatten_code' p (PushCon\<^sub>e n # \<C>) = flatten_code' p \<C> @ [PushCon\<^sub>b n]"
| "flatten_code' p (PushLam\<^sub>e \<C>' # \<C>) = (
    let \<C>\<^sub>b' = flatten_code' p \<C>'
    in \<C>\<^sub>b' @ flatten_code' (p + length \<C>\<^sub>b') \<C> @ [PushLam\<^sub>b (p + length \<C>\<^sub>b')])"
| "flatten_code' p (Apply\<^sub>e # \<C>) = flatten_code' p \<C> @ [Apply\<^sub>b]"
| "flatten_code' p (Return\<^sub>e # \<C>) = flatten_code' p \<C> @ [Return\<^sub>b]"
| "flatten_code' p (Jump\<^sub>e # \<C>) = flatten_code' p \<C> @ [Jump\<^sub>b]"

definition flatten_code :: "code\<^sub>e list \<Rightarrow> code\<^sub>b list" where
  "flatten_code \<C> \<equiv> flatten_code' 0 \<C>"

text \<open>One might think that, like previous compilation passes, we could simply map \<open>flatten_code\<close> up
the levels of the state and produce a compiled state. Unfortunately, we cannot. Once evaluation 
begins, the code stored in the tree-code stack could come from all over the codebase, and there is 
no guarantee that \<open>flatten_code\<close> would assign the right internal addresses. The structure of the 
code would be the same, of course, but rather than get bogged down in trying to define an 
"alpha-equivalence for code pointers" we cut to the chase and define a code-unflattening function.\<close>

fun unflatten_code :: "code\<^sub>b list \<Rightarrow> nat \<Rightarrow> code\<^sub>e list" where
  "unflatten_code \<C> 0 = []"
| "unflatten_code \<C> (Suc p) = (case lookup \<C> p of
      Some (Lookup\<^sub>b x) \<Rightarrow> Lookup\<^sub>e x # unflatten_code \<C> p
    | Some (PushCon\<^sub>b n) \<Rightarrow>  PushCon\<^sub>e n # unflatten_code \<C> p
    | Some (PushLam\<^sub>b p') \<Rightarrow> (
        if p' \<le> p then PushLam\<^sub>e (unflatten_code \<C> p') # unflatten_code \<C> p else undefined) 
    | Some Apply\<^sub>b \<Rightarrow> Apply\<^sub>e # unflatten_code \<C> p
    | Some Return\<^sub>b \<Rightarrow> [Return\<^sub>e]
    | Some Jump\<^sub>b \<Rightarrow> [Jump\<^sub>e]
    | None \<Rightarrow> undefined)"

primrec unflatten_closure :: "code\<^sub>b list \<Rightarrow> closure\<^sub>b \<Rightarrow> closure\<^sub>e" where
  "unflatten_closure \<C> (Const\<^sub>b n) = Const\<^sub>e n"
| "unflatten_closure \<C> (Lam\<^sub>b \<Delta> p) = Lam\<^sub>e (map (unflatten_closure \<C>) \<Delta>) (unflatten_code \<C> p)"

abbreviation unflatten_values :: "code\<^sub>b list \<Rightarrow> closure\<^sub>b list \<Rightarrow> closure\<^sub>e list" where
  "unflatten_values \<C> \<V> \<equiv> map (unflatten_closure \<C>) \<V>"

primrec unflatten_frame :: "code\<^sub>b list \<Rightarrow> (closure\<^sub>b list \<times> nat) \<Rightarrow> frame\<^sub>e" where
  "unflatten_frame \<C> (\<Delta>, p) = (unflatten_values \<C> \<Delta>, unflatten_code \<C> p)"

abbreviation unflatten_stack :: "code\<^sub>b list \<Rightarrow> (closure\<^sub>b list \<times> nat) list \<Rightarrow> frame\<^sub>e list" where
  "unflatten_stack \<C> s \<equiv> map (unflatten_frame \<C>) s"

primrec unflatten_state :: "code\<^sub>b list \<Rightarrow> state\<^sub>b \<Rightarrow> state\<^sub>e" where
  "unflatten_state \<C> (S\<^sub>b \<V> s) = S\<^sub>e (unflatten_values \<C> \<V>) (unflatten_stack \<C> s)"

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
| "orderly_closure n (Lam\<^sub>b \<Delta> p) = (0 < p \<and> p \<le> n \<and> list_all (orderly_closure n) \<Delta>)"

fun orderly_stack :: "(closure\<^sub>b list \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "orderly_stack [] n = True"
| "orderly_stack ((\<Delta>, 0) # s) n = False"
| "orderly_stack ((\<Delta>, Suc p) # s) n = 
    (p < n \<and> list_all (orderly_closure n) \<Delta> \<and> orderly_stack s n)"

primrec orderly_state :: "code\<^sub>b list \<Rightarrow> state\<^sub>b \<Rightarrow> bool" where
  "orderly_state cd (S\<^sub>b vs sfs) = (orderly_code cd 0 \<and> properly_terminated\<^sub>b cd \<and> 
    orderly_stack sfs (length cd) \<and> list_all (orderly_closure (length cd)) vs)"

primrec code_size :: "code\<^sub>e \<Rightarrow> nat"
    and code_list_size :: "code\<^sub>e list \<Rightarrow> nat" where
  "code_size (Lookup\<^sub>e x) = 1"
| "code_size (PushCon\<^sub>e n) = 1"
| "code_size (PushLam\<^sub>e \<C>) = Suc (code_list_size \<C>)"
| "code_size Apply\<^sub>e = 1"
| "code_size Return\<^sub>e = 1"
| "code_size Jump\<^sub>e = 1"
| "code_list_size [] = 0"
| "code_list_size (op # \<C>) = code_size op + code_list_size \<C>"

lemma flatten_length [simp]: "length (flatten_code' lib cd) = code_list_size cd"
  by (induction lib cd rule: flatten_code'.induct) simp_all

lemma [simp]: "length (flatten_code cd) = code_list_size cd"
  by (simp add: flatten_code_def)

lemma [simp]: "0 < code_size cd"
  by (induction cd) simp_all

lemma [simp]: "(code_list_size cd = 0) = (cd = [])"
  by (induction cd) simp_all

lemma [simp]: "(flatten_code' lib cd = []) = (cd = [])"
  by (induction lib cd rule: flatten_code'.induct) simp_all

lemma [simp]: "(flatten_code cd = []) = (cd = [])"
  by (simp add: flatten_code_def)

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> properly_terminated\<^sub>b (cd @ cd') = properly_terminated\<^sub>b cd"
  by (induction cd) simp_all

lemma return_terminated_flatten' [simp]: "properly_terminated\<^sub>e cd \<Longrightarrow> 
    properly_terminated\<^sub>b (flatten_code' lib cd @ cd')"
  by (induction lib cd arbitrary: cd' rule: flatten_code'.induct) (auto split: if_splits)

lemma [simp]: "properly_terminated\<^sub>e cd \<Longrightarrow> properly_terminated\<^sub>b (flatten_code cd)"
proof (unfold flatten_code_def)
  assume "properly_terminated\<^sub>e cd"
  hence "properly_terminated\<^sub>b (flatten_code' 0 cd @ [])" by (metis return_terminated_flatten')
  thus "properly_terminated\<^sub>b (flatten_code' 0 cd)" by simp
qed

lemma [simp]: "orderly_op x op \<Longrightarrow> orderly_op (Suc x) op"
  by (induction op) simp_all

lemma [simp]: "orderly_op (x + n) op \<Longrightarrow> orderly_op (x + (m + n)) op"
  by (induction op) simp_all

lemma [simp]: "orderly_code (cd @ cd') n = (orderly_code cd n \<and> orderly_code cd' (length cd + n))"
  by (induction cd arbitrary: n) simp_all

lemma [simp]: "lib \<le> n \<Longrightarrow> properly_terminated\<^sub>e cd \<Longrightarrow> orderly_code (flatten_code' lib cd) n"
  by (induction lib cd arbitrary: n rule: flatten_code'.induct) auto

lemma [simp]: "properly_terminated\<^sub>e cdr \<Longrightarrow> orderly_code (flatten_code cdr) 0"
  by (simp add: flatten_code_def)

lemma [simp]: "x > 0 \<Longrightarrow> orderly_stack [([], x)] x"
  by (cases x) simp_all

lemma orderly_length_flatten [simp]: "cdr \<noteq> [] \<Longrightarrow> 
    orderly_stack [([], length (flatten_code cdr))] (length (flatten_code cdr))"
  by (cases cdr) simp_all

lemma [simp]: "cdr \<noteq> [] \<Longrightarrow> orderly_stack [([], code_list_size cdr)] (code_list_size cdr)"
proof -
  assume "cdr \<noteq> []" 
  hence "orderly_stack [([], length (flatten_code cdr))] (length (flatten_code cdr))" 
    by (metis orderly_length_flatten)
  thus ?thesis by simp
qed
 
lemma [simp]: "lookup vs x = Some v \<Longrightarrow> list_all (orderly_closure n) vs \<Longrightarrow> orderly_closure n v"
  by auto

lemma pushlam_ordered [simp]: "lookup cd x = Some (PushLam\<^sub>b pc) \<Longrightarrow> orderly_code cd n \<Longrightarrow> 
    x < length cd \<Longrightarrow> 0 < pc \<and> pc \<le> length cd + n"
  by (induction cd x arbitrary: n rule: lookup.induct) fastforce+

lemma [simp]: "lookup cd x = Some (PushLam\<^sub>b pc) \<Longrightarrow> orderly_code cd 0 \<Longrightarrow> x < length cd \<Longrightarrow> 
    0 < pc \<and> pc \<le> length cd"
  using pushlam_ordered by fastforce

lemma index_into_append [simp]: "lookup (flatten_code' lib cd @ cd') (code_list_size cd + n) = 
    lookup cd' n"
  by (metis flatten_length lookup_append_snd)

lemma [simp]: "lookup (flatten_code' lib cd @ op # acc) (code_list_size cd) = Some op"
proof -
  have "lookup (flatten_code' lib cd @ op # acc) (code_list_size cd + 0) = lookup (op # acc) 0" 
    by (metis index_into_append)
  thus ?thesis by simp
qed

lemma unflatten_front [simp]: "pc \<le> length cd \<Longrightarrow> 
    unflatten_code (cd @ cd') pc = unflatten_code cd pc"
  by (induction cd pc rule: unflatten_code.induct) (simp_all split: option.splits code\<^sub>b.splits) 

lemma unflatten_flatten [simp]: "properly_terminated\<^sub>e cd \<Longrightarrow> 
  unflatten_code (lib @ flatten_code' (length lib) cd @ acc) (length lib + code_list_size cd) = cd"
proof (induction "length lib" cd arbitrary: lib acc rule: flatten_code'.induct)
  case (4 cd' cd)
  let ?pc = "length lib + code_list_size cd'"
  let ?code' = "lib @ flatten_code' (length lib) cd' @ []"
  let ?code = "?code' @ flatten_code' ?pc cd @ PushLam\<^sub>b ?pc # acc"
  have X: "length lib + length (flatten_code' (length lib) cd') = length ?code'" by simp
  from 4 have "properly_terminated\<^sub>e cd" by simp
  with 4 X have "unflatten_code (?code' @ flatten_code' (length ?code') cd @
    PushLam\<^sub>b (length lib + length (flatten_code' (length lib) cd')) # acc)
      (length ?code' + code_list_size cd) = cd" by blast
  hence "unflatten_code ?code (length lib + code_list_size cd' + code_list_size cd) = cd" by simp
  hence X: "unflatten_code ?code (length lib + (code_list_size cd' + code_list_size cd)) = cd" 
    by (metis add.assoc)
  from 4 have "properly_terminated\<^sub>e cd'" by simp
  with 4 have "unflatten_code ?code' (length lib + code_list_size cd') = cd'" by blast
  moreover have "?pc \<le> length ?code'" by simp
  ultimately have Z: "unflatten_code ?code ?pc =  cd'" by (metis unflatten_front)
  with X Z show ?case by simp
qed simp_all

lemma [simp]: "properly_terminated\<^sub>e cd \<Longrightarrow> unflatten_code (flatten_code cd) (code_list_size cd) = cd"
proof -
  assume "properly_terminated\<^sub>e cd"
  hence "unflatten_code ([] @ flatten_code' (length []) cd @ []) 
    (length [] + code_list_size cd) = cd" by (metis unflatten_flatten list.size(3))
  thus ?thesis by (simp add: flatten_code_def)
qed

lemma orderly_lam [simp]: "lookup cd pc = Some (PushLam\<^sub>b pc') \<Longrightarrow> orderly_code cd n \<Longrightarrow> pc' \<le> pc + n"
  by (induction cd pc arbitrary: n rule: lookup.induct) fastforce+

lemma [simp]: "lookup cd pc = Some (PushLam\<^sub>b pc') \<Longrightarrow> orderly_code cd 0 \<Longrightarrow> pc' \<le> pc"
  using orderly_lam by fastforce

theorem completeb [simp]: "cd \<tturnstile> \<Sigma>\<^sub>b \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state cd \<Sigma>\<^sub>b \<Longrightarrow> 
  iter (\<leadsto>\<^sub>e) (unflatten_state cd \<Sigma>\<^sub>b) (unflatten_state cd \<Sigma>\<^sub>b')"
proof (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: eval\<^sub>b.induct)
  case (ev\<^sub>b_lookup cd pc x env v vs sfs)
  hence "S\<^sub>e (unflatten_values cd vs) 
    ((unflatten_values cd env, unflatten_code cd (Suc pc)) # unflatten_stack cd sfs) \<leadsto>\<^sub>e
      S\<^sub>e (unflatten_closure cd v # unflatten_values cd vs)
        ((unflatten_values cd env, unflatten_code cd pc) # unflatten_stack cd sfs)" by simp
  thus ?case by simp
next
  case (ev\<^sub>b_pushcon cd pc k vs env sfs)
  hence "S\<^sub>e (unflatten_values cd vs) 
    ((unflatten_values cd env, unflatten_code cd (Suc pc)) # unflatten_stack cd sfs) \<leadsto>\<^sub>e
      S\<^sub>e (Const\<^sub>e k # unflatten_values cd vs) 
        ((unflatten_values cd env, unflatten_code cd pc) # unflatten_stack cd sfs)" by simp
  thus ?case by simp
next
  case (ev\<^sub>b_pushlam cd pc pc' vs env sfs)
  moreover hence X: "pc' \<le> pc" by auto
  moreover have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (unflatten_values cd vs) ((unflatten_values cd env, 
    PushLam\<^sub>e (unflatten_code cd pc') # 
      unflatten_code cd pc) # unflatten_stack cd sfs))
        (S\<^sub>e (Lam\<^sub>e (unflatten_values cd env) (unflatten_code cd pc') # unflatten_values cd vs) 
          ((unflatten_values cd env, unflatten_code cd pc) # unflatten_stack cd sfs))" 
    by (metis ev\<^sub>e_pushlam iter_one)
  ultimately show ?case by simp
next
  case (ev\<^sub>b_apply cd pc v env' pc' vs env sfs)
  hence "S\<^sub>e (unflatten_closure cd v # Lam\<^sub>e (unflatten_values cd env') (unflatten_code cd pc') # unflatten_values cd vs) 
      ((unflatten_values cd env, unflatten_code cd (Suc pc)) # unflatten_stack cd sfs) \<leadsto>\<^sub>e
        S\<^sub>e (unflatten_values cd vs) ((unflatten_closure cd v # unflatten_values cd env', unflatten_code cd pc') # 
          (unflatten_values cd env, unflatten_code cd pc) # 
            unflatten_stack cd sfs)" by simp
  thus ?case by simp
next
  case (ev\<^sub>b_return cd pc vs env sfs)
  moreover have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (unflatten_values cd vs) ((unflatten_values cd env, [Return\<^sub>e]) # unflatten_stack cd sfs))
    (S\<^sub>e (unflatten_values cd vs) (unflatten_stack cd sfs))" by (metis ev\<^sub>e_return iter_one)
  ultimately show ?case by simp
next
  case (ev\<^sub>b_jump cd pc v env' pc' vs env sfs)
  have "S\<^sub>e (unflatten_closure cd v # Lam\<^sub>e (unflatten_values cd env') (unflatten_code cd pc') # unflatten_values cd vs) 
    ((unflatten_values cd env, [Jump\<^sub>e]) # unflatten_stack cd sfs) \<leadsto>\<^sub>e S\<^sub>e (unflatten_values cd vs)
        ((unflatten_closure cd v # unflatten_values cd env', unflatten_code cd pc') # 
          unflatten_stack cd sfs)" by (metis ev\<^sub>e_jump)
  with ev\<^sub>b_jump have "S\<^sub>e (unflatten_closure cd v # 
    Lam\<^sub>e (unflatten_values cd env') (unflatten_code cd pc') # unflatten_values cd vs)
      ((unflatten_values cd env, unflatten_code cd (Suc pc)) # unflatten_stack cd sfs) \<leadsto>\<^sub>e
        S\<^sub>e (unflatten_values cd vs) ((unflatten_closure cd v # unflatten_values cd env', unflatten_code cd pc') # unflatten_stack cd sfs)" by simp
  hence "iter (\<leadsto>\<^sub>e) (S\<^sub>e (unflatten_closure cd v # 
    Lam\<^sub>e (unflatten_values cd env') (unflatten_code cd pc') # unflatten_values cd vs)
      ((unflatten_values cd env, unflatten_code cd (Suc pc)) # unflatten_stack cd sfs))
        (S\<^sub>e (unflatten_values cd vs) ((unflatten_closure cd v # unflatten_values cd env', unflatten_code cd pc') # unflatten_stack cd sfs))" 
    by (metis iter_one)
  thus ?case by simp
qed

lemma [simp]: "Lam\<^sub>e envt cdt = unflatten_closure cdb vb \<Longrightarrow> 
  \<exists>envb pc. vb = Lam\<^sub>b envb pc \<and> envt = unflatten_values cdb envb \<and> cdt = unflatten_code cdb pc"
  by (induction vb) simp_all

lemma unfl_state [dest]: "S\<^sub>e vs sfs = unflatten_state cd \<Sigma>\<^sub>b \<Longrightarrow> \<exists>vsb sfsb. 
    \<Sigma>\<^sub>b = S\<^sub>b vsb sfsb \<and> vs = unflatten_values cd vsb \<and> sfs = unflatten_stack cd sfsb"
  by (induction \<Sigma>\<^sub>b) simp_all

lemma [dest]: "Lookup\<^sub>e x # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> orderly_code cdb 0 \<Longrightarrow> 
    pc < length cdb \<Longrightarrow> lookup cdb pc = Some (Lookup\<^sub>b x) \<and> cdt = unflatten_code cdb pc"
  by (simp split: option.splits code\<^sub>b.splits)

lemma [dest]: "PushCon\<^sub>e k # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> orderly_code cdb 0 \<Longrightarrow> 
    pc < length cdb \<Longrightarrow> lookup cdb pc = Some (PushCon\<^sub>b k) \<and> cdt = unflatten_code cdb pc"
  by (simp split: option.splits code\<^sub>b.splits)

lemma [dest]: "PushLam\<^sub>e cdt'' # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> 
  orderly_code cdb 0 \<Longrightarrow> pc < length cdb \<Longrightarrow>  
    \<exists>pc'. lookup cdb pc = Some (PushLam\<^sub>b pc') \<and> cdt = unflatten_code cdb pc \<and> 
      cdt'' = unflatten_code cdb pc'"
  by (simp split: option.splits code\<^sub>b.splits)

lemma [dest]: "Apply\<^sub>e # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> orderly_code cdb 0 \<Longrightarrow> 
    pc < length cdb \<Longrightarrow> lookup cdb pc = Some Apply\<^sub>b \<and> cdt = unflatten_code cdb pc"
  by (simp split: option.splits code\<^sub>b.splits)

lemma [dest]: "Return\<^sub>e # cd = unflatten_code cdb (Suc pc) \<Longrightarrow> 
    orderly_code cdb 0 \<Longrightarrow> pc < length cdb \<Longrightarrow> lookup cdb pc = Some Return\<^sub>b \<and> cd = []"
  by (simp split: option.splits code\<^sub>b.splits)

lemma [dest]: "Jump\<^sub>e # cd = unflatten_code cdb (Suc pc) \<Longrightarrow> 
    orderly_code cdb 0 \<Longrightarrow> pc < length cdb \<Longrightarrow> lookup cdb pc = Some Jump\<^sub>b \<and> cd = []"
  by (simp split: option.splits code\<^sub>b.splits)

lemma uf_to_lookup [dest]: "(envt, Lookup\<^sub>e x # cdt) # sfst = unflatten_stack cdb sfsb \<Longrightarrow> 
  orderly_code cdb 0 \<Longrightarrow> orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. 
    sfsb = (envb, Suc pc) # sfsb' \<and> envt = unflatten_values cdb envb \<and> lookup cdb pc = Some (Lookup\<^sub>b x) \<and> 
      cdt = unflatten_code cdb pc \<and> sfst = unflatten_stack cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "Lookup\<^sub>e x # cdt = unflatten_code cdb (Suc pc) \<and> orderly_code cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some (Lookup\<^sub>b x) \<and> cdt = unflatten_code cdb pc" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_pushcon [dest]: "(envt, PushCon\<^sub>e k # cdt) # sfst = unflatten_stack cdb sfsb \<Longrightarrow> 
  orderly_code cdb 0 \<Longrightarrow> orderly_stack sfsb (length cdb) \<Longrightarrow> 
    \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> envt = unflatten_values cdb envb \<and> 
      lookup cdb pc = Some (PushCon\<^sub>b k) \<and> cdt = unflatten_code cdb pc \<and> sfst = unflatten_stack cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "PushCon\<^sub>e k # cdt = unflatten_code cdb (Suc pc) \<and> orderly_code cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some (PushCon\<^sub>b k) \<and> cdt = unflatten_code cdb pc" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_pushlam [dest]: "(envt, PushLam\<^sub>e cdt' # cdt) # sfst = unflatten_stack cdb sfsb \<Longrightarrow> 
  orderly_code cdb 0 \<Longrightarrow> orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb' pc'. 
    sfsb = (envb, Suc pc) # sfsb' \<and> envt = unflatten_values cdb envb \<and> lookup cdb pc = Some (PushLam\<^sub>b pc') \<and> 
      cdt = unflatten_code cdb pc \<and> cdt' = unflatten_code cdb pc' \<and> sfst = unflatten_stack cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "PushLam\<^sub>e cdt' # cdt = unflatten_code cdb (Suc pc) \<and> orderly_code cdb 0 \<and> pc < length cdb" 
    by simp
  then obtain pc' where "lookup cdb pc = Some (PushLam\<^sub>b pc') \<and> cdt = unflatten_code cdb pc \<and> 
    cdt' = unflatten_code cdb pc'" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_apply [dest]: "(envt, Apply\<^sub>e # cdt) # sfst = unflatten_stack cdb sfsb \<Longrightarrow> orderly_code cdb 0 \<Longrightarrow> 
  orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> 
    envt = unflatten_values cdb envb \<and> lookup cdb pc = Some Apply\<^sub>b \<and> cdt = unflatten_code cdb pc \<and> 
      sfst = unflatten_stack cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "Apply\<^sub>e # cdt = unflatten_code cdb (Suc pc) \<and> orderly_code cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some Apply\<^sub>b \<and> cdt = unflatten_code cdb pc" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_return [dest]: "(envt, Return\<^sub>e # cd) # sfst = unflatten_stack cdb sfsb \<Longrightarrow> orderly_code cdb 0 \<Longrightarrow> 
  orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> 
    envt = unflatten_values cdb envb \<and> lookup cdb pc = Some Return\<^sub>b \<and> sfst = unflatten_stack cdb sfsb' \<and> cd = []"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "Return\<^sub>e # cd = unflatten_code cdb (Suc pc) \<and> 
    orderly_code cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some Return\<^sub>b \<and> cd = []" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_jump [dest]: "(envt, Jump\<^sub>e # cd) # sfst = unflatten_stack cdb sfsb \<Longrightarrow> orderly_code cdb 0 \<Longrightarrow> 
  orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> 
    envt = unflatten_values cdb envb \<and> lookup cdb pc = Some Jump\<^sub>b \<and> sfst = unflatten_stack cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "Jump\<^sub>e # cd = unflatten_code cdb (Suc pc) \<and> 
    orderly_code cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some Jump\<^sub>b \<and> cd = []" by blast
  with 3 show ?case by simp
qed simp_all

theorem correctb [simp]: "unflatten_state cd\<^sub>b \<Sigma>\<^sub>b \<leadsto>\<^sub>e \<Sigma>\<^sub>t' \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>b'. iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state cd\<^sub>b \<Sigma>\<^sub>b' = \<Sigma>\<^sub>t'"
proof (induction "unflatten_state cd\<^sub>b \<Sigma>\<^sub>b" \<Sigma>\<^sub>t' rule: eval\<^sub>e.induct)
  case (ev\<^sub>e_lookup env x v vs cd sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = S\<^sub>b vsb sfsb \<and> vs = unflatten_values cd\<^sub>b vsb \<and> 
    (env, Lookup\<^sub>e x # cd) # sfs = unflatten_stack cd\<^sub>b sfsb" by fastforce
  with ev\<^sub>e_lookup have "orderly_code cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = unflatten_values cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some (Lookup\<^sub>b x) \<and> cd = unflatten_code cd\<^sub>b pc \<and> 
      sfs = unflatten_stack cd\<^sub>b sfsb'" by (metis uf_to_lookup)
  with ev\<^sub>e_lookup obtain v' where V: "lookup envb x = Some v' \<and> unflatten_closure cd\<^sub>b v' = v"
    by fastforce
  with S have "cd\<^sub>b \<tturnstile> S\<^sub>b vsb ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b S\<^sub>b (v' # vsb) ((envb, pc) # sfsb')"
    by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b vsb ((envb, Suc pc) # sfsb')) (S\<^sub>b (v' # vsb) ((envb, pc) # sfsb'))" 
    by simp
  with B S V show ?case by fastforce
next
  case (ev\<^sub>e_pushcon vs env k cd sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = S\<^sub>b vsb sfsb \<and> vs = unflatten_values cd\<^sub>b vsb \<and> 
    (env, PushCon\<^sub>e k # cd) # sfs = unflatten_stack cd\<^sub>b sfsb" by fastforce
  with ev\<^sub>e_pushcon have "orderly_code cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = unflatten_values cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some (PushCon\<^sub>b k) \<and> cd = unflatten_code cd\<^sub>b pc \<and> 
      sfs = unflatten_stack cd\<^sub>b sfsb'" by (metis uf_to_pushcon)
  with S have "cd\<^sub>b \<tturnstile> S\<^sub>b vsb ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b S\<^sub>b (Const\<^sub>b k # vsb) ((envb, pc) # sfsb')"
    by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b vsb ((envb, Suc pc) # sfsb')) 
    (S\<^sub>b (Const\<^sub>b k # vsb) ((envb, pc) # sfsb'))" by simp
  with B S show ?case by fastforce
next
  case (ev\<^sub>e_pushlam vs env cd' cd sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = S\<^sub>b vsb sfsb \<and> vs = unflatten_values cd\<^sub>b vsb \<and> 
    (env, PushLam\<^sub>e cd' # cd) # sfs = unflatten_stack cd\<^sub>b sfsb" by fastforce
  with ev\<^sub>e_pushlam have "orderly_code cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' pc' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = unflatten_values cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some (PushLam\<^sub>b pc') \<and> cd = unflatten_code cd\<^sub>b pc \<and> 
      sfs = unflatten_stack cd\<^sub>b sfsb' \<and> cd' = unflatten_code cd\<^sub>b pc'" by (metis uf_to_pushlam)
  with S have "cd\<^sub>b \<tturnstile> S\<^sub>b vsb ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b 
    S\<^sub>b (Lam\<^sub>b envb pc' # vsb) ((envb, pc) # sfsb')" by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b vsb ((envb, Suc pc) # sfsb')) 
    (S\<^sub>b (Lam\<^sub>b envb pc' # vsb) ((envb, pc) # sfsb'))" by simp
  with B S show ?case by fastforce
next
  case (ev\<^sub>e_apply v env' cd' vs env cd sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = S\<^sub>b vsb sfsb \<and> 
    v # Lam\<^sub>e env' cd' # vs = unflatten_values cd\<^sub>b vsb \<and> (env, Apply\<^sub>e # cd) # sfs = unflatten_stack cd\<^sub>b sfsb" 
      by fastforce
  with ev\<^sub>e_apply have "orderly_code cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = unflatten_values cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some Apply\<^sub>b \<and> cd = unflatten_code cd\<^sub>b pc \<and> 
      sfs = unflatten_stack cd\<^sub>b sfsb'" by (metis uf_to_apply)
  from B obtain vb envb' pc' vsb' where V: "vsb = vb # Lam\<^sub>b envb' pc' # vsb' \<and> 
    v = unflatten_closure cd\<^sub>b vb \<and> env' = unflatten_values cd\<^sub>b envb' \<and> cd' = unflatten_code cd\<^sub>b pc' \<and>
      vs = unflatten_values cd\<^sub>b vsb'" by fastforce
  from S have "cd\<^sub>b \<tturnstile> S\<^sub>b (vb # Lam\<^sub>b envb' pc' # vsb') ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b
    S\<^sub>b vsb' ((vb # envb', pc') # (envb, pc) # sfsb')" by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b (vb # Lam\<^sub>b envb' pc' # vsb') ((envb, Suc pc) # sfsb')) 
    (S\<^sub>b vsb' ((vb # envb', pc') # (envb, pc) # sfsb'))" by simp
  with B S V show ?case by auto                                              
next
  case (ev\<^sub>e_return vs env cd sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = S\<^sub>b vsb sfsb \<and> vs = unflatten_values cd\<^sub>b vsb \<and> 
    (env, Return\<^sub>e # cd) # sfs = unflatten_stack cd\<^sub>b sfsb" by fastforce
  with ev\<^sub>e_return have "orderly_code cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = unflatten_values cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some Return\<^sub>b \<and> sfs = unflatten_stack cd\<^sub>b sfsb'" 
      by (metis uf_to_return)
  with S have "cd\<^sub>b \<tturnstile> S\<^sub>b vsb ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b S\<^sub>b vsb sfsb'" by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b vsb ((envb, Suc pc) # sfsb')) (S\<^sub>b vsb sfsb')" by simp
  with B S show ?case by fastforce
next
  case (ev\<^sub>e_jump v env' cd' vs env cd sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = S\<^sub>b vsb sfsb \<and> 
    v # Lam\<^sub>e env' cd' # vs = unflatten_values cd\<^sub>b vsb \<and> 
      (env, Jump\<^sub>e # cd) # sfs = unflatten_stack cd\<^sub>b sfsb" by fastforce
  with ev\<^sub>e_jump have "orderly_code cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = unflatten_values cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some Jump\<^sub>b \<and> sfs = unflatten_stack cd\<^sub>b sfsb'" 
      by (metis uf_to_jump)
  from B obtain vb envb' pc' vsb' where V: "vsb = vb # Lam\<^sub>b envb' pc' # vsb' \<and> 
    v = unflatten_closure cd\<^sub>b vb \<and> env' = unflatten_values cd\<^sub>b envb' \<and> cd' = unflatten_code cd\<^sub>b pc' \<and>
      vs = unflatten_values cd\<^sub>b vsb'" by fastforce
  from S have "cd\<^sub>b \<tturnstile> S\<^sub>b (vb # Lam\<^sub>b envb' pc' # vsb') ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b
    S\<^sub>b vsb' ((vb # envb', pc') # sfsb')" by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (S\<^sub>b (vb # Lam\<^sub>b envb' pc' # vsb') ((envb, Suc pc) # sfsb')) 
    (S\<^sub>b vsb' ((vb # envb', pc') # sfsb'))" by simp
  with B S V show ?case by auto                                              
qed

lemma [simp]: "cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>b \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b'"
proof (induction cd\<^sub>b \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: eval\<^sub>b.induct)
  case (ev\<^sub>b_lookup cd pc x env v vs sfs)
  thus ?case by (cases pc, cases cd) simp_all
next
  case (ev\<^sub>b_pushcon cd pc k vs env sfs)
  thus ?case by (cases pc, cases cd) simp_all
next
  case (ev\<^sub>b_pushlam cd pc pc' vs env sfs)
  thus ?case 
  proof (cases pc)
    case 0
    with ev\<^sub>b_pushlam show ?thesis by (cases cd) simp_all
  qed simp_all
next
  case (ev\<^sub>b_apply cd pc v env' pc' vs env sfs)
  thus ?case by (cases pc', simp, cases pc, cases cd) simp_all
next
  case (ev\<^sub>b_jump cd pc v env' pc' vs env sfs)
  thus ?case by (cases pc') simp_all
qed simp_all

lemma [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b'"
  by (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: iter.induct) simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>e) (unflatten_state cd\<^sub>b \<Sigma>\<^sub>b) \<Sigma>\<^sub>t' \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>b'. iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state cd\<^sub>b \<Sigma>\<^sub>b' = \<Sigma>\<^sub>t'"
proof (induction "unflatten_state cd\<^sub>b \<Sigma>\<^sub>b" \<Sigma>\<^sub>t' arbitrary: \<Sigma>\<^sub>b rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>t' \<Sigma>\<^sub>t'')
  moreover then obtain \<Sigma>\<^sub>b' where S: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state cd\<^sub>b \<Sigma>\<^sub>b' = \<Sigma>\<^sub>t'" 
    by fastforce
  moreover with iter_step have "orderly_state cd\<^sub>b \<Sigma>\<^sub>b'" by fastforce
  ultimately obtain \<Sigma>\<^sub>b'' where "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b' \<Sigma>\<^sub>b'' \<and> unflatten_state cd\<^sub>b \<Sigma>\<^sub>b'' = \<Sigma>\<^sub>t''" 
    by fastforce
  with S show ?case by (metis iter_append)
qed force+

lemma unfl_terminal [simp]: "unflatten_state cd \<Sigma> = S\<^sub>e [c] [] \<Longrightarrow>
  \<exists>v. \<Sigma> = S\<^sub>b [v] [] \<and> c = unflatten_closure cd v"
proof -
  assume "unflatten_state cd \<Sigma> = S\<^sub>e [c] []"
  then obtain vs sfs where S: "\<Sigma> = S\<^sub>b vs sfs \<and> [c] = unflatten_values cd vs \<and> [] = unflatten_stack cd sfs" 
    by (metis unfl_state)
  moreover then obtain v where "vs = [v] \<and> c = unflatten_closure cd v" by blast
  ultimately show ?thesis by simp
qed

lemma evalb_end [simp]: "iter (\<leadsto>\<^sub>e) (unflatten_state cd\<^sub>b \<Sigma>\<^sub>b) (S\<^sub>e [c] []) \<Longrightarrow> 
  orderly_state cd\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow> 
    \<exists>v. iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b (S\<^sub>b [v] []) \<and> c = unflatten_closure cd\<^sub>b v"
proof -
  assume "iter (\<leadsto>\<^sub>e) (unflatten_state cd\<^sub>b \<Sigma>\<^sub>b) (S\<^sub>e [c] [])"
  moreover assume O: "orderly_state cd\<^sub>b \<Sigma>\<^sub>b"
  ultimately obtain \<Sigma>\<^sub>b' where E: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state cd\<^sub>b \<Sigma>\<^sub>b' = S\<^sub>e [c] []" 
    by fastforce
  moreover with O have "orderly_state cd\<^sub>b \<Sigma>\<^sub>b'" by fastforce
  moreover with E obtain v where "\<Sigma>\<^sub>b' = S\<^sub>b [v] [] \<and> c = unflatten_closure cd\<^sub>b v" 
    by (metis unfl_terminal)
  ultimately show ?thesis by blast
qed

end