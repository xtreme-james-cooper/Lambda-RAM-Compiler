theory CodeFlattening
  imports ByteCode "../05TreeCode/TreeCode"
begin

fun flatten_code' :: "nat \<Rightarrow> tree_code list \<Rightarrow> byte_code list \<Rightarrow> byte_code list" where
  "flatten_code' lib [] acc = acc"
| "flatten_code' lib (TLookup x # cd) acc = flatten_code' lib cd (BLookup x # acc)"
| "flatten_code' lib (TPushCon k # cd) acc = flatten_code' lib cd (BPushCon k # acc)"
| "flatten_code' lib (TPushLam cd' # cd) acc = (
    let clo = flatten_code' lib cd' []
    in clo @ flatten_code' (lib + length clo) cd (BPushLam (lib + length clo) # acc))"
| "flatten_code' lib (TApply # cd) acc = flatten_code' lib cd (BApply # acc)"
| "flatten_code' lib (TReturn # cd) acc = flatten_code' lib cd (BReturn # acc)"
| "flatten_code' lib (TJump # cd) acc = flatten_code' lib cd (BJump # acc)"

definition flatten_code :: "tree_code list \<Rightarrow> byte_code list" where
  "flatten_code cd = flatten_code' 0 cd []"

fun unflatten_code :: "byte_code list \<Rightarrow> nat \<Rightarrow> tree_code list" where
  "unflatten_code cd 0 = undefined"
| "unflatten_code cd (Suc pc) = (case cd ! pc of
      BLookup x \<Rightarrow> TLookup x # unflatten_code cd pc
    | BPushCon k \<Rightarrow> TPushCon k # unflatten_code cd pc
    | BPushLam pc' \<Rightarrow> 
        if pc' \<le> pc then TPushLam (unflatten_code cd pc') # unflatten_code cd pc else undefined
    | BApply \<Rightarrow> TApply # unflatten_code cd pc
    | BReturn \<Rightarrow> [TReturn]
    | BJump \<Rightarrow> [TJump])"

abbreviation ufcd :: "byte_code list \<Rightarrow> nat list \<Rightarrow> tree_code list" where
  "ufcd cd pcs \<equiv> concat (map (unflatten_code cd) pcs)"

primrec unflatten_closure :: "byte_code list \<Rightarrow> bclosure \<Rightarrow> tclosure" where
  "unflatten_closure cd (BConst k) = TConst k"
| "unflatten_closure cd (BLam vs pc) = 
    TLam (map (unflatten_closure cd) vs) (unflatten_code cd pc)"

abbreviation ufcs :: "byte_code list \<Rightarrow> bclosure list \<Rightarrow> tclosure list" where
  "ufcs cd vs \<equiv> map (unflatten_closure cd) vs"

primrec unflatten_state :: "byte_code_state \<Rightarrow> tree_code_state" where
  "unflatten_state (BS vs envs pcs cd) = TS (ufcs cd vs) (map (ufcs cd) envs) (ufcd cd pcs)"

primrec code_size :: "tree_code \<Rightarrow> nat"
    and code_list_size :: "tree_code list \<Rightarrow> nat" where
  "code_size (TLookup x) = 1"
| "code_size (TPushCon k) = 1"
| "code_size (TPushLam cd) = Suc (code_list_size cd)"
| "code_size TApply = 1"
| "code_size TReturn = 1"
| "code_size TJump = 1"
| "code_list_size [] = 0"
| "code_list_size (c # cd) = code_size c + code_list_size cd"

fun ordered :: "byte_code \<Rightarrow> nat \<Rightarrow> bool" where
  "ordered (BPushLam pc) n = (0 < pc \<and> pc \<le> n)"
| "ordered _ n = True"

primrec ordered_closure :: "bclosure \<Rightarrow> nat \<Rightarrow> bool" 
    and ordered_closures :: "bclosure list \<Rightarrow> nat \<Rightarrow> bool" where
  "ordered_closure (BConst k) n = True"
| "ordered_closure (BLam vs pc) n = (0 < pc \<and> pc \<le> n \<and> ordered_closures vs n)"
| "ordered_closures [] n = True"
| "ordered_closures (v # vs) n = (ordered_closure v n \<and> ordered_closures vs n)"

primrec orderly :: "byte_code list \<Rightarrow> nat \<Rightarrow> bool" where
  "orderly [] n = True"
| "orderly (op # cd) n = (ordered op n \<and> orderly cd (Suc n))"

primrec return_terminated\<^sub>b :: "byte_code list \<Rightarrow> bool" where
  "return_terminated\<^sub>b [] = False"
| "return_terminated\<^sub>b (op # cd) = (op = BReturn \<or> op = BJump)"

primrec orderly_state :: "byte_code_state \<Rightarrow> bool" where
  "orderly_state (BS vs envs pcs cd) = (orderly cd 0 \<and> return_terminated\<^sub>b cd \<and> 
    (\<forall>pc \<in> set pcs. 0 < pc \<and> pc \<le> length cd) \<and> (ordered_closures vs (length cd)) \<and> 
      (\<forall>env \<in> set envs. ordered_closures env (length cd)))"

fun return_terminated\<^sub>t :: "tree_code list \<Rightarrow> bool" where
  "return_terminated\<^sub>t [] = False"
| "return_terminated\<^sub>t (TReturn # cd) = (cd = [])"
| "return_terminated\<^sub>t (TJump # cd) = (cd = [])"
| "return_terminated\<^sub>t (TPushLam cd' # cd) = (return_terminated\<^sub>t cd' \<and> return_terminated\<^sub>t cd)"
| "return_terminated\<^sub>t (op # cd) = return_terminated\<^sub>t cd"

(*

lemma flatten_length [simp]: "length (flatten_code' lib cd acc) = code_list_size cd + length acc"
  by (induction lib cd acc rule: flatten_code'.induct) simp_all

lemma [simp]: "length (flatten_code cd) = code_list_size cd"
  by (simp add: flatten_code_def)

lemma [simp]: "Suc 0 \<le> code_list_size cd"
  by (induction cd) simp_all

lemma [simp]: "0 < code_list_size cd"
  by (induction cd) simp_all

lemma [simp]: "flatten_code' cd lib acc \<noteq> []"
  by (induction cd lib acc rule: flatten_code'.induct) simp_all

lemma [simp]: "flatten_code cd \<noteq> []"
  by (simp add: flatten_code_def)

lemma [simp]: "flatten_code' cd lib acc ! 0 = BReturn_Old"
proof (induction cd lib acc rule: flatten_code'.induct)
  case (4 lib cd' cd acc)
  moreover have "length (flatten_code' lib cd' []) > 0" by simp
  ultimately have "(flatten_code' lib cd' [] @ 
    flatten_code' (lib + code_list_size cd') cd (BPushLam (lib + code_list_size cd') # acc)) ! 0 =
      BReturn_Old" by (metis nth_append)
  thus ?case by simp
qed simp_all

lemma [simp]: "flatten_code cd ! 0 = BReturn_Old"
  by (simp add: flatten_code_def)

lemma [simp]: "ordered op x \<Longrightarrow> ordered op (Suc x)"
  by (induction op) simp_all

lemma [simp]: "ordered op (x + n) \<Longrightarrow> ordered op (x + (m + n))"
  by (induction op) simp_all

lemma [simp]: "\<forall>x < length cd. ordered (cd ! x) (x + n) \<Longrightarrow> ordered op n \<Longrightarrow>
    x < Suc (length cd) \<Longrightarrow> ordered ((op # cd) ! x) (x + n)" 
  by (cases x) simp_all

lemma [simp]: "\<forall>x < length cd. ordered (cd ! x) (x + n) \<Longrightarrow> orderly cd (Suc n)"
  by (induction cd arbitrary: n) force+

lemma [simp]: "orderly (cd @ cd') n = (orderly cd n \<and> orderly cd' (length cd + n))"
  by (induction cd arbitrary: n) simp_all

lemma [simp]: "\<forall>x < length acc. ordered (acc ! x) (x + n) \<Longrightarrow> lib \<le> n \<Longrightarrow> 
    orderly (flatten_code' lib cd acc) n"
  by (induction lib cd acc arbitrary: n rule: flatten_code'.induct) simp_all

lemma [simp]: "orderly (flatten_code cd) 0"
  by (simp add: flatten_code_def)

lemma [simp]: "lookup vs x = Some v \<Longrightarrow> ordered_closures vs n \<Longrightarrow> ordered_closure v n"
  by (induction vs x rule: lookup.induct) simp_all

lemma pushlam_ordered [simp]: "cd ! x = BPushLam pc \<Longrightarrow> orderly cd n \<Longrightarrow> x < length cd \<Longrightarrow> 
    0 < pc \<and> pc \<le> length cd + n"
  by (induction cd x arbitrary: n rule: lookup.induct) fastforce+

lemma [simp]: "cd ! x = BPushLam pc \<Longrightarrow> orderly cd 0 \<Longrightarrow> x < length cd \<Longrightarrow> 0 < pc \<and> pc \<le> length cd"
  using pushlam_ordered by fastforce

lemma index_into_append [simp]: 
  "(flatten_code' lib cd [] @ cd') ! (code_list_size cd + n) = cd' ! n"
    by (metis add.right_neutral flatten_length list.size(3) nth_append_length_plus)

lemma index_into_flatten [simp]: "flatten_code' lib cd acc ! (n + code_list_size cd) = acc ! n"
proof (induction lib cd acc arbitrary: n rule: flatten_code'.induct)
  case (2 lib x cd acc)
  hence "flatten_code' lib cd (BLookup x # acc) ! (Suc n + code_list_size cd) = 
    (BLookup x # acc) ! Suc n" by blast
  then show ?case by simp
next
  case (3 lib k cd acc)
  hence "flatten_code' lib cd (BPushCon k # acc) ! (Suc n + code_list_size cd) = 
    (BPushCon k # acc) ! Suc n" by blast
  then show ?case by simp
next
  case (4 lib cd' cd acc)
  hence "flatten_code' (lib + length (flatten_code' lib cd' [])) cd 
    (BPushLam (lib + length (flatten_code' lib cd' [])) # acc) ! (Suc n + code_list_size cd) = 
      (BPushLam (lib + length (flatten_code' lib cd' [])) # acc) ! Suc n" by blast
  hence "flatten_code' (lib + code_list_size cd') cd 
    (BPushLam (lib + code_list_size cd') # acc) ! Suc (n + code_list_size cd) = acc ! n" by simp
  hence "(flatten_code' lib cd' [] @ flatten_code' (lib + code_list_size cd') cd 
    (BPushLam (lib + code_list_size cd') # acc)) !
      (code_list_size cd' + Suc (n + code_list_size cd)) = acc ! n" by (metis index_into_append)
  moreover have "code_list_size cd' + Suc (n + code_list_size cd) = 
    Suc (n + (code_list_size cd' + code_list_size cd))" by simp
  ultimately have "(flatten_code' lib cd' [] @ flatten_code' (lib + code_list_size cd') cd 
    (BPushLam (lib + code_list_size cd') # acc)) !
      Suc (n + (code_list_size cd' + code_list_size cd)) = acc ! n" by metis
  thus ?case by simp
next
  case (5 lib cd acc)
  hence "flatten_code' lib cd (BApply # acc) ! (Suc n + code_list_size cd) = 
    (BApply # acc) ! Suc n" by blast
  then show ?case by simp
next
  case (6 lib cd acc)
  hence "flatten_code' lib cd (BReturn # acc) ! (Suc n + code_list_size cd) = 
    (BReturn # acc) ! Suc n" by blast
  then show ?case by simp
next
  case (7 lib cd acc)
  hence "flatten_code' lib cd (BJump # acc) ! (Suc n + code_list_size cd) = 
    (BJump # acc) ! Suc n" by blast
  then show ?case by simp
qed simp_all

lemma [simp]: "flatten_code' lib cd (op # acc) ! code_list_size cd = op"
proof -
  have "flatten_code' lib cd (op # acc) ! (0 + code_list_size cd) = (op # acc) ! 0" 
    by (metis index_into_flatten)
  thus ?thesis by simp
qed

lemma unflatten_front [simp]: "pc \<le> length cd \<Longrightarrow> 
  unflatten_code (cd @ cd') pc = unflatten_code cd pc"
proof (induction cd pc rule: unflatten_code.induct)
  case (2 cd pc)
  hence "pc < length cd" by simp
  hence "(cd @ cd') ! pc = cd ! pc" by (metis nth_append)
  with 2 show ?case by (cases "cd ! pc") simp_all
qed simp_all

lemma unflatten_flatten [simp]: "return_terminated cd \<Longrightarrow> 
  unflatten_code (lib @ flatten_code' (length lib) cd acc) (length lib + code_list_size cd) = cd"
proof (induction "length lib" cd acc arbitrary: lib rule: flatten_code'.induct)
  case (4 cd' cd acc)
  let ?pc = "length lib + code_list_size cd'"
  let ?code' = "lib @ flatten_code' (length lib) cd' []"
  let ?code = "?code' @ flatten_code' ?pc cd (BPushLam ?pc # acc)"
  have Y: "length lib + length (flatten_code' (length lib) cd' []) = length ?code'" by simp
  from 4 have "return_terminated cd" by simp
  with 4 Y have "unflatten_code (?code' @ flatten_code' (length ?code') cd
    (BPushLam (length lib + length (flatten_code' (length lib) cd' [])) # acc))
      (length ?code' + code_list_size cd) = cd" by blast
  hence "unflatten_code ?code (length lib + code_list_size cd' + code_list_size cd) = cd" by simp
  hence X: "unflatten_code ?code (length lib + (code_list_size cd' + code_list_size cd)) = cd" 
    by (metis add.assoc)
  have "?pc \<le> length ?code'" by simp
  moreover from 4 have "unflatten_code ?code' (length lib + code_list_size cd') = cd'" by simp
  ultimately have "unflatten_code (?code' @ flatten_code' ?pc cd (BPushLam ?pc # acc)) ?pc =  cd'" 
    by (metis unflatten_front)
  with X show ?case by simp
next
  case (6 cd acc)
  moreover have "(lib @ BReturn # acc) ! length lib = BReturn" by simp
  ultimately show ?case by simp
next
  case (7 cd acc)
  moreover have "(lib @ BJump # acc) ! length lib = BJump" by simp
  ultimately show ?case by simp
qed simp_all

lemma [simp]: "return_terminated cd \<Longrightarrow> unflatten_code (flatten_code cd) (code_list_size cd) = cd"
proof (unfold flatten_code_def)
  assume "return_terminated cd"
  hence "unflatten_code ([] @ flatten_code' (length []) cd []) (length [] + code_list_size cd) = cd" 
    by (metis unflatten_flatten list.size(3))
  thus "unflatten_code (flatten_code' 0 cd []) (code_list_size cd) = cd" by simp
qed

lemma orderly_lam [simp]: "Suc pc \<le> length cd \<Longrightarrow> cd ! pc = BPushLam pc' \<Longrightarrow> orderly cd n \<Longrightarrow> 
    pc' \<le> pc + n"
  by (induction cd pc arbitrary: n rule: lookup.induct) fastforce+

lemma [simp]: "Suc pc \<le> length cd \<Longrightarrow> cd ! pc = BPushLam pc' \<Longrightarrow> orderly cd 0 \<Longrightarrow> pc' \<le> pc"
  using orderly_lam by fastforce

*)

theorem correctb [simp]: "\<Sigma>\<^sub>b \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state \<Sigma>\<^sub>b \<Longrightarrow> 
  iter (\<leadsto>\<^sub>t) (unflatten_state \<Sigma>\<^sub>b) (unflatten_state \<Sigma>\<^sub>b')"
  by simp
(*
proof (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: evalb.induct)
  case (evb_lookup cd pc x env v vs envs pcs)
  hence "TS (ufcs cd vs) (ufcs cd env # map (ufcs cd) envs) 
    (unflatten_code cd (Suc pc) @ ufcd cd pcs) \<leadsto>\<^sub>t
      TS (unflatten_closure cd v # ufcs cd vs) (map (ufcs cd) envs) 
        (unflatten_code cd pc @ ufcd cd pcs)" by simp
  thus ?case by simp
next
  case (evb_pushcon cd pc k vs env envs pcs)
  hence "TS (ufcs cd vs) (ufcs cd env # map (ufcs cd) envs) 
    (unflatten_code cd (Suc pc) @ ufcd cd pcs) \<leadsto>\<^sub>t
      TS (TConst k # ufcs cd vs) (map (ufcs cd) envs) (unflatten_code cd pc @ ufcd cd pcs)" by simp
  thus ?case by simp
next
  case (evb_pushlam cd pc pc' vs env envs pcs)
  moreover hence "pc' \<le> pc" by auto
  moreover have "iter (\<leadsto>\<^sub>t) (TS (ufcs cd vs) (ufcs cd env # map (ufcs cd) envs)
    (TPushLam (unflatten_code cd pc') # unflatten_code cd pc @ ufcd cd pcs))
      (TS (TLam (ufcs cd env) (unflatten_code cd pc') # ufcs cd vs) (map (ufcs cd) envs)
        (unflatten_code cd pc @ ufcd cd pcs))" by (metisx evt_pushlam iter_step iter_refl)
  ultimately show ?case by simp
next
  case (evb_enter cd pc vs env envs pcs)
  hence "TS (ufcs cd vs) (ufcs cd env # map (ufcs cd) envs) 
    (unflatten_code cd (Suc pc) @ ufcd cd pcs) \<leadsto>\<^sub>t
      TS (ufcs cd vs) (ufcs cd env # ufcs cd env # map (ufcs cd) envs) 
        (unflatten_code cd pc @ ufcd cd pcs)" by simp
  thus ?case by simp
next
  case (evb_apply cd pc v env pc' vs envs pcs)
  hence "TS (unflatten_closure cd v # TLam (ufcs cd env) (unflatten_code cd pc') # ufcs cd vs) 
    (map (ufcs cd) envs) (unflatten_code cd (Suc pc) @ ufcd cd pcs) \<leadsto>\<^sub>t
      TS (ufcs cd vs) ((unflatten_closure cd v # ufcs cd env) # map (ufcs cd) envs)
        (unflatten_code cd pc' @ unflatten_code cd pc @ ufcd cd pcs)" by simp
  thus ?case by simp
next
  case (evb_returnb cd pc vs env envs pcs)
  hence "TS (ufcs cd vs) (ufcs cd env # map (ufcs cd) envs) 
    (unflatten_code cd (Suc pc) @ ufcd cd pcs) \<leadsto>\<^sub>t 
      TS (ufcs cd vs) (map (ufcs cd) envs) (ufcd cd pcs)" by simp
  thus ?case by simp
next
  case (evb_jump cd pc v env' pc' vs env envs pcs)
  hence "TS (unflatten_closure cd v # TLam (ufcs cd env') (unflatten_code cd pc') # ufcs cd vs)
    (ufcs cd env # map (ufcs cd) envs) (unflatten_code cd (Suc pc) @ ufcd cd pcs) \<leadsto>\<^sub>t
      TS (ufcs cd vs) ((unflatten_closure cd v # ufcs cd env') # map (ufcs cd) envs)
        (unflatten_code cd pc' @ ufcd cd pcs)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS (unflatten_closure cd v # TLam (ufcs cd env') (unflatten_code cd pc') # 
    ufcs cd vs) (ufcs cd env # map (ufcs cd) envs) (unflatten_code cd (Suc pc) @ ufcd cd pcs))
      (TS (ufcs cd vs) ((unflatten_closure cd v # ufcs cd env') # map (ufcs cd) envs)
        (unflatten_code cd pc' @ ufcd cd pcs))" using iter_step iter_refl by fast
  thus ?case by simp
qed simp_all

lemma [simp]: "TLam envt cdt = unflatten_closure cdb vb \<Longrightarrow> 
    \<exists>envb pc. vb = BLam envb pc \<and> envt = ufcs cdb envb \<and> cdt = unflatten_code cdb pc"
  by (induction vb) simp_all

lemma unfl_state [simp]: "TS vs envs cd = unflatten_state \<Sigma>\<^sub>b \<Longrightarrow> \<exists>vsb envsb pcs cdb. 
    \<Sigma>\<^sub>b = BS vsb envsb pcs cdb \<and> vs = ufcs cdb vsb \<and> envs = map (ufcs cdb) envsb \<and> cd = ufcd cdb pcs"
  by (induction \<Sigma>\<^sub>b) simp_all

lemma unfl_tlu [simp]: "TLookup x # cdt = unflatten_code cdb (Suc pc) @ cdt' \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  Suc pc \<le> length cdb \<Longrightarrow> (cdb ! pc = BLookup x \<and> cdt = unflatten_code cdb pc @ cdt')
    \<or> (cdb ! pc = BReturn_Old \<and> cdt' = TLookup x # cdt)"
  by (cases "cdb ! pc") simp_all

lemma unfl_tpc [simp]: "TPushCon k # cdt = unflatten_code cdb (Suc pc) @ cdt' \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  Suc pc \<le> length cdb \<Longrightarrow> (cdb ! pc = BPushCon k \<and> cdt = unflatten_code cdb pc @ cdt')
    \<or> (cdb ! pc = BReturn_Old \<and> cdt' = TPushCon k # cdt)"
  by (cases "cdb ! pc") simp_all

lemma unfl_tpl [simp]: "TPushLam cdt'' # cdt = unflatten_code cdb (Suc pc) @ cdt' \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> Suc pc \<le> length cdb \<Longrightarrow> 
    (\<exists>pc'. cdb ! pc = BPushLam pc' \<and> cdt = unflatten_code cdb pc @ cdt' \<and> 
      cdt'' = unflatten_code cdb pc') \<or> (cdb ! pc = BReturn_Old \<and> cdt' = TPushLam cdt'' # cdt)"
  by (cases "cdb ! pc") simp_all

lemma unfl_te [simp]: "TEnter # cdt = unflatten_code cdb (Suc pc) @ cdt' \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  Suc pc \<le> length cdb \<Longrightarrow> (cdb ! pc = BEnter \<and> cdt = unflatten_code cdb pc @ cdt')
    \<or> (cdb ! pc = BReturn_Old \<and> cdt' = TEnter # cdt)"
  by (cases "cdb ! pc") simp_all

lemma unfl_ta [simp]: "TApply # cdt = unflatten_code cdb (Suc pc) @ cdt' \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  Suc pc \<le> length cdb \<Longrightarrow> (cdb ! pc = BApply \<and> cdt = unflatten_code cdb pc @ cdt')
    \<or> (cdb ! pc = BReturn_Old \<and> cdt' = TApply # cdt)"
  by (cases "cdb ! pc") simp_all

abbreviation poppable :: "byte_code list \<Rightarrow> nat list \<Rightarrow> bool" where
  "poppable cd rs \<equiv> (\<forall>r \<in> set rs. \<exists>r'. r = Suc r' \<and> cd ! r' = BReturn_Old)"

lemma [simp]: "TLookup x # cdt = ufcd cdb pcs \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  \<forall>pc \<in> set pcs. pc \<le> length cdb \<and> pc \<noteq> 0 \<Longrightarrow> \<exists>rs pc pcs'. pcs = rs @ Suc pc # pcs' \<and> 
    poppable cdb rs \<and> cdb ! pc = BLookup x \<and> cdt = unflatten_code cdb pc @ ufcd cdb pcs'"
proof (induction pcs)
  case (Cons pc pcs)
  thus ?case
  proof (induction pc)
    case (Suc pc)
    show ?case
    proof (cases "cdb ! pc = BLookup x \<and> cdt = unflatten_code cdb pc @ ufcd cdb pcs")
      case False
      moreover from Suc have "TLookup x # cdt = unflatten_code cdb (Suc pc) @ ufcd cdb pcs" by simp
      moreover from Suc have "orderly cdb 0" by simp
      moreover from Suc have "Suc pc \<le> length cdb" by simp
      ultimately have X: "cdb ! pc = BReturn_Old \<and> ufcd cdb pcs = TLookup x # cdt" by (metis unfl_tlu)
      from Suc have "\<forall>pc\<in>set pcs. pc \<le> length cdb \<and> pc \<noteq> 0" by simp
      with Suc X obtain rs pc' pcs' where "pcs = rs @ Suc pc' # pcs' \<and> poppable cdb rs \<and> 
        cdb ! pc' = BLookup x \<and> cdt = unflatten_code cdb pc' @ ufcd cdb pcs'" by metis
      with X have "Suc pc # pcs = (Suc pc # rs) @ Suc pc' # pcs' \<and> poppable cdb (Suc pc # rs) \<and> 
        cdb ! pc' = BLookup x \<and> cdt = unflatten_code cdb pc' @ ufcd cdb pcs'" by simp
      thus ?thesis by blast
    qed fastforcex+
  qed simp_all
qed simp_all

lemma [simp]: "TPushCon k # cdt = ufcd cdb pcs \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  \<forall>pc \<in> set pcs. pc \<le> length cdb \<and> pc \<noteq> 0 \<Longrightarrow> \<exists>rs pc pcs'. pcs = rs @ Suc pc # pcs' \<and> 
    poppable cdb rs \<and> cdb ! pc = BPushCon k \<and> cdt = unflatten_code cdb pc @ ufcd cdb pcs'"
proof (induction pcs)
  case (Cons pc pcs)
  thus ?case
  proof (induction pc)
    case (Suc pc)
    show ?case
    proof (cases "cdb ! pc = BPushCon k \<and> cdt = unflatten_code cdb pc @ ufcd cdb pcs")
      case False
      moreover from Suc have "TPushCon k # cdt = unflatten_code cdb (Suc pc) @ ufcd cdb pcs" by simp
      moreover from Suc have "orderly cdb 0" by simp
      moreover from Suc have "Suc pc \<le> length cdb" by simp
      ultimately have X: "cdb ! pc = BReturn_Old \<and> ufcd cdb pcs = TPushCon k # cdt" by (metis unfl_tpc)
      from Suc have "\<forall>pc\<in>set pcs. pc \<le> length cdb \<and> pc \<noteq> 0" by simp
      with Suc X obtain rs pc' pcs' where "pcs = rs @ Suc pc' # pcs' \<and> poppable cdb rs \<and> 
        cdb ! pc' = BPushCon k \<and> cdt = unflatten_code cdb pc' @ ufcd cdb pcs'" by metis
      with X have "Suc pc # pcs = (Suc pc # rs) @ Suc pc' # pcs' \<and> poppable cdb (Suc pc # rs) \<and> 
        cdb ! pc' = BPushCon k \<and> cdt = unflatten_code cdb pc' @ ufcd cdb pcs'" by simp
      thus ?thesis by blast
    qed fastforcex+
  qed simp_all
qed simp_all

lemma ufcd_pl [simp]: "TPushLam cdt' # cdt = ufcd cdb pcs \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  \<forall>pc \<in> set pcs. pc \<le> length cdb \<and> pc \<noteq> 0 \<Longrightarrow> \<exists>rs pc pcs' pc'. pcs = rs @ Suc pc # pcs' \<and> 
    poppable cdb rs \<and> cdb ! pc = BPushLam pc' \<and> cdt' = unflatten_code cdb pc' \<and> 
      cdt = unflatten_code cdb pc @ ufcd cdb pcs'"
proof (induction pcs)
  case (Cons pc pcs)
  thus ?case
  proof (induction pc)
    case (Suc pc)
    show ?case
    proof (cases "\<exists>pc'. cdb ! pc = BPushLam pc' \<and> cdt = unflatten_code cdb pc @ ufcd cdb pcs \<and> 
                  cdt' = unflatten_code cdb pc'")
      case False
      moreover from Suc have "TPushLam cdt' # cdt = unflatten_code cdb (Suc pc) @ ufcd cdb pcs" 
        by simp
      moreover from Suc have "orderly cdb 0" by simp
      moreover from Suc have "Suc pc \<le> length cdb" by simp
      ultimately have X: "cdb ! pc = BReturn_Old \<and> ufcd cdb pcs = TPushLam cdt' # cdt" 
        by (metisx unfl_tpl)
      from Suc have "\<forall>pc\<in>set pcs. pc \<le> length cdb \<and> pc \<noteq> 0" by simp
      with Suc X obtain rs pca pcs' pc' where "pcs = rs @ Suc pca # pcs' \<and> poppable cdb rs \<and>
       cdb ! pca = BPushLam pc' \<and> cdt' = unflatten_code cdb pc' \<and> 
        cdt = unflatten_code cdb pca @ ufcd cdb pcs'" by metis
      with X have "Suc pc # pcs = (Suc pc # rs) @ Suc pca # pcs' \<and> poppable cdb (Suc pc # rs) \<and> 
        cdb ! pca = BPushLam pc' \<and> cdt' = unflatten_code cdb pc' \<and> 
          cdt = unflatten_code cdb pca @ ufcd cdb pcs'" by simp
      thus ?thesis by blast
    qed fastforcex+
  qed simp_all
qed simp_all

lemma [simp]: "TEnter # cdt = ufcd cdb pcs \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  \<forall>pc \<in> set pcs. pc \<le> length cdb \<and> pc \<noteq> 0 \<Longrightarrow> \<exists>rs pc pcs'. pcs = rs @ Suc pc # pcs' \<and> 
    poppable cdb rs \<and> cdb ! pc = BEnter \<and> cdt = unflatten_code cdb pc @ ufcd cdb pcs'"
proof (induction pcs)
  case (Cons pc pcs)
  thus ?case
  proof (induction pc)
    case (Suc pc)
    show ?case
    proof (cases "cdb ! pc = BEnter \<and> cdt = unflatten_code cdb pc @ ufcd cdb pcs")
      case False
      moreover from Suc have "TEnter # cdt = unflatten_code cdb (Suc pc) @ ufcd cdb pcs" by simp
      moreover from Suc have "orderly cdb 0" by simp
      moreover from Suc have "Suc pc \<le> length cdb" by simp
      ultimately have X: "cdb ! pc = BReturn_Old \<and> ufcd cdb pcs = TEnter # cdt" by (metis unfl_te)
      from Suc have "\<forall>pc\<in>set pcs. pc \<le> length cdb \<and> pc \<noteq> 0" by simp
      with Suc X obtain rs pc' pcs' where "pcs = rs @ Suc pc' # pcs' \<and> poppable cdb rs \<and> 
        cdb ! pc' = BEnter \<and> cdt = unflatten_code cdb pc' @ ufcd cdb pcs'" by metis
      with X have "Suc pc # pcs = (Suc pc # rs) @ Suc pc' # pcs' \<and> poppable cdb (Suc pc # rs) \<and> 
        cdb ! pc' = BEnter \<and> cdt = unflatten_code cdb pc' @ ufcd cdb pcs'" by simp
      thus ?thesis by blast
    qed fastforcex+
  qed simp_all
qed simp_all

lemma [simp]: "TApply # cdt = ufcd cdb pcs \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  \<forall>pc \<in> set pcs. pc \<le> length cdb \<and> pc \<noteq> 0 \<Longrightarrow> \<exists>rs pc pcs'. pcs = rs @ Suc pc # pcs' \<and> 
    poppable cdb rs \<and> cdb ! pc = BApply \<and> cdt = unflatten_code cdb pc @ ufcd cdb pcs'"
proof (induction pcs)
  case (Cons pc pcs)
  thus ?case
  proof (induction pc)
    case (Suc pc)
    show ?case
    proof (cases "cdb ! pc = BApply \<and> cdt = unflatten_code cdb pc @ ufcd cdb pcs")
      case False
      moreover from Suc have "TApply # cdt = unflatten_code cdb (Suc pc) @ ufcd cdb pcs" by simp
      moreover from Suc have "orderly cdb 0" by simp
      moreover from Suc have "Suc pc \<le> length cdb" by simp
      ultimately have X: "cdb ! pc = BReturn_Old \<and> ufcd cdb pcs = TApply # cdt" by (metis unfl_ta)
      from Suc have "\<forall>pc\<in>set pcs. pc \<le> length cdb \<and> pc \<noteq> 0" by simp
      with Suc X obtain rs pc' pcs' where "pcs = rs @ Suc pc' # pcs' \<and> poppable cdb rs \<and> 
        cdb ! pc' = BApply \<and> cdt = unflatten_code cdb pc' @ ufcd cdb pcs'" by metis
      with X have "Suc pc # pcs = (Suc pc # rs) @ Suc pc' # pcs' \<and> poppable cdb (Suc pc # rs) \<and> 
        cdb ! pc' = BApply \<and> cdt = unflatten_code cdb pc' @ ufcd cdb pcs'" by simp
      thus ?thesis by blast
    qed fastforcex+
  qed simp_all
qed simp_all

lemma ev_poppable [simp]: "poppable cdb rs \<Longrightarrow> 
  iter (\<leadsto>\<^sub>b) (BS vs envs (rs @ pcs) cdb) (BS vs envs pcs cdb)"
proof (induction rs)
  case (Cons r rs)
  then obtain r' where "r = Suc r' \<and> cdb ! r' = BReturn_Old" by fastforce
  hence "BS vs envs (r # rs @ pcs) cdb \<leadsto>\<^sub>b BS vs envs (rs @ pcs) cdb" by simp
  moreover from Cons have "iter (\<leadsto>\<^sub>b) (BS vs envs (rs @ pcs) cdb) (BS vs envs pcs cdb)" by simp
  ultimately show ?case by simp
qed simp_all

*)

theorem completeb [simp]: "unflatten_state \<Sigma>\<^sub>b \<leadsto>\<^sub>t \<Sigma>\<^sub>t' \<Longrightarrow> orderly_state \<Sigma>\<^sub>b \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>b'. iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state \<Sigma>\<^sub>b' = \<Sigma>\<^sub>t'"
  by simp
(*
proof (induction "unflatten_state \<Sigma>\<^sub>b" \<Sigma>\<^sub>t' rule: evalt.induct)
  case (evt_lookup env x v vs envs cd)
  then obtain vsb envsb pcs cdb where S: "\<Sigma>\<^sub>b = BS vsb envsb pcs cdb \<and> vs = ufcs cdb vsb \<and> 
    env # envs = map (ufcs cdb) envsb \<and> TLookup x # cd = ufcd cdb pcs" by fastforce
  then obtain envb envsb' where E: "envsb = envb # envsb' \<and> env = ufcs cdb envb \<and> 
    envs = map (ufcs cdb) envsb'" by fastforce
  from S evt_lookup obtain rs pc pcs' where R: "pcs = rs @ Suc pc # pcs' \<and> poppable cdb rs \<and> 
    cdb ! pc = BLookup x \<and> cd = unflatten_code cdb pc @ ufcd cdb pcs'" by fastforce
  hence X: "iter (\<leadsto>\<^sub>b) (BS vsb (envb # envsb') (rs @ Suc pc # pcs') cdb) 
    (BS vsb (envb # envsb') (Suc pc # pcs') cdb)" by simp
  from evt_lookup E obtain vb where V: "lookup envb x = Some vb \<and> unflatten_closure cdb vb = v" 
    by fastforce
  with R have "BS vsb (envb # envsb') (Suc pc # pcs') cdb \<leadsto>\<^sub>b 
    BS (vb # vsb) envsb' (pc # pcs') cdb" by simp
  with X have "iter (\<leadsto>\<^sub>b) (BS vsb (envb # envsb') (rs @ Suc pc # pcs') cdb) 
    (BS (vb # vsb) envsb' (pc # pcs') cdb)" by simp
  with S E R V show ?case by fastforcex
next
  case (evt_pushcon vs env envs k cd)
  then obtain vsb envsb pcs cdb where S: "\<Sigma>\<^sub>b = BS vsb envsb pcs cdb \<and> vs = ufcs cdb vsb \<and> 
    env # envs = map (ufcs cdb) envsb \<and> TPushCon k # cd = ufcd cdb pcs" by fastforce
  then obtain envb envsb' where E: "envsb = envb # envsb' \<and> env = ufcs cdb envb \<and> 
    envs = map (ufcs cdb) envsb'" by fastforce
  from S evt_pushcon obtain rs pc pcs' where R: "pcs = rs @ Suc pc # pcs' \<and> poppable cdb rs \<and> 
    cdb ! pc = BPushCon k \<and> cd = unflatten_code cdb pc @ ufcd cdb pcs'" by fastforcex
  hence "iter (\<leadsto>\<^sub>b) (BS vsb (envb # envsb') (rs @ Suc pc # pcs') cdb) 
    (BS vsb (envb # envsb') (Suc pc # pcs') cdb)" by simp
  moreover from R have "BS vsb (envb # envsb') (Suc pc # pcs') cdb \<leadsto>\<^sub>b 
    BS (BConst k # vsb) envsb' (pc # pcs') cdb" by simp
  ultimately have "iter (\<leadsto>\<^sub>b) (BS vsb (envb # envsb') (rs @ Suc pc # pcs') cdb) 
    (BS (BConst k # vsb) envsb' (pc # pcs') cdb)" by simp
  with S E R show ?case by fastforce
next
  case (evt_pushlam vs env envs cd' cd)
  then obtain vsb envsb pcs cdb where S: "\<Sigma>\<^sub>b = BS vsb envsb pcs cdb \<and> vs = ufcs cdb vsb \<and> 
    env # envs = map (ufcs cdb) envsb \<and> TPushLam cd' # cd = ufcd cdb pcs" by fastforcex
  then obtain envb envsb' where E: "envsb = envb # envsb' \<and> env = ufcs cdb envb \<and> 
    envs = map (ufcs cdb) envsb'" by fastforce
  from S evt_pushlam obtain rs pc pcs' pc' where R: "pcs = rs @ Suc pc # pcs' \<and> poppable cdb rs \<and> 
    cdb ! pc = BPushLam pc' \<and> cd' = unflatten_code cdb pc' \<and> 
      cd = unflatten_code cdb pc @ ufcd cdb pcs'" using ufcd_pl by fastforcex
  hence "iter (\<leadsto>\<^sub>b) (BS vsb (envb # envsb') (rs @ Suc pc # pcs') cdb) 
    (BS vsb (envb # envsb') (Suc pc # pcs') cdb)" by simp
  moreover from R have "BS vsb (envb # envsb') (Suc pc # pcs') cdb \<leadsto>\<^sub>b 
    BS (BLam envb pc' # vsb) envsb' (pc # pcs') cdb" by simp
  ultimately have "iter (\<leadsto>\<^sub>b) (BS vsb (envb # envsb') (rs @ Suc pc # pcs') cdb) 
    (BS (BLam envb pc' # vsb) envsb' (pc # pcs') cdb)" by simp
  with S E R show ?case by fastforce
next
  case (evt_enter vs env envs cd)
  then obtain vsb envsb pcs cdb where S: "\<Sigma>\<^sub>b = BS vsb envsb pcs cdb \<and> vs = ufcs cdb vsb \<and> 
    env # envs = map (ufcs cdb) envsb \<and> TEnter # cd = ufcd cdb pcs" by fastforcex
  then obtain envb envsb' where E: "envsb = envb # envsb' \<and> env = ufcs cdb envb \<and> 
    envs = map (ufcs cdb) envsb'" by fastforce
  from S evt_enter obtain rs pc pcs' where R: "pcs = rs @ Suc pc # pcs' \<and> poppable cdb rs \<and> 
    cdb ! pc = BEnter \<and> cd = unflatten_code cdb pc @ ufcd cdb pcs'" by fastforce
  hence "iter (\<leadsto>\<^sub>b) (BS vsb (envb # envsb') (rs @ Suc pc # pcs') cdb) 
    (BS vsb (envb # envsb') (Suc pc # pcs') cdb)" by simp
  moreover from R have "BS vsb (envb # envsb') (Suc pc # pcs') cdb \<leadsto>\<^sub>b 
    BS vsb (envb # envb # envsb') (pc # pcs') cdb" by simp
  ultimately have "iter (\<leadsto>\<^sub>b) (BS vsb (envb # envsb') (rs @ Suc pc # pcs') cdb) 
    (BS vsb (envb # envb # envsb') (pc # pcs') cdb)" by simp
  with S E R show ?case by fastforce
next
  case (evt_apply v env cd' vs envs cd)
  then obtain vsb envsb pcs cdb where S: "\<Sigma>\<^sub>b = BS vsb envsb pcs cdb \<and> 
    v # TLam env cd' # vs = ufcs cdb vsb \<and> envs = map (ufcs cdb) envsb \<and> 
      TApply # cd = ufcd cdb pcs" by fastforcex
  then obtain vb vvb vsb' where V: "vsb = vb # vvb # vsb' \<and> v = unflatten_closure cdb vb \<and> 
    TLam env cd' = unflatten_closure cdb vvb \<and> vs = ufcs cdb vsb'" by fastforce
  then obtain envb pc' where L: "vvb = BLam envb pc' \<and> env = ufcs cdb envb \<and> 
    cd' = unflatten_code cdb pc'" by fastforce
  from S evt_apply obtain rs pc pcs' where R: "pcs = rs @ Suc pc # pcs' \<and> poppable cdb rs \<and> 
    cdb ! pc = BApply \<and> cd = unflatten_code cdb pc @ ufcd cdb pcs'" by fastforcex
  hence "iter (\<leadsto>\<^sub>b) (BS (vb # BLam envb pc' # vsb') envsb (rs @ Suc pc # pcs') cdb) 
    (BS (vb # BLam envb pc' # vsb') envsb (Suc pc # pcs') cdb)" by simp
  moreover from R have "BS (vb # BLam envb pc' # vsb') envsb (Suc pc # pcs') cdb \<leadsto>\<^sub>b 
    BS vsb' ((vb # envb) # envsb) (pc' # pc # pcs') cdb" by simp
  ultimately have X: "iter (\<leadsto>\<^sub>b) (BS (vb # BLam envb pc' # vsb') envsb (rs @ Suc pc # pcs') cdb) 
    (BS vsb' ((vb # envb) # envsb) (pc' # pc # pcs') cdb)" by simp
  from S V L R have "unflatten_state (BS vsb' ((vb # envb) # envsb) (pc' # pc # pcs') cdb) = 
    TS vs ((v # env) # envs) (cd' @ cd)" by simp
  with S V L R X show ?case by blast
next
  case evt_return
  thus ?case by simp
next
  case evt_jump
  thus ?case by simp
qed

*)

lemma [simp]: "\<Sigma>\<^sub>b \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state \<Sigma>\<^sub>b \<Longrightarrow> orderly_state \<Sigma>\<^sub>b'"
proof (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: evalb.induct)
  case (evb_lookup cd pc x env v vs envs pcs)
  thus ?case by (cases pc) simp_all
next
  case (evb_pushcon cd pc k vs envs pcs)
  thus ?case by (cases pc) simp_all
next
  case (evb_pushlam cd pc pc' vs env envs pcs)
  thus ?case by (cases pc) simp_all
next
  case (evb_apply cd pc v env pc' vs envs pcs)
  thus ?case by (cases pc) simp_all
qed simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state \<Sigma>\<^sub>b \<Longrightarrow> orderly_state \<Sigma>\<^sub>b'"
  by (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: iter.induct) simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>t) (unflatten_state \<Sigma>\<^sub>b) \<Sigma>\<^sub>t' \<Longrightarrow> orderly_state \<Sigma>\<^sub>b \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>b'. iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state \<Sigma>\<^sub>b' = \<Sigma>\<^sub>t'"
proof (induction "unflatten_state \<Sigma>\<^sub>b" \<Sigma>\<^sub>t' arbitrary: \<Sigma>\<^sub>b rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>t' \<Sigma>\<^sub>t'')
  moreover then obtain \<Sigma>\<^sub>b' where S: "iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state \<Sigma>\<^sub>b' = \<Sigma>\<^sub>t'" by fastforcex
  moreover with iter_step have "orderly_state \<Sigma>\<^sub>b'" by fastforcex
  ultimately obtain \<Sigma>\<^sub>b'' where "iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b' \<Sigma>\<^sub>b'' \<and> unflatten_state \<Sigma>\<^sub>b'' = \<Sigma>\<^sub>t''" by fastforcex
  with S show ?case by (metis iter_append)
qed forcex+

lemma unfl_terminal [simp]: "unflatten_state \<Sigma> = TS [c] [] [] \<Longrightarrow> orderly_state \<Sigma> \<Longrightarrow>
  \<exists>v cd. \<Sigma> = BS [v] [] [] cd \<and> c = unflatten_closure cd v "
proof -
  assume "unflatten_state \<Sigma> = TS [c] [] []"
  then obtain vs envs pcs cd where S: "\<Sigma> = BS vs envs pcs cd \<and> [c] = ufcs cd vs \<and> 
    [] = map (ufcs cd) envs \<and> ufcd cd pcs = []" by (metis unfl_state)
  moreover then obtain v where "vs = [v] \<and> c = unflatten_closure cd v" by blast
  moreover from S have "envs = []" by blast
  moreover assume "orderly_state \<Sigma>"
  moreover with S have "orderly cd 0 \<and> (\<forall>pc \<in> set pcs. pc \<le> length cd \<and> pc \<noteq> 0)" by simpx
  ultimately show ?thesis by (metis no_code_poppable)
qed

lemma evalb_end [simp]: "iter (\<leadsto>\<^sub>t) (unflatten_state \<Sigma>\<^sub>b) (TS [c] [] []) \<Longrightarrow> orderly_state \<Sigma>\<^sub>b \<Longrightarrow>
  \<exists>v. iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b (BS [v] [] [] (code \<Sigma>\<^sub>b)) \<and> c = unflatten_closure (code \<Sigma>\<^sub>b) v"
proof -
  assume "iter (\<leadsto>\<^sub>t) (unflatten_state \<Sigma>\<^sub>b) (TS [c] [] [])"
  moreover assume O: "orderly_state \<Sigma>\<^sub>b"
  ultimately obtain \<Sigma>\<^sub>b' where E: "iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state \<Sigma>\<^sub>b' = TS [c] [] []" 
    by fastforcex
  moreover with O have "orderly_state \<Sigma>\<^sub>b'" by fastforcex
  moreover with E obtain v cd where "\<Sigma>\<^sub>b' = BS [v] [] [] cd \<and> c = unflatten_closure cd v" 
    by (metis unfl_terminal)
  moreover with E have "code \<Sigma>\<^sub>b = cd" by fastforcex
  ultimately show ?thesis by blast
qed

end