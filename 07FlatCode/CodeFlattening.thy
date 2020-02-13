theory CodeFlattening
  imports ByteCode "../06TailCall/TailCall"
begin

fun flatten_code' :: "nat \<Rightarrow> tco_code list \<Rightarrow> tco_return \<Rightarrow> byte_code list" where
  "flatten_code' lib [] (TCOReturn d) = [BReturn d]"
| "flatten_code' lib [] (TCOJump d) = [BJump d]"
| "flatten_code' lib (TCOLookup x # cd) r = flatten_code' lib cd r @ [BLookup x]"
| "flatten_code' lib (TCOPushCon k # cd) r = flatten_code' lib cd r @ [BPushCon k]"
| "flatten_code' lib (TCOPushLam cd' r' d # cd) r = (
    let clo = flatten_code' lib cd' r'
    in clo @ flatten_code' (lib + length clo) cd r @ [BPushLam (lib + length clo) d])"
| "flatten_code' lib (TCOApply # cd) r = flatten_code' lib cd r @ [BApply]"

primrec flatten_code :: "tco_code list \<times> tco_return \<Rightarrow> byte_code list" where
  "flatten_code (cd, r) = flatten_code' 0 cd r"

fun unflatten_return :: "byte_code list \<Rightarrow> nat \<Rightarrow> tco_return" where
  "unflatten_return cd 0 = undefined"
| "unflatten_return cd (Suc pc) = (case cd ! pc of
      BReturn d \<Rightarrow> TCOReturn d
    | BJump d \<Rightarrow> TCOJump d
    | op \<Rightarrow> unflatten_return cd pc)"

fun unflatten_code :: "byte_code list \<Rightarrow> nat \<Rightarrow> tco_code list" where
  "unflatten_code cd 0 = []"
| "unflatten_code cd (Suc pc) = (case cd ! pc of
      BLookup x \<Rightarrow> TCOLookup x # unflatten_code cd pc
    | BPushCon k \<Rightarrow>  TCOPushCon k # unflatten_code cd pc
    | BPushLam pc' d \<Rightarrow> (
        if pc' \<le> pc 
        then TCOPushLam (unflatten_code cd pc') (unflatten_return cd pc') d # unflatten_code cd pc 
        else undefined) 
    | BApply \<Rightarrow> TCOApply # unflatten_code cd pc
    | BReturn d \<Rightarrow> []
    | BJump d \<Rightarrow> [])"

primrec unflatten_closure :: "byte_code list \<Rightarrow> bclosure \<Rightarrow> tco_closure" where
  "unflatten_closure cd (BConst k) = TCOConst k"
| "unflatten_closure cd (BLam vs pc) = 
    TCOLam (map (unflatten_closure cd) vs) (unflatten_code cd pc) (unflatten_return cd pc)"

abbreviation ufcs :: "byte_code list \<Rightarrow> bclosure list \<Rightarrow> tco_closure list" where
  "ufcs cd vs \<equiv> map (unflatten_closure cd) vs"

primrec ufsf :: "byte_code list \<Rightarrow> (bclosure list \<times> nat) \<Rightarrow> tco_stack_frame" where
  "ufsf cd (vs, pc) = (ufcs cd vs, unflatten_code cd pc, unflatten_return cd pc)"

abbreviation ufsfs :: "byte_code list \<Rightarrow> (bclosure list \<times> nat) list \<Rightarrow> tco_stack_frame list" where
  "ufsfs cd pcs \<equiv> map (ufsf cd) pcs"

primrec unflatten_state :: "byte_code_state \<Rightarrow> tco_code_state" where
  "unflatten_state (BS vs sfs cd) = TCOS (ufcs cd vs) (ufsfs cd sfs)"

primrec code_size :: "tco_code \<Rightarrow> nat"
    and code_list_size :: "tco_code list \<Rightarrow> nat" where
  "code_size (TCOLookup x) = 1"
| "code_size (TCOPushCon k) = 1"
| "code_size (TCOPushLam cd r d) = Suc (code_list_size cd)"
| "code_size TCOApply = 1"
| "code_list_size [] = 1"
| "code_list_size (c # cd) = code_size c + code_list_size cd"

fun ordered :: "byte_code \<Rightarrow> nat \<Rightarrow> bool" where
  "ordered (BPushLam pc d) n = (0 < pc \<and> pc \<le> n)"
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

primrec return_terminated :: "byte_code list \<Rightarrow> bool" where
  "return_terminated [] = False"
| "return_terminated (op # cd) = (\<exists>d. op = BReturn d \<or> op = BJump d)"

fun orderly_stack :: "(bclosure list \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "orderly_stack [] cd = True"
| "orderly_stack ((env, 0) # sfs) cd = False"
| "orderly_stack ((env, Suc pc) # sfs) cd = 
    (pc < cd \<and> ordered_closures env cd \<and> orderly_stack sfs cd)"

primrec orderly_state :: "byte_code_state \<Rightarrow> bool" where
  "orderly_state (BS vs sfs cd) = (orderly cd 0 \<and> return_terminated cd \<and> 
    orderly_stack sfs (length cd) \<and> ordered_closures vs (length cd))"

lemma flatten_length [simp]: "length (flatten_code' lib cd r) = code_list_size cd"
  by (induction lib cd r rule: flatten_code'.induct) simp_all

lemma [simp]: "length (flatten_code (cd, r)) = code_list_size cd"
  by (simp add: flatten_code_def)

lemma [simp]: "Suc 0 \<le> code_list_size cd"
  by (induction cd) simp_all

lemma [simp]: "0 < code_list_size cd"
  by (induction cd) simp_all

lemma [simp]: "flatten_code' lib cd r \<noteq> []"
  by (induction lib cd r rule: flatten_code'.induct) simp_all

lemma [simp]: "flatten_code (cd, r) \<noteq> []"
  by (simp add: flatten_code_def)

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> return_terminated (cd @ cd') = return_terminated cd"
  by (induction cd) simp_all

lemma [simp]: "return_terminated (flatten_code' lib cd r)"
  by (induction lib cd r rule: flatten_code'.induct) simp_all

lemma [simp]: "return_terminated (flatten_code cdr)"
  by (cases cdr) (simp add: flatten_code_def)

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

lemma [simp]: "lib \<le> n \<Longrightarrow> orderly (flatten_code' lib cd r) n"
  by (induction lib cd r arbitrary: n rule: flatten_code'.induct) simp_all

lemma [simp]: "orderly (flatten_code cdr) 0"
  by (cases cdr) (simp add: flatten_code_def)

lemma [simp]: "x > 0 \<Longrightarrow> orderly_stack [([], x)] x"
  by (cases x) simp_all

lemma [simp]: "orderly_stack [([], length (flatten_code cdr))] (length (flatten_code cdr))"
  by (cases cdr) simp_all

lemma [simp]: "lookup vs x = Some v \<Longrightarrow> ordered_closures vs n \<Longrightarrow> ordered_closure v n"
  by (induction vs x rule: lookup.induct) simp_all

lemma pushlam_ordered [simp]: "cd ! x = BPushLam pc d \<Longrightarrow> orderly cd n \<Longrightarrow> x < length cd \<Longrightarrow> 
    0 < pc \<and> pc \<le> length cd + n"
  by (induction cd x arbitrary: n rule: lookup.induct) fastforce+

lemma [simp]: "cd ! x = BPushLam pc d \<Longrightarrow> orderly cd 0 \<Longrightarrow> x < length cd \<Longrightarrow> 
    0 < pc \<and> pc \<le> length cd"
  using pushlam_ordered by fastforce

lemma index_into_append [simp]: "(flatten_code' lib cd r @ cd') ! (code_list_size cd + n) = cd' ! n"
  by (metis flatten_length nth_append_length_plus)

lemma [simp]: "(flatten_code' lib cd r @ op # acc) ! code_list_size cd = op"
proof -
  have "(flatten_code' lib cd r @ op # acc) ! (code_list_size cd + 0) = (op # acc) ! 0" 
    by (metis index_into_append)
  thus ?thesis by simp
qed

lemma unflatten_r_front [simp]: "pc \<le> length cd \<Longrightarrow> 
  unflatten_return (cd @ cd') pc = unflatten_return cd pc"
proof (induction cd pc rule: unflatten_return.induct)
  case (2 cd pc)
  hence "pc < length cd" by simp
  hence "(cd @ cd') ! pc = cd ! pc" by (metis nth_append)
  with 2 show ?case by (cases "cd ! pc") simp_all
qed simp_all

lemma unflatten_front [simp]: "pc \<le> length cd \<Longrightarrow> 
  unflatten_code (cd @ cd') pc = unflatten_code cd pc"
proof (induction cd pc rule: unflatten_code.induct)
  case (2 cd pc)
  hence "pc < length cd" by simp
  hence "(cd @ cd') ! pc = cd ! pc" by (metis nth_append)
  with 2 show ?case by (cases "cd ! pc") simp_all
qed simp_all

lemma unflatten_flatten_r [simp]: "unflatten_return (lib @ flatten_code' (length lib) cd r @ acc) 
  (length lib + code_list_size cd) = r"
proof (induction "length lib" cd r arbitrary: lib acc rule: flatten_code'.induct)
  case (5 cd' r' d cd r)
  let ?pc = "length lib + code_list_size cd'"
  let ?code' = "lib @ flatten_code' (length lib) cd' r'"
  let ?code = "?code' @ flatten_code' ?pc cd r @ BPushLam ?pc d # acc"
  have "length lib + length (flatten_code' (length lib) cd' r') = length ?code'" by simp
  with 5 have "unflatten_return (?code' @ flatten_code' (length ?code') cd r @
    BPushLam (length lib + length (flatten_code' (length lib) cd' r')) d # acc)
     (length ?code' + code_list_size cd) = r" by blast
  hence "unflatten_return ?code (length lib + code_list_size cd' + code_list_size cd) = r" by simp
  hence "unflatten_return ?code (length lib + (code_list_size cd' + code_list_size cd)) = r" 
    by (metis add.assoc)
  thus ?case by simp
qed simp_all

lemma unflatten_flatten [simp]: "unflatten_code (lib @ flatten_code' (length lib) cd r @ acc) 
  (length lib + code_list_size cd) = cd"
proof (induction "length lib" cd r arbitrary: lib acc rule: flatten_code'.induct)
  case (5 cd' r' d cd r)
  let ?pc = "length lib + code_list_size cd'"
  let ?code' = "lib @ flatten_code' (length lib) cd' r' @ []"
  let ?code = "?code' @ flatten_code' ?pc cd r @ BPushLam ?pc d # acc"
  have "length lib + length (flatten_code' (length lib) cd' r') = length ?code'" by simp
  with 5 have "unflatten_code (?code' @ flatten_code' (length ?code') cd r @
    BPushLam (length lib + length (flatten_code' (length lib) cd' r')) d # acc)
      (length ?code' + code_list_size cd) = cd" by blast
  hence "unflatten_code ?code (length lib + code_list_size cd' + code_list_size cd) = cd" by simp
  hence X: "unflatten_code ?code (length lib + (code_list_size cd' + code_list_size cd)) = cd" 
    by (metis add.assoc)
  have P: "?pc \<le> length ?code'" by simp
  moreover from 5 have "unflatten_code ?code' (length lib + code_list_size cd') = cd'" by blast
  ultimately have Z: "unflatten_code ?code ?pc =  cd'" by (metis unflatten_front)
  from P have "unflatten_return ?code ?pc = unflatten_return ?code' ?pc" 
    by (metis unflatten_r_front)
  with X Z show ?case by simp
qed simp_all

lemma [simp]: "unflatten_return (flatten_code (cd, r)) (code_list_size cd) = r"
proof -
  have "unflatten_return ([] @ flatten_code' (length []) cd r @ []) (length [] + code_list_size cd) = 
    r" by (metis unflatten_flatten_r list.size(3))
  thus ?thesis by simp
qed

lemma [simp]: "unflatten_code (flatten_code (cd, r)) (code_list_size cd) = cd"
proof -
  have "unflatten_code ([] @ flatten_code' (length []) cd r @ []) 
    (length [] + code_list_size cd) = cd" by (metis unflatten_flatten list.size(3))
  thus ?thesis by simp
qed

lemma orderly_lam [simp]: "pc < length cd \<Longrightarrow> cd ! pc = BPushLam pc' d \<Longrightarrow> orderly cd n \<Longrightarrow> 
    pc' \<le> pc + n"
  by (induction cd pc arbitrary: n rule: lookup.induct) fastforce+

lemma [simp]: "pc < length cd \<Longrightarrow> cd ! pc = BPushLam pc' d \<Longrightarrow> orderly cd 0 \<Longrightarrow> pc' \<le> pc"
  using orderly_lam by fastforce

theorem correctb [simp]: "\<Sigma>\<^sub>b \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state \<Sigma>\<^sub>b \<Longrightarrow> 
  iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (unflatten_state \<Sigma>\<^sub>b) (unflatten_state \<Sigma>\<^sub>b')"
proof (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: evalb.induct)
  case (evb_lookup cd pc x env v vs sfs)
  hence "TCOS (ufcs cd vs) 
    ((ufcs cd env, unflatten_code cd (Suc pc), unflatten_return cd (Suc pc)) # ufsfs cd sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      TCOS (unflatten_closure cd v # ufcs cd vs)
        ((ufcs cd env, unflatten_code cd pc, unflatten_return cd pc) # ufsfs cd sfs)" by simp
  thus ?case by simp
next
  case (evb_pushcon cd pc k vs env sfs)
  hence "TCOS (ufcs cd vs) 
    ((ufcs cd env, unflatten_code cd (Suc pc), unflatten_return cd (Suc pc)) # ufsfs cd sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
      TCOS (TCOConst k # ufcs cd vs) 
        ((ufcs cd env, unflatten_code cd pc, unflatten_return cd pc) # ufsfs cd sfs)" by simp
  thus ?case by simp
next
  case (evb_pushlam cd pc pc' env vs sfs)
  moreover hence X: "pc' \<le> pc" by auto
  moreover have "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (ufcs cd vs) ((ufcs cd env, 
    TCOPushLam (unflatten_code cd pc') (unflatten_return cd pc') (length env) # 
      unflatten_code cd pc, unflatten_return cd pc) # ufsfs cd sfs))
        (TCOS (TCOLam (ufcs cd env) (unflatten_code cd pc') (unflatten_return cd pc') # ufcs cd vs) 
          ((ufcs cd env, unflatten_code cd pc, unflatten_return cd pc) # ufsfs cd sfs))" 
    by (metis evtco_pushlam iter_one length_map)
  ultimately show ?case by simp
next
  case (evb_apply cd pc v env' pc' vs env sfs)
  hence "TCOS (unflatten_closure cd v # TCOLam (ufcs cd env') (unflatten_code cd pc') 
    (unflatten_return cd pc') # ufcs cd vs) 
      ((ufcs cd env, unflatten_code cd (Suc pc), unflatten_return cd (Suc pc)) # ufsfs cd sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        TCOS (ufcs cd vs) ((unflatten_closure cd v # ufcs cd env', unflatten_code cd pc', 
          unflatten_return cd pc') # (ufcs cd env, unflatten_code cd pc, unflatten_return cd pc) # 
            ufsfs cd sfs)" by simp
  thus ?case by simp
next
  case (evb_return cd pc env vs sfs)
  moreover have "TCOS (ufcs cd vs) ((ufcs cd env, [], TCOReturn (length env)) # ufsfs cd sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
    TCOS (ufcs cd vs) (ufsfs cd sfs)" by (metis evtco_return length_map)
  ultimately show ?case by simp
next
  case (evb_jump cd pc env v env' pc' vs sfs)
  have "TCOS (unflatten_closure cd v # TCOLam (ufcs cd env') (unflatten_code cd pc') 
    (unflatten_return cd pc') # ufcs cd vs) ((ufcs cd env, [], 
      TCOJump (length env)) # ufsfs cd sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o TCOS (ufcs cd vs)
        ((unflatten_closure cd v # ufcs cd env', unflatten_code cd pc', unflatten_return cd pc') # 
          ufsfs cd sfs)" by (metis evtco_jump length_map)
  with evb_jump have "TCOS (unflatten_closure cd v # 
    TCOLam (ufcs cd env') (unflatten_code cd pc') (unflatten_return cd pc') # ufcs cd vs)
      ((ufcs cd env, unflatten_code cd (Suc pc), unflatten_return cd (Suc pc)) # ufsfs cd sfs) \<leadsto>\<^sub>t\<^sub>c\<^sub>o
        TCOS (ufcs cd vs) ((unflatten_closure cd v # ufcs cd env', unflatten_code cd pc', 
          unflatten_return cd pc') # ufsfs cd sfs)" by simp
  hence "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS (unflatten_closure cd v # 
    TCOLam (ufcs cd env') (unflatten_code cd pc') (unflatten_return cd pc') # ufcs cd vs)
      ((ufcs cd env, unflatten_code cd (Suc pc), unflatten_return cd (Suc pc)) # ufsfs cd sfs))
        (TCOS (ufcs cd vs) ((unflatten_closure cd v # ufcs cd env', unflatten_code cd pc', 
          unflatten_return cd pc') # ufsfs cd sfs))" by (metis iter_one)
  thus ?case by simp
qed

lemma [simp]: "TCOLam envt cdt rt = unflatten_closure cdb vb \<Longrightarrow> 
  \<exists>envb pc. vb = BLam envb pc \<and> envt = ufcs cdb envb \<and> cdt = unflatten_code cdb pc \<and>
    rt = unflatten_return cdb pc"
  by (induction vb) simp_all

lemma unfl_state [dest]: "TCOS vs sfs = unflatten_state \<Sigma>\<^sub>b \<Longrightarrow> \<exists>vsb sfsb cdb. 
    \<Sigma>\<^sub>b = BS vsb sfsb cdb \<and> vs = ufcs cdb vsb \<and> sfs = ufsfs cdb sfsb"
  by (induction \<Sigma>\<^sub>b) simp_all

lemma [dest]: "TCOLookup x # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
    pc < length cdb \<Longrightarrow> cdb ! pc = BLookup x \<and> cdt = unflatten_code cdb pc"
  by (cases "cdb ! pc") simp_all

lemma [dest]: "TCOPushCon k # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
    pc < length cdb \<Longrightarrow> cdb ! pc = BPushCon k \<and> cdt = unflatten_code cdb pc"
  by (cases "cdb ! pc") simp_all

lemma [dest]: "TCOPushLam cdt'' r d # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> pc < length cdb \<Longrightarrow> 
    \<exists>pc'. cdb ! pc = BPushLam pc' d \<and> cdt = unflatten_code cdb pc \<and> 
      cdt'' = unflatten_code cdb pc' \<and> r = unflatten_return cdb pc'"
  by (cases "cdb ! pc") simp_all

lemma [dest]: "TCOApply # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
    pc < length cdb \<Longrightarrow> cdb ! pc = BApply \<and> cdt = unflatten_code cdb pc"
  by (cases "cdb ! pc") simp_all

lemma [dest]: "[] = unflatten_code cdb (Suc pc) \<Longrightarrow> TCOReturn d = unflatten_return cdb (Suc pc) \<Longrightarrow> 
    orderly cdb 0 \<Longrightarrow> pc < length cdb \<Longrightarrow> cdb ! pc = BReturn d"
  by (cases "cdb ! pc") simp_all

lemma [dest]: "[] = unflatten_code cdb (Suc pc) \<Longrightarrow> TCOJump d = unflatten_return cdb (Suc pc) \<Longrightarrow> 
    orderly cdb 0 \<Longrightarrow> pc < length cdb \<Longrightarrow> cdb ! pc = BJump d"
  by (cases "cdb ! pc") simp_all

lemma uf_to_lookup [dest]: "(envt, TCOLookup x # cdt, r) # sfst = ufsfs cdb sfsb \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. 
    sfsb = (envb, Suc pc) # sfsb' \<and> envt = ufcs cdb envb \<and> cdb ! pc = BLookup x \<and> 
      cdt = unflatten_code cdb pc \<and> r = unflatten_return cdb pc \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "TCOLookup x # cdt = unflatten_code cdb (Suc pc) \<and> orderly cdb 0 \<and> pc < length cdb" by simp
  hence "cdb ! pc = BLookup x \<and> cdt = unflatten_code cdb pc" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_pushcon [dest]: "(envt, TCOPushCon k # cdt, r) # sfst = ufsfs cdb sfsb \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> orderly_stack sfsb (length cdb) \<Longrightarrow> 
    \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> envt = ufcs cdb envb \<and> cdb ! pc = BPushCon k \<and> 
      cdt = unflatten_code cdb pc \<and> r = unflatten_return cdb pc \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "TCOPushCon k # cdt = unflatten_code cdb (Suc pc) \<and> orderly cdb 0 \<and> pc < length cdb" by simp
  hence "cdb ! pc = BPushCon k \<and> cdt = unflatten_code cdb pc" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_pushlam [dest]: "(envt, TCOPushLam cdt' r' d # cdt, r) # sfst = ufsfs cdb sfsb \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb' pc'. 
    sfsb = (envb, Suc pc) # sfsb' \<and> envt = ufcs cdb envb \<and> cdb ! pc = BPushLam pc' d \<and> 
      cdt = unflatten_code cdb pc \<and> r = unflatten_return cdb pc \<and> cdt' = unflatten_code cdb pc' \<and> 
        r' = unflatten_return cdb pc' \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "TCOPushLam cdt' r' d # cdt = unflatten_code cdb (Suc pc) \<and> orderly cdb 0 \<and> pc < length cdb" 
    by simp
  then obtain pc' where "cdb ! pc = BPushLam pc' d \<and> cdt = unflatten_code cdb pc \<and> 
    cdt' = unflatten_code cdb pc' \<and> r' = unflatten_return cdb pc'" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_apply [dest]: "(envt, TCOApply # cdt, r) # sfst = ufsfs cdb sfsb \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> 
    envt = ufcs cdb envb \<and> cdb ! pc = BApply \<and> cdt = unflatten_code cdb pc \<and> 
      r = unflatten_return cdb pc \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "TCOApply # cdt = unflatten_code cdb (Suc pc) \<and> orderly cdb 0 \<and> pc < length cdb" by simp
  hence "cdb ! pc = BApply \<and> cdt = unflatten_code cdb pc" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_return [dest]: "(envt, [], TCOReturn d) # sfst = ufsfs cdb sfsb \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> 
    envt = ufcs cdb envb \<and> cdb ! pc = BReturn d \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "[] = unflatten_code cdb (Suc pc) \<and> TCOReturn d = unflatten_return cdb (Suc pc) \<and> 
    orderly cdb 0 \<and> pc < length cdb" by simp
  hence "cdb ! pc = BReturn d" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_jump [dest]: "(envt, [], TCOJump d) # sfst = ufsfs cdb sfsb \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> 
    envt = ufcs cdb envb \<and> cdb ! pc = BJump d \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "[] = unflatten_code cdb (Suc pc) \<and> TCOJump d = unflatten_return cdb (Suc pc) \<and> 
    orderly cdb 0 \<and> pc < length cdb" by simp
  hence "cdb ! pc = BJump d" by blast
  with 3 show ?case by simp
qed simp_all

theorem completeb [simp]: "unflatten_state \<Sigma>\<^sub>b \<leadsto>\<^sub>t\<^sub>c\<^sub>o \<Sigma>\<^sub>t' \<Longrightarrow> orderly_state \<Sigma>\<^sub>b \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>b'. iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state \<Sigma>\<^sub>b' = \<Sigma>\<^sub>t'"
proof (induction "unflatten_state \<Sigma>\<^sub>b" \<Sigma>\<^sub>t' rule: evaltco.induct)
  case (evtco_lookup env x v vs cd r sfs)
  then obtain vsb sfsb cdb where B: "\<Sigma>\<^sub>b = BS vsb sfsb cdb \<and> vs = ufcs cdb vsb \<and> 
    (env, TCOLookup x # cd, r) # sfs = ufsfs cdb sfsb" by fastforce
  with evtco_lookup have "orderly cdb 0 \<and> orderly_stack sfsb (length cdb)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cdb envb \<and> cdb ! pc = BLookup x \<and> cd = unflatten_code cdb pc \<and> 
      r = unflatten_return cdb pc \<and> sfs = ufsfs cdb sfsb'" by (metis uf_to_lookup)
  with evtco_lookup obtain v' where V: "lookup envb x = Some v' \<and> unflatten_closure cdb v' = v"
    by fastforce
  with S have "BS vsb ((envb, Suc pc) # sfsb') cdb \<leadsto>\<^sub>b BS (v' # vsb) ((envb, pc) # sfsb') cdb"
    by simp
  hence "iter (\<leadsto>\<^sub>b) (BS vsb ((envb, Suc pc) # sfsb') cdb) (BS (v' # vsb) ((envb, pc) # sfsb') cdb)" 
    by simp
  with B S V show ?case by fastforce
next
  case (evtco_pushcon vs env k cd r sfs)
  then obtain vsb sfsb cdb where B: "\<Sigma>\<^sub>b = BS vsb sfsb cdb \<and> vs = ufcs cdb vsb \<and> 
    (env, TCOPushCon k # cd, r) # sfs = ufsfs cdb sfsb" by fastforce
  with evtco_pushcon have "orderly cdb 0 \<and> orderly_stack sfsb (length cdb)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cdb envb \<and> cdb ! pc = BPushCon k \<and> cd = unflatten_code cdb pc \<and> 
      r = unflatten_return cdb pc \<and> sfs = ufsfs cdb sfsb'" by (metis uf_to_pushcon)
  with S have "BS vsb ((envb, Suc pc) # sfsb') cdb \<leadsto>\<^sub>b BS (BConst k # vsb) ((envb, pc) # sfsb') cdb"
    by simp
  hence "iter (\<leadsto>\<^sub>b) (BS vsb ((envb, Suc pc) # sfsb') cdb) 
    (BS (BConst k # vsb) ((envb, pc) # sfsb') cdb)" by simp
  with B S show ?case by fastforce
next
  case (evtco_pushlam vs env cd' r' cd r sfs)
  then obtain vsb sfsb cdb where B: "\<Sigma>\<^sub>b = BS vsb sfsb cdb \<and> vs = ufcs cdb vsb \<and> 
    (env, TCOPushLam cd' r' (length env) # cd, r) # sfs = ufsfs cdb sfsb" by fastforce
  with evtco_pushlam have "orderly cdb 0 \<and> orderly_stack sfsb (length cdb)" by simp
  with B obtain envb pc sfsb' pc' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cdb envb \<and> cdb ! pc = BPushLam pc' (length env) \<and> cd = unflatten_code cdb pc \<and> 
      r = unflatten_return cdb pc \<and> sfs = ufsfs cdb sfsb' \<and> cd' = unflatten_code cdb pc' \<and> 
        r' = unflatten_return cdb pc'" by (metis uf_to_pushlam)
  with S have "BS vsb ((envb, Suc pc) # sfsb') cdb \<leadsto>\<^sub>b 
    BS (BLam envb pc' # vsb) ((envb, pc) # sfsb') cdb" by simp
  hence "iter (\<leadsto>\<^sub>b) (BS vsb ((envb, Suc pc) # sfsb') cdb) 
    (BS (BLam envb pc' # vsb) ((envb, pc) # sfsb') cdb)" by simp
  with B S show ?case by fastforce
next
  case (evtco_apply v env' cd' r' vs env cd r sfs)
  then obtain vsb sfsb cdb where B: "\<Sigma>\<^sub>b = BS vsb sfsb cdb \<and> 
    v # TCOLam env' cd' r' # vs = ufcs cdb vsb \<and> (env, TCOApply # cd, r) # sfs = ufsfs cdb sfsb" 
      by fastforce
  with evtco_apply have "orderly cdb 0 \<and> orderly_stack sfsb (length cdb)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cdb envb \<and> cdb ! pc = BApply \<and> cd = unflatten_code cdb pc \<and> 
      r = unflatten_return cdb pc \<and> sfs = ufsfs cdb sfsb'" by (metis uf_to_apply)
  from B obtain vb envb' pc' vsb' where V: "vsb = vb # BLam envb' pc' # vsb' \<and> 
    v = unflatten_closure cdb vb \<and> env' = ufcs cdb envb' \<and> cd' = unflatten_code cdb pc' \<and>
      r' = unflatten_return cdb pc' \<and> vs = ufcs cdb vsb'" by fastforce
  from S have "BS (vb # BLam envb' pc' # vsb') ((envb, Suc pc) # sfsb') cdb \<leadsto>\<^sub>b
    BS vsb' ((vb # envb', pc') # (envb, pc) # sfsb') cdb" by simp
  hence "iter (\<leadsto>\<^sub>b) (BS (vb # BLam envb' pc' # vsb') ((envb, Suc pc) # sfsb') cdb) 
    (BS vsb' ((vb # envb', pc') # (envb, pc) # sfsb') cdb)" by simp
  with B S V show ?case by auto                                              
next
  case (evtco_return vs env sfs)
  then obtain vsb sfsb cdb where B: "\<Sigma>\<^sub>b = BS vsb sfsb cdb \<and> vs = ufcs cdb vsb \<and> 
    (env, [], TCOReturn (length env)) # sfs = ufsfs cdb sfsb" by fastforce
  with evtco_return have "orderly cdb 0 \<and> orderly_stack sfsb (length cdb)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cdb envb \<and> cdb ! pc = BReturn (length env) \<and> sfs = ufsfs cdb sfsb'" 
      by (metis uf_to_return)
  with S have "BS vsb ((envb, Suc pc) # sfsb') cdb \<leadsto>\<^sub>b BS vsb sfsb' cdb" by simp
  hence "iter (\<leadsto>\<^sub>b) (BS vsb ((envb, Suc pc) # sfsb') cdb) (BS vsb sfsb' cdb)" by simp
  with B S show ?case by fastforce
next
  case (evtco_jump v env' cd' r' vs env sfs)
  then obtain vsb sfsb cdb where B: "\<Sigma>\<^sub>b = BS vsb sfsb cdb \<and> 
    v # TCOLam env' cd' r' # vs = ufcs cdb vsb \<and> 
      (env, [], TCOJump (length env)) # sfs = ufsfs cdb sfsb" by fastforce
  with evtco_jump have "orderly cdb 0 \<and> orderly_stack sfsb (length cdb)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cdb envb \<and> cdb ! pc = BJump (length env) \<and> sfs = ufsfs cdb sfsb'" 
      by (metis uf_to_jump)
  from B obtain vb envb' pc' vsb' where V: "vsb = vb # BLam envb' pc' # vsb' \<and> 
    v = unflatten_closure cdb vb \<and> env' = ufcs cdb envb' \<and> cd' = unflatten_code cdb pc' \<and>
      r' = unflatten_return cdb pc' \<and> vs = ufcs cdb vsb'" by fastforce
  from S have "BS (vb # BLam envb' pc' # vsb') ((envb, Suc pc) # sfsb') cdb \<leadsto>\<^sub>b
    BS vsb' ((vb # envb', pc') # sfsb') cdb" by simp
  hence "iter (\<leadsto>\<^sub>b) (BS (vb # BLam envb' pc' # vsb') ((envb, Suc pc) # sfsb') cdb) 
    (BS vsb' ((vb # envb', pc') # sfsb') cdb)" by simp
  with B S V show ?case by auto                                              
qed

lemma [simp]: "\<Sigma>\<^sub>b \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state \<Sigma>\<^sub>b \<Longrightarrow> orderly_state \<Sigma>\<^sub>b'"
proof (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: evalb.induct)
  case (evb_lookup cd pc x env v vs sfs)
  thus ?case by (cases pc, cases cd) simp_all
next
  case (evb_pushcon cd pc k vs env sfs)
  thus ?case by (cases pc, cases cd) simp_all
next
  case (evb_pushlam cd pc pc' vs env sfs)
  thus ?case 
  proof (cases pc)
    case 0
    with evb_pushlam show ?thesis by (cases cd) simp_all
  qed simp_all
next
  case (evb_apply cd pc v env' pc' vs env sfs)
  thus ?case by (cases pc', simp, cases pc, cases cd) simp_all
next
  case (evb_jump cd pc env v env' pc' vs sfs)
  thus ?case by (cases pc') simp_all
qed simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state \<Sigma>\<^sub>b \<Longrightarrow> orderly_state \<Sigma>\<^sub>b'"
  by (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: iter.induct) simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (unflatten_state \<Sigma>\<^sub>b) \<Sigma>\<^sub>t' \<Longrightarrow> orderly_state \<Sigma>\<^sub>b \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>b'. iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state \<Sigma>\<^sub>b' = \<Sigma>\<^sub>t'"
proof (induction "unflatten_state \<Sigma>\<^sub>b" \<Sigma>\<^sub>t' arbitrary: \<Sigma>\<^sub>b rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>t' \<Sigma>\<^sub>t'')
  moreover then obtain \<Sigma>\<^sub>b' where S: "iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state \<Sigma>\<^sub>b' = \<Sigma>\<^sub>t'" by fastforce
  moreover with iter_step have "orderly_state \<Sigma>\<^sub>b'" by fastforce
  ultimately obtain \<Sigma>\<^sub>b'' where "iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b' \<Sigma>\<^sub>b'' \<and> unflatten_state \<Sigma>\<^sub>b'' = \<Sigma>\<^sub>t''" by fastforce
  with S show ?case by (metis iter_append)
qed force+

lemma unfl_terminal [simp]: "unflatten_state \<Sigma> = TCOS [c] [] \<Longrightarrow>
  \<exists>v cd. \<Sigma> = BS [v] [] cd \<and> c = unflatten_closure cd v"
proof -
  assume "unflatten_state \<Sigma> = TCOS [c] []"
  then obtain vs sfs cd where S: "\<Sigma> = BS vs sfs cd \<and> [c] = ufcs cd vs \<and> [] = ufsfs cd sfs" 
    by (metis unfl_state)
  moreover then obtain v where "vs = [v] \<and> c = unflatten_closure cd v" by blast
  ultimately show ?thesis by simp
qed

lemma evalb_end [simp]: "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (unflatten_state \<Sigma>\<^sub>b) (TCOS [c] []) \<Longrightarrow> orderly_state \<Sigma>\<^sub>b \<Longrightarrow>
  \<exists>v. iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b (BS [v] [] (code \<Sigma>\<^sub>b)) \<and> c = unflatten_closure (code \<Sigma>\<^sub>b) v"
proof -
  assume "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (unflatten_state \<Sigma>\<^sub>b) (TCOS [c] [])"
  moreover assume O: "orderly_state \<Sigma>\<^sub>b"
  ultimately obtain \<Sigma>\<^sub>b' where E: "iter (\<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state \<Sigma>\<^sub>b' = TCOS [c] []" 
    by fastforce
  moreover with O have "orderly_state \<Sigma>\<^sub>b'" by fastforce
  moreover with E obtain v cd where "\<Sigma>\<^sub>b' = BS [v] [] cd \<and> c = unflatten_closure cd v" 
    by (metis unfl_terminal)
  moreover with E have "code \<Sigma>\<^sub>b = cd" by fastforce
  ultimately show ?thesis by blast
qed

end