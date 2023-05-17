theory CodeFlattening
  imports ByteCode "../07TailCall/TailCall"
begin

primrec flatten_return :: "tco_return \<Rightarrow> byte_code" where
  "flatten_return TCOReturn = BReturn"
| "flatten_return TCOJump = BJump"

fun flatten_code' :: "nat \<Rightarrow> tco_code list \<Rightarrow> tco_return \<Rightarrow> byte_code list" where
  "flatten_code' lib [] r = [flatten_return r]"
| "flatten_code' lib (TCOLookup x # cd) r = flatten_code' lib cd r @ [BLookup x]"
| "flatten_code' lib (TCOPushCon k # cd) r = flatten_code' lib cd r @ [BPushCon k]"
| "flatten_code' lib (TCOPushLam cd' r' # cd) r = (
    let clo = flatten_code' lib cd' r'
    in clo @ flatten_code' (lib + length clo) cd r @ [BPushLam (lib + length clo)])"
| "flatten_code' lib (TCOApply # cd) r = flatten_code' lib cd r @ [BApply]"

primrec flatten_code :: "tco_code list \<times> tco_return \<Rightarrow> byte_code list" where
  "flatten_code (cd, r) = flatten_code' 0 cd r"

primrec unflatten_return :: "byte_code list \<Rightarrow> nat \<Rightarrow> tco_return" where
  "unflatten_return cd 0 = undefined"
| "unflatten_return cd (Suc pc) = (case lookup cd pc of
      Some BReturn \<Rightarrow> TCOReturn
    | Some BJump \<Rightarrow> TCOJump
    | Some op \<Rightarrow> unflatten_return cd pc
    | None \<Rightarrow> undefined)"

fun unflatten_code :: "byte_code list \<Rightarrow> nat \<Rightarrow> tco_code list" where
  "unflatten_code cd 0 = []"
| "unflatten_code cd (Suc pc) = (case lookup cd pc of
      Some (BLookup x) \<Rightarrow> TCOLookup x # unflatten_code cd pc
    | Some (BPushCon k) \<Rightarrow>  TCOPushCon k # unflatten_code cd pc
    | Some (BPushLam pc') \<Rightarrow> (
        if pc' \<le> pc 
        then TCOPushLam (unflatten_code cd pc') (unflatten_return cd pc') # unflatten_code cd pc 
        else undefined) 
    | Some BApply \<Rightarrow> TCOApply # unflatten_code cd pc
    | Some BReturn \<Rightarrow> []
    | Some BJump \<Rightarrow> []
    | None \<Rightarrow> undefined)"

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

primrec unflatten_state :: "byte_code list \<Rightarrow> byte_code_state \<Rightarrow> tco_code_state" where
  "unflatten_state cd (BS vs sfs) = TCOS (ufcs cd vs) (ufsfs cd sfs)"

primrec code_size :: "tco_code \<Rightarrow> nat"
    and code_list_size :: "tco_code list \<Rightarrow> nat" where
  "code_size (TCOLookup x) = 1"
| "code_size (TCOPushCon k) = 1"
| "code_size (TCOPushLam cd r) = Suc (code_list_size cd)"
| "code_size TCOApply = 1"
| "code_list_size [] = 1"
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

primrec return_terminated :: "byte_code list \<Rightarrow> bool" where
  "return_terminated [] = False"
| "return_terminated (op # cd) = (op = BReturn \<or> op = BJump)"

fun orderly_stack :: "(bclosure list \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "orderly_stack [] cd = True"
| "orderly_stack ((env, 0) # sfs) cd = False"
| "orderly_stack ((env, Suc pc) # sfs) cd = 
    (pc < cd \<and> ordered_closures env cd \<and> orderly_stack sfs cd)"

primrec orderly_state :: "byte_code list \<Rightarrow> byte_code_state \<Rightarrow> bool" where
  "orderly_state cd (BS vs sfs) = (orderly cd 0 \<and> return_terminated cd \<and> 
    orderly_stack sfs (length cd) \<and> ordered_closures vs (length cd))"

lemma flatten_length [simp]: "length (flatten_code' lib cd r) = code_list_size cd"
  by (induction lib cd r rule: flatten_code'.induct) simp_all

lemma [simp]: "length (flatten_code (cd, r)) = code_list_size cd"
  by (simp add: flatten_code_def)

lemma [simp]: "Suc 0 \<le> code_list_size cd"
  by (induction cd) simp_all

lemma [simp]: "0 < code_list_size cd"
  by (induction cd) simp_all

lemma [simp]: "code_list_size cd \<noteq> 0"
  by (induction cd) simp_all

lemma [simp]: "flatten_code' lib cd r \<noteq> []"
  by (induction lib cd r rule: flatten_code'.induct) simp_all

lemma [simp]: "flatten_code cdr \<noteq> []"
  by (cases cdr) (simp add: flatten_code_def)

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> return_terminated (cd @ cd') = return_terminated cd"
  by (induction cd) simp_all

lemma [simp]: "flatten_return r = BReturn \<or> flatten_return r = BJump"
  by (induction r) simp_all

lemma [simp]: "return_terminated (flatten_code' lib cd r)"
  by (induction lib cd r rule: flatten_code'.induct) simp_all

lemma [simp]: "return_terminated (flatten_code cdr)"
  by (cases cdr) (simp add: flatten_code_def)

lemma [simp]: "ordered op x \<Longrightarrow> ordered op (Suc x)"
  by (induction op) simp_all

lemma [simp]: "ordered op (x + n) \<Longrightarrow> ordered op (x + (m + n))"
  by (induction op) simp_all

lemma [simp]: "orderly (cd @ cd') n = (orderly cd n \<and> orderly cd' (length cd + n))"
  by (induction cd arbitrary: n) simp_all

lemma [simp]: "ordered (flatten_return r) n"
  by (induction r) simp_all

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

lemma pushlam_ordered [simp]: "lookup cd x = Some (BPushLam pc) \<Longrightarrow> orderly cd n \<Longrightarrow> 
    x < length cd \<Longrightarrow> 0 < pc \<and> pc \<le> length cd + n"
  by (induction cd x arbitrary: n rule: lookup.induct) fastforce+

lemma [simp]: "lookup cd x = Some (BPushLam pc) \<Longrightarrow> orderly cd 0 \<Longrightarrow> x < length cd \<Longrightarrow> 
    0 < pc \<and> pc \<le> length cd"
  using pushlam_ordered by fastforce

lemma index_into_append [simp]: "lookup (flatten_code' lib cd r @ cd') (code_list_size cd + n) = 
    lookup cd' n"
  by (metis flatten_length lookup_append_snd)

lemma [simp]: "lookup (flatten_code' lib cd r @ op # acc) (code_list_size cd) = Some op"
proof -
  have "lookup (flatten_code' lib cd r @ op # acc) (code_list_size cd + 0) = lookup (op # acc) 0" 
    by (metis index_into_append)
  thus ?thesis by simp
qed

lemma unflatten_r_front [simp]: "pc \<le> length cd \<Longrightarrow> 
    unflatten_return (cd @ cd') pc = unflatten_return cd pc"
  by (induction pc) (simp_all split: option.splits byte_code.splits) 

lemma unflatten_front [simp]: "pc \<le> length cd \<Longrightarrow> 
    unflatten_code (cd @ cd') pc = unflatten_code cd pc"
  by (induction cd pc rule: unflatten_code.induct) (simp_all split: option.splits byte_code.splits) 

lemma unflatten_flatten_r [simp]: "unflatten_return (lib @ flatten_code' (length lib) cd r @ acc) 
  (length lib + code_list_size cd) = r"
proof (induction "length lib" cd r arbitrary: lib acc rule: flatten_code'.induct)
  case (1 r)
  thus ?case by (cases r) simp_all
next
  case (4 cd' r' cd r)
  let ?pc = "length lib + code_list_size cd'"
  let ?code' = "lib @ flatten_code' (length lib) cd' r'"
  let ?code = "?code' @ flatten_code' ?pc cd r @ BPushLam ?pc # acc"
  have "length lib + length (flatten_code' (length lib) cd' r') = length ?code'" by simp
  with 4 have "unflatten_return (?code' @ flatten_code' (length ?code') cd r @
    BPushLam (length lib + length (flatten_code' (length lib) cd' r')) # acc)
     (length ?code' + code_list_size cd) = r" by blast
  hence "unflatten_return ?code (length lib + code_list_size cd' + code_list_size cd) = r" by simp
  hence "unflatten_return ?code (length lib + (code_list_size cd' + code_list_size cd)) = r" 
    by (metis add.assoc)
  thus ?case by simp
qed simp_all

lemma unflatten_flatten [simp]: "unflatten_code (lib @ flatten_code' (length lib) cd r @ acc) 
  (length lib + code_list_size cd) = cd"
proof (induction "length lib" cd r arbitrary: lib acc rule: flatten_code'.induct)
  case (1 r)
  thus ?case by (cases r) simp_all
next
  case (4 cd' r' cd r)
  let ?pc = "length lib + code_list_size cd'"
  let ?code' = "lib @ flatten_code' (length lib) cd' r' @ []"
  let ?code = "?code' @ flatten_code' ?pc cd r @ BPushLam ?pc # acc"
  have "length lib + length (flatten_code' (length lib) cd' r') = length ?code'" by simp
  with 4 have "unflatten_code (?code' @ flatten_code' (length ?code') cd r @
    BPushLam (length lib + length (flatten_code' (length lib) cd' r')) # acc)
      (length ?code' + code_list_size cd) = cd" by blast
  hence "unflatten_code ?code (length lib + code_list_size cd' + code_list_size cd) = cd" by simp
  hence X: "unflatten_code ?code (length lib + (code_list_size cd' + code_list_size cd)) = cd" 
    by (metis add.assoc)
  have P: "?pc \<le> length ?code'" by simp
  moreover from 4 have "unflatten_code ?code' (length lib + code_list_size cd') = cd'" by blast
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

lemma orderly_lam [simp]: "lookup cd pc = Some (BPushLam pc') \<Longrightarrow> orderly cd n \<Longrightarrow> pc' \<le> pc + n"
  by (induction cd pc arbitrary: n rule: lookup.induct) fastforce+

lemma [simp]: "lookup cd pc = Some (BPushLam pc') \<Longrightarrow> orderly cd 0 \<Longrightarrow> pc' \<le> pc"
  using orderly_lam by fastforce

theorem correctb [simp]: "cd \<tturnstile> \<Sigma>\<^sub>b \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state cd \<Sigma>\<^sub>b \<Longrightarrow> 
  iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (unflatten_state cd \<Sigma>\<^sub>b) (unflatten_state cd \<Sigma>\<^sub>b')"
proof (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: evalb.induct)
  case (evb_lookup cd pc x env v vs sfs)
  hence "TCOS (ufcs cd vs) 
    ((ufcs cd env, unflatten_code cd (Suc pc), unflatten_return cd (Suc pc)) # ufsfs cd sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
      TCOS (unflatten_closure cd v # ufcs cd vs)
        ((ufcs cd env, unflatten_code cd pc, unflatten_return cd pc) # ufsfs cd sfs)" by simp
  thus ?case by simp
next
  case (evb_pushcon cd pc k vs env sfs)
  hence "TCOS (ufcs cd vs) 
    ((ufcs cd env, unflatten_code cd (Suc pc), unflatten_return cd (Suc pc)) # ufsfs cd sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
      TCOS (TCOConst k # ufcs cd vs) 
        ((ufcs cd env, unflatten_code cd pc, unflatten_return cd pc) # ufsfs cd sfs)" by simp
  thus ?case by simp
next
  case (evb_pushlam cd pc pc' vs env sfs)
  moreover hence X: "pc' \<le> pc" by auto
  moreover have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (TCOS (ufcs cd vs) ((ufcs cd env, 
    TCOPushLam (unflatten_code cd pc') (unflatten_return cd pc') # 
      unflatten_code cd pc, unflatten_return cd pc) # ufsfs cd sfs))
        (TCOS (TCOLam (ufcs cd env) (unflatten_code cd pc') (unflatten_return cd pc') # ufcs cd vs) 
          ((ufcs cd env, unflatten_code cd pc, unflatten_return cd pc) # ufsfs cd sfs))" 
    by (metis evtco_pushlam iter_one)
  ultimately show ?case by simp
next
  case (evb_apply cd pc v env' pc' vs env sfs)
  hence "TCOS (unflatten_closure cd v # TCOLam (ufcs cd env') (unflatten_code cd pc') 
    (unflatten_return cd pc') # ufcs cd vs) 
      ((ufcs cd env, unflatten_code cd (Suc pc), unflatten_return cd (Suc pc)) # ufsfs cd sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
        TCOS (ufcs cd vs) ((unflatten_closure cd v # ufcs cd env', unflatten_code cd pc', 
          unflatten_return cd pc') # (ufcs cd env, unflatten_code cd pc, unflatten_return cd pc) # 
            ufsfs cd sfs)" by simp
  thus ?case by simp
next
  case (evb_return cd pc vs env sfs)
  moreover have "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (TCOS (ufcs cd vs) ((ufcs cd env, [], TCOReturn) # ufsfs cd sfs))
    (TCOS (ufcs cd vs) (ufsfs cd sfs))" by (metis evtco_return iter_one)
  ultimately show ?case by simp
next
  case (evb_jump cd pc v env' pc' vs env sfs)
  have "TCOS (unflatten_closure cd v # TCOLam (ufcs cd env') (unflatten_code cd pc') 
    (unflatten_return cd pc') # ufcs cd vs) ((ufcs cd env, [], 
      TCOJump) # ufsfs cd sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o TCOS (ufcs cd vs)
        ((unflatten_closure cd v # ufcs cd env', unflatten_code cd pc', unflatten_return cd pc') # 
          ufsfs cd sfs)" by (metis evtco_jump)
  with evb_jump have "TCOS (unflatten_closure cd v # 
    TCOLam (ufcs cd env') (unflatten_code cd pc') (unflatten_return cd pc') # ufcs cd vs)
      ((ufcs cd env, unflatten_code cd (Suc pc), unflatten_return cd (Suc pc)) # ufsfs cd sfs) \<leadsto>\<^sub>e\<^sub>c\<^sub>o
        TCOS (ufcs cd vs) ((unflatten_closure cd v # ufcs cd env', unflatten_code cd pc', 
          unflatten_return cd pc') # ufsfs cd sfs)" by simp
  hence "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (TCOS (unflatten_closure cd v # 
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

lemma unfl_state [dest]: "TCOS vs sfs = unflatten_state cd \<Sigma>\<^sub>b \<Longrightarrow> \<exists>vsb sfsb. 
    \<Sigma>\<^sub>b = BS vsb sfsb \<and> vs = ufcs cd vsb \<and> sfs = ufsfs cd sfsb"
  by (induction \<Sigma>\<^sub>b) simp_all

lemma [dest]: "TCOLookup x # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
    pc < length cdb \<Longrightarrow> lookup cdb pc = Some (BLookup x) \<and> cdt = unflatten_code cdb pc"
  by (simp split: option.splits byte_code.splits)

lemma [dest]: "TCOPushCon k # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
    pc < length cdb \<Longrightarrow> lookup cdb pc = Some (BPushCon k) \<and> cdt = unflatten_code cdb pc"
  by (simp split: option.splits byte_code.splits)

lemma [dest]: "TCOPushLam cdt'' r # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> pc < length cdb \<Longrightarrow>  
    \<exists>pc'. lookup cdb pc = Some (BPushLam pc') \<and> cdt = unflatten_code cdb pc \<and> 
      cdt'' = unflatten_code cdb pc' \<and> r = unflatten_return cdb pc'"
  by (simp split: option.splits byte_code.splits)

lemma [dest]: "TCOApply # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
    pc < length cdb \<Longrightarrow> lookup cdb pc = Some BApply \<and> cdt = unflatten_code cdb pc"
  by (simp split: option.splits byte_code.splits)

lemma [dest]: "[] = unflatten_code cdb (Suc pc) \<Longrightarrow> TCOReturn = unflatten_return cdb (Suc pc) \<Longrightarrow> 
    orderly cdb 0 \<Longrightarrow> pc < length cdb \<Longrightarrow> lookup cdb pc = Some BReturn"
  by (simp split: option.splits byte_code.splits)

lemma [dest]: "[] = unflatten_code cdb (Suc pc) \<Longrightarrow> TCOJump = unflatten_return cdb (Suc pc) \<Longrightarrow> 
    orderly cdb 0 \<Longrightarrow> pc < length cdb \<Longrightarrow> lookup cdb pc = Some BJump"
  by (simp split: option.splits byte_code.splits)

lemma uf_to_lookup [dest]: "(envt, TCOLookup x # cdt, r) # sfst = ufsfs cdb sfsb \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. 
    sfsb = (envb, Suc pc) # sfsb' \<and> envt = ufcs cdb envb \<and> lookup cdb pc = Some (BLookup x) \<and> 
      cdt = unflatten_code cdb pc \<and> r = unflatten_return cdb pc \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "TCOLookup x # cdt = unflatten_code cdb (Suc pc) \<and> orderly cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some (BLookup x) \<and> cdt = unflatten_code cdb pc" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_pushcon [dest]: "(envt, TCOPushCon k # cdt, r) # sfst = ufsfs cdb sfsb \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> orderly_stack sfsb (length cdb) \<Longrightarrow> 
    \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> envt = ufcs cdb envb \<and> 
      lookup cdb pc = Some (BPushCon k) \<and> cdt = unflatten_code cdb pc \<and> 
        r = unflatten_return cdb pc \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "TCOPushCon k # cdt = unflatten_code cdb (Suc pc) \<and> orderly cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some (BPushCon k) \<and> cdt = unflatten_code cdb pc" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_pushlam [dest]: "(envt, TCOPushLam cdt' r' # cdt, r) # sfst = ufsfs cdb sfsb \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb' pc'. 
    sfsb = (envb, Suc pc) # sfsb' \<and> envt = ufcs cdb envb \<and> lookup cdb pc = Some (BPushLam pc') \<and> 
      cdt = unflatten_code cdb pc \<and> r = unflatten_return cdb pc \<and> cdt' = unflatten_code cdb pc' \<and> 
        r' = unflatten_return cdb pc' \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "TCOPushLam cdt' r' # cdt = unflatten_code cdb (Suc pc) \<and> orderly cdb 0 \<and> pc < length cdb" 
    by simp
  then obtain pc' where "lookup cdb pc = Some (BPushLam pc') \<and> cdt = unflatten_code cdb pc \<and> 
    cdt' = unflatten_code cdb pc' \<and> r' = unflatten_return cdb pc'" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_apply [dest]: "(envt, TCOApply # cdt, r) # sfst = ufsfs cdb sfsb \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> 
    envt = ufcs cdb envb \<and> lookup cdb pc = Some BApply \<and> cdt = unflatten_code cdb pc \<and> 
      r = unflatten_return cdb pc \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "TCOApply # cdt = unflatten_code cdb (Suc pc) \<and> orderly cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some BApply \<and> cdt = unflatten_code cdb pc" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_return [dest]: "(envt, [], TCOReturn) # sfst = ufsfs cdb sfsb \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> 
    envt = ufcs cdb envb \<and> lookup cdb pc = Some BReturn \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "[] = unflatten_code cdb (Suc pc) \<and> TCOReturn = unflatten_return cdb (Suc pc) \<and> 
    orderly cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some BReturn" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_jump [dest]: "(envt, [], TCOJump) # sfst = ufsfs cdb sfsb \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> 
    envt = ufcs cdb envb \<and> lookup cdb pc = Some BJump \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "[] = unflatten_code cdb (Suc pc) \<and> TCOJump = unflatten_return cdb (Suc pc) \<and> 
    orderly cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some BJump" by blast
  with 3 show ?case by simp
qed simp_all

theorem completeb [simp]: "unflatten_state cd\<^sub>b \<Sigma>\<^sub>b \<leadsto>\<^sub>e\<^sub>c\<^sub>o \<Sigma>\<^sub>t' \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>b'. iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state cd\<^sub>b \<Sigma>\<^sub>b' = \<Sigma>\<^sub>t'"
proof (induction "unflatten_state cd\<^sub>b \<Sigma>\<^sub>b" \<Sigma>\<^sub>t' rule: evaltco.induct)
  case (evtco_lookup env x v vs cd r sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = BS vsb sfsb \<and> vs = ufcs cd\<^sub>b vsb \<and> 
    (env, TCOLookup x # cd, r) # sfs = ufsfs cd\<^sub>b sfsb" by fastforce
  with evtco_lookup have "orderly cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some (BLookup x) \<and> cd = unflatten_code cd\<^sub>b pc \<and> 
      r = unflatten_return cd\<^sub>b pc \<and> sfs = ufsfs cd\<^sub>b sfsb'" by (metis uf_to_lookup)
  with evtco_lookup obtain v' where V: "lookup envb x = Some v' \<and> unflatten_closure cd\<^sub>b v' = v"
    by fastforce
  with S have "cd\<^sub>b \<tturnstile> BS vsb ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b BS (v' # vsb) ((envb, pc) # sfsb')"
    by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (BS vsb ((envb, Suc pc) # sfsb')) (BS (v' # vsb) ((envb, pc) # sfsb'))" 
    by simp
  with B S V show ?case by fastforce
next
  case (evtco_pushcon vs env k cd r sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = BS vsb sfsb \<and> vs = ufcs cd\<^sub>b vsb \<and> 
    (env, TCOPushCon k # cd, r) # sfs = ufsfs cd\<^sub>b sfsb" by fastforce
  with evtco_pushcon have "orderly cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some (BPushCon k) \<and> cd = unflatten_code cd\<^sub>b pc \<and> 
      r = unflatten_return cd\<^sub>b pc \<and> sfs = ufsfs cd\<^sub>b sfsb'" by (metis uf_to_pushcon)
  with S have "cd\<^sub>b \<tturnstile> BS vsb ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b BS (BConst k # vsb) ((envb, pc) # sfsb')"
    by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (BS vsb ((envb, Suc pc) # sfsb')) 
    (BS (BConst k # vsb) ((envb, pc) # sfsb'))" by simp
  with B S show ?case by fastforce
next
  case (evtco_pushlam vs env cd' r' cd r sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = BS vsb sfsb \<and> vs = ufcs cd\<^sub>b vsb \<and> 
    (env, TCOPushLam cd' r' # cd, r) # sfs = ufsfs cd\<^sub>b sfsb" by fastforce
  with evtco_pushlam have "orderly cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' pc' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some (BPushLam pc') \<and> cd = unflatten_code cd\<^sub>b pc \<and> 
      r = unflatten_return cd\<^sub>b pc \<and> sfs = ufsfs cd\<^sub>b sfsb' \<and> cd' = unflatten_code cd\<^sub>b pc' \<and> 
        r' = unflatten_return cd\<^sub>b pc'" by (metis uf_to_pushlam)
  with S have "cd\<^sub>b \<tturnstile> BS vsb ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b 
    BS (BLam envb pc' # vsb) ((envb, pc) # sfsb')" by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (BS vsb ((envb, Suc pc) # sfsb')) 
    (BS (BLam envb pc' # vsb) ((envb, pc) # sfsb'))" by simp
  with B S show ?case by fastforce
next
  case (evtco_apply v env' cd' r' vs env cd r sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = BS vsb sfsb \<and> 
    v # TCOLam env' cd' r' # vs = ufcs cd\<^sub>b vsb \<and> (env, TCOApply # cd, r) # sfs = ufsfs cd\<^sub>b sfsb" 
      by fastforce
  with evtco_apply have "orderly cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some BApply \<and> cd = unflatten_code cd\<^sub>b pc \<and> 
      r = unflatten_return cd\<^sub>b pc \<and> sfs = ufsfs cd\<^sub>b sfsb'" by (metis uf_to_apply)
  from B obtain vb envb' pc' vsb' where V: "vsb = vb # BLam envb' pc' # vsb' \<and> 
    v = unflatten_closure cd\<^sub>b vb \<and> env' = ufcs cd\<^sub>b envb' \<and> cd' = unflatten_code cd\<^sub>b pc' \<and>
      r' = unflatten_return cd\<^sub>b pc' \<and> vs = ufcs cd\<^sub>b vsb'" by fastforce
  from S have "cd\<^sub>b \<tturnstile> BS (vb # BLam envb' pc' # vsb') ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b
    BS vsb' ((vb # envb', pc') # (envb, pc) # sfsb')" by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (BS (vb # BLam envb' pc' # vsb') ((envb, Suc pc) # sfsb')) 
    (BS vsb' ((vb # envb', pc') # (envb, pc) # sfsb'))" by simp
  with B S V show ?case by auto                                              
next
  case (evtco_return vs env sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = BS vsb sfsb \<and> vs = ufcs cd\<^sub>b vsb \<and> 
    (env, [], TCOReturn) # sfs = ufsfs cd\<^sub>b sfsb" by fastforce
  with evtco_return have "orderly cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some BReturn \<and> sfs = ufsfs cd\<^sub>b sfsb'" 
      by (metis uf_to_return)
  with S have "cd\<^sub>b \<tturnstile> BS vsb ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b BS vsb sfsb'" by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (BS vsb ((envb, Suc pc) # sfsb')) (BS vsb sfsb')" by simp
  with B S show ?case by fastforce
next
  case (evtco_jump v env' cd' r' vs env sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = BS vsb sfsb \<and> 
    v # TCOLam env' cd' r' # vs = ufcs cd\<^sub>b vsb \<and> 
      (env, [], TCOJump) # sfs = ufsfs cd\<^sub>b sfsb" by fastforce
  with evtco_jump have "orderly cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some BJump \<and> sfs = ufsfs cd\<^sub>b sfsb'" 
      by (metis uf_to_jump)
  from B obtain vb envb' pc' vsb' where V: "vsb = vb # BLam envb' pc' # vsb' \<and> 
    v = unflatten_closure cd\<^sub>b vb \<and> env' = ufcs cd\<^sub>b envb' \<and> cd' = unflatten_code cd\<^sub>b pc' \<and>
      r' = unflatten_return cd\<^sub>b pc' \<and> vs = ufcs cd\<^sub>b vsb'" by fastforce
  from S have "cd\<^sub>b \<tturnstile> BS (vb # BLam envb' pc' # vsb') ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b
    BS vsb' ((vb # envb', pc') # sfsb')" by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (BS (vb # BLam envb' pc' # vsb') ((envb, Suc pc) # sfsb')) 
    (BS vsb' ((vb # envb', pc') # sfsb'))" by simp
  with B S V show ?case by auto                                              
qed

lemma [simp]: "cd\<^sub>b \<tturnstile> \<Sigma>\<^sub>b \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b'"
proof (induction cd\<^sub>b \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: evalb.induct)
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
  case (evb_jump cd pc v env' pc' vs env sfs)
  thus ?case by (cases pc') simp_all
qed simp_all

lemma [simp]: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b'"
  by (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: iter.induct) simp_all

lemma [simp]: "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (unflatten_state cd\<^sub>b \<Sigma>\<^sub>b) \<Sigma>\<^sub>t' \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow>
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

lemma unfl_terminal [simp]: "unflatten_state cd \<Sigma> = TCOS [c] [] \<Longrightarrow>
  \<exists>v. \<Sigma> = BS [v] [] \<and> c = unflatten_closure cd v"
proof -
  assume "unflatten_state cd \<Sigma> = TCOS [c] []"
  then obtain vs sfs where S: "\<Sigma> = BS vs sfs \<and> [c] = ufcs cd vs \<and> [] = ufsfs cd sfs" 
    by (metis unfl_state)
  moreover then obtain v where "vs = [v] \<and> c = unflatten_closure cd v" by blast
  ultimately show ?thesis by simp
qed

lemma evalb_end [simp]: "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (unflatten_state cd\<^sub>b \<Sigma>\<^sub>b) (TCOS [c] []) \<Longrightarrow> 
  orderly_state cd\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow> 
    \<exists>v. iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b (BS [v] []) \<and> c = unflatten_closure cd\<^sub>b v"
proof -
  assume "iter (\<leadsto>\<^sub>e\<^sub>c\<^sub>o) (unflatten_state cd\<^sub>b \<Sigma>\<^sub>b) (TCOS [c] [])"
  moreover assume O: "orderly_state cd\<^sub>b \<Sigma>\<^sub>b"
  ultimately obtain \<Sigma>\<^sub>b' where E: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state cd\<^sub>b \<Sigma>\<^sub>b' = TCOS [c] []" 
    by fastforce
  moreover with O have "orderly_state cd\<^sub>b \<Sigma>\<^sub>b'" by fastforce
  moreover with E obtain v where "\<Sigma>\<^sub>b' = BS [v] [] \<and> c = unflatten_closure cd\<^sub>b v" 
    by (metis unfl_terminal)
  ultimately show ?thesis by blast
qed

end