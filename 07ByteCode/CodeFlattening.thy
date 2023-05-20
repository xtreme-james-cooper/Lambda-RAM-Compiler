theory CodeFlattening
  imports ByteCode "../06TreeCode/TreeCode"
begin

fun flatten_code' :: "nat \<Rightarrow> code\<^sub>e list \<Rightarrow> byte_code list" where
  "flatten_code' lib [] = []"
| "flatten_code' lib (Lookup\<^sub>e x # cd) = flatten_code' lib cd @ [BLookup x]"
| "flatten_code' lib (PushCon\<^sub>e k # cd) = flatten_code' lib cd @ [BPushCon k]"
| "flatten_code' lib (PushLam\<^sub>e cd' # cd) = (
    let clo = flatten_code' lib cd'
    in clo @ flatten_code' (lib + length clo) cd @ [BPushLam (lib + length clo)])"
| "flatten_code' lib (Apply\<^sub>e # cd) = flatten_code' lib cd @ [BApply]"
| "flatten_code' lib (Return\<^sub>e # cd) = flatten_code' lib cd @ [BReturn]"
| "flatten_code' lib (Jump\<^sub>e # cd) = flatten_code' lib cd @ [BJump]"

definition flatten_code :: "code\<^sub>e list \<Rightarrow> byte_code list" where
  "flatten_code cd \<equiv> flatten_code' 0 cd"

fun unflatten_code :: "byte_code list \<Rightarrow> nat \<Rightarrow> code\<^sub>e list" where
  "unflatten_code cd 0 = []"
| "unflatten_code cd (Suc pc) = (case lookup cd pc of
      Some (BLookup x) \<Rightarrow> Lookup\<^sub>e x # unflatten_code cd pc
    | Some (BPushCon k) \<Rightarrow>  PushCon\<^sub>e k # unflatten_code cd pc
    | Some (BPushLam pc') \<Rightarrow> (
        if pc' \<le> pc then PushLam\<^sub>e (unflatten_code cd pc') # unflatten_code cd pc else undefined) 
    | Some BApply \<Rightarrow> Apply\<^sub>e # unflatten_code cd pc
    | Some BReturn \<Rightarrow> [Return\<^sub>e]
    | Some BJump \<Rightarrow> [Jump\<^sub>e]
    | None \<Rightarrow> undefined)"

primrec unflatten_closure :: "byte_code list \<Rightarrow> bclosure \<Rightarrow> closure\<^sub>e" where
  "unflatten_closure cd (BConst k) = Const\<^sub>e k"
| "unflatten_closure cd (BLam vs pc) = Lam\<^sub>e (map (unflatten_closure cd) vs) (unflatten_code cd pc)"

abbreviation ufcs :: "byte_code list \<Rightarrow> bclosure list \<Rightarrow> closure\<^sub>e list" where
  "ufcs cd vs \<equiv> map (unflatten_closure cd) vs"

primrec ufsf :: "byte_code list \<Rightarrow> (bclosure list \<times> nat) \<Rightarrow> frame\<^sub>e" where
  "ufsf cd (vs, pc) = (ufcs cd vs, unflatten_code cd pc)"

abbreviation ufsfs :: "byte_code list \<Rightarrow> (bclosure list \<times> nat) list \<Rightarrow> frame\<^sub>e list" where
  "ufsfs cd pcs \<equiv> map (ufsf cd) pcs"

primrec unflatten_state :: "byte_code list \<Rightarrow> byte_code_state \<Rightarrow> state\<^sub>e" where
  "unflatten_state cd (BS vs sfs) = S\<^sub>e (ufcs cd vs) (ufsfs cd sfs)"

primrec code_size :: "code\<^sub>e \<Rightarrow> nat"
    and code_list_size :: "code\<^sub>e list \<Rightarrow> nat" where
  "code_size (Lookup\<^sub>e x) = 1"
| "code_size (PushCon\<^sub>e k) = 1"
| "code_size (PushLam\<^sub>e cd) = Suc (code_list_size cd)"
| "code_size Apply\<^sub>e = 1"
| "code_size Return\<^sub>e = 1"
| "code_size Jump\<^sub>e = 1"
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

fun return_terminated\<^sub>e :: "code\<^sub>e list \<Rightarrow> bool" where
  "return_terminated\<^sub>e [] = False"
| "return_terminated\<^sub>e (PushLam\<^sub>e cd' # cd) = (return_terminated\<^sub>e cd' \<and> return_terminated\<^sub>e cd)"
| "return_terminated\<^sub>e (Return\<^sub>e # cd) = (cd = [])"
| "return_terminated\<^sub>e (Jump\<^sub>e # cd) = (cd = [])"
| "return_terminated\<^sub>e (op # cd) = return_terminated\<^sub>e cd"

fun orderly_stack :: "(bclosure list \<times> nat) list \<Rightarrow> nat \<Rightarrow> bool" where
  "orderly_stack [] cd = True"
| "orderly_stack ((env, 0) # sfs) cd = False"
| "orderly_stack ((env, Suc pc) # sfs) cd = 
    (pc < cd \<and> ordered_closures env cd \<and> orderly_stack sfs cd)"

primrec orderly_state :: "byte_code list \<Rightarrow> byte_code_state \<Rightarrow> bool" where
  "orderly_state cd (BS vs sfs) = (orderly cd 0 \<and> return_terminated\<^sub>b cd \<and> 
    orderly_stack sfs (length cd) \<and> ordered_closures vs (length cd))"

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

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> return_terminated\<^sub>b (cd @ cd') = return_terminated\<^sub>b cd"
  by (induction cd) simp_all

lemma return_terminated_flatten' [simp]: "return_terminated\<^sub>e cd \<Longrightarrow> 
    return_terminated\<^sub>b (flatten_code' lib cd @ cd')"
  by (induction lib cd arbitrary: cd' rule: flatten_code'.induct) (auto split: if_splits)

lemma [simp]: "return_terminated\<^sub>e cd \<Longrightarrow> return_terminated\<^sub>b (flatten_code cd)"
proof (unfold flatten_code_def)
  assume "return_terminated\<^sub>e cd"
  hence "return_terminated\<^sub>b (flatten_code' 0 cd @ [])" by (metis return_terminated_flatten')
  thus "return_terminated\<^sub>b (flatten_code' 0 cd)" by simp
qed

lemma [simp]: "ordered op x \<Longrightarrow> ordered op (Suc x)"
  by (induction op) simp_all

lemma [simp]: "ordered op (x + n) \<Longrightarrow> ordered op (x + (m + n))"
  by (induction op) simp_all

lemma [simp]: "orderly (cd @ cd') n = (orderly cd n \<and> orderly cd' (length cd + n))"
  by (induction cd arbitrary: n) simp_all

lemma [simp]: "lib \<le> n \<Longrightarrow> return_terminated\<^sub>e cd \<Longrightarrow> orderly (flatten_code' lib cd) n"
  by (induction lib cd arbitrary: n rule: flatten_code'.induct) auto

lemma [simp]: "return_terminated\<^sub>e cdr \<Longrightarrow> orderly (flatten_code cdr) 0"
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
 
lemma [simp]: "lookup vs x = Some v \<Longrightarrow> ordered_closures vs n \<Longrightarrow> ordered_closure v n"
  by (induction vs x rule: lookup.induct) simp_all

lemma pushlam_ordered [simp]: "lookup cd x = Some (BPushLam pc) \<Longrightarrow> orderly cd n \<Longrightarrow> 
    x < length cd \<Longrightarrow> 0 < pc \<and> pc \<le> length cd + n"
  by (induction cd x arbitrary: n rule: lookup.induct) fastforce+

lemma [simp]: "lookup cd x = Some (BPushLam pc) \<Longrightarrow> orderly cd 0 \<Longrightarrow> x < length cd \<Longrightarrow> 
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
  by (induction cd pc rule: unflatten_code.induct) (simp_all split: option.splits byte_code.splits) 

lemma unflatten_flatten [simp]: "return_terminated\<^sub>e cd \<Longrightarrow> 
  unflatten_code (lib @ flatten_code' (length lib) cd @ acc) (length lib + code_list_size cd) = cd"
proof (induction "length lib" cd arbitrary: lib acc rule: flatten_code'.induct)
  case (4 cd' cd)
  let ?pc = "length lib + code_list_size cd'"
  let ?code' = "lib @ flatten_code' (length lib) cd' @ []"
  let ?code = "?code' @ flatten_code' ?pc cd @ BPushLam ?pc # acc"
  have X: "length lib + length (flatten_code' (length lib) cd') = length ?code'" by simp
  from 4 have "return_terminated\<^sub>e cd" by simp
  with 4 X have "unflatten_code (?code' @ flatten_code' (length ?code') cd @
    BPushLam (length lib + length (flatten_code' (length lib) cd')) # acc)
      (length ?code' + code_list_size cd) = cd" by blast
  hence "unflatten_code ?code (length lib + code_list_size cd' + code_list_size cd) = cd" by simp
  hence X: "unflatten_code ?code (length lib + (code_list_size cd' + code_list_size cd)) = cd" 
    by (metis add.assoc)
  from 4 have "return_terminated\<^sub>e cd'" by simp
  with 4 have "unflatten_code ?code' (length lib + code_list_size cd') = cd'" by blast
  moreover have "?pc \<le> length ?code'" by simp
  ultimately have Z: "unflatten_code ?code ?pc =  cd'" by (metis unflatten_front)
  with X Z show ?case by simp
qed simp_all

lemma [simp]: "return_terminated\<^sub>e cd \<Longrightarrow> unflatten_code (flatten_code cd) (code_list_size cd) = cd"
proof -
  assume "return_terminated\<^sub>e cd"
  hence "unflatten_code ([] @ flatten_code' (length []) cd @ []) 
    (length [] + code_list_size cd) = cd" by (metis unflatten_flatten list.size(3))
  thus ?thesis by (simp add: flatten_code_def)
qed

lemma orderly_lam [simp]: "lookup cd pc = Some (BPushLam pc') \<Longrightarrow> orderly cd n \<Longrightarrow> pc' \<le> pc + n"
  by (induction cd pc arbitrary: n rule: lookup.induct) fastforce+

lemma [simp]: "lookup cd pc = Some (BPushLam pc') \<Longrightarrow> orderly cd 0 \<Longrightarrow> pc' \<le> pc"
  using orderly_lam by fastforce

theorem completeb [simp]: "cd \<tturnstile> \<Sigma>\<^sub>b \<leadsto>\<^sub>b \<Sigma>\<^sub>b' \<Longrightarrow> orderly_state cd \<Sigma>\<^sub>b \<Longrightarrow> 
  iter (\<leadsto>\<^sub>e) (unflatten_state cd \<Sigma>\<^sub>b) (unflatten_state cd \<Sigma>\<^sub>b')"
proof (induction \<Sigma>\<^sub>b \<Sigma>\<^sub>b' rule: evalb.induct)
  case (evb_lookup cd pc x env v vs sfs)
  hence "S\<^sub>e (ufcs cd vs) 
    ((ufcs cd env, unflatten_code cd (Suc pc)) # ufsfs cd sfs) \<leadsto>\<^sub>e
      S\<^sub>e (unflatten_closure cd v # ufcs cd vs)
        ((ufcs cd env, unflatten_code cd pc) # ufsfs cd sfs)" by simp
  thus ?case by simp
next
  case (evb_pushcon cd pc k vs env sfs)
  hence "S\<^sub>e (ufcs cd vs) 
    ((ufcs cd env, unflatten_code cd (Suc pc)) # ufsfs cd sfs) \<leadsto>\<^sub>e
      S\<^sub>e (Const\<^sub>e k # ufcs cd vs) 
        ((ufcs cd env, unflatten_code cd pc) # ufsfs cd sfs)" by simp
  thus ?case by simp
next
  case (evb_pushlam cd pc pc' vs env sfs)
  moreover hence X: "pc' \<le> pc" by auto
  moreover have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (ufcs cd vs) ((ufcs cd env, 
    PushLam\<^sub>e (unflatten_code cd pc') # 
      unflatten_code cd pc) # ufsfs cd sfs))
        (S\<^sub>e (Lam\<^sub>e (ufcs cd env) (unflatten_code cd pc') # ufcs cd vs) 
          ((ufcs cd env, unflatten_code cd pc) # ufsfs cd sfs))" 
    by (metis ev\<^sub>e_pushlam iter_one)
  ultimately show ?case by simp
next
  case (evb_apply cd pc v env' pc' vs env sfs)
  hence "S\<^sub>e (unflatten_closure cd v # Lam\<^sub>e (ufcs cd env') (unflatten_code cd pc') # ufcs cd vs) 
      ((ufcs cd env, unflatten_code cd (Suc pc)) # ufsfs cd sfs) \<leadsto>\<^sub>e
        S\<^sub>e (ufcs cd vs) ((unflatten_closure cd v # ufcs cd env', unflatten_code cd pc') # 
          (ufcs cd env, unflatten_code cd pc) # 
            ufsfs cd sfs)" by simp
  thus ?case by simp
next
  case (evb_return cd pc vs env sfs)
  moreover have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (ufcs cd vs) ((ufcs cd env, [Return\<^sub>e]) # ufsfs cd sfs))
    (S\<^sub>e (ufcs cd vs) (ufsfs cd sfs))" by (metis ev\<^sub>e_return iter_one)
  ultimately show ?case by simp
next
  case (evb_jump cd pc v env' pc' vs env sfs)
  have "S\<^sub>e (unflatten_closure cd v # Lam\<^sub>e (ufcs cd env') (unflatten_code cd pc') # ufcs cd vs) 
    ((ufcs cd env, [Jump\<^sub>e]) # ufsfs cd sfs) \<leadsto>\<^sub>e S\<^sub>e (ufcs cd vs)
        ((unflatten_closure cd v # ufcs cd env', unflatten_code cd pc') # 
          ufsfs cd sfs)" by (metis ev\<^sub>e_jump)
  with evb_jump have "S\<^sub>e (unflatten_closure cd v # 
    Lam\<^sub>e (ufcs cd env') (unflatten_code cd pc') # ufcs cd vs)
      ((ufcs cd env, unflatten_code cd (Suc pc)) # ufsfs cd sfs) \<leadsto>\<^sub>e
        S\<^sub>e (ufcs cd vs) ((unflatten_closure cd v # ufcs cd env', unflatten_code cd pc') # ufsfs cd sfs)" by simp
  hence "iter (\<leadsto>\<^sub>e) (S\<^sub>e (unflatten_closure cd v # 
    Lam\<^sub>e (ufcs cd env') (unflatten_code cd pc') # ufcs cd vs)
      ((ufcs cd env, unflatten_code cd (Suc pc)) # ufsfs cd sfs))
        (S\<^sub>e (ufcs cd vs) ((unflatten_closure cd v # ufcs cd env', unflatten_code cd pc') # ufsfs cd sfs))" 
    by (metis iter_one)
  thus ?case by simp
qed

lemma [simp]: "Lam\<^sub>e envt cdt = unflatten_closure cdb vb \<Longrightarrow> 
  \<exists>envb pc. vb = BLam envb pc \<and> envt = ufcs cdb envb \<and> cdt = unflatten_code cdb pc"
  by (induction vb) simp_all

lemma unfl_state [dest]: "S\<^sub>e vs sfs = unflatten_state cd \<Sigma>\<^sub>b \<Longrightarrow> \<exists>vsb sfsb. 
    \<Sigma>\<^sub>b = BS vsb sfsb \<and> vs = ufcs cd vsb \<and> sfs = ufsfs cd sfsb"
  by (induction \<Sigma>\<^sub>b) simp_all

lemma [dest]: "Lookup\<^sub>e x # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
    pc < length cdb \<Longrightarrow> lookup cdb pc = Some (BLookup x) \<and> cdt = unflatten_code cdb pc"
  by (simp split: option.splits byte_code.splits)

lemma [dest]: "PushCon\<^sub>e k # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
    pc < length cdb \<Longrightarrow> lookup cdb pc = Some (BPushCon k) \<and> cdt = unflatten_code cdb pc"
  by (simp split: option.splits byte_code.splits)

lemma [dest]: "PushLam\<^sub>e cdt'' # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> pc < length cdb \<Longrightarrow>  
    \<exists>pc'. lookup cdb pc = Some (BPushLam pc') \<and> cdt = unflatten_code cdb pc \<and> 
      cdt'' = unflatten_code cdb pc'"
  by (simp split: option.splits byte_code.splits)

lemma [dest]: "Apply\<^sub>e # cdt = unflatten_code cdb (Suc pc) \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
    pc < length cdb \<Longrightarrow> lookup cdb pc = Some BApply \<and> cdt = unflatten_code cdb pc"
  by (simp split: option.splits byte_code.splits)

lemma [dest]: "Return\<^sub>e # cd = unflatten_code cdb (Suc pc) \<Longrightarrow> 
    orderly cdb 0 \<Longrightarrow> pc < length cdb \<Longrightarrow> lookup cdb pc = Some BReturn \<and> cd = []"
  by (simp split: option.splits byte_code.splits)

lemma [dest]: "Jump\<^sub>e # cd = unflatten_code cdb (Suc pc) \<Longrightarrow> 
    orderly cdb 0 \<Longrightarrow> pc < length cdb \<Longrightarrow> lookup cdb pc = Some BJump \<and> cd = []"
  by (simp split: option.splits byte_code.splits)

lemma uf_to_lookup [dest]: "(envt, Lookup\<^sub>e x # cdt) # sfst = ufsfs cdb sfsb \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. 
    sfsb = (envb, Suc pc) # sfsb' \<and> envt = ufcs cdb envb \<and> lookup cdb pc = Some (BLookup x) \<and> 
      cdt = unflatten_code cdb pc \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "Lookup\<^sub>e x # cdt = unflatten_code cdb (Suc pc) \<and> orderly cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some (BLookup x) \<and> cdt = unflatten_code cdb pc" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_pushcon [dest]: "(envt, PushCon\<^sub>e k # cdt) # sfst = ufsfs cdb sfsb \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> orderly_stack sfsb (length cdb) \<Longrightarrow> 
    \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> envt = ufcs cdb envb \<and> 
      lookup cdb pc = Some (BPushCon k) \<and> cdt = unflatten_code cdb pc \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "PushCon\<^sub>e k # cdt = unflatten_code cdb (Suc pc) \<and> orderly cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some (BPushCon k) \<and> cdt = unflatten_code cdb pc" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_pushlam [dest]: "(envt, PushLam\<^sub>e cdt' # cdt) # sfst = ufsfs cdb sfsb \<Longrightarrow> 
  orderly cdb 0 \<Longrightarrow> orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb' pc'. 
    sfsb = (envb, Suc pc) # sfsb' \<and> envt = ufcs cdb envb \<and> lookup cdb pc = Some (BPushLam pc') \<and> 
      cdt = unflatten_code cdb pc \<and> cdt' = unflatten_code cdb pc' \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "PushLam\<^sub>e cdt' # cdt = unflatten_code cdb (Suc pc) \<and> orderly cdb 0 \<and> pc < length cdb" 
    by simp
  then obtain pc' where "lookup cdb pc = Some (BPushLam pc') \<and> cdt = unflatten_code cdb pc \<and> 
    cdt' = unflatten_code cdb pc'" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_apply [dest]: "(envt, Apply\<^sub>e # cdt) # sfst = ufsfs cdb sfsb \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> 
    envt = ufcs cdb envb \<and> lookup cdb pc = Some BApply \<and> cdt = unflatten_code cdb pc \<and> 
      sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "Apply\<^sub>e # cdt = unflatten_code cdb (Suc pc) \<and> orderly cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some BApply \<and> cdt = unflatten_code cdb pc" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_return [dest]: "(envt, Return\<^sub>e # cd) # sfst = ufsfs cdb sfsb \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> 
    envt = ufcs cdb envb \<and> lookup cdb pc = Some BReturn \<and> sfst = ufsfs cdb sfsb' \<and> cd = []"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "Return\<^sub>e # cd = unflatten_code cdb (Suc pc) \<and> 
    orderly cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some BReturn \<and> cd = []" by blast
  with 3 show ?case by simp
qed simp_all

lemma uf_to_jump [dest]: "(envt, Jump\<^sub>e # cd) # sfst = ufsfs cdb sfsb \<Longrightarrow> orderly cdb 0 \<Longrightarrow> 
  orderly_stack sfsb (length cdb) \<Longrightarrow> \<exists>envb pc sfsb'. sfsb = (envb, Suc pc) # sfsb' \<and> 
    envt = ufcs cdb envb \<and> lookup cdb pc = Some BJump \<and> sfst = ufsfs cdb sfsb'"
proof (induction sfsb "length cdb" rule: orderly_stack.induct)
  case (3 envb pc sfsb')
  hence "Jump\<^sub>e # cd = unflatten_code cdb (Suc pc) \<and> 
    orderly cdb 0 \<and> pc < length cdb" by simp
  hence "lookup cdb pc = Some BJump \<and> cd = []" by blast
  with 3 show ?case by simp
qed simp_all

theorem correctb [simp]: "unflatten_state cd\<^sub>b \<Sigma>\<^sub>b \<leadsto>\<^sub>e \<Sigma>\<^sub>t' \<Longrightarrow> orderly_state cd\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>b'. iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state cd\<^sub>b \<Sigma>\<^sub>b' = \<Sigma>\<^sub>t'"
proof (induction "unflatten_state cd\<^sub>b \<Sigma>\<^sub>b" \<Sigma>\<^sub>t' rule: eval\<^sub>e.induct)
  case (ev\<^sub>e_lookup env x v vs cd sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = BS vsb sfsb \<and> vs = ufcs cd\<^sub>b vsb \<and> 
    (env, Lookup\<^sub>e x # cd) # sfs = ufsfs cd\<^sub>b sfsb" by fastforce
  with ev\<^sub>e_lookup have "orderly cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some (BLookup x) \<and> cd = unflatten_code cd\<^sub>b pc \<and> 
      sfs = ufsfs cd\<^sub>b sfsb'" by (metis uf_to_lookup)
  with ev\<^sub>e_lookup obtain v' where V: "lookup envb x = Some v' \<and> unflatten_closure cd\<^sub>b v' = v"
    by fastforce
  with S have "cd\<^sub>b \<tturnstile> BS vsb ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b BS (v' # vsb) ((envb, pc) # sfsb')"
    by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (BS vsb ((envb, Suc pc) # sfsb')) (BS (v' # vsb) ((envb, pc) # sfsb'))" 
    by simp
  with B S V show ?case by fastforce
next
  case (ev\<^sub>e_pushcon vs env k cd sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = BS vsb sfsb \<and> vs = ufcs cd\<^sub>b vsb \<and> 
    (env, PushCon\<^sub>e k # cd) # sfs = ufsfs cd\<^sub>b sfsb" by fastforce
  with ev\<^sub>e_pushcon have "orderly cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some (BPushCon k) \<and> cd = unflatten_code cd\<^sub>b pc \<and> 
      sfs = ufsfs cd\<^sub>b sfsb'" by (metis uf_to_pushcon)
  with S have "cd\<^sub>b \<tturnstile> BS vsb ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b BS (BConst k # vsb) ((envb, pc) # sfsb')"
    by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (BS vsb ((envb, Suc pc) # sfsb')) 
    (BS (BConst k # vsb) ((envb, pc) # sfsb'))" by simp
  with B S show ?case by fastforce
next
  case (ev\<^sub>e_pushlam vs env cd' cd sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = BS vsb sfsb \<and> vs = ufcs cd\<^sub>b vsb \<and> 
    (env, PushLam\<^sub>e cd' # cd) # sfs = ufsfs cd\<^sub>b sfsb" by fastforce
  with ev\<^sub>e_pushlam have "orderly cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' pc' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some (BPushLam pc') \<and> cd = unflatten_code cd\<^sub>b pc \<and> 
      sfs = ufsfs cd\<^sub>b sfsb' \<and> cd' = unflatten_code cd\<^sub>b pc'" by (metis uf_to_pushlam)
  with S have "cd\<^sub>b \<tturnstile> BS vsb ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b 
    BS (BLam envb pc' # vsb) ((envb, pc) # sfsb')" by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (BS vsb ((envb, Suc pc) # sfsb')) 
    (BS (BLam envb pc' # vsb) ((envb, pc) # sfsb'))" by simp
  with B S show ?case by fastforce
next
  case (ev\<^sub>e_apply v env' cd' vs env cd sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = BS vsb sfsb \<and> 
    v # Lam\<^sub>e env' cd' # vs = ufcs cd\<^sub>b vsb \<and> (env, Apply\<^sub>e # cd) # sfs = ufsfs cd\<^sub>b sfsb" 
      by fastforce
  with ev\<^sub>e_apply have "orderly cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some BApply \<and> cd = unflatten_code cd\<^sub>b pc \<and> 
      sfs = ufsfs cd\<^sub>b sfsb'" by (metis uf_to_apply)
  from B obtain vb envb' pc' vsb' where V: "vsb = vb # BLam envb' pc' # vsb' \<and> 
    v = unflatten_closure cd\<^sub>b vb \<and> env' = ufcs cd\<^sub>b envb' \<and> cd' = unflatten_code cd\<^sub>b pc' \<and>
      vs = ufcs cd\<^sub>b vsb'" by fastforce
  from S have "cd\<^sub>b \<tturnstile> BS (vb # BLam envb' pc' # vsb') ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b
    BS vsb' ((vb # envb', pc') # (envb, pc) # sfsb')" by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (BS (vb # BLam envb' pc' # vsb') ((envb, Suc pc) # sfsb')) 
    (BS vsb' ((vb # envb', pc') # (envb, pc) # sfsb'))" by simp
  with B S V show ?case by auto                                              
next
  case (ev\<^sub>e_return vs env cd sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = BS vsb sfsb \<and> vs = ufcs cd\<^sub>b vsb \<and> 
    (env, Return\<^sub>e # cd) # sfs = ufsfs cd\<^sub>b sfsb" by fastforce
  with ev\<^sub>e_return have "orderly cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some BReturn \<and> sfs = ufsfs cd\<^sub>b sfsb'" 
      by (metis uf_to_return)
  with S have "cd\<^sub>b \<tturnstile> BS vsb ((envb, Suc pc) # sfsb') \<leadsto>\<^sub>b BS vsb sfsb'" by simp
  hence "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) (BS vsb ((envb, Suc pc) # sfsb')) (BS vsb sfsb')" by simp
  with B S show ?case by fastforce
next
  case (ev\<^sub>e_jump v env' cd' vs env cd sfs)
  then obtain vsb sfsb where B: "\<Sigma>\<^sub>b = BS vsb sfsb \<and> 
    v # Lam\<^sub>e env' cd' # vs = ufcs cd\<^sub>b vsb \<and> 
      (env, Jump\<^sub>e # cd) # sfs = ufsfs cd\<^sub>b sfsb" by fastforce
  with ev\<^sub>e_jump have "orderly cd\<^sub>b 0 \<and> orderly_stack sfsb (length cd\<^sub>b)" by simp
  with B obtain envb pc sfsb' where S: "sfsb = (envb, Suc pc) # sfsb' \<and> 
    env = ufcs cd\<^sub>b envb \<and> lookup cd\<^sub>b pc = Some BJump \<and> sfs = ufsfs cd\<^sub>b sfsb'" 
      by (metis uf_to_jump)
  from B obtain vb envb' pc' vsb' where V: "vsb = vb # BLam envb' pc' # vsb' \<and> 
    v = unflatten_closure cd\<^sub>b vb \<and> env' = ufcs cd\<^sub>b envb' \<and> cd' = unflatten_code cd\<^sub>b pc' \<and>
      vs = ufcs cd\<^sub>b vsb'" by fastforce
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
  \<exists>v. \<Sigma> = BS [v] [] \<and> c = unflatten_closure cd v"
proof -
  assume "unflatten_state cd \<Sigma> = S\<^sub>e [c] []"
  then obtain vs sfs where S: "\<Sigma> = BS vs sfs \<and> [c] = ufcs cd vs \<and> [] = ufsfs cd sfs" 
    by (metis unfl_state)
  moreover then obtain v where "vs = [v] \<and> c = unflatten_closure cd v" by blast
  ultimately show ?thesis by simp
qed

lemma evalb_end [simp]: "iter (\<leadsto>\<^sub>e) (unflatten_state cd\<^sub>b \<Sigma>\<^sub>b) (S\<^sub>e [c] []) \<Longrightarrow> 
  orderly_state cd\<^sub>b \<Sigma>\<^sub>b \<Longrightarrow> 
    \<exists>v. iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b (BS [v] []) \<and> c = unflatten_closure cd\<^sub>b v"
proof -
  assume "iter (\<leadsto>\<^sub>e) (unflatten_state cd\<^sub>b \<Sigma>\<^sub>b) (S\<^sub>e [c] [])"
  moreover assume O: "orderly_state cd\<^sub>b \<Sigma>\<^sub>b"
  ultimately obtain \<Sigma>\<^sub>b' where E: "iter (\<tturnstile> cd\<^sub>b \<leadsto>\<^sub>b) \<Sigma>\<^sub>b \<Sigma>\<^sub>b' \<and> unflatten_state cd\<^sub>b \<Sigma>\<^sub>b' = S\<^sub>e [c] []" 
    by fastforce
  moreover with O have "orderly_state cd\<^sub>b \<Sigma>\<^sub>b'" by fastforce
  moreover with E obtain v where "\<Sigma>\<^sub>b' = BS [v] [] \<and> c = unflatten_closure cd\<^sub>b v" 
    by (metis unfl_terminal)
  ultimately show ?thesis by blast
qed

end