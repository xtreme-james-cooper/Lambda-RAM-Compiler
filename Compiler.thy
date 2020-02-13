theory Compiler
  imports "01Source/AlgorithmicTypechecking" Printing "03Stack/StackConversion" 
begin

primrec get_return :: "nat \<Rightarrow> nexpr \<Rightarrow> tco_return" where
  "get_return d (NVar x) = TCOReturn d"
| "get_return d (NConst k) = TCOReturn d"
| "get_return d (NLam x t e) = TCOReturn d"
| "get_return d (NApp e\<^sub>1 e\<^sub>2) = TCOJump d"

primrec flatten_return :: "tco_return \<Rightarrow> byte_code" where 
  "flatten_return (TCOReturn d) = BReturn d"
| "flatten_return (TCOJump d) = BJump d"

function xflatten_code' :: "nat \<Rightarrow> nat \<Rightarrow> byte_code list \<Rightarrow> tco_code list \<Rightarrow> 
    byte_code list \<times> byte_code list \<times> nat" where
  "xflatten_code' ofst sz acc [] = ([], acc, Suc (ofst + sz))"
| "xflatten_code' ofst sz acc (TCOLookup x # cd) = 
    xflatten_code' ofst (Suc sz) (BLookup x # acc) cd"
| "xflatten_code' ofst sz acc (TCOPushCon k # cd) = 
    xflatten_code' ofst (Suc sz) (BPushCon k # acc) cd"
| "xflatten_code' ofst sz acc (TCOPushLam cd' r' d # cd) = (case xflatten_code' ofst 0 [] cd' of
    (lib', cdb', sz') \<Rightarrow> (case xflatten_code' sz' (Suc sz) (BPushLam sz' d # acc) cd of
      (lib, cdb, sz'') \<Rightarrow> (lib' @ flatten_return r' # cdb' @ lib, cdb, sz'')))"
| "xflatten_code' ofst sz acc (TCOApply # cd) = xflatten_code' ofst (Suc sz) (BApply # acc) cd"
  by pat_completeness auto
termination
  by (relation "measure (code_list_size \<circ> snd \<circ> snd \<circ> snd)") simp_all

primrec compile' :: "var list \<Rightarrow> nat \<Rightarrow> tco_code list \<Rightarrow> bool \<Rightarrow> nexpr \<Rightarrow> tco_code list" where
  "compile' var_idxs depth acc tail_pos (NVar x) = TCOLookup (the (idx_of var_idxs x)) # acc"
| "compile' var_idxs depth acc tail_pos (NConst k) = TCOPushCon k # acc"
| "compile' var_idxs depth acc tail_pos (NLam x t e) = 
    TCOPushLam (compile' (x # var_idxs) (Suc depth) [] True e) 
      (get_return (Suc depth) e) depth # acc"
| "compile' var_idxs depth acc tail_pos (NApp e\<^sub>1 e\<^sub>2) = 
    compile' var_idxs depth 
      (compile' var_idxs depth (if tail_pos then acc else TCOApply # acc) False e\<^sub>2) False e\<^sub>1"

primrec xflatten_code :: "tco_code list \<times> tco_return \<Rightarrow> byte_code list \<times> nat" where
  "xflatten_code (cd, r) = (case xflatten_code' 0 0 [] cd of
    (lib, cdb, sz) \<Rightarrow> (lib @ flatten_return r # cdb, sz))"

definition compile :: "nexpr \<Rightarrow> tco_code list \<times> tco_return" where
  "compile e = (compile' [] 0 [] True e, get_return 0 e)"

lemma [simp]: "[flatten_return r] = flatten_code' lib [] r"
  by (induction r) simp_all

lemma flatten'_correctness [simp]: "sz = length acc \<Longrightarrow> 
  xflatten_code' ofst sz acc cd = (lib, cdb, sz') \<Longrightarrow> 
    sz' = ofst + code_list_size cd + sz \<and> 
      lib @ flatten_return r # cdb = flatten_code' ofst cd r @ acc"
proof (induction ofst sz acc cd arbitrary: lib cdb sz' r rule: xflatten_code'.induct)
  case (4 ofst sz acc cd' r' d cd)
  moreover obtain lib' cdb' sz'' where "xflatten_code' ofst 0 [] cd' = (lib', cdb', sz'')" 
    by (cases "xflatten_code' ofst 0 [] cd'")
  moreover obtain lib2 cdb2 sz2 where 
    "xflatten_code' sz'' (Suc sz) (BPushLam sz'' d # acc) cd = (lib2, cdb2, sz2)" 
      by (cases "xflatten_code' sz'' (Suc sz) (BPushLam sz'' d # acc) cd")
  ultimately show ?case by force
qed (auto split: prod.splits)

lemma [simp]: "xflatten_code cdr = (flatten_code cdr, length (flatten_code cdr))"
proof (cases cdr)
  case (Pair cd r)
  moreover obtain lib cdb sz where S :"xflatten_code' 0 0 [] cd = (lib, cdb, sz)" 
    by (cases "xflatten_code' 0 0 [] cd") simp_all
  moreover have "0 = length []" by simp
  moreover with S have "sz = 0 + code_list_size cd + length [] \<and> 
    lib @ flatten_return r # cdb = flatten_code' 0 cd r @ []" by (metis flatten'_correctness)
  ultimately show ?thesis by simp
qed

lemma [simp]: "get_return d e = tco_r d (encode' (convert' \<Phi> e) d')"
proof (induction e arbitrary: \<Phi> d)
  case (NApp e1 e2)
  have "tco_r d ((encode' (convert' \<Phi> e1) d' @ encode' (convert' \<Phi> e2) d') @ [TApply]) = 
    tco_r d [TApply]" using tco_r_append by blast
  thus ?case by simp
qed simp_all

lemma compile_correct [simp]: "cd' = tco_cd cd \<Longrightarrow> 
  compile' \<Phi> d cd' (cd = []) e = tco_cd (encode' (convert' \<Phi> e) d @ cd)"
proof (induction e arbitrary: \<Phi> d cd cd')
  case (NLam x t e)
  moreover have "[] = tco_cd []" by simp
  ultimately have "compile' (x # \<Phi>) (Suc d) [] True e =
    tco_cd (encode' (convert' (x # \<Phi>) e) (Suc d) @ [])" by (metis (full_types))
  with NLam show ?case by (cases \<Phi>) simp_all
next
  case (NApp e1 e2)
  hence "(if cd = [] then cd' else TCOApply # cd') = tco_cd (TApply # cd)" 
    by (simp split: list.splits)
  with NApp have "compile' \<Phi> d (if cd = [] then cd' else TCOApply # cd') 
    (TApply # cd = []) e2 = 
      tco_cd (encode' (convert' \<Phi> e2) d @ TApply # cd)" by blast
  moreover from NApp have "compile' \<Phi> d (tco_cd (encode' (convert' \<Phi> e2) d @ TApply # cd)) 
    ((encode' (convert' \<Phi> e2) d @ TApply # cd) = []) e1 = 
      tco_cd (encode' (convert' \<Phi> e1) d @ encode' (convert' \<Phi> e2) d @ TApply # cd)" by blast
  ultimately show ?case by simp
qed simp_all

lemma [simp]: "compile = tco \<circ> encode \<circ> convert"
proof (rule, unfold compile_def tco_def encode_def convert_def)
  fix e
  have "[] = tco_cd []" by simp
  hence "compile' [] 0 [] ([] = []) e = tco_cd (encode' (convert' [] e) 0 @ [])" 
    by (metis (full_types) compile_correct)
  thus "(compile' [] 0 [] True e, get_return 0 e) =
    ((\<lambda>cd. (tco_cd cd, tco_r 0 cd)) \<circ> (\<lambda>e. encode' e 0) \<circ> convert' []) e" by simp
qed

lemma [simp]: "tco_cd (encode' e d) \<noteq> []"
  by (induction e) simp_all

lemma [simp]: "tco_cd (encode e) \<noteq> []"
  by (simp add: encode_def)

theorem tc_terminationn: "typechecks e \<Longrightarrow> xflatten_code (compile e) = (cd, pc) \<Longrightarrow> 
  \<exists>v. valn v \<and> e \<Down> v \<and> 
    (\<exists>h v\<^sub>f. iter (\<leadsto>\<^sub>f) (FS hempty [] [[pc]] cd) (FS h [v\<^sub>f] [] cd) \<and> 
      print_hclosure (get_closure h v\<^sub>f) = print_nexpr v)"
proof -
  assume "typechecks e"
  then obtain t where TN: "Map.empty \<turnstile>\<^sub>n e : t" by fastforce
  then obtain v\<^sub>n where EN: "e \<Down> v\<^sub>n" by fastforce
  hence VN: "valn v\<^sub>n" by simp
  from TN have TD: "[] \<turnstile>\<^sub>d convert e : t" by simp
  from EN TN have ED: "convert e \<Down>\<^sub>d convert v\<^sub>n" by simp
  hence VD: "vald (convert v\<^sub>n)" by simp
  from ED have "iter (\<leadsto>\<^sub>d) (convert e) (convert v\<^sub>n)" by (metis BigStep.correctb)
  with ED EN TD have ES: "iter (\<leadsto>\<^sub>s) (SS [FReturn] (convert e)) (SS [] (convert v\<^sub>n))" by simp
  from TD have TC: "CSE [CReturn []] [] (convert e) :\<^sub>c t" 
    by (metis tcc_state_ev tcc_nil tcc_snil tcc_scons_ret latest_environment.simps(4))
  with ES VD EN obtain c where EC: "iter (\<leadsto>\<^sub>c) (CSE [CReturn []] [] (convert e)) (CSC [] c) \<and> 
    declosure c = convert v\<^sub>n" by fastforce
  with VN have VC: "print_closure c = print_nexpr v\<^sub>n" by simp
  from TC EC have "iter (\<leadsto>\<^sub>t) (encode_state (CSE [CReturn []] [] (convert e))) 
    (encode_state (CSC [] c))" by (metis iter_completet)
  hence "iter (\<leadsto>\<^sub>t) (TS [] [([], encode (convert e))]) (TS [encode_closure c] [])" 
    by (simp add: encode_def)
  hence "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS [] [([], encode (convert e))])) 
    (tco_state (TS [encode_closure c] []))" by (metis iter_tco_eval)
  hence ET: "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS [] [([], tco_cd (encode (convert e)), tco_r 0 (encode (convert e)))]) 
    (TCOS [tco_val (encode_closure c)] [])" by simp
  assume "xflatten_code (compile e) = (cd, pc)"
  hence C: "flatten_code (tco (encode (convert e))) = cd \<and> 
    pc = length (flatten_code (tco (encode (convert e))))" by auto
  hence UB: "unflatten_state (BS [] [([], pc)] cd) = 
    TCOS [] [([], tco_cd (encode (convert e)), tco_r 0 (encode (convert e)))]" 
      by (auto simp add: tco_def simp del: flatten_code.simps)
  from C have "orderly_state (BS [] [([], pc)] cd)" by auto
  with ET UB obtain v\<^sub>b where EB: 
    "iter (\<leadsto>\<^sub>b) (BS [] [([], pc)] cd) (BS [v\<^sub>b] [] cd) \<and> 
      tco_val (encode_closure c) = unflatten_closure cd v\<^sub>b" 
    by (metis evalb_end byte_code_state.sel(3))
  hence "print_bclosure v\<^sub>b = print_tco_closure (tco_val (encode_closure c))" by simp
  with VC have VB: "print_bclosure v\<^sub>b = print_nexpr v\<^sub>n" by simp
  from EB obtain \<Sigma>\<^sub>h' where EH: "iter (\<leadsto>\<^sub>h) (HS hempty [] [([], pc)] cd) \<Sigma>\<^sub>h' \<and> 
    BS [v\<^sub>b] [] cd = unheap \<Sigma>\<^sub>h'" by fastforce
  then obtain h\<^sub>h v\<^sub>h where SH: "\<Sigma>\<^sub>h' = HS h\<^sub>h [v\<^sub>h] [] cd \<and> v\<^sub>b = unheap_closure h\<^sub>h v\<^sub>h" 
    using unheap_empty by blast
  with VB have VH: "print_hclosure (hlookup h\<^sub>h v\<^sub>h) = print_nexpr v\<^sub>n" by simp
  have HS: "heap_structured (HS hempty [] [([], pc)] cd)" by simp
  have FS: "flatten (HS hempty [] [([], pc)] cd) = FS hempty [] [[pc]] cd" by simp
  obtain h\<^sub>f mp where HC: "hsplay splay_closure h\<^sub>h = (h\<^sub>f, mp)" by fastforce
  with SH have "flatten \<Sigma>\<^sub>h' = FS h\<^sub>f [mp v\<^sub>h] [] cd" by simp
  with EH FS HS have EF: "iter (\<leadsto>\<^sub>f) (FS hempty [] [[pc]] cd) (FS h\<^sub>f [mp v\<^sub>h] [] cd)"
    by (metis completef_iter)
  from EH have "heap_structured \<Sigma>\<^sub>h'" by fastforce
  with SH have "hcontains h\<^sub>h v\<^sub>h" by simp
  with HC have "get_closure h\<^sub>f (mp v\<^sub>h) = flatten_closure mp (hlookup h\<^sub>h v\<^sub>h)" 
    by (metis get_closure_flatten)
  with VH have VF: "print_hclosure (get_closure h\<^sub>f (mp v\<^sub>h)) = print_nexpr v\<^sub>n" 
    by (simp del: get_closure.simps)



  from EF VF have "iter (\<leadsto>\<^sub>f) (FS hempty [] [[pc]] cd) (FS h\<^sub>f [mp v\<^sub>h] [] cd) \<and> 
    print_hclosure (get_closure h\<^sub>f (mp v\<^sub>h)) = print_nexpr v\<^sub>n" by simp
  with EN VN show ?thesis by fastforce
qed

end