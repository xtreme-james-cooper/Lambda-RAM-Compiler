theory Compiler
  imports "01Source/AlgorithmicTypechecking" Printing "03Stack/StackConversion" 
begin

primrec get_return :: "nat \<Rightarrow> nexpr \<Rightarrow> byte_code" where
  "get_return d (NVar x) = BReturn d"
| "get_return d (NConst k) = BReturn d"
| "get_return d (NLam x t e) = BReturn d"
| "get_return d (NApp e\<^sub>1 e\<^sub>2) = BJump d"

primrec compile' :: "var list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> byte_code list \<Rightarrow> bool \<Rightarrow> nat \<Rightarrow> byte_code list \<Rightarrow> 
    nexpr \<Rightarrow> byte_code list \<times> nat \<times> byte_code list \<times> nat" where
  "compile' var_idxs depth sz acc tail_pos ofst lib (NVar x) = 
    (lib, ofst, BLookup (the (idx_of var_idxs x)) # acc, Suc sz)"
| "compile' var_idxs depth sz acc tail_pos ofst lib (NConst k) = 
    (lib, ofst, BPushCon k # acc, Suc sz)"
| "compile' var_idxs depth sz acc tail_pos ofst lib (NLam x t e) = (
    let (lib', ofst', cd', sz') = compile' (x # var_idxs) (Suc depth) 0 [] True ofst lib e
    in (lib' @ get_return (Suc depth) e # cd', 
        Suc (ofst' + sz'),
        BPushLam (Suc (ofst' + sz')) depth # acc,
        Suc sz))"
| "compile' var_idxs depth sz acc tail_pos ofst lib (NApp e\<^sub>1 e\<^sub>2) = (
    let (lib1, ofst1, cd1, sz1) = compile' var_idxs depth sz acc False ofst lib e\<^sub>1
    in let (lib2, ofst2, cd2, sz2) = compile' var_idxs depth sz1 cd1 False ofst1 lib1 e\<^sub>2
    in if tail_pos then (lib2, ofst2, cd2, sz2) else (lib2, ofst2, BApply # cd2, Suc sz2))"

definition compile :: "nexpr \<Rightarrow> byte_code list \<times> nat" where
  "compile e = (  
    let (lib, ofst, cdb, sz) = compile' [] 0 0 [] True 0 [] e
    in (lib @ get_return 0 e # cdb, Suc (ofst + sz)))"

abbreviation maybe_return :: "bool \<Rightarrow> nat" where
  "maybe_return tail_pos \<equiv> (if tail_pos then 1 else 0)"

primrec tco_code_size :: "bool \<Rightarrow> nexpr \<Rightarrow> nat" where
  "tco_code_size tail_pos (NVar x) = 1 + maybe_return tail_pos"
| "tco_code_size tail_pos (NConst k) = 1 + maybe_return tail_pos"
| "tco_code_size tail_pos (NLam x t e) = 1 + tco_code_size True e + maybe_return tail_pos"
| "tco_code_size tail_pos (NApp e\<^sub>1 e\<^sub>2) = 
    1 + tco_code_size False e\<^sub>1 + tco_code_size False e\<^sub>2"

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> code_list_size (tco_cd_one op # cd) = 
    code_size (tco_cd_one op) + code_list_size cd"
  by (induction op) simp_all

lemma [simp]: "cd' \<noteq> [] \<Longrightarrow> code_list_size (map tco_cd_one cd @ cd') = 
  code_list_size (map tco_cd_one cd) + code_list_size cd' - 1"
proof (induction cd)
  case (Cons op cd)
  thus ?case by (cases "code_list_size cd'") simp_all
qed simp_all

lemma tco_code_size_as_code_list_size [simp]: "tco_code_size True e =
    code_list_size (tco_cd (encode' (convert' var_idxs e) depth))"
  and [simp]: "tco_code_size False e =
    code_list_size (map tco_cd_one (encode' (convert' var_idxs e) depth)) - 1"
proof (induction e arbitrary: var_idxs depth)
  case (NApp e1 e2) case 1
  let ?cd1 = "map tco_cd_one (encode' (convert' var_idxs e1) depth)"
  let ?cd2 = "map tco_cd_one (encode' (convert' var_idxs e2) depth)"
  have "Suc ((code_list_size ?cd1 - 1) + (code_list_size ?cd2 - 1)) = 
    code_list_size ?cd1 + code_list_size ?cd2 - 1" 
      by (cases "code_list_size ?cd1") simp_all
  with NApp show ?case by simp
next 
  case (NApp e1 e2) case 2
  let ?cd1 = "map tco_cd_one (encode' (convert' var_idxs e1) depth)"
  let ?cd2 = "map tco_cd_one (encode' (convert' var_idxs e2) depth)"
  have "Suc ((code_list_size ?cd1 - 1) + (code_list_size ?cd2 - 1)) = 
    code_list_size ?cd1 + code_list_size ?cd2 - 1" 
      by (cases "code_list_size ?cd1") simp_all
  with NApp show ?case by simp
qed simp_all

lemma compile_lengths [simp]: 
  "compile' var_idxs depth (length acc) acc tail_pos (length lib) lib e = (lib', ofst, cd, sz) \<Longrightarrow> 
    sz = length cd \<and> ofst = length lib'"
proof (induction e arbitrary: var_idxs depth acc tail_pos lib lib' cd sz ofst)
  case (NLam x t e)
  from NLam(2) obtain lib'' ofst'' cd' sz'' where 
    "compile' (x # var_idxs) (Suc depth) 0 [] True (length lib) lib e = (lib'', ofst'', cd', sz'') \<and>
      lib' = lib'' @ get_return (Suc depth) e # cd' \<and> 
        cd = BPushLam (Suc (ofst'' + sz'')) depth # acc \<and> sz = Suc (length acc) \<and> 
          ofst = Suc (ofst'' + sz'')"
      by (cases "compile' (x # var_idxs) (Suc depth) 0 [] True (length lib) lib e") auto
  moreover from NLam(1) have "compile' (x # var_idxs) (Suc depth) 0 [] True (length lib) lib e = 
    (lib'', ofst'', cd', sz'') \<Longrightarrow> sz'' = length cd' \<and> ofst'' = length lib''" 
      by (metis list.size(3))
  ultimately show ?case by simp
next
  case (NApp e1 e2)
  obtain lib1 ofst1 cd1 sz1 where C1: 
    "compile' var_idxs depth (length acc) acc False (length lib) lib e1 = (lib1, ofst1, cd1, sz1)" 
      by (cases "compile' var_idxs depth (length acc) acc False (length lib) lib e1") fastforce+
  obtain lib2 ofst2 cd2 sz2 where C2: 
    "compile' var_idxs depth sz1 cd1 False ofst1 lib1 e2 = (lib2, ofst2, cd2, sz2)"
      by (cases "compile' var_idxs depth sz1 cd1 False ofst1 lib1 e2") fastforce+
  with NApp C1 have "sz2 = length cd2 \<and> ofst2 = length lib2" by blast
  with NApp(3) C1 C2 show ?case by (auto split: if_splits)
qed auto

lemma compile_code_size [simp]: 
  "compile' var_idxs depth (length acc) acc tail_pos (length lib) lib e = (lib', ofst, cd, sz) \<Longrightarrow> 
    ofst + sz + maybe_return tail_pos = length lib + length acc + tco_code_size tail_pos e"
proof (induction e arbitrary: var_idxs depth acc tail_pos lib lib' cd sz ofst)
  case (NLam x t e)
  obtain lib'' ofst' cd' sz' where X:
    "compile' (x # var_idxs) (Suc depth) 0 [] True (length lib) lib e = (lib'', ofst', cd', sz')" 
      by (cases "compile' (x # var_idxs) (Suc depth) 0 [] True (length lib) lib e") blast
  from NLam have "\<And>xacc. 
    compile' (x # var_idxs) (Suc depth) (length xacc) xacc True (length lib) lib e = 
      (lib'', ofst', cd', sz') \<Longrightarrow>
        ofst' + sz' + maybe_return True = length lib + length xacc + tco_code_size True e" by blast
  hence "compile' (x # var_idxs) (Suc depth) (length []) [] True (length lib) lib e = 
    (lib'', ofst', cd', sz') \<Longrightarrow>
      ofst' + sz' + maybe_return True = length lib + length [] + tco_code_size True e" 
    by (metis list.size(3))
  with X have "Suc (ofst' + sz') + Suc (length acc) = 
    Suc (length lib + length acc + tco_code_size True e)" by simp
  with NLam X show ?case by simp
next
  case (NApp e1 e2)
  obtain lib1 ofst1 cd1 sz1 where X:
    "compile' var_idxs depth (length acc) acc False (length lib) lib e1 = (lib1, ofst1, cd1, sz1)"
      by (cases "compile' var_idxs depth (length acc) acc False (length lib) lib e1") blast+
  obtain lib2 ofst2 cd2 sz2 where Y:
    "compile' var_idxs depth sz1 cd1 False ofst1 lib1 e2 = (lib2, ofst2, cd2, sz2)"
    by (cases "compile' var_idxs depth sz1 cd1 False ofst1 lib1 e2") blast+
  from NApp X have Z: "ofst1 + sz1 + maybe_return False = 
    length lib + length acc + tco_code_size False e1" by blast
  from X have L: "sz1 = length cd1 \<and> ofst1 = length lib1" by simp
  with NApp Y have W: "ofst2 + sz2 + maybe_return False = 
    length lib1 + length cd1 + tco_code_size False e2" by blast
  thus ?case
  proof (cases tail_pos)
    case True
    with NApp X Y Z L W show ?thesis by simp
  next
    case False
    moreover with NApp X Y have "(lib2, ofst2, BApply # cd2, Suc sz2) = (lib', ofst, cd, sz)" 
      by simp
    moreover from Z L W have "ofst2 + sz2 = 
      length lib + length acc + tco_code_size False e1 + tco_code_size False e2" by simp
    ultimately show ?thesis by fastforce
  qed
qed auto

lemma compile_code [simp]: "compile' var_idxs depth (length acc) acc tail_pos (length lib) lib e =
  (lib', ofst', cd, sz') \<Longrightarrow> lib' @ get_return depth e # cd = 
    lib @ flatten_code' (length lib) (tco_cd (encode' (convert' var_idxs e) depth)) 
      (tco_r depth (encode' (convert' var_idxs e) depth)) @ acc"
proof (induction e arbitrary: var_idxs depth acc tail_pos lib lib' ofst' cd sz')
  case (NLam x t e)
  let ?cde = "encode' (convert' (x # var_idxs) e) (Suc depth)"
  from NLam obtain lib'' ofst'' cd' sz'' where C:
    "compile' (x # var_idxs) (Suc depth) 0 [] True (length lib) lib e = (lib'', ofst'', cd', sz'') \<and>
      lib' = lib'' @ get_return (Suc depth) e # cd' \<and> 
        cd = BPushLam (Suc (ofst'' + sz'')) depth # acc \<and> sz' = Suc (length acc) \<and> 
          ofst' = Suc (ofst'' + sz'')"
    by (cases "compile' (x # var_idxs) (Suc depth) 0 [] True (length lib) lib e") auto
  with NLam(1) have L: "lib' =
    lib @ flatten_code' (length lib) (tco_cd ?cde) (tco_r (Suc depth) ?cde) @ []" 
      by (metis list.size(3))
  from C have S: "sz'' = length cd' \<and> ofst'' = length lib''" by (metis compile_lengths list.size(3))
  have "\<And>xacc. compile' (x # var_idxs) (Suc depth) (length xacc) xacc True (length lib) lib e = 
    (lib'', ofst'', cd', sz'') \<Longrightarrow> 
      ofst'' + sz'' + maybe_return True = length lib + length xacc + tco_code_size True e"
        using compile_code_size by blast
  hence "compile' (x # var_idxs) (Suc depth) (length []) [] True (length lib) lib e = 
    (lib'', ofst'', cd', sz'') \<Longrightarrow> 
      ofst'' + sz'' + maybe_return True = length lib + length [] + tco_code_size True e"
        by (metis list.size(3))
  with C S have X: "Suc (length lib'' + length cd') = length lib + tco_code_size True e" by simp
  have "code_list_size (tco_cd ?cde) = tco_code_size True e" 
    by (metis tco_code_size_as_code_list_size)
  with C L S X show ?case by (cases var_idxs) simp_all
next
  case (NApp e1 e2)
  obtain lib1 ofst1 cd1 sz1 where X:
    "compile' var_idxs depth (length acc) acc False (length lib) lib e1 = (lib1, ofst1, cd1, sz1)"
      by (cases "compile' var_idxs depth (length acc) acc False (length lib) lib e1") blast+
  obtain lib2 ofst2 cd2 sz2 where Y:
    "compile' var_idxs depth sz1 cd1 False ofst1 lib1 e2 = (lib2, ofst2, cd2, sz2)"
    by (cases "compile' var_idxs depth sz1 cd1 False ofst1 lib1 e2") blast+


  from NApp X have "lib1 @ get_return depth e1 # cd1 = 
    lib @ flatten_code' (length lib) (tco_cd (encode' (convert' var_idxs e1) depth)) 
      (tco_r depth (encode' (convert' var_idxs e1) depth)) @ acc" by simp


  from X have "sz1 = length cd1 \<and> ofst1 = length lib1" by simp 
  with NApp Y have "lib2 @ get_return depth e2 # cd2 = 
    lib1 @ flatten_code' (length lib1) (tco_cd (encode' (convert' var_idxs e2) depth)) 
      (tco_r depth (encode' (convert' var_idxs e2) depth)) @ cd1" by simp



  show ?case
  proof (cases tail_pos)
    case True
  
  
    have "lib2 @ BJump depth # cd2 =
      lib @ flatten_code' (length lib) (map tco_cd_one (encode' (convert' var_idxs e1) depth) @
        map tco_cd_one (encode' (convert' var_idxs e2) depth)) (TCOJump depth) @ acc" by simp
    with NApp X Y True show ?thesis by simp
  next
    case False
  
  
    have "lib2 @ BJump depth # BApply # cd2 =
      lib @ flatten_code' (length lib) (map tco_cd_one (encode' (convert' var_idxs e1) depth) @
        map tco_cd_one (encode' (convert' var_idxs e2) depth)) (TCOJump depth) @ acc" by simp
    with NApp X Y False show ?thesis by simp
  qed
qed simp_all

lemma [simp]: "tco_cd (encode' e d) \<noteq> []"
  by (induction e) simp_all

lemma [simp]: "tco_cd (encode e) \<noteq> []"
  by (simp add: encode_def)

lemma compile_correct: "compile e = (cd, pc) \<Longrightarrow> 
  cd = flatten_code (tco (encode (convert e))) \<and> pc = length cd"
proof (unfold compile_def convert_def encode_def tco_def)
  obtain lib ofst cdb sz where C: "compile' [] 0 0 [] True 0 [] e = (lib, ofst, cdb, sz)"
    by (cases "compile' [] 0 0 [] True 0 [] e") blast+
  moreover assume "(let (lib, ofst, cdb, sz) = compile' [] 0 0 [] True 0 [] e
    in (lib @ get_return 0 e # cdb, Suc (ofst + sz))) = (cd, pc)"
  ultimately have X: "cd = lib @ get_return 0 e # cdb \<and> pc = Suc (ofst + sz)" by simp
  have "\<And>acc xlib. compile' [] 0 (length acc) acc True (length xlib) xlib e = 
    (lib, ofst, cdb, sz) \<Longrightarrow> lib @ get_return 0 e # cdb = 
      xlib @ flatten_code' (length xlib) (tco_cd (encode' (convert' [] e) 0)) 
        (tco_r 0 (encode' (convert' [] e) 0)) @ acc" by (metis compile_code)
  hence "compile' [] 0 (length []) [] True (length []) [] e = (lib, ofst, cdb, sz) \<Longrightarrow> 
    lib @ get_return 0 e # cdb = [] @ flatten_code' (length []) (tco_cd (encode' (convert' [] e) 0)) 
      (tco_r 0 (encode' (convert' [] e) 0)) @ []" by (metis list.size(3))
  with C have Y: "lib @ get_return 0 e # cdb = flatten_code' 0 (tco_cd (encode' (convert' [] e) 0)) 
    (tco_r 0 (encode' (convert' [] e) 0))" by simp
  have "\<And>acc xlib. compile' [] 0 (length acc) acc True (length xlib) xlib e = 
    (lib, ofst, cdb, sz) \<Longrightarrow> 
      ofst + sz + maybe_return True = length xlib + length acc + tco_code_size True e" 
        using compile_code_size by blast
  hence "compile' [] 0 (length []) [] True (length []) [] e = (lib, ofst, cdb, sz) \<Longrightarrow> 
    ofst + sz + maybe_return True = length [] + length [] + tco_code_size True e" 
      by (metis list.size(3))
  with C X Y show "cd = 
    flatten_code (tco_cd (encode' (convert' [] e) 0), tco_r 0 (encode' (convert' [] e) 0)) \<and> 
      pc = length cd" by simp
qed

theorem tc_terminationn: "typechecks e \<Longrightarrow> compile e = (cd, pc) \<Longrightarrow> 
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
  assume "compile e = (cd, pc)"
  hence C: "cd = flatten_code (tco (encode (convert e))) \<and> pc = length cd" 
    by (metis compile_correct)
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