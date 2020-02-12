theory Compiler
  imports "01Source/AlgorithmicTypechecking" Printing "03Stack/StackConversion" 
begin

definition compile :: "nexpr \<Rightarrow> byte_code list" where
  "compile = flatten_code \<circ> tco \<circ> encode \<circ> convert"

primrec one_pass_r' :: "nat \<Rightarrow> nexpr \<Rightarrow> tco_return" where
  "one_pass_r' d (NVar x) = TCOReturn d"
| "one_pass_r' d (NConst k) = TCOReturn d"
| "one_pass_r' d (NLam x t e) = TCOReturn d"
| "one_pass_r' d (NApp e\<^sub>1 e\<^sub>2) = TCOJump d"

primrec one_pass_cd' :: "var list \<Rightarrow> nat \<Rightarrow> tco_code list \<Rightarrow> bool \<Rightarrow> nexpr \<Rightarrow> tco_code list" where
  "one_pass_cd' \<Phi> d cd b (NVar x) = TCOLookup (the (idx_of \<Phi> x)) # cd"
| "one_pass_cd' \<Phi> d cd b (NConst k) = TCOPushCon k # cd"
| "one_pass_cd' \<Phi> d cd b (NLam x t e) = 
    TCOPushLam (one_pass_cd' (insert_at 0 x \<Phi>) (Suc d) [] True e) (one_pass_r' (Suc d) e) d # cd"
| "one_pass_cd' \<Phi> d cd b (NApp e\<^sub>1 e\<^sub>2) = 
    one_pass_cd' \<Phi> d (one_pass_cd' \<Phi> d (if b then cd else TCOApply # cd) False e\<^sub>2) False e\<^sub>1"

definition one_pass :: "nexpr \<Rightarrow> tco_code list \<times> tco_return" where
  "one_pass e = (one_pass_cd' [] 0 [] True e, one_pass_r' 0 e)"

lemma [simp]: "one_pass_r' d e = tco_r d (encode' (convert' \<Phi> e) d' [])"
proof (induction e arbitrary: \<Phi> d)
  case (NApp e1 e2)
  have "tco_r d ((encode' (convert' \<Phi> e1) d' [] @ encode' (convert' \<Phi> e2) d' []) @ [TApply]) = 
    tco_r d [TApply]" using tco_r_append by blast
  thus ?case by simp
qed simp_all

lemma one_pass_cd_correct [simp]: "cd' = tco_cd cd \<Longrightarrow> 
  one_pass_cd' \<Phi> d cd' (cd = []) e = tco_cd (encode' (convert' \<Phi> e) d cd)"
proof (induction e arbitrary: \<Phi> d cd cd')
  case (NLam x t e)
  moreover have "[] = tco_cd []" by simp
  ultimately have "one_pass_cd' (insert_at 0 x \<Phi>) (Suc d) [] True e =
    tco_cd (encode' (convert' (insert_at 0 x \<Phi>) e) (Suc d) [])" by (metis (full_types))
  with NLam show ?case by simp
next
  case (NApp e1 e2)
  hence "(if cd = [] then cd' else TCOApply # cd') = tco_cd (TApply # cd)" 
    by (simp split: list.splits)
  with NApp have "one_pass_cd' \<Phi> d (if cd = [] then cd' else TCOApply # cd') 
    (TApply # cd = []) e2 = 
      tco_cd (encode' (convert' \<Phi> e2) d (TApply # cd))" by blast
  moreover from NApp have "one_pass_cd' \<Phi> d (tco_cd (encode' (convert' \<Phi> e2) d (TApply # cd))) 
    (encode' (convert' \<Phi> e2) d (TApply # cd) = []) e1 = 
      tco_cd (encode' (convert' \<Phi> e1) d (encode' (convert' \<Phi> e2) d (TApply # cd)))" by blast
  ultimately show ?case by simp
qed simp_all

lemma [simp]: "one_pass = tco \<circ> encode \<circ> convert"
proof (rule, unfold one_pass_def tco_def encode_def convert_def)
  fix e
  have "[] = tco_cd []" by simp
  hence "one_pass_cd' [] 0 [] ([] = []) e = tco_cd (encode' (convert' [] e) 0 [])" 
    by (metis (full_types) one_pass_cd_correct)
  thus "(one_pass_cd' [] 0 [] True e, one_pass_r' 0 e) =
    ((\<lambda>cd. (tco_cd cd, tco_r 0 cd)) \<circ> (\<lambda>e. encode' e 0 []) \<circ> convert' []) e" by simp
qed

lemma [simp]: "tco_cd (encode' e d acc) \<noteq> []"
  by (induction e arbitrary: acc) simp_all

lemma [simp]: "tco_cd (encode e) \<noteq> []"
  by (simp add: encode_def)

theorem tc_terminationn: "typechecks e \<Longrightarrow> compile e = cd \<Longrightarrow> 
  \<exists>v. valn v \<and> e \<Down> v \<and> 
    (\<exists>h v\<^sub>f. iter (\<leadsto>\<^sub>f) (FS hempty [] [[length cd]] cd) (FS h [v\<^sub>f] [] cd) \<and> 
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
  assume "compile e = cd"
  hence C: "flatten_code (tco (encode (convert e))) = cd" by (simp add: compile_def)
  hence UB: "unflatten_state (BS [] [([], length cd)] cd) = 
    TCOS [] [([], tco_cd (encode (convert e)), tco_r 0 (encode (convert e)))]" 
      by (auto simp add: tco_def simp del: flatten_code.simps)
  from C have "orderly_state (BS [] [([], length cd)] cd)" by auto
  with ET UB obtain v\<^sub>b where EB: 
    "iter (\<leadsto>\<^sub>b) (BS [] [([], length cd)] cd) (BS [v\<^sub>b] [] cd) \<and> 
      tco_val (encode_closure c) = unflatten_closure cd v\<^sub>b" 
    by (metis evalb_end byte_code_state.sel(3))
  hence "print_bclosure v\<^sub>b = print_tco_closure (tco_val (encode_closure c))" by simp
  with VC have VB: "print_bclosure v\<^sub>b = print_nexpr v\<^sub>n" by simp
  from EB obtain \<Sigma>\<^sub>h' where EH: "iter (\<leadsto>\<^sub>h) (HS hempty [] [([], length cd)] cd) \<Sigma>\<^sub>h' \<and> 
    BS [v\<^sub>b] [] cd = unheap \<Sigma>\<^sub>h'" by fastforce
  then obtain h\<^sub>h v\<^sub>h where SH: "\<Sigma>\<^sub>h' = HS h\<^sub>h [v\<^sub>h] [] cd \<and> v\<^sub>b = unheap_closure h\<^sub>h v\<^sub>h" 
    using unheap_empty by blast
  with VB have VH: "print_hclosure (hlookup h\<^sub>h v\<^sub>h) = print_nexpr v\<^sub>n" by simp
  have HS: "heap_structured (HS hempty [] [([], length cd)] cd)" by simp
  have FS: "flatten (HS hempty [] [([], length cd)] cd) = FS hempty [] [[length cd]] cd" by simp
  obtain h\<^sub>f mp where HC: "hsplay splay_closure h\<^sub>h = (h\<^sub>f, mp)" by fastforce
  with SH have "flatten \<Sigma>\<^sub>h' = FS h\<^sub>f [mp v\<^sub>h] [] cd" by simp
  with EH FS HS have EF: "iter (\<leadsto>\<^sub>f) (FS hempty [] [[length cd]] cd) (FS h\<^sub>f [mp v\<^sub>h] [] cd)"
    by (metis completef_iter)
  from EH have "heap_structured \<Sigma>\<^sub>h'" by fastforce
  with SH have "hcontains h\<^sub>h v\<^sub>h" by simp
  with HC have "get_closure h\<^sub>f (mp v\<^sub>h) = flatten_closure mp (hlookup h\<^sub>h v\<^sub>h)" 
    by (metis get_closure_flatten)
  with VH have VF: "print_hclosure (get_closure h\<^sub>f (mp v\<^sub>h)) = print_nexpr v\<^sub>n" 
    by (simp del: get_closure.simps)



  from EF VF have "iter (\<leadsto>\<^sub>f) (FS hempty [] [[length cd]] cd) (FS h\<^sub>f [mp v\<^sub>h] [] cd) \<and> 
    print_hclosure (get_closure h\<^sub>f (mp v\<^sub>h)) = print_nexpr v\<^sub>n" by simp
  with EN VN show ?thesis by fastforce
qed

end