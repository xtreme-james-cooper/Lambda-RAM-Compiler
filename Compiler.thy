theory Compiler
  imports "02Source/AlgorithmicTypechecking" Printing "04Stack/StackConversion" 
begin

abbreviation compile :: "nexpr \<Rightarrow> byte_code list" where 
  "compile \<equiv> flatten_code \<circ> tco \<circ> encode \<circ> convert"

lemma [simp]: "live_frame (env, tco_cd (encode e), tco_r (encode e))"
  by (induction e) simp_all

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
  with ED EN TD have ES: "iter (\<leadsto>\<^sub>s) (SS False [FReturn] (convert e)) (SS True [] (convert v\<^sub>n))" 
    by simp
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
  hence ET: "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS [] [([], tco_cd (encode (convert e)), tco_r (encode (convert e)))]) 
    (TCOS [tco_val (encode_closure c)] [])" by simp
  assume C: "compile e = cd"
  hence UB: "unflatten_state (BS [] [([], length cd)] cd) = 
    TCOS [] [([], tco_cd (encode (convert e)), tco_r (encode (convert e)))]" 
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