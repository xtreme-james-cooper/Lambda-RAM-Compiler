theory Compiler
  imports "01Source/AlgorithmicTypechecking" Printing "03Stack/StackConversion" 
begin

definition compile :: "nexpr \<Rightarrow> byte_code list" where
  "compile = flatten_code \<circ> tco \<circ> encode \<circ> convert"

lemma [simp]: "tco_cd (encode' e d acc) \<noteq> []"
  by (induction e arbitrary: acc) simp_all

lemma [simp]: "tco_cd (encode e) \<noteq> []"
  by (simp add: encode_def)

theorem tc_terminationn: "typechecks e \<Longrightarrow> compile e = cd \<Longrightarrow> 
  \<exists>v. valn v \<and> iter (\<leadsto>\<^sub>n) e v \<and> 
    (\<exists>h v\<^sub>f. iter (\<leadsto>\<^sub>f) (FS hempty [] [[length cd]] cd) (FS h [v\<^sub>f] [] cd) \<and> 
      print_hclosure (get_closure h v\<^sub>f) = print_nexpr v)"
proof -
  assume "typechecks e"
  then obtain t where TN: "Map.empty \<turnstile>\<^sub>n e : t" by fastforce
  hence TD: "[] \<turnstile>\<^sub>d convert e : t" by simp
  then obtain v\<^sub>d where VD: "vald v\<^sub>d \<and> iter (\<leadsto>\<^sub>d) (convert e) v\<^sub>d" by fastforce
  with TN obtain v\<^sub>n where EN: "iter (\<leadsto>\<^sub>n) e v\<^sub>n \<and> v\<^sub>d = convert v\<^sub>n" by fastforce
  with VD have VN: "valn v\<^sub>n" by (metis convert_val_back)
  with VD EN TD have ES: "iter (\<leadsto>\<^sub>s) (SS [FReturn] (convert e)) (SS [] (convert v\<^sub>n))" by simp
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
  assume "compile e = cd"
  hence C: "flatten_code (tco (encode (convert e))) = cd" by (simp add: compile_def)
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