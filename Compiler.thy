theory Compiler
  imports Printing "04Stack/StackConversion" "12UnstructuredMemory/Unstructuring" 
begin

abbreviation compile :: "texpr \<Rightarrow> byte_code list" where 
  "compile \<equiv> flatten_code \<circ> tco \<circ> encode \<circ> convert"

lemma [simp]: "live_frame (env, tco_cd (encode e), tco_r (encode e))"
  by (induction e) simp_all

theorem tc_terminationn: "\<exists>t. Map.empty \<turnstile>\<^sub>n e : t \<Longrightarrow> compile e = cd \<Longrightarrow> 
  \<exists>v. valn v \<and> e \<Down> v \<and> 
    (\<exists>h hp e ep v\<^sub>u s. iter (\<leadsto>\<^sub>u) (US nmem 0 0 0 nmem 0 nmem 0 (nmem(0 := 0)) 1 (length cd) cd) 
      (US h hp 0 0 e ep v\<^sub>u 1 s 0 0 cd) \<and> print_uclosure h (v\<^sub>u 0) = print_texpr v)"
proof -
  assume "\<exists>t. Map.empty \<turnstile>\<^sub>n e : t"
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
  with VN have VC: "print_closure c = print_texpr v\<^sub>n" by simp
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
  with VC have VB: "print_bclosure v\<^sub>b = print_texpr v\<^sub>n" by simp
  from EB obtain \<Sigma>\<^sub>h' where EH: "iter (\<leadsto>\<^sub>h) (HS hempty [] [([], length cd)] cd) \<Sigma>\<^sub>h' \<and> 
    BS [v\<^sub>b] [] cd = unheap \<Sigma>\<^sub>h'" by fastforce
  then obtain h\<^sub>h v\<^sub>h where SH: "\<Sigma>\<^sub>h' = HS h\<^sub>h [v\<^sub>h] [] cd \<and> v\<^sub>b = unheap_closure h\<^sub>h v\<^sub>h" 
    using unheap_empty by blast
  with VB have VH: "print_hclosure (hlookup h\<^sub>h v\<^sub>h) = print_texpr v\<^sub>n" by simp
  have HS: "heap_structured (HS hempty [] [([], length cd)] cd)" by simp
  have CES: "unchain_state (CES hempty hempty [] [(0, length cd)] cd) = 
    HS hempty [] [([], length cd)] cd" by simp
  with EH SH obtain \<Sigma>\<^sub>c\<^sub>e' where ECE: "iter (\<leadsto>\<^sub>c\<^sub>e) (CES hempty hempty [] [(0, length cd)] cd) \<Sigma>\<^sub>c\<^sub>e' \<and> 
    HS h\<^sub>h [v\<^sub>h] [] cd = unchain_state \<Sigma>\<^sub>c\<^sub>e'" by fastforce
  then obtain h\<^sub>c\<^sub>e env\<^sub>h where VCE: "\<Sigma>\<^sub>c\<^sub>e' = CES h\<^sub>c\<^sub>e env\<^sub>h [v\<^sub>h] [] cd \<and> h\<^sub>h = unchain_heap h\<^sub>c\<^sub>e env\<^sub>h" 
    by (metis unchain_state_reverse map_is_Nil_conv)
  with VH have PCE: "print_ceclosure (hlookup h\<^sub>c\<^sub>e v\<^sub>h) = print_texpr v\<^sub>n" by (metis print_ce)
  from ECE VCE have "iter (\<leadsto>\<^sub>f) (flatten (CES hempty hempty [] [(0, length cd)] cd))
    (flatten (CES h\<^sub>c\<^sub>e env\<^sub>h [v\<^sub>h] [] cd))" by (metis completef_iter)
  hence EF: "iter (\<leadsto>\<^sub>f) (FS (H nmem 0) (H nmem 0) [] [length cd, 0] cd)
     (FS (flatten_values h\<^sub>c\<^sub>e) (flatten_environment env\<^sub>h) [v\<^sub>h] [] cd)" by (simp add: hempty_def)
  from PCE have PF: "print_ceclosure (get_closure (flatten_values h\<^sub>c\<^sub>e) v\<^sub>h) = print_texpr v\<^sub>n" 
    by (simp del: get_closure.simps)
  from C have "cd \<noteq> []" by auto
  with EF have "\<exists>\<Sigma>\<^sub>u'. iter (\<leadsto>\<^sub>u) (US nmem 0 0 0 nmem 0 nmem 0 (nmem(0 := 0)) 1 (length cd) cd) \<Sigma>\<^sub>u' \<and> 
    FS (flatten_values h\<^sub>c\<^sub>e) (flatten_environment env\<^sub>h) [v\<^sub>h] [] cd = restructure \<Sigma>\<^sub>u'" 
      by (cases cd) simp_all
  then obtain \<Sigma>\<^sub>u' where 
    "iter (\<leadsto>\<^sub>u) (US nmem 0 0 0 nmem 0 nmem 0 (nmem(0 := 0)) 1 (length cd) cd) \<Sigma>\<^sub>u' \<and> 
      FS (flatten_values h\<^sub>c\<^sub>e) (flatten_environment env\<^sub>h) [v\<^sub>h] [] cd = restructure \<Sigma>\<^sub>u'" by blast
  moreover then obtain h\<^sub>u hp\<^sub>u x\<^sub>u p\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u vp\<^sub>u sh\<^sub>u sp\<^sub>u where VU:
    "\<Sigma>\<^sub>u' = US h\<^sub>u hp\<^sub>u x\<^sub>u p\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u vp\<^sub>u sh\<^sub>u sp\<^sub>u 0 cd \<and> flatten_values h\<^sub>c\<^sub>e = H h\<^sub>u hp\<^sub>u \<and> 
      flatten_environment env\<^sub>h = H e\<^sub>u ep\<^sub>u \<and> listify' vs\<^sub>u vp\<^sub>u = v\<^sub>h # []" by auto
  moreover hence VSU: "vs\<^sub>u 0 = v\<^sub>h \<and> vp\<^sub>u = 1" by auto
  ultimately have "iter (\<leadsto>\<^sub>u) (US nmem 0 0 0 nmem 0 nmem 0 (nmem(0 := 0)) 1 (length cd) cd) 
    (US h\<^sub>u hp\<^sub>u x\<^sub>u p\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u 1 sh\<^sub>u sp\<^sub>u 0 cd)" by simp
  moreover hence "x\<^sub>u = 0 \<and> p\<^sub>u = 0 \<and> sp\<^sub>u = 0" by (metis evalu_clears_regs)
  ultimately have EU: "iter (\<leadsto>\<^sub>u) (US nmem 0 0 0 nmem 0 nmem 0 (nmem(0 := 0)) 1 (length cd) cd) 
    (US h\<^sub>u hp\<^sub>u 0 0 e\<^sub>u ep\<^sub>u vs\<^sub>u 1 sh\<^sub>u 0 0 cd)" by simp



  from PF VU VSU have PU: "print_uclosure h\<^sub>u (vs\<^sub>u 0) = print_texpr v\<^sub>n" by (metis print_u)




  with EN EU VN PU show ?thesis by blast
qed

end