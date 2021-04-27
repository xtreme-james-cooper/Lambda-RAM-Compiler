theory Compiler
  imports Printing "04Stack/StackConversion" "12UnstructuredMemory/Unstructuring" 
    "13AssemblyCode/Assemble" 
begin

abbreviation compile :: "nexpr \<rightharpoonup> assm list" where 
  "compile \<equiv> map_option (fst \<circ> assemble \<circ> flatten_code \<circ> tco \<circ> encode \<circ> convert \<circ> fst) \<circ> typecheck"

lemma [simp]: "live_frame (env, tco_cd (encode e), tco_r (encode e))"
  by (induction e) simp_all

theorem tc_failure: "compile e = None \<Longrightarrow> \<nexists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> e = erase e\<^sub>t"
proof -
  assume "compile e = None"
  hence "typecheck e = None" by simp
  thus ?thesis by (metis typecheck_fails)
qed

theorem tc_terminationn: "compile e = Some cd \<Longrightarrow> 
  \<exists>v. valn v \<and> e \<Down> v \<and> (\<exists>rs mem. rs VP = 1 \<and> rs SP = 0 \<and> 
    print_uclosure (mem Hp) (mem Val 0) = print_nexpr v \<and>
      iter (\<tturnstile> cd \<leadsto>\<^sub>a) (AS ((\<lambda>r. 0)(SP := 1)) ((\<lambda>m. nmem)(Stk := nmem(0 := 0))) (length cd))
        (AS rs mem 0))"
proof -
  assume C: "compile e = Some cd"
  then obtain e\<^sub>t t where T: "typecheck e = Some (e\<^sub>t, t)" by fastforce
  hence TN: "(Map.empty \<turnstile>\<^sub>n e\<^sub>t : t) \<and> e = erase e\<^sub>t" by simp
  then obtain v\<^sub>t where ET: "e\<^sub>t \<Down>\<^sub>t v\<^sub>t" by fastforce
  hence VT: "valt v\<^sub>t" by simp
  hence VN: "valn (erase v\<^sub>t)" by simp
  from ET have EN: "erase e\<^sub>t \<Down> erase v\<^sub>t" by simp
  from TN have TD: "[] \<turnstile>\<^sub>d convert e\<^sub>t : t" by simp
  from ET TN have ED: "convert e\<^sub>t \<Down>\<^sub>d convert v\<^sub>t" by fastforce
  hence VD: "vald (convert v\<^sub>t)" by simp
  from ED have "iter (\<leadsto>\<^sub>d) (convert e\<^sub>t) (convert v\<^sub>t)" by (metis BigStep.correctb)
  with ED EN TD have ES: "iter (\<leadsto>\<^sub>s) (SS False [FReturn] (convert e\<^sub>t)) (SS True [] (convert v\<^sub>t))" 
    by simp
  from TD have TC: "CSE [CReturn []] [] (convert e\<^sub>t) :\<^sub>c t" 
    by (metis tcc_state_ev tcc_nil tcc_snil tcc_scons_ret latest_environment.simps(4))
  with ES VD EN obtain c where EC: "iter (\<leadsto>\<^sub>c) (CSE [CReturn []] [] (convert e\<^sub>t)) (CSC [] c) \<and> 
    declosure c = convert v\<^sub>t" by fastforce
  with VT have VC: "print_closure c = print_nexpr (erase v\<^sub>t)" by simp
  from TC EC have "iter (\<leadsto>\<^sub>t) (encode_state (CSE [CReturn []] [] (convert e\<^sub>t))) 
    (encode_state (CSC [] c))" by (metis iter_completet)
  hence "iter (\<leadsto>\<^sub>t) (TS [] [([], encode (convert e\<^sub>t))]) (TS [encode_closure c] [])" 
    by (simp add: encode_def)
  hence "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (tco_state (TS [] [([], encode (convert e\<^sub>t))])) 
    (tco_state (TS [encode_closure c] []))" by (metis iter_tco_eval)
  hence ET: "iter (\<leadsto>\<^sub>t\<^sub>c\<^sub>o) (TCOS [] [([], tco_cd (encode (convert e\<^sub>t)), tco_r (encode (convert e\<^sub>t)))]) 
    (TCOS [tco_val (encode_closure c)] [])" by simp
  let ?cd = "(flatten_code \<circ> tco \<circ> encode \<circ> convert) e\<^sub>t"
  have UB: "unflatten_state ?cd (BS [] [([], length ?cd)]) = 
    TCOS [] [([], tco_cd (encode (convert e\<^sub>t)), tco_r (encode (convert e\<^sub>t)))]" 
      by (auto simp add: tco_def simp del: flatten_code.simps)
  have "orderly_state ?cd (BS [] [([], length ?cd)])" by auto
  with ET UB obtain v\<^sub>b where EB: "iter (\<tturnstile> ?cd \<leadsto>\<^sub>b) (BS [] [([], length ?cd)]) (BS [v\<^sub>b] []) \<and> 
    tco_val (encode_closure c) = unflatten_closure ?cd v\<^sub>b" by (metis evalb_end)
  hence "print_bclosure v\<^sub>b = print_tco_closure (tco_val (encode_closure c))" by simp
  with VC have VB: "print_bclosure v\<^sub>b = print_nexpr (erase v\<^sub>t)" by simp
  from EB obtain \<Sigma>\<^sub>h' where EH: "iter (\<tturnstile> ?cd \<leadsto>\<^sub>h) (HS hempty [] [([], length ?cd)]) \<Sigma>\<^sub>h' \<and> 
    BS [v\<^sub>b] [] = unheap \<Sigma>\<^sub>h'" by fastforce
  then obtain h\<^sub>h v\<^sub>h where SH: "\<Sigma>\<^sub>h' = HS h\<^sub>h [v\<^sub>h] [] \<and> v\<^sub>b = unheap_closure h\<^sub>h v\<^sub>h" 
    using unheap_empty by blast
  with VB have VH: "print_hclosure (hlookup h\<^sub>h v\<^sub>h) = print_nexpr (erase v\<^sub>t)" by simp
  have HS: "heap_structured (HS hempty [] [([], length ?cd)])" by simp
  have CES: "unchain_state (CES hempty hempty [] [(0, length ?cd)]) = 
    HS hempty [] [([], length ?cd)]" by simp
  with EH SH obtain \<Sigma>\<^sub>c\<^sub>e' where ECE: "iter (\<tturnstile> ?cd \<leadsto>\<^sub>c\<^sub>e) 
    (CES hempty hempty [] [(0, length ?cd)]) \<Sigma>\<^sub>c\<^sub>e' \<and> HS h\<^sub>h [v\<^sub>h] [] = unchain_state \<Sigma>\<^sub>c\<^sub>e'" by fastforce
  then obtain h\<^sub>c\<^sub>e env\<^sub>h where VCE: "\<Sigma>\<^sub>c\<^sub>e' = CES h\<^sub>c\<^sub>e env\<^sub>h [v\<^sub>h] [] \<and> h\<^sub>h = unchain_heap h\<^sub>c\<^sub>e env\<^sub>h" 
    by (metis unchain_state_reverse map_is_Nil_conv)
  with VH have PCE: "print_ceclosure (hlookup h\<^sub>c\<^sub>e v\<^sub>h) = print_nexpr (erase v\<^sub>t)" by (metis print_ce)
  from ECE VCE have "iter (\<tturnstile> ?cd \<leadsto>\<^sub>f) (flatten (CES hempty hempty [] [(0, length ?cd)]))
    (flatten (CES h\<^sub>c\<^sub>e env\<^sub>h [v\<^sub>h] []))" by (metis completef_iter)
  hence EF: "iter (\<tturnstile> ?cd \<leadsto>\<^sub>f) (FS (H nmem 0) (H nmem 0) [] [length ?cd, 0])
     (FS (flatten_values h\<^sub>c\<^sub>e) (flatten_environment env\<^sub>h) [v\<^sub>h] [])" by (simp add: hempty_def)
  from PCE have PF: "print_ceclosure (get_closure (flatten_values h\<^sub>c\<^sub>e) v\<^sub>h) = print_nexpr (erase v\<^sub>t)" 
    by (simp del: get_closure.simps)
  from C have "?cd \<noteq> []" by auto
  with EF have "\<exists>\<Sigma>\<^sub>u'. 
    iter (\<tturnstile> ?cd \<leadsto>\<^sub>u) (US nmem 0 nmem 0 nmem 0 (nmem(0 := 0)) 1 (length ?cd)) \<Sigma>\<^sub>u' \<and> 
      FS (flatten_values h\<^sub>c\<^sub>e) (flatten_environment env\<^sub>h) [v\<^sub>h] [] = restructure \<Sigma>\<^sub>u'"
        by (cases ?cd) simp_all
  then obtain \<Sigma>\<^sub>u' where 
    "iter (\<tturnstile> ?cd \<leadsto>\<^sub>u) (US nmem 0 nmem 0 nmem 0 (nmem(0 := 0)) 1 (length ?cd)) \<Sigma>\<^sub>u' \<and> 
      FS (flatten_values h\<^sub>c\<^sub>e) (flatten_environment env\<^sub>h) [v\<^sub>h] [] = restructure \<Sigma>\<^sub>u'" by blast
  moreover then obtain h\<^sub>u hp\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u vp\<^sub>u sh\<^sub>u sp\<^sub>u where VU:
    "\<Sigma>\<^sub>u' = US h\<^sub>u hp\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u vp\<^sub>u sh\<^sub>u sp\<^sub>u 0 \<and> flatten_values h\<^sub>c\<^sub>e = H h\<^sub>u hp\<^sub>u \<and> 
      flatten_environment env\<^sub>h = H e\<^sub>u ep\<^sub>u \<and> listify' vs\<^sub>u vp\<^sub>u = v\<^sub>h # []" by auto
  moreover hence VSU: "vs\<^sub>u 0 = v\<^sub>h \<and> vp\<^sub>u = 1" by auto
  ultimately have "iter (\<tturnstile> ?cd \<leadsto>\<^sub>u) (US nmem 0 nmem 0 nmem 0 (nmem(0 := 0)) 1 (length ?cd)) 
    (US h\<^sub>u hp\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u 1 sh\<^sub>u sp\<^sub>u 0)" by simp
  moreover hence "sp\<^sub>u = 0" by (metis evalu_clears_regs)
  ultimately have EU: "iter (\<tturnstile> ?cd \<leadsto>\<^sub>u) (US nmem 0 nmem 0 nmem 0 (nmem(0 := 0)) 1 (length ?cd)) 
    (US h\<^sub>u hp\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u 1 sh\<^sub>u 0 0)" by simp
  let ?mem = "(\<lambda>m. case m of Hp \<Rightarrow> h\<^sub>u | Env \<Rightarrow> e\<^sub>u | Val \<Rightarrow> vs\<^sub>u | Stk \<Rightarrow> sh\<^sub>u)"
  let ?rs = "(\<lambda>r. case r of HP \<Rightarrow> hp\<^sub>u | EP \<Rightarrow> ep\<^sub>u | VP \<Rightarrow> Suc 0 | SP \<Rightarrow> 0)"

  from C T obtain mp where "assemble ?cd = (cd, mp)" by (cases "assemble ?cd") simp_all
  with EU have "iter (\<tturnstile> cd \<leadsto>\<^sub>a) 
    (assemble_state mp (US nmem 0 nmem 0 nmem 0 (nmem(0 := 0)) 1 (length ?cd))) 
      (assemble_state mp (US h\<^sub>u hp\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u 1 sh\<^sub>u 0 0))" by (metis correcta_iter)
  hence EA: "iter (\<tturnstile> cd \<leadsto>\<^sub>a) (AS ((\<lambda>r. 0)(SP := 1)) ((\<lambda>m. nmem)(Stk := nmem(0 := 0))) (length cd))
    (AS ?rs ?mem 0)" by simp


  from PF VU VSU have "print_uclosure h\<^sub>u (vs\<^sub>u 0) = print_nexpr (erase v\<^sub>t)" by (metis print_u)
  hence PA: "print_uclosure (?mem Hp) (?mem Val 0) = print_nexpr (erase v\<^sub>t)" by simp



  have "?rs VP = 1 \<and> ?rs SP = 0" by simp
  with VN TN EN EA PA show ?thesis by blast
qed

end