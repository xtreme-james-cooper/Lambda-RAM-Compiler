theory Correctness
  imports Compiler
begin

abbreviation initial_state :: "mach list \<Rightarrow> mach_state" where
  "initial_state cd \<equiv> MS (case_reg 0 1 2 11 0) ((\<lambda>x. 0)(7 := 1)) (length cd)"

primrec final_state :: "mach_state \<Rightarrow> bool" where
  "final_state (MS rs mem pc) = (pc = 0 \<and> rs R3 = 6 \<and> rs R4 = 3)"

theorem tc_failure: "alg_compile e = None \<Longrightarrow> 
  \<nexists>e\<^sub>t t. (Map.empty \<turnstile>\<^sub>t e\<^sub>t : t) \<and> e = erase e\<^sub>t"
proof -
  assume "alg_compile e = None"
  hence "typecheck e = None" by (auto split: option.splits prod.splits)
  thus ?thesis by (metis typecheck_fails)
qed

lemma [simp]: "properly_terminated\<^sub>e (cd @ [Apply\<^sub>e, Return\<^sub>e]) = properly_terminated\<^sub>e (cd @ [Return\<^sub>e])"
  by (induction cd rule: properly_terminated\<^sub>e.induct) simp_all

lemma [simp]: "properly_terminated\<^sub>e (e1 @ [Return\<^sub>e]) \<Longrightarrow> properly_terminated\<^sub>e (e2 @ [Return\<^sub>e]) \<Longrightarrow> 
    properly_terminated\<^sub>e (e1 @ e2 @ [Apply\<^sub>e, Return\<^sub>e])"
  by (induction e1 rule: properly_terminated\<^sub>e.induct) simp_all

lemma [simp]: "properly_terminated\<^sub>e (encode e)"
  by (induction e) (simp_all add: encode_def)


theorem tc_success: "alg_compile e = Some (cd, t) \<Longrightarrow> \<exists>e\<^sub>t. (Map.empty \<turnstile>\<^sub>t e\<^sub>t : t) \<and> erase e\<^sub>t = e \<and>
  (\<exists>v. value\<^sub>s v \<and> e \<Down>\<^sub>s v \<and> (\<exists>\<Sigma>. final_state \<Sigma> \<and> iter (\<tturnstile> cd \<leadsto>\<^sub>m) (initial_state cd) \<Sigma> \<and> 
    print_mach_state \<Sigma> = print_nexpr v))"
proof -
  assume C: "alg_compile e = Some (cd, t)"
  then obtain e\<^sub>t where T: "typecheck e = Some (e\<^sub>t, t)" by (auto split: option.splits prod.splits)
  hence TN: "(Map.empty \<turnstile>\<^sub>t e\<^sub>t : t) \<and> e = erase e\<^sub>t" by simp
  then obtain v\<^sub>t where ET: "e\<^sub>t \<Down>\<^sub>s v\<^sub>t" by fastforce
  hence VT: "value\<^sub>s v\<^sub>t" by simp
  hence VN: "value\<^sub>s (erase v\<^sub>t)" by simp
  from ET have EN: "erase e\<^sub>t \<Down>\<^sub>s erase v\<^sub>t" by simp
  from TN have TD: "[] \<turnstile>\<^sub>d unname e\<^sub>t : t" by simp
  from ET TN have ED: "unname e\<^sub>t \<Down>\<^sub>d unname v\<^sub>t" by fastforce
  hence VD: "value\<^sub>d (unname v\<^sub>t)" by simp
  from ED have "iter (\<leadsto>\<^sub>d) (unname e\<^sub>t) (unname v\<^sub>t)" by (metis correct\<^sub>d\<^sub>b)
  with ED EN TD have ES: "iter (\<leadsto>\<^sub>k) (S\<^sub>k False [FReturn\<^sub>k] (unname e\<^sub>t)) (S\<^sub>k True [] (unname v\<^sub>t))" 
    by simp
  from TD have TC: "SE\<^sub>c [FReturn\<^sub>c []] [] (unname e\<^sub>t) :\<^sub>c t" 
    by (metis tcc_state_ev tc\<^sub>c_nil tcc_snil tcc_scons_ret latest_environment.simps(4))
  with ES VD EN obtain c where EC: "iter (\<leadsto>\<^sub>c) (SE\<^sub>c [FReturn\<^sub>c []] [] (unname e\<^sub>t)) (SC\<^sub>c [] c) \<and> 
    declosure c = unname v\<^sub>t" by fastforce
  from TC EC have "iter (\<leadsto>\<^sub>e) (encode_state (SE\<^sub>c [FReturn\<^sub>c []] [] (unname e\<^sub>t))) 
    (encode_state (SC\<^sub>c [] c))" by (metis correct\<^sub>e_iter)
  hence "iter (\<leadsto>\<^sub>e) (S\<^sub>e [] [([], encode (unname e\<^sub>t))]) (S\<^sub>e [encode_closure c] [])" 
    by (simp add: encode_def)
  moreover have "complete_lams_state (S\<^sub>e [] [([], encode (unname e\<^sub>t))])" by simp
  ultimately have "iter (\<leadsto>\<^sub>e) (tco_state (S\<^sub>e [] [([], encode (unname e\<^sub>t))])) 
    (tco_state (S\<^sub>e [encode_closure c] []))" by (metis correctness\<^sub>t\<^sub>c\<^sub>o_iter)
  hence ET: "iter (\<leadsto>\<^sub>e) (S\<^sub>e [] [([], tco_code (encode (unname e\<^sub>t)))]) 
    (S\<^sub>e [tco_val (encode_closure c)] [])" by (simp add: encode_def)
  let ?cd = "(flatten_code \<circ> tco_code \<circ> encode \<circ> unname) e\<^sub>t"
  have UB: "unflatten_state ?cd (S\<^sub>b [] [([], length ?cd)]) = 
    S\<^sub>e [] [([], tco_code (encode (unname e\<^sub>t)))]" by simp
  have "orderly_state ?cd (S\<^sub>b [] [([], length ?cd)])" by simp
  with ET UB obtain v\<^sub>b where EB: "iter (\<tturnstile> ?cd \<leadsto>\<^sub>b) (S\<^sub>b [] [([], length ?cd)]) (S\<^sub>b [v\<^sub>b] []) \<and> 
    tco_val (encode_closure c) = unflatten_closure ?cd v\<^sub>b" by (metis eval\<^sub>b_end)
  then obtain \<Sigma>\<^sub>h' where EH: "iter (\<tturnstile> ?cd \<leadsto>\<^sub>h) (S\<^sub>h hempty [] [([], length ?cd)]) \<Sigma>\<^sub>h' \<and> 
    S\<^sub>b [v\<^sub>b] [] = unheap \<Sigma>\<^sub>h'" by fastforce
  then obtain h\<^sub>h v\<^sub>h where SH: "\<Sigma>\<^sub>h' = S\<^sub>h h\<^sub>h [v\<^sub>h] [] \<and> v\<^sub>b = unheap_closure h\<^sub>h v\<^sub>h" 
    using unheap_to_empty by blast
  have S\<^sub>h: "heap_structured (S\<^sub>h hempty [] [([], length ?cd)])" by simp
  have S\<^sub>v: "unchain_state (S\<^sub>v hempty hempty [] [(0, length ?cd)]) = 
    S\<^sub>h hempty [] [([], length ?cd)]" by simp
  with EH SH obtain \<Sigma>\<^sub>c\<^sub>e' where ECE: "iter (\<tturnstile> ?cd \<leadsto>\<^sub>v) 
    (S\<^sub>v hempty hempty [] [(0, length ?cd)]) \<Sigma>\<^sub>c\<^sub>e' \<and> S\<^sub>h h\<^sub>h [v\<^sub>h] [] = unchain_state \<Sigma>\<^sub>c\<^sub>e'" by fastforce
  then obtain h\<^sub>c\<^sub>e env\<^sub>h where VCE: "\<Sigma>\<^sub>c\<^sub>e' = S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>h [v\<^sub>h] [] \<and> h\<^sub>h = unchain_heap h\<^sub>c\<^sub>e env\<^sub>h" 
    by (metis unchain_state_reverse map_is_Nil_conv)
  let ?nmem = "\<lambda>x. undefined"
  have CS: "chained_state (S\<^sub>v hempty hempty [] [(0, length ?cd)])" by simp
  with ECE VCE have "iter (\<tturnstile> ?cd \<leadsto>\<^sub>f) (flatten (S\<^sub>v hempty hempty [] [(0, length ?cd)]))
    (flatten (S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>h [v\<^sub>h] []))" by (metis correct\<^sub>f_iter)
  hence EF: "iter (\<tturnstile> ?cd \<leadsto>\<^sub>f) (S\<^sub>f (H ?nmem 0) (H ?nmem 0) [] [length ?cd, 0])
     (S\<^sub>f (flatten_values h\<^sub>c\<^sub>e) (flatten_environment env\<^sub>h) [3 * v\<^sub>h] [])" by (simp add: hempty_def)
  with ECE CS have "chained_state \<Sigma>\<^sub>c\<^sub>e'" by (metis preserve_chained)
  with VCE have VH: "hcontains h\<^sub>c\<^sub>e v\<^sub>h" by simp
  have R: "restructurable (S\<^sub>u ?nmem 0 ?nmem 0 ?nmem 0 (?nmem(0 := 0, 1 := 0)) 2 (length ?cd)) ?cd" 
    by simp
  with EF have "\<exists>\<Sigma>\<^sub>u'. 
    iter (\<tturnstile> ?cd \<leadsto>\<^sub>u) (S\<^sub>u ?nmem 0 ?nmem 0 ?nmem 0 (?nmem(0 := 0, 1 := 0)) 2 (length ?cd)) \<Sigma>\<^sub>u' \<and>
      S\<^sub>f (flatten_values h\<^sub>c\<^sub>e) (flatten_environment env\<^sub>h) [3 * v\<^sub>h] [] = restructure \<Sigma>\<^sub>u'" by simp_all
  then obtain \<Sigma>\<^sub>u' where EU:
    "iter (\<tturnstile> ?cd \<leadsto>\<^sub>u) (S\<^sub>u ?nmem 0 ?nmem 0 ?nmem 0 (?nmem(0 := 0, 1 := 0)) 2 (length ?cd)) \<Sigma>\<^sub>u' \<and> 
      S\<^sub>f (flatten_values h\<^sub>c\<^sub>e) (flatten_environment env\<^sub>h) [3 * v\<^sub>h] [] = restructure \<Sigma>\<^sub>u'" by blast
  moreover with R have R': "restructurable \<Sigma>\<^sub>u' ?cd" by fastforce
  moreover with EU obtain h\<^sub>u hp\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u vp\<^sub>u sh\<^sub>u where VU:
    "\<Sigma>\<^sub>u' = S\<^sub>u h\<^sub>u hp\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u vp\<^sub>u sh\<^sub>u 0 0 \<and> flatten_values h\<^sub>c\<^sub>e = H h\<^sub>u hp\<^sub>u \<and> 
      flatten_environment env\<^sub>h = H e\<^sub>u ep\<^sub>u \<and> listify_heap vs\<^sub>u vp\<^sub>u = 3 * v\<^sub>h # []" by auto
  moreover hence VSU: "vs\<^sub>u 0 = 3 * v\<^sub>h \<and> vp\<^sub>u = 1" by auto
  ultimately have "iter (\<tturnstile> ?cd \<leadsto>\<^sub>u) (S\<^sub>u ?nmem 0 ?nmem 0 ?nmem 0 (?nmem(0 := 0, 1 := 0)) 2 
    (length ?cd)) (S\<^sub>u h\<^sub>u hp\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u 1 sh\<^sub>u 0 0)" by simp
  hence EU: "iter (\<tturnstile> ?cd \<leadsto>\<^sub>u) (S\<^sub>u ?nmem 0 ?nmem 0 ?nmem 0 (?nmem(0 := 0, 1 := 0)) 2 (length ?cd)) 
    (S\<^sub>u h\<^sub>u hp\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u 1 sh\<^sub>u 0 0)" by simp
  let ?cd' = "assemble_code ?cd"
  let ?mp = "assembly_map ?cd"
  let ?mem = "case_register (assm_hp ?cd h\<^sub>u hp\<^sub>u) (assemble_env e\<^sub>u ep\<^sub>u) (assemble_vals vs\<^sub>u 1) 
    (assm_stk ?cd sh\<^sub>u 0)"
  let ?rs = "case_register hp\<^sub>u ep\<^sub>u (Suc 0) 0"
  from R EU have "iter (\<tturnstile> ?cd' \<leadsto>\<^sub>a) 
    (assemble_state ?mp (S\<^sub>u ?nmem 0 ?nmem 0 ?nmem 0 (?nmem(0 := 0, 1 := 0)) 2 (length ?cd))) 
      (assemble_state ?mp (S\<^sub>u h\<^sub>u hp\<^sub>u e\<^sub>u ep\<^sub>u vs\<^sub>u 1 sh\<^sub>u 0 0))" by (metis correct\<^sub>a_iter)
  hence "iter (\<tturnstile> ?cd' \<leadsto>\<^sub>a) (AS (case_register (assm_hp ?cd ?nmem 0) (assemble_env ?nmem 0)
    (assemble_vals ?nmem 0) (assm_stk ?cd (?nmem(0 := 0, 1 := 0)) 2)) (case_register 0 0 0 2) 0 
      None (length ?cd')) (AS ?mem ?rs 0 None 0)" by simp
  hence "iter (\<tturnstile> disassemble ?cd' \<leadsto>\<^sub>m) 
    (disassemble_state (AS (case_register (assm_hp ?cd ?nmem 0) (assemble_env ?nmem 0)
      (assemble_vals ?nmem 0) (assm_stk ?cd (?nmem(0 := 0, 1 := 0)) 2)) (case_register 0 0 0 2) 0 
        None (length ?cd'))) (disassemble_state (AS ?mem ?rs 0 None 0))" 
    by (metis correctm_iter)
  hence "iter (\<tturnstile> disassemble ?cd' \<leadsto>\<^sub>m) (MS (case_reg 0 1 2 11 0)
    (unmap_mem (case_register (\<lambda>x. (None, 0)) (\<lambda>x. (None, 0)) (\<lambda>x. (None, 0)) 
      ((\<lambda>x. (None, 0))(0 := (None, 0), Suc 0 := (Some Env, 0))))) (length ?cd')) 
        (MS (case_reg (4 * hp\<^sub>u) (Suc (4 * ep\<^sub>u)) 6 3 0) (unmap_mem ?mem) 0)" 
    by simp
  with C T have EM: "iter (\<tturnstile> cd \<leadsto>\<^sub>m) (MS (case_reg 0 1 2 11 0) ((\<lambda>x. 0)(7 := 1)) 
    (length cd)) (MS (case_reg (4 * hp\<^sub>u) (Suc (4 * ep\<^sub>u)) 6 3 0) (unmap_mem ?mem) 0)" by auto
  from EC VT have "print_closure c = print_nexpr (erase v\<^sub>t)" by simp
  moreover from EB have "print_bclosure v\<^sub>b = print_eclosure (tco_val (encode_closure c))" by simp
  ultimately have "print_bclosure v\<^sub>b = print_nexpr (erase v\<^sub>t)" by simp
  with SH have "print_hclosure (hlookup h\<^sub>h v\<^sub>h) = print_nexpr (erase v\<^sub>t)" by simp
  with VCE VH have "print_ceclosure (hlookup h\<^sub>c\<^sub>e v\<^sub>h) = print_nexpr (erase v\<^sub>t)" by (metis print_ce)
  with VH have "print_ceclosure (get_closure (flatten_values h\<^sub>c\<^sub>e) (3 * v\<^sub>h)) = print_nexpr (erase v\<^sub>t)" 
    by (simp del: get_closure.simps)
  with VU VSU have PU: "print_uval (snd \<circ> h\<^sub>u) (vs\<^sub>u 0) = print_nexpr (erase v\<^sub>t)" by (metis print_u)
  from VH VU VSU have SH: "Suc (vs\<^sub>u 0) < hp\<^sub>u" by (metis flatten_lt_3)
  from VSU have V3: "3 dvd vs\<^sub>u 0" by simp
  with SH have PU2: "print_uval (pseudoreg_map \<circ> assm_hp ?cd h\<^sub>u hp\<^sub>u) (vs\<^sub>u 0) = 
    print_uval (snd \<circ> h\<^sub>u) (vs\<^sub>u 0)" by (metis print_a)
  have "unmap_mem' (unmap_mem ?mem 2) = (Hp, vs\<^sub>u 0)" 
  proof (induction "vs\<^sub>u 0")
    case (Suc x)
    hence "vs\<^sub>u 0 = Suc x" by simp
    thus ?case by (auto simp add: unmap_mem_def assemble_vals_def split: prod.splits)
  qed (simp add: unmap_mem_def assemble_vals_def)
  hence "print_mval (unmap_mem ?mem) (unmap_mem ?mem 2) = 
    print_uval (pseudoreg_map \<circ> ?mem Hp) (vs\<^sub>u 0)" using print_m by blast
  with PU PU2 have PM: "print_mach_state (MS (case_reg (4 * hp\<^sub>u) (Suc (4 * ep\<^sub>u)) 6 3 0) 
    (unmap_mem ?mem) 0) = print_nexpr (erase v\<^sub>t)" by simp
  have "final_state (MS (case_reg (4 * hp\<^sub>u) (Suc (4 * ep\<^sub>u)) 6 3 0) (unmap_mem ?mem) 0)" by simp
  with VN TN EN EM PM show ?thesis by blast
qed

end