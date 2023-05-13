theory Unification
  imports Substitution
begin        

function unify :: "constraint \<rightharpoonup> subst" where
  "unify [] = Some Map.empty"
| "unify ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess) = (
    if k\<^sub>1 = k\<^sub>2 \<and> length es\<^sub>1 = length es\<^sub>2 then unify (zip es\<^sub>1 es\<^sub>2 @ ess)
    else None)"
| "unify ((Ctor k es, Var x) # ess) = unify ((Var x, Ctor k es) # ess)"
| "unify ((Var x, e) # ess) = (
    if e = Var x then unify ess
    else if x \<notin> uvars e then map_option (extend_subst x e) (unify (constr_subst x e ess))
    else None)"
  by pat_completeness auto
termination
  by (relation "measures [card \<circ> constr_vars, constr_ctor_count, length]") 
     (simp_all add: card_insert_if)

lemma unify_induct [case_names Nil CtorCtorYes CtorCtorNo CtorVar VarSame Occurs VarNo VarYes]: "
    P [] \<Longrightarrow>
    (\<And>k es\<^sub>1 es\<^sub>2 ess. length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> P (zip es\<^sub>1 es\<^sub>2 @ ess) \<Longrightarrow> 
      P ((Ctor k es\<^sub>1, Ctor k es\<^sub>2) # ess)) \<Longrightarrow>
    (\<And>k\<^sub>1 k\<^sub>2 es\<^sub>1 es\<^sub>2 ess. k\<^sub>1 \<noteq> k\<^sub>2 \<or> length es\<^sub>1 \<noteq> length es\<^sub>2 \<Longrightarrow> 
      P ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess)) \<Longrightarrow>
    (\<And>x es k ess. P ((Var x, Ctor k es) # ess) \<Longrightarrow> P ((Ctor k es, Var x) # ess)) \<Longrightarrow>
    (\<And>x ess. P ess \<Longrightarrow> P ((Var x, Var x) # ess)) \<Longrightarrow>
    (\<And>x e ess. e \<noteq> Var x \<Longrightarrow> x \<in> uvars e \<Longrightarrow> P ((Var x, e) # ess)) \<Longrightarrow>
    (\<And>x e ess. e \<noteq> Var x \<Longrightarrow> x \<notin> uvars e \<Longrightarrow> P (constr_subst x e ess) \<Longrightarrow> 
      unify (constr_subst x e ess) = None \<Longrightarrow> P ((Var x, e) # ess)) \<Longrightarrow> 
    (\<And>x e ess s'. e \<noteq> Var x \<Longrightarrow> x \<notin> uvars e \<Longrightarrow> P (constr_subst x e ess) \<Longrightarrow> 
      unify (constr_subst x e ess) = Some s' \<Longrightarrow> P ((Var x, e) # ess)) \<Longrightarrow> 
    P ts"
proof (induction ts rule: unify.induct)
  case (2 k\<^sub>1 es\<^sub>1 k\<^sub>2 es\<^sub>2 ess)
  thus ?case by (cases "k\<^sub>1 = k\<^sub>2 \<and> length es\<^sub>1 = length es\<^sub>2") simp_all
next
  case (4 x e ess)
  thus ?case 
    by (cases "e \<noteq> Var x") (cases "x \<notin> uvars e", cases "unify (constr_subst x e ess)", simp_all)
qed simp_all

definition fail :: constraint where
  "fail = [(Ctor ''a'' [], Ctor ''b'' [])]"

lemma unify_dom [simp]: "unify ess = Some s \<Longrightarrow> dom s \<subseteq> constr_vars ess"
proof (induction ess arbitrary: s rule: unify_induct)
  case (VarYes x e ess s')
  hence "dom s' \<subseteq> constr_vars (constr_subst x e ess)" by simp
  hence "dom (extend_subst x e s') \<subseteq> insert x (uvars e \<union> constr_vars ess)" by (auto split: if_splits)
  with VarYes show ?case by simp
qed auto

lemma unify_ran [simp]: "unify ess = Some s \<Longrightarrow> subst_vars s \<subseteq> constr_vars ess"
proof (induction ess arbitrary: s rule: unify_induct)
  case (VarYes x e ess s')
  hence X: "subst_vars s' \<subseteq> constr_vars (constr_subst x e ess)" by simp
  from VarYes have "dom s' \<subseteq> constr_vars (constr_subst x e ess)" by (metis unify_dom)
  with VarYes have "x \<notin> dom s'" by (auto simp del: constr_subst_no_var split: if_splits)
  hence D: "subst_vars (extend_subst x e s') = uvars (subst s' e) \<union> subst_vars s'" by simp
  from X have "uvars e - dom s' \<union> subst_vars s' \<subseteq> insert x (uvars e \<union> constr_vars ess)" 
    by (auto split: if_splits)
  moreover have "uvars (subst s' e) \<subseteq> uvars e - dom s' \<union> subst_vars s'" by simp
  ultimately have Y: "uvars (subst s' e) \<subseteq> insert x (uvars e \<union> constr_vars ess)" by blast
  from X have "subst_vars s' \<subseteq> insert x (uvars e \<union> constr_vars ess)" by (auto split: if_splits)
  with VarYes D Y show ?case by simp
qed auto

lemma [simp]: "unify ess = Some s \<Longrightarrow> idempotent s"
proof (induction ess arbitrary: s rule: unify_induct)
  case (VarYes x e ess s')
  hence "dom s' \<subseteq> constr_vars (constr_subst x e ess)" by (metis unify_dom)
  hence D: "dom s' \<subseteq> constr_vars ess - {x} \<union> (if x \<in> constr_vars ess then uvars e else {})" by simp
  from VarYes have A: "idempotent s'" by simp
  from VarYes have B: "x \<notin> uvars e" by simp
  from VarYes D have C: "x \<notin> dom s'" by (auto simp del: constr_subst_no_var split: if_splits)
  from VarYes have "subst_vars s' \<subseteq> constr_vars (constr_subst x e ess)" by (metis unify_ran) 
  with VarYes have "x \<notin> subst_vars s'" by (auto simp del: constr_subst_no_var split: if_splits)
  with A B C have "idempotent (extend_subst x e s')" by simp
  with VarYes show ?case by simp
qed auto

lemma unify_none [simp]: "unify ess = None \<Longrightarrow> \<nexists>s'. s' unifies\<^sub>\<kappa> ess"
proof (induction ess rule: unify_induct)
  case (Occurs x e ess)
  hence "\<And>s'. \<not> s' unifies Var x and e" by (metis occurs_check)
  thus ?case by simp
next
  case (VarNo x e ess)
  have "\<And>s. s unifies Var x and e \<Longrightarrow> \<not> s unifies\<^sub>\<kappa> ess" 
  proof -
    fix s
    assume U: "s unifies Var x and e"
    show "?thesis s" 
    proof (cases "s x")
      case None
      with U have "subst s e = Var x" by simp
      with VarNo obtain y where Y: "e = Var y \<and> s y = Some (Var x)" by auto
      with VarNo have "\<not> extend_subst x (Var y) s unifies\<^sub>\<kappa> ess" by simp
      with None Y show ?thesis by simp
    next
      case (Some e')
      hence S: "s(x \<mapsto> e') = s" by auto
      from VarNo have "\<not> extend_subst x e (s(x := None)) unifies\<^sub>\<kappa> ess" by simp
      with VarNo(2) U Some S show ?thesis by auto
    qed
  qed
  thus ?case by simp
qed simp_all
 
lemma unify_some [simp]: "unify ess = Some s \<Longrightarrow> s unifies\<^sub>\<kappa> ess"
  by (induction ess arbitrary: s rule: unify_induct) auto

lemma [simp]: "unify ess = Some s \<Longrightarrow> t unifies\<^sub>\<kappa> ess \<Longrightarrow> idempotent t \<Longrightarrow>
  \<exists>u. subst t = subst u \<circ> subst s \<and> idempotent u"
proof (induction ess arbitrary: s t rule: unify_induct)
  case Nil
  thus ?case by auto
next
  case (VarYes x e ess s')
  hence "dom s' \<subseteq> constr_vars (constr_subst x e ess)" by (metis unify_dom)
  with VarYes have D: "x \<notin> dom s'" by (auto simp del: constr_subst_no_var split: if_splits)
  from VarYes have "subst_vars s' \<subseteq> constr_vars (constr_subst x e ess)" by (metis unify_ran)
  with VarYes have R: "x \<notin> subst_vars s'" by (auto simp del: constr_subst_no_var split: if_splits)
  thus ?case
  proof (cases "t x")
    case None
    with VarYes have T: "subst t e = Var x \<and> t unifies\<^sub>\<kappa> ess" by simp
    with VarYes obtain y where Y: "e = Var y \<and> t y = Some (Var x)" by fastforce
    with None T have "t unifies\<^sub>\<kappa> constr_subst x (Var y) ess" by simp
    with VarYes Y obtain u where U: "subst t = subst u \<circ> subst s' \<and> idempotent u" by fastforce
    from None have "x \<notin> dom t" by auto
    with D U have X: "x \<notin> dom u" by (metis split_not_in_domain)
    from T Y U have "(subst u \<circ> subst s') (Var y) = Var x" by simp
    thus ?thesis
    proof (induction rule: subst_subst_var)
      case Eq
      with VarYes Y show ?case by simp
    next
      case FstOnly
      have "subst u \<circ> subst s' = subst u \<circ> subst [x \<mapsto> Var x] \<circ> subst s'" by simp
      with D R Y U FstOnly have "subst t = subst u \<circ> subst s' \<circ> subst [x \<mapsto> e] \<and> idempotent u"
        using comp_assoc by blast
      with VarYes show ?case by (auto simp add: expand_extend_subst)
    next
      case SndOnly
      with X have "subst u \<circ> subst s' = subst u \<circ> subst [y \<mapsto> Var x] \<circ> subst s'" by simp
      hence "subst u \<circ> subst s' = subst (extend_subst y (Var x) u) \<circ> subst [x \<mapsto> Var y] \<circ> subst s'" 
        by (simp add: expand_extend_subst comp_assoc)
      with D R Y U SndOnly have S: "subst t = 
        subst (extend_subst y (Var x) u) \<circ> subst s' \<circ> subst [x \<mapsto> e]" by (simp add: comp_assoc)
      from SndOnly X have "u y = Some (case u x of None \<Rightarrow> Var x | Some e \<Rightarrow> e)" 
        by (auto split: option.splits)
      with VarYes U have "idempotent (extend_subst y (Var x) u)" by simp
      moreover from VarYes S have "subst t = subst (extend_subst y (Var x) u) \<circ> subst s" 
        by (auto simp add: expand_extend_subst)
      ultimately show ?case by blast
    next
      case (Both z)
      with X have "subst u \<circ> subst s' = subst (extend_subst x (Var z) u) \<circ> subst s'" by auto
      hence Z: "subst u \<circ> subst s' = subst u \<circ> subst [x \<mapsto> Var z] \<circ> subst s'" 
        by (simp add: expand_extend_subst)
      from D R Both have "subst s' \<circ> subst [x \<mapsto> Var y] = subst [x \<mapsto> Var z] \<circ> subst s'" by simp
      with U Z have "subst t = subst u \<circ> subst s' \<circ> subst [x \<mapsto> Var y]" by (metis comp_assoc)
      with Y have S: "subst t = subst u \<circ> subst s' \<circ> subst [x \<mapsto> e]" by simp
      from U have "idempotent u" by simp
      with VarYes S show ?case by (auto simp add: expand_extend_subst)
  qed
  next
    case (Some e')
    with VarYes have "e' = subst t e \<and> t unifies\<^sub>\<kappa> ess" by simp
    with VarYes Some obtain t' where T: "t = extend_subst x e t' \<and> t' unifies\<^sub>\<kappa> constr_subst x e ess \<and> 
      idempotent t'" by (metis dissect_subst)
    with VarYes obtain u where "subst t' = subst u \<circ> subst s' \<and> idempotent u" by fastforce
    with VarYes T show ?thesis by (auto simp add: expand_extend_subst)
  qed
qed simp_all

lemma unify_append_fst [simp]: "unify (ess\<^sub>1 @ ess\<^sub>2) = Some s \<Longrightarrow> 
    \<exists>s\<^sub>1. unify ess\<^sub>1 = Some s\<^sub>1 \<and> s generalizes s\<^sub>1"
  by (induction ess\<^sub>1 arbitrary: ess\<^sub>2 s rule: unify_induct) auto

lemma [simp]: "unify ess\<^sub>1 = None \<Longrightarrow> unify (ess\<^sub>1 @ ess\<^sub>2) = None"
  by (induction ess\<^sub>1 arbitrary: ess\<^sub>2 rule: unify_induct) auto

lemma unify_occurs' [simp]: "e \<noteq> Var x \<Longrightarrow> x \<in> uvars e \<Longrightarrow> 
  unify ((e', subst [x \<mapsto> e'] e) # ess) = None"
proof (cases "unify ((e', subst [x \<mapsto> e'] e) # ess)")
  case (Some s)
  moreover assume "e \<noteq> Var x" and "x \<in> uvars e"
  ultimately show ?thesis by (metis unify_some constr_unifier.simps(2) occurs_check2)
qed simp_all

lemma unify_occurs: "unify ((e, Ctor k (map (subst [x \<mapsto> e]) es)) # ess) = Some s \<Longrightarrow> x \<notin> uvarss es"
proof 
  assume "x \<in> uvarss es"
  hence "unify ((e, subst [x \<mapsto> e] (Ctor k es)) # ess) = None" using unify_occurs' by fastforce
  moreover assume "unify ((e, Ctor k (map (subst [x \<mapsto> e]) es)) # ess) = Some s"
  ultimately show False by simp
qed

lemma [simp]: "s unifies\<^sub>\<kappa> ess \<Longrightarrow> idempotent s \<Longrightarrow> \<exists>s'. unify ess = Some s' \<and> s generalizes s'"
proof (cases "unify ess")
  case None
  moreover assume "s unifies\<^sub>\<kappa> ess"
  ultimately show ?thesis by (metis unify_none)
next
  case (Some s')
  assume "s unifies\<^sub>\<kappa> ess" and "idempotent s"
  with Some obtain u where "subst s = subst u \<circ> subst s' \<and> idempotent u" by fastforce
  hence "s generalizes s'" by (auto simp add: subst_generalize_def)
  with Some show ?thesis by fastforce
qed

lemma [simp]: "unify (constr_subst x e' ess) = Some s \<Longrightarrow> x \<notin> uvars e' \<Longrightarrow> 
  \<exists>s\<^sub>2. unify ess = Some s\<^sub>2 \<and> extend_subst x e' s generalizes s\<^sub>2"
proof -
  assume U: "unify (constr_subst x e' ess) = Some s" 
  hence L: "s unifies\<^sub>\<kappa> constr_subst x e' ess" and O: "idempotent s" by (metis unify_some, simp)
  assume X: "x \<notin> uvars e'"
  hence "x \<notin> constr_vars ess - {x} \<union> (if x \<in> constr_vars ess then uvars e' else {})" by simp
  moreover from U have "dom s \<subseteq> constr_vars (constr_subst x e' ess)" by (metis unify_dom)
  moreover from U have "subst_vars s \<subseteq> constr_vars (constr_subst x e' ess)" by (metis unify_ran)
  ultimately have "x \<notin> dom s" and "x \<notin> subst_vars s" by auto
  with O X L show ?thesis by simp
qed

lemma unify_append_snd [simp]: "unify (ess\<^sub>1 @ ess\<^sub>2) = Some s \<Longrightarrow> 
    \<exists>s\<^sub>2. unify ess\<^sub>2 = Some s\<^sub>2 \<and> s generalizes s\<^sub>2"
proof (induction ess\<^sub>1 arbitrary: ess\<^sub>2 s rule: unify_induct)
  case (VarYes x e ess s')
  then obtain t where T: "unify (constr_subst x e ess @ constr_subst x e ess\<^sub>2) = Some t \<and> 
    extend_subst x e t = s" by fastforce
  with VarYes obtain u where U: "unify (constr_subst x e ess\<^sub>2) = Some u \<and> t generalizes u" 
    by fastforce
  moreover with VarYes obtain s\<^sub>2 where "unify ess\<^sub>2 = Some s\<^sub>2 \<and> extend_subst x e u generalizes s\<^sub>2" 
    by fastforce
  moreover with U have "extend_subst x e t generalizes extend_subst x e u" by simp
  ultimately have "unify ess\<^sub>2 = Some s\<^sub>2 \<and> extend_subst x e t generalizes s\<^sub>2" by fastforce
  with T show ?case by fastforce
qed (simp_all split: if_splits)

lemma [simp]: "unify fail = None"
  by (simp add: fail_def)

lemma [simp]: "constr_vars fail = {}"
  by (simp add: fail_def)

end