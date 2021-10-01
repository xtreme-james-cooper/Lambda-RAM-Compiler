theory Unification
  imports Substitution
begin

function unify' :: "(uexpr \<times> uexpr) list \<rightharpoonup> subst" where
  "unify' [] = Some Map.empty"
| "unify' ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess) = (
    if k\<^sub>1 = k\<^sub>2 \<and> length es\<^sub>1 = length es\<^sub>2 then unify' (zip es\<^sub>1 es\<^sub>2 @ ess)
    else None)"
| "unify' ((Ctor k es, Var x) # ess) = unify' ((Var x, Ctor k es) # ess)"
| "unify' ((Var x, e) # ess) = (
    if e = Var x then unify' ess
    else if x \<notin> vars e then map_option (extend_subst x e) (unify' (list_subst x e ess))
    else None)"
  by pat_completeness auto
termination
  by (relation "measures [card \<circ> list_vars, list_ctor_count, length]") 
     (simp_all add: card_insert_if)

lemma unify'_induct [case_names Nil CtorCtorYes CtorCtorNo CtorVar VarSame Occurs VarNo VarYes]: "
    P [] \<Longrightarrow>
    (\<And>k es\<^sub>1 es\<^sub>2 ess. length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> P (zip es\<^sub>1 es\<^sub>2 @ ess) \<Longrightarrow> 
      P ((Ctor k es\<^sub>1, Ctor k es\<^sub>2) # ess)) \<Longrightarrow>
    (\<And>k\<^sub>1 k\<^sub>2 es\<^sub>1 es\<^sub>2 ess. k\<^sub>1 \<noteq> k\<^sub>2 \<or> length es\<^sub>1 \<noteq> length es\<^sub>2 \<Longrightarrow> 
      P ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess)) \<Longrightarrow>
    (\<And>x es k ess. P ((Var x, Ctor k es) # ess) \<Longrightarrow> P ((Ctor k es, Var x) # ess)) \<Longrightarrow>
    (\<And>x ess. P ess \<Longrightarrow> P ((Var x, Var x) # ess)) \<Longrightarrow>
    (\<And>x e ess. e \<noteq> Var x \<Longrightarrow> x \<in> vars e \<Longrightarrow> P ((Var x, e) # ess)) \<Longrightarrow>
    (\<And>x e ess. e \<noteq> Var x \<Longrightarrow> x \<notin> vars e \<Longrightarrow> P (list_subst x e ess) \<Longrightarrow> 
      unify' (list_subst x e ess) = None \<Longrightarrow> P ((Var x, e) # ess)) \<Longrightarrow> 
    (\<And>x e ess s'. e \<noteq> Var x \<Longrightarrow> x \<notin> vars e \<Longrightarrow> P (list_subst x e ess) \<Longrightarrow> 
      unify' (list_subst x e ess) = Some s' \<Longrightarrow> P ((Var x, e) # ess)) \<Longrightarrow> 
    P ts"
proof (induction ts rule: unify'.induct)
  case (2 k\<^sub>1 es\<^sub>1 k\<^sub>2 es\<^sub>2 ess)
  thus ?case by (cases "k\<^sub>1 = k\<^sub>2 \<and> length es\<^sub>1 = length es\<^sub>2") simp_all
next
  case (4 x e ess)
  thus ?case 
    by (cases "e \<noteq> Var x") (cases "x \<notin> vars e", cases "unify' (list_subst x e ess)", simp_all)
qed simp_all

definition unify :: "uexpr \<Rightarrow> uexpr \<rightharpoonup> subst" where
  "unify e\<^sub>1 e\<^sub>2 = unify' [(e\<^sub>1, e\<^sub>2)]"

definition fail :: "(uexpr \<times> uexpr) list" where
  "fail = [(Ctor ''a'' [], Ctor ''b'' [])]"

lemma unify_dom [simp]: "unify' ess = Some s \<Longrightarrow> dom s \<subseteq> list_vars ess"
proof (induction ess arbitrary: s rule: unify'_induct)
  case (VarYes x e ess s')
  hence "dom s' \<subseteq> list_vars (list_subst x e ess)" by simp
  hence "dom (extend_subst x e s') \<subseteq> insert x (vars e \<union> list_vars ess)" by (auto split: if_splits)
  with VarYes show ?case by simp
qed auto

lemma unify_ran [simp]: "unify' ess = Some s \<Longrightarrow> subst_vars s \<subseteq> list_vars ess"
proof (induction ess arbitrary: s rule: unify'_induct)
  case (VarYes x e ess s')
  hence X: "subst_vars s' \<subseteq> list_vars (list_subst x e ess)" by simp
  from VarYes have "dom s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_dom)
  with VarYes have "x \<notin> dom s'" by (auto split: if_splits)
  hence D: "subst_vars (extend_subst x e s') = vars (subst s' e) \<union> subst_vars s'" by simp
  from X have "vars e - dom s' \<union> subst_vars s' \<subseteq> insert x (vars e \<union> list_vars ess)" 
    by (auto split: if_splits)
  moreover have "vars (subst s' e) \<subseteq> vars e - dom s' \<union> subst_vars s'" by simp
  ultimately have Y: "vars (subst s' e) \<subseteq> insert x (vars e \<union> list_vars ess)" by blast
  from X have "subst_vars s' \<subseteq> insert x (vars e \<union> list_vars ess)" by (auto split: if_splits)
  with VarYes D Y show ?case by simp
qed auto

lemma [simp]: "unify' ess = Some s \<Longrightarrow> ordered_subst s"
proof (induction ess arbitrary: s rule: unify'_induct)
  case (VarYes x e ess s')
  hence "dom s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_dom)
  hence D: "dom s' \<subseteq> list_vars ess - {x} \<union> (if x \<in> list_vars ess then vars e else {})" by simp
  from VarYes have A: "ordered_subst s'" by simp
  from VarYes have B: "x \<notin> vars e" by simp
  from VarYes D have C: "x \<notin> dom s'" by (auto split: if_splits)
  from VarYes have "subst_vars s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_ran) 
  with VarYes have "x \<notin> subst_vars s'" by (auto split: if_splits)
  with A B C have "ordered_subst (extend_subst x e s')" by simp
  with VarYes show ?case by simp
qed auto

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = Some s \<Longrightarrow> ordered_subst s"
  by (simp add: unify_def)

lemma unify_none [simp]: "unify' ess = None \<Longrightarrow> \<nexists>s'. s' unifies\<^sub>l ess"
proof (induction ess rule: unify'_induct)
  case (Occurs x e ess)
  hence "\<And>s'. \<not> s' unifies Var x and e" by (metis occurs_check)
  thus ?case by simp
next
  case (VarNo x e ess)
  have "\<And>s. s unifies Var x and e \<Longrightarrow> \<not> s unifies\<^sub>l ess" 
  proof -
    fix s
    assume U: "s unifies Var x and e"
    show "?thesis s" 
    proof (cases "s x")
      case None
      with U have "subst s e = Var x" by simp
      with VarNo obtain y where Y: "e = Var y \<and> s y = Some (Var x)" by auto
      with VarNo have "\<not> extend_subst x (Var y) s unifies\<^sub>l ess" by simp
      with None Y show ?thesis by simp
    next
      case (Some e')
      hence S: "s(x \<mapsto> e') = s" by auto
      from VarNo have "\<not> extend_subst x e (s(x := None)) unifies\<^sub>l ess" by simp
      with VarNo(2) U Some S show ?thesis by auto
    qed
  qed
  thus ?case by simp
qed simp_all

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = None \<Longrightarrow> \<nexists>s. s unifies e\<^sub>1 and e\<^sub>2"
proof (unfold unify_def)
  assume "unify' [(e\<^sub>1, e\<^sub>2)] = None"
  hence "\<nexists>s'. s' unifies\<^sub>l [(e\<^sub>1, e\<^sub>2)]" by (metis unify_none)
  thus "\<nexists>s. s unifies e\<^sub>1 and e\<^sub>2" by simp
qed
 
lemma unify_some [simp]: "unify' ess = Some s \<Longrightarrow> s unifies\<^sub>l ess"
  by (induction ess arbitrary: s rule: unify'_induct) auto

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = Some s \<Longrightarrow> s unifies e\<^sub>1 and e\<^sub>2"
proof (unfold unify_def)
  assume "unify' [(e\<^sub>1, e\<^sub>2)] = Some s"
  hence "s unifies\<^sub>l [(e\<^sub>1, e\<^sub>2)]" by (metis unify_some)
  thus "s unifies e\<^sub>1 and e\<^sub>2" by simp
qed

lemma [simp]: "unify' ess = Some s \<Longrightarrow> t unifies\<^sub>l ess \<Longrightarrow> ordered_subst t \<Longrightarrow>
  \<exists>u. subst t = subst u \<circ> subst s \<and> ordered_subst u"
proof (induction ess arbitrary: s t rule: unify'_induct)
  case Nil
  thus ?case by auto
next
  case (VarYes x e ess s')
  hence "dom s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_dom)
  with VarYes have D: "x \<notin> dom s'" by (auto split: if_splits)
  from VarYes have "subst_vars s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_ran)
  with VarYes have R: "x \<notin> subst_vars s'" by (auto split: if_splits)
  thus ?case
  proof (cases "t x")
    case None
    with VarYes have T: "subst t e = Var x \<and> t unifies\<^sub>l ess" by simp
    with VarYes obtain y where Y: "e = Var y \<and> t y = Some (Var x)" by fastforce
    with None T have "t unifies\<^sub>l list_subst x (Var y) ess" by simp
    with VarYes Y obtain u where U: "subst t = subst u \<circ> subst s' \<and> ordered_subst u" by fastforce
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
      with D R Y U FstOnly have "subst t = subst u \<circ> subst s' \<circ> subst [x \<mapsto> e] \<and> ordered_subst u"
        using comp_assoc by blast
      with VarYes show ?case by auto
    next
      case SndOnly
      with X have "subst u \<circ> subst s' = subst u \<circ> subst [y \<mapsto> Var x] \<circ> subst s'" by simp
      hence "subst u \<circ> subst s' = subst (extend_subst y (Var x) u) \<circ> subst [x \<mapsto> Var y] \<circ> subst s'" 
        by (simp add: expand_extend_subst comp_assoc)
      with D R Y U SndOnly have S: "subst t = 
        subst (extend_subst y (Var x) u) \<circ> subst s' \<circ> subst [x \<mapsto> e]" by (simp add: comp_assoc)
      from SndOnly X have "u y = Some (case u x of None \<Rightarrow> Var x | Some e \<Rightarrow> e)" 
        by (auto split: option.splits)
      with VarYes U have "ordered_subst (extend_subst y (Var x) u)" by simp
      with VarYes S show ?case by auto
    next
      case (Both z)
      with X have "subst u \<circ> subst s' = subst (extend_subst x (Var z) u) \<circ> subst s'" by auto
      hence Z: "subst u \<circ> subst s' = subst u \<circ> subst [x \<mapsto> Var z] \<circ> subst s'" 
        by (simp add: expand_extend_subst)
      from D R Both have "subst s' \<circ> subst [x \<mapsto> Var y] = subst [x \<mapsto> Var z] \<circ> subst s'" by simp
      with U Z have "subst t = subst u \<circ> subst s' \<circ> subst [x \<mapsto> Var y]" by (metis comp_assoc)
      with Y have S: "subst t = subst u \<circ> subst s' \<circ> subst [x \<mapsto> e]" by simp
      from U have "ordered_subst u" by simp
      with VarYes S show ?case by auto
  qed
  next
    case (Some e')
    with VarYes have "e' = subst t e \<and> t unifies\<^sub>l ess" by simp
    with VarYes Some obtain t' where T: "t = extend_subst x e t' \<and> t' unifies\<^sub>l list_subst x e ess \<and> 
      ordered_subst t'" by (metis dissect_subst)
    with VarYes obtain u where "subst t' = subst u \<circ> subst s' \<and> ordered_subst u" by fastforce
    with VarYes T show ?thesis by (auto simp add: expand_extend_subst)
  qed
qed simp_all

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = Some s \<Longrightarrow> t unifies e\<^sub>1 and e\<^sub>2 \<Longrightarrow> ordered_subst t \<Longrightarrow> t extends s"
proof (unfold unify_def)
  assume "t unifies e\<^sub>1 and e\<^sub>2"
  hence "t unifies\<^sub>l [(e\<^sub>1, e\<^sub>2)]" by simp
  moreover assume "unify' [(e\<^sub>1, e\<^sub>2)] = Some s"
  moreover assume "ordered_subst t"
  ultimately have "\<exists>u. subst t = subst u \<circ> subst s \<and> ordered_subst u" by simp
  thus ?thesis by (auto simp add: subst_extends_def)
qed

lemma unify_append_fst [simp]: "unify' (ess\<^sub>1 @ ess\<^sub>2) = Some s \<Longrightarrow> 
    \<exists>s\<^sub>1. unify' ess\<^sub>1 = Some s\<^sub>1 \<and> s extends s\<^sub>1"
  by (induction ess\<^sub>1 arbitrary: ess\<^sub>2 s rule: unify'_induct) auto

lemma [simp]: "unify' ess\<^sub>1 = None \<Longrightarrow> unify' (ess\<^sub>1 @ ess\<^sub>2) = None"
  by (induction ess\<^sub>1 arbitrary: ess\<^sub>2 rule: unify'_induct) auto

lemma [simp]: "unify' ((e, e) # ess) = unify' ess"
  and [simp]: "unify' (zip es es @ ess) = unify' ess"
  by (induction e and es arbitrary: ess and ess rule: vars_varss.induct)  simp_all

lemma [simp]: "e \<noteq> Var x \<Longrightarrow> x \<in> vars e \<Longrightarrow> unify' ((e', subst [x \<mapsto> e'] e) # ess) = None"
proof (cases "unify' ((e', subst [x \<mapsto> e'] e) # ess)")
  case (Some s)
  moreover assume "e \<noteq> Var x" and "x \<in> vars e"
  ultimately show ?thesis by (metis unify_some list_unifier.simps(2) occurs_check2)
qed simp_all

lemma unify_subst_back [simp]: "unify' (list_subst x e' ess) = Some s \<Longrightarrow> x \<notin> vars e' \<Longrightarrow>
  \<exists>s'. unify' ess = Some s' \<and> (\<forall>t. t extends s \<longrightarrow> extend_subst x e' t extends s')"
proof (induction ess arbitrary: s rule: unify'_induct)
  case (CtorVar y es k ess)
  thus ?case 
  proof (cases "x = y")
    case True
    with CtorVar show ?thesis
    proof (cases e')
      case (Ctor k' es')
      from CtorVar True Ctor have K: "k = k' \<and> length es = length es' \<and> 
        unify' (zip (map (subst [x \<mapsto> Ctor k' es']) es) es' @ list_subst x (Ctor k' es') ess) = 
          Some s" by (simp split: if_splits)



      have "unify' (zip es' (map (subst [x \<mapsto> Ctor k es']) es) @ list_subst x (Ctor k es') ess) = Some xs" by simp
      with CtorVar True Ctor K obtain s' where "unify' ((Var x, Ctor k es) # ess) = Some s' \<and> 
        (\<forall>t. t extends xs \<longrightarrow> extend_subst x (Ctor k es') t extends s')" by fastforce
      then obtain s'' where X: "x \<notin> varss es \<and> unify' (list_subst x (Ctor k es) ess) = Some s'' \<and>
        s' = extend_subst x (Ctor k es) s'' \<and> (\<forall>t. t extends xs \<longrightarrow> 
          extend_subst x (Ctor k es') t extends extend_subst x (Ctor k es) s'')" 
            by (auto split: if_splits)



      from CtorVar have "x \<notin> varss es'" by simp
   
    
      have "\<forall>t. t extends s \<longrightarrow> extend_subst x (Ctor k es') t extends extend_subst x (Ctor k es) s''" by simp
      with True Ctor K X show ?thesis by fastforce
    qed simp_all
  qed simp_all
next
  case (Occurs y e ess)
  thus ?case
  proof (cases "x = y")
    case True
    with Occurs have "unify' ((e', subst [x \<mapsto> e'] e) # list_subst x e' ess) = Some s" by simp
    with Occurs True show ?thesis by (metis occurs_check2 list_unifier.simps(2) unify_some)
  qed (auto split: if_splits)
next
  case (VarNo y e ess)
  from VarNo have "e \<noteq> Var y" by simp
  from VarNo have "y \<notin> vars e" by simp
  from VarNo have "unify' (list_subst y e ess) = None" by simp
  from VarNo have "unify' (list_subst x e' ((Var y, e) # ess)) = Some s" by simp
  from VarNo have "x \<notin> vars e'" by simp


  have "False" by simp
  thus ?case by simp
next
  case (VarYes y e ess s')
  thus ?case by simp
qed fastforce+
  
lemma unify_append_snd [simp]: "unify' (ess\<^sub>1 @ ess\<^sub>2) = Some s \<Longrightarrow> 
    \<exists>s\<^sub>2. unify' ess\<^sub>2 = Some s\<^sub>2 \<and> s extends s\<^sub>2"
  using unify_subst_back by (induction ess\<^sub>1 arbitrary: ess\<^sub>2 s rule: unify'_induct) fastforce+

lemma [simp]: "unify' (es # ess) = Some s \<Longrightarrow> \<exists>s\<^sub>2. unify' ess = Some s\<^sub>2 \<and> s extends s\<^sub>2"
proof -
  assume "unify' (es # ess) = Some s" 
  hence "unify' ([es] @ ess) = Some s" by simp
  thus "\<exists>s\<^sub>2. unify' ess = Some s\<^sub>2 \<and> s extends s\<^sub>2" by (metis unify_append_snd)
qed

lemma unify'_props: "unify' ess = Some s \<Longrightarrow> structural P \<Longrightarrow> 
  list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) ess \<Longrightarrow> \<forall>x\<in>ran s. P x"
proof (induction ess arbitrary: s rule: unify'_induct)
  case (CtorCtorYes k es\<^sub>1 es\<^sub>2 ess)
  from CtorCtorYes(1, 3) have X: "unify' (zip es\<^sub>1 es\<^sub>2 @ ess) = Some s" by simp
  from CtorCtorYes(1) have "length es\<^sub>1 = length es\<^sub>2" by simp
  moreover from CtorCtorYes(5) have "list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) ess" by simp
  moreover from CtorCtorYes(4, 5) have "list_all P es\<^sub>1" by (auto simp add: structural_def)
  moreover from CtorCtorYes(4, 5) have "list_all P es\<^sub>2" by (auto simp add: structural_def)
  ultimately have "list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) (zip es\<^sub>1 es\<^sub>2 @ ess)" by simp
  with CtorCtorYes(2, 4) X show ?case by blast
next
  case (CtorVar x es k ess)
  from CtorVar(2) have X: "unify' ((Var x, Ctor k es) # ess) = Some s" by simp
  from CtorVar(4) have "list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) ((Var x, Ctor k es) # ess)" by simp
  with CtorVar(1, 3) X show ?case by blast
next
  case (VarSame x ess)
  from VarSame(2) have X: "unify' ess = Some s" by simp
  from VarSame(4) have "list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) ess" by simp
  with VarSame(1, 3) X show ?case by blast
next
  case (VarYes x e ess s')
  from VarYes(6, 7) have "list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) (list_subst x e ess)" by simp
  with VarYes(3, 4, 6) have S: "\<forall>a\<in>ran s'. P a" by blast
  hence "\<forall>x\<in>ran (s'(x := None)). P x" by (auto simp add: ran_def)
  with S VarYes(1, 2, 3, 5, 6, 7) S show ?case by auto
qed fastforce+

lemma unify_props: "unify e\<^sub>1 e\<^sub>2 = Some s \<Longrightarrow> P e\<^sub>1 \<Longrightarrow> P e\<^sub>2 \<Longrightarrow> structural P \<Longrightarrow> \<forall>x \<in> ran s. P x"
proof (unfold unify_def)
  assume "P e\<^sub>1" and "P e\<^sub>2"
  hence "list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) [(e\<^sub>1, e\<^sub>2)]" by simp
  moreover assume "unify' [(e\<^sub>1, e\<^sub>2)] = Some s" and "structural P"
  ultimately show "\<forall>x\<in>ran s. P x" by (metis unify'_props)
qed

lemma [simp]: "unify' fail = None"
  by (simp add: fail_def)

end