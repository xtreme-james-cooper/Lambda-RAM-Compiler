theory Unification
  imports Substitution
begin        

function unify :: "(uexpr \<times> uexpr) list \<rightharpoonup> subst" where
  "unify [] = Some Map.empty"
| "unify ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess) = (
    if k\<^sub>1 = k\<^sub>2 \<and> length es\<^sub>1 = length es\<^sub>2 then unify (zip es\<^sub>1 es\<^sub>2 @ ess)
    else None)"
| "unify ((Ctor k es, Var x) # ess) = unify ((Var x, Ctor k es) # ess)"
| "unify ((Var x, e) # ess) = (
    if e = Var x then unify ess
    else if x \<notin> vars e then map_option (extend_subst x e) (unify (list_subst x e ess))
    else None)"
  by pat_completeness auto
termination
  by (relation "measures [card \<circ> list_vars, list_ctor_count, length]") 
     (simp_all add: card_insert_if)

lemma unify_induct [case_names Nil CtorCtorYes CtorCtorNo CtorVar VarSame Occurs VarNo VarYes]: "
    P [] \<Longrightarrow>
    (\<And>k es\<^sub>1 es\<^sub>2 ess. length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> P (zip es\<^sub>1 es\<^sub>2 @ ess) \<Longrightarrow> 
      P ((Ctor k es\<^sub>1, Ctor k es\<^sub>2) # ess)) \<Longrightarrow>
    (\<And>k\<^sub>1 k\<^sub>2 es\<^sub>1 es\<^sub>2 ess. k\<^sub>1 \<noteq> k\<^sub>2 \<or> length es\<^sub>1 \<noteq> length es\<^sub>2 \<Longrightarrow> 
      P ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess)) \<Longrightarrow>
    (\<And>x es k ess. P ((Var x, Ctor k es) # ess) \<Longrightarrow> P ((Ctor k es, Var x) # ess)) \<Longrightarrow>
    (\<And>x ess. P ess \<Longrightarrow> P ((Var x, Var x) # ess)) \<Longrightarrow>
    (\<And>x e ess. e \<noteq> Var x \<Longrightarrow> x \<in> vars e \<Longrightarrow> P ((Var x, e) # ess)) \<Longrightarrow>
    (\<And>x e ess. e \<noteq> Var x \<Longrightarrow> x \<notin> vars e \<Longrightarrow> P (list_subst x e ess) \<Longrightarrow> 
      unify (list_subst x e ess) = None \<Longrightarrow> P ((Var x, e) # ess)) \<Longrightarrow> 
    (\<And>x e ess s'. e \<noteq> Var x \<Longrightarrow> x \<notin> vars e \<Longrightarrow> P (list_subst x e ess) \<Longrightarrow> 
      unify (list_subst x e ess) = Some s' \<Longrightarrow> P ((Var x, e) # ess)) \<Longrightarrow> 
    P ts"
proof (induction ts rule: unify.induct)
  case (2 k\<^sub>1 es\<^sub>1 k\<^sub>2 es\<^sub>2 ess)
  thus ?case by (cases "k\<^sub>1 = k\<^sub>2 \<and> length es\<^sub>1 = length es\<^sub>2") simp_all
next
  case (4 x e ess)
  thus ?case 
    by (cases "e \<noteq> Var x") (cases "x \<notin> vars e", cases "unify (list_subst x e ess)", simp_all)
qed simp_all

definition fail :: "(uexpr \<times> uexpr) list" where
  "fail = [(Ctor ''a'' [], Ctor ''b'' [])]"

lemma unify_dom [simp]: "unify ess = Some s \<Longrightarrow> dom s \<subseteq> list_vars ess"
proof (induction ess arbitrary: s rule: unify_induct)
  case (VarYes x e ess s')
  hence "dom s' \<subseteq> list_vars (list_subst x e ess)" by simp
  hence "dom (extend_subst x e s') \<subseteq> insert x (vars e \<union> list_vars ess)" by (auto split: if_splits)
  with VarYes show ?case by simp
qed auto

lemma unify_ran [simp]: "unify ess = Some s \<Longrightarrow> subst_vars s \<subseteq> list_vars ess"
proof (induction ess arbitrary: s rule: unify_induct)
  case (VarYes x e ess s')
  hence X: "subst_vars s' \<subseteq> list_vars (list_subst x e ess)" by simp
  from VarYes have "dom s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_dom)
  with VarYes have "x \<notin> dom s'" by (auto simp del: list_subst_no_var split: if_splits)
  hence D: "subst_vars (extend_subst x e s') = vars (subst s' e) \<union> subst_vars s'" by simp
  from X have "vars e - dom s' \<union> subst_vars s' \<subseteq> insert x (vars e \<union> list_vars ess)" 
    by (auto split: if_splits)
  moreover have "vars (subst s' e) \<subseteq> vars e - dom s' \<union> subst_vars s'" by simp
  ultimately have Y: "vars (subst s' e) \<subseteq> insert x (vars e \<union> list_vars ess)" by blast
  from X have "subst_vars s' \<subseteq> insert x (vars e \<union> list_vars ess)" by (auto split: if_splits)
  with VarYes D Y show ?case by simp
qed auto

lemma [simp]: "unify ess = Some s \<Longrightarrow> ordered_subst s"
proof (induction ess arbitrary: s rule: unify_induct)
  case (VarYes x e ess s')
  hence "dom s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_dom)
  hence D: "dom s' \<subseteq> list_vars ess - {x} \<union> (if x \<in> list_vars ess then vars e else {})" by simp
  from VarYes have A: "ordered_subst s'" by simp
  from VarYes have B: "x \<notin> vars e" by simp
  from VarYes D have C: "x \<notin> dom s'" by (auto simp del: list_subst_no_var split: if_splits)
  from VarYes have "subst_vars s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_ran) 
  with VarYes have "x \<notin> subst_vars s'" by (auto simp del: list_subst_no_var split: if_splits)
  with A B C have "ordered_subst (extend_subst x e s')" by simp
  with VarYes show ?case by simp
qed auto

lemma unify_none [simp]: "unify ess = None \<Longrightarrow> \<nexists>s'. s' unifies\<^sub>l ess"
proof (induction ess rule: unify_induct)
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
 
lemma unify_some [simp]: "unify ess = Some s \<Longrightarrow> s unifies\<^sub>l ess"
  by (induction ess arbitrary: s rule: unify_induct) auto

lemma [simp]: "unify ess = Some s \<Longrightarrow> t unifies\<^sub>l ess \<Longrightarrow> ordered_subst t \<Longrightarrow>
  \<exists>u. subst t = subst u \<circ> subst s \<and> ordered_subst u"
proof (induction ess arbitrary: s t rule: unify_induct)
  case Nil
  thus ?case by auto
next
  case (VarYes x e ess s')
  hence "dom s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_dom)
  with VarYes have D: "x \<notin> dom s'" by (auto simp del: list_subst_no_var split: if_splits)
  from VarYes have "subst_vars s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_ran)
  with VarYes have R: "x \<notin> subst_vars s'" by (auto simp del: list_subst_no_var split: if_splits)
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
      with VarYes show ?case by (auto simp add: subst_merge)
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
      moreover from VarYes S have "subst t = subst (extend_subst y (Var x) u) \<circ> subst s" 
        by (auto simp add: subst_merge)
      ultimately show ?case by blast
    next
      case (Both z)
      with X have "subst u \<circ> subst s' = subst (extend_subst x (Var z) u) \<circ> subst s'" by auto
      hence Z: "subst u \<circ> subst s' = subst u \<circ> subst [x \<mapsto> Var z] \<circ> subst s'" 
        by (simp add: expand_extend_subst)
      from D R Both have "subst s' \<circ> subst [x \<mapsto> Var y] = subst [x \<mapsto> Var z] \<circ> subst s'" by simp
      with U Z have "subst t = subst u \<circ> subst s' \<circ> subst [x \<mapsto> Var y]" by (metis comp_assoc)
      with Y have S: "subst t = subst u \<circ> subst s' \<circ> subst [x \<mapsto> e]" by simp
      from U have "ordered_subst u" by simp
      with VarYes S show ?case by (auto simp add: subst_merge)
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

lemma unify_append_fst [simp]: "unify (ess\<^sub>1 @ ess\<^sub>2) = Some s \<Longrightarrow> 
    \<exists>s\<^sub>1. unify ess\<^sub>1 = Some s\<^sub>1 \<and> s extends s\<^sub>1"
  by (induction ess\<^sub>1 arbitrary: ess\<^sub>2 s rule: unify_induct) auto

lemma [simp]: "unify ess\<^sub>1 = None \<Longrightarrow> unify (ess\<^sub>1 @ ess\<^sub>2) = None"
  by (induction ess\<^sub>1 arbitrary: ess\<^sub>2 rule: unify_induct) auto

lemma [simp]: "unify ((e, e) # ess) = unify ess"
  and [simp]: "unify (zip es es @ ess) = unify ess"
  by (induction e and es arbitrary: ess and ess rule: vars_varss.induct)  simp_all

lemma unify_occurs' [simp]: "e \<noteq> Var x \<Longrightarrow> x \<in> vars e \<Longrightarrow> 
  unify ((e', subst [x \<mapsto> e'] e) # ess) = None"
proof (cases "unify ((e', subst [x \<mapsto> e'] e) # ess)")
  case (Some s)
  moreover assume "e \<noteq> Var x" and "x \<in> vars e"
  ultimately show ?thesis by (metis unify_some list_unifier.simps(2) occurs_check2)
qed simp_all

lemma unify_occurs: "unify ((e, Ctor k (map (subst [x \<mapsto> e]) es)) # ess) = Some s \<Longrightarrow> x \<notin> varss es"
proof 
  assume "x \<in> varss es"
  hence "unify ((e, subst [x \<mapsto> e] (Ctor k es)) # ess) = None" using unify_occurs' by fastforce
  moreover assume "unify ((e, Ctor k (map (subst [x \<mapsto> e]) es)) # ess) = Some s"
  ultimately show False by simp
qed

lemma [simp]: "length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> 
    unify (ess\<^sub>1 @ (Ctor k es\<^sub>1, Ctor k es\<^sub>2) # ess\<^sub>2) = unify (ess\<^sub>1 @ zip es\<^sub>1 es\<^sub>2 @ ess\<^sub>2)" 
  by (induction ess\<^sub>1 arbitrary: es\<^sub>1 es\<^sub>2 ess\<^sub>2 rule: unify_induct) auto

lemma [simp]: "length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> 
  unify (ess\<^sub>1 # (Ctor k es\<^sub>1, Ctor k es\<^sub>2) # ess\<^sub>2) = unify (ess\<^sub>1 # zip es\<^sub>1 es\<^sub>2 @ ess\<^sub>2)" 
proof -
  assume "length es\<^sub>1 = length es\<^sub>2"
  hence "unify ([ess\<^sub>1] @ (Ctor k es\<^sub>1, Ctor k es\<^sub>2) # ess\<^sub>2) = unify ([ess\<^sub>1] @ zip es\<^sub>1 es\<^sub>2 @ ess\<^sub>2)" 
    by (simp del: append.simps)
  thus ?thesis by simp
qed

lemma [simp]: "unify (ess\<^sub>1 @ (e, e) # ess\<^sub>2) = unify (ess\<^sub>1 @ ess\<^sub>2)" 
  by (induction ess\<^sub>1 arbitrary: e ess\<^sub>2 rule: unify_induct) auto

lemma [simp]: "unify (es # (e, e) # ess) = unify (es # ess)" 
proof -
  have "unify ([es] @ (e, e) # ess) = unify ([es] @ ess)" by (simp del: append.simps)
  thus ?thesis by simp
qed

lemma [simp]: "k\<^sub>1 \<noteq> k\<^sub>2 \<Longrightarrow> unify (ess\<^sub>1 @ (Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess\<^sub>2) = None"
  by (induction ess\<^sub>1 arbitrary: es\<^sub>1 es\<^sub>2 ess\<^sub>2 rule: unify_induct) auto

lemma [simp]: "k\<^sub>1 \<noteq> k\<^sub>2 \<Longrightarrow> unify (es # (Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess\<^sub>2) = None"
proof -
  assume "k\<^sub>1 \<noteq> k\<^sub>2"
  hence "unify ([es] @ (Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess\<^sub>2) = None" by (simp del: append.simps)
  thus ?thesis by simp
qed

lemma [simp]: "length es\<^sub>1 \<noteq> length es\<^sub>2 \<Longrightarrow> unify (ess\<^sub>1 @ (Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess\<^sub>2) = None"
  by (induction ess\<^sub>1 arbitrary: es\<^sub>1 es\<^sub>2 ess\<^sub>2 rule: unify_induct) auto

lemma [simp]: "length es\<^sub>1 \<noteq> length es\<^sub>2 \<Longrightarrow> unify (es # (Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess\<^sub>2) = None"
proof -
  assume "length es\<^sub>1 \<noteq> length es\<^sub>2"
  hence "unify ([es] @ (Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess\<^sub>2) = None" by (simp del: append.simps)
  thus ?thesis by simp
qed

lemma [simp]: "unify ess = None \<Longrightarrow> unify (list_subst x e' ess) = None"
proof -
  assume "unify ess = None"
  hence "\<nexists>s'. s' unifies\<^sub>l ess" by simp
  hence "\<exists>s. unify (list_subst x e' ess) = Some s \<Longrightarrow> False" 
  proof -
    assume "\<exists>s. unify (list_subst x e' ess) = Some s"
    then obtain s where "unify (list_subst x e' ess) = Some s" by fastforce
    hence "s unifies\<^sub>l list_subst x e' ess" by (metis unify_some)
    moreover assume "\<nexists>s'. s' unifies\<^sub>l ess"
    ultimately show False by simp
  qed
  thus ?thesis by fastforce
qed

lemma [simp]: "s unifies\<^sub>l ess \<Longrightarrow> ordered_subst s \<Longrightarrow> \<exists>s'. unify ess = Some s' \<and> s extends s'"
proof (cases "unify ess")
  case None
  moreover assume "s unifies\<^sub>l ess"
  ultimately show ?thesis by (metis unify_none)
next
  case (Some s')
  assume "s unifies\<^sub>l ess" and "ordered_subst s"
  with Some obtain u where "subst s = subst u \<circ> subst s' \<and> ordered_subst u" by fastforce
  hence "s extends s'" by (auto simp add: subst_extends_def)
  with Some show ?thesis by fastforce
qed

lemma [simp]: "unify (list_subst x e' ess) = Some s \<Longrightarrow> x \<notin> vars e' \<Longrightarrow> 
  \<exists>s\<^sub>2. unify ess = Some s\<^sub>2 \<and> extend_subst x e' s extends s\<^sub>2"
proof -
  assume U: "unify (list_subst x e' ess) = Some s" 
  hence L: "s unifies\<^sub>l list_subst x e' ess" and O: "ordered_subst s" by (metis unify_some, simp)
  assume X: "x \<notin> vars e'"
  hence "x \<notin> list_vars ess - {x} \<union> (if x \<in> list_vars ess then vars e' else {})" by simp
  moreover from U have "dom s \<subseteq> list_vars (list_subst x e' ess)" by (metis unify_dom)
  moreover from U have "subst_vars s \<subseteq> list_vars (list_subst x e' ess)" by (metis unify_ran)
  ultimately have "x \<notin> dom s" and "x \<notin> subst_vars s" by auto
  with O X L show ?thesis by simp
qed

lemma unify_append_snd [simp]: "unify (ess\<^sub>1 @ ess\<^sub>2) = Some s \<Longrightarrow> 
    \<exists>s\<^sub>2. unify ess\<^sub>2 = Some s\<^sub>2 \<and> s extends s\<^sub>2"
proof (induction ess\<^sub>1 arbitrary: ess\<^sub>2 s rule: unify_induct)
  case (VarYes x e ess s')
  then obtain t where T: "unify (list_subst x e ess @ list_subst x e ess\<^sub>2) = Some t \<and> 
    extend_subst x e t = s" by fastforce
  with VarYes obtain u where "unify (list_subst x e ess\<^sub>2) = Some u \<and> t extends u" by fastforce
  moreover with VarYes obtain s\<^sub>2 where "unify ess\<^sub>2 = Some s\<^sub>2 \<and> extend_subst x e u extends s\<^sub>2" 
    by fastforce
  ultimately have "unify ess\<^sub>2 = Some s\<^sub>2 \<and> extend_subst x e t extends s\<^sub>2" by fastforce
  with T show ?case by fastforce
qed (simp_all split: if_splits)

lemma unify_props: "unify ess = Some s \<Longrightarrow> structural P \<Longrightarrow> 
  list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) ess \<Longrightarrow> \<forall>x\<in>ran s. P x"
proof (induction ess arbitrary: s rule: unify_induct)
  case (CtorCtorYes k es\<^sub>1 es\<^sub>2 ess)
  from CtorCtorYes(1, 3) have X: "unify (zip es\<^sub>1 es\<^sub>2 @ ess) = Some s" by simp
  from CtorCtorYes(1) have "length es\<^sub>1 = length es\<^sub>2" by simp
  moreover from CtorCtorYes(5) have "list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) ess" by simp
  moreover from CtorCtorYes(4, 5) have "list_all P es\<^sub>1" by (auto simp add: structural_def)
  moreover from CtorCtorYes(4, 5) have "list_all P es\<^sub>2" by (auto simp add: structural_def)
  ultimately have "list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) (zip es\<^sub>1 es\<^sub>2 @ ess)" by simp
  with CtorCtorYes(2, 4) X show ?case by blast
next
  case (CtorVar x es k ess)
  from CtorVar(2) have X: "unify ((Var x, Ctor k es) # ess) = Some s" by simp
  from CtorVar(4) have "list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) ((Var x, Ctor k es) # ess)" by simp
  with CtorVar(1, 3) X show ?case by blast
next
  case (VarSame x ess)
  from VarSame(2) have X: "unify ess = Some s" by simp
  from VarSame(4) have "list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) ess" by simp
  with VarSame(1, 3) X show ?case by blast
next
  case (VarYes x e ess s')
  from VarYes(6, 7) have "list_all (\<lambda>(e\<^sub>1, e\<^sub>2). P e\<^sub>1 \<and> P e\<^sub>2) (list_subst x e ess)" by simp
  with VarYes(3, 4, 6) have S: "\<forall>a\<in>ran s'. P a" by blast
  hence "\<forall>x\<in>ran (s'(x := None)). P x" by (auto simp add: ran_def)
  with S VarYes(1, 2, 3, 5, 6, 7) S show ?case by auto
qed fastforce+

lemma [simp]: "unify fail = None"
  by (simp add: fail_def)

lemma [simp]: "list_vars fail = {}"
  by (simp add: fail_def)

lemma [simp]: "list_subst x e fail = fail"
  by (simp add: fail_def)

end