theory Unification
  imports Substitution
begin

function unify' :: "(expr \<times> expr) list \<rightharpoonup> subst" where
  "unify' [] = Some Map.empty"
| "unify' ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess) = (
    if k\<^sub>1 = k\<^sub>2 \<and> length es\<^sub>1 = length es\<^sub>2 then unify' (zip es\<^sub>1 es\<^sub>2 @ ess)
    else None)"
| "unify' ((Ctor k es, Var x) # ess) = unify' ((Var x, Ctor k es) # ess)"
| "unify' ((Var x, e) # ess) = (
    if e = Var x then unify' ess
    else if x \<in> vars e then None
    else map_option (extend_subst x e) (unify' (list_subst x e ess)))"
  by pat_completeness auto
termination
  by (relation "measures [card \<circ> list_vars, list_ctor_count, length]") 
     (simp_all add: card_insert_if)

lemma unify'_induct: "P [] \<Longrightarrow>
    (\<And>k es\<^sub>1 es\<^sub>2 ess. length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> P (zip es\<^sub>1 es\<^sub>2 @ ess) \<Longrightarrow> 
      P ((Ctor k es\<^sub>1, Ctor k es\<^sub>2) # ess)) \<Longrightarrow>
    (\<And>k\<^sub>1 k\<^sub>2 es\<^sub>1 es\<^sub>2 ess. k\<^sub>1 \<noteq> k\<^sub>2 \<or> length es\<^sub>1 \<noteq> length es\<^sub>2 \<Longrightarrow> 
      P ((Ctor k\<^sub>1 es\<^sub>1, Ctor k\<^sub>2 es\<^sub>2) # ess)) \<Longrightarrow>
    (\<And>x es k ess. P ((Var x, Ctor k es) # ess) \<Longrightarrow> P ((Ctor k es, Var x) # ess)) \<Longrightarrow>
    (\<And>x ess. P ess \<Longrightarrow> P ((Var x, Var x) # ess)) \<Longrightarrow>
    (\<And>x e ess. e \<noteq> Var x \<Longrightarrow> x \<in> vars e \<Longrightarrow> P ((Var x, e) # ess)) \<Longrightarrow>
    (\<And>x e ess. e \<noteq> Var x \<Longrightarrow> x \<notin> vars e \<Longrightarrow> P (list_subst x e ess) \<Longrightarrow> 
      unify' (list_subst x e ess) = None \<Longrightarrow>P ((Var x, e) # ess)) \<Longrightarrow> 
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

definition unify :: "expr \<Rightarrow> expr \<rightharpoonup> subst" where
  "unify e\<^sub>1 e\<^sub>2 = unify' [(e\<^sub>1, e\<^sub>2)]"

lemma unify_dom [simp]: "unify' ess = Some s \<Longrightarrow> dom s \<subseteq> list_vars ess"
proof (induction ess arbitrary: s rule: unify'_induct)
  case (8 x e ess s')
  hence "dom s' \<subseteq> list_vars (list_subst x e ess)" by simp
  hence "dom (extend_subst x e s') \<subseteq> insert x (vars e \<union> list_vars ess)" by (auto split: if_splits)
  with 8 show ?case by simp
qed auto

lemma unify_ran [simp]: "unify' ess = Some s \<Longrightarrow> subst_vars s \<subseteq> list_vars ess"
proof (induction ess arbitrary: s rule: unify'_induct)
  case (8 x e ess s')
  hence X: "subst_vars s' \<subseteq> list_vars (list_subst x e ess)" by simp
  from 8 have "dom s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_dom)
  with 8 have "x \<notin> dom s'" by (auto split: if_splits)
  hence D: "subst_vars (extend_subst x e s') = vars (subst s' e) \<union> subst_vars s'" by simp
  from X have "vars e - dom s' \<union> subst_vars s' \<subseteq> insert x (vars e \<union> list_vars ess)" 
    by (auto split: if_splits)
  moreover have "vars (subst s' e) \<subseteq> vars e - dom s' \<union> subst_vars s'" by simp
  ultimately have Y: "vars (subst s' e) \<subseteq> insert x (vars e \<union> list_vars ess)" by blast
  from X have "subst_vars s' \<subseteq> insert x (vars e \<union> list_vars ess)" by (auto split: if_splits)
  with 8 D Y show ?case by simp
qed auto

lemma [simp]: "unify' ess = Some s \<Longrightarrow> ordered_subst s"
proof (induction ess arbitrary: s rule: unify'_induct)
  case (8 x e ess s')
  hence "dom s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_dom)
  hence D: "dom s' \<subseteq> list_vars ess - {x} \<union> (if x \<in> list_vars ess then vars e else {})" by simp
  from 8 have A: "ordered_subst s'" by simp
  from 8 have B: "x \<notin> vars e" by simp
  from 8 D have C: "x \<notin> dom s'" by (auto split: if_splits)
  from 8 have "subst_vars s' \<subseteq> list_vars (list_subst x e ess)" by (metis unify_ran) 
  with 8 have "x \<notin> subst_vars s'" by (auto split: if_splits)
  with A B C have "ordered_subst (extend_subst x e s')" by simp
  with 8 show ?case by simp
qed auto

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = Some s \<Longrightarrow> ordered_subst s"
  by (simp add: unify_def)

lemma unify_none [simp]: "unify' ess = None \<Longrightarrow> \<nexists>s'. s' unifies\<^sub>l ess"
proof (induction ess rule: unify'_induct)
  case (6 x e ess)
  hence "\<And>s'. \<not> s' unifies Var x and e" by (metis occurs_check)
  thus ?case by simp
next
  case (7 x e ess)
  have "\<And>s. s unifies Var x and e \<Longrightarrow> \<not> s unifies\<^sub>l ess" 
  proof -
    fix s
    assume U: "s unifies Var x and e"
    show "?thesis s" 
    proof (cases "s x")
      case None
      with U have "Var x = subst s e" by simp
      with 7 obtain y where Y: "e = Var y \<and> s y = Some (Var x)" by (metis var_subst)
      with 7 have "\<not> extend_subst x (Var y) s unifies\<^sub>l ess" by simp
      with None Y show ?thesis by simp
    next
      case (Some e')
      hence S: "s(x \<mapsto> e') = s" by auto
      from 7 have "\<not> extend_subst x e (s(x := None)) unifies\<^sub>l ess" by simp
      with 7(2) U Some S show ?thesis by auto
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

lemma [simp]: "unify' ess = Some s \<Longrightarrow> t unifies\<^sub>l ess \<Longrightarrow> \<exists>u. subst t = subst u \<circ> subst s"
proof (induction ess arbitrary: s t rule: unify'_induct)
  case 1
  then show ?case by auto
next
  case (8 x e ess s')
  thus ?case
  proof (cases "t x")
    case None
    with 8 have "Var x = subst t e \<and> t unifies\<^sub>l ess" by simp
    with 8 obtain y where Y: "e = Var y \<and> t y = Some (Var x)" by (metis var_subst)


    from 8 have "x \<notin> vars e" by simp
    from 8 have "unify' (list_subst x e ess) = Some s'" by simp
    from 8 None Y have "\<exists>u. subst t = subst u \<circ> subst s'" by fastforce
    then obtain u where U: "subst t = subst u \<circ> subst s'" by fastforce

  
  
    have "subst u \<circ> subst s' = subst uu \<circ> subst (extend_subst x e s')" by simp
    with 8 U show ?thesis by auto
  next
    case (Some e')
    from 8 have "e \<noteq> Var x" by simp
    from 8 have "x \<notin> vars e" by simp
    from 8 have "unify' (list_subst x e ess) = Some s'" by simp
    from 8 Some have "e' = subst t e \<and> t unifies\<^sub>l ess" by simp


    from 8 Some obtain u where "subst (t(x := None)) = subst u \<circ> subst s'" by fastforce


    have "subst t = subst uu \<circ> subst (extend_subst x e s')" by simp
    with 8 show ?thesis by auto
  qed
qed simp_all

lemma [simp]: "unify e\<^sub>1 e\<^sub>2 = Some s \<Longrightarrow> t unifies e\<^sub>1 and e\<^sub>2 \<Longrightarrow> \<exists>u. subst t = subst u \<circ> subst s"
proof (unfold unify_def)
  assume "t unifies e\<^sub>1 and e\<^sub>2"
  hence "t unifies\<^sub>l [(e\<^sub>1, e\<^sub>2)]" by simp
  moreover assume "unify' [(e\<^sub>1, e\<^sub>2)] = Some s"
  ultimately show ?thesis by simp
qed


end