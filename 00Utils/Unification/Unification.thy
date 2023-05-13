theory Unification
  imports Substitution
begin        

subsection \<open>Unification\<close>

text \<open>Now we define the unification algorithm. It solves its constraints in the standard way (see 
[5]), matching constructors and assembling the unifying substitution. It can only fail if it 
encounters a constructor mismatch, or the occurs check \<open>x \<notin> uvars \<tau>\<close> fails. We must include the 
check, despite its implications for the algorithm's time and space complexity, because without it we 
get bogus "infinite tree" solutions and thereby lose the soundness properties of the algorithm that 
we need for typechecking.\<close>

text \<open>The unification algorithm is by far the most complicated we will encounter - most of the 
others amount to little more than tree-walks over the relevant ASTs - and has the only really 
interesting termination proof. We prove termination via a sequence of three measures. First, the 
number of free variables in the constraint equations: we never add variables, and the fourth 
recursive call eliminates at least one - note the importance of the occurs check here. Second, the
number of constructors in the left-hand sides of the equations: the first recursive call eliminates 
one; so does the second (the restriction to the left-hand side is precisely to ensure that this 
call is smaller); and the third cannot increase it. Finally, the number of equations overall: this 
decreases in the third recursive call.\<close>

function unify :: "constraint \<rightharpoonup> subst" where
  "unify [] = Some Map.empty"
| "unify ((Ctor g\<^sub>1 \<tau>s\<^sub>1, Ctor g\<^sub>2 \<tau>s\<^sub>2) # \<kappa>) = (
    if g\<^sub>1 = g\<^sub>2 \<and> length \<tau>s\<^sub>1 = length \<tau>s\<^sub>2 then unify (zip \<tau>s\<^sub>1 \<tau>s\<^sub>2 @ \<kappa>)
    else None)"
| "unify ((Ctor g \<tau>s, Var x) # \<kappa>) = unify ((Var x, Ctor g \<tau>s) # \<kappa>)"
| "unify ((Var x, \<tau>) # \<kappa>) = (
    if \<tau> = Var x then unify \<kappa>
    else if x \<notin> uvars \<tau> then map_option (extend_subst x \<tau>) (unify (constr_subst x \<tau> \<kappa>))
    else None)"
  by pat_completeness auto
termination
  by (relation "measures [card \<circ> constr_vars, constr_ctor_count, length]") 
     (simp_all add: card_insert_if)

text \<open>We prove a specialized induction principle that more closely matches the structure of the 
algorithm, to ease proving its properties.\<close>

lemma unify_induct [case_names Nil CtorCtorYes CtorCtorNo CtorVar VarSame Occurs VarNo VarYes]: "
  P [] \<Longrightarrow>
  (\<And>g \<tau>s\<^sub>1 \<tau>s\<^sub>2 \<kappa>. length \<tau>s\<^sub>1 = length \<tau>s\<^sub>2 \<Longrightarrow> P (zip \<tau>s\<^sub>1 \<tau>s\<^sub>2 @ \<kappa>) \<Longrightarrow> 
    P ((Ctor g \<tau>s\<^sub>1, Ctor g \<tau>s\<^sub>2) # \<kappa>)) \<Longrightarrow>
  (\<And>g\<^sub>1 g\<^sub>2 \<tau>s\<^sub>1 \<tau>s\<^sub>2 \<kappa>. g\<^sub>1 \<noteq> g\<^sub>2 \<or> length \<tau>s\<^sub>1 \<noteq> length \<tau>s\<^sub>2 \<Longrightarrow> 
    P ((Ctor g\<^sub>1 \<tau>s\<^sub>1, Ctor g\<^sub>2 \<tau>s\<^sub>2) # \<kappa>)) \<Longrightarrow>
  (\<And>x \<tau>s g \<kappa>. P ((Var x, Ctor g \<tau>s) # \<kappa>) \<Longrightarrow> P ((Ctor g \<tau>s, Var x) # \<kappa>)) \<Longrightarrow>
  (\<And>x \<kappa>. P \<kappa> \<Longrightarrow> P ((Var x, Var x) # \<kappa>)) \<Longrightarrow>
  (\<And>x \<tau> \<kappa>. \<tau> \<noteq> Var x \<Longrightarrow> x \<in> uvars \<tau> \<Longrightarrow> P ((Var x, \<tau>) # \<kappa>)) \<Longrightarrow>
  (\<And>x \<tau> \<kappa>. \<tau> \<noteq> Var x \<Longrightarrow> x \<notin> uvars \<tau> \<Longrightarrow> P (constr_subst x \<tau> \<kappa>) \<Longrightarrow> 
    unify (constr_subst x \<tau> \<kappa>) = None \<Longrightarrow> P ((Var x, \<tau>) # \<kappa>)) \<Longrightarrow> 
  (\<And>x \<tau> \<kappa> \<sigma>. \<tau> \<noteq> Var x \<Longrightarrow> x \<notin> uvars \<tau> \<Longrightarrow> P (constr_subst x \<tau> \<kappa>) \<Longrightarrow> 
    unify (constr_subst x \<tau> \<kappa>) = Some \<sigma> \<Longrightarrow> P ((Var x, \<tau>) # \<kappa>)) \<Longrightarrow> 
  P \<kappa>"
proof (induction \<kappa> rule: unify.induct)
  case (2 g\<^sub>1 \<tau>s\<^sub>1 g\<^sub>2 \<tau>s\<^sub>2 \<kappa>)
  thus ?case by (cases "g\<^sub>1 = g\<^sub>2 \<and> length \<tau>s\<^sub>1 = length \<tau>s\<^sub>2") simp_all
next
  case (4 x \<tau> \<kappa>)
  thus ?case 
    by (cases "\<tau> \<noteq> Var x") (cases "x \<notin> uvars \<tau>", cases "unify (constr_subst x \<tau> \<kappa>)", simp_all)
qed simp_all

text \<open>The domain and range of a successful substitution are limited to the variables from the 
constraints, and are distinct from each other (and thus the substitution is idempotent).\<close>

lemma unify_dom [simp]: "unify \<kappa> = Some \<sigma> \<Longrightarrow> dom \<sigma> \<subseteq> constr_vars \<kappa>"
proof (induction \<kappa> arbitrary: \<sigma> rule: unify_induct)
  case (VarYes x \<tau> \<kappa> \<sigma>')
  hence "dom \<sigma>' \<subseteq> constr_vars (constr_subst x \<tau> \<kappa>)" by simp
  hence "dom (extend_subst x \<tau> \<sigma>') \<subseteq> insert x (uvars \<tau> \<union> constr_vars \<kappa>)" by (auto split: if_splits)
  with VarYes show ?case by simp
qed auto

lemma unify_ran [simp]: "unify \<kappa> = Some \<sigma> \<Longrightarrow> subst_vars \<sigma> \<subseteq> constr_vars \<kappa>"
proof (induction \<kappa> arbitrary: \<sigma> rule: unify_induct)
  case (VarYes x \<tau> \<kappa> \<sigma>')
  hence X: "subst_vars \<sigma>' \<subseteq> constr_vars (constr_subst x \<tau> \<kappa>)" by simp
  from VarYes have "dom \<sigma>' \<subseteq> constr_vars (constr_subst x \<tau> \<kappa>)" by (metis unify_dom)
  with VarYes have "x \<notin> dom \<sigma>'" by (auto simp del: constr_subst_no_var split: if_splits)
  hence D: "subst_vars (extend_subst x \<tau> \<sigma>') = uvars (subst \<sigma>' \<tau>) \<union> subst_vars \<sigma>'" by simp
  from X have "uvars \<tau> - dom \<sigma>' \<union> subst_vars \<sigma>' \<subseteq> insert x (uvars \<tau> \<union> constr_vars \<kappa>)" 
    by (auto split: if_splits)
  moreover have "uvars (subst \<sigma>' \<tau>) \<subseteq> uvars \<tau> - dom \<sigma>' \<union> subst_vars \<sigma>'" by simp
  ultimately have Y: "uvars (subst \<sigma>' \<tau>) \<subseteq> insert x (uvars \<tau> \<union> constr_vars \<kappa>)" by blast
  from X have "subst_vars \<sigma>' \<subseteq> insert x (uvars \<tau> \<union> constr_vars \<kappa>)" by (auto split: if_splits)
  with VarYes D Y show ?case by simp
qed auto

lemma unify_idempotent [simp]: "unify \<kappa> = Some \<sigma> \<Longrightarrow> idempotent \<sigma>"
proof (induction \<kappa> arbitrary: \<sigma> rule: unify_induct)
  case (VarYes x \<tau> \<kappa> \<sigma>')
  hence "dom \<sigma>' \<subseteq> constr_vars (constr_subst x \<tau> \<kappa>)" by (metis unify_dom)
  hence D: "dom \<sigma>' \<subseteq> constr_vars \<kappa> - {x} \<union> (if x \<in> constr_vars \<kappa> then uvars \<tau> else {})" by simp
  from VarYes have A: "idempotent \<sigma>'" by simp
  from VarYes have B: "x \<notin> uvars \<tau>" by simp
  from VarYes D have C: "x \<notin> dom \<sigma>'" by (auto simp del: constr_subst_no_var split: if_splits)
  from VarYes have "subst_vars \<sigma>' \<subseteq> constr_vars (constr_subst x \<tau> \<kappa>)" by (metis unify_ran) 
  with VarYes have "x \<notin> subst_vars \<sigma>'" by (auto simp del: constr_subst_no_var split: if_splits)
  with A B C have "idempotent (extend_subst x \<tau> \<sigma>')" by simp
  with VarYes show ?case by simp
qed auto

text \<open>If unification fails, then no substitution could have succeeded:\<close>

lemma unify_none [simp]: "unify \<kappa> = None \<Longrightarrow> \<nexists>\<sigma>. \<sigma> unifies\<^sub>\<kappa> \<kappa>"
proof (induction \<kappa> rule: unify_induct)
  case (Occurs x \<tau> \<kappa>)
  hence "\<And>\<sigma>. \<not> \<sigma> unifies Var x and \<tau>" by (metis occurs_check)
  thus ?case by simp
next
  case (VarNo x \<tau> \<kappa>)
  have "\<And>\<sigma>. \<sigma> unifies Var x and \<tau> \<Longrightarrow> \<not> \<sigma> unifies\<^sub>\<kappa> \<kappa>" 
  proof -
    fix \<sigma>
    assume U: "\<sigma> unifies Var x and \<tau>"
    show "?thesis \<sigma>" 
    proof (cases "\<sigma> x")
      case None
      with U have "subst \<sigma> \<tau> = Var x" by simp
      with VarNo obtain y where Y: "\<tau> = Var y \<and> \<sigma> y = Some (Var x)" by auto
      with VarNo have "\<not> extend_subst x (Var y) \<sigma> unifies\<^sub>\<kappa> \<kappa>" by simp
      with None Y show ?thesis by simp
    next
      case (Some e')
      hence S: "\<sigma>(x \<mapsto> e') = \<sigma>" by auto
      from VarNo have "\<not> extend_subst x \<tau> (\<sigma>(x := None)) unifies\<^sub>\<kappa> \<kappa>" by simp
      with VarNo(2) U Some S show ?thesis by auto
    qed
  qed
  thus ?case by simp
qed simp_all

text \<open>The most crucial property of all: if unification succeeds, then the substitution produced 
really does unify all the constraint equations. In fact, it produces the most general unifier, in 
that any other unifying substitution is a specialization of this one.\<close>
 
lemma unify_some [simp]: "unify \<kappa> = Some \<sigma> \<Longrightarrow> \<sigma> unifies\<^sub>\<kappa> \<kappa>"
  by (induction \<kappa> arbitrary: \<sigma> rule: unify_induct) auto

lemma unify_most_general' [simp]: "unify \<kappa> = Some \<sigma> \<Longrightarrow> \<sigma>' unifies\<^sub>\<kappa> \<kappa> \<Longrightarrow> idempotent \<sigma>' \<Longrightarrow>
  \<exists>u. subst \<sigma>' = subst u \<circ> subst \<sigma> \<and> idempotent u"
proof (induction \<kappa> arbitrary: \<sigma> \<sigma>' rule: unify_induct)
  case Nil
  thus ?case by auto
next
  case (VarYes x \<tau> \<kappa> \<sigma>\<^sub>1)
  hence "dom \<sigma>\<^sub>1 \<subseteq> constr_vars (constr_subst x \<tau> \<kappa>)" by (metis unify_dom)
  with VarYes have D: "x \<notin> dom \<sigma>\<^sub>1" by (auto simp del: constr_subst_no_var split: if_splits)
  from VarYes have "subst_vars \<sigma>\<^sub>1 \<subseteq> constr_vars (constr_subst x \<tau> \<kappa>)" by (metis unify_ran)
  with VarYes have R: "x \<notin> subst_vars \<sigma>\<^sub>1" by (auto simp del: constr_subst_no_var split: if_splits)
  thus ?case
  proof (cases "\<sigma>' x")
    case None
    with VarYes have T: "subst \<sigma>' \<tau> = Var x \<and> \<sigma>' unifies\<^sub>\<kappa> \<kappa>" by simp
    with VarYes obtain y where Y: "\<tau> = Var y \<and> \<sigma>' y = Some (Var x)" by fastforce
    with None T have "\<sigma>' unifies\<^sub>\<kappa> constr_subst x (Var y) \<kappa>" by simp
    with VarYes Y obtain \<sigma>\<^sub>2 where U: "subst \<sigma>' = subst \<sigma>\<^sub>2 \<circ> subst \<sigma>\<^sub>1 \<and> idempotent \<sigma>\<^sub>2" by fastforce
    from None have "x \<notin> dom \<sigma>'" by auto
    with D U have X: "x \<notin> dom \<sigma>\<^sub>2" by (metis split_not_in_domain)
    from T Y U have "(subst \<sigma>\<^sub>2 \<circ> subst \<sigma>\<^sub>1) (Var y) = Var x" by simp
    thus ?thesis
    proof (induction rule: subst_subst_var)
      case Eq
      with VarYes Y show ?case by simp
    next
      case FstOnly
      have "subst \<sigma>\<^sub>2 \<circ> subst \<sigma>\<^sub>1 = subst \<sigma>\<^sub>2 \<circ> subst [x \<mapsto> Var x] \<circ> subst \<sigma>\<^sub>1" by simp
      with D R Y U FstOnly have "subst \<sigma>' = subst \<sigma>\<^sub>2 \<circ> subst \<sigma>\<^sub>1 \<circ> subst [x \<mapsto> \<tau>] \<and> idempotent \<sigma>\<^sub>2"
        using comp_assoc by blast
      with VarYes show ?case by (auto simp add: expand_extend_subst)
    next
      case SndOnly
      with X have "subst \<sigma>\<^sub>2 \<circ> subst \<sigma>\<^sub>1 = subst \<sigma>\<^sub>2 \<circ> subst [y \<mapsto> Var x] \<circ> subst \<sigma>\<^sub>1" by simp
      hence "subst \<sigma>\<^sub>2 \<circ> subst \<sigma>\<^sub>1 = subst (extend_subst y (Var x) \<sigma>\<^sub>2) \<circ> subst [x \<mapsto> Var y] \<circ> subst \<sigma>\<^sub>1" 
        by (simp add: expand_extend_subst comp_assoc)
      with D R Y U SndOnly have S: "subst \<sigma>' = 
        subst (extend_subst y (Var x) \<sigma>\<^sub>2) \<circ> subst \<sigma>\<^sub>1 \<circ> subst [x \<mapsto> \<tau>]" by (simp add: comp_assoc)
      from SndOnly X have "\<sigma>\<^sub>2 y = Some (case \<sigma>\<^sub>2 x of None \<Rightarrow> Var x | Some \<tau> \<Rightarrow> \<tau>)" 
        by (auto split: option.splits)
      with VarYes U have "idempotent (extend_subst y (Var x) \<sigma>\<^sub>2)" by simp
      moreover from VarYes S have "subst \<sigma>' = subst (extend_subst y (Var x) \<sigma>\<^sub>2) \<circ> subst \<sigma>" 
        by (auto simp add: expand_extend_subst)
      ultimately show ?case by blast
    next
      case (Both z)
      with X have "subst \<sigma>\<^sub>2 \<circ> subst \<sigma>\<^sub>1 = subst (extend_subst x (Var z) \<sigma>\<^sub>2) \<circ> subst \<sigma>\<^sub>1" by auto
      hence Z: "subst \<sigma>\<^sub>2 \<circ> subst \<sigma>\<^sub>1 = subst \<sigma>\<^sub>2 \<circ> subst [x \<mapsto> Var z] \<circ> subst \<sigma>\<^sub>1" 
        by (simp add: expand_extend_subst)
      from D R Both have "subst \<sigma>\<^sub>1 \<circ> subst [x \<mapsto> Var y] = subst [x \<mapsto> Var z] \<circ> subst \<sigma>\<^sub>1" by simp
      with U Z have "subst \<sigma>' = subst \<sigma>\<^sub>2 \<circ> subst \<sigma>\<^sub>1 \<circ> subst [x \<mapsto> Var y]" by (metis comp_assoc)
      with Y have S: "subst \<sigma>' = subst \<sigma>\<^sub>2 \<circ> subst \<sigma>\<^sub>1 \<circ> subst [x \<mapsto> \<tau>]" by simp
      from U have "idempotent \<sigma>\<^sub>2" by simp
      with VarYes S show ?case by (auto simp add: expand_extend_subst)
  qed
  next
    case (Some \<tau>')
    with VarYes have "\<tau>' = subst \<sigma>' \<tau> \<and> \<sigma>' unifies\<^sub>\<kappa> \<kappa>" by simp
    with VarYes Some obtain \<sigma>\<^sub>2 where T: "\<sigma>' = extend_subst x \<tau> \<sigma>\<^sub>2 \<and> \<sigma>\<^sub>2 unifies\<^sub>\<kappa> constr_subst x \<tau> \<kappa> \<and> 
      idempotent \<sigma>\<^sub>2" by (metis dissect_subst)
    with VarYes obtain \<sigma>\<^sub>3 where "subst \<sigma>\<^sub>2 = subst \<sigma>\<^sub>3 \<circ> subst \<sigma>\<^sub>1 \<and> idempotent \<sigma>\<^sub>3" by fastforce
    with VarYes T show ?thesis by (auto simp add: expand_extend_subst)
  qed
qed simp_all

lemma unify_most_general [simp]: "\<sigma> unifies\<^sub>\<kappa> \<kappa> \<Longrightarrow> idempotent \<sigma> \<Longrightarrow> 
  \<exists>\<sigma>'. unify \<kappa> = Some \<sigma>' \<and> \<sigma> specializes \<sigma>'"
proof (cases "unify \<kappa>")
  case None
  moreover assume "\<sigma> unifies\<^sub>\<kappa> \<kappa>"
  ultimately show ?thesis by (metis unify_none)
next
  case (Some \<sigma>')
  assume "\<sigma> unifies\<^sub>\<kappa> \<kappa>" and "idempotent \<sigma>"
  with Some obtain u where "subst \<sigma> = subst u \<circ> subst \<sigma>' \<and> idempotent u" by fastforce
  hence "\<sigma> specializes \<sigma>'" by (auto simp add: subst_specialize_def)
  with Some show ?thesis by fastforce
qed

text \<open>Finally, we prove some facts about unifying appended systems of equations: if it succeeds, 
then both halves must also succeed independently.\<close>

lemma unify_append_fst [simp]: "unify (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2) = Some \<sigma> \<Longrightarrow> 
    \<exists>s\<^sub>1. unify \<kappa>\<^sub>1 = Some s\<^sub>1 \<and> \<sigma> specializes s\<^sub>1"
  by (induction \<kappa>\<^sub>1 arbitrary: \<kappa>\<^sub>2 \<sigma> rule: unify_induct) auto

lemma unify_append_none [simp]: "unify \<kappa>\<^sub>1 = None \<Longrightarrow> unify (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2) = None"
  by (induction \<kappa>\<^sub>1 arbitrary: \<kappa>\<^sub>2 rule: unify_induct) auto

lemma unify_constr_subst [simp]: "unify (constr_subst x \<tau> \<kappa>) = Some \<sigma> \<Longrightarrow> x \<notin> uvars \<tau> \<Longrightarrow> 
  \<exists>\<sigma>'. unify \<kappa> = Some \<sigma>' \<and> extend_subst x \<tau> \<sigma> specializes \<sigma>'"
proof -
  assume U: "unify (constr_subst x \<tau> \<kappa>) = Some \<sigma>" 
  hence L: "\<sigma> unifies\<^sub>\<kappa> constr_subst x \<tau> \<kappa>" and O: "idempotent \<sigma>" by (metis unify_some, simp)
  assume X: "x \<notin> uvars \<tau>"
  hence "x \<notin> constr_vars \<kappa> - {x} \<union> (if x \<in> constr_vars \<kappa> then uvars \<tau> else {})" by simp
  moreover from U have "dom \<sigma> \<subseteq> constr_vars (constr_subst x \<tau> \<kappa>)" by (metis unify_dom)
  moreover from U have "subst_vars \<sigma> \<subseteq> constr_vars (constr_subst x \<tau> \<kappa>)" by (metis unify_ran)
  ultimately have "x \<notin> dom \<sigma>" and "x \<notin> subst_vars \<sigma>" by auto
  with O X L show ?thesis by simp
qed

lemma unify_append_snd [simp]: "unify (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2) = Some \<sigma> \<Longrightarrow> 
    \<exists>s\<^sub>2. unify \<kappa>\<^sub>2 = Some s\<^sub>2 \<and> \<sigma> specializes s\<^sub>2"
proof (induction \<kappa>\<^sub>1 arbitrary: \<kappa>\<^sub>2 \<sigma> rule: unify_induct)
  case (VarYes x \<tau> \<kappa> \<sigma>')
  then obtain t where T: "unify (constr_subst x \<tau> \<kappa> @ constr_subst x \<tau> \<kappa>\<^sub>2) = Some t \<and> 
    extend_subst x \<tau> t = \<sigma>" by fastforce
  with VarYes obtain u where U: "unify (constr_subst x \<tau> \<kappa>\<^sub>2) = Some u \<and> t specializes u" 
    by fastforce
  moreover with VarYes obtain s\<^sub>2 where "unify \<kappa>\<^sub>2 = Some s\<^sub>2 \<and> extend_subst x \<tau> u specializes s\<^sub>2" 
    by fastforce
  moreover with U have "extend_subst x \<tau> t specializes extend_subst x \<tau> u" by simp
  ultimately have "unify \<kappa>\<^sub>2 = Some s\<^sub>2 \<and> extend_subst x \<tau> t specializes s\<^sub>2" by fastforce
  with T show ?case by fastforce
qed (simp_all split: if_splits)

text \<open>We also define an unsatisfiable constraint. There are any number of ways of doing this; we 
assert that \<open>a() =? b ()\<close>\<close>

definition fail :: constraint where
  "fail \<equiv> [(Ctor ''a'' [], Ctor ''b'' [])]"

lemma cannot_unify_fail [simp]: "unify fail = None"
  by (simp add: fail_def)

lemma no_vars_in_fail [simp]: "constr_vars fail = {}"
  by (simp add: fail_def)

end