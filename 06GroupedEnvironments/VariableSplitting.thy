theory VariableSplitting
  imports GroupedEnvironments "../05Closure/Closure"
begin

section \<open>Variable splitting\<close>

text \<open>Now we divide our variables into frame-offset pairs. The process is quite simple for 
expressions: we accumulate a map from Debruijn indices to frame-offset pairs, adding to it every 
time we pass a binder, and then map variables when we reach them. (As mentioned before, we also 
record the frame-size every time we reach a \<open>Lam\<^sub>d\<close>.)\<close>

abbreviation map_past_let :: "(nat \<rightharpoonup> nat \<times> nat) \<Rightarrow> nat \<Rightarrow> nat \<rightharpoonup> nat \<times> nat" where
  "map_past_let \<Phi> n \<equiv> case_nat (Some (0, n)) \<Phi>"

abbreviation map_past_lam :: "(nat \<rightharpoonup> nat \<times> nat) \<Rightarrow> nat \<rightharpoonup> nat \<times> nat" where
  "map_past_lam \<Phi> \<equiv> case_nat (Some (0, 0)) (map_option (apfst Suc) \<circ> \<Phi>)"

primrec split_vars' :: "(nat \<rightharpoonup> nat \<times> nat) \<Rightarrow> nat \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>g" where
  "split_vars' \<Phi> n (Var\<^sub>d x) = (case the (\<Phi> x) of (y, z) \<Rightarrow> Var\<^sub>g y z)"
| "split_vars' \<Phi> n (Const\<^sub>d m) = Const\<^sub>g m"
| "split_vars' \<Phi> n (Lam\<^sub>d t e) = (
    let e\<^sub>g = split_vars' (map_past_lam \<Phi>) 1 e 
    in Lam\<^sub>g t e\<^sub>g (let_count e\<^sub>g))"
| "split_vars' \<Phi> n (App\<^sub>d e\<^sub>1 e\<^sub>2) = App\<^sub>g (split_vars' \<Phi> n e\<^sub>1) (split_vars' \<Phi> n e\<^sub>2)"
| "split_vars' \<Phi> n (Let\<^sub>d e\<^sub>1 e\<^sub>2) = 
    Let\<^sub>g (split_vars' \<Phi> n e\<^sub>1) (split_vars' (map_past_let \<Phi> n) (Suc n) e\<^sub>2)"

definition split_vars :: "expr\<^sub>d \<Rightarrow> expr\<^sub>g" where
  "split_vars e \<equiv> split_vars' Map.empty 0 e"

lemma non_redex_split_vars [simp]: "non_redex\<^sub>g (split_vars' \<Phi> n e) = (is_var\<^sub>d e \<or> value\<^sub>d e)"
  by (induction e arbitrary: \<Phi>) (simp_all add: Let_def split: prod.splits)

lemma let_free_split_vars [simp]: "let_free\<^sub>g (split_vars' \<Phi> n e) = let_free\<^sub>d e"
  by (induction e arbitrary: \<Phi>) (simp_all add: Let_def split: prod.splits)

lemma let_floated_split_vars' [simp]: "let_floated\<^sub>g (split_vars' \<Phi> n e) = let_floated\<^sub>d e"
  by (induction e arbitrary: \<Phi> n) (simp_all add: Let_def split: prod.splits)

lemma let_floated_split_vars [simp]: "let_floated\<^sub>g (split_vars e) = let_floated\<^sub>d e"
  by (simp add: split_vars_def)

lemma let_count_split_vars [simp]: "let_count (split_vars' \<Phi> n e) = length (strip_lets e)"
  by (induction e arbitrary: \<Phi> n) (simp_all add: Let_def split: prod.splits)

text \<open>With the help of an auxiliary function to generate the splitting map from an environment, we
can prove type-safety as well.\<close>

fun inv_map_from_env :: "'a list list \<Rightarrow> nat \<rightharpoonup> nat \<times> nat" where
  "inv_map_from_env [] x = None"
| "inv_map_from_env (bs # bss) x = (
    if x < length bs then Some (0, length bs - Suc x) 
    else map_option (apfst Suc) (inv_map_from_env bss (x - length bs)))"

lemma inv_map_from_env_empty [simp]: "inv_map_from_env [[]] = Map.empty"
  by auto

lemma inv_map_from_env_insert [simp]: "inv_map_from_env (insert_at 0 [a] as) = 
    map_past_lam (inv_map_from_env as)"
  by (induction as) (auto split: nat.splits)

lemma inv_map_from_env_snoc' [simp]: "as \<noteq> [] \<Longrightarrow> 
    inv_map_from_env (snoc_fst a as) x = map_past_let (inv_map_from_env as) (length (hd as)) x"
  by (induction as) (simp_all split: nat.splits)

lemma inv_map_from_env_snoc [simp]: "as \<noteq> [] \<Longrightarrow> 
    inv_map_from_env (snoc_fst a as) = map_past_let (inv_map_from_env as) (length (hd as))"
  by auto

lemma lookup_inv_map [simp]: "lookup (concat (map rev \<Gamma>)) x = Some t \<Longrightarrow> 
  \<exists>y z ts. inv_map_from_env \<Gamma> x = Some (y, z) \<and> lookup \<Gamma> y = Some ts \<and> lookup ts z = Some t"
proof (induction \<Gamma> arbitrary: x)
  case (Cons ts \<Gamma>)
  thus ?case
  proof (cases "x < length ts")
    case False
    hence "\<exists>k. x = length ts + k" by presburger
    then obtain k where K: "x = length ts + k" by auto
    with Cons obtain y z ts' where "inv_map_from_env \<Gamma> k = Some (y, z) \<and> lookup \<Gamma> y = Some ts' \<and> 
      lookup ts' z = Some t" by fastforce
    with False K show ?thesis by auto
  qed auto
qed simp_all

lemma typecheck_split' [simp]: "concat (map rev \<Gamma>) \<turnstile>\<^sub>d e : t \<Longrightarrow> let_free\<^sub>d e \<or> \<Gamma> \<noteq> [] \<Longrightarrow>
  \<Gamma> \<turnstile>\<^sub>g split_vars' (inv_map_from_env \<Gamma>) (length (hd \<Gamma>)) e : t"
proof (induction "concat (map rev \<Gamma>)" e t arbitrary: \<Gamma> rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_var x t)
  hence "lookup (concat (map rev \<Gamma>)) x = Some t" by simp
  then obtain y z ts where "inv_map_from_env \<Gamma> x = Some (y, z) \<and> lookup \<Gamma> y = Some ts \<and> 
    lookup ts z = Some t" by (metis lookup_inv_map)
  thus ?case by simp
next
  case (tc\<^sub>d_lam t\<^sub>1 e t\<^sub>2)
  moreover hence "let_free\<^sub>d e \<or> insert_at 0 [t\<^sub>1] \<Gamma> \<noteq> []" by (cases \<Gamma>) simp_all
  moreover have "insert_at 0 t\<^sub>1 (concat (map rev \<Gamma>)) = concat (map rev (insert_at 0 [t\<^sub>1] \<Gamma>))" 
    by simp
  ultimately have "insert_at 0 [t\<^sub>1] \<Gamma> \<turnstile>\<^sub>g 
    split_vars' (inv_map_from_env (insert_at 0 [t\<^sub>1] \<Gamma>)) (length (hd (insert_at 0 [t\<^sub>1] \<Gamma>))) e : t\<^sub>2" 
      by blast
  thus ?case by (simp add: Let_def del: let_count_split_vars)
qed fastforce+

lemma typecheck_split [simp]:  "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> [[]] \<turnstile>\<^sub>g split_vars e : t"
proof (unfold split_vars_def)
  assume "[] \<turnstile>\<^sub>d e : t" 
  hence "(concat (map rev [[]]) \<turnstile>\<^sub>d e : t)" by simp
  hence "[[]] \<turnstile>\<^sub>g split_vars' (inv_map_from_env [[]]) (length (hd [[]])) e : t" 
    using typecheck_split' by fastforce
  thus "[[]] \<turnstile>\<^sub>g split_vars' Map.empty 0 e : t" by simp
qed

text \<open>The problem arises when we try to map closures (and, for the same reason, the callstack). We 
have an environment and an expression to be evaluated in that environment; we need to split the 
environment up somehow. But the closure is contextless: unlike an expression, which sits within a 
larger expression from which we can determine the structure of its environment, a closure's 
environment is complete in itself, and provides no information about how it was constructed. 
The same closure could group to multiple different legitimate grouped-environment closures. So we 
cannot run the splitting process on the whole of the state.\<close>

text \<open>Instead, we define the inverse, combining operation. First we define it on expressions:\<close>

abbreviation inv_map_past_lam :: "(nat \<times> nat \<rightharpoonup> nat) \<Rightarrow> nat \<times> nat \<rightharpoonup> nat" where
  "inv_map_past_lam \<Phi> x \<equiv> (case x of 
      (0, 0) \<Rightarrow> Some 0 
    | (0, Suc z) \<Rightarrow> None
    | (Suc y, z) \<Rightarrow> map_option Suc (\<Phi> (y, z)))"

abbreviation inv_map_past_let :: "(nat \<times> nat \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> nat \<times> nat \<rightharpoonup> nat" where
  "inv_map_past_let \<Phi> n x \<equiv> (if x = (0, n) then Some 0 else map_option Suc (\<Phi> x))"

primrec combine_vars' :: "(nat \<times> nat \<rightharpoonup> nat) \<Rightarrow> nat \<Rightarrow> expr\<^sub>g \<Rightarrow> expr\<^sub>d" where
  "combine_vars' \<Phi> n (Var\<^sub>g x y) = Var\<^sub>d (the (\<Phi> (x, y)))"
| "combine_vars' \<Phi> n (Const\<^sub>g m) = Const\<^sub>d m"
| "combine_vars' \<Phi> n (Lam\<^sub>g t e m) = Lam\<^sub>d t (combine_vars' (inv_map_past_lam \<Phi>) 1 e)"
| "combine_vars' \<Phi> n (App\<^sub>g e\<^sub>1 e\<^sub>2) = App\<^sub>d (combine_vars' \<Phi> n e\<^sub>1) (combine_vars' \<Phi> n e\<^sub>2)"
| "combine_vars' \<Phi> n (Let\<^sub>g e\<^sub>1 e\<^sub>2) = 
    Let\<^sub>d (combine_vars' \<Phi> n e\<^sub>1) (combine_vars' (inv_map_past_let \<Phi> n) (Suc n) e\<^sub>2)"

definition combine_vars :: "expr\<^sub>g \<Rightarrow> expr\<^sub>d" where
  "combine_vars e \<equiv> combine_vars' Map.empty 0 e"

lemma non_redex_combine_vars [simp]: "
    (is_var\<^sub>d (combine_vars' \<Phi> n e) \<or> value\<^sub>d (combine_vars' \<Phi> n e)) = non_redex\<^sub>g e"
  by (induction e arbitrary: \<Phi>) simp_all

lemma let_free_combine_vars [simp]: "let_free\<^sub>d (combine_vars' \<Phi> n e) = let_free\<^sub>g e"
  by (induction e arbitrary: \<Phi>) simp_all

lemma let_floated_combine_vars [simp]: "let_floated\<^sub>d (combine_vars' \<Phi> n e) = let_floated\<^sub>g e"
  by (induction e arbitrary: \<Phi> n) simp_all

lemma let_count_combine_vars [simp]: "length (strip_lets (combine_vars' \<Phi> n e)) = let_count e"
  by (induction e arbitrary: \<Phi> n) simp_all

text \<open>We can prove (in \<open>combine_split_cancel\<close> and \<open>split_combine_cancel\<close>) that our two operations 
split and combine are inverses; or at least, are inverses on closed expressions (as shown by their 
typechecking in the empty context).\<close>

lemma inv_map_past_lam_inv [simp]: "(\<And>x y. \<Phi> x = Some y \<Longrightarrow> \<Phi>' y = Some x) \<Longrightarrow> 
    map_past_lam \<Phi> x = Some y \<Longrightarrow> inv_map_past_lam \<Phi>' y = Some x"
  by (cases x) auto

lemma inv_inv_map_past_lam_inv [simp]: "(\<And>x y. \<Phi> x = Some y \<Longrightarrow> \<Phi>' y = Some x) \<Longrightarrow> 
    inv_map_past_lam \<Phi> x = Some y \<Longrightarrow> map_past_lam \<Phi>' y = Some x"
  by (cases x) (auto split: nat.splits)

abbreviation initially_bounded :: "(nat \<rightharpoonup> nat \<times> nat) \<Rightarrow> nat \<Rightarrow> bool" where
  "initially_bounded \<Phi> n \<equiv> (\<forall>x m. \<Phi> x = Some (0, m) \<longrightarrow> m < n)"

lemma inv_map_past_let_inv [simp]: "(\<And>x y. \<Phi> x = Some y \<Longrightarrow> \<Phi>' y = Some x) \<Longrightarrow> 
  initially_bounded \<Phi> n \<Longrightarrow> map_past_let \<Phi> n x = Some y \<Longrightarrow> 
    inv_map_past_let \<Phi>' n y = Some x"
  by (auto split: nat.splits)

lemma inv_inv_map_past_let_inv [simp]: "(\<And>x y. \<Phi> x = Some y \<Longrightarrow> \<Phi>' y = Some x) \<Longrightarrow> 
    inv_map_past_let \<Phi> n x = Some y \<Longrightarrow> map_past_let \<Phi>' n y = Some x"
  by (cases x) (auto split: if_splits)

lemma dom_map_past_lam [simp]: "dom (map_past_lam \<Phi>) = insert 0 (Suc ` dom \<Phi>)"
proof (auto simp add: dom_def split: nat.splits)
  fix x
  show "x \<notin> Suc ` {a. \<exists>aa b. \<Phi> a = Some (aa, b)} \<Longrightarrow> 
    \<forall>x2. x = Suc x2 \<longrightarrow> (\<exists>b a. \<Phi> x2 = Some (a, b)) \<Longrightarrow> x = 0" by (cases x) auto
qed

lemma dom_map_past_let [simp]: "dom (map_past_let \<Phi> n) = insert 0 (Suc ` dom \<Phi>)"
proof (auto simp add: dom_def split: nat.splits)
  fix x
  show "x \<notin> Suc ` {a. \<exists>aa b. \<Phi> a = Some (aa, b)} \<Longrightarrow>
    \<forall>x2. x = Suc x2 \<longrightarrow> (\<exists>a b. \<Phi> x2 = Some (a, b)) \<Longrightarrow> x = 0" by (cases x) auto
qed

lemma dom_inv_map_past_lam [simp]: "dom (inv_map_past_lam \<Phi>) = insert (0, 0) (apfst Suc ` dom \<Phi>)"
  by (auto simp add: dom_def image_iff split: nat.splits) force+

lemma dom_inv_map_past_let [simp]: "dom (inv_map_past_let \<Phi> n) = insert (0, n) (dom \<Phi>)"
  by (simp add: dom_def)

lemma not_at_limit_past_let [simp]: "initially_bounded \<Phi> n \<Longrightarrow> 
    initially_bounded (map_past_let \<Phi> n) (Suc n)"
  by (auto split: nat.splits) fastforce

lemma not_at_limit_past_lam [simp]: "initially_bounded (map_past_lam \<Phi>) (Suc 0)"
  by (auto split: nat.splits)

lemma combine_split_cancel' [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> dom \<Phi> = dom (lookup \<Gamma>) \<Longrightarrow> 
  (\<And>x y. \<Phi> x = Some y \<Longrightarrow> \<Phi>' y = Some x) \<Longrightarrow> initially_bounded \<Phi> n \<Longrightarrow> 
    combine_vars' \<Phi>' n (split_vars' \<Phi> n e) = e"
proof (induction \<Gamma> e t arbitrary: \<Phi> \<Phi>' n rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_var \<Gamma> x t)
  moreover hence "x \<in> dom \<Phi>" by auto
  ultimately show ?case by fastforce
next
  case (tc\<^sub>d_lam t\<^sub>1 \<Gamma> e t\<^sub>2)
  moreover hence "\<And>x y. map_past_lam \<Phi> x = Some y \<Longrightarrow> inv_map_past_lam \<Phi>' y = Some x"
    using inv_map_past_lam_inv by fastforce
  moreover from tc\<^sub>d_lam have "dom (map_past_lam \<Phi>) = dom (lookup (insert_at 0 t\<^sub>1 \<Gamma>))" by simp
  moreover have "initially_bounded (map_past_lam \<Phi>) (Suc 0)" by (metis not_at_limit_past_lam)
  ultimately show ?case by (simp add: Let_def)
next
  case (tc\<^sub>d_let \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
  moreover from tc\<^sub>d_let(6, 7) have "\<And>x y. map_past_let \<Phi> n x = Some y \<Longrightarrow> 
    inv_map_past_let \<Phi>' n y = Some x" 
      using inv_map_past_let_inv by fastforce
  ultimately show ?case by simp
qed simp_all
     
lemma combine_split_cancel_empty [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> 
  combine_vars' Map.empty 0 (split_vars' Map.empty 0 e) = e" 
proof -
  assume "[] \<turnstile>\<^sub>d e : t" 
  moreover have "dom Map.empty = dom (lookup [])" by simp
  moreover have "\<And>x y. Map.empty x = Some y \<Longrightarrow> Map.empty y = Some x" by simp
  moreover have "initially_bounded Map.empty 0" by simp
  ultimately show ?thesis using combine_split_cancel' by fastforce
qed

lemma combine_split_cancel [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> combine_vars (split_vars e) = e" 
  by (simp add: combine_vars_def split_vars_def)

lemma split_combine_cancel' [simp]: "\<Gamma> \<turnstile>\<^sub>g e : t \<Longrightarrow> (\<And>x y. \<Phi> x = Some y \<Longrightarrow> \<Phi>' y = Some x) \<Longrightarrow>  
  dom \<Phi> = {xy. \<exists>z. lookup \<Gamma> (fst xy) = Some z \<and> snd xy \<in> dom (lookup z)} \<Longrightarrow> 
  lookup \<Gamma> 0 = Some ts \<Longrightarrow> split_vars' \<Phi>' (length ts) (combine_vars' \<Phi> (length ts) e) = e"
proof (induction \<Gamma> e t arbitrary: \<Phi> \<Phi>' ts rule: typing\<^sub>g.induct)
  case (tc\<^sub>g_var \<Gamma> x ts y t)
  hence "(x, y) \<in> dom \<Phi>" by auto
  with tc\<^sub>g_var show ?case by fastforce
next
  case (tc\<^sub>g_lam t\<^sub>1 \<Gamma> e t\<^sub>2)
  hence X: "\<And>x y. inv_map_past_lam \<Phi> x = Some y \<Longrightarrow> map_past_lam \<Phi>' y = Some x" 
    using inv_inv_map_past_lam_inv by fastforce
  have Y: "lookup (insert_at 0 [t\<^sub>1] \<Gamma>) 0 = Some [t\<^sub>1]" by simp
  have "\<And>xy. (xy = (0, 0) \<or> 
    (\<exists>a b. (\<exists>z. lookup \<Gamma> a = Some z \<and> b \<in> dom (lookup z)) \<and> xy = (Suc a, b))) =
    (\<exists>z. lookup ([t\<^sub>1] # \<Gamma>) (fst xy) = Some z \<and> snd xy \<in> dom (lookup z))" 
  proof 
    fix xy
    assume "\<exists>z. lookup ([t\<^sub>1] # \<Gamma>) (fst xy) = Some z \<and> snd xy \<in> dom (lookup z)"
    moreover obtain x y where X: "xy = (x, y)" by fastforce
    ultimately obtain z where "lookup ([t\<^sub>1] # \<Gamma>) x = Some z \<and> y \<in> dom (lookup z)" by auto
    with X show "xy = (0, 0) \<or> 
      (\<exists>a b. (\<exists>z. lookup \<Gamma> a = Some z \<and> b \<in> dom (lookup z)) \<and> xy = (Suc a, b))" 
        by (cases x, cases y) auto
  qed auto
  with tc\<^sub>g_lam have "\<And>xy. xy \<in> insert (0, 0) (apfst Suc ` dom \<Phi>) =
    (xy \<in> {xy. \<exists>z. lookup (insert_at 0 [t\<^sub>1] \<Gamma>) (fst xy) = Some z \<and> snd xy \<in> dom (lookup z)})" 
      by (cases \<Gamma>) (simp_all add: image_iff)
  hence "insert (0, 0) (apfst Suc ` dom \<Phi>) =
    {xy. \<exists>z. lookup (insert_at 0 [t\<^sub>1] \<Gamma>) (fst xy) = Some z \<and> snd xy \<in> dom (lookup z)}" 
    by (rule set_eqI)
  with tc\<^sub>g_lam X Y have "split_vars' (map_past_lam \<Phi>') (Suc 0) 
    (combine_vars' (inv_map_past_lam \<Phi>) (Suc 0) e) = e" by fastforce
  thus ?case by (simp add: Let_def)
next
  case (tc\<^sub>g_let \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
  hence X: "\<And>x y. inv_map_past_let \<Phi> (length ts) x = Some y \<Longrightarrow> 
    map_past_let \<Phi>' (length ts) y = Some x" using inv_inv_map_past_let_inv by fastforce
  have "\<And>xy. (xy \<in> insert (0, length ts) (dom (\<lambda>x. map_option Suc (\<Phi> x)))) =
    (xy \<in> {xy. \<exists>z. (case fst xy of 0 \<Rightarrow> (case lookup \<Gamma> 0 of None \<Rightarrow> Some [t\<^sub>1] 
        | Some aa \<Rightarrow> Some (aa @ [t\<^sub>1])) | Suc x' \<Rightarrow> lookup \<Gamma> (fst xy)) = Some z \<and> 
      snd xy \<in> dom (lookup z)})" 
  proof -
    fix xy
    from tc\<^sub>g_let(7) have "(xy = (0, length ts) \<or> (\<exists>z. lookup \<Gamma> (fst xy) = Some z \<and> 
      snd xy \<in> dom (lookup z))) =
    (\<exists>z. (case fst xy of 0 \<Rightarrow> (case lookup \<Gamma> 0 of None \<Rightarrow> Some [t\<^sub>1] | Some aa \<Rightarrow> Some (aa @ [t\<^sub>1]))
          | Suc x' \<Rightarrow> lookup \<Gamma> (fst xy)) =
         Some z \<and>
         snd xy \<in> dom (lookup z))" 
      using lookup_down_lemma by (cases xy) (auto split: nat.splits option.splits, fastforce)
    with tc\<^sub>g_let show "?thesis xy" by (simp add: dom_map_option)
  qed
  hence "insert (0, length ts) (dom (\<lambda>x. map_option Suc (\<Phi> x))) =
    {xy. \<exists>z. (case fst xy of 0 \<Rightarrow> (case lookup \<Gamma> 0 of None \<Rightarrow> Some [t\<^sub>1] 
        | Some aa \<Rightarrow> Some (aa @ [t\<^sub>1])) | Suc x' \<Rightarrow> lookup \<Gamma> (fst xy)) = Some z \<and> 
      snd xy \<in> dom (lookup z)}" by blast
  with tc\<^sub>g_let X show ?case by fastforce
qed simp_all

lemma split_combine_cancel [simp]: "[[]] \<turnstile>\<^sub>g e : t \<Longrightarrow> split_vars (combine_vars e) = e"
proof (unfold combine_vars_def split_vars_def)
  assume "[[]] \<turnstile>\<^sub>g e : t"
  moreover have "\<And>x y. Map.empty x = Some y \<Longrightarrow> Map.empty y = Some x" by simp 
  moreover have "dom Map.empty = {xy. \<exists>z. lookup [[]] (fst xy) = Some z \<and> snd xy \<in> dom (lookup z)}" 
    using lookup.elims option.simps(3) by force
  moreover have "lookup [[]] 0 = Some []" by simp
  ultimately show "split_vars' Map.empty 0 (combine_vars' Map.empty 0 e) = e"
    by (smt split_combine_cancel' Collect_cong list.size(3))
qed

text \<open>Now, we can define our combining function on closures, callstacks, and states. The 
environments contained in the closures, which caused so much difficulties the other way around, are 
simply concatenated together.\<close>

fun map_from_env :: "'a list list \<Rightarrow> nat \<times> nat \<rightharpoonup> nat" where
  "map_from_env [] (x, y) = None"
| "map_from_env (cs # \<Delta>) (0, y) = (if y < length cs then Some (length cs - Suc y) else None)"
| "map_from_env (cs # \<Delta>) (Suc x, y) = map_option ((+) (length cs)) (map_from_env \<Delta> (x, y))"

lemma map_from_env_empty [simp]: "map_from_env [] = Map.empty"
  by auto

lemma map_from_env_cons_empty' [simp]: "map_from_env [[]] x = None"
proof (cases x)
  case (Pair x y)
  thus ?thesis by (cases x) simp_all
qed

lemma map_from_env_cons_empty [simp]: "map_from_env [[]] = Map.empty"
  by auto

lemma lookup_map_from_env [simp]: "lookup \<Delta> x = Some cs \<Longrightarrow> lookup cs y = Some c \<Longrightarrow> 
    map_from_env \<Delta> (x, y) \<noteq> None"
  by (induction \<Delta> "(x, y)" arbitrary: x y rule: map_from_env.induct) simp_all

lemma lookup_concat_map_from_env [simp]: "lookup \<Delta> x = Some cs \<Longrightarrow> lookup cs y = Some c \<Longrightarrow> 
    lookup (concat (map rev \<Delta>)) (the (map_from_env \<Delta> (x, y))) = Some c"
proof (induction \<Delta> "(x, y)" arbitrary: x y rule: map_from_env.induct)
  case (3 cs \<Delta> x y)
  then show ?case by (cases "map_from_env \<Delta> (x, y)") simp_all
qed simp_all

primrec combine_closure :: "closure\<^sub>g \<Rightarrow> closure\<^sub>c" where
  "combine_closure (Num\<^sub>g n) = Const\<^sub>c n"
| "combine_closure (Fun\<^sub>g t \<Delta> e n) = 
    Lam\<^sub>c t (concat (map rev (map (map combine_closure) \<Delta>))) 
      (combine_vars' (inv_map_past_lam (map_from_env \<Delta>)) 1 e)"

abbreviation combine_env :: "closure\<^sub>g list list \<Rightarrow> closure\<^sub>c list" where
  "combine_env \<Delta> \<equiv> concat (map (rev \<circ> map combine_closure) \<Delta>)"

fun combine_stack' :: "frame\<^sub>g list \<Rightarrow> frame\<^sub>c list \<times> nat" where
  "combine_stack' [] = ([], 0)" 
| "combine_stack' (FApp1\<^sub>g \<Delta> e # s) = (
    let (s', n) = combine_stack' s
    in (FApp1\<^sub>c (combine_env \<Delta>) (combine_vars' (map_from_env \<Delta>) n e) # s', n))"
| "combine_stack' (FApp2\<^sub>g c # s) = (
    let (s', n) = combine_stack' s
    in (FApp2\<^sub>c (combine_closure c) # s', n))"
| "combine_stack' (FLet\<^sub>g \<Delta> e # s) = (
    let (s', n) = combine_stack' s
    in (FLet\<^sub>c (combine_env \<Delta>) (combine_vars' (inv_map_past_let (map_from_env \<Delta>) n) (Suc n) e) # s',
        n))"
| "combine_stack' (FReturn\<^sub>g \<Delta> # s) = (
    let (s', n) = combine_stack' s
    in (FReturn\<^sub>c (combine_env \<Delta>) # s', length (hd \<Delta>)))"

abbreviation combine_stack :: "frame\<^sub>g list \<Rightarrow> frame\<^sub>c list" where
  "combine_stack s \<equiv> fst (combine_stack' s)"

lemma return_headed_combine_stack [simp]: "return_headed\<^sub>c (combine_stack s) = return_headed\<^sub>g s"
  by (induction s rule: combine_stack'.induct) (simp_all split: prod.splits)

primrec combine_state :: "state\<^sub>g \<Rightarrow> state\<^sub>c" where
  "combine_state (SE\<^sub>g s \<Delta> e) = (
    let (s', n) = combine_stack' s
    in SE\<^sub>c s' (combine_env \<Delta>) (combine_vars' (map_from_env \<Delta>) n e))"
| "combine_state (SC\<^sub>g s c) = SC\<^sub>c (combine_stack s) (combine_closure c)"

text \<open>We can now prove our typechecking theorems:\<close>

lemma map_from_env_insert' [simp]: "map_from_env (insert_at 0 [t] \<Gamma>) x = 
    inv_map_past_lam (map_from_env \<Gamma>) x"
  by (induction \<Gamma> x rule: map_from_env.induct) (simp_all split: nat.splits)

lemma map_from_env_insert [simp]: "map_from_env (insert_at 0 [t] \<Gamma>) = 
    inv_map_past_lam (map_from_env \<Gamma>)"
  by auto

lemma map_from_env_insert2 [simp]: "map_from_env ([t] # \<Gamma>) = inv_map_past_lam (map_from_env \<Gamma>)"
proof -
  have "map_from_env (insert_at 0 [t] \<Gamma>) = inv_map_past_lam (map_from_env \<Gamma>)" by simp
  thus ?thesis by (cases \<Gamma>) simp_all
qed

lemma map_from_env_mapfst' [simp]: "lookup \<Gamma> 0 = Some ts \<Longrightarrow> map_from_env (snoc_fst t \<Gamma>) x = 
    inv_map_past_let (map_from_env \<Gamma>) (length ts) x"
proof (induction \<Gamma> x arbitrary: ts rule: map_from_env.induct)
  case (1 x y)
  thus ?case by (cases x) (simp_all split: nat.splits)
qed (auto simp add: option.map_comp)

lemma map_from_env_mapfst [simp]: "lookup \<Gamma> 0 = Some ts \<Longrightarrow> 
    map_from_env (snoc_fst t \<Gamma>) = inv_map_past_let (map_from_env \<Gamma>) (length ts)"
  by auto

lemma typecheck_combine [simp]: "\<Gamma> \<turnstile>\<^sub>g e : t \<Longrightarrow> lookup \<Gamma> 0 = Some ts \<Longrightarrow> 
    concat (map rev \<Gamma>) \<turnstile>\<^sub>d combine_vars' (map_from_env \<Gamma>) (length ts) e : t"
  by (induction \<Gamma> e t arbitrary: ts rule: typing\<^sub>g.induct) fastforce+

lemma "c :\<^sub>g\<^sub>c\<^sub>l t \<Longrightarrow> True"
  and map_from_env_type_vals' [simp]: "\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> map_from_env \<Gamma> x = map_from_env \<Delta> x"
proof (induction c t and \<Delta> \<Gamma> arbitrary: and x rule: typing_closure\<^sub>g_typing_environment\<^sub>g.inducts)
  case tc\<^sub>g_nil
  thus ?case by (cases x) simp_all
next
  case (tc\<^sub>g_cons_nil \<Delta> \<Gamma>)
  thus ?case
  proof (induction x)
    case (Pair a b)
    then show ?case by (cases a) simp_all
  qed
next
  case (tc\<^sub>g_cons_cons c t cs \<Delta> ts \<Gamma>)
  thus ?case 
  proof (induction x)
    case (Pair a b)
    hence Y: "length cs = length ts" by simp
    hence "map_from_env ((t # ts) # \<Gamma>) (a, b) = map_from_env ((c # cs) # \<Delta>) (a, b)" 
    proof (cases a)
      case (Suc a)
      from Pair have "map_from_env (ts # \<Gamma>) (Suc a, b) = map_from_env (cs # \<Delta>) (Suc a, b)" by blast
      with Y Suc show ?thesis 
        by (cases "map_from_env \<Gamma> (a, b)", simp, cases "map_from_env \<Delta> (a, b)") simp_all
    qed simp_all
    thus ?case by simp
  qed
qed simp_all

lemma map_from_env_type_vals [simp]: "\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> map_from_env \<Gamma> = map_from_env \<Delta>"
  by auto

lemma typecheck_combine_closure [simp]: "c :\<^sub>g\<^sub>c\<^sub>l t \<Longrightarrow> combine_closure c :\<^sub>c\<^sub>l t"
  and typecheck_concat_combine_closure [simp]: "\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> combine_env \<Delta> :\<^sub>c\<^sub>l\<^sub>s concat (map rev \<Gamma>)"
proof (induction c t and \<Delta> \<Gamma> rule: typing_closure\<^sub>g_typing_environment\<^sub>g.inducts)
  case (tc\<^sub>g_lam \<Delta> \<Gamma> t\<^sub>1 e t\<^sub>2)
  hence X: "map_from_env \<Gamma> = map_from_env \<Delta>" by simp
  have "lookup (insert_at 0 [t\<^sub>1] \<Gamma>) 0 = Some [t\<^sub>1]" by simp
  with tc\<^sub>g_lam have "concat (map rev (insert_at 0 [t\<^sub>1] \<Gamma>)) \<turnstile>\<^sub>d 
    combine_vars' (map_from_env (insert_at 0 [t\<^sub>1] \<Gamma>)) (length [t\<^sub>1]) e : t\<^sub>2" by (metis typecheck_combine)
  hence "insert_at 0 t\<^sub>1 (concat (map rev \<Gamma>)) \<turnstile>\<^sub>d 
    combine_vars' (inv_map_past_lam (map_from_env \<Gamma>)) 1 e : t\<^sub>2" by simp
  hence Y: "insert_at 0 t\<^sub>1 (concat (map rev \<Gamma>)) \<turnstile>\<^sub>d 
    combine_vars' (inv_map_past_lam (map_from_env \<Delta>)) 1 e : t\<^sub>2" using X by metis
  from tc\<^sub>g_lam have "combine_env \<Delta> :\<^sub>c\<^sub>l\<^sub>s concat (map rev \<Gamma>)" by blast
  with tc\<^sub>g_lam Y show ?case by simp
qed simp_all

lemma combine_env_mapfst [simp]: "combine_env (snoc_fst c \<Delta>) = combine_closure c # combine_env \<Delta>"
  by (induction \<Delta>) simp_all

lemma latest_combine_env [simp]: "latest_environment\<^sub>c (combine_stack s) =
    map_option combine_env (latest_environment\<^sub>g s)"
  by (induction s rule: combine_stack'.induct) (auto simp add: comp_def split: prod.splits)

lemma typecheck_stack [simp]: "s :\<^sub>g t\<^sub>2 \<rightarrow> t \<Longrightarrow> combine_stack s :\<^sub>c t\<^sub>2 \<rightarrow> t"
proof (induction s t\<^sub>2 t rule: typing_stack\<^sub>g.induct)
  case (tcg_scons_app1 \<Delta> \<Gamma> e t\<^sub>1 s t\<^sub>2 t)
  hence X: "combine_env \<Delta> :\<^sub>c\<^sub>l\<^sub>s concat (map rev \<Gamma>)" by simp
  obtain s' n where C: "combine_stack' s = (s', n)" by fastforce
  from tcg_scons_app1 have "map_from_env \<Delta> = map_from_env \<Gamma>" by simp
  with tcg_scons_app1(2) C have Y: "concat (map rev \<Gamma>) \<turnstile>\<^sub>d combine_vars' (map_from_env \<Delta>) n e : t\<^sub>1" 
    by simp

  have "\<Gamma> \<turnstile>\<^sub>g e : t \<Longrightarrow> lookup \<Gamma> 0 = Some ts \<Longrightarrow> 
    concat (map rev \<Gamma>) \<turnstile>\<^sub>d combine_vars' (map_from_env \<Gamma>) (length ts) e : t" by simp

  from tcg_scons_app1 have "latest_environment\<^sub>c (combine_stack s) = Some (combine_env \<Delta>)" by simp
  with C have Z: "latest_environment\<^sub>c s' = Some (combine_env \<Delta>)" by simp


  have "s' :\<^sub>c t\<^sub>2 \<rightarrow> t" by simp
  with tcg_scons_app1(3, 4) X Y Z have "
    FApp1\<^sub>c (combine_env \<Delta>) (combine_vars' (map_from_env \<Delta>) n e) # s' :\<^sub>c Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t" by simp
  with tcg_scons_app1(3, 4, 7) X C Y show ?case by simp
next
  case (tcg_scons_app2 c t\<^sub>1 t\<^sub>2 s t)
  hence "combine_closure c :\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2" by simp
  moreover from tcg_scons_app2 have "combine_stack s :\<^sub>c t\<^sub>2 \<rightarrow> t" by simp
  moreover from tcg_scons_app2 have "latest_environment\<^sub>c (combine_stack s) \<noteq> None" by simp
  ultimately show ?case by simp
next
  case (tcg_scons_let s \<Delta> \<Gamma> t\<^sub>1 e t\<^sub>2 t)
  hence "concat (snoc_fst t\<^sub>1 \<Gamma>) \<turnstile>\<^sub>d combine_vars' (map_from_env (snoc_fst t\<^sub>1 \<Gamma>)) n e : t\<^sub>2" 
    by (metis typecheck_combine)
  hence X: "insert_at 0 t\<^sub>1 (concat \<Gamma>) \<turnstile>\<^sub>d combine_vars' (inv_map_past_let (map_from_env \<Gamma>) n) n e : t\<^sub>2"
    by simp
  from tcg_scons_let have "map_from_env \<Delta> = map_from_env \<Gamma>" by simp
  with X have "insert_at 0 t\<^sub>1 (concat \<Gamma>) \<turnstile>\<^sub>d 
    combine_vars' (inv_map_past_let (map_from_env \<Delta>) n) n e : t\<^sub>2" by metis
  moreover from tcg_scons_let have "latest_environment\<^sub>c (combine_stack s) = Some (combine_env \<Delta>)" 
    by simp
  moreover from tcg_scons_let have "combine_env \<Delta> :\<^sub>c\<^sub>l\<^sub>s concat (map rev \<Gamma>)" by simp
  moreover from tcg_scons_let have "combine_stack s :\<^sub>c t\<^sub>2 \<rightarrow> t" by simp
  moreover from tcg_scons_let have "
    let_floated\<^sub>d (combine_vars' (inv_map_past_let (map_from_env \<Delta>) n) n e)" by simp
  moreover from tcg_scons_let have "return_headed\<^sub>c (combine_stack s)" by simp
  ultimately show ?case by simp
next
  case (tcg_scons_ret \<Delta> \<Gamma> s t' t)
  hence "combine_env \<Delta> :\<^sub>c\<^sub>l\<^sub>s concat (map rev \<Gamma>)" by simp
  moreover from tcg_scons_ret have "combine_stack s :\<^sub>c t' \<rightarrow> t" by simp
  ultimately show ?case by simp
qed simp_all

lemma typecheck_state [simp]: "\<Sigma> :\<^sub>g t \<Longrightarrow> combine_state \<Sigma> :\<^sub>c t"
proof (induction \<Sigma> t rule: typecheck_state\<^sub>g.induct)
  case (tcg_state_ev s t' t \<Delta> \<Gamma> e)
  hence "concat \<Gamma> \<turnstile>\<^sub>d combine_vars' (map_from_env \<Gamma>) 0 e : t'" 
    by (metis typecheck_combine)
  with tcg_state_ev have "concat \<Gamma> \<turnstile>\<^sub>d combine_vars' (map_from_env \<Delta>) 0 e : t'" by simp
  moreover from tcg_state_ev have "combine_stack s :\<^sub>c t' \<rightarrow> t" by simp
  moreover from tcg_state_ev have "combine_env \<Delta> :\<^sub>c\<^sub>l\<^sub>s concat (map rev \<Gamma>)" by simp
  moreover from tcg_state_ev have "latest_environment\<^sub>c (combine_stack s) = Some (combine_env \<Delta>)" 
    by simp
  moreover from tcg_state_ev have "let_floated\<^sub>d (combine_vars' (map_from_env \<Delta>) 0 e)" by simp
  moreover from tcg_state_ev have "let_free\<^sub>d (combine_vars' (map_from_env \<Delta>) 0 e) \<or> 
    return_headed\<^sub>c (combine_stack s)" by simp
  ultimately show ?case by simp
next
  case (tcg_state_ret s t' t c)
  hence "combine_stack s :\<^sub>c t' \<rightarrow> t" by simp
  moreover from tcg_state_ret have "combine_closure c :\<^sub>c\<^sub>l t'" by simp
  ultimately show ?case by simp
qed

text \<open>Now, the evaluation correctness theorems. As usual, one way is much simpler than the other.\<close>

lemma lookup_combine_env [simp]: "lookup \<Delta> x = Some cs \<Longrightarrow> lookup cs y = Some c \<Longrightarrow> 
    lookup (combine_env \<Delta>) (the (map_from_env \<Delta> (x, y))) = Some (combine_closure c)"
proof (induction \<Delta> "(x, y)" arbitrary: x y rule: map_from_env.induct)
  case (2 cs \<Delta> y)
  hence "lookup (map combine_closure cs) y = Some (combine_closure c)" by simp
  hence "lookup (rev (map combine_closure cs) @ combine_env \<Delta>) 
    (length (map combine_closure cs) - Suc y) = Some (combine_closure c)" 
      by (metis lookup_append_fst_rev)
  with 2 show ?case by simp
next
  case (3 cs \<Delta> x y)
  have X: "length (rev (map combine_closure cs)) = length cs" by simp
  from 3 show ?case by (cases "map_from_env \<Delta> (x, y)") (simp_all, metis X lookup_append_snd)
qed simp_all

theorem completeness\<^sub>g [simp]: "\<Sigma> \<leadsto>\<^sub>g \<Sigma>' \<Longrightarrow> combine_state \<Sigma> \<leadsto>\<^sub>c combine_state \<Sigma>'"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>g.induct)
  case (ret\<^sub>g_let \<Delta> e\<^sub>2 s c\<^sub>1)
  obtain s' n where S: "combine_stack' s = (s', n)" by fastforce

  have "SC\<^sub>c 
      (FLet\<^sub>c (combine_env \<Delta>) 
       (combine_vars' (inv_map_past_let (map_from_env \<Delta>) (length (hd \<Delta>))) (Suc (length (hd \<Delta>)))
         e\<^sub>2) # 
      FReturn\<^sub>c (combine_env \<Delta>) # s') 
      (combine_closure c\<^sub>1) \<leadsto>\<^sub>c 
    SE\<^sub>c (FReturn\<^sub>c ((combine_closure c\<^sub>1) # (combine_env \<Delta>)) # s') ((combine_closure c\<^sub>1) # (combine_env \<Delta>)) 
    (combine_vars' (inv_map_past_let (map_from_env \<Delta>) (length (hd \<Delta>))) (Suc (length (hd \<Delta>)))
         e\<^sub>2)" by simp

  hence "SC\<^sub>c
     (FLet\<^sub>c (combine_env \<Delta>)
       (combine_vars' (inv_map_past_let (map_from_env \<Delta>) (length (hd \<Delta>))) (Suc (length (hd \<Delta>)))
         e\<^sub>2) #
      FReturn\<^sub>c (combine_env \<Delta>) # s')
     (combine_closure c\<^sub>1) \<leadsto>\<^sub>c
    SE\<^sub>c (FReturn\<^sub>c (combine_closure c\<^sub>1 # combine_env \<Delta>) # s') (combine_closure c\<^sub>1 # combine_env \<Delta>)
     (combine_vars' (map_from_env (snoc_fst c\<^sub>1 \<Delta>)) (length (hd (snoc_fst c\<^sub>1 \<Delta>))) e\<^sub>2)" by simp
  with S show ?case by simp
qed (simp_all split: prod.splits)

lemma combine_to_var [dest]: "\<Gamma> \<turnstile>\<^sub>g e\<^sub>g : t \<Longrightarrow> Var\<^sub>d x = combine_vars' (map_from_env \<Delta>) n e\<^sub>g \<Longrightarrow> 
    \<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> \<exists>y z. e\<^sub>g = Var\<^sub>g y z \<and> map_from_env \<Delta> (y, z) = Some x"
proof (induction \<Gamma> e\<^sub>g t rule: typing\<^sub>g.induct) 
  case (tc\<^sub>g_var \<Gamma> x ts y t)
  hence "map_from_env \<Delta> = map_from_env \<Gamma>" by simp
  with tc\<^sub>g_var have "map_from_env \<Delta> (x, y) \<noteq> None" by (metis lookup_map_from_env)
  with tc\<^sub>g_var show ?case by simp
qed simp_all
 
lemma combine_to_con [dest]: "Const\<^sub>d n = combine_vars' \<Phi> m e\<^sub>g \<Longrightarrow> e\<^sub>g = Const\<^sub>g n"
  by (induction e\<^sub>g) simp_all

lemma combine_to_lam [dest]: "Lam\<^sub>d t e\<^sub>c = combine_vars' \<Phi> n e\<^sub>g \<Longrightarrow> 
    \<exists>e\<^sub>g' n. e\<^sub>g = Lam\<^sub>g t e\<^sub>g' n \<and> e\<^sub>c = combine_vars' (inv_map_past_lam \<Phi>) (Suc 0) e\<^sub>g'"
  by (induction e\<^sub>g) simp_all

lemma combine_to_app [dest]: "App\<^sub>d e\<^sub>1\<^sub>c e\<^sub>2\<^sub>c = combine_vars' \<Phi> n e\<^sub>g \<Longrightarrow> 
    \<exists>e\<^sub>1\<^sub>g e\<^sub>2\<^sub>g. e\<^sub>g = App\<^sub>g e\<^sub>1\<^sub>g e\<^sub>2\<^sub>g \<and> e\<^sub>1\<^sub>c = combine_vars' \<Phi> n e\<^sub>1\<^sub>g \<and> e\<^sub>2\<^sub>c = combine_vars' \<Phi> n e\<^sub>2\<^sub>g"
  by (induction e\<^sub>g) simp_all

lemma combine_to_let [dest]: "Let\<^sub>d e\<^sub>1\<^sub>c e\<^sub>2\<^sub>c = combine_vars' \<Phi> n e\<^sub>g \<Longrightarrow> 
  \<exists>e\<^sub>1\<^sub>g e\<^sub>2\<^sub>g. e\<^sub>g = Let\<^sub>g e\<^sub>1\<^sub>g e\<^sub>2\<^sub>g \<and> e\<^sub>1\<^sub>c = combine_vars' \<Phi> n e\<^sub>1\<^sub>g \<and> 
    e\<^sub>2\<^sub>c = combine_vars' (inv_map_past_let \<Phi> n) (Suc n) e\<^sub>2\<^sub>g"
  by (induction e\<^sub>g) simp_all

lemma combine_to_lamc [dest]: "Lam\<^sub>c t \<Delta>\<^sub>c e\<^sub>c = combine_closure c\<^sub>g \<Longrightarrow> 
  \<exists>\<Delta>\<^sub>g e\<^sub>g n. c\<^sub>g = Fun\<^sub>g t \<Delta>\<^sub>g e\<^sub>g n \<and> \<Delta>\<^sub>c = combine_env \<Delta>\<^sub>g \<and> 
    e\<^sub>c = combine_vars' (inv_map_past_lam (map_from_env \<Delta>\<^sub>g)) (Suc 0) e\<^sub>g"
  by (induction c\<^sub>g) simp_all

lemma combine_to_fapp1 [dest]: "FApp1\<^sub>c \<Delta>\<^sub>c e\<^sub>c # s\<^sub>c = combine_stack s\<^sub>g \<Longrightarrow> 
  \<exists>n s\<^sub>g' \<Delta>\<^sub>g e\<^sub>g. s\<^sub>g = FApp1\<^sub>g \<Delta>\<^sub>g e\<^sub>g # s\<^sub>g' \<and> combine_stack' s\<^sub>g' = (s\<^sub>c, n) \<and> \<Delta>\<^sub>c = combine_env \<Delta>\<^sub>g \<and> 
    e\<^sub>c = combine_vars' (map_from_env \<Delta>\<^sub>g) n e\<^sub>g"
  by (induction s\<^sub>g rule: combine_stack'.induct) (simp_all split: prod.splits)

lemma combine_to_fapp2 [dest]: "FApp2\<^sub>c c\<^sub>c # s\<^sub>c = combine_stack s\<^sub>g \<Longrightarrow> 
  \<exists>n s\<^sub>g' c\<^sub>g. s\<^sub>g = FApp2\<^sub>g c\<^sub>g # s\<^sub>g' \<and> combine_stack' s\<^sub>g' = (s\<^sub>c, n) \<and> c\<^sub>c = combine_closure c\<^sub>g"
  by (induction s\<^sub>g rule: combine_stack'.induct) (simp_all split: prod.splits)

lemma combine_to_flet [dest]: "FLet\<^sub>c \<Delta>\<^sub>c e\<^sub>c # s\<^sub>c = combine_stack s\<^sub>g \<Longrightarrow> 
  \<exists>n s\<^sub>g' \<Delta>\<^sub>g e\<^sub>g. s\<^sub>g = FLet\<^sub>g \<Delta>\<^sub>g e\<^sub>g # s\<^sub>g' \<and> combine_stack' s\<^sub>g' = (s\<^sub>c, n) \<and> \<Delta>\<^sub>c = combine_env \<Delta>\<^sub>g \<and> 
    e\<^sub>c = combine_vars' (inv_map_past_let (map_from_env \<Delta>\<^sub>g) n) (Suc n) e\<^sub>g"
  by (induction s\<^sub>g rule: combine_stack'.induct) (simp_all split: prod.splits)

lemma combine_to_freturn [dest]: "FReturn\<^sub>c \<Delta>\<^sub>c # s\<^sub>c = combine_stack s\<^sub>g \<Longrightarrow> 
    \<exists>n s\<^sub>g' \<Delta>\<^sub>g. s\<^sub>g = FReturn\<^sub>g \<Delta>\<^sub>g # s\<^sub>g' \<and> combine_stack' s\<^sub>g' = (s\<^sub>c, n) \<and> \<Delta>\<^sub>c = combine_env \<Delta>\<^sub>g"
  by (induction s\<^sub>g rule: combine_stack'.induct) (simp_all split: prod.splits)

lemma combine_to_eval_state [dest]: "SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e\<^sub>c = combine_state \<Sigma>\<^sub>g \<Longrightarrow> 
  \<exists>s\<^sub>g \<Delta>\<^sub>g e\<^sub>g. \<Sigma>\<^sub>g = SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e\<^sub>g \<and> s\<^sub>c = combine_stack s\<^sub>g \<and> \<Delta>\<^sub>c = combine_env \<Delta>\<^sub>g \<and> 
    e\<^sub>c = combine_vars' (map_from_env \<Delta>\<^sub>g) 0 e\<^sub>g"
  by (induction \<Sigma>\<^sub>g) simp_all

lemma combine_to_return_state [dest]: "SC\<^sub>c s\<^sub>c c\<^sub>c = combine_state \<Sigma>\<^sub>g \<Longrightarrow> 
    \<exists>s\<^sub>g c\<^sub>g. \<Sigma>\<^sub>g = SC\<^sub>g s\<^sub>g c\<^sub>g \<and> s\<^sub>c = combine_stack s\<^sub>g \<and> c\<^sub>c = combine_closure c\<^sub>g"
  by (induction \<Sigma>\<^sub>g) simp_all

lemma lookup_map_inv [simp]: "map_from_env \<Delta> (y, z) = Some x \<Longrightarrow>
  lookup (combine_env \<Delta>) x = Some c \<Longrightarrow> 
    \<exists>cs c\<^sub>g. lookup \<Delta> y = Some cs \<and> lookup cs z = Some c\<^sub>g \<and> c = combine_closure c\<^sub>g" 
  by (induction \<Delta> "(y, z)" arbitrary: x y z rule: map_from_env.induct) (auto split: if_splits)

theorem correctness\<^sub>g [simp]: "combine_state \<Sigma>\<^sub>g \<leadsto>\<^sub>c \<Sigma>\<^sub>c' \<Longrightarrow> \<Sigma>\<^sub>g :\<^sub>g t \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>g'. \<Sigma>\<^sub>g \<leadsto>\<^sub>g \<Sigma>\<^sub>g' \<and> \<Sigma>\<^sub>c' = combine_state \<Sigma>\<^sub>g'"
proof (induction "combine_state \<Sigma>\<^sub>g" \<Sigma>\<^sub>c' rule: eval\<^sub>c.induct)
  case (ev\<^sub>c_var \<Delta>\<^sub>c x c\<^sub>c s\<^sub>c)
  then obtain s\<^sub>g \<Delta>\<^sub>g e\<^sub>g where S: "\<Sigma>\<^sub>g = SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e\<^sub>g \<and> s\<^sub>c = combine_stack s\<^sub>g \<and> 
    \<Delta>\<^sub>c = combine_env \<Delta>\<^sub>g \<and> Var\<^sub>d x = combine_vars' (map_from_env \<Delta>\<^sub>g) 0 e\<^sub>g" by auto
  with ev\<^sub>c_var obtain t' \<Gamma> where "(s\<^sub>g :\<^sub>g t' \<rightarrow> t) \<and> (\<Delta>\<^sub>g :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> 
    latest_environment\<^sub>g s\<^sub>g = Some \<Delta>\<^sub>g \<and> \<Gamma> \<turnstile>\<^sub>g e\<^sub>g : t'" by auto
  with S obtain y z where Y: "e\<^sub>g = Var\<^sub>g y z \<and> map_from_env \<Delta>\<^sub>g (y, z) = Some x" by auto
  from ev\<^sub>c_var S have "lookup (combine_env \<Delta>\<^sub>g) x = Some c\<^sub>c" by blast
  with Y obtain cs c\<^sub>g where "lookup \<Delta>\<^sub>g y = Some cs \<and> lookup cs z = Some c\<^sub>g \<and> c\<^sub>c = combine_closure c\<^sub>g" 
    using lookup_map_inv by blast
  with S have "SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g (Var\<^sub>g y z) \<leadsto>\<^sub>g SC\<^sub>g s\<^sub>g c\<^sub>g \<and> SC\<^sub>c s\<^sub>c c\<^sub>c = combine_state (SC\<^sub>g s\<^sub>g c\<^sub>g)" by simp
  with S Y show ?case by blast
next
  case (ev\<^sub>c_con s\<^sub>c \<Delta>\<^sub>c n)
  then obtain s\<^sub>g \<Delta>\<^sub>g where "\<Sigma>\<^sub>g = SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g (Const\<^sub>g n) \<and> s\<^sub>c = combine_stack s\<^sub>g \<and> \<Delta>\<^sub>c = combine_env \<Delta>\<^sub>g" 
    by blast
  moreover hence "SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g (Const\<^sub>g n) \<leadsto>\<^sub>g SC\<^sub>g s\<^sub>g (Num\<^sub>g n) \<and> 
    SC\<^sub>c s\<^sub>c (Const\<^sub>c n) = combine_state (SC\<^sub>g s\<^sub>g (Num\<^sub>g n))" by simp
  ultimately show ?case by blast
next
  case (ev\<^sub>c_lam s\<^sub>c \<Delta>\<^sub>c t e\<^sub>c)
  then obtain s\<^sub>g \<Delta>\<^sub>g e\<^sub>g where S: "\<Sigma>\<^sub>g = SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e\<^sub>g \<and> s\<^sub>c = combine_stack s\<^sub>g \<and> \<Delta>\<^sub>c = combine_env \<Delta>\<^sub>g \<and> 
    Lam\<^sub>d t e\<^sub>c = combine_vars' (map_from_env \<Delta>\<^sub>g) 0 e\<^sub>g" by auto
  moreover then obtain e\<^sub>g' n where "e\<^sub>g = Lam\<^sub>g t e\<^sub>g' n \<and> 
    e\<^sub>c = combine_vars' (inv_map_past_lam (map_from_env \<Delta>\<^sub>g)) 0 e\<^sub>g'" by auto
  moreover with S have "SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g (Lam\<^sub>g t e\<^sub>g' n) \<leadsto>\<^sub>g SC\<^sub>g s\<^sub>g (Fun\<^sub>g t \<Delta>\<^sub>g e\<^sub>g' n) \<and> 
    SC\<^sub>c s\<^sub>c (Lam\<^sub>c t \<Delta>\<^sub>c e\<^sub>c) = combine_state (SC\<^sub>g s\<^sub>g (Fun\<^sub>g t \<Delta>\<^sub>g e\<^sub>g' n))" by simp
  ultimately show ?case by blast
next
  case (ev\<^sub>c_app s\<^sub>c \<Delta>\<^sub>c e\<^sub>1\<^sub>c e\<^sub>2\<^sub>c)
  then obtain s\<^sub>g \<Delta>\<^sub>g e\<^sub>g where S: "\<Sigma>\<^sub>g = SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e\<^sub>g \<and> s\<^sub>c = combine_stack s\<^sub>g \<and> \<Delta>\<^sub>c = combine_env \<Delta>\<^sub>g \<and> 
    App\<^sub>d e\<^sub>1\<^sub>c e\<^sub>2\<^sub>c = combine_vars' (map_from_env \<Delta>\<^sub>g) 0 e\<^sub>g" by auto
  moreover then obtain e\<^sub>1\<^sub>g e\<^sub>2\<^sub>g where "e\<^sub>g = App\<^sub>g e\<^sub>1\<^sub>g e\<^sub>2\<^sub>g \<and> 
    e\<^sub>1\<^sub>c = combine_vars' (map_from_env \<Delta>\<^sub>g) 0 e\<^sub>1\<^sub>g \<and> e\<^sub>2\<^sub>c = combine_vars' (map_from_env \<Delta>\<^sub>g) 0 e\<^sub>2\<^sub>g" 
      by auto
  moreover with S have "SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g (App\<^sub>g e\<^sub>1\<^sub>g e\<^sub>2\<^sub>g) \<leadsto>\<^sub>g SE\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e\<^sub>2\<^sub>g # s\<^sub>g) \<Delta>\<^sub>g e\<^sub>1\<^sub>g \<and> 
    SE\<^sub>c (FApp1\<^sub>c \<Delta>\<^sub>c e\<^sub>2\<^sub>c # s\<^sub>c) \<Delta>\<^sub>c e\<^sub>1\<^sub>c = combine_state (SE\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e\<^sub>2\<^sub>g # s\<^sub>g) \<Delta>\<^sub>g e\<^sub>1\<^sub>g)" by simp
  ultimately show ?case by blast
next
  case (ev\<^sub>c_let \<Delta>\<^sub>c s\<^sub>c e\<^sub>1\<^sub>c e\<^sub>2\<^sub>c)
  then obtain s\<^sub>g \<Delta>\<^sub>g e\<^sub>g where S: "\<Sigma>\<^sub>g = SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e\<^sub>g \<and> FReturn\<^sub>c \<Delta>\<^sub>c # s\<^sub>c = combine_stack s\<^sub>g \<and> 
    \<Delta>\<^sub>c = combine_env \<Delta>\<^sub>g \<and> Let\<^sub>d e\<^sub>1\<^sub>c e\<^sub>2\<^sub>c = combine_vars' (map_from_env \<Delta>\<^sub>g) 0 e\<^sub>g" by blast
  moreover then obtain \<Delta>\<^sub>g' s\<^sub>g' where S': "s\<^sub>g = FReturn\<^sub>g \<Delta>\<^sub>g' # s\<^sub>g'" by blast
  moreover from S obtain e\<^sub>1\<^sub>g e\<^sub>2\<^sub>g where E: "e\<^sub>g = Let\<^sub>g e\<^sub>1\<^sub>g e\<^sub>2\<^sub>g \<and> 
    e\<^sub>1\<^sub>c = combine_vars' (map_from_env \<Delta>\<^sub>g) 0 e\<^sub>1\<^sub>g \<and> 
      e\<^sub>2\<^sub>c = combine_vars' (inv_map_past_let (map_from_env \<Delta>\<^sub>g) 0) (Suc 0) e\<^sub>2\<^sub>g" by auto
  moreover from ev\<^sub>c_let S S' have "\<Delta>\<^sub>g' = \<Delta>\<^sub>g" by auto
  moreover with S S' E have "SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g (Let\<^sub>g e\<^sub>1\<^sub>g e\<^sub>2\<^sub>g) \<leadsto>\<^sub>g SE\<^sub>g (FLet\<^sub>g \<Delta>\<^sub>g e\<^sub>2\<^sub>g # s\<^sub>g) \<Delta>\<^sub>g e\<^sub>1\<^sub>g \<and> 
    SE\<^sub>c (FLet\<^sub>c \<Delta>\<^sub>c e\<^sub>2\<^sub>c # FReturn\<^sub>c \<Delta>\<^sub>c # s\<^sub>c) \<Delta>\<^sub>c e\<^sub>1\<^sub>c = combine_state (SE\<^sub>g (FLet\<^sub>g \<Delta>\<^sub>g e\<^sub>2\<^sub>g # s\<^sub>g) \<Delta>\<^sub>g e\<^sub>1\<^sub>g)" 
      by simp
  ultimately show ?case by blast
next
  case (ret\<^sub>c_app1 \<Delta>\<^sub>c e\<^sub>c s\<^sub>c c\<^sub>c)
  then obtain s\<^sub>g' c\<^sub>g where S: "\<Sigma>\<^sub>g = SC\<^sub>g s\<^sub>g' c\<^sub>g \<and> FApp1\<^sub>c \<Delta>\<^sub>c e\<^sub>c # s\<^sub>c = combine_stack s\<^sub>g' \<and> 
    c\<^sub>c = combine_closure c\<^sub>g" by blast
  moreover then obtain n s\<^sub>g \<Delta>\<^sub>g e\<^sub>g where F: "s\<^sub>g' = FApp1\<^sub>g \<Delta>\<^sub>g e\<^sub>g # s\<^sub>g \<and> combine_stack' s\<^sub>g = (s\<^sub>c, n) \<and> 
    \<Delta>\<^sub>c = combine_env \<Delta>\<^sub>g \<and> e\<^sub>c = combine_vars' (map_from_env \<Delta>\<^sub>g) n e\<^sub>g" by blast
  moreover with S have "SC\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e\<^sub>g # s\<^sub>g) c\<^sub>g \<leadsto>\<^sub>g SE\<^sub>g (FApp2\<^sub>g c\<^sub>g # s\<^sub>g) \<Delta>\<^sub>g e\<^sub>g \<and> 
    SE\<^sub>c (FApp2\<^sub>c c\<^sub>c # s\<^sub>c) \<Delta>\<^sub>c e\<^sub>c = combine_state (SE\<^sub>g (FApp2\<^sub>g c\<^sub>g # s\<^sub>g) \<Delta>\<^sub>g e\<^sub>g)" by simp
  ultimately show ?case by blast
next
  case (ret\<^sub>c_app2 t \<Delta>\<^sub>c e\<^sub>c s\<^sub>c c\<^sub>c)
  then obtain s\<^sub>g' c\<^sub>g where S: "\<Sigma>\<^sub>g = SC\<^sub>g s\<^sub>g' c\<^sub>g \<and> FApp2\<^sub>c (Lam\<^sub>c t \<Delta>\<^sub>c e\<^sub>c) # s\<^sub>c = combine_stack s\<^sub>g' \<and> 
    c\<^sub>c = combine_closure c\<^sub>g" by blast
  moreover then obtain n s\<^sub>g c\<^sub>g where F: "s\<^sub>g' = FApp2\<^sub>g c\<^sub>g # s\<^sub>g \<and> combine_stack' s\<^sub>g = (s\<^sub>c, n) \<and> 
    Lam\<^sub>c t \<Delta>\<^sub>c e\<^sub>c = combine_closure c\<^sub>g" by blast
  moreover then obtain \<Delta>\<^sub>g e\<^sub>g n where "c\<^sub>g = Fun\<^sub>g t \<Delta>\<^sub>g e\<^sub>g n \<and> \<Delta>\<^sub>c = combine_env \<Delta>\<^sub>g \<and> 
    e\<^sub>c = combine_vars' (inv_map_past_lam (map_from_env \<Delta>\<^sub>g)) (Suc 0) e\<^sub>g" by blast
  moreover with S F have "SC\<^sub>g (FApp2\<^sub>g (Fun\<^sub>g t \<Delta>\<^sub>g e\<^sub>g n) # s\<^sub>g) c\<^sub>g \<leadsto>\<^sub>g 
    SE\<^sub>g (FReturn\<^sub>g ([c\<^sub>g] # \<Delta>\<^sub>g) # s\<^sub>g) ([c\<^sub>g] # \<Delta>\<^sub>g) e\<^sub>g \<and> 
    SE\<^sub>c (FReturn\<^sub>c (c\<^sub>c # \<Delta>\<^sub>c) # s\<^sub>c) (c\<^sub>c # \<Delta>\<^sub>c) e\<^sub>c = 
      combine_state (SE\<^sub>g (FReturn\<^sub>g ([c\<^sub>g] # \<Delta>\<^sub>g) # s\<^sub>g) ([c\<^sub>g] # \<Delta>\<^sub>g) e\<^sub>g)" by simp
  ultimately show ?case by blastx
next
  case (ret\<^sub>c_let \<Delta>\<^sub>c e\<^sub>c s\<^sub>c c\<^sub>c)
  then obtain s\<^sub>g' c\<^sub>g where S: "\<Sigma>\<^sub>g = SC\<^sub>g s\<^sub>g' c\<^sub>g \<and> 
    FLet\<^sub>c \<Delta>\<^sub>c e\<^sub>c # FReturn\<^sub>c \<Delta>\<^sub>c # s\<^sub>c = map combine_frame s\<^sub>g' \<and> c\<^sub>c = combine_closure c\<^sub>g" by blastx
  moreover then obtain f\<^sub>g \<Delta>\<^sub>g' s\<^sub>g where F: "FLet\<^sub>c \<Delta>\<^sub>c e\<^sub>c = combine_frame f\<^sub>g \<and> 
    s\<^sub>c = map combine_frame s\<^sub>g \<and> \<Delta>\<^sub>c = concat (map (map combine_closure) \<Delta>\<^sub>g') \<and> 
      s\<^sub>g' = f\<^sub>g # FReturn\<^sub>g \<Delta>\<^sub>g' # s\<^sub>g" by blast
  moreover then obtain \<Delta>\<^sub>g e\<^sub>g where E: "f\<^sub>g = FLet\<^sub>g \<Delta>\<^sub>g e\<^sub>g \<and> 
    \<Delta>\<^sub>c = concat (map (map combine_closure) \<Delta>\<^sub>g) \<and> 
      e\<^sub>c = combine_vars' (inv_map_past_let (map_from_env \<Delta>\<^sub>g)) e\<^sub>g" by blast
  moreover from ret\<^sub>c_let S F E have "latest_environment\<^sub>g (FReturn\<^sub>g \<Delta>\<^sub>g' # s\<^sub>g) = Some \<Delta>\<^sub>g" by blast
  moreover hence G: "\<Delta>\<^sub>g' = \<Delta>\<^sub>g" by simp
  moreover have "insert_at 0 (combine_closure c\<^sub>g) (concat (map (map combine_closure) \<Delta>\<^sub>g)) = 
    combine_closure c\<^sub>g # concat (map (map combine_closure) \<Delta>\<^sub>g)" 
  proof (induction \<Delta>\<^sub>g)
    case (Cons cs \<Delta>)
    thus ?case by (cases cs) simp_all
  qed simp_all
  moreover with S F E G have "SC\<^sub>g (FLet\<^sub>g \<Delta>\<^sub>g e\<^sub>g # FReturn\<^sub>g \<Delta>\<^sub>g' # s\<^sub>g) c\<^sub>g \<leadsto>\<^sub>g 
    SE\<^sub>g (FReturn\<^sub>g (snoc_fst c\<^sub>g \<Delta>\<^sub>g') # s\<^sub>g) (snoc_fst c\<^sub>g \<Delta>\<^sub>g) e\<^sub>g \<and> 
    SE\<^sub>c (FReturn\<^sub>c (c\<^sub>c # \<Delta>\<^sub>c) # s\<^sub>c) (c\<^sub>c # \<Delta>\<^sub>c) e\<^sub>c = 
      combine_state (SE\<^sub>g (FReturn\<^sub>g (snoc_fst c\<^sub>g \<Delta>\<^sub>g') # s\<^sub>g) (snoc_fst c\<^sub>g \<Delta>\<^sub>g) e\<^sub>g)" 
    by simp
  ultimately show ?case by blastx
next
  case (ret\<^sub>c_ret \<Delta>\<^sub>c s\<^sub>c c\<^sub>c)
  then obtain s\<^sub>g' c\<^sub>g where S: "\<Sigma>\<^sub>g = SC\<^sub>g s\<^sub>g' c\<^sub>g \<and> FReturn\<^sub>c \<Delta>\<^sub>c # s\<^sub>c = map combine_frame s\<^sub>g' \<and> 
    c\<^sub>c = combine_closure c\<^sub>g" by blastx
  moreover then obtain f\<^sub>g s\<^sub>g where F: "FReturn\<^sub>c \<Delta>\<^sub>c = combine_frame f\<^sub>g \<and> 
    s\<^sub>c = map combine_frame s\<^sub>g \<and> s\<^sub>g' = f\<^sub>g # s\<^sub>g" by blast
  moreover then obtain \<Delta>\<^sub>g where "f\<^sub>g = FReturn\<^sub>g \<Delta>\<^sub>g \<and> \<Delta>\<^sub>c = concat (map (map combine_closure) \<Delta>\<^sub>g)" 
    by blast
  moreover with S F have "SC\<^sub>g (FReturn\<^sub>g \<Delta>\<^sub>g # s\<^sub>g) c\<^sub>g \<leadsto>\<^sub>g SC\<^sub>g s\<^sub>g c\<^sub>g \<and> 
    SC\<^sub>c s\<^sub>c c\<^sub>c = combine_state (SC\<^sub>g s\<^sub>g c\<^sub>g)" by simp
  ultimately show ?case by blast
qed

lemma iter_correctness\<^sub>g [simp]: "iter (\<leadsto>\<^sub>c) (combine_state \<Sigma>\<^sub>g) \<Sigma>\<^sub>c' \<Longrightarrow> \<Sigma>\<^sub>g :\<^sub>g t \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>g'. iter (\<leadsto>\<^sub>g) \<Sigma>\<^sub>g \<Sigma>\<^sub>g' \<and> \<Sigma>\<^sub>c' = combine_state \<Sigma>\<^sub>g'"
proof (induction "combine_state \<Sigma>\<^sub>g" \<Sigma>\<^sub>c' arbitrary: \<Sigma>\<^sub>g rule: iter.induct)
  case iter_refl
  have "iter (\<leadsto>\<^sub>g) \<Sigma>\<^sub>g \<Sigma>\<^sub>g \<and> combine_state \<Sigma>\<^sub>g = combine_state \<Sigma>\<^sub>g" by simp
  thus ?case by blast
next
  case (iter_step \<Sigma>\<^sub>c' \<Sigma>\<^sub>c'')
  then obtain \<Sigma>\<^sub>g' where S: "\<Sigma>\<^sub>g \<leadsto>\<^sub>g \<Sigma>\<^sub>g' \<and> \<Sigma>\<^sub>c' = combine_state \<Sigma>\<^sub>g'" by fastforce
  with iter_step have "\<Sigma>\<^sub>g' :\<^sub>g t" by fastforce
  with iter_step S obtain \<Sigma>\<^sub>g'' where "iter (\<leadsto>\<^sub>g) \<Sigma>\<^sub>g' \<Sigma>\<^sub>g'' \<and> \<Sigma>\<^sub>c'' = combine_state \<Sigma>\<^sub>g''" by fastforce
  with S have "iter (\<leadsto>\<^sub>g) \<Sigma>\<^sub>g \<Sigma>\<^sub>g'' \<and> \<Sigma>\<^sub>c'' = combine_state \<Sigma>\<^sub>g''" by fastforce
  thus ?case by blast
qed

text \<open>However, there is still one slight obstacle to overcome. Our ultimate compilation process will
use \<open>split_vars\<close>, but our theorem is defined in terms of \<open>combine_vars\<close>. Fortunately, we can use our
inverse theorems to get the result we need.\<close>

lemma iter_correctness_forward\<^sub>g [simp]: "iter (\<leadsto>\<^sub>c) (SE\<^sub>c [FReturn\<^sub>c []] [] e\<^sub>c) \<Sigma>\<^sub>c' \<Longrightarrow> [] \<turnstile>\<^sub>d e\<^sub>c : t \<Longrightarrow> 
  let_floated\<^sub>d e\<^sub>c \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>g'. iter (\<leadsto>\<^sub>g) (SE\<^sub>g [FReturn\<^sub>g [[]]] [[]] (split_vars e\<^sub>c)) \<Sigma>\<^sub>g' \<and> \<Sigma>\<^sub>c' = combine_state \<Sigma>\<^sub>g'"
proof -
  assume "iter (\<leadsto>\<^sub>c) (SE\<^sub>c [FReturn\<^sub>c []] [] e\<^sub>c) \<Sigma>\<^sub>c'" and T: "[] \<turnstile>\<^sub>d e\<^sub>c : t" and L: "let_floated\<^sub>d e\<^sub>c"
  hence X: "iter (\<leadsto>\<^sub>c) (combine_state (SE\<^sub>g [FReturn\<^sub>g [[]]] [[]] (split_vars e\<^sub>c))) \<Sigma>\<^sub>c'" 
    by (simp add: split_vars_def)
  from T have "[[]] \<turnstile>\<^sub>g split_vars e\<^sub>c : t" by simp
  moreover have "[FReturn\<^sub>g [[]]] :\<^sub>g t \<rightarrow> t" 
    using tc\<^sub>g_nil tc\<^sub>g_cons_nil tcg_scons_ret tcg_snil by blast
  moreover from L have "let_floated\<^sub>g (split_vars e\<^sub>c)" by simp
  moreover have "[[]] :\<^sub>g\<^sub>c\<^sub>l\<^sub>s [[]]" by simp
  ultimately have "SE\<^sub>g [FReturn\<^sub>g [[]]] [[]] (split_vars e\<^sub>c) :\<^sub>g t" 
    by (metis tcg_state_ev return_headed\<^sub>g.simps(1) latest_environment\<^sub>g.simps(5))
  with X show ?thesis by auto
qed

end