theory VariableSplitting
  imports GroupedEnvironments "../05Closure/Closure"
begin

section \<open>Variable splitting\<close>

text \<open>Now we divide our variables into frame-offset pairs. The process is quite simple for 
expressions: we accumulate a map from Debruijn indices to frame-offset pairs, adding to it every 
time we pass a binder, and then map variables when we reach them. (As mentioned before, we also 
record the frame-size every time we reach a \<open>Lam\<^sub>d\<close>.\<close>

abbreviation map_past_lam :: "(nat \<rightharpoonup> nat \<times> nat) \<Rightarrow> nat \<rightharpoonup> nat \<times> nat" where
  "map_past_lam \<Phi> x \<equiv> (case x of 
      0 \<Rightarrow> Some (0, 0) 
    | Suc x \<Rightarrow> map_option (apfst Suc) (\<Phi> x))"

abbreviation map_past_let :: "(nat \<rightharpoonup> nat \<times> nat) \<Rightarrow> nat \<rightharpoonup> nat \<times> nat" where
  "map_past_let \<Phi> x \<equiv> (case x of 
      0 \<Rightarrow> Some (0, 0) 
    | Suc x \<Rightarrow> map_option (\<lambda>(y, z). (y, if y = 0 then Suc z else z)) (\<Phi> x))"

primrec split_vars' :: "(nat \<rightharpoonup> nat \<times> nat) \<Rightarrow> expr\<^sub>d \<Rightarrow> expr\<^sub>g" where
  "split_vars' \<Phi> (Var\<^sub>d x) = (case the (\<Phi> x) of (y, z) \<Rightarrow> Var\<^sub>g y z)"
| "split_vars' \<Phi> (Const\<^sub>d n) = Const\<^sub>g n"
| "split_vars' \<Phi> (Lam\<^sub>d t e) = (let e\<^sub>g = split_vars' (map_past_lam \<Phi>) e in Lam\<^sub>g t e\<^sub>g (let_count e\<^sub>g))"
| "split_vars' \<Phi> (App\<^sub>d e\<^sub>1 e\<^sub>2) = App\<^sub>g (split_vars' \<Phi> e\<^sub>1) (split_vars' \<Phi> e\<^sub>2)"
| "split_vars' \<Phi> (Let\<^sub>d e\<^sub>1 e\<^sub>2) = Let\<^sub>g (split_vars' \<Phi> e\<^sub>1) (split_vars' (map_past_let \<Phi>) e\<^sub>2)"

definition split_vars :: "expr\<^sub>d \<Rightarrow> expr\<^sub>g" where
  "split_vars e \<equiv> split_vars' Map.empty e"

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

abbreviation inv_map_past_let :: "(nat \<times> nat \<rightharpoonup> nat) \<Rightarrow> nat \<times> nat \<rightharpoonup> nat" where
  "inv_map_past_let \<Phi> x \<equiv> (case x of (y, z) \<Rightarrow> 
      if y = 0 \<and> z = 0 then Some 0
      else map_option Suc (\<Phi> (y, if y = 0 then z - 1 else z)))"

primrec combine_vars' :: "(nat \<times> nat \<rightharpoonup> nat) \<Rightarrow> expr\<^sub>g \<Rightarrow> expr\<^sub>d" where
  "combine_vars' \<Phi> (Var\<^sub>g x y) = Var\<^sub>d (the (\<Phi> (x, y)))"
| "combine_vars' \<Phi> (Const\<^sub>g n) = Const\<^sub>d n"
| "combine_vars' \<Phi> (Lam\<^sub>g t e n) = Lam\<^sub>d t (combine_vars' (inv_map_past_lam \<Phi>) e)"
| "combine_vars' \<Phi> (App\<^sub>g e\<^sub>1 e\<^sub>2) = App\<^sub>d (combine_vars' \<Phi> e\<^sub>1) (combine_vars' \<Phi> e\<^sub>2)"
| "combine_vars' \<Phi> (Let\<^sub>g e\<^sub>1 e\<^sub>2) = Let\<^sub>d (combine_vars' \<Phi> e\<^sub>1) (combine_vars' (inv_map_past_let \<Phi>) e\<^sub>2)"

definition combine_vars :: "expr\<^sub>g \<Rightarrow> expr\<^sub>d" where
  "combine_vars e \<equiv> combine_vars' Map.empty e"

text \<open>We can prove (in \<open>combine_split_cancel\<close> and \<open>split_combine_cancel\<close>) that our two operations 
split and combine are inverses; or at least, are inverses on closed expressions (as shown by their 
typechecking in the empty context).\<close>

lemma inv_map_past_lam_inv [simp]: "(\<And>x y. \<Phi> x = Some y \<Longrightarrow> \<Phi>' y = Some x) \<Longrightarrow> 
    map_past_lam \<Phi> x = Some y \<Longrightarrow> inv_map_past_lam \<Phi>' y = Some x"
  by (cases x) auto

lemma inv_inv_map_past_lam_inv [simp]: "(\<And>x y. \<Phi> x = Some y \<Longrightarrow> \<Phi>' y = Some x) \<Longrightarrow> 
    inv_map_past_lam \<Phi> x = Some y \<Longrightarrow> map_past_lam \<Phi>' y = Some x"
  by (cases x) (auto split: nat.splits)

lemma inv_map_past_let_inv [simp]: "(\<And>x y. \<Phi> x = Some y \<Longrightarrow> \<Phi>' y = Some x) \<Longrightarrow> 
    map_past_let \<Phi> x = Some y \<Longrightarrow> inv_map_past_let \<Phi>' y = Some x"
  by (cases x) auto

lemma inv_inv_map_past_let_inv [simp]: "(\<And>x y. \<Phi> x = Some y \<Longrightarrow> \<Phi>' y = Some x) \<Longrightarrow> 
    inv_map_past_let \<Phi> x = Some y \<Longrightarrow> map_past_let \<Phi>' y = Some x"
  by (cases x) (auto split: if_splits)

lemma dom_map_past_lam [simp]: "dom (map_past_lam \<Phi>) = insert 0 (Suc ` dom \<Phi>)"
proof (auto simp add: dom_def split: nat.splits)
  fix x
  show "x \<notin> Suc ` {a. \<exists>aa b. \<Phi> a = Some (aa, b)} \<Longrightarrow> 
    \<forall>x2. x = Suc x2 \<longrightarrow> (\<exists>b a. \<Phi> x2 = Some (a, b)) \<Longrightarrow> x = 0" by (cases x) auto
qed

lemma dom_map_past_let [simp]: "dom (map_past_let \<Phi>) = insert 0 (Suc ` dom \<Phi>)"
proof (auto simp add: dom_def split: nat.splits)
  fix x
  show "x \<notin> Suc ` {a. \<exists>aa b. \<Phi> a = Some (aa, b)} \<Longrightarrow>
    \<forall>x2. x = Suc x2 \<longrightarrow> (\<exists>a b. \<Phi> x2 = Some (a, b)) \<Longrightarrow> x = 0" by (cases x) auto
qed

lemma dom_inv_map_past_lam [simp]: "dom (inv_map_past_lam \<Phi>) = insert (0, 0) (apfst Suc ` dom \<Phi>)"
  by (auto simp add: dom_def image_iff split: nat.splits) force+

lemma dom_inv_map_past_let [simp]: "dom (inv_map_past_let \<Phi>) = 
    insert (0, 0) ((\<lambda>(x, y). (x, if x = 0 then Suc y else y)) ` dom \<Phi>)"
  by (auto simp add: dom_def image_iff split: if_splits)
     (force, metis Suc_pred not_None_eq, force)

lemma combine_split_cancel' [simp]: "\<Gamma> \<turnstile>\<^sub>d e : t \<Longrightarrow> dom \<Phi> = dom (lookup \<Gamma>) \<Longrightarrow> 
  (\<And>x y. \<Phi> x = Some y \<Longrightarrow> \<Phi>' y = Some x) \<Longrightarrow> combine_vars' \<Phi>' (split_vars' \<Phi> e) = e"
proof (induction \<Gamma> e t arbitrary: \<Phi> \<Phi>' rule: typing\<^sub>d.induct)
  case (tc\<^sub>d_var \<Gamma> x t)
  moreover hence "x \<in> dom \<Phi>" by auto
  ultimately show ?case by fastforce
next
  case (tc\<^sub>d_lam t\<^sub>1 \<Gamma> e t\<^sub>2)
  moreover hence "\<And>x y. map_past_lam \<Phi> x = Some y \<Longrightarrow> inv_map_past_lam \<Phi>' y = Some x"
    using inv_map_past_lam_inv by fastforce
  ultimately show ?case by (simp add: Let_def)
next
  case (tc\<^sub>d_let \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
  moreover hence "\<And>x y. map_past_let \<Phi> x = Some y \<Longrightarrow> inv_map_past_let \<Phi>' y = Some x" 
    using inv_map_past_let_inv by fastforce
  ultimately show ?case by simp
qed simp_all
     
lemma combine_split_cancel [simp]: "[] \<turnstile>\<^sub>d e : t \<Longrightarrow> combine_vars (split_vars e) = e"
proof (unfold combine_vars_def split_vars_def)
  assume "[] \<turnstile>\<^sub>d e : t" 
  moreover have "dom Map.empty = dom (lookup [])" by simp
  moreover have "\<And>x y. Map.empty x = Some y \<Longrightarrow> Map.empty y = Some x" by simp
  ultimately show "combine_vars' Map.empty (split_vars' Map.empty e) = e" 
    by (metis combine_split_cancel')
qed

lemma split_combine_cancel' [simp]: "\<Gamma> \<turnstile>\<^sub>g e : t \<Longrightarrow> (\<And>x y. \<Phi> x = Some y \<Longrightarrow> \<Phi>' y = Some x) \<Longrightarrow>  
  dom \<Phi> = {xy. \<exists>z. lookup \<Gamma> (fst xy) = Some z \<and> snd xy \<in> dom (lookup z)} \<Longrightarrow>
  split_vars' \<Phi>' (combine_vars' \<Phi> e) = e"
proof (induction \<Gamma> e t arbitrary: \<Phi> \<Phi>' rule: typing\<^sub>g.induct)
  case (tc\<^sub>g_var \<Gamma> x ts y t)
  hence "(x, y) \<in> dom \<Phi>" by auto
  with tc\<^sub>g_var show ?case by fastforce
next
  case (tc\<^sub>g_lam t\<^sub>1 \<Gamma> e t\<^sub>2)
  hence X: "\<And>x y. inv_map_past_lam \<Phi> x = Some y \<Longrightarrow> map_past_lam \<Phi>' y = Some x" 
    using inv_inv_map_past_lam_inv by fastforce
  have Y: "insert_at 0 [t\<^sub>1] \<Gamma> \<noteq> []" by (cases \<Gamma>) simp_all
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
  with tc\<^sub>g_lam X Y show ?case by (simp add: Let_def)
next
  case (tc\<^sub>g_let \<Gamma> e\<^sub>1 t\<^sub>1 e\<^sub>2 t\<^sub>2)
  hence X: "\<And>x y. inv_map_past_let \<Phi> x = Some y \<Longrightarrow> map_past_let \<Phi>' y = Some x" 
    using inv_inv_map_past_let_inv by fastforce

  from tc\<^sub>g_let have "\<Gamma> \<turnstile>\<^sub>g e\<^sub>1 : t\<^sub>1" by simp
  from tc\<^sub>g_let have "cons_fst t\<^sub>1 \<Gamma> \<turnstile>\<^sub>g e\<^sub>2 : t\<^sub>2" by simp
  from tc\<^sub>g_let have "split_vars' \<Phi>' (combine_vars' \<Phi> e\<^sub>1) = e\<^sub>1" by simp
  from tc\<^sub>g_let have "\<Phi> xx = Some xy \<Longrightarrow> \<Phi>' xy = Some xx" by simp
  from tc\<^sub>g_let have "dom \<Phi> = {xy. \<exists>z. lookup \<Gamma> (fst xy) = Some z \<and> snd xy \<in> dom (lookup z)}" by simp


  have Y: "\<And>xy. xy \<in> insert (0, 0) ((\<lambda>x. case x of (x, y) \<Rightarrow> (x, if x = 0 then Suc y else y)) `
    {xy. \<exists>z. lookup \<Gamma> (fst xy) = Some z \<and> snd xy \<in> dom (lookup z)}) \<Longrightarrow>
    xy \<in> {xy. \<exists>z. (case fst xy of 0 \<Rightarrow> (case lookup \<Gamma> 0 of None \<Rightarrow> Some [t\<^sub>1] 
      | Some aa \<Rightarrow> Some (t\<^sub>1 # aa)) | Suc x' \<Rightarrow> lookup \<Gamma> (fst xy)) = Some z \<and> 
      snd xy \<in> dom (lookup z)}" 
    by (auto simp add: image_iff split: option.splits nat.splits)
  have "\<And>xy. xy \<in> {xy. \<exists>z. (case fst xy of 0 \<Rightarrow> (case lookup \<Gamma> 0 of None \<Rightarrow> Some [t\<^sub>1] 
      | Some aa \<Rightarrow> Some (t\<^sub>1 # aa)) | Suc x' \<Rightarrow> lookup \<Gamma> (fst xy)) = Some z \<and> 
      snd xy \<in> dom (lookup z)} \<Longrightarrow> 
    xy \<in> insert (0, 0) ((\<lambda>x. case x of (x, y) \<Rightarrow> (x, if x = 0 then Suc y else y)) `
      {xy. \<exists>z. lookup \<Gamma> (fst xy) = Some z \<and> snd xy \<in> dom (lookup z)})" 
  proof
    fix xy
    assume "xy \<in> {xy. \<exists>z. (case fst xy of 0 \<Rightarrow> (case lookup \<Gamma> 0 of None \<Rightarrow> Some [t\<^sub>1] 
      | Some aa \<Rightarrow> Some (t\<^sub>1 # aa)) | Suc x' \<Rightarrow> lookup \<Gamma> (fst xy)) = Some z \<and>
        snd xy \<in> dom (lookup z)}"
    moreover assume "xy \<notin> (\<lambda>x. case x of (x, y) \<Rightarrow> (x, if x = 0 then Suc y else y)) `
      {xy. \<exists>z. lookup \<Gamma> (fst xy) = Some z \<and> snd xy \<in> dom (lookup z)}"
    moreover obtain x y where "xy = (x, y)" by fastforce
    ultimately show "xy = (0, 0)" by (auto simp add: image_iff split: nat.splits option.splits)
  qed
  with Y have "insert (0, 0) ((\<lambda>x. case x of (x, y) \<Rightarrow> (x, if x = 0 then Suc y else y)) `
    {xy. \<exists>z. lookup \<Gamma> (fst xy) = Some z \<and> snd xy \<in> dom (lookup z)}) =
    {xy. \<exists>z. (case fst xy of 0 \<Rightarrow> (case lookup \<Gamma> 0 of None \<Rightarrow> Some [t\<^sub>1] | Some aa \<Rightarrow> Some (t\<^sub>1 # aa))
      | Suc x' \<Rightarrow> lookup \<Gamma> (fst xy)) = Some z \<and> snd xy \<in> dom (lookup z)}" 
    by blast
  with tc\<^sub>g_let X show ?case by simp
qed simp_all

lemma split_combine_cancel [simp]: "[] \<turnstile>\<^sub>g e : t \<Longrightarrow> split_vars (combine_vars e) = e"
proof (unfold combine_vars_def split_vars_def)
  assume "[] \<turnstile>\<^sub>g e : t"
  moreover have "\<And>x y. Map.empty x = Some y \<Longrightarrow> Map.empty y = Some x" by simp 
  moreover have "dom Map.empty = {xy. \<exists>z. lookup [] (fst xy) = Some z \<and> snd xy \<in> dom (lookup z)}" 
    using lookup.elims option.simps(3) by force
  ultimately show "split_vars' Map.empty (combine_vars' Map.empty e) = e"
    by (rule split_combine_cancel')
qed

text \<open>Now, we can define our combining function on closures, callstacks, and states. The 
environments contained in the closures, which caused so much difficulties the other way around, are 
simply concatenated together.\<close>

fun map_from_env :: "'a list list \<Rightarrow> nat \<times> nat \<rightharpoonup> nat" where
  "map_from_env [] (x, y) = None"
| "map_from_env (cs # \<Delta>) (0, y) = (if y < length cs then Some y else None)"
| "map_from_env (cs # \<Delta>) (Suc x, y) = map_option ((+) (length cs)) (map_from_env \<Delta> (x, y))"

lemma lookup_map_from_env [simp]: "lookup \<Delta> x = Some cs \<Longrightarrow> lookup cs y = Some c \<Longrightarrow> 
    map_from_env \<Delta> (x, y) \<noteq> None"
  by (induction \<Delta> "(x, y)" arbitrary: x y rule: map_from_env.induct) simp_all

lemma lookup_concat_map_from_env [simp]: "lookup \<Delta> x = Some cs \<Longrightarrow> lookup cs y = Some c \<Longrightarrow> 
    lookup (concat \<Delta>) (the (map_from_env \<Delta> (x, y))) = Some c"
proof (induction \<Delta> "(x, y)" arbitrary: x y rule: map_from_env.induct)
  case (3 cs \<Delta> x y)
  then show ?case by (cases "map_from_env \<Delta> (x, y)") simp_all
qed simp_all

primrec combine_closure :: "closure\<^sub>g \<Rightarrow> closure\<^sub>c" where
  "combine_closure (Num\<^sub>g n) = Const\<^sub>c n"
| "combine_closure (Fun\<^sub>g t \<Delta> e n) = 
    Lam\<^sub>c t (concat (map (map combine_closure) \<Delta>)) 
      (combine_vars' (inv_map_past_lam (map_from_env \<Delta>)) e)"

primrec combine_frame :: "frame\<^sub>g \<Rightarrow> frame\<^sub>c" where
  "combine_frame (FApp1\<^sub>g \<Delta> e) = 
    FApp1\<^sub>c (concat (map (map combine_closure) \<Delta>)) (combine_vars' (map_from_env \<Delta>) e)"
| "combine_frame (FApp2\<^sub>g c) = FApp2\<^sub>c (combine_closure c)"
| "combine_frame (FLet\<^sub>g \<Delta> e) = 
    FLet\<^sub>c (concat (map (map combine_closure) \<Delta>)) (combine_vars' (map_from_env \<Delta>) e)"
| "combine_frame (FPop\<^sub>g c) = FPop\<^sub>c (combine_closure c)"
| "combine_frame (FReturn\<^sub>g \<Delta>) = FReturn\<^sub>c (concat (map (map combine_closure) \<Delta>))"

primrec combine_state :: "state\<^sub>g \<Rightarrow> state\<^sub>c" where
  "combine_state (SE\<^sub>g s \<Delta> e) = 
    SE\<^sub>c (map combine_frame s) (concat (map (map combine_closure) \<Delta>)) 
      (combine_vars' (map_from_env \<Delta>) e)"
| "combine_state (SC\<^sub>g s c) = SC\<^sub>c (map combine_frame s) (combine_closure c)"

text \<open>We can now prove our typechecking theorems: note again how the "empty" context cannot really 
be \<open>[]\<close>, because of the need for a space to put top-level lets in.\<close>

lemma map_from_env_insert' [simp]: "map_from_env (insert_at 0 [t] \<Gamma>) x = 
    inv_map_past_lam (map_from_env \<Gamma>) x"
  by (induction \<Gamma> x rule: map_from_env.induct) (simp_all split: nat.splits)

lemma map_from_env_insert [simp]: "map_from_env (insert_at 0 [t] \<Gamma>) = 
    inv_map_past_lam (map_from_env \<Gamma>)"
  by auto

lemma map_from_env_mapfst' [simp]: "map_from_env (cons_fst t \<Gamma>) x = 
    inv_map_past_let (map_from_env \<Gamma>) x"
proof (induction \<Gamma> x rule: map_from_env.induct)
  case (1 x y)
  thus ?case by (cases x) simp_all
qed (auto simp add: option.map_comp)

lemma map_from_env_mapfst [simp]: "map_from_env (cons_fst t \<Gamma>) = inv_map_past_let (map_from_env \<Gamma>)"
  by auto

lemma typecheck_combine [simp]: "\<Gamma> \<turnstile>\<^sub>g e : t \<Longrightarrow> concat \<Gamma> \<turnstile>\<^sub>d combine_vars' (map_from_env \<Gamma>) e : t"
  by (induction \<Gamma> e t rule: typing\<^sub>g.induct) simp_all

lemma "c :\<^sub>g\<^sub>c\<^sub>l t \<Longrightarrow> True"
  and map_from_env_type_vals' [simp]: "\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> map_from_env \<Gamma> x = map_from_env \<Delta> x"
proof (induction c t and \<Delta> \<Gamma> arbitrary: and x rule: typing_closure\<^sub>g_typing_environment\<^sub>g.inducts)
  case tc\<^sub>c_nil
  thus ?case by (cases x) simp_all
next
  case (tc\<^sub>c_cons_nil \<Delta> \<Gamma>)
  thus ?case
  proof (induction x)
    case (Pair a b)
    then show ?case by (cases a) simp_all
  qed
next
  case (tc\<^sub>c_cons_cons c t cs \<Delta> ts \<Gamma>)
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
  and typecheck_concat_combine_closure [simp]: "\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma> \<Longrightarrow> 
    concat (map (map combine_closure) \<Delta>) :\<^sub>c\<^sub>l\<^sub>s concat \<Gamma>"
proof (induction c t and \<Delta> \<Gamma> rule: typing_closure\<^sub>g_typing_environment\<^sub>g.inducts)
  case (tc\<^sub>c_lam \<Delta> \<Gamma> t\<^sub>1 e t\<^sub>2)
  hence X: "map_from_env \<Gamma> = map_from_env \<Delta>" by simp
  from tc\<^sub>c_lam have "concat (insert_at 0 [t\<^sub>1] \<Gamma>) \<turnstile>\<^sub>d 
    combine_vars' (map_from_env (insert_at 0 [t\<^sub>1] \<Gamma>)) e : t\<^sub>2" by (metis typecheck_combine)
  hence "insert_at 0 t\<^sub>1 (concat \<Gamma>) \<turnstile>\<^sub>d combine_vars' (inv_map_past_lam (map_from_env \<Gamma>)) e : t\<^sub>2" 
    by simp
  hence "insert_at 0 t\<^sub>1 (concat \<Gamma>) \<turnstile>\<^sub>d combine_vars' (inv_map_past_lam (map_from_env \<Delta>)) e : t\<^sub>2" 
    using X by metis
  with tc\<^sub>c_lam show ?case by simp
qed simp_all

lemma combine_clsoure_mapfst [simp]: "concat (map (map combine_closure) (cons_fst c \<Delta>)) = 
    combine_closure c # concat (map (map combine_closure) \<Delta>)"
  by (induction \<Delta>) simp_all

lemma latest_combine_env [simp]: "latest_environment\<^sub>c (map combine_frame s) =
  map_option (\<lambda>\<Delta>. concat (map (map combine_closure) \<Delta>)) (latest_environment\<^sub>g s)"
proof (induction s rule: latest_environment\<^sub>g.induct)
  case (5 c s)
  then show ?case by (simp add: option.map_comp comp_def)
qed simp_all

lemma typecheck_stack [simp]: "s :\<^sub>g t\<^sub>2 \<rightarrow> t \<Longrightarrow> map combine_frame s :\<^sub>c t\<^sub>2 \<rightarrow> t"
proof (induction s t\<^sub>2 t rule: typing_stack\<^sub>g.induct)
  case (tcc_scons_app1 \<Delta> \<Gamma> e t\<^sub>1 s t\<^sub>2 t)
  hence X: "concat (map (map combine_closure) \<Delta>) :\<^sub>c\<^sub>l\<^sub>s concat \<Gamma>" by simp
  from tcc_scons_app1 have "map_from_env \<Delta> = map_from_env \<Gamma>" by simp
  with tcc_scons_app1(2) have Y: "concat \<Gamma> \<turnstile>\<^sub>d combine_vars' (map_from_env \<Delta>) e : t\<^sub>1" by simp
  from tcc_scons_app1 have "latest_environment\<^sub>c (map combine_frame s) = 
    Some (concat (map (map combine_closure) \<Delta>))" by simp
  with tcc_scons_app1 X Y have "FApp1\<^sub>c (concat (map (map combine_closure) \<Delta>)) 
    (combine_vars' (map_from_env \<Delta>) e) # map combine_frame s :\<^sub>c Arrow t\<^sub>1 t\<^sub>2 \<rightarrow> t" 
      by (metis typing_stack\<^sub>c.tcc_scons_app1)
  thus ?case by simp
next
  case (tcc_scons_app2 c t\<^sub>1 t\<^sub>2 s t)
  then show ?case by simp
next
  case (tcc_scons_let s \<Delta> \<Gamma> t\<^sub>1 e t\<^sub>2 t)
  then show ?case by simp
next
  case (tcc_scons_pop s \<Delta> c tt t' t)
  then show ?case by simp
next
  case (tcc_scons_ret \<Delta> \<Gamma> s t' t)
  then show ?case by simp
qed simp_all
                                  
end