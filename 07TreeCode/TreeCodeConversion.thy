theory TreeCodeConversion
  imports TreeCode "../06GroupedEnvironments/GroupedEnvironments"
begin

subsection \<open>Compilation to Tree-Code\<close>

text \<open>This is our first real compilation phase; typechecking, name-removal, and variable-splitting 
were fundamentally just modifying an underlying expression, but here we genuinely reshape our 
expressions into code. The first few steps are simple: encoding an expression means shuffling it 
into a postfix form, and tree-code closures-values are just encoded stack closure-values. We add a 
\<open>Return\<^sub>e\<close> operation on at the end of every code block, too; we never encode the \<open>Jump\<^sub>e\<close> operation. 
Its place will come a little later.\<close>

primrec encode' :: "expr\<^sub>g \<Rightarrow> code\<^sub>e list" where
  "encode' (Var\<^sub>g x y) = [Lookup\<^sub>e x y]"
| "encode' (Const\<^sub>g n) = [PushCon\<^sub>e n]"
| "encode' (Lam\<^sub>g t e n) = [PushLam\<^sub>e (encode' e @ [Return\<^sub>e]) n]"
| "encode' (App\<^sub>g e\<^sub>1 e\<^sub>2) = encode' e\<^sub>1 @ encode' e\<^sub>2 @ [Apply\<^sub>e]"
| "encode' (Let\<^sub>g e\<^sub>1 e\<^sub>2) = encode' e\<^sub>1 @ PushEnv\<^sub>e # encode' e\<^sub>2"

definition encode :: "expr\<^sub>g \<Rightarrow> code\<^sub>e list" where
  "encode e \<equiv> encode' e @ [Return\<^sub>e]"

primrec encode_closure :: "closure\<^sub>g \<Rightarrow> closure\<^sub>e" where
  "encode_closure (Num\<^sub>g n) = Const\<^sub>e n"
| "encode_closure (Fun\<^sub>g t \<Delta> e n) = Lam\<^sub>e (map (map encode_closure) \<Delta>) (encode e) n" 

lemma tl_encode [simp]: "tl (encode' e @ \<C>) = tl (encode' e) @ \<C>"
  by (induction e arbitrary: \<C>) simp_all

text \<open>It is the callstack where things get complicated: we have to divide the stack into a 
callstack and a value stack. The value stack consists of the returned closure-values in \<open>FApp2\<^sub>g\<close> 
frames:\<close>

fun vals_from_stack :: "frame\<^sub>g list \<Rightarrow> closure\<^sub>e list" where
  "vals_from_stack [] = []"
| "vals_from_stack (FApp1\<^sub>g \<Delta> e # s\<^sub>g) = vals_from_stack s\<^sub>g"
| "vals_from_stack (FApp2\<^sub>g c # s\<^sub>g) = encode_closure c # vals_from_stack s\<^sub>g"
| "vals_from_stack (FLet\<^sub>g \<Delta> e # s\<^sub>g) = vals_from_stack s\<^sub>g"
| "vals_from_stack (FReturn\<^sub>g \<Delta> # s\<^sub>g) = vals_from_stack s\<^sub>g"

text \<open>The callstack requires some more careful work. Each frame represents a place where we are part
of the way through the block of code associated with a particular expression; fortunately, we can 
reconstruct what the code must have been to get us to this state, and then prepend it into the most
recent stack frame. The \<open>FReturn\<^sub>g\<close> frames and their environments that we have been so diligently 
recording for the last two stages finally prove their worth, as well: they show us where (and with 
what environment) callstack frames begin.\<close>

fun prepend_to_top_frame :: "code\<^sub>e list \<Rightarrow> frame\<^sub>e list \<Rightarrow> frame\<^sub>e list" where
  "prepend_to_top_frame \<C> [] = []"
| "prepend_to_top_frame \<C> ((\<Delta>, \<C>') # s\<^sub>e) = (\<Delta>, \<C> @ \<C>') # s\<^sub>e"

fun prepend_to_top_env :: "closure\<^sub>e \<Rightarrow> frame\<^sub>e list \<Rightarrow> frame\<^sub>e list" where
  "prepend_to_top_env c [] = []"
| "prepend_to_top_env c ((\<Delta>, \<C>) # s\<^sub>e) = (snoc_fst c \<Delta>, \<C>) # s\<^sub>e"

fun stack_from_stack :: "frame\<^sub>g list \<Rightarrow> frame\<^sub>e list" where
  "stack_from_stack [] = []"
| "stack_from_stack (FApp1\<^sub>g \<Delta> e # s\<^sub>g) = 
    prepend_to_top_frame (encode' e @ [Apply\<^sub>e]) (stack_from_stack s\<^sub>g)"
| "stack_from_stack (FApp2\<^sub>g c # s\<^sub>g) = prepend_to_top_frame [Apply\<^sub>e] (stack_from_stack s\<^sub>g)"
| "stack_from_stack (FLet\<^sub>g \<Delta> e # s\<^sub>g) = 
    prepend_to_top_frame (PushEnv\<^sub>e # encode' e) (stack_from_stack s\<^sub>g)"
| "stack_from_stack (FReturn\<^sub>g \<Delta> # s\<^sub>g) = 
    (map (map encode_closure) \<Delta>, [Return\<^sub>e]) # stack_from_stack s\<^sub>g"

lemma prepend_nil [simp]: "prepend_to_top_frame [] s\<^sub>e = s\<^sub>e"
  by (induction "[] :: code\<^sub>e list" s\<^sub>e rule: prepend_to_top_frame.induct) simp_all

lemma prepend_append [simp]: "prepend_to_top_frame (\<C> @ \<C>') s\<^sub>e = 
    prepend_to_top_frame \<C> (prepend_to_top_frame \<C>' s\<^sub>e)"
  by (induction "\<C> @ \<C>'" s\<^sub>e rule: prepend_to_top_frame.induct) simp_all

text \<open>We once again collapse the distinction between our two states, evaluating and returning; an 
evaluation state is simply one where a little more code is there to be executed in the topmost 
frame.\<close>

primrec encode_state :: "state\<^sub>g \<Rightarrow> state\<^sub>e" where
  "encode_state (SE\<^sub>g s\<^sub>g \<Delta> e) = 
    S\<^sub>e (vals_from_stack s\<^sub>g) (prepend_to_top_frame (encode' e) (stack_from_stack s\<^sub>g))"
| "encode_state (SC\<^sub>g s\<^sub>g c) = S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>g) (stack_from_stack s\<^sub>g)"

text \<open>Because the conversion functions run forwards, we can once again prove correctness easily.
(Because we have no typing judgement for tree code, we do not - cannot - prove type safety.) 
We again have to use \<open>iter\<close> in our statement of the theorem, because the frame-adjustment evaluation
steps (\<open>ret\<^sub>g_app1\<close> and \<open>ret\<^sub>g_app2\<close>) are not matched by any steps in the tree-code evaluation.\<close>

lemma lookup_latest [dest]: "latest_environment\<^sub>g s\<^sub>g = Some \<Delta> \<Longrightarrow> 
    \<exists>\<C> s\<^sub>e. stack_from_stack s\<^sub>g = (map (map encode_closure) \<Delta>, \<C>) # s\<^sub>e"
  by (induction s\<^sub>g arbitrary: \<Delta> rule: stack_from_stack.induct) fastforce+

theorem correct\<^sub>e [simp]: "\<Sigma> \<leadsto>\<^sub>g \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>g t \<Longrightarrow> iter (\<leadsto>\<^sub>e) (encode_state \<Sigma>) (encode_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>g.induct)
  case (ev\<^sub>g_var \<Delta> x ts y c s\<^sub>g)
  then obtain ts t' \<Gamma> where "(s\<^sub>g :\<^sub>g t' \<rightarrow> t) \<and> (\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> latest_environment\<^sub>g s\<^sub>g = Some \<Delta> \<and> 
    lookup \<Gamma> x = Some ts \<and> lookup ts y = Some t'" by fastforce
  then obtain \<C> s\<^sub>e where S: "stack_from_stack s\<^sub>g = (map (map encode_closure) \<Delta>, \<C>) # s\<^sub>e" by auto
  with ev\<^sub>g_var have "
    S\<^sub>e (vals_from_stack s\<^sub>g) ((map (map encode_closure) \<Delta>, Lookup\<^sub>e x y # \<C>) # s\<^sub>e) \<leadsto>\<^sub>e 
      S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>g) ((map (map encode_closure) \<Delta>, \<C>) # s\<^sub>e)" by simp
  hence "iter (\<leadsto>\<^sub>e) (S\<^sub>e (vals_from_stack s\<^sub>g) ((map (map encode_closure) \<Delta>, Lookup\<^sub>e x y # \<C>) # s\<^sub>e))
    (S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>g) ((map (map encode_closure) \<Delta>, \<C>) # s\<^sub>e))" 
      by (metis iter_one)
  with S show ?case by simp
next
  case (ev\<^sub>g_con s\<^sub>g \<Delta> n)
  then obtain \<Gamma> where "(s\<^sub>g :\<^sub>g Num \<rightarrow> t) \<and> (\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> latest_environment\<^sub>g s\<^sub>g = Some \<Delta>" 
    by fastforce
  then obtain \<C> s\<^sub>e where S: "stack_from_stack s\<^sub>g = (map (map encode_closure) \<Delta>, \<C>) # s\<^sub>e" by auto
  have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (vals_from_stack s\<^sub>g) ((map (map encode_closure) \<Delta>, PushCon\<^sub>e n # \<C>) # s\<^sub>e)) 
    (S\<^sub>e (Const\<^sub>e n # vals_from_stack s\<^sub>g) ((map (map encode_closure) \<Delta>, \<C>) # s\<^sub>e))" 
      by (metis ev\<^sub>e_pushcon iter_one)
  with S show ?case by simp
next
  case (ev\<^sub>g_lam s\<^sub>g \<Delta> tt e n)
  then obtain t' \<Gamma> where "(s\<^sub>g :\<^sub>g t' \<rightarrow> t) \<and> (\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> latest_environment\<^sub>g s\<^sub>g = Some \<Delta> \<and>
    (\<Gamma> \<turnstile>\<^sub>g Lam\<^sub>g tt e n : t')" by fastforce
  then obtain \<C> s\<^sub>e where S: "stack_from_stack s\<^sub>g = (map (map encode_closure) \<Delta>, \<C>) # s\<^sub>e" by auto
  have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (vals_from_stack s\<^sub>g) ((map (map encode_closure) \<Delta>, 
    PushLam\<^sub>e (encode e) n # \<C>) # s\<^sub>e)) 
      (S\<^sub>e (Lam\<^sub>e (map (map encode_closure) \<Delta>) (encode e) n # vals_from_stack s\<^sub>g)
        ((map (map encode_closure) \<Delta>, \<C>) # s\<^sub>e))" by (metis ev\<^sub>e_pushlam iter_one)
  with S show ?case by (simp add: encode_def)
next
  case (ret\<^sub>g_app2 t\<^sub>1 \<Delta> e\<^sub>1 n s\<^sub>g c\<^sub>2)
  then obtain \<Gamma> t\<^sub>2 \<Delta>' where "(\<Delta> :\<^sub>g\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> (insert_at 0 [t\<^sub>1] \<Gamma> \<turnstile>\<^sub>g e\<^sub>1 : t\<^sub>2) \<and> (s\<^sub>g :\<^sub>g t\<^sub>2 \<rightarrow> t) \<and> 
    latest_environment\<^sub>g s\<^sub>g = Some \<Delta>' \<and> (c\<^sub>2 :\<^sub>g\<^sub>c\<^sub>l t\<^sub>1)" by blast
  then obtain \<C> s\<^sub>e where S: "stack_from_stack s\<^sub>g = (map (map encode_closure) \<Delta>', \<C>) # s\<^sub>e" by auto
  hence "iter (\<leadsto>\<^sub>e) 
    (S\<^sub>e (encode_closure c\<^sub>2 # Lam\<^sub>e (map (map encode_closure) \<Delta>) (encode e\<^sub>1) n # vals_from_stack s\<^sub>g) 
      ((map (map encode_closure) \<Delta>', Apply\<^sub>e # \<C>) # s\<^sub>e)) 
    (S\<^sub>e (vals_from_stack s\<^sub>g) (([encode_closure c\<^sub>2] # map (map encode_closure) \<Delta>, encode e\<^sub>1) # 
      stack_from_stack s\<^sub>g))" by (metis ev\<^sub>e_apply iter_one)
  with S show ?case by (simp add: encode_def)
next
  case (ret\<^sub>g_let \<Delta> e\<^sub>2 s\<^sub>g c\<^sub>1)
  have "iter (\<leadsto>\<^sub>e)
    (S\<^sub>e (encode_closure c\<^sub>1 # vals_from_stack s\<^sub>g)
      ((map (map encode_closure) \<Delta>, PushEnv\<^sub>e # encode' e\<^sub>2 @ [Return\<^sub>e]) # stack_from_stack s\<^sub>g))
    (S\<^sub>e (vals_from_stack s\<^sub>g)
      ((snoc_fst (encode_closure c\<^sub>1) (map (map encode_closure) \<Delta>), encode' e\<^sub>2 @ [Return\<^sub>e]) # 
      stack_from_stack s\<^sub>g))" 
    by (metis ev\<^sub>e_pushenv iter_one)
  thus ?case by simp
next
  case (ret\<^sub>g_ret \<Delta> s\<^sub>g c)
  have "S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>g) ((map (map encode_closure) \<Delta>, [Return\<^sub>e]) # 
    stack_from_stack s\<^sub>g) \<leadsto>\<^sub>e
    S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>g) (stack_from_stack s\<^sub>g)" by simp
  hence "iter (\<leadsto>\<^sub>e) 
    (S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>g) ((map (map encode_closure) \<Delta>, [Return\<^sub>e]) # 
    stack_from_stack s\<^sub>g))
    (S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>g) (stack_from_stack s\<^sub>g))" by (metis iter_one)
  thus ?case by simp
qed fastforce+

lemma correct\<^sub>e_iter [simp]: "iter (\<leadsto>\<^sub>g) \<Sigma> \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>g t \<Longrightarrow>
  iter (\<leadsto>\<^sub>e) (encode_state \<Sigma>) (encode_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: iter.induct)
  case (iter_step \<Sigma> \<Sigma>' \<Sigma>'')
  hence "iter (\<leadsto>\<^sub>e) (encode_state \<Sigma>) (encode_state \<Sigma>')" by simp
  moreover from iter_step have "iter (\<leadsto>\<^sub>e) (encode_state \<Sigma>') (encode_state \<Sigma>'')" by simp
  ultimately show ?case by (metis iter_append)
qed simp_all

text \<open>Completeness, inevitably, is much more difficult. In particular, we not only need the usual 
host of reconstruction lemmas, we also need some helper functions just to precisely state them. 
\<open>head_expr\<close> and \<open>tail_expr\<close> pull an expression apart into its leftmost leaf (value or variable) and 
the closure call-stack that the expression will unwind to.\<close>

primrec head_expr :: "expr\<^sub>g \<Rightarrow> expr\<^sub>g" where
  "head_expr (Var\<^sub>g x y) = Var\<^sub>g x y"
| "head_expr (Const\<^sub>g n) = Const\<^sub>g n"
| "head_expr (Lam\<^sub>g t e n) = Lam\<^sub>g t e n"
| "head_expr (App\<^sub>g e\<^sub>1 e\<^sub>2) = head_expr e\<^sub>1"
| "head_expr (Let\<^sub>g e\<^sub>1 e\<^sub>2) = head_expr e\<^sub>1"

primrec tail_expr :: "closure\<^sub>g list list \<Rightarrow> expr\<^sub>g \<Rightarrow> frame\<^sub>g list" where
  "tail_expr \<Delta> (Var\<^sub>g x y) = []"
| "tail_expr \<Delta> (Const\<^sub>g n) = []"
| "tail_expr \<Delta> (Lam\<^sub>g t e n) = []"
| "tail_expr \<Delta> (App\<^sub>g e\<^sub>1 e\<^sub>2) = tail_expr \<Delta> e\<^sub>1 @ [FApp1\<^sub>g \<Delta> e\<^sub>2]"
| "tail_expr \<Delta> (Let\<^sub>g e\<^sub>1 e\<^sub>2) = tail_expr \<Delta> e\<^sub>1 @ [FLet\<^sub>g \<Delta> e\<^sub>2]"

lemma vals_from_tail_expr [simp]: "vals_from_stack (tail_expr \<Delta> e @ s\<^sub>g) = vals_from_stack s\<^sub>g"
  by (induction e arbitrary: s\<^sub>g) simp_all

lemma stack_from_tail_expr [simp]: "stack_from_stack (tail_expr \<Delta> e @ s\<^sub>g) = 
    prepend_to_top_frame (tl (encode' e)) (stack_from_stack s\<^sub>g)"
  by (induction e arbitrary: s\<^sub>g) simp_all

lemma evaluate_to_head_tail [simp]: "let_floated\<^sub>g e \<Longrightarrow> let_free\<^sub>g e \<or> return_headed\<^sub>g s \<Longrightarrow>
  latest_environment\<^sub>g s = Some \<Delta> \<Longrightarrow> 
    iter (\<leadsto>\<^sub>g) (SE\<^sub>g s \<Delta> e) (SE\<^sub>g (tail_expr \<Delta> e @ s) \<Delta> (head_expr e))"
proof (induction e arbitrary: s)
  case (App\<^sub>g e\<^sub>1 e\<^sub>2)
  hence "iter (\<leadsto>\<^sub>g) (SE\<^sub>g (FApp1\<^sub>g \<Delta> e\<^sub>2 # s) \<Delta> e\<^sub>1) 
    (SE\<^sub>g (tail_expr \<Delta> e\<^sub>1 @ FApp1\<^sub>g \<Delta> e\<^sub>2 # s) \<Delta> (head_expr e\<^sub>1))" by simp
  moreover have "SE\<^sub>g s \<Delta> (App\<^sub>g e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>g SE\<^sub>g (FApp1\<^sub>g \<Delta> e\<^sub>2 # s) \<Delta> e\<^sub>1" by simp
  ultimately have "iter (\<leadsto>\<^sub>g) (SE\<^sub>g s \<Delta> (App\<^sub>g e\<^sub>1 e\<^sub>2))
    (SE\<^sub>g (tail_expr \<Delta> e\<^sub>1 @ FApp1\<^sub>g \<Delta> e\<^sub>2 # s) \<Delta> (head_expr e\<^sub>1))" 
      by (metis iter_step)
  thus ?case by simp
next
  case (Let\<^sub>g e1 e2)
  moreover hence "SE\<^sub>g s \<Delta> (Let\<^sub>g e1 e2) \<leadsto>\<^sub>g SE\<^sub>g (FLet\<^sub>g \<Delta> e2 # s) \<Delta> e1" by auto
  ultimately show ?case by simp
qed simp_all

text \<open>We now reconstruct encodings, stack-encodings, and state-encodings:\<close>

lemma encode'_not_nil [simp]: "encode' e \<noteq> []"
  by (induction e) simp_all

lemma encode_not_nil [simp]: "encode e \<noteq> []"
  by (simp add: encode_def)

lemma encode_to_lookup [dest]: "encode' e @ \<C>' = Lookup\<^sub>e x y # \<C> \<Longrightarrow> 
    head_expr e = Var\<^sub>g x y \<and> \<C> = tl (encode' e) @ \<C>'"
  by (induction e arbitrary: \<C>') fastforce+

lemma encode_to_pushcon [dest]: "encode' e @ \<C>' = PushCon\<^sub>e n # \<C> \<Longrightarrow> 
    head_expr e = Const\<^sub>g n \<and> \<C> = tl (encode' e) @ \<C>'"
  by (induction e arbitrary: \<C>') fastforce+

lemma encode_to_pushlam [dest]: "encode' e @ \<C>' = PushLam\<^sub>e \<C>'' n # \<C> \<Longrightarrow> 
  \<exists>t e'. head_expr e = Lam\<^sub>g t e' n \<and> \<C>'' = encode e' \<and> \<C> = tl (encode' e) @ \<C>'"
  using encode_def by (induction e arbitrary: \<C>') fastforce+

lemma encode_to_apply [dest]: "encode' e @ \<C>' = Apply\<^sub>e # \<C> \<Longrightarrow> False"
  by (induction e arbitrary: \<C>') simp_all

lemma encode_to_push [dest]: "encode' e @ \<C>' = PushEnv\<^sub>e # \<C> \<Longrightarrow> False"
  by (induction e arbitrary: \<C>') simp_all

lemma encode_to_return [dest]: "encode' e @ \<C>' = Return\<^sub>e # \<C> \<Longrightarrow> False"
  by (induction e arbitrary: \<C>') simp_all

lemma encode_to_jump [dest]: "encode' e @ \<C>' = Jump\<^sub>e # \<C> \<Longrightarrow> False"
  by (induction e arbitrary: \<C>') simp_all

lemma encode_lam_closure [dest]: "Lam\<^sub>e env \<C> n = encode_closure c \<Longrightarrow> 
    \<exists>t \<Delta> e. c = Fun\<^sub>g t \<Delta> e n \<and> env = map (map encode_closure) \<Delta> \<and> \<C> = encode e"
  by (induction c) simp_all

lemma prepend_frame_to_cons [dest]: "prepend_to_top_frame \<C>' s\<^sub>e = (\<Delta>, \<C>) # s\<^sub>e' \<Longrightarrow> 
    \<exists>\<C>''. s\<^sub>e = (\<Delta>, \<C>'') # s\<^sub>e' \<and> \<C> = \<C>' @ \<C>''"
  by (induction \<C>' s\<^sub>e rule: prepend_to_top_frame.induct) simp_all

lemma prepend_env_to_cons [dest]: "prepend_to_top_env c s\<^sub>e = (\<Delta>, \<C>) # s\<^sub>e' \<Longrightarrow> 
    \<exists>\<Delta>'. s\<^sub>e = (\<Delta>', \<C>) # s\<^sub>e' \<and> \<Delta> = snoc_fst c \<Delta>'"
  by (induction c s\<^sub>e rule: prepend_to_top_env.induct) simp_all

lemma prepend_to_apply [dest]: "prepend_to_top_frame (encode' e) s\<^sub>e = (\<Delta>, Apply\<^sub>e # \<C>) # s\<^sub>e' \<Longrightarrow> 
    False"
  by (induction "encode' e" s\<^sub>e rule: prepend_to_top_frame.induct) auto

lemma prepend_to_push [dest]: "prepend_to_top_frame (encode' e) s\<^sub>e = (\<Delta>, PushEnv\<^sub>e # \<C>) # s\<^sub>e' \<Longrightarrow> 
    False"
  by (induction "encode' e" s\<^sub>e rule: prepend_to_top_frame.induct) auto

lemma prepend_to_return [dest]: "prepend_to_top_frame (encode' e) s\<^sub>e = (\<Delta>, Return\<^sub>e # \<C>) # s\<^sub>e' \<Longrightarrow> 
    False"
  by (induction "encode' e" s\<^sub>e rule: prepend_to_top_frame.induct) auto

lemma prepend_to_jump [dest]: "prepend_to_top_frame (encode' e) s\<^sub>e = (\<Delta>, Jump\<^sub>e # \<C>) # s\<^sub>e' \<Longrightarrow> 
    False"
  by (induction "encode' e" s\<^sub>e rule: prepend_to_top_frame.induct) auto

lemma encode_stack_to_lookup [dest]: "stack_from_stack s\<^sub>g = (\<Delta>\<^sub>e, Lookup\<^sub>e x y # \<C>) # s\<^sub>e \<Longrightarrow> 
  \<exists>\<Delta>\<^sub>g e s\<^sub>g' \<C>'. s\<^sub>g = FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g' \<and> stack_from_stack s\<^sub>g' = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e \<and> 
    head_expr e = Var\<^sub>g x y \<and> \<C> = tl (encode' e) @ Apply\<^sub>e # \<C>'"
proof (induction s\<^sub>g rule: stack_from_stack.induct)
  case (2 \<Delta> e s\<^sub>g)
  then obtain \<C>' where "stack_from_stack s\<^sub>g = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e \<and> 
    encode' e @ Apply\<^sub>e # \<C>' = Lookup\<^sub>e x y # \<C>" by fastforce
  thus ?case by auto
qed auto

lemma encode_stack_to_pushcon [dest]: "stack_from_stack s\<^sub>g = (\<Delta>\<^sub>e, PushCon\<^sub>e n # \<C>) # s\<^sub>e \<Longrightarrow> 
  \<exists>\<Delta>\<^sub>g e s\<^sub>g' \<C>'. s\<^sub>g = FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g' \<and> stack_from_stack s\<^sub>g' = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e \<and> 
    head_expr e = Const\<^sub>g n \<and> \<C> = tl (encode' e) @ Apply\<^sub>e # \<C>'"
proof (induction s\<^sub>g rule: stack_from_stack.induct)
  case (2 \<Delta>\<^sub>s e s\<^sub>g)
  then obtain \<C>' where "stack_from_stack s\<^sub>g = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e \<and> 
    encode' e @ Apply\<^sub>e # \<C>' = PushCon\<^sub>e n # \<C>" by fastforce
  thus ?case by auto
qed auto

lemma encode_stack_to_pushlam [dest]: "stack_from_stack s\<^sub>g = (\<Delta>\<^sub>e, PushLam\<^sub>e \<C>' n # \<C>) # s\<^sub>e \<Longrightarrow> 
  \<exists>\<Delta>\<^sub>g e s\<^sub>g' t e' \<C>''. s\<^sub>g = FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g' \<and> stack_from_stack s\<^sub>g' = (\<Delta>\<^sub>e, \<C>'') # s\<^sub>e \<and> 
    head_expr e = Lam\<^sub>g t e' n \<and> \<C> = tl (encode' e) @ Apply\<^sub>e # \<C>'' \<and> \<C>' = encode e'"
proof (induction s\<^sub>g rule: stack_from_stack.induct)
  case (2 \<Delta>\<^sub>g e s\<^sub>g)
  then obtain \<C>'' where "stack_from_stack s\<^sub>g = (\<Delta>\<^sub>e, \<C>'') # s\<^sub>e \<and> 
    encode' e @ Apply\<^sub>e # \<C>'' = PushLam\<^sub>e \<C>' n # \<C>" by fastforce
  moreover then obtain t e' where "head_expr e = Lam\<^sub>g t e' n \<and> \<C>' = encode e' \<and> 
    \<C> = tl (encode' e) @ Apply\<^sub>e # \<C>''" by (metis encode_to_pushlam)
  ultimately show ?case by auto
qed auto

lemma encode_stack_to_apply [dest]: "stack_from_stack s = (\<Delta>\<^sub>e, Apply\<^sub>e # \<C>) # s\<^sub>e \<Longrightarrow> 
    \<exists>s\<^sub>g' c. s = FApp2\<^sub>g c # s\<^sub>g' \<and> stack_from_stack s\<^sub>g' = (\<Delta>\<^sub>e, \<C>) # s\<^sub>e"
  by (induction s rule: stack_from_stack.induct) auto

lemma encode_stack_to_pushenv [dest]: "stack_from_stack s = (\<Delta>\<^sub>e, PushEnv\<^sub>e # \<C>) # s\<^sub>e \<Longrightarrow> 
  \<exists>s\<^sub>g' \<Delta> e \<C>'. s = FLet\<^sub>g \<Delta> e # s\<^sub>g' \<and> \<C> = encode' e @ \<C>' \<and> 
    stack_from_stack s\<^sub>g' = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e"
  by (induction s rule: stack_from_stack.induct) auto

lemma encode_stack_to_return [dest]: "stack_from_stack s = (\<Delta>\<^sub>e, Return\<^sub>e # \<C>) # s\<^sub>e \<Longrightarrow> 
  \<exists>\<Delta>\<^sub>g s\<^sub>g'. s = FReturn\<^sub>g \<Delta>\<^sub>g # s\<^sub>g' \<and> \<Delta>\<^sub>e = map (map encode_closure) \<Delta>\<^sub>g \<and> s\<^sub>e = stack_from_stack s\<^sub>g' \<and> 
    \<C> = []"
  by (induction s rule: stack_from_stack.induct) auto

lemma encode_stack_to_jump [dest]: "stack_from_stack s = (\<Delta>\<^sub>e, Jump\<^sub>e # \<C>) # s\<^sub>e \<Longrightarrow> False"
  by (induction s rule: stack_from_stack.induct) auto

lemma encode_state_to_lookup [dest, consumes 1, case_names SE\<^sub>g SC\<^sub>g]: "
  encode_state \<Sigma>\<^sub>g = S\<^sub>e \<V> ((\<Delta>\<^sub>e, Lookup\<^sub>e x y # \<C>) # s\<^sub>e) \<Longrightarrow> 
    (\<And>s\<^sub>g \<Delta>\<^sub>g e \<C>'. head_expr e = Var\<^sub>g x y \<Longrightarrow> \<C> = tl (encode' e) @ \<C>' \<Longrightarrow> 
      stack_from_stack s\<^sub>g = ((\<Delta>\<^sub>e, \<C>') # s\<^sub>e) \<Longrightarrow> \<V> = vals_from_stack s\<^sub>g \<Longrightarrow> P (SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e)) \<Longrightarrow> 
    (\<And>s\<^sub>g c \<Delta>\<^sub>g e \<C>'. head_expr e = Var\<^sub>g x y \<Longrightarrow> 
      \<C> = tl (encode' e) @ Apply\<^sub>e # \<C>' \<Longrightarrow> stack_from_stack s\<^sub>g = ((\<Delta>\<^sub>e, \<C>') # s\<^sub>e) \<Longrightarrow> 
      \<V> = encode_closure c # vals_from_stack s\<^sub>g \<Longrightarrow> P (SC\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g) c)) \<Longrightarrow> P \<Sigma>\<^sub>g"
proof (induction \<Sigma>\<^sub>g)
  case (SE\<^sub>g s \<Delta> e)
  moreover then obtain \<C>' where "stack_from_stack s = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e \<and> 
    encode' e @ \<C>' = Lookup\<^sub>e x y # \<C>" by auto
  ultimately show ?case by auto
qed auto

lemma encode_state_to_pushcon [dest, consumes 1, case_names SE\<^sub>g SC\<^sub>g]: "
  encode_state \<Sigma>\<^sub>g = S\<^sub>e \<V> ((\<Delta>\<^sub>e, PushCon\<^sub>e n # \<C>) # s\<^sub>e) \<Longrightarrow> 
    (\<And>s\<^sub>g \<Delta>\<^sub>g e \<C>'. head_expr e = Const\<^sub>g n \<Longrightarrow> \<C> = tl (encode' e) @ \<C>' \<Longrightarrow> 
      stack_from_stack s\<^sub>g = ((\<Delta>\<^sub>e, \<C>') # s\<^sub>e) \<Longrightarrow> \<V> = vals_from_stack s\<^sub>g \<Longrightarrow> P (SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e)) \<Longrightarrow> 
    (\<And>s\<^sub>g c \<Delta>\<^sub>g e \<C>'. head_expr e = Const\<^sub>g n \<Longrightarrow> \<C> = tl (encode' e) @ Apply\<^sub>e # \<C>' \<Longrightarrow> 
      stack_from_stack s\<^sub>g = ((\<Delta>\<^sub>e, \<C>') # s\<^sub>e) \<Longrightarrow> \<V> = encode_closure c # vals_from_stack s\<^sub>g \<Longrightarrow> 
      P (SC\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g) c)) \<Longrightarrow> P \<Sigma>\<^sub>g"
proof (induction \<Sigma>\<^sub>g)
  case (SE\<^sub>g s \<Delta> e)
  moreover then obtain \<C>' where "stack_from_stack s = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e \<and> 
    encode' e @ \<C>' = PushCon\<^sub>e n # \<C>" by auto
  ultimately show ?case by auto
qed auto

lemma encode_state_to_pushlam [dest, consumes 1, case_names SE\<^sub>g SC\<^sub>g]: "
  encode_state \<Sigma>\<^sub>g = S\<^sub>e \<V> ((\<Delta>\<^sub>e, PushLam\<^sub>e \<C>' n # \<C>) # s\<^sub>e) \<Longrightarrow> 
    (\<And>s\<^sub>g \<Delta>\<^sub>g e tt e' \<C>''. \<Sigma>\<^sub>g = SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e \<Longrightarrow> head_expr e = Lam\<^sub>g tt e' n \<Longrightarrow> 
      \<C> = tl (encode' e) @ \<C>'' \<Longrightarrow> \<C>' = encode e' \<Longrightarrow> 
      \<V> = vals_from_stack s\<^sub>g \<Longrightarrow> stack_from_stack s\<^sub>g = (\<Delta>\<^sub>e, \<C>'') # s\<^sub>e \<Longrightarrow> P) \<Longrightarrow> 
    (\<And>s\<^sub>g c \<Delta>\<^sub>g e tt e' \<C>''. \<Sigma>\<^sub>g = SC\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g) c \<Longrightarrow> head_expr e = Lam\<^sub>g tt e' n \<Longrightarrow> 
      \<C> = tl (encode' e) @ Apply\<^sub>e # \<C>'' \<Longrightarrow> \<C>' = encode e' \<Longrightarrow> 
      \<V> = encode_closure c # vals_from_stack s\<^sub>g \<Longrightarrow> stack_from_stack s\<^sub>g = (\<Delta>\<^sub>e, \<C>'') # s\<^sub>e \<Longrightarrow> P) \<Longrightarrow> 
    P"
proof (induction \<Sigma>\<^sub>g)
  case (SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e)
  moreover then obtain \<C>'' where "stack_from_stack s\<^sub>g = (\<Delta>\<^sub>e, \<C>'') # s\<^sub>e \<and> 
    encode' e @ \<C>'' = PushLam\<^sub>e \<C>' n # \<C>" by auto
  moreover then obtain tt e' where "head_expr e = Lam\<^sub>g tt e' n \<and> \<C>' = encode e' \<and> 
    \<C> = tl (encode' e) @ \<C>''" by (metis encode_to_pushlam)
  ultimately show ?case by auto
qed auto

lemma encode_state_to_apply [dest]: "
  encode_state \<Sigma>\<^sub>g = S\<^sub>e (v # Lam\<^sub>e \<Delta>\<^sub>e' \<C>' n # \<V>) ((\<Delta>\<^sub>e, Apply\<^sub>e # \<C>) # s\<^sub>e) \<Longrightarrow>
    \<exists>s\<^sub>g c c'. \<Sigma>\<^sub>g = SC\<^sub>g (FApp2\<^sub>g c' # s\<^sub>g) c \<and> stack_from_stack s\<^sub>g = ((\<Delta>\<^sub>e, \<C>) # s\<^sub>e) \<and> 
      v = encode_closure c \<and> Lam\<^sub>e \<Delta>\<^sub>e' \<C>' n = encode_closure c' \<and> \<V> = vals_from_stack s\<^sub>g"
  by (induction \<Sigma>\<^sub>g) auto

lemma encode_state_to_pushenv [dest]: "encode_state \<Sigma>\<^sub>g = S\<^sub>e (v # \<V>) ((\<Delta>\<^sub>e, PushEnv\<^sub>e # \<C>) # s\<^sub>e) \<Longrightarrow> 
  \<exists>c s\<^sub>g. \<Sigma>\<^sub>g = SC\<^sub>g s\<^sub>g c \<and> v = encode_closure c \<and> \<V> = vals_from_stack s\<^sub>g \<and> 
    stack_from_stack s\<^sub>g = (\<Delta>\<^sub>e, PushEnv\<^sub>e # \<C>) # s\<^sub>e"
  by (induction \<Sigma>\<^sub>g) auto

lemma encode_state_to_return [dest]: "encode_state \<Sigma>\<^sub>g = S\<^sub>e \<V> ((\<Delta>\<^sub>e, Return\<^sub>e # \<C>) # s\<^sub>e) \<Longrightarrow> 
  \<exists>\<Delta>\<^sub>g s c. \<Sigma>\<^sub>g = SC\<^sub>g (FReturn\<^sub>g \<Delta>\<^sub>g # s) c \<and> s\<^sub>e = stack_from_stack s \<and>
    \<Delta>\<^sub>e = map (map encode_closure) \<Delta>\<^sub>g \<and> \<V> = encode_closure c # vals_from_stack s \<and> \<C> = []"
  by (induction \<Sigma>\<^sub>g) auto

lemma encode_state_to_jump [dest]: "encode_state \<Sigma>\<^sub>g = S\<^sub>e \<V> ((\<Delta>\<^sub>e, Jump\<^sub>e # \<C>) # s\<^sub>e) \<Longrightarrow> False"
  by (induction \<Sigma>\<^sub>g) auto

text \<open>And now, we can finally prove completeness.\<close>

theorem complete\<^sub>e [simp]: "encode_state \<Sigma>\<^sub>g \<leadsto>\<^sub>e \<Sigma>\<^sub>t' \<Longrightarrow> \<Sigma>\<^sub>g :\<^sub>g t \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>g'. iter (\<leadsto>\<^sub>g) \<Sigma>\<^sub>g \<Sigma>\<^sub>g' \<and> \<Sigma>\<^sub>t' = encode_state \<Sigma>\<^sub>g'"
proof (induction "encode_state \<Sigma>\<^sub>g" \<Sigma>\<^sub>t' rule: eval\<^sub>e.induct)
  case (ev\<^sub>e_lookup \<Delta>\<^sub>e x vs y v \<V> \<C> s\<^sub>e)
  hence X: "encode_state \<Sigma>\<^sub>g = S\<^sub>e \<V> ((\<Delta>\<^sub>e, Lookup\<^sub>e x y # \<C>) # s\<^sub>e)" by simp
  from X ev\<^sub>e_lookup show ?case
  proof (induction rule: encode_state_to_lookup)
    case (SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e \<C>')
    hence "latest_environment\<^sub>g s\<^sub>g = Some \<Delta>\<^sub>g \<and> let_floated\<^sub>g e \<and> (let_free\<^sub>g e \<or> return_headed\<^sub>g s\<^sub>g)"
      by blast
    hence X: "iter (\<leadsto>\<^sub>g) (SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e) (SE\<^sub>g (tail_expr \<Delta>\<^sub>g e @ s\<^sub>g) \<Delta>\<^sub>g (head_expr e))" 
      by simp
    from SE\<^sub>g obtain cs c where C: "lookup \<Delta>\<^sub>g x = Some cs \<and> lookup cs y = Some c \<and> 
      encode_closure c = v" by fastforce
    with X SE\<^sub>g have "iter (\<leadsto>\<^sub>g) (SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e) (SC\<^sub>g (tail_expr \<Delta>\<^sub>g e @ s\<^sub>g) c)" by simp
    with SE\<^sub>g C show ?case by auto
  next
    case (SC\<^sub>g s\<^sub>g c \<Delta>\<^sub>g e \<C>')
    hence "latest_environment\<^sub>g s\<^sub>g = Some \<Delta>\<^sub>g \<and> let_floated\<^sub>g e \<and> let_free\<^sub>g e" by blast
    hence I: "iter (\<leadsto>\<^sub>g) (SE\<^sub>g (FApp2\<^sub>g c # s\<^sub>g) \<Delta>\<^sub>g e) 
      (SE\<^sub>g (tail_expr \<Delta>\<^sub>g e @ FApp2\<^sub>g c # s\<^sub>g) \<Delta>\<^sub>g (head_expr e))" by simp
    have "SC\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g) c \<leadsto>\<^sub>g SE\<^sub>g (FApp2\<^sub>g c # s\<^sub>g) \<Delta>\<^sub>g e" by simp
    with SC\<^sub>g I have X: "iter (\<leadsto>\<^sub>g) (SC\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g) c) 
      (SE\<^sub>g (tail_expr \<Delta>\<^sub>g e @ FApp2\<^sub>g c # s\<^sub>g) \<Delta>\<^sub>g (Var\<^sub>g x y))" by (metis iter_step)
    from SC\<^sub>g obtain cs c' where C: "lookup \<Delta>\<^sub>g x = Some cs \<and> lookup cs y = Some c' \<and> 
      encode_closure c' = v" by fastforce
    with X have "iter (\<leadsto>\<^sub>g) (SC\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g) c) (SC\<^sub>g (tail_expr \<Delta>\<^sub>g e @ FApp2\<^sub>g c # s\<^sub>g) c')" 
      by simp
    with SC\<^sub>g C show ?case by auto
  qed
next
  case (ev\<^sub>e_pushcon \<V> \<Delta>\<^sub>e n \<C> s\<^sub>e)
  hence X: "encode_state \<Sigma>\<^sub>g = S\<^sub>e \<V> ((\<Delta>\<^sub>e, PushCon\<^sub>e n # \<C>) # s\<^sub>e)" by simp
  from X ev\<^sub>e_pushcon(2) show ?case
  proof (induction rule: encode_state_to_pushcon)
    case (SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e \<C>')
    hence "latest_environment\<^sub>g s\<^sub>g = Some \<Delta>\<^sub>g \<and> let_floated\<^sub>g e \<and> (let_free\<^sub>g e \<or> return_headed\<^sub>g s\<^sub>g)"
      by blast
    hence "iter (\<leadsto>\<^sub>g) (SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e) (SE\<^sub>g (tail_expr \<Delta>\<^sub>g e @ s\<^sub>g) \<Delta>\<^sub>g (head_expr e))" by simp
    with SE\<^sub>g have "iter (\<leadsto>\<^sub>g) (SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e) (SC\<^sub>g (tail_expr \<Delta>\<^sub>g e @ s\<^sub>g) (Num\<^sub>g n))" by simp
    with SE\<^sub>g show ?case by auto
  next
    case (SC\<^sub>g s\<^sub>g c \<Delta>\<^sub>g e \<C>')
    hence "latest_environment\<^sub>g s\<^sub>g = Some \<Delta>\<^sub>g \<and> let_floated\<^sub>g e \<and> let_free\<^sub>g e" by blast
    hence X: "iter (\<leadsto>\<^sub>g) (SE\<^sub>g (FApp2\<^sub>g c # s\<^sub>g) \<Delta>\<^sub>g e) 
      (SE\<^sub>g (tail_expr \<Delta>\<^sub>g e @ FApp2\<^sub>g c # s\<^sub>g) \<Delta>\<^sub>g (head_expr e))" by simp
    have Y: "SC\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g) c \<leadsto>\<^sub>g SE\<^sub>g (FApp2\<^sub>g c # s\<^sub>g) \<Delta>\<^sub>g e" by simp
    have "SE\<^sub>g (tail_expr \<Delta>\<^sub>g e @ FApp2\<^sub>g c # s\<^sub>g) \<Delta>\<^sub>g (Const\<^sub>g n) \<leadsto>\<^sub>g 
      SC\<^sub>g (tail_expr \<Delta>\<^sub>g e @ FApp2\<^sub>g c # s\<^sub>g) (Num\<^sub>g n)" by simp
    with SC\<^sub>g X Y have "iter (\<leadsto>\<^sub>g) (SC\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g) c)
      (SC\<^sub>g (tail_expr \<Delta>\<^sub>g e @ FApp2\<^sub>g c # s\<^sub>g) (Num\<^sub>g n))" 
        by (metis iter_step iter_step_after)
    with SC\<^sub>g show ?case by auto
  qed
next
  case (ev\<^sub>e_pushlam \<V> \<Delta>\<^sub>e \<C>' n \<C> s\<^sub>e)
  hence X: "encode_state \<Sigma>\<^sub>g = S\<^sub>e \<V> ((\<Delta>\<^sub>e, PushLam\<^sub>e \<C>' n # \<C>) # s\<^sub>e)" by simp
  from X ev\<^sub>e_pushlam(2) show ?case
  proof (induction rule: encode_state_to_pushlam)
    case (SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e tt e' \<C>'')
    hence "latest_environment\<^sub>g s\<^sub>g = Some \<Delta>\<^sub>g \<and> let_floated\<^sub>g e \<and> (let_free\<^sub>g e \<or> return_headed\<^sub>g s\<^sub>g)"
      by blast
    hence X: "iter (\<leadsto>\<^sub>g) (SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e) (SE\<^sub>g (tail_expr \<Delta>\<^sub>g e @ s\<^sub>g) \<Delta>\<^sub>g (head_expr e))" by simp
    have "SE\<^sub>g (tail_expr \<Delta>\<^sub>g e @ s\<^sub>g) \<Delta>\<^sub>g (Lam\<^sub>g tt e' n) \<leadsto>\<^sub>g 
      SC\<^sub>g (tail_expr \<Delta>\<^sub>g e @ s\<^sub>g) (Fun\<^sub>g tt \<Delta>\<^sub>g e' n)" by simp
    with SE\<^sub>g X have E: "iter (\<leadsto>\<^sub>g) (SE\<^sub>g s\<^sub>g \<Delta>\<^sub>g e) (SC\<^sub>g (tail_expr \<Delta>\<^sub>g e @ s\<^sub>g) (Fun\<^sub>g tt \<Delta>\<^sub>g e' n))"
      by (metis iter_step_after)
    from SE\<^sub>g have "\<Delta>\<^sub>e = map (map encode_closure) \<Delta>\<^sub>g" by fastforce
    with SE\<^sub>g E show ?case by auto
  next
    case (SC\<^sub>g s\<^sub>g c \<Delta>\<^sub>g e tt e' \<C>'')
    hence "latest_environment\<^sub>g s\<^sub>g = Some \<Delta>\<^sub>g \<and> let_floated\<^sub>g e \<and> let_free\<^sub>g e" by blast
    hence X: "iter (\<leadsto>\<^sub>g) (SE\<^sub>g (FApp2\<^sub>g c # s\<^sub>g) \<Delta>\<^sub>g e) 
      (SE\<^sub>g (tail_expr \<Delta>\<^sub>g e @ FApp2\<^sub>g c # s\<^sub>g) \<Delta>\<^sub>g (head_expr e))" by simp
    have Y: "SC\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g) c \<leadsto>\<^sub>g SE\<^sub>g (FApp2\<^sub>g c # s\<^sub>g) \<Delta>\<^sub>g e" by simp
    have "SE\<^sub>g (tail_expr \<Delta>\<^sub>g e @ FApp2\<^sub>g c # s\<^sub>g) \<Delta>\<^sub>g (Lam\<^sub>g tt e' n) \<leadsto>\<^sub>g 
      SC\<^sub>g (tail_expr \<Delta>\<^sub>g e @ FApp2\<^sub>g c # s\<^sub>g) (Fun\<^sub>g tt \<Delta>\<^sub>g e' n)" by simp
    with SC\<^sub>g X Y have E: "iter (\<leadsto>\<^sub>g) (SC\<^sub>g (FApp1\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g) c) 
      (SC\<^sub>g (tail_expr \<Delta>\<^sub>g e @ FApp2\<^sub>g c # s\<^sub>g) (Fun\<^sub>g tt \<Delta>\<^sub>g e' n))" 
        by (metis iter_step iter_step_after)
    from SC\<^sub>g have "\<Delta>\<^sub>e = map (map encode_closure) \<Delta>\<^sub>g" by fastforce
    with SC\<^sub>g E show ?case by auto
  qed
next
  case (ev\<^sub>e_apply v \<Delta>\<^sub>e' \<C>' n \<V> \<Delta>\<^sub>e \<C> s\<^sub>e)
  hence "encode_state \<Sigma>\<^sub>g = S\<^sub>e (v # Lam\<^sub>e \<Delta>\<^sub>e' \<C>' n # \<V>) ((\<Delta>\<^sub>e, Apply\<^sub>e # \<C>) # s\<^sub>e)" by simp
  then obtain s\<^sub>g c c' where "\<Sigma>\<^sub>g = SC\<^sub>g (FApp2\<^sub>g c' # s\<^sub>g) c \<and> 
    stack_from_stack s\<^sub>g = ((\<Delta>\<^sub>e, \<C>) # s\<^sub>e) \<and> v = encode_closure c \<and> 
    Lam\<^sub>e \<Delta>\<^sub>e' \<C>' n = encode_closure c' \<and> \<V> = vals_from_stack s\<^sub>g" 
      by auto
  moreover then obtain t \<Delta>\<^sub>g e where "c' = Fun\<^sub>g t \<Delta>\<^sub>g e n \<and> \<Delta>\<^sub>e' = map (map encode_closure) \<Delta>\<^sub>g \<and> 
    \<C>' = encode e" by auto
  moreover have "SC\<^sub>g (FApp2\<^sub>g (Fun\<^sub>g t \<Delta>\<^sub>g e n) # s\<^sub>g) c \<leadsto>\<^sub>g SE\<^sub>g (FReturn\<^sub>g ([c] # \<Delta>\<^sub>g) # s\<^sub>g) ([c] # \<Delta>\<^sub>g) e" 
    by simp
  moreover hence "iter (\<leadsto>\<^sub>g) (SC\<^sub>g (FApp2\<^sub>g (Fun\<^sub>g t \<Delta>\<^sub>g e n) # s\<^sub>g) c) 
    (SE\<^sub>g (FReturn\<^sub>g ([c] # \<Delta>\<^sub>g) # s\<^sub>g) ([c] # \<Delta>\<^sub>g) e)" by (metis iter_one)
  ultimately show ?case by (auto simp add: encode_def)
next
  case (ev\<^sub>e_pushenv v \<V> \<Delta>\<^sub>e \<C> s\<^sub>e)
  hence "encode_state \<Sigma>\<^sub>g = S\<^sub>e (v # \<V>) ((\<Delta>\<^sub>e, PushEnv\<^sub>e # \<C>) # s\<^sub>e)" by simp
  then obtain c s\<^sub>g where S: "\<Sigma>\<^sub>g = SC\<^sub>g s\<^sub>g c \<and> v = encode_closure c \<and> \<V> = vals_from_stack s\<^sub>g \<and> 
    stack_from_stack s\<^sub>g = (\<Delta>\<^sub>e, PushEnv\<^sub>e # \<C>) # s\<^sub>e" by auto
  then obtain s\<^sub>g' \<Delta>\<^sub>g e \<C>' where S': "s\<^sub>g = FLet\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g' \<and> \<C> = encode' e @ \<C>' \<and> 
    stack_from_stack s\<^sub>g' = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e" by auto
  from ev\<^sub>e_pushenv S S' have "return_headed\<^sub>g s\<^sub>g' \<and> latest_environment\<^sub>g s\<^sub>g' = Some \<Delta>\<^sub>g" by blast
  then obtain s\<^sub>g'' where S'': "s\<^sub>g' = FReturn\<^sub>g \<Delta>\<^sub>g # s\<^sub>g''" by auto
  hence "SC\<^sub>g (FLet\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g') c \<leadsto>\<^sub>g SE\<^sub>g (FReturn\<^sub>g (snoc_fst c \<Delta>\<^sub>g) # s\<^sub>g'') (snoc_fst c \<Delta>\<^sub>g) e" 
    by auto
  hence "iter (\<leadsto>\<^sub>g) (SC\<^sub>g (FLet\<^sub>g \<Delta>\<^sub>g e # s\<^sub>g') c) 
    (SE\<^sub>g (FReturn\<^sub>g (snoc_fst c \<Delta>\<^sub>g) # s\<^sub>g'') (snoc_fst c \<Delta>\<^sub>g) e)" by (metis iter_one)
  with S S' S'' show ?case by auto
next
  case (ev\<^sub>e_return \<V> \<Delta>\<^sub>e \<C> s\<^sub>e)
  hence "encode_state \<Sigma>\<^sub>g = S\<^sub>e \<V> ((\<Delta>\<^sub>e, Return\<^sub>e # \<C>) # s\<^sub>e)" by simp
  then obtain \<Delta>\<^sub>g s\<^sub>g c where S: "\<Sigma>\<^sub>g = SC\<^sub>g (FReturn\<^sub>g \<Delta>\<^sub>g # s\<^sub>g) c \<and> s\<^sub>e = stack_from_stack s\<^sub>g \<and>
    \<Delta>\<^sub>e = map (map encode_closure) \<Delta>\<^sub>g \<and> \<V> = encode_closure c # vals_from_stack s\<^sub>g" by auto
  have "SC\<^sub>g (FReturn\<^sub>g \<Delta>\<^sub>g # s\<^sub>g) c \<leadsto>\<^sub>g SC\<^sub>g s\<^sub>g c" by simp
  hence "iter (\<leadsto>\<^sub>g) (SC\<^sub>g (FReturn\<^sub>g \<Delta>\<^sub>g # s\<^sub>g) c) (SC\<^sub>g s\<^sub>g c)" by (metis iter_one)
  with S show ?case by auto
next
  case (ev\<^sub>e_jump v \<Delta>\<^sub>e' \<C>' n \<V> \<Delta>\<^sub>e \<C> s\<^sub>e)
  hence "encode_state \<Sigma>\<^sub>g = S\<^sub>e (v # Lam\<^sub>e \<Delta>\<^sub>e' \<C>' n # \<V>) ((\<Delta>\<^sub>e, Jump\<^sub>e # \<C>) # s\<^sub>e)" by simp
  thus ?case by auto
qed

end