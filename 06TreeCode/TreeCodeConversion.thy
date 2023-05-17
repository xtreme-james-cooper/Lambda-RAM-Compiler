theory TreeCodeConversion
  imports TreeCode "../05Closure/Closure" "../00Utils/Iteration"
begin

subsection \<open>Compilation to Tree-Code\<close>

text \<open>This is our first real compilation phase; typechecking and name-removal were fundamentally 
just modifying an underlying expression, but here we genuinely reshape our expressions into code. 
The first few steps are simple: encoding an expression means shuffling it into a postfix form, and 
tree-code closures-values are just encoded stack closure-values.\<close>

primrec encode :: "expr\<^sub>d \<Rightarrow> code\<^sub>e list" where
  "encode (Var\<^sub>d x) = [Lookup\<^sub>e x]"
| "encode (Const\<^sub>d n) = [PushCon\<^sub>e n]"
| "encode (Lam\<^sub>d t e) = [PushLam\<^sub>e (encode e)]"
| "encode (App\<^sub>d e\<^sub>1 e\<^sub>2) = encode e\<^sub>1 @ encode e\<^sub>2 @ [Apply\<^sub>e]"

primrec encode_closure :: "closure\<^sub>c \<Rightarrow> closure\<^sub>e" where
  "encode_closure (Const\<^sub>c n) = Const\<^sub>e n"
| "encode_closure (Lam\<^sub>c t \<Delta> e) = Lam\<^sub>e (map encode_closure \<Delta>) (encode e)"

lemma tl_encode [simp]: "tl (encode e @ \<C>) = tl (encode e) @ \<C>"
  by (induction e arbitrary: \<C>) simp_all

text \<open>It is the callstack where things get complicated: we have to divide the stack into a 
callstack and a value stack. The value stack consists of the returned closure-values in \<open>FApp2\<^sub>c\<close> 
frames:\<close>

fun vals_from_stack :: "frame\<^sub>c list \<Rightarrow> closure\<^sub>e list" where
  "vals_from_stack [] = []"
| "vals_from_stack (FApp1\<^sub>c \<Delta> e # s\<^sub>c) = vals_from_stack s\<^sub>c"
| "vals_from_stack (FApp2\<^sub>c c # s\<^sub>c) = encode_closure c # vals_from_stack s\<^sub>c"
| "vals_from_stack (FReturn\<^sub>c \<Delta> # s\<^sub>c) = vals_from_stack s\<^sub>c"

text \<open>The callstack requires some more careful work. Each frame represents a place where we are part
of the way through the block of code associated with a particular expression; fortunately, we can 
reconstruct what the code must have been to get us to this state, and then prepend it into the most
recent stack frame. The \<open>FReturn\<^sub>c\<close> frames and their environments that we have been so diligently 
recording for the last two stages finally prove their worth, as well: they show us where (and with 
what environment) callstack frames begin.\<close>

fun prepend_to_top_frame :: "code\<^sub>e list \<Rightarrow> frame\<^sub>e list \<Rightarrow> frame\<^sub>e list" where
  "prepend_to_top_frame \<C> [] = []"
| "prepend_to_top_frame \<C> ((\<Delta>, \<C>') # s\<^sub>e) = (\<Delta>, \<C> @ \<C>') # s\<^sub>e"

fun stack_from_stack :: "frame\<^sub>c list \<Rightarrow> frame\<^sub>e list" where
  "stack_from_stack [] = []"
| "stack_from_stack (FApp1\<^sub>c \<Delta>' e # s\<^sub>c) = 
    prepend_to_top_frame (encode e @ [Apply\<^sub>e]) (stack_from_stack s\<^sub>c)"
| "stack_from_stack (FApp2\<^sub>c c # s\<^sub>c) = prepend_to_top_frame [Apply\<^sub>e] (stack_from_stack s\<^sub>c)"
| "stack_from_stack (FReturn\<^sub>c \<Delta> # s\<^sub>c) = (map encode_closure \<Delta>, []) # stack_from_stack s\<^sub>c"

lemma prepend_nil [simp]: "prepend_to_top_frame [] s\<^sub>e = s\<^sub>e"
  by (induction "[] :: code\<^sub>e list" s\<^sub>e rule: prepend_to_top_frame.induct) simp_all

lemma prepend_append [simp]: "prepend_to_top_frame (\<C> @ \<C>') s\<^sub>e = 
    prepend_to_top_frame \<C> (prepend_to_top_frame \<C>' s\<^sub>e)"
  by (induction "\<C> @ \<C>'" s\<^sub>e rule: prepend_to_top_frame.induct) simp_all

text \<open>We once again collapse the distinction between our two states, evaluating and returning; an 
evaluation state is simply one where a little more code is there to be executed in the topmost 
frame.\<close>

primrec encode_state :: "state\<^sub>c \<Rightarrow> state\<^sub>e" where
  "encode_state (SE\<^sub>c s\<^sub>c \<Delta> e) = 
    S\<^sub>e (vals_from_stack s\<^sub>c) (prepend_to_top_frame (encode e) (stack_from_stack s\<^sub>c))"
| "encode_state (SC\<^sub>c s\<^sub>c c) = S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>c) (stack_from_stack s\<^sub>c)"

text \<open>Because the conversion functions run forwards, we can once again prove correctness easily.
(Because we have no typing judgement for tree code, we do not - cannot - prove type safety.) 
We again have to use \<open>iter\<close> in our statement of the theorem, because the frame-adjustment evaluation
steps (\<open>ret\<^sub>c_app1\<close> and \<open>ret\<^sub>c_app2\<close>) are not matched by any steps in the tree-code evaluation.\<close>

lemma lookup_latest [dest]: "latest_environment s\<^sub>c = Some \<Delta> \<Longrightarrow> 
    \<exists>\<C> s\<^sub>e. stack_from_stack s\<^sub>c = (map encode_closure \<Delta>, \<C>) # s\<^sub>e"
  by (induction s\<^sub>c rule: stack_from_stack.induct) auto

theorem correct\<^sub>e [simp]: "\<Sigma> \<leadsto>\<^sub>c \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow> iter (\<leadsto>\<^sub>e) (encode_state \<Sigma>) (encode_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>c.induct)
  case (ev\<^sub>c_var \<Delta> x c s\<^sub>c)
  then obtain t' \<Gamma> where "(s\<^sub>c :\<^sub>c t' \<rightarrow> t) \<and> (\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> latest_environment s\<^sub>c = Some \<Delta> \<and> 
    lookup \<Gamma> x = Some t'" by fastforce
  then obtain \<C> s\<^sub>e where S: "stack_from_stack s\<^sub>c = (map encode_closure \<Delta>, \<C>) # s\<^sub>e" 
    by auto
  with ev\<^sub>c_var have "S\<^sub>e (vals_from_stack s\<^sub>c) ((map encode_closure \<Delta>, Lookup\<^sub>e x # \<C>) # s\<^sub>e) \<leadsto>\<^sub>e 
    S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>c) ((map encode_closure \<Delta>, \<C>) # s\<^sub>e)" by simp
  hence "iter (\<leadsto>\<^sub>e) (S\<^sub>e (vals_from_stack s\<^sub>c) ((map encode_closure \<Delta>, Lookup\<^sub>e x # \<C>) # s\<^sub>e))
    (S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>c) ((map encode_closure \<Delta>, \<C>) # s\<^sub>e))" 
      by (metis iter_one)
    with S show ?case by simp
next
  case (ev\<^sub>c_con s\<^sub>c \<Delta> n)
  then obtain \<Gamma> where "(s\<^sub>c :\<^sub>c Num \<rightarrow> t) \<and> (\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> latest_environment s\<^sub>c = Some \<Delta>" 
    by fastforce
  then obtain \<C> s\<^sub>e where S: "stack_from_stack s\<^sub>c = (map encode_closure \<Delta>, \<C>) # s\<^sub>e" 
    by auto
  have "S\<^sub>e (vals_from_stack s\<^sub>c) ((map encode_closure \<Delta>, PushCon\<^sub>e n # \<C>) # s\<^sub>e) \<leadsto>\<^sub>e 
    S\<^sub>e (Const\<^sub>e n # vals_from_stack s\<^sub>c) ((map encode_closure \<Delta>, \<C>) # s\<^sub>e)" by simp
  hence "iter (\<leadsto>\<^sub>e) (S\<^sub>e (vals_from_stack s\<^sub>c) ((map encode_closure \<Delta>, PushCon\<^sub>e n # \<C>) # s\<^sub>e)) 
    (S\<^sub>e (Const\<^sub>e n # vals_from_stack s\<^sub>c) ((map encode_closure \<Delta>, \<C>) # s\<^sub>e))" by (metis iter_one)
  with S show ?case by simp
next
  case (ev\<^sub>c_lam s\<^sub>c \<Delta> tt e)
  then obtain t' \<Gamma> where "(s\<^sub>c :\<^sub>c t' \<rightarrow> t) \<and> (\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> latest_environment s\<^sub>c = Some \<Delta> \<and>
    (\<Gamma> \<turnstile>\<^sub>d Lam\<^sub>d tt e : t')" by fastforce
  then obtain \<C> s\<^sub>e where S: "stack_from_stack s\<^sub>c = (map encode_closure \<Delta>, \<C>) # s\<^sub>e" 
    by auto
  hence "S\<^sub>e (vals_from_stack s\<^sub>c) ((map encode_closure \<Delta>, PushLam\<^sub>e (encode e) # \<C>) # s\<^sub>e) \<leadsto>\<^sub>e 
    S\<^sub>e (Lam\<^sub>e (map encode_closure \<Delta>) (encode e) # vals_from_stack s\<^sub>c) 
      ((map encode_closure \<Delta>, \<C>) # s\<^sub>e)" by (metis ev\<^sub>e_pushlam)
  hence "iter (\<leadsto>\<^sub>e) (S\<^sub>e (vals_from_stack s\<^sub>c) 
    ((map encode_closure \<Delta>, PushLam\<^sub>e (encode e) # \<C>) # s\<^sub>e)) 
      (S\<^sub>e (Lam\<^sub>e (map encode_closure \<Delta>) (encode e) # vals_from_stack s\<^sub>c)
        ((map encode_closure \<Delta>, \<C>) # s\<^sub>e))" by (metis iter_one)
  with S show ?case by (simp add: encode_def)
next
  case (ret\<^sub>c_app2 t\<^sub>1 \<Delta> e\<^sub>1 s\<^sub>c c\<^sub>2)
  then obtain \<Gamma> t\<^sub>2 \<Delta>' where "(\<Delta> :\<^sub>c\<^sub>l\<^sub>s \<Gamma>) \<and> (insert_at 0 t\<^sub>1 \<Gamma> \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2) \<and> (s\<^sub>c :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> 
    latest_environment s\<^sub>c = Some \<Delta>' \<and> (c\<^sub>2 :\<^sub>c\<^sub>l t\<^sub>1)" by blast
  then obtain \<C> s\<^sub>e where S: "stack_from_stack s\<^sub>c = (map encode_closure \<Delta>', \<C>) # s\<^sub>e" 
    by auto
  hence "S\<^sub>e (encode_closure c\<^sub>2 # Lam\<^sub>e (map encode_closure \<Delta>) (encode e\<^sub>1) # 
    vals_from_stack s\<^sub>c) ((map encode_closure \<Delta>', Apply\<^sub>e # \<C>) # s\<^sub>e) \<leadsto>\<^sub>e
      S\<^sub>e (vals_from_stack s\<^sub>c) ((encode_closure c\<^sub>2 # map encode_closure \<Delta>, 
        encode e\<^sub>1) # stack_from_stack s\<^sub>c)" by (metis ev\<^sub>e_apply)
  hence "iter (\<leadsto>\<^sub>e)
    (S\<^sub>e (encode_closure c\<^sub>2 # Lam\<^sub>e (map encode_closure \<Delta>) (encode e\<^sub>1) # 
      vals_from_stack s\<^sub>c) ((map encode_closure \<Delta>', Apply\<^sub>e # \<C>) # s\<^sub>e))
        (S\<^sub>e (vals_from_stack s\<^sub>c) ((encode_closure c\<^sub>2 # map encode_closure \<Delta>, 
          encode e\<^sub>1) # stack_from_stack s\<^sub>c))"
    by (metis iter_one)
  with S show ?case by (simp add: encode_def)
next
  case (ret\<^sub>c_ret \<Delta> s\<^sub>c c)
  have "S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>c) 
    ((map encode_closure \<Delta>, []) # stack_from_stack s\<^sub>c) \<leadsto>\<^sub>e
      S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>c) (stack_from_stack s\<^sub>c)" by simp
  hence "iter (\<leadsto>\<^sub>e) 
    (S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>c) ((map encode_closure \<Delta>, []) # stack_from_stack s\<^sub>c))
      (S\<^sub>e (encode_closure c # vals_from_stack s\<^sub>c) (stack_from_stack s\<^sub>c))" by (metis iter_one)
  thus ?case by simp
qed fastforce+

lemma correct\<^sub>e_iter [simp]: "iter (\<leadsto>\<^sub>c) \<Sigma> \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow>
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

primrec head_expr :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d" where
  "head_expr (Var\<^sub>d x) = Var\<^sub>d x"
| "head_expr (Const\<^sub>d n) = Const\<^sub>d n"
| "head_expr (Lam\<^sub>d t e) = Lam\<^sub>d t e"
| "head_expr (App\<^sub>d e\<^sub>1 e\<^sub>2) = head_expr e\<^sub>1"

primrec tail_expr :: "closure\<^sub>c list \<Rightarrow> expr\<^sub>d \<Rightarrow> frame\<^sub>c list" where
  "tail_expr \<Delta> (Var\<^sub>d x) = []"
| "tail_expr \<Delta> (Const\<^sub>d n) = []"
| "tail_expr \<Delta> (Lam\<^sub>d t e) = []"
| "tail_expr \<Delta> (App\<^sub>d e\<^sub>1 e\<^sub>2) = tail_expr \<Delta> e\<^sub>1 @ [FApp1\<^sub>c \<Delta> e\<^sub>2]"

lemma vals_from_tail_expr [simp]: "vals_from_stack (tail_expr \<Delta> e @ s\<^sub>c) = vals_from_stack s\<^sub>c"
  by (induction e arbitrary: s\<^sub>c) simp_all

lemma stack_from_tail_expr [simp]: "stack_from_stack (tail_expr \<Delta> e @ s\<^sub>c) = 
    prepend_to_top_frame (tl (encode e)) (stack_from_stack s\<^sub>c)"
  by (induction e arbitrary: s\<^sub>c) simp_all

lemma evaluate_to_head_tail [simp]: "
  iter (\<leadsto>\<^sub>c) (SE\<^sub>c s \<Delta> e) (SE\<^sub>c (tail_expr \<Delta> e @ s) \<Delta> (head_expr e))"
proof (induction e arbitrary: s)
  case (App\<^sub>d e\<^sub>1 e\<^sub>2)
  moreover have "SE\<^sub>c s \<Delta> (App\<^sub>d e\<^sub>1 e\<^sub>2) \<leadsto>\<^sub>c SE\<^sub>c (FApp1\<^sub>c \<Delta> e\<^sub>2 # s) \<Delta> e\<^sub>1" by simp
  ultimately have "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s \<Delta> (App\<^sub>d e\<^sub>1 e\<^sub>2))
    (SE\<^sub>c (tail_expr \<Delta> e\<^sub>1 @ FApp1\<^sub>c \<Delta> e\<^sub>2 # s) \<Delta> (head_expr e\<^sub>1))" 
      by (metis iter_step)
  thus ?case by simp
qed simp_all

text \<open>We now reconstruct encodings, stack-encodings, and state-encodings:\<close>

lemma encode_not_nil [dest]: "encode e = [] \<Longrightarrow> False"
  by (induction e) simp_all

lemma encode_to_lookup [dest]: "encode e @ \<C>' = Lookup\<^sub>e x # \<C> \<Longrightarrow> 
    head_expr e = Var\<^sub>d x \<and> \<C> = tl (encode e) @ \<C>'"
  by (induction e arbitrary: \<C>') fastforce+

lemma encode_to_pushcon [dest]: "encode e @ \<C>' = PushCon\<^sub>e n # \<C> \<Longrightarrow> 
    head_expr e = Const\<^sub>d n \<and> \<C> = tl (encode e) @ \<C>'"
  by (induction e arbitrary: \<C>') fastforce+

lemma encode_to_pushlam [dest]: "encode e @ \<C>' = PushLam\<^sub>e \<C>'' # \<C> \<Longrightarrow> 
    \<exists>t e'. head_expr e = Lam\<^sub>d t e' \<and> \<C>'' = encode e' \<and> \<C> = tl (encode e) @ \<C>'"
  by (induction e arbitrary: \<C>') fastforce+

lemma encode_to_apply [dest]: "encode e @ \<C>' = Apply\<^sub>e # \<C> \<Longrightarrow> False"
  by (induction e arbitrary: \<C>') simp_all

lemma encode_lam_closure [dest]: "Lam\<^sub>e env \<C> = encode_closure c \<Longrightarrow> 
    \<exists>t \<Delta> e. c = Lam\<^sub>c t \<Delta> e \<and> env = map encode_closure \<Delta> \<and> \<C> = encode e"
  by (induction c) simp_all

lemma prepend_to_cons [dest]: "prepend_to_top_frame \<C>' s\<^sub>e = (\<Delta>, \<C>) # s\<^sub>e' \<Longrightarrow> 
    \<exists>\<C>''. s\<^sub>e = (\<Delta>, \<C>'') # s\<^sub>e' \<and> \<C> = \<C>' @ \<C>''"
  by (induction \<C>' s\<^sub>e rule: prepend_to_top_frame.induct) simp_all

lemma prepend_to_apply [dest]: "prepend_to_top_frame (encode e) s\<^sub>e = (\<Delta>, Apply\<^sub>e # \<C>) # s\<^sub>e' \<Longrightarrow> 
    False"
  by (induction "encode e" s\<^sub>e rule: prepend_to_top_frame.induct) auto

lemma encode_stack_to_lookup [dest]: "stack_from_stack s\<^sub>c = (\<Delta>\<^sub>e, Lookup\<^sub>e x # \<C>) # s\<^sub>e \<Longrightarrow> 
  \<exists>\<Delta>\<^sub>c e s\<^sub>c' \<C>'. s\<^sub>c = FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c' \<and> stack_from_stack s\<^sub>c' = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e \<and> 
    head_expr e = Var\<^sub>d x \<and> \<C> = tl (encode e) @ Apply\<^sub>e # \<C>'"
proof (induction s\<^sub>c rule: stack_from_stack.induct)
  case (2 \<Delta> e s\<^sub>c)
  then obtain \<C>' where "stack_from_stack s\<^sub>c = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e \<and> 
    encode e @ Apply\<^sub>e # \<C>' = Lookup\<^sub>e x # \<C>" by fastforce
  thus ?case by auto
qed auto

lemma encode_stack_to_pushcon [dest]: "stack_from_stack s\<^sub>c = (\<Delta>\<^sub>e, PushCon\<^sub>e n # \<C>) # s\<^sub>e \<Longrightarrow> 
  \<exists>\<Delta>\<^sub>c e s\<^sub>c' \<C>'. s\<^sub>c = FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c' \<and> stack_from_stack s\<^sub>c' = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e \<and> 
    head_expr e = Const\<^sub>d n \<and> \<C> = tl (encode e) @ Apply\<^sub>e # \<C>'"
proof (induction s\<^sub>c rule: stack_from_stack.induct)
  case (2 \<Delta>\<^sub>s e s\<^sub>c)
  then obtain \<C>' where "stack_from_stack s\<^sub>c = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e \<and> 
    encode e @ Apply\<^sub>e # \<C>' = PushCon\<^sub>e n # \<C>" by fastforce
  thus ?case by auto
qed auto

lemma encode_stack_to_pushlam [dest]: "stack_from_stack s\<^sub>c = (\<Delta>\<^sub>e, PushLam\<^sub>e \<C>' # \<C>) # s\<^sub>e \<Longrightarrow> 
  \<exists>\<Delta>\<^sub>c e s\<^sub>c' t e' \<C>''. s\<^sub>c = FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c' \<and> stack_from_stack s\<^sub>c' = (\<Delta>\<^sub>e, \<C>'') # s\<^sub>e \<and> 
    head_expr e = Lam\<^sub>d t e' \<and> \<C> = tl (encode e) @ Apply\<^sub>e # \<C>'' \<and> \<C>' = encode e'"
proof (induction s\<^sub>c rule: stack_from_stack.induct)
  case (2 \<Delta>\<^sub>c e s\<^sub>c)
  then obtain \<C>'' where "stack_from_stack s\<^sub>c = (\<Delta>\<^sub>e, \<C>'') # s\<^sub>e \<and> 
    encode e @ Apply\<^sub>e # \<C>'' = PushLam\<^sub>e \<C>' # \<C>" by fastforce
  moreover then obtain t e' where "head_expr e = Lam\<^sub>d t e' \<and> \<C>' = encode e' \<and> 
    \<C> = tl (encode e) @ Apply\<^sub>e # \<C>''" by (metis encode_to_pushlam)
  ultimately show ?case by fastforce
qed auto

lemma encode_stack_to_apply [dest]: "stack_from_stack s = (\<Delta>\<^sub>e, Apply\<^sub>e # \<C>) # s\<^sub>e \<Longrightarrow> 
    \<exists>s\<^sub>c' c. s = FApp2\<^sub>c c # s\<^sub>c' \<and> stack_from_stack s\<^sub>c' = (\<Delta>\<^sub>e, \<C>) # s\<^sub>e"
  by (induction s rule: stack_from_stack.induct) auto

lemma encode_stack_to_return [dest]: "stack_from_stack s = (\<Delta>\<^sub>e, []) # s\<^sub>e \<Longrightarrow> 
    \<exists>\<Delta>\<^sub>c s\<^sub>c'. s = FReturn\<^sub>c \<Delta>\<^sub>c # s\<^sub>c' \<and> \<Delta>\<^sub>e = map encode_closure \<Delta>\<^sub>c \<and> s\<^sub>e = stack_from_stack s\<^sub>c'"
  by (induction s rule: stack_from_stack.induct) auto

lemma encode_state_to_lookup [dest, consumes 1, case_names SE\<^sub>c SC\<^sub>c]: "
  encode_state \<Sigma>\<^sub>c = S\<^sub>e \<V> ((\<Delta>\<^sub>e, Lookup\<^sub>e x # \<C>) # s\<^sub>e) \<Longrightarrow> 
    (\<And>s\<^sub>c \<Delta>\<^sub>c e \<C>'. head_expr e = Var\<^sub>d x \<Longrightarrow> \<C> = tl (encode e) @ \<C>' \<Longrightarrow> 
      stack_from_stack s\<^sub>c = ((\<Delta>\<^sub>e, \<C>') # s\<^sub>e) \<Longrightarrow> \<V> = vals_from_stack s\<^sub>c \<Longrightarrow> P (SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e)) \<Longrightarrow> 
    (\<And>s\<^sub>c c \<Delta>\<^sub>c e \<C>'. head_expr e = Var\<^sub>d x \<Longrightarrow> \<C> = tl (encode e) @ Apply\<^sub>e # \<C>' \<Longrightarrow> 
      stack_from_stack s\<^sub>c = ((\<Delta>\<^sub>e, \<C>') # s\<^sub>e) \<Longrightarrow> \<V> = encode_closure c # vals_from_stack s\<^sub>c \<Longrightarrow> 
      P (SC\<^sub>c (FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c) c)) \<Longrightarrow> P \<Sigma>\<^sub>c"
proof (induction \<Sigma>\<^sub>c)
  case (SE\<^sub>c s \<Delta> e)
  moreover then obtain \<C>' where "stack_from_stack s = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e \<and> 
    encode e @ \<C>' = Lookup\<^sub>e x # \<C>" by auto
  ultimately show ?case by auto
qed auto

lemma encode_state_to_pushcon [dest, consumes 1, case_names SE\<^sub>c SC\<^sub>c]: "
  encode_state \<Sigma>\<^sub>c = S\<^sub>e \<V> ((\<Delta>\<^sub>e, PushCon\<^sub>e n # \<C>) # s\<^sub>e) \<Longrightarrow> 
    (\<And>s\<^sub>c \<Delta>\<^sub>c e \<C>'. head_expr e = Const\<^sub>d n \<Longrightarrow> \<C> = tl (encode e) @ \<C>' \<Longrightarrow> 
      stack_from_stack s\<^sub>c = ((\<Delta>\<^sub>e, \<C>') # s\<^sub>e) \<Longrightarrow> \<V> = vals_from_stack s\<^sub>c \<Longrightarrow> P (SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e)) \<Longrightarrow> 
    (\<And>s\<^sub>c c \<Delta>\<^sub>c e \<C>'. head_expr e = Const\<^sub>d n \<Longrightarrow> \<C> = tl (encode e) @ Apply\<^sub>e # \<C>' \<Longrightarrow> 
      stack_from_stack s\<^sub>c = ((\<Delta>\<^sub>e, \<C>') # s\<^sub>e) \<Longrightarrow> \<V> = encode_closure c # vals_from_stack s\<^sub>c \<Longrightarrow> 
      P (SC\<^sub>c (FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c) c)) \<Longrightarrow> P \<Sigma>\<^sub>c"
proof (induction \<Sigma>\<^sub>c)
  case (SE\<^sub>c s \<Delta> e)
  moreover then obtain \<C>' where "stack_from_stack s = (\<Delta>\<^sub>e, \<C>') # s\<^sub>e \<and> 
    encode e @ \<C>' = PushCon\<^sub>e n # \<C>" by auto
  ultimately show ?case by auto
qed auto

lemma encode_state_to_pushlam [dest, consumes 1, case_names SE\<^sub>c SC\<^sub>c]: "
  encode_state \<Sigma>\<^sub>c = S\<^sub>e \<V> ((\<Delta>\<^sub>e, PushLam\<^sub>e \<C>' # \<C>) # s\<^sub>e) \<Longrightarrow> 
    (\<And>s\<^sub>c \<Delta>\<^sub>c e tt e' \<C>''. \<Sigma>\<^sub>c = SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e \<Longrightarrow> head_expr e = Lam\<^sub>d tt e' \<Longrightarrow> 
      \<C> = tl (encode e) @ \<C>'' \<Longrightarrow> \<C>' = encode e' \<Longrightarrow> \<V> = vals_from_stack s\<^sub>c \<Longrightarrow> 
      stack_from_stack s\<^sub>c = (\<Delta>\<^sub>e, \<C>'') # s\<^sub>e \<Longrightarrow> P) \<Longrightarrow> 
    (\<And>s\<^sub>c c \<Delta>\<^sub>c e tt e' \<C>''. \<Sigma>\<^sub>c = SC\<^sub>c (FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c) c \<Longrightarrow> head_expr e = Lam\<^sub>d tt e' \<Longrightarrow> 
      \<C> = tl (encode e) @ Apply\<^sub>e # \<C>'' \<Longrightarrow> \<C>' = encode e' \<Longrightarrow> 
      \<V> = encode_closure c # vals_from_stack s\<^sub>c \<Longrightarrow> stack_from_stack s\<^sub>c = (\<Delta>\<^sub>e, \<C>'') # s\<^sub>e \<Longrightarrow> P) \<Longrightarrow> 
    P"
proof (induction \<Sigma>\<^sub>c)
  case (SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e)
  moreover then obtain \<C>'' where "stack_from_stack s\<^sub>c = (\<Delta>\<^sub>e, \<C>'') # s\<^sub>e \<and> 
    encode e @ \<C>'' = PushLam\<^sub>e \<C>' # \<C>" by auto
  moreover then obtain tt e' where "head_expr e = Lam\<^sub>d tt e' \<and> \<C>' = encode e' \<and> 
    \<C> = tl (encode e) @ \<C>''" by (metis encode_to_pushlam)
  ultimately show ?case by auto
qed auto

lemma encode_state_to_apply [dest]: "
  encode_state \<Sigma>\<^sub>c = S\<^sub>e (v # Lam\<^sub>e \<Delta>\<^sub>e' \<C>' # \<V>) ((\<Delta>\<^sub>e, Apply\<^sub>e # \<C>) # s\<^sub>e) \<Longrightarrow>
    \<exists>s\<^sub>c c c'. \<Sigma>\<^sub>c = SC\<^sub>c (FApp2\<^sub>c c' # s\<^sub>c) c \<and> stack_from_stack s\<^sub>c = ((\<Delta>\<^sub>e, \<C>) # s\<^sub>e) \<and> 
      v = encode_closure c \<and> Lam\<^sub>e \<Delta>\<^sub>e' \<C>' = encode_closure c' \<and> \<V> = vals_from_stack s\<^sub>c"
  by (induction \<Sigma>\<^sub>c) auto

lemma encode_state_to_return [dest]: "encode_state \<Sigma>\<^sub>c = S\<^sub>e \<V> ((\<Delta>\<^sub>e, []) # s\<^sub>e) \<Longrightarrow> 
  (\<exists>\<Delta>\<^sub>c s c. \<Sigma>\<^sub>c = SC\<^sub>c (FReturn\<^sub>c \<Delta>\<^sub>c # s) c \<and> s\<^sub>e = stack_from_stack s \<and>
    \<Delta>\<^sub>e = map encode_closure \<Delta>\<^sub>c \<and> \<V> = encode_closure c # vals_from_stack s)"
  by (induction \<Sigma>\<^sub>c) auto

text \<open>And now, we can finally prove completeness.\<close>

theorem complete\<^sub>e [simp]: "encode_state \<Sigma>\<^sub>c \<leadsto>\<^sub>e \<Sigma>\<^sub>t' \<Longrightarrow> \<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>c'. iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> \<Sigma>\<^sub>t' = encode_state \<Sigma>\<^sub>c'"
proof (induction "encode_state \<Sigma>\<^sub>c" \<Sigma>\<^sub>t' rule: eval\<^sub>e.induct)
  case (ev\<^sub>e_lookup \<Delta>\<^sub>e x v \<V> \<C> s\<^sub>e)
  hence X: "encode_state \<Sigma>\<^sub>c = S\<^sub>e \<V> ((\<Delta>\<^sub>e, Lookup\<^sub>e x # \<C>) # s\<^sub>e)" by simp
  from X ev\<^sub>e_lookup(1, 3) show ?case
  proof (induction rule: encode_state_to_lookup)
    case (SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e \<C>')
    have X: "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e) (SE\<^sub>c (tail_expr \<Delta>\<^sub>c e @ s\<^sub>c) \<Delta>\<^sub>c (head_expr e))" by simp
    from SE\<^sub>c obtain c where C: "lookup \<Delta>\<^sub>c x = Some c \<and> encode_closure c = v" by fastforce
    with X SE\<^sub>c have "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e) (SC\<^sub>c (tail_expr \<Delta>\<^sub>c e @ s\<^sub>c) c)" by simp
    with SE\<^sub>c C show ?case by auto
  next
    case (SC\<^sub>c s\<^sub>c c \<Delta>\<^sub>c e \<C>')
    moreover have "iter (\<leadsto>\<^sub>c) (SE\<^sub>c (FApp2\<^sub>c c # s\<^sub>c) \<Delta>\<^sub>c e) 
      (SE\<^sub>c (tail_expr \<Delta>\<^sub>c e @ FApp2\<^sub>c c # s\<^sub>c) \<Delta>\<^sub>c (head_expr e))" by simp
    moreover have "SC\<^sub>c (FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c) c \<leadsto>\<^sub>c SE\<^sub>c (FApp2\<^sub>c c # s\<^sub>c) \<Delta>\<^sub>c e" by simp
    ultimately have X: "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c) c) 
      (SE\<^sub>c (tail_expr \<Delta>\<^sub>c e @ FApp2\<^sub>c c # s\<^sub>c) \<Delta>\<^sub>c (Var\<^sub>d x))" by (metis iter_step)
    from SC\<^sub>c obtain c' where C: "lookup \<Delta>\<^sub>c x = Some c' \<and> encode_closure c' = v" by fastforce
    with X have "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c) c) (SC\<^sub>c (tail_expr \<Delta>\<^sub>c e @ FApp2\<^sub>c c # s\<^sub>c) c')" 
      by simp
    with SC\<^sub>c C show ?case by auto
  qed
next
  case (ev\<^sub>e_pushcon \<V> \<Delta>\<^sub>e n \<C> s\<^sub>e)
  hence X: "encode_state \<Sigma>\<^sub>c = S\<^sub>e \<V> ((\<Delta>\<^sub>e, PushCon\<^sub>e n # \<C>) # s\<^sub>e)" by simp
  from X ev\<^sub>e_pushcon(2) show ?case
  proof (induction rule: encode_state_to_pushcon)
    case (SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e \<C>')
    moreover have "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e) (SE\<^sub>c (tail_expr \<Delta>\<^sub>c e @ s\<^sub>c) \<Delta>\<^sub>c (head_expr e))" by simp
    ultimately have "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e) (SC\<^sub>c (tail_expr \<Delta>\<^sub>c e @ s\<^sub>c) (Const\<^sub>c n))" by simp
    with SE\<^sub>c show ?case by auto
  next
    case (SC\<^sub>c s\<^sub>c c \<Delta>\<^sub>c e \<C>')
    moreover have "iter (\<leadsto>\<^sub>c) (SE\<^sub>c (FApp2\<^sub>c c # s\<^sub>c) \<Delta>\<^sub>c e) 
      (SE\<^sub>c (tail_expr \<Delta>\<^sub>c e @ FApp2\<^sub>c c # s\<^sub>c) \<Delta>\<^sub>c (head_expr e))" by simp
    moreover have "SC\<^sub>c (FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c) c \<leadsto>\<^sub>c SE\<^sub>c (FApp2\<^sub>c c # s\<^sub>c) \<Delta>\<^sub>c e" by simp
    moreover have "SE\<^sub>c (tail_expr \<Delta>\<^sub>c e @ FApp2\<^sub>c c # s\<^sub>c) \<Delta>\<^sub>c (Const\<^sub>d n) \<leadsto>\<^sub>c 
      SC\<^sub>c (tail_expr \<Delta>\<^sub>c e @ FApp2\<^sub>c c # s\<^sub>c) (Const\<^sub>c n)" by simp
    ultimately have "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c) c)
      (SC\<^sub>c (tail_expr \<Delta>\<^sub>c e @ FApp2\<^sub>c c # s\<^sub>c) (Const\<^sub>c n))" 
        by (metis iter_step iter_step_after)
    with SC\<^sub>c show ?case by auto
  qed
next
  case (ev\<^sub>e_pushlam \<V> \<Delta>\<^sub>e \<C>' \<C> s\<^sub>e)
  hence X: "encode_state \<Sigma>\<^sub>c = S\<^sub>e \<V> ((\<Delta>\<^sub>e, PushLam\<^sub>e \<C>' # \<C>) # s\<^sub>e)" by simp
  from X ev\<^sub>e_pushlam(2) show ?case
  proof (induction rule: encode_state_to_pushlam)
    case (SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e tt e' \<C>'')
    moreover have "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e) (SE\<^sub>c (tail_expr \<Delta>\<^sub>c e @ s\<^sub>c) \<Delta>\<^sub>c (head_expr e))" by simp
    moreover have "SE\<^sub>c (tail_expr \<Delta>\<^sub>c e @ s\<^sub>c) \<Delta>\<^sub>c (Lam\<^sub>d tt e') \<leadsto>\<^sub>c 
      SC\<^sub>c (tail_expr \<Delta>\<^sub>c e @ s\<^sub>c) (Lam\<^sub>c tt \<Delta>\<^sub>c e')" by simp
    ultimately have X: "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s\<^sub>c \<Delta>\<^sub>c e) (SC\<^sub>c (tail_expr \<Delta>\<^sub>c e @ s\<^sub>c) (Lam\<^sub>c tt \<Delta>\<^sub>c e'))"
      by (metis iter_step_after)
    from SE\<^sub>c have "\<Delta>\<^sub>e = map encode_closure \<Delta>\<^sub>c" by fastforce
    with SE\<^sub>c X show ?case by auto
  next
    case (SC\<^sub>c s\<^sub>c c \<Delta>\<^sub>c e tt e' \<C>'')
    moreover have "iter (\<leadsto>\<^sub>c) (SE\<^sub>c (FApp2\<^sub>c c # s\<^sub>c) \<Delta>\<^sub>c e) 
      (SE\<^sub>c (tail_expr \<Delta>\<^sub>c e @ FApp2\<^sub>c c # s\<^sub>c) \<Delta>\<^sub>c (head_expr e))" by simp
    moreover have "SC\<^sub>c (FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c) c \<leadsto>\<^sub>c SE\<^sub>c (FApp2\<^sub>c c # s\<^sub>c) \<Delta>\<^sub>c e" by simp
    moreover have "SE\<^sub>c (tail_expr \<Delta>\<^sub>c e @ FApp2\<^sub>c c # s\<^sub>c) \<Delta>\<^sub>c (Lam\<^sub>d tt e') \<leadsto>\<^sub>c 
      SC\<^sub>c (tail_expr \<Delta>\<^sub>c e @ FApp2\<^sub>c c # s\<^sub>c) (Lam\<^sub>c tt \<Delta>\<^sub>c e')" by simp
    ultimately have X: "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FApp1\<^sub>c \<Delta>\<^sub>c e # s\<^sub>c) c) 
      (SC\<^sub>c (tail_expr \<Delta>\<^sub>c e @ FApp2\<^sub>c c # s\<^sub>c) (Lam\<^sub>c tt \<Delta>\<^sub>c e'))" 
        by (metis iter_step iter_step_after)
    from SC\<^sub>c have "\<Delta>\<^sub>e = map encode_closure \<Delta>\<^sub>c" by fastforce
    with SC\<^sub>c X show ?case by auto
  qed
next
  case (ev\<^sub>e_apply v \<Delta>\<^sub>e' \<C>' \<V> \<Delta>\<^sub>e \<C> s\<^sub>e)
  hence "encode_state \<Sigma>\<^sub>c = S\<^sub>e (v # Lam\<^sub>e \<Delta>\<^sub>e' \<C>' # \<V>) ((\<Delta>\<^sub>e, Apply\<^sub>e # \<C>) # s\<^sub>e)" by simp
  then obtain s\<^sub>c c c' where "\<Sigma>\<^sub>c = SC\<^sub>c (FApp2\<^sub>c c' # s\<^sub>c) c \<and> stack_from_stack s\<^sub>c = ((\<Delta>\<^sub>e, \<C>) # s\<^sub>e) \<and> 
    v = encode_closure c \<and> Lam\<^sub>e \<Delta>\<^sub>e' \<C>' = encode_closure c' \<and> \<V> = vals_from_stack s\<^sub>c" 
      by auto
  moreover then obtain t \<Delta>\<^sub>c e where "c' = Lam\<^sub>c t \<Delta>\<^sub>c e \<and> \<Delta>\<^sub>e' = map encode_closure \<Delta>\<^sub>c \<and> 
    \<C>' = encode e" by auto
  moreover have "SC\<^sub>c (FApp2\<^sub>c (Lam\<^sub>c t \<Delta>\<^sub>c e) # s\<^sub>c) c \<leadsto>\<^sub>c SE\<^sub>c (FReturn\<^sub>c (c # \<Delta>\<^sub>c) # s\<^sub>c) (c # \<Delta>\<^sub>c) e" 
    by simp
  moreover hence "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FApp2\<^sub>c (Lam\<^sub>c t \<Delta>\<^sub>c e) # s\<^sub>c) c) 
    (SE\<^sub>c (FReturn\<^sub>c (c # \<Delta>\<^sub>c) # s\<^sub>c) (c # \<Delta>\<^sub>c) e)" by (metis iter_one)
  ultimately show ?case by auto
next
  case (ev\<^sub>e_return \<V> \<Delta>\<^sub>e s\<^sub>e)
  hence "encode_state \<Sigma>\<^sub>c = S\<^sub>e \<V> ((\<Delta>\<^sub>e, []) # s\<^sub>e)" by simp
  then obtain \<Delta>\<^sub>c s\<^sub>c c where S: "\<Sigma>\<^sub>c = SC\<^sub>c (FReturn\<^sub>c \<Delta>\<^sub>c # s\<^sub>c) c \<and> s\<^sub>e = stack_from_stack s\<^sub>c \<and>
    \<Delta>\<^sub>e = map encode_closure \<Delta>\<^sub>c \<and> \<V> = encode_closure c # vals_from_stack s\<^sub>c" by auto
  have "SC\<^sub>c (FReturn\<^sub>c \<Delta>\<^sub>c # s\<^sub>c) c \<leadsto>\<^sub>c SC\<^sub>c s\<^sub>c c" by simp
  hence "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FReturn\<^sub>c \<Delta>\<^sub>c # s\<^sub>c) c) (SC\<^sub>c s\<^sub>c c)" by (metis iter_one)
  with S show ?case by auto
qed

end