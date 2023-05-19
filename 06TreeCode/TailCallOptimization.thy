theory TailCallOptimization
  imports TreeCode "../00Utils/Iteration"
begin

subsection \<open>Tail-Call Optimization\<close>

text \<open>A tail-call is a function call that takes place at the very end of another function's body. 
The significance of this becomes clear when you consider the naive execution of such a function. The 
last thing the outer function does before it returns is to call the inner function; then, when the 
inner function returns, the outer function immediately returns too. The outer function's stack frame 
remains in the stack the whole time the inner function is executing, despite the fact that it will 
never be needed again. Tail-call optimization changes the push into the inner function into a 
_jump_ to the inner function, replacing the one frame with the other - the call stack is shorter, 
and execution is quicker too, since the effort of preserving and then popping the outer frame is 
avoided. When applied systematically the effect can be quite great: notably, recursive functions 
that only make recursive calls in tail-position ("tail-recursive functions") can be executed in 
constant space, just like an imperative loop. This is precisely what we added the \<open>Jump\<^sub>e\<close> 
instruction to express.\<close>

text \<open>What exactly do we change with tail-call optimization? We replace every sequence of an
\<open>Apply\<^sub>e\<close> followed by a \<open>Return\<^sub>e\<close> with a \<open>Jump\<^sub>e\<close>, obviously. But we also eliminate certain frames from
the call stack; specifically, any frame that consists of an empty codeblock followed by a \<open>Return\<^sub>e\<close>.
We mark these frames as \<open>dead_frame\<close>s.\<close>

fun dead_frame :: "frame\<^sub>e \<Rightarrow> bool" where
  "dead_frame (\<V>, [], Return\<^sub>e) = True"
| "dead_frame (\<V>, [], Jump\<^sub>e) = False"
| "dead_frame (\<V>, op # \<C>, r) = False"

text \<open>The optimization itself is simple: we convert the code and returns, then map the conversion up 
through the levels of the state, taking care to eliminate the dead frames in the stack:\<close>

primrec tco_return :: "code\<^sub>e list \<Rightarrow> return\<^sub>e \<Rightarrow> return\<^sub>e" where
  "tco_return [] r = r"
| "tco_return (op # cd) r = (if op = Apply\<^sub>e \<and> cd = [] then Jump\<^sub>e else tco_return cd r)"

fun tco_code :: "code\<^sub>e list \<Rightarrow> code\<^sub>e list" where
  "tco_code [] = []"
| "tco_code (Apply\<^sub>e # []) = []"
| "tco_code (PushLam\<^sub>e \<C>' r # \<C>) = PushLam\<^sub>e (tco_code \<C>') (tco_return \<C>' r) # tco_code \<C>"
| "tco_code (op # \<C>) = op # tco_code \<C>"

primrec tco_val :: "closure\<^sub>e \<Rightarrow> closure\<^sub>e" where
  "tco_val (Const\<^sub>e n) = Const\<^sub>e n"
| "tco_val (Lam\<^sub>e \<Delta> \<C> r) = Lam\<^sub>e (map tco_val \<Delta>) (tco_code \<C>) (tco_return \<C> r)"

fun tco_frame :: "frame\<^sub>e \<Rightarrow> frame\<^sub>e" where
  "tco_frame (\<Delta>, \<C>, r) = (map tco_val \<Delta>, tco_code \<C>, tco_return \<C> r)"

abbreviation tco_stack :: "frame\<^sub>e list \<Rightarrow> frame\<^sub>e list" where
  "tco_stack s \<equiv> filter (\<lambda>f. \<not> dead_frame f) (map tco_frame s)"

primrec tco_state :: "state\<^sub>e \<Rightarrow> state\<^sub>e" where
  "tco_state (S\<^sub>e \<V> s) = S\<^sub>e (map tco_val \<V>) (tco_stack s)"

text \<open>We will of course prove that tail-call removal is semantics-preserving, but we will not 
formally prove that it really is "an optimization". Instead, we will prove some much simpler results 
that indicate _why_ it is an optimization, and what a full proof would need to formalize.\<close>

text \<open>The optimized code is always shorter. Since tail-call removal is a local optimization, leaving 
the global structure of the computation intact, any codeblock executed before it will be executed 
after as well. Assuming that each operation takes roughly equal time, this means that tail-call 
optimization reduces runtime. (In fact, we will see much later that \<open>Jump\<^sub>e\<close> is shorter to run as 
machine code than the \<open>Apply\<^sub>e; Return\<^sub>e\<close> sequence, so we do even better. But we're not there yet.)\<close>

theorem tco_always_shorter_code [simp]: "length (tco_code \<C>) \<le> length \<C>"
  by (induction \<C> rule: tco_code.induct) simp_all

text \<open>The value stack - what we might consider something like a proxy for the heap usage - is 
unchanged by tail-call removal. But the call stack - which remains the call stack throughout 
compilation - is made shorter:\<close>

primrec get_callstack :: "state\<^sub>e \<Rightarrow> frame\<^sub>e list" where
  "get_callstack (S\<^sub>e \<V> s) = s"

theorem tco_always_smaller_stack [simp]: "
    length (get_callstack (tco_state \<Sigma>)) \<le> length (get_callstack \<Sigma>)"
  by (induction \<Sigma>) simp_all

text \<open>Correctness is the easier proof for this pass. First off, we need some auxiliary functions to 
express that no \<open>PushLam\<^sub>e\<close> contains code for a dead frame, and every return is a \<open>Return\<^sub>e\<close> (as will
always be the case, pre-optimization).\<close>

fun complete_lams :: "code\<^sub>e list \<Rightarrow> bool" where
  "complete_lams [] = True"
| "complete_lams (PushLam\<^sub>e \<C>' r # \<C>) = (\<C>' \<noteq> [] \<and> r = Return\<^sub>e \<and> complete_lams \<C>' \<and> complete_lams \<C>)"
| "complete_lams (op # \<C>) = complete_lams \<C>"

primrec complete_lams_val :: "closure\<^sub>e \<Rightarrow> bool" where
  "complete_lams_val (Const\<^sub>e n) = True"
| "complete_lams_val (Lam\<^sub>e \<Delta> \<C> r) = 
    (\<C> \<noteq> [] \<and> r = Return\<^sub>e \<and> list_all complete_lams_val \<Delta> \<and> complete_lams \<C>)"

fun complete_lams_frame :: "frame\<^sub>e \<Rightarrow> bool" where
  "complete_lams_frame (\<Delta>, \<C>, r) = (list_all complete_lams_val \<Delta> \<and> complete_lams \<C> \<and> r = Return\<^sub>e)"

primrec complete_lams_state :: "state\<^sub>e \<Rightarrow> bool" where
  "complete_lams_state (S\<^sub>e \<V> s) = (list_all complete_lams_val \<V> \<and> list_all complete_lams_frame s)"

lemma eval_complete_lams [simp]: "\<Sigma> \<leadsto>\<^sub>e \<Sigma>' \<Longrightarrow> complete_lams_state \<Sigma> \<Longrightarrow> complete_lams_state \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: eval\<^sub>e.induct) auto

text \<open>The \<open>iter (\<leadsto>\<^sub>e)\<close> in correctness is unusual, in that it doesn't merely mean one-or-more 
evaluation steps, or zero-or-one, but either: clearing a dead stack frame incorporates an extra step 
in every case except \<open>ev\<^sub>e_return\<close>, where the optimization pass has already cleared the dead frame 
for us and it takes no steps. It may seem odd that the optimized code requires two steps where the 
original code needed one, but what is actually happening is the "missing" steps from the 
\<open>ev\<^sub>e_return\<close> are being moved there; we are still reducing the number of steps steps in total.\<close>

lemma tco_to_dead_frame [simp]: "dead_frame (\<Delta>, tco_code \<C>, tco_return \<C> r) = (\<C> = [] \<and> r = Return\<^sub>e)"
proof (induction \<C> rule: tco_code.induct)
  case 1
  thus ?case by (induction r) simp_all
qed simp_all

lemma tco_to_dead_frame_apply [simp]: "
  dead_frame (map tco_val \<Delta>, tco_code (Apply\<^sub>e # \<C>), tco_return \<C> r) = (\<C> = [] \<and> r = Return\<^sub>e)"
proof (induction \<C> rule: tco_code.induct)
  case 1
  thus ?case by (induction r) simp_all
qed simp_all

theorem correctness\<^sub>t\<^sub>c\<^sub>o: "\<Sigma> \<leadsto>\<^sub>e \<Sigma>' \<Longrightarrow> complete_lams_state \<Sigma> \<Longrightarrow> 
  iter (\<leadsto>\<^sub>e) (tco_state \<Sigma>) (tco_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>e.induct)
  case (ev\<^sub>e_lookup \<Delta> x v \<V> \<C> r s)
  thus ?case
  proof (cases "\<C> = []")
    case True
    with ev\<^sub>e_lookup have  "
      S\<^sub>e (tco_val v # map tco_val \<V>) ((map tco_val \<Delta>, tco_code \<C>, tco_return \<C> r) # tco_stack s) \<leadsto>\<^sub>e
        S\<^sub>e (tco_val v # map tco_val \<V>) (tco_stack s)" by simp
    moreover from ev\<^sub>e_lookup have "
      S\<^sub>e (map tco_val \<V>) ((map tco_val \<Delta>, Lookup\<^sub>e x # tco_code \<C>, tco_return \<C> r) # tco_stack s) \<leadsto>\<^sub>e
        S\<^sub>e (tco_val v # map tco_val \<V>) ((map tco_val \<Delta>, tco_code \<C>, tco_return \<C> r) # tco_stack s)"
      by simp
    ultimately have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (map tco_val \<V>) 
      ((map tco_val \<Delta>, Lookup\<^sub>e x # tco_code \<C>, tco_return \<C> r) # tco_stack s))
        (S\<^sub>e (tco_val v # map tco_val \<V>) (tco_stack s))"
      by (metis (no_types, lifting) iter_refl iter_step)
    with ev\<^sub>e_lookup True show ?thesis by simp
  next
    case False
    with ev\<^sub>e_lookup have "tco_state (S\<^sub>e \<V> ((\<Delta>, Lookup\<^sub>e x # \<C>, r) # s)) \<leadsto>\<^sub>e
      tco_state (S\<^sub>e (v # \<V>) ((\<Delta>, \<C>, r) # s))" by auto
    thus ?thesis by (metis iter_one)
  qed
next
  case (ev\<^sub>e_pushcon \<V> \<Delta> n \<C> r s)
  thus ?case
  proof (cases "\<C> = []")
    case True
    with ev\<^sub>e_pushcon have "
      S\<^sub>e (Const\<^sub>e n # map tco_val \<V>) ((map tco_val \<Delta>, tco_code \<C>, tco_return \<C> r) # tco_stack s) \<leadsto>\<^sub>e 
        S\<^sub>e (Const\<^sub>e n # map tco_val \<V>) (tco_stack s)" by simp
    moreover have "
      S\<^sub>e (map tco_val \<V>) ((map tco_val \<Delta>, PushCon\<^sub>e n # tco_code \<C>, tco_return \<C> r) # tco_stack s) \<leadsto>\<^sub>e 
        S\<^sub>e (Const\<^sub>e n # map tco_val \<V>) ((map tco_val \<Delta>, tco_code \<C>, tco_return \<C> r) # tco_stack s)"
      by simp
    ultimately have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (map tco_val \<V>) 
      ((map tco_val \<Delta>, PushCon\<^sub>e n # tco_code \<C>, tco_return \<C> r) # tco_stack s))
        (S\<^sub>e (Const\<^sub>e n # map tco_val \<V>) (tco_stack s))"
      by (metis (no_types, lifting) iter_refl iter_step)
    with ev\<^sub>e_pushcon True show ?thesis by simp
  next
    case False
    hence "tco_state (S\<^sub>e \<V> ((\<Delta>, PushCon\<^sub>e n # \<C>, r) # s)) \<leadsto>\<^sub>e 
      tco_state (S\<^sub>e (Const\<^sub>e n # \<V>) ((\<Delta>, \<C>, r) # s))" by auto
    thus ?thesis by (metis iter_one)
  qed
next
  case (ev\<^sub>e_pushlam \<V> \<Delta> \<C>' r' \<C> r s)
  thus ?case
  proof (cases "\<C> = []")
    case True
    with ev\<^sub>e_pushlam have "S\<^sub>e (Lam\<^sub>e (map tco_val \<Delta>) (tco_code \<C>') (tco_return \<C>' r') # map tco_val \<V>) 
      ((map tco_val \<Delta>, tco_code \<C>, tco_return \<C> r) # tco_stack s) \<leadsto>\<^sub>e 
      S\<^sub>e (Lam\<^sub>e (map tco_val \<Delta>) (tco_code \<C>') (tco_return \<C>' r') # map tco_val \<V>) (tco_stack s)" 
        by simp
    moreover have "S\<^sub>e (map tco_val \<V>) ((map tco_val \<Delta>, PushLam\<^sub>e (tco_code \<C>') (tco_return \<C>' r') # 
      tco_code \<C>, tco_return \<C> r) # tco_stack s) \<leadsto>\<^sub>e 
      S\<^sub>e (Lam\<^sub>e (map tco_val \<Delta>) (tco_code \<C>') (tco_return \<C>' r') # map tco_val \<V>) 
      ((map tco_val \<Delta>, tco_code \<C>, tco_return \<C> r) # tco_stack s)"
        by simp
    ultimately have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (map tco_val \<V>) ((map tco_val \<Delta>, PushLam\<^sub>e (tco_code \<C>') 
      (tco_return \<C>' r') # tco_code \<C>, tco_return \<C> r) # tco_stack s))
      (S\<^sub>e (Lam\<^sub>e (map tco_val \<Delta>) (tco_code \<C>') (tco_return \<C>' r') # map tco_val \<V>) (tco_stack s))"
      by (metis (no_types, lifting) iter_refl iter_step)
    with ev\<^sub>e_pushlam True show ?thesis by simp
  next
    case False
    hence "tco_state (S\<^sub>e \<V> ((\<Delta>, PushLam\<^sub>e \<C>' r' # \<C>, r) # s)) \<leadsto>\<^sub>e 
      tco_state (S\<^sub>e (Lam\<^sub>e \<Delta> \<C>' r' # \<V>) ((\<Delta>, \<C>, r) # s))" by simp
    thus ?thesis by (metis iter_one)
  qed
next
  case (ev\<^sub>e_apply v \<Delta>' \<C>' r' \<V> \<Delta> \<C> r s)
  thus ?case
  proof (cases "\<C> = []")
    case True
    with ev\<^sub>e_apply have "tco_state (S\<^sub>e (v # Lam\<^sub>e \<Delta>' \<C>' r' # \<V>) ((\<Delta>, Apply\<^sub>e # \<C>, r) # s)) \<leadsto>\<^sub>e
      tco_state (S\<^sub>e \<V> ((v # \<Delta>', \<C>', r') # (\<Delta>, \<C>, r) # s))" by auto
    thus ?thesis by (metis iter_one)
  next
    case False
    with ev\<^sub>e_apply have "tco_state (S\<^sub>e (v # Lam\<^sub>e \<Delta>' \<C>' r' # \<V>) ((\<Delta>, Apply\<^sub>e # \<C>, r) # s)) \<leadsto>\<^sub>e 
      tco_state (S\<^sub>e \<V> ((v # \<Delta>', \<C>', r') # (\<Delta>, \<C>, r) # s))" 
      by (cases \<C> rule: tco_code.cases) simp_all
    thus ?thesis by (metis iter_one)
  qed
qed simp_all

lemma correctness\<^sub>t\<^sub>c\<^sub>o_iter: "iter (\<leadsto>\<^sub>e) \<Sigma> \<Sigma>' \<Longrightarrow> complete_lams_state \<Sigma> \<Longrightarrow> 
  iter (\<leadsto>\<^sub>e) (tco_state \<Sigma>) (tco_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: iter.induct)
  case (iter_step \<Sigma> \<Sigma>' \<Sigma>'')
  hence "iter (\<leadsto>\<^sub>e) (tco_state \<Sigma>') (tco_state \<Sigma>'')" by simp
  moreover from iter_step have "iter (\<leadsto>\<^sub>e) (tco_state \<Sigma>) (tco_state \<Sigma>')" by (metis correctness\<^sub>t\<^sub>c\<^sub>o)
  ultimately show ?case by (metis iter_append)
qed simp_all

text \<open>We now prove the reconstruction lemmas for completeness:\<close>

lemma [dest]: "(\<Delta>\<^sub>t\<^sub>c\<^sub>o, \<C>\<^sub>t\<^sub>c\<^sub>o, r\<^sub>t\<^sub>c\<^sub>o) = tco_frame f\<^sub>e \<Longrightarrow> \<exists>\<Delta>\<^sub>e \<C>\<^sub>e r\<^sub>e. f\<^sub>e = (\<Delta>\<^sub>e, \<C>\<^sub>e, r\<^sub>e) \<and> 
    \<Delta>\<^sub>t\<^sub>c\<^sub>o = map tco_val \<Delta>\<^sub>e \<and> \<C>\<^sub>t\<^sub>c\<^sub>o = tco_code \<C>\<^sub>e \<and> r\<^sub>t\<^sub>c\<^sub>o = tco_return \<C>\<^sub>e r\<^sub>e"
  by (induction f\<^sub>e) simp_all

lemma [dest]: "f\<^sub>t\<^sub>c\<^sub>o # s\<^sub>t\<^sub>c\<^sub>o = tco_stack s\<^sub>e \<Longrightarrow> \<exists>s\<^sub>e\<^sub>1 s\<^sub>e\<^sub>2 f\<^sub>e. s\<^sub>e = s\<^sub>e\<^sub>1 @ f\<^sub>e # s\<^sub>e\<^sub>2 \<and> 
  list_all dead_frame (map tco_frame s\<^sub>e\<^sub>1) \<and> f\<^sub>t\<^sub>c\<^sub>o = tco_frame f\<^sub>e \<and> s\<^sub>t\<^sub>c\<^sub>o = tco_stack s\<^sub>e\<^sub>2"
proof (induction s\<^sub>e)
  case (Cons f\<^sub>e s\<^sub>e)
  thus ?case
  proof (cases "dead_frame (tco_frame f\<^sub>e)")
    case True
    with Cons obtain s\<^sub>e\<^sub>1 s\<^sub>e\<^sub>2 f\<^sub>e' where "s\<^sub>e = s\<^sub>e\<^sub>1 @ f\<^sub>e' # s\<^sub>e\<^sub>2 \<and> list_all dead_frame (map tco_frame s\<^sub>e\<^sub>1) \<and> 
      f\<^sub>t\<^sub>c\<^sub>o = tco_frame f\<^sub>e' \<and> s\<^sub>t\<^sub>c\<^sub>o = tco_stack s\<^sub>e\<^sub>2" by auto
    with True have "f\<^sub>e # s\<^sub>e = (f\<^sub>e # s\<^sub>e\<^sub>1) @ f\<^sub>e' # s\<^sub>e\<^sub>2 \<and> list_all dead_frame (map tco_frame (f\<^sub>e # s\<^sub>e\<^sub>1)) \<and> 
      f\<^sub>t\<^sub>c\<^sub>o = tco_frame f\<^sub>e' \<and> s\<^sub>t\<^sub>c\<^sub>o = tco_stack s\<^sub>e\<^sub>2" by simp
    thus ?thesis by blast
  next
    case False
    with Cons have "f\<^sub>e # s\<^sub>e = [] @ f\<^sub>e # s\<^sub>e \<and> list_all dead_frame (map tco_frame []) \<and> 
      f\<^sub>t\<^sub>c\<^sub>o = tco_frame f\<^sub>e \<and> s\<^sub>t\<^sub>c\<^sub>o = tco_stack s\<^sub>e" by simp
    thus ?thesis by blast
  qed
qed simp_all

lemma [dest]: "S\<^sub>e \<V>\<^sub>t\<^sub>c\<^sub>o s\<^sub>t\<^sub>c\<^sub>o = tco_state \<Sigma>\<^sub>e \<Longrightarrow> 
    \<exists>\<V>\<^sub>e s\<^sub>e. \<Sigma>\<^sub>e = S\<^sub>e \<V>\<^sub>e s\<^sub>e \<and> \<V>\<^sub>t\<^sub>c\<^sub>o = map tco_val \<V>\<^sub>e \<and> s\<^sub>t\<^sub>c\<^sub>o = tco_stack s\<^sub>e"
  by (induction \<Sigma>\<^sub>e) simp_all

text \<open>Completeness then follows:\<close>

theorem complete\<^sub>t\<^sub>c\<^sub>o [simp]: "tco_state \<Sigma>\<^sub>e \<leadsto>\<^sub>e \<Sigma>\<^sub>t\<^sub>c\<^sub>o' \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>e'. iter (\<leadsto>\<^sub>e) \<Sigma>\<^sub>e \<Sigma>\<^sub>e' \<and> \<Sigma>\<^sub>t\<^sub>c\<^sub>o' = tco_state \<Sigma>\<^sub>e'"
proof (induction "tco_state \<Sigma>\<^sub>e" \<Sigma>\<^sub>t\<^sub>c\<^sub>o' rule: eval\<^sub>e.induct)
  case (ev\<^sub>e_lookup \<Delta>\<^sub>t\<^sub>c\<^sub>o x v \<V>\<^sub>t\<^sub>c\<^sub>o \<C>\<^sub>t\<^sub>c\<^sub>o r\<^sub>t\<^sub>c\<^sub>o s\<^sub>t\<^sub>c\<^sub>o)
  then obtain \<V>\<^sub>e s\<^sub>e\<^sub>1 s\<^sub>e\<^sub>2 \<Delta>\<^sub>e \<C>\<^sub>e r\<^sub>e where "\<Sigma>\<^sub>e = S\<^sub>e \<V>\<^sub>e (s\<^sub>e\<^sub>1 @ (\<Delta>\<^sub>e, \<C>\<^sub>e, r\<^sub>e) # s\<^sub>e\<^sub>2) \<and> \<V>\<^sub>t\<^sub>c\<^sub>o = map tco_val \<V>\<^sub>e \<and> 
    list_all dead_frame (map tco_frame s\<^sub>e\<^sub>1) \<and> \<Delta>\<^sub>t\<^sub>c\<^sub>o = map tco_val \<Delta>\<^sub>e \<and> Lookup\<^sub>e x # \<C>\<^sub>t\<^sub>c\<^sub>o = tco_code \<C>\<^sub>e \<and> 
      r\<^sub>t\<^sub>c\<^sub>o = tco_return \<C>\<^sub>e r\<^sub>e \<and> s\<^sub>t\<^sub>c\<^sub>o = tco_stack s\<^sub>e\<^sub>2" by fast



  have "iter (\<leadsto>\<^sub>e) \<Sigma>\<^sub>e \<Sigma>\<^sub>e' \<and> S\<^sub>e (v # \<V>\<^sub>t\<^sub>c\<^sub>o) ((\<Delta>\<^sub>t\<^sub>c\<^sub>o, \<C>\<^sub>t\<^sub>c\<^sub>o, r\<^sub>t\<^sub>c\<^sub>o) # s\<^sub>t\<^sub>c\<^sub>o) = tco_state \<Sigma>\<^sub>e'" by simp
  thus ?case by blast
next
  case (ev\<^sub>e_pushcon \<V>\<^sub>t\<^sub>c\<^sub>o \<Delta>\<^sub>t\<^sub>c\<^sub>o n \<C>\<^sub>t\<^sub>c\<^sub>o r\<^sub>t\<^sub>c\<^sub>o s\<^sub>t\<^sub>c\<^sub>o)
  then obtain \<V>\<^sub>e s\<^sub>e\<^sub>1 s\<^sub>e\<^sub>2 f\<^sub>e where "\<Sigma>\<^sub>e = S\<^sub>e \<V>\<^sub>e (s\<^sub>e\<^sub>1 @ f\<^sub>e # s\<^sub>e\<^sub>2) \<and> \<V>\<^sub>t\<^sub>c\<^sub>o = map tco_val \<V>\<^sub>e \<and> 
    list_all dead_frame (map tco_frame s\<^sub>e\<^sub>1) \<and> (\<Delta>\<^sub>t\<^sub>c\<^sub>o, PushCon\<^sub>e n # \<C>\<^sub>t\<^sub>c\<^sub>o, r\<^sub>t\<^sub>c\<^sub>o) = tco_frame f\<^sub>e \<and> 
      s\<^sub>t\<^sub>c\<^sub>o = tco_stack s\<^sub>e\<^sub>2" by blast

  then show ?case by simp
next
  case (ev\<^sub>e_pushlam \<V>\<^sub>t\<^sub>c\<^sub>o \<Delta>\<^sub>t\<^sub>c\<^sub>o \<C>' r' \<C>\<^sub>t\<^sub>c\<^sub>o r\<^sub>t\<^sub>c\<^sub>o s\<^sub>t\<^sub>c\<^sub>o)
  then obtain \<V>\<^sub>e s\<^sub>e\<^sub>1 s\<^sub>e\<^sub>2 f\<^sub>e where "\<Sigma>\<^sub>e = S\<^sub>e \<V>\<^sub>e (s\<^sub>e\<^sub>1 @ f\<^sub>e # s\<^sub>e\<^sub>2) \<and> \<V>\<^sub>t\<^sub>c\<^sub>o = map tco_val \<V>\<^sub>e \<and> 
    list_all dead_frame (map tco_frame s\<^sub>e\<^sub>1) \<and> (\<Delta>\<^sub>t\<^sub>c\<^sub>o, PushLam\<^sub>e \<C>' r' # \<C>\<^sub>t\<^sub>c\<^sub>o, r\<^sub>t\<^sub>c\<^sub>o) = tco_frame f\<^sub>e \<and> 
      s\<^sub>t\<^sub>c\<^sub>o = tco_stack s\<^sub>e\<^sub>2" by blast

  then show ?case by simp
next
  case (ev\<^sub>e_apply v \<Delta>' \<C>' r' \<V>\<^sub>t\<^sub>c\<^sub>o \<Delta>\<^sub>t\<^sub>c\<^sub>o \<C>\<^sub>t\<^sub>c\<^sub>o r\<^sub>t\<^sub>c\<^sub>o s\<^sub>t\<^sub>c\<^sub>o)
  then obtain \<V>\<^sub>e s\<^sub>e\<^sub>1 s\<^sub>e\<^sub>2 f\<^sub>e where "\<Sigma>\<^sub>e = S\<^sub>e \<V>\<^sub>e (s\<^sub>e\<^sub>1 @ f\<^sub>e # s\<^sub>e\<^sub>2) \<and> (v # Lam\<^sub>e \<Delta>' \<C>' r' # \<V>\<^sub>t\<^sub>c\<^sub>o) = map tco_val \<V>\<^sub>e \<and> 
    list_all dead_frame (map tco_frame s\<^sub>e\<^sub>1) \<and> (\<Delta>\<^sub>t\<^sub>c\<^sub>o, Apply\<^sub>e # \<C>\<^sub>t\<^sub>c\<^sub>o, r\<^sub>t\<^sub>c\<^sub>o) = tco_frame f\<^sub>e \<and> 
      s\<^sub>t\<^sub>c\<^sub>o = tco_stack s\<^sub>e\<^sub>2" by blast

  then show ?case by simp
next
  case (ev\<^sub>e_return \<V>\<^sub>t\<^sub>c\<^sub>o \<Delta>\<^sub>t\<^sub>c\<^sub>o s\<^sub>t\<^sub>c\<^sub>o)
  then obtain \<V>\<^sub>e s\<^sub>e\<^sub>1 s\<^sub>e\<^sub>2 f\<^sub>e where "\<Sigma>\<^sub>e = S\<^sub>e \<V>\<^sub>e (s\<^sub>e\<^sub>1 @ f\<^sub>e # s\<^sub>e\<^sub>2) \<and> \<V>\<^sub>t\<^sub>c\<^sub>o = map tco_val \<V>\<^sub>e \<and> 
    list_all dead_frame (map tco_frame s\<^sub>e\<^sub>1) \<and> (\<Delta>\<^sub>t\<^sub>c\<^sub>o, [], Return\<^sub>e) = tco_frame f\<^sub>e \<and> 
      s\<^sub>t\<^sub>c\<^sub>o = tco_stack s\<^sub>e\<^sub>2" by blast

  then show ?case by simp
next
  case (ev\<^sub>e_jump v \<Delta>' \<C>' r' \<V>\<^sub>t\<^sub>c\<^sub>o \<Delta>\<^sub>t\<^sub>c\<^sub>o s\<^sub>t\<^sub>c\<^sub>o)
  then obtain \<V>\<^sub>e s\<^sub>e\<^sub>1 s\<^sub>e\<^sub>2 f\<^sub>e where "\<Sigma>\<^sub>e = S\<^sub>e \<V>\<^sub>e (s\<^sub>e\<^sub>1 @ f\<^sub>e # s\<^sub>e\<^sub>2) \<and> (v # Lam\<^sub>e \<Delta>' \<C>' r' # \<V>\<^sub>t\<^sub>c\<^sub>o) = map tco_val \<V>\<^sub>e \<and> 
    list_all dead_frame (map tco_frame s\<^sub>e\<^sub>1) \<and> (\<Delta>\<^sub>t\<^sub>c\<^sub>o, [], Jump\<^sub>e) = tco_frame f\<^sub>e \<and> 
      s\<^sub>t\<^sub>c\<^sub>o = tco_stack s\<^sub>e\<^sub>2" by blast

  then show ?case by simp
qed

(*
lemma [simp]: "cd \<noteq> [] \<Longrightarrow> tco_r (op # cd) = tco_r cd"
  by (induction op) (simp_all split: list.splits)

lemma tco_r_append [simp]: "cd' \<noteq> [] \<Longrightarrow> tco_r (cd @ cd') = tco_r cd'"
  by (induction cd) simp_all

lemma [simp]: "cd \<noteq> [] \<Longrightarrow> cd' \<noteq> [] \<Longrightarrow> tco_cd (cd @ cd') \<noteq> []"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "(env, cd, r) # sfs = tco_stack sfs' \<Longrightarrow> \<exists>dsfs env' cd' sfs''. 
  sfs' = dsfs @ (env', cd') # sfs'' \<and> env = map tco_val env' \<and> cd = tco_cd cd' \<and> 
    r = tco_r cd' \<and> list_all dead_frame dsfs \<and> sfs = tco_stack sfs''"
proof (induction sfs')
  case (Cons sf sfs')
  thus ?case
  proof (induction sf)
    case (Pair env' cd')
    thus ?case
    proof (induction cd' rule: tco_cd.induct)
      case 1
      then obtain dsfs env'' cd' sfs'' where X: "sfs' = dsfs @ (env'', cd') # sfs'' \<and> 
        env = map tco_val env'' \<and> cd = tco_cd cd' \<and> r = tco_r cd' \<and> list_all dead_frame dsfs \<and> 
          sfs = tco_stack sfs''" by auto
      hence "\<exists>dsfsx. (env', []) # dsfs @ (env'', cd') # sfs'' = dsfsx @ (env'', cd') # sfs'' \<and> 
          list_all dead_frame dsfsx \<and> sfs = tco_stack sfs''" by simp
      hence "\<exists>dsfsx sfs'''. 
        (env', []) # dsfs @ (env'', cd') # sfs'' = dsfsx @ (env'', cd') # sfs''' \<and> 
          list_all dead_frame dsfsx \<and> sfs = tco_stack sfs'''" by fastforce
      with X show ?case by fastforce
    next
      case (2 x cd')
      hence "env = map tco_val env' \<and> cd = Lookup\<^sub>e x # tco_cd cd' \<and> r = tco_r cd' \<and> 
        sfs = tco_stack sfs'" by simp
      thus ?case by fastforce
    next
      case (3 k cd')
      hence "env = map tco_val env' \<and> cd = PushCon\<^sub>e k # tco_cd cd' \<and> r = tco_r cd' \<and> 
        sfs = tco_stack sfs'" by simp
      thus ?case by fastforce
    next
      case (4 cd\<^sub>e cd')
      hence "env = map tco_val env' \<and> cd = PushLam\<^sub>e (tco_cd cd\<^sub>e) (tco_r cd\<^sub>e) # tco_cd cd' \<and> 
        r = tco_r cd' \<and> sfs = tco_stack sfs'" by simp
      thus ?case by fastforce
    next
      case (5 cd')
      thus ?case
      proof (cases cd')
        case Nil
        moreover with 5 have "env = map tco_val env' \<and> cd = [] \<and> r = Jump\<^sub>e \<and> sfs = tco_stack sfs'" 
          by simp
        ultimately show ?thesis by fastforce
      next
        case (Cons op cd'')
        moreover with 5 have "env = map tco_val env' \<and> cd = Apply\<^sub>e # tco_cd (op # cd'') \<and> 
          r = tco_r (op # cd'') \<and> sfs = tco_stack sfs'" by simp
        ultimately show ?thesis by fastforce
      qed
    qed
  qed
qed simp_all

lemma [dest]: "S\<^sub>e vs ((env, cd, r) # sfs) = tco_state \<Sigma> \<Longrightarrow> \<exists>dsfs vs' env' cd' sfs'. 
  \<Sigma> = S\<^sub>e vs' (dsfs @ (env', cd') # sfs') \<and> vs = map tco_val vs' \<and> env = map tco_val env' \<and> 
    cd = tco_cd cd' \<and> r = tco_r cd' \<and> list_all dead_frame dsfs \<and> sfs = tco_stack sfs'"
  by (induction \<Sigma>) auto

lemma [dest]: "Lookup\<^sub>e x # cd = tco_cd cd' \<Longrightarrow> \<exists>cd''. cd' = Lookup\<^sub>e x # cd'' \<and> cd = tco_cd cd''"
  by (induction cd' rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "PushCon\<^sub>e k # cd = tco_cd cd' \<Longrightarrow> \<exists>cd''. cd' = PushCon\<^sub>e k # cd'' \<and> cd = tco_cd cd''"
  by (induction cd' rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "PushLam\<^sub>e cd' r # cd = tco_cd cd\<^sub>t \<Longrightarrow> \<exists>cd\<^sub>t' cd\<^sub>t''. cd\<^sub>t = PushLam\<^sub>e cd\<^sub>t'' # cd\<^sub>t' \<and> 
    cd = tco_cd cd\<^sub>t' \<and> r = tco_r cd\<^sub>t'' \<and> cd' = tco_cd cd\<^sub>t''"
  by (induction cd\<^sub>t rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "Apply\<^sub>e # cd = tco_cd cd' \<Longrightarrow> 
    \<exists>op cd''. cd' = Apply\<^sub>e # op # cd'' \<and> cd = tco_cd (op # cd'')"
  by (induction cd' rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "Const\<^sub>e k = tco_val v \<Longrightarrow> v = Const\<^sub>e k"
  by (induction v) simp_all

lemma [dest]: "Lam\<^sub>e env cd r = tco_val v \<Longrightarrow> 
    \<exists>env\<^sub>t cd\<^sub>t. v = Lam\<^sub>e env\<^sub>t cd\<^sub>t \<and> env = map tco_val env\<^sub>t \<and> cd = tco_cd cd\<^sub>t \<and> r = tco_r cd\<^sub>t"
  by (induction v) simp_all

lemma [dest]: "Return\<^sub>e = tco_r cd \<Longrightarrow> [] = tco_cd cd \<Longrightarrow> cd = []"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

lemma [dest]: "Jump\<^sub>e = tco_r cd \<Longrightarrow> [] = tco_cd cd \<Longrightarrow> cd = [Apply\<^sub>e]"
  by (induction cd rule: tco_cd.induct) (simp_all split: list.splits)

lemma [simp]: "list_all dead_frame dsfs \<Longrightarrow> iter (\<leadsto>\<^sub>e) (S\<^sub>e vs (dsfs @ sfs)) (S\<^sub>e vs sfs)"
proof (induction dsfs)
  case (Cons sf dsfs)
  then obtain vs' where "sf = (vs', [])" by (cases sf) simp_all
  hence "S\<^sub>e vs ((sf # dsfs) @ sfs) \<leadsto>\<^sub>e S\<^sub>e vs (dsfs @ sfs)" by simp
  with Cons show ?case by simp
qed simp_all

lemma [simp]: "\<not> live_frame fr \<Longrightarrow> iter (\<leadsto>\<^sub>e) (S\<^sub>e vs (fr # sfs)) (S\<^sub>e vs sfs)"
proof (induction fr rule: live_frame.induct)
  case (1 env)
  hence "S\<^sub>e vs ((env, [], Return\<^sub>e) # sfs) \<leadsto>\<^sub>e S\<^sub>e vs sfs" by simp
  thus ?case by (metis iter_one)
qed simp_all

lemma [simp]: "tco_cd (op # cd) = [] \<Longrightarrow> tco_r (op # cd) = Jump\<^sub>e"
  by (induction op) (simp_all split: list.splits)

lemma [simp]: "live_frame (env, cd, Jump\<^sub>e)"
  by (induction cd) simp_all

lemma tco_never_dead [simp]: "live_frame (env, tco_cd (op # cd), tco_r (op # cd))"
  by (induction op) (simp_all split: list.splits)
*)

end