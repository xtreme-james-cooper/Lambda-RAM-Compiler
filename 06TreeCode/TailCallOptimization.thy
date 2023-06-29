theory TailCallOptimization
  imports TreeCodeConversion "../00Utils/Iteration"
begin

subsection \<open>Tail-Call Optimization\<close>

text \<open>A tail-call is a function call that takes place at the very end of another function's body. 
The significance of this becomes clear when you consider the naive execution of such a function. The 
last thing the outer function does before it returns is to call the inner function; then, when the 
inner function returns, the outer function returns immediately after. The outer function's stack 
frame remains in the stack the whole time the inner function is executing, despite the fact that it 
will never be needed again. Tail-call optimization changes the push into the inner function into a 
_jump_ to the inner function, replacing the one frame with the other - the call stack is shorter, 
and execution is quicker too, since the effort of preserving and then popping the outer frame is 
avoided. When applied systematically the effect can be quite great: notably, recursive functions 
that only make recursive calls in tail-position ("tail-recursive functions") can be executed in 
constant space, just like an imperative loop. This improvement is precisely what we added the 
\<open>Jump\<^sub>e\<close> instruction to express.\<close>

text \<open>What exactly do we change with tail-call optimization? We replace every sequence of an
\<open>Apply\<^sub>e\<close> followed by a \<open>Return\<^sub>e\<close> with a \<open>Jump\<^sub>e\<close>, obviously. But we also can eliminate any number of 
intervening \<open>PopEnv\<^sub>e\<close>s, since a pop followed by a return is just a return; and thanks to our 
let-floating phase, we know that _every_ \<open>PopEnv\<^sub>e\<close> occurs just before a \<open>Return\<^sub>e\<close>, so we can 
eliminate them all. We also eliminate certain frames from the call stack: specifically, any frame 
that consists nothing but a sequence of \<open>PopEnv\<^sub>e\<close>s followed by a \<open>Return\<^sub>e\<close>. We mark these frames as 
\<open>dead_frame\<close>s.\<close>

fun dead_code :: "code\<^sub>e list \<Rightarrow> bool" where
  "dead_code [] = False"
| "dead_code (Return\<^sub>e # \<C>) = (\<C> = [])"
| "dead_code (PopEnv\<^sub>e # \<C>) = dead_code \<C>"
| "dead_code (op # \<C>) = False"

primrec dead_frame :: "frame\<^sub>e \<Rightarrow> bool" where
  "dead_frame (\<V>, \<C>) = dead_code \<C>"

text \<open>The optimization itself is simple: we convert the code, eliminating 
\<open>Apply\<^sub>e; PopEnv\<^sub>e ... PopEnv\<^sub>e ; Return\<^sub>e\<close>s, then map the conversion up through the levels of the state, 
taking care to also eliminate the dead frames in the stack:\<close>

fun tco_code :: "code\<^sub>e list \<Rightarrow> code\<^sub>e list" where
  "tco_code [] = []"
| "tco_code (Apply\<^sub>e # \<C>) = (if dead_code \<C> then [Jump\<^sub>e] else Apply\<^sub>e # tco_code \<C>)"
| "tco_code (PushLam\<^sub>e \<C>' # \<C>) = PushLam\<^sub>e (tco_code \<C>') # tco_code \<C>"
| "tco_code (op # \<C>) = op # tco_code \<C>"

primrec tco_val :: "closure\<^sub>e \<Rightarrow> closure\<^sub>e" where
  "tco_val (Const\<^sub>e n) = Const\<^sub>e n"
| "tco_val (Lam\<^sub>e \<Delta> \<C>) = Lam\<^sub>e (map tco_val \<Delta>) (tco_code \<C>)"

fun tco_frame :: "frame\<^sub>e \<Rightarrow> frame\<^sub>e" where
  "tco_frame (\<Delta>, \<C>) = (map tco_val \<Delta>, tco_code \<C>)"

abbreviation tco_stack :: "frame\<^sub>e list \<Rightarrow> frame\<^sub>e list" where
  "tco_stack s \<equiv> filter (\<lambda>f. \<not> dead_frame f) (map tco_frame s)"

primrec tco_state :: "state\<^sub>e \<Rightarrow> state\<^sub>e" where
  "tco_state (S\<^sub>e \<V> s) = S\<^sub>e (map tco_val \<V>) (tco_stack s)"

lemma tco_to_empty [simp]: "(tco_code \<C> = []) = (\<C> = [])"
  by (induction \<C> rule: tco_code.induct) simp_all

lemma tco_to_return [simp]: "dead_code (tco_code \<C>) = dead_code \<C>"
  by (induction \<C> rule: tco_code.induct) simp_all

lemma tco_to_dead_frame [simp]: "dead_frame (\<Delta>, tco_code \<C>) = dead_code \<C>"
  by (induction \<C> rule: tco_code.induct) simp_all

lemma tco_frame_to_dead_frame [simp]: "dead_frame (tco_frame f) = dead_frame f"
  by (induction f) simp_all

lemma tco_to_dead_frame_apply [simp]: "dead_frame (map tco_val \<Delta>, tco_code (Apply\<^sub>e # \<C>)) = False"
proof (induction \<C> rule: tco_code.induct)
  case ("4_3" \<C>)
  thus ?case by (cases \<C>) simp_all
qed simp_all

lemma dead_code_terminated [simp]: "dead_code \<C> \<Longrightarrow> properly_terminated\<^sub>e \<C>"
  by (induction \<C> rule: dead_code.induct) simp_all

lemma tcoed_code_terminated [simp]: "properly_terminated\<^sub>e (tco_code \<C>) = properly_terminated\<^sub>e \<C>"
  by (induction \<C> rule: tco_code.induct) simp_all

text \<open>We will of course prove that tail-call removal is semantics-preserving, but we will not 
formally prove that it really is "an optimization". Instead, we will prove some much simpler results 
that indicate _why_ it is an optimization, and gesture towards what a full proof would need to 
formalize.\<close>

text \<open>The optimized code is always shorter. Since tail-call removal is a local optimization, leaving 
the global structure of the computation intact, any codeblock executed without it will be executed 
with it as well. Assuming that each operation takes roughly equal time, this means that tail-call 
optimization reduces runtime. (In fact, we will see much later that \<open>Jump\<^sub>e\<close> is shorter to run as 
machine code than the \<open>Apply\<^sub>e; Return\<^sub>e\<close> sequence, so we do even better. But we're not there yet.)\<close>

theorem tco_always_shorter_code [simp]: "length (tco_code \<C>) \<le> length \<C>"
  by (induction \<C> rule: tco_code.induct) simp_all

text \<open>The value stack - what we might consider something like a proxy for the heap usage - is 
unchanged by tail-call removal. But the call stack, which remains the call stack throughout 
compilation, is made shorter:\<close>

primrec get_callstack :: "state\<^sub>e \<Rightarrow> frame\<^sub>e list" where
  "get_callstack (S\<^sub>e \<V> s) = s"

theorem tco_always_smaller_stack [simp]: "
    length (get_callstack (tco_state \<Sigma>)) \<le> length (get_callstack \<Sigma>)"
  by (induction \<Sigma>) simp_all

text \<open>Correctness is the easier proof for this pass. First off, we need some auxiliary functions to 
express that no \<open>PushLam\<^sub>e\<close> contains code for a dead frame, and every return is a \<open>Return\<^sub>e\<close> (as will
always be the case, pre-optimization).\<close>

fun complete_lams :: "code\<^sub>e list \<Rightarrow> bool" where
  "complete_lams [] = False"
| "complete_lams (PushLam\<^sub>e \<C>' # \<C>) = (\<not> dead_code \<C>' \<and> complete_lams \<C>' \<and> complete_lams \<C>)"
| "complete_lams (Return\<^sub>e # \<C>) = (\<C> = [])"
| "complete_lams (Jump\<^sub>e # \<C>) = False"
| "complete_lams (op # \<C>) = complete_lams \<C>"

primrec complete_lams_val :: "closure\<^sub>e \<Rightarrow> bool" where
  "complete_lams_val (Const\<^sub>e n) = True"
| "complete_lams_val (Lam\<^sub>e \<Delta> \<C>) = (\<not> dead_code \<C> \<and> list_all complete_lams_val \<Delta> \<and> complete_lams \<C>)"

fun complete_lams_frame :: "frame\<^sub>e \<Rightarrow> bool" where
  "complete_lams_frame (\<Delta>, \<C>) = (list_all complete_lams_val \<Delta> \<and> complete_lams \<C>)"

primrec complete_lams_state :: "state\<^sub>e \<Rightarrow> bool" where
  "complete_lams_state (S\<^sub>e \<V> s) = (list_all complete_lams_val \<V> \<and> list_all complete_lams_frame s)"

lemma complete_lams_apply [simp]: "complete_lams (e @ [Apply\<^sub>e, Return\<^sub>e]) = 
    complete_lams (e @ [Return\<^sub>e])"
  by (induction e rule: complete_lams.induct) simp_all

lemma complete_lams_append [simp]: "complete_lams (e\<^sub>1 @ [Return\<^sub>e]) \<Longrightarrow> 
    complete_lams (e\<^sub>2 @ [Return\<^sub>e]) \<Longrightarrow> complete_lams (e\<^sub>1 @ e\<^sub>2 @ [Apply\<^sub>e, Return\<^sub>e])"
  by (induction e\<^sub>1 rule: complete_lams.induct) simp_all

lemma encode_complete_lams [simp]: "complete_lams (encode e)"
  by (induction e) (auto simp add: encode_def)

lemma eval_complete_lams [simp]: "\<Sigma> \<leadsto>\<^sub>e \<Sigma>' \<Longrightarrow> complete_lams_state \<Sigma> \<Longrightarrow> complete_lams_state \<Sigma>'"
  by (induction \<Sigma> \<Sigma>' rule: eval\<^sub>e.induct) (auto split: if_splits)

lemma tco_not_to_jump [simp]: "\<C> \<noteq> [Return\<^sub>e] \<Longrightarrow> complete_lams \<C> \<Longrightarrow> 
    tco_code (Apply\<^sub>e # \<C>) = Apply\<^sub>e # tco_code \<C>"
  by (induction \<C> rule: tco_code.induct) simp_all

text \<open>The \<open>iter (\<leadsto>\<^sub>e)\<close> in correctness is unusual, in that it doesn't merely mean one-or-more 
evaluation steps, or zero-or-one, but either: clearing a dead stack frame incorporates an extra step 
in every case except \<open>ev\<^sub>e_return\<close>, where the optimization pass has already cleared the dead frame 
for us and it takes no steps. It may seem odd that the optimized code requires two steps where the 
original code needed one, but what is actually happening is the "missing" steps from the 
\<open>ev\<^sub>e_return\<close> are being moved there; we are still reducing the number of steps steps in total.\<close>

theorem correctness\<^sub>t\<^sub>c\<^sub>o: "\<Sigma> \<leadsto>\<^sub>e \<Sigma>' \<Longrightarrow> complete_lams_state \<Sigma> \<Longrightarrow> 
  iter (\<leadsto>\<^sub>e) (tco_state \<Sigma>) (tco_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>e.induct)
  case (ev\<^sub>e_lookup \<Delta> x v \<V> \<C> s)
  thus ?case
  proof (cases "\<C> = [Return\<^sub>e]")
    case True
    with ev\<^sub>e_lookup have  "
      S\<^sub>e (tco_val v # map tco_val \<V>) ((map tco_val \<Delta>, tco_code \<C>) # tco_stack s) \<leadsto>\<^sub>e
        S\<^sub>e (tco_val v # map tco_val \<V>) (tco_stack s)" by simp
    moreover from ev\<^sub>e_lookup have "
      S\<^sub>e (map tco_val \<V>) ((map tco_val \<Delta>, Lookup\<^sub>e x # tco_code \<C>) # tco_stack s) \<leadsto>\<^sub>e
        S\<^sub>e (tco_val v # map tco_val \<V>) ((map tco_val \<Delta>, tco_code \<C>) # tco_stack s)"
      by simp
    ultimately have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (map tco_val \<V>) ((map tco_val \<Delta>, Lookup\<^sub>e x # tco_code \<C>) # 
      tco_stack s)) (S\<^sub>e (tco_val v # map tco_val \<V>) (tco_stack s))"
      by (metis (no_types, lifting) iter_refl iter_step)
    with ev\<^sub>e_lookup True show ?thesis by simp
  next
    case False
    with ev\<^sub>e_lookup have "tco_state (S\<^sub>e \<V> ((\<Delta>, Lookup\<^sub>e x # \<C>) # s)) \<leadsto>\<^sub>e
      tco_state (S\<^sub>e (v # \<V>) ((\<Delta>, \<C>) # s))" by auto
    thus ?thesis by (metis iter_one)
  qed
next
  case (ev\<^sub>e_pushcon \<V> \<Delta> n \<C> s)
  thus ?case
  proof (cases "\<C> = [Return\<^sub>e]")
    case True
    with ev\<^sub>e_pushcon have "
      S\<^sub>e (Const\<^sub>e n # map tco_val \<V>) ((map tco_val \<Delta>, tco_code \<C>) # tco_stack s) \<leadsto>\<^sub>e 
        S\<^sub>e (Const\<^sub>e n # map tco_val \<V>) (tco_stack s)" by simp
    moreover have "
      S\<^sub>e (map tco_val \<V>) ((map tco_val \<Delta>, PushCon\<^sub>e n # tco_code \<C>) # tco_stack s) \<leadsto>\<^sub>e 
        S\<^sub>e (Const\<^sub>e n # map tco_val \<V>) ((map tco_val \<Delta>, tco_code \<C>) # tco_stack s)"
      by simp
    ultimately have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (map tco_val \<V>) 
      ((map tco_val \<Delta>, PushCon\<^sub>e n # tco_code \<C>) # tco_stack s))
        (S\<^sub>e (Const\<^sub>e n # map tco_val \<V>) (tco_stack s))"
      by (metis (no_types, lifting) iter_refl iter_step)
    with ev\<^sub>e_pushcon True show ?thesis by simp
  next
    case False
    hence "tco_state (S\<^sub>e \<V> ((\<Delta>, PushCon\<^sub>e n # \<C>) # s)) \<leadsto>\<^sub>e tco_state (S\<^sub>e (Const\<^sub>e n # \<V>) ((\<Delta>, \<C>) # s))"
      by auto
    thus ?thesis by (metis iter_one)
  qed
next
  case (ev\<^sub>e_pushlam \<V> \<Delta> \<C>' \<C> s)
  thus ?case
  proof (cases "\<C> = [Return\<^sub>e]")
    case True
    with ev\<^sub>e_pushlam have "S\<^sub>e (Lam\<^sub>e (map tco_val \<Delta>) (tco_code \<C>') # map tco_val \<V>) 
      ((map tco_val \<Delta>, tco_code \<C>) # tco_stack s) \<leadsto>\<^sub>e 
      S\<^sub>e (Lam\<^sub>e (map tco_val \<Delta>) (tco_code \<C>') # map tco_val \<V>) (tco_stack s)" 
        by simp
    moreover have "S\<^sub>e (map tco_val \<V>) ((map tco_val \<Delta>, PushLam\<^sub>e (tco_code \<C>') # 
      tco_code \<C>) # tco_stack s) \<leadsto>\<^sub>e 
      S\<^sub>e (Lam\<^sub>e (map tco_val \<Delta>) (tco_code \<C>') # map tco_val \<V>) 
      ((map tco_val \<Delta>, tco_code \<C>) # tco_stack s)"
        by simp
      ultimately have "iter (\<leadsto>\<^sub>e) (S\<^sub>e (map tco_val \<V>) ((map tco_val \<Delta>, PushLam\<^sub>e (tco_code \<C>') # 
      tco_code \<C>) # tco_stack s))
      (S\<^sub>e (Lam\<^sub>e (map tco_val \<Delta>) (tco_code \<C>') # map tco_val \<V>) (tco_stack s))"
      by (metis (no_types, lifting) iter_refl iter_step)
    with ev\<^sub>e_pushlam True show ?thesis by simp
  next
    case False
    hence "tco_state (S\<^sub>e \<V> ((\<Delta>, PushLam\<^sub>e \<C>' # \<C>) # s)) \<leadsto>\<^sub>e 
      tco_state (S\<^sub>e (Lam\<^sub>e \<Delta> \<C>' # \<V>) ((\<Delta>, \<C>) # s))" by simp
    thus ?thesis by (metis iter_one)
  qed
next
  case (ev\<^sub>e_apply v \<Delta>' \<C>' \<V> \<Delta> \<C> s)
  thus ?case
  proof (cases "\<C> = [Return\<^sub>e]")
    case True
    with ev\<^sub>e_apply have "tco_state (S\<^sub>e (v # Lam\<^sub>e \<Delta>' \<C>' # \<V>) ((\<Delta>, Apply\<^sub>e # \<C>) # s)) \<leadsto>\<^sub>e
      tco_state (S\<^sub>e \<V> ((v # \<Delta>', \<C>') # (\<Delta>, \<C>) # s))" by simp
    thus ?thesis by (metis iter_one)
  next
    case False
    with ev\<^sub>e_apply have "tco_state (S\<^sub>e (v # Lam\<^sub>e \<Delta>' \<C>' # \<V>) ((\<Delta>, Apply\<^sub>e # \<C>) # s)) \<leadsto>\<^sub>e 
      tco_state (S\<^sub>e \<V> ((v # \<Delta>', \<C>') # (\<Delta>, \<C>) # s))" by simp
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

text \<open>Completeness would then follow, after the usual reconstruction lemmas. However, the way that 
optimized steps don't quite align with unoptimized steps mentioned above now comes back to bite, 
unpleasantly. Optimized evaluation may put us in a state that simply has no unoptimized equivalent; 
we have to sometimes take an additional optimized step to get back to matching states. The actual
statement would end up being 
  \<open>tco_state \<Sigma>\<^sub>e \<leadsto>\<^sub>e \<Sigma>\<^sub>t\<^sub>c\<^sub>o' \<Longrightarrow> 
    \<exists>\<Sigma>\<^sub>e'' \<Sigma>\<^sub>t\<^sub>c\<^sub>o''. iter (\<leadsto>\<^sub>e) \<Sigma>\<^sub>t\<^sub>c\<^sub>o' \<Sigma>\<^sub>t\<^sub>c\<^sub>o'' \<and> iter (\<leadsto>\<^sub>e) \<Sigma>\<^sub>e \<Sigma>\<^sub>e'' \<and> \<Sigma>\<^sub>t\<^sub>c\<^sub>o'' = tco_state \<Sigma>\<^sub>e''\<close>
with the first iter indicating zero-or-one, and the second one-or-more. Rather than deal with this
complication, we note that completeness is the only part of this that we need, and skip it. (We will 
later encounter the exact same evaluation-mismatch problem, and abandon completeness with the exact
same justification, when we move to assembly code in stage 12.)\<close>

end