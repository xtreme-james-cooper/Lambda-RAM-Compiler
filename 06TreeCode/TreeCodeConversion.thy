theory TreeCodeConversion
  imports TreeCode "../05Closure/Closure" "../00Utils/Iteration"
begin

primrec encode :: "expr\<^sub>d \<Rightarrow> tree_code list" where
  "encode (Var\<^sub>d x) = [TLookup x]"
| "encode (Const\<^sub>d k) = [TPushCon k]"
| "encode (Lam\<^sub>d t e) = [TPushLam (encode e)]"
| "encode (App\<^sub>d e\<^sub>1 e\<^sub>2) = encode e\<^sub>1 @ encode e\<^sub>2 @ [TApply]"

primrec encode_closure :: "closure\<^sub>c \<Rightarrow> tclosure" where
  "encode_closure (Const\<^sub>c k) = TConst k"
| "encode_closure (Lam\<^sub>c t cs e) = TLam (map encode_closure cs) (encode e)"

fun vals_from_stack :: "frame\<^sub>c list \<Rightarrow> tclosure list" where
  "vals_from_stack [] = []"
| "vals_from_stack (FApp1\<^sub>c cs e # s) = vals_from_stack s"
| "vals_from_stack (FApp2\<^sub>c c # s) = encode_closure c # vals_from_stack s"
| "vals_from_stack (FReturn\<^sub>c cs # s) = vals_from_stack s"

fun stack_from_stack :: "frame\<^sub>c list \<Rightarrow> tree_stack_frame list" where
  "stack_from_stack [] = []"
| "stack_from_stack (FApp1\<^sub>c cs e # s) = (case stack_from_stack s of
      [] \<Rightarrow> []
    | ((env, cd) # sfs) \<Rightarrow> (env, encode e @ TApply # cd) # sfs)"
| "stack_from_stack (FApp2\<^sub>c c # s) = (case stack_from_stack s of
      [] \<Rightarrow> []
    | ((env, cd) # sfs) \<Rightarrow> (env, TApply # cd) # sfs)"
| "stack_from_stack (FReturn\<^sub>c cs # s) = (map encode_closure cs, []) # stack_from_stack s"

primrec encode_state :: "state\<^sub>c \<Rightarrow> tree_code_state" where
  "encode_state (SE\<^sub>c s cs e) = 
    TS (vals_from_stack s) (case stack_from_stack s of 
        [] \<Rightarrow> []
      | ((env, cd) # sfs) \<Rightarrow> ((env, encode e @ cd) # sfs))"
| "encode_state (SC\<^sub>c s c) = 
    TS (encode_closure c # vals_from_stack s) (stack_from_stack s)"

primrec unzip :: "expr\<^sub>d \<Rightarrow> expr\<^sub>d \<times> expr\<^sub>d list" where
  "unzip (Var\<^sub>d x) = (Var\<^sub>d x, [])"
| "unzip (Const\<^sub>d k) = (Const\<^sub>d k, [])"
| "unzip (Lam\<^sub>d t e) = (Lam\<^sub>d t e, [])"
| "unzip (App\<^sub>d e\<^sub>1 e\<^sub>2) = (case unzip e\<^sub>1 of (e, es) \<Rightarrow> (e, e\<^sub>2 # es))"

primrec zip_encode :: "expr\<^sub>d list \<Rightarrow> tree_code list" where 
  "zip_encode [] = []"
| "zip_encode (e # es) = zip_encode es @ encode e @ [TApply]"

lemma [simp]: "full_block (encode e) n = Some (Suc n)"
  by (induction e arbitrary: n) simp_all

lemma [simp]: "list_all full_code_closure (encode e)"
  by (induction e) simp_all

lemma [simp]: "full_closure (encode_closure c)"
proof (induction c)
  case (Lam\<^sub>c t cs e)
  thus ?case using list_all_iff by fastforce
qed simp_all

lemma [simp]: "list_all full_closure (vals_from_stack s)"
  by (induction s rule: vals_from_stack.induct) simp_all

lemma full_frame_from_stack [simp]: "list_all full_frame (stack_from_stack s)"
proof (induction s rule: vals_from_stack.induct)
  case (2 cs e s)
  thus ?case
  proof (cases "stack_from_stack s")
    case (Cons envcd sfs)
    with 2 show ?thesis by (cases envcd) simp_all
  qed simp_all
next
  case (3 c s)
  thus ?case
  proof (cases "stack_from_stack s")
    case (Cons envcd sfs)
    with 3 show ?thesis by (cases envcd) simp_all
  qed simp_all
next
  case (4 cs s)
  thus ?case by (induction cs) simp_all
qed simp_all

lemma [simp]: "stack_from_stack s = (env, cd) # sfs \<Longrightarrow>
  list_all full_closure env \<and> list_all full_code_closure cd \<and> list_all full_frame sfs"
proof -
  assume "stack_from_stack s = (env, cd) # sfs"
  hence "list_all full_frame ((env, cd) # sfs)" by (metis full_frame_from_stack)
  thus ?thesis by simp
qed

lemma [simp]: "full_state (encode_state \<Sigma>)"
  by (induction \<Sigma>) (simp_all split: list.splits)

lemma [simp]: "encode e \<noteq> []"
  by (induction e) simp_all

lemma [simp]: "unzip e = (e', es) \<Longrightarrow> encode e' @ zip_encode es = encode e"
  by (induction e arbitrary: e' es) (auto split: prod.splits)

lemma [simp]: "vals_from_stack (map (FApp1\<^sub>c cs) (rev es) @ s) = vals_from_stack s"
  by (induction es arbitrary: s) simp_all

lemma [simp]: "stack_from_stack s = (env, cd) # sfs \<Longrightarrow> 
    stack_from_stack (map (FApp1\<^sub>c cs) (rev es) @ s) = (env, zip_encode es @ cd) # sfs"
  by (induction es arbitrary: s cd) simp_all

lemma [dest]: "encode e @ cd' = TLookup x # cd \<Longrightarrow> 
    (\<And>es. unzip e = (Var\<^sub>d x, es) \<Longrightarrow> cd = zip_encode es @ cd' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction e arbitrary: cd') fastforce+

lemma [dest]: "encode e @ cd' = TPushCon k # cd \<Longrightarrow> 
    (\<And>es. unzip e = (Const\<^sub>d k, es) \<Longrightarrow> cd = zip_encode es @ cd' \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction e arbitrary: cd') fastforce+

lemma encode_to_pushlam' [dest]: "encode e @ cd' = TPushLam cd'' # cd \<Longrightarrow> 
  (\<And>es t e'. unzip e = (Lam\<^sub>d t e', es) \<Longrightarrow> cd'' = encode e' \<Longrightarrow> cd = zip_encode es @ cd' \<Longrightarrow> 
    P) \<Longrightarrow> P"
  by (induction e arbitrary: cd') fastforce+

lemma [dest]: "encode e @ cd' = TApply # cd \<Longrightarrow> P"
  by (induction e arbitrary: cd') simp_all

lemma [dest]: "encode_closure c = TConst k \<Longrightarrow> c = Const\<^sub>c k"
  by (induction c) simp_all

lemma encode_lam_closure [dest]: "encode_closure c = TLam env cd \<Longrightarrow> (\<And>t cs e. 
    c = Lam\<^sub>c t cs e \<Longrightarrow> env = map encode_closure cs \<Longrightarrow> cd = encode e \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction c) simp_all

lemma tc_latest_environment [simp]: "s @ FApp1\<^sub>c cs e # s' :\<^sub>c t \<rightarrow> t' \<Longrightarrow> 
  latest_environment s' = Some cs"
proof (induction s arbitrary: t)
  case (Cons f s)
  moreover from Cons(2) obtain tt where "s @ FApp1\<^sub>c cs e # s' :\<^sub>c tt \<rightarrow> t'" 
    by (induction "(f # s) @ FApp1\<^sub>c cs e # s'" t t' rule: typing_stack\<^sub>c.induct) simp_all
  ultimately show ?case by simp
qed fastforce+

lemma encode_stack_to_lookup [dest]: "stack_from_stack s = (env, TLookup x # cd) # sfs \<Longrightarrow> 
  \<exists>cs e es s' cd'. s = FApp1\<^sub>c cs e # s' \<and> stack_from_stack s' = (env, cd') # sfs \<and> 
    unzip e = (Var\<^sub>d x, es) \<and> cd = zip_encode es @ TApply # cd'"
proof (induction s rule: stack_from_stack.induct)
  case (2 cs e s)
  then obtain cd' where "stack_from_stack s = (env, cd') # sfs \<and> 
    encode e @ TApply # cd' = TLookup x # cd" 
      by (cases "stack_from_stack s") (auto split: prod.splits)
  thus ?case by auto
qed (auto split: list.splits)

lemma encode_stack_to_pushcon [dest]: "stack_from_stack s = (env, TPushCon k # cd) # sfs \<Longrightarrow> 
  \<exists>cs e es s' cd'. s = FApp1\<^sub>c cs e # s' \<and> stack_from_stack s' = (env, cd') # sfs \<and> 
    unzip e = (Const\<^sub>d k, es) \<and> cd = zip_encode es @ TApply # cd'"
proof (induction s rule: stack_from_stack.induct)
  case (2 cs e s)
  then obtain cd' where "stack_from_stack s = (env, cd') # sfs \<and> 
    encode e @ TApply # cd' = TPushCon k # cd" 
      by (cases "stack_from_stack s") (auto split: prod.splits)
  thus ?case by auto
qed (auto split: list.splits)

lemma encode_stack_to_pushlam [dest]: "stack_from_stack s = (env, TPushLam cd' # cd) # sfs \<Longrightarrow> 
  \<exists>cs e es s' t e' cd''. s = FApp1\<^sub>c cs e # s' \<and> stack_from_stack s' = (env, cd'') # sfs \<and> 
    unzip e = (Lam\<^sub>d t e', es) \<and> cd = zip_encode es @ TApply # cd'' \<and> cd' = encode e'"
proof (induction s rule: stack_from_stack.induct)
  case (2 cs e s)
  then obtain cd'' where "stack_from_stack s = (env, cd'') # sfs \<and> 
    encode e @ TApply # cd'' = TPushLam cd' # cd" 
      by (cases "stack_from_stack s") (auto split: prod.splits)
  moreover then obtain t e' es where "unzip e = (Lam\<^sub>d t e', es) \<and> cd' = encode e' \<and> 
    cd = zip_encode es @ TApply # cd''" by (metis encode_to_pushlam')
  ultimately show ?case by fastforce
qed (auto split: list.splits)

lemma encode_stack_to_apply [dest]: "stack_from_stack s = (env, TApply # cd) # sfs \<Longrightarrow> 
    \<exists>s' c. s = FApp2\<^sub>c c # s' \<and> stack_from_stack s' = (env, cd) # sfs"
  by (induction s rule: stack_from_stack.induct) (auto split: list.splits)

lemma encode_stack_to_return [dest]: "stack_from_stack s = (env, []) # sfs \<Longrightarrow> 
  (s = [] \<and> env = [] \<and>  sfs = []) \<or> (\<exists>cs s'. s = FReturn\<^sub>c cs # s' \<and> env = map encode_closure cs \<and> 
    sfs = stack_from_stack s')"
  by (induction s rule: stack_from_stack.induct) (auto split: list.splits)

lemma encode_to_lookup [simp]: "encode_state \<Sigma> = TS vs ((env, TLookup x # cd) # sfs) \<Longrightarrow> 
  (\<exists>s cs e es cd'. \<Sigma> = SE\<^sub>c s cs e \<and> unzip e = (Var\<^sub>d x, es) \<and> 
    cd = zip_encode es @ cd' \<and> stack_from_stack s = ((env, cd') # sfs) \<and> 
      vs = vals_from_stack s) \<or> (\<exists>s c cs e es cd'. \<Sigma> = SC\<^sub>c (FApp1\<^sub>c cs e # s) c \<and> 
        unzip e = (Var\<^sub>d x, es) \<and> cd = zip_encode es @ TApply # cd' \<and> 
          stack_from_stack s = ((env, cd') # sfs) \<and> vs = encode_closure c # vals_from_stack s)"
proof (induction \<Sigma>)
  case (SE\<^sub>c s cs e)
  moreover then obtain cd' where "stack_from_stack s = (env, cd') # sfs \<and> 
    encode e @ cd' = TLookup x # cd" by (auto split: list.splits)
  ultimately show ?case by auto
qed auto

lemma encode_to_pushcon [simp]: "encode_state \<Sigma> = TS vs ((env, TPushCon k # cd) # sfs) \<Longrightarrow> 
  (\<exists>s cs e es cd'. \<Sigma> = SE\<^sub>c s cs e \<and> unzip e = (Const\<^sub>d k, es) \<and> 
    cd = zip_encode es @ cd' \<and> stack_from_stack s = ((env, cd') # sfs) \<and> 
      vs = vals_from_stack s) \<or> (\<exists>s c cs e es cd'. \<Sigma> = SC\<^sub>c (FApp1\<^sub>c cs e # s) c \<and> 
        unzip e = (Const\<^sub>d k, es) \<and> cd = zip_encode es @ TApply # cd' \<and> 
          stack_from_stack s = ((env, cd') # sfs) \<and> vs = encode_closure c # vals_from_stack s)"
proof (induction \<Sigma>)
  case (SE\<^sub>c s cs e)
  moreover then obtain cd' where "stack_from_stack s = (env, cd') # sfs \<and> 
    encode e @ cd' = TPushCon k # cd" by (auto split: list.splits)
  ultimately show ?case by auto
qed auto

lemma encode_to_pushlam [simp]: "encode_state \<Sigma> = TS vs ((env, TPushLam cd' # cd) # sfs) \<Longrightarrow> 
  (\<exists>s cs e es tt e' cd''. \<Sigma> = SE\<^sub>c s cs e \<and> unzip e = (Lam\<^sub>d tt e', es) \<and> 
    cd = zip_encode es @ cd'' \<and> cd' = encode e' \<and> vs = vals_from_stack s \<and> 
      stack_from_stack s = ((env, cd'') # sfs)) \<or> (\<exists>s c cs e es tt e' cd''. 
        \<Sigma> = SC\<^sub>c (FApp1\<^sub>c cs e # s) c \<and> unzip e = (Lam\<^sub>d tt e', es) \<and> 
          cd = zip_encode es @ TApply # cd'' \<and> cd' = encode e' \<and> 
            vs = encode_closure c # vals_from_stack s \<and> stack_from_stack s = ((env, cd'') # sfs))"
proof (induction \<Sigma>)
  case (SE\<^sub>c s cs e)
  moreover then obtain cd'' where "stack_from_stack s = (env, cd'') # sfs \<and> 
    encode e @ cd'' = TPushLam cd' # cd" by (auto split: list.splits)
  moreover then obtain es tt e' where "unzip e = (Lam\<^sub>d tt e', es) \<and> cd' = encode e' \<and> 
    cd = zip_encode es @ cd''" by (metis encode_to_pushlam')
  ultimately show ?case by auto
qed auto

lemma encode_to_apply [simp]: "encode_state \<Sigma> = TS vs ((env, TApply # cd) # sfs) \<Longrightarrow> 
  \<exists>s c c'. \<Sigma> = SC\<^sub>c (FApp2\<^sub>c c' # s) c \<and> stack_from_stack s = ((env, cd) # sfs) \<and> 
    vs = encode_closure c # encode_closure c' # vals_from_stack s"
  by (induction \<Sigma>) (auto split: list.splits)

lemma encode_to_return [simp]: "encode_state \<Sigma> = TS vs ((env, []) # sfs) \<Longrightarrow> 
  (\<exists>c. \<Sigma> = SC\<^sub>c [] c \<and> env = [] \<and> sfs = [] \<and> vs = [encode_closure c]) \<or> 
    (\<exists>cs s c. \<Sigma> = SC\<^sub>c (FReturn\<^sub>c cs # s) c \<and> sfs = stack_from_stack s \<and>
      env = map encode_closure cs \<and> vs = encode_closure c # vals_from_stack s)"
  by (induction \<Sigma>) (auto split: list.splits)

lemma [simp]: "unzip e = (e', es) \<Longrightarrow> 
  iter (\<leadsto>\<^sub>c) (SE\<^sub>c s cs e) (SE\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ s) cs e')"
proof (induction e arbitrary: s es)
  case (App\<^sub>d e1 e2)
  then obtain es' where "unzip e1 = (e', es') \<and> es = e2 # es'" by (auto split: prod.splits)
  moreover with App\<^sub>d have "iter (\<leadsto>\<^sub>c) (SE\<^sub>c (FApp1\<^sub>c cs e2 # s) cs e1) 
    (SE\<^sub>c (map (FApp1\<^sub>c cs) (rev (e2 # es')) @ s) cs e')" by simp
  moreover have "SE\<^sub>c s cs (App\<^sub>d e1 e2) \<leadsto>\<^sub>c SE\<^sub>c (FApp1\<^sub>c cs e2 # s) cs e1" by simp
  ultimately show ?case by (metis iter_step)
qed simp_all 

lemma [simp]: "stack_from_stack s = (env, cd) # sfs \<Longrightarrow> latest_environment s = Some cs \<Longrightarrow> 
    env = map encode_closure cs"
  by (induction s arbitrary: cd rule: latest_environment.induct) 
     (simp_all split: list.splits prod.splits)

theorem correctt [simp]: "encode_state \<Sigma>\<^sub>c \<leadsto>\<^sub>t \<Sigma>\<^sub>t' \<Longrightarrow> \<Sigma>\<^sub>c :\<^sub>c t \<Longrightarrow>
  \<exists>\<Sigma>\<^sub>c'. iter (\<leadsto>\<^sub>c) \<Sigma>\<^sub>c \<Sigma>\<^sub>c' \<and> \<Sigma>\<^sub>t' = encode_state \<Sigma>\<^sub>c'"
proof (induction "encode_state \<Sigma>\<^sub>c" \<Sigma>\<^sub>t' rule: evalt.induct)
  case (evt_lookup env x v vs cd sfs)
  moreover hence "(\<exists>s cs e es cd'. \<Sigma>\<^sub>c = SE\<^sub>c s cs e \<and> unzip e = (Var\<^sub>d x, es) \<and> 
    cd = zip_encode es @ cd' \<and> stack_from_stack s = ((env, cd') # sfs) \<and> 
      vs = vals_from_stack s) \<or> (\<exists>s c cs e es cd'. \<Sigma>\<^sub>c = SC\<^sub>c (FApp1\<^sub>c cs e # s) c \<and> 
        unzip e = (Var\<^sub>d x, es) \<and> cd = zip_encode es @ TApply # cd' \<and> 
          stack_from_stack s = ((env, cd') # sfs) \<and> vs = encode_closure c # vals_from_stack s)" 
    using encode_to_lookup by simp
  ultimately show ?case
  proof (induction \<Sigma>\<^sub>c)
    case (SE\<^sub>c s cs e)
    then obtain es cd' where E: "unzip e = (Var\<^sub>d x, es) \<and> cd = zip_encode es @ cd' \<and>
      stack_from_stack s = ((env, cd') # sfs) \<and> vs = vals_from_stack s" by auto 
    hence X: "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s cs e) (SE\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ s) cs (Var\<^sub>d x))" by simp
    from SE\<^sub>c obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and>
      latest_environment s = Some cs \<and> (ts \<turnstile>\<^sub>d e : t')" by fastforce
    with E have "env = map encode_closure cs" by fastforce
    with SE\<^sub>c obtain c where C: "lookup cs x = Some c \<and> encode_closure c = v" by fastforce
    with X have "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s cs e) (SC\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ s) c)" by simp
    with E C show ?case by fastforce
  next
    case (SC\<^sub>c s c)
    then obtain s' cs e es cd' where S: "s = FApp1\<^sub>c cs e # s' \<and> unzip e = (Var\<^sub>d x, es) \<and>
        cd = zip_encode es @ TApply # cd' \<and> stack_from_stack s' = ((env, cd') # sfs) \<and>
          vs = encode_closure c # vals_from_stack s'" by auto
    hence "iter (\<leadsto>\<^sub>c) (SE\<^sub>c (FApp2\<^sub>c c # s') cs e) 
      (SE\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ FApp2\<^sub>c c # s') cs (Var\<^sub>d x))" by simp
    moreover have "SC\<^sub>c (FApp1\<^sub>c cs e # s') c \<leadsto>\<^sub>c SE\<^sub>c (FApp2\<^sub>c c # s') cs e" by simp
    ultimately have X: "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FApp1\<^sub>c cs e # s') c) 
      (SE\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ FApp2\<^sub>c c # s') cs (Var\<^sub>d x))" by (metis iter_step)
    from SC\<^sub>c obtain t' where "(s :\<^sub>c t' \<rightarrow> t) \<and> (c :\<^sub>c\<^sub>l t')" by fastforce
    with S obtain ts t\<^sub>1 t\<^sub>2 where "t' = Arrow t\<^sub>1 t\<^sub>2 \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (ts \<turnstile>\<^sub>d e : t\<^sub>1) \<and> (s' :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> 
      latest_environment s' = Some cs" by fastforce
    with S have "env = map encode_closure cs" by fastforce
    with SC\<^sub>c obtain c' where C: "lookup cs x = Some c' \<and> encode_closure c' = v" by fastforce
    with X have "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FApp1\<^sub>c cs e # s') c) 
      (SC\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ FApp2\<^sub>c c # s') c')" by simp
    with S C show ?case by fastforce
  qed
next
  case (evt_pushcon vs env k cd sfs)
  hence "(\<exists>s cs e es cd'. \<Sigma>\<^sub>c = SE\<^sub>c s cs e \<and> unzip e = (Const\<^sub>d k, es) \<and> 
    cd = zip_encode es @ cd' \<and>stack_from_stack s = ((env, cd') # sfs) \<and> 
      vs = vals_from_stack s) \<or> (\<exists>s c cs e es cd'. \<Sigma>\<^sub>c = SC\<^sub>c (FApp1\<^sub>c cs e # s) c \<and> 
        unzip e = (Const\<^sub>d k, es) \<and> cd = zip_encode es @ TApply # cd' \<and>
          stack_from_stack s = ((env, cd') # sfs) \<and> vs = encode_closure c # vals_from_stack s)" 
    using encode_to_pushcon by simp
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (SE\<^sub>c s cs e)
    then obtain es cd' where E: "unzip e = (Const\<^sub>d k, es) \<and> cd = zip_encode es @ cd' \<and> 
      stack_from_stack s = ((env, cd') # sfs) \<and> vs = vals_from_stack s" by auto
    hence "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s cs e) (SE\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ s) cs (Const\<^sub>d k))" by simp
    moreover have "SE\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ s) cs (Const\<^sub>d k) \<leadsto>\<^sub>c 
      SC\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ s) (Const\<^sub>c k)" by simp
    ultimately have "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s cs e) (SC\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ s) (Const\<^sub>c k))" by simp
    with E show ?case by fastforce
  next
    case (SC\<^sub>c s c)
    then obtain s' cs e es cd' where S: "s = FApp1\<^sub>c cs e # s' \<and> unzip e = (Const\<^sub>d k, es) \<and> 
        cd = zip_encode es @ TApply # cd' \<and> stack_from_stack s' = ((env, cd') # sfs) \<and>
          vs = encode_closure c # vals_from_stack s'" by auto
    hence "iter (\<leadsto>\<^sub>c) (SE\<^sub>c (FApp2\<^sub>c c # s') cs e) 
      (SE\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ FApp2\<^sub>c c # s') cs (Const\<^sub>d k))" by simp
    moreover have "SC\<^sub>c (FApp1\<^sub>c cs e # s') c \<leadsto>\<^sub>c SE\<^sub>c (FApp2\<^sub>c c # s') cs e" by simp
    moreover have "SE\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ FApp2\<^sub>c c # s') cs (Const\<^sub>d k) \<leadsto>\<^sub>c 
      SC\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ FApp2\<^sub>c c # s') (Const\<^sub>c k)" by simp
    ultimately have "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FApp1\<^sub>c cs e # s') c)
      (SC\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ FApp2\<^sub>c c # s') (Const\<^sub>c k))" 
        by (metis iter_step iter_step_after)
    with S show ?case by fastforce
  qed
next
  case (evt_pushlam vs env cd' cd sfs)
  thus ?case
  proof (induction \<Sigma>\<^sub>c)
    case (SE\<^sub>c s cs e)
    hence "encode_state (SE\<^sub>c s cs e) = TS vs ((env, TPushLam cd' # cd) # sfs)" by simp
    then obtain es tt e' cd'' where E: "unzip e = (Lam\<^sub>d tt e', es) \<and> 
      cd = zip_encode es @ cd'' \<and> cd' = encode e' \<and> vs = vals_from_stack s \<and> 
        stack_from_stack s = ((env, cd'') # sfs)" 
      using encode_to_pushlam by blast
    hence "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s cs e) (SE\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ s) cs (Lam\<^sub>d tt e'))" by simp
    moreover have "SE\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ s) cs (Lam\<^sub>d tt e') \<leadsto>\<^sub>c 
      SC\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ s) (Lam\<^sub>c tt cs e')" by simp
    ultimately have X: "iter (\<leadsto>\<^sub>c) (SE\<^sub>c s cs e) (SC\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ s) (Lam\<^sub>c tt cs e'))"
      by (metis iter_step_after)
    from SE\<^sub>c E have "env = map encode_closure cs" by fastforce
    with SE\<^sub>c E X show ?case by fastforce
  next
    case (SC\<^sub>c s c)
    hence "encode_state (SC\<^sub>c s c) = TS vs ((env, TPushLam cd' # cd) # sfs)" by simp
    then obtain s' cs e es tt e' cd'' where S: "s = FApp1\<^sub>c cs e # s' \<and> 
      unzip e = (Lam\<^sub>d tt e', es) \<and> cd = zip_encode es @ TApply # cd'' \<and> 
        cd' = encode e' \<and> vs = encode_closure c # vals_from_stack s' \<and> 
          stack_from_stack s' = ((env, cd'') # sfs)" 
      using encode_to_pushlam by fastforce
    hence "iter (\<leadsto>\<^sub>c) (SE\<^sub>c (FApp2\<^sub>c c # s') cs e) 
      (SE\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ FApp2\<^sub>c c # s') cs (Lam\<^sub>d tt e'))" by simp
    moreover have "SC\<^sub>c (FApp1\<^sub>c cs e # s') c \<leadsto>\<^sub>c SE\<^sub>c (FApp2\<^sub>c c # s') cs e" by simp
    moreover have "SE\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ FApp2\<^sub>c c # s') cs (Lam\<^sub>d tt e') \<leadsto>\<^sub>c 
      SC\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ FApp2\<^sub>c c # s') (Lam\<^sub>c tt cs e')" by simp
    ultimately have X: "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FApp1\<^sub>c cs e # s') c) 
      (SC\<^sub>c (map (FApp1\<^sub>c cs) (rev es) @ FApp2\<^sub>c c # s') (Lam\<^sub>c tt cs e'))" 
        by (metis iter_step iter_step_after)
    from SC\<^sub>c S have "env = map encode_closure cs" by fastforce
    with SC\<^sub>c S X show ?case by fastforce
  qed
next
  case (evt_apply v env' cd' vs env cd sfs)
  hence "encode_state \<Sigma>\<^sub>c = TS (v # TLam env' cd' # vs) ((env, TApply # cd) # sfs)" by simp
  then obtain s c c' where "\<Sigma>\<^sub>c = SC\<^sub>c (FApp2\<^sub>c c' # s) c \<and> 
    stack_from_stack s = ((env, cd) # sfs) \<and> v = encode_closure c \<and> 
      TLam env' cd' = encode_closure c' \<and> vs = vals_from_stack s" using encode_to_apply by blast
  moreover then obtain t cs e where "c' = Lam\<^sub>c t cs e \<and> env' = map encode_closure cs \<and> 
    cd' = encode e" by (metis encode_lam_closure)
  moreover have "SC\<^sub>c (FApp2\<^sub>c (Lam\<^sub>c t cs e) # s) c \<leadsto>\<^sub>c SE\<^sub>c (FReturn\<^sub>c (c # cs) # s) (c # cs) e" by simp
  moreover hence "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FApp2\<^sub>c (Lam\<^sub>c t cs e) # s) c) 
    (SE\<^sub>c (FReturn\<^sub>c (c # cs) # s) (c # cs) e)" by (metis iter_one)
  ultimately show ?case using encode_def by fastforce
next
  case (evt_return vs env sfs)
  hence R: "(\<exists>c. \<Sigma>\<^sub>c = SC\<^sub>c [] c \<and> env = [] \<and> sfs = [] \<and> vs = [encode_closure c]) \<or> 
    (\<exists>cs s c. \<Sigma>\<^sub>c = SC\<^sub>c (FReturn\<^sub>c cs # s) c \<and> sfs = stack_from_stack s \<and>
      env = map encode_closure cs \<and> vs = encode_closure c # vals_from_stack s)" by simp
  thus ?case
  proof (cases "\<exists>c. \<Sigma>\<^sub>c = SC\<^sub>c [] c \<and> env = [] \<and> sfs = [] \<and> vs = [encode_closure c]")
    case True
    then obtain c where "\<Sigma>\<^sub>c = SC\<^sub>c [] c \<and> env = [] \<and> sfs = [] \<and> vs = [encode_closure c]" 
      by fastforce
    moreover have "iter (\<leadsto>\<^sub>c) (SC\<^sub>c [] c) (SC\<^sub>c [] c)" by simp
    ultimately show ?thesis by fastforce
  next
    case False
    with R obtain cs s c where S: "\<Sigma>\<^sub>c = SC\<^sub>c (FReturn\<^sub>c cs # s) c \<and> sfs = stack_from_stack s \<and>
      env = map encode_closure cs \<and> vs = encode_closure c # vals_from_stack s" by fastforce
    have "SC\<^sub>c (FReturn\<^sub>c cs # s) c \<leadsto>\<^sub>c SC\<^sub>c s c" by simp
    hence "iter (\<leadsto>\<^sub>c) (SC\<^sub>c (FReturn\<^sub>c cs # s) c) (SC\<^sub>c s c)" by (metis iter_one)
    with S show ?thesis by fastforce
  qed
qed

lemma lookup_latest [simp]: "latest_environment s = Some cs \<Longrightarrow> 
    \<exists>cd sfs. stack_from_stack s = (map encode_closure cs, cd) # sfs"
  by (induction s rule: stack_from_stack.induct) (auto split: list.splits)

theorem completet [simp]: "\<Sigma> \<leadsto>\<^sub>c \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow> iter (\<leadsto>\<^sub>t) (encode_state \<Sigma>) (encode_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: eval\<^sub>c.induct)
  case (ev\<^sub>c_var cs x c s)
  then obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs \<and> 
    lookup ts x = Some t'" by fastforce
  then obtain cd sfs where S: "stack_from_stack s = (map encode_closure cs, cd) # sfs" 
    by (metis lookup_latest)
  with ev\<^sub>c_var have "TS (vals_from_stack s) ((map encode_closure cs, TLookup x # cd) # sfs) \<leadsto>\<^sub>t 
    TS (encode_closure c # vals_from_stack s) ((map encode_closure cs, cd) # sfs)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS (vals_from_stack s) ((map encode_closure cs, TLookup x # cd) # sfs))
    (TS (encode_closure c # vals_from_stack s) ((map encode_closure cs, cd) # sfs))" 
      by (metis iter_one)
    with S show ?case by simp
next
  case (ev\<^sub>c_con s cs k)
  then obtain ts where "(s :\<^sub>c Num \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs" 
    by fastforce
  then obtain cd sfs where S: "stack_from_stack s = (map encode_closure cs, cd) # sfs" 
    by (metis lookup_latest)
  have "TS (vals_from_stack s) ((map encode_closure cs, TPushCon k # cd) # sfs) \<leadsto>\<^sub>t 
    TS (TConst k # vals_from_stack s) ((map encode_closure cs, cd) # sfs)" by simp
  hence "iter (\<leadsto>\<^sub>t) (TS (vals_from_stack s) ((map encode_closure cs, TPushCon k # cd) # sfs)) 
    (TS (TConst k # vals_from_stack s) ((map encode_closure cs, cd) # sfs))" by (metis iter_one)
  with S show ?case by simp
next
  case (ev\<^sub>c_lam s cs tt e)
  then obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs \<and>
    (ts \<turnstile>\<^sub>d Lam\<^sub>d tt e : t')" by fastforce
  then obtain cd sfs where S: "stack_from_stack s = (map encode_closure cs, cd) # sfs" 
    by (metis lookup_latest)
  hence "TS (vals_from_stack s) ((map encode_closure cs, TPushLam (encode e) # cd) # sfs) \<leadsto>\<^sub>t 
    TS (TLam (map encode_closure cs) (encode e) # vals_from_stack s) 
      ((map encode_closure cs, cd) # sfs)" by (metis evt_pushlam)
  hence "iter (\<leadsto>\<^sub>t) (TS (vals_from_stack s) 
    ((map encode_closure cs, TPushLam (encode e) # cd) # sfs)) 
      (TS (TLam (map encode_closure cs) (encode e) # vals_from_stack s)
        ((map encode_closure cs, cd) # sfs))" by (metis iter_one)
  with S show ?case by (simp add: encode_def)
next
  case (ev\<^sub>c_app s cs e\<^sub>1 e\<^sub>2)
  then obtain t' ts where "(s :\<^sub>c t' \<rightarrow> t) \<and> (cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> latest_environment s = Some cs \<and>
    (ts \<turnstile>\<^sub>d App\<^sub>d e\<^sub>1 e\<^sub>2 : t')" by fastforce
  then obtain cd sfs where S: "stack_from_stack s = (map encode_closure cs, cd) # sfs" 
    by (metis lookup_latest)
  then show ?case by simp
next
  case (ret\<^sub>c_app1 cs e\<^sub>2 s c\<^sub>1)
  then obtain ts t\<^sub>1 t\<^sub>2 where "(cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (ts \<turnstile>\<^sub>d e\<^sub>2 : t\<^sub>1) \<and> (s :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and>
    latest_environment s = Some cs \<and> (c\<^sub>1 :\<^sub>c\<^sub>l Arrow t\<^sub>1 t\<^sub>2)" by blast
  then obtain cd sfs where "stack_from_stack s = (map encode_closure cs, cd) # sfs" 
    by (metis lookup_latest)
  thus ?case by simp
next
  case (ret\<^sub>c_app2 t\<^sub>1 cs e\<^sub>1 s c\<^sub>2)
  then obtain ts t\<^sub>2 cs' where "(cs :\<^sub>c\<^sub>l\<^sub>s ts) \<and> (insert_at 0 t\<^sub>1 ts \<turnstile>\<^sub>d e\<^sub>1 : t\<^sub>2) \<and> (s :\<^sub>c t\<^sub>2 \<rightarrow> t) \<and> 
    latest_environment s = Some cs' \<and> (c\<^sub>2 :\<^sub>c\<^sub>l t\<^sub>1)" by blast
  then obtain cd sfs where S: "stack_from_stack s = (map encode_closure cs', cd) # sfs" 
    by (metis lookup_latest)
  hence "TS (encode_closure c\<^sub>2 # TLam (map encode_closure cs) (encode e\<^sub>1) # 
    vals_from_stack s) ((map encode_closure cs', TApply # cd) # sfs) \<leadsto>\<^sub>t
      TS (vals_from_stack s) ((encode_closure c\<^sub>2 # map encode_closure cs, 
        encode e\<^sub>1) # stack_from_stack s)" by (metis evt_apply)
  hence "iter (\<leadsto>\<^sub>t)
    (TS (encode_closure c\<^sub>2 # TLam (map encode_closure cs) (encode e\<^sub>1) # 
      vals_from_stack s) ((map encode_closure cs', TApply # cd) # sfs))
        (TS (vals_from_stack s) ((encode_closure c\<^sub>2 # map encode_closure cs, 
          encode e\<^sub>1) # stack_from_stack s))"
    by (metis iter_one)
  with S show ?case by (simp add: encode_def)
next
  case (ret\<^sub>c_ret cs s c)
  have "TS (encode_closure c # vals_from_stack s) 
    ((map encode_closure cs, []) # stack_from_stack s) \<leadsto>\<^sub>t
      TS (encode_closure c # vals_from_stack s) (stack_from_stack s)" by simp
  hence "iter (\<leadsto>\<^sub>t) 
    (TS (encode_closure c # vals_from_stack s) ((map encode_closure cs, []) # stack_from_stack s))
      (TS (encode_closure c # vals_from_stack s) (stack_from_stack s))" by (metis iter_one)
  thus ?case by simp
qed

lemma iter_completet [simp]: "iter (\<leadsto>\<^sub>c) \<Sigma> \<Sigma>' \<Longrightarrow> \<Sigma> :\<^sub>c t \<Longrightarrow>
  iter (\<leadsto>\<^sub>t) (encode_state \<Sigma>) (encode_state \<Sigma>')"
proof (induction \<Sigma> \<Sigma>' rule: iter.induct)
  case (iter_step \<Sigma> \<Sigma>' \<Sigma>'')
  hence "iter (\<leadsto>\<^sub>t) (encode_state \<Sigma>) (encode_state \<Sigma>')" by simp
  moreover from iter_step have "iter (\<leadsto>\<^sub>t) (encode_state \<Sigma>') (encode_state \<Sigma>'')" by simp
  ultimately show ?case by (metis iter_append)
qed simp_all

end