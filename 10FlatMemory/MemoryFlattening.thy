theory MemoryFlattening                   
  imports FlatMemory "../08HeapMemory/HeapConversion" "../09ChainedEnvironment/Chaining"
begin

primrec flatten_closure :: "closure\<^sub>v \<Rightarrow> nat list" where
  "flatten_closure (Const\<^sub>v k) = [1, k, 0]"
| "flatten_closure (Lam\<^sub>v p pc) = [0, 2 * p, pc]"

primrec flatten_closure' :: "closure\<^sub>v \<Rightarrow> closure\<^sub>v" where
  "flatten_closure' (Const\<^sub>v k) = Const\<^sub>v k"
| "flatten_closure' (Lam\<^sub>v p pc) = Lam\<^sub>v (2 * p) pc"

abbreviation flatten_values :: "closure\<^sub>v heap \<Rightarrow> nat heap" where
  "flatten_values h \<equiv> hsplay flatten_closure h"

primrec flatten_env :: "(ptr \<times> ptr) \<Rightarrow> ptr list" where
  "flatten_env (a, b) = [3 * a, 2 * b]"

abbreviation flatten_environment :: "(ptr \<times> ptr) heap \<Rightarrow> ptr heap" where
  "flatten_environment h \<equiv> hsplay flatten_env h"

abbreviation flatten_vals :: "ptr list \<Rightarrow> ptr list" where
  "flatten_vals vs \<equiv> map ((*) 3) vs"

primrec flatten_frame :: "(ptr \<times> nat) \<Rightarrow> nat list" where
  "flatten_frame (a, b) = [b, 2 * a]"

abbreviation flatten_stack :: "(ptr \<times> nat) list \<Rightarrow> nat list" where
  "flatten_stack sfs \<equiv> concat (map flatten_frame sfs)"

primrec flatten :: "state\<^sub>v \<Rightarrow> state\<^sub>f" where
  "flatten (S\<^sub>v h env vs sfs) = 
      S\<^sub>f (flatten_values h) (flatten_environment env) (flatten_vals vs) (flatten_stack sfs)"

fun get_closure :: "nat heap \<Rightarrow> ptr \<Rightarrow> closure\<^sub>v" where
  "get_closure h p = (case hlookup h p of
      0 \<Rightarrow> Lam\<^sub>v (hlookup h (Suc p)) (hlookup h (Suc (Suc p)))
    | Suc _ \<Rightarrow> Const\<^sub>v (hlookup h (Suc p)))"

lemma [simp]: "length (flatten_closure c) = 3"
  by (induction c) simp_all

lemma [simp]: "flatten_closure c ! 0 = (case c of Lam\<^sub>v _ _ \<Rightarrow> 0 | Const\<^sub>v _ \<Rightarrow> 1)"
  by (simp split: closure\<^sub>v.splits)

lemma flatten_c1 [simp]: "flatten_closure c ! Suc 0 = (case c of Const\<^sub>v k \<Rightarrow> k | Lam\<^sub>v p _ \<Rightarrow> 2 * p)"
  by (simp split: closure\<^sub>v.splits)

lemma flatten_c2 [simp]: "flatten_closure c ! Suc (Suc 0) = 
    (case c of Const\<^sub>v k \<Rightarrow> 0 | Lam\<^sub>v _ pc \<Rightarrow> pc)"
  by (simp split: closure\<^sub>v.splits)

lemma [simp]: "hcontains h v \<Longrightarrow> 
  hlookup (flatten_values h) (3 * v) = (case hlookup h v of Lam\<^sub>v _ _ \<Rightarrow> 0 | Const\<^sub>v _ \<Rightarrow> 1)"
proof -
  assume "hcontains h v"
  moreover have "\<And>a. length (flatten_closure a) = 3 \<and> 
    flatten_closure a ! 0 = (case a of Lam\<^sub>v _ _ \<Rightarrow> 0 | Const\<^sub>v _ \<Rightarrow> 1)" 
      by (simp split: closure\<^sub>v.splits)
  ultimately show ?thesis by (metis hlookup_hsplay zero_less_numeral add_0)
qed

lemma [simp]: "hcontains h v \<Longrightarrow> hlookup (flatten_values h) (Suc (3 * v)) = 
  (case hlookup h v of Lam\<^sub>v p\<^sub>\<Delta> _ \<Rightarrow> 2 * p\<^sub>\<Delta> | Const\<^sub>v n \<Rightarrow> n)"
proof -
  assume "hcontains h v"
  moreover have "(1::nat) < 3" by simp
  moreover have "\<And>a. length (flatten_closure a) = 3 \<and> 
    flatten_closure a ! 1 = (case a of Lam\<^sub>v p\<^sub>\<Delta> _ \<Rightarrow> 2 * p\<^sub>\<Delta> | Const\<^sub>v n \<Rightarrow> n)" 
      by (simp split: closure\<^sub>v.splits)
  ultimately show ?thesis by (metis hlookup_hsplay plus_1_eq_Suc)
qed

lemma [simp]: "hcontains h v \<Longrightarrow> hlookup (flatten_values h) (Suc (Suc (3 * v))) = 
  (case hlookup h v of Lam\<^sub>v _ p\<^sub>\<C> \<Rightarrow> p\<^sub>\<C> | Const\<^sub>v _ \<Rightarrow> 0)"
proof -
  assume "hcontains h v"
  moreover have "(2::nat) < 3" by simp
  moreover have "\<And>a. length (flatten_closure a) = 3 \<and> 
    flatten_closure a ! 2 = (case a of Lam\<^sub>v _ p\<^sub>\<C> \<Rightarrow> p\<^sub>\<C> | Const\<^sub>v _ \<Rightarrow> 0)" 
      by (simp split: closure\<^sub>v.splits)
  ultimately show ?thesis by (metis hlookup_hsplay plus_1_eq_Suc Suc_1 add_Suc)
qed

lemma [simp]: "hcontains h v \<Longrightarrow> 
    get_closure (flatten_values h) (3 * v) = flatten_closure' (hlookup h v)"
  by (simp split: closure\<^sub>v.splits)

lemma [dest]: "hcontains h v \<Longrightarrow> get_closure (flatten_values h) (3 * v) = Const\<^sub>v k \<Longrightarrow> 
    hlookup h v = Const\<^sub>v k"
  by (cases "hlookup h v") (simp_all del: get_closure.simps)

lemma [dest]: "hcontains h v \<Longrightarrow> get_closure (flatten_values h) (3 * v) = Lam\<^sub>v p pc \<Longrightarrow> 
    \<exists>p'. hlookup h v = Lam\<^sub>v p' pc \<and> p = 2 * p'"
  by (cases "hlookup h v") (simp_all del: get_closure.simps)

lemma [simp]: "length (flatten_env e) = 2"
  by (induction e) simp_all

lemma flatten_e0 [simp]: "(flatten_env e ! 0) = 3 * fst e"
  by (induction e) simp_all

lemma flatten_e1 [simp]: "(flatten_env e ! 1) = 2 * snd e"
  by (induction e) simp_all

lemma [simp]: "chained_heap_pointer env p \<Longrightarrow> chain_structured h env \<Longrightarrow>
  flat_lookup (flatten_environment env) (2 * p) x = map_option ((*) 3) (chain_lookup env p x)"
proof (induction env p x rule: chain_lookup.induct)
  case (2 env p)
  hence "hcontains env p" by auto
  hence "\<And>k g. (\<And>a. flatten_env a ! k = g a) \<Longrightarrow> k < 2 \<Longrightarrow>
    hlookup (hsplay flatten_env env) (k + 2 * p) = g (hlookup env p)" by simp
  hence "hlookup (hsplay flatten_env env) (2 * p) = 3 * fst (hlookup env p)" 
    using flatten_e0 by force
  thus ?case by (simp split: prod.splits)
next
  case (3 env p x)
  hence P: "hcontains env p" by auto
  hence "\<And>k g. (\<And>a. flatten_env a ! k = g a) \<Longrightarrow> k < 2 \<Longrightarrow>
    hlookup (hsplay flatten_env env) (k + 2 * p) = g (hlookup env p)" by simp
  moreover have "\<And>a. (flatten_env a ! 1) = 2 * snd a \<and> (1::nat) < 2" by auto
  ultimately have X: "hlookup (hsplay flatten_env env) (1 + 2 * p) = 2 * snd (hlookup env p)" 
    by meson
  obtain a b where A: "hlookup env p = (a, b)" by (cases "hlookup env p")
  with 3 P have "b \<le> p" using hlookup_all by fast
  with P have "chained_heap_pointer env b" by auto
  with 3 X A show ?case by simp
qed simp_all

lemma flatten_halloc [simp]: "halloc h c = (h', v) \<Longrightarrow> 
    halloc_list (flatten_values h) (flatten_closure c) = (flatten_values h', 3 * v)"
  by simp

lemma flatten_lt_3: "hcontains h x \<Longrightarrow> flatten_values h = H h' hp \<Longrightarrow> Suc (3 * x) < hp"
  by simp

lemma [dest]: "S\<^sub>f h env vs sfs = flatten \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow> \<exists>h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e. \<Sigma>\<^sub>c\<^sub>e = S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e \<and> 
  h = flatten_values h\<^sub>c\<^sub>e \<and> env = flatten_environment env\<^sub>c\<^sub>e \<and> vs = flatten_vals vs\<^sub>c\<^sub>e \<and> 
    sfs = flatten_stack sfs\<^sub>c\<^sub>e"
  by (induction \<Sigma>\<^sub>c\<^sub>e) simp_all

lemma [dest]: "pc # p # sfs = flatten_stack sfs\<^sub>c\<^sub>e \<Longrightarrow> \<exists>p\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e'. sfs\<^sub>c\<^sub>e = (p\<^sub>c\<^sub>e, pc) # sfs\<^sub>c\<^sub>e' \<and> 
  sfs = flatten_stack sfs\<^sub>c\<^sub>e' \<and> p = 2 * p\<^sub>c\<^sub>e"
proof (induction sfs\<^sub>c\<^sub>e)
  case (Cons sf\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e)
  thus ?case by (cases sf\<^sub>c\<^sub>e) simp_all
qed simp_all

lemma [dest]: "halloc_list (flatten_values h\<^sub>c\<^sub>e) (flatten_closure c) = (h', v) \<Longrightarrow> 
  \<exists>h\<^sub>c\<^sub>e' v\<^sub>c\<^sub>e. h' = hsplay flatten_closure h\<^sub>c\<^sub>e' \<and> v = 3 * v\<^sub>c\<^sub>e \<and> halloc h\<^sub>c\<^sub>e c = (h\<^sub>c\<^sub>e', v\<^sub>c\<^sub>e)"
proof -
  obtain h\<^sub>c\<^sub>e' v\<^sub>c\<^sub>e where "halloc h\<^sub>c\<^sub>e c = (h\<^sub>c\<^sub>e', v\<^sub>c\<^sub>e)" by fastforce
  moreover assume "halloc_list (flatten_values h\<^sub>c\<^sub>e) (flatten_closure c) = (h', v)"
  ultimately show ?thesis by auto
qed

lemma [simp]: "halloc env (v, p) = (env', p') \<Longrightarrow> 
  halloc_list (flatten_environment env) [3 * v, 2 * p] = (flatten_environment env', 2 * p')" 
proof -
  assume "halloc env (v, p) = (env', p')"
  moreover have "\<And>x. length (flatten_env x) = 2" by simp
  ultimately have "halloc_list (flatten_environment env) (flatten_env (v, p)) = 
    (flatten_environment env', 2 * p')" by (metis halloc_list_hsplay)
  thus ?thesis by simp
qed

theorem correctf: "cd \<tturnstile> flatten \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>f \<Sigma>\<^sub>f' \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow> 
  \<exists>\<Sigma>\<^sub>c\<^sub>e'. (cd \<tturnstile> \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>v \<Sigma>\<^sub>c\<^sub>e') \<and> flatten \<Sigma>\<^sub>c\<^sub>e' = \<Sigma>\<^sub>f'" 
proof (induction "flatten \<Sigma>\<^sub>c\<^sub>e" \<Sigma>\<^sub>f' rule: eval\<^sub>f.induct)
  case (ev\<^sub>f_lookup cd pc x env p v h vs sfs)
  then obtain h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e p\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e where S: "\<Sigma>\<^sub>c\<^sub>e = S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e ((p\<^sub>c\<^sub>e, Suc pc) # sfs\<^sub>c\<^sub>e) \<and> 
    h = flatten_values h\<^sub>c\<^sub>e \<and> env = flatten_environment env\<^sub>c\<^sub>e \<and> vs = flatten_vals vs\<^sub>c\<^sub>e \<and> 
      sfs = flatten_stack sfs\<^sub>c\<^sub>e \<and> p = 2 * p\<^sub>c\<^sub>e" by fastforce
  with ev\<^sub>f_lookup obtain v\<^sub>c\<^sub>e where V: "chain_lookup env\<^sub>c\<^sub>e p\<^sub>c\<^sub>e x = Some v\<^sub>c\<^sub>e \<and> v = 3 * v\<^sub>c\<^sub>e" by fastforce
  with S have X: "flatten (S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e (v\<^sub>c\<^sub>e # vs\<^sub>c\<^sub>e) ((p\<^sub>c\<^sub>e, pc) # sfs\<^sub>c\<^sub>e)) = 
    S\<^sub>f h env (v # vs) (pc # p # sfs)" by simp
  from ev\<^sub>f_lookup V have "cd \<tturnstile> S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e ((p\<^sub>c\<^sub>e, Suc pc) # sfs\<^sub>c\<^sub>e) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e (v\<^sub>c\<^sub>e # vs\<^sub>c\<^sub>e) ((p\<^sub>c\<^sub>e, pc) # sfs\<^sub>c\<^sub>e)" by simp
  with S X show ?case by blast
next
  case (ev\<^sub>f_pushcon cd pc k h h' v env vs p sfs)
  then obtain h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e p\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e where S: "\<Sigma>\<^sub>c\<^sub>e = S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e ((p\<^sub>c\<^sub>e, Suc pc) # sfs\<^sub>c\<^sub>e) \<and> 
    h = flatten_values h\<^sub>c\<^sub>e \<and> env = flatten_environment env\<^sub>c\<^sub>e \<and> vs = flatten_vals vs\<^sub>c\<^sub>e \<and> 
      sfs = flatten_stack sfs\<^sub>c\<^sub>e \<and> p = 2 * p\<^sub>c\<^sub>e" by fastforce
  with ev\<^sub>f_pushcon have "halloc_list (hsplay flatten_closure h\<^sub>c\<^sub>e) (flatten_closure (Const\<^sub>v k)) = 
    (h', v)" by simp
  then obtain h\<^sub>c\<^sub>e' v\<^sub>c\<^sub>e where H: "h' = hsplay flatten_closure h\<^sub>c\<^sub>e' \<and> v = 3 * v\<^sub>c\<^sub>e \<and> 
    halloc h\<^sub>c\<^sub>e (Const\<^sub>v k) = (h\<^sub>c\<^sub>e', v\<^sub>c\<^sub>e)" by fastforce
  with S have X: "flatten (S\<^sub>v h\<^sub>c\<^sub>e' env\<^sub>c\<^sub>e (v\<^sub>c\<^sub>e # vs\<^sub>c\<^sub>e) ((p\<^sub>c\<^sub>e, pc) # sfs\<^sub>c\<^sub>e)) = 
    S\<^sub>f h' env (v # vs) (pc # p # sfs)" by simp
  from ev\<^sub>f_pushcon H have "cd \<tturnstile> S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e ((p\<^sub>c\<^sub>e, Suc pc) # sfs\<^sub>c\<^sub>e) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>c\<^sub>e' env\<^sub>c\<^sub>e (v\<^sub>c\<^sub>e # vs\<^sub>c\<^sub>e) ((p\<^sub>c\<^sub>e, pc) # sfs\<^sub>c\<^sub>e)" by simp
  with S X show ?case by blast
next
  case (ev\<^sub>f_pushlam cd pc pc' h p h' v env vs sfs)
  then obtain h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e p\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e where S: "\<Sigma>\<^sub>c\<^sub>e = S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e ((p\<^sub>c\<^sub>e, Suc pc) # sfs\<^sub>c\<^sub>e) \<and> 
    h = flatten_values h\<^sub>c\<^sub>e \<and> env = flatten_environment env\<^sub>c\<^sub>e \<and> vs = flatten_vals vs\<^sub>c\<^sub>e \<and> 
      sfs = flatten_stack sfs\<^sub>c\<^sub>e \<and> p = 2 * p\<^sub>c\<^sub>e" by fastforce
  with ev\<^sub>f_pushlam have "halloc_list (hsplay flatten_closure h\<^sub>c\<^sub>e) (flatten_closure (Lam\<^sub>v p\<^sub>c\<^sub>e pc')) = 
    (h', v)" by simp
  then obtain h\<^sub>c\<^sub>e' v\<^sub>c\<^sub>e where H: "h' = hsplay flatten_closure h\<^sub>c\<^sub>e' \<and> v = 3 * v\<^sub>c\<^sub>e \<and> 
    halloc h\<^sub>c\<^sub>e (Lam\<^sub>v p\<^sub>c\<^sub>e pc') = (h\<^sub>c\<^sub>e', v\<^sub>c\<^sub>e)" by fastforce
  with S have X: "flatten (S\<^sub>v h\<^sub>c\<^sub>e' env\<^sub>c\<^sub>e (v\<^sub>c\<^sub>e # vs\<^sub>c\<^sub>e) ((p\<^sub>c\<^sub>e, pc) # sfs\<^sub>c\<^sub>e)) = 
    S\<^sub>f h' env (v # vs) (pc # p # sfs)" by simp
  from ev\<^sub>f_pushlam S H have "cd \<tturnstile> S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e ((p\<^sub>c\<^sub>e, Suc pc) # sfs\<^sub>c\<^sub>e) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>c\<^sub>e' env\<^sub>c\<^sub>e (v\<^sub>c\<^sub>e # vs\<^sub>c\<^sub>e) ((p\<^sub>c\<^sub>e, pc) # sfs\<^sub>c\<^sub>e)" by simp
  with S X show ?case by blast
next
  case (ev\<^sub>f_apply cd pc h v2 env v1 env' p2 vs p sfs)
  then obtain h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e v1\<^sub>c\<^sub>e v2\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e p\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e where S: "
    \<Sigma>\<^sub>c\<^sub>e = S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e (v1\<^sub>c\<^sub>e # v2\<^sub>c\<^sub>e # vs\<^sub>c\<^sub>e) ((p\<^sub>c\<^sub>e, Suc pc) # sfs\<^sub>c\<^sub>e) \<and> h = flatten_values h\<^sub>c\<^sub>e \<and> 
      env = flatten_environment env\<^sub>c\<^sub>e \<and> v1 = 3 * v1\<^sub>c\<^sub>e \<and> v2 = 3 * v2\<^sub>c\<^sub>e \<and> vs = flatten_vals vs\<^sub>c\<^sub>e \<and> 
        sfs = flatten_stack sfs\<^sub>c\<^sub>e \<and> p = 2 * p\<^sub>c\<^sub>e" by fastforce
  let ?p' = "hlookup (flatten_values h\<^sub>c\<^sub>e) (Suc (3 * v2\<^sub>c\<^sub>e))"
  let ?pc' = "hlookup (flatten_values h\<^sub>c\<^sub>e) (Suc (Suc (3 * v2\<^sub>c\<^sub>e)))"
  from ev\<^sub>f_apply S have "get_closure (flatten_values h\<^sub>c\<^sub>e) (3 * v2\<^sub>c\<^sub>e) = Lam\<^sub>v ?p' ?pc'" by simp
  moreover from ev\<^sub>f_apply S have "hcontains h\<^sub>c\<^sub>e v2\<^sub>c\<^sub>e" by simp
  ultimately obtain p\<^sub>c\<^sub>e' where P: "hlookup h\<^sub>c\<^sub>e v2\<^sub>c\<^sub>e = Lam\<^sub>v p\<^sub>c\<^sub>e' ?pc' \<and> ?p' = 2 * p\<^sub>c\<^sub>e'" by blast
  obtain env\<^sub>c\<^sub>e' p2\<^sub>c\<^sub>e where E: "halloc env\<^sub>c\<^sub>e (v1\<^sub>c\<^sub>e, p\<^sub>c\<^sub>e') = (env\<^sub>c\<^sub>e', p2\<^sub>c\<^sub>e)" by fastforce
  with ev\<^sub>f_apply S P have X: "flatten (S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e' vs\<^sub>c\<^sub>e ((Suc p2\<^sub>c\<^sub>e, ?pc') # (p\<^sub>c\<^sub>e, pc) # sfs\<^sub>c\<^sub>e)) = 
    S\<^sub>f h env' vs (?pc' # Suc (Suc p2) # pc # p # sfs)" by simp
  from ev\<^sub>f_apply P E have "cd \<tturnstile> S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e (v1\<^sub>c\<^sub>e # v2\<^sub>c\<^sub>e # vs\<^sub>c\<^sub>e) ((p\<^sub>c\<^sub>e, Suc pc) # sfs\<^sub>c\<^sub>e) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e' vs\<^sub>c\<^sub>e ((Suc p2\<^sub>c\<^sub>e, ?pc') # (p\<^sub>c\<^sub>e, pc) # sfs\<^sub>c\<^sub>e)" by simp
  with S X show ?case by blast
next
  case (ev\<^sub>f_return cd pc h env vs p sfs)
  then obtain h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e p\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e where S: "\<Sigma>\<^sub>c\<^sub>e = S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e ((p\<^sub>c\<^sub>e, Suc pc) # sfs\<^sub>c\<^sub>e) \<and> 
    h = flatten_values h\<^sub>c\<^sub>e \<and> env = flatten_environment env\<^sub>c\<^sub>e \<and> vs = flatten_vals vs\<^sub>c\<^sub>e \<and> 
      sfs = flatten_stack sfs\<^sub>c\<^sub>e \<and> p = 2 * p\<^sub>c\<^sub>e" by fastforce
  hence X: "flatten (S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e) = S\<^sub>f h env vs sfs" by simp
  from ev\<^sub>f_return have "cd \<tturnstile> S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e ((p\<^sub>c\<^sub>e, Suc pc) # sfs\<^sub>c\<^sub>e) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e" by simp
  with S X show ?case by blast
next
  case (ev\<^sub>f_jump cd pc h v2 env v1 env' p2 vs p sfs)
  then obtain h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e v1\<^sub>c\<^sub>e v2\<^sub>c\<^sub>e vs\<^sub>c\<^sub>e p\<^sub>c\<^sub>e sfs\<^sub>c\<^sub>e where S: "
    \<Sigma>\<^sub>c\<^sub>e = S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e (v1\<^sub>c\<^sub>e # v2\<^sub>c\<^sub>e # vs\<^sub>c\<^sub>e) ((p\<^sub>c\<^sub>e, Suc pc) # sfs\<^sub>c\<^sub>e) \<and> h = flatten_values h\<^sub>c\<^sub>e \<and> 
      env = flatten_environment env\<^sub>c\<^sub>e \<and> v1 = 3 * v1\<^sub>c\<^sub>e \<and> v2 = 3 * v2\<^sub>c\<^sub>e \<and> vs = flatten_vals vs\<^sub>c\<^sub>e \<and> 
        sfs = flatten_stack sfs\<^sub>c\<^sub>e \<and> p = 2 * p\<^sub>c\<^sub>e" by fastforce
  let ?p' = "hlookup (flatten_values h\<^sub>c\<^sub>e) (Suc (3 * v2\<^sub>c\<^sub>e))"
  let ?pc' = "hlookup (flatten_values h\<^sub>c\<^sub>e) (Suc (Suc (3 * v2\<^sub>c\<^sub>e)))"
  from ev\<^sub>f_jump S have "get_closure (flatten_values h\<^sub>c\<^sub>e) (3 * v2\<^sub>c\<^sub>e) = Lam\<^sub>v ?p' ?pc'" by simp
  moreover from ev\<^sub>f_jump S have "hcontains h\<^sub>c\<^sub>e v2\<^sub>c\<^sub>e" by simp
  ultimately obtain p\<^sub>c\<^sub>e' where P: "hlookup h\<^sub>c\<^sub>e v2\<^sub>c\<^sub>e = Lam\<^sub>v p\<^sub>c\<^sub>e' ?pc' \<and> ?p' = 2 * p\<^sub>c\<^sub>e'" by blast
  obtain env\<^sub>c\<^sub>e' p2\<^sub>c\<^sub>e where E: "halloc env\<^sub>c\<^sub>e (v1\<^sub>c\<^sub>e, p\<^sub>c\<^sub>e') = (env\<^sub>c\<^sub>e', p2\<^sub>c\<^sub>e)" by fastforce
  with ev\<^sub>f_jump S P have X: "flatten (S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e' vs\<^sub>c\<^sub>e ((Suc p2\<^sub>c\<^sub>e, ?pc') # sfs\<^sub>c\<^sub>e)) = 
    S\<^sub>f h env' vs (?pc' # Suc (Suc p2) # sfs)" by simp
  from ev\<^sub>f_jump P E have "cd \<tturnstile> S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e (v1\<^sub>c\<^sub>e # v2\<^sub>c\<^sub>e # vs\<^sub>c\<^sub>e) ((p\<^sub>c\<^sub>e, Suc pc) # sfs\<^sub>c\<^sub>e) \<leadsto>\<^sub>v 
    S\<^sub>v h\<^sub>c\<^sub>e env\<^sub>c\<^sub>e' vs\<^sub>c\<^sub>e ((Suc p2\<^sub>c\<^sub>e, ?pc') # sfs\<^sub>c\<^sub>e)" by simp
  with S X show ?case by blast
qed

theorem completef [simp]: "cd \<tturnstile> \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>v \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow> 
  cd \<tturnstile> flatten \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>f flatten \<Sigma>\<^sub>c\<^sub>e'" 
proof (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: eval\<^sub>v.induct)
  case (ev\<^sub>v_pushcon cd pc k h h' v env vs p sfs)
  moreover hence "halloc_list (flatten_values h) [1, k, 0] = (flatten_values h', 3 * v)"
    using flatten_halloc by fastforce
  ultimately show ?case by simp
next
  case (ev\<^sub>v_pushlam cd pc pc' h p h' v env vs sfs)
  moreover hence "halloc_list (flatten_values h) [0, 2 * p, pc'] = (flatten_values h', 3 * v)" 
    using flatten_halloc by fastforce
  ultimately show ?case by simp
next
  case (ev\<^sub>v_apply \<C> p\<^sub>\<C> h v2 p' pc' env v1 env' p'' vs p\<^sub>\<Delta> sfs)
  moreover hence "halloc_list (flatten_environment env) 
    [3 * v1, hlookup (flatten_values h) (Suc (3 * v2))] = (flatten_environment env', 2 * p'')" 
      by simp
  moreover from ev\<^sub>v_apply have "hlookup (flatten_values h) (3 * v2) = 0" by simp
  ultimately have "\<C> \<tturnstile> S\<^sub>f (flatten_values h) (flatten_environment env) 
      (3 * v1 # 3 * v2 # flatten_vals vs) (Suc p\<^sub>\<C> # 2 * p\<^sub>\<Delta> # flatten_stack sfs) \<leadsto>\<^sub>f 
    S\<^sub>f (flatten_values h) (flatten_environment env') (flatten_vals vs) 
      (hlookup (flatten_values h) (Suc (Suc (3 * v2))) # Suc (Suc (2 * p'')) # p\<^sub>\<C> # 2 * p\<^sub>\<Delta> # 
        flatten_stack sfs)"
    by (metis ev\<^sub>f_apply)
  with ev\<^sub>v_apply show ?case by simp
next
  case (ev\<^sub>v_jump \<C> p\<^sub>\<C> h v2 p' pc' env v1 env' p'' vs p\<^sub>\<Delta> sfs)
  moreover hence "halloc_list (flatten_environment env) 
    [3 * v1, hlookup (flatten_values h) (Suc (3 * v2))] = (flatten_environment env', 2 * p'')" 
      by simp
  moreover from ev\<^sub>v_jump have "hlookup (flatten_values h) (3 * v2) = 0" by simp
  ultimately have "\<C> \<tturnstile> S\<^sub>f (flatten_values h) (flatten_environment env) 
      (3 * v1 # 3 * v2 # flatten_vals vs) (Suc p\<^sub>\<C> # 2 * p\<^sub>\<Delta> # flatten_stack sfs) \<leadsto>\<^sub>f 
    S\<^sub>f (flatten_values h) (flatten_environment env') (flatten_vals vs) 
      (hlookup (flatten_values h) (Suc (Suc (3 * v2))) # Suc (Suc (2 * p'')) # flatten_stack sfs)"
    by (metis ev\<^sub>f_jump)
  with ev\<^sub>v_jump show ?case by simp
qed fastforce+

lemma completef_iter [simp]: "iter (\<tturnstile> cd \<leadsto>\<^sub>v) \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Longrightarrow> chained_state \<Sigma>\<^sub>c\<^sub>e \<Longrightarrow>
  iter (\<tturnstile> cd \<leadsto>\<^sub>f) (flatten \<Sigma>\<^sub>c\<^sub>e) (flatten \<Sigma>\<^sub>c\<^sub>e')"
proof (induction \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' rule: iter.induct)
  case (iter_step \<Sigma>\<^sub>c\<^sub>e \<Sigma>\<^sub>c\<^sub>e' \<Sigma>\<^sub>c\<^sub>e'')
  hence "iter (\<tturnstile> cd \<leadsto>\<^sub>f) (flatten \<Sigma>\<^sub>c\<^sub>e') (flatten \<Sigma>\<^sub>c\<^sub>e'')" by simp
  moreover from iter_step have "cd \<tturnstile> flatten \<Sigma>\<^sub>c\<^sub>e \<leadsto>\<^sub>f flatten \<Sigma>\<^sub>c\<^sub>e'" by simp
  ultimately show ?case by simp
qed simp_all

end