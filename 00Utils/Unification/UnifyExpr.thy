theory UnifyExpr
  imports "../Utils" "../Variable"
begin

datatype uexpr = 
  Var var
  | Ctor string "uexpr list"

fun vars :: "uexpr \<Rightarrow> var set" 
and varss :: "uexpr list \<Rightarrow> var set" where
  "vars (Var x) = {x}"
| "vars (Ctor k es) = varss es"
| "varss [] = {}"
| "varss (e # es) = vars e \<union> varss es"

primrec ctor_count :: "uexpr \<Rightarrow> nat" where
  "ctor_count (Var x) = 0"
| "ctor_count (Ctor k es) = Suc (sum_list (map ctor_count es))"

fun list_vars :: "(uexpr \<times> uexpr) list \<Rightarrow> var set" where
  "list_vars [] = {}"
| "list_vars ((e\<^sub>1, e\<^sub>2) # ess) = vars e\<^sub>1 \<union> vars e\<^sub>2 \<union> list_vars ess"

fun list_ctor_count :: "(uexpr \<times> uexpr) list \<Rightarrow> nat" where
  "list_ctor_count [] = 0"
| "list_ctor_count ((e\<^sub>1, e\<^sub>2) # ess) = ctor_count e\<^sub>1 + list_ctor_count ess"

definition structural :: "(uexpr \<Rightarrow> bool) \<Rightarrow> bool" where
  "structural P = (\<exists>f. \<forall>k es. P (Ctor k es) = (list_all P es \<and> f k (length es)))"

lemma [simp]: "finite (vars e)"
  and [simp]: "finite (varss es)"
  by (induction e and es rule: vars_varss.induct) simp_all

lemma [simp]: "finite (list_vars ess)"
  by (induction ess rule: list_vars.induct) simp_all

lemma [simp]: "list_vars (ess\<^sub>1 @ ess\<^sub>2) = list_vars ess\<^sub>1 \<union> list_vars ess\<^sub>2"
  by (induction ess\<^sub>1 rule: list_ctor_count.induct) auto

lemma [simp]: "length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> list_vars (zip es\<^sub>1 es\<^sub>2) = varss es\<^sub>1 \<union> varss es\<^sub>2"
proof (induction es\<^sub>1 arbitrary: es\<^sub>2)
  case (Cons e\<^sub>1 es\<^sub>1)
  thus ?case by (induction es\<^sub>2) auto
qed simp_all

lemma [simp]: "list_ctor_count (ess\<^sub>1 @ ess\<^sub>2) = list_ctor_count ess\<^sub>1 + list_ctor_count ess\<^sub>2"
  by (induction ess\<^sub>1 rule: list_ctor_count.induct) simp_all

lemma [simp]: "length es\<^sub>1 = length es\<^sub>2 \<Longrightarrow> 
  list_ctor_count (zip es\<^sub>1 es\<^sub>2) = sum_list (map ctor_count es\<^sub>1)"
proof (induction es\<^sub>1 arbitrary: es\<^sub>2)
  case (Cons e\<^sub>1 es\<^sub>1)
  thus ?case by (induction es\<^sub>2) simp_all
qed simp_all

end