theory UnifiableTerm
  imports "../Utils" "../Variable"
begin

section \<open>Unification\<close>

text \<open>Before we can do typechecking, we need a key tool: the unification algorithm. Our treatment 
here is based on Pierce [5].\<close>

subsection \<open>Unifiable terms\<close>

text \<open>The unification algorithm acts on terms, which for clarity we will always refer to as such (in
contrast to our compilation languages' "expressions". We reuse our variables, since we need to 
generate fresh names; constructor tags are simply strings. In theory, we do not need the full 
generality of the treatment here, since we only ever unify terms representing our limited selection 
of types. However, specializing the term language would only simplify the (quite straightforward) 
conversion between types and terms, while complicating the unification algorithm itself, which is 
where the subtlety already lies anyway. (It would also prevent us from reusing the algorithm if we 
wished to add unification elsewhere - adding a logic-programming component to the source language, 
perhaps.) We therefore define unifiable terms in a very general way:\<close>

datatype uterm = 
  Var var
  | Ctor string "uterm list"

fun uvars :: "uterm \<Rightarrow> var set" 
and uvarss :: "uterm list \<Rightarrow> var set" where
  "uvars (Var x) = {x}"
| "uvars (Ctor \<gamma> \<tau>s) = uvarss \<tau>s"
| "uvarss [] = {}"
| "uvarss (\<tau> # \<tau>s) = uvars \<tau> \<union> uvarss \<tau>s"

lemma finite_uvars [simp]: "finite (uvars \<tau>)"
  and "finite (uvarss \<tau>s)"
  by (induction \<tau> and \<tau>s rule: uvars_uvarss.induct) simp_all

text \<open>"Structural" properties are those that relate purely to the constructor well-formedness of 
terms; that is, the names of constructors and the number of arguments to them, but not which 
constructors or variables exist inside of which. We will use this to show that the well-formedness 
of terms representing types is preserved through substitution.\<close>

definition structural :: "(uterm \<Rightarrow> bool) \<Rightarrow> bool" where
  "structural P \<equiv> (\<exists>f. \<forall>\<gamma> \<tau>s. P (Ctor \<gamma> \<tau>s) = (list_all P \<tau>s \<and> f \<gamma> (length \<tau>s)))"

text \<open>We also define constraints, pairs of terms which must be unified with each other. Functions on 
terms extend to constraints in an obvious way.\<close>

type_synonym constraint = "(uterm \<times> uterm) list"

fun constr_vars :: "constraint \<Rightarrow> var set" where
  "constr_vars [] = {}"
| "constr_vars ((\<tau>\<^sub>1, \<tau>\<^sub>2) # \<kappa>) = uvars \<tau>\<^sub>1 \<union> uvars \<tau>\<^sub>2 \<union> constr_vars \<kappa>"

lemma finite_constr_vars [simp]: "finite (constr_vars \<kappa>)"
  by (induction \<kappa> rule: constr_vars.induct) simp_all

lemma constr_vars_append [simp]: "constr_vars (\<kappa>\<^sub>1 @ \<kappa>\<^sub>2) = constr_vars \<kappa>\<^sub>1 \<union> constr_vars \<kappa>\<^sub>2"
  by (induction \<kappa>\<^sub>1 rule: constr_vars.induct) auto

lemma constr_vars_zip [simp]: "length \<tau>s\<^sub>1 = length \<tau>s\<^sub>2 \<Longrightarrow> 
  constr_vars (zip \<tau>s\<^sub>1 \<tau>s\<^sub>2) = uvarss \<tau>s\<^sub>1 \<union> uvarss \<tau>s\<^sub>2"
proof (induction \<tau>s\<^sub>1 arbitrary: \<tau>s\<^sub>2)
  case (Cons \<tau>\<^sub>1 \<tau>s\<^sub>1)
  thus ?case by (induction \<tau>s\<^sub>2) auto
qed simp_all

text \<open>\<open>list_ctor_count\<close> is used in one very specific place for the termination of the unification 
algorithm, hence its slightly odd definition ignoring the right-hand sides of constraint equations.\<close>

primrec ctor_count :: "uterm \<Rightarrow> nat" where
  "ctor_count (Var x) = 0"
| "ctor_count (Ctor \<gamma> \<tau>s) = Suc (sum_list (map ctor_count \<tau>s))"

fun constr_ctor_count :: "constraint \<Rightarrow> nat" where
  "constr_ctor_count [] = 0"
| "constr_ctor_count ((\<tau>\<^sub>1, \<tau>\<^sub>2) # \<kappa>) = ctor_count \<tau>\<^sub>1 + constr_ctor_count \<kappa>"

lemma constr_ctor_count_append [simp]: "constr_ctor_count (ess\<^sub>1 @ ess\<^sub>2) = 
    constr_ctor_count ess\<^sub>1 + constr_ctor_count ess\<^sub>2"
  by (induction ess\<^sub>1 rule: constr_ctor_count.induct) simp_all

lemma constr_ctor_count_zip [simp]: "length \<tau>s\<^sub>1 = length \<tau>s\<^sub>2 \<Longrightarrow> 
  constr_ctor_count (zip \<tau>s\<^sub>1 \<tau>s\<^sub>2) = sum_list (map ctor_count \<tau>s\<^sub>1)"
proof (induction \<tau>s\<^sub>1 arbitrary: \<tau>s\<^sub>2)
  case (Cons \<tau>\<^sub>1 \<tau>s\<^sub>1)
  thus ?case by (induction \<tau>s\<^sub>2) simp_all
qed simp_all

end