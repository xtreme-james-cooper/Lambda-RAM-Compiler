theory Iteration
  imports Main
begin

subsection \<open>Reflexive Transitive Closure\<close>

text \<open>Our final utility is the reflexive transitive closure of a relation. This will be used for 
iterating evaluation steps. We will also reuse it for the case of "zero or one" relations, that is,
where the two arguments are either the same or separated by only a single step. We could define a
second operator on relations for that, but the only subsequent use for them is to concatenate them 
together into an iterated relation, which would be expressed in terms of \<open>iter\<close> anyways, so we cut 
out the middleman and just use \<open>iter\<close> for these as well.\<close>

inductive iter :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for f where
  iter_refl [simp]: "iter f a a"
| iter_step [simp]: "f a b \<Longrightarrow> iter f b c \<Longrightarrow> iter f a c"

lemma iter_one: "f a b \<Longrightarrow> iter f a b"
  by (metis iter_refl iter_step)

lemma iter_append: "iter f a b \<Longrightarrow> iter f b c \<Longrightarrow> iter f a c"
  by (induction a b rule: iter.induct) simp_all

lemma iter_step_after [simp]: "iter f a b \<Longrightarrow> f b c \<Longrightarrow> iter f a c"
  by (induction a b rule: iter.induct) simp_all

end