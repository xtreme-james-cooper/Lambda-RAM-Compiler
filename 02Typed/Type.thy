theory Type
  imports "../00Utils/Variable"
begin

datatype ty = 
  TyVar var
  | Num 
  | Arrow ty ty

primrec tvars :: "ty \<Rightarrow> var set" where
  "tvars (TyVar y) = {y}"
| "tvars Num = {}"
| "tvars (Arrow t\<^sub>1 t\<^sub>2) = tvars t\<^sub>1 \<union> tvars t\<^sub>2"

fun tsubst :: "var \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty" where
  "tsubst x t' (TyVar y) = (if x = y then t' else TyVar y)"
| "tsubst x t' Num = Num"
| "tsubst x t' (Arrow t\<^sub>1 t\<^sub>2) = Arrow (tsubst x t' t\<^sub>1) (tsubst x t' t\<^sub>2)"

lemma [simp]: "x \<notin> tvars t \<Longrightarrow> tsubst x t' t = t"
  by (induction t) simp_all

lemma [simp]: "tsubst x (TyVar x) t = t"
  by (induction t) simp_all

lemma [simp]: "y \<notin> tvars t \<Longrightarrow> tsubst y t' (tsubst x (TyVar y) t) = tsubst x t' t"
  by (induction t) simp_all

lemma tsubst_arrow [consumes 1, case_names TyVar Arrow]: "Arrow t\<^sub>1 t\<^sub>2 = tsubst y t' tt \<Longrightarrow> 
  (t' = Arrow t\<^sub>1 t\<^sub>2 \<Longrightarrow> tt = TyVar y \<Longrightarrow> P) \<Longrightarrow> 
    (\<And>tt\<^sub>1 tt\<^sub>2. t\<^sub>1 = tsubst y t' tt\<^sub>1 \<Longrightarrow> t\<^sub>2 = tsubst y t' tt\<^sub>2 \<Longrightarrow> tt = Arrow tt\<^sub>1 tt\<^sub>2 \<Longrightarrow> P) \<Longrightarrow> P"
  by (induction tt) (simp_all split: if_splits)

end