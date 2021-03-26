theory Type
  imports "../00Utils/Variable"
begin

datatype ty = 
  TVar var
  | Base 
  | Arrow ty ty

primrec tsubst_var :: "var \<Rightarrow> var \<Rightarrow> ty \<Rightarrow> ty" where
  "tsubst_var x x' (TVar y) = TVar (if x = y then x' else y)"
| "tsubst_var x x' Base = Base"
| "tsubst_var x x' (Arrow t\<^sub>1 t\<^sub>2) = Arrow (tsubst_var x x' t\<^sub>1) (tsubst_var x x' t\<^sub>2)"

lemma [simp]: "size (tsubst_var x x' t) = size t"
  by (induction t) simp_all

fun tsubst :: "var \<Rightarrow> ty \<Rightarrow> ty \<Rightarrow> ty" where
  "tsubst x t' (TVar y) = (if x = y then t' else TVar y)"
| "tsubst x t' Base = Base"
| "tsubst x t' (Arrow t\<^sub>1 t\<^sub>2) = Arrow (tsubst x t' t\<^sub>1) (tsubst x t' t\<^sub>2)"

end