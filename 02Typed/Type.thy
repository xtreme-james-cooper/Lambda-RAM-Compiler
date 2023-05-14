theory Type
  imports "../00Utils/Variable"
begin

section \<open>Typed language\<close>

text \<open>Now we are ready to begin typechecking our source language. Since we use only simple types, 
with no free or even bound type variables, this is quite quick.\<close>

datatype ty = 
  Num 
  | Arrow ty ty

end