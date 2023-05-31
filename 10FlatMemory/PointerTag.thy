theory PointerTag
  imports Main
begin

section \<open>Flat Memory\<close>

text \<open>We declare some tags for the various sorts of pointers we use; they live in a separate file so 
they can be reused by later stages.\<close>

datatype pointer_tag = 
  PConst
  | PEnv
  | PCode

end