theory Type
  imports "../00Utils/Variable"
begin

datatype ty = 
  Num 
  | Arrow ty ty

end