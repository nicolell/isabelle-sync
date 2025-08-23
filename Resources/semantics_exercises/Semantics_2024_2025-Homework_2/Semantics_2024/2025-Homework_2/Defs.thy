theory Defs
  imports "HOL-IMP.AExp"
begin

declare [[names_short]]

datatype bexp' = V vname | And "bexp'" "bexp'" | Not "bexp'" | TT | FF
type_synonym assignment = "vname \<Rightarrow> bool"

fun has_const where
  "has_const TT = True"
| "has_const FF = True"
| "has_const (Not a) = has_const a"
| "has_const (And a b) \<longleftrightarrow> has_const a \<or> has_const b"
| "has_const _ = False"

definition "simplified \<phi> \<longleftrightarrow> \<phi> = TT \<or> \<phi> = FF \<or> \<not> has_const \<phi>"


consts sat :: "bexp' \<Rightarrow> assignment \<Rightarrow> bool"

consts models :: "bexp' \<Rightarrow> assignment set"

consts simplify :: "bexp' \<Rightarrow> bexp'"


end