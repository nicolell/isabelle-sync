theory Defs
  imports "HOL-IMP.AExp"
begin

datatype paren = Open | Close

inductive S where
  S_empty: "S []" |
  S_append: "S xs \<Longrightarrow> S ys \<Longrightarrow> S (xs @ ys)" |
  S_paren: "S xs \<Longrightarrow> S (Open # xs @ [Close])"

fun count :: "'a list \<Rightarrow> 'a \<Rightarrow> nat" where
"count [] _ = 0" |
"count (x # xs) y = (if x = y then Suc (count xs y) else count xs y)"

type_synonym reg = nat

datatype op = REG reg | VAL val

datatype instr =
  LD reg vname
| ADD reg op op

datatype v_or_reg = Var vname | Reg reg

type_synonym mstate = "v_or_reg \<Rightarrow> int"

definition "is_N a = (case a of N _ \<Rightarrow> True | _ \<Rightarrow> False)"

fun num_add :: "instr list \<Rightarrow> nat" where
  "num_add [] = 0"
| "num_add (x#xs) = (case x of (ADD _ _ _) \<Rightarrow> 1 | _ \<Rightarrow> 0) + num_add xs"

lemma num_add_append[simp]: "num_add (xs @ ys) = num_add xs + num_add ys"
  by (induct xs) auto

fun num_plus :: "aexp \<Rightarrow> nat" where
  "num_plus (Plus a1 a2) = 1 + num_plus a1 + num_plus a2"
| "num_plus _ = 0"


consts T :: "paren list \<Rightarrow> bool"

consts op_val :: "op \<Rightarrow> mstate \<Rightarrow> int"

consts exec1 :: "instr \<Rightarrow> mstate \<Rightarrow> mstate"

consts exec :: "instr list \<Rightarrow> mstate \<Rightarrow> mstate"

consts cmp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list"


end