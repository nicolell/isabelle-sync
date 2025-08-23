theory Defs
  imports Main
begin

text \<open>Definitions and lemmas from the tutorial\<close>

fun snoc :: "'a list \<Rightarrow> 'a \<Rightarrow> 'a list" where
"snoc [] x = [x]" |
"snoc (y # ys) x = y # (snoc ys x)"

fun reverse :: "'a list \<Rightarrow> 'a list" where
"reverse [] = []" |
"reverse (x # xs) = snoc (reverse xs) x"

lemma reverse_snoc: "reverse (snoc xs y) = y # reverse xs"
  by (induction xs) simp_all

theorem reverse_reverse: "reverse (reverse xs) = xs"
  by (induction xs) (simp_all add: reverse_snoc)


consts list_product :: "nat list \<Rightarrow> nat"

consts flatten :: "'a list list \<Rightarrow> 'a list"


end