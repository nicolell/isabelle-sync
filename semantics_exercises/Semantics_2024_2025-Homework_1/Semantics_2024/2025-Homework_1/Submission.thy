theory Submission
  imports Defs
begin

fun list_product :: "nat list \<Rightarrow> nat"  where
"list_product Nil = 1" |
"list_product (x # xs) = x * (list_product xs)"

value "list_product [1, 2, 3, 4] = 24"
value "list_product [0, 5, 6, 7] = 0"

lemma list_product_filter_neq_1:
  "list_product (filter (\<lambda>x. x \<noteq> 1) xs) = list_product xs"
  apply(induction xs)
  apply(auto)
  done

lemma list_product_app [simp]: "list_product (xs @ ys) = (list_product xs) * (list_product ys)"
  apply(induction xs)
  apply(auto)
  done

lemma list_product_rev: "list_product (rev xs) = list_product xs"
  apply(induction xs)
   apply(auto)
  done

fun flatten :: "'a list list \<Rightarrow> 'a list"  where
  "flatten Nil = Nil" |
"flatten (xs # xxs) = xs @ (flatten xxs)"

value "flatten [[1,2,3],[2]] = [1,2,3,2::int]"
value "flatten [[1,2,3],[],[2]] = [1,2,3,2::int]"

lemma list_product_flatten: "list_product (flatten xss) = list_product (map list_product xss)"
  apply (induction xss)
  apply(auto)
  done

end