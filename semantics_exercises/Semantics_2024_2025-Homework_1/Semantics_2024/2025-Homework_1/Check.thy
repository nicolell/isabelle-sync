theory Check
  imports Submission
begin

lemma list_product_filter_neq_1: "list_product (filter (\<lambda>x. x \<noteq> 1) xs) = list_product xs"
  by (rule Submission.list_product_filter_neq_1)

lemma list_product_rev: "list_product (rev xs) = list_product xs"
  by (rule Submission.list_product_rev)

lemma list_product_flatten: "list_product (flatten xss) = list_product (map list_product xss)"
  by (rule Submission.list_product_flatten)

end