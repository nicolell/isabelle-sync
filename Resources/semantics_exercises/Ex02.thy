theory Ex02 imports "HOL-IMP.AExp" "HOL-IMP.BExp" begin

fun deduplicate :: "'a list \<Rightarrow> 'a list" where
"deduplicate Nil = Nil" |
"deduplicate [x] = [x]" |
"deduplicate (x # y # xs) = (if x = y then (deduplicate (y # xs)) else (x # (deduplicate (y # xs))))"

value "deduplicate [1,1,2,3,2,2,1::nat] = [1,2,3,2,1]"
value "deduplicate [1,1,2,3,2,2,1::nat]"

lemma "length (deduplicate xs) \<le> length xs"
  apply(induction xs rule: deduplicate.induct)
  apply(auto)
  done

text "2.2"


fun subst :: "vname \<Rightarrow> aexp \<Rightarrow> aexp \<Rightarrow> aexp"  where
  "subst v r (V w) = (if v = w then r else V w)"
| "subst _ _ (N n) = N n"
| "subst v r (Plus e1 e2) = Plus (subst v r e1) (subst v r e2)"

lemma subst_lemma: "aval (subst x a' a) s = aval a (s(x := aval a' s))"
  apply(induction a)
    apply(auto)
done

value "subst [] (N 0) (N 0) "
value "aval ( subst [] (N 0) (N 0)) (\<lambda>x. - 1)"
value "aval (N 0)( (\<lambda>x. - 1)(  [] :=   aval(N 0)  (\<lambda>x. - 1)))"

lemma comp: "aval a1 s = aval a2 s \<Longrightarrow> aval (subst x a1 a) s = aval (subst x a2 a) s"
  apply(induction a1 arbitrary: a2 s)
  apply(simp_all add: subst_lemma)
  done

typ aexp
datatype aexp' = N' int | V' vname | Plus' aexp' aexp' | PI' vname

fun aval' :: "aexp' \<Rightarrow> state \<Rightarrow> val\<times>state" where
"aval' (N' x) s = (x,s)" |
"aval' (V' x) s = (s x, s)" |
"aval' (PI' x) s = (s x+1, s(x := s x+1))" |
"aval' (Plus' a\<^sub>1 a\<^sub>2) s =
  (let (v\<^sub>1, s\<^sub>1) = aval' a\<^sub>1 s; (v\<^sub>2, s\<^sub>2) = aval' a\<^sub>2 s\<^sub>1 in (v\<^sub>1 + v\<^sub>2, s\<^sub>2))"


value "<>(x := 0)"
value "aval' (Plus' (PI' ''x'') (V' ''x'')) <>"
value "aval' (Plus' (Plus' (PI' ''x'') (PI' ''x'')) (PI' ''x'')) <>"

value "aval' (Plus' (N' 3) (V' x)) (\<lambda>x. 0)"
value "aval' (Plus' (V' x) (N' 3)) (\<lambda>x. 0)"

text "disprove commutativity, because the increment destroys it"
value "aval' (Plus' (PI' x) (V' x)) s"
value "aval' (Plus' (V' x) (PI' x)) s"
text "these two values should be the same if addition is commutative, but for s = (\<lambda>x. 0) this is not true:"
value "fst (aval' (Plus' (PI' x) (V' x)) (\<lambda>x. 0)) = fst(aval' (Plus' (V' x) (PI' x)) (\<lambda>x. 0))"

thm aval'.induct
lemma aval'_inc_gen:
  "aval' a s0 = (v, s') \<Longrightarrow> s0 x \<le> s' x"
  apply(induction a arbitrary: s0 v s')
  using aval'.induct
  by (fastforce split: prod.splits)+

lemma aval'_inc:
  "aval' a <> = (v, s') \<Longrightarrow> 0 \<le> s' x"
  unfolding null_state_def
  using aval'_inc_gen
  by force

end
