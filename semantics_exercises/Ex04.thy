theory Ex04
  imports Main
begin

inductive ev :: "nat \<Rightarrow> bool" where
  ev0: "ev 0" |
  evSS: "ev n \<Longrightarrow> ev (Suc (Suc n))"

lemma "ev (Suc (Suc n)) \<Longrightarrow> ev n"
proof -
  assume "ev (Suc (Suc n))" then show "ev n"
  proof (cases)
    case evSS
    then show ?thesis by auto
  qed
qed

inductive_cases evSS_elim: "ev (Suc (Suc n))"

lemma "\<not> ev (Suc (Suc (Suc 0)))"
proof 
  assume " ev (Suc (Suc (Suc 0)))"
  then show False
  proof cases
    case evSS
    then show ?thesis using ev.cases by blast
    qed
qed

type_synonym ('q,'l) lts = "'q \<Rightarrow> 'l \<Rightarrow> 'q \<Rightarrow> bool"

inductive word :: "('q,'l) lts \<Rightarrow> 'q \<Rightarrow> 'l list \<Rightarrow> 'q \<Rightarrow> bool" for \<delta> where
word_refl : "word \<delta> u [] u" |
word_step : "\<delta> u x v \<Longrightarrow> word \<delta> u [x] v" | 
word_steps : "\<lbrakk>\<delta> u x v; word \<delta> v xs w \<rbrakk> \<Longrightarrow> word \<delta> u (x # xs) w" 


definition "det \<delta> \<equiv> \<forall>p l q1 q2. \<delta> p l q1 \<and> \<delta> p l q2 \<longrightarrow> q1 = q2"

lemma 
    assumes det: "det \<delta>"
  shows "word \<delta> p ls q \<Longrightarrow> word \<delta> p ls q' \<Longrightarrow> q = q'"
proof (induction rule: word.induct)
  case (word_refl u)
  then show ?case using word.cases by fastforce
next
  case (word_step u x v)
  then show ?case using word.cases by (metis (no_types, lifting) det det_def list.distinct(1) list.inject)
next
  case (word_steps u x v xs w)
  then show ?case by (smt (verit) Ex04.word.simps det det_def list.discI list.inject
      word.cases)
qed

fun count :: "'a \<Rightarrow> 'a list \<Rightarrow> nat" where
  "count x [] = 0"
| "count x (y # ys) = (if x=y then Suc (count x ys) else count x ys)"


lemma 
    assumes "count a xs = Suc n"
    shows "\<exists>ps ss. xs = ps @ a # ss \<and> count a ps = 0 \<and> count a ss = n"
  using assms 
proof (induction a xs arbitrary: n rule: count.induct)
  case (1 x)
  then show ?case by simp
next
  case (2 a x xs)
  then show ?case
  proof (cases "a = x")
    case True
    with 2 have "x # xs = [] @ a # xs" "count a [] = 0" "count a xs = n" by auto
    then show ?thesis by blast
  next
    case False
    with 2 obtain ss ps where "xs = ps @ a # ss" "count a ps = 0" "count a ss = n" by auto
    moreover with False have "x # xs = (x # ps) @ a # ss" "count a (x # ps) = 0" by auto
    ultimately show ?thesis by blast
  qed
qed

end