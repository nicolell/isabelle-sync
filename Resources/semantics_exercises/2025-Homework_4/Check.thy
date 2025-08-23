theory Check
  imports Submission
begin

theorem prod_sound: "(word (prod \<delta>\<^sub>1 \<delta>\<^sub>2) (p\<^sub>1,p\<^sub>2) ls (q\<^sub>1,q\<^sub>2)) \<Longrightarrow> word \<delta>\<^sub>1 p\<^sub>1 ls q\<^sub>1 \<and> word \<delta>\<^sub>2 p\<^sub>2 ls q\<^sub>2"
  by (rule Submission.prod_sound)

lemma prod_complete: "(word \<delta>\<^sub>1 p\<^sub>1 ls q\<^sub>1) \<Longrightarrow> (word \<delta>\<^sub>2 p\<^sub>2 ls q\<^sub>2) \<Longrightarrow> word (prod \<delta>\<^sub>1 \<delta>\<^sub>2) (p\<^sub>1,p\<^sub>2) ls (q\<^sub>1,q\<^sub>2)"
  by (rule Submission.prod_complete)

theorem vars_in_ins: "(x \<in> vars a) \<Longrightarrow> correct a ins \<Longrightarrow> LOAD x \<in> set ins"
  by (rule Submission.vars_in_ins)

end