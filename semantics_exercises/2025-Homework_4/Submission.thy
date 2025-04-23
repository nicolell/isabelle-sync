theory Submission
  imports Defs
begin

inductive prod :: "('q\<^sub>1,'l) lts \<Rightarrow> ('q\<^sub>2,'l) lts \<Rightarrow> 'q\<^sub>1\<times>'q\<^sub>2 \<Rightarrow> 'l \<Rightarrow> 'q\<^sub>1\<times>'q\<^sub>2 \<Rightarrow> bool" for \<delta>\<^sub>1 \<delta>\<^sub>2 where
p_step [intro]: "\<lbrakk>\<delta>\<^sub>1 p1 l p2; \<delta>\<^sub>2 q1 l q2\<rbrakk> \<Longrightarrow> prod \<delta>\<^sub>1 \<delta>\<^sub>2 (p1,q1) l (p2,q2)"

value "p\<^sub>1 p\<^sub>2 q\<^sub>1 q\<^sub>2"
inductive_cases epsilonE[elim]: "word \<delta> q [] q'"
inductive_cases stepE[elim]: "word \<delta> q (x # xs) q'"
declare word.intros [simp, intro]

text " induction over the goal state q1,q2 because that's how word is defined"
theorem prod_sound:
    assumes "word (prod \<delta>\<^sub>1 \<delta>\<^sub>2) (p\<^sub>1,p\<^sub>2) ls (q\<^sub>1,q\<^sub>2)"
    shows "word \<delta>\<^sub>1 p\<^sub>1 ls q\<^sub>1 \<and> word \<delta>\<^sub>2 p\<^sub>2 ls q\<^sub>2"
  using assms
proof (induction "(p\<^sub>1,p\<^sub>2)" ls "(q\<^sub>1,q\<^sub>2)" arbitrary: p\<^sub>1 p\<^sub>2 q\<^sub>1 q\<^sub>2 rule: word.induct)
  case empty
  then show ?case using assms empty.prems by auto
next
  case (prepend l ph ls)
  then show ?case using assms prepend.prems 
  by (metis (no_types, lifting) Defs.word.prepend Product_Type.prod.inject
      Submission.prod.simps)
qed




lemma prod_complete:
    assumes "word \<delta>\<^sub>1 p\<^sub>1 ls q\<^sub>1"
      and "word \<delta>\<^sub>2 p\<^sub>2 ls q\<^sub>2"
  shows "word (prod \<delta>\<^sub>1 \<delta>\<^sub>2) (p\<^sub>1,p\<^sub>2) ls (q\<^sub>1,q\<^sub>2)"
using assms
proof (induction ls q\<^sub>1 arbitrary: p\<^sub>2 q\<^sub>2 rule: word.induct)
  case empty
  then show ?case using assms empty.prems by auto
next
  case (prepend p l ph ls q)
  then  obtain qh where  "\<delta>\<^sub>2 p\<^sub>2 l qh" and "word \<delta>\<^sub>2 qh ls q\<^sub>2" by (metis stepE)
  then show ?case using assms prepend by auto
qed


corollary "{w. word (prod \<delta>\<^sub>1 \<delta>\<^sub>2) (p\<^sub>1,p\<^sub>2) w (q\<^sub>1,q\<^sub>2)} = {w. word \<delta>\<^sub>1 p\<^sub>1 w q\<^sub>1} \<inter> {w. word \<delta>\<^sub>2 p\<^sub>2 w q\<^sub>2}"
  using prod_sound prod_complete by fast

text "you will need auxiliary lemmas
about aval and exec with changed state (those need induction)"

lemma aval_helper [simp] : "aval a s \<le> aval a (s(x := (s x) + 1))"
proof (induction a arbitrary: s)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus a1 a2)
  then show ?case 
  by (smt (verit) AExp.aval.simps(3))
qed


lemma aval_state [simp] : "\<lbrakk>x \<in> vars a\<rbrakk> \<Longrightarrow> aval a s \<noteq> aval a (s(x := (s x) + 1))"
proof (induction a)
  case (N x)
  then show ?case by simp
next
  case (V x)
  then show ?case by simp
next
  case (Plus a1 a2)
  then have "aval (Plus a1 a2) s = aval a1 s + aval a2 s" by simp
  moreover have "aval (Plus a1 a2) (s(x := (s x) + 1)) = aval a1 (s(x := (s x) + 1)) + aval a2 (s(x := (s x) + 1))" by simp
  moreover have "aval a1 s \<le> aval a1 (s(x := (s x) + 1))" by simp
  moreover have "aval a2 s \<le> aval a2 (s(x := (s x) + 1))" by simp
  moreover have "(aval a1 s \<noteq> aval a1 (s(x := (s x) + 1))) \<or> (aval a2 s \<noteq> aval a2 (s(x := (s x) + 1)))" using Plus.prems Plus.IH by auto
  moreover have "(aval a1 s < aval a1 (s(x := (s x) + 1))) \<or> (aval a2 s < aval a2 (s(x := (s x) + 1)))"  using calculation(3,4,5) by linarith
  moreover have "aval (Plus a1 a2) s \<le> aval (Plus a1 a2) (s(x := (s x) + 1))"  using calculation(1,2,3,4) by linarith
  ultimately show ?case by arith
qed

lemma exec1_state [simp] : "(LOAD x) \<noteq> i \<Longrightarrow> exec1 i s stk = exec1 i (s(x := (s x) + 1)) stk"
proof -
  assume "(LOAD x) \<noteq> i"
  show "exec1 i s stk = exec1 i (s(x := (s x) + 1)) stk"
proof(rule ccontr)
  assume "exec1 i s stk \<noteq> exec1 i (s(x := s x + 1)) stk"
  then show False
  proof (cases i)
    case (LOADI x1)
    then have "exec1 (LOADI x1) s stk = Some (x1 # stk)" by simp
    moreover have "exec1 (LOADI x1) (s(x := s x + 1)) stk = Some (x1 # stk)" by simp
    ultimately show ?thesis using LOADI \<open>exec1 i s stk \<noteq> exec1 i (s(x := s x + 1)) stk\<close> by auto
  next
    case (LOAD x2)
    then have "exec1 (LOAD x2) s stk = Some ((s x2) # stk)" by simp
    moreover have "s x2 = (s(x := s x + 1)) x2"  using LOAD \<open>LOAD x \<noteq> i\<close> by auto
    moreover have "exec1 (LOAD x2) (s(x := s x + 1)) stk = Some ((s x2) # stk)"  by (simp add: calculation(2))
    ultimately show ?thesis using LOAD \<open>exec1 i s stk \<noteq> exec1 i (s(x := s x + 1)) stk\<close> by fastforce
  next
    case ADD
    then have "exec1 ADD s stk = exec1 ADD (s(x := (s x) + 1)) stk" using exec1.simps by auto
    then show ?thesis using ADD \<open>exec1 i s stk \<noteq> exec1 i (s(x := s x + 1)) stk\<close> by auto
  qed
qed
qed


lemma exec_state [simp] : "\<lbrakk>LOAD x \<notin> set ins\<rbrakk> \<Longrightarrow> exec ins (s(x := (s x) + 1)) stk = exec ins s stk"
proof (induction ins "(s(x := (s x) + 1))" stk arbitrary: s x rule: exec.induct)
  case (1 stk)
  then show ?case by simp
next
  case (2 i ins stk) 
  then show ?case using "2.prems"
  proof (cases "exec1 i (s(x := s x + 1)) stk")
    case None
    then show ?thesis  by (metis "local.2.prems" Defs.exec.simps(2) List.list.set_intros(1) Option.option.simps(4)
        exec1_state)
  next
    case (Some a)
    then have "exec1 i (s(x := s x + 1)) stk = Some a" by simp
    moreover have "exec1 i s stk = Some a" by (metis "local.2.prems" List.list.set_intros(1) calculation exec1_state)
    moreover have "exec ins s a = exec ins (s(x := s x + 1)) a"  by (metis "local.2.hyps" "local.2.prems" List.list.set_intros(2) Some)
    moreover have "exec (i # ins) s stk = exec ins s a" using exec.cases \<open>exec1 i s stk = Some a\<close> by auto
    moreover have "exec (i # ins) (s(x := s x + 1)) stk = exec ins (s(x := s x + 1)) a" using exec.cases \<open>exec1 i (s(x := s x + 1)) stk = Some a\<close> by simp
    ultimately show ?thesis by presburger
  qed
qed

theorem vars_in_ins:
    assumes "x \<in> vars a"
    shows "correct a ins \<Longrightarrow> LOAD x \<in> set ins"
  using assms correct_def
proof -
  assume "x \<in> vars a" "correct a ins"
  show "LOAD x \<in> set ins"
proof (rule ccontr)
  assume " LOAD x \<notin> set ins"
  then have "\<forall>s stk. exec ins s stk = Some (aval a s # stk)" using \<open>correct a ins\<close> correct_def by blast
  fix s stk 
  have "exec ins s stk = Some (aval a s # stk)" using \<open>correct a ins\<close> correct_def by fastforce
  moreover have "exec ins (s(x := (s x) + 1)) stk = Some (aval a (s(x := (s x) + 1)) # stk)" using \<open>correct a ins\<close> correct_def by fastforce
  moreover have "aval a s \<noteq> aval a (s(x := (s x) + 1))" using aval_state assms by blast
  moreover have "exec ins s stk = exec ins (s(x := (s x) + 1)) stk" by (simp add: \<open>LOAD x \<notin> set ins\<close>)
  ultimately show "False" by auto
qed
qed
  

end