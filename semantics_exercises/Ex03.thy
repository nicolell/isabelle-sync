theory Ex03
  imports "HOL-IMP.ASM"
begin

inductive star :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl :  "star r x x" |
trans : "r x y \<Longrightarrow> star r y z \<Longrightarrow> star r x z"

declare star.intros[intro]

lemma star_prepend: "\<lbrakk>r x y; star r y z\<rbrakk> \<Longrightarrow> star r x z"
  by auto

lemma star_append: "\<lbrakk> star r x y; r y z \<rbrakk> \<Longrightarrow> star r x z"
  by (induction rule: star.induct) auto

inductive star' :: "('a \<Rightarrow> 'a \<Rightarrow> bool) \<Rightarrow> 'a \<Rightarrow> 'a \<Rightarrow> bool" for r where
refl' :  "star' r x x" |
trans' : "star' r x y \<Longrightarrow>  r y z \<Longrightarrow> star' r x z"

declare star'.intros[intro]

lemma star'_prepend [intro]:
  assumes "r x y"
  and "star' r y z"
  shows "star' r x z"
  using assms(2,1)
  by (induction rule: star'.induct) auto

lemma star'_append [intro]:
  assumes "star' r x y"
and "r y z"
shows "star' r x z"
  using assms(2,1)
  by auto


lemma "star r x y = star' r x y"
  proof
    assume "star r x y"
    thus "star' r x y"
      by induct (auto intro: star'.intros)
  next
    assume "star' r x y"
    thus "star r x y"
      by induct (auto intro: star.intros star_append)
  qed

fun exec1 :: "instr \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option"  where
  "exec1 _ = undefined"

fun exec :: "instr list \<Rightarrow> state \<Rightarrow> stack \<Rightarrow> stack option"  where
  "exec _ = undefined"

theorem exec_comp: "exec (comp a) s stk = Some (aval a s # stk)"
  sorry

lemma 
    assumes total: "\<forall>x y. T x y \<or> T y x"
      and anti: "\<forall>x y. A x y \<and> A y x \<longrightarrow> x = y"
      and subset: "\<forall>x y. T x y \<longrightarrow> A x y"
  shows "A x y \<longrightarrow> T x y"
    (* using assms by blast *)
proof 
  fix x y assume "A x y"
  from total have "T x y \<or> T y x" by simp
  then show "T x y"
  proof 
    assume "T x y" then show ?thesis .
    next
      assume "T y x"
      with subset have "A y x" by simp
      with \<open>A x y\<close> anti have "x = y" by simp
      with \<open>T y x\<close> show ?thesis by simp 
    qed
qed
  

end