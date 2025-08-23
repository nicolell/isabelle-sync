theory Submission
  imports Defs
begin

lemma count_app [simp] : "count (xs @ ys) x = count xs x + count ys x"
  apply(induction xs arbitrary: x ys)
   apply(auto)
  done

theorem S_count : "S xs \<Longrightarrow> count xs Open = count xs Close"
  apply(induction xs rule: S.induct)
    apply(auto)
  done

inductive T :: "paren list \<Rightarrow> bool" where
T_0 : "S xs \<Longrightarrow> T xs" |
T_open: "T xs \<Longrightarrow> T (Open # xs)"

declare T.intros [intro, simp]
declare S.intros [intro, simp]
lemma example: "T [Open, Open]" by simp

theorem S_T: "S xs \<Longrightarrow> T xs" by simp

lemma T_count: "T xs \<Longrightarrow> count xs Open \<ge> count xs Close"
  apply(induction xs rule: T.induct)
  apply(simp_all add: S_count)
  done

lemma lem2 : "\<lbrakk>T xs; Suc (count xs Open) = count xs Close \<rbrakk> \<Longrightarrow> T (Open # xs)"
  apply(induction xs rule: T.induct)
  apply(auto)
  done

value "S (Open # xs)"



lemma S_count2: "S xs \<Longrightarrow> (\<not> (S (Open # xs)))" by (metis S_count count.simps(2) n_not_Suc_n paren.distinct(1))

lemma T_count2: "T xs \<Longrightarrow> Suc (count xs Open) \<noteq> count xs Close" by (metis Suc_n_not_le_n T_count)

theorem T_S: "T xs \<Longrightarrow> count xs Open = count xs Close \<Longrightarrow> S xs"
  apply(induction xs rule: T.induct)
  apply(simp_all add: S_count T_count S_count2 T_count2)
  done

fun op_val :: "op \<Rightarrow> mstate \<Rightarrow> int"  where
  "op_val (REG r) \<sigma>  = \<sigma> (Reg r)" |
  "op_val (VAL v) \<sigma> = v"

fun exec1 :: "instr \<Rightarrow> mstate \<Rightarrow> mstate"  where
  "exec1 (LD r v) \<sigma> = \<sigma>((Reg r):= \<sigma>(Var v))" |
  "exec1 (ADD r a b) \<sigma> = \<sigma>((Reg r):= (op_val a \<sigma> + op_val b \<sigma>))"

fun exec :: "instr list \<Rightarrow> mstate \<Rightarrow> mstate"  where
  "exec [] rs = rs" |
  "exec ((LD r v) # xs) rs = exec xs (exec1 (LD r v) rs)" |
  "exec ((ADD r a b) # xs) rs = exec xs (exec1 (ADD r a b) rs)" 


fun cmp :: "aexp \<Rightarrow> reg \<Rightarrow> instr list" where
  "cmp (N n) r = [ADD r (VAL n) (VAL 0)]" |
  "cmp (V v) r = [LD r v]" |
  "cmp (Plus (N n) (N m)) r = [ADD r (VAL n) (VAL m)]" |
  "cmp (Plus (N n) b) r = (cmp b r) @ [ADD r (VAL n) (REG r)]" |
  "cmp (Plus b (N n)) r = (cmp b r) @ [ADD r (VAL n) (REG r)]" |
  "cmp (Plus a b) r = (cmp a r) @ (cmp b (Suc r)) @ [ADD r (REG r) (REG (Suc r))]"


theorem cmp_len: "\<not>is_N a \<Longrightarrow> num_add (cmp a r) \<le> num_plus a"
  apply(induction r rule: cmp.induct)
  unfolding is_N_def
  apply(auto split: aexp.split)
  done

lemma reg_var[simp]: "s (Reg r := x) o Var = s o Var"
  by auto

lemma cmp_r [simp]: "(r' < r) \<Longrightarrow> exec (cmp a r) rs (Reg r') = rs (Reg r')"
  sorry

lemma cmp_app [simp] : "exec (is1 @ is2) rs = exec is2 (exec is1 rs)"
  sorry

lemma cmp_plus_decomp [simp] : "exec (cmp (Plus a b) r) rs (Reg r) = exec (cmp a r) rs (Reg r) + exec (cmp b r) rs (Reg r)"
  sorry


theorem cmp_correct: "exec (cmp a r) \<sigma> (Reg r) = aval a (\<sigma> o Var)"
  apply(induction a arbitrary: r \<sigma>)
    apply(auto split: aexp.split)
  done

end