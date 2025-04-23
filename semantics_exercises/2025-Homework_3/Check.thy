theory Check
  imports Submission
begin

theorem S_count: "S xs \<Longrightarrow> count xs Open = count xs Close"
  by (rule Submission.S_count)

lemma example: "T [Open, Open]"
  by (rule Submission.example)

theorem S_T: "S xs \<Longrightarrow> T xs"
  by (rule Submission.S_T)

theorem T_S: "T xs \<Longrightarrow> count xs Open = count xs Close \<Longrightarrow> S xs"
  by (rule Submission.T_S)

theorem cmp_len: "\<not>is_N a \<Longrightarrow> num_add (cmp a r) \<le> num_plus a"
  by (rule Submission.cmp_len)

theorem cmp_correct: "exec (cmp a r) \<sigma> (Reg r) = aval a (\<sigma> o Var)"
  by (rule Submission.cmp_correct)

end