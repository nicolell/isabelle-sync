theory Check
  imports Submission
begin

theorem sat_iff_model: "sat \<phi> \<sigma> \<longleftrightarrow> \<sigma> \<in> models \<phi>"
  by (rule Submission.sat_iff_model)

theorem simplify_simplified: "simplified (simplify \<phi>)"
  by (rule Submission.simplify_simplified)

theorem simplify_models: "models (simplify \<phi>) = models \<phi>"
  by (rule Submission.simplify_models)

end