theory Submission
  imports Defs
begin

value "has_const TT"

fun sat :: "bexp' \<Rightarrow> assignment \<Rightarrow> bool"  where
  "sat TT _ = True" |
"sat FF _ = False" |
"sat (And e1 e2) a = (if (sat e1 a) \<and> (sat e2 a) then True else False)" |
"sat (V s) a = a s" |
"sat (Not e) a = (if (sat e a) then False else True)"

value "sat (And TT FF) (\<lambda>x. True)"
value "sat (Not (V x)) (\<lambda>x. True)"
value "sat (V x) (\<lambda>x. True)" 

fun models :: "bexp' \<Rightarrow> assignment set" where
  "models (V x) = {\<sigma>. \<sigma> x}" 
| "models TT = UNIV"
| "models FF = {} "|
"models (And e1 e2) = (models e1) \<inter> (models e2)" |
"models (Not e) = - (models e)"

theorem sat_iff_model: "sat \<phi> \<sigma> \<longleftrightarrow> \<sigma> \<in> models \<phi>"
  apply(induction rule: models.induct)
  apply(auto)
  done

fun s_and :: "bexp'\<Rightarrow> bexp'  \<Rightarrow> bexp'" where
"s_and TT TT = TT" |
"s_and TT FF = FF" |
"s_and FF TT = FF" |
"s_and FF FF = FF" |
"s_and TT e = e" |
"s_and FF e = FF" |
"s_and e TT = e" |
"s_and e FF = FF" |
"s_and e1 e2 = And e1 e2"

fun s_not :: "bexp' \<Rightarrow> bexp'" where
"s_not TT = FF" |
"s_not FF = TT" |
"s_not e = Not e"



value "sat (s_and TT FF) s"
value " sat (And TT FF) s"

lemma sat_s_and [simp]:
"sat (s_and e1 e2) s = sat (And e1 e2) s"
  apply (induction e1 e2 rule: s_and.induct)
  apply (auto)
  done

lemma sat_s_not [simp]:
"sat (s_not e) s = sat (Not e) s"
  apply (induction e rule: s_not.induct)
  apply (auto)
  done

fun simplify :: "bexp' \<Rightarrow> bexp'" where
"simplify TT = TT" |
"simplify FF = FF" |
"simplify (V v) = V v" |
"simplify (And e1 e2) = s_and (simplify e1) (simplify e2)" |
"simplify (Not e) = s_not (simplify e)"

value "simplify (And (Not FF) (V ''x'')) = V ''x''"

value "simplify (And (Not FF) (V ''x''))"
value "simplify (And TT (V ''x''))"
value "simplify (And (Not FF) (V ''x'')) = V ''x''"

value "simplified TT"

lemma s_not_simplified: "e = TT \<or> e = FF \<or> e = (V v) \<Longrightarrow> simplified (s_not e)"
  apply(induction e rule: s_not.induct)
  unfolding simplified_def
      apply(auto)
  done

lemma simplify_id [simp]: "e = TT \<or> e = FF \<or> e = (V v) \<Longrightarrow> simplified e"
  apply(induction e)
  unfolding simplified_def
  apply(auto)
  done

lemma simplified_s_not [simp]: "simplified e \<Longrightarrow> simplified (s_not e)"
  apply(induction e)
  unfolding simplified_def
  apply(auto)
  done

lemma s_and_simplified [simp]: "simplified (And e1 e2) \<Longrightarrow> simplified (s_and e1 e2)"
  apply(induction e1 e2 rule: s_and.induct)
  unfolding simplified_def
  apply(auto)
  done 

lemma more [simp]: "(e = TT \<or> e = FF \<or> e = (V v)) \<and> simplified e2 \<Longrightarrow> simplified (s_and e e2)"
  apply(induction e2)
  unfolding simplified_def
  apply(auto)
  done

lemma s_and_and [simp]: "simplified (And e11 e12) \<Longrightarrow>
       simplified e2 \<Longrightarrow> simplified (s_and (And e11 e12) e2)"
  apply(induction e2)
  unfolding simplified_def
  apply(auto)
  done

lemma s_and_not [simp]: "simplified (Not e1) \<Longrightarrow> simplified e2 \<Longrightarrow> simplified (s_and (Not e1) e2)"
  apply(induction e2)
  unfolding simplified_def
  apply(auto)
  done

lemma simplified_s_and [simp]: "simplified e1 \<Longrightarrow> simplified e2 \<Longrightarrow> simplified (s_and e1 e2)"
  apply(induction e1 arbitrary: e2)
  apply(auto)
  done

theorem simplify_simplified: "simplified (simplify \<phi>)"
  apply(induction \<phi> rule: simplify.induct)
      apply(auto)
  done






lemma s_not_models [simp]: "models (s_not e) = models (Not e)"
  apply(induction e)
  apply(auto)
  done

lemma s_and_models_eq [simp]: "models (s_and e1 e2) = models (And e1 e2) "
  apply(induction e1 e2 rule: s_and.induct)
  apply(auto)
  done 


theorem simplify_models: "models (simplify \<phi>) = models \<phi>"
  apply(induction \<phi>)
  apply(auto)
  done

end