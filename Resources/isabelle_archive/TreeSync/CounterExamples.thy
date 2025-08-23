theory CounterExamples
  imports CommunicatingAutomaton

begin

context NetworkOfCA
begin

section "counterexample stuff"

subsection "second condition fix "

(*the right set of the new subset relation, with !? signs not removed yet
essentially it takes any prefix of p (and thus a valid word in its infl. language) 
and checks if the receives that happend thus far in the prefix
and those that might come afterwards (i.e. in any possible suffix s.t. the concatenated word remains in the lang.)
→ in other words, the set of all possible receives of&after prefix w (including the receives of w)*)
abbreviation possible_recvs_of_peer_prefix :: "('information, 'peer) action word ⇒ 'peer ⇒  ('information, 'peer) action language"  ("⟦_⟧⇩_" [90, 90] 110) where  
  "⟦w⟧⇩p ≡ {y⋅x | x y. (w ⋅ x) ∈ ℒ⇧*(p) ∧ (x = x↓⇩?) ∧ prefix y (w↓⇩?)}"


definition subset_condition1 :: "'peer ⇒ 'peer ⇒ bool"
  where "subset_condition1 p q ⟷ (∀ w ∈ ℒ⇧*(p). ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (⟦w⟧⇩p)⇂⇩!⇩? )"

definition subset_condition1_alt :: "'peer ⇒ 'peer ⇒ bool"
  where "subset_condition1_alt p q ⟷ (∀ w ∈ ℒ⇧*(p). (∀ w' ∈ ℒ⇧*(q). ((w'↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∈ ((⟦w⟧⇩p)⇂⇩!⇩?)))"

lemma subset_cond1_parent_infl_lang: 
  assumes "((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (⟦w⟧⇩p)⇂⇩!⇩?"
  shows "(∀ w' ∈ ℒ⇧*(q). ((w'↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∈ ((⟦w⟧⇩p)⇂⇩!⇩?))"
  by (smt (z3) Collect_mono_iff assms mem_Collect_eq)

lemma subset_conds1_eq:
  shows "subset_condition1_alt p q ⟷ subset_condition1 p q" 
  sorry


lemma subset_condition1_alt_concrete:
  assumes "w' ∈ ℒ⇧*(q)" and "w ∈ ℒ⇧*(p)" and  "subset_condition1 p q" 
  shows "((w'↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∈ ((⟦w⟧⇩p)⇂⇩!⇩?)"
proof -
  have "subset_condition1_alt p q" by (simp add: assms(3) subset_conds1_eq)
  then show ?thesis using assms(1,2) subset_condition1_alt_def by force
qed

definition theorem_rightside2 :: "bool"
  where "theorem_rightside2 ⟷ (∀p ∈ 𝒫. ∀q ∈ 𝒫. ((is_parent_of p q) ⟶ ((subset_condition1 p q) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))"

lemma shuffled_lang_cond_for_node:
  assumes "(∀p q. ((is_parent_of p q) ⟶ ((subset_condition1 p q) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))"
  shows "(∀p ∈ 𝒫. ((is_node p) ⟶ (((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))"
  by (metis UNIV_I assms node_parent path_from_root.simps path_to_root_exists paths_eq root_defs_eq)


subsection "counterexample 1 to original theorem"

lemma
  assumes Aq: "𝒜 q = ({q0, q1}, q0, {(q0, (!⟨(a⇗q→p⇖)⟩), q1)})" and "is_root q" 
and Lq: "ℒ q = {ε, [(!⟨(a⇗q→p⇖)⟩)]}" 
and " q0 ≠ q1 "
shows "ℒ q ⊆ ℒ⇧* q"
  using assms(2) lang_subset_infl_lang by blast

lemma CE1_trace: 
 assumes Ap: "𝒜 p = ({p0, p1}, p0, {(p0, (?⟨(a⇗q→p⇖)⟩), p1), (p0, (!⟨(b⇗p→x⇖)⟩), p1)})"
and Aq: "𝒜 q = ({q0, q1}, q0, {(q0, (!⟨(a⇗q→p⇖)⟩), q1)})"
and Ax: "𝒜 x = ({x0, x1}, x0, {(x0, (?⟨(b⇗p→x⇖)⟩), x1)})"
and Ms: "ℳ = {(a⇗q→p⇖), (b⇗p→x⇖)}"
and Ps: "𝒫 = {p,q,x}"
  and G: "𝒢 = {(q,p), (p,x)}" 
and peers_diff: "q ≠ x ∧ x ≠ p ∧ q ≠ p"
and states_diff: "p0 ≠ p1 ∧ q0 ≠ q1 ∧ x0 ≠ x1"
shows "[(!⟨(a⇗q→p⇖)⟩), (!⟨(b⇗p→x⇖)⟩)] ∈ 𝒯⇘None⇙" 
  using assms 
proof - 
  have "(q0, (!⟨(a⇗q→p⇖)⟩), q1) ∈ ℛ q"  using Aq by auto 
  then have "q0 ─(!⟨(a⇗q→p⇖)⟩)→q q1" by simp
  then have step1: "mbox_step (𝒞⇩ℐ⇩𝔪) (!⟨(a⇗q→p⇖)⟩) None (((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)])))"
    by (metis (no_types, lifting) Ap Aq fst_conv initial_configuration_is_mailbox_configuration self_append_conv2
        send_trans_to_mbox_step snd_conv)
  have s0: "p0 ─(!⟨(b⇗p→x⇖)⟩)→p p1" by (simp add: Ap)
  have s1: "is_mbox_config (((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)])))" using ‹(λp. (𝒞⇩ℐ⇩𝟬 p, ε)) ─⟨!⟨(a⇗q→p⇖)⟩, ∞⟩→ (λp. (𝒞⇩ℐ⇩𝟬 p, ε)) (q := (q1, ε), p := (p0, a⇗q→p⇖ # ε))›
      mbox_step_rev(2) by auto 
  have "(𝒞⇩ℐ⇩𝔪) x = (x0, ε)" using Ax by auto 
  then have s2: "(((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)]))) x = (x0, ε)"  using peers_diff by force

  have "fst ((((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)]))) p) = p0 ∧ fst (((((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p1, [(a⇗q→p⇖)])))(x:= (x0, [b⇗p→x⇖]))) p) = p1" 
    using peers_diff by auto
  then have s3: "let C1 = (((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)]))); C2 = ((((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p1, [(a⇗q→p⇖)])))(x:= (x0, [b⇗p→x⇖]))) 
in fst (C1 p) ─(!⟨(b⇗p→x⇖)⟩)→p (fst (C2 p))"
    using s0 by fastforce
  have s4: "let C1 = (((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)]))); C2 = ((((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p1, [(a⇗q→p⇖)])))(x:= (x0, [b⇗p→x⇖]))) 
in snd (C1 p) = snd (C2 p) " 
    using peers_diff by force
  have C2_1: "((((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p1, [(a⇗q→p⇖)])))(x:= (x0, [b⇗p→x⇖]))) x = (x0, [(b⇗p→x⇖)])" by simp
  have C2_2: "(((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)]))) x = (x0, ε)" using s2 by metis 
  then have C2_buf: "let C1 = (((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)]))); C2 = ((((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p1, [(a⇗q→p⇖)])))(x:= (x0, [b⇗p→x⇖])))
in C2 x = (fst (C1 x), (snd (C1 x)) ⋅ [(b⇗p→x⇖)])"
    by simp

  have "let C1 = (((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)]))); C2 = ((((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p1, [(a⇗q→p⇖)])))(x:= (x0, [b⇗p→x⇖])))
in (∀y. y ∉ {p, x} ⟶ C1(y) = C2(y))" by simp

  then have "let C1 = (((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)]))); C2 = ((((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p1, [(a⇗q→p⇖)])))(x:= (x0, [b⇗p→x⇖])))
in
is_mbox_config C1 ∧ fst (C1 p) ─(!⟨(b⇗p→x⇖)⟩)→p (fst (C2 p)) ∧
            snd (C1 p) = snd (C2 p) ∧ ( | (snd (C1 q)) | ) <⇩ℬ None ∧
            C2 x = (fst (C1 x), (snd (C1 x)) ⋅ [(b⇗p→x⇖)]) ∧  (∀y. y ∉ {p, x} ⟶ C1(y) = C2(y))"
    using s0 s1 s2 s3 s4 C2_buf by simp
    then have step2: "mbox_step (((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)])))  (!⟨(b⇗p→x⇖)⟩) None
((((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p1, [(a⇗q→p⇖)])))(x:= (x0, [b⇗p→x⇖])))"  by (meson gen_send_step_to_mbox_step)
    from step1 have "let C1 = (((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)]))) in
mbox_run (𝒞⇩ℐ⇩𝔪) None [(!⟨(a⇗q→p⇖)⟩)] ([C1])" by (simp add: mbox_step_to_run)
    then have "let C1 = (((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)]))); C2 = ((((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p1, [(a⇗q→p⇖)])))(x:= (x0, [b⇗p→x⇖])))
in mbox_run (𝒞⇩ℐ⇩𝔪) None [(!⟨(a⇗q→p⇖)⟩)] ([C1]) ∧ last ((𝒞⇩ℐ⇩𝔪)#[C1]) ─⟨(!⟨(b⇗p→x⇖)⟩), ∞⟩→ C2"
      using step2 by auto 
    then have "let C1 = (((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p0, [(a⇗q→p⇖)]))); C2 = ((((𝒞⇩ℐ⇩𝔪)(q:= (q1, ε)))(p:= (p1, [(a⇗q→p⇖)])))(x:= (x0, [b⇗p→x⇖])))
in mbox_run (𝒞⇩ℐ⇩𝔪) None [(!⟨(a⇗q→p⇖)⟩), (!⟨(b⇗p→x⇖)⟩)] ([C1] @ [C2])" using MRComposedInf 
      by (smt (verit, ccfv_threshold) append_Cons append_self_conv2)

    then show "[(!⟨(a⇗q→p⇖)⟩), (!⟨(b⇗p→x⇖)⟩)] ∈ 𝒯⇘None⇙" using MboxTraces.intros by auto
  qed

lemma CE1_not_sync: 
 assumes Ap: "𝒜 p = ({p0, p1}, p0, {(p0, (?⟨(a⇗q→p⇖)⟩), p1), (p0, (!⟨(b⇗p→x⇖)⟩), p1)})"
and Aq: "𝒜 q = ({q0, q1}, q0, {(q0, (!⟨(a⇗q→p⇖)⟩), q1)})"
and Ax: "𝒜 x = ({x0, x1}, x0, {(x0, (?⟨(b⇗p→x⇖)⟩), x1)})"
and Ms: "ℳ = {(a⇗q→p⇖), (b⇗p→x⇖)}"
and Ps: "𝒫 = {p,q,x}"
  and G: "𝒢 = {(q,p), (p,x)}" 
and peers_diff: "q ≠ x ∧ x ≠ p ∧ q ≠ p"
and states_diff: "p0 ≠ p1 ∧ q0 ≠ q1 ∧ x0 ≠ x1"
shows "[(!⟨(a⇗q→p⇖)⟩), (!⟨(b⇗p→x⇖)⟩)] ∉ ℒ⇩𝟬"
proof (rule ccontr)
  assume "¬ !⟨(a⇗q→p⇖)⟩ # !⟨(b⇗p→x⇖)⟩ # ε ∉ ℒ⇩𝟬" 
  then have "[(!⟨(a⇗q→p⇖)⟩), (!⟨(b⇗p→x⇖)⟩)] ∈ ℒ⇩𝟬" by simp
  then have "[(!⟨(a⇗q→p⇖)⟩)] ∈ ℒ⇩𝟬" by (metis append_Cons append_Nil sync_lang_app)
  have "sync_run 𝒞⇩ℐ⇩𝟬 [(!⟨(a⇗q→p⇖)⟩)] [((𝒞⇩ℐ⇩𝟬)(q:= q1))(p:= p1)]" sorry
  have s2_rule: "∀ s2. (𝒞⇩ℐ⇩𝟬 p) ─(?⟨(a⇗q→p⇖)⟩)→p s2 ⟶ s2 = p1"
  proof (rule ccontr)
    assume "¬ (∀s2. 𝒞⇩ℐ⇩𝟬 p ─(?⟨(a⇗q→p⇖)⟩)→p s2 ⟶ s2 = p1)" 
    then obtain s2 where s2_step: "𝒞⇩ℐ⇩𝟬 p ─(?⟨(a⇗q→p⇖)⟩)→p s2" and "p1 ≠ s2" and "s2 ∈ {p0, p1}" by (simp add: Ap)
    then have "s2 = p0" by simp
    then have "𝒞⇩ℐ⇩𝟬 p ─(?⟨(a⇗q→p⇖)⟩)→p p0" using s2_step by simp
    then have t1: "p0 ─(?⟨(a⇗q→p⇖)⟩)→p p0" by (simp add: Ap)
    have "(p0, (?⟨(a⇗q→p⇖)⟩), p0) ∉ ℛ p" using states_diff Ap by simp
    then show "False" using t1 by simp
  qed

  obtain yc C where "sync_run 𝒞⇩ℐ⇩𝟬 [(!⟨(a⇗q→p⇖)⟩), (!⟨(b⇗p→x⇖)⟩)] (yc@[C])"  by (metis SyncTraces_rev ‹!⟨(a⇗q→p⇖)⟩ # !⟨(b⇗p→x⇖)⟩ # ε ∈ ℒ⇩𝟬› list.discI sync_run.cases)
  then  have run_decomp: "sync_run 𝒞⇩ℐ⇩𝟬 [(!⟨(a⇗q→p⇖)⟩)] yc ∧ last (𝒞⇩ℐ⇩𝟬#yc) ─⟨(!⟨(b⇗p→x⇖)⟩), 𝟬⟩→ C" 
    sorry
  then have "length (yc) = 1" using sync_run_word_configs_len_eq[of "𝒞⇩ℐ⇩𝟬" "[(!⟨(a⇗q→p⇖)⟩)]" yc] by simp
  then obtain C1 where "length (yc) = 1" and C1_prop: "yc = [C1]" by (metis One_nat_def Suc_length_conv length_0_conv)
  have "sync_run 𝒞⇩ℐ⇩𝟬 [(!⟨(a⇗q→p⇖)⟩)] [C1]" using C1_prop run_decomp by auto 
  then have "𝒞⇩ℐ⇩𝟬 ─⟨(!⟨(a⇗q→p⇖)⟩), 𝟬⟩→ C1" using sync_run.cases by fastforce
  then have "C1 p = p1" by (meson s2_rule sync_send_step_to_recv_step)
  have "last (𝒞⇩ℐ⇩𝟬#yc) = last (𝒞⇩ℐ⇩𝟬#[C1])" by (simp add: C1_prop)
  then have "last (𝒞⇩ℐ⇩𝟬#yc) = C1" by simp
  then have "C1 ─⟨(!⟨(b⇗p→x⇖)⟩), 𝟬⟩→ C" using run_decomp by simp
  then have  "p1 ─(!⟨(b⇗p→x⇖)⟩)→p (C p)"  using ‹C1 p = p1› sync_step_output_rev(4) by blast
  then show "False" using Ap states_diff by auto
qed

lemma only_one_trans_in_Ap_to_p_lang:
  assumes "ℐ q = q0" and "ℛ q = {(q0, a, q1)}" and "q0 ≠ q1"
  shows "ℒ q = {ε, [a]}"
  using assms 
proof - 
  have  "ε ∈ ℒ q" by (meson CommunicatingAutomaton.REmpty2 CommunicatingAutomaton.Traces.simps automaton_of_peer)
  have "q0 ─a→q q1" by (simp add: assms(2))
  then have "[a] ∈ ℒ q" using trans_to_act_in_lang  using assms(1) by auto
  then have ea: "{ε, [a]} ⊆ ℒ q" by (simp add: ‹ε ∈ ℒ q›)
  have ea2: "ℒ q ⊆ {ε, [a]}"
  proof (rule ccontr)
    assume "¬ ℒ q ⊆ {ε, a # ε}" 
    then obtain w where w_def1: "w ∈ ℒ q" and we: "w ≠ ε" and wa: "w ≠ [a]" by auto 
    then show "False" using assms wa we proof (induct w) 
      case Nil
      then show ?case by simp
    next
      case (Cons x v)
      then have "∃s2 s3. (ℐ q) ─[x]→⇧*q s2 ∧ s2 ─v→⇧*q s3" by (metis lang_implies_prepend_run last_ConsL)
      then have "∃s2 s3. (ℐ q) ─x→q s2 ∧ s2 ─v→⇧*q s3" using lang_implies_trans by blast
      then obtain s2 s3 where "(ℐ q) ─x→q s2" and "s2 ─v→⇧*q s3" by blast
      then have "s2 = q1"  by (simp add: assms(2))
      then have v_run: "q1 ─v→⇧*q s3"  using ‹s2 = s3 ∧ v = ε ∧ s2 ∈ 𝒮 q ∨ (∃xs. run_of_peer_from_state q s2 v xs ∧ last xs = s3)› by auto
      then show ?case using Cons v_run
      proof (cases v) 
        case Nil
        then have "x # v = [x]" by simp
        then show ?thesis
        proof (cases "x = a")
          case True
          then show ?thesis using Cons.prems(3) local.Nil by fastforce
        next
          case False
          then have "(q0, x, s2) ∈ ℛ q" 
            using ‹𝒞⇩ℐ⇩𝟬 q ─x→q s2› assms(1) by auto
          then show ?thesis  using False assms(2) by auto
        qed
      next
        case (Cons y ys)

        then have "q1 ─([y]@ys)→⇧*q s3"  using v_run by auto
        then have "(∃xs. CommunicatingAutomaton.run (ℛ q) q1 ([y]@ys) xs ∧ last xs = s3)" by simp
        then obtain xs where "CommunicatingAutomaton.run (ℛ q) q1 ([y]@ys) xs" and "last xs = s3" by auto

        then have "CommunicatingAutomaton.run (ℛ q) q1 ([y]@ys) xs ∧ [y] ≠ ε" by auto
        then have "∃us vs. CommunicatingAutomaton.run (ℛ q) q1 [y] us ∧ CommunicatingAutomaton.run (ℛ q) (last us) ys vs ∧ xs = us @ vs" 
using CommunicatingAutomaton.run_app[of q "𝒮 q" q0 "ℳ" "(ℛ q)" q1 "[y]" ys xs] using assms(1) automaton_of_peer by blast
  then obtain us where "CommunicatingAutomaton.run (ℛ q) q1 [y] us" by blast
  then obtain sy where "q1 ─y→q sy"  by (meson lang_implies_trans)
  then show ?thesis using assms(2,3) by force
qed
qed
qed
  show ?thesis using ea ea2 by auto
qed


lemma CE1_infl_langs: 
 assumes Ap: "𝒜 p = ({p0, p1}, p0, {(p0, (?⟨(a⇗q→p⇖)⟩), p1), (p0, (!⟨(b⇗p→x⇖)⟩), p1)})"
and Aq: "𝒜 q = ({q0, q1}, q0, {(q0, (!⟨(a⇗q→p⇖)⟩), q1)})"
and Ax: "𝒜 x = ({x0, x1}, x0, {(x0, (?⟨(b⇗p→x⇖)⟩), x1)})"
and Ms: "ℳ = {(a⇗q→p⇖), (b⇗p→x⇖)}"
and Ps: "𝒫 = {p,q,x}"
  and G: "𝒢 = {(q,p), (p,x)}" 
and peers_diff: "q ≠ x ∧ x ≠ p ∧ q ≠ p"
and states_diff: "p0 ≠ p1 ∧ q0 ≠ q1 ∧ x0 ≠ x1"
shows "∀peer ∈ 𝒫. ℒ⇧* peer = ℒ peer" using assms
  sorry

lemma CE1_original_subset_cond:
assumes Ap: "𝒜 p = ({p0, p1}, p0, {(p0, (?⟨(a⇗q→p⇖)⟩), p1), (p0, (!⟨(b⇗p→x⇖)⟩), p1)})"
and Aq: "𝒜 q = ({q0, q1}, q0, {(q0, (!⟨(a⇗q→p⇖)⟩), q1)})"
and Ax: "𝒜 x = ({x0, x1}, x0, {(x0, (?⟨(b⇗p→x⇖)⟩), x1)})"
and Ms: "ℳ = {(a⇗q→p⇖), (b⇗p→x⇖)}"
and Ps: "𝒫 = {p,q,x}"
  and G: "𝒢 = {(q,p), (p,x)}" 
and peers_diff: "q ≠ x ∧ x ≠ p ∧ q ≠ p"
and states_diff: "p0 ≠ p1 ∧ q0 ≠ q1 ∧ x0 ≠ x1"
shows "∀p ∈ 𝒫. ∀ q ∈ 𝒫. (((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (ℒ⇧*(p))⇂⇩!⇩?)"
  sorry

lemma CE1_shuffled_langs: 
 assumes Ap: "𝒜 p = ({p0, p1}, p0, {(p0, (?⟨(a⇗q→p⇖)⟩), p1), (p0, (!⟨(b⇗p→x⇖)⟩), p1)})"
and Aq: "𝒜 q = ({q0, q1}, q0, {(q0, (!⟨(a⇗q→p⇖)⟩), q1)})"
and Ax: "𝒜 x = ({x0, x1}, x0, {(x0, (?⟨(b⇗p→x⇖)⟩), x1)})"
and Ms: "ℳ = {(a⇗q→p⇖), (b⇗p→x⇖)}"
and Ps: "𝒫 = {p,q,x}"
  and G: "𝒢 = {(q,p), (p,x)}" 
and peers_diff: "q ≠ x ∧ x ≠ p ∧ q ≠ p"
and states_diff: "p0 ≠ p1 ∧ q0 ≠ q1 ∧ x0 ≠ x1"
shows "∀peer ∈ 𝒫. ℒ⇧*(peer) ⊆ ℒ⇧*⇩⊔⇩⊔(peer)" by (simp add: language_shuffle_subset)

lemma CE1_not_synchronisable: 
 assumes Ap: "𝒜 p = ({p0, p1}, p0, {(p0, (?⟨(a⇗q→p⇖)⟩), p1), (p0, (!⟨(b⇗p→x⇖)⟩), p1)})"
and Aq: "𝒜 q = ({q0, q1}, q0, {(q0, (!⟨(a⇗q→p⇖)⟩), q1)})"
and Ax: "𝒜 x = ({x0, x1}, x0, {(x0, (?⟨(b⇗p→x⇖)⟩), x1)})"
and Ms: "ℳ = {(a⇗q→p⇖), (b⇗p→x⇖)}"
and Ps: "𝒫 = {p,q,x}"
  and G: "𝒢 = {(q,p), (p,x)}" 
and peers_diff: "q ≠ x ∧ x ≠ p ∧ q ≠ p"
and states_diff: "p0 ≠ p1 ∧ q0 ≠ q1 ∧ x0 ≠ x1"
shows "ℒ⇩𝟬 ≠ 𝒯⇘None⇙⇂⇩!" using assms
proof -
  have sync: "[(!⟨(a⇗q→p⇖)⟩), (!⟨(b⇗p→x⇖)⟩)] ∉ ℒ⇩𝟬" using assms CE1_not_sync by simp
  have mbox: "[(!⟨(a⇗q→p⇖)⟩), (!⟨(b⇗p→x⇖)⟩)] ∈ 𝒯⇘None⇙" using assms CE1_trace by simp
  then have "[(!⟨(a⇗q→p⇖)⟩), (!⟨(b⇗p→x⇖)⟩)] ∈ 𝒯⇘None⇙⇂⇩!" by force
  then show ?thesis using sync by blast
qed

lemma CE1_not_synchronisable2: 
 assumes Ap: "𝒜 p = ({p0, p1}, p0, {(p0, (?⟨(a⇗q→p⇖)⟩), p1), (p0, (!⟨(b⇗p→x⇖)⟩), p1)})"
and Aq: "𝒜 q = ({q0, q1}, q0, {(q0, (!⟨(a⇗q→p⇖)⟩), q1)})"
and Ax: "𝒜 x = ({x0, x1}, x0, {(x0, (?⟨(b⇗p→x⇖)⟩), x1)})"
and Ms: "ℳ = {(a⇗q→p⇖), (b⇗p→x⇖)}"
and Ps: "𝒫 = {p,q,x}"
  and G: "𝒢 = {(q,p), (p,x)}" 
and peers_diff: "q ≠ x ∧ x ≠ p ∧ q ≠ p"
and states_diff: "p0 ≠ p1 ∧ q0 ≠ q1 ∧ x0 ≠ x1"
shows "¬ is_synchronisable" using assms using CE1_not_synchronisable by fastforce


lemma CE1_theorem_original_rightside:
 assumes Ap: "𝒜 p = ({p0, p1}, p0, {(p0, (?⟨(a⇗q→p⇖)⟩), p1), (p0, (!⟨(b⇗p→x⇖)⟩), p1)})"
and Aq: "𝒜 q = ({q0, q1}, q0, {(q0, (!⟨(a⇗q→p⇖)⟩), q1)})"
and Ax: "𝒜 x = ({x0, x1}, x0, {(x0, (?⟨(b⇗p→x⇖)⟩), x1)})"
and Ms: "ℳ = {(a⇗q→p⇖), (b⇗p→x⇖)}"
and Ps: "𝒫 = {p,q,x}"
  and G: "𝒢 = {(q,p), (p,x)}" 
and peers_diff: "q ≠ x ∧ x ≠ p ∧ q ≠ p"
and states_diff: "p0 ≠ p1 ∧ q0 ≠ q1 ∧ x0 ≠ x1"
shows "(∀p ∈ 𝒫. ∀ q ∈ 𝒫. ((is_parent_of p q) ⟶ ((((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (ℒ⇧*(p))⇂⇩!⇩?) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))"
  sorry

lemma CE1_theorem_original_wrong:
 assumes Ap: "𝒜 p = ({p0, p1}, p0, {(p0, (?⟨(a⇗q→p⇖)⟩), p1), (p0, (!⟨(b⇗p→x⇖)⟩), p1)})"
and Aq: "𝒜 q = ({q0, q1}, q0, {(q0, (!⟨(a⇗q→p⇖)⟩), q1)})"
and Ax: "𝒜 x = ({x0, x1}, x0, {(x0, (?⟨(b⇗p→x⇖)⟩), x1)})"
and Ms: "ℳ = {(a⇗q→p⇖), (b⇗p→x⇖)}"
and Ps: "𝒫 = {p,q,x}"
  and G: "𝒢 = {(q,p), (p,x)}" 
and peers_diff: "q ≠ x ∧ x ≠ p ∧ q ≠ p"
and states_diff: "p0 ≠ p1 ∧ q0 ≠ q1 ∧ x0 ≠ x1"
shows "(is_synchronisable ⟷ (∀p ∈ 𝒫. ∀ q ∈ 𝒫. ((is_parent_of p q) ⟶ ((((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (ℒ⇧*(p))⇂⇩!⇩?) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))) ⟹ False"
proof -
  assume t0: "(is_synchronisable ⟷ (∀p ∈ 𝒫. ∀ q ∈ 𝒫. ((is_parent_of p q) ⟶ ((((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (ℒ⇧*(p))⇂⇩!⇩?) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) )))"
  have t1: "(∀p ∈ 𝒫. ∀ q ∈ 𝒫. ((is_parent_of p q) ⟶ ((((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (ℒ⇧*(p))⇂⇩!⇩?) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))" using assms CE1_theorem_original_rightside by auto
  have t2: "¬ is_synchronisable" using assms CE1_not_synchronisable2 by auto
  have " ¬(is_synchronisable ⟷ (∀p ∈ 𝒫. ∀ q ∈ 𝒫. ((is_parent_of p q) ⟶ ((((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (ℒ⇧*(p))⇂⇩!⇩?) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) )))"
    using t1 t2 by linarith
  then show "False" using t0 by blast
qed

lemma CE1_tree_topology:
  assumes Ap: "𝒜 p = ({p0, p1}, p0, {(p0, (?⟨(a⇗q→p⇖)⟩), p1), (p0, (!⟨(b⇗p→x⇖)⟩), p1)})"
and Aq: "𝒜 q = ({q0, q1}, q0, {(q0, (!⟨(a⇗q→p⇖)⟩), q1)})"
and Ax: "𝒜 x = ({x0, x1}, x0, {(x0, (?⟨(b⇗p→x⇖)⟩), x1)})"
and Ms: "ℳ = {(a⇗q→p⇖), (b⇗p→x⇖)}"
and Ps: "𝒫 = {p,q,x}"
  and G: "𝒢 = {(q,p), (p,x)}" 
shows "tree_topology"
  using eps_in_mbox_execs is_in_infl_lang_rev_tree mbox_exec_to_infl_peer_word by auto

lemma theorem_original_ver: 
  assumes "tree_topology" 
  shows "(is_synchronisable ⟷ (∀p ∈ 𝒫. ∀ q ∈ 𝒫. ((is_parent_of p q) ⟶ ((((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (ℒ⇧*(p))⇂⇩!⇩?) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) )))"
  using CE1_tree_topology CE1_theorem_original_wrong sorry



definition theorem_orig_rightside :: "bool"
  where "theorem_orig_rightside ⟷ (∀p ∈ 𝒫. ∀ q ∈ 𝒫. ((is_parent_of p q) ⟶ ((((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (ℒ⇧*(p))⇂⇩!⇩?) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))"


end

lemma theorem_original_ver: 
  assumes "NetworkOfCA.tree_topology ℳ" 
  shows "NetworkOfCA.is_synchronisable 𝒜 ℳ ⟷ NetworkOfCA.theorem_orig_rightside 𝒜 ℳ"
  sorry

theorem synchronisability_for_trees:
  assumes "NetworkOfCA.tree_topology ℳ"
  shows "(NetworkOfCA.is_synchronisable 𝒜 ℳ ⟷ NetworkOfCA.theorem_rightside 𝒜 ℳ)"
  using assms unfolding NetworkOfCA_def NetworkOfCA.MboxTraces_def NetworkOfCA.SyncTraces_def NetworkOfCA.theorem_rightside_def 
  sorry

end
