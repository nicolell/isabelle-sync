(*contains most recent attemps, comments, etc. that might still be helpful at some point*)

theory Extras
begin

section \<open>shuffles and shuffled languages\<close>

(*
― ‹another variant for the shuffled language (should be the same but using inductive_set)›
inductive_set  sh  ::"('information, 'peer) action word ⇒ ('information, 'peer) action language" for w ::"('information, 'peer) action word" where
sh_refl: "w ∈ sh w" |
sh_once: "⟦w = (xs @ a # b # ys); is_output a; is_input b⟧ ⟹ (xs @ b # a # ys) ∈ sh w" |
sh_trans: "⟦(xs @ a # b # ys) ∈ sh w; is_output a; is_input b⟧ ⟹ (xs @ b # a # ys) ∈ sh w"
*)

(*
lemma rightmost_shuffle_unique:
  assumes "rightmost_shuffle v v'" and "v' ≠ w"
  shows "¬ rightmost_shuffle v w"
proof (rule ccontr)
  assume "¬ (¬ rightmost_shuffle v w)" 
  then have "rightmost_shuffle v w" by blast
  then have "(∃ xs a b ys. is_output a ∧ is_input b ∧ v = (xs @ a # b # ys) ∧ (¬ shuffling_possible ys) ∧ w = (xs @ b # a # ys))" by blast
  then obtain xs a b ys where "is_output a" and "is_input b" and "v = (xs @ a # b # ys)" and  "(¬ shuffling_possible ys)" and "w = (xs @ b # a # ys)" by blast
  then have "v' ≠  (xs @ b # a # ys)" using assms(2) by blast
   
  from assms have "(∃ as x y bs. is_output x ∧ is_input y ∧ v = (as @ x # y # bs) ∧ (¬ shuffling_possible bs) ∧ v' = (as @ y # x # bs))" by blast
  then obtain as x y bs where "is_output x" and "is_input y" and "v = (as @ x # y # bs)" and  "(¬ shuffling_possible bs)" and "v' = (as @ y # x # bs)" by blast
  then have "bs = ys" 
  then show "False" 
qed
  *)  

(*lemma that takes word and shuffles ?a forward multiple steps (before w?)
lemma rightmost_shuffle_until:
  assumes "(w @ [?⟨(a⇗q→p⇖)⟩] @ xs) ∈ shuffled_lang L" and "xs = xs↓⇩!" 
    and "shuffling_possible (w @ [?⟨(a⇗q→p⇖)⟩] @ xs)"
  shows ""
*)


(*
lemma rightmost_shuffle_decomp: 
  assumes "rightmost_shuffle v v'" 
  shows "∃ w xs a. v' = (w @ a # xs) ∧ xs = xs↓⇩! ∧ is_input a"
  (*xs can either be empty (if there was only one shuffling possible)
, or there is at least one send and recv in xs, in which case v' isn't a rightmost shuffle*)
  using assms proof -
have  "rightmost_shuffle v v'" using assms by simp
  then have "(∃ xs a b ys. is_output a ∧ is_input b ∧ v = (xs @ a # b # ys) ∧ (¬ shuffling_possible ys) ∧ v' = (xs @ b # a # ys))" by blast
  then obtain xs a b ys where shuf_decomp: "is_output a ∧ is_input b ∧ v = (xs @ a # b # ys) ∧ (¬ shuffling_possible ys) ∧ v' = (xs @ b # a # ys)" by blast
  then show ?thesis using assms
  proof (cases "ys↓⇩! = ys")
    case True
    then show ?thesis by (metis filter.simps(2) shuf_decomp)
  next
    case False
    (*then there cannot be !x?y, since that would make a shuffle possible, so it must be ?y...?y!x..!x*)
    then show ?thesis 
    proof (cases "(∃ xxs a b yys. is_output a ∧ is_input b ∧ ys = (xxs @ a # b # yys))")
      case True
      then show ?thesis using shuf_decomp by blast
    next
      case False
      (*then ys = xxs @ b a # yys  and yys is only inputs *)
      then show ?thesis sorry
    qed
    qed
  qed 

lemma unshuffled_word_in_original_lang:
  assumes "w' ∈ shuffled_lang L" and "∀w. (w ∈ L) ⟶ ¬ rightmost_shuffle w w'"
  shows "w' ∈ L"
  using assms
(*then w' cannot be created through shuffling, but must be created from some word in L → refl rule of shuffle*)
  sorry

lemma shuffled_infl_lang_peers_inv:
  assumes "v ∈ ℒ⇧*⇩⊔⇩⊔(p)" and "is_parent_of p q"
  shows "v↓⇩p = v" and "∀a. (a ∈ set (v↓⇩?)) ⟶ (∃i. a = ?⟨(i⇗q→p⇖)⟩)"
  sorry
*)



section \<open>mbox related\<close>

(*
lemma only_sends_run_to_mbox_run:
  assumes "w ∈ ℒ p" and "w = w↓⇩!"
  shows "∃xc. mbox_run 𝒞⇩ℐ⇩𝔪 None w xc"
  using assms  
proof (induct "length w" arbitrary: w)
  case 0
  then show ?case using MREmpty by auto
next
  case (Suc x)
  then obtain v a where w_def: "w = v @ [a]" and v_len : "x = length v" and v_L : "v ∈ ℒ p"
    by (metis (no_types, lifting) Lang_app length_Suc_conv_rev)  
  then have "x = |v| ⟹ v ∈ ℒ p ⟹ v = v↓⇩! ⟹ Ex (mbox_run (λp. (𝒞⇩ℐ⇩𝟬 p, ε)) None v)" 
    by (simp add: Suc.hyps(1))
  then have "v ∈ ℒ p ⟹ v = v↓⇩! ⟹ Ex (mbox_run (λp. (𝒞⇩ℐ⇩𝟬 p, ε)) None v)" 
    using v_len by blast
  then have " v = v↓⇩! ⟹ Ex (mbox_run (λp. (𝒞⇩ℐ⇩𝟬 p, ε)) None v)" by (simp add: v_L)
  have "v @ [a] = (v @ [a])↓⇩!" using Suc.prems(2) w_def by blast
  then have "v = v↓⇩!" 
      proof -
    have f1: "∀as p. ε = filter p as ∨ (∃a. p (a::('information, 'peer) action) ∧ a ∈ set as)"
      by (metis (lifting) filter_False)
    have "∀a. a ∉ set w ∨ is_output a"
      by (metis Suc.prems(2) filter_id_conv)
    then have "ε = w↓⇩?"
      using f1 by blast
    then have "ε = v↓⇩?"
      by (simp add: w_def)
    then show ?thesis
      by (simp add: empty_filter_conv)
    qed 
  then obtain xc where v_run: "(mbox_run (λp. (𝒞⇩ℐ⇩𝟬 p, ε)) None v xc)" 
    using ‹v = v↓⇩! ⟹ Ex (mbox_run (λp. (𝒞⇩ℐ⇩𝟬 p, ε)) None v)› by auto
  then have "is_output a" by (metis ‹v = v↓⇩!› ‹v ⋅ a # ε = (v ⋅ a # ε)↓⇩!› append_self_conv filter.simps(2) filter_append
        not_Cons_self2)
  then show ?case using Suc assms 
  proof (cases "v = []")
    case True
    then have "(mbox_run (λp. (𝒞⇩ℐ⇩𝟬 p, ε)) None v [])" by (simp add: MREmpty)
    then have "w = [a]" by (simp add: True w_def)
    then have "[a] ∈ ℒ p"  using Suc.prems(1) by auto
    then have "∃C. 𝒞⇩ℐ⇩𝔪 ─⟨a, ∞⟩→ C"  by (simp add: ‹is_output a› send_step_to_mbox_step)
    then obtain C where C_def: "𝒞⇩ℐ⇩𝔪 ─⟨a, ∞⟩→ C" by auto
    then have "mbox_step 𝒞⇩ℐ⇩𝔪 a None C" by simp
    then have "mbox_run (𝒞⇩ℐ⇩𝔪) None [a] [C]" by (simp add: mbox_step_to_run)
    then show ?thesis using ‹w = a # ε› by auto
  next
    case False
    then obtain xcs C0 s1  where v_run2: "(mbox_run (λp. (𝒞⇩ℐ⇩𝟬 p, ε)) None v xcs)" and xcs_nonemp : "xcs ≠ []"
and C0_def: "last xcs = C0"  and s1_def: "fst (C0 p) = s1" 
     by (smt (verit) Nil_is_append_conv mbox_run.simps not_Cons_self2 v_run)
    then have "is_mbox_config C0" using run_produces_mailbox_configurations by force
    have "v @ [a] ∈ ℒ p"  using Suc.prems(1) w_def by auto

--_> Need to show that a is of form !ipq and that the transition s1,a,s2 exists (then with my existing lemmas i can
      show that the mbox step from last config of xcs with a to s2 exists
and in turn that the mboxrun for w a exists

    obtain q i where a_def: "a = !⟨(i⇗p→q⇖)⟩" and p_def: "p = get_actor a" and q_def: "q = get_object a"
      sledgehammer
    then obtain s2 where "(s1, a, s2) ∈ ℛ p"
      srry

    then have "∃C1. C0 ─⟨a, ∞⟩→ C1" sledgehammer
    then have "∃C1. mbox_step C0 a None C1" sledgehammer

    then obtain s2 where a_trans: "(s1, a, s2) ∈ ℛ p" 
    sledgehammer 
  then obtain q i where a_def: "a = !⟨(i⇗p→q⇖)⟩" 
    let ?C0 = "(last xc)"
    let ?p_buf = "snd (?C0 p)"
    let ?C1 = "(?C0)(p := (s2, ?p_buf))"
    let ?q0 = "fst (?C0 q)"
    let ?q_buf = "snd (?C0 q)"
    let ?C2 = "(?C1)(q := (?q0, ?q_buf ⋅ [(i⇗p→q⇖)]))"
    have p_buf_def: "?p_buf = snd (?C0 p)" by simp
    have C1_def : "?C1 = (?C0)(p := (s2, ?p_buf))" by simp
    have q0_def : "?q0 = fst (?C0 q)" by simp
    have q_buf_def : "?q_buf = snd (?C0 q)" by simp
    have C2_def: "?C2 = (?C1)(q := (?q0, ?q_buf ⋅ [(i⇗p→q⇖)]))" by simp
    have "q ≠ p" using assms(1) valid_send_to_p_not_q by blast
    then show ?thesis srry
  qed
 
  
    by (metis CommunicatingAutomaton_def action.exhaust assms(2) automaton_of_peer
        get_actor.simps(1) get_sender.simps is_output.simps(2) message.exhaust) 
  then have "get_actor a = p" sledgehammer
  then obtain i q where a_def: "a = !⟨(i⇗p→q⇖)⟩" sledgehammer 
  then show ?case sledgehammer
qed
*)

(*
fixes C1 C2 :: "'peer ⇒ ('state × ('information, 'peer) message word)"
    and i     :: "'information"
    and p q   :: "'peer"
    and k     :: "bound"
lemma root_word_to_mbox_run: 
  assumes "w ∈ ℒ(p)" and "tree_topology" and "{}⟨→p⟩ = {}"
  shows "∃xc. mbox_run 𝒞⇩ℐ⇩𝔪 None w xc"
  sledgehammer


lemma sends_have_mbox_run :
  assumes "w ∈ ℒ⇧*(p)" and "{}⟨→p⟩ = {}" and "tree_topology"
  shows "w ∈ 𝒯⇘None⇙"
  srry
*)

(*
lemma root_lang_in_mbox_traces: 
  assumes "𝒫⇩?(q) = {}" and "(∀p. q ∉ 𝒫⇩!(p))" and "tree_topology"
  shows "ℒ(q) ⊆ 𝒯⇘None⇙"
proof auto
  fix w
  assume "w ∈ ℒ(q)"
  then show "w ∈ 𝒯⇘None⇙"
  proof (induct "length w" arbitrary: w)
    case 0
    then show ?case using MboxTraces.simps initial_configuration_is_mailbox_configuration runc_empty
        runc_to_mbox_run by fastforce
  next
    case (Suc x)
    then obtain v a where w_def: "w = v @ [a]" and v_len: "length v = x" by (metis length_Suc_conv_rev)
    then have "v ∈ ℒ(q)" using Lang_app Suc.prems by blast
    then have "v ∈ 𝒯⇘None⇙" by (simp add: Suc.hyps(1) v_len)
    have "w = w↓⇩!" using Suc.prems assms(1) no_inputs_implies_only_sends by auto
    then have "is_output a" by (metis append1_eq_conv append_is_Nil_conv decompose_send is_output.simps(1) list.distinct(1)
          w_def)
    have "w = w↓⇩q" by (simp add: w_in_peer_lang_impl_p_actor ‹w ∈ ℒ(q)›)
    then have "get_actor a = q" by (metis (mono_tags, lifting) ‹v ∈ ℒ q› append_self_conv filter.simps(2) filter_append
          filter_head_helper w_def w_in_peer_lang_impl_p_actor)
    then obtain i p where a_def: "a = !⟨(i⇗q→p⇖)⟩"  by (metis ‹is_output a› get_actor.simps(1) get_sender.simps is_output.simps(2)
          local_config_step.elims message.exhaust)
    then show ?case using Suc assms
    proof (cases "v = ε")
      case True
      then show ?thesis  by (metis MboxTraces.intros Suc.prems ‹is_output a› mbox_step_to_run self_append_conv2
            send_step_to_mbox_step w_def)
    next
      case False
      then obtain xs where w_run: "run_of_peer q w xs" using Suc.prems lang_implies_run by auto
      then obtain ys y where v_run: "run_of_peer q v ys" and a_run: "(last ([(ℐ q)]@ys))  ─a→q y" sledgehammer
      then have "∃s1 s2. (ℐ q) ─v→⇧*q s1 ∧ s1 ─a→q s2" sledgehammer
      then obtain xc C  where vrun: "mbox_run 𝒞⇩ℐ⇩𝔪 None v (xc)" and Cl :"last xc = C" by (metis MboxTraces.cases ‹v ∈ 𝒯⇘None⇙›)
      then have "(fst (C q)) ∈ 𝒮 q" using False is_mbox_config_def mbox_run.cases mbox_run_prod_mbox_config by fastforce
        then obtain s2 where  C_prop: "(fst (C q), a, s2) ∈ (ℛ q)"
  sledgehammer

      then obtain xc C where vrun: "mbox_run 𝒞⇩ℐ⇩𝔪 None v (xc@[C])" by (smt (verit) MboxTraces.cases ‹v ∈ 𝒯⇘None⇙› mbox_run.cases)
      then obtain s1 s2 where a_trans: "(s1, a, s2) ∈ ℛ q" and "fst (C q) = s1" sledgehammer 
      then obtain C2 where a_step: "mbox_step C a None C2" sledgehammer
      then show ?thesis sledgehammer
    qed
  qed
    
qed
*)

(*this is the (∀p q. ((is_parent_of p q) ⟶ ((subset_condition p q) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) )) chunk of the <== direction of the theorem, outside for better clarity
lemma mbox_trace_with_matching_recvs_is_mbox_exec1:
  assumes "w ∈ 𝒯⇘None⇙⇂⇩!" and "tree_topology" and "(∀p q. ((𝒫⇩?(p) = {q}) ⟶ (((((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩?) ⊆ ((ℒ⇧*(p))⇂⇩!⇩?)) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))"
  shows "(add_matching_recvs w) ∈ 𝒯⇘None⇙"
  sorry *)

(*
lemma mbox_run_impl_run_for_each_peer: 
  assumes "mbox_run C None w xc" and "p ∈ 𝒫"
  shows "run_of_peer_from_state p (fst (C p)) w (mbox_run_to_run p C xc)"
  using assms
proof (induct rule: mbox_run.induct)
  case (MREmpty C k)
  then have "(mbox_run_to_run p C ε) = []" by simp
  then have "run_of_peer_from_state p (fst (C p)) ε ε" sledgehammer
  then show ?case sledgehammer
next
  case (MRComposedNat C0 k w xc a C)
  then show ?case sorry
next
  case (MRComposedInf C0 w xc a C)
  then show ?case sorry
qed
*)



section \<open>path to root\<close>
(*
lemma 
  assumes "path_to_root p ps" and "q ∈ 𝒫" and "path_from_to q p (qp@[p])"
  shows "∃qs. path_from_root q (qp@ps)"
  using assms
proof (induct p ps)
  case (PTRRoot p)
  then show ?case srry
next
  case (PTRNode p q as)
  then show ?case srry
qed
*)


(*
lemma 
  assumes "path_to_root p ps" and "is_parent_of q p"
  shows "(∀xs ys. ps ≠ (xs @ [q] @ ys))"
  using assms 
proof (induct arbitrary: q )
  case (PTRRoot p)
  then have "is_root p" by auto
  then have "q ≠ p" using PTRRoot.prems is_parent_of_rev(2) is_parent_of_rev2(2) by fastforce
  then show ?case  by (simp add: Cons_eq_append_conv)
next
  case (PTRNode p x as)
  then have p_not_in_as: "∀xs ys. as ≠ xs ⋅ (p # ε ⋅ ys)" by simp
  have "path_to_root p (p # as)"  using PTRNode.hyps(2,3) p2root_down_step by auto
  have "∀qq. (qq ≠ p) ⟶ ¬ is_parent_of q qq" by (metis (mono_tags, lifting) PTRNode.prems is_parent_of_rev(2) mem_Collect_eq singleton_conv)
  have "p ≠ q"  by (metis NetworkOfCA.path_to_root_unique NetworkOfCA_axioms PTRNode.hyps(2,3)
        ‹∀qq. qq ≠ p ⟶ ¬ is_parent_of q qq› ‹path_to_root p (p # as)› not_Cons_self2)
  have "x ≠ q" by (metis PTRNode.hyps(3,5) PTRNode.prems ‹path_to_root p (p # as)› distinct_length_2_or_more p2root_down_step
        path_to_root_unique)
  have "∃aas. as = x # aas"  using PTRNode.hyps(3) path_to_root_rev by auto
  have "∀xs ys. as ≠ xs ⋅ (q # ε ⋅ ys)" 
  proof (rule ccontr)
    assume "¬ (∀xs ys. as ≠ xs ⋅ (q # ε ⋅ ys))" 
    then obtain xs ys where "as = xs ⋅ (q # ε ⋅ ys)" by auto
    then have "∃ qq. is_parent_of qq q" by (smt (verit) Cons_eq_append_conv NetworkOfCA.p2root_down_step NetworkOfCA.path_to_root_unique
          NetworkOfCA_axioms PTRNode.hyps(3) PTRNode.prems ‹∃aas. as = x # aas› ‹path_to_root p (p # as)› ‹x ≠ q›
          app_path_peer_is_parent_or_root list.distinct(1) list.inject
          path_to_root_of_root_exists)
    then obtain qq where "is_parent_of qq q" by blast
(**)
    then show "False" srry
  qed

  then show ?case srry
qed
*)


section \<open>influenced language archive\<close>

(*
fun infl_lang_rec :: "'peer list ⇒ ('information, 'peer) action language" where
"infl_lang_rec [] = {}" |
"infl_lang_rec [r::'peer] = {ε::('information, 'peer) action word}" |
"infl_lang_rec (p # q # ps) = {w | w::('information, 'peer) action word. w ∈ ℒ(p) ∧ (w↓⇩?)↓⇩!⇩? ∈ ((infl_lang_rec ((q::'peer) # ps))⇂⇩! )⇂⇩!⇩? ∧ 𝒫⇩?(p) = {q}}" 

fun infl_lang :: "'peer list ⇒ ('information, 'peer) action language" where
"infl_lang [] = {}" |
"infl_lang [r] = ℒ(r)" |
"infl_lang ps = infl_lang_rec ps" 

abbreviation InfluencedLanguage :: "'peer ⇒ ('information, 'peer) action language"  ("ℒ⇧* _" [90] 100) where
"ℒ⇧* p ≡ infl_lang (get_path_to_root p)"

abbreviation InfluencedLanguageSend :: "'peer ⇒ ('information, 'peer) action language"  ("ℒ⇩!⇧* _" [90] 100) where
"ℒ⇩!⇧* p ≡ (ℒ⇧* p)⇂⇩! "

abbreviation InfluencedLanguageRecv :: "'peer ⇒ ('information, 'peer) action language"  ("ℒ⇩?⇧* _" [90] 100) where
"ℒ⇩?⇧* p ≡ (ℒ⇧* p)⇂⇩! "

abbreviation ShuffledInfluencedLanguage :: "'peer ⇒ ('information, 'peer) action language" ("ℒ⇧*⇩⊔⇩⊔ _" [90] 100) where
"ℒ⇧*⇩⊔⇩⊔ p ≡ shuffled_lang (ℒ⇧* p)"
*)

(*NEED TO FIX: add projection to p and q to the sends of w', otherwise this is only correct if each node sends 
to exactly one child
→ this also impacts all subsequent lemmas, etc.
side note: proj. only needed in w', since each p has a unique parent, and thus the receives 
in w can already only be between p and q (i.e. one could addd the projection there as well but it's not necessary)
*)
inductive is_in_infl_lang :: "'peer ⇒ ('information, 'peer) action word ⇒ bool" where
IL_root: "⟦is_root r; w ∈ ℒ(r)⟧ ⟹ is_in_infl_lang r w" | ―‹influenced language of root r is language of r›
IL_node: "⟦tree_topology; is_parent_of p q; w ∈ ℒ(p); is_in_infl_lang q w'; ((w↓⇩?)↓⇩!⇩?) = (((w'↓⇩{⇩p⇩,⇩q⇩})↓⇩!)↓⇩!⇩?)⟧ ⟹ is_in_infl_lang p w" ―‹p is any node and q its parent has a matching send for each of p's receives›
(*
IL_root: "⟦is_root r; w ∈ ℒ(r)⟧ ⟹ is_in_infl_lang r w" | ―‹influenced language of root r is language of r›
IL_node: "⟦tree_topology; is_parent_of p q; w ∈ ℒ(p); is_in_infl_lang q w'; ((w↓⇩?)↓⇩!⇩?) = ((w'↓⇩!)↓⇩!⇩?)⟧ ⟹ is_in_infl_lang p w" ―‹p is any node and q its parent has a matching send for each of p's receives›

IL_node: "⟦tree_topology; 𝒫⇩?(p) = {q}; w ∈ ℒ(p); is_in_infl_lang q w'; ((w↓⇩?)↓⇩!⇩?) = ((w'↓⇩!)↓⇩!⇩?)⟧ ⟹ is_in_infl_lang p w" ―‹p is any node and q its parent has a matching send for each of p's receives›*)

(*
lemma is_in_infl_lang_rev: 
  assumes "is_in_infl_lang p w" and "is_parent_of p q" and "tree_topology"
  shows "w ∈ ℒ(p)" and "∃w'. is_in_infl_lang q w' ∧ ((w↓⇩?)↓⇩!⇩?) = ((w'↓⇩!)↓⇩!⇩?)"
  using assms
proof -
  show "w ∈ ℒ(p)" using assms(1) is_in_infl_lang.simps by blast
  show "∃w'. is_in_infl_lang q w' ∧ ((w↓⇩?)↓⇩!⇩?) = ((w'↓⇩!)↓⇩!⇩?)"
qed
*)
(*
lemma is_in_infl_lang_rev2: 
  assumes "w ∈ ℒ⇧* p" and "𝒫⇩?(p) = {q}" and "tree_topology"
  shows "w ∈ ℒ(p)" and "∃w'. w'∈ ℒ⇧* q ∧ ((w↓⇩?)↓⇩!⇩?) = ((w'↓⇩!)↓⇩!⇩?)"
  using assms
proof -
  show "w ∈ ℒ(p)" using assms(1) is_in_infl_lang.simps by blast
  show "∃w'. w' ∈ ℒ⇧* q ∧ w↓⇩?↓⇩!⇩? = w'↓⇩!↓⇩!⇩?" using assms(1,2) is_in_infl_lang.simps[of p w] mem_Collect_eq[of _ "is_in_infl_lang q"]
      mem_Collect_eq[of w "is_in_infl_lang p"] sends_of_peer_subset_of_predecessors_in_topology[of p]
      singleton_insert_inj_eq[of q _ "{}"] singleton_insert_inj_eq[of q q "{}"] subset_antisym[of "{q}" "{}"]
    by auto
qed
*)

(*
lemma "infl_parent_child_unique":
  assumes "w ∈ ℒ⇧*(p)" and "is_parent_of p q" 
  shows "𝒫⇩?(p) = {q}" 
  by (metis (no_types, lifting) UNIV_def assms(2) eps_in_infl insert_not_empty is_in_infl_lang.simps
      is_parent_of.simps local_to_global_root mem_Collect_eq sends_of_peer_subset_of_predecessors_in_topology
      subset_singleton_iff)
*)


section \<open>concat_infl stuff\<close>

(*
(*go from node pn and its word wn towards the root *)
inductive infl_path_2_mbox_w :: "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ bool" for w⇩n :: "('information, 'peer) action word" where
i2mROOT: "⟦path_to_root p [p];  w⇩1 ∈ ℒ⇧*(p)⟧ ⟹ infl_path_2_mbox_w w⇩n w⇩1 (w⇩a⇩c⇩c)" |
i2mNODE: "⟦infl_path_2_mbox_w w⇩n w⇩i w⇩a⇩c⇩c; path_to_root p (p # q # ps); 𝒫⇩?(p) = {q}; w⇩1 ∈ ℒ⇧*(p); w' ∈ ℒ⇧*(q); ((w↓⇩?)↓⇩!⇩?) = ((w'↓⇩!)↓⇩!⇩?)⟧ ⟹ infl_path_2_mbox_w w (w' ⋅ w)" 
*)

(* construct w' where w' is the concatenation w1...wn where wi is in influenced language of peer i 
(numbered by closeness to root, root is 1) 
→ this construction is in mbox 
lemma infl_word_2_mbox :
  assumes "w ∈ ℒ⇧*(q)" 
  shows "∃w'. (w' @ w) ∈ 𝒯⇘None⇙"
  sorry
*)

(*
lemma concat_infl_rev:
  assumes "concat_infl p w ps w_acc"
  shows "∃w1 ws q qs. w_acc = w1 @ ws ∧ w1 ∈ ℒ⇧*(q) ∧ ps = q # qs ∧ (((w_acc2↓⇩x)↓⇩?)↓⇩!⇩?) = ((w1↓⇩!)↓⇩!⇩?)"
*)

(*
inductive yes :: "'peer ⇒ ('information, 'peer) action word ⇒ 'peer list  ⇒ ('information, 'peer) action word ⇒ bool" for p::"'peer" and w:: "('information, 'peer) action word" where
at_p: "⟦tree_topology; w ∈ ℒ⇧*(p); path_to_root p ps⟧ ⟹ yes p w ps w" | (*start condition*)
reach_root: "⟦is_root x; rw ∈ ℒ⇧*(x); yes p w (q # [x]) w_acc; (((w_acc↓⇩{⇩x⇩,⇩q⇩})↓⇩?)↓⇩!⇩?) = ((rw↓⇩!)↓⇩!⇩?)⟧ ⟹ yes p w [x] (rw ⋅ w_acc)" | (*end condition*)
node_step: "⟦tree_topology; 𝒫⇩?(x) = {q}; qw ∈ ℒ⇧*(q); yes p w (x # [q] @ ps) w_acc; (((w_acc↓⇩{⇩x⇩,⇩q⇩})↓⇩?)↓⇩!⇩?) = ((qw↓⇩!)↓⇩!⇩?)⟧ ⟹ yes p w (q#ps) (qw ⋅ w_acc)" 

inductive yes :: "'peer list ⇒ ('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ bool" where
root_word: "⟦is_root p; w ∈ ℒ⇧*(p)⟧ ⟹ yes [p] w w" |
root_reached: "⟦is_root p; w ∈ ℒ⇧*(p); yes (q # [p]) w w_acc; (((w_acc↓⇩{⇩p⇩,⇩q⇩})↓⇩?)↓⇩!⇩?) = ((w↓⇩!)↓⇩!⇩?)⟧ ⟹ yes [p] w (w ⋅ w_acc)" |
node_step: "⟦tree_topology; 𝒫⇩?(p) = {q}; yes (p # [q] @ ps) w w_acc; (((w_acc↓⇩{⇩p⇩,⇩q⇩})↓⇩?)↓⇩!⇩?) = ((w↓⇩!)↓⇩!⇩?)⟧ ⟹ yes (q#ps) w w_acc" |


enn: "⟦is_root p; w ∈ ℒ⇧*(p); (((w_acc↓⇩{⇩p⇩,⇩q⇩})↓⇩?)↓⇩!⇩?) = ((w↓⇩!)↓⇩!⇩?); yes (q # [p]) w w_acc⟧ ⟹ yes [p] w (w ⋅ w_acc)" |
ynode: "⟦tree_topology; 𝒫⇩?(p) = {q}; (((w_acc↓⇩{⇩p⇩,⇩q⇩})↓⇩?)↓⇩!⇩?) = ((w↓⇩!)↓⇩!⇩?); yes (p # [q] @ ps) w w_acc⟧ ⟹ yes (q#ps) w w_acc" | 
ennn:"⟦tree_topology; 𝒫⇩?(p) = {q}; path_to_root p (p#q#ps); w ∈ ℒ⇧*(p); w' ∈ ℒ⇧*(q); ((w↓⇩?)↓⇩!⇩?) = ((w'↓⇩!)↓⇩!⇩?)⟧ 
        ⟹ yes q w ()"
*)



section \<open>misc wrong lemmas\<close>
(*i.e. lemmas that might seem true at first glance but aren't actually*)

(* the xs property isnt necessarily true, w ⋅ ?x ⋅ ?a ⋯ ?a ⋅ !b ⋯ !b can't be shuffled after ?x as well
lemma
  assumes "shuffling_possible v"
  shows "∃ w a xs. v = (w @ a # xs) ∧ is_input a ∧ (xs = xs↓⇩! ∨ xs = xs↓⇩?)"
  using assms 
proof auto
  have "∃ xs a b ys. is_output a ∧ is_input b ∧ v = (xs @ a # b # ys) ∧ ¬ (shuffling_possible ys)" using rightmost_shuffle_concrete[of v] using assms by blast
  then obtain xs a b ys where "is_output a" and "is_input b" and "v = (xs @ a # b # ys)" and  "(¬ shuffling_possible ys)" by blast
  then show ?thesis

lemma shuffled_word_implies_original_word:
  assumes "(w @ [?⟨(a⇗q→p⇖)⟩] @ xs) ∈ shuffled_lang L" and "xs = xs↓⇩!" 
and "shuffling_possible (w @ [?⟨(a⇗q→p⇖)⟩] @ xs)"
  shows "(w @ xs @ [?⟨(a⇗q→p⇖)⟩]) ∈ L"
*) 

(*
― ‹this is not true, as P? is defined only on each peer (q might send something to p but p may never receive it,
leading to an edge in the topology but to an empty P?(p)›
lemma paranents_in_tree_is_ReceivedFromPeers:
  fixes p :: "'peer"
  assumes "tree_topology"
  shows "𝒢⟨→p⟩ = 𝒫⇩?(p)"
― ‹proof (induct)›
  srry
*)

(* this implication does not hold necessarily in all trees.
To have an edge between nodes, a receive OR send message must exist in across the ENTIRE network.
A counter example to this lemma would be the PCP instance!
lemma edge_impl_psend_and_qrecv:
  assumes "𝒢⟨→p⟩ = {q}" and "tree_topology"
  shows "(𝒫⇩? p = {q} ∧ p ∈ 𝒫⇩!(q))"
*)

(* P? being empty does not yet mean r is root, it could be P? is empty but r in P! of some other node
lemma root_no_recvss :
  fixes w :: "('information, 'peer) action word"
  assumes "𝒫⇩?(r) = {}" and "w ∈ (ℒ(r))"
  shows "w = (w↓⇩!)"
proof (induction w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case
  proof (cases "is_output a")
    case True
    then have "is_output a" by simp
    then have "[a] = [a]↓⇩!"  by simp
    moreover have "[a] @ w = a # w " by simp
    moreover have "(a # w) = ([a]↓⇩!) @ (w↓⇩!)" 
      using calculation(1,2) local.Cons by presburger
    then show ?thesis
      by (metis calculation(1) filter_append local.Cons)
  next
    case False
    then have "is_input a" by simp
    then have "[] = [a]↓⇩!" by simp
    moreover have "w = ([a]↓⇩!) @ (w↓⇩!)"   using calculation local.Cons by auto
    moreover have "∃ p. p = get_object a" by simp
    moreover have "∃ q. q = get_actor a" by simp
    ultimately show ?thesis using assms Cons
    proof (cases "∃ s1 s2. (s1, a, s2) ∈ ℛ(r)" )
      case True
      then obtain s1 s2 where "(s1, a, s2) ∈ ℛ(r)" by auto
      then show ?thesis  using False assms(1) empty_receiving_from_peers4 by blast
    next
      case False
      then have "∀ s1 s2. (s1, a, s2) ∉ ℛ(r)" by simp
      then have "(a # w) ∉ (ℒ(r))"  using ‹is_input a› local.Cons  using no_input_trans_no_word_in_lang by blast
      moreover have "(a # w) ∈ (ℒ(r)) = False"  by (simp add: calculation)
      moreover have "(𝒫⇩?(r) = {}) ∧ (a # w) ∈ (ℒ(r)) = False" by (simp add: assms(1) calculation(1))
      moreover have "((𝒫⇩?(r) = {}) ∧ (a # w) ∈ (ℒ(r))) ⟹(a # w) = ((a # w)↓⇩!)"  by (simp add: calculation(1))
      moreover have "∀a. is_input a ⟶ (a # w) ∉ (ℒ(r))"  using assms(1) no_input_trans_no_word_in_lang no_input_trans_root by blast
      moreover have "𝒫⇩?(r) = {}" using assms by simp
      moreover have "ε = (a # ε)↓⇩!" using ‹ε = (a # ε)↓⇩!› by auto
      ultimately have "False" using assms Cons ‹(a # w) ∉ (ℒ(r))› sledgehammer
      ultimately show ?thesis using False Cons sledgehammer
      moreover have "(a # w) = ((a # w)↓⇩!)" sledgehammer 
      ultimately show ?thesis sledgehammer
    qed
  qed
qed
*)


(* P? being empty does not yet mean r is root, it could be P? is empty but r in P! of some other node
lemma root_no_recvs : 
  assumes "𝒫⇩?(r) = {}" and "w ∈ (ℒ(r))"
  shows "(w↓⇩?) = ε"
proof (rule ccontr)
  assume "(w↓⇩?) ≠ ε"
  then show "False"
  proof
    have "∃ x  xs. (x # xs) = (w↓⇩?)"  using ‹w↓⇩? ≠ ε› list.collapse by blast
    moreover obtain x xs where "(x#xs) = (w↓⇩?)" using calculation by blast
    moreover have "(filter is_input (w↓⇩?)) = (w↓⇩?)" using filter_recursion by blast
    moreover have "filter is_input (x#xs) = (x#xs)"   by (simp add: calculation(2))
    moreover have "x # (filter is_input xs) = filter is_input (x#xs)" 
      by (metis calculation(4) filter.simps(2) filter_id_conv list.set_intros(1))
    moreover have "is_input x" using calculation(5) by force
    moreover have "ℛ(r) ≠ {}" 
      by (metis NetworkOfCA.no_word_no_trans NetworkOfCA_axioms ‹w↓⇩? ≠ ε› assms(2) empty_iff filter.simps(1)
          neq_Nil_conv)
    moreover have "(x # xs) ∈ (ℒ⇩?(r))" 
      using assms(2) calculation(2) by blast

    ultimately show "(w↓⇩?) = ε" sledgehammer
  qed
qed


lemma root_only_sends : "⟦𝒫⇩?(r) = {}; w ∈ ℒ(r)⟧ ⟹ (w↓⇩!) = w" srry

―‹this is a rule I removed from test2, because the two existing rules should suffice,
this needs to be proven however, which is not yet fully accomplished
in particular, it needs to be shown that if P(r) = {} (i.e. r is root), then any words in w ∈ ℒ(r) are outputs/sends
because the root does not receive any messages.
Also useful would be that if w ∈ ℒ(p), then for each x in w, there must be a transition in ℛ(r)›
lemma test2_rule_q_direct_child_of_root : "⟦𝒫⇩?(q) = {r}; 𝒫⇩?(r) = {}; w ∈ ℒ(q); ((w↓⇩?)↓⇩!⇩?) ∈ ((ℒ(r))⇂⇩!⇩?) ⟧ ⟹ test2 q w"
proof
  assume "𝒫⇩?(q) = {r}" and "𝒫⇩?(r) = {}" and "w ∈ ℒ(q)" and  "((w↓⇩?)↓⇩!⇩?) ∈ ((ℒ(r))⇂⇩!⇩?)"
  then have "∃w'. w' ∈ ℒ(r)" using ‹((w↓⇩?)↓⇩!⇩?) ∈ ((ℒ(r))⇂⇩!⇩?)› by blast
  moreover obtain w' where "w' ∈ ℒ(r)" and "((w↓⇩?)↓⇩!⇩?) = w'↓⇩!⇩?" using ‹∃w'. w' ∈ ℒ r›  ‹((w↓⇩?)↓⇩!⇩?) ∈ (ℒ r)⇂⇩!⇩?› by blast
  moreover have "test2 r w'"  by (simp add: ‹𝒫⇩? r = {}› calculation(2) t00)
  ultimately show ?thesis 
  by (metis ‹𝒫⇩? q = {r}› ‹𝒫⇩? r = {}› ‹w ∈ ℒ q› root_only_sends test2.simps)
  moreover have "w↓⇩?↓⇩!⇩? = w'↓⇩!↓⇩!⇩?" using ‹𝒫⇩? r = {}› 
    by (simp add: ‹w' ∈ ℒ r› ‹w↓⇩?↓⇩!⇩? = w'↓⇩!⇩?› root_only_sends)
qed

lemma "⟦x = 2; y = x + 1; y > x; y < 5⟧ ⟹ y = 3" by auto



abbreviation infl_lang2 :: "'peer ⇒ ('information, 'peer) action language" where
"infl_lang2 p ≡ {w | w. test p w}"
*)


(* v' is also in the shuffled language *)
(*! this isn't necessarily true, needs more assumptions at the very least but even with more assumptions isn't true in general
assume q can only send a and p only has one branch with ?a!b, then v is of the required form and the lang. is even
sync but a v' does not exist where !b and ?a are swapped, as the shuffled lang. is the identity
lemma shortest_shuffled_words :
  assumes "v ∈ (ℒ⇧*⇩⊔⇩⊔(p))" and "v = w # ?⟨(a⇗q→p⇖)⟩ # xs" and "xs = xs↓⇩!"
  shows "∃v'. v ⊔⊔⇩? v' ∧ v' = w # xs @ [?⟨(a⇗q→p⇖)⟩]"
  srry
*)


(* not correct! since the execution is usually (unless w is root word) composed of different peer words
lemma mbox_2_peer_run:
  assumes "w ∈ 𝒯⇘None⇙"
  shows "∃p. w ∈ ℒ⇧*(p)"
  srry

only if p is root or only consists of sends (otherwise some q needs to provide the matching recvs for p)
by assumption those matching receives exist, but are only received in w and not sent
lemma infl_word_2_mbox:
  assumes "w ∈ ℒ⇧*(p)"
  shows "w ∈ 𝒯⇘None⇙"
  srry
*)

lemma sync_local_parent_to_global_parent:
  assumes "tree_topology" and "(𝒫⇩?(p) = {q})"
  shows "(p ∈ 𝒫⇩!(q))"
  sorry





section \<open>theorem misc lemmas/older versions & wips\<close>

(*this is the main chunk of the <== direction of the current theorem, outside for better clarity*)
lemma mbox_trace_with_matching_recvs_is_mbox_exec:
  assumes "w ∈ 𝒯⇘None⇙⇂⇩!" and "tree_topology" and "(∀p q. ((is_parent_of p q) ⟶ ((subset_condition p q) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))"
  shows "(add_matching_recvs w) ∈ 𝒯⇘None⇙"
  using assms
proof (induct "length w" arbitrary: w)
  case 0
  then show ?case by (simp add: eps_in_mbox_execs)
next
  case (Suc n)
  then obtain v a where w_def: "w = v ⋅ [a]" and v_len: "length v = n" by (metis length_Suc_conv_rev)
  then have "v ∈ 𝒯⇘None⇙⇂⇩!" using Suc.prems(1) prefix_mbox_trace_valid by blast
  then have v_IH_prems: "n = |v| ∧ v ∈ 𝒯⇘None⇙⇂⇩! ∧ is_tree (𝒫) (𝒢) ∧
    (∀p q. is_parent_of p q ⟶ subset_condition p q ∧ ℒ⇧* p = ℒ⇧*⇩⊔⇩⊔ p)"  using Suc.prems(3) assms(2) v_len by blast
  have v_IH: "add_matching_recvs v ∈ 𝒯⇘None⇙" using v_IH_prems Suc by blast
(*left to show is that a can be sent (and received) after v*)
  have "(v ⋅ [a]) = (v ⋅ [a])↓⇩!" using Suc.prems(1) w_def by fastforce
  then obtain i p q where a_def: "a = (!⟨(i⇗q→p⇖)⟩)" by (metis Nil_is_append_conv append1_eq_conv decompose_send neq_Nil_conv)
  then have "∃ s1 s2. (s1, !⟨(i⇗q→p⇖)⟩, s2) ∈ ℛ q" using mbox_word_to_peer_act[of v "!⟨(i⇗q→p⇖)⟩"]  using Suc.prems(1) assms(2) w_def by blast
  then have "p ∈ 𝒫⇩!(q)" by (metis CommunicatingAutomaton.SendingToPeers.intros automaton_of_peer get_message.simps(1)
        is_output.simps(1) message.inject output_message_to_act_both_known trans_to_edge)
  then have "𝒢⟨→p⟩ = {q}" by (simp add: assms(2) local_parent_to_global)  
  then have "is_parent_of p q" using assms by (simp add: node_parent)
(*unsure if wq is leading somewhere useful 
  obtain wq where "wq ∈ 𝒯⇘None⇙" and "wq↓⇩! = w"  using ‹w ∈ 𝒯⇘None⇙⇂⇩!› by blast
  then have "(wq)↓⇩q ∈ ℒ⇧* q" using mbox_exec_to_infl_peer_word by auto
  have "wq↓⇩! = v ⋅ [a]"  by (simp add: ‹wq↓⇩! = w› w_def)
  then have "(wq↓⇩!)↓⇩q = (v ⋅ [a])↓⇩q" by simp
  then have "((wq↓⇩!)↓⇩q) = (v↓⇩q) ⋅ [a]↓⇩q" by (metis filter_append)
  have "((wq↓⇩!)↓⇩q) = ((wq↓⇩q)↓⇩!)" using filter_pair_commutative by blast
  have "get_actor a = q ∧ get_object a = p"  by (simp add: a_def)
  then have "[a]↓⇩q = [a]" by simp
  then have wq_decomp: "((wq↓⇩q)↓⇩!) = (v↓⇩q) ⋅ [a]" using ‹wq↓⇩!↓⇩q = v↓⇩q ⋅ (a # ε)↓⇩q› ‹wq↓⇩!↓⇩q = wq↓⇩q↓⇩!› by presburger 
  then have "((wq↓⇩q)↓⇩!) ∈ (ℒ⇩!⇧*(q))" using ‹wq↓⇩q ∈ ℒ⇧* q› by blast
  have "[a]↓⇩{⇩p⇩,⇩q⇩} = [a]" by (simp add: ‹get_actor a = q ∧ get_object a = p›)
  then have "((v↓⇩q)↓⇩{⇩p⇩,⇩q⇩} ⋅ [a]) ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})" by (metis (mono_tags, lifting) ‹wq↓⇩q↓⇩! ∈ (ℒ⇧* q)⇂⇩!› filter_append mem_Collect_eq wq_decomp)
  then have "(((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩?)"
*)
  have "(add_matching_recvs v)↓⇩q ∈ ℒ⇧* q" using mbox_exec_to_infl_peer_word v_IH by auto
  have a_ok: "((add_matching_recvs v) ⋅ (add_matching_recvs [a])) ∈ 𝒯⇘None⇙" sorry
(*since the trace is valid, a can be sent after the sends in v. Obtain p and q of a, and then use subset condition
because if a can't be received then p can't receive a send of its parent (contradiction)*)
  then show ?case by (simp add: add_matching_recvs_app w_def)
qed
(*

  
    proof (cases "w↓⇩! = ε") ― ‹this edge case isn't in the paper but i need it here›
      case True
      assume "w ∈ 𝒯⇘None⇙"
      then have "w↓⇩! ∈ ℒ⇩𝟬" using SREmpty SyncTraces.intros ‹w↓⇩! = ε› by auto
      then show ?thesis by (simp add: ‹w↓⇩! ∈ ℒ⇩𝟬›)
    next
      case False (*the trace contains at least one send*)
      assume "w ∈ 𝒯⇘None⇙" "w↓⇩! ≠ ε"
      then have w_trace: "w↓⇩! ∈ ℒ⇩∞" by blast
      then obtain v a q p where w_def: "(w↓⇩!) = v ⋅ [!⟨(a⇗q→p⇖)⟩]" using ‹w↓⇩! ≠ ε› decompose_send by blast
      have "(v ⋅ [!⟨(a⇗q→p⇖)⟩]) ∈ ℒ⇩∞"  using ‹w↓⇩! ∈ 𝒯⇘None⇙⇂⇩!› w_def by argo
      then have v_mbox_trace: "v ∈ ℒ⇩∞"  using prefix_mbox_trace_valid by blast
      have "v = v↓⇩!" using ‹v ∈ 𝒯⇘None⇙⇂⇩!› by fastforce
      then have "add_matching_recvs (w↓⇩!) ∈ 𝒯⇘None⇙" using False w_def w_trace v_mbox_trace (*
do induction over length of the mbox trace to show that the matching receive trace is an mbox execution*)
      proof (induct "length (w↓⇩!)" arbitrary: w v a q p) ― ‹the paper uses base case 1 but idk how to do this here, case 0 is trivial though›
        case 0
        then show ?case by simp
      next
        case (Suc n)
        then have "length v = n" by simp
        then obtain w' where w'_def: "w' = add_matching_recvs (w↓⇩!)" by simp
        then obtain v' where "v' = add_matching_recvs v" by auto
        then have "add_matching_recvs [!⟨(a⇗q→p⇖)⟩] = [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]" by simp
        then have "add_matching_recvs (v ⋅ [!⟨(a⇗q→p⇖)⟩]) = (add_matching_recvs v) ⋅ add_matching_recvs [!⟨(a⇗q→p⇖)⟩]" by (simp add: add_matching_recvs_app)
        then have  w'_decomp : "w' = v' ⋅ [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]"  by (simp add: ‹v' = add_matching_recvs v› ‹w↓⇩! = v ⋅ !⟨(a⇗q→p⇖)⟩ # ε› w'_def)
            (*then v' is also mbox trace*)
        have "v'↓⇩! = v↓⇩!"  using ‹v' = add_matching_recvs v› adding_recvs_keeps_send_order by presburger
        then have "v'↓⇩! = v" using Suc.prems(1) by presburger
        then have "(v'↓⇩!) ∈ ℒ⇩∞" using Suc.prems(5) by blast
        have "length (v'↓⇩!) = n"   by (simp add: ‹v'↓⇩! = v› ‹|v| = n›)

(*use IH to have v' mbox execution*)

        then have "(w') ∈ 𝒯⇘None⇙" 
        proof (cases "v' = ε")
          case True
          then have "w' = [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]" by (simp add: w'_decomp)
          then show ?thesis sorry
        next
          case False
then have "v' ∈ 𝒯⇘None⇙" sledgehammer
          then show ?thesis sledgehammer
        qed

        
        have "v ∈ ℒ⇩∞" (*use IH to have v in mbox traces*)
        proof (cases "v = ε")
          case True
          then show ?thesis using MboxTraces.intros NetworkOfCA.MREmpty NetworkOfCA_axioms execution_implies_mbox_trace
            by fastforce
        next
          case False
          then obtain vv aa qq pp where "v↓⇩! = vv ⋅ (!⟨(aa⇗qq→pp⇖)⟩) # ε" by (metis (no_types, opaque_lifting) Suc.prems(1) append_self_conv2 decompose_send filter.simps(2)
                filter_append filter_recursion)
          then have "n = |v↓⇩!| ∧ v↓⇩! = vv ⋅ !⟨(aa⇗qq→pp⇖)⟩ # ε ∧ v↓⇩! ≠ ε" by (smt (verit) Nil_is_append_conv Suc.prems(1) ‹|v| = n› append_same_eq filter.simps(1,2) filter_append
                filter_recursion is_output.simps(1) not_Cons_self2)
          then have " v↓⇩! ∈ ℒ⇩𝟬" by (smt (verit, del_insts) Suc.hyps(1) Suc.prems(1) append_same_eq filter.simps(1,2) filter_append
                is_output.simps(1))
          then show ?thesis using Suc.prems(1) mbox_sync_lang_unbounded_inclusion by auto
        qed*)




(*
the following does the <= direction but by fixing an arbitrary execution instead of an arbitrary case,
which shouldn't change things really but introduces a tiny bit of unnecessary bloat
especially since there are many more executions than there are traces, so its also computationally inefficient
just for reference:
(* Direction 2: language conditions => is_synchronisable *)
  assume "?R"
  show "?L" ― ‹show that TMbox = TSync, i.e. ℒ = (i.e. the sends are equal›
  proof auto ― ‹cases: w in TMbox, w in TSync›
    fix w
    show "w ∈ 𝒯⇘None⇙ ⟹ w↓⇩! ∈ ℒ⇩𝟬" 
    proof (cases "w↓⇩! = ε") ― ‹this edge case isn't in the paper but i need it here›
      case True
      assume "w ∈ 𝒯⇘None⇙"
      then have "w ∈ 𝒯⇘None⇙"   using MREmpty MboxTraces.intros by blast
      then have "w↓⇩! ∈ ℒ⇩𝟬" using SREmpty SyncTraces.intros ‹w↓⇩! = ε› by auto
      then have "w ∈ 𝒯⇘None⇙ ⟹ w↓⇩! ∈ ℒ⇩𝟬"  by simp 
      then show ?thesis by (simp add: ‹w↓⇩! ∈ ℒ⇩𝟬›)
    next
      case False
      assume "w ∈ 𝒯⇘None⇙" "w↓⇩! ≠ ε"
      then have w_trace: "w↓⇩! ∈ ℒ⇩∞" by blast
      then obtain v a q p where w_def: "(w↓⇩!) = v ⋅ [!⟨(a⇗q→p⇖)⟩]" using ‹w↓⇩! ≠ ε› decompose_send by blast
      have "(v ⋅ [!⟨(a⇗q→p⇖)⟩]) ∈ ℒ⇩∞"  using ‹w↓⇩! ∈ 𝒯⇘None⇙⇂⇩!› w_def by argo
      then have v_mbox_trace: "v ∈ ℒ⇩∞"  using prefix_mbox_trace_valid by blast
      have "v = v↓⇩!"  using ‹v ∈ 𝒯⇘None⇙⇂⇩!› by fastforce
      then show ?thesis using False w_def w_trace v_mbox_trace
      proof (induct "length (w↓⇩!)" arbitrary: w v a q p) ― ‹the paper uses base case 1 but idk how to do this here, case 0 is trivial though›
        case 0
        then show ?case by simp
      next
        case (Suc n)
        then have "length v = n" by simp
        then obtain w' where w'_def: "w' = add_matching_recvs (w↓⇩!)" by simp
        then obtain v' where "v' = add_matching_recvs v" by auto
        then have "add_matching_recvs [!⟨(a⇗q→p⇖)⟩] = [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]" by simp
        then have "add_matching_recvs (v ⋅ [!⟨(a⇗q→p⇖)⟩]) = (add_matching_recvs v) ⋅ add_matching_recvs [!⟨(a⇗q→p⇖)⟩]" by (simp add: add_matching_recvs_app)
        then have  w'_decomp : "w' = v' ⋅ [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]"  by (simp add: ‹v' = add_matching_recvs v› ‹w↓⇩! = v ⋅ !⟨(a⇗q→p⇖)⟩ # ε› w'_def)
            (*then v' is also mbox trace*)
        have "v'↓⇩! = v↓⇩!"  using ‹v' = add_matching_recvs v› adding_recvs_keeps_send_order by presburger
        then have "v'↓⇩! = v" using Suc.prems(1) by argo
        then have "(v'↓⇩!) ∈ ℒ⇩∞" using Suc.prems(5) by blast
        have "length (v'↓⇩!) = n"  by (simp add: ‹v'↓⇩! = v› ‹|v| = n›)

        have "(v') ∈ 𝒯⇘None⇙" sledgehammer

        have "v ∈ ℒ⇩∞" (*use IH to have v in mbox traces*)
        proof (cases "v = ε")
          case True
          then show ?thesis using MboxTraces.intros NetworkOfCA.MREmpty NetworkOfCA_axioms execution_implies_mbox_trace
            by fastforce
        next
          case False
          then obtain vv aa qq pp where "v↓⇩! = vv ⋅ (!⟨(aa⇗qq→pp⇖)⟩) # ε" by (metis (no_types, opaque_lifting) Suc.prems(1) append_self_conv2 decompose_send filter.simps(2)
                filter_append filter_recursion)
          then have "n = |v↓⇩!| ∧ v↓⇩! = vv ⋅ !⟨(aa⇗qq→pp⇖)⟩ # ε ∧ v↓⇩! ≠ ε" by (smt (verit) Nil_is_append_conv Suc.prems(1) ‹|v| = n› append_same_eq filter.simps(1,2) filter_append
                filter_recursion is_output.simps(1) not_Cons_self2)
          then have " v↓⇩! ∈ ℒ⇩𝟬" by (smt (verit, del_insts) Suc.hyps(1) Suc.prems(1) append_same_eq filter.simps(1,2) filter_append
                is_output.simps(1))
          then show ?thesis using Suc.prems(1) mbox_sync_lang_unbounded_inclusion by auto
        qed

        
        then have "v' ∈ 𝒯⇘None⇙" sledgehammer

        
        
         
        then show ?case sorry
      qed
    qed
  next ― ‹w in TSync  --> show that w' (= w with recvs added) is in EMbox›
    fix w
    show "w ∈ ℒ⇩𝟬 ⟹ ∃w'. w = w'↓⇩! ∧ w' ∈ 𝒯⇘None⇙"
    proof -
      assume "w ∈ ℒ⇩𝟬"
      ― ‹For every output in w, Nsync was able to send the respective message and directly
      receive it›
      then have "w = w↓⇩!" by (metis SyncTraces.cases run_produces_no_inputs(1))
      then obtain xc where w_sync_run : "sync_run 𝒞⇩ℐ⇩𝟬 w xc" using SyncTraces.simps ‹w ∈ ℒ⇩𝟬› by auto
      then have "w ∈ ℒ⇩∞"  using ‹w ∈ ℒ⇩𝟬› mbox_sync_lang_unbounded_inclusion by blast
      obtain w' where "w' = add_matching_recvs w" by simp
      ― ‹then Nmbox can simulate the run of w in Nsync by sending every mes-
      sage first to the mailbox of the receiver and then receiving this message›
      then show ?thesis 
      proof (cases "xc = []") ― ‹this case distinction isn't in the paper but i need it here to properly get the simulated run›
        case True
        then have "mbox_run 𝒞⇩ℐ⇩𝔪 None (w') []"  using ‹w' = add_matching_recvs w› empty_sync_run_to_mbox_run w_sync_run by auto
        then show ?thesis using ‹w ∈ 𝒯⇘None⇙⇂⇩!› by blast
      next
        case False
      then obtain xcm where sim_run:  "mbox_run 𝒞⇩ℐ⇩𝔪 None w' xcm ∧ (∀p. (last xcm p ) = ((last xc) p, ε ))"
        using ‹w' = add_matching_recvs w› sync_run_to_mbox_run w_sync_run by blast
      then have "w' ∈ 𝒯⇘None⇙" using MboxTraces.intros by auto
      then have "w = w'↓⇩!" using ‹w = w↓⇩!› ‹w' = add_matching_recvs w› adding_recvs_keeps_send_order by auto
      then have "(w'↓⇩!) ∈ ℒ⇩∞" using ‹w' ∈ 𝒯⇘None⇙› by blast
      then show ?thesis using ‹w = w'↓⇩!› ‹w' ∈ 𝒯⇘None⇙› by blast
    qed      
    qed
  qed
*) 


(*if C0=C1 (because p is not the actor of the action which moves from C0 to C1) 
then this just puts the same state into the list multiple times for no reason*)
fun mbox_run_to_run :: "'peer ⇒ ('peer ⇒ ('state × ('information, 'peer) message word)) ⇒ ('peer ⇒ ('state × ('information, 'peer) message word)) list ⇒ 'state list" where
  "mbox_run_to_run p C0 [] = []" |
  "mbox_run_to_run p C0 (C1 # Cs) = (fst (C1 p)) # mbox_run_to_run p C0 (Cs)"























section ‹old version of the theorem with proof skeleton (obsolete)›

(* Nsync = L0, ENsync = T0, EMbox = Tinf/None, TMbox = Linf, E = !?, T = only sends *)
theorem synchronisability_for_trees_old:
  assumes "tree_topology" 
  shows "is_synchronisable ⟷ (∀p q. ((𝒫⇩?(p) = {q}) ⟶ (((((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩?) ⊆ ((ℒ⇧*(p))⇂⇩!⇩?)) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))" (is "?L ⟷ ?R")
proof
  (* Direction 1: is_synchronisable => language conditions *)
  assume "?L"
  show "?R"
  proof clarify
    fix p q
    assume p_parent: "𝒫⇩?(p) = {q}"
    then have "is_node_from_local p"  using assms by auto
    then have "𝒢⟨→p⟩ = {q}" by (metis global_local_eq_node insert_not_empty p_parent sends_of_peer_subset_of_predecessors_in_topology
          subset_singletonD)
    then have "is_parent_of p q" by (simp add: assms is_parent_of.simps)
    
    have sync_def: "𝒯⇘None⇙⇂⇩! = ℒ⇩𝟬"
      using ‹?L› by simp
    
    show "(((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩?) ⊆ ((ℒ⇧*(p))⇂⇩!⇩?) ∧ (ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p))"
    proof (rule conjI)
      (* Part 1: Prove the subset relation for traces *)
      show "((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (ℒ⇧*(p))⇂⇩!⇩?"
      proof (rule ccontr)
        assume subset_not_holds: "¬(((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (ℒ⇧*(p))⇂⇩!⇩?)"
        (* Extract a counterexample trace where p does not have matching inputs for its parent q*)
        then obtain v where v_def: "v ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})" and
                     not_in_p: "v↓⇩!⇩? ∉ (ℒ⇧*(p))⇂⇩!⇩?" by blast
        (* v is a sequence of sends of q*)
        have "v = v↓⇩!" using v_def send_infl_lang_pair_proj_inv_with_send by blast
        have "∃v'. v' ∈ ((ℒ⇧*(q))) ∧ ((v'↓⇩!)↓⇩{⇩p⇩,⇩q⇩}) = v" using v_def by blast
        then obtain full_v where full_v_def: "full_v ∈ ((ℒ⇧*(q)))" and full_v2v: "((full_v↓⇩!)↓⇩{⇩p⇩,⇩q⇩}) = v" by blast
        then have "tree_topology ∧ full_v ∈ ℒ⇧*(q) ∧ q ∈ 𝒫" by (simp add: assms)
        then have "∃ w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩q = full_v ∧ ((is_parent_of p q) ⟶  w'↓⇩p = ε))"  using lemma4_4 by blast
        then have e2: "∃ w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩q = full_v ∧ ((is_parent_of p q) ⟶  w'↓⇩p = ε) ∧ 
                  ((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = v)" using full_v2v by blast
        then have "∃ w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩q = full_v ∧ ((is_parent_of p q) ⟶  w'↓⇩p = ε) ∧ 
                  ((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = ((full_v↓⇩!)↓⇩{⇩p⇩,⇩q⇩}))" using full_v2v by blast
        then have "∃ w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩q = full_v ∧ ((is_parent_of p q) ⟶  w'↓⇩p = ε) ∧ 
                 (w'↓⇩q) = full_v)" using full_v2v by blast
        then obtain w' where "w' ∈ 𝒯⇘None⇙" and w'_fullv: "w'↓⇩q = full_v" and w'_2: "((is_parent_of p q) ⟶  w'↓⇩p = ε)" and 
                  w'_def: "((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = v" using e2 by blast
        then have "(w'↓⇩q) = full_v" by blast
        have "(((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩}) = (((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩})" using  proj_trio_inv[of q p w'] by blast
        have "(v↓⇩{⇩p⇩,⇩q⇩}) = v" using ‹w'↓⇩q↓⇩!↓⇩{⇩p⇩,⇩q⇩} = v› filter_recursion by blast
        have "(((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩}) = (((w'↓⇩{⇩p⇩,⇩q⇩})↓⇩!)↓⇩q)" using  proj_trio_inv2[of q p w'] by blast
        then have "(((w'↓⇩{⇩p⇩,⇩q⇩})↓⇩!)↓⇩q) = v" using ‹w'↓⇩q↓⇩!↓⇩{⇩p⇩,⇩q⇩} = v› ‹w'↓⇩q↓⇩!↓⇩{⇩p⇩,⇩q⇩} = w'↓⇩!↓⇩q↓⇩{⇩p⇩,⇩q⇩}› by presburger
        have "v = v↓⇩q" using ‹w'↓⇩!↓⇩q↓⇩{⇩p⇩,⇩q⇩} = w'↓⇩{⇩p⇩,⇩q⇩}↓⇩!↓⇩q› ‹w'↓⇩q↓⇩!↓⇩{⇩p⇩,⇩q⇩} = v›
            ‹w'↓⇩q↓⇩!↓⇩{⇩p⇩,⇩q⇩} = w'↓⇩!↓⇩q↓⇩{⇩p⇩,⇩q⇩}› by force
        have w'_p_proj: "w'↓⇩p = ε" using w'_2 by (simp add: ‹is_parent_of p q›)
        then have "∀ x. x ∈ (set (w')) ⟶ get_actor x ≠ p"  by (simp add: filter_empty_conv)
        then have p_no_sends_in_w': "∀ x. x ∈ (set (w'↓⇩!)) ⟶ get_actor x ≠ p" by auto

        (* Use Lemma 4.4 to find an execution v' in mailbox system 
        then obtain v' where v'_def: "v' ∈ 𝒯⇘∞⇙" and
                       v'_proj_q: "(v'↓⇩!)↓⇩q = v" and ― ‹is this possible?? proj on p&q is not necessarily the same as proj on q only, i.e. if q sends to more than one child›
                       v'_proj_p: "v'↓⇩p = ε"
          using lemma4_4 sorry*)
          
        (* Use synchronisability to show trace is also in synchronous system *)
        have "w'↓⇩! ∈ ℒ⇘∞⇙" using ‹w' ∈ 𝒯⇘None⇙› by blast
        also have "ℒ⇘∞⇙ = 𝒯⇩𝟬" using sync_def by simp
        also have "𝒯⇩𝟬 = ℒ⇩𝟬" by simp
        have w'_sync: "w'↓⇩! ∈ ℒ⇩𝟬" using calculation by auto
        
        have "((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})" using v_def w'_def by blast
        then have "((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})"  using ‹w'↓⇩q↓⇩!↓⇩{⇩p⇩,⇩q⇩} = w'↓⇩!↓⇩q↓⇩{⇩p⇩,⇩q⇩}› by argo
        then have "((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ⇩!(q))⇂⇩{⇩p⇩,⇩q⇩})" using w_in_infl_lang by auto
        then have "(w'↓⇩q)↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ(q))⇂⇩{⇩p⇩,⇩q⇩})"  using full_v_def w'_fullv w_in_infl_lang by auto
        have "((w'↓⇩q))↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})" using full_v_def w'_fullv by blast

        (* Since w'↓⇩p = ε and w'↓⇩! ∈ ℒ⇩𝟬, p must be able to receive outputs without sending anything*)
(*the main point is that v is subset of the sync sends w', but p has no sends in this word, which means that there are no sends needed to receive v in *)
        have "(((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∈ ((ℒ(p))⇂⇩?)⇂⇩!⇩?" using subword_of_sync_is_receivable[of w' p q]  using ‹is_parent_of p q› ‹w'↓⇩q↓⇩!↓⇩{⇩p⇩,⇩q⇩} ∈ (ℒ⇧* q)⇂⇩!⇂⇩{⇩p⇩,⇩q⇩}› calculation w'_p_proj by blast 
        then have "v↓⇩!⇩? ∈ ((ℒ(p))⇂⇩?)⇂⇩!⇩?" using w'_def by fastforce
        then have "v↓⇩!⇩? ∈ (ℒ⇩?(p))⇂⇩!⇩?" by blast
        have in_p: "v↓⇩!⇩? ∈ (ℒ⇧*(p))⇂⇩!⇩?" using subword_of_sync_is_receivable2[of w' p q] using ‹is_parent_of p q› ‹w'↓⇩q↓⇩!↓⇩{⇩p⇩,⇩q⇩} ∈ (ℒ⇧* q)⇂⇩!⇂⇩{⇩p⇩,⇩q⇩}› ‹w'↓⇩q↓⇩!↓⇩{⇩p⇩,⇩q⇩}↓⇩!⇩? ∈ (ℒ p)⇂⇩?⇂⇩!⇩?› w'_def w'_p_proj
            w'_sync by fastforce
        (* Contradiction with our assumption *)
        from in_p not_in_p show "False" by blast
      qed

      (* Part 2: Prove influenced language and shuffled language equivalence *)
      show "ℒ⇧*(p) = ℒ⇧*⇩⊔⇩⊔(p)" 
      proof
        (* First inclusion is by definition *)
        show "ℒ⇧*(p) ⊆ ℒ⇧*⇩⊔⇩⊔(p)" using language_shuffle_subset by auto
        (* Second inclusion via proof*)
        show "ℒ⇧*⇩⊔⇩⊔(p) ⊆ ℒ⇧*(p)" sorry
(*
        proof
          fix v
          assume "v ∈ ℒ⇧*⇩⊔⇩⊔(p)"
          (*probs need case distinction if v does not have the desired form as below*)
then show "v ∈ ℒ⇧*(p)" proof (cases "∃ v'. v' ∈ ℒ⇧*(p) ∧ rightmost_shuffle v' v")
  case True
(*v can be shuffled at least once*)
(*v has form as selected in the proof, do proof as normal*)
  then obtain v' where v'_shuffled: "rightmost_shuffle v' v" and v'_in_infl: "v' ∈ ℒ⇧*(p)" by blast 
  from v'_shuffled have "∃ w xs a. v = (w @ a # xs) ∧ xs = xs↓⇩! ∧ is_input a" using rightmost_shuffle_decomp[of v' v] 
    by fastforce
  then obtain w xs a where v_def: "v = (w @ a # xs)" and xs_prop: "xs = xs↓⇩!" and a_input: "is_input a" by blast
  have v_peers_inv: "∀aa. aa ∈ set ((w ⋅ a # xs)↓⇩?) ⟶ (∃i. aa = ?⟨(i⇗q→p⇖)⟩)"using shuffled_infl_lang_peers_inv[of " (w @ a # xs)" p q]
    ‹is_parent_of p q› ‹v ∈ ℒ⇧*⇩⊔⇩⊔ p› v_def by fastforce
  have "a ∈ set ((w ⋅ a # xs))" by auto
  then have "a ∈ set ((w ⋅ a # xs)↓⇩?)" using a_input by auto
  then obtain i where "a = ?⟨(i⇗q→p⇖)⟩"   using v_peers_inv by blast
  then have "(w @ [?⟨(i⇗q→p⇖)⟩] @ xs) ⊔⊔⇩? (w @ xs @ [?⟨(i⇗q→p⇖)⟩])"  by (meson fully_shuffled_w_prepend xs_prop)
  then have "(w @ xs @ [?⟨(i⇗q→p⇖)⟩]) ∈ ℒ⇧*(p)" sledgehammer

  then show ?thesis sledgehammer
next
  case False
(*there is no word that can be shuffled at all*)
(*v does not have this form, this means either v has no input → has only outputs → thesis trivially true
or the last input is followed by something other than only sends (i.e. xs cannot be found) 
  → then there is at least one action in xs. xs can't only have recvs, because otherwise we could choose empty xs and have the xs prop satisfied
  → then there is at least one send and one recv in xs, so we have *)
  then show "v ∈ ℒ⇧*(p)"  using ‹v ∈ ℒ⇧*⇩⊔⇩⊔ p› unshuffled_word_in_original_lang by blast
qed

          (* Find shortest words v and v' where v' is in language but v is shuffled *)
          then have "∃v'. v' ∈ ℒ⇧*(p) ∧ v ⊔⊔⇩? v'" using shuffled_infl_lang_impl_valid_shuffle by auto ― ‹in the paper it's v' _ v›
          (* Focus on specific form of these words *)
          obtain a w xs where  v_form: "v = (w @ [?⟨(a⇗q→p⇖)⟩] @ xs)" and  xs_form: "xs = xs↓⇩!" sorry
          then have "v = (w @ [?⟨(a⇗q→p⇖)⟩] @ xs) ∧ v ∈ ℒ⇧*⇩⊔⇩⊔(p) ∧ xs = xs↓⇩!" using ‹v ∈ ℒ⇧*⇩⊔⇩⊔ p› by auto
          then have "(w @ [?⟨(a⇗q→p⇖)⟩] @ xs) ⊔⊔⇩? (w @ xs @ [?⟨(a⇗q→p⇖)⟩])"  by (metis fully_shuffled mem_Collect_eq shuffled.refl)
          have "(w @ xs @ [?⟨(a⇗q→p⇖)⟩]) ∈ ℒ⇧*(p)" sorry
          then obtain v'  where  v'_def: "v' ∈ ℒ⇧*(p)" and
                                    "v ⊔⊔⇩? v'" and
                                v'_form: "v' = w @ xs @ [?⟨(a⇗q→p⇖)⟩]" 
                                 ― ‹xs are outputs to p's children, maybe thats also necessary here›
            using ‹w ⋅ (?⟨(a⇗q→p⇖)⟩ # ε ⋅ xs) ⊔⊔⇩? (w ⋅ (xs ⋅ ?⟨(a⇗q→p⇖)⟩ # ε))› v_form by blast

          have "tree_topology ∧ v' ∈ ℒ⇧*(p) ∧ p ∈ 𝒫" using assms v'_def by auto
          then have "∃ w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩p = v')" using lemma4_4 by blast
          (* Apply Lemma 4.4 to find execution in mailbox system *)
          then obtain w' where w'_def: "w' ∈ 𝒯⇘∞⇙" and
                        w'_proj: "w'↓⇩p = w @ xs @ [?⟨(a⇗q→p⇖)⟩]"
            using v'_def lemma4_4 v'_form by blast
            
          (* By construction of w' in lemma4.4, outputs from q to p happen before p's outputs *)
          (*probably better to use an abbreviation/ a separate property rather than doing this explicitly*)
          have "∃m mm mmm. w' = m @ [!⟨(a⇗q→p⇖)⟩] @ mm @ xs @ mmm" sorry
          then have "∃m mm mmm. w'↓⇩! = m @ [!⟨(a⇗q→p⇖)⟩] @ mm @ xs @ mmm"
            using w'_def  w'_proj sorry
            
          (* Use synchronisability to show trace is in synchronous system *)
          have "w'↓⇩! ∈ ℒ⇘∞⇙" using w'_def by auto
          also have "ℒ⇘∞⇙ = ℒ⇩𝟬" using sync_def by simp
          also have "ℒ⇩𝟬 = 𝒯⇩𝟬" by simp
          then have w'_sync: "w'↓⇩! ∈ 𝒯⇩𝟬" by (simp add: calculation)
          (* In synchronous system, p must receive input before sending outputs *)
          have "(w @ [?⟨(a⇗q→p⇖)⟩] @ xs) ∈ ℒ⇧*(p)" sorry
          then show "v ∈ ℒ⇧*(p)" using v_form by auto
        qed      
*)    
      qed
    qed
  qed
next
  (* Direction 2: language conditions => is_synchronisable *)
  assume "?R"
  show "?L" ― ‹show that TMbox = TSync, i.e. ℒ = (i.e. the sends are equal›
  proof auto ― ‹cases: w in TMbox, w in TSync›
    fix w
    show "w ∈ 𝒯⇘None⇙ ⟹ w↓⇩! ∈ ℒ⇩𝟬" 
    proof (cases "w↓⇩! = ε") ― ‹this edge case isn't in the paper but i need it here›
      case True
      assume "w ∈ 𝒯⇘None⇙"
      then have "w ∈ 𝒯⇘None⇙"   using MREmpty MboxTraces.intros by blast
      then have "w↓⇩! ∈ ℒ⇩𝟬" using SREmpty SyncTraces.intros ‹w↓⇩! = ε› by auto
      then have "w ∈ 𝒯⇘None⇙ ⟹ w↓⇩! ∈ ℒ⇩𝟬"  by simp 
      then show ?thesis by (simp add: ‹w↓⇩! ∈ ℒ⇩𝟬›)
    next
      case False
      assume "w ∈ 𝒯⇘None⇙" "w↓⇩! ≠ ε"
      then have "w↓⇩! ∈ ℒ⇩∞" by blast
      then obtain v a q p where w_def: "(w↓⇩!) = v ⋅ [!⟨(a⇗q→p⇖)⟩]" using ‹w↓⇩! ≠ ε› decompose_send by blast
      then have "v = v↓⇩!" by (smt (verit) append1_eq_conv filter.simps(1,2) filter_append filter_recursion is_output.simps(1))
      then show ?thesis using False w_def
      proof (induct "length (w↓⇩!)" arbitrary: w v a q p) ― ‹the paper uses base case 1 but idk how to do this here, case 0 is trivial though›
        case 0
        then show ?case by simp
      next
        case (Suc n)
        then have "length v = n" by simp
        then obtain w' where w'_def: "w' = add_matching_recvs (w↓⇩!)" by simp
        then obtain v' where "v' = add_matching_recvs v" by auto
        then have "add_matching_recvs [!⟨(a⇗q→p⇖)⟩] = [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]" by simp
        then have "add_matching_recvs (v ⋅ [!⟨(a⇗q→p⇖)⟩]) = (add_matching_recvs v) ⋅ add_matching_recvs [!⟨(a⇗q→p⇖)⟩]" by (simp add: add_matching_recvs_app)
        then have  w'_decomp : "w' = v' ⋅ [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]"  by (simp add: ‹v' = add_matching_recvs v› ‹w↓⇩! = v ⋅ !⟨(a⇗q→p⇖)⟩ # ε› w'_def)

        then have "v'↓⇩! ∈ ℒ⇩𝟬" sorry

        have "v ∈ ℒ⇩∞" (*use IH to have v in mbox traces*)
        proof (cases "v = ε")
          case True
          then show ?thesis using MboxTraces.intros NetworkOfCA.MREmpty NetworkOfCA_axioms execution_implies_mbox_trace
            by fastforce
        next
          case False
          then obtain vv aa qq pp where "v↓⇩! = vv ⋅ (!⟨(aa⇗qq→pp⇖)⟩) # ε" by (metis (no_types, opaque_lifting) Suc.prems(1) append_self_conv2 decompose_send filter.simps(2)
                filter_append filter_recursion)
          then have "n = |v↓⇩!| ∧ v↓⇩! = vv ⋅ !⟨(aa⇗qq→pp⇖)⟩ # ε ∧ v↓⇩! ≠ ε" by (smt (verit) Nil_is_append_conv Suc.prems(1) ‹|v| = n› append_same_eq filter.simps(1,2) filter_append
                filter_recursion is_output.simps(1) not_Cons_self2)
          then have " v↓⇩! ∈ ℒ⇩𝟬" by (smt (verit, del_insts) Suc.hyps(1) Suc.prems(1) append_same_eq filter.simps(1,2) filter_append
                is_output.simps(1))
          then show ?thesis using Suc.prems(1) mbox_sync_lang_unbounded_inclusion by auto
        qed

        
        then have "v' ∈ 𝒯⇘None⇙" sorry
  
        then show ?case sorry
      qed
    qed
  next ― ‹w in TSync  --> show that w' (= w with recvs added) is in EMbox›
    fix w
    show "w ∈ ℒ⇩𝟬 ⟹ ∃w'. w = w'↓⇩! ∧ w' ∈ 𝒯⇘None⇙"
    proof -
      assume "w ∈ ℒ⇩𝟬"
      ― ‹For every output in w, Nsync was able to send the respective message and directly
      receive it›
      then have "w = w↓⇩!" by (metis SyncTraces.cases run_produces_no_inputs(1))
      then obtain xc where w_sync_run : "sync_run 𝒞⇩ℐ⇩𝟬 w xc" using SyncTraces.simps ‹w ∈ ℒ⇩𝟬› by auto
      then have "w ∈ ℒ⇩∞"  using ‹w ∈ ℒ⇩𝟬› mbox_sync_lang_unbounded_inclusion by blast
      obtain w' where "w' = add_matching_recvs w" by simp
      ― ‹then Nmbox can simulate the run of w in Nsync by sending every mes-
      sage first to the mailbox of the receiver and then receiving this message›
      then show ?thesis 
      proof (cases "xc = []") ― ‹this case distinction isn't in the paper but i need it here to properly get the simulated run›
        case True
        then have "mbox_run 𝒞⇩ℐ⇩𝔪 None (w') []"  using ‹w' = add_matching_recvs w› empty_sync_run_to_mbox_run w_sync_run by auto
        then show ?thesis using ‹w ∈ 𝒯⇘None⇙⇂⇩!› by blast
      next
        case False
      then obtain xcm where sim_run:  "mbox_run 𝒞⇩ℐ⇩𝔪 None w' xcm ∧ (∀p. (last xcm p ) = ((last xc) p, ε ))"
        using ‹w' = add_matching_recvs w› sync_run_to_mbox_run w_sync_run by blast
      then have "w' ∈ 𝒯⇘None⇙" using MboxTraces.intros by auto
      then have "w = w'↓⇩!" using ‹w = w↓⇩!› ‹w' = add_matching_recvs w› adding_recvs_keeps_send_order by auto
      then have "(w'↓⇩!) ∈ ℒ⇩∞" using ‹w' ∈ 𝒯⇘None⇙› by blast
      then show ?thesis using ‹w = w'↓⇩!› ‹w' ∈ 𝒯⇘None⇙› by blast
    qed      
    qed
  qed
qed



(*theorem current version*)
(*TODO: fix all subproofs to reflect the new condition(s)*)
(* Nsync = L0, ENsync = T0, EMbox = Tinf/None, TMbox = Linf, E = !?, T = only sends *)
theorem synchronisability_for_trees:
  assumes "tree_topology" 
  shows "is_synchronisable ⟷ (∀p q. ((is_parent_of p q) ⟶ ((subset_condition p q) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))" (is "?L ⟷ ?R")
proof
  (* Direction 1: is_synchronisable => language conditions *)
  assume "?L"
  show "?R"
  proof clarify
    fix p q
    assume q_parent: "is_parent_of p q"
    have sync_def: "𝒯⇘None⇙⇂⇩! = ℒ⇩𝟬" using ‹?L› by simp
    show "subset_condition p q ∧ ℒ⇧* p = ℒ⇧*⇩⊔⇩⊔ p"
    proof (rule conjI)
      (* Part 1: Prove the subset relation for traces *)
      show "subset_condition p q"
      proof (rule ccontr)
        assume subset_not_holds: "¬(subset_condition p q)"
        then have "¬(∀ w. (w ∈ ℒ⇧*(p)) ⟶ ( (((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩?) ⊆ ((⟦w⟧⇩p)⇂⇩!⇩?) ))" by (simp add: subset_condition_def)
        then have "∃w. (w ∈ ℒ⇧*(p)) ∧ ¬(((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩?) ⊆ ((⟦w⟧⇩p)⇂⇩!⇩?)" by blast
        (*obtain prefix where condition is not satisfied*)
        then obtain pref where pref_in_L: "(pref ∈ ℒ⇧*(p))" and pref_contr: "¬(((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩?) ⊆ ((⟦pref⟧⇩p)⇂⇩!⇩?)" by blast
        then have "∃v. v ∈ (((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩?) ∧ v ∉ ((⟦pref⟧⇩p)⇂⇩!⇩?)" by blast
        (*v is sequence of outputs that are not received by and or after prefix pref, for any suffix*)
        then have "∃v. v ∈ (((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})) ∧ v↓⇩!⇩? ∉ ((⟦pref⟧⇩p)⇂⇩!⇩?)" by blast
        then obtain v where v_def: "v ∈ (((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩}))" and v_not_recv: "v↓⇩!⇩? ∉ ((⟦pref⟧⇩p)⇂⇩!⇩?)" by blast
        (* Extract a counterexample trace where p does not have matching inputs for its parent q*)
        (* v is a sequence of sends of q*)
        have "v = v↓⇩!" using v_def send_infl_lang_pair_proj_inv_with_send by blast
        have "∃v'. v' ∈ ((ℒ⇧*(q))) ∧ ((v'↓⇩!)↓⇩{⇩p⇩,⇩q⇩}) = v" using v_def by blast
        then obtain full_v where full_v_def: "full_v ∈ ((ℒ⇧*(q)))" and full_v2v: "((full_v↓⇩!)↓⇩{⇩p⇩,⇩q⇩}) = v" by blast
        then have "tree_topology ∧ full_v ∈ ℒ⇧*(q) ∧ q ∈ 𝒫" by (simp add: assms)
        then have "∃ w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩q = full_v ∧ ((is_parent_of p q) ⟶  w'↓⇩p = ε))"  using lemma4_4 by blast
        then have e2: "∃ w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩q = full_v ∧ ((is_parent_of p q) ⟶  w'↓⇩p = ε) ∧ 
                  ((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = v)" using full_v2v by blast
        then have "∃ w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩q = full_v ∧ ((is_parent_of p q) ⟶  w'↓⇩p = ε) ∧ 
                  ((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = ((full_v↓⇩!)↓⇩{⇩p⇩,⇩q⇩}))" using full_v2v by blast
        then have "∃ w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩q = full_v ∧ ((is_parent_of p q) ⟶  w'↓⇩p = ε) ∧ 
                 (w'↓⇩q) = full_v)" using full_v2v by blast
        then obtain w' where "w' ∈ 𝒯⇘None⇙" and w'_fullv: "w'↓⇩q = full_v" and w'_2: "((is_parent_of p q) ⟶  w'↓⇩p = ε)" and 
                  w'_def: "((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = v" using e2 by blast
        then have "(w'↓⇩q) = full_v" by blast
        have "(((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩}) = (((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩})" using  proj_trio_inv[of q p w'] by blast
        have "(v↓⇩{⇩p⇩,⇩q⇩}) = v" using ‹(((w')↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = v› filter_recursion by blast
        have "(((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩}) = (((w'↓⇩{⇩p⇩,⇩q⇩})↓⇩!)↓⇩q)" using  proj_trio_inv2[of q p w'] by blast
        then have "(((w'↓⇩{⇩p⇩,⇩q⇩})↓⇩!)↓⇩q) = v" using ‹(((w')↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = v› ‹((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = ((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩}› by presburger
        have "v = v↓⇩q" using ‹((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩} = ((w'↓⇩{⇩p⇩,⇩q⇩})↓⇩!)↓⇩q› ‹(((w')↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = v›
            ‹((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = ((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩}› by force
        have w'_p_proj: "w'↓⇩p = ε" using w'_2 by (simp add: ‹is_parent_of p q›)
        then have "∀ x. x ∈ (set (w')) ⟶ get_actor x ≠ p"  by (simp add: filter_empty_conv)
        then have p_no_sends_in_w': "∀ x. x ∈ (set (w'↓⇩!)) ⟶ get_actor x ≠ p" by auto
          
        (* Use synchronisability to show trace is also in synchronous system *)
        have "w'↓⇩! ∈ ℒ⇘∞⇙" using ‹w' ∈ 𝒯⇘None⇙› by blast
        also have "ℒ⇘∞⇙ = 𝒯⇩𝟬" using sync_def by simp
        also have "𝒯⇩𝟬 = ℒ⇩𝟬" by simp
        have w'_sync: "w'↓⇩! ∈ ℒ⇩𝟬" using calculation by auto
        
        have "((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})" using v_def w'_def by blast
        then have "((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})"  using ‹((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = ((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩}› by argo
        then have "((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ⇩!(q))⇂⇩{⇩p⇩,⇩q⇩})" using w_in_infl_lang by auto
        then have "(w'↓⇩q)↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ(q))⇂⇩{⇩p⇩,⇩q⇩})"  using full_v_def w'_fullv w_in_infl_lang by auto
        have "((w'↓⇩q))↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})" using full_v_def w'_fullv by blast

        (* Since w'↓⇩p = ε and w'↓⇩! ∈ ℒ⇩𝟬, p must be able to receive outputs without sending anything*)
(*the main point is that v is subset of the sync sends w', but p has no sends in this word, which means that there are no sends needed to receive v in *)
        have "(((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∈ ((ℒ(p))⇂⇩?)⇂⇩!⇩?" using subword_of_sync_is_receivable[of w' p q] 
          using ‹is_parent_of p q› assms sync_def v_def w'_def w'_p_proj w'_sync by fastforce
        then have "v↓⇩!⇩? ∈ ((ℒ(p))⇂⇩?)⇂⇩!⇩?" using w'_def by fastforce
        then have "v↓⇩!⇩? ∈ (ℒ⇩?(p))⇂⇩!⇩?" by blast
        have in_p: "v↓⇩!⇩? ∈ (ℒ⇧*(p))⇂⇩!⇩?" using subword_of_sync_is_receivable2[of w' p q] using ‹is_parent_of p q› ‹((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ⇧* q)⇂⇩!)⇂⇩{⇩p⇩,⇩q⇩}› ‹(((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∈ (ℒ p)⇂⇩?⇂⇩!⇩?› w'_def w'_p_proj
            w'_sync by fastforce
        (* Contradiction found*)
        show "False" sorry
      qed

      (* Part 2: Prove influenced language and shuffled language equivalence *)
      show "ℒ⇧*(p) = ℒ⇧*⇩⊔⇩⊔(p)" 
      proof
        (* First inclusion is by definition *)
        show "ℒ⇧*(p) ⊆ ℒ⇧*⇩⊔⇩⊔(p)" using language_shuffle_subset by auto
        (* Second inclusion via proof*)
        show "ℒ⇧*⇩⊔⇩⊔(p) ⊆ ℒ⇧*(p)" 
        proof
          fix v
          assume "v ∈ ℒ⇧*⇩⊔⇩⊔(p)"
          then obtain v' where v_orig: "v ⊔⊔⇩? v'" and orig_in_L: "v' ∈ ℒ⇧*(p)" using shuffled_infl_lang_impl_valid_shuffle by auto
          then show "v ∈ ℒ⇧*(p)" 
          proof (induct v' v)
            case (refl w)
            then show ?case by simp
          next
            case (swap x a w xs ys)
            (*exactly one swap occurred*)
            (*use lemma 4.4 to get execution in mbox*)
            then have "tree_topology ∧ w ∈ ℒ⇧*(p) ∧ p ∈ 𝒫" by (simp add: assms)
            then have "∃ w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩p = w ) ∧ (∃ xs. (xs @ w) = w')" using lemm4_4_extra by blast
            then obtain w' ws' where "w' ∈ 𝒯⇘None⇙" and "w'↓⇩p = w" and "(ws' @ w) = w'" by blast
            (*use that by construction, ws' contains !a *)

            have "is_input a ∧ is_parent_of p q" by (simp add: q_parent swap.hyps(2))
            have pw_def: "(xs ⋅ x # a # ys) ∈ ℒ⇧* p"  using swap.hyps(3) swap.prems by blast
            then have "(xs ⋅ x # a # ys) ∈ ℒ p" using w_in_infl_lang by auto
            then have "w ∈ ℒ(p) ∧ a ∈ set w" using swap.hyps(3) by auto
            then have  "∃s1 s2. (s1, a, s2) ∈ ℛ p" using act_in_word_has_trans by blast
            then have "get_actor a = p"  using ‹w ∈ ℒ p ∧ a ∈ set w› ‹w'↓⇩p = w› by force
            have "get_object a = q"  using ‹∃s1 s2. s1 ─a→p s2› ‹get_actor a = p› ‹is_input a ∧ is_parent_of p q› child_send_is_from_parent
              by blast
            have "∃i. a = ?⟨(i⇗q→p⇖)⟩" by (metis ‹get_actor a = p› ‹get_object a = q› action.exhaust get_actor.simps(2) get_object.simps(2)
                  get_receiver.simps get_sender.simps is_output.simps(1) message.exhaust swap.hyps(2))
            then obtain i where i_def: "get_message a = ((i⇗q→p⇖))" and a_def: "a = ?⟨(i⇗q→p⇖)⟩" by auto

            have "w'↓⇩! ∈ ℒ⇩𝟬" using ‹w' ∈ 𝒯⇘None⇙› sync_def by auto
            then have "(ws' @ w)↓⇩!  ∈ ℒ⇩𝟬" using ‹ws' ⋅ w = w'› sync_def by blast
            then have "ws'↓⇩! ∈ ℒ⇩𝟬" using sync_lang_sends_app by blast

            have "get_actor (!⟨(i⇗q→p⇖)⟩) = q" by simp
            have send_not_in_w: "(!⟨(i⇗q→p⇖)⟩) ∉ set w" by (metis (mono_tags, lifting) ‹∃w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩p = w) ∧ (∃xs. xs ⋅ w = w')›
                  ‹get_actor (!⟨(i⇗q→p⇖)⟩) = q› ‹is_input a ∧ is_parent_of p q› filter_id_conv filter_recursion
                  parent_child_diff)

            show ?case
            proof (cases "(!⟨(i⇗q→p⇖)⟩) ∈ set ws'")
              case True
              (*since sends of w' are sync word, the word where ?a cannot be blocked by any sends in w
              i.e. when i is sent by q, it must be immediately received in p*)
              then have "∀x. x ∈ (set (ws'↓⇩!)) ⟶ (∃ C1 C2. C1 ─⟨x, 𝟬⟩→ C2)"  using ‹ws'↓⇩! ∈ ℒ⇩𝟬› act_in_sync_word_to_sync_step by blast
              then have "(∃ C1 C2. C1 ─⟨(!⟨(i⇗q→p⇖)⟩), 𝟬⟩→ C2)" by (simp add: True)
              then obtain C1 C2 where sync_step_i: "C1 ─⟨(!⟨(i⇗q→p⇖)⟩), 𝟬⟩→ C2" by blast
              then have sync_i_rev: "is_sync_config C1 ∧ is_sync_config C2 ∧ p ≠ q ∧ C1 q ─(!⟨(i⇗q→p⇖)⟩)→q (C2 q) ∧ C1 p ─(?⟨(i⇗q→p⇖)⟩)→p (C2 p) ∧ (∀x. x ∉ {p, q} ⟶ C1(x) = C2(x))" 
                by (smt (verit, ccfv_SIG) insert_commute sync_send_step_to_recv_step sync_step_output_rev(3,4,6)
                    sync_step_rev(1,2))
              then have recv_step_in_q: "C1 p ─(?⟨(i⇗q→p⇖)⟩)→p (C2 p)" by blast
              (*a is sent before w, so also before the !x*)
              have send_in_ws': "(!⟨(i⇗q→p⇖)⟩) ∈ set ws' ∧ (!⟨(i⇗q→p⇖)⟩) ∉ set w" by (simp add: True send_not_in_w)
              have w'_decomp2: "w' = (ws' ⋅ xs) ⋅ (x # a # ys)"  using ‹ws' ⋅ w = w'› swap.hyps(3) by auto

              have "(xs ⋅ x # a # ys) ∈ ℒ⇧* p" using pw_def by blast  
              then have "((xs @ [x] @ [a]) @ ys) ∈ ℒ⇧* p"  by fastforce
              then have "xs ⋅ x # a # ε ∈ ℒ⇧* p" using infl_word_impl_prefix_valid  by (metis Cons_eq_append_conv)  
              (*then !x!a in sync traces*)
              have "(ws')↓⇩!  @ (w)↓⇩!  ∈ ℒ⇩𝟬"  using ‹(ws' ⋅ w)↓⇩! ∈ ℒ⇩𝟬› by auto
have "(xs ⋅ x # a # ε)↓⇩! = ((xs↓⇩!) @ [(x)]↓⇩! @ [a]↓⇩!)" by fastforce
  have "(xs ⋅ x # a # ε)↓⇩! = (xs↓⇩!) @ [x]" by (simp add: swap.hyps(1,2))
  then have w_trace: "(w)↓⇩! = (xs↓⇩!) @ [x] @ (ys↓⇩!)"  by (metis append.assoc append_Cons append_Nil filter_append swap.hyps(3))
  (*if ?a!x not in L(p), then !a!x in mbox but not in sync → contradiction*)
  have trace_equi: "(xs ⋅ a # x # ys)↓⇩! = (xs↓⇩!) @ [x] @ (ys↓⇩!)" by (metis append.left_neutral append_Cons filter.simps(2) filter_append swap.hyps(2,3) w_trace)

  have "∃ as bs. ws' = as @ [!⟨(i⇗q→p⇖)⟩] @ bs"  by (metis Cons_eq_appendI True append_self_conv2 in_set_conv_decomp_first)
  then obtain as bs where ws'_decomp: "ws' = as @ [!⟨(i⇗q→p⇖)⟩] @ bs" by blast
  then have "(as @ [!⟨(i⇗q→p⇖)⟩] @ bs)↓⇩!  @ (w)↓⇩!  ∈ ℒ⇩𝟬"  using ‹ws'↓⇩! ⋅ w↓⇩! ∈ ℒ⇩𝟬› by auto
  then have "(as↓⇩! @ [!⟨(i⇗q→p⇖)⟩] @ bs↓⇩!)  @ (w)↓⇩!  ∈ ℒ⇩𝟬" using Cons_eq_appendI filter.simps(2) by auto
  then have full_trace: "as↓⇩! @ [!⟨(i⇗q→p⇖)⟩] @ bs↓⇩! @ (xs↓⇩!) @ [x] @ (ys↓⇩!)  ∈ ℒ⇩𝟬"  by (simp add: w_trace)
  have full_exec: "as @ [!⟨(i⇗q→p⇖)⟩] @ bs @ xs @ [x] @ [?⟨(i⇗q→p⇖)⟩] @ ys = w'" using ‹ws' ⋅ w = w'› a_def swap.hyps(3) ws'_decomp by force
 have "(xs @ [x] @ [?⟨(i⇗q→p⇖)⟩] @ ys) ∈ ℒ⇧* p"
    using ‹xs ⋅ (x # ε ⋅ a # ε) ⋅ ys ∈ ℒ⇧* p› a_def by auto
 (**)
  have "as @ [!⟨(i⇗q→p⇖)⟩] @ bs @ xs @ [x] @ [?⟨(i⇗q→p⇖)⟩] @ ys ∈ 𝒯⇘None⇙" using ‹w' ∈ 𝒯⇘None⇙› full_exec by auto
  (*since the trace is in sync, we must be able to receive immediately after sending*)
  then have sync_exec: "as @ [!⟨(i⇗q→p⇖)⟩] @ [?⟨(i⇗q→p⇖)⟩] @ bs @ xs @ [x] @ ys ∈ 𝒯⇘None⇙"
    using sync_mbox_exec_impl[of as i q p "bs@xs@[x]" ys]  by (simp add: assms sync_def)
  have "(as @ [!⟨(i⇗q→p⇖)⟩] @ bs @ xs @ [x] @ [?⟨(i⇗q→p⇖)⟩] @ ys)↓⇩p = (xs @ [x] @ [?⟨(i⇗q→p⇖)⟩] @ ys)" 
    using ‹w'↓⇩p = w› a_def full_exec swap.hyps(3) by auto
  then have e0: "(as @ [!⟨(i⇗q→p⇖)⟩] @ [?⟨(i⇗q→p⇖)⟩] @ bs @ xs @ [x] @ ys)↓⇩p = (as↓⇩p @ [!⟨(i⇗q→p⇖)⟩]↓⇩p @ [?⟨(i⇗q→p⇖)⟩]↓⇩p @ bs↓⇩p @ xs↓⇩p @ [x]↓⇩p @ ys↓⇩p)" by simp
  have e1: "(as↓⇩p @ [!⟨(i⇗q→p⇖)⟩]↓⇩p @ [?⟨(i⇗q→p⇖)⟩]↓⇩p @ bs↓⇩p @ xs↓⇩p @ [x]↓⇩p @ ys↓⇩p) = ([?⟨(i⇗q→p⇖)⟩]↓⇩p  @ xs↓⇩p @ [x]↓⇩p @ ys↓⇩p)" 
    by (smt (verit) Nil_is_append_conv ‹w'↓⇩p = w› ‹ws' ⋅ w = w'› a_def filter_append filter_recursion
        self_append_conv2 ws'_decomp) 
  have "(xs @ [x] @ [?⟨(i⇗q→p⇖)⟩] @ ys)↓⇩p = (xs @ [x] @ [?⟨(i⇗q→p⇖)⟩] @ ys)"  by (metis
        ‹(as ⋅ (!⟨(i⇗q→p⇖)⟩ # ε ⋅ (bs ⋅ (xs ⋅ (x # ε ⋅ (?⟨(i⇗q→p⇖)⟩ # ε ⋅ ys))))))↓⇩p = xs ⋅ (x # ε ⋅ (?⟨(i⇗q→p⇖)⟩ # ε ⋅ ys))›
        filter_recursion)
  then have indiv_projs: "xs↓⇩p = xs ∧ [x]↓⇩p = [x] ∧ [?⟨(i⇗q→p⇖)⟩]↓⇩p = [?⟨(i⇗q→p⇖)⟩] ∧ ys↓⇩p = ys"  by (metis actors_4_proj_app_inv)
  then have "(xs @ [x] @ ys)↓⇩p = (xs @ [x] @ ys)"  by (metis filter_append)
  then have e2: "([?⟨(i⇗q→p⇖)⟩]↓⇩p @ xs↓⇩p @ [x]↓⇩p @ ys↓⇩p) = ([?⟨(i⇗q→p⇖)⟩] @ xs @ [x] @ ys)"  using indiv_projs by presburger
  then have "(as @ [!⟨(i⇗q→p⇖)⟩] @ [?⟨(i⇗q→p⇖)⟩] @ bs @ xs @ [x] @ ys)↓⇩p = ([?⟨(i⇗q→p⇖)⟩] @ xs @ [x] @ ys)"  using e0 e1 by order
  (*word where ?a is received first must be in p, otherwise no sync trace which would contradict assumption*)
  then have "([?⟨(i⇗q→p⇖)⟩] @ xs @ [x] @ ys) ∈ ℒ⇧* p" using sync_exec by (metis mbox_exec_to_infl_peer_word)
  (*so, we can have ?a either in the beginning of the word, or after x*)
  then have two_p_words: "([?⟨(i⇗q→p⇖)⟩] @ xs @ [x] @ ys) ∈ ℒ⇧* p ∧ (xs @ [x] @ [?⟨(i⇗q→p⇖)⟩] @ ys) ∈ ℒ⇧* p"  using ‹xs ⋅ (x # ε ⋅ (?⟨(i⇗q→p⇖)⟩ # ε ⋅ ys)) ∈ ℒ⇧* p› by linarith
  (*since we are using FIFO buffers, ?a is the first receive that occurs and so xs cannot contain other receives,
otherwise xs or bs would need to change from one of the two words to the other
e.g. if ?a?b!x, then !a!b..!x must be sent, but ?b!x?a is also a valid execution for this send
but then !a!b..?b?a, which cant be because FIFO
→ in other words, xs and bs cannot contain further receives from p (for bs this is trivial, for xs the contr. would occur)
→ so, xs can only be sends to children of p, and bs can be anything from q
*)
  then show ?thesis sorry

  (*
  have "∀z zz. z @ zz = xs ⟶ z @ [?⟨(i⇗q→p⇖)⟩] @ zz @ [x] @ ys ∈ ℒ⇧* p" sledgehammer
  have exec_facts: "(!⟨(i⇗q→p⇖)⟩) ∈ set ws' ∧ (!⟨(i⇗q→p⇖)⟩) ∉ set w ∧ (ws')↓⇩! @ (w)↓⇩!  ∈ ℒ⇩𝟬 ∧ 
as↓⇩! @ [!⟨(i⇗q→p⇖)⟩] @ bs↓⇩! @ (xs↓⇩!) @ [x] @ (ys↓⇩!) = (ws')↓⇩! @ (w)↓⇩! ∧ tree_topology ∧ is_synchronisable ∧ 
is_output x ∧ (xs ⋅ x # a # ys) ∈ ℒ⇧* p"
  
  have "(xs ⋅ a # x # ys) ∈ ℒ⇧* p"
  proof (induct "length xs" arbitrary: xs)
    case 0
    then show ?case sledgehammer
  next
    case (Suc xa)
    then show ?case sorry
  qed

  proof (rule ccontr)
    assume "(xs ⋅ a # x # ys) ∉ ℒ⇧* p"
(*but since a is sent before x, it must be received before x or the trace can't be in sync*)
(*and since we know that !x!a is in sync by assumption, a must be able to be received in p both before and after x*)
(*maybe contradiction isn't enough and need to use induction (maybe on xs? instead)*)
    then show "False" sledgehammer
(*show that a shuffled forward must also be in language by contradiction
*)*)

            next
              case False (*then a is received but never sent in w', contradicting that it is valid mbox word*)
              have "set w' = (set ws') ∪ (set w)" using ‹ws' ⋅ w = w'› by fastforce
              then have send_notin_w': "(!⟨(i⇗q→p⇖)⟩) ∉ set w'"  by (simp add: False send_not_in_w)
              have recv_in_w': "(?⟨(i⇗q→p⇖)⟩) ∈ set w'"   using ‹set w' = set ws' ∪ set w› ‹w ∈ ℒ p ∧ a ∈ set w› a_def by auto
              then show ?thesis using ‹w' ∈ 𝒯⇘None⇙› recv_in_mbox_requ_send send_notin_w' by auto
            qed

(* da ?iqp in w und w in mbox muss es gesendet werden sonst contr *)
(*oder mach vllt case distinction drüber ob iqp in ws' oder nicht 
(in w kanns ja eh net sein, weil sonst sendet p zu sich selbst und p=q
wenn in ws': dann muss es auch empfangen werden instant wegen sync, d.h. a muss vor b empfangen werden können
wenn nicht in ws' dann wird was empfangen was aber nicht gesendet wird → man kann diesen step net gehen in mbox → contr
*)


          next
            case (trans w w' w'')
            then show ?case by simp
          qed
        qed
        qed
      qed
    qed
  
next
  (* Direction 2: language conditions => is_synchronisable *)
  assume "?R"
  show "?L" ― ‹show that TMbox = TSync, i.e. ℒ = (i.e. the sends are equal›
  proof auto ― ‹cases: w in TMbox, w in TSync›
    fix w 
    show "w ∈ 𝒯⇘None⇙ ⟹ w↓⇩! ∈ ℒ⇩𝟬" 
    proof -(*take arbitrary mbox trace, show that w' where w' = add_matching_recvs w is (also) an mbox execution
since in w' each send immediately is received and it is a valid execution, it's also a sync execution
and thus we have found the matching sync trace to the arbitrary mbox trace.*)
      assume "w ∈ 𝒯⇘None⇙" 
      then have "(w↓⇩!) ∈ 𝒯⇘None⇙⇂⇩!" by blast
      (*the next line uses the conclusion of the large induction part of the paper proof (for clarity the induction is proven outside)*)
      then have match_exec: "add_matching_recvs (w↓⇩!) ∈ 𝒯⇘None⇙" using mbox_trace_with_matching_recvs_is_mbox_exec[of "(w↓⇩!)"] 
        using ‹∀p q. is_parent_of p q ⟶ subset_condition p q ∧ ℒ⇧* p = ℒ⇧*⇩⊔⇩⊔ p› assms by blast
      then obtain xcm where "mbox_run 𝒞⇩ℐ⇩𝔪 None (add_matching_recvs (w↓⇩!)) xcm"  by (metis MboxTraces.cases)
      then show "(w↓⇩!) ∈ ℒ⇩𝟬" using SyncTraces.simps ‹w↓⇩! ∈ 𝒯⇘None⇙⇂⇩!› matched_mbox_run_to_sync_run by blast
    qed
  next ― ‹w in TSync  --> show that w' (= w with recvs added) is in EMbox›
    fix w
    show "w ∈ ℒ⇩𝟬 ⟹ ∃w'. w = w'↓⇩! ∧ w' ∈ 𝒯⇘None⇙"
    proof -
      assume "w ∈ ℒ⇩𝟬"
      ― ‹For every output in w, Nsync was able to send the respective message and directly
      receive it›
      then have "w = w↓⇩!" by (metis SyncTraces.cases run_produces_no_inputs(1))
      then obtain xc where w_sync_run : "sync_run 𝒞⇩ℐ⇩𝟬 w xc" using SyncTraces.simps ‹w ∈ ℒ⇩𝟬› by auto
      then have "w ∈ ℒ⇩∞"  using ‹w ∈ ℒ⇩𝟬› mbox_sync_lang_unbounded_inclusion by blast
      obtain w' where "w' = add_matching_recvs w" by simp
      ― ‹then Nmbox can simulate the run of w in Nsync by sending every mes-
      sage first to the mailbox of the receiver and then receiving this message›
      then show ?thesis 
      proof (cases "xc = []") ― ‹this case distinction isn't in the paper but i need it here to properly get the simulated run›
        case True
        then have "mbox_run 𝒞⇩ℐ⇩𝔪 None (w') []"  using ‹w' = add_matching_recvs w› empty_sync_run_to_mbox_run w_sync_run by auto
        then show ?thesis using ‹w ∈ 𝒯⇘None⇙⇂⇩!› by blast
      next
        case False
      then obtain xcm where sim_run:  "mbox_run 𝒞⇩ℐ⇩𝔪 None w' xcm ∧ (∀p. (last xcm p ) = ((last xc) p, ε ))"
        using ‹w' = add_matching_recvs w› sync_run_to_mbox_run w_sync_run by blast
      then have "w' ∈ 𝒯⇘None⇙" using MboxTraces.intros by auto
      then have "w = w'↓⇩!" using ‹w = w↓⇩!› ‹w' = add_matching_recvs w› adding_recvs_keeps_send_order by auto
      then have "(w'↓⇩!) ∈ ℒ⇩∞" using ‹w' ∈ 𝒯⇘None⇙› by blast
      then show ?thesis using ‹w = w'↓⇩!› ‹w' ∈ 𝒯⇘None⇙› by blast
    qed      
    qed
  qed
qed

(*this is the main chunk of the <== direction of the current theorem, outside for better clarity*)
lemma mbox_trace_with_matching_recvs_is_mbox_exec:
  assumes "w ∈ 𝒯⇘None⇙⇂⇩!" and "tree_topology" and "(∀p q. ((is_parent_of p q) ⟶ ((subset_condition p q) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))"
  shows "(add_matching_recvs w) ∈ 𝒯⇘None⇙"
  using assms
proof (induct "length w" arbitrary: w)
  case 0
  then show ?case by (simp add: eps_in_mbox_execs)
next
  case (Suc n)
  then obtain v a where w_def: "w = v ⋅ [a]" and v_len: "length v = n" by (metis length_Suc_conv_rev)
  then have "v ∈ 𝒯⇘None⇙⇂⇩!" using Suc.prems(1) prefix_mbox_trace_valid by blast
  then have v_IH_prems: "n = |v| ∧ v ∈ 𝒯⇘None⇙⇂⇩! ∧ is_tree (𝒫) (𝒢) ∧
    (∀p q. is_parent_of p q ⟶ subset_condition p q ∧ ℒ⇧* p = ℒ⇧*⇩⊔⇩⊔ p)"  using Suc.prems(3) assms(2) v_len by blast
  have v_IH: "add_matching_recvs v ∈ 𝒯⇘None⇙" using v_IH_prems Suc by blast
      (*left to show is that a can be sent (and received) after v*)
  have "(v ⋅ [a]) = (v ⋅ [a])↓⇩!" using Suc.prems(1) w_def by fastforce
  then obtain i p q where a_def: "a = (!⟨(i⇗q→p⇖)⟩)" by (metis Nil_is_append_conv append1_eq_conv decompose_send neq_Nil_conv)
  then have "∃ s1 s2. (s1, !⟨(i⇗q→p⇖)⟩, s2) ∈ ℛ q" using mbox_word_to_peer_act[of v "!⟨(i⇗q→p⇖)⟩"]  using Suc.prems(1) assms(2) w_def by blast
  then have "p ∈ 𝒫⇩!(q)" by (metis CommunicatingAutomaton.SendingToPeers.intros automaton_of_peer get_message.simps(1)
        is_output.simps(1) message.inject output_message_to_act_both_known trans_to_edge)
  then have "𝒢⟨→p⟩ = {q}" by (simp add: assms(2) local_parent_to_global)  
  then have "is_parent_of p q" using assms by (simp add: node_parent)
      (*unsure if wq is leading somewhere useful 
  obtain wq where "wq ∈ 𝒯⇘None⇙" and "wq↓⇩! = w"  using ‹w ∈ 𝒯⇘None⇙⇂⇩!› by blast
  then have "(wq)↓⇩q ∈ ℒ⇧* q" using mbox_exec_to_infl_peer_word by auto
  have "wq↓⇩! = v ⋅ [a]"  by (simp add: ‹wq↓⇩! = w› w_def)
  then have "(wq↓⇩!)↓⇩q = (v ⋅ [a])↓⇩q" by simp
  then have "((wq↓⇩!)↓⇩q) = (v↓⇩q) ⋅ [a]↓⇩q" by (metis filter_append)
  have "((wq↓⇩!)↓⇩q) = ((wq↓⇩q)↓⇩!)" using filter_pair_commutative by blast
  have "get_actor a = q ∧ get_object a = p"  by (simp add: a_def)
  then have "[a]↓⇩q = [a]" by simp
  then have wq_decomp: "((wq↓⇩q)↓⇩!) = (v↓⇩q) ⋅ [a]" using ‹wq↓⇩!↓⇩q = v↓⇩q ⋅ (a # ε)↓⇩q› ‹wq↓⇩!↓⇩q = wq↓⇩q↓⇩!› by presburger 
  then have "((wq↓⇩q)↓⇩!) ∈ (ℒ⇩!⇧*(q))" using ‹wq↓⇩q ∈ ℒ⇧* q› by blast
  have "[a]↓⇩{⇩p⇩,⇩q⇩} = [a]" by (simp add: ‹get_actor a = q ∧ get_object a = p›)
  then have "((v↓⇩q)↓⇩{⇩p⇩,⇩q⇩} ⋅ [a]) ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})" by (metis (mono_tags, lifting) ‹wq↓⇩q↓⇩! ∈ (ℒ⇧* q)⇂⇩!› filter_append mem_Collect_eq wq_decomp)
  then have "(((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩?)"
*)
  have "(add_matching_recvs v)↓⇩q ∈ ℒ⇧* q" using mbox_exec_to_infl_peer_word v_IH by auto
  have a_ok: "((add_matching_recvs v) ⋅ (add_matching_recvs [a])) ∈ 𝒯⇘None⇙" sorry
      (*since the trace is valid, a can be sent after the sends in v. Obtain p and q of a, and then use subset condition
because if a can't be received then p can't receive a send of its parent (contradiction)*)
  then show ?case by (simp add: add_matching_recvs_app w_def)
qed
  (*
    proof (cases "w↓⇩! = ε") ― ‹this edge case isn't in the paper but i need it here›
      case True
      assume "w ∈ 𝒯⇘None⇙"
      then have "w↓⇩! ∈ ℒ⇩𝟬" using SREmpty SyncTraces.intros ‹w↓⇩! = ε› by auto
      then show ?thesis by (simp add: ‹w↓⇩! ∈ ℒ⇩𝟬›)
    next
      case False (*the trace contains at least one send*)
      assume "w ∈ 𝒯⇘None⇙" "w↓⇩! ≠ ε"
      then have w_trace: "w↓⇩! ∈ ℒ⇩∞" by blast
      then obtain v a q p where w_def: "(w↓⇩!) = v ⋅ [!⟨(a⇗q→p⇖)⟩]" using ‹w↓⇩! ≠ ε› decompose_send by blast
      have "(v ⋅ [!⟨(a⇗q→p⇖)⟩]) ∈ ℒ⇩∞"  using ‹w↓⇩! ∈ 𝒯⇘None⇙⇂⇩!› w_def by argo
      then have v_mbox_trace: "v ∈ ℒ⇩∞"  using prefix_mbox_trace_valid by blast
      have "v = v↓⇩!" using ‹v ∈ 𝒯⇘None⇙⇂⇩!› by fastforce
      then have "add_matching_recvs (w↓⇩!) ∈ 𝒯⇘None⇙" using False w_def w_trace v_mbox_trace (*
do induction over length of the mbox trace to show that the matching receive trace is an mbox execution*)
      proof (induct "length (w↓⇩!)" arbitrary: w v a q p) ― ‹the paper uses base case 1 but idk how to do this here, case 0 is trivial though›
        case 0
        then show ?case by simp
      next
        case (Suc n)
        then have "length v = n" by simp
        then obtain w' where w'_def: "w' = add_matching_recvs (w↓⇩!)" by simp
        then obtain v' where "v' = add_matching_recvs v" by auto
        then have "add_matching_recvs [!⟨(a⇗q→p⇖)⟩] = [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]" by simp
        then have "add_matching_recvs (v ⋅ [!⟨(a⇗q→p⇖)⟩]) = (add_matching_recvs v) ⋅ add_matching_recvs [!⟨(a⇗q→p⇖)⟩]" by (simp add: add_matching_recvs_app)
        then have  w'_decomp : "w' = v' ⋅ [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]"  by (simp add: ‹v' = add_matching_recvs v› ‹w↓⇩! = v ⋅ !⟨(a⇗q→p⇖)⟩ # ε› w'_def)
            (*then v' is also mbox trace*)
        have "v'↓⇩! = v↓⇩!"  using ‹v' = add_matching_recvs v› adding_recvs_keeps_send_order by presburger
        then have "v'↓⇩! = v" using Suc.prems(1) by presburger
        then have "(v'↓⇩!) ∈ ℒ⇩∞" using Suc.prems(5) by blast
        have "length (v'↓⇩!) = n"   by (simp add: ‹v'↓⇩! = v› ‹|v| = n›)

(*use IH to have v' mbox execution*)

        then have "(w') ∈ 𝒯⇘None⇙" 
        proof (cases "v' = ε")
          case True
          then have "w' = [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]" by (simp add: w'_decomp)
          then show ?thesis sorry
        next
          case False
then have "v' ∈ 𝒯⇘None⇙" sledgehammer
          then show ?thesis sledgehammer
        qed

        
        have "v ∈ ℒ⇩∞" (*use IH to have v in mbox traces*)
        proof (cases "v = ε")
          case True
          then show ?thesis using MboxTraces.intros NetworkOfCA.MREmpty NetworkOfCA_axioms execution_implies_mbox_trace
            by fastforce
        next
          case False
          then obtain vv aa qq pp where "v↓⇩! = vv ⋅ (!⟨(aa⇗qq→pp⇖)⟩) # ε" by (metis (no_types, opaque_lifting) Suc.prems(1) append_self_conv2 decompose_send filter.simps(2)
                filter_append filter_recursion)
          then have "n = |v↓⇩!| ∧ v↓⇩! = vv ⋅ !⟨(aa⇗qq→pp⇖)⟩ # ε ∧ v↓⇩! ≠ ε" by (smt (verit) Nil_is_append_conv Suc.prems(1) ‹|v| = n› append_same_eq filter.simps(1,2) filter_append
                filter_recursion is_output.simps(1) not_Cons_self2)
          then have " v↓⇩! ∈ ℒ⇩𝟬" by (smt (verit, del_insts) Suc.hyps(1) Suc.prems(1) append_same_eq filter.simps(1,2) filter_append
                is_output.simps(1))
          then show ?thesis using Suc.prems(1) mbox_sync_lang_unbounded_inclusion by auto
        qed*)



section ‹unnecessary lemmas (already covered by simp or definitions/ not used anywhere)

lemma word_implies_recv_word : 
  assumes "w ∈ (ℒ(r))"
  shows "(w↓⇩?) ∈ (ℒ⇩?(r))"
  using assms by blast

lemma word_implies_recv_word_rec : 
  assumes "w ∈ (ℒ⇩?(r))"
  shows "∃ xs. xs ∈ (ℒ(r)) ∧ (xs↓⇩?) = w" 
  using assms by blast

lemma word_implies_partitioned_word :
  assumes "w ∈ (ℒ(r))" and "w ≠ ε"
  shows "∃ xs ys a. (xs @ [a] @ ys) ∈ (ℒ(r)) ∧ (w = (xs @ [a] @ ys))"
  by (metis Cons_eq_appendI append_self_conv2 assms(1,2) rev_exhaust)

lemma word_implies_recv_word_rec2 : 
  assumes "(xs @ [a] @ ys) ∈ (ℒ⇩?(r))"
  shows "∃ w. w ∈ (ℒ(r)) ∧ (w↓⇩?) = (xs @ [a] @ ys)" 
  using assms by auto

  lemma full_word_of_send_proj_in_infl_lang:
  assumes "v ∈ (ℒ⇩!⇧*(q))"
  shows "∃v'. v' ∈ ((ℒ⇧*(q))) ∧ v'↓⇩! = v"
  using assms by blast

lemma
  assumes "v ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})" 
  shows "∃v'. v' ∈ ((ℒ⇧*(q))) ∧ ((v'↓⇩!)↓⇩{⇩p⇩,⇩q⇩}) = v"
  using assms by blast

  lemma simulate_sync_step_with_matching_recvs_helper:
  assumes "mbox_step c1 (!⟨(i⇗p→q⇖)⟩) None c2 ∧ mbox_step c2 (?⟨(i⇗p→q⇖)⟩) None c3"
  shows "c1 ─⟨(!⟨(i⇗p→q⇖)⟩), ∞⟩→ c2 ∧ c2 ─⟨?⟨(i⇗p→q⇖)⟩, ∞⟩→ c3"
  by (simp add: assms)

  lemma word_rec_partition : 
  assumes "w ∈ (ℒ(r)) ∧ (w↓⇩?) = (xs @ [a] @ ys)" 
  shows "(xs @ [a] @ ys) ∈ (ℒ⇩?(r))"
  using assms by force

inductive_set All_Senders :: "'peer set" where
  All : "⟦q ∈ Peers_of p; 𝒫⇩?(p) = {q}⟧ ⟹ q ∈ All_Senders" |
  All1 : "⟦p ∈ Peers_of q; p ∈ (𝒫⇩!(q))⟧ ⟹ q ∈ All_Senders"

lemma send_to_signs_proj_decomp:
  shows "(((u ⋅ v)↓⇩!)↓⇩!⇩?) = (((u)↓⇩!)↓⇩!⇩?) @ (((v)↓⇩!)↓⇩!⇩?)"
  by auto

lemma double_pair_proj_inv:
  assumes "w ∈ (ℒ(q))⇂⇩{⇩p⇩,⇩q⇩}" and "(ℒ(q))⇂⇩{⇩p⇩,⇩q⇩} = (ℒ(q))"
  shows "w↓⇩{⇩p⇩,⇩q⇩} = w" 
  sorry

lemma peer_word_in_sync_word_to_matching_recv_steps:
  assumes "(xs @ w @ ys) ∈ ℒ⇩𝟬" and "w ∈ ℒ⇩!(q)" and "is_parent_of p q"
  shows "w↓⇩!⇩? ∈ ((ℒ(p))⇂⇩?)⇂⇩!⇩?"
  sorry

lemma 
  assumes "v ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})"
  shows "∃v'. v' ∈ ((ℒ⇩!⇧*(q))) ∧ (v'↓⇩{⇩p⇩,⇩q⇩}) = v"
  using assms by blast

lemma valid_message_to_valid_act_rev :
  assumes "i⇗p→q⇖ ∈ ℳ ∧ (i⇗p→q⇖) = get_message a"
  shows "get_message a ∈ ℳ" 
  using assms by auto

lemma input_or_output_action : "∀x. is_input x ∨ is_output x"  by simp
lemma input_or_output_word : "∀w. (w ≠ ε) ⟹ (((w↓⇩?) ≠ ε) ∨ (ε ≠ (w↓⇩!)))" by blast
lemma filter_recursion : "filter f (filter f xs) = filter f xs"  by simp





(*
lemma el_in_word_set_to_trans:
  assumes "w ∈ ℒ(p)" and "x ∈ set w"
  shows "∃ s1 s2. (s1, x, s2) ∈ ℛ p"
  sorry
*)
subsubsection "different conversion/ experimental?"
(*convert peer runs to mbox and reverse?*)

(*go from node pn and its word wn towards the root *)
(* the base step for the root is probably not sufficient *)
inductive infl_2_mbox :: "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ bool" where
  i2mROOT: "⟦is_root p; w ∈ ℒ⇧*(p); (w_acc↓⇩p) = w⟧ ⟹ infl_2_mbox w w_acc" |
  i2mNODE: "⟦𝒫⇩?(p) = {q}; w ∈ ℒ⇧*(p); w' ∈ ℒ⇧*(q); ((w↓⇩?)↓⇩!⇩?) = (((w'↓⇩{⇩p⇩,⇩q⇩})↓⇩!)↓⇩!⇩?); infl_2_mbox w (w' ⋅ ws)⟧ ⟹ infl_2_mbox w (w ⋅ w' ⋅ ws)" 
  (* go from node towards root
at each step, the construction projected on only the current node and its parent must have matching sends/recvs
w in influenced language already implies this property
*)


value "tl ([1,2,3]::int list)"

fun get_C2 :: "('peer ⇒ ('state × ('information, 'peer) message word)) ⇒ (('information, 'peer) action) ⇒ 'state ⇒ ('peer ⇒ ('state × ('information, 'peer) message word))" where
  "get_C2 C1 (!⟨(i⇗p→q⇖)⟩) p2 = (C1(p := (p2, snd (C1 p))))(q := (fst (C1 q), (snd (C1 q))⋅[(i⇗p→q⇖)]))" |
  "get_C2 C1 (?⟨(i⇗q→p⇖)⟩) p2 = C1( p := (p2, tl (snd (C1 p))  ))"

lemma get_C2_valid :
  assumes "is_mbox_config C1" and "fst (C1 p) ─(!⟨(i⇗p→q⇖)⟩)→p s2"
  shows "mbox_step C1 (!⟨(i⇗p→q⇖)⟩) None (get_C2 C1 (!⟨(i⇗p→q⇖)⟩) s2)"
  using assms(1,2) send_trans_to_mbox_step by force

fun states_to_configs :: "('information, 'peer) action word ⇒ 'state ⇒ 'state list ⇒ ('peer ⇒ ('state × ('information, 'peer) message word)) ⇒ ('peer ⇒ ('state × ('information, 'peer) message word)) list" where
  "states_to_configs ε s0 xs C = []" |
  "states_to_configs (a # w) s0 (s1 # xs) C = C # (states_to_configs w s1 xs (get_C2 C a s1))" 

(*converts a config list of an mbox run to a set of states (for each changed state for p)*)
fun conf2s :: "'peer ⇒ ('peer ⇒ ('state × ('information, 'peer) message word)) list ⇒ 'state list" where
  "conf2s p [] = []" |
  "conf2s p [C] = (if (fst (C p)) = (ℐ p) then [] else [fst (C p)])" |
  "conf2s p (C0 # C1 # Cs) =  (if (fst (C0 p)) = (fst (C1 p)) then conf2s p (C1 # Cs) else (fst (C0 p)) # conf2s p (C1 # Cs))"

lemma conf2s_to_run:
  assumes "mbox_run C k w Cs"
  shows "run_of_peer_from_state p (fst (C p)) (w↓⇩p) (conf2s p Cs)"
  using assms
  sorry


inductive path_mbox_eq :: "'peer ⇒ ('information, 'peer) action word ⇒ 'state ⇒ 'state list ⇒ ('peer ⇒ ('state × ('information, 'peer) message word)) ⇒ ('peer ⇒ ('state × ('information, 'peer) message word)) list ⇒ bool" for p ::"'peer" where
  PM_eps: "path_mbox_eq p ε (ℐ p) [] (𝒞⇩ℐ⇩𝔪) []" |
  PM_send: "⟦a = (!⟨(i⇗p→q⇖)⟩); C2 = get_C2 C1 (!⟨(i⇗p→q⇖)⟩) s2 ⟧ ⟹ path_mbox_eq p [a] s0 [s2] C1 [C2]" |
  PM_recv: "⟦a = (?⟨(i⇗q→p⇖)⟩); C2 = get_C2 C1 (?⟨(i⇗q→p⇖)⟩) s2 ⟧ ⟹ path_mbox_eq p [a] s0 [s2] C1 [C2]" |
  PM_step_send: "⟦path_mbox_eq p w s0 xs C0 Cs; fst ((last (C0#Cs)) p) ─a→p s2; a = (!⟨(i⇗p→q⇖)⟩)⟧ ⟹ path_mbox_eq p w s0 xs C0 (Cs@[get_C2 C0 a s2])" |
  PM_step_recv: "⟦path_mbox_eq p w s0 xs C0 Cs; fst ((last (C0#Cs)) p) ─a→p s2; a = (!⟨(i⇗p→q⇖)⟩)⟧ ⟹ path_mbox_eq p w s0 xs C0 (Cs@[get_C2 C0 a s2])"

(*getC2 but applied to the complete run: get all configs starting from initial state until word read*)
fun get_Cs :: "('peer ⇒ ('state × ('information, 'peer) message word)) ⇒ ('state × ('information, 'peer) action × 'state) list ⇒ ('peer ⇒ ('state × ('information, 'peer) message word)) list" where
  "get_Cs C [] = [C]" |
  "get_Cs C ((s1,a,s2) # xs) = C # (get_Cs (get_C2 C a s2) xs)"

inductive cstep_valid :: "('peer ⇒ ('state × ('information, 'peer) message word)) ⇒ (('information, 'peer) action) ⇒ bool" where
  valid_send: "⟦∃p2. p2 ∈ 𝒮 p ∧ (fst (C1 p), (!⟨(i⇗p→q⇖)⟩), p2) ∈ ℛ p ∧ (get_C2 C1 (!⟨(i⇗p→q⇖)⟩) p2) = C2 ⟧ ⟹ cstep_valid C1 (!⟨(i⇗p→q⇖)⟩)"

(* takes a start config and a word, returns the list of traversed configs *)
fun w2cs ::  "('peer ⇒ ('state × ('information, 'peer) message word)) ⇒ (('information, 'peer) action word) ⇒ ('peer ⇒ ('state × ('information, 'peer) message word)) list option" where
  "w2cs C [] = (Some [])" |
  "w2cs C ((!⟨(i⇗p→q⇖)⟩) # w) = (Some [])" |
  "w2cs C ((?⟨(i⇗p→q⇖)⟩) # w) = (Some [])"

inductive stepc :: "('peer ⇒ ('state × ('information, 'peer) message word)) ⇒ ('information, 'peer) action  ⇒ ('peer ⇒ ('state × ('information, 'peer) message word)) ⇒ bool" where 
  stepcS: "⟦a = !⟨(i⇗p→q⇖)⟩; (fst (C1 p), a, p2) ∈ ℛ p;  C2 = ((C1)(p := (p2, (snd (C1 p)))))(q := ((fst (C1 q)), (snd (C1 q)) ⋅ [(i⇗p→q⇖)]))⟧ ⟹ stepc C1 a C2" |
  stepcR: "⟦a = ?⟨(i⇗q→p⇖)⟩; (fst (C1 p), a, p2) ∈ ℛ p; (snd (C1 p)) ≠ ε; hd (snd (C1 p)) = (i⇗q→p⇖); C2 = C1(p:= (p2, tl (snd (C1 p))))⟧ ⟹ stepc C1 a C2"

fun send_config :: "('peer ⇒ ('state × ('information, 'peer) message word)) ⇒ 'peer ⇒ 'peer ⇒ ('information, 'peer) message ⇒ ('peer ⇒ ('state × ('information, 'peer) message word))" where
  "send_config C1 p q m = C1"

fun recv_config :: "('peer ⇒ ('state × ('information, 'peer) message word)) ⇒ 'peer ⇒ ('information, 'peer) message ⇒ ('peer ⇒ ('state × ('information, 'peer) message word))" where
  "recv_config C1 p m = C1"

fun local_config_step :: "('peer ⇒ ('state × ('information, 'peer) message word)) ⇒  ('information, 'peer) action ⇒ ('peer ⇒ ('state × ('information, 'peer) message word))" where
  "local_config_step C1 (!⟨m⟩) = send_config C1 (get_sender m) (get_receiver m) m"  |
  "local_config_step C1 (?⟨m⟩) = recv_config C1 (get_receiver m)  m"

(*─!⟨(i⇗p→q⇖)⟩→p*)

lemma stepc_send_rev :
  assumes "stepc C1 a C2" and "a = !⟨(i⇗p→q⇖)⟩"
  shows "∃p2. (fst (C1 p), a, p2) ∈ ℛ p ∧ C2 = ((C1)(p := (p2, (snd (C1 p)))))(q := ((fst (C1 q)), (snd (C1 q)) ⋅ [(i⇗p→q⇖)]))"
  using assms(1,2) stepc.simps by auto

lemma stepc_recv_rev :
  assumes "stepc C1 a C2" and "a =  ?⟨(i⇗q→p⇖)⟩"
  shows "∃p2. (fst (C1 p), a, p2) ∈ ℛ p ∧ hd (snd (C1 p)) = (i⇗q→p⇖) ∧ C2 = C1(p:= (p2, tl (snd (C1 p))))"
  by (smt (verit) action.distinct(1) action.inject(2) assms(1,2) message.inject
      stepc.cases)

lemma stepc_to_mbox :
  assumes "stepc C1 a C2" and "is_mbox_config C1"
  shows "mbox_step C1 a None C2"
  using assms
proof (cases rule: stepc.cases)
  case (stepcS i p q p2)
  then show ?thesis
    using assms(2) get_C2_valid by force
next
  case (stepcR i q p p2)
  then have t1: "fst (C1 p) ─(?⟨(i⇗q→p⇖)⟩)→p (fst (C2 p))" by simp
  have "∀xs. xs ≠ ε ⟶ xs = (hd xs) # tl xs" by simp
  have "C2 = C1(p:= (p2, tl (snd (C1 p))))"   by (simp add: local.stepcR(5))
  then have "hd (snd (C1 p)) =  (i⇗q→p⇖)"  by (simp add: local.stepcR(4))
  have "snd (C1 p) ≠ ε" by (simp add: local.stepcR(3))
  then have "snd (C1 p) = (i⇗q→p⇖) # tl (snd (C1 p))"  using ‹∀xs. xs ≠ ε ⟶ xs = hd xs # tl xs› local.stepcR(4) by fastforce
  then have t2: "(snd (C1 p)) = [(i⇗q→p⇖)] ⋅ snd (C2 p)"  by (simp add: local.stepcR(5))
  then have t3: "∀x. x ≠ p ⟶ C1(x) = C2(x)" by (simp add: local.stepcR(5))
  then have "( | (snd (C1 p)) | ) <⇩ℬ None" by simp
  then show ?thesis using MboxRecv assms(2) local.stepcR(1) t1 t2 t3 by blast
qed

lemma stepc_produces_mbox_config :
  assumes "stepc C1 a C2" and "is_mbox_config C1"
  shows "is_mbox_config C2"
  using assms(1,2) mbox_step_rev(2) stepc_to_mbox by blast

lemma mbox_run_prod_mbox_config: 
  assumes "mbox_run C0 None w cs" and "cs ≠ []"
  shows "is_mbox_config (last cs)"
  using assms(1,2) run_produces_mailbox_configurations by auto

inductive runc :: "('peer ⇒ ('state × ('information, 'peer) message word)) ⇒ ('information, 'peer) action word  ⇒ ('peer ⇒ ('state × ('information, 'peer) message word)) list ⇒ bool" where
  runc_empty: "runc (𝒞⇩ℐ⇩𝔪) (ε) ([])" |
  runc_once: "⟦stepc (𝒞⇩ℐ⇩𝔪) a C2⟧ ⟹ runc (𝒞⇩ℐ⇩𝔪) ([a]) ([C2])" |
  runc_rec: "⟦runc C0 w cs; cs ≠ []; (stepc (last cs) a C2)⟧ ⟹ runc C0 (w@[a]) (cs@[C2])"

lemma runc_rev :
  assumes "runc C0 w cs"
  shows "(C0 = (𝒞⇩ℐ⇩𝔪) ∧ w = ε ∧ cs = []) ∨ (∃a C2. C0 = (𝒞⇩ℐ⇩𝔪) ∧ w = [a] ∧ cs = [C2]) ∨
(∃ccs v a C2. runc C0 v ccs ∧ ccs ≠ [] ∧ (stepc (last ccs) a C2 ∧ cs = ccs @ [C2]))"
  by (smt (verit) assms runc.simps)

lemma runc_to_mbox_run:
  assumes "runc C0 w cs" and "is_mbox_config C0"
  shows "mbox_run C0 None w cs"
  using assms
proof(induct rule: runc.induct)
  case runc_empty
  then show ?case by (simp add: MREmpty)
next
  case (runc_once a C2)
  then show ?case  by (simp add: mbox_step_to_run stepc_to_mbox)
next
  case (runc_rec C0 w cs a C2)
  then show ?case by (simp add: MRComposedInf mbox_run_prod_mbox_config stepc_to_mbox)
qed





section "start of an isabelle formalization of (the first?) counterexample to the theorem in the paper"

lemma ex_derive_infl_lang:
  assumes "((ℒ(p))) = {ε, [?⟨a⟩], [?⟨a⟩, ?⟨b⟩], [!⟨z⟩, ?⟨a⟩], [?⟨a⟩, !⟨z⟩]}" and "is_parent_of p q" and
    "((ℒ(q))) = {ε, [!⟨a⟩], [!⟨a⟩, !⟨b⟩]}" and "is_root q" and "(ℒ(q))⇂⇩{⇩p⇩,⇩q⇩} = (ℒ(q))"
  shows "ℒ⇧*(p) = ℒ(p)"
  using assms
proof -
  have "is_root q"  using assms(4) by auto
  then have "∀ w. (w ∈ ℒ(q)) ⟶ (w ∈ ℒ(q) ∧ is_root q)" by blast
  then have "∀ w. (w ∈ ℒ(q)) ⟶ is_in_infl_lang q w"  using IL_root by auto
  then have root_infl: "ℒ⇧*(q) = ℒ(q)"  by (simp add: infl_lang_subset_of_lang subsetI subset_antisym)

  have infl_p_pre1: "tree_topology ∧ is_parent_of p q"  using assms(2,4) by auto
  have d1: "(ε↓⇩?) = ε" by simp
  have d2: "([?⟨a⟩]↓⇩?) = [?⟨a⟩]" by simp
  have d3: "([?⟨a⟩, ?⟨b⟩]↓⇩?) = [?⟨a⟩, ?⟨b⟩]" by simp
  have d4: "([!⟨z⟩, ?⟨a⟩]↓⇩?) = [?⟨a⟩]"  by simp
  have d5: "([?⟨a⟩, !⟨z⟩]↓⇩?) = [?⟨a⟩]" by simp
  have "ℒ⇩?(p) = {w↓⇩? | w. w ∈  ℒ(p)}" by simp
  then have "ℒ⇩?(p) =  {w↓⇩? | w. w ∈ {ε, [?⟨a⟩], [?⟨a⟩, ?⟨b⟩], [!⟨z⟩, ?⟨a⟩], [?⟨a⟩, !⟨z⟩]}}"  by (simp add: assms(1))

  have d6: "∀ w. w ∈ ℒ(p) ⟶ ((w↓⇩?) ∈ {ε, [?⟨a⟩], [?⟨a⟩, ?⟨b⟩]})" 
  proof (rule ccontr)
    assume "¬ (∀w. w ∈ ℒ p ⟶ w↓⇩? ∈ {ε, ?⟨a⟩ # ε, ?⟨a⟩ # ?⟨b⟩ # ε})"
    then have "∃ w. w ∈ ℒ p ⟶ w↓⇩? ∉ {ε, ?⟨a⟩ # ε, ?⟨a⟩ # ?⟨b⟩ # ε}" by blast
    then show "False"  using ‹¬ (∀w. w ∈ ℒ p ⟶ w↓⇩? ∈ {ε, ?⟨a⟩ # ε, ?⟨a⟩ # ?⟨b⟩ # ε})› assms(1) d2 d4 d5 insertE insertI2
        insert_commute singleton_iff by auto
  qed
  have "ε↓⇩!⇩? = ε" by simp
  have "[?⟨a⟩]↓⇩!⇩? = [a]" by simp
  have "[?⟨a⟩, ?⟨b⟩]↓⇩!⇩? = [a, b]" by simp
  have t1: "∀ w. (w ∈ {ε, ?⟨a⟩ # ε, ?⟨a⟩ # ?⟨b⟩ # ε}) ⟶ (w↓⇩!⇩?  ∈ {ε, [a], [a,b]})"   by auto 
  then have "∀ w. w ∈ ℒ(p) ⟶ (((w↓⇩?)↓⇩!⇩? ∈ {ε, [a], [a,b]}))"  using d6 by presburger
  have r1: "∀ w. w ∈ ℒ(q) ⟶ (((w)↓⇩!⇩? ∈ {ε, [a], [a,b]}))"  by (simp add: assms(3))
  have "𝒫⇩?(q) = {}" using assms(4) global_to_local_root by presburger 
  then have r2: "∀ w. w ∈ ℒ(q) ⟶ ((w↓⇩!) = w)"  using no_inputs_implies_only_sends by auto
  then have "∀ w. w ∈ ℒ(q) ⟶ (((w↓⇩!)↓⇩!⇩? ∈ {ε, [a], [a,b]}))" using r1 by presburger
  have "ε↓⇩!⇩? = ε" by simp
  have "[!⟨a⟩]↓⇩!⇩? = [a]" by simp
  have "[!⟨a⟩, !⟨b⟩]↓⇩!⇩? = [a, b]" by simp
  then have "∀ w. w ∈ ℒ(q) ⟶ (((((w↓⇩{⇩p⇩,⇩q⇩})↓⇩!)↓⇩!⇩?) ∈ {ε, [a], [a,b]}))"   by (metis (mono_tags, lifting) assms(5) mem_Collect_eq r1 r2)
  have "∀ w. w ∈ ℒ(p) ⟶ (∃w'. ((w↓⇩?)↓⇩!⇩?) = (((w'↓⇩{⇩p⇩,⇩q⇩})↓⇩!)↓⇩!⇩?) ∧ is_in_infl_lang q w')" 
  proof (rule ccontr)
    assume "¬ (∀w. w ∈ ℒ p ⟶ (∃w'. w↓⇩?↓⇩!⇩? = w'↓⇩{⇩p⇩,⇩q⇩}↓⇩!↓⇩!⇩? ∧ is_in_infl_lang q w'))" 
    then have "∃ w. w ∈ ℒ p ⟶ ¬(∃w'. w↓⇩?↓⇩!⇩? = w'↓⇩{⇩p⇩,⇩q⇩}↓⇩!↓⇩!⇩? ∧ is_in_infl_lang q w')" by blast
    then have "∃ w. w ∈ ℒ p ∧ ¬(∃w'. w↓⇩?↓⇩!⇩? = w'↓⇩{⇩p⇩,⇩q⇩}↓⇩!↓⇩!⇩? ∧ is_in_infl_lang q w')"  using ‹¬ (∀w. w ∈ ℒ p ⟶ (∃w'. w↓⇩?↓⇩!⇩? = w'↓⇩{⇩p⇩,⇩q⇩}↓⇩!↓⇩!⇩? ∧ is_in_infl_lang q w'))› by blast
    then obtain w where "w ∈ ℒ p" and "¬(∃w'. w↓⇩?↓⇩!⇩? = w'↓⇩{⇩p⇩,⇩q⇩}↓⇩!↓⇩!⇩? ∧ is_in_infl_lang q w')" by blast
    then have "w↓⇩?↓⇩!⇩? ∈ {ε, [a], [a,b]}"  using ‹∀w. w ∈ ℒ p ⟶ w↓⇩?↓⇩!⇩? ∈ {ε, a # ε, a # b # ε}› by blast 
    have "(ℒ(q))⇂⇩{⇩p⇩,⇩q⇩} = (ℒ(q))" using assms by blast
    then have q_proj: "∀w. w ∈ (ℒ(q)) ⟶ w ∈ (ℒ(q))⇂⇩{⇩p⇩,⇩q⇩}" by blast
    have q_proj2: "∀w. w ∈ (ℒ(q))⇂⇩{⇩p⇩,⇩q⇩} ⟶ w↓⇩{⇩p⇩,⇩q⇩} = w" sorry
    have "w↓⇩?↓⇩!⇩? ≠ ε" using ‹∀w. w ∈ ℒ q ⟶ is_in_infl_lang q w› ‹∄w'. w↓⇩?↓⇩!⇩? = w'↓⇩{⇩p⇩,⇩q⇩}↓⇩!↓⇩!⇩? ∧ is_in_infl_lang q w'›
        assms(3) map_is_Nil_conv by force
    then show "False"
    proof (cases "w↓⇩?↓⇩!⇩? = [a]")
      case True
      have "[!⟨a⟩] ∈ ℒ q" by (simp add: assms(3))
      then have "is_in_infl_lang q [!⟨a⟩]"   by (simp add: ‹∀w. w ∈ ℒ q ⟶ is_in_infl_lang q w›)
      have "[!⟨a⟩]↓⇩{⇩p⇩,⇩q⇩} = [!⟨a⟩]" sorry
      have "[!⟨a⟩]↓⇩{⇩p⇩,⇩q⇩}↓⇩!↓⇩!⇩? = [a]" sorry
      then show ?thesis sorry
    next
      case False
      then show ?thesis sorry
    qed
  qed
  then have "∀ w. (∃w'. (w ∈ ℒ(p) ⟶ (tree_topology ∧ 
is_parent_of p q ∧ w ∈ ℒ(p) ∧  is_in_infl_lang q w' ∧  ((w↓⇩?)↓⇩!⇩?) = (((w'↓⇩{⇩p⇩,⇩q⇩})↓⇩!)↓⇩!⇩?))))"  using infl_p_pre1 by blast
  then have "∀ w. w ∈ ℒ(p) ⟶ is_in_infl_lang p w" using IL_node by blast
  then show ?thesis using w_in_infl_lang by force
qed


end