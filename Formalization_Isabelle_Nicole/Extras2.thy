


subsection "commented lemmas"
(*may or may not be useful at some point*)

(*any word can be shuffled from its origin where all sends are first and all receives come afterwards
lemma shuffle_origin:
  shows "x ⊔⊔⇩? ((x↓⇩!) ⋅ (x↓⇩?))"
  sorry
*)

lemma concat_infl_mbox:
  assumes "concat_infl p w [q] w_acc"
  shows "w_acc ∈ 𝒯⇘None⇙"
proof -
  define xp where xp_def: "xp = [q]"
  with assms  have "concat_infl p w xp w_acc"
    by simp
  from this xp_def show "w_acc ∈ 𝒯⇘None⇙"
  proof (induct)
    case (at_p ps)
    then show ?case sorry
  next
    case (reach_root q qw x w_acc)
    then show ?case sorry
  next
    case (node_step x q w_acc ps qw)
    then show ?case sorry
  qed
qed
(*
  using assms 
proof(induct "[q]" w_acc arbitrary: q rule: concat_infl.induct)
  case at_p
  then show ?case by (metis NetworkOfCA.path_to_root_first_elem_is_peer NetworkOfCA_axioms dual_order.eq_iff
        infl_lang_subset_of_lang lang_subset_infl_lang p_root root_lang_is_mbox)
next
  case (reach_root q qw x w_acc)
  then have "is_root q" by blast
  then have "qw ∈ 𝒯⇘None⇙" using reach_root.hyps(2) root_lang_is_mbox w_in_infl_lang by auto
      (* obtain end config C1 after qw, show that we can go from C1 to C2 by reading w *)
  then show ?case sorry
next
  case (node_step x q qw w_acc)
  then show ?case sorry
qed
*)


value "prefix [1] [1,2::nat]"
value "prefix [?⟨(a⇗q→p⇖)⟩] [?⟨(a⇗q→p⇖)⟩, !⟨(a⇗p→x⇖)⟩]" 
value "[?⟨y⟩, !⟨x⟩, ?⟨z⟩] ⊔⊔⇩? [!⟨x⟩, ?⟨y⟩, ?⟨z⟩]"
value "[!⟨x⟩, ?⟨y⟩, ?⟨z⟩] ⊔⊔⇩? [?⟨y⟩, !⟨x⟩, ?⟨z⟩]"

value "drop 5 [0,1,2,3,4,10,10,5,5,5,5,5::nat]" 

value "CommunicatingAutomaton.SendingToPeers ({(s1, !⟨(i⇗p→q⇖)⟩, s2)}::('state × ('information, 'peer) action × 'state) set)"
value "q ∈ CommunicatingAutomaton.SendingToPeers ({(s1, !⟨(i⇗p→q⇖)⟩, s2)}::('state × ('information, 'peer) action × 'state) set)"
term "𝒜"
term "𝒜 p"
term "(snd (snd (𝒜 p)))"

term "(fst (snd (𝒜 p)))"
term "(snd (snd (𝒜 p)))"

value "[!⟨(i⇗p→q⇖)⟩]↓⇩!⇩?"

value "[!⟨x⟩, ?⟨y⟩, ?⟨z⟩]"
value "let w = [!⟨x⟩, ?⟨y⟩, ?⟨z⟩] in ((w↓⇩?)↓⇩!⇩?)"
value "let w' = [?⟨a⟩, !⟨y⟩, !⟨z⟩] in ((w'↓⇩!)↓⇩!⇩?)"

value "(add_matching_recvs [!⟨m⟩])"


(* original run_rev
lemma run_rev : 
  fixes w :: "('information, 'peer) action word"
assumes "run s0 (w⋅[a]) (xs@[s])"
shows "last (s0#xs) ─a→ s ∧ run s0 w xs"
  using assms run.cases by fastforce
*)

(*TODO: fix this (as it is currently, it is incorrect since we do NOT enforce that xc is split in a way that makes sense with running u)
lemma sync_run_decompose: 
  assumes "sync_run C0 (u@v) (xc@yc)" 
  shows "sync_run C0 u xc ∧ sync_run (last (C0#xc)) v yc"
  using assms
proof (induct C0 "u@v" "xc@yc" arbitrary: u v xc yc)
  case (SREmpty C)
  then show ?case by (simp add: sync_run.SREmpty)
next
  case (SRComposed I0 w ws a Cn)
  then show ?case sorry
qed
*)

(* incorrect unless assumption is also that w contains only sens to p (and no other child)
lemma pair_proj_send_for_unique_parent:
  assumes "is_parent_of p q" and "w ∈ ℒ(q)"
  shows "(w↓⇩!)↓⇩{⇩p⇩,⇩q⇩} = (w↓⇩{⇩p⇩,⇩q⇩})"
  sorry
*)

(*
lemma path_to_root_exists: 
  assumes "tree_topology" and "p ∈ 𝒫"
  shows "∃ps. path_to_root p ps" 
proof (cases "is_root p")
  case True
  then show ?thesis using PTRRoot by auto
next
  case False
  then have "is_node p" using assms(1) root_or_node by blast
  then have "∃ q. is_parent_of p q" by (metis node_defs_eq node_parent)
  then obtain q where "q ∈ 𝒫" and "is_parent_of p q" by blast
  then have req1: "tree_topology ∧ is_parent_of p q" by (simp add: assms(1))
  have "∃ r. is_root r" using req1 root_exists by blast
  then obtain r where "is_root r" by auto
  then have "path_to_root r [r]" by (simp add: PTRRoot)
  then have "∃ps. path_to_root p (p # q # ps @ [r])" sorry (*by (blast dest: PTRNode)*)
  then show ?thesis by blast
qed

lemma path_to_root_exists2: 
  assumes "tree_topology" and "p ∈ 𝒫"
  shows "∃ps. path_to_root p ps" 
  using assms 
proof (induct "card (𝒫)")
  case 0
  then have "¬ is_tree (𝒫) (𝒢)" using finite_peers by auto
  then show ?case by (simp add: assms(1))
next
  case (Suc x)
  then show ?case using Suc 
  proof (cases "Suc x = 1")
    case True
    then have "is_root p" by (metis (mono_tags, lifting) Suc.hyps(2) UNIV_I assms(1) card_1_singletonE empty_Collect_eq singletonD
          tree_acyclic)
    then show ?thesis using PTRRoot by auto
  next
    case False
    then have "x ≥ 1"  by linarith
    then have "card (𝒫) ≥ 2"  using Suc.hyps(2) by linarith
    then have "∃q. q ∈ 𝒫 ∧ 𝒢⟨q→⟩ = {} ∧ is_node q" using assms(1) leaf_exists leaf_ingoing_edge by auto
    then obtain l where "l ∈ 𝒫 ∧ 𝒢⟨l→⟩ = {} ∧ is_node l" by auto
    then have "is_node l" by auto
    then have "∃r. r ∈ 𝒫 ∧ 𝒢⟨→l⟩ = {r}" using node_defs_eq by auto
    then obtain l_mom where "l_mom ∈ 𝒫" and "𝒢⟨→l⟩ = {l_mom}" by auto
    then have "is_node l ∧ 𝒢⟨→l⟩ = {l_mom}" by (simp add: assms(1))
    then have "is_parent_of l l_mom" using node_parent by force
    then have "card (𝒫 - {l}) = x" by (metis Suc.hyps(2) UNIV_I card_Diff_singleton_if diff_Suc_1)
    then have "∃a. path_to_root l_mom a" sorry
        (* remove leaf from tree, show use IH, then show that adding leaf keeps the path from IH
    then have "is_node l" 
    then obtain x where "(x, l) ∈ 𝒢" *)
    then show ?thesis sorry
  qed 
qed
*)


(*
lemma lem4_4_alt:
  assumes "∃ w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩q = w ∧ ((is_parent_of p q) ⟶  w'↓⇩p = ε)) ∧ (∃ xs. (xs @ w) ∈ 𝒯⇘None⇙)"
  shows "∃ w'. (w' ∈ 𝒯⇘None⇙ ∧ w'↓⇩q = w ∧ (∀g. (is_parent_of g q) ⟶  w'↓⇩g = ε)) ∧ (∃ xs. (xs @ w) ∈ 𝒯⇘None⇙)"
  sorry
*)



(*
lemma sync_send_to_child_recv:
  assumes "w ∈ ℒ⇩𝟬" and "(w)↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})" and "∀ a. a ∈ set w ⟶ (get_actor a = q ∧ get_object a = p)" and "is_parent_of p q" (*i.e. q is parent and sends to p*)
  shows "((w↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩?) ∈ ((ℒ⇩?(p))⇂⇩?)⇂⇩!⇩?" (*for all x in set w . get_actor x  = q *)
  sorry

lemma sync_word_to_sync_steps:
  assumes "w ∈ ℒ⇩𝟬" 
  shows "∀x. x ∈ (set (w)) ⟶ (∃ C1 C2. C1 ─⟨x, 𝟬⟩→ C2)"
  sorry
    (*
        have "(set v) ⊆ (set (w'↓⇩!))"  using w'_def by fastforce
        have w'_act_peers: "∀x. x ∈ set (((w'↓⇩!)↓⇩q)↓⇩{⇩p⇩,⇩q⇩}) ⟶ (get_actor x = q ∧ get_object x = p)" by auto

        have "∀x. x ∈ (set (w'↓⇩!)) ⟶ (∃ C1 C2. C1 ─⟨x, 𝟬⟩→ C2)"  using sync_word_to_sync_steps w'_sync by presburger
        then have "∀x. x ∈ set v ⟶ (∃ C1 C2. C1 ─⟨x, 𝟬⟩→ C2)"  using ‹set v ⊆ set (w'↓⇩!)› by blast
        then have "∀a. a ∈ set v ⟶ (∃ C1 C2. C1 (get_actor a) ─a→(get_actor a) (C2 (get_actor a)) ∧ (C1 (get_object a) ─(?⟨(get_message a)⟩)→(get_object a) (C2 (get_object a))))"  by (metis get_message.simps(1) sync_step_rev(5,6)) 
        
(*since w' is in infl. lang of q, and q sends stuff, and w' is sync word, all sends of w' must be immediately received*)
        
        (* probs need a lemma that shows that if i have some send sequence between two peers in sync lang, then
the send sequence is in the lang of that peer*) *)
*)

(*this one might be unnecessary but the conclusion of the lemma under this is needed
lemma subword_of_sync_is_receivable:
  assumes "w'↓⇩! ∈ ℒ⇩𝟬" and "w'↓⇩p = ε" and "((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})" and "is_parent_of p q" and "is_synchronisable" and "tree_topology"
  shows "(((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∈ ((ℒ(p))⇂⇩?)⇂⇩!⇩?"
  sorry

lemma subword_of_sync_is_receivable2:
  assumes "w'↓⇩! ∈ ℒ⇩𝟬" and "w'↓⇩p = ε" and "((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩} ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})" and "is_parent_of p q" and "(((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∈ ((ℒ(p))⇂⇩?)⇂⇩!⇩?"
  shows "(((w'↓⇩q)↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∈ (ℒ⇧*(p))⇂⇩!⇩?"
  sorry
*)



(*
(*show that !a must be immediately receivable*)
lemma subset_condition_alt_concrete_app:
  assumes "w' @ [(!⟨(i⇗q→p⇖)⟩)] ∈ ℒ⇧*(q)" and "w ∈ ℒ⇧*(p)" and "subset_condition p q" 
and  "((w'↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? = ((w↓⇩?))↓⇩!⇩?"
shows "w @ [(?⟨(i⇗q→p⇖)⟩)] ∈ ℒ⇧*(p)"
  using assms
proof -
  have sub: "subset_condition_alt p q"  by (simp add: assms(3) subset_conds_eq)
  have "((w'↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∈ ((⟦w⟧⇩p)⇂⇩!⇩?)" using assms(2,4) by force

  have "(((w' @ [(!⟨(i⇗q→p⇖)⟩)])↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∈ ((⟦w⟧⇩p)⇂⇩!⇩?)" 
  proof (rule ccontr)
    assume "(w' ⋅ !⟨(i⇗q→p⇖)⟩ # ε)↓⇩!↓⇩{⇩p⇩,⇩q⇩}↓⇩!⇩? ∉ ((⟦w⟧⇩p)⇂⇩!⇩?)"
    then have "(w ∈ ℒ⇧*(p) ∧ ( (w' ⋅ !⟨(i⇗q→p⇖)⟩ # ε) ∈ ℒ⇧*(q) ∧  (((w' ⋅ !⟨(i⇗q→p⇖)⟩ # ε)↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∉ ((⟦w⟧⇩p)⇂⇩!⇩?)))"
      using assms(1,2) by blast
    then have "¬ (∀ w ∈ ℒ⇧*(p). (∀ w' ∈ ℒ⇧*(q). ((w'↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? ∈ ((⟦w⟧⇩p)⇂⇩!⇩?)))" by blast
    then have no_sub: "¬ subset_condition_alt p q" unfolding subset_condition_alt_def by simp
    then show "False" using sub by simp
  qed
  then obtain x where "(w ⋅ x) ∈ ℒ⇧*(p)" and "(x = x↓⇩?)"  by auto
  then have "x = [(?⟨(i⇗q→p⇖)⟩)]" try 

  then show ?thesis try
qed
*)

(*given some parent word, show that there is a word
lemma subset_condition_for_parent_word:
  assumes "(w ∈ ℒ⇧*(q))" and "is_parent_of p q" and "subset_condition p q" and "w' ∈ ℒ⇧*(p)"
  shows "∃x. (w ⋅ x) ∈ ℒ⇧*(p) ∧ (x = x↓⇩?) ∧ (w↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? = ((w ⋅ x)↓⇩?)↓⇩!⇩?"
  sorry
 *)

(*shows that add_matching_recvs of a trace results in a word that receives exactly all sends (not arbitrary prefix)*)
(*follows from def./construction of add_matching_recvs of a trace
lemma matching_recvs_word_matches_sends:
  assumes "e ∈ 𝒯⇘None⇙" and "is_parent_of p q"
  shows "(((e↓⇩!))↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩? = (((add_matching_recvs (e↓⇩!)↓⇩?)↓⇩p)↓⇩!⇩?)" (*q sends a to p ⟶ p receives a*)
proof (induct "(e↓⇩!)" arbitrary: e rule: add_matching_recvs.induct)
  case 1
  then show ?case by simp
next
  case (2 a w)
  then obtain t where t_def: "e↓⇩! = [a]↓⇩! ⋅ t" by (metis Cons_eq_appendI append_self_conv2 filter_append filter_recursion)
  then show ?case sorry
qed
*)

(* this is true but unnecessary to prove
lemma matching_recvs_word_send_actor_proj_inv:
  assumes "e ∈ 𝒯⇘None⇙" and "is_parent_of q r" and "v' = add_matching_recvs (e↓⇩!)"
  shows "((v'↓⇩r)↓⇩!)↓⇩{⇩q⇩,⇩r⇩} = ((v')↓⇩!)↓⇩{⇩q⇩,⇩r⇩}"
  sorry


lemma match_recv_word_matches_parent_exactly:
assumes "e ∈ 𝒯⇘None⇙" and "is_parent_of p q"
shows "(((add_matching_recvs (e↓⇩!)↓⇩p)↓⇩?)↓⇩!⇩?) = (((e↓⇩!)↓⇩{⇩p⇩,⇩q⇩})↓⇩!⇩?)"
  sorry
*)

(*
lemma mbox_trace_impl_root_portion_in_lang:
  assumes "w ∈ 𝒯⇘None⇙⇂⇩!" and "is_root q"
  shows "w↓⇩q ∈ ℒ⇧* q "
  sorry


(*can always send something after any execution (as long as the peer is capable of it),
since in mbox nothing needs to be received*)
lemma mbox_exec_send_append:
  assumes "w ∈ 𝒯⇘None⇙" and "w↓⇩q ⋅ [a] ∈ ℒ⇧* q" and "is_output a"
  shows "w ⋅ [a] ∈ 𝒯⇘None⇙" 
  sorry
*)

(*
lemma prefix_matching_without_signs_to_with:
  assumes "prefix (w↓⇩!⇩?) (w'↓⇩!⇩?)" and "w↓⇩? = w" and "w'↓⇩! = w'" and "prefix w'_pre w'"
  shows "prefix (w↓⇩!⇩?) (w'_pre↓⇩!⇩?)"
  sorry

lemma prefix_of_full_word_eq_to_previous_prefix:
  assumes "prefix (w↓⇩?) (((w')↓⇩q)↓⇩?)" 
  shows "∃w''. prefix w'' (w') ∧ (w↓⇩?) = (((w''↓⇩q))↓⇩?)"
  sorry
*)

(*
lemma matching_no_sign_and_prefix_to_prefix:
  assumes "(w↓⇩!⇩?) = (w'↓⇩!⇩?)" and "prefix v w'"
  shows "prefix (v↓⇩!⇩?) (w↓⇩!⇩?)"
  by (simp add: assms(1,2) prefix_inv_no_signs)
*)


(*THIS IS SADLY NOT CORRECT! not every two words with same recv/send orders can be shuffled into each other,
one !a needs to be moved all the way right in w and ?b needs to be moved all the way left in w' (for ..!a?b.. as
origin) then w can't be shuffled into w', since !a is on the right in w but not in w' 
and w' can't be shuffled into w, since ?b cannot go left again to its position in w*)
(*all words with the same send/recv order (respectively) can shuffle into the  fully shuffled version of 
that word, and are shuffles of the word where all outputs are first, and then all inputs
e.g. a word with sends !a!a and receives ?b only has possibilities: !a!a?b, !a?b!a, ?b!a!a.
Thus, for any words with those sends&receives, one must be a shuffle of the other
e.g. for !a!a?b and ?b!a!a, the latter is a shuffle of the former.
lemma send_recv_orders_match_implies_shuffle:
  assumes "w↓⇩? = w'↓⇩? ∧ w↓⇩! = w'↓⇩!" 
  shows "w ⊔⊔⇩? w' ∨ w' ⊔⊔⇩? w" 
  using assms sorry
(*the proof boils down to every such w, w' being inbetween ?y0...?yn!x0...!xm and !x0...!xm?y0...?yn
using the transitive shuffled rule
the issue is: how to find out whether w or w' was shuffled less (i.e. is closer to the origin word)
→ maybe count number of shuffles that occurred for both w and w' (that also requires further helper lemmas though)*)
*)


(*for peer words wq and wq' = (v'q !a), if the latter can be shuffled into the former and they are NOT
equal, then their respective executions cannot have the same trace.
lemma diff_peer_word_impl_diff_trace:
  assumes "wq↓⇩? = (v'↓⇩q ⋅ [a])↓⇩?" and "wq↓⇩! = (v'↓⇩q ⋅ [a])↓⇩!" (*this also follows from the shuffling def.*)
and "wq ⊔⊔⇩? (v'↓⇩q ⋅ [a])" and "wq ≠ (v'↓⇩q ⋅ [a])"
and "e ∈ 𝒯⇘None⇙" and "v' ∈ 𝒯⇘None⇙" and "(v ⋅ [a]) ∈ 𝒯⇘None⇙⇂⇩!" and "v' = (add_matching_recvs v)"
and "v'↓⇩q ∈ ℒ⇧* q" and "wq ∈ ℒ⇧* q"
shows "e↓⇩! ≠ v'↓⇩!" 
  sorry
(*since wq is shuffle of (v'q !a), there is some unique (identify uniquely by number of occurence)
pair !x,?y, s.t. !x < ?y in v'q but ?y < !x in wq (!x is not !a, since !a cannot move left 
by shuffling and is already in the rightmost position of v'q !a)
→ by constr. of v', !x < !y in trace v and thus in trace w as well 
→ since e is valid execution, ?y must be sent before !x is sent and so !y < !x in w 
this then means that both executions do not have the same traces!
(this can then be used in the lemma below, to prove that if wq is shuffle of v'q !a, the assumption that
both e and v' !a have the same trace is violated.
 *)*)









(*
lemma recv_in_mbox_requ_send:
  assumes "(?⟨(i⇗q→p⇖)⟩) ∈ set w" and "w ∈ 𝒯⇘None⇙" 
  shows "(!⟨(i⇗q→p⇖)⟩) ∈ set w"
    (*otherwise there is configuration where the element is not in the buffer but it is taken out*)
    (*might need mboxstep lemma to show that if the step is recv, then the thing is in the buffer (but that should
be there already)*)
(*!warning! if the same send action occurs more than once it isn't sufficient to just have one send of that form,
i.e. this condition is insufficient depending on what it's used for*)
  sorry


WRONG:
lemma sync_mbox_exec_impl:
  assumes "xs @ [!⟨(i⇗q→p⇖)⟩] @ ys @ [?⟨(i⇗q→p⇖)⟩] @ zs ∈ 𝒯⇘None⇙" and "is_synchronisable" and "tree_topology"
  shows "xs @ [!⟨(i⇗q→p⇖)⟩] @ [?⟨(i⇗q→p⇖)⟩] @ ys @ zs ∈ 𝒯⇘None⇙"
  sorry

lemma mbox_word_to_peer_act:
  assumes "(w @ [a]) ∈ 𝒯⇘None⇙⇂⇩!" and "tree_topology" 
  shows "∃ s1 s2. (s1, a, s2) ∈ ℛ q"
  sorry

lemma matched_mbox_run_to_sync_run :
  assumes "mbox_run 𝒞⇩ℐ⇩𝔪 None (add_matching_recvs w) xcm" and "w ∈ 𝒯⇘None⇙⇂⇩!"
  shows "sync_run 𝒞⇩ℐ⇩𝟬 w xcs"
  sorry 




theorem another wip of ⟹2. (unnecessarily complicated since we know exactly ONE swap occurred)
 case (swap b a w xs ys) (*exactly one swap occurred*)
            (*obtain vq, matching word of q to v (which provides the exact sends to p needed for v)*)
            then have "∃vq.  vq ∈ ℒ⇧*(q) ∧ ((v↓⇩?)↓⇩!⇩?) = (((vq↓⇩{⇩p⇩,⇩q⇩})↓⇩!)↓⇩!⇩?)" 
              using infl_parent_child_matching_ws[of v p q] orig_in_L q_parent by blast
            then obtain vq where vq_v_match: "((v↓⇩?)↓⇩!⇩?) = (((vq↓⇩{⇩p⇩,⇩q⇩})↓⇩!)↓⇩!⇩?)" and vq_def: "vq ∈ ℒ⇧* q" by auto
            have lem4_4_prems: "tree_topology ∧ w ∈ ℒ⇧*(p) ∧ p ∈ 𝒫" using assms swap.prems by auto
            then show ?case using assms swap vq_v_match vq_def lem4_4_prems
            proof (cases "is_root q")
              case True
              then have "vq ∈ 𝒯⇘None⇙" sorry (*since q is root and thus vq are only sends*)
              (*then mix vq with v (while considering v') as valid mbox execution (works since vq needs
             nothing from any other peer, and vq provides all necessary sends for v)*)
          let ?mix = "mix_triple vq v' v []"
          have "?mix ∈ 𝒯⇘None⇙" sorry
          then obtain t where "t ∈ ℒ⇩𝟬 ∧ t ∈ 𝒯⇘None⇙⇂⇩! ∧ t = (?mix)↓⇩!" using sync_def by fastforce
          then obtain xc where t_sync_run : "sync_run 𝒞⇩ℐ⇩𝟬 t xc" using SyncTraces.simps by auto
          (*find the sync execution (here as mbox run) where each send is directly followed by recv
          → by constr. of the mix, this means each send is exactly in front of where a receive would
          be in v' (in v there may not be) → the sync execution yields v' when projected on p*)
          then have "∃xcm. mbox_run 𝒞⇩ℐ⇩𝔪 None (add_matching_recvs t) xcm" using empty_sync_run_to_mbox_run sync_run_to_mbox_run by blast
          (*then obtain the sync execution for the trace of the constructed execution*)
          then have sync_exec: "(add_matching_recvs t) ∈ 𝒯⇘None⇙" using MboxTraces.intros by auto
          (*then the sync execution has exactly v' as peer word of p, which then must be in the 
          infl. language of p since it is in an execution (shuffled lang. condition proven!)*)
          then have "(add_matching_recvs t)↓⇩p = v'" sorry
          then have "v' ∈ ℒ⇧* p" using sync_exec mbox_exec_to_infl_peer_word by blast
          then show ?thesis


theorem wip of ⟹2. 
  (* ⟹ 2.: prove influenced language is also shuffled language *)
      show "ℒ⇧*(p) = ℒ⇧*⇩⊔⇩⊔(p)" 
      proof
        (* First inclusion is by definition *)
        show "ℒ⇧*(p) ⊆ ℒ⇧*⇩⊔⇩⊔(p)" using language_shuffle_subset by auto
            (* Second inclusion via proof*)
        show "ℒ⇧*⇩⊔⇩⊔(p) ⊆ ℒ⇧*(p)" 
        proof
          fix v
            (*take arbitrary shuffled word v and show that is in the influenced lang, using (one of its) origin(s) v'*)
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
(*
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
                  → so, xs can only be sends to children of p, and bs can be anything from q *)
*)               
              then show ?thesis sorry
            next
              case False (*then a is received but never sent in w', contradicting that it is valid mbox word*)
              have "set w' = (set ws') ∪ (set w)" using ‹ws' ⋅ w = w'› by fastforce
              then have send_notin_w': "(!⟨(i⇗q→p⇖)⟩) ∉ set w'"  by (simp add: False send_not_in_w)
              have recv_in_w': "(?⟨(i⇗q→p⇖)⟩) ∈ set w'"   using ‹set w' = set ws' ∪ set w› ‹w ∈ ℒ p ∧ a ∈ set w› a_def by auto
              then show ?thesis using ‹w' ∈ 𝒯⇘None⇙› sorry (*recv_in_mbox_requ_send send_notin_w' by auto*)
            qed
          next
            case (trans w w' w'')
            then show ?case by simp
          qed
        qed
      qed
    qed
  qed








(*theorem prev.t version (without wips for brevity*)
(*state at a glance: all subproofs except <==2. need to be adjusted to reflect the new subset condition*)
(* Nsync = L0, ENsync = T0, EMbox = Tinf/None, TMbox = Linf, E = !?, T = only sends *)
theorem synchronisability_for_trees:
  assumes "tree_topology" 
  shows "is_synchronisable ⟷ (∀p q. ((is_parent_of p q) ⟶ ((subset_condition p q) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))" (is "?L ⟷ ?R")
  using assms unfolding subset_condition_def prefix_def NetworkOfCA_def 
proof
  (* ⟹: is_synchronisable ⟹ language conditions *)
  assume "?L"
  show "?R"
  proof clarify
    fix p q
    assume q_parent: "is_parent_of p q"
    have sync_def: "𝒯⇘None⇙⇂⇩! = ℒ⇩𝟬" using ‹?L› by simp
    show "subset_condition p q ∧ ℒ⇧* p = ℒ⇧*⇩⊔⇩⊔ p"
    proof (rule conjI)
      (* ⟹ 1.: prove the influenced language subset condition holds *)
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
            (* → contradiction not yet found with new condition, needs to be adjusted/ brought into the syntax of the new condition*)
        show "False" sorry
      qed
        (* ⟹ 2.: prove influenced language is also shuffled language *)
      show "ℒ⇧*(p) = ℒ⇧*⇩⊔⇩⊔(p)" 
      proof
        (* First inclusion is by definition *)
        show "ℒ⇧*(p) ⊆ ℒ⇧*⇩⊔⇩⊔(p)" using language_shuffle_subset by auto
            (* Second inclusion via proof*)
        show "ℒ⇧*⇩⊔⇩⊔(p) ⊆ ℒ⇧*(p)" 
        proof
          fix v
            (*take arbitrary shuffled word v and show that is in the influenced lang, using (one of its) origin(s) v'*)
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
                  → so, xs can only be sends to children of p, and bs can be anything from q *)
                then show ?thesis sorry
            next
              case False (*then a is received but never sent in w', contradicting that it is valid mbox word*)
              have "set w' = (set ws') ∪ (set w)" using ‹ws' ⋅ w = w'› by fastforce
              then have send_notin_w': "(!⟨(i⇗q→p⇖)⟩) ∉ set w'"  by (simp add: False send_not_in_w)
              have recv_in_w': "(?⟨(i⇗q→p⇖)⟩) ∈ set w'"   using ‹set w' = set ws' ∪ set w› ‹w ∈ ℒ p ∧ a ∈ set w› a_def by auto
              then show ?thesis using ‹w' ∈ 𝒯⇘None⇙› recv_in_mbox_requ_send send_notin_w' by auto
            qed
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
*)



(*
fun mix_pair :: "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ nat ⇒ nat ⇒ ('information, 'peer) action word" where
 "mix_pair [] [] acc = acc" |
 "mix_pair (a # w') [] acc = mix_pair w' [] (a # acc)" |
 "mix_pair [] (a # w) acc = mix_pair [] w (a # acc)" |
 "mix_pair (a # w') (b # w) acc  = (if a = !⟨get_message b⟩
      then (if b = ?⟨get_message a⟩ then mix_pair w' w (a # b # acc) else mix_pair (a # w') w (b # acc))
      else mix_pair w' (b # w) (a # acc))"

fun mix_shuf :: "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ nat ⇒ nat ⇒ ('information, 'peer) action word" where
 "mix_shuf [] [] i k = []" |
 "mix_shuf (a # vq) v i k = (if i < |v| ∧ k < |v| then 
(if a = !⟨get_message (v!i)⟩ ∧ (v!i) = ?⟨get_message a⟩ then a # (v!i) # mix_shuf vq v (Suc i) k else 
(if i = k ∧ (Suc i) < |v| ∧  a = !⟨get_message (v!(Suc i))⟩ then [] else []))
 else [])"



 "mix_shuf (a # vq) v i k = a # (mix_shuf vq v i k)" |
 "mix_shuf [] (a # v) k k_recv = a # (mix_shuf [] v k k_recv)" |
 "mix_shuf (a # vq) (b # v) k k_recv = (if a = !⟨get_message b⟩
      then (if b = ?⟨get_message a⟩ then mix_pair w' w (a # b # acc) else mix_pair (a # w') w (b # acc))
      else mix_pair w' (b # w) (a # acc))"


inductive mix_shuf :: "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ ('information, 'peer) action word  ⇒ bool" where
  mix_empty: "mix_shuf [] [] [] []" |
  mix_1: "⟦vq↓⇩!↓⇩{⇩p⇩,⇩q⇩}↓⇩!⇩? = v↓⇩?↓⇩!⇩?; v' ∈ ℒ⇧*⇩⊔⇩⊔(p); v' ⊔⊔⇩? v; v ∈ ℒ⇧*(p); vq ∈ ℒ⇧*(q)⟧ ⟹ mix_shuf vq v' v acc"
*)

(*construct acc, s.t. each send of vq is directly followed by the matching receive in v
unless 
fun mix_shuf :: "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ nat ⇒ ('information, 'peer) action ⇒ ('information, 'peer) action word" where
 "mix_shuf [] [] k k_recv = []" |
 "mix_shuf (a # vq) [] k k_recv = a # (mix_shuf vq [] k k_recv)" |
 "mix_shuf [] (a # v) k k_recv = a # (mix_shuf [] v k k_recv)" |
 "mix_shuf (a # vq) (b # v) k k_recv = (if a = !⟨get_message b⟩
      then (if b = ?⟨get_message a⟩ then mix_pair w' w (a # b # acc) else mix_pair (a # w') w (b # acc))
      else mix_pair w' (b # w) (a # acc))"
*)
(*mix a triple of w'' whose sends (to p) match receives in w, with w', s.t. w' is shuffle of w
the result consists of a mix of w'' and w, s.t. the sync trace of this mixture results in exactly w'
fun mix_triple :: "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ ('information, 'peer) action word" where
 "mix_triple [] [] [] acc = acc" |
 "mix_triple w'' w' w acc = undefined"
*)


