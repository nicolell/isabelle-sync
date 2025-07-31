(* Author: Kirstin Peters, Augsburg University, 2024 *)

theory Express
  imports CommunicatingAutomaton

begin

context NetworkOfCA
begin


(*TODO: w projected to x is empty for all x that are children/grandchildren, etc. of q, not just the direct children
and empty for all nodes not on the path to root from q. \<rightarrow> each node not on the path to root starting at q, performs
no action in this execution!*)
(*Let N be a network such that CF = C, G(N) is a tree, q \<in> P, and w \<in> L ≬(Aq). Then there
is an execution w\<Zprime> \<in> E(Nmbox) such that w\<Zprime>\<down>q = w and w\<Zprime>\<down>p = \<epsilon> for all p \<in> P with Pp
send = {q}.*)
lemma lemma4_4 : 
  fixes w :: "('information, 'peer) action word"
    and q :: "'peer"
  assumes "tree_topology" and "w \<in> \<L>\<^sup>*(q)" and "q \<in> \<P>"
  shows "\<exists> w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>q = w \<and> ((is_parent_of p q) \<longrightarrow>  w'\<down>\<^sub>p = \<epsilon>))"
    (*shows "\<exists> w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>q = w \<and> (\<forall>p. (p \<in> \<P> \<and> \<P>\<^sub>?(p) = {q}) \<longrightarrow>  w'\<down>\<^sub>p = \<epsilon>))"*)
  using assms
proof (cases "is_root q") 
  case True \<comment> \<open>q = r\<close>
  then have "w \<in> \<L>(q)" using assms(2) is_in_infl_lang.cases by blast
  then have "w = w\<down>\<^sub>!"  by (meson NetworkOfCA.no_inputs_implies_only_sends_alt NetworkOfCA_axioms True assms(1) global_to_local_root
        p_root)
  then have "w\<down>\<^sub>? = \<epsilon>"  by (simp add: output_proj_input_yields_eps)
  then have t2: "w = w\<down>\<^sub>q" by (simp add: \<open>w \<in> \<L> q\<close> w_in_peer_lang_impl_p_actor)
  then have "\<forall> p. p \<noteq> q \<longrightarrow> w\<down>\<^sub>p = \<epsilon>"  by (metis only_one_actor_proj)
  then have t3: "(\<forall>p. (p \<in> \<P> \<and> \<P>\<^sub>?(p) = {q}) \<longrightarrow>  w\<down>\<^sub>p = \<epsilon>)" by (metis True assms(1) global_to_local_root insert_not_empty ) 
      \<comment> \<open>need to prove lemma that if w is w of root r, then mbox (unbounded) has a run for it 
basically construct the configs, where it starts with (\<I>(r), \<epsilon>) and each step appends a send to the buffer of the respective receiver\<close>
  then have "w \<in> \<L>(q)" by (simp add: \<open>w \<in> \<L> q\<close>)
  then have "is_root q" using True by auto
  then have "w \<in> \<T>\<^bsub>None\<^esub>" using \<open>w \<in> \<L> q\<close> root_lang_is_mbox by auto
  have "w\<down>\<^sub>q = w" using t2 by auto
  then have "(is_parent_of p q \<longrightarrow> w\<down>\<^sub>p = \<epsilon>)" by (metis True is_parent_of_rev(2) iso_tuple_UNIV_I only_one_actor_proj root_defs_eq t3)
  then show ?thesis by (metis \<open>w \<in> \<T>\<^bsub>None\<^esub>\<close> t2)
next
  case False (*path to root of length n>1, i.e. q is NOT root*)
  then obtain p where q_parent: "is_parent_of q p" by (metis UNIV_I assms(1) path_to_root.cases path_to_root_exists)
  then obtain ps where p2root: "path_to_root p (p # ps)" by (metis UNIV_I assms(1) path_to_root_exists path_to_root_rev)
  then have "is_node q"  by (metis is_parent_of.cases q_parent)
  have "w \<in> \<L>\<^sup>*(q)"  using assms(2) by auto
  then have "is_parent_of q p" by (simp add: q_parent)
      (*by w in infl lang, we can find some w' with matching sends*)
  then have "\<exists>w'. w'\<in> \<L>\<^sup>* p \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>p\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"  using assms(2) infl_parent_child_matching_ws by blast
  then obtain w' where w'_w: "((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>p\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" and w'_Lp: "w' \<in> \<L>\<^sup>* p" by blast
  then have "w' \<in> \<L> p" by (meson mem_Collect_eq w_in_infl_lang)
  have "tree_topology"  using assms(1) by auto
  have c1: "((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>p\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?) \<and> w \<in> \<L>(q) \<and> w' \<in> \<L>(p) \<and> is_node q" using \<open>is_parent_of q p\<close>
      \<open>is_tree (\<P>) (\<G>) \<and> (\<exists>qa. \<G>\<langle>\<rightarrow>q\<rangle> = {qa}) \<or> is_tree (\<P>) (\<G>) \<and> (\<exists>qa. \<P>\<^sub>? q = {qa} \<or> q \<in> \<P>\<^sub>! qa)\<close> \<open>w' \<in> \<L> p\<close>
      assms(2) is_in_infl_lang_rev2(1) w'_w by blast
      (*repeat this argument for all peers on the path to the root*)
  obtain r where "is_root r" using assms(1) root_exists by blast
  have "path_to_root q (q # p # ps)" using p2root p2root_down_step q_parent by auto
  then have "concat_infl q w (q # p # ps) w"  using assms(1,2) at_p by auto
  have "w \<in> \<L>(q)"  by (simp add: c1)
  then have "w\<down>\<^sub>q = w"  using w_in_peer_lang_impl_p_actor by auto
      (* prepend first word to wn \<rightarrow>   w(n-1) \<cdot> w(n) *)
      (*then have "concat_infl q w (p # ps) (w' \<cdot> w)" *)
      (*obtain w1 \<cdot> w2 \<cdots> wn*)
  obtain w_acc where "concat_infl q w [r] w_acc" by (meson \<open>concat_infl q w (q # p # ps) w\<close>
        \<open>is_tree (\<P>) (\<G>) \<and> \<P>\<^sub>? r = {} \<and> (\<forall>q. r \<notin> \<P>\<^sub>! q) \<or> is_tree (\<P>) (\<G>) \<and> \<G>\<langle>\<rightarrow>r\<rangle> = {}\<close>
        concat_infl_word_exists)
  then have "w_acc \<in> \<T>\<^bsub>None\<^esub>" by (simp add: concat_infl_mbox)
  have "w_acc\<down>\<^sub>q = w"  using \<open>concat_infl q w (r # \<epsilon>) w_acc\<close> concat_infl_actor_consistent by blast
  then have "(\<forall>p. (is_parent_of p q) \<longrightarrow>  w_acc\<down>\<^sub>p = \<epsilon>)"  using \<open>concat_infl q w (r # \<epsilon>) w_acc\<close> concat_infl_children_not_included by blast
  then show ?thesis using \<open>w_acc \<in> \<T>\<^bsub>None\<^esub>\<close> \<open>w_acc\<down>\<^sub>q = w\<close> by blast
qed
  (*construct w from infl lang, for a given path from p to root r.
wn in infl lang of p, wn-1 (the matching sends) from parent of p, wn-2 with 
the matching sends of grandparent of p, ... until we reach w1 where infl lang = lang0
\<rightarrow> then w1 w2 .... wn (all concatenated in this order of the pth) is in mbox
*)


(*TODO: w projected to x is empty for all x that are children/grandchildren, etc. of q, not just the direct children
and empty for all nodes not on the path to root from q. \<rightarrow> each node not on the path to root starting at q, performs
no action in this execution!*)
lemma lemm4_4_extra:
  fixes w :: "('information, 'peer) action word"
    and q :: "'peer"
  assumes "tree_topology" and "w \<in> \<L>\<^sup>*(q)" and "q \<in> \<P>"
  shows "\<exists> w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>q = w \<and> ((is_parent_of p q) \<longrightarrow>  w'\<down>\<^sub>p = \<epsilon>)) \<and> (\<exists> xs. (xs @ w) = w')"
  using assms
proof (cases "is_root q") 
  case True \<comment> \<open>q = r\<close>
  then have "w \<in> \<L>(q)" using assms(2) is_in_infl_lang.cases by blast
  then have "w = w\<down>\<^sub>!"  by (meson NetworkOfCA.no_inputs_implies_only_sends_alt NetworkOfCA_axioms True assms(1) global_to_local_root
        p_root)
  then have "w\<down>\<^sub>? = \<epsilon>"  by (simp add: output_proj_input_yields_eps)
  then have t2: "w = w\<down>\<^sub>q" by (simp add: \<open>w \<in> \<L> q\<close> w_in_peer_lang_impl_p_actor)
  then have "\<forall> p. p \<noteq> q \<longrightarrow> w\<down>\<^sub>p = \<epsilon>"  by (metis only_one_actor_proj)
  then have t3: "(\<forall>p. (p \<in> \<P> \<and> \<P>\<^sub>?(p) = {q}) \<longrightarrow>  w\<down>\<^sub>p = \<epsilon>)" by (metis True assms(1) global_to_local_root insert_not_empty ) 
      \<comment> \<open>need to prove lemma that if w is w of root r, then mbox (unbounded) has a run for it 
basically construct the configs, where it starts with (\<I>(r), \<epsilon>) and each step appends a send to the buffer of the respective receiver\<close>
  then have "w \<in> \<L>(q)" by (simp add: \<open>w \<in> \<L> q\<close>)
  then have "is_root q" using True by auto
  then have "w \<in> \<T>\<^bsub>None\<^esub>" using \<open>w \<in> \<L> q\<close> root_lang_is_mbox by auto
  have "w\<down>\<^sub>q = w" using t2 by auto
  then have "(is_parent_of p q \<longrightarrow> w\<down>\<^sub>p = \<epsilon>)" by (metis True is_parent_of_rev(2) iso_tuple_UNIV_I only_one_actor_proj root_defs_eq t3)
  then show ?thesis by (metis \<open>w \<in> \<T>\<^bsub>None\<^esub>\<close>  append_self_conv2 t2)
next
  case False (*path to root of length n>1, i.e. q is NOT root*)
  then obtain p where q_parent: "is_parent_of q p" by (metis UNIV_I assms(1) path_to_root.cases path_to_root_exists)
  then obtain ps where p2root: "path_to_root p (p # ps)" by (metis UNIV_I assms(1) path_to_root_exists path_to_root_rev)
  then have "is_node q"  by (metis is_parent_of.cases q_parent)
  have "w \<in> \<L>\<^sup>*(q)"  using assms(2) by auto
  then have "is_parent_of q p" by (simp add: q_parent)
      (*by w in infl lang, we can find some w' with matching sends*)
  then have "\<exists>w'. w'\<in> \<L>\<^sup>* p \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>p\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"  using assms(2) infl_parent_child_matching_ws by blast
  then obtain w' where w'_w: "((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>p\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" and w'_Lp: "w' \<in> \<L>\<^sup>* p" by blast
  then have "w' \<in> \<L> p" by (meson mem_Collect_eq w_in_infl_lang)
  have "tree_topology"  using assms(1) by auto
  have c1: "((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>p\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?) \<and> w \<in> \<L>(q) \<and> w' \<in> \<L>(p) \<and> is_node q" using \<open>is_parent_of q p\<close>
      \<open>is_tree (\<P>) (\<G>) \<and> (\<exists>qa. \<G>\<langle>\<rightarrow>q\<rangle> = {qa}) \<or> is_tree (\<P>) (\<G>) \<and> (\<exists>qa. \<P>\<^sub>? q = {qa} \<or> q \<in> \<P>\<^sub>! qa)\<close> \<open>w' \<in> \<L> p\<close>
      assms(2) is_in_infl_lang_rev2(1) w'_w by blast
      (*repeat this argument for all peers on the path to the root*)
  obtain r where "is_root r" using assms(1) root_exists by blast
  have "path_to_root q (q # p # ps)" using p2root p2root_down_step q_parent by auto
  then have "concat_infl q w (q # p # ps) w"  using assms(1,2) at_p by auto
  have "w \<in> \<L>(q)"  by (simp add: c1)
  then have "w\<down>\<^sub>q = w"  using w_in_peer_lang_impl_p_actor by auto
      (* prepend first word to wn \<rightarrow>   w(n-1) \<cdot> w(n) *)
      (*then have "concat_infl q w (p # ps) (w' \<cdot> w)" *)
      (*obtain w1 \<cdot> w2 \<cdots> wn*)
  obtain w_acc where concat: "concat_infl q w [r] w_acc" by (meson \<open>concat_infl q w (q # p # ps) w\<close>
        \<open>is_tree (\<P>) (\<G>) \<and> \<P>\<^sub>? r = {} \<and> (\<forall>q. r \<notin> \<P>\<^sub>! q) \<or> is_tree (\<P>) (\<G>) \<and> \<G>\<langle>\<rightarrow>r\<rangle> = {}\<close>
        concat_infl_word_exists)
  then have "w_acc \<in> \<T>\<^bsub>None\<^esub>" by (simp add: concat_infl_mbox)
  have "w_acc\<down>\<^sub>q = w"  using \<open>concat_infl q w (r # \<epsilon>) w_acc\<close> concat_infl_actor_consistent by blast
  then have "(\<forall>p. (is_parent_of p q) \<longrightarrow>  w_acc\<down>\<^sub>p = \<epsilon>)"  using \<open>concat_infl q w (r # \<epsilon>) w_acc\<close> concat_infl_children_not_included by blast
  then have t1: "w_acc \<in> \<T>\<^bsub>None\<^esub> \<and> w_acc\<down>\<^sub>q = w \<and> ((is_parent_of p q) \<longrightarrow>  w_acc\<down>\<^sub>p = \<epsilon>)" using \<open>w_acc \<in> \<T>\<^bsub>None\<^esub>\<close> \<open>w_acc\<down>\<^sub>q = w\<close> by blast  
  have "\<exists> es. w_acc = es @ w" using concat by (simp add: concat_infl_w_in_w_acc)
  then show ?thesis using t1 using \<open>\<forall>p. is_parent_of p q \<longrightarrow> w_acc\<down>\<^sub>p = \<epsilon>\<close> by blast
qed

(*all peers not on the path to root starting from q are NOT part of the execution constructed with lemma 4.4*)
(*TODO: there can be an execution !a?a!b?b s.t. r sends a to p, and b to q, then the assumptions hold, but despite p not
being on the path to root from q, it's present in the execution
lemma lem4_4_extra2:
  assumes "tree_topology" and "w \<in> \<L>\<^sup>*(q)" and "q \<in> \<P>" and "w' \<in> \<T>\<^bsub>None\<^esub>" and "w'\<down>\<^sub>q = w"
and "path_to_root q ps"
shows "\<forall> x \<in> \<P>. x \<notin> (set ps) \<longrightarrow> w'\<down>\<^sub>x = \<epsilon>"
  using assms sorry
*)



(*this is the main chunk of the (<==,1.) direction of the current theorem *)
lemma mbox_trace_with_matching_recvs_is_mbox_exec:
  assumes "w \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!" and "tree_topology" and "theorem_rightside"
  shows "(add_matching_recvs w) \<in> \<T>\<^bsub>None\<^esub>"
  using assms
proof (induct "length w" arbitrary: w)
  case 0
  then show ?case by (simp add: eps_in_mbox_execs)
next
  case (Suc n)
    (*defining and setting basic facts about v, v' and !a*)
  then obtain v a where w_def: "w = v \<cdot> [a]" and v_len: "length v = n" by (metis length_Suc_conv_rev)
  then have "v \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!" using Suc.prems(1) prefix_mbox_trace_valid by blast
  then have v_IH_prems: "n = |v| \<and> v \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>! \<and> is_tree (\<P>) (\<G>) \<and> theorem_rightside"  using Suc.prems(3) assms(2) v_len by blast
  let ?v' =  "add_matching_recvs v" 
  have v_IH: "?v' \<in> \<T>\<^bsub>None\<^esub>" using v_IH_prems Suc by blast
  have "(v \<cdot> [a]) = (v \<cdot> [a])\<down>\<^sub>!" using Suc.prems(1) w_def by fastforce
  then obtain i p q where a_def: "a = (!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)"  by (metis Nil_is_append_conv append1_eq_conv decompose_send neq_Nil_conv)
  then have "\<exists> s1 s2 . (s1, !\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>, s2) \<in> \<R> q" using Suc.prems(1) assms(2) mbox_exec_to_peer_act w_def by auto
  then have "p \<in> \<P>\<^sub>!(q)" by (metis CommunicatingAutomaton.SendingToPeers.intros automaton_of_peer get_message.simps(1)
        is_output.simps(1) message.inject output_message_to_act_both_known trans_to_edge)
  then have "\<G>\<langle>\<rightarrow>p\<rangle> = {q}" by (simp add: assms(2) local_parent_to_global)  
  then have pq: "is_parent_of p q" using assms by (simp add: node_parent)
  have "(?v')\<down>\<^sub>q \<in> \<L>\<^sup>* q" using mbox_exec_to_infl_peer_word v_IH by auto
  have w_sends_0: "w = ((?v') \<cdot> [a])\<down>\<^sub>!" by (metis \<open>v \<cdot> a # \<epsilon> = (v \<cdot> a # \<epsilon>)\<down>\<^sub>!\<close> adding_recvs_keeps_send_order filter_append w_def)
  then have w_sends_1: "w = (?v')\<down>\<^sub>! \<cdot> [a]" using \<open>v \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!\<close> adding_recvs_keeps_send_order w_def by fastforce
  have a_facts: "is_output a \<and> get_actor a = q \<and> get_object a = p \<and> p \<noteq> q" using a_def is_output.simps(1) by (simp add: \<open>is_parent_of p q\<close> parent_child_diff)
  then have "[a]\<down>\<^sub>q = [a]" by simp
  have "[a]\<down>\<^sub>? = \<epsilon>" using a_def a_facts by simp
  have v'_q_recvs_inv_to_a: "(?v'\<down>\<^sub>q)\<down>\<^sub>? = ((?v' \<cdot> [a])\<down>\<^sub>q)\<down>\<^sub>?" using \<open>(a # \<epsilon>)\<down>\<^sub>? = \<epsilon>\<close> by auto
  (*p q theorem conditions:*)
  have "p \<in> \<P> \<and> q \<in> \<P>" by simp 
  then have "(is_parent_of p q) \<longrightarrow> ((subset_condition p q) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p))))" using assms(3) theorem_rightside_def by blast
  then have theorem_right_pq:  "((subset_condition p q) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p))))"  using pq by auto
  (*then show that q can send !a after performing actions in v'. producing the execution v' !a*)
  then have a_send_ok: "(?v' \<cdot> [a]) \<in> \<T>\<^bsub>None\<^esub>" using a_def Suc assms
  proof (cases "is_root q")
    case True
    then have "(v\<down>\<^sub>q \<cdot> [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]) \<in> (\<L>\<^sup>*(q))" using mbox_trace_to_root_word[of v i q p] using Suc.prems(1) a_def w_def by fastforce
        (*then the words of q in v' a and v a are equal*)
    have "?v'\<down>\<^sub>q = (?v'\<down>\<^sub>q)\<down>\<^sub>!" using root_infl_word_no_recvs[of q "?v'\<down>\<^sub>q" ] using True \<open>add_matching_recvs v\<down>\<^sub>q \<in> \<L>\<^sup>* q\<close> by presburger
    then have "?v'\<down>\<^sub>q \<cdot> [a] \<in> \<L>\<^sup>* q" by (metis (no_types, lifting) \<open>v\<down>\<^sub>q \<cdot> !\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<in> \<L>\<^sup>* q\<close> \<open>w = add_matching_recvs v\<down>\<^sub>! \<cdot> a # \<epsilon>\<close> a_def
          append1_eq_conv filter_pair_commutative w_def)
    show ?thesis using mbox_exec_app_send[of q "?v'" a] using \<open>add_matching_recvs v\<down>\<^sub>q \<cdot> a # \<epsilon> \<in> \<L>\<^sup>* q\<close> a_facts v_IH by linarith
  next
    case False (*q is node *)
    (*obtain separate execution for trace w and wq of that execution *)
    obtain e where e_def: "e \<in> \<T>\<^bsub>None\<^esub>" and e_trace: "e\<down>\<^sub>! = w" using Suc.prems(1) by blast
    then obtain wq where wq_def: "wq = e\<down>\<^sub>q" and wq_in_q: "wq \<in> \<L>\<^sup>* q" using mbox_exec_to_infl_peer_word by presburger  
    (*sends in wq and sends of q in v' with !a after, are equal:*)
    have v'a0: "((?v')\<down>\<^sub>q \<cdot> [a])\<down>\<^sub>! = ((?v')\<down>\<^sub>q)\<down>\<^sub>! \<cdot> [a]\<down>\<^sub>!" by simp
    have v'a1: "((?v')\<down>\<^sub>q)\<down>\<^sub>! \<cdot> [a]\<down>\<^sub>! = ((?v')\<down>\<^sub>q)\<down>\<^sub>! \<cdot> [a]" using a_facts by simp
    then have v'a2: "((?v')\<down>\<^sub>q)\<down>\<^sub>! \<cdot> [a] = v\<down>\<^sub>q \<cdot> [a]" by (smt (verit, ccfv_threshold)  \<open>v \<cdot> a # \<epsilon> = (v \<cdot> a # \<epsilon>)\<down>\<^sub>!\<close> adding_recvs_keeps_send_order append1_eq_conv filter_append filter_pair_commutative same_append_eq)
    have "wq\<down>\<^sub>! = w\<down>\<^sub>q" using e_trace filter_pair_commutative wq_def by blast
    have wq_v'_sends: "wq\<down>\<^sub>! = ((?v')\<down>\<^sub>! \<cdot> [a])\<down>\<^sub>q" using \<open>w = add_matching_recvs v\<down>\<^sub>! \<cdot> a # \<epsilon>\<close> \<open>wq\<down>\<^sub>! = w\<down>\<^sub>q\<close> by fastforce
    have v'a3: "((?v')\<down>\<^sub>! \<cdot> [a])\<down>\<^sub>q = ((?v')\<down>\<^sub>!)\<down>\<^sub>q \<cdot> [a]\<down>\<^sub>q" by simp
    have v'a4: "((?v')\<down>\<^sub>!)\<down>\<^sub>q \<cdot> [a]\<down>\<^sub>q = ((?v')\<down>\<^sub>q)\<down>\<^sub>! \<cdot> [a]\<down>\<^sub>q" using filter_pair_commutative by blast
    have "[a]\<down>\<^sub>q = [a]" using a_def by simp
    have wq_to_v'a_trace: "wq\<down>\<^sub>! = ((?v')\<down>\<^sub>q)\<down>\<^sub>! \<cdot> [a]" using \<open>(a # \<epsilon>)\<down>\<^sub>q = a # \<epsilon>\<close> v'a3 v'a4 wq_v'_sends by argo
    (*obtain parent r and its word wr to match wq*)
    have "is_node q" by (metis False NetworkOfCA.root_or_node NetworkOfCA_axioms assms(2))
    then obtain r where "is_parent_of q r" by (metis False UNIV_I path_to_root.cases path_to_root_exists)
    (*receives of wq are prefix of receives in v' (otherwise execs have different traces!)*)
    have v'_recvs_match: "(((?v'\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>? = (((add_matching_recvs ((?v'\<down>\<^sub>!))\<down>\<^sub>?)\<down>\<^sub>q)\<down>\<^sub>!\<^sub>?)" using matching_recvs_word_matches_sends_explicit[of "?v'" q r] using \<open>is_parent_of q r\<close> v_IH by simp
    then have "(((?v'\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>? = (((?v'\<down>\<^sub>?)\<down>\<^sub>q)\<down>\<^sub>!\<^sub>?)" using \<open>w = add_matching_recvs v\<down>\<^sub>! \<cdot> a # \<epsilon>\<close> w_def by fastforce
    then have wr_0: "(((?v'\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>? = (((?v'\<down>\<^sub>q)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)" by (metis filter_pair_commutative)
    then have e_pref:"prefix (((e\<down>\<^sub>q)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) ((((e\<down>\<^sub>r)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" using peer_recvs_in_exec_is_prefix_of_parent_sends[of e q r] using \<open>is_parent_of q r\<close> e_def by linarith
    then have wq_e_pref: "prefix (((wq)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) ((((e\<down>\<^sub>r)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" using wq_def by fastforce
    have e_trace2: "(e\<down>\<^sub>!) = ((?v' \<cdot> [a])\<down>\<^sub>!)" using \<open>w = (add_matching_recvs v \<cdot> a # \<epsilon>)\<down>\<^sub>!\<close> e_trace by blast
    then have "prefix (((wq)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) (((((?v' \<cdot> [a])\<down>\<^sub>r)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)"  by (metis (no_types, lifting) e_pref filter_pair_commutative
          wq_def)
    have "((((?v' \<cdot> [a])\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = ((((?v')\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) \<cdot> (((([a])\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" by simp
    have "(((([a])\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = ((([a])\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" using a_facts by simp
    have "r \<noteq> q" using \<open>is_parent_of q r\<close> parent_child_diff by blast
    have "p \<noteq> q" by (simp add: a_facts)
    have "r \<noteq> p" proof (rule ccontr) (*otherwise cycle in tree*)
      assume "\<not> r \<noteq> p"
      then have "r = p" by simp
      then have "is_parent_of q p" using \<open>is_parent_of q r\<close> by auto
      then have g1: "\<G>\<langle>\<rightarrow>q\<rangle> = {p}" using is_parent_of_rev by simp
      then have e1: "(p, q) \<in> \<G>" by auto
      have g2: "\<G>\<langle>\<rightarrow>p\<rangle> = {q}" using pq is_parent_of_rev by simp
      then have e2: "(q, p) \<in> \<G>" by auto
      show "False" using tree_acyclic[of "\<P>" "\<G>" p q] using assms(2) e1 e2 by auto
    qed 
    have "[a]\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>} = \<epsilon>" using a_facts using \<open>r \<noteq> p\<close> by auto
    then have "((([a])\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = (\<epsilon>)\<down>\<^sub>!\<^sub>? " using a_facts by simp
    then have "((((?v' \<cdot> [a])\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = ((((?v')\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" by simp
    have "((((?v' \<cdot> [a])\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = (((e\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" using \<open>e\<down>\<^sub>! = (add_matching_recvs v \<cdot> a # \<epsilon>)\<down>\<^sub>!\<close> by presburger
    then have "(((e\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = ((((?v')\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)"  using \<open>(add_matching_recvs v \<cdot> a # \<epsilon>)\<down>\<^sub>!\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>}\<down>\<^sub>!\<^sub>? = add_matching_recvs v\<down>\<^sub>!\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>}\<down>\<^sub>!\<^sub>?\<close>
      by argo
    have v'_match: "(((((?v')\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = ((((?v')\<down>\<^sub>?)\<down>\<^sub>q)\<down>\<^sub>!\<^sub>?)" using \<open>w = add_matching_recvs v\<down>\<^sub>! \<cdot> a # \<epsilon>\<close> v'_recvs_match w_def by force
    then have e_v'_match:"((((e\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = ((((?v')\<down>\<^sub>?)\<down>\<^sub>q)\<down>\<^sub>!\<^sub>?)"  using \<open>(a # \<epsilon>)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>} = \<epsilon>\<close> \<open>w = add_matching_recvs v\<down>\<^sub>! \<cdot> a # \<epsilon>\<close> e_trace by force
    then have wq_recvs_pref: "prefix (((wq)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) ((((?v')\<down>\<^sub>?)\<down>\<^sub>q)\<down>\<^sub>!\<^sub>?)" by (metis filter_pair_commutative wq_e_pref)
    have v'_proj_inv: " ((((?v')\<down>\<^sub>?)\<down>\<^sub>q)\<down>\<^sub>!\<^sub>?) =  ((((?v')\<down>\<^sub>q)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)" by (metis filter_pair_commutative)
        (*wq's receives are a prefix of those in v' (of q)*)
    then have wq_recvs_prefix: "prefix (wq\<down>\<^sub>?) (((?v')\<down>\<^sub>q)\<down>\<^sub>?)"  by (metis wq_recvs_pref filter_recursion no_sign_recv_prefix_to_sign_inv)
        (*the next two steps are probably unnecessary*)
    have "(((((?v' \<cdot> [a])\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = ((((?v' \<cdot> [a])\<down>\<^sub>?)\<down>\<^sub>q)\<down>\<^sub>!\<^sub>?)" by (metis (no_types, lifting) e_trace2 e_v'_match filter_pair_commutative v'_q_recvs_inv_to_a)
    have "prefix (wq\<down>\<^sub>?) (((?v' \<cdot> [a])\<down>\<^sub>q)\<down>\<^sub>?)" using v'_q_recvs_inv_to_a wq_recvs_prefix by presburger(*recvs in wq must have same order as in v', otherwise diff trace!*)
    have wq_pref_of_rq_sends: "prefix (((wq)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) (((((?v')\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)"  using v'_match wq_recvs_pref by argo
    then have "prefix (((wq)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) ((((?v'\<down>\<^sub>r)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" by (metis filter_pair_commutative)
    have v'_match_alt: "(((((?v')\<down>\<^sub>r)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = ((((?v')\<down>\<^sub>q)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)" by (metis (no_types, lifting) filter_pair_commutative v'_match)
    then have "\<exists>wr'. prefix wr' ((?v')\<down>\<^sub>r) \<and> (((wr'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = (((wq)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) \<and> wr' \<in> \<L>\<^sup>* r"
      using match_exec_and_child_prefix_to_parent_match[of r q "?v'" wq]  \<open>is_parent_of q r\<close> v_IH wq_recvs_prefix by blast
    then obtain wr' x' where v'r_def: "((?v')\<down>\<^sub>r) = wr' \<cdot> x'" and wr'_match: "(((wr'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = (((wq)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)" and "wr' \<in> \<L>\<^sup>* r" by (meson prefixE)
    have "((?v')\<down>\<^sub>r) \<in> \<L>\<^sup>* r" using mbox_exec_to_infl_peer_word[of "?v'" r]  using v_IH by blast
    then have "wr' \<cdot> x' \<in> \<L>\<^sup>* r" by (simp add: v'r_def)

    have "q \<in> \<P> \<and> r \<in> \<P>" by simp 
    then have "(is_parent_of q r) \<longrightarrow> ((subset_condition q r) \<and> ((\<L>\<^sup>*(q)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(q))))" using assms(3) theorem_rightside_def by blast
    then have theorem_right_qr:  "((subset_condition q r) \<and> ((\<L>\<^sup>*(q)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(q))))" by (simp add: \<open>is_parent_of q r\<close>)

    have "\<exists>x. (wq \<cdot> x) \<in> \<L>\<^sup>* q \<and> (((wq \<cdot> x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((((wr' \<cdot> x')\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" using subset_cond_from_child_prefix_and_parent[
          of q r wq wr' x'] using \<open>wr' \<cdot> x' \<in> \<L>\<^sup>* r\<close> theorem_right_qr wq_in_q wr'_match by fastforce
    then obtain x where wqx_def: "(wq \<cdot> x) \<in> \<L>\<^sup>* q" and wqx_match: "(((wq \<cdot> x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((((wr' \<cdot> x')\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" by auto
    then have wqx_match_v': "(((wq \<cdot> x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((((?v' \<cdot> [a])\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" using e_trace2 e_v'_match v'_match_alt v'_proj_inv v'r_def by argo
    (*shuffle x s.t. only the missing receives are added to wq (no extra sends*)
    then obtain xs ys where x_shuf: "(xs \<cdot> ys) \<squnion>\<squnion>\<^sub>? x" and "xs\<down>\<^sub>? = xs" and "ys\<down>\<^sub>! = ys" using full_shuffle_of by blast (*fully shuffle x*)
    then have xsys_recvs: "(((wq \<cdot> (xs \<cdot> ys))\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((((?v' \<cdot> [a])\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)"  by (metis (mono_tags, lifting) filter_append shuffled_keeps_recv_order wqx_match_v') (*xs ys have the same receives as the x we obtained*) 
    have "(wq \<cdot> xs \<cdot> ys) \<squnion>\<squnion>\<^sub>? (wq \<cdot> x)" using x_shuf shuffle_prepend by auto (*shuffle prepend lemma*)
    then have "wq \<cdot> xs \<cdot> ys \<in> \<L>\<^sup>* q" by (metis UNIV_def \<open>is_parent_of q r\<close> \<open>wq \<cdot> x \<in> \<L>\<^sup>* q\<close> assms(3) input_shuffle_implies_shuffled_lang
          mem_Collect_eq theorem_rightside_def)
    then have wqxs_L: "wq \<cdot> xs \<in> \<L>\<^sup>* q" using local.infl_word_impl_prefix_valid by simp
    have "(wq \<cdot> xs)\<down>\<^sub>! = wq\<down>\<^sub>!" by (simp add: \<open>xs\<down>\<^sub>? = xs\<close> input_proj_output_yields_eps)
    have wqx_match_v'a: "((((?v' \<cdot> [a])\<down>\<^sub>q)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((wq \<cdot> x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)"  using e_trace2 e_v'_match v'_proj_inv v'_q_recvs_inv_to_a wqx_match_v' by presburger
    have "xs\<down>\<^sub>? = (xs \<cdot> ys)\<down>\<^sub>?" by (simp add: \<open>ys\<down>\<^sub>! = ys\<close> output_proj_input_yields_eps)
    have "(xs \<cdot> ys)\<down>\<^sub>? = (x)\<down>\<^sub>?" using x_shuf by (metis shuffled_keeps_recv_order) (*shuffling keeps receive order*)
    then have "xs\<down>\<^sub>? = (x)\<down>\<^sub>?"  using \<open>xs\<down>\<^sub>? = (xs \<cdot> ys)\<down>\<^sub>?\<close> by presburger
    have "(((wq \<cdot> x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((wq \<cdot> xs)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)"  by (simp add: \<open>xs\<down>\<^sub>? = x\<down>\<^sub>?\<close>)
    then have xs_recvs: "(((wq \<cdot> xs)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((((?v' \<cdot> [a])\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" using wqx_match_v' wqx_match_v'a by argo
    have v'_eq: "(((((?v' \<cdot> [a])\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = (((?v' \<cdot> [a])\<down>\<^sub>q)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?" using e_trace2 e_v'_match v'_proj_inv v'_q_recvs_inv_to_a by presburger
    then have "(((wq \<cdot> xs)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((?v' \<cdot> [a])\<down>\<^sub>q)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?" using xs_recvs by presburger
    then have "(wq \<cdot> xs)\<down>\<^sub>? = (((?v' \<cdot> [a])\<down>\<^sub>q)\<down>\<^sub>?)"  using no_sign_recv_prefix_to_sign_inv[of "(wq \<cdot> xs)\<down>\<^sub>?" "(((?v' \<cdot> [a])\<down>\<^sub>q)\<down>\<^sub>?)"] by (metis filter_recursion no_sign_recv_prefix_to_sign_inv prefix_order.dual_order.antisym
          prefix_order.dual_order.refl) (*since wq's receives are already prefix and we only added receives, i.e. removing or adding signs changes nothing*)
    then have wqxs_order:"(wq \<cdot> xs)\<down>\<^sub>? = (((?v' \<cdot> [a])\<down>\<^sub>q)\<down>\<^sub>?) \<and> (wq \<cdot> xs)\<down>\<^sub>! = ((?v' \<cdot> [a])\<down>\<^sub>q)\<down>\<^sub>!" using \<open>(a # \<epsilon>)\<down>\<^sub>q = a # \<epsilon>\<close> \<open>(wq \<cdot> xs)\<down>\<^sub>! = wq\<down>\<^sub>!\<close> w_sends_0 w_sends_1 wq_to_v'a_trace by force (*same sends & recvs in isolation, respectively*)
    have wqxs_trace_match: "(((wq \<cdot> xs)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((((v \<cdot> [a])\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)"  using \<open>v \<cdot> a # \<epsilon> = (v \<cdot> a # \<epsilon>)\<down>\<^sub>!\<close> e_trace e_trace2 w_def xs_recvs by presburger
    let ?wq = "wq \<cdot> xs"
    show ?thesis using wqxs_order 
    proof (cases "(?v'\<down>\<^sub>q \<cdot> [a]) \<squnion>\<squnion>\<^sub>? (?wq)")
      case True
      then have "(?v'\<down>\<^sub>q \<cdot> [a]) \<in> (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(q))" using input_shuffle_implies_shuffled_lang wqxs_L by blast
      then have "(?v'\<down>\<^sub>q \<cdot> [a]) \<in> (\<L>\<^sup>*(q))" using theorem_right_qr by simp
      then show ?thesis using mbox_exec_app_send[of q "?v'" a] using a_facts v_IH by blast
    next
      case False
      then have "(?v'\<down>\<^sub>q \<cdot> [a]) \<noteq> (?wq)" by (metis shuffled.refl)
(*either wq is shuffle of (v'q a), or wq and (v'q a) can't be shuffled into each other
it remains to be shown that this can't occur*)
      then have "\<not> ((?v'\<down>\<^sub>q \<cdot> [a]) \<squnion>\<squnion>\<^sub>? (?wq))" using False by blast
      then have "\<not> ((?v'\<down>\<^sub>q \<cdot> [a]) \<squnion>\<squnion>\<^sub>? (?wq)) \<and> (wq \<cdot> xs)\<down>\<^sub>? = (((?v' \<cdot> [a])\<down>\<^sub>q)\<down>\<^sub>?) \<and> (wq \<cdot> xs)\<down>\<^sub>! = ((?v' \<cdot> [a])\<down>\<^sub>q)\<down>\<^sub>!" 
        using wqxs_order by blast
(*then wq must have some ?y < !x but in v'q !a it's !x < ?y*)
      then have "\<exists> xs' a' ys' b' zs' xs'' ys'' zs''. is_input a' \<and> is_output b' \<and> (?wq) = (xs' @ [a'] @ ys' @ [b'] @ zs') \<and>
(?v'\<down>\<^sub>q \<cdot> [a]) = (xs'' @ [b'] @ ys'' @ [a'] @ zs'')"  using no_shuffle_implies_output_input_exists[of 
"?wq" "(?v'\<down>\<^sub>q \<cdot> [a])"]  by (metis \<open>(a # \<epsilon>)\<down>\<^sub>q = a # \<epsilon>\<close> filter_append)
(*by construction of v', !x < !y must be in the trace*)
(*but there is no execution with wq that can produce this trace, since ?y < !x and thus the trace must be
!y < !x*)
      (*we can infer the trace by construction of v', but since some ?y is received earlier in wq
than in v', it must also be sent earlier in e, contradicting that they have the same trace.*)
      have diff_trace_prems: "?wq\<down>\<^sub>? = (?v'\<down>\<^sub>q \<cdot> [a])\<down>\<^sub>? \<and> ?wq\<down>\<^sub>! = (?v'\<down>\<^sub>q \<cdot> [a])\<down>\<^sub>! \<and> 
\<not>((?v'\<down>\<^sub>q \<cdot> [a]) \<squnion>\<squnion>\<^sub>? ?wq) \<and> ?wq \<noteq> (?v'\<down>\<^sub>q \<cdot> [a])
\<and> e \<in> \<T>\<^bsub>None\<^esub> \<and> ?v' \<in> \<T>\<^bsub>None\<^esub> \<and> (v \<cdot> [a]) \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>! \<and> ?v' = (add_matching_recvs v) \<and> ?v'\<down>\<^sub>q \<in> \<L>\<^sup>* q
\<and> ?wq \<in> \<L>\<^sup>* q" 
        by (metis (no_types, lifting) False Suc.prems(1) \<open>(a # \<epsilon>)\<down>\<^sub>q = a # \<epsilon>\<close> \<open>(wq \<cdot> xs)\<down>\<^sub>! = wq\<down>\<^sub>!\<close>
            \<open>((wq \<cdot> xs)\<down>\<^sub>?) = ((add_matching_recvs v \<cdot> a # \<epsilon>)\<down>\<^sub>q)\<down>\<^sub>?\<close> \<open>add_matching_recvs v\<down>\<^sub>q \<cdot> a # \<epsilon> \<noteq> wq \<cdot> xs\<close>
            \<open>add_matching_recvs v\<down>\<^sub>q \<in> \<L>\<^sup>* q\<close> e_def filter_append v'a1 v_IH w_def wq_to_v'a_trace wqxs_L)

      have "(e \<cdot> xs) \<in> \<T>\<^bsub>None\<^esub>" using exec_append_missing_recvs[of wq xs r q v a e]  using diff_trace_prems wq_def wqxs_trace_match 
         e_trace w_def by blast
      have "(e \<cdot> xs)\<down>\<^sub>q = e\<down>\<^sub>q \<cdot> xs\<down>\<^sub>q" by simp
      have "xs\<down>\<^sub>q = xs" using infl_word_actor_app  by (meson wqxs_L) (*since wq xs is in L*(Aq), xs must consist of q's actions only*)
      then have "(e \<cdot> xs)\<down>\<^sub>q = ?wq" using \<open>(e \<cdot> xs)\<down>\<^sub>q = e\<down>\<^sub>q \<cdot> xs\<down>\<^sub>q\<close> wq_def by presburger
      have "(e \<cdot> xs)\<down>\<^sub>! = e\<down>\<^sub>!" by (simp add: \<open>xs\<down>\<^sub>? = xs\<close> input_proj_output_yields_eps)
have diff_trace_prems2: "?wq\<down>\<^sub>? = (?v'\<down>\<^sub>q \<cdot> [a])\<down>\<^sub>? \<and> ?wq\<down>\<^sub>! = (?v'\<down>\<^sub>q \<cdot> [a])\<down>\<^sub>! \<and> 
\<not>((?v'\<down>\<^sub>q \<cdot> [a]) \<squnion>\<squnion>\<^sub>? ?wq) \<and> ?wq \<noteq> (?v'\<down>\<^sub>q \<cdot> [a])
\<and> (e \<cdot> xs) \<in> \<T>\<^bsub>None\<^esub> \<and> (e \<cdot> xs)\<down>\<^sub>q = ?wq \<and> ?v' \<in> \<T>\<^bsub>None\<^esub> \<and> (v \<cdot> [a]) \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>! \<and> ?v' = (add_matching_recvs v) \<and> ?v'\<down>\<^sub>q \<in> \<L>\<^sup>* q
\<and> ?wq \<in> \<L>\<^sup>* q"  using \<open>(e \<cdot> xs)\<down>\<^sub>q = wq \<cdot> xs\<close> \<open>e \<cdot> xs \<in> \<T>\<^bsub>None\<^esub>\<close> diff_trace_prems by blast
  then have "(e \<cdot> xs)\<down>\<^sub>! \<noteq> (?v' \<cdot> [a])\<down>\<^sub>!" using diff_peer_word_impl_diff_trace
[of "?wq" q "?v'" a "(e \<cdot> xs)" v] by simp
      then show ?thesis using \<open>(e \<cdot> xs)\<down>\<^sub>! = e\<down>\<^sub>!\<close> e_trace2 by argo
    qed
  qed

(*since q can send all its outputs in v and then a, its child p must be able to receive a after its current word in v'*)
  then have "((add_matching_recvs v)\<down>\<^sub>q @ [a]\<down>\<^sub>q ) \<in> \<L>\<^sup>* q"  using mbox_exec_to_infl_peer_word by fastforce
  then have q_full: "((add_matching_recvs v)\<down>\<^sub>q @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]) \<in> \<L>\<^sup>* q" using a_def by simp
  have v'p_in_L: "(add_matching_recvs v)\<down>\<^sub>p \<in> \<L>\<^sup>* p" using mbox_exec_to_infl_peer_word v_IH by blast
  (*all of q's sends to p must be received by p in v'*)
  have v'_recvs_match_pq: "(((?v'\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? = (((add_matching_recvs ((?v'\<down>\<^sub>!))\<down>\<^sub>?)\<down>\<^sub>p)\<down>\<^sub>!\<^sub>?)" 
    using matching_recvs_word_matches_sends_explicit[of "?v'" p q] using \<open>is_parent_of p q\<close> v_IH by simp
  then have v'_recvs_match_pq2: "(((?v'\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? = (((?v'\<down>\<^sub>?)\<down>\<^sub>p)\<down>\<^sub>!\<^sub>?)" using \<open>w = add_matching_recvs v\<down>\<^sub>! \<cdot> a # \<epsilon>\<close> w_def by fastforce
  let ?wp = "(?v'\<down>\<^sub>p)"
  let ?wq_full = "((add_matching_recvs v)\<down>\<^sub>q @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>])"
(*p has not received a in v' yet, but q can send it, so by the subset cond. p must be able to receive it still*)
  have "(?wp \<cdot> [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]) \<in> \<L>\<^sup>* p \<and> (((?wp \<cdot> [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>])\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((((?wq_full)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>?)"
    using subset_cond_from_child_prefix_and_parent_act[of p q "?wp" "(?v'\<down>\<^sub>q)" i] by (smt (verit, ccfv_SIG) filter_pair_commutative pq q_full theorem_right_pq v'_recvs_match_pq2
        v'p_in_L)
  then have "(((?v')\<down>\<^sub>p \<cdot> [(?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)])) \<in> \<L>\<^sup>* p" by simp
      (*then p can receive ?a after its word in v', and left to show is that the trace is valid
  \<rightarrow> probably instantiate the mbox run and step again*)
  then have a_ok0: "(?v' \<cdot> ([!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] \<cdot> [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>])) \<in> \<T>\<^bsub>None\<^esub>" 
    using mbox_exec_recv_append[of "?v'" i q p] using a_def a_send_ok by (metis (no_types, lifting) append1_eq_conv append_assoc filter_pair_commutative pq v'_recvs_match_pq w_def
        w_sends_1)
  have a_match: "(add_matching_recvs [a]) = ([!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] \<cdot> [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>])"  using a_def by force
  then have a_ok: "((add_matching_recvs v) \<cdot> (add_matching_recvs [a])) \<in> \<T>\<^bsub>None\<^esub>" using a_ok0 by auto
      (*since the trace is valid, a can be sent after the sends in v. Obtain p and q of a, and then use subset condition
because if a can't be received then p can't receive a send of its parent (contradiction)*)
  then show ?case by (simp add: add_matching_recvs_app w_def) 
qed




(*theorem current version*)
(*state at a glance: all subproofs except <==2. need to be adjusted to reflect the new subset condition*)
(* Nsync = L0, ENsync = T0, EMbox = Tinf/None, TMbox = Linf, E = !?, T = only sends *)
theorem synchronisability_for_trees:
  assumes "tree_topology" 
  shows "is_synchronisable \<longleftrightarrow> ((\<forall>p \<in> \<P>. \<forall>q \<in> \<P>. ((is_parent_of p q) \<longrightarrow> ((subset_condition p q) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) )))" (is "?L \<longleftrightarrow> ?R")
  (*using assms unfolding theorem_rightside_def subset_condition_def prefix_def NetworkOfCA_def *)
proof 
  (* \<Longrightarrow>: is_synchronisable \<Longrightarrow> language conditions *)
  assume "?L"
  show "?R"
  proof clarify
    fix p q
    assume q_parent: "is_parent_of p q"
    have sync_def: "\<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>! = \<L>\<^sub>\<zero>" using \<open>?L\<close> by simp
    show "subset_condition p q \<and> \<L>\<^sup>* p = \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion> p"
    proof (rule conjI)
      (* \<Longrightarrow> 1.: prove the influenced language subset condition holds *)
      show "subset_condition p q" unfolding subset_condition_def
      proof auto
        (*fix arbitrary w and w' s.t. receives in w match the sends to p in w'
        and fix some arbitrary suffix x' s.t. w' x' is a word in L*(Aq) *)
        fix w w' x'
        assume w_Lp: "is_in_infl_lang p w"
               and w'_Lq: "is_in_infl_lang q w'"
               and w'_w_match: "filter (\<lambda>x. is_output x \<and> (get_object x = q \<and> get_actor x = p 
                   \<or> get_object x = p \<and> get_actor x = q)) w'\<down>\<^sub>!\<^sub>? = w\<down>\<^sub>?\<down>\<^sub>!\<^sub>?"
               and w'x'_Lq: "is_in_infl_lang q (w' \<cdot> x')"
        then show "\<exists>wa. filter (\<lambda>x. is_output x \<and> (get_object x = q \<and> get_actor x = p \<or> get_object x = p \<and>
                   get_actor x = q)) x'\<down>\<^sub>!\<^sub>? =  wa\<down>\<^sub>!\<^sub>? \<and>  (\<exists>x. wa = x\<down>\<^sub>? \<and> is_in_infl_lang p (w \<cdot> x))" 
          using w_Lp  w'_Lq w'_w_match w'x'_Lq
        proof (cases "is_root q")
          case True
          then have "(w' \<cdot> x') \<in> \<L> q" using w'x'_Lq w_in_infl_lang by auto
          (*then w’ x’ consists only of sends*)
          (*then w’ x’ is also a valid mbox execution*) 
          then have "(w' \<cdot> x') \<in> \<T>\<^bsub>None\<^esub>" using root_lang_is_mbox True by blast (*since q is root and thus w' x' are only sends*)
          (*then have "(w' \<cdot> x')\<down>\<^sub>! = (w' \<cdot> x')" sorry *)
          have "w'\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? = w\<down>\<^sub>?\<down>\<^sub>!\<^sub>?" using w'_w_match by force
          (*then have "(w' \<cdot> x') \<cdot> w \<in> \<T>\<^bsub>None\<^esub>" sorry (*since w' x' is valid execution and provides all sends for w*)*)
          (*then mix w’ with w and append x’ as valid mbox execution 
          (works since both w’ and x’ need nothing from any other peer, and w’ provides all necessary sends for w)*)
          let ?mix = "(mix_pair w' w [])"
          have "?mix \<cdot> x' \<in> \<T>\<^bsub>None\<^esub>" sorry
          then obtain t where "t \<in> \<L>\<^sub>\<zero> \<and> t \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>! \<and> t = (?mix \<cdot> x')\<down>\<^sub>!" using sync_def by fastforce
          then obtain xc where t_sync_run : "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> t xc" using SyncTraces.simps by auto
          (*find the sync execution (here as mbox run) where each send is directly followed by recv*)
          then have "\<exists>xcm. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (add_matching_recvs t) xcm" using empty_sync_run_to_mbox_run sync_run_to_mbox_run by blast
          (*then obtain the sync execution for the trace of the constructed execution*)
          then have sync_exec: "(add_matching_recvs t) \<in> \<T>\<^bsub>None\<^esub>" using MboxTraces.intros by auto
          (*then the sync execution has exactly w and some x as peer word of p
          , which receives w’ x’ exactly (subset condition proven!)*)
          then have "\<exists>x. (add_matching_recvs t)\<down>\<^sub>p = w \<cdot> x" sorry
          then obtain x where x_def: "(add_matching_recvs t)\<down>\<^sub>p = w \<cdot> x" by blast
          then have w'x'_wx_match: "(w' \<cdot> x')\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? = (w \<cdot> x)\<down>\<^sub>?\<down>\<^sub>!\<^sub>?" sorry
          have "(w \<cdot> x) \<in> \<L>\<^sup>* p" using sync_exec x_def by (metis mbox_exec_to_infl_peer_word)
          have "\<exists>wa. x'\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? =  wa\<down>\<^sub>!\<^sub>? \<and>  (\<exists>x. wa = x\<down>\<^sub>? \<and> is_in_infl_lang p (w \<cdot> x))"  using \<open>w \<cdot> x \<in> \<L>\<^sup>* p\<close> \<open>w'\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? = w\<down>\<^sub>?\<down>\<^sub>!\<^sub>?\<close> w'x'_wx_match by auto
          then show ?thesis by simp
        next
          case False (*q is node with parent r*)
          then have "is_node q" by (metis NetworkOfCA.root_or_node NetworkOfCA_axioms assms)
          then obtain r where qr: "is_parent_of q r" by (metis False UNIV_I path_from_root.simps path_to_root_exists paths_eq)
          (*obtain w’’ s.t. w’’ provides matching sends for w’x’ (must exist since w’x’ in infl lang)*)
          have "(w' \<cdot> x') \<in> \<L>\<^sup>* q" by (simp add: w'x'_Lq)
          then have "\<exists>w''.  w'' \<in> \<L>\<^sup>*(r) \<and> (((w' \<cdot> x')\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w''\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" 
            using infl_parent_child_matching_ws[of "(w' \<cdot> x')" q r] using qr by blast
          then obtain w'' where w''_w'_match: "w''\<down>\<^sub>!\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>}\<down>\<^sub>!\<^sub>? = (w' \<cdot> x')\<down>\<^sub>?\<down>\<^sub>!\<^sub>?" and w''_def: "w'' \<in> \<L>\<^sup>* r" by (metis (no_types, lifting) filter_pair_commutative)
          (*then use lemma 4.4 to obtain execution e for w’’ (by construction, 
          p and q perform no actions here and q gets sent the necessary sends to perform w’, 
          while p gets sent nothing, p and q send and receive nothing in w’’)*)
          have "\<exists> e. (e \<in> \<T>\<^bsub>None\<^esub> \<and> e\<down>\<^sub>r = w'' \<and> ((is_parent_of q r) \<longrightarrow>  e\<down>\<^sub>q = \<epsilon>))"  using lemma4_4[of
              w'' r q] using \<open>w'' \<in> \<L>\<^sup>* r\<close> assms by blast 
          then obtain e where e_def: "e \<in> \<T>\<^bsub>None\<^esub>" and e_proj_r: "e\<down>\<^sub>r = w''" 
            and e_proj_q: "e\<down>\<^sub>q = \<epsilon>" using qr by blast
          (*e provides all sends for w'x' and w' provides all sends for w
          \<rightarrow> mix w' and w s.t. each send of w' to p is directly followed by the matching send in w*)
          let ?mix = "(mix_pair w' w [])"
          (*then append w_mix to e and append x’ to that. This is an execution, since x’ also gets all 
          necessary sends from e, w_mix doesn’t send anything to q and thus q is still in the position 
          to perform x’ (whether w is performed inbetween e and x’ or not doesn’t hinder q)*)
          have "e \<cdot> ?mix \<cdot> x' \<in> \<T>\<^bsub>None\<^esub>" sorry
          (*since the network is synchronisable, obtain the sync execution e’ with the same trace as e.
           By construction of e, e’ and e projected to only actions between p and q, before x’
          (i.e. sends from q to p and receives of these sends) are equal. Since mix peforms each 
          send of q directly before the receive of p (i.e. simulating the sync execution between these
         two peers), e’ must have the same w in its execution, otherwise a different trace is performed.*)
          then obtain t where "t \<in> \<L>\<^sub>\<zero> \<and> t \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>! \<and> t = (e \<cdot> ?mix \<cdot> x')\<down>\<^sub>!" using sync_def by fastforce
          then obtain xc where t_sync_run : "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> t xc" using SyncTraces.simps by auto
          (*find the sync execution (here as mbox run) where each send is directly followed by recv*)
          then have "\<exists>xcm. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (add_matching_recvs t) xcm" using empty_sync_run_to_mbox_run sync_run_to_mbox_run by blast
          (*then obtain the sync execution for the trace of the constructed execution*)
          then have sync_exec: "(add_matching_recvs t) \<in> \<T>\<^bsub>None\<^esub>" using MboxTraces.intros by auto
          (*then the sync execution has exactly w and some x as peer word of p
          , which receives w’ x’ exactly (subset condition proven!)*)
          then have "\<exists>x. (add_matching_recvs t)\<down>\<^sub>p = w \<cdot> x" sorry
          then obtain x where x_def: "(add_matching_recvs t)\<down>\<^sub>p = w \<cdot> x" by blast
          then have w'x'_wx_match: "(w' \<cdot> x')\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? = (w \<cdot> x)\<down>\<^sub>?\<down>\<^sub>!\<^sub>?" sorry
          (*since e’ is an execution, and by construction, the word of p in this execution is exactly 
          w x, and by being in an execution, this w x must also be part of the influenced language of p
          \<Rightarrow> we have found a matching x for our arbitrary x’ and thus shown the subset condition.*)
          have "(w \<cdot> x) \<in> \<L>\<^sup>* p" using sync_exec x_def by (metis mbox_exec_to_infl_peer_word)
          have "w'\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? = w\<down>\<^sub>?\<down>\<^sub>!\<^sub>?" using w'_w_match by force
          have "\<exists>wa. x'\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? =  wa\<down>\<^sub>!\<^sub>? \<and>  (\<exists>x. wa = x\<down>\<^sub>? \<and> is_in_infl_lang p (w \<cdot> x))"  using \<open>w \<cdot> x \<in> \<L>\<^sup>* p\<close> \<open>w'\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? = w\<down>\<^sub>?\<down>\<^sub>!\<^sub>?\<close> w'x'_wx_match by auto
          then show ?thesis by simp
        qed
      qed
        (* \<Longrightarrow> 2.: prove influenced language is also shuffled language *)
      show "\<L>\<^sup>*(p) = \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)" 
      proof
        (* First inclusion is by definition *)
        show "\<L>\<^sup>*(p) \<subseteq> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)" using language_shuffle_subset by auto
            (* Second inclusion via proof*)
        show "\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p) \<subseteq> \<L>\<^sup>*(p)" 
        proof
          fix v'
            (*take arbitrary shuffled word v' and show that is in the influenced lang, using (one of its) origin(s) v*)
          assume "v' \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)"
          then obtain v where v_orig: "v' \<squnion>\<squnion>\<^sub>? v" and orig_in_L: "v \<in> \<L>\<^sup>*(p)" using shuffled_infl_lang_impl_valid_shuffle by auto
          then show "v' \<in> \<L>\<^sup>*(p)" 
          proof (induct v v')
            case (refl w) (*v = v'*)
            then show ?case by simp
          next
            case (swap b a w xs ys) (*exactly one swap occurred*)
            (*obtain vq, matching word of q to v (which provides the exact sends to p needed for v)*)
            then have "\<exists>vq.  vq \<in> \<L>\<^sup>*(q) \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((vq\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" 
              using infl_parent_child_matching_ws[of w p q] orig_in_L q_parent by blast
            then obtain vq where vq_v_match: "((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((vq\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" and vq_def: "vq \<in> \<L>\<^sup>* q" by auto 
            have lem4_4_prems: "tree_topology \<and> w \<in> \<L>\<^sup>*(p) \<and> p \<in> \<P>" using assms swap.prems by auto
            then show ?case using assms swap vq_v_match vq_def lem4_4_prems
            proof (cases "is_root q")
              case True
              have "vq \<in> \<L> q" using vq_def w_in_infl_lang by auto
              then have "vq \<in> \<T>\<^bsub>None\<^esub>" using root_lang_is_mbox True by simp (*since q is root and thus vq are only sends*)
              (*then mix vq with v (while considering v') as valid mbox execution (works since vq needs
             nothing from any other peer, and vq provides all necessary sends for v)*)
              let ?w' = "xs \<cdot> a # b # ys"
              have "\<exists> acc. mix_shuf vq v v' acc" sorry
              then obtain mix where "mix_shuf vq v v' mix" by blast
              let ?mix = "mix"
              have "?mix \<in> \<T>\<^bsub>None\<^esub>" sorry
              then obtain t where "t \<in> \<L>\<^sub>\<zero> \<and> t \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>! \<and> t = (?mix)\<down>\<^sub>!" using sync_def by fastforce
              then obtain xc where t_sync_run : "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> t xc" using SyncTraces.simps by auto
              (*find the sync execution (here as mbox run) where each send is directly followed by recv
              \<rightarrow> by constr. of the mix, this means each send is exactly in front of where a receive would
              be in v' (in v there may not be) \<rightarrow> the sync execution yields v' when projected on p*)
              then have "\<exists>xcm. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (add_matching_recvs t) xcm" using empty_sync_run_to_mbox_run sync_run_to_mbox_run by blast
              (*then obtain the sync execution for the trace of the constructed execution*)
              then have sync_exec: "(add_matching_recvs t) \<in> \<T>\<^bsub>None\<^esub>" using MboxTraces.intros by auto
              (*then the sync execution has exactly v' as peer word of p, which then must be in the 
              infl. language of p since it is in an execution (shuffled lang. condition proven!)*)
              then have "(add_matching_recvs t)\<down>\<^sub>p = ?w'" sorry
              then have "?w' \<in> \<L>\<^sup>* p" using sync_exec mbox_exec_to_infl_peer_word by metis
              then show ?thesis by simp
            next
              case False (*q is node with parent r*)
              then have "is_node q" by (metis NetworkOfCA.root_or_node NetworkOfCA_axioms assms)
              then obtain r where qr: "is_parent_of q r" by (metis False UNIV_I path_from_root.simps path_to_root_exists paths_eq)
              then have "\<exists>vr.  vr \<in> \<L>\<^sup>*(r) \<and> ((vq\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((vr\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"
                using infl_parent_child_matching_ws[of vq q r] orig_in_L vq_def by blast
              (*now we have vr which matches vq which matches w*)
              then obtain vr where vr_def: "vr \<in> \<L>\<^sup>*(r)" and vr_vq_match: "((vq\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((vr\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" by blast
          (*then use lemma 4.4 to obtain execution e for vr (by construction,
          p and q perform no actions here and q gets sent the necessary sends to perform vq, 
          while p gets sent nothing, p and q send and receive nothing in vr)*)
          have "\<exists> e. (e \<in> \<T>\<^bsub>None\<^esub> \<and> e\<down>\<^sub>r = vr \<and> ((is_parent_of q r) \<longrightarrow>  e\<down>\<^sub>q = \<epsilon>))"  using lemma4_4[of
              vr r q] using \<open>vr \<in> \<L>\<^sup>* r\<close> assms by blast 
          then obtain e where e_def: "e \<in> \<T>\<^bsub>None\<^esub>" and e_proj_r: "e\<down>\<^sub>r = vr" 
            and e_proj_q: "e\<down>\<^sub>q = \<epsilon>" using qr by blast
          (*e provides all sends for w'x' and w' provides all sends for w
          \<rightarrow> mix w' and w s.t. each send of w' to p is directly followed by the matching send in w*)
          let ?w' = "xs \<cdot> a # b # ys"
          have "\<exists> acc. mix_shuf vq v v' acc" sorry
          then obtain mix where "mix_shuf vq v v' mix" by blast
          let ?mix = "mix"
          (*then append w_mix to e. This is an execution, since vq gets all 
          necessary sends from e and in turn vq provides all necessary sends to w*)
          have "e \<cdot> ?mix \<in> \<T>\<^bsub>None\<^esub>" sorry
          (*since the network is synchronisable, obtain the sync execution e’ with the same trace as e.
           By construction of e, e’ and e projected to only actions between p and q, before x’
          (i.e. sends from q to p and receives of these sends) are equal. Since mix peforms each 
          send of q directly before the receive of p except for the swapped pair (i.e. simulating the sync execution between these
         two peers), e’ has w' as result of the projection on only p*)
          then obtain t where "t \<in> \<L>\<^sub>\<zero> \<and> t \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>! \<and> t = (e \<cdot> ?mix)\<down>\<^sub>!" using sync_def by fastforce
          then obtain xc where t_sync_run : "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> t xc" using SyncTraces.simps by auto
          (*find the sync execution (here as mbox run) where each send is directly followed by recv*)
          then have "\<exists>xcm. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (add_matching_recvs t) xcm" using empty_sync_run_to_mbox_run sync_run_to_mbox_run by blast
          (*then obtain the sync execution for the trace of the constructed execution*)
          then have sync_exec: "(add_matching_recvs t) \<in> \<T>\<^bsub>None\<^esub>" using MboxTraces.intros by auto
          (*then the sync execution has exactly v' as peer word of p, which then must be in the 
              infl. language of p since it is in an execution (shuffled lang. condition proven!)*)
          then have "(add_matching_recvs t)\<down>\<^sub>p = ?w'" sorry
          then have "?w' \<in> \<L>\<^sup>* p" using sync_exec mbox_exec_to_infl_peer_word by metis
          then show ?thesis by simp
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
  show "?L" \<comment> \<open>show that TMbox = TSync, i.e. \<L> = (i.e. the sends are equal\<close>
  proof auto \<comment> \<open>cases: w in TMbox, w in TSync\<close>
    fix w 
    show "w \<in> \<T>\<^bsub>None\<^esub> \<Longrightarrow> w\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>" 
    proof -(*take arbitrary mbox trace, show that w' where w' = add_matching_recvs w is (also) an mbox execution
since in w' each send immediately is received and it is a valid execution, it's also a sync execution
and thus we have found the matching sync trace to the arbitrary mbox trace.*)
      assume "w \<in> \<T>\<^bsub>None\<^esub>" 
      then have "(w\<down>\<^sub>!) \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!" by blast
      (*the next line uses the conclusion of the large induction part of the paper proof (for clarity the induction is proven outside)*)
      then have match_exec: "add_matching_recvs (w\<down>\<^sub>!) \<in> \<T>\<^bsub>None\<^esub>"
        using mbox_trace_with_matching_recvs_is_mbox_exec \<open>\<forall>p\<in>\<P>. \<forall>q\<in>\<P>. is_parent_of p q \<longrightarrow> subset_condition p q \<and> \<L>\<^sup>* p = \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion> p\<close> assms theorem_rightside_def
        by blast
      then obtain xcm where "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (add_matching_recvs (w\<down>\<^sub>!)) xcm"  by (metis MboxTraces.cases)
      then show "(w\<down>\<^sub>!) \<in> \<L>\<^sub>\<zero>" using SyncTraces.simps \<open>w\<down>\<^sub>! \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!\<close> matched_mbox_run_to_sync_run by blast
    qed
  next \<comment> \<open>w in TSync  --> show that w' (= w with recvs added) is in EMbox\<close>
    fix w
    show "w \<in> \<L>\<^sub>\<zero> \<Longrightarrow> \<exists>w'. w = w'\<down>\<^sub>! \<and> w' \<in> \<T>\<^bsub>None\<^esub>"
    proof -
      assume "w \<in> \<L>\<^sub>\<zero>"
        \<comment> \<open>For every output in w, Nsync was able to send the respective message and directly
      receive it\<close>
      then have "w = w\<down>\<^sub>!" by (metis SyncTraces.cases run_produces_no_inputs(1))
      then obtain xc where w_sync_run : "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xc" using SyncTraces.simps \<open>w \<in> \<L>\<^sub>\<zero>\<close> by auto
      then have "w \<in> \<L>\<^sub>\<infinity>"  using \<open>w \<in> \<L>\<^sub>\<zero>\<close> mbox_sync_lang_unbounded_inclusion by blast
      obtain w' where "w' = add_matching_recvs w" by simp
          \<comment> \<open>then Nmbox can simulate the run of w in Nsync by sending every mes-
      sage first to the mailbox of the receiver and then receiving this message\<close>
      then show ?thesis 
      proof (cases "xc = []") \<comment> \<open>this case distinction isn't in the paper but i need it here to properly get the simulated run\<close>
        case True
        then have "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (w') []"  using \<open>w' = add_matching_recvs w\<close> empty_sync_run_to_mbox_run w_sync_run by auto
        then show ?thesis using \<open>w \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!\<close> by blast
      next
        case False
        then obtain xcm where sim_run:  "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None w' xcm \<and> (\<forall>p. (last xcm p ) = ((last xc) p, \<epsilon> ))"
          using \<open>w' = add_matching_recvs w\<close> sync_run_to_mbox_run w_sync_run by blast
        then have "w' \<in> \<T>\<^bsub>None\<^esub>" using MboxTraces.intros by auto
        then have "w = w'\<down>\<^sub>!" using \<open>w = w\<down>\<^sub>!\<close> \<open>w' = add_matching_recvs w\<close> adding_recvs_keeps_send_order by auto
        then have "(w'\<down>\<^sub>!) \<in> \<L>\<^sub>\<infinity>" using \<open>w' \<in> \<T>\<^bsub>None\<^esub>\<close> by blast
        then show ?thesis using \<open>w = w'\<down>\<^sub>!\<close> \<open>w' \<in> \<T>\<^bsub>None\<^esub>\<close> by blast
      qed      
    qed
  qed
qed



subsubsection ‹Topology is a Forest›

inductive is_forest :: "'peer set ⇒ 'peer topology ⇒ bool" where
  IFSingle:  "is_tree P E ⟹ is_forest P E" |
  IFAddTree: "⟦is_forest P1 E1; is_tree P2 E2; P1 ∩ P2 = {}⟧ ⟹ is_forest (P1 ∪ P2) (E1 ∪ E2)"

abbreviation forest_topology :: "bool" where
  "forest_topology ≡ is_forest (UNIV :: 'peer set) (𝒢)"




end
end

