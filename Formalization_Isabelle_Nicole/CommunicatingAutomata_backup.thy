(* Author: Kirstin Peters, Augsburg University, 2024 *)

theory CommunicatingAutomata
  imports FormalLanguages
begin

section \<open>Communicating Automata\<close>

subsection \<open>Messages and Actions\<close>

datatype ('information, 'peer) message =
  Message 'information 'peer 'peer  ("_\<^bsup>_\<rightarrow>_\<^esup>" [120, 120, 120] 100)

primrec get_information :: "('information, 'peer) message \<Rightarrow> 'information" where
  "get_information (i\<^bsup>p\<rightarrow>q\<^esup>) = i"

primrec get_sender :: "('information, 'peer) message \<Rightarrow> 'peer" where
  "get_sender (i\<^bsup>p\<rightarrow>q\<^esup>) = p"

primrec get_receiver :: "('information, 'peer) message \<Rightarrow> 'peer" where
  "get_receiver (i\<^bsup>p\<rightarrow>q\<^esup>) = q"

value "get_information (i\<^bsup>p\<rightarrow>q\<^esup>)"
value "get_sender (i\<^bsup>p\<rightarrow>q\<^esup>)"
value "get_receiver (i\<^bsup>p\<rightarrow>q\<^esup>)"

datatype ('information, 'peer) action =
  Output "('information, 'peer) message"  ("!\<langle>_\<rangle>" [120] 100) |
  Input "('information, 'peer) message"  ("?\<langle>_\<rangle>" [120] 100)

primrec is_output :: "('information, 'peer) action \<Rightarrow> bool" where
  "is_output (!\<langle>m\<rangle>) = True" |
  "is_output (?\<langle>m\<rangle>) = False"

abbreviation is_input :: "('information, 'peer) action \<Rightarrow> bool" where
  "is_input a \<equiv> \<not>(is_output a)"

primrec get_message :: "('information, 'peer) action \<Rightarrow> ('information, 'peer) message" where
  "get_message (!\<langle>m\<rangle>) = m" |
  "get_message (?\<langle>m\<rangle>) = m"

primrec get_actor :: "('information, 'peer) action \<Rightarrow> 'peer" where
  "get_actor (!\<langle>m\<rangle>) = get_sender m" |
  "get_actor (?\<langle>m\<rangle>) = get_receiver m"

primrec get_object :: "('information, 'peer) action \<Rightarrow> 'peer" where
  "get_object (!\<langle>m\<rangle>) = get_receiver m" |
  "get_object (?\<langle>m\<rangle>) = get_sender m"

abbreviation get_info :: "('information, 'peer) action \<Rightarrow> 'information" where
  "get_info a \<equiv> get_information (get_message a)"

abbreviation projection_on_outputs
  :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word"  ("_\<down>\<^sub>!" [90] 110)
  where
  "w\<down>\<^sub>! \<equiv> filter is_output w"

abbreviation projection_on_outputs_language
  :: "('information, 'peer) action language \<Rightarrow> ('information, 'peer) action language"
     ("_\<downharpoonright>\<^sub>!" [120] 100)
  where
  "L\<downharpoonright>\<^sub>! \<equiv> {w\<down>\<^sub>! | w. w \<in> L}"

abbreviation projection_on_inputs
  :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word"  ("_\<down>\<^sub>?" [90] 110)
  where
  "w\<down>\<^sub>? \<equiv> filter is_input w"

abbreviation projection_on_inputs_language
  :: "('information, 'peer) action language \<Rightarrow> ('information, 'peer) action language"
     ("_\<downharpoonright>\<^sub>?" [120] 100)
  where
  "L\<downharpoonright>\<^sub>? \<equiv> {w\<down>\<^sub>? | w. w \<in> L}"

abbreviation ignore_signs
  :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) message word"  ("_\<down>\<^sub>!\<^sub>?" [90] 110)
  where
  "w\<down>\<^sub>!\<^sub>? \<equiv> map get_message w"

abbreviation ignore_signs_in_language
  :: "('information, 'peer) action language \<Rightarrow> ('information, 'peer) message language"
     ("_\<downharpoonright>\<^sub>!\<^sub>?" [90] 110) where
  "L\<downharpoonright>\<^sub>!\<^sub>? \<equiv> {w\<down>\<^sub>!\<^sub>? | w. w \<in> L}"

\<comment> \<open>projection on receives towards p and sends from p\<close>
abbreviation projection_on_single_peer :: "('information, 'peer) action word  \<Rightarrow> 'peer \<Rightarrow> ('information, 'peer) action word"  ("_\<down>\<^sub>_" [90, 90] 110)
  where
"w\<down>\<^sub>p  \<equiv> filter (\<lambda>x. get_actor x = p) w"

abbreviation projection_on_single_peer_language
  :: "('information, 'peer) action language \<Rightarrow> 'peer \<Rightarrow> ('information, 'peer) action language"
     ("_\<downharpoonright>\<^sub>_" [90, 90] 110) where
  "(L\<downharpoonright>\<^sub>p) \<equiv> {(w\<down>\<^sub>p) | w. w \<in> L}"

abbreviation projection_on_peer_pair
  :: "('information, 'peer) action word \<Rightarrow> 'peer \<Rightarrow> 'peer \<Rightarrow> ('information, 'peer) action word"  ("_\<down>\<^sub>{\<^sub>_\<^sub>,\<^sub>_\<^sub>}" [90, 90, 90] 110)
  where
  "w\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}  \<equiv> filter (\<lambda>x. (get_object x = q \<and> get_actor x = p) \<or> (get_object x = p \<and> get_actor x = q)) w"

abbreviation projection_on_peer_pair_language
  :: "('information, 'peer) action language \<Rightarrow> 'peer \<Rightarrow> 'peer \<Rightarrow> ('information, 'peer) action language"
     ("_\<downharpoonright>\<^sub>{\<^sub>_\<^sub>,\<^sub>_\<^sub>}" [90, 90, 90] 110) where
  "(L\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}) \<equiv> {(w\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}) | w. w \<in> L}"




subsection \<open>Shuffled Language\<close>

inductive shuffled ::"('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
  (* Base case: every word shuffles to itself *)
  refl: "shuffled w w" |
  (* Single swap: !x?y \<rightarrow> ?y!x *)
  swap: "\<lbrakk> is_output a; is_input b ; w =  (xs @ a # b # ys) \<rbrakk> 
         \<Longrightarrow> shuffled w (xs @ b # a # ys)" |
  (* Transitive closure *)
  trans: "\<lbrakk> shuffled w w'; shuffled w' w'' \<rbrakk> \<Longrightarrow> shuffled w w''"

\<comment> \<open>another variant for the shuffled language\<close>
inductive_set  sh  ::"('information, 'peer) action word \<Rightarrow> ('information, 'peer) action language" for w ::"('information, 'peer) action word" where
sh_refl: "w \<in> sh w" |
sh_once: "\<lbrakk>w = (xs @ a # b # ys); is_output a; is_input b\<rbrakk> \<Longrightarrow> (xs @ b # a # ys) \<in> sh w" |
sh_trans: "\<lbrakk>w' \<in> sh w; w' = (xs @ a # b # ys); is_output a; is_input b\<rbrakk> \<Longrightarrow> (xs @ b # a # ys) \<in> sh w"


(* All possible shuffles of a word *)
definition all_shuffles :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word set" where
  "all_shuffles w = {w'. shuffled w w'}"

(* Shuffled language *)
definition shuffled_lang :: "('information, 'peer) action  language \<Rightarrow> ('information, 'peer) action language" where
  "shuffled_lang L = (\<Union>w\<in>L. all_shuffles w)"

lemma shuffle_preserves_length:
  "shuffled w w' \<Longrightarrow> length w = length w'"
  by (induction rule: shuffled.induct) auto

abbreviation valid_input_shuffles_of_w :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action language" where
  "valid_input_shuffles_of_w w \<equiv> {w'. shuffled w w'}"

abbreviation valid_input_shuffle :: 
  "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" (infixl "\<squnion>\<squnion>\<^sub>?" 60) where
  "w' \<squnion>\<squnion>\<^sub>? w \<equiv> shuffled w w'"

lemma shuffled_lang_subset_lang : 
  assumes "w \<in> L"
  shows "valid_input_shuffles_of_w w \<subseteq> shuffled_lang L"
  using all_shuffles_def assms shuffled_lang_def by fastforce

lemma input_shuffle_implies_shuffled_lang :
assumes "w \<in> L" and "w' \<in> valid_input_shuffles_of_w w"
shows "w' \<in> shuffled_lang L"
  using assms(1,2) shuffled_lang_subset_lang by auto


lemma shuffled_lang_not_empty :
  shows "(valid_input_shuffles_of_w w) \<noteq> {}"
  using shuffled.refl by auto

lemma valid_input_shuffles_of_lang : 
  assumes "w \<in> L"
  shows "\<exists> w'. (w' \<squnion>\<squnion>\<^sub>? w \<and> w' \<in> shuffled_lang L)"
  by (metis assms input_shuffle_implies_shuffled_lang mem_Collect_eq shuffled.refl)



lemma valid_input_shuffle_partner :
  assumes "{} \<noteq> valid_input_shuffles_of_w w"
  shows "\<exists>w'. w' \<squnion>\<squnion>\<^sub>? w"
  using assms by auto

value "[?\<langle>y\<rangle>, !\<langle>x\<rangle>, ?\<langle>z\<rangle>] \<squnion>\<squnion>\<^sub>? [!\<langle>x\<rangle>, ?\<langle>y\<rangle>, ?\<langle>z\<rangle>]"
value "[!\<langle>x\<rangle>, ?\<langle>y\<rangle>, ?\<langle>z\<rangle>] \<squnion>\<squnion>\<^sub>? [?\<langle>y\<rangle>, !\<langle>x\<rangle>, ?\<langle>z\<rangle>]"


lemma shuffle_id :
  fixes w
  assumes  "w \<in> L"
  shows "w \<in> shuffled_lang L"
  using assms 
  by (simp add: input_shuffle_implies_shuffled_lang shuffled.refl)
(*
lemma valid_input_shuffles_of_lang_rev : 
  assumes " w' \<in> shuffled_lang L"
  shows "\<exists>w. (w \<in> L \<and> w' \<squnion>\<squnion>\<^sub>? w)"
  sorry
lemma "shuffle_rev" : 
  assumes "v' \<in> shuffled_lang L"
  shows "\<exists>v. (v' \<squnion>\<squnion>\<^sub>? v \<and> v \<in> L)"
*)  

lemma shuffled_prepend:
  assumes "w'  \<squnion>\<squnion>\<^sub>?  w"
  shows "a # w'  \<squnion>\<squnion>\<^sub>? a # w"
  using assms 
proof (induct rule: shuffled.induct)
  case (refl w)
  then show ?case  using shuffled.refl by blast
next
  case (swap a b w xs ys)
  then show ?case by (metis append_Cons shuffled.swap)
next
  case (trans w w' w'')
  then show ?case using shuffled.trans by auto
qed

lemma fully_shuffled_implies_output_right :
  assumes "xs = xs\<down>\<^sub>?" and "is_output a"
  shows "shuffled ([a] @ xs) (xs @ [a]) "
  using assms
proof (induct xs)
  case Nil
  then show ?case by (simp add: shuffled.refl)
next
  case (Cons y ys)
  then have "ys @ [a] \<squnion>\<squnion>\<^sub>? (a #  ys)" 
    by (metis append_Cons append_eq_append_conv_if drop_eq_Nil2 filter.simps(2) impossible_Cons length_filter_le list.sel(3))
  have "is_input y" by (metis Cons.prems(1) filter_id_conv list.set_intros(1))
  then have "y # [a] \<squnion>\<squnion>\<^sub>? (a #  [y])" using append.assoc append.right_neutral assms(2) same_append_eq shuffled.simps by fastforce
  then have "y # a # ys  \<squnion>\<squnion>\<^sub>? a # y # ys" by (metis \<open>is_input y\<close> append_self_conv2 assms(2) shuffled.swap)
  then have "y # ys @ [a]  \<squnion>\<squnion>\<^sub>? y # a # ys" using \<open>ys \<cdot> a # \<epsilon> \<squnion>\<squnion>\<^sub>? a # ys\<close> shuffled_prepend by auto
  then show ?case using \<open>y # a # ys \<squnion>\<squnion>\<^sub>? a # y # ys\<close> shuffled.trans by auto
qed

lemma "fully_shuffled":
  assumes "v' = w # xs @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]" and "v' \<in> L" and "xs = xs\<down>\<^sub>!"
  shows "\<exists>v. v \<squnion>\<squnion>\<^sub>? v' \<and> v = w # ?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # xs"
  sorry


subsection \<open>A Communicating Automaton\<close>

locale CommunicatingAutomaton =
  fixes peer        :: "'peer"
    and States      :: "'state set"
    and initial     :: "'state"
    and Messages    :: "('information, 'peer) message set"
    and Transitions :: "('state \<times> ('information, 'peer) action \<times> 'state) set"
  assumes finite_states:          "finite States"
      and initial_state:          "initial \<in> States"
      and message_alphabet:       "Alphabet Messages"
      and well_formed_transition: "\<And>s1 a s2. (s1, a, s2) \<in> Transitions \<Longrightarrow>
                                   s1 \<in> States \<and> get_message a \<in> Messages \<and> get_actor a = peer \<and>
                                   get_object a \<noteq> peer \<and> s2 \<in> States"
begin

inductive_set ActionsOverMessages :: "('information, 'peer) action set" where
AOMOutput: "m \<in> Messages \<Longrightarrow> !\<langle>m\<rangle> \<in> ActionsOverMessages" |
AOMInput:  "m \<in> Messages \<Longrightarrow> ?\<langle>m\<rangle> \<in> ActionsOverMessages"

lemma ActionsOverMessages_is_finite:
  shows "finite ActionsOverMessages"
  using message_alphabet Alphabet.finite_letters[of Messages]
  by (simp add: ActionsOverMessages_def ActionsOverMessagesp.simps)

lemma action_is_action_over_message:
  fixes s1 s2 :: "'state"
    and a     :: "('information, 'peer) action"
  assumes "(s1, a, s2) \<in> Transitions"
  shows "a \<in> ActionsOverMessages"
  using assms
proof (induct a)
  case (Output m)
  assume "(s1, !\<langle>m\<rangle>, s2) \<in> Transitions"
  thus "!\<langle>m\<rangle> \<in> ActionsOverMessages"
    using well_formed_transition[of s1 "!\<langle>m\<rangle>" s2] AOMOutput[of m]
    by simp
next
  case (Input  m)
  assume "(s1, ?\<langle>m\<rangle>, s2) \<in> Transitions"
  thus "?\<langle>m\<rangle> \<in> ActionsOverMessages"
    using well_formed_transition[of s1 "?\<langle>m\<rangle>" s2] AOMInput[of m]
    by simp
qed

lemma transition_set_is_finite:
  shows "finite Transitions"
proof -
  have "Transitions \<subseteq> {(s1, a, s2). s1 \<in> States \<and> a \<in> ActionsOverMessages \<and> s2 \<in> States}"
    using well_formed_transition action_is_action_over_message
    by blast
  moreover have "finite {(s1, a, s2). s1 \<in> States \<and> a \<in> ActionsOverMessages \<and> s2 \<in> States}"
    using finite_states ActionsOverMessages_is_finite
    by simp
  ultimately show "finite Transitions"
    using finite_subset[of Transitions
                           "{(s1, a, s2). s1 \<in> States \<and> a \<in> ActionsOverMessages \<and> s2 \<in> States}"]
    by simp
qed

inductive_set Actions :: "('information, 'peer) action set"  ("Act") where
ActOfTrans: "(s1, a, s2) \<in> Transitions \<Longrightarrow> a \<in> Act"

lemma Actions_rev :
  assumes "a \<in> Act"
  shows "\<exists> s1 s2. (s1, a, s2) \<in> Transitions"
 by (meson Actions.cases assms)

lemma Act_is_subset_of_ActionsOverMessages:
  shows "Act \<subseteq> ActionsOverMessages"
proof
  fix a :: "('information, 'peer) action"
  assume "a \<in> Act"
  then obtain s1 s2 where "(s1, a, s2) \<in> Transitions"
    by (auto simp add: Actions_def Actionsp.simps)
  hence "get_message a \<in> Messages"
    using well_formed_transition[of s1 a s2]
    by simp
  thus "a \<in> ActionsOverMessages"
  proof (induct a)
    case (Output m)
    assume "get_message (!\<langle>m\<rangle>) \<in> Messages"
    thus "!\<langle>m\<rangle> \<in> ActionsOverMessages"
      using AOMOutput[of m]
      by simp
  next
    case (Input m)
    assume "get_message (?\<langle>m\<rangle>) \<in> Messages"
    thus "?\<langle>m\<rangle> \<in> ActionsOverMessages"
      using AOMInput[of m]
      by simp
  qed
qed

lemma Act_is_finite:
  shows "finite Act"
  using ActionsOverMessages_is_finite Act_is_subset_of_ActionsOverMessages
        finite_subset[of Act ActionsOverMessages]
  by simp

inductive_set CommunicationPartners :: "'peer set" where
CPAction: "(s1, a, s2) \<in> Transitions \<Longrightarrow> get_object a \<in> CommunicationPartners"

lemma ComunicationPartners_is_finite:
  shows "finite CommunicationPartners"
proof -
  have "CommunicationPartners \<subseteq> {p. \<exists>a. a \<in> ActionsOverMessages \<and> p = get_object a}"
    using action_is_action_over_message
    by (auto simp add: CommunicationPartners_def CommunicationPartnersp.simps)
  moreover have "finite {p. \<exists>a. a \<in> ActionsOverMessages \<and> p = get_object a}"
    using ActionsOverMessages_is_finite
    by simp
  ultimately show "finite CommunicationPartners"
    using finite_subset[of CommunicationPartners
                           "{p. \<exists>a. a \<in> ActionsOverMessages \<and> p = get_object a}"]
    by simp
qed

inductive_set SendingToPeers :: "'peer set" where
SPSend: "\<lbrakk>(s1, a, s2) \<in> Transitions; is_output a\<rbrakk> \<Longrightarrow> get_object a \<in> SendingToPeers"

lemma SendingToPeers_rev:
  fixes p :: "'peer"
  assumes "p \<in> SendingToPeers"
  shows "\<exists>s1 a s2. (s1, a, s2) \<in> Transitions \<and> is_output a \<and> get_object a = p"
  using assms
  by (induct, blast)

lemma SendingToPeers_is_subset_of_CommunicationPartners:
  shows "SendingToPeers \<subseteq> CommunicationPartners"
  using CommunicationPartners.intros SendingToPeersp.simps SendingToPeersp_SendingToPeers_eq
  by auto

inductive_set ReceivingFromPeers :: "'peer set" where
RPRecv: "\<lbrakk>(s1, a, s2) \<in> Transitions; is_input a\<rbrakk> \<Longrightarrow> get_object a \<in> ReceivingFromPeers"

lemma ReceivingFromPeers_rev:
  fixes p :: "'peer"
  assumes "p \<in> ReceivingFromPeers"
  shows "\<exists>s1 a s2. (s1, a, s2) \<in> Transitions \<and> is_input a \<and> get_object a = p"
  using assms
  by (induct, blast)

lemma ReceivingFromPeers_is_subset_of_CommunicationPartners:
  shows "ReceivingFromPeers \<subseteq> CommunicationPartners"
  using CommunicationPartners.intros ReceivingFromPeersp.simps
        ReceivingFromPeersp_ReceivingFromPeers_eq
  by auto


\<comment>\<open>this is to show that if p receives from no one, then there is no transition where p is the receiver\<close>
lemma empty_receiving_from_peers : 
  fixes p :: "'peer" 
  assumes "p \<notin> ReceivingFromPeers" and "(s1, a, s2) \<in> Transitions" and "is_input a"
  shows "get_object a \<noteq> p"
proof (rule ccontr)
  assume "\<not> get_object a \<noteq> p"
  then show "False"
  proof
  have "get_object a = p" using \<open>\<not> get_object a \<noteq> p\<close> by auto
    moreover have "p \<in> ReceivingFromPeers" 
      using ReceivingFromPeers.intros \<open>\<not> get_object a \<noteq> p\<close> assms(2,3) by auto
  moreover have "False" 
    using assms(1) calculation by auto
  ultimately show "get_object a \<noteq> p"  using assms(1) by auto
qed
qed



abbreviation step
  :: "'state \<Rightarrow> ('information, 'peer) action \<Rightarrow> 'state \<Rightarrow> bool"  ("_ \<midarrow>_\<rightarrow> _" [90, 90, 90] 110)
  where
  "s1 \<midarrow>a\<rightarrow> s2 \<equiv> (s1, a, s2) \<in> Transitions"

(*
\<comment> \<open>this is the original run def, i swapped it to (a#w) (see below)\<close>
inductive run :: "'state \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'state list \<Rightarrow> bool" where
REmpty:    "run s \<epsilon> ([])" |
RComposed: "\<lbrakk>run s0 w xs; last (s0#xs) \<midarrow>a\<rightarrow> s\<rbrakk> \<Longrightarrow> run s0 (w\<cdot>[a]) (xs@[s])"
*)

inductive run :: "'state \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'state list \<Rightarrow> bool" where
REmpty2:    "run s \<epsilon> ([])" |
RComposed2: "\<lbrakk>run s1 w xs; s0 \<midarrow>a\<rightarrow> s1\<rbrakk> \<Longrightarrow> run s0 (a # w) (s1 # xs)"

lemma run_rev :
  assumes "run s0 (a # w) (s1 # xs)"
  shows "run s1 w xs \<and> s0 \<midarrow>a\<rightarrow> s1"
  by (smt (verit, best) assms list.discI list.inject run.simps)

lemma run_app :
  assumes "run s0 (u @ v) xs" and "u \<noteq> \<epsilon>"
  shows "\<exists>us vs. run s0 u us \<and> run (last us) v vs \<and>xs = us @ vs"
  using assms
proof (induct "u@v" xs  arbitrary: u v rule: run.induct)
  case (REmpty2 s)
  then show ?case by simp
next
  case (RComposed2 s1 w xs s0 a)
  then have "a # w = u \<cdot> v" by simp
  then have "\<exists> u'. w = u' \<cdot> v \<and> u = a # u'" 
    by (metis RComposed2.prems append_eq_Cons_conv)
  then obtain u' where w_decomp: "w = u' @ v" and u_decomp: "u = a # u'" by auto 
  then have "run s1 (u' @ v) xs" using RComposed2.hyps(1) by auto
  then show ?case 
  proof (cases "u' = \<epsilon>")
    case True
    then have "run s1 v xs" using RComposed2.hyps(1) w_decomp by auto
    then have "run s0 [a] [s1]" 
      by (metis CommunicatingAutomaton.RComposed2 CommunicatingAutomaton.REmpty2
          CommunicatingAutomaton_axioms RComposed2.hyps(3))
    then have "run s0 (a # v) (s1 # xs)"  by (simp add: RComposed2.hyps(3) \<open>run s1 v xs\<close> run.RComposed2)
    then show ?thesis  using True \<open>run s0 (a # \<epsilon>) (s1 # \<epsilon>)\<close> \<open>run s1 v xs\<close> u_decomp by auto
  next
    case False
    then obtain us' vs where xs_decomp: "run s1 u' us' \<and> run (last us') v vs \<and> xs = us' \<cdot> vs" 
      using RComposed2.hyps(2) w_decomp by blast 
    then have "run s0 (a # w) (s1 # us' @ vs)" using RComposed2.hyps(1,3) run.RComposed2 by auto
    then have full_run_decomp: "run s0 (a # u' @ v) (s1 # us' @ vs)"  by (simp add: w_decomp)
    then have "run s1 u' us'"  by (simp add: xs_decomp)
    then have "run s0 [a] [s1]" by (simp add: RComposed2.hyps(3) REmpty2 run.RComposed2)
    then have "run (last us') v vs" by (simp add: xs_decomp)
    then have "run s0 u (s1 # us')"  by (simp add: RComposed2.hyps(3) run.RComposed2 u_decomp xs_decomp)
    then have "run s0 u (s1 # us') \<and> run (last (s1 # us')) v vs \<and> s1 # xs = (s1 # us') \<cdot> vs" 
      using False run.cases xs_decomp by force
    then show ?thesis by blast
  qed
qed

lemma run_second :
  assumes "run s0 (u @ v) (us@vs)" and "u \<noteq> \<epsilon>" and "run s0 u us"
  shows "run (last us) v vs"
  using assms
proof (induct "u@v" "us@vs"  arbitrary: u v us vs rule: run.induct)
  case (REmpty2 s)
  then show ?case by simp
next
  case (RComposed2 s1 w xs s0 a)
   then show ?case by (smt (verit) append_eq_Cons_conv append_self_conv2 last_ConsL last_ConsR list.discI
        list.inject run.simps)
qed


inductive_set Traces :: "('information, 'peer) action word set" where
STRun: "run initial w xs \<Longrightarrow> w \<in> Traces"

lemma Traces_rev : 
  fixes w :: "('information, 'peer) action word"
  assumes "w \<in> Traces"
  shows "\<exists> xs. run initial w xs"
  using assms
  by (induct, blast)


\<comment> \<open>since all states are final, if u \<cdot> v is valid then u must also be valid 
otherwise some transition for u is missing and hence u \<cdot> v would be invalid\<close>
lemma Traces_app :
  assumes "(u @ v) \<in> Traces"
  shows "u \<in> Traces"
  by (metis CommunicatingAutomaton.REmpty2 CommunicatingAutomaton_axioms Traces.cases
      Traces.intros assms run_app)

lemma Traces_second :
  assumes "(u @ v) \<in> Traces" and "u \<noteq> \<epsilon>"
  shows "\<exists>s0 us vs. run s0 (u @ v) (us@vs) \<and> run (last us) v vs"
  using Traces_rev assms(1,2) run_app by blast


(*
lemma run_rev : 
  fixes w :: "('information, 'peer) action word"
assumes "run s0 (w\<cdot>[a]) (xs@[s])"
shows "last (s0#xs) \<midarrow>a\<rightarrow> s \<and> run s0 w xs"
  using assms run.cases by fastforce
*)

abbreviation Lang :: "('information, 'peer) action language" where
  "Lang \<equiv> Traces"

abbreviation LangSend :: "('information, 'peer) action language" where
  "LangSend \<equiv> Lang\<downharpoonright>\<^sub>!"

abbreviation LangRecv :: "('information, 'peer) action language" where
  "LangRecv \<equiv> Lang\<downharpoonright>\<^sub>?"

end

subsection \<open>Network of Communicating Automata\<close>

locale NetworkOfCA =
  fixes automata :: "'peer \<Rightarrow> ('state set \<times> 'state \<times>
                     ('state \<times> ('information, 'peer) action \<times> 'state) set)"  ("\<A>" 1000)
    and messages :: "('information, 'peer) message set"                       ("\<M>" 1000)
  assumes finite_peers:      "finite (UNIV :: 'peer set)"
      and automaton_of_peer: "\<And>p. CommunicatingAutomaton p (fst (\<A> p)) (fst (snd (\<A> p))) \<M>
                                   (snd (snd (\<A> p)))"
      and message_alphabet:  "Alphabet \<M>"
      and peers_of_message:  "\<And>m. m \<in> \<M> \<Longrightarrow> get_sender m \<noteq> get_receiver m"
      and messages_used:     "\<forall>m \<in> \<M>. \<exists>s1 a s2 p. (s1, a, s2) \<in> snd (snd (\<A> p)) \<and>
                              m = get_message a"
begin

\<comment> \<open>all peers in network\<close>
abbreviation get_peers :: "'peer set" ("\<P>" 110) where
"\<P> \<equiv> (UNIV :: 'peer set)"

abbreviation get_states :: "'peer \<Rightarrow> 'state set"  ("\<S> _" [90] 110) where
  "\<S>(p) \<equiv> fst (\<A> p)"

abbreviation get_initial_state :: "'peer \<Rightarrow> 'state"  ("\<I> _" [90] 110) where
  "\<I>(p) \<equiv> fst (snd (\<A> p))"

abbreviation get_transitions
  :: "'peer \<Rightarrow> ('state \<times> ('information, 'peer) action \<times> 'state) set"  ("\<R> _" [90] 110) where
  "\<R>(p) \<equiv> snd (snd (\<A> p))"

abbreviation WordsOverMessages :: "('information, 'peer) message word set"  ("\<M>\<^sup>*" 100) where
  "\<M>\<^sup>* \<equiv> Alphabet.WordsOverAlphabet \<M>"

\<comment> \<open>all q that p sends to in Ap (for which there is a transition !p->q in Ap)\<close>
abbreviation sendingToPeers_of_peer :: "'peer \<Rightarrow> 'peer set"  ("\<P>\<^sub>! _" [90] 110) where
  "\<P>\<^sub>!(p) \<equiv> CommunicatingAutomaton.SendingToPeers (snd (snd (\<A> p)))"

\<comment> \<open>all q that p receives from in Ap (for which there is a transition ?q->p in Ap)\<close>
abbreviation receivingFromPeers_of_peer :: "'peer \<Rightarrow> 'peer set"  ("\<P>\<^sub>? _" [90] 110) where
  "\<P>\<^sub>?(p) \<equiv> CommunicatingAutomaton.ReceivingFromPeers (snd (snd (\<A> p)))"

abbreviation Peers_of :: "'peer \<Rightarrow> 'peer set" where
"Peers_of p \<equiv> CommunicatingAutomaton.CommunicationPartners (snd (snd (\<A> p)))"


value "CommunicatingAutomaton.SendingToPeers ({(s1, !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, s2)}::('state \<times> ('information, 'peer) action \<times> 'state) set)"
value "q \<in> CommunicatingAutomaton.SendingToPeers ({(s1, !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, s2)}::('state \<times> ('information, 'peer) action \<times> 'state) set)"
term "\<A>"
term "\<A> p"
term "(snd (snd (\<A> p)))"

abbreviation step_of_peer
  :: "'state \<Rightarrow> ('information, 'peer) action \<Rightarrow> 'peer \<Rightarrow> 'state \<Rightarrow> bool"
     ("_ \<midarrow>_\<rightarrow>_ _" [90, 90, 90, 90] 110) where
  "s1 \<midarrow>a\<rightarrow>p s2 \<equiv> (s1, a, s2) \<in> snd (snd (\<A> p))"

abbreviation language_of_peer
  :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L> _" [90] 110) where
  "\<L>(p) \<equiv> CommunicatingAutomaton.Lang (fst (snd (\<A> p))) (snd (snd (\<A> p)))"

term "(fst (snd (\<A> p)))"
term "(snd (snd (\<A> p)))"

abbreviation output_language_of_peer
  :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>! _" [90] 110) where
  "\<L>\<^sub>!(p) \<equiv> CommunicatingAutomaton.LangSend (fst (snd (\<A> p))) (snd (snd (\<A> p)))"

abbreviation input_language_of_peer
  :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>? _" [90] 110) where
  "\<L>\<^sub>?(p) \<equiv> CommunicatingAutomaton.LangRecv (fst (snd (\<A> p))) (snd (snd (\<A> p)))"



\<comment>\<open>this is to show that if p receives from no one, then there is no transition where p is the receiver\<close>

lemma empty_receiving_from_peers2 : 
  fixes p :: "'peer" 
  assumes "p \<notin> ReceivingFromPeers" and "(s1, a, s2) \<in> \<R>(p)" and "is_input a"
  shows "get_object a \<noteq> p"
proof (rule ccontr)
  assume "\<not> get_object a \<noteq> p"
  then show "False"
  proof
  have "get_object a = p" using \<open>\<not> get_object a \<noteq> p\<close> by auto
  moreover have "False" 
    by (metis CommunicatingAutomaton.well_formed_transition \<open>\<not> get_object a \<noteq> p\<close> assms(2)
        automaton_of_peer)
  ultimately show "get_object a \<noteq> p"  using assms(1) by auto
qed
qed


lemma empty_receiving_from_peers3 : 
  fixes p :: "'peer" 
  assumes "\<P>\<^sub>?(p) = {}" and "(s1, a, s2) \<in> \<R>(p)" and "is_input a"
  shows "get_object a \<noteq> p"
proof (rule ccontr)
  assume "\<not> get_object a \<noteq> p"
  then show "False"
  proof
  have "get_object a = p" using \<open>\<not> get_object a \<noteq> p\<close> by auto
  moreover have "False" 
    by (metis CommunicatingAutomaton.well_formed_transition \<open>\<not> get_object a \<noteq> p\<close> assms(2)
        automaton_of_peer)
  ultimately show "get_object a \<noteq> p"  using assms(1) by auto
qed
qed

lemma empty_receiving_from_peers4 : 
  fixes p :: "'peer" 
  assumes "\<P>\<^sub>?(p) = {}" and "(s1, a, s2) \<in> \<R>(p)"
  shows "is_output a"
  by (metis CommunicatingAutomaton.ReceivingFromPeers.intros assms(1,2) automaton_of_peer
      empty_iff)

lemma no_input_trans_root : 
  fixes p :: "'peer"
  assumes "is_input a" and "\<P>\<^sub>?(p) = {}"
  shows "(s1, a, s2) \<notin> \<R>(p)"
  using assms(1,2) empty_receiving_from_peers4 by auto


lemma act_in_lang_means_trans_exists : 
  fixes p :: "'peer"
  assumes "[a] \<in> \<L>(p)"
  shows "\<exists>s1 s2. (s1, a, s2) \<in> \<R>(p)"
by (smt (verit) CommunicatingAutomaton.Traces_rev CommunicatingAutomaton.run.cases assms automaton_of_peer list.distinct(1)
      list.inject)

lemma act_not_in_lang_no_trans :
  fixes p :: "'peer"
  assumes "\<forall>s1 s2. (s1, a, s2) \<notin> \<R>(p)"
  shows "[a] \<notin> \<L>(p)"
  using act_in_lang_means_trans_exists assms by auto



lemma no_input_trans_no_word_in_lang : 
  fixes p :: "'peer"
  assumes "(a # w) \<in> \<L>(p)"
  shows "\<exists>s1 s2. (s1, a, s2) \<in> \<R>(p)"
by (smt (verit, ccfv_SIG) CommunicatingAutomaton.Traces_rev CommunicatingAutomaton.run.cases assms automaton_of_peer
      list.distinct(1) list.inject)

lemma no_word_no_trans :
  fixes p :: "'peer"
  assumes "\<forall>s1 s2. (s1, a, s2) \<notin> \<R>(p)"
  shows "(a # w) \<notin> \<L>(p)"
  using assms no_input_trans_no_word_in_lang by blast

lemma root_head_is_output : 
  fixes p :: "'peer"
  assumes "\<P>\<^sub>?(p) = {}" and "(a # w)  \<in> \<L>(p)"
  shows "is_output a"
  using assms(1,2) no_input_trans_root no_word_no_trans by blast

lemma root_head_is_not_input :
fixes p :: "'peer"
assumes "\<P>\<^sub>?(p) = {}" and "is_input a"
shows "(a # w)  \<notin> \<L>(p)"
  using assms(1,2) root_head_is_output by auto


lemma eps_always_in_lang :
  fixes p :: "'peer"
  assumes "\<L>(p) \<noteq> {}"
  shows "\<epsilon> \<in> \<L>(p)"
  by (meson CommunicatingAutomaton.Traces.simps CommunicatingAutomaton.run.simps automaton_of_peer)


lemma no_recvs_no_input_trans :
fixes p :: "'peer"
assumes "\<P>\<^sub>?(p) = {}"
shows "\<forall> s1 a s2. (is_input a \<longrightarrow> (s1, a, s2) \<notin> \<R>(p))"
  by (simp add: assms no_input_trans_root)

lemma no_input_trans_no_recvs :
  fixes p :: "'peer"
assumes "\<forall> s1 a s2. (is_input a \<longrightarrow> (s1, a, s2) \<notin> \<R>(p))"
shows "\<P>\<^sub>?(p) = {}"
  by (meson CommunicatingAutomaton.ReceivingFromPeers.simps assms automaton_of_peer subsetI subset_empty)

lemma Lang_app :
  assumes "(u @ v) \<in> \<L>(p)"
  shows "u \<in> \<L>(p)"
  by (meson CommunicatingAutomaton.Traces_app assms automaton_of_peer)


lemma lang_implies_run: 
  assumes "w \<in> \<L>(p)"
  shows "\<exists>xs. CommunicatingAutomaton.run (\<R> p) (\<I> p) w xs"
  by (meson CommunicatingAutomaton.Traces.simps assms automaton_of_peer)

lemma lang_implies_prepend_run : 
assumes "(a # w) \<in> \<L>(p)"
  shows "\<exists>xs s1. CommunicatingAutomaton.run (\<R> p) (s1) w xs \<and> CommunicatingAutomaton.run (\<R> p) (\<I> p) [a] [s1]"
  by (smt (verit) CommunicatingAutomaton.RComposed2 CommunicatingAutomaton.REmpty2
      CommunicatingAutomaton.run.cases assms automaton_of_peer concat.simps(1) list.distinct(1)
      list.inject lang_implies_run)

\<comment> \<open>start in s1, read w (in 0 or more steps) and end in s2 \<close>
abbreviation path_of_peer
  :: "'state \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'peer \<Rightarrow> 'state \<Rightarrow> bool"
     ("_ \<midarrow>_\<rightarrow>\<^sup>*_ _" [90, 90, 90, 90] 110) where
  "s1 \<midarrow>w\<rightarrow>\<^sup>*p s2 \<equiv> (s1=s2 \<and> w = \<epsilon> \<and> s1 \<in> \<S> p)  \<or> (\<exists>xs. CommunicatingAutomaton.run (\<R> p) s1 w xs \<and> last xs = s2)"


abbreviation run_of_peer
:: " 'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'state  list \<Rightarrow> bool" where
  "run_of_peer p w xs \<equiv> (CommunicatingAutomaton.run (\<R> p) (\<I> p) w xs)"

abbreviation run_of_peer_from_state
:: " 'peer \<Rightarrow> 'state \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'state  list \<Rightarrow> bool" where
  "run_of_peer_from_state p s w xs \<equiv> (CommunicatingAutomaton.run (\<R> p) s w xs)"

fun get_trans_of_run :: "'state \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'state list \<Rightarrow> ('state \<times> ('information, 'peer) action \<times> 'state) list" where
"get_trans_of_run s0 \<epsilon> [] = []" |
"get_trans_of_run s0 [a] [s1] = [(s0, a, s1)]" |
"get_trans_of_run s0 (a # as) (s1 # xs) = (s0, a, s1) # get_trans_of_run s1 as xs"


lemma lang_implies_run_alt :
  assumes "w \<in> \<L>(p)"
  shows "\<exists>s2. (\<I> p) \<midarrow>w\<rightarrow>\<^sup>*p s2"
  using assms lang_implies_run by blast

lemma Lang_app_both :
  assumes "(u @ v) \<in> \<L>(p)"
  shows "\<exists>s2 s3. (\<I> p) \<midarrow>u\<rightarrow>\<^sup>*p s2 \<and> s2 \<midarrow>v\<rightarrow>\<^sup>*p s3"
  by (metis CommunicatingAutomaton.initial_state CommunicatingAutomaton.run_app assms
      automaton_of_peer lang_implies_run self_append_conv2)

lemma lang_implies_trans :
  assumes "s1 \<midarrow>[a]\<rightarrow>\<^sup>*p s2"
  shows "s1 \<midarrow>a\<rightarrow>p s2"
  by (smt (verit, best) CommunicatingAutomaton.run.cases assms automaton_of_peer last.simps
      list.distinct(1) list.inject)


subsection \<open>Synchronous System\<close>

definition is_sync_config :: "('peer \<Rightarrow> 'state) \<Rightarrow> bool" where
  "is_sync_config C \<equiv> (\<forall>p. C p \<in> \<S>(p))"

abbreviation initial_sync_config :: "'peer \<Rightarrow> 'state"  ("\<C>\<^sub>\<I>\<^sub>\<zero>") where
  "\<C>\<^sub>\<I>\<^sub>\<zero> \<equiv> \<lambda>p. \<I>(p)"

lemma initial_configuration_is_synchronous_configuration:
  shows "is_sync_config \<C>\<^sub>\<I>\<^sub>\<zero>"
  unfolding is_sync_config_def
proof clarify
  fix p :: "'peer"
  show "\<C>\<^sub>\<I>\<^sub>\<zero>(p) \<in> \<S>(p)"
    using automaton_of_peer[of p]
          CommunicatingAutomaton.initial_state[of p "\<S> p" "\<C>\<^sub>\<I>\<^sub>\<zero> p" \<M> "\<R> p"]
    by simp
qed

inductive sync_step
  :: "('peer \<Rightarrow> 'state) \<Rightarrow> ('information, 'peer) action \<Rightarrow> ('peer \<Rightarrow> 'state) \<Rightarrow> bool"
     ("_ \<midarrow>\<langle>_, \<zero>\<rangle>\<rightarrow> _" [90, 90, 90] 110) where
SynchStep: "\<lbrakk>is_sync_config C1; a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>; C1 p \<midarrow>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>p (C2 p);
             C1 q \<midarrow>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>q (C2 q); \<forall>x. x \<notin> {p, q} \<longrightarrow> C1(x) = C2(x)\<rbrakk> \<Longrightarrow> C1 \<midarrow>\<langle>a, \<zero>\<rangle>\<rightarrow> C2"

lemma sync_step_rev:
  fixes C1 C2 :: "'peer \<Rightarrow> 'state"
    and a     :: "('information, 'peer) action"
  assumes "C1 \<midarrow>\<langle>a, \<zero>\<rangle>\<rightarrow> C2"
  shows "is_sync_config C1" and "is_sync_config C2" and "\<exists>i p q. a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>"
    and "get_actor a \<noteq> get_object a" and "C1 (get_actor a) \<midarrow>a\<rightarrow>(get_actor a) (C2 (get_actor a))"
    and "\<exists>m. a = !\<langle>m\<rangle> \<and> C1 (get_object a) \<midarrow>?\<langle>m\<rangle>\<rightarrow>(get_object a) (C2 (get_object a))"
    and "\<forall>x. x \<notin> {get_actor a, get_object a} \<longrightarrow> C1(x) = C2(x)"
  using assms
proof induct
  case (SynchStep C1 a i p q C2)
  assume A1: "is_sync_config C1"
  thus "is_sync_config C1" .
  assume A2: "a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>"
  thus "\<exists>i p q. a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>"
    by blast
  assume A3: "C1 p \<midarrow>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>p (C2 p)"
  with A2 show "C1 (get_actor a) \<midarrow>a\<rightarrow>(get_actor a) (C2 (get_actor a))"
    by simp
  have A4: "CommunicatingAutomaton p (\<S> p) (\<I> p) \<M> (\<R> p)"
    using automaton_of_peer[of p]
    by simp
  with A2 A3 show "get_actor a \<noteq> get_object a"
    using CommunicatingAutomaton.well_formed_transition[of p "\<S> p" "\<I> p" \<M> "\<R> p" "C1 p" a "C2 p"]
    by auto
  assume A5: "C1 q \<midarrow>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>q (C2 q)"
  with A2 show "\<exists>m. a = !\<langle>m\<rangle> \<and> C1 (get_object a) \<midarrow>?\<langle>m\<rangle>\<rightarrow>(get_object a) (C2 (get_object a))"
    by auto
  assume A6: "\<forall>x. x \<notin> {p, q} \<longrightarrow> C1 x = C2 x"
  with A2 show "\<forall>x. x \<notin> {get_actor a, get_object a} \<longrightarrow> C1(x) = C2(x)"
    by simp
  show "is_sync_config C2"
    unfolding is_sync_config_def
  proof clarify
    fix x :: "'peer"
    show "C2(x) \<in> \<S>(x)"
    proof (cases "x = p")
      assume "x = p"
      with A3 A4 show "C2(x) \<in> \<S>(x)"
        using CommunicatingAutomaton.well_formed_transition[of p "\<S> p" "\<I> p" \<M> "\<R> p" "C1 p"
                "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" "C2 p"]
        by simp
    next
      assume B: "x \<noteq> p"
      show "C2(x) \<in> \<S>(x)"
      proof (cases "x = q")
        assume "x = q"
        with A5 show "C2(x) \<in> \<S>(x)"
          using automaton_of_peer[of q]
                CommunicatingAutomaton.well_formed_transition[of q "\<S> q" "\<I> q" \<M> "\<R> q" "C1 q"
                "?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" "C2 q"]
          by simp
      next
        assume "x \<noteq> q"
        with A1 A6 B show "C2(x) \<in> \<S>(x)"
          unfolding is_sync_config_def
          by (metis empty_iff insertE)
      qed
    qed
  qed
qed

lemma sync_step_output_rev:
  fixes C1 C2 :: "'peer \<Rightarrow> 'state"
    and i     :: "'information"
    and p q   :: "'peer"
  assumes "C1 \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<zero>\<rangle>\<rightarrow> C2"
  shows "is_sync_config C1" and "is_sync_config C2" and "p \<noteq> q" and "C1 p \<midarrow>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>p (C2 p)"
    and "C1 q \<midarrow>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>q (C2 q)" and "\<forall>x. x \<notin> {p, q} \<longrightarrow> C1(x) = C2(x)"
  using assms sync_step_rev[of C1 "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" C2]
  by simp_all

inductive sync_run
  :: "('peer \<Rightarrow> 'state) \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('peer \<Rightarrow> 'state) list \<Rightarrow> bool"
  where
SREmpty:    "sync_run C \<epsilon> ([])" |
SRComposed: "\<lbrakk>sync_run C0 w xc; last (C0#xc) \<midarrow>\<langle>a, \<zero>\<rangle>\<rightarrow> C\<rbrakk> \<Longrightarrow> sync_run C0 (w\<cdot>[a]) (xc@[C])"

lemma sync_run_rev :
  assumes "sync_run C0 (w\<cdot>[a]) (xc@[C])"
  shows "sync_run C0 w xc \<and> last (C0#xc) \<midarrow>\<langle>a, \<zero>\<rangle>\<rightarrow> C"
  using NetworkOfCA.sync_run.cases NetworkOfCA_axioms assms by blast

lemma run_produces_synchronous_configurations:
  fixes C C' :: "'peer \<Rightarrow> 'state"
    and w    :: "('information, 'peer) action word"
    and xc   :: "('peer \<Rightarrow> 'state) list"
  assumes "sync_run C w xc"
      and "C' \<in> set xc"
    shows "is_sync_config C'"
  using assms
proof induct
  case (SREmpty C)
  assume "C' \<in> set []"
  hence False
    by simp
  thus "is_sync_config C'"
    by simp
next
  case (SRComposed C0 w xc a C)
  assume A1: "C' \<in> set xc \<Longrightarrow> is_sync_config C'" and A2: "last (C0#xc) \<midarrow>\<langle>a, \<zero>\<rangle>\<rightarrow> C"
     and A3: "C' \<in> set (xc\<cdot>[C])"
  show "is_sync_config C'"
  proof (cases "C = C'")
    assume "C = C'"
    with A2 show "is_sync_config C'"
      using sync_step_rev(2)[of "last (C0#xc)" a C]
      by simp
  next
    assume "C \<noteq> C'"
    with A1 A3 show "is_sync_config C'"
      by simp
  qed
qed

lemma run_produces_no_inputs:
  fixes C C' :: "'peer \<Rightarrow> 'state"
    and w    :: "('information, 'peer) action word"
    and xc   :: "('peer \<Rightarrow> 'state) list"
  assumes "sync_run C w xc"
  shows "w\<down>\<^sub>! = w" and "w\<down>\<^sub>? = \<epsilon>"
  using assms
proof induct
  case (SREmpty C)
  show "\<epsilon>\<down>\<^sub>! = \<epsilon>" and "\<epsilon>\<down>\<^sub>? = \<epsilon>"
    by simp_all
next
  case (SRComposed C0 w xc a C)
  assume "w\<down>\<^sub>! = w"
  moreover assume "last (C0#xc) \<midarrow>\<langle>a, \<zero>\<rangle>\<rightarrow> C"
  hence A: "is_output a"
    using sync_step_rev(3)[of "last (C0#xc)" a C]
    by auto
  ultimately show "(w \<cdot> [a])\<down>\<^sub>! = w \<cdot> [a]"
    by simp
  assume "w\<down>\<^sub>? = \<epsilon>"
  with A show "(w \<cdot> [a])\<down>\<^sub>? = \<epsilon>"
    by simp
qed

\<comment> \<open>E(Nsync)\<close>
inductive_set SyncTraces :: "('information, 'peer) action language"  ("\<T>\<^sub>\<zero>" 120) where
STRun: "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xc \<Longrightarrow> w \<in> \<T>\<^sub>\<zero>"

lemma SyncTraces_rev :
  assumes "w \<in> \<T>\<^sub>\<zero>"
  shows "\<exists>xc. sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xc"
  using SyncTraces.simps assms by auto

\<comment> \<open>T(Nsync)\<close>
abbreviation SyncLang :: "('information, 'peer) action language"  ("\<L>\<^sub>\<zero>" 120) where
  "\<L>\<^sub>\<zero> \<equiv> \<T>\<^sub>\<zero>"

lemma no_inputs_in_synchronous_communication:
  shows "\<L>\<^sub>\<zero>\<downharpoonright>\<^sub>! = \<L>\<^sub>\<zero>" and "\<L>\<^sub>\<zero>\<downharpoonright>\<^sub>? \<subseteq> {\<epsilon>}"
proof -
  have "\<forall>w \<in> \<L>\<^sub>\<zero>. w\<down>\<^sub>! = w"
    using SyncTraces.simps run_produces_no_inputs(1)
    by blast
  thus "\<L>\<^sub>\<zero>\<downharpoonright>\<^sub>! = \<L>\<^sub>\<zero>"
    by force
  have "\<forall>w \<in> \<L>\<^sub>\<zero>. w\<down>\<^sub>? = \<epsilon>"
    using SyncTraces.simps run_produces_no_inputs(2)
    by blast
  thus "\<L>\<^sub>\<zero>\<downharpoonright>\<^sub>? \<subseteq> {\<epsilon>}"
    by auto
qed

subsection \<open>Mailbox System\<close>

subsubsection \<open>Semantics and Language\<close>

definition is_mbox_config
  :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> bool" where
  "is_mbox_config C \<equiv> (\<forall>p. fst (C p) \<in> \<S>(p) \<and> snd (C p) \<in> \<M>\<^sup>*)"



\<comment> \<open>all mbox configurations of system\<close>
abbreviation mbox_configs 
  :: "('peer \<Rightarrow> 'state \<times> ('information, 'peer) message list) set"  ("\<C>\<^sub>\<mm>") where
  "\<C>\<^sub>\<mm> \<equiv> {C | C. is_mbox_config C}"

abbreviation initial_mbox_config
  :: "'peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)"  ("\<C>\<^sub>\<I>\<^sub>\<mm>") where
  "\<C>\<^sub>\<I>\<^sub>\<mm> \<equiv> \<lambda>p. (\<I> p, \<epsilon>)"

lemma initial_mbox_alt :
  shows "(\<forall>p. \<C>\<^sub>\<I>\<^sub>\<mm> p = (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>))"
  by simp

lemma initial_configuration_is_mailbox_configuration:
  shows "is_mbox_config \<C>\<^sub>\<I>\<^sub>\<mm>"
  unfolding is_mbox_config_def
proof clarify
  fix p :: "'peer"
  show "fst (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>) \<in> \<S> p \<and> snd (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>) \<in> \<M>\<^sup>*"
    using automaton_of_peer[of p] message_alphabet Alphabet.EmptyWord[of \<M>]
          CommunicatingAutomaton.initial_state[of p "\<S> p" "\<I> p" \<M> "\<R> p"]
    by simp
qed

definition is_stable
  :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> bool" where
  "is_stable C \<equiv> is_mbox_config C \<and> (\<forall>p. snd (C p) = \<epsilon>)"

lemma initial_configuration_is_stable:
  shows "is_stable \<C>\<^sub>\<I>\<^sub>\<mm>"
  unfolding is_stable_def using initial_configuration_is_mailbox_configuration
  by simp

lemma sync_config_to_mbox :
  assumes "is_sync_config C"
  shows "\<exists>C'. is_mbox_config C' \<and> C' = (\<lambda>p. (C p, \<epsilon>))"
 using assms initial_configuration_is_mailbox_configuration is_mbox_config_def
    is_sync_config_def by auto

type_synonym bound = "nat option"

abbreviation nat_bound :: "nat \<Rightarrow> bound"  ("\<B> _" [90] 110) where
  "\<B> k \<equiv> Some k"

abbreviation unbounded :: "bound"  ("\<infinity>" 100) where
  "\<infinity> \<equiv> None"

primrec is_bounded :: "nat \<Rightarrow> bound \<Rightarrow> bool"  ("_ <\<^sub>\<B> _" [90, 90] 110) where
  "n <\<^sub>\<B> \<infinity> = True" |
  "n <\<^sub>\<B> \<B> k = (n < k)"

inductive mbox_step
  :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> ('information, 'peer) action \<Rightarrow>
      bound \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> bool" where
MboxSend: "\<lbrakk>is_mbox_config C1; a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>; fst (C1 p) \<midarrow>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>p (fst (C2 p));
            snd (C1 p) = snd (C2 p); ( | (snd (C1 q)) | ) <\<^sub>\<B> k;
            C2 q = (fst (C1 q), (snd (C1 q)) \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)]); \<forall>x. x \<notin> {p, q} \<longrightarrow> C1(x) = C2(x)\<rbrakk> \<Longrightarrow>
            mbox_step C1 a k C2" |
MboxRecv: "\<lbrakk>is_mbox_config C1; a = ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>; fst (C1 q) \<midarrow>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>q (fst (C2 q));
            (snd (C1 q)) = [(i\<^bsup>p\<rightarrow>q\<^esup>)] \<cdot> snd (C2 q); \<forall>x. x \<noteq> q \<longrightarrow> C1(x) = C2(x)\<rbrakk> \<Longrightarrow>
            mbox_step C1 a k C2"


lemma mbox_step_rev:
  fixes C1 C2 :: "'peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)"
    and a     :: "('information, 'peer) action"
    and k     :: "bound"
  assumes "mbox_step C1 a k C2"
  shows "is_mbox_config C1" and "is_mbox_config C2"
    and "\<exists>i p q. a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle> \<or> a = ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" and "get_actor a \<noteq> get_object a"
    and "fst (C1 (get_actor a)) \<midarrow>a\<rightarrow>(get_actor a) (fst (C2 (get_actor a)))"
    and "is_output a \<Longrightarrow> snd (C1 (get_actor a)) = snd (C2 (get_actor a))"
    and "is_output a \<Longrightarrow> ( | (snd (C1 (get_object a))) | ) <\<^sub>\<B> k"
    and "is_output a \<Longrightarrow> C2 (get_object a) =
                         (fst (C1 (get_object a)), (snd (C1 (get_object a))) \<cdot> [get_message a])"
    and "is_input a \<Longrightarrow> (snd (C1 (get_actor a))) = [get_message a] \<cdot> snd (C2 (get_actor a))"
    and "is_output a \<Longrightarrow> \<forall>x. x \<notin> {get_actor a, get_object a} \<longrightarrow> C1(x) = C2(x)"
    and "is_input a \<Longrightarrow> \<forall>x. x \<noteq> get_actor a \<longrightarrow> C1(x) = C2(x)"
  using assms
proof induct
  case (MboxSend C1 a i p q C2 k)
  assume A1: "is_mbox_config C1"
  thus "is_mbox_config C1" .
  assume A2: "a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>"
  thus "\<exists>i p q. a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle> \<or> a = ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>"
    by blast
  assume A3: "fst (C1 p) \<midarrow>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>p (fst (C2 p))"
  with A2 show "fst (C1 (get_actor a)) \<midarrow>a\<rightarrow>(get_actor a) (fst (C2 (get_actor a)))"
    by simp
  have A4: "CommunicatingAutomaton p (\<S> p) (\<I> p) \<M> (\<R> p)"
    using automaton_of_peer[of p]
    by simp
  with A2 A3 show "get_actor a \<noteq> get_object a"
    using CommunicatingAutomaton.well_formed_transition[of p "\<S> p" "\<I> p" \<M> "\<R> p" "fst (C1 p)" a
            "fst (C2 p)"]
    by auto
  assume A5: "snd (C1 p) = snd (C2 p)"
  with A2 show "is_output a \<Longrightarrow> snd (C1 (get_actor a)) = snd (C2 (get_actor a))"
    by simp
  assume "( |snd (C1 q)| ) <\<^sub>\<B> k"
  with A2 show "is_output a \<Longrightarrow> ( | (snd (C1 (get_object a))) | ) <\<^sub>\<B> k"
    by simp
  assume A6: "C2 q = (fst (C1 q), snd (C1 q) \<cdot> [i\<^bsup>p\<rightarrow>q\<^esup>])"
  with A2 show "is_output a \<Longrightarrow> C2 (get_object a) =
                (fst (C1 (get_object a)), (snd (C1 (get_object a))) \<cdot> [get_message a])"
    by simp
  from A2 show "is_input a \<Longrightarrow> (snd (C1 (get_actor a))) = [get_message a] \<cdot> snd (C2 (get_actor a))"
    by simp
  assume A7: "\<forall>x. x \<notin> {p, q} \<longrightarrow> C1 x = C2 x"
  with A2 show "is_output a \<Longrightarrow> \<forall>x. x \<notin> {get_actor a, get_object a} \<longrightarrow> C1(x) = C2(x)"
    by simp
  from A2 show "is_input a \<Longrightarrow> \<forall>x. x \<noteq> get_actor a \<longrightarrow> C1(x) = C2(x)"
    by simp
  show "is_mbox_config C2"
    unfolding is_mbox_config_def
  proof clarify
    fix x :: "'peer"
    show "fst (C2 x) \<in> \<S>(x) \<and> snd (C2 x) \<in> \<M>\<^sup>*"
    proof (cases "x = p")
      assume B: "x = p"
      with A3 A4 have "fst (C2 x) \<in> \<S>(x)"
        using CommunicatingAutomaton.well_formed_transition[of p "\<S> p" "\<I> p" \<M> "\<R> p" "fst (C1 p)"
                "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" "fst (C2 p)"]
        by simp
      moreover from A1 A5 B have "snd (C2 x) \<in> \<M>\<^sup>*"
        unfolding is_mbox_config_def
        by metis
      ultimately show "fst (C2 x) \<in> \<S>(x) \<and> snd (C2 x) \<in> \<M>\<^sup>*"
        by simp
    next
      assume B: "x \<noteq> p"
      show "fst (C2 x) \<in> \<S>(x) \<and> snd (C2 x) \<in> \<M>\<^sup>*"
      proof (cases "x = q")
        assume "x = q"
        moreover from A1 A6 have "fst (C2 q) \<in> \<S>(q)"
          unfolding is_mbox_config_def
          by simp
        moreover from A3 A4 have "i\<^bsup>p\<rightarrow>q\<^esup> \<in> \<M>"
          using CommunicatingAutomaton.well_formed_transition[of p "\<S> p" "\<I> p" \<M> "\<R> p"
                  "fst (C1 p)" "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" "fst (C2 p)"]
          by simp
        with A1 A6 have "snd (C2 q) \<in> \<M>\<^sup>*"
          unfolding is_mbox_config_def
          using message_alphabet Alphabet.EmptyWord[of \<M>] Alphabet.Composed[of \<M> "i\<^bsup>p\<rightarrow>q\<^esup>" \<epsilon>]
                Alphabet.concat_words_over_an_alphabet[of \<M> "snd (C1 q)" "[i\<^bsup>p\<rightarrow>q\<^esup>]"]
          by simp
        ultimately show "fst (C2 x) \<in> \<S>(x) \<and> snd (C2 x) \<in> \<M>\<^sup>*"
          by simp
      next
        assume "x \<noteq> q"
        with A1 A7 B show "fst (C2 x) \<in> \<S>(x) \<and> snd (C2 x) \<in> \<M>\<^sup>*"
          unfolding is_mbox_config_def
          by (metis insertE singletonD)
      qed
    qed
  qed
next
  case (MboxRecv C1 a i p q C2 k)
  assume A1: "is_mbox_config C1"
  thus "is_mbox_config C1" .
  assume A2: "a = ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>"
  thus "\<exists>i p q. a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle> \<or> a = ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>"
    by blast
  assume A3: "fst (C1 q) \<midarrow>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>q (fst (C2 q))"
  with A2 show "fst (C1 (get_actor a)) \<midarrow>a\<rightarrow>(get_actor a) (fst (C2 (get_actor a)))"
    by simp
  have A4: "CommunicatingAutomaton q (\<S> q) (\<I> q) \<M> (\<R> q)"
    using automaton_of_peer[of q]
    by simp
  with A2 A3 show "get_actor a \<noteq> get_object a"
    using CommunicatingAutomaton.well_formed_transition[of q "\<S> q" "\<I> q" \<M> "\<R> q" "fst (C1 q)" a
            "fst (C2 q)"]
    by auto
  from A2 show "is_output a \<Longrightarrow> snd (C1 (get_actor a)) = snd (C2 (get_actor a))"
    by simp
  from A2 show "is_output a \<Longrightarrow> ( | (snd (C1 (get_object a))) | ) <\<^sub>\<B> k"
    by simp
  from A2 show "is_output a \<Longrightarrow> C2 (get_object a) =
                (fst (C1 (get_object a)), (snd (C1 (get_object a))) \<cdot> [get_message a])"
    by simp
  assume A5: "snd (C1 q) = [i\<^bsup>p\<rightarrow>q\<^esup>] \<cdot> snd (C2 q)"
  with A2 show "is_input a \<Longrightarrow> (snd (C1 (get_actor a))) = [get_message a] \<cdot> snd (C2 (get_actor a))"
    by simp
  from A2 show "is_output a \<Longrightarrow> \<forall>x. x \<notin> {get_actor a, get_object a} \<longrightarrow> C1(x) = C2(x)"
    by simp
  assume A6: "\<forall>x. x \<noteq> q \<longrightarrow> C1 x = C2 x"
  with A2 show "is_input a \<Longrightarrow> \<forall>x. x \<noteq> get_actor a \<longrightarrow> C1(x) = C2(x)"
    by simp
  show "is_mbox_config C2"
    unfolding is_mbox_config_def
  proof clarify
    fix x :: "'peer"
    show "fst (C2 x) \<in> \<S>(x) \<and> snd (C2 x) \<in> \<M>\<^sup>*"
    proof (cases "x = q")
      assume B: "x = q"
      with A3 A4 have "fst (C2 x) \<in> \<S>(x)"
        using CommunicatingAutomaton.well_formed_transition[of q "\<S> q" "\<I> q" \<M> "\<R> q" "fst (C1 q)"
                "?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" "fst (C2 q)"]
        by simp
      moreover from A3 A4 have "i\<^bsup>p\<rightarrow>q\<^esup> \<in> \<M>"
        using CommunicatingAutomaton.well_formed_transition[of q "\<S> q" "\<I> q" \<M> "\<R> q" "fst (C1 q)"
                "?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" "fst (C2 q)"]
        by simp
      with A1 A5 B have "snd (C2 x) \<in> \<M>\<^sup>*"
        unfolding is_mbox_config_def
        using message_alphabet
              Alphabet.split_a_word_over_an_alphabet(2)[of \<M> "[i\<^bsup>p\<rightarrow>q\<^esup>]" "snd (C2 q)"]
        by metis
      ultimately show "fst (C2 x) \<in> \<S>(x) \<and> snd (C2 x) \<in> \<M>\<^sup>*"
        by simp
    next
      assume "x \<noteq> q"
      with A1 A6 show "fst (C2 x) \<in> \<S>(x) \<and> snd (C2 x) \<in> \<M>\<^sup>*"
        unfolding is_mbox_config_def
        by metis
    qed
  qed
qed

lemma mbox_step_output_rev:
  fixes C1 C2 :: "'peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)"
    and i     :: "'information"
    and p q   :: "'peer"
    and k     :: "bound"
  assumes "mbox_step C1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) k C2"
  shows "is_mbox_config C1" and "is_mbox_config C2" and "p \<noteq> q"
    and "fst (C1 p) \<midarrow>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>p (fst (C2 p))" and "snd (C1 p) = snd (C2 p)"
    and "( | (snd (C1 q)) | ) <\<^sub>\<B> k"
    and "C2 q = (fst (C1 q), (snd (C1 q)) \<cdot> [get_message (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)])"
    and "\<forall>x. x \<notin> {p, q} \<longrightarrow> C1(x) = C2(x)"
proof -
  show "is_mbox_config C1"
    using assms mbox_step_rev(1)[of C1 "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" k C2]
    by simp
  show "is_mbox_config C2"
    using assms mbox_step_rev(2)[of C1 "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" k C2]
    by simp
  show "p \<noteq> q"
    using assms mbox_step_rev(4)[of C1 "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" k C2]
    by simp
  show "fst (C1 p) \<midarrow>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>p (fst (C2 p))"
    using assms mbox_step_rev(5)[of C1 "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" k C2]
    by simp
  show "snd (C1 p) = snd (C2 p)"
    using assms mbox_step_rev(6)[of C1 "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" k C2]
    by simp
  show "( | (snd (C1 q)) | ) <\<^sub>\<B> k"
    using assms mbox_step_rev(7)[of C1 "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" k C2]
    by fastforce
  show "C2 q = (fst (C1 q), (snd (C1 q)) \<cdot> [get_message (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)])"
    using assms mbox_step_rev(8)[of C1 "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" k C2]
    by simp
  show "\<forall>x. x \<notin> {p, q} \<longrightarrow> C1(x) = C2(x)"
    using assms mbox_step_rev(10)[of C1 "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" k C2]
    by simp
qed

lemma mbox_step_input_rev:
  fixes C1 C2 :: "'peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)"
    and i     :: "'information"
    and p q   :: "'peer"
    and k     :: "bound"
  assumes "mbox_step C1 (?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) k C2"
  shows "is_mbox_config C1" and "is_mbox_config C2" and "p \<noteq> q"
    and "fst (C1 q) \<midarrow>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>q (fst (C2 q))" and "(snd (C1 q)) = [i\<^bsup>p\<rightarrow>q\<^esup>] \<cdot> snd (C2 q)"
    and "\<forall>x. x \<noteq> q \<longrightarrow> C1(x) = C2(x)"
  using assms mbox_step_rev[of C1 "?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" k C2]
  by simp_all


abbreviation mbox_step_bounded
  :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> ('information, 'peer) action \<Rightarrow>
      nat \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> bool"
     ("_ \<midarrow>\<langle>_, _\<rangle>\<rightarrow> _" [90, 90, 90, 90] 110) where
  "C1 \<midarrow>\<langle>a, n\<rangle>\<rightarrow> C2 \<equiv> mbox_step C1 a (Some n) C2"

abbreviation mbox_step_unbounded
  :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> ('information, 'peer) action \<Rightarrow>
      ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> bool"
     ("_ \<midarrow>\<langle>_, \<infinity>\<rangle>\<rightarrow> _" [90, 90, 90] 110) where
  "C1 \<midarrow>\<langle>a, \<infinity>\<rangle>\<rightarrow> C2 \<equiv> mbox_step C1 a None C2"

\<comment> \<open>if mbox can take a bounded step, it can also take an unbounded step\<close>
lemma mbox_step_inclusion :
  assumes "mbox_step C1 a (Some k) C2"
  shows "mbox_step C1 a None C2"
  by (smt (verit) MboxRecv MboxSend NetworkOfCA.mbox_step_input_rev(6) NetworkOfCA_axioms assms
      get_actor.simps(1,2) get_message.simps(1,2) get_object.simps(1) get_receiver.simps
      get_sender.simps is_bounded.simps(1) is_output.simps(1,2) mbox_step_output_rev(5)
      mbox_step_rev(1,10,3,5,8,9) these_empty)



lemma send_step_to_mbox_step:
  assumes "[a] \<in> \<L> p" and "is_output a"
  shows "\<exists>C. \<C>\<^sub>\<I>\<^sub>\<mm> \<midarrow>\<langle>a, \<infinity>\<rangle>\<rightarrow> C"
  using assms 
proof -
  obtain s2 where s2_def: "(\<I> p, a, s2) \<in> \<R> p"  by (meson assms(1) lang_implies_run lang_implies_trans)
  then obtain q i where a_def: "a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" 
    by (metis CommunicatingAutomaton_def action.exhaust assms(2) automaton_of_peer
        get_actor.simps(1) get_sender.simps is_output.simps(2) message.exhaust) 
  then have "p \<noteq> q" by (metis CommunicatingAutomaton.well_formed_transition
        \<open>\<And>thesis. (\<And>s2. \<C>\<^sub>\<I>\<^sub>\<zero> p \<midarrow>a\<rightarrow>p s2 \<Longrightarrow> thesis) \<Longrightarrow> thesis\<close> automaton_of_peer
        get_object.simps(1) get_receiver.simps)
  let ?C0 = "(\<C>\<^sub>\<I>\<^sub>\<mm>)(p := (s2, \<epsilon>))"
  let ?C = "(?C0)(q := (\<I> q, [(i\<^bsup>p\<rightarrow>q\<^esup>)]))"
  have "is_mbox_config ?C" by (smt (verit) Alphabet.WordsOverAlphabet.simps CommunicatingAutomaton.well_formed_transition
        a_def automaton_of_peer fun_upd_apply get_message.simps(1)
        initial_configuration_is_synchronous_configuration is_mbox_config_def is_sync_config_def
        message_alphabet s2_def snd_conv split_pairs)
  then have C_prop: "\<forall>x. x \<notin> {p, q} \<longrightarrow> \<C>\<^sub>\<I>\<^sub>\<mm>(x) = ?C(x)" by simp
  then have "fst (\<C>\<^sub>\<I>\<^sub>\<mm> p) = \<I> p" by auto
  then have "fst (?C p) = s2" by (simp add: \<open>p \<noteq> q\<close>)
have "(\<I> p) \<midarrow>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>p s2" using a_def s2_def by auto
have "is_mbox_config \<C>\<^sub>\<I>\<^sub>\<mm>" by (simp add: initial_configuration_is_mailbox_configuration)
  have "fst (\<C>\<^sub>\<I>\<^sub>\<mm> p) \<midarrow>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>p (fst (?C p))" 
    using \<open>fst (((\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)) (p := (s2, \<epsilon>), q := (\<C>\<^sub>\<I>\<^sub>\<zero> q, i\<^bsup>p\<rightarrow>q\<^esup> # \<epsilon>))) p) = s2\<close> a_def
      s2_def by auto
then have C_prop2: "snd (\<C>\<^sub>\<I>\<^sub>\<mm> p) = snd (?C p)"  by (simp add: \<open>p \<noteq> q\<close>)
then have  C_prop3: "?C q = (fst ( \<C>\<^sub>\<I>\<^sub>\<mm> q), (snd ( \<C>\<^sub>\<I>\<^sub>\<mm> q)) \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)])" by simp
  then have "mbox_step \<C>\<^sub>\<I>\<^sub>\<mm> a None ?C" 
    using C_prop2 MboxSend
      \<open>fst (((\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)) (p := (s2, \<epsilon>), q := (\<C>\<^sub>\<I>\<^sub>\<zero> q, i\<^bsup>p\<rightarrow>q\<^esup> # \<epsilon>))) p) = s2\<close> a_def
      initial_configuration_is_mailbox_configuration s2_def by force
  then show ?thesis by auto
qed




lemma gen_send_step_to_mbox_step:
  assumes "(s1, !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, s2) \<in> \<R> p"  and "fst (C0 p) = s1" and "fst (C1 p) = s2"
and "snd (C0 p) = snd (C1 p)" and "C1 q = (fst ( C0 q), (snd ( C0 q)) \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)])"  and "is_mbox_config C0"
and "\<forall>x. x \<notin> {p, q} \<longrightarrow> C0(x) = C1(x)"  
shows "C0 \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> C1"
  using assms
proof auto
  have "fst (C0 p) \<midarrow>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>p (fst (C1 p))" by (simp add: assms(1,2,3))
  have all: "is_mbox_config C0 \<and> fst (C0 p) \<midarrow>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>p (fst (C1 p)) \<and>
            snd (C0 p) = snd (C1 p) \<and> ( | (snd (C0 q)) | ) <\<^sub>\<B> None \<and> 
            C1 q = (fst (C0 q), (snd (C0 q)) \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)]) \<and> (\<forall>x. x \<notin> {p, q} \<longrightarrow> C0(x) = C1(x))"
    using assms by auto
  show ?thesis  by (simp add: NetworkOfCA.MboxSend NetworkOfCA_axioms all)
qed

lemma valid_send_to_p_not_q : 
  assumes "(s1, !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, s2) \<in> \<R> p"
  shows "p \<noteq> q"
  by (metis CommunicatingAutomaton.well_formed_transition assms automaton_of_peer
      get_object.simps(1) get_receiver.simps)

lemma valid_recv_to_p_not_q : 
  assumes "(s1, ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, s2) \<in> \<R> p"
  shows "p \<noteq> q"
  by (metis CommunicatingAutomaton_def NetworkOfCA.automaton_of_peer NetworkOfCA_axioms assms
      get_object.simps(2) get_sender.simps)

\<comment> \<open>define the mbox step for a given send step (of e.g. a root)\<close>
lemma send_trans_to_mbox_step :
assumes "(s1, !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, s2) \<in> \<R> p" and "is_mbox_config C0" and "fst (C0 p) = s1"
shows "let p_buf = snd (C0 p); C1 = (C0)(p := (s2, p_buf)); q0 = fst (C0 q); q_buf = snd (C0 q); 
  C2 = (C1)(q := (q0, q_buf \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)])) in 
mbox_step C0 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None C2" 
  using assms 
proof -
  let ?p_buf = "snd (C0 p)"
  let ?C1 = "(C0)(p := (s2, ?p_buf))"
  let ?q0 = "fst (C0 q)"
  let ?q_buf = "snd (C0 q)"
  let ?C2 = "(?C1)(q := (?q0, ?q_buf \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)]))"
  have "q \<noteq> p" using assms(1) valid_send_to_p_not_q by blast
  have m1: "snd (C0 p) = snd (?C2 p)" using \<open>q \<noteq> p\<close> by auto
  have m2: "fst (C0 p) \<midarrow>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>p (fst (?C2 p))" using \<open>q \<noteq> p\<close> assms(1,3) by fastforce
  have m3: "?C2 q = (fst (C0 q), (snd (C0 q)) \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)])" by simp
  have m4: " (\<forall>x. x \<notin> {p, q} \<longrightarrow> C0(x) = ?C2(x))" by simp
  have m5: "( | (snd (C0 q)) | ) <\<^sub>\<B> None" by simp
  have "mbox_step C0 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None ?C2" using assms(2) gen_send_step_to_mbox_step m1 m2 m3 m4 by blast
  then show ?thesis by auto
qed


inductive mbox_run
  :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> bound \<Rightarrow>
      ('information, 'peer) action word \<Rightarrow>
      ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) list \<Rightarrow> bool" where
MREmpty:       "mbox_run C k \<epsilon> ([])" |
MRComposedNat: "\<lbrakk>mbox_run C0 (Some k) w xc; last (C0#xc) \<midarrow>\<langle>a, k\<rangle>\<rightarrow> C\<rbrakk> \<Longrightarrow>
                mbox_run C0 (Some k) (w\<cdot>[a]) (xc@[C])" |
MRComposedInf: "\<lbrakk>mbox_run C0 None w xc; last (C0#xc) \<midarrow>\<langle>a, \<infinity>\<rangle>\<rightarrow> C\<rbrakk> \<Longrightarrow>
                mbox_run C0 None (w\<cdot>[a]) (xc@[C])"

lemma mbox_run_rev_unbound :
  assumes "mbox_run C0 None (w\<cdot>[a]) (xc@[C])"
  shows "mbox_run C0 None w xc \<and> last (C0#xc) \<midarrow>\<langle>a, \<infinity>\<rangle>\<rightarrow> C"
  by (smt (verit) Nil_is_append_conv append1_eq_conv assms mbox_run.simps
      not_Cons_self2)

lemma mbox_run_rev_bound :
  assumes "mbox_run C0 (Some k) (w\<cdot>[a]) (xc@[C])"
  shows "mbox_run C0 (Some k) w xc \<and> last (C0#xc) \<midarrow>\<langle>a, k\<rangle>\<rightarrow> C"
  by (smt (verit) Nil_is_append_conv append1_eq_conv assms mbox_run.simps
      not_Cons_self2)

lemma run_produces_mailbox_configurations:
  fixes C C' :: "'peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)"
    and k    :: "bound"
    and w    :: "('information, 'peer) action word"
    and xc   :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) list"
  assumes "mbox_run C k w xc"
      and "C' \<in> set xc"
    shows "is_mbox_config C'"
  using assms
proof induct
  case (MREmpty C k)
  assume "C' \<in> set []"
  hence False
    by simp
  thus "is_mbox_config C'"
    by simp
next
  case (MRComposedNat C0 k w xc a C)
  assume A1: "C' \<in> set xc \<Longrightarrow> is_mbox_config C'" and A2: "last (C0#xc) \<midarrow>\<langle>a, k\<rangle>\<rightarrow> C"
     and A3: "C' \<in> set (xc \<cdot> [C])"
  show "is_mbox_config C'"
  proof (cases "C = C'")
    assume "C = C'"
    with A2 show "is_mbox_config C'"
      using mbox_step_rev(2)[of "last (C0#xc)" a "Some k" C]
      by simp
  next
    assume "C \<noteq> C'"
    with A1 A3 show "is_mbox_config C'"
      by simp
  qed
next
  case (MRComposedInf C0 w xc a C)
  assume A1: "C' \<in> set xc \<Longrightarrow> is_mbox_config C'" and A2: "last (C0#xc) \<midarrow>\<langle>a, \<infinity>\<rangle>\<rightarrow> C"
     and A3: "C' \<in> set (xc \<cdot> [C])"
  show "is_mbox_config C'"
  proof (cases "C = C'")
    assume "C = C'"
    with A2 show "is_mbox_config C'"
      using mbox_step_rev(2)[of "last (C0#xc)" a None C]
      by simp
  next
    assume "C \<noteq> C'"
    with A1 A3 show "is_mbox_config C'"
      by simp
  qed
qed

lemma mbox_step_to_run:
  assumes "mbox_step C0 a None C" 
  shows "mbox_run C0 None [a] [C]"
  by (metis MRComposedInf MREmpty append.left_neutral assms last_ConsL)

(*
lemma only_sends_run_to_mbox_run:
  assumes "w \<in> \<L> p" and "w = w\<down>\<^sub>!"
  shows "\<exists>xc. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None w xc"
  using assms  
proof (induct "length w" arbitrary: w)
  case 0
  then show ?case using MREmpty by auto
next
  case (Suc x)
  then obtain v a where w_def: "w = v @ [a]" and v_len : "x = length v" and v_L : "v \<in> \<L> p"
    by (metis (no_types, lifting) Lang_app length_Suc_conv_rev)  
  then have "x = |v| \<Longrightarrow> v \<in> \<L> p \<Longrightarrow> v = v\<down>\<^sub>! \<Longrightarrow> Ex (mbox_run (\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)) None v)" 
    by (simp add: Suc.hyps(1))
  then have "v \<in> \<L> p \<Longrightarrow> v = v\<down>\<^sub>! \<Longrightarrow> Ex (mbox_run (\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)) None v)" 
    using v_len by blast
  then have " v = v\<down>\<^sub>! \<Longrightarrow> Ex (mbox_run (\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)) None v)" by (simp add: v_L)
  have "v @ [a] = (v @ [a])\<down>\<^sub>!" using Suc.prems(2) w_def by blast
  then have "v = v\<down>\<^sub>!" 
      proof -
    have f1: "\<forall>as p. \<epsilon> = filter p as \<or> (\<exists>a. p (a::('information, 'peer) action) \<and> a \<in> set as)"
      by (metis (lifting) filter_False)
    have "\<forall>a. a \<notin> set w \<or> is_output a"
      by (metis Suc.prems(2) filter_id_conv)
    then have "\<epsilon> = w\<down>\<^sub>?"
      using f1 by blast
    then have "\<epsilon> = v\<down>\<^sub>?"
      by (simp add: w_def)
    then show ?thesis
      by (simp add: empty_filter_conv)
    qed 
  then obtain xc where v_run: "(mbox_run (\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)) None v xc)" 
    using \<open>v = v\<down>\<^sub>! \<Longrightarrow> Ex (mbox_run (\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)) None v)\<close> by auto
  then have "is_output a" by (metis \<open>v = v\<down>\<^sub>!\<close> \<open>v \<cdot> a # \<epsilon> = (v \<cdot> a # \<epsilon>)\<down>\<^sub>!\<close> append_self_conv filter.simps(2) filter_append
        not_Cons_self2)
  then show ?case using Suc assms 
  proof (cases "v = []")
    case True
    then have "(mbox_run (\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)) None v [])" by (simp add: MREmpty)
    then have "w = [a]" by (simp add: True w_def)
    then have "[a] \<in> \<L> p"  using Suc.prems(1) by auto
    then have "\<exists>C. \<C>\<^sub>\<I>\<^sub>\<mm> \<midarrow>\<langle>a, \<infinity>\<rangle>\<rightarrow> C"  by (simp add: \<open>is_output a\<close> send_step_to_mbox_step)
    then obtain C where C_def: "\<C>\<^sub>\<I>\<^sub>\<mm> \<midarrow>\<langle>a, \<infinity>\<rangle>\<rightarrow> C" by auto
    then have "mbox_step \<C>\<^sub>\<I>\<^sub>\<mm> a None C" by simp
    then have "mbox_run (\<C>\<^sub>\<I>\<^sub>\<mm>) None [a] [C]" by (simp add: mbox_step_to_run)
    then show ?thesis using \<open>w = a # \<epsilon>\<close> by auto
  next
    case False
    then obtain xcs C0 s1  where v_run2: "(mbox_run (\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)) None v xcs)" and xcs_nonemp : "xcs \<noteq> []"
and C0_def: "last xcs = C0"  and s1_def: "fst (C0 p) = s1" 
     by (smt (verit) Nil_is_append_conv mbox_run.simps not_Cons_self2 v_run)
    then have "is_mbox_config C0" using run_produces_mailbox_configurations by force
    have "v @ [a] \<in> \<L> p"  using Suc.prems(1) w_def by auto

--_> Need to show that a is of form !ipq and that the transition s1,a,s2 exists (then with my existing lemmas i can
      show that the mbox step from last config of xcs with a to s2 exists
and in turn that the mboxrun for w a exists

    obtain q i where a_def: "a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" and p_def: "p = get_actor a" and q_def: "q = get_object a"
      sledgehammer
    then obtain s2 where "(s1, a, s2) \<in> \<R> p"
      sorry

    then have "\<exists>C1. C0 \<midarrow>\<langle>a, \<infinity>\<rangle>\<rightarrow> C1" sledgehammer
    then have "\<exists>C1. mbox_step C0 a None C1" sledgehammer

    then obtain s2 where a_trans: "(s1, a, s2) \<in> \<R> p" 
    sledgehammer 
  then obtain q i where a_def: "a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" 
    let ?C0 = "(last xc)"
    let ?p_buf = "snd (?C0 p)"
    let ?C1 = "(?C0)(p := (s2, ?p_buf))"
    let ?q0 = "fst (?C0 q)"
    let ?q_buf = "snd (?C0 q)"
    let ?C2 = "(?C1)(q := (?q0, ?q_buf \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)]))"
    have p_buf_def: "?p_buf = snd (?C0 p)" by simp
    have C1_def : "?C1 = (?C0)(p := (s2, ?p_buf))" by simp
    have q0_def : "?q0 = fst (?C0 q)" by simp
    have q_buf_def : "?q_buf = snd (?C0 q)" by simp
    have C2_def: "?C2 = (?C1)(q := (?q0, ?q_buf \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)]))" by simp
    have "q \<noteq> p" using assms(1) valid_send_to_p_not_q by blast
    then show ?thesis sorry
  qed
 
  
    by (metis CommunicatingAutomaton_def action.exhaust assms(2) automaton_of_peer
        get_actor.simps(1) get_sender.simps is_output.simps(2) message.exhaust) 
  then have "get_actor a = p" sledgehammer
  then obtain i q where a_def: "a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" sledgehammer 
  then show ?case sledgehammer
qed
*)

\<comment> \<open>E(mbox)\<close>
inductive_set MboxTraces
  :: "nat option \<Rightarrow> ('information, 'peer) action language"  ("\<T>\<^bsub>_\<^esub>" [100] 120)
  for k :: "nat option" where
MTRun: "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> k w xc \<Longrightarrow> w \<in> \<T>\<^bsub>k\<^esub>"

lemma Mbox_Traces_rev :
  assumes "w \<in> \<T>\<^bsub>k\<^esub>"
  shows "\<exists> xc. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> k w xc"
  by (metis MboxTraces.cases assms)

lemma mbox_run_inclusion:
  assumes "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> (Some k) w xc"
  shows "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None w xc"
  using assms
proof (induct rule: mbox_run.induct)
  case (MREmpty C k)
  then show ?case  by (simp add: mbox_run.MREmpty)
next
  case (MRComposedNat C0 k w xc a C)
  then show ?case by (simp add: MRComposedInf mbox_step_inclusion)
next
  case (MRComposedInf C0 w xc a C)
  then show ?case by (simp add: mbox_run.MRComposedInf)
qed

lemma mbox_bounded_lang_inclusion :
  shows "\<T>\<^bsub>(Some k)\<^esub> \<subseteq> \<T>\<^bsub>None\<^esub>"
  using MboxTraces_def MboxTracesp.simps mbox_run_inclusion by fastforce

\<comment> \<open>T(mbox)\<close>
abbreviation MboxLang :: "bound \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^bsub>_\<^esub>" [100] 120)
  where
  "\<L>\<^bsub>k\<^esub> \<equiv> { w\<down>\<^sub>! | w. w \<in> \<T>\<^bsub>k\<^esub> }"

abbreviation MboxLang_bounded_by_one :: "('information, 'peer) action language"  ("\<L>\<^sub>\<one>" 120) where
  "\<L>\<^sub>\<one> \<equiv> \<L>\<^bsub>\<B> 1\<^esub>"

abbreviation MboxLang_unbounded :: "('information, 'peer) action language"  ("\<L>\<^sub>\<infinity>" 120) where
  "\<L>\<^sub>\<infinity> \<equiv> \<L>\<^bsub>\<infinity>\<^esub>"

abbreviation MboxLangSend :: "bound \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>!\<^bsub>_\<^esub>" [100] 120)
  where
  "\<L>\<^sub>!\<^bsub>k\<^esub> \<equiv> (\<L>\<^bsub>k\<^esub>)\<downharpoonright>\<^sub>!"

abbreviation MboxLangRecv :: "bound \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>?\<^bsub>_\<^esub>" [100] 120)
  where
  "\<L>\<^sub>?\<^bsub>k\<^esub> \<equiv> (\<L>\<^bsub>k\<^esub>)\<downharpoonright>\<^sub>?"

lemma execution_implies_mbox_trace :
  assumes "w \<in> \<T>\<^bsub>k\<^esub>"
  shows "w\<down>\<^sub>! \<in> \<L>\<^bsub>k\<^esub>"
  using assms by blast
lemma mbox_trace_implies_execution :
  assumes "w \<in> \<L>\<^bsub>k\<^esub>"
  shows "\<exists>w'. w'\<down>\<^sub>! = w \<and> w' \<in> \<T>\<^bsub>k\<^esub>"
using assms by blast

subsubsection \<open>Language Hierarchy\<close>

theorem sync_word_in_mbox_size_one:
  shows "\<L>\<^sub>\<zero> \<subseteq> \<L>\<^sub>\<one>"
proof clarify
  fix v :: "('information, 'peer) action word"
  assume "v \<in> \<L>\<^sub>\<zero>"
  then obtain xcs C0 where "sync_run C0 v xcs" and "C0 = \<C>\<^sub>\<I>\<^sub>\<zero>"
    using SyncTracesp.simps SyncTracesp_SyncTraces_eq
    by auto
  hence "\<exists>w xcm. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> (\<B> 1) w xcm \<and> v = w\<down>\<^sub>! \<and>
         (\<forall>p. last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm) p = (last (\<C>\<^sub>\<I>\<^sub>\<zero>#xcs) p, \<epsilon>))"
  proof induct
    case (SREmpty C)
    have "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> (\<B> 1) \<epsilon> []"
      using MREmpty[of \<C>\<^sub>\<I>\<^sub>\<mm> "\<B> 1"]
      by simp
    moreover have "\<epsilon> = \<epsilon>\<down>\<^sub>!"
      by simp
    moreover have "\<forall>p. \<C>\<^sub>\<I>\<^sub>\<mm> p = (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)"
      by simp
    ultimately show "\<exists>w xcm. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> (\<B> 1) w xcm \<and> \<epsilon> = w\<down>\<^sub>! \<and>
                     (\<forall>p. last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm) p = (last [\<C>\<^sub>\<I>\<^sub>\<zero>] p, \<epsilon>))"
      by fastforce
  next
    case (SRComposed C0 v xc a C)
    assume "C0 = \<C>\<^sub>\<I>\<^sub>\<zero> \<Longrightarrow> \<exists>w xcm. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> (\<B> 1) w xcm \<and> v = w\<down>\<^sub>! \<and>
            (\<forall>p. last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm) p = (last (\<C>\<^sub>\<I>\<^sub>\<zero>#xc) p, \<epsilon>))"
       and B1: "C0 = \<C>\<^sub>\<I>\<^sub>\<zero>"
    then obtain w xcm where B2: "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> (\<B> 1) w xcm" and B3: "v = w\<down>\<^sub>!"
                        and B4: "\<forall>p. last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm) p = (last (\<C>\<^sub>\<I>\<^sub>\<zero>#xc) p, \<epsilon>)"
      by blast
    assume "last (C0#xc) \<midarrow>\<langle>a, \<zero>\<rangle>\<rightarrow> C"
    with B1 obtain C1 where B5: "C1 = last (\<C>\<^sub>\<I>\<^sub>\<zero>#xc)" and B6: "C1 \<midarrow>\<langle>a, \<zero>\<rangle>\<rightarrow> C"
      by blast
    from B6 obtain i p q where B7: "a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" and B8: "C1 p \<midarrow>a\<rightarrow>p (C p)"
                           and B9: "C1 q \<midarrow>(?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>q (C q)" and B10: "p \<noteq> q"
                           and B11: "\<forall>x. x \<notin> {p, q} \<longrightarrow> C1 x = C x"
      using sync_step_rev[of C1 a C]
      by auto
    define C2::"'peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)" where
      C2_def: "C2 \<equiv> \<lambda>x. if x = p then (C p, \<epsilon>) else (C1 x, if x = q then [i\<^bsup>p\<rightarrow>q\<^esup>] else \<epsilon>)"
    define C3::"'peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)" where
      C3_def: "C3 \<equiv> \<lambda>x. (C x, \<epsilon>)"
    from B2 have "is_mbox_config (last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm))"
      using run_produces_mailbox_configurations[of \<C>\<^sub>\<I>\<^sub>\<mm> "\<B> 1" w xcm "last xcm"]
            initial_configuration_is_mailbox_configuration
      by simp
    moreover from B4 B5 B7 B8 have "fst (last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm) p) \<midarrow>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>p (fst (C2 p))"
      unfolding C2_def
      by simp
    moreover from B4 have "snd (last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm) p) = snd (C2 p)"
      unfolding C2_def
      by simp
    moreover from B4 have "( | snd (last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm) q) | ) <\<^sub>\<B> \<B> 1"
      by simp
    moreover from B4 B5 B10
    have "C2 q = (fst (last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm) q), snd (last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm) q) \<cdot> [i\<^bsup>p\<rightarrow>q\<^esup>])"
      unfolding C2_def
      by simp
    moreover from B4 B5 have "\<forall>x. x \<notin> {p, q} \<longrightarrow> last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm) x = C2 x"
      unfolding C2_def
      by simp
    ultimately have B12: "last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm) \<midarrow>\<langle>a, 1\<rangle>\<rightarrow> C2"
      using B7 MboxSend[of "last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm)" "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" i p q C2 "\<B> 1"]
      by simp
    hence "is_mbox_config C2"
      using mbox_step_rev(2)[of "last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm)" a "\<B> 1" C2]
      by simp
    moreover from B9 B10 have "fst (C2 q) \<midarrow>(?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>q (fst (C3 q))"
      unfolding C2_def C3_def
      by simp
    moreover from B10 have "snd (C2 q) = [i\<^bsup>p\<rightarrow>q\<^esup>] \<cdot> snd (C3 q)"
      unfolding C2_def C3_def
      by simp
    moreover from B11 have "\<forall>x. x \<noteq> q \<longrightarrow> C2 x = C3 x"
      unfolding C2_def C3_def
      by simp
    ultimately have "C2 \<midarrow>\<langle>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, 1\<rangle>\<rightarrow> C3"
      using MboxRecv[of C2 "?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" i p q C3 "\<B> 1"]
      by simp
    with B2 B12 have "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> (\<B> 1) (w\<cdot>[a, ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>]) (xcm\<cdot>[C2, C3])"
      using MRComposedNat[of \<C>\<^sub>\<I>\<^sub>\<mm> 1 w xcm a C2]
            MRComposedNat[of \<C>\<^sub>\<I>\<^sub>\<mm> 1 "w\<cdot>[a]" "xcm\<cdot>[C2]" "?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" C3]
      by simp
    moreover from B3 B7 have "v\<cdot>[a] = (w\<cdot>[a, ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>])\<down>\<^sub>!"
      using filter_append[of is_output w "[a, ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>]"]
      by simp
    moreover have "\<forall>p. last (\<C>\<^sub>\<I>\<^sub>\<mm>#(xcm\<cdot>[C2, C3])) p = (last (\<C>\<^sub>\<I>\<^sub>\<zero>#(xc\<cdot>[C])) p, \<epsilon>)"
      unfolding C3_def
      by simp
    ultimately show "\<exists>w xcm. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> (\<B> 1) w xcm \<and> v\<cdot>[a] = w\<down>\<^sub>! \<and>
                     (\<forall>p. last (\<C>\<^sub>\<I>\<^sub>\<mm>#xcm) p = (last (\<C>\<^sub>\<I>\<^sub>\<zero>#(xc\<cdot>[C])) p, \<epsilon>))"
      by blast
  qed
  then obtain w xcm where A1: "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> (\<B> 1) w xcm" and A2: "v = w\<down>\<^sub>!"
    by blast
  from A1 have "w \<in> \<T>\<^bsub>\<B> 1\<^esub>"
    by (simp add: MboxTraces.intros)
  with A2 show "\<exists>w. v = w\<down>\<^sub>! \<and> w \<in> \<T>\<^bsub>\<B> 1\<^esub>"
    by blast
qed

lemma mbox_sync_lang_unbounded_inclusion:
  shows "\<L>\<^sub>\<zero> \<subseteq> \<L>\<^sub>\<infinity>"
  using NetworkOfCA.mbox_bounded_lang_inclusion NetworkOfCA_axioms sync_word_in_mbox_size_one
  by force


\<comment> \<open>C1 ->send-> C1(p:= (C2 p)) ->recv\<rightarrow> C2\<close>
\<comment> \<open>shows that a sync step can be simulated with two Mbox steps\<close>
lemma sync_step_to_mbox_steps:
  assumes "C1 \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<zero>\<rangle>\<rightarrow> C2" 
  shows "let c1 = \<lambda>x. (C1 x, \<epsilon>); c3 = \<lambda>x. (C2 x, \<epsilon>); c2 = (c3)(q := (C1 q, [(i\<^bsup>p\<rightarrow>q\<^esup>)])) in
  mbox_step c1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c2 \<and> mbox_step c2 (?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c3"
proof -  \<comment> \<open>C1 -> C2 in sync means we have c1 -> c2 -> c3 in mbox, where in c2 the message is in the mbox of the respective peer\<close> 
  let ?c1 = "\<lambda>x. (C1 x, \<epsilon>)" \<comment> \<open>C1 as mbox config \<close>
  let ?c3 = "\<lambda>x. (C2 x, \<epsilon>)" \<comment> \<open>C2 as mbox config \<close>
  let ?c2 = "(?c3)(q := (C1 q, [(i\<^bsup>p\<rightarrow>q\<^esup>)]))" \<comment> \<open>additional step in mbox that isnt there in sync (sequential vs synchronously)\<close>
  let ?a = "!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>"
  have O1: "(C1 p) \<midarrow>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>p (C2 p)" by (simp add: assms sync_step_output_rev(4))
  then have "(C1 q) \<midarrow>(?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>q (C2 q)" by (simp add: assms sync_step_output_rev(5))
  then have " \<forall>x. x \<notin> {p, q} \<longrightarrow> C1(x) = C2(x)" using assms sync_step_output_rev(6) by blast
  then have S0: "fst (?c2 p) = C2 p"  using assms sync_step_output_rev(3) by auto
  then have S1: "is_mbox_config ?c1"  using assms sync_config_to_mbox sync_step_rev(1) by blast
  then have S2: "fst (?c1 p) \<midarrow>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>p (fst (?c2 p))"  using O1 S0 by auto
  then have S3: "snd (?c1 p) = snd (?c2 p)" using assms sync_step_output_rev(3) by auto
  then have S4: "( | (snd (?c1 q)) | ) <\<^sub>\<B> None" by simp
  then have S5: "?c2 q = (fst (?c1 q), (snd (?c1 q)) \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)])"  by simp
  then have S6: "(\<forall>x. x \<notin> {p, q} \<longrightarrow> ?c1(x) = ?c2(x))" by (simp add: \<open>\<forall>x. x \<notin> {p, q} \<longrightarrow> C1 x = C2 x\<close>)
  then have "is_mbox_config ?c1 \<and> ?a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle> \<and> fst (?c1 p) \<midarrow>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>p (fst (?c2 p)) \<and>
            snd (?c1 p) = snd (?c2 p) \<and> ( | (snd (?c1 q)) | ) <\<^sub>\<B> None \<and>
            ?c2 q = (fst (?c1 q), (snd (?c1 q)) \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)]) \<and> (\<forall>x. x \<notin> {p, q} \<longrightarrow> ?c1(x) = ?c2(x))" 
  using S1 S2 S3 S4 S5 by blast  
  then have mbox_step_1 : "mbox_step ?c1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None ?c2"  using MboxSend by blast
  \<comment> \<open>we have shown that mbox takes a send step from ?c1 to ?c2, now we need to show the receive step\<close>

  have R1 : "is_mbox_config ?c2" using mbox_step_1 mbox_step_rev(2) by auto
  then have R2 : "fst (?c2 q) = C1 q" by simp
  then have R3 : "fst (?c3 q) = C2 q" by simp
  then have R4 : "fst (?c2 q) \<midarrow>(?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>q (fst (?c3 q))" using R2 R3 \<open>(C1 q) \<midarrow>(?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>q (C2 q)\<close> by simp
  then have R5: "(snd (?c2 q)) = [(i\<^bsup>p\<rightarrow>q\<^esup>)] \<cdot> snd (?c3 q)" by simp 
  then have R6: "\<forall>x. x \<noteq> q \<longrightarrow> ?c2(x) = ?c3(x)" by simp
  then have "is_mbox_config ?c2 \<and> fst (?c2 q) \<midarrow>(?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>q (fst (?c3 q)) \<and>
            (snd (?c2 q)) = [(i\<^bsup>p\<rightarrow>q\<^esup>)] \<cdot> snd (?c3 q) \<and> (\<forall>x. x \<noteq> q \<longrightarrow> ?c2(x) = ?c3(x))"
    using R1 R4 by auto
  then have mbox_step_2 : "mbox_step ?c2 (?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None ?c3" by (simp add: MboxRecv)
  then have "mbox_step ?c1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None ?c2 \<and> mbox_step ?c2 (?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None ?c3"  by (simp add: mbox_step_1)
  then have "?c1 \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> ?c2 \<and> ?c2 \<midarrow>\<langle>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> ?c3 " by simp
  then show ?thesis by auto
qed

\<comment> \<open>shows that sync step means mbox steps exist in general\<close>
lemma sync_step_to_mbox_steps_existence:
  assumes "C1 \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<zero>\<rangle>\<rightarrow> C2" 
  shows "\<exists> c1 c2 c3. mbox_step c1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c2 \<and> mbox_step c2 (?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c3" 
   by (meson assms sync_step_to_mbox_steps)

lemma sync_step_to_mbox_steps_alt:
  assumes "C1 \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<zero>\<rangle>\<rightarrow> C2" and "c1 = (\<lambda>x. (C1 x, \<epsilon>))" and "c3 = (\<lambda>x. (C2 x, \<epsilon>))" and "c2 = (c3)(q := (C1 q, [(i\<^bsup>p\<rightarrow>q\<^esup>)]))" 
  shows "mbox_step c1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c2 \<and> mbox_step c2 (?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c3"
  using assms
proof auto
  have  "let c1 = \<lambda>x. (C1 x, \<epsilon>); c3 = \<lambda>x. (C2 x, \<epsilon>); c2 = (c3)(q := (C1 q, [(i\<^bsup>p\<rightarrow>q\<^esup>)])) in
  mbox_step c1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c2 \<and> mbox_step c2 (?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c3"
    by (simp add: assms(1) sync_step_to_mbox_steps)
  then show "(\<lambda>x. (C1 x, \<epsilon>)) \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> (\<lambda>x. (C2 x, \<epsilon>))(q := (C1 q, i\<^bsup>p\<rightarrow>q\<^esup> # \<epsilon>))" by meson
next
have  "let c1 = \<lambda>x. (C1 x, \<epsilon>); c3 = \<lambda>x. (C2 x, \<epsilon>); c2 = (c3)(q := (C1 q, [(i\<^bsup>p\<rightarrow>q\<^esup>)])) in
  mbox_step c1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c2 \<and> mbox_step c2 (?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c3"
    by (simp add: assms(1) sync_step_to_mbox_steps)
  then show "(\<lambda>x. (C2 x, \<epsilon>))(q := (C1 q, i\<^bsup>p\<rightarrow>q\<^esup> # \<epsilon>)) \<midarrow>\<langle>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> (\<lambda>x. (C2 x, \<epsilon>))" by meson
qed

section \<open>Synchronisability\<close>

abbreviation is_synchronisable :: "bool" where
  "is_synchronisable \<equiv> \<L>\<^sub>\<infinity> = \<L>\<^sub>\<zero>"

type_synonym 'a topology = "('a \<times> 'a) set"

\<comment> \<open>the topology graph of all peers\<close>
inductive_set Edges :: "'peer topology"  ("\<G>" 110) where
TEdge: "i\<^bsup>p\<rightarrow>q\<^esup> \<in> \<M> \<Longrightarrow> (p, q) \<in> \<G>"

lemma Edges_rev:
  fixes e :: "'peer \<times> 'peer"
  assumes "e \<in> \<G>"
  shows "\<exists>i p q. i\<^bsup>p\<rightarrow>q\<^esup> \<in> \<M> \<and> e = (p, q)"
proof -
  obtain p q where A: "e = (p, q)"
    by fastforce
  with assms have "(p, q) \<in> \<G>"
    by simp
  from this A show "\<exists>i p q. i\<^bsup>p\<rightarrow>q\<^esup> \<in> \<M> \<and> e = (p, q)"
    by (induct, blast)
qed

lemma trans_to_edge : 
  assumes "(s1, a, s2) \<in> \<R>(p)"
  shows "get_message a \<in> \<M>"
  by (meson CommunicatingAutomaton.well_formed_transition assms automaton_of_peer)


lemma valid_message_to_valid_act :
  assumes "get_message a \<in> \<M>" 
  shows "\<exists> i p q. i\<^bsup>p\<rightarrow>q\<^esup> \<in> \<M> \<and> (i\<^bsup>p\<rightarrow>q\<^esup>) = get_message a" 
  by (metis assms message.exhaust)

lemma valid_message_to_valid_act_rev :
  assumes "i\<^bsup>p\<rightarrow>q\<^esup> \<in> \<M> \<and> (i\<^bsup>p\<rightarrow>q\<^esup>) = get_message a"
  shows "get_message a \<in> \<M>" 
  using assms by auto

lemma input_message_to_act :
  assumes "get_message a \<in> \<M>" and "is_input a" and "get_actor a = p"
  shows "\<exists> i q. i\<^bsup>q\<rightarrow>p\<^esup> \<in> \<M> \<and> (i\<^bsup>q\<rightarrow>p\<^esup>) = get_message a"
  by (metis action.exhaust assms(1,2,3) get_actor.simps(2) get_message.simps(2) get_receiver.simps is_output.simps(1)
      valid_message_to_valid_act)

lemma output_message_to_act : 
assumes "get_message a \<in> \<M>" and "is_output a" and "get_actor a = p"
shows "\<exists> i q. i\<^bsup>p\<rightarrow>q\<^esup> \<in> \<M> \<and> (i\<^bsup>p\<rightarrow>q\<^esup>) = get_message a"
  by (metis action.exhaust assms(1,2,3) get_actor.simps(1) get_message.simps(1) get_sender.simps is_output.simps(2)
      valid_message_to_valid_act)

lemma input_message_to_act_both_known :
  assumes "get_message a \<in> \<M>" and "is_input a" and "get_actor a = p" and "get_object a = q"
  shows "\<exists> i. i\<^bsup>q\<rightarrow>p\<^esup> \<in> \<M> \<and> (i\<^bsup>q\<rightarrow>p\<^esup>) = get_message a"
  by (metis action.exhaust assms(1,2,3,4) get_message.simps(2) get_object.simps(2) get_sender.simps
      input_message_to_act is_output.simps(1))

lemma output_message_to_act_both_known :
  assumes "get_message a \<in> \<M>" and "is_output a" and "get_actor a = p" and "get_object a = q"
  shows "\<exists> i. i\<^bsup>p\<rightarrow>q\<^esup> \<in> \<M> \<and> (i\<^bsup>p\<rightarrow>q\<^esup>) = get_message a"
  by (metis action.exhaust assms(1,2,3,4) get_message.simps(1) get_object.simps(1) get_receiver.simps
      is_output.simps(2) output_message_to_act)


lemma w_in_peer_lang_impl_p_actor: 
  assumes "w \<in> \<L>(p)"
  shows "w = w\<down>\<^sub>p"
  using assms 
proof (induct "length w" arbitrary: w)
  case 0
  then show ?case by simp
next
  case (Suc x)
  then obtain v a where w_def: "w = v @ [a]" and v_len : "length v = x" and v_def : "v \<in> \<L> p"
    by (metis (no_types, lifting) Lang_app length_Suc_conv_rev)
  then have "v\<down>\<^sub>p = v" using Suc.hyps(1) Suc.prems by auto
  then obtain s2 s3 where v_run: "(\<I> p) \<midarrow>v\<rightarrow>\<^sup>*p s2" and a_run: "s2 \<midarrow>[a]\<rightarrow>\<^sup>*p s3" 
    using Lang_app_both Suc.prems(1) w_def by blast
  then have "s2 \<midarrow>a\<rightarrow>p s3"  by (simp add: lang_implies_trans)
  then have "(s2, a, s3) \<in> \<R> p" by simp
  then have "get_actor a = p" using CommunicatingAutomaton.well_formed_transition
    automaton_of_peer by fastforce
  then show ?case 
    by (simp add: \<open>v\<down>\<^sub>p = v\<close> w_def)
qed


abbreviation Successors :: "'peer topology \<Rightarrow> 'peer \<Rightarrow> 'peer set"  ("_\<langle>_\<rightarrow>\<rangle>" [90, 90] 110) where
  "E\<langle>p\<rightarrow>\<rangle> \<equiv> {q. (p, q) \<in> E}"

abbreviation Predecessors :: "'peer topology \<Rightarrow> 'peer \<Rightarrow> 'peer set"  ("_\<langle>\<rightarrow>_\<rangle>" [90, 90] 110) where
  "E\<langle>\<rightarrow>q\<rangle> \<equiv> {p. (p, q) \<in> E}"

subsection \<open>Synchronisability is Deciable for Tree Topology in Mailbox Communication\<close>

subsubsection \<open>Topology is a Tree\<close>

inductive is_tree :: "'peer set \<Rightarrow> 'peer topology \<Rightarrow> bool" where
ITRoot: "is_tree {p} {}" |
ITNode: "\<lbrakk>is_tree P E; p \<in> P; q \<notin> P\<rbrakk> \<Longrightarrow> is_tree (insert q P) (insert (p, q) E)"

lemma is_tree_rev:
  assumes "is_tree P E"
  shows "(\<exists>p. P = {p} \<and> E = {}) \<or> (\<exists>P' E' p q. is_tree P' E' \<and> p \<in> P' \<and> q \<notin> P' \<and> P = insert q P' \<and> E = insert (p, q) E')"
  using assms
proof (induction P E rule: is_tree.induct)
  case (ITRoot p)
  then show ?case by simp
next
  case (ITNode P E p q)
  then show ?case
    by (intro disjI2, auto simp: insert_commute)
qed

lemma is_tree_rev_nonempty:
  assumes "is_tree P E" and "E \<noteq> {}"
  shows "(\<exists>P' E' p q. is_tree P' E' \<and> p \<in> P' \<and> q \<notin> P' \<and> P = insert q P' \<and> E = insert (p, q) E')"
  using assms(1,2) is_tree_rev by auto
  

lemma edge_on_peers_in_tree:
  fixes P   :: "'peer set"
    and E   :: "'peer topology"
    and p q :: "'peer"
  assumes "is_tree P E"
      and "(p, q) \<in> E"
    shows "p \<in> P" and "q \<in> P"
  using assms
proof induct
  case (ITRoot x)
  assume "(p, q) \<in> {}"
  thus "p \<in> {x}" and "q \<in> {x}"
    by simp_all
next
  case (ITNode P E x y)
  assume "(p, q) \<in> E \<Longrightarrow> p \<in> P" and "(p, q) \<in> E \<Longrightarrow> q \<in> P" and "x \<in> P"
     and "(p, q) \<in> insert (x, y) E"
  thus "p \<in> insert y P" and "q \<in> insert y P"
    by auto
qed

lemma at_most_one_parent_in_tree:
  fixes P :: "'peer set"
    and E :: "'peer topology"
    and p :: "'peer"
  assumes "is_tree P E"
  shows "card (E\<langle>\<rightarrow>p\<rangle>) \<le> 1"
  using assms
proof induct
  case (ITRoot x)
  have "{}\<langle>\<rightarrow>p\<rangle> = {}"
    by simp
  thus "card ({}\<langle>\<rightarrow>p\<rangle>) \<le> 1"
    by simp
next
  case (ITNode P E x y)
  assume A1: "is_tree P E" and A2: "card (E\<langle>\<rightarrow>p\<rangle>) \<le> 1" and A3: "y \<notin> P"
  show "card (insert (x, y) E\<langle>\<rightarrow>p\<rangle>) \<le> 1"
  proof (cases "y = p")
    assume B: "y = p"
    with A1 A3 have "E\<langle>\<rightarrow>p\<rangle> = {}"
      using edge_on_peers_in_tree(2)[of P E _ p]
      by blast
    with B have "insert (x, y) E\<langle>\<rightarrow>p\<rangle> = {x}"
      by simp
    thus "card (insert (x, y) E\<langle>\<rightarrow>p\<rangle>) \<le> 1"
      by simp
  next
    assume "y \<noteq> p"
    hence "insert (x, y) E\<langle>\<rightarrow>p\<rangle> = E\<langle>\<rightarrow>p\<rangle>"
      by simp
    with A2 show "card (insert (x, y) E\<langle>\<rightarrow>p\<rangle>) \<le> 1"
      by simp
  qed
qed


lemma edge_doesnt_vanish_in_growing_tree :
  assumes "is_tree P E" and "qa \<in> P" and "card (E\<langle>\<rightarrow>qa\<rangle>) = 1" and "is_tree (insert q P) (insert (p, q) E)"
and "qa \<noteq> p" and "qa \<noteq> q"
  shows "card (insert (p, q) E\<langle>\<rightarrow>qa\<rangle>) = 1"
  using assms
proof - 
  have before_le_1 : "card (E\<langle>\<rightarrow>qa\<rangle>) \<le> 1"  by (simp add: assms(3))
  have after_le_1 : "card (insert (p, q) E\<langle>\<rightarrow>qa\<rangle>) \<le> 1"  using assms(4) at_most_one_parent_in_tree by presburger
  have at_least_1 : "card (E\<langle>\<rightarrow>qa\<rangle>) = 1" by (simp add: assms(3))
  then show "card (insert (p, q) E\<langle>\<rightarrow>qa\<rangle>) = 1" using assms(6) by auto
qed

lemma edge_doesnt_vanish_in_growing_tree2 :
  assumes "card (E\<langle>\<rightarrow>qa\<rangle>) = 1" and "p \<noteq> qa" and "q \<noteq> qa" 
  shows "card (insert (p, q) E\<langle>\<rightarrow>qa\<rangle>) = 1"
  using assms(1,3) by auto


lemma tree_acyclic: 
fixes P :: "'peer set"
    and E :: "'peer topology"
  assumes "is_tree P E" and "(p,q) \<in> E"
  shows "(q,p) \<notin> E"
  using assms 
proof(induct rule: is_tree.induct)
  case (ITRoot p)
  then show ?case by simp
next
  case (ITNode P E p q)
  then show ?case using edge_on_peers_in_tree(1) by blast
qed




lemma root_exists:
  fixes P :: "'peer set"
    and E :: "'peer topology"
  assumes "is_tree P E"
  shows "\<exists>p. p \<in> P \<and> E\<langle>\<rightarrow>p\<rangle> = {}" 
  using assms
proof (induct)
  case (ITRoot p)
  then show ?case by simp
next
  case (ITNode P E p q)
  then obtain p' where p'_def: "p' \<in> P \<and> E\<langle>\<rightarrow>p'\<rangle> = {}" by blast
  then have new_tree: "is_tree (insert q P) (insert (p, q) E)" by (simp add: ITNode.hyps(1,3,4) is_tree.ITNode)
  then have p'_not_q: "p' \<noteq> q" using ITNode.hyps(4) p'_def by auto
  then have "is_tree (insert q P) (insert (p', q) E)"  by (simp add: ITNode.hyps(1,4) is_tree.ITNode p'_def)
  then have t2: "(insert (p', q) E)\<langle>\<rightarrow>p'\<rangle> = {}" by (simp add: p'_def p'_not_q)
  then have t1: "p' \<in> (insert q P)"  using p'_def by auto
  then have "p' \<in> (insert q P) \<and> (insert (p', q) E)\<langle>\<rightarrow>p'\<rangle> = {}" using t2 by auto
  then have "p' \<in> (insert q P) \<and> (insert (p, q) E)\<langle>\<rightarrow>p'\<rangle> = {}" by blast 
  then show ?case by blast
qed

lemma at_most_one_parent:
  assumes "is_tree P E"
  shows "card (E\<langle>\<rightarrow>q\<rangle>) \<le> 1"
  using assms at_most_one_parent_in_tree by auto

lemma unique_root:
  fixes P :: "'peer set"
    and E :: "'peer topology"
  assumes "is_tree P E" and "p \<in> P" and "E\<langle>\<rightarrow>p\<rangle> = {}" and "q \<noteq> p" and "q \<in> P"
  shows "(card (E\<langle>\<rightarrow>q\<rangle>)) = 1"
  using assms
proof (induct P E rule: is_tree.induct)
  case (ITRoot p)
  then show ?case by simp
next
  case (ITNode P E p' q')
    then have "p \<in> insert q' P \<and> insert (p', q') E\<langle>\<rightarrow>p\<rangle> = {}" by blast
    then have "E\<langle>\<rightarrow>p\<rangle> = {}" by simp
    then show "card (insert (p', q') E\<langle>\<rightarrow>q\<rangle>) = 1"
    proof (cases "card (E\<langle>\<rightarrow>q\<rangle>) = 1")
      case True
      then show ?thesis 
        by (smt (verit) Collect_cong ITNode.hyps(1,4) card_1_singletonE edge_on_peers_in_tree(2)
            empty_def insert_iff insert_not_empty prod.inject)
    next
      case False
      have "is_tree P E" by (simp add: ITNode.hyps(1))
      then have q_le_1: "card (E\<langle>\<rightarrow>q\<rangle>) \<le> 1" by (metis \<open>is_tree P E\<close> at_most_one_parent)
      then have q_0: "card (E\<langle>\<rightarrow>q\<rangle>) = 0"  using False by linarith
      then have "q \<notin> P" 
        using False ITNode.hyps(2) ITNode.prems(1,2) assms(4) by blast
      then have "p \<in> P"  using ITNode.prems(1,4) assms(4) by auto
      then have "q = q'" 
        using ITNode.prems(4) \<open>q \<notin> P\<close> by auto
      then have "(insert (p', q') E\<langle>\<rightarrow>q\<rangle>) = (insert (p', q) E\<langle>\<rightarrow>q\<rangle>)" by auto
      then have "({(p', q)}\<langle>\<rightarrow>q\<rangle>) = {p'}" by auto
    then have "card (insert (p', q) E\<langle>\<rightarrow>q\<rangle>) = card (E\<langle>\<rightarrow>q\<rangle>) + card {p'}" 
      by (smt (verit, ccfv_SIG) Collect_cong ITNode.hyps(1,4) \<open>q = q'\<close> add_0 edge_on_peers_in_tree(2)
          insert_iff q_0 singleton_iff)
    then have "card (insert (p', q) E\<langle>\<rightarrow>q\<rangle>) = 1" 
      by (simp add: q_0)
      then show ?thesis 
        using \<open>insert (p', q') E\<langle>\<rightarrow>q\<rangle> = insert (p', q) E\<langle>\<rightarrow>q\<rangle>\<close> by fastforce
    qed  
qed




abbreviation tree_topology :: "bool" where
  "tree_topology \<equiv> is_tree (UNIV :: 'peer set) (\<G>)"

inductive_set All_Senders :: "'peer set" where
All : "\<lbrakk>q \<in> Peers_of p; \<P>\<^sub>?(p) = {q}\<rbrakk> \<Longrightarrow> q \<in> All_Senders" |
All1 : "\<lbrakk>p \<in> Peers_of q; p \<in> (\<P>\<^sub>!(q))\<rbrakk> \<Longrightarrow> q \<in> All_Senders"


\<comment> \<open>P? is defined on each automaton p, G is the topology graph\<close>
\<comment> \<open>This means there may be P?(p) = {} but p \<in> P!(q), thus (q,p) \<in> \<G> and q \<in> \<G>\<langle>\<rightarrow>p\<rangle>, but q \<notin> {}\<close>
lemma sends_of_peer_subset_of_predecessors_in_topology:
  fixes p :: "'peer"
  shows "\<P>\<^sub>?(p) \<subseteq> \<G>\<langle>\<rightarrow>p\<rangle>"
proof (cases "\<P>\<^sub>?(p) = {}")
  case True
  then show ?thesis by simp
next
  case False
  show ?thesis
  proof
    fix q
    assume "q \<in> \<P>\<^sub>?(p)"
    then have "\<exists> s1 a s2. (s1, a, s2) \<in> \<R>(p) \<and> is_input a" using no_input_trans_no_recvs by blast
    then have "\<exists> s1 a s2. (s1, a, s2) \<in> \<R>(p) \<and> is_input a \<and> get_object a = q" 
      using CommunicatingAutomaton.ReceivingFromPeers_rev \<open>q \<in> \<P>\<^sub>? p\<close> automaton_of_peer by fastforce
    then obtain s1 s2 a where "(s1, a, s2) \<in> \<R>(p) \<and> is_input a \<and> get_object a = q \<and> get_actor a = p" 
      by (metis CommunicatingAutomaton.well_formed_transition automaton_of_peer)
    then have "get_message a \<in> \<M>" 
      by (metis trans_to_edge)
    then have "\<exists>i. i\<^bsup>q\<rightarrow>p\<^esup> = get_message a"
      using \<open>s1 \<midarrow>a\<rightarrow>p s2 \<and> is_input a \<and> get_object a = q \<and> get_actor a = p\<close> input_message_to_act_both_known
      by blast
    then obtain i where " a = (?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)"
      by (metis \<open>s1 \<midarrow>a\<rightarrow>p s2 \<and> is_input a \<and> get_object a = q \<and> get_actor a = p\<close> action.exhaust get_message.simps(2)
          is_output.simps(1))
    then have "(q, p) \<in> \<G>" 
      using Edges.intros \<open>get_message a \<in> \<M>\<close> by force
    then show "q \<in> \<G>\<langle>\<rightarrow>p\<rangle>" 
      by simp
  qed
qed

(*
\<comment> \<open>this is not true, as P? is defined only on each peer (q might send something to p but p may never receive it,
leading to an edge in the topology but to an empty P?(p)\<close>
lemma paranents_in_tree_is_ReceivedFromPeers:
  fixes p :: "'peer"
  assumes "tree_topology"
  shows "\<G>\<langle>\<rightarrow>p\<rangle> = \<P>\<^sub>?(p)"
\<comment> \<open>proof (induct)\<close>
  sorry
*)

subsubsection "influenced language approaches 1"

(*combines all local info (i.e. that of each automaton and its sends/recvs)
and receives the global information from it*)
lemma local_to_global_root :
  assumes "\<P>\<^sub>?(p) = {}" and "(\<forall>q. p \<notin> \<P>\<^sub>!(q))" and "tree_topology"
  shows "\<G>\<langle>\<rightarrow>p\<rangle> = {}"
  using assms 
proof auto
  fix q
  assume "(q, p) \<in> \<G>"
  then show "False" 
  proof -
    have "(q, p) \<in> \<G>"  by (simp add: \<open>(q, p) \<in> \<G>\<close>)
    then obtain i where i_def: "i\<^bsup>q\<rightarrow>p\<^esup> \<in> \<M>" by (metis Edges.cases)
    then obtain s1 a s2 x where trans: "(s1, a, s2) \<in> snd (snd (\<A> x)) \<and>
                             (i\<^bsup>q\<rightarrow>p\<^esup>) = get_message a"  using messages_used by blast
    then have "x = p \<or> x = q" by (metis CommunicatingAutomaton.well_formed_transition NetworkOfCA.automaton_of_peer
          NetworkOfCA.output_message_to_act NetworkOfCA_axioms input_message_to_act_both_known
          message.inject)
    then have "x = q" by (metis CommunicatingAutomaton.SendingToPeers.intros assms(1,2) automaton_of_peer i_def
          local.trans message.inject no_recvs_no_input_trans output_message_to_act_both_known)
    then have "a = !\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>"  by (metis CommunicatingAutomaton.well_formed_transition action.exhaust automaton_of_peer
          get_message.simps(1,2) get_object.simps(2) get_sender.simps local.trans)
    then have "\<not> (\<forall>q. p \<notin> \<P>\<^sub>!(q))" using CommunicatingAutomaton.SendingToPeers.intros automaton_of_peer local.trans
      by fastforce
    then show ?thesis by (simp add: assms(2)) 
  qed
qed


lemma global_to_local_root: 
  assumes "\<G>\<langle>\<rightarrow>p\<rangle> = {}" and "tree_topology"
  shows "\<P>\<^sub>?(p) = {} \<and> (\<forall>q. p \<notin> \<P>\<^sub>!(q))"
proof auto
  fix q 
  assume "q \<in> \<P>\<^sub>? p"
  then obtain s1 i a s2 where trans_def : "(s1, a, s2) \<in> snd (snd (\<A> p))"
    and "a = ?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>"  by (metis (mono_tags, lifting) Collect_mem_eq Collect_mono_iff assms(1) empty_Collect_eq
        sends_of_peer_subset_of_predecessors_in_topology)
  then show "False" using \<open>q \<in> \<P>\<^sub>? p\<close> assms(1) sends_of_peer_subset_of_predecessors_in_topology by force
next 
  fix q 
  assume "p \<in> \<P>\<^sub>! q"
  then have "\<exists>s1 a s2. (s1, a, s2) \<in> snd (snd (\<A> q)) \<and> is_output a \<and> get_object a = p"
    by (metis CommunicatingAutomaton.SendingToPeers.simps automaton_of_peer)
  then obtain s1 i a s2 where trans_def : "(s1, a, s2) \<in> snd (snd (\<A> q))"
    and "a = !\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>" 
    by (metis Edges.intros assms(1) empty_Collect_eq output_message_to_act_both_known
        trans_to_edge)
  then show "False"  using Edges.simps assms(1) trans_to_edge by fastforce
qed



abbreviation is_root_from_topology :: "'peer \<Rightarrow> bool" where
"is_root_from_topology p \<equiv> (tree_topology \<and> \<G>\<langle>\<rightarrow>p\<rangle> = {})"

abbreviation is_root_from_local :: "'peer \<Rightarrow> bool"  where
"is_root_from_local p \<equiv> tree_topology \<and> \<P>\<^sub>?(p) = {} \<and> (\<forall>q. p \<notin> \<P>\<^sub>!(q))"

abbreviation is_root :: "'peer \<Rightarrow> bool"  where
"is_root p \<equiv> is_root_from_local p \<or> is_root_from_topology p"
(*tree_topology \<and> ((\<P>\<^sub>?(p) = {} \<and> (\<forall>q. p \<notin> \<P>\<^sub>!(q))) \<or> \<G>\<langle>\<rightarrow>p\<rangle> = {})*)


lemma edge_impl_psend_or_qrecv:
  assumes "\<G>\<langle>\<rightarrow>p\<rangle> = {q}" and "tree_topology"
  shows "(\<P>\<^sub>? p = {q} \<or> p \<in> \<P>\<^sub>!(q))"
proof (rule ccontr)
  assume "\<not> (\<P>\<^sub>? p = {q} \<or> p \<in> \<P>\<^sub>!(q))"
  then show "False" 
  proof -
    have "\<P>\<^sub>? p \<noteq> {q}" using \<open>\<not> (\<P>\<^sub>? p = {q} \<or> p \<in> \<P>\<^sub>! q)\<close> by auto
    have "p \<notin> \<P>\<^sub>!(q)" using \<open>\<not> (\<P>\<^sub>? p = {q} \<or> p \<in> \<P>\<^sub>! q)\<close> by auto

    have "\<exists>i. i\<^bsup>q\<rightarrow>p\<^esup> \<in> \<M>" using Edges.simps  assms(1) by auto
    then obtain i where m: "i\<^bsup>q\<rightarrow>p\<^esup> \<in> \<M>" by auto
    then have "\<exists>s1 a s2 pp. (s1, a, s2) \<in> snd (snd (\<A> pp)) \<and>
                              (i\<^bsup>q\<rightarrow>p\<^esup>) = get_message a" using messages_used by auto
    then have "\<exists>s1 a s2. ((s1, a, s2) \<in> \<R> p \<or> (s1, a, s2) \<in> \<R> q) \<and>
                              (i\<^bsup>q\<rightarrow>p\<^esup>) = get_message a"  by (metis (mono_tags, lifting) CommunicatingAutomaton.well_formed_transition
          NetworkOfCA.input_message_to_act_both_known NetworkOfCA_axioms automaton_of_peer message.inject
          output_message_to_act_both_known)
    (*show that if in Rq then P!q cont otherwise P1p contr*)
    then obtain s1 a s2 where "((s1, a, s2) \<in> \<R> p \<or> (s1, a, s2) \<in> \<R> q) \<and> (i\<^bsup>q\<rightarrow>p\<^esup>) = get_message a" by blast
    then show ?thesis 
    proof (cases "is_output a")
      case True
      then have "(s1, a, s2) \<in> \<R> q"  by (metis CommunicatingAutomaton_def NetworkOfCA.automaton_of_peer NetworkOfCA.output_message_to_act_both_known
            NetworkOfCA_axioms \<open>(s1 \<midarrow>a\<rightarrow>p s2 \<or> s1 \<midarrow>a\<rightarrow>q s2) \<and> i\<^bsup>q\<rightarrow>p\<^esup> = get_message a\<close> message.inject) 
      then show ?thesis by (metis CommunicatingAutomaton.SendingToPeers.intros True
            \<open>(s1 \<midarrow>a\<rightarrow>p s2 \<or> s1 \<midarrow>a\<rightarrow>q s2) \<and> i\<^bsup>q\<rightarrow>p\<^esup> = get_message a\<close> \<open>p \<notin> \<P>\<^sub>! q\<close> automaton_of_peer m message.inject
            output_message_to_act_both_known)
    next
      case False
      then have "(s1, a, s2) \<in> \<R> p" by (metis \<open>(s1 \<midarrow>a\<rightarrow>p s2 \<or> s1 \<midarrow>a\<rightarrow>q s2) \<and> i\<^bsup>q\<rightarrow>p\<^esup> = get_message a\<close> empty_receiving_from_peers2
            input_message_to_act_both_known insert_absorb insert_not_empty m message.inject)
      then have "is_input a" by (simp add: False)
      then have "q \<in> \<P>\<^sub>?(p)"  by (metis CommunicatingAutomaton.ReceivingFromPeers.intros
            \<open>(s1 \<midarrow>a\<rightarrow>p s2 \<or> s1 \<midarrow>a\<rightarrow>q s2) \<and> i\<^bsup>q\<rightarrow>p\<^esup> = get_message a\<close> \<open>s1 \<midarrow>a\<rightarrow>p s2\<close> automaton_of_peer
            input_message_to_act_both_known m message.inject)
      have "(\<P>\<^sub>?(p)) = {q}" 
      proof 
        show "{q} \<subseteq> \<P>\<^sub>? p" by (simp add: \<open>q \<in> \<P>\<^sub>? p\<close>)
      
        show "\<P>\<^sub>? p \<subseteq> {q}"
        proof (rule ccontr)
          assume "\<not> \<P>\<^sub>? p \<subseteq> {q}" 
          then obtain pp where "pp \<in> \<P>\<^sub>? p" and "pp \<noteq> q" by auto
          then have "pp \<in> \<G>\<langle>\<rightarrow>p\<rangle>" using sends_of_peer_subset_of_predecessors_in_topology by auto
          then show "False" by (simp add: \<open>pp \<noteq> q\<close> assms(1))
        qed
      qed
      then show ?thesis by (simp add: \<open>\<P>\<^sub>? p \<noteq> {q}\<close>)
    qed
  qed
qed

(* this implication does not hold necessarily in all trees.
To have an edge between nodes, a receive OR send message must exist in across the ENTIRE network.
A counter example to this lemma would be the PCP instance!
lemma edge_impl_psend_and_qrecv:
  assumes "\<G>\<langle>\<rightarrow>p\<rangle> = {q}" and "tree_topology"
  shows "(\<P>\<^sub>? p = {q} \<and> p \<in> \<P>\<^sub>!(q))"
*)

lemma root_or_node:
  assumes "tree_topology"
  shows "is_root p \<or> (\<exists>q. \<P>\<^sub>?(p) = {q} \<or> p \<in> \<P>\<^sub>!(q))"
  using assms
proof (cases "\<G>\<langle>\<rightarrow>p\<rangle> = {}")
  case True
  then show ?thesis by (simp add: assms)
next
  case False
  then have "card (\<G>\<langle>\<rightarrow>p\<rangle>) \<noteq> 0" by (metis card_0_eq finite_peers finite_subset top_greatest)
  have  "card (\<G>\<langle>\<rightarrow>p\<rangle>) \<le> 1" using assms at_most_one_parent by auto
  then have "card (\<G>\<langle>\<rightarrow>p\<rangle>) = 1" using \<open>card (\<G>\<langle>\<rightarrow>p\<rangle>) \<noteq> 0\<close> by linarith
  then obtain q where "\<G>\<langle>\<rightarrow>p\<rangle> = {q}" using card_1_singletonE by blast
  then show ?thesis using assms edge_impl_psend_or_qrecv by blast
qed

abbreviation is_node_from_topology :: "'peer \<Rightarrow> bool" where
"is_node_from_topology p \<equiv> (tree_topology \<and> (\<exists>q. \<G>\<langle>\<rightarrow>p\<rangle> = {q}))"

abbreviation is_node_from_local :: "'peer \<Rightarrow> bool"  where
"is_node_from_local p \<equiv> tree_topology \<and> (\<exists>q. \<P>\<^sub>?(p) = {q} \<or> p \<in> \<P>\<^sub>!(q))"

abbreviation is_node :: "'peer \<Rightarrow> bool"  where
"is_node p \<equiv> is_node_from_topology p \<or> is_node_from_local p"

lemma root_defs_eq:
  shows "is_root_from_topology p = is_root_from_local p"
  using global_to_local_root local_to_global_root by blast

lemma local_global_eq_node: 
  assumes "is_node_from_topology p"
  shows "is_node_from_local p"
  using assms edge_impl_psend_or_qrecv by auto

lemma global_local_eq_node:
  assumes "is_node_from_local p"
  shows "is_node_from_topology p"
proof -
  have local_p: "tree_topology \<and> (\<exists>q. \<P>\<^sub>?(p) = {q} \<or> p \<in> \<P>\<^sub>!(q))" by (simp add: assms)
  then have t1: "tree_topology" by simp
  then show ?thesis using assms
  proof (cases "\<exists>q. \<P>\<^sub>?(p) = {q}")
    case True
    then obtain q where "\<P>\<^sub>?(p) = {q}" by auto
    then have "q \<in> \<G>\<langle>\<rightarrow>p\<rangle>" using sends_of_peer_subset_of_predecessors_in_topology by auto
    have "\<not> (is_root p)" using \<open>\<P>\<^sub>? p = {q}\<close> \<open>q \<in> \<G>\<langle>\<rightarrow>p\<rangle>\<close> by blast
    have "card (\<G>\<langle>\<rightarrow>p\<rangle>) \<le> 1" using at_most_one_parent t1 by auto
    then have "card (\<G>\<langle>\<rightarrow>p\<rangle>) = 1" by (smt (verit) Collect_cong \<open>q \<in> \<G>\<langle>\<rightarrow>p\<rangle>\<close> edge_on_peers_in_tree(2) empty_Collect_eq empty_iff root_exists t1
          unique_root)
    then show ?thesis by (meson is_singleton_altdef is_singleton_the_elem t1)
  next
    case False
    then obtain q where "p \<in> \<P>\<^sub>!(q)" using local_p by auto
    then obtain s1 a s2 where "is_output a" and "get_actor a = q" and "get_object a = p" and "(s1,a,s2) \<in> \<R> q" 
      by (meson CommunicatingAutomaton.SendingToPeers_rev CommunicatingAutomaton.well_formed_transition
          automaton_of_peer)
    then have "q \<in> \<G>\<langle>\<rightarrow>p\<rangle>" by (metis Edges.intros mem_Collect_eq output_message_to_act_both_known trans_to_edge)
    have "card (\<G>\<langle>\<rightarrow>p\<rangle>) \<le> 1" using at_most_one_parent t1 by auto
    then have "card (\<G>\<langle>\<rightarrow>p\<rangle>) = 1" by (smt (verit) Collect_cong \<open>q \<in> \<G>\<langle>\<rightarrow>p\<rangle>\<close> edge_on_peers_in_tree(2) empty_Collect_eq empty_iff root_exists t1
          unique_root)
    then show ?thesis by (meson is_singleton_altdef is_singleton_the_elem t1)
  qed
qed

lemma node_defs_eq: 
  shows "is_node_from_topology p = is_node_from_local p"
  using edge_impl_psend_or_qrecv global_local_eq_node by blast

(*q is parent of p*)
inductive is_parent_of :: "'peer \<Rightarrow> 'peer \<Rightarrow> bool" where
node_parent : "\<lbrakk>is_node p; \<G>\<langle>\<rightarrow>p\<rangle> = {q}\<rbrakk> \<Longrightarrow> is_parent_of p q"

lemma is_parent_of_rev:
  assumes "is_parent_of p q"
  shows "is_node p" and "\<G>\<langle>\<rightarrow>p\<rangle> = {q}"
  using assms
proof (cases rule: is_parent_of.cases)
  case node_parent
  then show "is_node p" by simp
next 
  have "is_node p"  by (metis assms is_parent_of.cases)
  then show "\<G>\<langle>\<rightarrow>p\<rangle> = {q}" by (metis assms is_parent_of.cases)
qed

lemma is_parent_of_rev2:
  assumes "is_parent_of p q"
  shows "is_node p" and "\<P>\<^sub>?(p) = {q} \<or> p \<in> \<P>\<^sub>!(q)"
  using assms
proof (cases rule: is_parent_of.cases)
  case node_parent
  then show "is_node p" by simp
next 
  have "is_node p"  by (metis assms is_parent_of.cases)
  then show "\<P>\<^sub>?(p) = {q} \<or> p \<in> \<P>\<^sub>!(q)" using assms edge_impl_psend_or_qrecv is_parent_of_rev(2) by blast
qed



inductive path_to_root :: "'peer \<Rightarrow> 'peer list \<Rightarrow> bool" where
PTRRoot: "\<lbrakk>is_root p\<rbrakk> \<Longrightarrow> path_to_root p [p]" |
PTRNode: "\<lbrakk>tree_topology; is_parent_of p q; path_to_root q as\<rbrakk> \<Longrightarrow> path_to_root p (p # as)"

lemma path_to_root_rev:
  assumes "path_to_root p ps" and "ps \<noteq> [p]"
  shows "\<exists>q as. is_parent_of p q \<and> path_to_root q as \<and> ps = (p # as)"
  using assms
  by (meson path_to_root.simps)

lemma path_to_root_rev_empty:
  assumes "path_to_root p ps" and "ps = [p]"
  shows "is_root p"
  by (metis assms(1,2) list.discI list.inject path_to_root.simps)


fun get_root :: "'peer topology \<Rightarrow> 'peer" where
"get_root E = (THE x. is_root x)"

lemma path_ends_at_root:
  assumes "path_to_root p ps"
  shows  "is_root (last ps)"
  using assms
proof (induct rule: path_to_root.induct)
  case (PTRRoot p)
  then show ?case by auto
next
  case (PTRNode p q as)
  then show ?case by (metis last_ConsR list.discI path_to_root.cases)
qed

lemma single_path_impl_root: 
  assumes "path_to_root p [p]"
  shows "is_root p"
  using assms path_to_root_rev_empty by blast


abbreviation get_path_to_root :: "'peer \<Rightarrow>  'peer list" where
"get_path_to_root p \<equiv>  (THE ps. path_to_root p ps)"

lemma path_to_root_first_elem_is_peer: 
  assumes  "path_to_root p (x # ps)" 
  shows  "p = x"
  using assms path_to_root_rev by auto

lemma path_to_root_stepback:
  assumes "path_to_root p (p # ps)"
  shows "ps = [] \<or> (\<exists>q. is_parent_of p q \<and> path_to_root q ps)" 
  using assms path_to_root_rev by auto 


lemma path_to_root_unique:
  assumes "path_to_root p ps" and "path_to_root p qs"
  shows "qs = ps"
  using assms 
proof (induct p ps arbitrary: qs rule: path_to_root.induct)
  case (PTRRoot p)
  then show ?case by (metis (mono_tags, lifting) ITRoot empty_iff is_parent_of.cases local_to_global_root path_to_root.simps
        root_exists)
next
  case (PTRNode p q as)
  then have "path_to_root p (p # as)" using path_to_root.PTRNode by blast
  then have "\<forall> ys. (path_to_root q ys) \<longrightarrow> as = ys " using PTRNode.hyps(4) by auto 
  then have pq: "is_parent_of p q" by (simp add: PTRNode.hyps(2))
  then have "as \<noteq> qs"  by (metis PTRNode.hyps(3) PTRNode.prems \<open>\<forall>ys. path_to_root q ys \<longrightarrow> as = ys\<close> \<open>path_to_root p (p # as)\<close>
        list.inject not_Cons_self2 path_to_root_rev)
  have "qs \<noteq> []" using path_to_root.cases PTRNode.prems by auto
  then obtain x qqs where qs_decomp:  "qs = x # qqs" using list.exhaust by auto
  then have "path_to_root p (x # qqs)" using PTRNode.prems by auto
  then have "x = p" using path_to_root_first_elem_is_peer by auto
  then have "qs = p # qqs" by (simp add: qs_decomp)
  then have "qqs = [] \<or> (\<exists>y. is_parent_of p y \<and> path_to_root y qqs)" using \<open>path_to_root p (x # qqs)\<close> \<open>x = p\<close> path_to_root_stepback by auto
  then have "qqs \<noteq> []" using pq using \<open>path_to_root p (x # qqs)\<close> \<open>x = p\<close> is_parent_of_rev(2) root_defs_eq single_path_impl_root
    by fastforce
  then have "(\<exists>y. is_parent_of p y \<and> path_to_root y qqs)" using \<open>qqs = \<epsilon> \<or> (\<exists>y. is_parent_of p y \<and> path_to_root y qqs)\<close> by auto
  then obtain y where "is_parent_of p y \<and> path_to_root y qqs" by auto
  then have "is_parent_of p q \<and> is_parent_of p y" by (simp add: pq)
  then have "\<G>\<langle>\<rightarrow>p\<rangle> = {q} \<and> \<G>\<langle>\<rightarrow>p\<rangle> = {y}"  using is_parent_of_rev(2) by auto
  then have "q = y" by blast
  then have "is_parent_of p q \<and> path_to_root q qqs"  by (simp add: \<open>is_parent_of p y \<and> path_to_root y qqs\<close>)
  then show ?case by (simp add: PTRNode.hyps(4) \<open>qs = p # qqs\<close>)
qed





lemma
  assumes "is_tree (\<P>) (\<G>)" and "(\<P>) = {p}" 
  shows "is_root p" 
  by (metis assms(1,2) root_exists singleton_iff)

lemma leaf_exists:
  assumes "tree_topology"
  shows "\<exists>q. q \<in> \<P> \<and> \<G>\<langle>q\<rightarrow>\<rangle> = {}"
  using assms
proof (induct)
  case (ITRoot p)
  then show ?case by simp
next
  case (ITNode P E p q)
  then show ?case  using edge_on_peers_in_tree(1) prod.inject by fastforce
qed

lemma path_to_root_exists: 
  assumes "tree_topology" and "p \<in> \<P>"
  shows "\<exists>ps. path_to_root p ps" 
  using assms
proof (induct "card (\<P>)" )
  case 0
  then have "\<not> is_tree (\<P>) (\<G>)" using finite_peers by auto
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
    then have "x \<ge> 1"  by linarith
    then have "card (\<P>) \<ge> 2"  using Suc.hyps(2) by linarith
    then have "\<exists>q. q \<in> \<P> \<and> \<G>\<langle>q\<rightarrow>\<rangle> = {}" using assms(1) leaf_exists by blast
    then obtain l where "l \<in> \<P> \<and> \<G>\<langle>l\<rightarrow>\<rangle> = {}" by auto
    (* remove leaf from tree, show use IH, then show that adding leaf keeps the path from IH
    then have "is_node l" 
    then obtain x where "(x, l) \<in> \<G>" *)
    then show ?thesis sorry
  qed 
qed



(*
fun infl_lang_rec :: "'peer list \<Rightarrow> ('information, 'peer) action language" where
"infl_lang_rec [] = {}" |
"infl_lang_rec [r::'peer] = {\<epsilon>::('information, 'peer) action word}" |
"infl_lang_rec (p # q # ps) = {w | w::('information, 'peer) action word. w \<in> \<L>(p) \<and> (w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>? \<in> ((infl_lang_rec ((q::'peer) # ps))\<downharpoonright>\<^sub>! )\<downharpoonright>\<^sub>!\<^sub>? \<and> \<P>\<^sub>?(p) = {q}}" 

fun infl_lang :: "'peer list \<Rightarrow> ('information, 'peer) action language" where
"infl_lang [] = {}" |
"infl_lang [r] = \<L>(r)" |
"infl_lang ps = infl_lang_rec ps" 

abbreviation InfluencedLanguage :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sup>* _" [90] 100) where
"\<L>\<^sup>* p \<equiv> infl_lang (get_path_to_root p)"

abbreviation InfluencedLanguageSend :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>!\<^sup>* _" [90] 100) where
"\<L>\<^sub>!\<^sup>* p \<equiv> (\<L>\<^sup>* p)\<downharpoonright>\<^sub>! "

abbreviation InfluencedLanguageRecv :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>?\<^sup>* _" [90] 100) where
"\<L>\<^sub>?\<^sup>* p \<equiv> (\<L>\<^sup>* p)\<downharpoonright>\<^sub>! "

abbreviation ShuffledInfluencedLanguage :: "'peer \<Rightarrow> ('information, 'peer) action language" ("\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion> _" [90] 100) where
"\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion> p \<equiv> shuffled_lang (\<L>\<^sup>* p)"
*)

lemma recv_proj_w_prepend_is_in_w:
  assumes "(w\<down>\<^sub>?) = (x # xs)" and "w \<in> \<L>(p)"
  shows "\<exists> ys zs. w = ys @ [x] @ zs" 
  using assms 
proof (induct "length (w\<down>\<^sub>?)" arbitrary: w x xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (metis Cons_eq_filterD append_Cons append_Nil)
qed

lemma recv_proj_w_prepend_has_trans:
  assumes "(w\<down>\<^sub>?) = (x # xs)" and "w \<in> \<L>(p)"
  shows "\<exists>s1 s2. (s1, x, s2) \<in> \<R> p"
  using assms 
proof (induct "length (w\<down>\<^sub>?)" arbitrary: w x xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain ys zs where w_def: "w = ys @ [x] @ zs"  using recv_proj_w_prepend_is_in_w by blast
  then have "(ys @ [x] @ zs) \<in> \<L>(p)"  using Suc.prems(2) by blast
  then have "(ys @ [x]) \<in> \<L>(p)" by (metis Lang_app append_assoc) 
  then have "\<exists>s1 s2. (s1, x, s2) \<in> \<R> p" using Lang_app_both lang_implies_trans by blast
  then show ?case by simp
qed

lemma send_proj_w_prepend_is_in_w:
  assumes "(w\<down>\<^sub>!) = (x # xs)" and "w \<in> \<L>(p)"
  shows "\<exists> ys zs. w = ys @ [x] @ zs" 
  using assms 
proof (induct "length (w\<down>\<^sub>!)" arbitrary: w x xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then show ?case by (metis Cons_eq_filterD append_Cons append_Nil)
qed

lemma send_proj_w_prepend_has_trans:
  assumes "(w\<down>\<^sub>!) = (x # xs)" and "w \<in> \<L>(p)"
  shows "\<exists>s1 s2. (s1, x, s2) \<in> \<R> p"
  using assms 
proof (induct "length (w\<down>\<^sub>!)" arbitrary: w x xs)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then obtain ys zs where w_def: "w = ys @ [x] @ zs"  using send_proj_w_prepend_is_in_w by blast
  then have "(ys @ [x] @ zs) \<in> \<L>(p)"  using Suc.prems(2) by blast
  then have "(ys @ [x]) \<in> \<L>(p)" by (metis Lang_app append_assoc) 
  then have "\<exists>s1 s2. (s1, x, s2) \<in> \<R> p" using Lang_app_both lang_implies_trans by blast
  then show ?case by simp
qed


lemma edge_elem_to_edge:
  assumes "q \<in> \<G>\<langle>\<rightarrow>p\<rangle>"
  shows "(q, p) \<in> \<G>"
  using assms by (meson Set.CollectD Set.CollectE)

value "[!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>]\<down>\<^sub>!\<^sub>?"



lemma matching_words_to_peer_sets:
  assumes "tree_topology" and "((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" and "w \<in> \<L>(p)" and "w' \<in> \<L>(q)" and "is_node p" and "is_parent_of p q" and "(w\<down>\<^sub>?) \<noteq> \<epsilon>"
  shows "\<P>\<^sub>?(p) = {q}" and "p \<in> \<P>\<^sub>!(q)"
  using assms
proof -
  have t1: "tree_topology" using assms by simp
  have pq: "is_parent_of p q" using assms by simp
  have "is_node p"  using assms(5) by blast
  then have "\<G>\<langle>\<rightarrow>p\<rangle> = {q}" by (metis is_parent_of.cases pq)
  then have local_node: "is_node_from_local p" using edge_impl_psend_or_qrecv using t1 by blast
  then have "\<P>\<^sub>?(p) = {q} \<or> p \<in> \<P>\<^sub>!(q)" using pq by (meson edge_impl_psend_or_qrecv is_parent_of.cases) 
  then have "(q,p) \<in> \<G>" using is_parent_of_rev(2) pq by auto
  then have qintop: "q \<in> \<G>\<langle>\<rightarrow>p\<rangle>" by blast
  then have "(\<G>\<langle>\<rightarrow>p\<rangle>) \<noteq> {}" by blast
  then have no0: "card (\<G>\<langle>\<rightarrow>p\<rangle>) \<noteq> 0" by (meson card_0_eq finite_peers finite_subset top_greatest)
  have le1: "card (\<G>\<langle>\<rightarrow>p\<rangle>) \<le> 1"  using at_most_one_parent t1 by auto
  then have "card (\<G>\<langle>\<rightarrow>p\<rangle>) \<noteq> 0 \<and> card (\<G>\<langle>\<rightarrow>p\<rangle>) \<le> 1" by (simp add: no0)
  have "card ({q}) = 1" by simp
(*  then have "\<P>\<^sub>?(p) = {q} \<and> p \<in> \<P>\<^sub>!(q)"

  proof (cases "\<P>\<^sub>?(p) = {q}")
    case True
    then have "\<P>\<^sub>?(p) = {q}" by simp
*)    
have "(\<forall>pp. (pp \<noteq> q) \<longrightarrow> (pp,p) \<notin> \<G>)" using \<open>\<G>\<langle>\<rightarrow>p\<rangle> = {q}\<close> by auto
    have "\<exists>a as b bs. (a#as) = (w\<down>\<^sub>?) \<and> (b#bs) = (w'\<down>\<^sub>!)" by (metis assms(2,7) list.map_disc_iff neq_Nil_conv)
    then have "\<exists>a as b bs. (a#as) = (w\<down>\<^sub>?) \<and> (b#bs) = (w'\<down>\<^sub>!) \<and> ((a#as)\<down>\<^sub>!\<^sub>?) = ((b#bs)\<down>\<^sub>!\<^sub>?)" by (metis assms(2))
    then obtain a as b bs where as_def: "(a#as) = (w\<down>\<^sub>?)" and bs_def: "(b#bs) = (w'\<down>\<^sub>!)" and newt: "((a#as)\<down>\<^sub>!\<^sub>?) = ((b#bs)\<down>\<^sub>!\<^sub>?)"
      by blast
    then have "(([a]\<down>\<^sub>!\<^sub>?) @ ( as\<down>\<^sub>!\<^sub>?)) = (([b]\<down>\<^sub>!\<^sub>?) @ ( bs\<down>\<^sub>!\<^sub>?))"  by (metis Cons_eq_appendI append_self_conv2 map_append)
    then have "([a]\<down>\<^sub>!\<^sub>?) = ([b]\<down>\<^sub>!\<^sub>?)" by simp
    have "(w\<down>\<^sub>?) = [a] @ (as)"  by (simp add: as_def)
    have "(w'\<down>\<^sub>!) = [b] @ (bs)"  by (simp add: bs_def)
    then have  "is_input a" 
    proof auto
      assume a_out: "is_output a" 
      then show "False"
      proof -
        have "(w\<down>\<^sub>?) = [a] @ as" by (simp add: \<open>w\<down>\<^sub>? = a # \<epsilon> \<cdot> as\<close>) 
        have "(a#as)\<down>\<^sub>? = ([a]\<down>\<^sub>?) @ (as)\<down>\<^sub>?" by (metis \<open>w\<down>\<^sub>? = a # \<epsilon> \<cdot> as\<close> as_def filter_append)
        then have "([a]\<down>\<^sub>?) = []" using a_out by auto
        then show "False"  by (metis Cons_eq_filterD as_def filter.simps(1,2))
      qed
    qed
    
    have "is_output b" 
    proof (rule ccontr)
      assume b_out: "is_input b" 
      then show "False"
      proof -
        have "(w'\<down>\<^sub>!) = [b] @ bs" by (simp add: \<open>w'\<down>\<^sub>! = b # \<epsilon> \<cdot> bs\<close>) 
        have "(b#bs)\<down>\<^sub>! = ([b]\<down>\<^sub>!) @ (bs)\<down>\<^sub>!" by (metis \<open>w'\<down>\<^sub>! = b # \<epsilon> \<cdot> bs\<close> bs_def filter_append)
        then have c1: "([b]\<down>\<^sub>!) = []" using b_out by auto
        have "(w'\<down>\<^sub>!)\<down>\<^sub>! = (w'\<down>\<^sub>!)"  by fastforce
        then have "([b] @ bs)\<down>\<^sub>! = [b] @ bs" using \<open>w'\<down>\<^sub>! = b # \<epsilon> \<cdot> bs\<close> by auto
        have "([b] @ bs)\<down>\<^sub>! = ([b]\<down>\<^sub>!) @ (bs)\<down>\<^sub>!"  using \<open>(b # bs)\<down>\<^sub>! = (b # \<epsilon>)\<down>\<^sub>! \<cdot> bs\<down>\<^sub>!\<close> \<open>w'\<down>\<^sub>! = b # \<epsilon> \<cdot> bs\<close> bs_def by argo
        then have "([b]\<down>\<^sub>!) @ (bs)\<down>\<^sub>! = [] @ (bs)\<down>\<^sub>!" using c1 by blast
        have "(w'\<down>\<^sub>!)\<down>\<^sub>! = ([b] @ bs)\<down>\<^sub>!" using \<open>(b # \<epsilon> \<cdot> bs)\<down>\<^sub>! = (b # \<epsilon>)\<down>\<^sub>! \<cdot> bs\<down>\<^sub>!\<close> \<open>(b # bs)\<down>\<^sub>! = (b # \<epsilon>)\<down>\<^sub>! \<cdot> bs\<down>\<^sub>!\<close> bs_def by argo 
        then have "(w'\<down>\<^sub>!)\<down>\<^sub>! = ([] @ bs)\<down>\<^sub>!"  using \<open>(b # bs)\<down>\<^sub>! = (b # \<epsilon>)\<down>\<^sub>! \<cdot> bs\<down>\<^sub>!\<close> c1 by auto
        then have "([] @ bs) \<noteq> (w'\<down>\<^sub>!)"  by (metis append.left_neutral bs_def not_Cons_self2)
        have "(([b] @ bs)\<down>\<^sub>!)\<down>\<^sub>! = (([b] @ bs)\<down>\<^sub>!)" by auto
        have "\<forall>c. length (c\<down>\<^sub>!) = length ((c\<down>\<^sub>!)\<down>\<^sub>!)" by simp
        then show "False"  by (metis \<open>w'\<down>\<^sub>!\<down>\<^sub>! = (\<epsilon> \<cdot> bs)\<down>\<^sub>!\<close> append_Nil bs_def impossible_Cons length_filter_le)
      qed
    qed
    then have "is_input a \<and> is_output b \<and> get_message a = get_message b"  using \<open>(a # \<epsilon>)\<down>\<^sub>!\<^sub>? = (b # \<epsilon>)\<down>\<^sub>!\<^sub>?\<close> \<open>is_input a\<close> by auto
    then have "\<exists>s1 s2. (s1, a, s2) \<in> \<R> p"  by (metis NetworkOfCA.recv_proj_w_prepend_has_trans NetworkOfCA_axioms as_def assms(3))
    then have "\<P>\<^sub>?(p) = {q}" 
      by (metis \<open>is_input a\<close> is_parent_of_rev(2) no_recvs_no_input_trans pq
          sends_of_peer_subset_of_predecessors_in_topology subset_singletonD)
    then show "\<P>\<^sub>?(p) = {q}" by blast
    have "\<exists>q1 q2. (q1, b, q2) \<in> \<R> q" by (metis assms(4) bs_def send_proj_w_prepend_has_trans)
    then have "p \<in> \<P>\<^sub>!(q)" by (metis CommunicatingAutomaton.SendingToPeers.simps CommunicatingAutomaton.well_formed_transition
          \<open>\<exists>s1 s2. s1 \<midarrow>a\<rightarrow>p s2\<close> \<open>is_input a \<and> is_output b \<and> get_message a = get_message b\<close> automaton_of_peer
          input_message_to_act_both_known message.inject output_message_to_act_both_known)
    then show "p \<in> \<P>\<^sub>!(q)" by simp
  qed


(*this def. requires *)
inductive is_in_infl_lang :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
IL_root: "\<lbrakk>is_root r; w \<in> \<L>(r)\<rbrakk> \<Longrightarrow> is_in_infl_lang r w" | \<comment>\<open>influenced language of root r is language of r\<close>
IL_node: "\<lbrakk>tree_topology; \<P>\<^sub>?(p) = {q}; w \<in> \<L>(p); is_in_infl_lang q w'; ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> is_in_infl_lang p w" \<comment>\<open>p is any node and q its parent has a matching send for each of p's receives\<close>
(*IL_node: "\<lbrakk>tree_topology; \<P>\<^sub>?(p) = {q}; w \<in> \<L>(p); is_in_infl_lang q w'; ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> is_in_infl_lang p w" \<comment>\<open>p is any node and q its parent has a matching send for each of p's receives\<close>*)

lemma is_in_infl_lang_rev: 
  assumes "is_in_infl_lang p w" and "\<P>\<^sub>?(p) = {q}" and "tree_topology"
  shows "w \<in> \<L>(p)" and "\<exists>w'. is_in_infl_lang q w' \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"
  using assms
proof -
  show "w \<in> \<L>(p)" using assms(1) is_in_infl_lang.simps by blast
  show "\<exists>w'. is_in_infl_lang q w' \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" by (metis assms(1,2) insert_not_empty is_in_infl_lang.simps sends_of_peer_subset_of_predecessors_in_topology
        subset_antisym subset_insertI the_elem_eq)
qed


lemma w_in_infl_lang : "is_in_infl_lang p w \<Longrightarrow>  w \<in> \<L>(p)" using is_in_infl_lang.simps by blast
lemma recv_has_matching_send : "\<lbrakk>\<P>\<^sub>?(p) = {q}; w \<in> \<L>(p); is_in_infl_lang q w'; ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) \<in> (((\<L>(q))\<downharpoonright>\<^sub>!)\<downharpoonright>\<^sub>!\<^sub>?)" 
  using w_in_infl_lang by blast


abbreviation InfluencedLanguage :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sup>* _" [90] 100) where
"\<L>\<^sup>* p \<equiv> {w. is_in_infl_lang p w}"

abbreviation InfluencedLanguageSend :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>!\<^sup>* _" [90] 100) where
"\<L>\<^sub>!\<^sup>* p \<equiv> (\<L>\<^sup>* p)\<downharpoonright>\<^sub>! "

abbreviation InfluencedLanguageRecv :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>?\<^sup>* _" [90] 100) where
"\<L>\<^sub>?\<^sup>* p \<equiv> (\<L>\<^sup>* p)\<downharpoonright>\<^sub>! "

abbreviation ShuffledInfluencedLanguage :: "'peer \<Rightarrow> ('information, 'peer) action language" ("\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion> _" [90] 100) where
"\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion> p \<equiv> shuffled_lang (\<L>\<^sup>* p)"

lemma is_in_infl_lang_rev2: 
  assumes "w \<in> \<L>\<^sup>* p" and "\<P>\<^sub>?(p) = {q}" and "tree_topology"
  shows "w \<in> \<L>(p)" and "\<exists>w'. w'\<in> \<L>\<^sup>* q \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"
  using assms
proof -
  show "w \<in> \<L>(p)" using assms(1) is_in_infl_lang.simps by blast
  show "\<exists>w'. w' \<in> \<L>\<^sup>* q \<and> w\<down>\<^sub>?\<down>\<^sub>!\<^sub>? = w'\<down>\<^sub>!\<down>\<^sub>!\<^sub>?" using assms(1,2) is_in_infl_lang.simps[of p w] mem_Collect_eq[of _ "is_in_infl_lang q"]
      mem_Collect_eq[of w "is_in_infl_lang p"] sends_of_peer_subset_of_predecessors_in_topology[of p]
      singleton_insert_inj_eq[of q _ "{}"] singleton_insert_inj_eq[of q q "{}"] subset_antisym[of "{q}" "{}"]
    by auto
qed


(*infl_lang only keeps words that can be built depending on the ancestors
this means there may be less words in the influenced language than in the original one
see Def. 4.2., Ex. 4.1*)
lemma infl_lang_subset_of_lang:
  shows "(\<L>\<^sup>* p) \<subseteq> (\<L> p)"
  using w_in_infl_lang by fastforce

lemma lang_subset_infl_lang:
  assumes "is_root p"
  shows "(\<L> p) \<subseteq> (\<L>\<^sup>* p)"
proof auto
  fix x
  assume "x \<in> \<L> p"
  show "is_in_infl_lang p x" using IL_root \<open>x \<in> \<L> p\<close> assms by presburger
qed


lemma root_lang_is_infl_lang: 
  assumes "is_root p" and "w \<in> \<L>(p)" 
  shows "w \<in> \<L>\<^sup>*(p)"
  using IL_root assms(1,2) by blast


lemma eps_in_infl:
  assumes "tree_topology" and "p \<in> \<P>"
  shows "\<epsilon> \<in> \<L>\<^sup>*(p)"
proof -
  have a1: "((\<epsilon>\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((\<epsilon>\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"  by simp
  have a2: "\<epsilon> \<in> \<L>(p)" by (meson CommunicatingAutomaton.REmpty2 CommunicatingAutomaton.Traces.simps automaton_of_peer)
  have "\<exists>ps. path_to_root p ps"  by (simp add: assms(1) path_to_root_exists)
  then obtain ps where "path_to_root p ps" by blast
  from this a2 show ?thesis 
  proof (induct arbitrary: ps)
    case (PTRRoot p)
    then show ?case using root_lang_is_infl_lang by blast
  next
    case (PTRNode p q as)
    have "\<epsilon> \<in> \<L> q"  by (meson CommunicatingAutomaton.REmpty2 CommunicatingAutomaton.Traces.simps automaton_of_peer)
    then have "\<epsilon> \<in> \<L>\<^sup>* q"  using PTRNode.hyps(4) by auto
    then show ?case sledgehammer
  qed
  have "is_root p \<or> is_node p" using assms(1) root_or_node by blast
  
  then show ?thesis
  proof (cases "is_root p")
    case True
    then show ?thesis using IL_root \<open>\<epsilon> \<in> \<L> p\<close> by blast
  next
    case False
    have "\<forall>q. \<epsilon> \<in> \<L>(p)" by (simp add: \<open>\<epsilon> \<in> \<L> p\<close>)
    have "\<forall>x y. (is_parent_of x y \<and> \<epsilon> \<in> \<L>(x) \<and> \<epsilon> \<in> \<L>(y)) \<longrightarrow> (((\<epsilon>\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((\<epsilon>\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?))" by auto
    then show ?thesis sorry
  qed
qed


lemma infl_lang_has_tree_topology:
  assumes "w \<in> \<L>\<^sup>*(p)"
  shows "tree_topology"
  using assms is_in_infl_lang.simps by blast

(* if w is in influenced language of a node p, its parent q must have matching sends for each receive in p*)
lemma infl_parent_child_matching_ws :
  fixes w :: "('information, 'peer) action word"
  assumes "w \<in> \<L>\<^sup>*(p)" and "\<P>\<^sub>?(p) = {q}"
  shows "\<exists>w'.  w' \<in> \<L>\<^sup>*(q) \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"
  using assms(1,2) infl_lang_has_tree_topology is_in_infl_lang_rev2(2) by blast

lemma "infl_parent_child_unique":
  assumes "w \<in> \<L>\<^sup>*(p)" and "is_parent_of p q" 
  shows "\<P>\<^sub>?(p) = {q}" 
  by (metis (no_types, lifting) UNIV_def assms(2) eps_in_infl insert_not_empty is_in_infl_lang.simps
      is_parent_of.simps local_to_global_root mem_Collect_eq sends_of_peer_subset_of_predecessors_in_topology
      subset_singleton_iff)


lemma word_in_shuffled_infl_lang :
  fixes w :: "('information, 'peer) action word"
  assumes "w \<in> \<L>\<^sup>*(p)"
  shows "w \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)" 
  by (meson assms shuffle_id)

lemma language_shuffle_subset :
  shows "\<L>\<^sup>*(p) \<subseteq> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)"
  using word_in_shuffled_infl_lang by auto

lemma shuffled_lang_rev :
  assumes "v \<in> \<L>\<^sup>*(p)"
  shows "\<exists>v'. ( v' \<squnion>\<squnion>\<^sub>? v \<and> v' \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p))"
  using assms by (rule CommunicatingAutomata.valid_input_shuffles_of_lang)








lemma input_or_output_action : "\<forall>x. is_input x \<or> is_output x"  by simp
lemma input_or_output_word : "\<forall>w. (w \<noteq> \<epsilon>) \<Longrightarrow> (((w\<down>\<^sub>?) \<noteq> \<epsilon>) \<or> (\<epsilon> \<noteq> (w\<down>\<^sub>!)))" by blast

lemma filter_recursion : "filter f (filter f xs) = filter f xs"  by simp

lemma filter_head_helper :
  assumes  "x # (filter f xs) = (filter f (x#xs))"
shows "f x"
proof (induction xs)
  case Nil
  then show ?case by (meson Cons_eq_filterD assms)
next
  case (Cons a xs)
  then show ?case by simp
qed


(*
lemma root_no_recvss :
  fixes w :: "('information, 'peer) action word"
  assumes "\<P>\<^sub>?(r) = {}" and "w \<in> (\<L>(r))"
  shows "w = (w\<down>\<^sub>!)"
proof (induction w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case
  proof (cases "is_output a")
    case True
    then have "is_output a" by simp
    then have "[a] = [a]\<down>\<^sub>!"  by simp
    moreover have "[a] @ w = a # w " by simp
    moreover have "(a # w) = ([a]\<down>\<^sub>!) @ (w\<down>\<^sub>!)" 
      using calculation(1,2) local.Cons by presburger
    then show ?thesis
      by (metis calculation(1) filter_append local.Cons)
  next
    case False
    then have "is_input a" by simp
    then have "[] = [a]\<down>\<^sub>!" by simp
    moreover have "w = ([a]\<down>\<^sub>!) @ (w\<down>\<^sub>!)"   using calculation local.Cons by auto
    moreover have "\<exists> p. p = get_object a" by simp
    moreover have "\<exists> q. q = get_actor a" by simp
    ultimately show ?thesis using assms Cons
    proof (cases "\<exists> s1 s2. (s1, a, s2) \<in> \<R>(r)" )
      case True
      then obtain s1 s2 where "(s1, a, s2) \<in> \<R>(r)" by auto
      then show ?thesis  using False assms(1) empty_receiving_from_peers4 by blast
    next
      case False
      then have "\<forall> s1 s2. (s1, a, s2) \<notin> \<R>(r)" by simp
      then have "(a # w) \<notin> (\<L>(r))"  using \<open>is_input a\<close> local.Cons  using no_input_trans_no_word_in_lang by blast
      moreover have "(a # w) \<in> (\<L>(r)) = False"  by (simp add: calculation)
      moreover have "(\<P>\<^sub>?(r) = {}) \<and> (a # w) \<in> (\<L>(r)) = False" by (simp add: assms(1) calculation(1))
      moreover have "((\<P>\<^sub>?(r) = {}) \<and> (a # w) \<in> (\<L>(r))) \<Longrightarrow>(a # w) = ((a # w)\<down>\<^sub>!)"  by (simp add: calculation(1))
      moreover have "\<forall>a. is_input a \<longrightarrow> (a # w) \<notin> (\<L>(r))"  using assms(1) no_input_trans_no_word_in_lang no_input_trans_root by blast
      moreover have "\<P>\<^sub>?(r) = {}" using assms by simp
      moreover have "\<epsilon> = (a # \<epsilon>)\<down>\<^sub>!" using \<open>\<epsilon> = (a # \<epsilon>)\<down>\<^sub>!\<close> by auto
      ultimately have "False" using assms Cons \<open>(a # w) \<notin> (\<L>(r))\<close> sledgehammer
      ultimately show ?thesis using False Cons sledgehammer
      moreover have "(a # w) = ((a # w)\<down>\<^sub>!)" sledgehammer 
      ultimately show ?thesis sledgehammer
    qed
  qed
qed
*)

lemma word_implies_recv_word : 
  assumes "w \<in> (\<L>(r))"
  shows "(w\<down>\<^sub>?) \<in> (\<L>\<^sub>?(r))"
  using assms by blast

lemma word_implies_recv_word_rec : 
  assumes "w \<in> (\<L>\<^sub>?(r))"
  shows "\<exists> xs. xs \<in> (\<L>(r)) \<and> (xs\<down>\<^sub>?) = w" 
  using assms by blast

lemma word_implies_partitioned_word :
  assumes "w \<in> (\<L>(r))" and "w \<noteq> \<epsilon>"
  shows "\<exists> xs ys a. (xs @ [a] @ ys) \<in> (\<L>(r)) \<and> (w = (xs @ [a] @ ys))"
  by (metis Cons_eq_appendI append_self_conv2 assms(1,2) rev_exhaust)

lemma word_implies_recv_word_rec2 : 
  assumes "(xs @ [a] @ ys) \<in> (\<L>\<^sub>?(r))"
  shows "\<exists> w. w \<in> (\<L>(r)) \<and> (w\<down>\<^sub>?) = (xs @ [a] @ ys)" 
  using assms by auto

lemma word_rec_partition : 
  assumes "w \<in> (\<L>(r)) \<and> (w\<down>\<^sub>?) = (xs @ [a] @ ys)" 
  shows "(xs @ [a] @ ys) \<in> (\<L>\<^sub>?(r))"
  using assms by force

lemma output_proj_input_yields_eps : 
  assumes "(w\<down>\<^sub>!) = w"
  shows "(w\<down>\<^sub>?) = \<epsilon>"
  by (metis assms filter_False filter_id_conv)

lemma input_proj_output_yields_eps :
assumes "(w\<down>\<^sub>?) = w"
shows "(w\<down>\<^sub>!) = \<epsilon>"
  by (metis assms filter_False filter_id_conv)

lemma input_proj_nonempty_impl_input_act :
  assumes "(w\<down>\<^sub>?) \<noteq> \<epsilon>"
  shows "\<exists> xs a ys. ((w\<down>\<^sub>?) = (xs @ [a] @ ys)) \<and> is_input a"
  by (metis append.left_neutral append_Cons assms filter.simps(2) filter_recursion
      input_proj_output_yields_eps list.distinct(1) list.exhaust)

lemma output_proj_nonempty_impl_input_act :
  assumes "(w\<down>\<^sub>!) \<noteq> \<epsilon>"
  shows "\<exists> xs a ys. ((w\<down>\<^sub>!) = (xs @ [a] @ ys)) \<and> is_output a"
  by (metis append.left_neutral append_Cons assms filter_empty_conv filter_recursion split_list)


(*
lemma root_no_recvs : 
  assumes "\<P>\<^sub>?(r) = {}" and "w \<in> (\<L>(r))"
  shows "(w\<down>\<^sub>?) = \<epsilon>"
proof (rule ccontr)
  assume "(w\<down>\<^sub>?) \<noteq> \<epsilon>"
  then show "False"
  proof
    have "\<exists> x  xs. (x # xs) = (w\<down>\<^sub>?)"  using \<open>w\<down>\<^sub>? \<noteq> \<epsilon>\<close> list.collapse by blast
    moreover obtain x xs where "(x#xs) = (w\<down>\<^sub>?)" using calculation by blast
    moreover have "(filter is_input (w\<down>\<^sub>?)) = (w\<down>\<^sub>?)" using filter_recursion by blast
    moreover have "filter is_input (x#xs) = (x#xs)"   by (simp add: calculation(2))
    moreover have "x # (filter is_input xs) = filter is_input (x#xs)" 
      by (metis calculation(4) filter.simps(2) filter_id_conv list.set_intros(1))
    moreover have "is_input x" using calculation(5) by force
    moreover have "\<R>(r) \<noteq> {}" 
      by (metis NetworkOfCA.no_word_no_trans NetworkOfCA_axioms \<open>w\<down>\<^sub>? \<noteq> \<epsilon>\<close> assms(2) empty_iff filter.simps(1)
          neq_Nil_conv)
    moreover have "(x # xs) \<in> (\<L>\<^sub>?(r))" 
      using assms(2) calculation(2) by blast

    ultimately show "(w\<down>\<^sub>?) = \<epsilon>" sledgehammer
  qed
qed


lemma root_only_sends : "\<lbrakk>\<P>\<^sub>?(r) = {}; w \<in> \<L>(r)\<rbrakk> \<Longrightarrow> (w\<down>\<^sub>!) = w" sorry

\<comment>\<open>this is a rule I removed from test2, because the two existing rules should suffice,
this needs to be proven however, which is not yet fully accomplished
in particular, it needs to be shown that if P(r) = {} (i.e. r is root), then any words in w \<in> \<L>(r) are outputs/sends
because the root does not receive any messages.
Also useful would be that if w \<in> \<L>(p), then for each x in w, there must be a transition in \<R>(r)\<close>
lemma test2_rule_q_direct_child_of_root : "\<lbrakk>\<P>\<^sub>?(q) = {r}; \<P>\<^sub>?(r) = {}; w \<in> \<L>(q); ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) \<in> ((\<L>(r))\<downharpoonright>\<^sub>!\<^sub>?) \<rbrakk> \<Longrightarrow> test2 q w"
proof
  assume "\<P>\<^sub>?(q) = {r}" and "\<P>\<^sub>?(r) = {}" and "w \<in> \<L>(q)" and  "((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) \<in> ((\<L>(r))\<downharpoonright>\<^sub>!\<^sub>?)"
  then have "\<exists>w'. w' \<in> \<L>(r)" using \<open>((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) \<in> ((\<L>(r))\<downharpoonright>\<^sub>!\<^sub>?)\<close> by blast
  moreover obtain w' where "w' \<in> \<L>(r)" and "((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = w'\<down>\<^sub>!\<^sub>?" using \<open>\<exists>w'. w' \<in> \<L> r\<close>  \<open>((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) \<in> (\<L> r)\<downharpoonright>\<^sub>!\<^sub>?\<close> by blast
  moreover have "test2 r w'"  by (simp add: \<open>\<P>\<^sub>? r = {}\<close> calculation(2) t00)
  ultimately show ?thesis 
  by (metis \<open>\<P>\<^sub>? q = {r}\<close> \<open>\<P>\<^sub>? r = {}\<close> \<open>w \<in> \<L> q\<close> root_only_sends test2.simps)
  moreover have "w\<down>\<^sub>?\<down>\<^sub>!\<^sub>? = w'\<down>\<^sub>!\<down>\<^sub>!\<^sub>?" using \<open>\<P>\<^sub>? r = {}\<close> 
    by (simp add: \<open>w' \<in> \<L> r\<close> \<open>w\<down>\<^sub>?\<down>\<^sub>!\<^sub>? = w'\<down>\<^sub>!\<^sub>?\<close> root_only_sends)
qed

lemma "\<lbrakk>x = 2; y = x + 1; y > x; y < 5\<rbrakk> \<Longrightarrow> y = 3" by auto



abbreviation infl_lang2 :: "'peer \<Rightarrow> ('information, 'peer) action language" where
"infl_lang2 p \<equiv> {w | w. test p w}"
*)
value "[!\<langle>x\<rangle>, ?\<langle>y\<rangle>, ?\<langle>z\<rangle>]"
value "let w = [!\<langle>x\<rangle>, ?\<langle>y\<rangle>, ?\<langle>z\<rangle>] in ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)"
value "let w' = [?\<langle>a\<rangle>, !\<langle>y\<rangle>, !\<langle>z\<rangle>] in ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"


\<comment> \<open>p receives from no one and there is no q that sends to p\<close>
abbreviation no_sends_to_or_recvs_in :: "'peer \<Rightarrow> bool"  where
"no_sends_to_or_recvs_in p \<equiv> (\<P>\<^sub>?(p) = {} \<and> (\<forall>q. p \<notin> \<P>\<^sub>!(q)))"



\<comment> \<open>for each sending action, add the matching receive action directly after it\<close>
fun add_matching_recvs :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word" where
"add_matching_recvs [] = []" |
"add_matching_recvs (a # w) = (if is_output a
      then a # (?\<langle>get_message a\<rangle>) # add_matching_recvs w 
      else a # add_matching_recvs w)"

lemma add_matching_recvs_app : 
  shows "add_matching_recvs (xs \<cdot> ys) = (add_matching_recvs xs) \<cdot> (add_matching_recvs ys)"
proof (induct xs arbitrary: ys rule: add_matching_recvs.induct)
  case 1
  then show ?case by simp
next
  case (2 a w)
  then show ?case by simp
qed

value "(add_matching_recvs [!\<langle>m\<rangle>])"

lemma decompose_send :
  assumes "(w\<down>\<^sub>!) \<noteq> \<epsilon>"
  shows "\<exists>v a q p. (w\<down>\<^sub>!) = v \<cdot> [!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]"
proof -
  have "\<exists> v x. (w\<down>\<^sub>!) = v \<cdot> [x]" by (metis assms rev_exhaust)
  then obtain v x where "(w\<down>\<^sub>!) = v \<cdot> [x]" by auto 
  then have "is_output x" by (metis assms filter_id_conv filter_recursion last_in_set last_snoc)
  then obtain a q p where "x = !\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>"  by (metis action.exhaust is_output.simps(2) message.exhaust)
  then show ?thesis by (simp add: \<open>w\<down>\<^sub>! = v \<cdot> x # \<epsilon>\<close>)
qed


lemma adding_recvs_keeps_send_order :
shows "w\<down>\<^sub>! = (add_matching_recvs w)\<down>\<^sub>!"
proof (induct w)
  case Nil
  then show ?case by simp
next
  case (Cons a w')
  then show ?case using Cons
  proof (cases "is_input a")
    case True
    then show ?thesis by (simp add: local.Cons)
  next
    case False
    then show ?thesis  by (simp add: local.Cons)
  qed
qed




lemma simulate_sync_step_with_matching_recvs_helper:
  assumes "mbox_step c1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c2 \<and> mbox_step c2 (?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c3"
  shows "c1 \<midarrow>\<langle>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>), \<infinity>\<rangle>\<rightarrow> c2 \<and> c2 \<midarrow>\<langle>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> c3"
  by (simp add: assms)

lemma simulate_sync_step_with_matching_recvs_helper2:
  assumes "c1 \<midarrow>\<langle>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>), \<infinity>\<rangle>\<rightarrow> c2 \<and> c2 \<midarrow>\<langle>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> c3"
  shows "mbox_run c1 None [!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>] [c2,c3]"
  using assms 
proof -
  have "mbox_run c1 None [] []"  by (simp add: MREmpty) 
  have "last (c1 # []) \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> c2"  by (simp add: assms)
  have "mbox_run c1 None [!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>] [c2]"  by (metis MRComposedInf \<open>last (c1 # \<epsilon>) \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> c2\<close> \<open>mbox_run c1 None \<epsilon> \<epsilon>\<close>
        self_append_conv2) 
  have "last (c1 # [c2]) \<midarrow>\<langle>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> c3" by (simp add: assms)
  have "mbox_run c1 None [!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>] [c2, c3]"  using MRComposedInf \<open>last (c1 # c2 # \<epsilon>) \<midarrow>\<langle>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> c3\<close>
      \<open>mbox_run c1 None (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle> # \<epsilon>) (c2 # \<epsilon>)\<close> by fastforce
  show ?thesis by (simp add: \<open>mbox_run c1 None (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle> # ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle> # \<epsilon>) (c2 # c3 # \<epsilon>)\<close>)
qed

lemma simulate_sync_step_with_matching_recvs:
  assumes "c1 \<midarrow>\<langle>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>), \<infinity>\<rangle>\<rightarrow> c2 \<and> c2 \<midarrow>\<langle>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> c3"
  shows "mbox_run c1 None (add_matching_recvs [!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>]) [c2,c3]"
  by (simp add: assms simulate_sync_step_with_matching_recvs_helper2)



\<comment> \<open>shows that we can simulate a synchronous run by adding the matching receives after each send\<close>
\<comment> \<open>this also shows that both the first config and the last config of the mbox run are the same as in sync run\<close>
lemma sync_run_to_mbox_run :
  assumes "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xcs" and "xcs \<noteq> []"
  shows "\<exists>xcm. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (add_matching_recvs w) xcm \<and> (\<forall>p. (last xcm p ) = ((last xcs) p, \<epsilon> ))"
  using assms
proof (induct "length w" arbitrary: w xcs)
  case 0
  then have "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xcs = sync_run \<C>\<^sub>\<I>\<^sub>\<zero> [] xcs" by simp
  then have "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xcs = sync_run \<C>\<^sub>\<I>\<^sub>\<zero> [] []" 
    by (simp add: "0.prems"(1) SREmpty)
  then show ?case 
    by (metis "0.prems"(2) \<open>sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xcs = sync_run \<C>\<^sub>\<I>\<^sub>\<zero> \<epsilon> xcs\<close> append_is_Nil_conv
        not_Cons_self2 sync_run.simps) 
next
  case (Suc x)
  then have fact1: "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xcs" by auto
  then have fact2: "Suc x = |w|" using Suc.hyps(2) by auto
  then obtain v a xc s_a where "w = v @ [a]" and v_sync: "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> v xc" and xc_def : "xcs = xc @ [s_a]"
    by (metis Suc.prems(2) fact1 sync_run.simps)
  then have "length v = x" 
    by (simp add: Suc_inject fact2)
  then show ?case using assms Suc 
  proof (cases "xc \<noteq> \<epsilon>")
    case True
  (*assume "xc \<noteq> \<epsilon>"*)
   have "\<exists>xcm. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (add_matching_recvs v) xcm \<and> (\<forall>p. (last xcm p ) = ((last xc) p, \<epsilon> ))"
      by (simp add: Suc.hyps(1) True \<open>|v| = x\<close> v_sync)
  then obtain xcm where  v_mbox: "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (add_matching_recvs v) xcm" 
and v_state :"(\<forall>p. (last xcm p ) = ((last xc) p, \<epsilon> ))" by auto
  then obtain s_1  where s_1_1: "sync_step s_1 a s_a" and s_1_2: "s_1 = last xc"
    by (metis \<open>w = v \<cdot> a # \<epsilon>\<close> \<open>xc \<noteq> \<epsilon>\<close> fact1 last_ConsR sync_run_rev xc_def)
  then obtain i p q where a_decomp: "a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" using sync_step_rev(3) by blast
  let ?c1 = "(\<lambda>x. (s_1 x, \<epsilon>))"
  let ?c3 = "(\<lambda>x. (s_a x, \<epsilon>))" 
  let ?c2 = "(?c3)(q := ((s_1) q, [(i\<^bsup>p\<rightarrow>q\<^esup>)]))"
  have c1_def : "?c1 = (\<lambda>x. (s_1 x, \<epsilon>))" by simp
  have c3_def : "?c3 = (\<lambda>x. (s_a x, \<epsilon>))" by simp
  have c2_def : "?c2 = (?c3)(q := ((s_1) q, [(i\<^bsup>p\<rightarrow>q\<^esup>)]))" by simp
  have "sync_step s_1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) s_a"  using a_decomp s_1_1 by auto
  then have sync_abb : "s_1 \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<zero>\<rangle>\<rightarrow> s_a" by simp
  then have mbox_steps: "let c1 = \<lambda>x. (s_1 x, \<epsilon>); c3 = \<lambda>x. (s_a x, \<epsilon>); c2 = (c3)(q := (s_1 q, [(i\<^bsup>p\<rightarrow>q\<^esup>)])) in
  mbox_step c1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c2 \<and> mbox_step c2 (?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None c3"  by (simp add: sync_step_to_mbox_steps)
  then have mbox_steps_init : "mbox_step ?c1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None ?c2 \<and> mbox_step ?c2 (?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None ?c3" by metis
  then have a_mbox_run: "mbox_run ?c1 None (add_matching_recvs ([a])) ([?c2, ?c3])"  using a_decomp simulate_sync_step_with_matching_recvs by blast
  then have "(\<forall>p. fst (last xcm p ) = (s_1) p )"   by (simp add: s_1_2 v_state)
  then have "(\<forall>p. (last xcm p ) = ?c1 p)"  by (simp add: v_state)
  then have last_config_xcm : "last xcm = ?c1" by auto
  then have "(last xcm) \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> ?c2"  by (metis mbox_steps)
  then have "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (add_matching_recvs v) xcm" by (simp add: v_mbox)
  then have mbox_inter : "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None ((add_matching_recvs v)@ [!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>]) (xcm@[?c2])" 
    by (smt (verit) Nil_is_append_conv
        \<open>last xcm \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> (\<lambda>x. (s_a x, \<epsilon>)) (q := (s_1 q, i\<^bsup>p\<rightarrow>q\<^esup> # \<epsilon>))\<close> \<open>xc \<noteq> \<epsilon>\<close>
        add_matching_recvs.elims last_ConsR list.distinct(1) mbox_run.simps sync_run.cases
        v_sync)
  then have "(last (xcm@[?c2])) \<midarrow>\<langle>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> ?c3"  by (simp add: mbox_steps_init)
then have mbox_inter2 : "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None ((add_matching_recvs v)@ [!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>]@[?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>]) (xcm@[?c2]@[?c3])" 
  using MRComposedInf mbox_inter by fastforce
  \<comment> \<open>found existing run when xc not empty\<close>
  then have mbox_run_final: "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None ((add_matching_recvs (v@[a]))) (xcm@[?c2,?c3])"
    using NetworkOfCA.add_matching_recvs_app NetworkOfCA_axioms a_decomp append_Cons by fastforce
  then have xc_nonempty_thesis : "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None ((add_matching_recvs (v@[a]))) (xcm@[?c2,?c3]) \<and> (\<forall>p. (last (xcm@[?c2,?c3]) p ) = ((last xcs) p, \<epsilon> ))" 
    by (simp add: xc_def)
  then show ?thesis  using \<open>w = v \<cdot> a # \<epsilon>\<close> by blast

next
  case False
  then have xc_empty: "xc = \<epsilon>" by simp
  then have w_a : "w = [a]" using NetworkOfCA.sync_run.cases NetworkOfCA_axioms \<open>w = v \<cdot> a # \<epsilon>\<close> v_sync by blast
  then have "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xcs = sync_run \<C>\<^sub>\<I>\<^sub>\<zero> [a] xcs"  by (simp add: SREmpty fact1)
  then obtain i p q C where C_def: "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> [a] [C]" and C_def2: "xcs = [C]" and a_def: "a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>" 
    by (metis fact1 self_append_conv2 sync_run_rev sync_step_rev(3) xc_def xc_empty)
  let ?c1 = "(\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>))"
  let ?c3 = "(\<lambda>x. (C x, \<epsilon>))" 
  let ?c2 = "(?c3)(q := ((\<C>\<^sub>\<I>\<^sub>\<zero>) q, [(i\<^bsup>p\<rightarrow>q\<^esup>)]))"
  have c1_def : "?c1 = (\<lambda>x. (\<C>\<^sub>\<I>\<^sub>\<zero> x, \<epsilon>))" by simp
  have c3_def : "?c3 = (\<lambda>x. (C x, \<epsilon>))" by simp
  have c2_def : "?c2 = (?c3)(q := ((\<C>\<^sub>\<I>\<^sub>\<zero>) q, [(i\<^bsup>p\<rightarrow>q\<^esup>)]))" by simp
  have "(\<forall>p. \<C>\<^sub>\<I>\<^sub>\<mm> p = (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>))" by simp
  then have "\<C>\<^sub>\<I>\<^sub>\<mm> = (\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>))" by simp
  then have "?c1 = \<C>\<^sub>\<I>\<^sub>\<mm>" by simp
  have "sync_step \<C>\<^sub>\<I>\<^sub>\<zero> a C" by (metis C_def2 \<open>w = v \<cdot> a # \<epsilon>\<close> fact1 last_ConsL self_append_conv2 sync_run_rev)
  then have "\<C>\<^sub>\<I>\<^sub>\<zero> \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<zero>\<rangle>\<rightarrow> C" by (simp add: a_def)
   then have steps : "mbox_step ?c1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None ?c2 \<and> mbox_step ?c2 (?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None ?c3" 
     by (metis sync_step_to_mbox_steps)
  then have "mbox_run ?c1 None (add_matching_recvs ([a])) [?c2, ?c3]" 
    using a_def simulate_sync_step_with_matching_recvs by blast
  then have "mbox_run ?c1 None (add_matching_recvs w) [?c2, ?c3]" by (simp add: w_a)
  then have "mbox_run ?c1 None (add_matching_recvs w) [?c2, ?c3]" by simp
  then have "mbox_run (\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)) None (add_matching_recvs w) [?c2, ?c3]" by simp
  then show ?thesis  using C_def2 by auto
qed
qed


lemma empty_sync_run_to_mbox_run :
  assumes "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xcs" and "xcs = []"
  shows "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (add_matching_recvs w) []"
  using assms by (metis (no_types, lifting) MREmpty Nil_is_append_conv add_matching_recvs.simps(1)
      not_Cons_self2 sync_run.simps)


lemma no_inputs_implies_only_sends :
  assumes "\<P>\<^sub>?(p) = {}" 
  shows "\<forall>w. w \<in> \<L>(p) \<longrightarrow> (w = w\<down>\<^sub>!)"
  using assms
proof auto
  fix w 
  show "\<P>\<^sub>? p = {} \<Longrightarrow> w \<in> \<L> p \<Longrightarrow> w = w\<down>\<^sub>!"
  proof -
    assume "w \<in> \<L> p"
    then show "w = w\<down>\<^sub>!"
    proof (induct "length w" arbitrary: w)
      case 0
      then show ?case by simp
    next
      case (Suc x)
      then obtain v a where w_def: "w = v @ [a]" and v_len: "length v = x" by (metis length_Suc_conv_rev)
      then have "v \<in> \<L> p" using Lang_app Suc.prems by blast
      then have "v = v\<down>\<^sub>!" by (simp add: Suc.hyps(1) v_len)
      then obtain s2 s3 where v_run: "(\<I> p) \<midarrow>v\<rightarrow>\<^sup>*p s2" and a_run : "s2 \<midarrow>[a]\<rightarrow>\<^sup>*p s3"
        using Lang_app_both Suc.prems w_def by blast
      then have "\<forall>s1 s2. (s1, a, s2) \<in> \<R>(p) \<longrightarrow> is_output a" using assms no_recvs_no_input_trans by blast
      then have " (s2, a, s3) \<in> \<R>(p)" using a_run lang_implies_trans by force
      then have "is_output a" by (simp add: \<open>\<forall>s1 s2. s1 \<midarrow>a\<rightarrow>p s2 \<longrightarrow> is_output a\<close>)
      then show ?case  using \<open>v = v\<down>\<^sub>!\<close> w_def by auto
    qed
  qed
qed

lemma no_inputs_implies_only_sends_alt :
  assumes "\<P>\<^sub>?(p) = {}" and "w \<in> \<L>(p)" 
  shows "w = w\<down>\<^sub>!"
  using assms(1,2) no_inputs_implies_only_sends by auto

lemma no_inputs_implies_send_lang :
  assumes "\<P>\<^sub>?(p) = {}"
  shows "\<L>(p) = (\<L>(p))\<downharpoonright>\<^sub>!"
proof 
  show " \<L> p \<subseteq> (\<L> p)\<downharpoonright>\<^sub>!" using assms no_inputs_implies_only_sends_alt by auto
  next
    show " (\<L> p)\<downharpoonright>\<^sub>! \<subseteq> \<L> p" using assms no_inputs_implies_only_sends_alt by auto
qed


lemma shortest_shuffled_words :
  assumes "v \<in> (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p))" and "v = w # ?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # xs" and "xs = xs\<down>\<^sub>!"
  shows "\<exists>v'. v \<squnion>\<squnion>\<^sub>? v' \<and> v' = w # xs @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]"
  sorry


lemma only_one_actor_proj:
  assumes "w = w\<down>\<^sub>q" and "p \<noteq> q"
  shows "w\<down>\<^sub>p = \<epsilon>"
  by (metis (mono_tags, lifting) assms(1,2) filter_False filter_id_conv)

value "tl ([1,2,3]::int list)"


fun get_C2 :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> (('information, 'peer) action) \<Rightarrow> 'state \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word))" where
"get_C2 C1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) p2 = (C1(p := (p2, snd (C1 p))))(q := (fst (C1 q), (snd (C1 q))\<cdot>[(i\<^bsup>p\<rightarrow>q\<^esup>)]))" |
"get_C2 C1 (?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) p2 = C1( p := (p2, tl (snd (C1 p))  ))"

lemma get_C2_valid :
  assumes "is_mbox_config C1" and "fst (C1 p) \<midarrow>(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rightarrow>p s2"
  shows "mbox_step C1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) None (get_C2 C1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) s2)"
  using assms(1,2) send_trans_to_mbox_step by force



fun states_to_configs :: "('information, 'peer) action word \<Rightarrow> 'state \<Rightarrow> 'state list \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) list" where
"states_to_configs \<epsilon> s0 xs C = []" |
"states_to_configs (a # w) s0 (s1 # xs) C = C # (states_to_configs w s1 xs (get_C2 C a s1))" 

(*converts a config list of an mbox run to a set of states (for each changed state for p)*)
fun conf2s :: "'peer \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) list \<Rightarrow> 'state list" where
"conf2s p [] = []" |
"conf2s p [C] = (if (fst (C p)) = (\<I> p) then [] else [fst (C p)])" |
"conf2s p (C0 # C1 # Cs) =  (if (fst (C0 p)) = (fst (C1 p)) then conf2s p (C1 # Cs) else (fst (C0 p)) # conf2s p (C1 # Cs))"

lemma conf2s_to_run:
  assumes "mbox_run C k w Cs"
  shows "run_of_peer_from_state p (fst (C p)) (w\<down>\<^sub>p) (conf2s p Cs)"
  using assms
  sorry

 

inductive path_mbox_eq :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'state \<Rightarrow> 'state list \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) list \<Rightarrow> bool" for p ::"'peer" where
PM_eps: "path_mbox_eq p \<epsilon> (\<I> p) [] (\<C>\<^sub>\<I>\<^sub>\<mm>) []" |
PM_send: "\<lbrakk>a = (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>); C2 = get_C2 C1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) s2 \<rbrakk> \<Longrightarrow> path_mbox_eq p [a] s0 [s2] C1 [C2]" |
PM_recv: "\<lbrakk>a = (?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>); C2 = get_C2 C1 (?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) s2 \<rbrakk> \<Longrightarrow> path_mbox_eq p [a] s0 [s2] C1 [C2]" |
PM_step_send: "\<lbrakk>path_mbox_eq p w s0 xs C0 Cs; fst ((last (C0#Cs)) p) \<midarrow>a\<rightarrow>p s2; a = (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rbrakk> \<Longrightarrow> path_mbox_eq p w s0 xs C0 (Cs@[get_C2 C0 a s2])" |
PM_step_recv: "\<lbrakk>path_mbox_eq p w s0 xs C0 Cs; fst ((last (C0#Cs)) p) \<midarrow>a\<rightarrow>p s2; a = (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)\<rbrakk> \<Longrightarrow> path_mbox_eq p w s0 xs C0 (Cs@[get_C2 C0 a s2])"





\<comment> \<open>dasselbe wie getC2 aber gette den gesamten run, also alle configs ab initial config bis wort gelesen\<close>
fun get_Cs :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> ('state \<times> ('information, 'peer) action \<times> 'state) list \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) list" where
"get_Cs C [] = [C]" |
"get_Cs C ((s1,a,s2) # xs) = C # (get_Cs (get_C2 C a s2) xs)"

inductive cstep_valid :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> (('information, 'peer) action) \<Rightarrow> bool" where
valid_send: "\<lbrakk>\<exists>p2. p2 \<in> \<S> p \<and> (fst (C1 p), (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>), p2) \<in> \<R> p \<and> (get_C2 C1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) p2) = C2 \<rbrakk> \<Longrightarrow> cstep_valid C1 (!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>)"

(* takes a start config and a word, returns the list of traversed configs *)
fun w2cs ::  "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> (('information, 'peer) action word) \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) list option" where
"w2cs C [] = (Some [])" |
"w2cs C ((!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) # w) = (Some [])" |
"w2cs C ((?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) # w) = (Some [])"


(*(if ((snd (C1 p)) \<noteq> []) \<and> ((i\<^bsup>p\<rightarrow>q\<^esup>) = hd (snd (C1 p)))
then C1( p := (p2, tl (snd (C1 p))  ))  
else C1)"*)


inductive stepc :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> ('information, 'peer) action  \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> bool" where 
stepcS: "\<lbrakk>a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>; (fst (C1 p), a, p2) \<in> \<R> p;  C2 = ((C1)(p := (p2, (snd (C1 p)))))(q := ((fst (C1 q)), (snd (C1 q)) \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)]))\<rbrakk> \<Longrightarrow> stepc C1 a C2" |
stepcR: "\<lbrakk>a = ?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>; (fst (C1 p), a, p2) \<in> \<R> p; (snd (C1 p)) \<noteq> \<epsilon>; hd (snd (C1 p)) = (i\<^bsup>q\<rightarrow>p\<^esup>); C2 = C1(p:= (p2, tl (snd (C1 p))))\<rbrakk> \<Longrightarrow> stepc C1 a C2"


fun send_config :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> 'peer \<Rightarrow> 'peer \<Rightarrow> ('information, 'peer) message \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word))" where
"send_config C1 p q m = C1"

fun recv_config :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> 'peer \<Rightarrow> ('information, 'peer) message \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word))" where
"recv_config C1 p m = C1"

fun local_config_step :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow>  ('information, 'peer) action \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word))" where
"local_config_step C1 (!\<langle>m\<rangle>) = send_config C1 (get_sender m) (get_receiver m) m"  |
"local_config_step C1 (?\<langle>m\<rangle>) = recv_config C1 (get_receiver m)  m"

(*\<midarrow>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>p*)

lemma stepc_send_rev :
  assumes "stepc C1 a C2" and "a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>"
  shows "\<exists>p2. (fst (C1 p), a, p2) \<in> \<R> p \<and> C2 = ((C1)(p := (p2, (snd (C1 p)))))(q := ((fst (C1 q)), (snd (C1 q)) \<cdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)]))"
  using assms(1,2) stepc.simps by auto

lemma stepc_recv_rev :
  assumes "stepc C1 a C2" and "a =  ?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>"
  shows "\<exists>p2. (fst (C1 p), a, p2) \<in> \<R> p \<and> hd (snd (C1 p)) = (i\<^bsup>q\<rightarrow>p\<^esup>) \<and> C2 = C1(p:= (p2, tl (snd (C1 p))))"
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
  then have t1: "fst (C1 p) \<midarrow>(?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>p (fst (C2 p))" by simp
  have "\<forall>xs. xs \<noteq> \<epsilon> \<longrightarrow> xs = (hd xs) # tl xs" by simp
  have "C2 = C1(p:= (p2, tl (snd (C1 p))))"   by (simp add: local.stepcR(5))
  then have "hd (snd (C1 p)) =  (i\<^bsup>q\<rightarrow>p\<^esup>)"  by (simp add: local.stepcR(4))
  have "snd (C1 p) \<noteq> \<epsilon>" by (simp add: local.stepcR(3))
  then have "snd (C1 p) = (i\<^bsup>q\<rightarrow>p\<^esup>) # tl (snd (C1 p))"  using \<open>\<forall>xs. xs \<noteq> \<epsilon> \<longrightarrow> xs = hd xs # tl xs\<close> local.stepcR(4) by fastforce
  then have t2: "(snd (C1 p)) = [(i\<^bsup>q\<rightarrow>p\<^esup>)] \<cdot> snd (C2 p)"  by (simp add: local.stepcR(5))
  then have t3: "\<forall>x. x \<noteq> p \<longrightarrow> C1(x) = C2(x)" by (simp add: local.stepcR(5))
  then have "( | (snd (C1 p)) | ) <\<^sub>\<B> None" by simp
  then show ?thesis using MboxRecv assms(2) local.stepcR(1) t1 t2 t3 by blast
qed

lemma stepc_produces_mbox_config :
  assumes "stepc C1 a C2" and "is_mbox_config C1"
  shows "is_mbox_config C2"
  using assms(1,2) mbox_step_rev(2) stepc_to_mbox by blast

lemma mbox_run_prod_mbox_config: 
  assumes "mbox_run C0 None w cs" and "cs \<noteq> []"
  shows "is_mbox_config (last cs)"
  using assms(1,2) run_produces_mailbox_configurations by auto



inductive runc :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> ('information, 'peer) action word  \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) list \<Rightarrow> bool" where
runc_empty: "runc (\<C>\<^sub>\<I>\<^sub>\<mm>) (\<epsilon>) ([])" |
runc_once: "\<lbrakk>stepc (\<C>\<^sub>\<I>\<^sub>\<mm>) a C2\<rbrakk> \<Longrightarrow> runc (\<C>\<^sub>\<I>\<^sub>\<mm>) ([a]) ([C2])" |
runc_rec: "\<lbrakk>runc C0 w cs; cs \<noteq> []; (stepc (last cs) a C2)\<rbrakk> \<Longrightarrow> runc C0 (w@[a]) (cs@[C2])"

lemma runc_rev :
  assumes "runc C0 w cs"
  shows "(C0 = (\<C>\<^sub>\<I>\<^sub>\<mm>) \<and> w = \<epsilon> \<and> cs = []) \<or> (\<exists>a C2. C0 = (\<C>\<^sub>\<I>\<^sub>\<mm>) \<and> w = [a] \<and> cs = [C2]) \<or>
(\<exists>ccs v a C2. runc C0 v ccs \<and> ccs \<noteq> [] \<and> (stepc (last ccs) a C2 \<and> cs = ccs @ [C2]))"
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

(*
"\<lbrakk>is_mbox_config C1; a = ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>; fst (C1 q) \<midarrow>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>q (fst (C2 q));
            (snd (C1 q)) = [(i\<^bsup>p\<rightarrow>q\<^esup>)] \<cdot> snd (C2 q); \<forall>x. x \<noteq> q \<longrightarrow> C1(x) = C2(x)\<rbrakk> \<Longrightarrow>
            mbox_step C1 a k C2"



MRComposedNat: "\<lbrakk>mbox_run C0 (Some k) w xc; last (C0#xc) \<midarrow>\<langle>a, k\<rangle>\<rightarrow> C\<rbrakk> \<Longrightarrow>
                mbox_run C0 (Some k) (w\<cdot>[a]) (xc@[C])" |
MRComposedInf: "\<lbrakk>mbox_run C0 None w xc; last (C0#xc) \<midarrow>\<langle>a, \<infinity>\<rangle>\<rightarrow> C\<rbrakk> \<Longrightarrow>
                mbox_run C0 None (w\<cdot>[a]) (xc@[C])"
*)
(*run2 : "runc C0 [(\<I> p, a, s2), (s2, b, s3)] []"

let ?c1 = "(\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>))"
  let ?c3 = "(\<lambda>x. (C x, \<epsilon>))" 
  let ?c2 = "(?c3)(q := ((\<C>\<^sub>\<I>\<^sub>\<zero>) q, [(i\<^bsup>p\<rightarrow>q\<^esup>)]))"
*)




(*
fixes C1 C2 :: "'peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)"
    and i     :: "'information"
    and p q   :: "'peer"
    and k     :: "bound"
lemma root_word_to_mbox_run: 
  assumes "w \<in> \<L>(p)" and "tree_topology" and "{}\<langle>\<rightarrow>p\<rangle> = {}"
  shows "\<exists>xc. mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None w xc"
  sledgehammer


lemma sends_have_mbox_run :
  assumes "w \<in> \<L>\<^sup>*(p)" and "{}\<langle>\<rightarrow>p\<rangle> = {}" and "tree_topology"
  shows "w \<in> \<T>\<^bsub>None\<^esub>"
  sorry
*)

lemma root_graph: 
  assumes "\<P> = {p}" and "tree_topology"
  shows "\<G>\<langle>\<rightarrow>p\<rangle> = {}"
  by (metis (full_types, lifting) UNIV_I assms(1,2) empty_Collect_eq singleton_iff tree_acyclic)

lemma p_root: 
  assumes "path_to_root p [p]" and "tree_topology"
  shows "\<G>\<langle>\<rightarrow>p\<rangle> = {}"
proof auto
  fix q
  assume "(q, p) \<in> \<G>"
  then show "False" 
    by (smt (verit, ccfv_threshold) CommunicatingAutomaton.SendingToPeers.intros
        CommunicatingAutomaton.well_formed_transition Edges_rev NetworkOfCA.no_input_trans_root NetworkOfCA_axioms
        assms(1) automaton_of_peer get_receiver.simps global_to_local_root input_message_to_act messages_used
        output_message_to_act_both_known prod.inject single_path_impl_root)
qed

lemma root_lang_word_facts: 
  assumes "\<P>\<^sub>?(q) = {}" and "(\<forall>p. q \<notin> \<P>\<^sub>!(p))" and "w \<in> \<L>\<^sup>*(q)" and "tree_topology"
  shows "w = w\<down>\<^sub>q \<and> w = w\<down>\<^sub>! \<and> w \<in> \<L>(q)"
  using assms(1,3) no_inputs_implies_only_sends_alt w_in_infl_lang w_in_peer_lang_impl_p_actor by auto

(*
lemma root_lang_in_mbox_traces: 
  assumes "\<P>\<^sub>?(q) = {}" and "(\<forall>p. q \<notin> \<P>\<^sub>!(p))" and "tree_topology"
  shows "\<L>(q) \<subseteq> \<T>\<^bsub>None\<^esub>"
proof auto
  fix w
  assume "w \<in> \<L>(q)"
  then show "w \<in> \<T>\<^bsub>None\<^esub>"
  proof (induct "length w" arbitrary: w)
    case 0
    then show ?case using MboxTraces.simps initial_configuration_is_mailbox_configuration runc_empty
        runc_to_mbox_run by fastforce
  next
    case (Suc x)
    then obtain v a where w_def: "w = v @ [a]" and v_len: "length v = x" by (metis length_Suc_conv_rev)
    then have "v \<in> \<L>(q)" using Lang_app Suc.prems by blast
    then have "v \<in> \<T>\<^bsub>None\<^esub>" by (simp add: Suc.hyps(1) v_len)
    have "w = w\<down>\<^sub>!" using Suc.prems assms(1) no_inputs_implies_only_sends by auto
    then have "is_output a" by (metis append1_eq_conv append_is_Nil_conv decompose_send is_output.simps(1) list.distinct(1)
          w_def)
    have "w = w\<down>\<^sub>q" by (simp add: w_in_peer_lang_impl_p_actor \<open>w \<in> \<L>(q)\<close>)
    then have "get_actor a = q" by (metis (mono_tags, lifting) \<open>v \<in> \<L> q\<close> append_self_conv filter.simps(2) filter_append
          filter_head_helper w_def w_in_peer_lang_impl_p_actor)
    then obtain i p where a_def: "a = !\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>"  by (metis \<open>is_output a\<close> get_actor.simps(1) get_sender.simps is_output.simps(2)
          local_config_step.elims message.exhaust)
    then show ?case using Suc assms
    proof (cases "v = \<epsilon>")
      case True
      then show ?thesis  by (metis MboxTraces.intros Suc.prems \<open>is_output a\<close> mbox_step_to_run self_append_conv2
            send_step_to_mbox_step w_def)
    next
      case False
      then obtain xs where w_run: "run_of_peer q w xs" using Suc.prems lang_implies_run by auto
      then obtain ys y where v_run: "run_of_peer q v ys" and a_run: "(last ([(\<I> q)]@ys))  \<midarrow>a\<rightarrow>q y" sledgehammer
      then have "\<exists>s1 s2. (\<I> q) \<midarrow>v\<rightarrow>\<^sup>*q s1 \<and> s1 \<midarrow>a\<rightarrow>q s2" sledgehammer
      then obtain xc C  where vrun: "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None v (xc)" and Cl :"last xc = C" by (metis MboxTraces.cases \<open>v \<in> \<T>\<^bsub>None\<^esub>\<close>)
      then have "(fst (C q)) \<in> \<S> q" using False is_mbox_config_def mbox_run.cases mbox_run_prod_mbox_config by fastforce
        then obtain s2 where  C_prop: "(fst (C q), a, s2) \<in> (\<R> q)"
  sledgehammer

      then obtain xc C where vrun: "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None v (xc@[C])" by (smt (verit) MboxTraces.cases \<open>v \<in> \<T>\<^bsub>None\<^esub>\<close> mbox_run.cases)
      then obtain s1 s2 where a_trans: "(s1, a, s2) \<in> \<R> q" and "fst (C q) = s1" sledgehammer 
      then obtain C2 where a_step: "mbox_step C a None C2" sledgehammer
      then show ?thesis sledgehammer
    qed
  qed
    
qed
*)

(* not correct!
lemma mbox_2_peer_run:
  assumes "w \<in> \<T>\<^bsub>None\<^esub>"
  shows "\<exists>p. w \<in> \<L>\<^sup>*(p)"
  sorry


lemma infl_word_2_mbox:
  assumes "w \<in> \<L>\<^sup>*(p)"
  shows "w \<in> \<T>\<^bsub>None\<^esub>"
  sorry
*)

fun mbox_run_to_run :: "'peer \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) list \<Rightarrow> 'state list" where
"mbox_run_to_run p C0 [] = []" |
"mbox_run_to_run p C0 (C1 # Cs) = (fst (C1 p)) # mbox_run_to_run p C0 (Cs)"

(*
lemma mbox_run_impl_run_for_each_peer: 
  assumes "mbox_run C None w xc" and "p \<in> \<P>"
  shows "run_of_peer_from_state p (fst (C p)) w (mbox_run_to_run p C xc)"
  using assms
proof (induct rule: mbox_run.induct)
  case (MREmpty C k)
  then have "(mbox_run_to_run p C \<epsilon>) = []" by simp
  then have "run_of_peer_from_state p (fst (C p)) \<epsilon> \<epsilon>" sledgehammer
  then show ?case sledgehammer
next
  case (MRComposedNat C0 k w xc a C)
  then show ?case sorry
next
  case (MRComposedInf C0 w xc a C)
  then show ?case sorry
qed
*)

lemma root_lang_is_mbox:
  assumes "is_root p" and "w \<in> \<L>(p)"
  shows "w \<in> \<T>\<^bsub>None\<^esub>"
  sorry


lemma parent_in_infl_has_matching_sends: 
  assumes "w \<in> \<L>\<^sup>*(p)" and "path_to_root p (p#q#ps)" and "\<P>\<^sub>?(p) = {q}"
  shows "\<exists>w'. w' \<in> \<L>\<^sup>*(q) \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"
  by (metis assms(1,3) is_in_infl_lang.cases is_in_infl_lang_rev(2) mem_Collect_eq)
(*
(*go from node pn and its word wn towards the root *)
inductive infl_path_2_mbox_w :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" for w\<^sub>n :: "('information, 'peer) action word" where
i2mROOT: "\<lbrakk>path_to_root p [p];  w\<^sub>1 \<in> \<L>\<^sup>*(p)\<rbrakk> \<Longrightarrow> infl_path_2_mbox_w w\<^sub>n w\<^sub>1 (w\<^sub>a\<^sub>c\<^sub>c)" |
i2mNODE: "\<lbrakk>infl_path_2_mbox_w w\<^sub>n w\<^sub>i w\<^sub>a\<^sub>c\<^sub>c; path_to_root p (p # q # ps); \<P>\<^sub>?(p) = {q}; w\<^sub>1 \<in> \<L>\<^sup>*(p); w' \<in> \<L>\<^sup>*(q); ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> infl_path_2_mbox_w w (w' \<cdot> w)" 
*)

(* the base step for the root is probably not sufficient *)
inductive infl_2_mbox :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
i2mROOT: "\<lbrakk>is_root p; w \<in> \<L>\<^sup>*(p); (w_acc\<down>\<^sub>p) = w\<rbrakk> \<Longrightarrow> infl_2_mbox w w_acc" |
i2mNODE: "\<lbrakk>\<P>\<^sub>?(p) = {q}; w \<in> \<L>\<^sup>*(p); w' \<in> \<L>\<^sup>*(q); ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?); infl_2_mbox w (w' \<cdot> ws)\<rbrakk> \<Longrightarrow> infl_2_mbox w (w \<cdot> w' \<cdot> ws)" 


(* go from node towards root
at each step, the construction projected on only the current node and its parent must have matching sends/recvs

w in influenced language already implies this property

*)

lemma adj_in_path_parent_child:
  assumes "path_to_root p (x # y # ps)"
  shows "\<P>\<^sub>?(x) = {y} \<or> x \<in> \<P>\<^sub>!(y)"
  by (metis assms is_parent_of_rev2(2) neq_Nil_conv path_to_root_first_elem_is_peer
      path_to_root_stepback)

(*starts at some node and a full path from that node to root, then walks up to the root while accumulating the word w1....wn*)
inductive concat_infl :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'peer list  \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" for p::"'peer" and w:: "('information, 'peer) action word" where
at_p: "\<lbrakk>tree_topology; w \<in> \<L>\<^sup>*(p); path_to_root p ps\<rbrakk> \<Longrightarrow> concat_infl p w ps w" | (*start condition*)
reach_root: "\<lbrakk>is_root q; qw \<in> \<L>\<^sup>*(q); path_to_root x (x # [q]); (\<forall>g. w_acc\<down>\<^sub>g \<in> \<L>\<^sup>*(g));  concat_infl p w (x # [q]) w_acc; (((w_acc\<down>\<^sub>x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((qw\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> concat_infl p w [q] (qw \<cdot> w_acc)" | (*end condition*)
node_step: "\<lbrakk>tree_topology; \<P>\<^sub>?(x) = {q}; (\<forall>g. w_acc\<down>\<^sub>g \<in> \<L>\<^sup>*(g)); path_to_root x (x # q # ps); qw \<in> \<L>\<^sup>*(q); concat_infl p w (x # q # ps) w_acc; (((w_acc\<down>\<^sub>x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((qw\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> concat_infl p w (q#ps) (qw \<cdot> w_acc)" 

lemma concat_infl_path_rev :
  assumes "concat_infl p w (q#ps) w'"
  shows "path_to_root q (q#ps)"
  using assms
proof(induct "(q#ps)" w' arbitrary: q ps rule: concat_infl.induct)
  case at_p
  then show ?case using path_to_root_first_elem_is_peer by blast
next
  case (reach_root q qw x w_acc)
  then show ?case  using path_to_root_first_elem_is_peer path_to_root_stepback by blast
next
  case (node_step x q ps qw w_acc)
  then show ?case  by (metis list.discI path_to_root_first_elem_is_peer path_to_root_stepback)
qed

lemma concat_infl_tree_rev :
  assumes "concat_infl p w ps w'"
  shows "tree_topology"
  using assms concat_infl.cases by blast

lemma concat_infl_p_first_or_not_exists:
  assumes "concat_infl p w ps w'"
  shows "(\<exists>qs. ps = p#qs) \<or> (\<forall>xs ys. ps \<noteq> xs @ [p] @ ys)"
  using assms 
  sorry

lemma concat_infl_actor_consistent:
  assumes "concat_infl p w ps w_acc"
  shows "w_acc\<down>\<^sub>p = w"
  using assms
proof (induct ps w_acc rule: concat_infl.induct)
  case (at_p ps)
  then show ?case  using w_in_infl_lang w_in_peer_lang_impl_p_actor by force
next
  case (reach_root q qw x w_acc')
  then have "qw \<in> \<L> q"  by (simp add: w_in_infl_lang)
  then have "qw\<down>\<^sub>q = qw"  using w_in_peer_lang_impl_p_actor by fastforce
  then show ?case
  proof (cases "q = p") \<comment> \<open>can't be the case because then concat_infl __ is not true\<close>
    case True
    then have "qw\<down>\<^sub>p = qw"  using \<open>qw\<down>\<^sub>q = qw\<close> by blast
    then have "qw \<in> \<L> p"  using True \<open>qw \<in> \<L> q\<close> by blast
    then have "is_root p"  using True reach_root.hyps(1) by auto
    then have "\<not> path_to_root p (x # q # \<epsilon>)" by (metis True list.distinct(1) list.inject path_to_root_first_elem_is_peer path_to_root_stepback
          path_to_root_unique)
    have "concat_infl p w (x # q # \<epsilon>) w_acc'" by (simp add: reach_root.hyps(5))
    then have "path_to_root x (x # q # \<epsilon>)" by (simp add: reach_root.hyps(3))
    then have "x \<noteq> q"  using True \<open>\<not> path_to_root p (x # q # \<epsilon>)\<close> by auto
    have "(\<forall>xs ys. (x # q # \<epsilon>) \<noteq> xs @ [p] @ ys)"  using True \<open>x \<noteq> q\<close> concat_infl_p_first_or_not_exists reach_root.hyps(5) by blast
    have "(x # q # \<epsilon>) = [x] @ [p] @ []"   using True by auto
    then show ?thesis  using \<open>\<forall>xs ys. x # q # \<epsilon> \<noteq> xs \<cdot> (p # \<epsilon> \<cdot> ys)\<close> by blast
  next
    case False
    then have "qw\<down>\<^sub>p = \<epsilon>"  by (metis \<open>qw\<down>\<^sub>q = qw\<close> only_one_actor_proj)
    then show ?thesis  by (simp add: reach_root.hyps(6))
  qed
next
  case (node_step x q w_acc' ps qw)
  then have "qw \<in> \<L> q"   by (meson mem_Collect_eq w_in_infl_lang)
  then have "qw\<down>\<^sub>q = qw"  using w_in_peer_lang_impl_p_actor by fastforce
  then show ?case
  proof (cases "q = p") \<comment> \<open>can't be the case because then concat_infl __ is not true\<close>
    case True
    then have "qw\<down>\<^sub>p = qw"  using \<open>qw\<down>\<^sub>q = qw\<close> by blast
    then have "qw \<in> \<L> p"  using True \<open>qw \<in> \<L> q\<close> by blast
    have "concat_infl p w (x # q # ps) w_acc'"  by (simp add: node_step.hyps(6))
    then have "path_to_root x (x # q # ps)" by (simp add: node_step.hyps(4))
    then have "x \<noteq> q"  by (metis insert_subset mem_Collect_eq node_step.hyps(1,2) sends_of_peer_subset_of_predecessors_in_topology
          tree_acyclic)
    have "(\<forall>xs ys. (x # q # ps) \<noteq> xs @ [p] @ ys)"   using True \<open>x \<noteq> q\<close> concat_infl_p_first_or_not_exists node_step.hyps(6) by blast
    have "(x # q # ps) = [x] @ [p] @ ps"    using True by auto
    then show ?thesis using \<open>\<forall>xs ys. x # q # ps \<noteq> xs \<cdot> (p # \<epsilon> \<cdot> ys)\<close> by blast
  next
    case False
    then have "qw\<down>\<^sub>p = \<epsilon>"  by (metis \<open>qw\<down>\<^sub>q = qw\<close> only_one_actor_proj)
    then show ?thesis  by (simp add: node_step.hyps(7))
  qed
qed

lemma concat_infl_word_exists:
  assumes "concat_infl p w ps w" and "is_root r"
  shows "\<exists>w'. concat_infl p w [r] w'"
  sorry

lemma concat_infl_mbox:
  assumes "concat_infl p w [q] w_acc"
  shows "w_acc \<in> \<T>\<^bsub>None\<^esub>"
  using assms 
proof(induct "[q]" w_acc arbitrary: q p w rule: concat_infl.induct)
  case at_p
  then show ?case by (metis NetworkOfCA.path_to_root_first_elem_is_peer NetworkOfCA_axioms dual_order.eq_iff
        infl_lang_subset_of_lang lang_subset_infl_lang p_root root_lang_is_mbox)
next
  case (reach_root q qw x w_acc)
  then have "is_root q" by blast
  then have "qw \<in> \<T>\<^bsub>None\<^esub>" using reach_root.hyps(2) root_lang_is_mbox w_in_infl_lang by auto
  (* obtain end config C1 after qw, show that we can go from C1 to C2 by reading w *)
  then show ?case sorry
next
  case (node_step x q qw w_acc)
  then show ?case sorry
qed

lemma concat_infl_children_not_included:
  assumes "concat_infl p w ps w_acc"
  shows "(\<forall>p. (p \<in> \<P> \<and> \<P>\<^sub>?(p) = {q}) \<longrightarrow>  w_acc\<down>\<^sub>p = \<epsilon>)"
  (*to show, simply that p is child of q, so p is not on the path_to_root of p*)
  sorry

(*
lemma concat_infl_rev:
  assumes "concat_infl p w ps w_acc"
  shows "\<exists>w1 ws q qs. w_acc = w1 @ ws \<and> w1 \<in> \<L>\<^sup>*(q) \<and> ps = q # qs \<and> (((w_acc2\<down>\<^sub>x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w1\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"
*)

(*
inductive yes :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'peer list  \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" for p::"'peer" and w:: "('information, 'peer) action word" where
at_p: "\<lbrakk>tree_topology; w \<in> \<L>\<^sup>*(p); path_to_root p ps\<rbrakk> \<Longrightarrow> yes p w ps w" | (*start condition*)
reach_root: "\<lbrakk>is_root x; rw \<in> \<L>\<^sup>*(x); yes p w (q # [x]) w_acc; (((w_acc\<down>\<^sub>{\<^sub>x\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((rw\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> yes p w [x] (rw \<cdot> w_acc)" | (*end condition*)
node_step: "\<lbrakk>tree_topology; \<P>\<^sub>?(x) = {q}; qw \<in> \<L>\<^sup>*(q); yes p w (x # [q] @ ps) w_acc; (((w_acc\<down>\<^sub>{\<^sub>x\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((qw\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> yes p w (q#ps) (qw \<cdot> w_acc)" 

inductive yes :: "'peer list \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
root_word: "\<lbrakk>is_root p; w \<in> \<L>\<^sup>*(p)\<rbrakk> \<Longrightarrow> yes [p] w w" |
root_reached: "\<lbrakk>is_root p; w \<in> \<L>\<^sup>*(p); yes (q # [p]) w w_acc; (((w_acc\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> yes [p] w (w \<cdot> w_acc)" |
node_step: "\<lbrakk>tree_topology; \<P>\<^sub>?(p) = {q}; yes (p # [q] @ ps) w w_acc; (((w_acc\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> yes (q#ps) w w_acc" |


enn: "\<lbrakk>is_root p; w \<in> \<L>\<^sup>*(p); (((w_acc\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?); yes (q # [p]) w w_acc\<rbrakk> \<Longrightarrow> yes [p] w (w \<cdot> w_acc)" |
ynode: "\<lbrakk>tree_topology; \<P>\<^sub>?(p) = {q}; (((w_acc\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?); yes (p # [q] @ ps) w w_acc\<rbrakk> \<Longrightarrow> yes (q#ps) w w_acc" | 
ennn:"\<lbrakk>tree_topology; \<P>\<^sub>?(p) = {q}; path_to_root p (p#q#ps); w \<in> \<L>\<^sup>*(p); w' \<in> \<L>\<^sup>*(q); ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> 
        \<Longrightarrow> yes q w ()"
*)


(* construct w' where w' is the concatenation w1...wn where wi is in influenced language of peer i 
(numbered by closeness to root, root is 1) 
\<rightarrow> this construction is in mbox 
lemma infl_word_2_mbox :
  assumes "w \<in> \<L>\<^sup>*(q)" 
  shows "\<exists>w'. (w' @ w) \<in> \<T>\<^bsub>None\<^esub>"
  sorry
*)


(*Let N be a network such that CF = C, G(N) is a tree, q \<in> P, and w \<in> L ≬(Aq). Then there
is an execution w\<Zprime> \<in> E(Nmbox) such that w\<Zprime>\<down>q = w and w\<Zprime>\<down>p = \<epsilon> for all p \<in> P with Pp
send = {q}.*)
lemma lemma4_4 : 
  fixes w :: "('information, 'peer) action word"
    and q :: "'peer"
  assumes "tree_topology" and "w \<in> \<L>\<^sup>*(q)" and "q \<in> \<P>"
  shows "\<exists> w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>q = w \<and> (\<forall>p. (p \<in> \<P> \<and> \<P>\<^sub>?(p) = {q}) \<longrightarrow>  w'\<down>\<^sub>p = \<epsilon>))"
  using assms
proof (cases "is_root q") 
  case True \<comment> \<open>q = r\<close>
  then have "w \<in> \<L>(q)" using assms(2) is_in_infl_lang.cases by blast
  then have "w = w\<down>\<^sub>!"  by (meson NetworkOfCA.no_inputs_implies_only_sends_alt NetworkOfCA_axioms True assms(1) global_to_local_root
        p_root)
  then have "w\<down>\<^sub>? = \<epsilon>"  by (simp add: output_proj_input_yields_eps)
  then have t2: "w = w\<down>\<^sub>q" by (simp add: \<open>w \<in> \<L> q\<close> w_in_peer_lang_impl_p_actor)
  then have "\<forall> p. p \<noteq> q \<longrightarrow> w\<down>\<^sub>p = \<epsilon>"  by (metis NetworkOfCA.only_one_actor_proj NetworkOfCA_axioms)
  then have t3: "(\<forall>p. (p \<in> \<P> \<and> \<P>\<^sub>?(p) = {q}) \<longrightarrow>  w\<down>\<^sub>p = \<epsilon>)" by (metis True assms(1) global_to_local_root insert_not_empty ) 
\<comment> \<open>need to prove lemma that if w is w of root r, then mbox (unbounded) has a run for it 
basically construct the configs, where it starts with (\<I>(r), \<epsilon>) and each step appends a send to the buffer of the respective receiver\<close>
  then have "w \<in> \<L>(q)" by (simp add: \<open>w \<in> \<L> q\<close>)
  then have "is_root q" using True by auto
  then have "w \<in> \<T>\<^bsub>None\<^esub>" using \<open>w \<in> \<L> q\<close> root_lang_is_mbox by auto
  then show ?thesis  by (metis t2 t3)
next
  case False (*path to root of length n>1, i.e. q is NOT root*)
  then obtain p where q_parent: "is_parent_of q p" by (metis UNIV_I assms(1) path_to_root.cases path_to_root_exists)
  then obtain ps where p2root: "path_to_root p (p # ps)" by (metis UNIV_I assms(1) path_to_root_exists path_to_root_rev)
  then have "is_node q"  by (metis is_parent_of.cases q_parent)
  have "w \<in> \<L>\<^sup>*(q)"  using assms(2) by auto
  then have "\<P>\<^sub>?(q) = {p}"  by (simp add: infl_parent_child_unique q_parent)
  (*by w in infl lang, we can find some w' with matching sends*)
  then have "\<exists>w'. w'\<in> \<L>\<^sup>* p \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"  using assms(2) infl_parent_child_matching_ws by blast
  then obtain w' where w'_w: "((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" and w'_Lp: "w' \<in> \<L>\<^sup>* p" by blast
  then have "w' \<in> \<L> p" by (meson mem_Collect_eq w_in_infl_lang)
  have "tree_topology"  using assms(1) by auto
  have  "((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?) \<and> w \<in> \<L>(q) \<and> w' \<in> \<L>(p) \<and> is_node q" using \<open>\<P>\<^sub>? q = {p}\<close>
      \<open>is_tree (\<P>) (\<G>) \<and> (\<exists>qa. \<G>\<langle>\<rightarrow>q\<rangle> = {qa}) \<or> is_tree (\<P>) (\<G>) \<and> (\<exists>qa. \<P>\<^sub>? q = {qa} \<or> q \<in> \<P>\<^sub>! qa)\<close> \<open>w' \<in> \<L> p\<close>
      assms(2) is_in_infl_lang_rev2(1) w'_w by blast
  (*repeat this argument for all peers on the path to the root*)
  obtain r where "is_root r" using assms(1) root_exists by blast
  have "path_to_root q (q # p # ps)" using PTRNode assms(1) p2root q_parent by auto
  then have "concat_infl q w (q # p # ps) w"  using assms(1,2) at_p by auto
  have "w \<in> \<L>(q)"  by (simp add:
        \<open>w\<down>\<^sub>?\<down>\<^sub>!\<^sub>? = w'\<down>\<^sub>!\<down>\<^sub>!\<^sub>? \<and> w \<in> \<L> q \<and> w' \<in> \<L> p \<and> (is_tree (\<P>) (\<G>) \<and> (\<exists>qa. \<G>\<langle>\<rightarrow>q\<rangle> = {qa}) \<or> is_tree (\<P>) (\<G>) \<and> (\<exists>qa. \<P>\<^sub>? q = {qa} \<or> q \<in> \<P>\<^sub>! qa))\<close>)
  then have "w\<down>\<^sub>q = w"  using w_in_peer_lang_impl_p_actor by auto
  (* prepend first word to wn \<rightarrow>   w(n-1) \<cdot> w(n) *)
  (*then have "concat_infl q w (p # ps) (w' \<cdot> w)" *)
  (*obtain w1 \<cdot> w2 \<cdots> wn*)
  obtain w_acc where "concat_infl q w [r] w_acc" by (meson \<open>concat_infl q w (q # p # ps) w\<close>
        \<open>is_tree (\<P>) (\<G>) \<and> \<P>\<^sub>? r = {} \<and> (\<forall>q. r \<notin> \<P>\<^sub>! q) \<or> is_tree (\<P>) (\<G>) \<and> \<G>\<langle>\<rightarrow>r\<rangle> = {}\<close>
        concat_infl_word_exists)
  then have "w_acc \<in> \<T>\<^bsub>None\<^esub>" by (simp add: concat_infl_mbox)
  have "w_acc\<down>\<^sub>q = w"  using \<open>concat_infl q w (r # \<epsilon>) w_acc\<close> concat_infl_actor_consistent by blast
  then have "(\<forall>p. (p \<in> \<P> \<and> \<P>\<^sub>?(p) = {q}) \<longrightarrow>  w_acc\<down>\<^sub>p = \<epsilon>)"   using \<open>concat_infl q w (r # \<epsilon>) w_acc\<close> concat_infl_children_not_included by blast
then show ?thesis using \<open>w_acc \<in> \<T>\<^bsub>None\<^esub>\<close> \<open>w_acc\<down>\<^sub>q = w\<close> by blast
qed
(*construct w from infl lang, for a given path from p to root r.
wn in infl lang of p, wn-1 (the matching sends) from parent of p, wn-2 with 
the matching sends of grandparent of p, ... until we reach w1 where infl lang = lang0
\<rightarrow> then w1 w2 .... wn (all concatenated in this order of the pth) is in mbox
*)
 
(*p is q(n-1)
  then have "path_to_root q (q#p#ps)"  by (meson path_to_root.simps q_parent)*)
(*because w is in infl. lang. of q, p must have a word with matching sends
  then have "\<exists>w'.  w' \<in> \<L>\<^sup>*(p) \<and> ((w'\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" *)

(*construct w' s.t. w1....wn is a mbox trace*)





\<comment> \<open>TNsync = L0, ENsync = T0, EMbox = Tinf/None, TMbox = Linf, E = !?, T = only sends\<close>
theorem synchronisability_for_trees:
  assumes "tree_topology" 
  shows "is_synchronisable \<longleftrightarrow> (\<forall>p q. ((\<P>\<^sub>?(p) = {q}) \<longrightarrow> (((((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>?) \<subseteq> ((\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?)) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) ))" (is "?L \<longleftrightarrow> ?R")
proof
  (* Direction 1: is_synchronisable => language conditions *)
  assume "?L"
  show "?R"
  proof clarify
    fix p q
    assume p_parent: "\<P>\<^sub>?(p) = {q}"
    
    have sync_def: "\<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>! = \<L>\<^sub>\<zero>"
      using \<open>?L\<close> by simp
    
    show "(((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>?) \<subseteq> ((\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?) \<and> (\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p))"
    proof (rule conjI)
      (* Part 1: Prove the subset relation for traces *)
      show "((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?"
      proof (rule ccontr)
        assume subset_not_holds: "\<not>(((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?)"
        (* Extract a counterexample trace *)
        then obtain v where v_def: "v \<in> ((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})" and
                     not_in_p: "v\<down>\<^sub>!\<^sub>? \<notin> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?" by blast
         
        (* Use Lemma 4.4 to find an execution v' in mailbox system *)
        obtain v' where v'_def: "v' \<in> \<T>\<^bsub>\<infinity>\<^esub>" and
                       v'_proj_q: "(v'\<down>\<^sub>!)\<down>\<^sub>q = v" and
                       v'_proj_p: "v'\<down>\<^sub>p = \<epsilon>"
          using lemma4_4 sorry
          
        (* Use synchronisability to show trace is also in synchronous system *)
        have "v'\<down>\<^sub>! \<in> \<L>\<^bsub>\<infinity>\<^esub>" using v'_def by blast
        also have "\<L>\<^bsub>\<infinity>\<^esub> = \<T>\<^sub>\<zero>" using sync_def by simp
        also have "\<T>\<^sub>\<zero> = \<L>\<^sub>\<zero>" by simp
        have v'_sync: "v'\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>" using calculation by auto
        
        (* Since v'\<down>\<^sub>p = \<epsilon>, p must be able to receive outputs without sending *)
        have "v\<down>\<^sub>!\<^sub>? \<in> ((\<L>(p))\<downharpoonright>\<^sub>?)\<downharpoonright>\<^sub>!\<^sub>?" using v'_sync v'_proj_p sorry
        have "v\<down>\<^sub>!\<^sub>? \<in> (\<L>\<^sub>?\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?" sorry
        
        (* Contradiction with our assumption *)
        show "False" using not_in_p sorry
      qed
      
      (* Part 2: Prove influenced language and shuffled language equivalence *)
      show "\<L>\<^sup>*(p) = \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)"
      proof
        (* First inclusion is by definition *)
        show "\<L>\<^sup>*(p) \<subseteq> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)" using language_shuffle_subset by auto
        (* Second inclusion via proof*)
        show "\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p) \<subseteq> \<L>\<^sup>*(p)"
        proof
          fix v
          assume "v \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)"
          (* Find shortest words v and v' where v' is in language but v is shuffled *)
          then have "\<exists>v'. v' \<in> \<L>\<^sup>*(p) \<and> v \<squnion>\<squnion>\<^sub>? v'" using shuffle_rev by auto \<comment> \<open>in the paper it's v' _ v\<close>
          (* Focus on specific form of these words *)
          obtain v' w a xs where  v'_def: "v' \<in> \<L>\<^sup>*(p)" and 
                                    "v \<squnion>\<squnion>\<^sub>? v'" and
                                    v_form: "v = w # ?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # xs" and
                                v'_form: "v' = w # xs @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]" and
                                 xs_form: "xs = xs\<down>\<^sub>!" \<comment> \<open>xs are outputs to p's children, maybe thats also necessary here\<close>
            sorry

          (* Apply Lemma 4.4 to find execution in mailbox system *)
          obtain w' where w'_def: "w' \<in> \<T>\<^bsub>\<infinity>\<^esub>" and
                        w'_proj: "w'\<down>\<^sub>p = w # xs @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]"
            using v'_def lemma4_4 sorry
            
          (* By construction, outputs from q to p happen before p's outputs *)
          have "\<exists>m mm mmm. w'\<down>\<^sub>! = m @ [!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ mm @ xs @ mmm"
            using w'_def  w'_proj sorry
            
          (* Use synchronisability to show trace is in synchronous system *)
          have "w'\<down>\<^sub>! \<in> \<L>\<^bsub>\<infinity>\<^esub>" using w'_def by auto
          also have "\<L>\<^bsub>\<infinity>\<^esub> = \<L>\<^sub>\<zero>" using sync_def by simp
          also have "\<L>\<^sub>\<zero> = \<T>\<^sub>\<zero>" by simp
          then have w'_sync: "w'\<down>\<^sub>! \<in> \<T>\<^sub>\<zero>" by (simp add: calculation)
          (* In synchronous system, p must receive input before sending outputs *)
          have "v \<in> \<L>\<^sup>*(p)" sorry
            
          thus "v \<in> \<L>\<^sup>*(p)" by simp
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
    proof (cases "w\<down>\<^sub>! = \<epsilon>") \<comment> \<open>this edge case isn't in the paper but i need it here\<close>
      case True
      assume "w \<in> \<T>\<^bsub>None\<^esub>"
      then have "w \<in> \<T>\<^bsub>None\<^esub>"   using MREmpty MboxTraces.intros by blast
      then have "w\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>" using SREmpty SyncTraces.intros \<open>w\<down>\<^sub>! = \<epsilon>\<close> by auto
      then have "w \<in> \<T>\<^bsub>None\<^esub> \<Longrightarrow> w\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>"  by simp 
      then show ?thesis by (simp add: \<open>w\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>\<close>)
    next
      case False
      assume "w \<in> \<T>\<^bsub>None\<^esub>" "w\<down>\<^sub>! \<noteq> \<epsilon>"
      then have "w\<down>\<^sub>! \<in> \<L>\<^sub>\<infinity>" by blast
      then obtain v a q p where "(w\<down>\<^sub>!) = v \<cdot> [!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]" using \<open>w\<down>\<^sub>! \<noteq> \<epsilon>\<close> decompose_send by blast
      then show ?thesis using False
      proof (induct "length (w\<down>\<^sub>!)" arbitrary: w) \<comment> \<open>the paper uses base case 1 but idk how to do this here, case 0 is trivial though\<close>
        case 0
        then show ?case by simp
      next
        case (Suc n)
        then have "length v = n" by simp
        then obtain w' where w'_def: "w' = add_matching_recvs (w\<down>\<^sub>!)" by simp
        then obtain v' where "v' = add_matching_recvs v" by auto
        then have "add_matching_recvs [!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] = [!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>, ?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]" by simp
        then have "add_matching_recvs (v \<cdot> [!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]) = (add_matching_recvs v) \<cdot> add_matching_recvs [!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]" by (simp add: add_matching_recvs_app)
        then have  w'_decomp : "w' = v' \<cdot> [!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>, ?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]"  by (simp add: \<open>v' = add_matching_recvs v\<close> \<open>w\<down>\<^sub>! = v \<cdot> !\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon>\<close> w'_def)
        then obtain v' where "w' = v' \<cdot> [!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>, ?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]" by simp
        
        then have "v' \<in> \<T>\<^bsub>None\<^esub>" sorry
         
        then show ?case sorry
      qed
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





  

subsubsection \<open>Topology is a Forest\<close>

inductive is_forest :: "'peer set \<Rightarrow> 'peer topology \<Rightarrow> bool" where
IFSingle:  "is_tree P E \<Longrightarrow> is_forest P E" |
IFAddTree: "\<lbrakk>is_forest P1 E1; is_tree P2 E2; P1 \<inter> P2 = {}\<rbrakk> \<Longrightarrow> is_forest (P1 \<union> P2) (E1 \<union> E2)"

abbreviation forest_topology :: "bool" where
  "forest_topology \<equiv> is_forest (UNIV :: 'peer set) (\<G>)"

end

end