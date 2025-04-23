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


abbreviation projection_on_peer_pair
  :: "('information, 'peer) action word \<Rightarrow> 'peer \<Rightarrow> 'peer \<Rightarrow> ('information, 'peer) action word"  ("_\<down> _ _" [90, 90, 90] 110)
  where
  "w\<down> p q  \<equiv> filter (\<lambda>x. (get_object x = q \<and> get_actor x = p) \<or> (get_object x = p \<and> get_actor x = q)) w"

abbreviation projection_on_peer_pair_language
  :: "('information, 'peer) action language \<Rightarrow> 'peer \<Rightarrow> 'peer \<Rightarrow> ('information, 'peer) action language"
     ("_\<downharpoonright> _ _" [90, 90, 90] 110) where
  "(L\<downharpoonright> p q) \<equiv> {(w\<down> p q) | w. w \<in> L}"


fun o_i_exists :: " ('information, 'peer) action word \<Rightarrow> bool" where
"o_i_exists [] = False" |
"o_i_exists [a] = False" |
"o_i_exists (m1 # m2 # ms) = ((is_output m1 \<and> is_input m2) \<or> o_i_exists (m2 # ms))"

fun shuffle_once :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word" where
"shuffle_once [] = []" |
"shuffle_once [a] = [a]" |
"shuffle_once (m1 # m2 # ms) = (if (is_output m1 \<and> is_input m2) then m2 # m1 # ms else m1 # shuffle_once (m2 # ms))" 

fun shuffle_n :: "('information, 'peer) action word \<Rightarrow> nat \<Rightarrow> ('information, 'peer) action language" where
"shuffle_n w 0 = {w}" |
"shuffle_n w (Suc n) = {w} \<union> shuffle_n (shuffle_once w) n"

value "shuffle_n [?\<langle>y\<rangle>, !\<langle>x\<rangle>, ?\<langle>z\<rangle>] 3"
value "shuffle_n [!\<langle>b\<rangle>, !\<langle>c\<rangle>, ?\<langle>a\<rangle>] 3"

value "o_i_exists [?\<langle>y\<rangle>, !\<langle>x\<rangle>, ?\<langle>z\<rangle>]"
value "shuffle_once [?\<langle>y\<rangle>, !\<langle>x\<rangle>, ?\<langle>z\<rangle>]"

abbreviation valid_input_shuffles_of_w :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action language" where
"valid_input_shuffles_of_w w \<equiv> {w' | w'. w' \<in> (shuffle_n w (length w))}"



abbreviation shuffled_lang :: "('information, 'peer) action language \<Rightarrow> ('information, 'peer) action language" where
"shuffled_lang L \<equiv> { w' | w w'. w \<in> L \<and> w' \<in> (shuffle_n w (length w))}"

abbreviation valid_input_shuffle 
  :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" (infixl "\<squnion>\<squnion>" 60) where
  "w' \<squnion>\<squnion> w \<equiv> w' \<in> valid_input_shuffles_of_w w"

value "[?\<langle>y\<rangle>, !\<langle>x\<rangle>, ?\<langle>z\<rangle>] \<squnion>\<squnion> [!\<langle>x\<rangle>, ?\<langle>y\<rangle>, ?\<langle>z\<rangle>]"
value "[!\<langle>x\<rangle>, ?\<langle>y\<rangle>, ?\<langle>z\<rangle>] \<squnion>\<squnion> [?\<langle>y\<rangle>, !\<langle>x\<rangle>, ?\<langle>z\<rangle>]"


lemma "w \<in> L \<Longrightarrow> w \<in> shuffled_lang L"
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

abbreviation step
  :: "'state \<Rightarrow> ('information, 'peer) action \<Rightarrow> 'state \<Rightarrow> bool"  ("_ \<midarrow>_\<rightarrow> _" [90, 90, 90] 110)
  where
  "s1 \<midarrow>a\<rightarrow> s2 \<equiv> (s1, a, s2) \<in> Transitions"

inductive run :: "'state \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'state list \<Rightarrow> bool" where
REmpty:    "run s \<epsilon> ([])" |
RComposed: "\<lbrakk>run s0 w xs; last (s0#xs) \<midarrow>a\<rightarrow> s\<rbrakk> \<Longrightarrow> run s0 (w\<cdot>[a]) (xs@[s])"

inductive_set Traces :: "('information, 'peer) action word set" where
STRun: "run initial w xs \<Longrightarrow> w \<in> Traces"

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

abbreviation get_states :: "'peer \<Rightarrow> 'state set"  ("\<S> _" [90] 110) where
  "\<S>(p) \<equiv> fst (\<A> p)"

abbreviation get_initial_state :: "'peer \<Rightarrow> 'state"  ("\<I> _" [90] 110) where
  "\<I>(p) \<equiv> fst (snd (\<A> p))"

abbreviation get_transitions
  :: "'peer \<Rightarrow> ('state \<times> ('information, 'peer) action \<times> 'state) set"  ("\<R> _" [90] 110) where
  "\<R>(p) \<equiv> snd (snd (\<A> p))"

abbreviation WordsOverMessages :: "('information, 'peer) message word set"  ("\<M>\<^sup>*" 100) where
  "\<M>\<^sup>* \<equiv> Alphabet.WordsOverAlphabet \<M>"

abbreviation sendingToPeers_of_peer :: "'peer \<Rightarrow> 'peer set"  ("\<P>\<^sub>! _" [90] 110) where
  "\<P>\<^sub>!(p) \<equiv> CommunicatingAutomaton.SendingToPeers (snd (snd (\<A> p)))"

abbreviation receivingFromPeers_of_peer :: "'peer \<Rightarrow> 'peer set"  ("\<P>\<^sub>? _" [90] 110) where
  "\<P>\<^sub>?(p) \<equiv> CommunicatingAutomaton.ReceivingFromPeers (snd (snd (\<A> p)))"

abbreviation step_of_peer
  :: "'state \<Rightarrow> ('information, 'peer) action \<Rightarrow> 'peer \<Rightarrow> 'state \<Rightarrow> bool"
     ("_ \<midarrow>_\<rightarrow>_ _" [90, 90, 90, 90] 110) where
  "s1 \<midarrow>a\<rightarrow>p s2 \<equiv> (s1, a, s2) \<in> snd (snd (\<A> p))"

abbreviation language_of_peer
  :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L> _" [90] 110) where
  "\<L>(p) \<equiv> CommunicatingAutomaton.Lang (fst (snd (\<A> p))) (snd (snd (\<A> p)))"

abbreviation output_language_of_peer
  :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>! _" [90] 110) where
  "\<L>\<^sub>!(p) \<equiv> CommunicatingAutomaton.LangSend (fst (snd (\<A> p))) (snd (snd (\<A> p)))"

abbreviation input_language_of_peer
  :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>? _" [90] 110) where
  "\<L>\<^sub>?(p) \<equiv> CommunicatingAutomaton.LangRecv (fst (snd (\<A> p))) (snd (snd (\<A> p)))"

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

inductive_set SyncTraces :: "('information, 'peer) action language"  ("\<T>\<^sub>\<zero>" 120) where
STRun: "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xc \<Longrightarrow> w \<in> \<T>\<^sub>\<zero>"

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

abbreviation initial_mbox_config
  :: "'peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)"  ("\<C>\<^sub>\<I>\<^sub>\<mm>") where
  "\<C>\<^sub>\<I>\<^sub>\<mm> \<equiv> \<lambda>p. (\<I> p, \<epsilon>)"

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

inductive mbox_run
  :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> bound \<Rightarrow>
      ('information, 'peer) action word \<Rightarrow>
      ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) list \<Rightarrow> bool" where
MREmpty:       "mbox_run C k \<epsilon> ([])" |
MRComposedNat: "\<lbrakk>mbox_run C0 (Some k) w xc; last (C0#xc) \<midarrow>\<langle>a, k\<rangle>\<rightarrow> C\<rbrakk> \<Longrightarrow>
                mbox_run C0 (Some k) (w\<cdot>[a]) (xc@[C])" |
MRComposedInf: "\<lbrakk>mbox_run C0 None w xc; last (C0#xc) \<midarrow>\<langle>a, \<infinity>\<rangle>\<rightarrow> C\<rbrakk> \<Longrightarrow>
                mbox_run C0 None (w\<cdot>[a]) (xc@[C])"

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

inductive_set MboxTraces
  :: "nat option \<Rightarrow> ('information, 'peer) action language"  ("\<T>\<^bsub>_\<^esub>" [100] 120)
  for k :: "nat option" where
MTRun: "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> k w xc \<Longrightarrow> w \<in> \<T>\<^bsub>k\<^esub>"

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

section \<open>Synchronisability\<close>

abbreviation is_synchronisable :: "bool" where
  "is_synchronisable \<equiv> \<L>\<^sub>\<infinity> = \<L>\<^sub>\<zero>"

type_synonym 'a topology = "('a \<times> 'a) set"

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

abbreviation Successors :: "'peer topology \<Rightarrow> 'peer \<Rightarrow> 'peer set"  ("_\<langle>_\<rightarrow>\<rangle>" [90, 90] 110) where
  "E\<langle>p\<rightarrow>\<rangle> \<equiv> {q. (p, q) \<in> E}"

abbreviation Predecessors :: "'peer topology \<Rightarrow> 'peer \<Rightarrow> 'peer set"  ("_\<langle>\<rightarrow>_\<rangle>" [90, 90] 110) where
  "E\<langle>\<rightarrow>q\<rangle> \<equiv> {p. (p, q) \<in> E}"

subsection \<open>Synchronisability is Deciable for Tree Topology in Mailbox Communication\<close>

subsubsection \<open>Topology is a Tree\<close>

inductive is_tree :: "'peer set \<Rightarrow> 'peer topology \<Rightarrow> bool" where
ITRoot: "is_tree {p} {}" |
ITNode: "\<lbrakk>is_tree P E; p \<in> P; q \<notin> P\<rbrakk> \<Longrightarrow> is_tree (insert q P) (insert (p, q) E)"

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

abbreviation tree_topology :: "bool" where
  "tree_topology \<equiv> is_tree (UNIV :: 'peer set) (\<G>)"

lemma paranents_in_tree_is_ReceivedFromPeers:
  fixes p :: "'peer"
  assumes "tree_topology"
  shows "\<G>\<langle>\<rightarrow>p\<rangle> = \<P>\<^sub>?(p)"
  sorry

subsubsection "influenced language approaches 1"

inductive path_to_root :: "'peer \<Rightarrow> 'peer list \<Rightarrow> bool" where
PTRRoot: "\<P>\<^sub>?(p) = {} \<Longrightarrow> path_to_root p [p]" |
PTRNode: "\<lbrakk>\<P>\<^sub>?(p) = {q}; path_to_root q as\<rbrakk> \<Longrightarrow> path_to_root p (p # as)"

fun is_root :: "'peer topology \<Rightarrow> 'peer \<Rightarrow> bool" where
"is_root E p = ((card (E\<langle>\<rightarrow>p\<rangle>)) = 0) "

fun get_root :: "'peer topology \<Rightarrow> 'peer" where
"get_root E = (THE x. is_root E x)"

fun get_path_to_root :: "'peer \<Rightarrow>  'peer list" where
"get_path_to_root p = (THE ps. path_to_root p ps)"

fun infl_lang_rec :: "'peer list \<Rightarrow> ('information, 'peer) action language" where
"infl_lang_rec [] = {}" |
"infl_lang_rec [r] = {\<epsilon>}" |
"infl_lang_rec (p # q # ps) = {w | w. w \<in> \<L>(p) \<and> (w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>? \<in> ((infl_lang_rec (q # ps))\<downharpoonright>\<^sub>! )\<downharpoonright>\<^sub>!\<^sub>? \<and> \<P>\<^sub>?(p) = {q}}" 

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


subsubsection "influenced language approaches 2"
text "test and test2 should do the same but I am not 100% sure (hence why I try to prove it with eqtest "

inductive test :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
t0 : "\<lbrakk>\<P>\<^sub>?(r) = {}; w \<in> \<L>(r)\<rbrakk> \<Longrightarrow> test r w" |
t1 : "\<lbrakk>\<P>\<^sub>?(r) = {}; \<P>\<^sub>?(q) = {r}; w \<in> \<L>(q); ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) \<in> ((\<L>(r))\<downharpoonright>\<^sub>!\<^sub>?) \<rbrakk> \<Longrightarrow> test q w" |
t2 : "\<lbrakk>\<P>\<^sub>?(p) = {q}; w \<in> \<L>(p); w' \<in> \<L>(q); test q w'; ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?); ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) \<in> (((\<L>(q))\<downharpoonright>\<^sub>!)\<downharpoonright>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> test p w"

inductive test2 :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
t00: "\<lbrakk>\<P>\<^sub>?(r) = {}; w \<in> \<L>(r)\<rbrakk> \<Longrightarrow> test2 r w" |
t10: "\<lbrakk>\<P>\<^sub>?(r) = {}; \<P>\<^sub>?(q) = {r}; w \<in> \<L>(q); ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) \<in> ((\<L>(r))\<downharpoonright>\<^sub>!\<^sub>?) \<rbrakk> \<Longrightarrow> test2 q w" |
t20: "\<lbrakk>\<P>\<^sub>?(p) = {q}; w \<in> \<L>(p); test2 q w'; ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> test2 p w"

lemma "\<lbrakk>x = 2; y = x + 1; y > x; y < 5\<rbrakk> \<Longrightarrow> y = 3" by auto

lemma eqtest : "test2 p w \<Longrightarrow> test p w"
proof (induction rule:test2.induct)
  case (t00 r w)
  then show ?case 
    by (simp add: t0)
next
  case (t10 r q w)
  then show ?case 
    by (simp add: t1)
next
  case (t20 p q w w')
  moreover have "w' \<in> \<L>(q)" using \<open>test q w'\<close> test.cases by blast
  moreover have "((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) \<in> (((\<L>(q))\<downharpoonright>\<^sub>!)\<downharpoonright>\<^sub>!\<^sub>?)"  using calculation(6) t20.hyps(4) by auto
  moreover have "((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" by (simp add: t20.hyps(4))
  ultimately show ?case sorry
qed

abbreviation infl_lang2 :: "'peer \<Rightarrow> ('information, 'peer) action language" where
"infl_lang2 p \<equiv> {w | w. test p w}"

value "[!\<langle>x\<rangle>, ?\<langle>y\<rangle>, ?\<langle>z\<rangle>]"
value "let w = [!\<langle>x\<rangle>, ?\<langle>y\<rangle>, ?\<langle>z\<rangle>] in ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)"
value "let w' = [?\<langle>a\<rangle>, !\<langle>y\<rangle>, !\<langle>z\<rangle>] in ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"




lemma left_sync_tree [simp]: 
  fixes p q
  assumes "tree_topology" and "is_synchronisable"
  shows "(\<P>\<^sub>?(p) = {q}) \<Longrightarrow> ((((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright> p q)\<downharpoonright>\<^sub>!\<^sub>?) \<subseteq> ((\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?) \<and> ((\<L>\<^sup>*(p)) = (shuffled_lang (\<L>\<^sup>*(p)))))"
proof
  assume "(\<P>\<^sub>?(p) = {q})"
  show "(((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright> p q)\<downharpoonright>\<^sub>!\<^sub>?) \<subseteq> ((\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?)" sorry
next
  assume "(\<P>\<^sub>?(p) = {q})"
  show "((\<L>\<^sup>*(p)) = (shuffled_lang (\<L>\<^sup>*(p))))" sorry
qed
text "assume ?L then show ?R using left_sync_tree"



theorem synchronisability_for_trees:
  assumes "tree_topology"
  shows "is_synchronisable \<longleftrightarrow> (\<forall>p q. (\<P>\<^sub>?(p) = {q} \<longrightarrow> (((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright> p q)\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>? \<and> (\<L>\<^sup>*(p) = shuffled_lang (\<L>\<^sup>*(p))))))" (is "?L \<longleftrightarrow> ?R")
proof 
  assume "?L"
  then show ?R
  proof -
    fix p q
    assume "\<P>\<^sub>?(p) = {q}"
    then show "(((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright> p q)\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>? \<and> (\<L>\<^sup>*(p) = shuffled_lang (\<L>\<^sup>*(p))))"
  qed
  next
    assume ?R
    then show ?L sorry
qed
  

subsubsection \<open>Topology is a Forest\<close>

inductive is_forest :: "'peer set \<Rightarrow> 'peer topology \<Rightarrow> bool" where
IFSingle:  "is_tree P E \<Longrightarrow> is_forest P E" |
IFAddTree: "\<lbrakk>is_forest P1 E1; is_tree P2 E2; P1 \<inter> P2 = {}\<rbrakk> \<Longrightarrow> is_forest (P1 \<union> P2) (E1 \<union> E2)"

abbreviation forest_topology :: "bool" where
  "forest_topology \<equiv> is_forest (UNIV :: 'peer set) (\<G>)"

end

end