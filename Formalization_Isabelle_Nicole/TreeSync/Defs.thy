
theory Defs
    imports "HOL-Library.Sublist" FormalLanguages

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

subsection \<open>Projections & Languages\<close>

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
  swap: "\<lbrakk> is_output a; is_input b ; w = (xs @ a # b # ys) \<rbrakk> 
         \<Longrightarrow> shuffled w (xs @ b # a # ys)" |
  (* Transitive closure *)
  trans: "\<lbrakk> shuffled w w'; shuffled w' w'' \<rbrakk> \<Longrightarrow> shuffled w w''"

abbreviation valid_input_shuffles_of_w :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action language" where
  "valid_input_shuffles_of_w w \<equiv> {w'. shuffled w w'}"

abbreviation valid_input_shuffle :: 
  "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" (infixl "\<squnion>\<squnion>\<^sub>?" 60) where
  "w' \<squnion>\<squnion>\<^sub>? w \<equiv> shuffled w w'"

(* All possible shuffles of a word *)
definition all_shuffles :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word set" where
  "all_shuffles w = {w'. shuffled w w'}"

(* Shuffled language *)
definition shuffled_lang :: "('information, 'peer) action  language \<Rightarrow> ('information, 'peer) action language" where
  "shuffled_lang L = (\<Union>w\<in>L. all_shuffles w)"

abbreviation shuffling_possible :: "('information, 'peer) action word \<Rightarrow> bool" where
  "shuffling_possible w \<equiv> (\<exists> xs a b ys. is_output a \<and> is_input b \<and> w = (xs @ a # b # ys))"

abbreviation shuffling_occurred :: "('information, 'peer) action word \<Rightarrow> bool" where
  "shuffling_occurred w \<equiv> (\<exists> xs a b ys. is_output a \<and> is_input b \<and> w = (xs @ b # a # ys))"

(*w' is the result of shuffling w once, on the rightmost eligible pair*) 
abbreviation rightmost_shuffle :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
  "rightmost_shuffle w w' \<equiv> (\<exists> xs a b ys. is_output a \<and> is_input b \<and> w = (xs @ a # b # ys) \<and> (\<not> shuffling_possible ys) \<and> w' = (xs @ b # a # ys))"

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

inductive_set Actions :: "('information, 'peer) action set"  ("Act") where
  ActOfTrans: "(s1, a, s2) \<in> Transitions \<Longrightarrow> a \<in> Act"

inductive_set CommunicationPartners :: "'peer set" where
  CPAction: "(s1, a, s2) \<in> Transitions \<Longrightarrow> get_object a \<in> CommunicationPartners"

inductive_set SendingToPeers :: "'peer set" where
  SPSend: "\<lbrakk>(s1, a, s2) \<in> Transitions; is_output a\<rbrakk> \<Longrightarrow> get_object a \<in> SendingToPeers"

inductive_set ReceivingFromPeers :: "'peer set" where
  RPRecv: "\<lbrakk>(s1, a, s2) \<in> Transitions; is_input a\<rbrakk> \<Longrightarrow> get_object a \<in> ReceivingFromPeers"

abbreviation step
  :: "'state \<Rightarrow> ('information, 'peer) action \<Rightarrow> 'state \<Rightarrow> bool"  ("_ \<midarrow>_\<rightarrow>\<^sub>\<C> _" [90, 90, 90] 110)
  where
    "s1 \<midarrow>a\<rightarrow>\<^sub>\<C> s2 \<equiv> (s1, a, s2) \<in> Transitions"

(*
\<comment> \<open>this is the original run def, i swapped it to (a#w) (see below)\<close>
inductive run :: "'state \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'state list \<Rightarrow> bool" where
REmpty:    "run s \<epsilon> ([])" |
RComposed: "\<lbrakk>run s0 w xs; last (s0#xs) \<midarrow>a\<rightarrow> s\<rbrakk> \<Longrightarrow> run s0 (w\<sqdot>[a]) (xs@[s])"
*)

inductive run :: "'state \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'state list \<Rightarrow> bool" where
  REmpty2:    "run s \<epsilon> ([])" |
  RComposed2: "\<lbrakk>run s1 w xs; s0 \<midarrow>a\<rightarrow>\<^sub>\<C> s1\<rbrakk> \<Longrightarrow> run s0 (a # w) (s1 # xs)"

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

abbreviation step_of_peer
  :: "'state \<Rightarrow> ('information, 'peer) action \<Rightarrow> 'peer \<Rightarrow> 'state \<Rightarrow> bool"
  ("_ \<midarrow>_\<rightarrow>\<^sub>\<C>_ _" [90, 90, 90, 90] 110) where
  "s1 \<midarrow>a\<rightarrow>\<^sub>\<C>p s2 \<equiv> (s1, a, s2) \<in> snd (snd (\<A> p))"

abbreviation language_of_peer
  :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L> _" [90] 110) where
  "\<L>(p) \<equiv> CommunicatingAutomaton.Lang (fst (snd (\<A> p))) (snd (snd (\<A> p)))"

abbreviation output_language_of_peer
  :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>! _" [90] 110) where
  "\<L>\<^sub>!(p) \<equiv> CommunicatingAutomaton.LangSend (fst (snd (\<A> p))) (snd (snd (\<A> p)))"

abbreviation input_language_of_peer
  :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>? _" [90] 110) where
  "\<L>\<^sub>?(p) \<equiv> CommunicatingAutomaton.LangRecv (fst (snd (\<A> p))) (snd (snd (\<A> p)))"

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


subsection \<open>Synchronous System\<close>

definition is_sync_config :: "('peer \<Rightarrow> 'state) \<Rightarrow> bool" where
  "is_sync_config C \<equiv> (\<forall>p. C p \<in> \<S>(p))"

abbreviation initial_sync_config :: "'peer \<Rightarrow> 'state"  ("\<C>\<^sub>\<I>\<^sub>\<zero>") where
  "\<C>\<^sub>\<I>\<^sub>\<zero> \<equiv> \<lambda>p. \<I>(p)"

inductive sync_step
  :: "('peer \<Rightarrow> 'state) \<Rightarrow> ('information, 'peer) action \<Rightarrow> ('peer \<Rightarrow> 'state) \<Rightarrow> bool"
  ("_ \<midarrow>\<langle>_, \<zero>\<rangle>\<rightarrow> _" [90, 90, 90] 110) where
  SynchStep: "\<lbrakk>is_sync_config C1; a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>; C1 p \<midarrow>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>\<^sub>\<C>p (C2 p);
             C1 q \<midarrow>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>\<^sub>\<C>q (C2 q); \<forall>x. x \<notin> {p, q} \<longrightarrow> C1(x) = C2(x)\<rbrakk> \<Longrightarrow> C1 \<midarrow>\<langle>a, \<zero>\<rangle>\<rightarrow> C2"

inductive sync_run
  :: "('peer \<Rightarrow> 'state) \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('peer \<Rightarrow> 'state) list \<Rightarrow> bool"
  where
    SREmpty:    "sync_run C \<epsilon> ([])" |
    SRComposed: "\<lbrakk>sync_run C0 w xc; last (C0#xc) \<midarrow>\<langle>a, \<zero>\<rangle>\<rightarrow> C\<rbrakk> \<Longrightarrow> sync_run C0 (w\<sqdot>[a]) (xc@[C])"

\<comment> \<open>E(Nsync)\<close>
inductive_set SyncTraces :: "('information, 'peer) action language"  ("\<T>\<^sub>\<zero>" 120) where
  STRun: "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xc \<Longrightarrow> w \<in> \<T>\<^sub>\<zero>"

\<comment> \<open>T(Nsync)\<close>
abbreviation SyncLang :: "('information, 'peer) action language"  ("\<L>\<^sub>\<zero>" 120) where
  "\<L>\<^sub>\<zero> \<equiv> \<T>\<^sub>\<zero>"


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

definition is_stable
  :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> bool" where
  "is_stable C \<equiv> is_mbox_config C \<and> (\<forall>p. snd (C p) = \<epsilon>)"

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
  MboxSend: "\<lbrakk>is_mbox_config C1; a = !\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>; fst (C1 p) \<midarrow>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>\<^sub>\<C>p (fst (C2 p));
            snd (C1 p) = snd (C2 p); ( | (snd (C1 q)) | ) <\<^sub>\<B> k;
            C2 q = (fst (C1 q), (snd (C1 q)) \<sqdot> [(i\<^bsup>p\<rightarrow>q\<^esup>)]); \<forall>x. x \<notin> {p, q} \<longrightarrow> C1(x) = C2(x)\<rbrakk> \<Longrightarrow>
            mbox_step C1 a k C2" |
  MboxRecv: "\<lbrakk>is_mbox_config C1; a = ?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>; fst (C1 q) \<midarrow>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>\<^sub>\<C>q (fst (C2 q));
            (snd (C1 q)) = [(i\<^bsup>p\<rightarrow>q\<^esup>)] \<sqdot> snd (C2 q); \<forall>x. x \<noteq> q \<longrightarrow> C1(x) = C2(x)\<rbrakk> \<Longrightarrow>
            mbox_step C1 a k C2"

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

subsubsection "mbox run"

inductive mbox_run
  :: "('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) \<Rightarrow> bound \<Rightarrow>
      ('information, 'peer) action word \<Rightarrow>
      ('peer \<Rightarrow> ('state \<times> ('information, 'peer) message word)) list \<Rightarrow> bool" where
  MREmpty:       "mbox_run C k \<epsilon> ([])" |
  MRComposedNat: "\<lbrakk>mbox_run C0 (Some k) w xc; last (C0#xc) \<midarrow>\<langle>a, k\<rangle>\<rightarrow> C\<rbrakk> \<Longrightarrow>
                mbox_run C0 (Some k) (w\<sqdot>[a]) (xc@[C])" |
  MRComposedInf: "\<lbrakk>mbox_run C0 None w xc; last (C0#xc) \<midarrow>\<langle>a, \<infinity>\<rangle>\<rightarrow> C\<rbrakk> \<Longrightarrow>
                mbox_run C0 None (w\<sqdot>[a]) (xc@[C])"

subsubsection "mbox traces"
\<comment> \<open>E(mbox)\<close>
inductive_set MboxTraces
  :: "nat option \<Rightarrow> ('information, 'peer) action language"  ("\<T>\<^bsub>_\<^esub>" [100] 120)
  for k :: "nat option" where
    MTRun: "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> k w xc \<Longrightarrow> w \<in> \<T>\<^bsub>k\<^esub>"

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

section \<open>Synchronisability\<close>

abbreviation is_synchronisable :: "bool" where
  "is_synchronisable \<equiv> \<L>\<^sub>\<infinity> = \<L>\<^sub>\<zero>"

type_synonym 'a topology = "('a \<times> 'a) set"

\<comment> \<open>the topology graph of all peers\<close>
inductive_set Edges :: "'peer topology"  ("\<G>" 110) where
  TEdge: "i\<^bsup>p\<rightarrow>q\<^esup> \<in> \<M> \<Longrightarrow> (p, q) \<in> \<G>"

abbreviation Successors :: "'peer topology \<Rightarrow> 'peer \<Rightarrow> 'peer set"  ("_\<langle>_\<rightarrow>\<rangle>" [90, 90] 110) where
  "E\<langle>p\<rightarrow>\<rangle> \<equiv> {q. (p, q) \<in> E}"

abbreviation Predecessors :: "'peer topology \<Rightarrow> 'peer \<Rightarrow> 'peer set"  ("_\<langle>\<rightarrow>_\<rangle>" [90, 90] 110) where
  "E\<langle>\<rightarrow>q\<rangle> \<equiv> {p. (p, q) \<in> E}"

subsection \<open>Synchronisability is Deciable for Tree Topology in Mailbox Communication\<close>

subsubsection \<open>Topology is a Tree\<close>

inductive is_tree :: "'peer set \<Rightarrow> 'peer topology \<Rightarrow> bool" where
  ITRoot: "is_tree {p} {}" |
  ITNode: "\<lbrakk>is_tree P E; p \<in> P; q \<notin> P\<rbrakk> \<Longrightarrow> is_tree (insert q P) (insert (p, q) E)"

abbreviation tree_topology :: "bool" where
  "tree_topology \<equiv> is_tree (UNIV :: 'peer set) (\<G>)"

abbreviation is_root_from_topology :: "'peer \<Rightarrow> bool" where
  "is_root_from_topology p \<equiv> (tree_topology \<and> \<G>\<langle>\<rightarrow>p\<rangle> = {})"

abbreviation is_root_from_local :: "'peer \<Rightarrow> bool"  where
  "is_root_from_local p \<equiv> tree_topology \<and> \<P>\<^sub>?(p) = {} \<and> (\<forall>q. p \<notin> \<P>\<^sub>!(q))"

abbreviation is_root :: "'peer \<Rightarrow> bool"  where
  "is_root p \<equiv> is_root_from_local p \<or> is_root_from_topology p"
  (*tree_topology \<and> ((\<P>\<^sub>?(p) = {} \<and> (\<forall>q. p \<notin> \<P>\<^sub>!(q))) \<or> \<G>\<langle>\<rightarrow>p\<rangle> = {})*)

abbreviation is_node_from_topology :: "'peer \<Rightarrow> bool" where
  "is_node_from_topology p \<equiv> (tree_topology \<and> (\<exists>q. \<G>\<langle>\<rightarrow>p\<rangle> = {q}))"

abbreviation is_node_from_local :: "'peer \<Rightarrow> bool"  where
  "is_node_from_local p \<equiv> tree_topology \<and> (\<exists>q. \<P>\<^sub>?(p) = {q} \<or> p \<in> \<P>\<^sub>!(q))"

abbreviation is_node :: "'peer \<Rightarrow> bool"  where
  "is_node p \<equiv> is_node_from_topology p \<or> is_node_from_local p"

subsubsection "parent-child relationship in tree"

(*q is parent of p*)
inductive is_parent_of :: "'peer \<Rightarrow> 'peer \<Rightarrow> bool" where
  node_parent : "\<lbrakk>is_node p; \<G>\<langle>\<rightarrow>p\<rangle> = {q}\<rbrakk> \<Longrightarrow> is_parent_of p q"

subsubsection "path to root and path related lemmas"

inductive path_to_root :: "'peer \<Rightarrow> 'peer list \<Rightarrow> bool" where
  PTRRoot: "\<lbrakk>is_root p\<rbrakk> \<Longrightarrow> path_to_root p [p]" |
  PTRNode: "\<lbrakk>tree_topology; is_parent_of p q; path_to_root q as; distinct (p # as)\<rbrakk> \<Longrightarrow> path_to_root p (p # as)"

definition get_root :: "'peer topology \<Rightarrow> 'peer" where "get_root E = (THE x. is_root x)"

abbreviation get_path_to_root :: "'peer \<Rightarrow>  'peer list" where
  "get_path_to_root p \<equiv>  (THE ps. path_to_root p ps)"

inductive path_from_root :: "'peer \<Rightarrow> 'peer list \<Rightarrow> bool" where
  PFRRoot: "\<lbrakk>is_root p\<rbrakk> \<Longrightarrow> path_from_root p [p]" |
  PFRNode: "\<lbrakk>tree_topology; is_parent_of p q; path_from_root q as; distinct (as @ [p])\<rbrakk> \<Longrightarrow> path_from_root p (as @ [p])"

inductive path_from_to :: "'peer \<Rightarrow> 'peer \<Rightarrow> 'peer list \<Rightarrow> bool" where
  path_refl: "\<lbrakk>tree_topology; p \<in> \<P>\<rbrakk> \<Longrightarrow> path_from_to p p [p]" |
  path_step: "\<lbrakk>tree_topology; is_parent_of p q; path_from_to r q as; distinct (as @ [p])\<rbrakk> \<Longrightarrow> path_from_to r p (as @ [p])"

subsection "Influenced Language"

(*fixed: without projection to p and q to the sends of w', the influenced language 
is only correct if each node sends to exactly one child
side note: proj. only needed in w', since by tree topology, each node p has a unique parent, and thus the receives 
in w can already only be between p and q (i.e. the projection can be added for w as well but is unnecessary)*)
inductive is_in_infl_lang :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
  IL_root: "\<lbrakk>is_root r; w \<in> \<L>(r)\<rbrakk> \<Longrightarrow> is_in_infl_lang r w" | \<comment>\<open>influenced language of root r is language of r\<close>
  IL_node: "\<lbrakk>tree_topology; is_parent_of p q; w \<in> \<L>(p); is_in_infl_lang q w'; ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> is_in_infl_lang p w" \<comment>\<open>p is any node and q its parent has a matching send for each of p's receives\<close>

abbreviation InfluencedLanguage :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sup>* _" [90] 100) where
  "\<L>\<^sup>* p \<equiv> {w. is_in_infl_lang p w}"

abbreviation InfluencedLanguageSend :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>!\<^sup>* _" [90] 100) where
  "\<L>\<^sub>!\<^sup>* p \<equiv> (\<L>\<^sup>* p)\<downharpoonright>\<^sub>! "

abbreviation InfluencedLanguageRecv :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>?\<^sup>* _" [90] 100) where
  "\<L>\<^sub>?\<^sup>* p \<equiv> (\<L>\<^sup>* p)\<downharpoonright>\<^sub>? "

abbreviation ShuffledInfluencedLanguage :: "'peer \<Rightarrow> ('information, 'peer) action language" ("\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion> _" [90] 100) where
  "\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion> p \<equiv> shuffled_lang (\<L>\<^sup>* p)"

\<comment> \<open>p receives from no one and there is no q that sends to p\<close>
abbreviation no_sends_to_or_recvs_in :: "'peer \<Rightarrow> bool"  where
  "no_sends_to_or_recvs_in p \<equiv> (\<P>\<^sub>?(p) = {} \<and> (\<forall>q. p \<notin> \<P>\<^sub>!(q)))"

subsubsection "simulate sync with mbox word"

\<comment> \<open>for each sending action, add the matching receive action directly after it\<close>
fun add_matching_recvs :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word" where
  "add_matching_recvs [] = []" |
  "add_matching_recvs (a # w) = (if is_output a
      then a # (?\<langle>get_message a\<rangle>) # add_matching_recvs w 
      else a # add_matching_recvs w)"


subsubsection "Lemma 4.4 and preparations"


(*this should do the same thing as concat_infl but more straightforward *)
inductive acc_infl_lang_word :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
  ACC_root: "\<lbrakk>is_root r; w \<in> \<L>\<^sup>*(r)\<rbrakk> \<Longrightarrow> acc_infl_lang_word r w" | \<comment>\<open>influenced language of root r is language of r\<close>
  ACC_node: "\<lbrakk>tree_topology; is_parent_of p q; w \<in> \<L>\<^sup>*(p); acc_infl_lang_word q w'; ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> acc_infl_lang_word p (w' @ w)" \<comment>\<open>p is any node and q its parent has a matching send for each of p's receives\<close>

(*starts at some node and a full path from that node to root, then walks up to the root while accumulating the word w1....wn*)
inductive concat_infl :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'peer list  \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" for p::"'peer" and w:: "('information, 'peer) action word" where
  at_p: "\<lbrakk>tree_topology; w \<in> \<L>\<^sup>*(p); path_to_root p ps\<rbrakk> \<Longrightarrow> concat_infl p w ps w" | (*start condition*)
  reach_root: "\<lbrakk>is_root q; qw \<in> \<L>\<^sup>*(q); path_to_root x (x # [q]); (\<forall>g. w_acc\<down>\<^sub>g \<in> \<L>\<^sup>*(g));  concat_infl p w (x # [q]) w_acc; (((w_acc\<down>\<^sub>x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((qw\<down>\<^sub>{\<^sub>x\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> concat_infl p w [q] (qw \<sqdot> w_acc)" | (*end condition*)
  node_step: "\<lbrakk>tree_topology; \<P>\<^sub>?(x) = {q}; (\<forall>g. w_acc\<down>\<^sub>g \<in> \<L>\<^sup>*(g)); path_to_root x (x # q # ps); qw \<in> \<L>\<^sup>*(q); concat_infl p w (x # q # ps) w_acc; (((w_acc\<down>\<^sub>x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((qw\<down>\<^sub>{\<^sub>x\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> concat_infl p w (q#ps) (qw \<sqdot> w_acc)" 

section "new formalization"

(*all receives possible in Aq, after performing actions in w*)
abbreviation possible_recv_suffixes :: "('information, 'peer) action word \<Rightarrow> 'peer \<Rightarrow>  ('information, 'peer) action language"  ("\<ddagger>_\<ddagger>\<^sub>_" [90, 90] 110) where  
  "\<ddagger>w\<ddagger>\<^sub>p \<equiv> {x\<down>\<^sub>? | x. (w \<sqdot> x) \<in> \<L>\<^sup>*(p)}"


(*all possible sends from q to p in Aq, after performing actions in w
if p is not child of q, the set is trivially {\<epsilon>}*)
abbreviation possible_send_suffixes_to_peer :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'peer \<Rightarrow>  ('information, 'peer) action language"  ("\<^sub>_\<ddagger>_\<ddagger>\<^sub>_" [90, 90, 90] 110) where  
  "\<^sub>q\<ddagger>w\<ddagger>\<^sub>p \<equiv> {(x\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} | x. (w \<sqdot> x) \<in> \<L>\<^sup>*(q)}"

(*for all words w in p, for all w' that provide all the sends for the receives in w,
w must be able to receive anything that q might send after performing w'.

(there must be at least one such w' per w, otherwise w is not in the influenced language of p)*)
definition subset_condition :: "'peer \<Rightarrow> 'peer \<Rightarrow> bool"
  where "subset_condition p q \<longleftrightarrow> (\<forall> w \<in> \<L>\<^sup>*(p). \<forall> w' \<in> \<L>\<^sup>*(q).
  (((w'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? = ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)) \<longrightarrow> ((\<^sub>q\<ddagger>w'\<ddagger>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<ddagger>w\<ddagger>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>? ))"

(*for all parent-child pairs, subset condition and shuffled language condition hold*)
definition theorem_rightside :: "bool"
  where "theorem_rightside \<longleftrightarrow> (\<forall>p \<in> \<P>. \<forall>q \<in> \<P>. ((is_parent_of p q) \<longrightarrow> ((subset_condition p q) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) ))"


subsection "=> 1. "

(*mix some w' of L*(Aq) with matching w of L*(Ap) s.t. each send in q (to p!) is directly followed
by the matching send. The order of the peer words in the result word is kept*)
fun mix_pair :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word" where
 "mix_pair [] [] acc = acc" |
 "mix_pair (a # w') [] acc = mix_pair w' [] (a # acc)" |
 "mix_pair [] (a # w) acc = mix_pair [] w (a # acc)" |
 "mix_pair (a # w') (b # w) acc  = (if a = !\<langle>get_message b\<rangle>
      then (if b = ?\<langle>get_message a\<rangle> then mix_pair w' w (a # b # acc) else mix_pair (a # w') w (b # acc))
      else mix_pair w' (b # w) (a # acc))"

subsection "=> 2."
(*construction: do mix_pair until k is reached, for k and k+1 instead put vq's send and then both v!k and v!(k+1) and then continue with mix_pair construction*)
inductive mix_shuf :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where  
  mix_shuf_constr: "\<lbrakk>vq\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? = v\<down>\<^sub>?\<down>\<^sub>!\<^sub>?; v' \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p); v' \<squnion>\<squnion>\<^sub>? v; v \<in> \<L>\<^sup>*(p); vq \<in> \<L>\<^sup>*(q); 
vq = (as \<sqdot> a_send # bs); v = xs \<sqdot> b # a_recv # ys; get_message a_recv = get_message a_send; is_input a_recv; is_output a_send; is_output b\<rbrakk> 
\<Longrightarrow> mix_shuf vq v v' ((mix_pair as xs []) \<sqdot> a_send # b # a_recv # (mix_pair bs ys []))"



end
end
