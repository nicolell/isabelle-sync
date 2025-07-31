(* Author: Kirstin Peters, Augsburg University, 2024 *)

theory CommunicatingAutomata
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

subsubsection \<open>projection simplifications on words/general cases\<close>

lemma proj_trio_inv:
  shows "((w\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = ((w\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}"
proof (induct w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case by fastforce
qed

lemma proj_trio_inv2:
  shows "(((w'\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>q)" 
proof (induct w')
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case by (metis (no_types, lifting) filter.simps(2))
qed


value "prefix [1] [1,2::nat]"
value "prefix [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>, !\<langle>(a\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>]" 


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

lemma only_one_actor_proj:
  assumes "w = w\<down>\<^sub>q" and "p \<noteq> q"
  shows "w\<down>\<^sub>p = \<epsilon>"
  by (metis (mono_tags, lifting) assms(1,2) filter_False filter_id_conv)

lemma filter_pair_commutative:
  shows "filter g (filter f xs) = filter f (filter g xs)"
proof (induction xs)
  case Nil
  then show ?case by simp
next
  case (Cons x xs)
  then show ?case
    by (simp add: conj_commute)
qed

lemma pair_proj_to_object_proj:
  assumes "(w\<down>\<^sub>p) = w"
  shows "w\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = (filter (\<lambda>x. get_object x = q) w)"
  by (smt (verit, del_insts) assms filter_cong filter_id_conv)

lemma actor_proj_app_inv: 
  assumes "(u@v)\<down>\<^sub>p = (u@v)"
  shows "u = u\<down>\<^sub>p \<and> v = v\<down>\<^sub>p"
  using assms
proof -
  from assms have "(u@v)\<down>\<^sub>p = u @ v" 
    by simp
  moreover have "(u@v)\<down>\<^sub>p = (u)\<down>\<^sub>p @ (v)\<down>\<^sub>p"
    by (rule filter_append)
  ultimately have eq: "(u)\<down>\<^sub>p @ (v)\<down>\<^sub>p = u @ v" by argo
  have u_len: "length (u\<down>\<^sub>p) \<le> length u" using length_filter_le by blast
  have v_len: "length (v\<down>\<^sub>p) \<le> length v" using length_filter_le by blast
  have t1: "(u)\<down>\<^sub>p = u"
  proof (rule ccontr)
    assume "u\<down>\<^sub>p \<noteq> u" 
    then have "length (u\<down>\<^sub>p) < length u" by (metis u_len \<open>(u \<cdot> v)\<down>\<^sub>p = u\<down>\<^sub>p \<cdot> v\<down>\<^sub>p\<close> \<open>u\<down>\<^sub>p \<noteq> u\<close> append_eq_append_conv assms le_neq_implies_less)
    then have "length ((u)\<down>\<^sub>p @ (v)\<down>\<^sub>p) \<le> length ((u@v))" by (metis \<open>(u \<cdot> v)\<down>\<^sub>p = u\<down>\<^sub>p \<cdot> v\<down>\<^sub>p\<close> length_filter_le)
    have "length ((u)\<down>\<^sub>p @ (v)\<down>\<^sub>p) = length (u\<down>\<^sub>p) + length (v\<down>\<^sub>p)" by simp
    have "length (u\<down>\<^sub>p) + length (v\<down>\<^sub>p) < length (u) + length (v)"  by (simp add: \<open>|u\<down>\<^sub>p| < |u|\<close> add_less_le_mono)
    then show "False" using eq length_append less_not_refl by metis
  qed
  have t2: "(v)\<down>\<^sub>p = v"
  proof (rule ccontr)
    assume "v\<down>\<^sub>p \<noteq> v" 
    then have "length (v\<down>\<^sub>p) < length v" by (metis v_len \<open>(u \<cdot> v)\<down>\<^sub>p = u\<down>\<^sub>p \<cdot> v\<down>\<^sub>p\<close> \<open>v\<down>\<^sub>p \<noteq> v\<close> append_eq_append_conv assms le_neq_implies_less)
    then have "length ((u)\<down>\<^sub>p @ (v)\<down>\<^sub>p) \<le> length ((u@v))" by (metis \<open>(u \<cdot> v)\<down>\<^sub>p = u\<down>\<^sub>p \<cdot> v\<down>\<^sub>p\<close> length_filter_le)
    have "length ((u)\<down>\<^sub>p @ (v)\<down>\<^sub>p) = length (u\<down>\<^sub>p) + length (v\<down>\<^sub>p)" by simp
    then show "False" using \<open>(u \<cdot> v)\<down>\<^sub>p = u\<down>\<^sub>p \<cdot> v\<down>\<^sub>p\<close> \<open>u\<down>\<^sub>p = u\<close> \<open>v\<down>\<^sub>p \<noteq> v\<close> assms same_append_eq by metis
  qed

  show ?thesis using t1 t2 by simp
qed

lemma actors_4_proj_app_inv: 
  assumes "(a @ b @ c @ d)\<down>\<^sub>p = (a @ b @ c @ d)" 
  shows "a\<down>\<^sub>p = a \<and> b\<down>\<^sub>p = b \<and> c\<down>\<^sub>p = c \<and> d\<down>\<^sub>p = d"
  by (metis actor_proj_app_inv assms)

lemma not_only_sends_impl_recv:
  assumes "w \<noteq> w\<down>\<^sub>!"
  shows "\<exists>x. x \<in> set w \<and> is_input x"
  by (metis assms filter_True)

lemma orderings_inv_for_prepend:
  assumes "w\<down>\<^sub>? = w'\<down>\<^sub>?" and "w\<down>\<^sub>! = w'\<down>\<^sub>!"
  shows "(a # w)\<down>\<^sub>? = (a # w')\<down>\<^sub>? \<and> (a # w)\<down>\<^sub>! = (a # w')\<down>\<^sub>!"
  by (simp add: assms(1,2))

(*this only holds if w and w' start with the same action, this is NOT true in general*)
lemma orderings_inv_for_prepend_rev:
  assumes "(a # w)\<down>\<^sub>? = (a # w')\<down>\<^sub>?" and "(a # w)\<down>\<^sub>! = (a # w')\<down>\<^sub>!"
  shows "w\<down>\<^sub>? = w'\<down>\<^sub>? \<and> w\<down>\<^sub>! = w'\<down>\<^sub>!"
  by (metis (no_types, lifting) assms(1,2) filter.simps(2) list.inject)

lemma prefix_trans:
  assumes "prefix x z" 
  shows "\<exists> y. prefix y z \<and> x = y" 
  by (simp add: assms)

lemma prefix_inv_no_signs:
  assumes  "prefix w w'"
shows "prefix (w\<down>\<^sub>!\<^sub>?) (w'\<down>\<^sub>!\<^sub>?)"
  using map_mono_prefix assms by auto


subsection \<open>Shuffled Language\<close>

inductive shuffled ::"('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
  (* Base case: every word shuffles to itself *)
  refl: "shuffled w w" |
  (* Single swap: !x?y \<rightarrow> ?y!x *)
  swap: "\<lbrakk> is_output a; is_input b ; w = (xs @ a # b # ys) \<rbrakk> 
         \<Longrightarrow> shuffled w (xs @ b # a # ys)" |
  (* Transitive closure *)
  trans: "\<lbrakk> shuffled w w'; shuffled w' w'' \<rbrakk> \<Longrightarrow> shuffled w w''"

lemma shuffled_rev:
  assumes "shuffled w w'"
  shows "w = w' \<or> (\<exists> a b xs ys. w =  (xs @ a # b # ys) \<and> is_output a \<and> is_input b \<and> w' = (xs @ b # a # ys)) \<or> (\<exists>tmp. shuffled w tmp \<and> shuffled tmp w')"
  using assms shuffled.refl by blast

lemma shuffled_prepend_inductive:
  assumes "shuffled w w'"
  shows "shuffled (a # w) (a # w')"
  using assms
proof (induct)
  case (refl w)
  then show ?case using shuffled.refl by auto
next
  case (swap a b w xs ys)
  then show ?case by (metis (no_types, lifting) Cons_eq_appendI shuffled.simps)
next
  case (trans w w' w'')
  then show ?case using shuffled.trans by auto
qed

lemma fully_shuffled_gen:
  assumes "xs = xs\<down>\<^sub>!"
  shows "shuffled (xs @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]) ([?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs)  "
  using assms 
proof (induct xs)
  case Nil
  then show ?case by (simp add: shuffled.refl)
next
  case (Cons y ys)
  then have "ys = ys\<down>\<^sub>!"  by (metis filter.simps(2) impossible_Cons length_filter_le list.inject)
  then have "shuffled (ys \<cdot> ?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon>) (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<cdot> ys)"  using Cons.hyps by blast
  have "is_output y"  by (meson Cons.prems Cons_eq_filterD)
  then have last_step: "shuffled (y # ?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # ys) (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<cdot> y # ys)"  by (metis Cons_eq_appendI eq_Nil_appendI is_output.simps(2) shuffled.swap)
  have "shuffled (y # ys \<cdot> ?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon>) (y # ?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # ys)"  using \<open>shuffled (ys \<cdot> ?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon>) (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<cdot> ys)\<close> shuffled_prepend_inductive by fastforce
  then show ?case by (meson last_step shuffled.trans)
qed

lemma fully_shuffled_w_prepend: 
  assumes "xs = xs\<down>\<^sub>!"
  shows "shuffled (w @ xs @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]) (w @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs)"
  using assms 
proof (induct w)
  case Nil
  then show ?case by (metis append_Nil fully_shuffled_gen)
next
  case (Cons a w)
  then show ?case  using shuffled_prepend_inductive by auto
qed

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
  assumes "w \<in> L"
  shows "w \<in> shuffled_lang L"
  using assms by (simp add: input_shuffle_implies_shuffled_lang shuffled.refl)

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

lemma shuffle_keeps_outputs_right_shuffled:
  assumes "shuffled w w'" and "is_output (last w)" 
  shows "is_output (last w')" 
using assms 
proof (induct rule: shuffled.induct)
  case (refl w)
  then show ?case by simp
next
  case (swap a b w xs ys)
  then show ?case by auto
next
  case (trans w w' w'')
  then show ?case by simp
qed

lemma all_shuffles_rev:
  assumes "w' \<in> all_shuffles w"
  shows "shuffled w w'"
  using all_shuffles_def assms by auto

lemma shuffled_lang_rev: 
  assumes "w \<in> shuffled_lang L"
  shows "\<exists> w'. w' \<in> L \<and> w \<in> all_shuffles w'"
  using assms shuffled_lang_def by auto

lemma shuffled_lang_impl_valid_shuffle :
  assumes "v \<in> shuffled_lang L" 
  shows "\<exists>v'. ( v \<squnion>\<squnion>\<^sub>? v' \<and> v' \<in> L)"
  by (meson all_shuffles_rev assms shuffled_lang_rev)

lemma fully_shuffled_valid_gen:
  assumes "(xs @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]) \<in> L" and "xs = xs\<down>\<^sub>!"
  shows "([?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs) \<squnion>\<squnion>\<^sub>? (xs @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>])"
  by (meson assms(2) fully_shuffled_gen)

abbreviation shuffling_possible :: "('information, 'peer) action word \<Rightarrow> bool" where
  "shuffling_possible w \<equiv> (\<exists> xs a b ys. is_output a \<and> is_input b \<and> w = (xs @ a # b # ys))"

abbreviation shuffling_occurred :: "('information, 'peer) action word \<Rightarrow> bool" where
  "shuffling_occurred w \<equiv> (\<exists> xs a b ys. is_output a \<and> is_input b \<and> w = (xs @ b # a # ys))"

lemma shuffling_possible_to_existing_shuffle:
  assumes "shuffling_possible w" 
  shows "\<exists>w'. shuffled w w' \<and> w \<noteq> w'"   using assms shuffled.swap by fastforce

subsubsection "rightmost shuffle & related"

lemma rightmost_shuffle_exists:
  assumes "v \<in> shuffled_lang L" and "shuffling_occurred v" 
  shows "\<exists> xs a b ys. v = (xs @ b # a # ys) \<and>  v \<squnion>\<squnion>\<^sub>? (xs @ a # b # ys)" 
  using assms(2) shuffled.swap by blast

lemma length_index_bound:
  shows "Suc (length xs) < length (xs @ a # b # ys)"
proof -
  have "length (xs @ a # b # ys) = length xs + length (a # b # ys)"
    by simp
  also have "length (a # b # ys) = 2 + length ys"
    by simp
  finally show ?thesis
    by simp
qed

lemma shuffle_index_exists: 
  assumes "shuffling_possible v"
  shows "\<exists> i. is_output (v!i) \<and> is_input (v!(Suc i)) \<and> (Suc i) < length v" 
proof -
  obtain xs a b ys where "is_output a" and " is_input b" and "v = (xs @ a # b # ys)" using assms by auto
  have t1: "v!(length xs) = a" by (simp add: \<open>v = xs \<cdot> a # b # ys\<close>)
  then have t2: "v!(Suc (length xs)) = b"  by (metis Cons_nth_drop_Suc \<open>v = xs \<cdot> a # b # ys\<close> append_eq_conv_conj drop_all linorder_le_less_linear
        list.distinct(1) list.inject)
  have t3: "(Suc (length xs)) < length v"  by (simp add: \<open>v = xs \<cdot> a # b # ys\<close>)
  from t1 t2 t3 have "is_output (v!(length xs)) \<and> is_input (v!(Suc (length xs))) \<and> (Suc (length xs)) < length v" 
    by (simp add: \<open>is_input b\<close> \<open>is_output a\<close>) 
  then show ?thesis by auto
qed

value "drop 5 [0,1,2,3,4,10,10,5,5,5,5,5::nat]" 

(*this is to uniquely obtain the shuffle used in the theorem later
it assumes that the word can be shuffled at least once,
but if the word can't be shuffled the thesis in the theorem trivially holds anyways
\<rightarrow> a case distinction over whether (w @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs) can be shuffled, is needed*)
lemma rightmost_shuffle_index_exists: 
  assumes "shuffling_possible v"
  shows "\<exists> i. is_output (v!i) \<and> is_input (v!(Suc i)) \<and> (Suc i) < length v \<and> \<not> (shuffling_possible (drop (Suc i) v))" 
  using assms
proof (induct v)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case
  proof (cases "shuffling_possible w")
    case True
    then obtain xs ys x y where  w_decomp: "is_output x \<and> is_input y \<and> w = xs \<cdot> x # y # ys" by blast
    then obtain i where i_def: "is_output (w ! i) \<and>
        is_input (w ! Suc i) \<and>
        Suc i < |w| \<and> (\<nexists>xs a b ys. is_output a \<and> is_input b \<and> drop (Suc i) w = xs \<cdot> a # b # ys)"
      using Cons.hyps by blast

    have "(a # w) = a # (xs \<cdot> x # y # ys)"   by (simp add: w_decomp)
    have t1: "is_output ((a # w) ! (Suc i))"  by (simp add: i_def)
    have t2: "is_input ((a # w) ! (Suc (Suc i)))" by (simp add: i_def)
    have t3: "(Suc (Suc i)) < |(a # w)|" by (simp add: i_def)
    have t4: "\<not> (shuffling_possible (drop (Suc (Suc i)) (a#w)))"  by (metis drop_Suc_Cons i_def)
    show ?thesis  using t1 t2 t3 t4 by blast
  next
    case False
    then have "\<exists> b ys. (a # w) = (a # b # ys) \<and> is_input b \<and> is_output a"  by (metis Cons.prems list.sel(1,3) self_append_conv2 tl_append2) 
    then obtain b ys where "(a # w) = (a # b # ys) \<and> is_input b \<and> is_output a" by blast
    then have "\<not> shuffling_possible (b#ys)"  using False by blast
    have "is_output ((a # w) ! 0) \<and>
        is_input ((a # w) ! Suc 0) \<and>
        Suc 0 < |(a # w)|"  by (simp add: \<open>a # w = a # b # ys \<and> is_input b \<and> is_output a\<close>)
    then show ?thesis  by (metis Cons_nth_drop_Suc False Suc_lessD drop0 list.inject)
  qed
qed

lemma rightmost_shuffle_concrete: 
  assumes "shuffling_possible v"
  shows "\<exists> xs a b ys. is_output a \<and> is_input b \<and> v = (xs @ a # b # ys) \<and> \<not> (shuffling_possible ys)" 
  using assms
proof (induct v)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case using Cons assms 
  proof (cases "shuffling_possible w")
    case True
    then have "\<exists>xs a b ys. is_output a \<and> is_input b \<and> w = xs \<cdot> a # b # ys" by blast
    then have "\<exists>xs a b ys.
       is_output a \<and>
       is_input b \<and> w = xs \<cdot> a # b # ys \<and> (\<nexists>xs a b ysa. is_output a \<and> is_input b \<and> ys = xs \<cdot> a # b # ysa)" using Cons by blast   
    then obtain xs ys x y where  w_decomp: "is_output x \<and> is_input y \<and> w = xs \<cdot> x # y # ys \<and> \<not> (shuffling_possible ys)" by blast

    have "(a # w) = a # (xs \<cdot> x # y # ys)"   by (simp add: w_decomp)
    then have "is_output x \<and> is_input y \<and> (a#w) = (a#xs) \<cdot> x # y # ys \<and> \<not> (shuffling_possible ys)" 
      using w_decomp by auto
    then show ?thesis by blast
  next
    case False
    then have "\<exists> b ys. (a # w) = (a # b # ys) \<and> is_input b \<and> is_output a"  by (metis Cons.prems list.sel(1,3) self_append_conv2 tl_append2) 
    then obtain b ys where "(a # w) = (a # b # ys) \<and> is_input b \<and> is_output a" by blast
    then have "\<not> shuffling_possible (b#ys)"  using False by blast
    then have "is_output a \<and> is_input b \<and> (a#w) = [] \<cdot> a # b # ys \<and> \<not> (shuffling_possible ys)"  by (metis Cons_eq_appendI \<open>a # w = a # b # ys \<and> is_input b \<and> is_output a\<close> append_self_conv2)
    then show ?thesis by blast
  qed
qed

(*w' is the result of shuffling w once, on the rightmost eligible pair*) 
abbreviation rightmost_shuffle :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
  "rightmost_shuffle w w' \<equiv> (\<exists> xs a b ys. is_output a \<and> is_input b \<and> w = (xs @ a # b # ys) \<and> (\<not> shuffling_possible ys) \<and> w' = (xs @ b # a # ys))"

lemma rightmost_shuffle_is_shuffle:
  assumes "rightmost_shuffle v w" 
  shows "w \<squnion>\<squnion>\<^sub>? v"
  using assms 
proof -
  have  "rightmost_shuffle v w" using assms by simp
  then have "(\<exists> xs a b ys. is_output a \<and> is_input b \<and> v = (xs @ a # b # ys) \<and> (\<not> shuffling_possible ys) \<and> w = (xs @ b # a # ys))" by blast
  then obtain xs a b ys where shuf_decomp: "is_output a \<and> is_input b \<and> v = (xs @ a # b # ys) \<and> (\<not> shuffling_possible ys) \<and> w = (xs @ b # a # ys)" by blast
  have "(xs @ b # a # ys) \<squnion>\<squnion>\<^sub>? (xs @ a # b # ys)"  by (simp add: shuf_decomp shuffled.swap)
  then show ?thesis   by (simp add: shuf_decomp)
qed

lemma rightmost_shuffle_exists_2: 
  assumes "shuffling_possible v"
  shows "\<exists> w. rightmost_shuffle v w"
  using assms
proof -
  have "shuffling_possible v" using assms by blast
  then have "\<exists> xs a b ys. is_output a \<and> is_input b \<and> v = (xs @ a # b # ys) \<and> \<not> (shuffling_possible ys)" using rightmost_shuffle_concrete[of v] by blast
  then obtain xs a b ys where "is_output a \<and> is_input b \<and> v = (xs @ a # b # ys) \<and> (\<not> shuffling_possible ys)" by blast
  then have "rightmost_shuffle v (xs @ b # a # ys)" by blast
  then show "\<exists> w. rightmost_shuffle v w" by blast
qed

lemma fully_shuffled_valid_w_prepend:
  assumes "(w @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs) \<in> L" and "xs = xs\<down>\<^sub>!"
  shows "(w @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs) \<squnion>\<squnion>\<^sub>? (w @ xs @ [?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>])"
  by (meson assms(2) fully_shuffled_w_prepend)

lemma shuffled_keeps_send_order: 
  assumes "shuffled v v'"
  shows "v\<down>\<^sub>! = v'\<down>\<^sub>!"
  using assms
proof (induct )
  case (refl w)
  then show ?case by simp
next
  case (swap a b w xs ys)
  have w_decomp: "w\<down>\<^sub>! = xs\<down>\<^sub>!  \<cdot> [a,b]\<down>\<^sub>!  @ ys\<down>\<^sub>!"  by (simp add: swap.hyps(3))
  have pair_decomp: "[a,b]\<down>\<^sub>! = [b,a]\<down>\<^sub>!"  by (simp add: swap.hyps(2))
  then show ?case  by (simp add: w_decomp)
next
  case (trans w w' w'')
  then show ?case by simp
qed

lemma shuffle_keeps_send_order: 
  assumes "v' \<squnion>\<squnion>\<^sub>? v"
  shows "v\<down>\<^sub>! = v'\<down>\<^sub>!"
  by (simp add: assms shuffled_keeps_send_order)

lemma shuffled_keeps_recv_order: 
  assumes "shuffled v v'"
  shows "v\<down>\<^sub>? = v'\<down>\<^sub>?"
  using assms
proof (induct )
  case (refl w)
  then show ?case by simp
next
  case (swap a b w xs ys)
  have w_decomp: "w\<down>\<^sub>? = xs\<down>\<^sub>?  \<cdot> [a,b]\<down>\<^sub>?  @ ys\<down>\<^sub>?"  by (simp add: swap.hyps(3))
  have pair_decomp: "[a,b]\<down>\<^sub>? = [b,a]\<down>\<^sub>?" by (simp add: swap.hyps(1))
  then show ?case  by (simp add: w_decomp)
next
  case (trans w w' w'')
  then show ?case by simp
qed

lemma shuffle_keeps_recv_order: 
  assumes "v' \<squnion>\<squnion>\<^sub>? v"
  shows "v\<down>\<^sub>? = v'\<down>\<^sub>?"
  by (simp add: assms shuffled_keeps_recv_order)

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

lemma ActionsOverMessages_rev:
  assumes "a \<in> ActionsOverMessages"
  shows "get_message a \<in> Messages" 
  using ActionsOverMessages.simps assms by force

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

lemma run_rev2: 
  assumes "run s0 (w) (xs)" and "w \<noteq> \<epsilon>"
  shows "\<exists> v vs a s1. run s1 v vs \<and> s0 \<midarrow>a\<rightarrow> s1 \<and> w = (a # v) \<and> xs = (s1 # vs)"
  using assms(1,2) run.cases by fastforce

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


(* original run_rev
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

lemma peer_trans_to_message_in_network:
  assumes "(s1, a, s2) \<in> \<R>(p)"
  shows "get_message a \<in> \<M>"
  by (meson CommunicatingAutomaton.ActionsOverMessages_rev CommunicatingAutomaton.action_is_action_over_message
      assms automaton_of_peer)

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


subsection \<open>helpful conclusions about language/ runs / etc. in concrete cases and peer runs\<close>

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

lemma trans_to_edge : 
  assumes "(s1, a, s2) \<in> \<R>(p)"
  shows "get_message a \<in> \<M>"
  by (meson CommunicatingAutomaton.well_formed_transition assms automaton_of_peer)

lemma valid_message_to_valid_act :
  assumes "get_message a \<in> \<M>" 
  shows "\<exists> i p q. i\<^bsup>p\<rightarrow>q\<^esup> \<in> \<M> \<and> (i\<^bsup>p\<rightarrow>q\<^esup>) = get_message a" 
  by (metis assms message.exhaust)

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

lemma trans_to_act_in_lang : 
  fixes p :: "'peer"
  assumes "(\<I> p, a, s2) \<in> \<R>(p)"
  shows "[a] \<in> \<L>(p)"
proof -
  have "CommunicatingAutomaton.run (\<R> p) (\<I> p) [a] [s2]" by (meson CommunicatingAutomaton.run.simps assms automaton_of_peer concat.simps(1))
  then show ?thesis by (meson CommunicatingAutomaton.Traces.intros automaton_of_peer)
qed

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

lemma Lang_last_act_app :
  assumes "(u @ [a]) \<in> \<L>(p)"
  shows "\<exists>s1 s2. s1 \<midarrow>a\<rightarrow>p s2"
  by (meson Lang_app_both assms lang_implies_trans)

lemma Lang_last_act_trans:
  assumes "(u @ [a]) \<in> \<L>(p)"
  shows "\<exists>s1 s2. (s1, a, s2) \<in> \<R> p"
  using Lang_last_act_app assms by auto

lemma act_in_word_has_trans:
  assumes "w \<in> \<L>(p)" and "a \<in> set w"
  shows "\<exists>s1 s2. (s1, a, s2) \<in> \<R> p"
proof -
  have "\<exists> xs ys. (xs @ [a] @ ys) = w" by (metis Cons_eq_appendI append_self_conv2 assms(2) in_set_conv_decomp_first)
  then obtain xs ys where "(xs @ [a] @ ys) = w" by blast
  then have "(xs @ [a] @ ys) \<in> \<L>(p)"  by (simp add: assms(1))
  then have "(xs @ [a]) \<in> \<L>(p)"  by (metis Lang_app append_assoc)
  then show ?thesis  by (simp add: Lang_last_act_trans)
qed


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

lemma sync_run_decompose: 
  assumes "sync_run C0 (u@v) (xc@yc)"
  shows "sync_run C0 u xc \<and> sync_run (last (C0#xc)) v yc"
  using assms
proof (induct C0 "u@v" "xc@yc" arbitrary: u v xc yc)
  case (SREmpty C)
  then show ?case by (simp add: sync_run.SREmpty)
next
  case (SRComposed I0 w ws a Cn)
  then show ?case sorry
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

lemma sync_send_step_to_recv_step: 
  assumes "C1 \<midarrow>\<langle>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>, \<zero>\<rangle>\<rightarrow> C2"
  shows "C1 q \<midarrow>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>q (C2 q)"
  using assms sync_step_output_rev(5) by auto

lemma act_in_sync_word_to_sync_step: 
  assumes "w \<in> \<L>\<^sub>\<zero>" and "a \<in> set w" 
  shows "\<exists> C1 C2. C1 \<midarrow>\<langle>a, \<zero>\<rangle>\<rightarrow> C2"
  sorry

lemma act_in_sync_word_to_matching_peer_steps: 
  assumes "w \<in> \<L>\<^sub>\<zero>" and "(!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>) \<in> set w"
  shows "\<exists>C1 C2. C1 p \<midarrow>!\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>p (C2 p) \<and> C1 q \<midarrow>?\<langle>(i\<^bsup>p\<rightarrow>q\<^esup>)\<rangle>\<rightarrow>q (C2 q)"
  using act_in_sync_word_to_sync_step assms(1,2) sync_send_step_to_recv_step sync_step_output_rev(4)
  by blast

lemma sync_lang_app: 
  assumes "(u @ v) \<in> \<L>\<^sub>\<zero>"
  shows "u \<in> \<L>\<^sub>\<zero>"
  by (metis SyncTraces.simps append.right_neutral assms sync_run_decompose)

lemma sync_lang_sends_app:
  assumes "(u@v)\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>"
  shows "u\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>"
  by (metis assms filter_append sync_lang_app)


lemma sync_run_word_configs_len_eq:
  assumes "sync_run C0 w xc"
  shows "length w = length xc" 
  using assms proof (induct rule: sync_run.induct)
  case (SREmpty C)
  then show ?case by simp
next
  case (SRComposed C0 w xc a C)
  then show ?case by simp
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

subsubsection "mbox step conversions to&from"

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

subsubsection "mbox run"

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

subsubsection "mbox traces"
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

lemma eps_in_mbox_execs: "\<epsilon> \<in> \<T>\<^bsub>None\<^esub>" using MREmpty MboxTraces.intros by blast

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

lemma tree_acyclic_gen: 
  fixes P :: "'peer set"
    and E :: "'peer topology"
  assumes "is_tree P E" and "(p,q) \<in> E" and "E\<langle>\<rightarrow>p\<rangle> = {} \<or> E\<langle>\<rightarrow>p\<rangle> = {x}" and "x \<noteq> y"
  shows "(y,p) \<notin> E"
  using assms(3,4) by fastforce

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

subsubsection "root & node specifications and more tree related lemmas"

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

subsubsection "parent-child relationship in tree"

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

lemma local_parent_to_global:
  assumes "tree_topology" and "\<P>\<^sub>?(p) = {q} \<or> p \<in> \<P>\<^sub>!(q)"
  shows "\<G>\<langle>\<rightarrow>p\<rangle> = {q}"
proof -
  show ?thesis using assms
  proof (cases "\<P>\<^sub>?(p) = {q}")
    case True
    then have "q \<in> \<G>\<langle>\<rightarrow>p\<rangle>" using sends_of_peer_subset_of_predecessors_in_topology by auto
    have "\<not> (is_root p)" using \<open>\<P>\<^sub>? p = {q}\<close> \<open>q \<in> \<G>\<langle>\<rightarrow>p\<rangle>\<close> by blast
    have "card (\<G>\<langle>\<rightarrow>p\<rangle>) \<le> 1" using at_most_one_parent assms by auto
    then have "card (\<G>\<langle>\<rightarrow>p\<rangle>) = 1" by (smt (verit) Collect_cong \<open>q \<in> \<G>\<langle>\<rightarrow>p\<rangle>\<close> edge_on_peers_in_tree(2) empty_Collect_eq empty_iff root_exists assms
          unique_root)
    then show ?thesis by (metis \<open>q \<in> \<G>\<langle>\<rightarrow>p\<rangle>\<close> card_1_singletonE singletonD)
  next
    case False
    then have "p \<in> \<P>\<^sub>!(q)" using assms by auto
    then obtain s1 a s2 where "is_output a" and "get_actor a = q" and "get_object a = p" and "(s1,a,s2) \<in> \<R> q" 
      by (meson CommunicatingAutomaton.SendingToPeers_rev CommunicatingAutomaton.well_formed_transition
          automaton_of_peer)
    then have c1: "q \<in> \<G>\<langle>\<rightarrow>p\<rangle>" by (metis Edges.intros mem_Collect_eq output_message_to_act_both_known trans_to_edge)
    have c2: "card (\<G>\<langle>\<rightarrow>p\<rangle>) \<le> 1" using at_most_one_parent assms by auto
    have c3: "finite (\<G>\<langle>\<rightarrow>p\<rangle>)"  using finite_peers rev_finite_subset by fastforce
    from c3 c1 c2 have "card (\<G>\<langle>\<rightarrow>p\<rangle>) = 1" using assms(1) root_exists unique_root by force
    then show ?thesis by (metis c1 card_1_singletonE singleton_iff)
  qed
qed

lemma parent_child_diff:
  assumes "is_parent_of p q" 
  shows "p \<noteq> q"
proof (rule ccontr)
  assume "\<not> p \<noteq> q" 
  then have "is_parent_of p p" using assms by auto
  then have "is_node p \<and> \<G>\<langle>\<rightarrow>p\<rangle> = {p}" using is_parent_of_rev(2) is_parent_of_rev2(1) by force
  then show "False" by (metis insert_iff mem_Collect_eq tree_acyclic)
qed

lemma child_word_filters_unique_parent:
  assumes "is_parent_of p q" and "w \<in> \<L>(p)"
  shows "(filter (\<lambda>x. get_object x = q) (w\<down>\<^sub>?)) = (w\<down>\<^sub>?)" 
  using assms
proof (induct "length w" arbitrary: w)
  case 0
  then show ?case by simp
next
  case (Suc x)
  then obtain a v where w_def: "w = v @ [a]" and "length v = x"  by (metis length_Suc_conv_rev)
  then have  "v \<in> \<L>(p)"   using Lang_app Suc.prems(2) by blast
  then have "filter (\<lambda>x. get_object x = q) (v\<down>\<^sub>?) = v\<down>\<^sub>?"  using Suc.hyps(1) \<open>|v| = x\<close> assms(1) by blast
  have "(v @ [a]) \<in> \<L> p"  using Suc.prems(2) w_def by auto
  then have "\<exists> s1 s2. (s1, a, s2) \<in> \<R> p"  using Lang_app_both lang_implies_trans by blast
  then obtain s1 s2 where "(s1, a, s2) \<in> \<R> p" by blast
  then have "get_actor a = p"  by (meson CommunicatingAutomaton.well_formed_transition NetworkOfCA.automaton_of_peer
        NetworkOfCA_axioms)
  then show ?case using Suc
  proof (cases "is_input a")
    case True
    then have "[a]\<down>\<^sub>? = [a]" by simp
    then show ?thesis using True
    proof (cases "get_object a = q")
      case True
      have "(w\<down>\<^sub>?) = (v @ [a])\<down>\<^sub>?"  by (simp add: w_def)
      then have "(v @ [a])\<down>\<^sub>? = (v\<down>\<^sub>? ) @ [a]"  using \<open>(a # \<epsilon>)\<down>\<^sub>? = a # \<epsilon>\<close> by force
      then have obj_proj_decomp: "(filter (\<lambda>x. get_object x = q) (w\<down>\<^sub>?)) = (filter (\<lambda>x. get_object x = q) (v\<down>\<^sub>?)) @ (filter (\<lambda>x. get_object x = q) ([a]))" 
        using w_def by force
      then show ?thesis using True \<open>filter (\<lambda>x. get_object x = q) (v\<down>\<^sub>?) = v\<down>\<^sub>?\<close> w_def by fastforce
    next
      case False (* then p has a second parent  \<rightarrow> contradiction*)
      then obtain qq where "get_object a = qq" and "qq \<noteq> q" by simp
      then have "qq \<in> \<G>\<langle>\<rightarrow>p\<rangle>"   by (metis Edges.intros True \<open>get_actor a = p\<close> \<open>s1 \<midarrow>a\<rightarrow>p s2\<close> input_message_to_act_both_known mem_Collect_eq
            trans_to_edge)
      then have "qq \<in> \<P>" by auto
      have "q \<in> \<G>\<langle>\<rightarrow>p\<rangle>"   using assms(1) is_parent_of_rev(2) by auto
      then have "\<G>\<langle>\<rightarrow>p\<rangle> \<noteq> {q}" using \<open>qq \<in> \<G>\<langle>\<rightarrow>p\<rangle>\<close> \<open>qq \<noteq> q\<close> by blast 
      then show ?thesis   using assms(1) is_parent_of_rev(2) by auto
    qed
  next
    case False
    then have "is_output a" by auto
    then have "[a]\<down>\<^sub>? = \<epsilon>" by simp
    then have "(w\<down>\<^sub>?) = (v\<down>\<^sub>?)"  using w_def by fastforce
    then show ?thesis  using \<open>filter (\<lambda>x. get_object x = q) (v\<down>\<^sub>?) = v\<down>\<^sub>?\<close> by presburger
  qed
qed

lemma pair_proj_recv_for_unique_parent:
  assumes "is_parent_of p q" and "w \<in> \<L>(p)"
  shows "(w\<down>\<^sub>?)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = (w\<down>\<^sub>?)"
proof -
  have "((w)\<down>\<^sub>p) = w" using assms(2) w_in_peer_lang_impl_p_actor by auto
  then have "((w\<down>\<^sub>p)\<down>\<^sub>?) = (w\<down>\<^sub>?)" by presburger
  then have "((w\<down>\<^sub>?)\<down>\<^sub>p) = (w\<down>\<^sub>?)" by (metis filter_pair_commutative)
  then have "(w\<down>\<^sub>?)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = (filter (\<lambda>x. get_object x = q) (w\<down>\<^sub>?))"  using pair_proj_to_object_proj by fastforce
  have "(filter (\<lambda>x. get_object x = q) (w\<down>\<^sub>?)) = (w\<down>\<^sub>?)" using assms child_word_filters_unique_parent by auto
  then show ?thesis  using \<open>w\<down>\<^sub>?\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = filter (\<lambda>x. get_object x = q) (w\<down>\<^sub>?)\<close> by presburger
qed


lemma filter_ignore_false_prop: 
  assumes "filter (\<lambda>x. False) w = \<epsilon>"
  shows "filter (\<lambda>x. False \<or> B) w = filter (\<lambda>x. B) w" 
  by (metis assms filter_False filter_True)
  

lemma pair_proj_send_for_unique_parent:
  assumes "is_parent_of p q" and "w \<in> \<L>(q)"
  shows "(w\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = (w\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})"
  sorry

lemma recv_lang_child_pair_proj_subset1: 
  assumes "is_parent_of p q"
  shows "(((\<L>(p))\<downharpoonright>\<^sub>?)) \<subseteq> ((((\<L>(p))\<downharpoonright>\<^sub>?)\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}))"
proof auto
  fix w
  show "w \<in> \<L> p \<Longrightarrow> \<exists>wa. w\<down>\<^sub>? = wa\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} \<and> (\<exists>w. wa = w\<down>\<^sub>? \<and> w \<in> \<L> p)"  by (metis (no_types, lifting) assms pair_proj_recv_for_unique_parent)
qed

(*this shows if the parent child pair are known, the child's language is invariant to pair proj. with itself and parent*)
lemma child_recv_lang_inv_to_proj_with_parent:
  assumes "is_parent_of p q"
  shows "(((\<L>(p))\<downharpoonright>\<^sub>?)) = ((((\<L>(p))\<downharpoonright>\<^sub>?)\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}))"
proof -
  have t1: "(((\<L>(p))\<downharpoonright>\<^sub>?)) \<subseteq> ((((\<L>(p))\<downharpoonright>\<^sub>?)\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}))"   using assms recv_lang_child_pair_proj_subset1 by blast
  have t2: "((((\<L>(p))\<downharpoonright>\<^sub>?)\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})) \<subseteq> (((\<L>(p))\<downharpoonright>\<^sub>?))"  by (smt (z3) Collect_mono_iff filter_recursion mem_Collect_eq t1)
  from t1 t2 show ?thesis by blast
qed

subsubsection "path to root and path related lemmas"

inductive path_to_root :: "'peer \<Rightarrow> 'peer list \<Rightarrow> bool" where
  PTRRoot: "\<lbrakk>is_root p\<rbrakk> \<Longrightarrow> path_to_root p [p]" |
  PTRNode: "\<lbrakk>tree_topology; is_parent_of p q; path_to_root q as; distinct (p # as)\<rbrakk> \<Longrightarrow> path_to_root p (p # as)"

lemma path_to_root_rev:
  assumes "path_to_root p ps" and "ps \<noteq> [p]"
  shows "\<exists>q as. is_parent_of p q \<and> path_to_root q as \<and> ps = (p # as) \<and> distinct (p # as)"
  using assms
  by (meson path_to_root.simps)

lemma path_to_root_rev_empty:
  assumes "path_to_root p ps" and "ps = [p]"
  shows "is_root p"
  by (metis (no_types, lifting) assms(1,2) list.distinct(1) list.inject path_to_root.simps)

definition get_root :: "'peer topology \<Rightarrow> 'peer" where "get_root E = (THE x. is_root x)"

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

lemma peer_on_path_unique:
  assumes "path_to_root p ps"
  shows "distinct ps"
  using assms distinct_singleton path_to_root_rev by fastforce

lemma only_peer_impl_root:
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

lemma leaf_root_or_child: 
  assumes "tree_topology" and "q \<in> \<P> \<and> \<G>\<langle>q\<rightarrow>\<rangle> = {}"
  shows "is_root q \<or> (\<exists>p. is_parent_of q p)" 
  using assms(1) is_parent_of.simps node_defs_eq root_or_node by presburger

lemma finite_set_card_union_with_singleton:
  assumes "finite A" and "a \<in> A" and "card A \<le> 1" 
  shows "A = {a}" 
proof (rule ccontr)
  assume "A \<noteq> {a}"
  have "A \<noteq> {}" using assms(2) by auto
  then show "False" by (metis One_nat_def \<open>A \<noteq> {a}\<close> assms(1,2,3) card_0_eq card_1_singleton_iff less_Suc0 linorder_le_less_linear
        order_antisym_conv singletonD)
qed

lemma tree_impl_finite_sets:
  assumes "tree_topology"
  shows "finite (\<P>)" and "finite (\<G>)" 
proof -
  show "finite (\<P>)" by (simp add: finite_peers)
  show "finite (\<G>)" by (meson UNIV_I finite_peers finite_prod finite_subset subsetI)
qed

lemma leaf_ingoing_edge:
  assumes "tree_topology" and "card (\<P>) \<ge> 2" and "q \<in> \<P> \<and> \<G>\<langle>q\<rightarrow>\<rangle> = {}"
  shows "\<exists>p. \<G>\<langle>\<rightarrow>q\<rangle> = {p}"
  using assms
proof (induct arbitrary: q)
  case (ITRoot p)
  then show ?case by simp
next
  case (ITNode P E x y)
  then show ?case using ITNode
  proof (cases "q \<in> P \<and> E\<langle>q\<rightarrow>\<rangle> = {}")
    case True
    then have IH_q: "2 \<le> card P \<Longrightarrow> q \<in> P \<and> E\<langle>q\<rightarrow>\<rangle> = {} \<Longrightarrow> \<exists>p. E\<langle>\<rightarrow>q\<rangle> = {p}" using ITNode.hyps(2) by presburger
    have "y \<noteq> q" using ITNode.hyps(4) True by auto
    then show ?thesis
    proof (cases "2 \<le> card P")
      case True
      then have "\<exists>p. E\<langle>\<rightarrow>q\<rangle> = {p}" using IH_q ITNode.prems(2) \<open>y \<noteq> q\<close> by auto
      have "insert (x, y) E\<langle>\<rightarrow>q\<rangle> = E\<langle>\<rightarrow>q\<rangle>" using \<open>y \<noteq> q\<close> by blast
      then show ?thesis by (simp add: \<open>\<exists>p. E\<langle>\<rightarrow>q\<rangle> = {p}\<close>)
    next
      case False
      then have "1 \<ge> card P" by simp
      have "q \<in> P" by (simp add: True)
      have "is_tree P E" by (simp add: ITNode.hyps(1))
      then have "finite P \<and> finite E" by (metis UNIV_I finite_peers finite_prod finite_subset subsetI)
      then have "finite P" by blast
      then have cq: "card P = 1" by (metis ITNode.hyps(3) \<open>card P \<le> 1\<close> finite_set_card_union_with_singleton is_singletonI
            is_singleton_altdef)
      then have "card P = 1 \<and> q \<in> P" by (simp add: \<open>q \<in> P\<close>)
      then have "{q} = P" by (metis \<open>card P \<le> 1\<close> \<open>finite P\<close> finite_set_card_union_with_singleton)
      then show ?thesis using ITNode.hyps(3) ITNode.prems(2) by blast
    qed
  next
    case False
    then have "y = q" using ITNode.prems(2) by auto
    then have "E\<langle>\<rightarrow>q\<rangle> = {}" using ITNode.hyps(1,4) edge_on_peers_in_tree(2) by auto
    then have "\<forall>g. (g, q) \<notin> E" by simp
    then have "insert (x, q) E\<langle>\<rightarrow>q\<rangle> = E\<langle>\<rightarrow>q\<rangle> \<union> {x}" by simp
    then have "insert (x, q) E\<langle>\<rightarrow>q\<rangle> = {x}" by (simp add: \<open>E\<langle>\<rightarrow>q\<rangle> = {}\<close>)
    then show ?thesis using \<open>y = q\<close> by auto
  qed
qed

lemma app_path_peer_is_parent_or_root:
  assumes "path_to_root p (xs @ [q] @ ys)" and "xs \<noteq> []"
  shows "is_root q \<or> (\<exists>qq. is_parent_of qq q)"
  using assms
proof (induct p "xs @ [q] @ ys" arbitrary: xs q ys)
  case (PTRRoot p)
  then have "p = q" by (metis (no_types, lifting) Nil_is_append_conv append_eq_Cons_conv list.distinct(1))
  then have "is_root q"  using PTRRoot.hyps(1) by auto
  then show ?case by blast
next
  case (PTRNode x y as)
  then show ?case 
  proof (cases "\<exists>xs ys. as = (xs \<cdot> (q # \<epsilon> \<cdot> ys))")
    case True
    then show ?thesis by (metis Cons_eq_appendI[of q \<epsilon> "q # \<epsilon>" "\<epsilon> \<cdot> _"] PTRNode.hyps(2,3) PTRNode.hyps(4)[of _ q]
          list.inject[of q _ y] path_to_root.cases[of y as] self_append_conv2[of _ \<epsilon>])
  next
    case False
    then have "\<forall>xs ys. as \<noteq> (xs \<cdot> (q # \<epsilon> \<cdot> ys))" by simp
    then have "q \<noteq> x"  by (metis PTRNode.hyps(6) PTRNode.prems append_eq_Cons_conv)
    then have "q \<noteq> y"  by (metis Cons_eq_appendI False PTRNode.hyps(3) eq_Nil_appendI path_to_root_rev)
    then have "\<forall>xs ys. (x#as) \<noteq> (xs \<cdot> (q # \<epsilon> \<cdot> ys))"  by (metis PTRNode.hyps(6) PTRNode.prems \<open>\<forall>xs ys. as \<noteq> xs \<cdot> (q # \<epsilon> \<cdot> ys)\<close> append_eq_Cons_conv)
    then show ?thesis using PTRNode.hyps(6) by auto
  qed
qed

lemma app_path_peer_is_parent_or_root2:
  assumes "path_to_root p ps" and "ps!i = q" and "i < length ps"
  shows "is_root q \<or> is_parent_of q (ps!(Suc i))"
  using assms
proof (induct p ps arbitrary: i q)
  case (PTRRoot p)
  then show ?case  using Suc_length_conv append_self_conv2 by auto
next
  case (PTRNode x y as)
  then show ?case 
  proof (cases "i = 0") 
    case True
    then have "x = q" using PTRNode.prems(1) by auto
    then have "is_parent_of q y" using PTRNode.hyps(2) by auto
    then show ?thesis by (metis PTRNode.hyps(3) True nth_Cons_0 nth_Cons_Suc path_to_root.simps)
  next
    case False
    then have "i \<ge> 1" by auto
    then have "as!(i-1) = q"  using PTRNode.prems(1) by auto
    then have "(i-1) < length as" by (metis One_nat_def PTRNode.prems(2) Suc_pred \<open>1 \<le> i\<close> le_less_Suc_eq length_Cons less_imp_diff_less
          less_numeral_extra(1) linorder_le_less_linear order.strict_trans2)
    then have "is_root q \<or> is_parent_of q (as!i)" by (metis One_nat_def PTRNode.hyps(4) Suc_pred UNIV_def \<open>1 \<le> i\<close> \<open>as ! (i - 1) = q\<close> less_eq_Suc_le
          root_defs_eq)
    then show ?thesis by simp
  qed
qed

lemma path_to_root_of_root_exists:
  assumes "is_root p"
  shows "path_to_root p [p]" 
  using PTRRoot assms by auto

lemma adj_in_path_parent_child:
  assumes "path_to_root p (x # y # ps)"
  shows "\<P>\<^sub>?(x) = {y} \<or> x \<in> \<P>\<^sub>!(y)"
  by (metis assms is_parent_of_rev2(2) neq_Nil_conv path_to_root_first_elem_is_peer
      path_to_root_stepback)

subsubsection "path from root downwards to a node"

lemma path_to_root_downwards:
  assumes "path_to_root q qs" and "is_parent_of p q" 
  shows "path_to_root p (p # qs)" 
  using assms
proof (induct q qs arbitrary: p)
  case (PTRRoot p)
  then show ?case  by (metis (lifting) NetworkOfCA.PTRNode NetworkOfCA_axioms distinct_length_2_or_more
        distinct_singleton empty_iff is_parent_of.simps local_to_global_root path_to_root_of_root_exists
        singletonI)
next
  case (PTRNode x y as)
  then have "path_to_root x (x # as)" by blast
  then have "tree_topology \<and> is_parent_of p x \<and> path_to_root x (x#as)" using PTRNode.hyps(1) PTRNode.prems by auto
  have "p \<noteq> x" by (metis PTRNode.hyps(2,3,5) PTRNode.prems distinct_length_2_or_more is_parent_of_rev(2) path_to_root_rev
        singleton_inject)
  have "distinct (p#x#as)" 
  proof (rule ccontr)
    assume "\<not> distinct (p # x # as)"
    then have "\<not> distinct (p # as)" using PTRNode.hyps(5) \<open>p \<noteq> x\<close> by auto
    then have "\<exists>i. as!i = p \<and> i < length as" by (meson PTRNode.hyps(5) distinct.simps(2) in_set_conv_nth)
    then obtain i where "as!i = p" and "i < length as" by blast
    then show "False"
    proof (cases "last as = p")
      case True
      then have "is_root p"  using PTRNode.hyps(3) path_ends_at_root by auto
      then show ?thesis  using PTRNode.prems is_parent_of_rev(2) local_to_global_root by force
    next
      case False
      then have "path_to_root y as \<and> as!i = p \<and> i < length as" by (simp add: PTRNode.hyps(3) \<open>as ! i = p\<close> \<open>i < |as|\<close>)
      then have "is_root p \<or> is_parent_of p (as!(Suc i))"  using app_path_peer_is_parent_or_root2 by blast
      then have "is_parent_of p (as!(Suc i))" by (metis PTRNode.prems  insert_not_empty is_parent_of.simps is_parent_of_rev2(2))
      then have c1: "is_node p \<and> \<G>\<langle>\<rightarrow>p\<rangle> = {(as!(Suc i))}" using PTRNode.hyps(1) is_parent_of_rev(2) by auto
      have "x \<notin> set as" using PTRNode.hyps(5) by auto 
      have "\<forall>j. j < length as \<longrightarrow> as!j \<noteq> x" using \<open>x \<notin> set as\<close> by auto
      have c3: "(as!(Suc i)) \<noteq> x" by (metis False Suc_lessI \<open>\<forall>j<|as|. as ! j \<noteq> x\<close> \<open>\<not> distinct (p # as)\<close> \<open>as ! i = p\<close> \<open>i < |as|\<close> append1_eq_conv
            append_butlast_last_id distinct_singleton length_Suc_conv_rev nth_append_length)
      have "is_parent_of p x" by (simp add: PTRNode.prems)
      then have c2: "is_node p \<and> \<G>\<langle>\<rightarrow>p\<rangle> = {x}" using PTRNode.hyps(1) is_parent_of_rev(2) by auto
      then show ?thesis using c1 c2 c3 by simp
    qed
  qed
  then show ?case using \<open>is_tree (\<P>) (\<G>) \<and> is_parent_of p x \<and> path_to_root x (x # as)\<close> path_to_root.PTRNode by blast
qed

inductive path_from_root :: "'peer \<Rightarrow> 'peer list \<Rightarrow> bool" where
  PFRRoot: "\<lbrakk>is_root p\<rbrakk> \<Longrightarrow> path_from_root p [p]" |
  PFRNode: "\<lbrakk>tree_topology; is_parent_of p q; path_from_root q as; distinct (as @ [p])\<rbrakk> \<Longrightarrow> path_from_root p (as @ [p])"

lemma path_from_root_rev:
  assumes "path_from_root p ps"
  shows "is_root p \<or> (\<exists>q as. tree_topology \<and> is_parent_of p q \<and> path_from_root q as \<and> distinct (as @ [p]))"
  by (metis assms path_from_root.cases)

lemma path_to_from:
  assumes "path_to_root p ps"
  shows "path_from_root p (rev ps)"
  using assms
proof (induct)
  case (PTRRoot p)
  then show ?case using PFRRoot by force
next
  case (PTRNode p q as)
  then show ?case  using PFRNode PTRNode.hyps(1,2,4,5) by force
qed

lemma path_from_to:
  assumes "path_from_root p ps"
  shows "path_to_root p (rev ps)"
  using assms
proof (induct)
  case (PFRRoot p)
  then show ?case using PTRRoot by force
next
  case (PFRNode p q as)
  then show ?case  using PTRNode PFRNode.hyps(1,2,4,5) by force
qed

lemma paths_eq: 
  shows "(\<exists>ps. path_from_root p ps) = (\<exists>qs. path_to_root p qs)"
  using path_from_to path_to_from by blast

inductive path_from_to :: "'peer \<Rightarrow> 'peer \<Rightarrow> 'peer list \<Rightarrow> bool" where
  path_refl: "\<lbrakk>tree_topology; p \<in> \<P>\<rbrakk> \<Longrightarrow> path_from_to p p [p]" |
  path_step: "\<lbrakk>tree_topology; is_parent_of p q; path_from_to r q as; distinct (as @ [p])\<rbrakk> \<Longrightarrow> path_from_to r p (as @ [p])"

lemma path_from_to_rev:
  assumes "path_from_to r p r2p"
  shows "(r = p) \<or> (\<exists>q qs. path_from_to r q qs \<and> r2p = (qs@[p]) \<and> is_parent_of p q)"
  by (metis assms path_from_to.simps)

lemma path_from_root_2_path_from_to:
  assumes "path_from_root p ps" and "is_root r"
  shows "path_from_to r p ps"
  using assms
proof (induct p ps)
  case (PFRRoot p)
  then have "is_root p" by auto
  then have "\<G>\<langle>\<rightarrow>p\<rangle> = {}" using root_defs_eq by auto
  have "is_root r" using PFRRoot.prems by auto
  then have "\<G>\<langle>\<rightarrow>r\<rangle> = {}" using root_defs_eq by auto
  have "r \<in> \<P>" by simp
  have "p \<in> \<P>" by simp
  have "r = p" 
  proof (rule ccontr)
    assume "r \<noteq> p"
    then have "is_tree (\<P>) (\<G>) \<and> p \<in> \<P> \<and> \<G>\<langle>\<rightarrow>p\<rangle> = {} \<and> r \<noteq> p \<and> r \<in> \<P>"  using PFRRoot.hyps \<open>\<G>\<langle>\<rightarrow>p\<rangle> = {}\<close> by auto
    then have "card (\<G>\<langle>\<rightarrow>r\<rangle>) = 1" using unique_root by blast
    then show "False" by (simp add: \<open>\<G>\<langle>\<rightarrow>r\<rangle> = {}\<close>)
  qed
  then show ?case by (metis NetworkOfCA.path_from_to.simps NetworkOfCA_axioms PFRRoot.prems \<open>p \<in> \<P>\<close>)
next
  case (PFRNode p q as)
  then have "path_from_to r q as" by simp
  then have "tree_topology \<and> is_parent_of p q \<and> path_from_to r q as \<and> distinct (as @ [p])" using PFRNode.hyps(1,2,5) by auto
  then show ?case using path_step by blast
qed

lemma p2root_down_step: 
  "(is_parent_of p q \<and> path_to_root q qs)  \<Longrightarrow> path_to_root p (p#qs)" 
  using path_to_root_downwards by auto

lemma path_to_root_exists: 
  assumes "tree_topology" and "p \<in> \<P>"
  shows "\<exists>ps. path_to_root p ps" 
proof (cases "is_root p")
  case True
  then show ?thesis using PTRRoot by auto
next
  case False
  then have "is_node p" using assms(1) root_or_node by blast
  then have "\<exists> q. is_parent_of p q" by (metis node_defs_eq node_parent)
  then obtain q where "q \<in> \<P>" and "is_parent_of p q" by blast
  then have req1: "tree_topology \<and> is_parent_of p q" by (simp add: assms(1))
  have "\<exists> r. is_root r" using req1 root_exists by blast
  then obtain r where "is_root r" by auto
  then have "path_to_root r [r]" by (simp add: PTRRoot)
  then have "\<exists>ps. path_to_root p (p # q # ps @ [r])" sorry (*by (blast dest: PTRNode)*)
  then show ?thesis by blast
qed

lemma path_to_root_exists2: 
  assumes "tree_topology" and "p \<in> \<P>"
  shows "\<exists>ps. path_to_root p ps" 
  using assms 
proof (induct "card (\<P>)")
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
    then have "\<exists>q. q \<in> \<P> \<and> \<G>\<langle>q\<rightarrow>\<rangle> = {} \<and> is_node q" using assms(1) leaf_exists leaf_ingoing_edge by auto
    then obtain l where "l \<in> \<P> \<and> \<G>\<langle>l\<rightarrow>\<rangle> = {} \<and> is_node l" by auto
    then have "is_node l" by auto
    then have "\<exists>r. r \<in> \<P> \<and> \<G>\<langle>\<rightarrow>l\<rangle> = {r}" using node_defs_eq by auto
    then obtain l_mom where "l_mom \<in> \<P>" and "\<G>\<langle>\<rightarrow>l\<rangle> = {l_mom}" by auto
    then have "is_node l \<and> \<G>\<langle>\<rightarrow>l\<rangle> = {l_mom}" by (simp add: assms(1))
    then have "is_parent_of l l_mom" using node_parent by force
    then have "card (\<P> - {l}) = x" by (metis Suc.hyps(2) UNIV_I card_Diff_singleton_if diff_Suc_1)
    then have "\<exists>a. path_to_root l_mom a" sorry
        (* remove leaf from tree, show use IH, then show that adding leaf keeps the path from IH
    then have "is_node l" 
    then obtain x where "(x, l) \<in> \<G>" *)
    then show ?thesis sorry
  qed 
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

subsection "Influenced Language"

(*fixed: without projection to p and q to the sends of w', the influenced language 
is only correct if each node sends to exactly one child
side note: proj. only needed in w', since by tree topology, each node p has a unique parent, and thus the receives 
in w can already only be between p and q (i.e. the projection can be added for w as well but is unnecessary)*)
inductive is_in_infl_lang :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
  IL_root: "\<lbrakk>is_root r; w \<in> \<L>(r)\<rbrakk> \<Longrightarrow> is_in_infl_lang r w" | \<comment>\<open>influenced language of root r is language of r\<close>
  IL_node: "\<lbrakk>tree_topology; is_parent_of p q; w \<in> \<L>(p); is_in_infl_lang q w'; ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> is_in_infl_lang p w" \<comment>\<open>p is any node and q its parent has a matching send for each of p's receives\<close>

lemma is_in_infl_lang_rev_tree:
  assumes "is_in_infl_lang p w" 
  shows "tree_topology" 
  using assms is_in_infl_lang.simps by blast

lemma is_in_infl_lang_rev_root:
  assumes "is_in_infl_lang p w" and "is_root p" 
  shows "w \<in> \<L>(p)" 
  using assms(1) is_in_infl_lang.simps by blast

lemma is_in_infl_lang_rev_node:
  assumes "is_in_infl_lang p w" and "is_node p" 
  shows "\<exists>q w'. is_parent_of p q \<and> w \<in> \<L>(p) \<and> is_in_infl_lang q w' \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"
  using assms
proof induct
  case (IL_root r w)
  then show ?case  using root_defs_eq by fastforce
next
  case (IL_node p q w w')
  then show ?case by blast
qed 

lemma w_in_infl_lang : "is_in_infl_lang p w \<Longrightarrow>  w \<in> \<L>(p)" using is_in_infl_lang.simps by blast
lemma recv_has_matching_send : "\<lbrakk>\<P>\<^sub>?(p) = {q}; w \<in> \<L>(p); is_in_infl_lang q w'; ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) \<in> ((((\<L>(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!)\<downharpoonright>\<^sub>!\<^sub>?)" 
  using w_in_infl_lang by blast

lemma child_matching_word_impl_in_infl_lang:
  assumes "tree_topology" and "is_parent_of p q" and "w \<in> \<L>(q)" and "is_in_infl_lang q w" and  "((w'\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" and "w' \<in> \<L>(p)"
  shows "is_in_infl_lang p w'"
  using IL_node assms(1,2,4,5,6) by blast

abbreviation InfluencedLanguage :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sup>* _" [90] 100) where
  "\<L>\<^sup>* p \<equiv> {w. is_in_infl_lang p w}"

abbreviation InfluencedLanguageSend :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>!\<^sup>* _" [90] 100) where
  "\<L>\<^sub>!\<^sup>* p \<equiv> (\<L>\<^sup>* p)\<downharpoonright>\<^sub>! "

abbreviation InfluencedLanguageRecv :: "'peer \<Rightarrow> ('information, 'peer) action language"  ("\<L>\<^sub>?\<^sup>* _" [90] 100) where
  "\<L>\<^sub>?\<^sup>* p \<equiv> (\<L>\<^sup>* p)\<downharpoonright>\<^sub>? "

abbreviation ShuffledInfluencedLanguage :: "'peer \<Rightarrow> ('information, 'peer) action language" ("\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion> _" [90] 100) where
  "\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion> p \<equiv> shuffled_lang (\<L>\<^sup>* p)"

lemma is_in_infl_lang_rev2: 
  assumes "w \<in> \<L>\<^sup>* p" and "is_node p"
  shows "w \<in> \<L>(p)" and "\<exists>q w'. is_parent_of p q \<and> w \<in> \<L>(p) \<and> w' \<in> \<L>\<^sup>* q \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"
  using assms
proof -
  show "w \<in> \<L>(p)" using assms(1) is_in_infl_lang.simps by blast
  have "is_in_infl_lang p w \<and> is_node p"  using assms(1,2) by auto
  then have "\<exists>q w'. is_parent_of p q \<and> w \<in> \<L>(p) \<and> is_in_infl_lang q w' \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" using is_in_infl_lang_rev_node by auto
  then show "\<exists>q w'. is_parent_of p q \<and> w \<in> \<L>(p) \<and> w' \<in> \<L>\<^sup>* q \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"  by blast
qed

(*infl_lang only keeps words in the original language that can be built depending on the ancestor's possible sends
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
  have a1: "\<forall>q. ((\<epsilon>\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((\<epsilon>\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"  by simp
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
    then have "is_parent_of p q \<and> \<epsilon> \<in> \<L>(p) \<and> is_in_infl_lang q \<epsilon> \<and> ((\<epsilon>\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((\<epsilon>\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"  by (simp add: PTRNode.hyps(2) PTRNode.prems)
    then show ?case  using IL_node assms(1) by blast
  qed
qed

lemma infl_lang_has_tree_topology:
  assumes "w \<in> \<L>\<^sup>*(p)"
  shows "tree_topology"
  using assms is_in_infl_lang.simps by blast

(* if w is in influenced language of a node p, its parent q must have matching sends for each receive in p*)
lemma infl_parent_child_matching_ws :
  fixes w :: "('information, 'peer) action word"
  assumes "w \<in> \<L>\<^sup>*(p)" and "is_parent_of p q"
  shows "\<exists>w'.  w' \<in> \<L>\<^sup>*(q) \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"
proof -
  have "\<exists>q w'. is_parent_of p q \<and> w \<in> \<L>(p) \<and> w' \<in> \<L>\<^sup>* q \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"  using assms(1,2) is_in_infl_lang_rev2(2) is_parent_of.simps by blast
  then show ?thesis by (metis (mono_tags, lifting) assms(2) is_parent_of_rev(2) mem_Collect_eq singleton_conv)
qed

lemma infl_parent_child_matching_ws2 :
  fixes w :: "('information, 'peer) action word"
  assumes "w \<in> \<L>\<^sup>*(q)" and "is_parent_of p q" and "((w'\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" and "w' \<in> \<L>(p)"
  shows "w' \<in> \<L>\<^sup>*(p)"
  using IL_node assms(1,2,3,4) is_parent_of_rev2(1) by blast

subsubsection "influenced language and its shuffles"

lemma word_in_shuffled_infl_lang :
  fixes w :: "('information, 'peer) action word"
  assumes "w \<in> \<L>\<^sup>*(p)"
  shows "w \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)" 
  by (meson assms shuffle_id)

lemma language_shuffle_subset :
  shows "\<L>\<^sup>*(p) \<subseteq> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)"
  using word_in_shuffled_infl_lang by auto

lemma shuffled_infl_lang_rev :
  assumes "v \<in> \<L>\<^sup>*(p)"
  shows "\<exists>v'. ( v' \<squnion>\<squnion>\<^sub>? v \<and> v' \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p))"
  using assms by (rule CommunicatingAutomata.valid_input_shuffles_of_lang)

lemma shuffled_infl_lang_impl_valid_shuffle :
  assumes "v \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)" 
  shows "\<exists>v'. ( v \<squnion>\<squnion>\<^sub>? v' \<and> v' \<in> \<L>\<^sup>*(p))"
  using assms shuffled_lang_impl_valid_shuffle by auto

value "[!\<langle>x\<rangle>, ?\<langle>y\<rangle>, ?\<langle>z\<rangle>]"
value "let w = [!\<langle>x\<rangle>, ?\<langle>y\<rangle>, ?\<langle>z\<rangle>] in ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)"
value "let w' = [?\<langle>a\<rangle>, !\<langle>y\<rangle>, !\<langle>z\<rangle>] in ((w'\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"

(*can prepend some prefix to a valid shuffle and it's still a valid shuffle*)
lemma shuffle_prepend:
  assumes "y \<squnion>\<squnion>\<^sub>? x" 
  shows "(w \<cdot> y) \<squnion>\<squnion>\<^sub>? (w \<cdot> x)"
  using assms proof (induct x y rule: shuffled.induct)
  case (refl w)
  then show ?case using shuffled.refl by blast
next
  case (swap a b w xs ys)
  then show ?case by (metis append.assoc shuffled.swap)
next
  case (trans w w' w'')
  then show ?case using shuffled.trans by blast
qed

(*can append a suffix to any shuffle and it remains a valid shuffle*)
lemma shuffle_append:
  assumes "y \<squnion>\<squnion>\<^sub>? x" 
  shows "(y \<cdot> w) \<squnion>\<squnion>\<^sub>? (x \<cdot> w)"
  using assms proof (induct x y rule: shuffled.induct)
  case (refl w)
  then show ?case using shuffled.refl by blast
next
  case (swap a b w xs ys)
  then show ?case by (simp add: shuffled.swap)
next
  case (trans w w' w'')
  then show ?case using shuffled.trans by blast
qed


(*any word x can be fully shuffled, i.e. decomposed into its receives xs and its sends ys*)
lemma full_shuffle_of:
  shows "\<exists> xs ys. (xs \<cdot> ys) \<squnion>\<squnion>\<^sub>? x \<and> xs\<down>\<^sub>? = xs \<and> ys\<down>\<^sub>! = ys"
proof (induct x)
  case Nil
  then show ?case by (metis append.right_neutral filter.simps(1) shuffled.refl)
next
  case (Cons a as)
  then obtain xs ys where shuf: "xs \<cdot> ys \<squnion>\<squnion>\<^sub>? as" and xs_def: "xs\<down>\<^sub>? = xs" and ys_def: "ys\<down>\<^sub>! = ys" by blast
  then show ?case proof (cases "is_input a")
    case True
    then have "([a] \<cdot> xs)\<down>\<^sub>? = ([a] \<cdot> xs)" by (simp add: xs_def)
    have new_shuf: "[a] \<cdot> xs \<cdot> ys \<squnion>\<squnion>\<^sub>? ([a] \<cdot> as)" by (simp add: shuf shuffled_prepend_inductive)
    then show ?thesis by (metis \<open>(a # \<epsilon> \<cdot> xs)\<down>\<^sub>? = a # \<epsilon> \<cdot> xs\<close> append_eq_Cons_conv self_append_conv2 ys_def)
  next
    case False
    then have a_ys_def: "([a] \<cdot> ys)\<down>\<^sub>! = ([a] \<cdot> ys)" by (simp add: ys_def)
    have "xs \<cdot> [a]  \<squnion>\<squnion>\<^sub>? ([a] \<cdot> xs)" using fully_shuffled_implies_output_right by (metis False xs_def)
    then have "xs \<cdot> [a] \<cdot> ys \<squnion>\<squnion>\<^sub>? ([a] \<cdot> xs \<cdot> ys)" using shuffle_append by blast
    then have new_shuf: "xs \<cdot> [a] \<cdot> ys \<squnion>\<squnion>\<^sub>? ([a] \<cdot> as)" by (metis (no_types, lifting) append.assoc shuf shuffle_prepend shuffled.trans)
    then show ?thesis using a_ys_def xs_def by fastforce
  qed
qed

(*same as above but directly gives the info that the receives and sends are in fact those of x*)
lemma full_shuffle_of_concrete:
  shows "((x\<down>\<^sub>?) \<cdot> (x\<down>\<^sub>!)) \<squnion>\<squnion>\<^sub>? x"
proof (induct x)
  case Nil
  then show ?case by (metis append.right_neutral filter.simps(1) shuffled.refl)
next
  case (Cons a as)
  then show ?case using Cons proof (cases "is_input a")
    case True
    have "(a # as)\<down>\<^sub>? = ([a]\<down>\<^sub>? \<cdot> as\<down>\<^sub>?)" by simp
    moreover have "[a]\<down>\<^sub>? = [a]"  by (simp add: True)
    then show ?thesis by (metis Cons_eq_appendI filter.simps(1,2) filter_head_helper local.Cons shuffled_prepend_inductive)
  next
    case False
    have "(a # as)\<down>\<^sub>! = ([a]\<down>\<^sub>! \<cdot> as\<down>\<^sub>!)" by simp
    moreover have "[a]\<down>\<^sub>! = [a]"  by (simp add: False)
    moreover have "(a # as)\<down>\<^sub>? = as\<down>\<^sub>?" using False by auto
    moreover have "is_output a" using False by auto
    ultimately show ?thesis  by (metis (mono_tags, lifting) append.right_neutral append_Nil filter_append full_shuffle_of
          input_proj_output_yields_eps output_proj_input_yields_eps shuffled_keeps_recv_order
          shuffled_keeps_send_order)
  qed
qed

(*any word can be shuffled from its origin where all sends are first and all receives come afterwards
lemma shuffle_origin:
  shows "x \<squnion>\<squnion>\<^sub>? ((x\<down>\<^sub>!) \<cdot> (x\<down>\<^sub>?))"
  sorry
*)

(*if an output is all the way on the right, there is no way to remove the send from the right by shuffling alone*)
lemma shuffle_keeps_outputs_right:
  assumes "w' \<squnion>\<squnion>\<^sub>? (w)" and "is_output (last w)" 
  shows "is_output (last w')" 
  using assms CommunicatingAutomata.shuffle_keeps_outputs_right_shuffled by metis



\<comment> \<open>p receives from no one and there is no q that sends to p\<close>
abbreviation no_sends_to_or_recvs_in :: "'peer \<Rightarrow> bool"  where
  "no_sends_to_or_recvs_in p \<equiv> (\<P>\<^sub>?(p) = {} \<and> (\<forall>q. p \<notin> \<P>\<^sub>!(q)))"


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

lemma root_lang_is_mbox:
  assumes "is_root p" and "w \<in> \<L>(p)"
  shows "w \<in> \<T>\<^bsub>None\<^esub>"
  sorry

lemma parent_in_infl_has_matching_sends: 
  assumes "w \<in> \<L>\<^sup>*(p)" and "path_to_root p (p#q#ps)" 
  shows "\<exists>w'. w' \<in> \<L>\<^sup>*(q) \<and> ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"
  using assms(1,2) infl_parent_child_matching_ws path_to_root_first_elem_is_peer path_to_root_stepback
  by blast

lemma send_proj_on_infl_word:
  assumes "v \<in> ((\<L>\<^sub>!\<^sup>*(p)))"
  shows "v = v\<down>\<^sub>!"
  using assms 
proof (induct v)
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  then show ?case by force
qed

lemma v_in_send_infl_to_send_L:
  assumes "v \<in> (\<L>\<^sub>!\<^sup>*(p))"
  shows "v \<in> (\<L>\<^sub>!(p))"
  using assms w_in_infl_lang by (induct, auto)

lemma send_infl_subset_send_lang: "(\<L>\<^sub>!\<^sup>*(p)) \<subseteq> (\<L>\<^sub>!(p))" using v_in_send_infl_to_send_L by blast

lemma pair_proj_comm:  "v\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = v\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>p\<^sub>}" by meson

lemma pair_proj_inv_with_send_proj: 
  assumes "v = v\<down>\<^sub>!"
  shows "(v\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} )= (v\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!"
  using assms
proof (induct v)
  case Nil
  then show ?case using eps_always_in_lang by auto
next
  case (Cons a as)
  then show ?case by (metis (no_types, lifting) filter.simps(2) list.distinct(1) list.inject
        output_proj_input_yields_eps)
qed

lemma send_infl_lang_pair_proj_inv_with_send:
  assumes "v \<in> ((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})"
  shows "v = v\<down>\<^sub>!"
  using assms
proof (induct v )
  case Nil
  then show ?case by simp
next
  case (Cons a as)
  obtain v' where "(a#as) =  (v'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})" and "v' \<in> (\<L>\<^sub>!\<^sup>*(q))" using Cons.prems by blast
  then have "(v') = (v')\<down>\<^sub>!" by force
  then have "(v'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}) = (v'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!" using pair_proj_inv_with_send_proj by fastforce
  then show ?case using \<open>a # as = v'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<close> by presburger
qed

lemma projs_on_peer_eq_if_in_peer_lang:
  assumes "v \<in> ((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})" and "is_parent_of p q"
  shows "v = (v)\<down>\<^sub>q"
proof -
  have "v \<in> ((\<L>\<^sub>!(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})"  using assms(1) w_in_infl_lang by auto
  then have "v \<in> (((\<L>(q))\<downharpoonright>\<^sub>!)\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})" by blast
  have "\<forall>x. (x \<in> (\<L>(q))) \<longrightarrow> (x = (x\<down>\<^sub>q))" by (simp add: w_in_peer_lang_impl_p_actor) 
  then have "\<forall>v'. ((((v')\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}) = v \<and> v' \<in> (\<L>(q))) \<longrightarrow> (v' = (v'\<down>\<^sub>q))" by simp
  then have "\<forall>v'. ((((v')\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}) = v \<and> v' \<in> (\<L>(q))) \<longrightarrow> (((((v')\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})) = (((((v')\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}))\<down>\<^sub>q))"  by (metis (mono_tags, lifting) filter_recursion proj_trio_inv proj_trio_inv2)
  then show ?thesis  using \<open>v \<in> (\<L> q)\<downharpoonright>\<^sub>!\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<close> by blast
qed

(*need to show that since i have all sends and receives of the full word, i just need to split the parent and
child word at appropriate places*)
lemma is_in_infl_lang_app: 
  assumes "is_in_infl_lang p (u @ v)"
  shows "is_in_infl_lang p u"
  using assms 
proof (induct p "(u @ v)" arbitrary: u v)
  case (IL_root r w)
  then show ?case using Lang_app is_in_infl_lang.IL_root by blast
next
  case (IL_node p q w w')
  then have "is_in_infl_lang p (w' \<cdot> v)" using is_in_infl_lang.IL_node by blast 
  then have "w \<in> \<L>\<^sup>*(q) \<and> (((w' \<cdot> v)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"  using IL_node.hyps(4,6) by blast
  then have p_w_match: "(((w' \<cdot> v)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" by blast
  have p_decomp: "(((w' \<cdot> v)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w')\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) @ (((v)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)" by simp
      (*
  have "\<exists>w'' w'''. w = (w'' @ w''') \<and> (((w')\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w''\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?) \<and> (((v)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'''\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" 
    sorry
  then obtain w'' w''' where "w = (w'' @ w''')" and "(((w')\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w''\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" and "(((v)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'''\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" by blast
*)  
  have "\<exists>w'' w'''. w = (w'' @ w''') \<and> (((w')\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w''\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" 
  proof (induct "length w'" arbitrary: w')
    case 0
    then show ?case by fastforce
  next
    case (Suc x)
    then obtain a as where "x = |as|" and "w' = as @ [a]"  by (metis length_Suc_conv_rev)
    then have "\<exists>w'' w'''. w = w'' \<cdot> w''' \<and> as\<down>\<^sub>?\<down>\<^sub>!\<^sub>? = w''\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<down>\<^sub>!\<^sub>?"  using Suc.hyps(1) by presburger
    then obtain w'' w''' where  "w = w'' \<cdot> w'''" and "as\<down>\<^sub>?\<down>\<^sub>!\<^sub>? = w''\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<down>\<^sub>!\<^sub>?" by blast
    then have "is_in_infl_lang q (w'')"  using IL_node.hyps(5) by blast
    then show ?case sorry
  qed

  then obtain w'' w''' where "w = (w'' @ w''')" and "(((w')\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w''\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" by blast

  then have "is_in_infl_lang q w''"  by (meson IL_node.hyps(5))
  have "w' \<in> \<L> p"  using IL_node.hyps(3) Lang_app by blast
  then have "tree_topology \<and>  is_parent_of p q \<and>  w' \<in> \<L>(p) \<and> is_in_infl_lang q w'' \<and> ((w'\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w''\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)"
    using IL_node.hyps(1,2) \<open>is_in_infl_lang q w''\<close> \<open>w'\<down>\<^sub>?\<down>\<^sub>!\<^sub>? = w''\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<down>\<^sub>!\<^sub>?\<close> by blast
  then have "is_in_infl_lang p w'" using is_in_infl_lang.IL_node[of p q w' w''] by blast
  then show ?case by simp
qed

lemma infl_word_impl_prefix_valid: 
  assumes "(u @ v) \<in> \<L>\<^sup>* p"
  shows "u \<in> \<L>\<^sup>* p"
  using assms is_in_infl_lang_app by blast

lemma peer_pair_infl_send_nosymb_comm: "(((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>q\<^sub>,\<^sub>p\<^sub>})\<downharpoonright>\<^sub>!\<^sub>?) = (((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>?)"
proof -
  have "(((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>q\<^sub>,\<^sub>p\<^sub>})) = (((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}))"  by (simp add: pair_proj_comm)
  then show ?thesis by presburger
qed

(*if child action is receive then it must receive from its unique parent*)
lemma child_send_is_from_parent:
  assumes "is_input a" and "is_parent_of p q" and "get_actor a = p" and "(s1, a, s2) \<in> (\<R> p)"
  shows "get_object a = q" 
proof (rule ccontr)
  assume "get_object a \<noteq> q" 
  then obtain qq where "qq \<noteq> q" and "get_object a = qq" and "qq \<in> \<P>"  by simp
  then have "qq \<in> \<P>\<^sub>? p"  by (metis CommunicatingAutomaton.empty_receiving_from_peers assms(1,4) automaton_of_peer) 
  have "card (\<P>\<^sub>? p) \<le> 1"  using \<open>get_object a = qq\<close> \<open>get_object a \<noteq> q\<close> \<open>qq \<in> \<P>\<^sub>? p\<close> assms(2) is_parent_of_rev(2)
      sends_of_peer_subset_of_predecessors_in_topology by fastforce
  then have "\<P>\<^sub>? p = {qq}"   by (meson \<open>qq \<in> \<P>\<^sub>? p\<close> finite_peers finite_set_card_union_with_singleton finite_subset subset_UNIV)
  then show "False" using \<open>\<P>\<^sub>? p = {qq}\<close> \<open>qq \<noteq> q\<close> assms(2) insert_subset is_parent_of_rev(2) sends_of_peer_subset_of_predecessors_in_topology  singleton_iff by metis
qed

lemma infl_word_actor_app:
  assumes "(w @ xs) \<in> (\<L>\<^sup>*(q))"
  shows "(w\<down>\<^sub>q = w) \<and> (xs\<down>\<^sub>q = xs)"
  using assms proof - 
  have "(w @ xs) \<in> (\<L>(q))" using assms w_in_infl_lang by auto
  then have "(w @ xs)\<down>\<^sub>q = (w @ xs)"  using w_in_peer_lang_impl_p_actor by presburger
  then show ?thesis  by (metis actor_proj_app_inv)
qed

subsubsection "simulate sync with mbox word"

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


subsubsection "Lemma 4.4 and preparations"


(*this should do the same thing as concat_infl but more straightforward *)
inductive acc_infl_lang_word :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where
  ACC_root: "\<lbrakk>is_root r; w \<in> \<L>\<^sup>*(r)\<rbrakk> \<Longrightarrow> acc_infl_lang_word r w" | \<comment>\<open>influenced language of root r is language of r\<close>
  ACC_node: "\<lbrakk>tree_topology; is_parent_of p q; w \<in> \<L>\<^sup>*(p); acc_infl_lang_word q w'; ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> acc_infl_lang_word p (w' @ w)" \<comment>\<open>p is any node and q its parent has a matching send for each of p's receives\<close>









(*starts at some node and a full path from that node to root, then walks up to the root while accumulating the word w1....wn*)
inductive concat_infl :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'peer list  \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" for p::"'peer" and w:: "('information, 'peer) action word" where
  at_p: "\<lbrakk>tree_topology; w \<in> \<L>\<^sup>*(p); path_to_root p ps\<rbrakk> \<Longrightarrow> concat_infl p w ps w" | (*start condition*)
  reach_root: "\<lbrakk>is_root q; qw \<in> \<L>\<^sup>*(q); path_to_root x (x # [q]); (\<forall>g. w_acc\<down>\<^sub>g \<in> \<L>\<^sup>*(g));  concat_infl p w (x # [q]) w_acc; (((w_acc\<down>\<^sub>x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((qw\<down>\<^sub>{\<^sub>x\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> concat_infl p w [q] (qw \<cdot> w_acc)" | (*end condition*)
  node_step: "\<lbrakk>tree_topology; \<P>\<^sub>?(x) = {q}; (\<forall>g. w_acc\<down>\<^sub>g \<in> \<L>\<^sup>*(g)); path_to_root x (x # q # ps); qw \<in> \<L>\<^sup>*(q); concat_infl p w (x # q # ps) w_acc; (((w_acc\<down>\<^sub>x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((qw\<down>\<^sub>{\<^sub>x\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)\<rbrakk> \<Longrightarrow> concat_infl p w (q#ps) (qw \<cdot> w_acc)" 

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
  assumes "concat_infl p w ps w_acc" and "is_parent_of q p"
  shows "w_acc\<down>\<^sub>q = \<epsilon>"
    (*to show, simply that p is child of q, so p is not on the path_to_root of p*)
  using assms 
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

(*construct w' s.t. w1....wn is a mbox trace*)
lemma concat_infl_w_in_w_acc:
  assumes "concat_infl p w ps w_acc"
  shows "\<exists> xs. w_acc = xs @ w"
  using assms
proof induct
  case (at_p ps)
  then show ?case by simp
next
  case (reach_root q qw x w_acc)
  then show ?case   by (metis append.assoc)
next
  case (node_step x q w_acc ps qw)
  then show ?case  by (metis append.assoc)
qed

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

lemma lem4_4_alt:
  assumes "\<exists> w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>q = w \<and> ((is_parent_of p q) \<longrightarrow>  w'\<down>\<^sub>p = \<epsilon>)) \<and> (\<exists> xs. (xs @ w) \<in> \<T>\<^bsub>None\<^esub>)"
  shows "\<exists> w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>q = w \<and> (\<forall>g. (is_parent_of g q) \<longrightarrow>  w'\<down>\<^sub>g = \<epsilon>)) \<and> (\<exists> xs. (xs @ w) \<in> \<T>\<^bsub>None\<^esub>)"
  sorry

subsubsection "sync and infl lang relations"

(*
lemma sync_send_to_child_recv:
  assumes "w \<in> \<L>\<^sub>\<zero>" and "(w)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} \<in> ((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})" and "\<forall> a. a \<in> set w \<longrightarrow> (get_actor a = q \<and> get_object a = p)" and "is_parent_of p q" (*i.e. q is parent and sends to p*)
  shows "((w\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>?) \<in> ((\<L>\<^sub>?(p))\<downharpoonright>\<^sub>?)\<downharpoonright>\<^sub>!\<^sub>?" (*for all x in set w . get_actor x  = q *)
  sorry

lemma sync_word_to_sync_steps:
  assumes "w \<in> \<L>\<^sub>\<zero>" 
  shows "\<forall>x. x \<in> (set (w)) \<longrightarrow> (\<exists> C1 C2. C1 \<midarrow>\<langle>x, \<zero>\<rangle>\<rightarrow> C2)"
  sorry
    (*
        have "(set v) \<subseteq> (set (w'\<down>\<^sub>!))"  using w'_def by fastforce
        have w'_act_peers: "\<forall>x. x \<in> set (((w'\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}) \<longrightarrow> (get_actor x = q \<and> get_object x = p)" by auto

        have "\<forall>x. x \<in> (set (w'\<down>\<^sub>!)) \<longrightarrow> (\<exists> C1 C2. C1 \<midarrow>\<langle>x, \<zero>\<rangle>\<rightarrow> C2)"  using sync_word_to_sync_steps w'_sync by presburger
        then have "\<forall>x. x \<in> set v \<longrightarrow> (\<exists> C1 C2. C1 \<midarrow>\<langle>x, \<zero>\<rangle>\<rightarrow> C2)"  using \<open>set v \<subseteq> set (w'\<down>\<^sub>!)\<close> by blast
        then have "\<forall>a. a \<in> set v \<longrightarrow> (\<exists> C1 C2. C1 (get_actor a) \<midarrow>a\<rightarrow>(get_actor a) (C2 (get_actor a)) \<and> (C1 (get_object a) \<midarrow>(?\<langle>(get_message a)\<rangle>)\<rightarrow>(get_object a) (C2 (get_object a))))"  by (metis get_message.simps(1) sync_step_rev(5,6)) 
        
(*since w' is in infl. lang of q, and q sends stuff, and w' is sync word, all sends of w' must be immediately received*)
        
        (* probs need a lemma that shows that if i have some send sequence between two peers in sync lang, then
the send sequence is in the lang of that peer*) *)
*)

(*this one might be unnecessary but the conclusion of the lemma under this is needed*)
lemma subword_of_sync_is_receivable:
  assumes "w'\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>" and "w'\<down>\<^sub>p = \<epsilon>" and "((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} \<in> ((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})" and "is_parent_of p q" and "is_synchronisable" and "tree_topology"
  shows "(((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? \<in> ((\<L>(p))\<downharpoonright>\<^sub>?)\<downharpoonright>\<^sub>!\<^sub>?"
  sorry

lemma subword_of_sync_is_receivable2:
  assumes "w'\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>" and "w'\<down>\<^sub>p = \<epsilon>" and "((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} \<in> ((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})" and "is_parent_of p q" and "(((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? \<in> ((\<L>(p))\<downharpoonright>\<^sub>?)\<downharpoonright>\<^sub>!\<^sub>?"
  shows "(((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? \<in> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?"
  sorry


section "new formalization"

(*all receives possible in Aq, after performing actions in w*)
abbreviation possible_recv_suffixes :: "('information, 'peer) action word \<Rightarrow> 'peer \<Rightarrow>  ('information, 'peer) action language"  ("\<ddagger>_\<ddagger>\<^sub>_" [90, 90] 110) where  
  "\<ddagger>w\<ddagger>\<^sub>p \<equiv> {x\<down>\<^sub>? | x. (w \<cdot> x) \<in> \<L>\<^sup>*(p)}"

(*all possible sends from q to p in Aq, after performing actions in w
if p is not child of q, the set is trivially {\<epsilon>}*)
abbreviation possible_send_suffixes_to_peer :: "'peer \<Rightarrow> ('information, 'peer) action word \<Rightarrow> 'peer \<Rightarrow>  ('information, 'peer) action language"  ("\<^sub>_\<ddagger>_\<ddagger>\<^sub>_" [90, 90, 90] 110) where  
  "\<^sub>q\<ddagger>w\<ddagger>\<^sub>p \<equiv> {(x\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} | x. (w \<cdot> x) \<in> \<L>\<^sup>*(q)}"

(*for all words w in p, for all w' that provide all the sends for the receives in w,
w must be able to receive anything that q might send after performing w'.

(there must be at least one such w' per w, otherwise w is not in the influenced language of p)*)
definition subset_condition :: "'peer \<Rightarrow> 'peer \<Rightarrow> bool"
  where "subset_condition p q \<longleftrightarrow> (\<forall> w \<in> \<L>\<^sup>*(p). \<forall> w' \<in> \<L>\<^sup>*(q).
  (((w'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? = ((w\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)) \<longrightarrow> ((\<^sub>q\<ddagger>w'\<ddagger>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<ddagger>w\<ddagger>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>? ))"

(*for all parent-child pairs, subset condition and shuffled language condition hold*)
definition theorem_rightside :: "bool"
  where "theorem_rightside \<longleftrightarrow> (\<forall>p \<in> \<P>. \<forall>q \<in> \<P>. ((is_parent_of p q) \<longrightarrow> ((subset_condition p q) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) ))"

lemma prefix_mbox_trace_valid:
  assumes "(w@v) \<in> \<L>\<^sub>\<infinity>"
  shows "w \<in> \<L>\<^sub>\<infinity>"
  sorry

lemma mbox_exec_to_peer_act:
  assumes "w \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!" and "(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<in> set w" and "tree_topology" 
  shows "\<exists> s1 s2 . (s1, !\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>, s2) \<in> \<R> q"
  sorry

lemma mbox_exec_to_infl_peer_word:
  assumes "w \<in> \<T>\<^bsub>None\<^esub>"
  shows "w\<down>\<^sub>p \<in> \<L>\<^sup>* p"
  sorry


(*for a given execution, a child's receives need to be a prefix of the parent's sends
i.e. the receives (if present) need to be in the same order as the sends and there can't be any receives
missing in the middle (since buffers are FIFO), otherwise p receives something somewhere that hasn't been sent yet,
or is unreachable as it isn't the first buffer element anymore *)
lemma peer_recvs_in_exec_is_prefix_of_parent_sends:
  assumes "e \<in> \<T>\<^bsub>None\<^esub>" and "is_parent_of p q"
  shows "prefix (((e\<down>\<^sub>p)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) ((((e\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>?)"
  sorry

lemma matching_recvs_word_matches_sends_explicit:
  assumes "e \<in> \<T>\<^bsub>None\<^esub>" and "is_parent_of p q"
  shows "(((e\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? = (((add_matching_recvs (e\<down>\<^sub>!)\<down>\<^sub>?)\<down>\<^sub>p)\<down>\<^sub>!\<^sub>?)" 
  sorry


lemma root_infl_word_no_recvs:
  assumes "is_root p" and "w \<in> \<L>\<^sup>* p"
  shows "w\<down>\<^sub>! = w"
proof (rule ccontr)
  assume "w\<down>\<^sub>! \<noteq> w"
  then have "\<exists>x. x \<in> set w \<and> is_input x"  by (simp add: not_only_sends_impl_recv)
  then obtain x where "x \<in> set w" and "is_input x" by auto
  then show "False" sorry
qed



(*if current exec ends on a send and the corresponding peer's buffer only contains
this send, the matching receive can be appended (if the peer can do it)
! only if all prior sends have already been received! (otherwise the buffer contains something other than the 
last element because of fifo buffers)*)
lemma mbox_exec_recv_append:
  assumes "(w \<cdot> [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]) \<in> \<T>\<^bsub>None\<^esub>" and "w\<down>\<^sub>p \<cdot> [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] \<in> \<L>\<^sup>* p"
and "(((((w)\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>?) = ((((w)\<down>\<^sub>p)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)" and "is_parent_of p q"
  shows "w \<cdot> [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] \<cdot> [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] \<in> \<T>\<^bsub>None\<^esub>" 
  sorry


(*adding or removing signs doesn't matter (if both words consist only of the same sign, here only receives*)
lemma no_sign_recv_prefix_to_sign_inv:
  assumes "prefix (w\<down>\<^sub>!\<^sub>?) (w'\<down>\<^sub>!\<^sub>?)" and "w\<down>\<^sub>? = w" and "w'\<down>\<^sub>? = w'"
  shows "prefix w w'"
  sorry


(*given the matched execution (!a?a!b?b...) and an unrelated child word, 
whose receives are a prefix of that execution's receives of q, find the matching parent prefix 
which gives exactly those sends (must be there since all states are final
and there must be a prefix s.t. exactly only the needed sends are there)*)
lemma match_exec_and_child_prefix_to_parent_match:
  assumes "(((((v')\<down>\<^sub>r)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = ((((v')\<down>\<^sub>q)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)"  and  "prefix (wq\<down>\<^sub>?) (((v')\<down>\<^sub>q)\<down>\<^sub>?)" and "is_parent_of q r" 
and "v' \<in> \<T>\<^bsub>None\<^esub>"
shows "\<exists>wr'. prefix wr' ((v')\<down>\<^sub>r) \<and> (((wr'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = (((wq)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) \<and> wr' \<in> \<L>\<^sup>* r"
  sorry


(*wq recvs match wr' sends exactly, and wr' can perform some suffix x' after wr'
\<rightarrow> by subset condition, wq must also have some suffix x that can receive all sends to q in x'*)
lemma subset_cond_from_child_prefix_and_parent:
  assumes "subset_condition q r" and "wq \<in> \<L>\<^sup>* q" and "wr' \<cdot> x' \<in> \<L>\<^sup>* r" and "(((wr'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = (((wq)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)"
  shows "\<exists>x. (wq \<cdot> x) \<in> \<L>\<^sup>* q \<and> (((wq \<cdot> x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((((wr' \<cdot> x')\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)"
  sorry (*for wr', projection to r can be added but is not necessary since it's implicity there by wr' x' being
in r's language*)


(*can append send to mbox exec if the peer sending it can perform the send
since sending has no requirements other than that the sender can perform it at its current state*)
lemma mbox_exec_app_send:
  assumes "(e\<down>\<^sub>q \<cdot> [a]) \<in> (\<L>\<^sup>*(q))" and "(e) \<in> \<T>\<^bsub>None\<^esub>" and "is_output a"
  shows "(e \<cdot> [a]) \<in> \<T>\<^bsub>None\<^esub>"
  sorry (*maybe instantiate mbox run of v' and then do manual mbox step with a*)

(*for given mbox trace, root word is simply the trace projected to the root
otherwise root would receive something, contradicting that it's the root*)
lemma mbox_trace_to_root_word:
  assumes "(v \<cdot> [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]) \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!" and "is_root q"
  shows "(v\<down>\<^sub>q \<cdot> [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]) \<in> (\<L>\<^sup>*(q))"
  sorry



(*if w cannot shuffle into w', then w != w' and there must be at least one ?y < !x dependency in w,
that is reversed to !x < ?y in w' (x and y do not need to be right next to each other though)*)
lemma no_shuffle_implies_output_input_exists:
  assumes "\<not>(w' \<squnion>\<squnion>\<^sub>? w)" and "w\<down>\<^sub>? = w'\<down>\<^sub>?" and "w\<down>\<^sub>! = w'\<down>\<^sub>!"
  shows "\<exists> xs a ys b zs xs' ys' zs'. is_input a \<and> is_output b \<and> w = (xs @ [a] @ ys @ [b] @ zs) \<and>
w' = (xs' @ [b] @ ys' @ [a] @ zs')"
  sorry 
(*some action pair a and b must have changed positions, since w != w' but both words have the same actions, i.e.
no action gets added or removed, so at least one pair must be swapped, then we can do case distinction:
- a, b both outputs (or both inputs) then the second (or third) assumption is violated
- all a,b in w and w' are always output a, input b \<rightarrow> but then w can shuffle into w'
\<longrightarrow> at least one pair a,b where a is input and b is output must exist, which does the reverse of a regular shuffle
from w to w' (i.e. the input moves right while the output moves left)*)


(*missing receives of some peer word can be appended after the original execution
this is doable, since all sends are already in the buffer of the peer (since the trace includes them and e has
this exact trace)
and all sends get received in FIFO order
in short: q's buffer contains the correct elements for xs to receive, and no other peer can block q from 
performing its receives*)
lemma exec_append_missing_recvs:
  assumes "(((wq \<cdot> xs)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((((v \<cdot> [a])\<down>\<^sub>!)\<down>\<^sub>r)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)"
and "(wq \<cdot> xs) \<in> \<L>\<^sup>* q" and "(v \<cdot> [a]) \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!" and "e \<in> \<T>\<^bsub>None\<^esub>" and "e\<down>\<^sub>q = wq"
and "e\<down>\<^sub>! = (v \<cdot> [a])"
shows "(e \<cdot> xs) \<in> \<T>\<^bsub>None\<^esub>"
  sorry

(*for peer words wq and wq = (v'q !a), if (v'q !a) is NOT a shuffle of wq
\<rightarrow> then either the shuffle is the other way round, or the words cannot be shuffled into each other*)
lemma diff_peer_word_impl_diff_trace:
  assumes "wq\<down>\<^sub>? = (v'\<down>\<^sub>q \<cdot> [a])\<down>\<^sub>?" and "wq\<down>\<^sub>! = (v'\<down>\<^sub>q \<cdot> [a])\<down>\<^sub>!" (*this also follows from the shuffling def.*)
and "\<not>((v'\<down>\<^sub>q \<cdot> [a]) \<squnion>\<squnion>\<^sub>? wq)" and "wq \<noteq> (v'\<down>\<^sub>q \<cdot> [a])"
and "e \<in> \<T>\<^bsub>None\<^esub>" and "e\<down>\<^sub>q = wq" and "v' \<in> \<T>\<^bsub>None\<^esub>" and "(v \<cdot> [a]) \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!" and "v' = (add_matching_recvs v)"
and "v'\<down>\<^sub>q \<in> \<L>\<^sup>* q" and "wq \<in> \<L>\<^sup>* q"
shows "e\<down>\<^sub>! \<noteq> (v'\<cdot> [a])\<down>\<^sub>!" 
  sorry
(*since wq is shuffle of (v'q !a), there is some unique (identify uniquely by number of occurence)
pair !x,?y, s.t. !x < ?y in v'q but ?y < !x in wq (!x is not !a, since !a cannot move left 
by shuffling and is already in the rightmost position of v'q !a)
\<rightarrow> by constr. of v', !x < !y in trace v and thus in trace w as well 
\<rightarrow> since e is valid execution, ?y must be sent before !x is sent and so !y < !x in w 
this then means that both executions do not have the same traces!
(this can then be used in the lemma below, to prove that if wq is shuffle of v'q !a, the assumption that
both e and v' !a have the same trace is violated.
 *)


(*same as before but the simpler case where only one action is appended to the parent word*)
(*if parent can perform one more send, the child must be able to receive it*)
lemma subset_cond_from_child_prefix_and_parent_act:
  assumes "subset_condition q r" and "wq \<in> \<L>\<^sup>* q" and "wr' \<cdot> [!\<langle>(i\<^bsup>r\<rightarrow>q\<^esup>)\<rangle>] \<in> \<L>\<^sup>* r" and "(((wr'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = (((wq)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)"
and "is_parent_of q r" and  "((\<L>\<^sup>*(q)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(q)))" 
  shows "(wq \<cdot> [?\<langle>(i\<^bsup>r\<rightarrow>q\<^esup>)\<rangle>]) \<in> \<L>\<^sup>* q \<and> (((wq \<cdot> [?\<langle>(i\<^bsup>r\<rightarrow>q\<^esup>)\<rangle>])\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((((wr' \<cdot> [!\<langle>(i\<^bsup>r\<rightarrow>q\<^esup>)\<rangle>])\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)"
proof -
  have "\<exists>x. (wq \<cdot> x) \<in> \<L>\<^sup>* q \<and> (((wq \<cdot> x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((((wr' \<cdot> [!\<langle>(i\<^bsup>r\<rightarrow>q\<^esup>)\<rangle>])\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" using 
subset_cond_from_child_prefix_and_parent assms by blast
      then obtain x where wqx_def: "(wq \<cdot> x) \<in> \<L>\<^sup>* q" and wqx_match: "(((wq \<cdot> x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((((wr' \<cdot> [!\<langle>(i\<^bsup>r\<rightarrow>q\<^esup>)\<rangle>])\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" by auto
    (*shuffle x s.t. only the missing receives are added to wq (no extra sends*)
    then obtain xs ys where x_shuf: "(xs \<cdot> ys) \<squnion>\<squnion>\<^sub>? x" and "xs\<down>\<^sub>? = xs" and "ys\<down>\<^sub>! = ys" using full_shuffle_of by blast (*fully shuffle x*)
    then have xsys_recvs: "(((wq \<cdot> (xs \<cdot> ys))\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((((wr' \<cdot> [!\<langle>(i\<^bsup>r\<rightarrow>q\<^esup>)\<rangle>])\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)"
      using shuffled_keeps_recv_order wqx_match by force (*xs ys have the same receives as the x we obtained*) 
    have "(wq \<cdot> xs \<cdot> ys) \<squnion>\<squnion>\<^sub>? (wq \<cdot> x)" using x_shuf shuffle_prepend by auto (*shuffle prepend lemma*)
    then have "wq \<cdot> xs \<cdot> ys \<in> \<L>\<^sup>* q" by (metis assms(6) input_shuffle_implies_shuffled_lang mem_Collect_eq wqx_def)
    then have wqxs_L: "wq \<cdot> xs \<in> \<L>\<^sup>* q" using local.infl_word_impl_prefix_valid by simp
    have "(wq \<cdot> xs)\<down>\<^sub>! = wq\<down>\<^sub>!" by (simp add: \<open>xs\<down>\<^sub>? = xs\<close> input_proj_output_yields_eps)
    have "xs\<down>\<^sub>? = (xs \<cdot> ys)\<down>\<^sub>?" by (simp add: \<open>ys\<down>\<^sub>! = ys\<close> output_proj_input_yields_eps)
    have "(xs \<cdot> ys)\<down>\<^sub>? = (x)\<down>\<^sub>?" using x_shuf by (metis shuffled_keeps_recv_order) (*shuffling keeps receive order*)
    then have "xs\<down>\<^sub>? = (x)\<down>\<^sub>?"  using \<open>xs\<down>\<^sub>? = (xs \<cdot> ys)\<down>\<^sub>?\<close> by presburger
    have "(((wq \<cdot> x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((wq \<cdot> xs)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)"  by (simp add: \<open>xs\<down>\<^sub>? = x\<down>\<^sub>?\<close>)
    then have t0: "((((wr' \<cdot> [!\<langle>(i\<^bsup>r\<rightarrow>q\<^esup>)\<rangle>])\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?) = (((wq \<cdot> xs)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?)"  using wqx_match by presburger
    then have t1: "(wq \<cdot> xs) \<in> \<L>\<^sup>* q \<and> (((wq \<cdot> xs)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = ((((wr' \<cdot> [!\<langle>(i\<^bsup>r\<rightarrow>q\<^esup>)\<rangle>])\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>})\<down>\<^sub>!\<^sub>?)" using wqxs_L by presburger
    have "xs = [?\<langle>(i\<^bsup>r\<rightarrow>q\<^esup>)\<rangle>]" sorry (*since only !a was added, only ?a is needed as receive*)
    then show ?thesis using t0 wqxs_L by argo
  qed



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
    then obtain r where "is_parent_of q r" by (metis False UNIV_I path_to_root.cases path_to_root_exists2)
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
            \<open>(wq \<cdot> xs)\<down>\<^sub>? = (add_matching_recvs v \<cdot> a # \<epsilon>)\<down>\<^sub>q\<down>\<^sub>?\<close> \<open>add_matching_recvs v\<down>\<^sub>q \<cdot> a # \<epsilon> \<noteq> wq \<cdot> xs\<close>
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


lemma matched_mbox_run_to_sync_run :
  assumes "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (add_matching_recvs w) xcm" and "w \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!"
  shows "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xcs"
  sorry 




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

(*for given decomposed child word, decompose matching parent word in the same manner*)
lemma decompose_vq_given_decomposed_vp:
  assumes "vq\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? = v\<down>\<^sub>?\<down>\<^sub>!\<^sub>?" and "v' \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)" and "v' \<squnion>\<squnion>\<^sub>? v" and "v \<in> \<L>\<^sup>*(p)" and "vq \<in> \<L>\<^sup>*(q)" 
and "is_output b" and "is_input a" and "v = xs \<cdot> b # a # ys"
shows "\<exists> as bs. vq\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = (as\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} \<cdot> (!\<langle>get_message a\<rangle>) # bs\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})"
  sorry

(*construction: do mix_pair until k is reached, for k and k+1 instead put vq's send and then both v!k and v!(k+1) and then continue with mix_pair construction*)
inductive mix_shuf :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> bool" where  
  mix_shuf_constr: "\<lbrakk>vq\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? = v\<down>\<^sub>?\<down>\<^sub>!\<^sub>?; v' \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p); v' \<squnion>\<squnion>\<^sub>? v; v \<in> \<L>\<^sup>*(p); vq \<in> \<L>\<^sup>*(q); 
vq = (as \<cdot> a_send # bs); v = xs \<cdot> b # a_recv # ys; get_message a_recv = get_message a_send; is_input a_recv; is_output a_send; is_output b\<rbrakk> 
\<Longrightarrow> mix_shuf vq v v' ((mix_pair as xs []) \<cdot> a_send # b # a_recv # (mix_pair bs ys []))"


(*
fun mix_pair :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('information, 'peer) action word" where
 "mix_pair [] [] acc = acc" |
 "mix_pair (a # w') [] acc = mix_pair w' [] (a # acc)" |
 "mix_pair [] (a # w) acc = mix_pair [] w (a # acc)" |
 "mix_pair (a # w') (b # w) acc  = (if a = !\<langle>get_message b\<rangle>
      then (if b = ?\<langle>get_message a\<rangle> then mix_pair w' w (a # b # acc) else mix_pair (a # w') w (b # acc))
      else mix_pair w' (b # w) (a # acc))"

fun mix_shuf :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> ('information, 'peer) action word" where
 "mix_shuf [] [] i k = []" |
 "mix_shuf (a # vq) v i k = (if i < |v| \<and> k < |v| then 
(if a = !\<langle>get_message (v!i)\<rangle> \<and> (v!i) = ?\<langle>get_message a\<rangle> then a # (v!i) # mix_shuf vq v (Suc i) k else 
(if i = k \<and> (Suc i) < |v| \<and>  a = !\<langle>get_message (v!(Suc i))\<rangle> then [] else []))
 else [])"



 "mix_shuf (a # vq) v i k = a # (mix_shuf vq v i k)" |
 "mix_shuf [] (a # v) k k_recv = a # (mix_shuf [] v k k_recv)" |
 "mix_shuf (a # vq) (b # v) k k_recv = (if a = !\<langle>get_message b\<rangle>
      then (if b = ?\<langle>get_message a\<rangle> then mix_pair w' w (a # b # acc) else mix_pair (a # w') w (b # acc))
      else mix_pair w' (b # w) (a # acc))"


inductive mix_shuf :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word  \<Rightarrow> bool" where
  mix_empty: "mix_shuf [] [] [] []" |
  mix_1: "\<lbrakk>vq\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? = v\<down>\<^sub>?\<down>\<^sub>!\<^sub>?; v' \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p); v' \<squnion>\<squnion>\<^sub>? v; v \<in> \<L>\<^sup>*(p); vq \<in> \<L>\<^sup>*(q)\<rbrakk> \<Longrightarrow> mix_shuf vq v' v acc"
*)

(*construct acc, s.t. each send of vq is directly followed by the matching receive in v
unless 
fun mix_shuf :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> nat \<Rightarrow> ('information, 'peer) action \<Rightarrow> ('information, 'peer) action word" where
 "mix_shuf [] [] k k_recv = []" |
 "mix_shuf (a # vq) [] k k_recv = a # (mix_shuf vq [] k k_recv)" |
 "mix_shuf [] (a # v) k k_recv = a # (mix_shuf [] v k k_recv)" |
 "mix_shuf (a # vq) (b # v) k k_recv = (if a = !\<langle>get_message b\<rangle>
      then (if b = ?\<langle>get_message a\<rangle> then mix_pair w' w (a # b # acc) else mix_pair (a # w') w (b # acc))
      else mix_pair w' (b # w) (a # acc))"
*)
(*mix a triple of w'' whose sends (to p) match receives in w, with w', s.t. w' is shuffle of w
the result consists of a mix of w'' and w, s.t. the sync trace of this mixture results in exactly w'
fun mix_triple :: "('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word \<Rightarrow> ('information, 'peer) action word" where
 "mix_triple [] [] [] acc = acc" |
 "mix_triple w'' w' w acc = undefined"
*)




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
          then have "(w' \<cdot> x') \<in> \<T>\<^bsub>None\<^esub>" sorry (*since q is root and thus w' x' are only sends*)
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
          then obtain r where qr: "is_parent_of q r" by (metis False UNIV_I path_from_root.simps path_to_root_exists2 paths_eq)
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
              then have "vq \<in> \<T>\<^bsub>None\<^esub>" sorry (*since q is root and thus vq are only sends*)
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
              then obtain r where qr: "is_parent_of q r" by (metis False UNIV_I path_from_root.simps path_to_root_exists2 paths_eq)
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



subsection "commented lemmas"


(*may or may not be useful at some point*)


(*
(*show that !a must be immediately receivable*)
lemma subset_condition_alt_concrete_app:
  assumes "w' @ [(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)] \<in> \<L>\<^sup>*(q)" and "w \<in> \<L>\<^sup>*(p)" and "subset_condition p q" 
and  "((w'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? = ((w\<down>\<^sub>?))\<down>\<^sub>!\<^sub>?"
shows "w @ [(?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)] \<in> \<L>\<^sup>*(p)"
  using assms
proof -
  have sub: "subset_condition_alt p q"  by (simp add: assms(3) subset_conds_eq)
  have "((w'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? \<in> ((\<lbrakk>w\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?)" using assms(2,4) by force

  have "(((w' @ [(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)])\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? \<in> ((\<lbrakk>w\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?)" 
  proof (rule ccontr)
    assume "(w' \<cdot> !\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon>)\<down>\<^sub>!\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<down>\<^sub>!\<^sub>? \<notin> ((\<lbrakk>w\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?)"
    then have "(w \<in> \<L>\<^sup>*(p) \<and> ( (w' \<cdot> !\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon>) \<in> \<L>\<^sup>*(q) \<and>  (((w' \<cdot> !\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon>)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? \<notin> ((\<lbrakk>w\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?)))"
      using assms(1,2) by blast
    then have "\<not> (\<forall> w \<in> \<L>\<^sup>*(p). (\<forall> w' \<in> \<L>\<^sup>*(q). ((w'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? \<in> ((\<lbrakk>w\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?)))" by blast
    then have no_sub: "\<not> subset_condition_alt p q" unfolding subset_condition_alt_def by simp
    then show "False" using sub by simp
  qed
  then obtain x where "(w \<cdot> x) \<in> \<L>\<^sup>*(p)" and "(x = x\<down>\<^sub>?)"  by auto
  then have "x = [(?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)]" try 

  then show ?thesis try
qed
*)

(*given some parent word, show that there is a word
lemma subset_condition_for_parent_word:
  assumes "(w \<in> \<L>\<^sup>*(q))" and "is_parent_of p q" and "subset_condition p q" and "w' \<in> \<L>\<^sup>*(p)"
  shows "\<exists>x. (w \<cdot> x) \<in> \<L>\<^sup>*(p) \<and> (x = x\<down>\<^sub>?) \<and> (w\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? = ((w \<cdot> x)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?"
  sorry
 *)

(*shows that add_matching_recvs of a trace results in a word that receives exactly all sends (not arbitrary prefix)*)
(*follows from def./construction of add_matching_recvs of a trace
lemma matching_recvs_word_matches_sends:
  assumes "e \<in> \<T>\<^bsub>None\<^esub>" and "is_parent_of p q"
  shows "(((e\<down>\<^sub>!))\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? = (((add_matching_recvs (e\<down>\<^sub>!)\<down>\<^sub>?)\<down>\<^sub>p)\<down>\<^sub>!\<^sub>?)" (*q sends a to p \<longrightarrow> p receives a*)
proof (induct "(e\<down>\<^sub>!)" arbitrary: e rule: add_matching_recvs.induct)
  case 1
  then show ?case by simp
next
  case (2 a w)
  then obtain t where t_def: "e\<down>\<^sub>! = [a]\<down>\<^sub>! \<cdot> t" by (metis Cons_eq_appendI append_self_conv2 filter_append filter_recursion)
  then show ?case sorry
qed
*)

(* this is true but unnecessary to prove
lemma matching_recvs_word_send_actor_proj_inv:
  assumes "e \<in> \<T>\<^bsub>None\<^esub>" and "is_parent_of q r" and "v' = add_matching_recvs (e\<down>\<^sub>!)"
  shows "((v'\<down>\<^sub>r)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>} = ((v')\<down>\<^sub>!)\<down>\<^sub>{\<^sub>q\<^sub>,\<^sub>r\<^sub>}"
  sorry


lemma match_recv_word_matches_parent_exactly:
assumes "e \<in> \<T>\<^bsub>None\<^esub>" and "is_parent_of p q"
shows "(((add_matching_recvs (e\<down>\<^sub>!)\<down>\<^sub>p)\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((e\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>?)"
  sorry
*)

(*
lemma mbox_trace_impl_root_portion_in_lang:
  assumes "w \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!" and "is_root q"
  shows "w\<down>\<^sub>q \<in> \<L>\<^sup>* q "
  sorry


(*can always send something after any execution (as long as the peer is capable of it),
since in mbox nothing needs to be received*)
lemma mbox_exec_send_append:
  assumes "w \<in> \<T>\<^bsub>None\<^esub>" and "w\<down>\<^sub>q \<cdot> [a] \<in> \<L>\<^sup>* q" and "is_output a"
  shows "w \<cdot> [a] \<in> \<T>\<^bsub>None\<^esub>" 
  sorry
*)

(*
lemma prefix_matching_without_signs_to_with:
  assumes "prefix (w\<down>\<^sub>!\<^sub>?) (w'\<down>\<^sub>!\<^sub>?)" and "w\<down>\<^sub>? = w" and "w'\<down>\<^sub>! = w'" and "prefix w'_pre w'"
  shows "prefix (w\<down>\<^sub>!\<^sub>?) (w'_pre\<down>\<^sub>!\<^sub>?)"
  sorry

lemma prefix_of_full_word_eq_to_previous_prefix:
  assumes "prefix (w\<down>\<^sub>?) (((w')\<down>\<^sub>q)\<down>\<^sub>?)" 
  shows "\<exists>w''. prefix w'' (w') \<and> (w\<down>\<^sub>?) = (((w''\<down>\<^sub>q))\<down>\<^sub>?)"
  sorry
*)

(*
lemma matching_no_sign_and_prefix_to_prefix:
  assumes "(w\<down>\<^sub>!\<^sub>?) = (w'\<down>\<^sub>!\<^sub>?)" and "prefix v w'"
  shows "prefix (v\<down>\<^sub>!\<^sub>?) (w\<down>\<^sub>!\<^sub>?)"
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
  assumes "w\<down>\<^sub>? = w'\<down>\<^sub>? \<and> w\<down>\<^sub>! = w'\<down>\<^sub>!" 
  shows "w \<squnion>\<squnion>\<^sub>? w' \<or> w' \<squnion>\<squnion>\<^sub>? w" 
  using assms sorry
(*the proof boils down to every such w, w' being inbetween ?y0...?yn!x0...!xm and !x0...!xm?y0...?yn
using the transitive shuffled rule
the issue is: how to find out whether w or w' was shuffled less (i.e. is closer to the origin word)
\<rightarrow> maybe count number of shuffles that occurred for both w and w' (that also requires further helper lemmas though)*)
*)


(*for peer words wq and wq' = (v'q !a), if the latter can be shuffled into the former and they are NOT
equal, then their respective executions cannot have the same trace.
lemma diff_peer_word_impl_diff_trace:
  assumes "wq\<down>\<^sub>? = (v'\<down>\<^sub>q \<cdot> [a])\<down>\<^sub>?" and "wq\<down>\<^sub>! = (v'\<down>\<^sub>q \<cdot> [a])\<down>\<^sub>!" (*this also follows from the shuffling def.*)
and "wq \<squnion>\<squnion>\<^sub>? (v'\<down>\<^sub>q \<cdot> [a])" and "wq \<noteq> (v'\<down>\<^sub>q \<cdot> [a])"
and "e \<in> \<T>\<^bsub>None\<^esub>" and "v' \<in> \<T>\<^bsub>None\<^esub>" and "(v \<cdot> [a]) \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!" and "v' = (add_matching_recvs v)"
and "v'\<down>\<^sub>q \<in> \<L>\<^sup>* q" and "wq \<in> \<L>\<^sup>* q"
shows "e\<down>\<^sub>! \<noteq> v'\<down>\<^sub>!" 
  sorry
(*since wq is shuffle of (v'q !a), there is some unique (identify uniquely by number of occurence)
pair !x,?y, s.t. !x < ?y in v'q but ?y < !x in wq (!x is not !a, since !a cannot move left 
by shuffling and is already in the rightmost position of v'q !a)
\<rightarrow> by constr. of v', !x < !y in trace v and thus in trace w as well 
\<rightarrow> since e is valid execution, ?y must be sent before !x is sent and so !y < !x in w 
this then means that both executions do not have the same traces!
(this can then be used in the lemma below, to prove that if wq is shuffle of v'q !a, the assumption that
both e and v' !a have the same trace is violated.
 *)*)









(*
lemma recv_in_mbox_requ_send:
  assumes "(?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<in> set w" and "w \<in> \<T>\<^bsub>None\<^esub>" 
  shows "(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<in> set w"
    (*otherwise there is configuration where the element is not in the buffer but it is taken out*)
    (*might need mboxstep lemma to show that if the step is recv, then the thing is in the buffer (but that should
be there already)*)
(*!warning! if the same send action occurs more than once it isn't sufficient to just have one send of that form,
i.e. this condition is insufficient depending on what it's used for*)
  sorry


WRONG:
lemma sync_mbox_exec_impl:
  assumes "xs @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ zs \<in> \<T>\<^bsub>None\<^esub>" and "is_synchronisable" and "tree_topology"
  shows "xs @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys @ zs \<in> \<T>\<^bsub>None\<^esub>"
  sorry

lemma mbox_word_to_peer_act:
  assumes "(w @ [a]) \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!" and "tree_topology" 
  shows "\<exists> s1 s2. (s1, a, s2) \<in> \<R> q"
  sorry

lemma matched_mbox_run_to_sync_run :
  assumes "mbox_run \<C>\<^sub>\<I>\<^sub>\<mm> None (add_matching_recvs w) xcm" and "w \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!"
  shows "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> w xcs"
  sorry 




theorem another wip of \<Longrightarrow>2. (unnecessarily complicated since we know exactly ONE swap occurred)
 case (swap b a w xs ys) (*exactly one swap occurred*)
            (*obtain vq, matching word of q to v (which provides the exact sends to p needed for v)*)
            then have "\<exists>vq.  vq \<in> \<L>\<^sup>*(q) \<and> ((v\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((vq\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" 
              using infl_parent_child_matching_ws[of v p q] orig_in_L q_parent by blast
            then obtain vq where vq_v_match: "((v\<down>\<^sub>?)\<down>\<^sub>!\<^sub>?) = (((vq\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>!\<^sub>?)" and vq_def: "vq \<in> \<L>\<^sup>* q" by auto
            have lem4_4_prems: "tree_topology \<and> w \<in> \<L>\<^sup>*(p) \<and> p \<in> \<P>" using assms swap.prems by auto
            then show ?case using assms swap vq_v_match vq_def lem4_4_prems
            proof (cases "is_root q")
              case True
              then have "vq \<in> \<T>\<^bsub>None\<^esub>" sorry (*since q is root and thus vq are only sends*)
              (*then mix vq with v (while considering v') as valid mbox execution (works since vq needs
             nothing from any other peer, and vq provides all necessary sends for v)*)
          let ?mix = "mix_triple vq v' v []"
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
          then have "(add_matching_recvs t)\<down>\<^sub>p = v'" sorry
          then have "v' \<in> \<L>\<^sup>* p" using sync_exec mbox_exec_to_infl_peer_word by blast
          then show ?thesis


theorem wip of \<Longrightarrow>2. 
  (* \<Longrightarrow> 2.: prove influenced language is also shuffled language *)
      show "\<L>\<^sup>*(p) = \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)" 
      proof
        (* First inclusion is by definition *)
        show "\<L>\<^sup>*(p) \<subseteq> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)" using language_shuffle_subset by auto
            (* Second inclusion via proof*)
        show "\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p) \<subseteq> \<L>\<^sup>*(p)" 
        proof
          fix v
            (*take arbitrary shuffled word v and show that is in the influenced lang, using (one of its) origin(s) v'*)
          assume "v \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)"
          then obtain v' where v_orig: "v \<squnion>\<squnion>\<^sub>? v'" and orig_in_L: "v' \<in> \<L>\<^sup>*(p)" using shuffled_infl_lang_impl_valid_shuffle by auto
          then show "v \<in> \<L>\<^sup>*(p)" 
          proof (induct v' v)
            case (refl w)
            then show ?case by simp
          next
            case (swap x a w xs ys)
              (*exactly one swap occurred*)
              (*use lemma 4.4 to get execution in mbox*)
            then have "tree_topology \<and> w \<in> \<L>\<^sup>*(p) \<and> p \<in> \<P>" by (simp add: assms)
            then have "\<exists> w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>p = w ) \<and> (\<exists> xs. (xs @ w) = w')" using lemm4_4_extra by blast
            then obtain w' ws' where "w' \<in> \<T>\<^bsub>None\<^esub>" and "w'\<down>\<^sub>p = w" and "(ws' @ w) = w'" by blast
                (*use that by construction, ws' contains !a *)
            have "is_input a \<and> is_parent_of p q" by (simp add: q_parent swap.hyps(2))
            have pw_def: "(xs \<cdot> x # a # ys) \<in> \<L>\<^sup>* p"  using swap.hyps(3) swap.prems by blast
            then have "(xs \<cdot> x # a # ys) \<in> \<L> p" using w_in_infl_lang by auto
            then have "w \<in> \<L>(p) \<and> a \<in> set w" using swap.hyps(3) by auto
            then have  "\<exists>s1 s2. (s1, a, s2) \<in> \<R> p" using act_in_word_has_trans by blast
            then have "get_actor a = p"  using \<open>w \<in> \<L> p \<and> a \<in> set w\<close> \<open>w'\<down>\<^sub>p = w\<close> by force
            have "get_object a = q"  using \<open>\<exists>s1 s2. s1 \<midarrow>a\<rightarrow>p s2\<close> \<open>get_actor a = p\<close> \<open>is_input a \<and> is_parent_of p q\<close> child_send_is_from_parent
              by blast
            have "\<exists>i. a = ?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>" by (metis \<open>get_actor a = p\<close> \<open>get_object a = q\<close> action.exhaust get_actor.simps(2) get_object.simps(2)
                  get_receiver.simps get_sender.simps is_output.simps(1) message.exhaust swap.hyps(2))
            then obtain i where i_def: "get_message a = ((i\<^bsup>q\<rightarrow>p\<^esup>))" and a_def: "a = ?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>" by auto

            have "w'\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>" using \<open>w' \<in> \<T>\<^bsub>None\<^esub>\<close> sync_def by auto
            then have "(ws' @ w)\<down>\<^sub>!  \<in> \<L>\<^sub>\<zero>" using \<open>ws' \<cdot> w = w'\<close> sync_def by blast
            then have "ws'\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>" using sync_lang_sends_app by blast

            have "get_actor (!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) = q" by simp
            have send_not_in_w: "(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<notin> set w" by (metis (mono_tags, lifting) \<open>\<exists>w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>p = w) \<and> (\<exists>xs. xs \<cdot> w = w')\<close>
                  \<open>get_actor (!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) = q\<close> \<open>is_input a \<and> is_parent_of p q\<close> filter_id_conv filter_recursion
                  parent_child_diff)
            show ?case
            proof (cases "(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<in> set ws'")
              case True
                (*since sends of w' are sync word, the word where ?a cannot be blocked by any sends in w
              i.e. when i is sent by q, it must be immediately received in p*)
              then have "\<forall>x. x \<in> (set (ws'\<down>\<^sub>!)) \<longrightarrow> (\<exists> C1 C2. C1 \<midarrow>\<langle>x, \<zero>\<rangle>\<rightarrow> C2)"  using \<open>ws'\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>\<close> act_in_sync_word_to_sync_step by blast
              then have "(\<exists> C1 C2. C1 \<midarrow>\<langle>(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), \<zero>\<rangle>\<rightarrow> C2)" by (simp add: True)
              then obtain C1 C2 where sync_step_i: "C1 \<midarrow>\<langle>(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), \<zero>\<rangle>\<rightarrow> C2" by blast
              then have sync_i_rev: "is_sync_config C1 \<and> is_sync_config C2 \<and> p \<noteq> q \<and> C1 q \<midarrow>(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>q (C2 q) \<and> C1 p \<midarrow>(?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>p (C2 p) \<and> (\<forall>x. x \<notin> {p, q} \<longrightarrow> C1(x) = C2(x))" 
                by (smt (verit, ccfv_SIG) insert_commute sync_send_step_to_recv_step sync_step_output_rev(3,4,6)
                    sync_step_rev(1,2))
              then have recv_step_in_q: "C1 p \<midarrow>(?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>p (C2 p)" by blast
                  (*a is sent before w, so also before the !x*)
              have send_in_ws': "(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<in> set ws' \<and> (!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<notin> set w" by (simp add: True send_not_in_w)
              have w'_decomp2: "w' = (ws' \<cdot> xs) \<cdot> (x # a # ys)"  using \<open>ws' \<cdot> w = w'\<close> swap.hyps(3) by auto

              have "(xs \<cdot> x # a # ys) \<in> \<L>\<^sup>* p" using pw_def by blast  
              then have "((xs @ [x] @ [a]) @ ys) \<in> \<L>\<^sup>* p"  by fastforce
              then have "xs \<cdot> x # a # \<epsilon> \<in> \<L>\<^sup>* p" using infl_word_impl_prefix_valid  by (metis Cons_eq_append_conv)  
                  (*then !x!a in sync traces*)
              have "(ws')\<down>\<^sub>!  @ (w)\<down>\<^sub>!  \<in> \<L>\<^sub>\<zero>"  using \<open>(ws' \<cdot> w)\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>\<close> by auto
              have "(xs \<cdot> x # a # \<epsilon>)\<down>\<^sub>! = ((xs\<down>\<^sub>!) @ [(x)]\<down>\<^sub>! @ [a]\<down>\<^sub>!)" by fastforce
              have "(xs \<cdot> x # a # \<epsilon>)\<down>\<^sub>! = (xs\<down>\<^sub>!) @ [x]" by (simp add: swap.hyps(1,2))
              then have w_trace: "(w)\<down>\<^sub>! = (xs\<down>\<^sub>!) @ [x] @ (ys\<down>\<^sub>!)"  by (metis append.assoc append_Cons append_Nil filter_append swap.hyps(3))
                  (*if ?a!x not in L(p), then !a!x in mbox but not in sync \<rightarrow> contradiction*)
              have trace_equi: "(xs \<cdot> a # x # ys)\<down>\<^sub>! = (xs\<down>\<^sub>!) @ [x] @ (ys\<down>\<^sub>!)" by (metis append.left_neutral append_Cons filter.simps(2) filter_append swap.hyps(2,3) w_trace)

              have "\<exists> as bs. ws' = as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs"  by (metis Cons_eq_appendI True append_self_conv2 in_set_conv_decomp_first)
              then obtain as bs where ws'_decomp: "ws' = as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs" by blast
              then have "(as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs)\<down>\<^sub>!  @ (w)\<down>\<^sub>!  \<in> \<L>\<^sub>\<zero>"  using \<open>ws'\<down>\<^sub>! \<cdot> w\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>\<close> by auto
              then have "(as\<down>\<^sub>! @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs\<down>\<^sub>!)  @ (w)\<down>\<^sub>!  \<in> \<L>\<^sub>\<zero>" using Cons_eq_appendI filter.simps(2) by auto
              then have full_trace: "as\<down>\<^sub>! @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs\<down>\<^sub>! @ (xs\<down>\<^sub>!) @ [x] @ (ys\<down>\<^sub>!)  \<in> \<L>\<^sub>\<zero>"  by (simp add: w_trace)
              have full_exec: "as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs @ xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys = w'" using \<open>ws' \<cdot> w = w'\<close> a_def swap.hyps(3) ws'_decomp by force
              have "(xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys) \<in> \<L>\<^sup>* p"
                using \<open>xs \<cdot> (x # \<epsilon> \<cdot> a # \<epsilon>) \<cdot> ys \<in> \<L>\<^sup>* p\<close> a_def by auto
                  (**)
              have "as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs @ xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys \<in> \<T>\<^bsub>None\<^esub>" using \<open>w' \<in> \<T>\<^bsub>None\<^esub>\<close> full_exec by auto
                  (*since the trace is in sync, we must be able to receive immediately after sending*)
(*
              then have sync_exec: "as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs @ xs @ [x] @ ys \<in> \<T>\<^bsub>None\<^esub>"
                using sync_mbox_exec_impl[of as i q p "bs@xs@[x]" ys]  by (simp add: assms sync_def)
              have "(as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs @ xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys)\<down>\<^sub>p = (xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys)" 
                using \<open>w'\<down>\<^sub>p = w\<close> a_def full_exec swap.hyps(3) by auto
              then have e0: "(as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs @ xs @ [x] @ ys)\<down>\<^sub>p = (as\<down>\<^sub>p @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p @ bs\<down>\<^sub>p @ xs\<down>\<^sub>p @ [x]\<down>\<^sub>p @ ys\<down>\<^sub>p)" by simp
              have e1: "(as\<down>\<^sub>p @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p @ bs\<down>\<^sub>p @ xs\<down>\<^sub>p @ [x]\<down>\<^sub>p @ ys\<down>\<^sub>p) = ([?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p  @ xs\<down>\<^sub>p @ [x]\<down>\<^sub>p @ ys\<down>\<^sub>p)" 
                by (smt (verit) Nil_is_append_conv \<open>w'\<down>\<^sub>p = w\<close> \<open>ws' \<cdot> w = w'\<close> a_def filter_append filter_recursion
                    self_append_conv2 ws'_decomp) 
              have "(xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys)\<down>\<^sub>p = (xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys)"  by (metis
                    \<open>(as \<cdot> (!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<cdot> (bs \<cdot> (xs \<cdot> (x # \<epsilon> \<cdot> (?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<cdot> ys))))))\<down>\<^sub>p = xs \<cdot> (x # \<epsilon> \<cdot> (?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<cdot> ys))\<close>
                    filter_recursion)
              then have indiv_projs: "xs\<down>\<^sub>p = xs \<and> [x]\<down>\<^sub>p = [x] \<and> [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p = [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] \<and> ys\<down>\<^sub>p = ys"  by (metis actors_4_proj_app_inv)
              then have "(xs @ [x] @ ys)\<down>\<^sub>p = (xs @ [x] @ ys)"  by (metis filter_append)
              then have e2: "([?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p @ xs\<down>\<^sub>p @ [x]\<down>\<^sub>p @ ys\<down>\<^sub>p) = ([?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs @ [x] @ ys)"  using indiv_projs by presburger
              then have "(as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs @ xs @ [x] @ ys)\<down>\<^sub>p = ([?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs @ [x] @ ys)"  using e0 e1 by order
                  (*word where ?a is received first must be in p, otherwise no sync trace which would contradict assumption*)
              then have "([?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs @ [x] @ ys) \<in> \<L>\<^sup>* p" using sync_exec by (metis mbox_exec_to_infl_peer_word)
                  (*so, we can have ?a either in the beginning of the word, or after x*)
              then have two_p_words: "([?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs @ [x] @ ys) \<in> \<L>\<^sup>* p \<and> (xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys) \<in> \<L>\<^sup>* p"  using \<open>xs \<cdot> (x # \<epsilon> \<cdot> (?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<cdot> ys)) \<in> \<L>\<^sup>* p\<close> by linarith
                  (*since we are using FIFO buffers, ?a is the first receive that occurs and so xs cannot contain other receives,
                  otherwise xs or bs would need to change from one of the two words to the other
                  e.g. if ?a?b!x, then !a!b..!x must be sent, but ?b!x?a is also a valid execution for this send
                  but then !a!b..?b?a, which cant be because FIFO
                  \<rightarrow> in other words, xs and bs cannot contain further receives from p (for bs this is trivial, for xs the contr. would occur)
                  \<rightarrow> so, xs can only be sends to children of p, and bs can be anything from q *)
*)               
              then show ?thesis sorry
            next
              case False (*then a is received but never sent in w', contradicting that it is valid mbox word*)
              have "set w' = (set ws') \<union> (set w)" using \<open>ws' \<cdot> w = w'\<close> by fastforce
              then have send_notin_w': "(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<notin> set w'"  by (simp add: False send_not_in_w)
              have recv_in_w': "(?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<in> set w'"   using \<open>set w' = set ws' \<union> set w\<close> \<open>w \<in> \<L> p \<and> a \<in> set w\<close> a_def by auto
              then show ?thesis using \<open>w' \<in> \<T>\<^bsub>None\<^esub>\<close> sorry (*recv_in_mbox_requ_send send_notin_w' by auto*)
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
  shows "is_synchronisable \<longleftrightarrow> (\<forall>p q. ((is_parent_of p q) \<longrightarrow> ((subset_condition p q) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) ))" (is "?L \<longleftrightarrow> ?R")
  using assms unfolding subset_condition_def prefix_def NetworkOfCA_def 
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
      show "subset_condition p q"
      proof (rule ccontr)
        assume subset_not_holds: "\<not>(subset_condition p q)"
        then have "\<not>(\<forall> w. (w \<in> \<L>\<^sup>*(p)) \<longrightarrow> ( (((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>?) \<subseteq> ((\<lbrakk>w\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?) ))" by (simp add: subset_condition_def)
        then have "\<exists>w. (w \<in> \<L>\<^sup>*(p)) \<and> \<not>(((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>?) \<subseteq> ((\<lbrakk>w\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?)" by blast
            (*obtain prefix where condition is not satisfied*)
        then obtain pref where pref_in_L: "(pref \<in> \<L>\<^sup>*(p))" and pref_contr: "\<not>(((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>?) \<subseteq> ((\<lbrakk>pref\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?)" by blast
        then have "\<exists>v. v \<in> (((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>?) \<and> v \<notin> ((\<lbrakk>pref\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?)" by blast
            (*v is sequence of outputs that are not received by and or after prefix pref, for any suffix*)
        then have "\<exists>v. v \<in> (((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})) \<and> v\<down>\<^sub>!\<^sub>? \<notin> ((\<lbrakk>pref\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?)" by blast
        then obtain v where v_def: "v \<in> (((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}))" and v_not_recv: "v\<down>\<^sub>!\<^sub>? \<notin> ((\<lbrakk>pref\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?)" by blast
            (* Extract a counterexample trace where p does not have matching inputs for its parent q*)
            (* v is a sequence of sends of q*)
        have "v = v\<down>\<^sub>!" using v_def send_infl_lang_pair_proj_inv_with_send by blast
        have "\<exists>v'. v' \<in> ((\<L>\<^sup>*(q))) \<and> ((v'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}) = v" using v_def by blast
        then obtain full_v where full_v_def: "full_v \<in> ((\<L>\<^sup>*(q)))" and full_v2v: "((full_v\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}) = v" by blast
        then have "tree_topology \<and> full_v \<in> \<L>\<^sup>*(q) \<and> q \<in> \<P>" by (simp add: assms)
        then have "\<exists> w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>q = full_v \<and> ((is_parent_of p q) \<longrightarrow>  w'\<down>\<^sub>p = \<epsilon>))"  using lemma4_4 by blast
        then have e2: "\<exists> w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>q = full_v \<and> ((is_parent_of p q) \<longrightarrow>  w'\<down>\<^sub>p = \<epsilon>) \<and> 
                  ((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = v)" using full_v2v by blast
        then have "\<exists> w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>q = full_v \<and> ((is_parent_of p q) \<longrightarrow>  w'\<down>\<^sub>p = \<epsilon>) \<and> 
                  ((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = ((full_v\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}))" using full_v2v by blast
        then have "\<exists> w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>q = full_v \<and> ((is_parent_of p q) \<longrightarrow>  w'\<down>\<^sub>p = \<epsilon>) \<and> 
                 (w'\<down>\<^sub>q) = full_v)" using full_v2v by blast
        then obtain w' where "w' \<in> \<T>\<^bsub>None\<^esub>" and w'_fullv: "w'\<down>\<^sub>q = full_v" and w'_2: "((is_parent_of p q) \<longrightarrow>  w'\<down>\<^sub>p = \<epsilon>)" and 
          w'_def: "((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = v" using e2 by blast
        then have "(w'\<down>\<^sub>q) = full_v" by blast
        have "(((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}) = (((w'\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})" using  proj_trio_inv[of q p w'] by blast
        have "(v\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}) = v" using \<open>(((w')\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = v\<close> filter_recursion by blast
        have "(((w'\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}) = (((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>q)" using  proj_trio_inv2[of q p w'] by blast
        then have "(((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>q) = v" using \<open>(((w')\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = v\<close> \<open>((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = ((w'\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<close> by presburger
        have "v = v\<down>\<^sub>q" using \<open>((w'\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = ((w'\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!)\<down>\<^sub>q\<close> \<open>(((w')\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = v\<close>
            \<open>((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = ((w'\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<close> by force
        have w'_p_proj: "w'\<down>\<^sub>p = \<epsilon>" using w'_2 by (simp add: \<open>is_parent_of p q\<close>)
        then have "\<forall> x. x \<in> (set (w')) \<longrightarrow> get_actor x \<noteq> p"  by (simp add: filter_empty_conv)
        then have p_no_sends_in_w': "\<forall> x. x \<in> (set (w'\<down>\<^sub>!)) \<longrightarrow> get_actor x \<noteq> p" by auto

        (* Use synchronisability to show trace is also in synchronous system *)
        have "w'\<down>\<^sub>! \<in> \<L>\<^bsub>\<infinity>\<^esub>" using \<open>w' \<in> \<T>\<^bsub>None\<^esub>\<close> by blast
        also have "\<L>\<^bsub>\<infinity>\<^esub> = \<T>\<^sub>\<zero>" using sync_def by simp
        also have "\<T>\<^sub>\<zero> = \<L>\<^sub>\<zero>" by simp
        have w'_sync: "w'\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>" using calculation by auto

        have "((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} \<in> ((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})" using v_def w'_def by blast
        then have "((w'\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} \<in> ((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})"  using \<open>((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} = ((w'\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<close> by argo
        then have "((w'\<down>\<^sub>!)\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} \<in> ((\<L>\<^sub>!(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})" using w_in_infl_lang by auto
        then have "(w'\<down>\<^sub>q)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} \<in> ((\<L>(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})"  using full_v_def w'_fullv w_in_infl_lang by auto
        have "((w'\<down>\<^sub>q))\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} \<in> ((\<L>\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})" using full_v_def w'_fullv by blast

        (* Since w'\<down>\<^sub>p = \<epsilon> and w'\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>, p must be able to receive outputs without sending anything*)
        (*the main point is that v is subset of the sync sends w', but p has no sends in this word, which means that there are no sends needed to receive v in *)
        have "(((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? \<in> ((\<L>(p))\<downharpoonright>\<^sub>?)\<downharpoonright>\<^sub>!\<^sub>?" using subword_of_sync_is_receivable[of w' p q] 
          using \<open>is_parent_of p q\<close> assms sync_def v_def w'_def w'_p_proj w'_sync by fastforce
        then have "v\<down>\<^sub>!\<^sub>? \<in> ((\<L>(p))\<downharpoonright>\<^sub>?)\<downharpoonright>\<^sub>!\<^sub>?" using w'_def by fastforce
        then have "v\<down>\<^sub>!\<^sub>? \<in> (\<L>\<^sub>?(p))\<downharpoonright>\<^sub>!\<^sub>?" by blast
        have in_p: "v\<down>\<^sub>!\<^sub>? \<in> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?" using subword_of_sync_is_receivable2[of w' p q] using \<open>is_parent_of p q\<close> \<open>((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>} \<in> ((\<L>\<^sup>* q)\<downharpoonright>\<^sub>!)\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>}\<close> \<open>(((w'\<down>\<^sub>q)\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? \<in> (\<L> p)\<downharpoonright>\<^sub>?\<downharpoonright>\<^sub>!\<^sub>?\<close> w'_def w'_p_proj
            w'_sync by fastforce
            (* \<rightarrow> contradiction not yet found with new condition, needs to be adjusted/ brought into the syntax of the new condition*)
        show "False" sorry
      qed
        (* \<Longrightarrow> 2.: prove influenced language is also shuffled language *)
      show "\<L>\<^sup>*(p) = \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)" 
      proof
        (* First inclusion is by definition *)
        show "\<L>\<^sup>*(p) \<subseteq> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)" using language_shuffle_subset by auto
            (* Second inclusion via proof*)
        show "\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p) \<subseteq> \<L>\<^sup>*(p)" 
        proof
          fix v
            (*take arbitrary shuffled word v and show that is in the influenced lang, using (one of its) origin(s) v'*)
          assume "v \<in> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)"
          then obtain v' where v_orig: "v \<squnion>\<squnion>\<^sub>? v'" and orig_in_L: "v' \<in> \<L>\<^sup>*(p)" using shuffled_infl_lang_impl_valid_shuffle by auto
          then show "v \<in> \<L>\<^sup>*(p)" 
          proof (induct v' v)
            case (refl w)
            then show ?case by simp
          next
            case (swap x a w xs ys)
              (*exactly one swap occurred*)
              (*use lemma 4.4 to get execution in mbox*)
            then have "tree_topology \<and> w \<in> \<L>\<^sup>*(p) \<and> p \<in> \<P>" by (simp add: assms)
            then have "\<exists> w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>p = w ) \<and> (\<exists> xs. (xs @ w) = w')" using lemm4_4_extra by blast
            then obtain w' ws' where "w' \<in> \<T>\<^bsub>None\<^esub>" and "w'\<down>\<^sub>p = w" and "(ws' @ w) = w'" by blast
                (*use that by construction, ws' contains !a *)
            have "is_input a \<and> is_parent_of p q" by (simp add: q_parent swap.hyps(2))
            have pw_def: "(xs \<cdot> x # a # ys) \<in> \<L>\<^sup>* p"  using swap.hyps(3) swap.prems by blast
            then have "(xs \<cdot> x # a # ys) \<in> \<L> p" using w_in_infl_lang by auto
            then have "w \<in> \<L>(p) \<and> a \<in> set w" using swap.hyps(3) by auto
            then have  "\<exists>s1 s2. (s1, a, s2) \<in> \<R> p" using act_in_word_has_trans by blast
            then have "get_actor a = p"  using \<open>w \<in> \<L> p \<and> a \<in> set w\<close> \<open>w'\<down>\<^sub>p = w\<close> by force
            have "get_object a = q"  using \<open>\<exists>s1 s2. s1 \<midarrow>a\<rightarrow>p s2\<close> \<open>get_actor a = p\<close> \<open>is_input a \<and> is_parent_of p q\<close> child_send_is_from_parent
              by blast
            have "\<exists>i. a = ?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>" by (metis \<open>get_actor a = p\<close> \<open>get_object a = q\<close> action.exhaust get_actor.simps(2) get_object.simps(2)
                  get_receiver.simps get_sender.simps is_output.simps(1) message.exhaust swap.hyps(2))
            then obtain i where i_def: "get_message a = ((i\<^bsup>q\<rightarrow>p\<^esup>))" and a_def: "a = ?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>" by auto

            have "w'\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>" using \<open>w' \<in> \<T>\<^bsub>None\<^esub>\<close> sync_def by auto
            then have "(ws' @ w)\<down>\<^sub>!  \<in> \<L>\<^sub>\<zero>" using \<open>ws' \<cdot> w = w'\<close> sync_def by blast
            then have "ws'\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>" using sync_lang_sends_app by blast

            have "get_actor (!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) = q" by simp
            have send_not_in_w: "(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<notin> set w" by (metis (mono_tags, lifting) \<open>\<exists>w'. (w' \<in> \<T>\<^bsub>None\<^esub> \<and> w'\<down>\<^sub>p = w) \<and> (\<exists>xs. xs \<cdot> w = w')\<close>
                  \<open>get_actor (!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) = q\<close> \<open>is_input a \<and> is_parent_of p q\<close> filter_id_conv filter_recursion
                  parent_child_diff)
            show ?case
            proof (cases "(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<in> set ws'")
              case True
                (*since sends of w' are sync word, the word where ?a cannot be blocked by any sends in w
              i.e. when i is sent by q, it must be immediately received in p*)
              then have "\<forall>x. x \<in> (set (ws'\<down>\<^sub>!)) \<longrightarrow> (\<exists> C1 C2. C1 \<midarrow>\<langle>x, \<zero>\<rangle>\<rightarrow> C2)"  using \<open>ws'\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>\<close> act_in_sync_word_to_sync_step by blast
              then have "(\<exists> C1 C2. C1 \<midarrow>\<langle>(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), \<zero>\<rangle>\<rightarrow> C2)" by (simp add: True)
              then obtain C1 C2 where sync_step_i: "C1 \<midarrow>\<langle>(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), \<zero>\<rangle>\<rightarrow> C2" by blast
              then have sync_i_rev: "is_sync_config C1 \<and> is_sync_config C2 \<and> p \<noteq> q \<and> C1 q \<midarrow>(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>q (C2 q) \<and> C1 p \<midarrow>(?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>p (C2 p) \<and> (\<forall>x. x \<notin> {p, q} \<longrightarrow> C1(x) = C2(x))" 
                by (smt (verit, ccfv_SIG) insert_commute sync_send_step_to_recv_step sync_step_output_rev(3,4,6)
                    sync_step_rev(1,2))
              then have recv_step_in_q: "C1 p \<midarrow>(?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>p (C2 p)" by blast
                  (*a is sent before w, so also before the !x*)
              have send_in_ws': "(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<in> set ws' \<and> (!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<notin> set w" by (simp add: True send_not_in_w)
              have w'_decomp2: "w' = (ws' \<cdot> xs) \<cdot> (x # a # ys)"  using \<open>ws' \<cdot> w = w'\<close> swap.hyps(3) by auto

              have "(xs \<cdot> x # a # ys) \<in> \<L>\<^sup>* p" using pw_def by blast  
              then have "((xs @ [x] @ [a]) @ ys) \<in> \<L>\<^sup>* p"  by fastforce
              then have "xs \<cdot> x # a # \<epsilon> \<in> \<L>\<^sup>* p" using infl_word_impl_prefix_valid  by (metis Cons_eq_append_conv)  
                  (*then !x!a in sync traces*)
              have "(ws')\<down>\<^sub>!  @ (w)\<down>\<^sub>!  \<in> \<L>\<^sub>\<zero>"  using \<open>(ws' \<cdot> w)\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>\<close> by auto
              have "(xs \<cdot> x # a # \<epsilon>)\<down>\<^sub>! = ((xs\<down>\<^sub>!) @ [(x)]\<down>\<^sub>! @ [a]\<down>\<^sub>!)" by fastforce
              have "(xs \<cdot> x # a # \<epsilon>)\<down>\<^sub>! = (xs\<down>\<^sub>!) @ [x]" by (simp add: swap.hyps(1,2))
              then have w_trace: "(w)\<down>\<^sub>! = (xs\<down>\<^sub>!) @ [x] @ (ys\<down>\<^sub>!)"  by (metis append.assoc append_Cons append_Nil filter_append swap.hyps(3))
                  (*if ?a!x not in L(p), then !a!x in mbox but not in sync \<rightarrow> contradiction*)
              have trace_equi: "(xs \<cdot> a # x # ys)\<down>\<^sub>! = (xs\<down>\<^sub>!) @ [x] @ (ys\<down>\<^sub>!)" by (metis append.left_neutral append_Cons filter.simps(2) filter_append swap.hyps(2,3) w_trace)

              have "\<exists> as bs. ws' = as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs"  by (metis Cons_eq_appendI True append_self_conv2 in_set_conv_decomp_first)
              then obtain as bs where ws'_decomp: "ws' = as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs" by blast
              then have "(as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs)\<down>\<^sub>!  @ (w)\<down>\<^sub>!  \<in> \<L>\<^sub>\<zero>"  using \<open>ws'\<down>\<^sub>! \<cdot> w\<down>\<^sub>! \<in> \<L>\<^sub>\<zero>\<close> by auto
              then have "(as\<down>\<^sub>! @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs\<down>\<^sub>!)  @ (w)\<down>\<^sub>!  \<in> \<L>\<^sub>\<zero>" using Cons_eq_appendI filter.simps(2) by auto
              then have full_trace: "as\<down>\<^sub>! @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs\<down>\<^sub>! @ (xs\<down>\<^sub>!) @ [x] @ (ys\<down>\<^sub>!)  \<in> \<L>\<^sub>\<zero>"  by (simp add: w_trace)
              have full_exec: "as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs @ xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys = w'" using \<open>ws' \<cdot> w = w'\<close> a_def swap.hyps(3) ws'_decomp by force
              have "(xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys) \<in> \<L>\<^sup>* p"
                using \<open>xs \<cdot> (x # \<epsilon> \<cdot> a # \<epsilon>) \<cdot> ys \<in> \<L>\<^sup>* p\<close> a_def by auto
                  (**)
              have "as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs @ xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys \<in> \<T>\<^bsub>None\<^esub>" using \<open>w' \<in> \<T>\<^bsub>None\<^esub>\<close> full_exec by auto
                  (*since the trace is in sync, we must be able to receive immediately after sending*)
              then have sync_exec: "as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs @ xs @ [x] @ ys \<in> \<T>\<^bsub>None\<^esub>"
                using sync_mbox_exec_impl[of as i q p "bs@xs@[x]" ys]  by (simp add: assms sync_def)
              have "(as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs @ xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys)\<down>\<^sub>p = (xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys)" 
                using \<open>w'\<down>\<^sub>p = w\<close> a_def full_exec swap.hyps(3) by auto
              then have e0: "(as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs @ xs @ [x] @ ys)\<down>\<^sub>p = (as\<down>\<^sub>p @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p @ bs\<down>\<^sub>p @ xs\<down>\<^sub>p @ [x]\<down>\<^sub>p @ ys\<down>\<^sub>p)" by simp
              have e1: "(as\<down>\<^sub>p @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p @ bs\<down>\<^sub>p @ xs\<down>\<^sub>p @ [x]\<down>\<^sub>p @ ys\<down>\<^sub>p) = ([?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p  @ xs\<down>\<^sub>p @ [x]\<down>\<^sub>p @ ys\<down>\<^sub>p)" 
                by (smt (verit) Nil_is_append_conv \<open>w'\<down>\<^sub>p = w\<close> \<open>ws' \<cdot> w = w'\<close> a_def filter_append filter_recursion
                    self_append_conv2 ws'_decomp) 
              have "(xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys)\<down>\<^sub>p = (xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys)"  by (metis
                    \<open>(as \<cdot> (!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<cdot> (bs \<cdot> (xs \<cdot> (x # \<epsilon> \<cdot> (?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<cdot> ys))))))\<down>\<^sub>p = xs \<cdot> (x # \<epsilon> \<cdot> (?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<cdot> ys))\<close>
                    filter_recursion)
              then have indiv_projs: "xs\<down>\<^sub>p = xs \<and> [x]\<down>\<^sub>p = [x] \<and> [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p = [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] \<and> ys\<down>\<^sub>p = ys"  by (metis actors_4_proj_app_inv)
              then have "(xs @ [x] @ ys)\<down>\<^sub>p = (xs @ [x] @ ys)"  by (metis filter_append)
              then have e2: "([?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>]\<down>\<^sub>p @ xs\<down>\<^sub>p @ [x]\<down>\<^sub>p @ ys\<down>\<^sub>p) = ([?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs @ [x] @ ys)"  using indiv_projs by presburger
              then have "(as @ [!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ bs @ xs @ [x] @ ys)\<down>\<^sub>p = ([?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs @ [x] @ ys)"  using e0 e1 by order
                  (*word where ?a is received first must be in p, otherwise no sync trace which would contradict assumption*)
              then have "([?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs @ [x] @ ys) \<in> \<L>\<^sup>* p" using sync_exec by (metis mbox_exec_to_infl_peer_word)
                  (*so, we can have ?a either in the beginning of the word, or after x*)
              then have two_p_words: "([?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ xs @ [x] @ ys) \<in> \<L>\<^sup>* p \<and> (xs @ [x] @ [?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>] @ ys) \<in> \<L>\<^sup>* p"  using \<open>xs \<cdot> (x # \<epsilon> \<cdot> (?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<cdot> ys)) \<in> \<L>\<^sup>* p\<close> by linarith
                  (*since we are using FIFO buffers, ?a is the first receive that occurs and so xs cannot contain other receives,
                  otherwise xs or bs would need to change from one of the two words to the other
                  e.g. if ?a?b!x, then !a!b..!x must be sent, but ?b!x?a is also a valid execution for this send
                  but then !a!b..?b?a, which cant be because FIFO
                  \<rightarrow> in other words, xs and bs cannot contain further receives from p (for bs this is trivial, for xs the contr. would occur)
                  \<rightarrow> so, xs can only be sends to children of p, and bs can be anything from q *)
                then show ?thesis sorry
            next
              case False (*then a is received but never sent in w', contradicting that it is valid mbox word*)
              have "set w' = (set ws') \<union> (set w)" using \<open>ws' \<cdot> w = w'\<close> by fastforce
              then have send_notin_w': "(!\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<notin> set w'"  by (simp add: False send_not_in_w)
              have recv_in_w': "(?\<langle>(i\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) \<in> set w'"   using \<open>set w' = set ws' \<union> set w\<close> \<open>w \<in> \<L> p \<and> a \<in> set w\<close> a_def by auto
              then show ?thesis using \<open>w' \<in> \<T>\<^bsub>None\<^esub>\<close> recv_in_mbox_requ_send send_notin_w' by auto
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
      then have match_exec: "add_matching_recvs (w\<down>\<^sub>!) \<in> \<T>\<^bsub>None\<^esub>" using mbox_trace_with_matching_recvs_is_mbox_exec[of "(w\<down>\<^sub>!)"] 
        using \<open>\<forall>p q. is_parent_of p q \<longrightarrow> subset_condition p q \<and> \<L>\<^sup>* p = \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion> p\<close> assms by blast
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
*)


subsubsection \<open>Topology is a Forest\<close>

inductive is_forest :: "'peer set \<Rightarrow> 'peer topology \<Rightarrow> bool" where
  IFSingle:  "is_tree P E \<Longrightarrow> is_forest P E" |
  IFAddTree: "\<lbrakk>is_forest P1 E1; is_tree P2 E2; P1 \<inter> P2 = {}\<rbrakk> \<Longrightarrow> is_forest (P1 \<union> P2) (E1 \<union> E2)"

abbreviation forest_topology :: "bool" where
  "forest_topology \<equiv> is_forest (UNIV :: 'peer set) (\<G>)"



section "counterexample stuff"

subsection "second condition fix "

(*the right set of the new subset relation, with !? signs not removed yet
essentially it takes any prefix of p (and thus a valid word in its infl. language) 
and checks if the receives that happend thus far in the prefix
and those that might come afterwards (i.e. in any possible suffix s.t. the concatenated word remains in the lang.)
\<rightarrow> in other words, the set of all possible receives of&after prefix w (including the receives of w)*)
abbreviation possible_recvs_of_peer_prefix :: "('information, 'peer) action word \<Rightarrow> 'peer \<Rightarrow>  ('information, 'peer) action language"  ("\<lbrakk>_\<rbrakk>\<^sub>_" [90, 90] 110) where  
  "\<lbrakk>w\<rbrakk>\<^sub>p \<equiv> {y\<cdot>x | x y. (w \<cdot> x) \<in> \<L>\<^sup>*(p) \<and> (x = x\<down>\<^sub>?) \<and> prefix y (w\<down>\<^sub>?)}"


definition subset_condition1 :: "'peer \<Rightarrow> 'peer \<Rightarrow> bool"
  where "subset_condition1 p q \<longleftrightarrow> (\<forall> w \<in> \<L>\<^sup>*(p). ((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<lbrakk>w\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>? )"

definition subset_condition1_alt :: "'peer \<Rightarrow> 'peer \<Rightarrow> bool"
  where "subset_condition1_alt p q \<longleftrightarrow> (\<forall> w \<in> \<L>\<^sup>*(p). (\<forall> w' \<in> \<L>\<^sup>*(q). ((w'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? \<in> ((\<lbrakk>w\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?)))"

lemma subset_cond1_parent_infl_lang: 
  assumes "((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<lbrakk>w\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?"
  shows "(\<forall> w' \<in> \<L>\<^sup>*(q). ((w'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? \<in> ((\<lbrakk>w\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?))"
  by (smt (z3) Collect_mono_iff assms mem_Collect_eq)

lemma subset_conds1_eq:
  shows "subset_condition1_alt p q \<longleftrightarrow> subset_condition1 p q" 
  sorry


lemma subset_condition1_alt_concrete:
  assumes "w' \<in> \<L>\<^sup>*(q)" and "w \<in> \<L>\<^sup>*(p)" and  "subset_condition1 p q" 
  shows "((w'\<down>\<^sub>!)\<down>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<down>\<^sub>!\<^sub>? \<in> ((\<lbrakk>w\<rbrakk>\<^sub>p)\<downharpoonright>\<^sub>!\<^sub>?)"
proof -
  have "subset_condition1_alt p q" by (simp add: assms(3) subset_conds1_eq)
  then show ?thesis using assms(1,2) subset_condition1_alt_def by force
qed

definition theorem_rightside2 :: "bool"
  where "theorem_rightside2 \<longleftrightarrow> (\<forall>p \<in> \<P>. \<forall>q \<in> \<P>. ((is_parent_of p q) \<longrightarrow> ((subset_condition1 p q) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) ))"

lemma shuffled_lang_cond_for_node:
  assumes "(\<forall>p q. ((is_parent_of p q) \<longrightarrow> ((subset_condition1 p q) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) ))"
  shows "(\<forall>p \<in> \<P>. ((is_node p) \<longrightarrow> (((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) ))"
  by (metis UNIV_I assms node_parent path_from_root.simps path_to_root_exists2 paths_eq root_defs_eq)


subsection "counterexample to original theorem"


lemma
  assumes Aq: "\<A> q = ({q0, q1}, q0, {(q0, (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), q1)})" and "is_root q" 
and Lq: "\<L> q = {\<epsilon>, [(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)]}" 
and " q0 \<noteq> q1 "
shows "\<L> q \<subseteq> \<L>\<^sup>* q"
  using assms(2) lang_subset_infl_lang by blast

lemma CE1_trace: 
 assumes Ap: "\<A> p = ({p0, p1}, p0, {(p0, (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), p1), (p0, (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), p1)})"
and Aq: "\<A> q = ({q0, q1}, q0, {(q0, (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), q1)})"
and Ax: "\<A> x = ({x0, x1}, x0, {(x0, (?\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), x1)})"
and Ms: "\<M> = {(a\<^bsup>q\<rightarrow>p\<^esup>), (b\<^bsup>p\<rightarrow>x\<^esup>)}"
and Ps: "\<P> = {p,q,x}"
  and G: "\<G> = {(q,p), (p,x)}" 
and peers_diff: "q \<noteq> x \<and> x \<noteq> p \<and> q \<noteq> p"
and states_diff: "p0 \<noteq> p1 \<and> q0 \<noteq> q1 \<and> x0 \<noteq> x1"
shows "[(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)] \<in> \<T>\<^bsub>None\<^esub>" 
  using assms 
proof - 
  have "(q0, (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), q1) \<in> \<R> q"  using Aq by auto 
  then have "q0 \<midarrow>(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>q q1" by simp
  then have step1: "mbox_step (\<C>\<^sub>\<I>\<^sub>\<mm>) (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>) None (((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))"
    by (metis (no_types, lifting) Ap Aq fst_conv initial_configuration_is_mailbox_configuration self_append_conv2
        send_trans_to_mbox_step snd_conv)
  have s0: "p0 \<midarrow>(!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)\<rightarrow>p p1" by (simp add: Ap)
  have s1: "is_mbox_config (((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))" using \<open>(\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)) \<midarrow>\<langle>!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>, \<infinity>\<rangle>\<rightarrow> (\<lambda>p. (\<C>\<^sub>\<I>\<^sub>\<zero> p, \<epsilon>)) (q := (q1, \<epsilon>), p := (p0, a\<^bsup>q\<rightarrow>p\<^esup> # \<epsilon>))\<close>
      mbox_step_rev(2) by auto 
  have "(\<C>\<^sub>\<I>\<^sub>\<mm>) x = (x0, \<epsilon>)" using Ax by auto 
  then have s2: "(((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)]))) x = (x0, \<epsilon>)"  using peers_diff by force

  have "fst ((((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)]))) p) = p0 \<and> fst (((((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p1, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))(x:= (x0, [b\<^bsup>p\<rightarrow>x\<^esup>]))) p) = p1" 
    using peers_diff by auto
  then have s3: "let C1 = (((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)]))); C2 = ((((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p1, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))(x:= (x0, [b\<^bsup>p\<rightarrow>x\<^esup>]))) 
in fst (C1 p) \<midarrow>(!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)\<rightarrow>p (fst (C2 p))"
    using s0 by fastforce
  have s4: "let C1 = (((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)]))); C2 = ((((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p1, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))(x:= (x0, [b\<^bsup>p\<rightarrow>x\<^esup>]))) 
in snd (C1 p) = snd (C2 p) " 
    using peers_diff by force
  have C2_1: "((((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p1, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))(x:= (x0, [b\<^bsup>p\<rightarrow>x\<^esup>]))) x = (x0, [(b\<^bsup>p\<rightarrow>x\<^esup>)])" by simp
  have C2_2: "(((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)]))) x = (x0, \<epsilon>)" using s2 by metis 
  then have C2_buf: "let C1 = (((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)]))); C2 = ((((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p1, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))(x:= (x0, [b\<^bsup>p\<rightarrow>x\<^esup>])))
in C2 x = (fst (C1 x), (snd (C1 x)) \<cdot> [(b\<^bsup>p\<rightarrow>x\<^esup>)])"
    by simp

  have "let C1 = (((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)]))); C2 = ((((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p1, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))(x:= (x0, [b\<^bsup>p\<rightarrow>x\<^esup>])))
in (\<forall>y. y \<notin> {p, x} \<longrightarrow> C1(y) = C2(y))" by simp

  then have "let C1 = (((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)]))); C2 = ((((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p1, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))(x:= (x0, [b\<^bsup>p\<rightarrow>x\<^esup>])))
in
is_mbox_config C1 \<and> fst (C1 p) \<midarrow>(!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)\<rightarrow>p (fst (C2 p)) \<and>
            snd (C1 p) = snd (C2 p) \<and> ( | (snd (C1 q)) | ) <\<^sub>\<B> None \<and>
            C2 x = (fst (C1 x), (snd (C1 x)) \<cdot> [(b\<^bsup>p\<rightarrow>x\<^esup>)]) \<and>  (\<forall>y. y \<notin> {p, x} \<longrightarrow> C1(y) = C2(y))"
    using s0 s1 s2 s3 s4 C2_buf by simp
    then have step2: "mbox_step (((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))  (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>) None
((((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p1, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))(x:= (x0, [b\<^bsup>p\<rightarrow>x\<^esup>])))"  by (meson gen_send_step_to_mbox_step)
    from step1 have "let C1 = (((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)]))) in
mbox_run (\<C>\<^sub>\<I>\<^sub>\<mm>) None [(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)] ([C1])" by (simp add: mbox_step_to_run)
    then have "let C1 = (((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)]))); C2 = ((((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p1, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))(x:= (x0, [b\<^bsup>p\<rightarrow>x\<^esup>])))
in mbox_run (\<C>\<^sub>\<I>\<^sub>\<mm>) None [(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)] ([C1]) \<and> last ((\<C>\<^sub>\<I>\<^sub>\<mm>)#[C1]) \<midarrow>\<langle>(!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), \<infinity>\<rangle>\<rightarrow> C2"
      using step2 by auto 
    then have "let C1 = (((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p0, [(a\<^bsup>q\<rightarrow>p\<^esup>)]))); C2 = ((((\<C>\<^sub>\<I>\<^sub>\<mm>)(q:= (q1, \<epsilon>)))(p:= (p1, [(a\<^bsup>q\<rightarrow>p\<^esup>)])))(x:= (x0, [b\<^bsup>p\<rightarrow>x\<^esup>])))
in mbox_run (\<C>\<^sub>\<I>\<^sub>\<mm>) None [(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)] ([C1] @ [C2])" using MRComposedInf 
      by (smt (verit, ccfv_threshold) append_Cons append_self_conv2)

    then show "[(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)] \<in> \<T>\<^bsub>None\<^esub>" using MboxTraces.intros by auto
  qed

lemma CE1_not_sync: 
 assumes Ap: "\<A> p = ({p0, p1}, p0, {(p0, (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), p1), (p0, (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), p1)})"
and Aq: "\<A> q = ({q0, q1}, q0, {(q0, (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), q1)})"
and Ax: "\<A> x = ({x0, x1}, x0, {(x0, (?\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), x1)})"
and Ms: "\<M> = {(a\<^bsup>q\<rightarrow>p\<^esup>), (b\<^bsup>p\<rightarrow>x\<^esup>)}"
and Ps: "\<P> = {p,q,x}"
  and G: "\<G> = {(q,p), (p,x)}" 
and peers_diff: "q \<noteq> x \<and> x \<noteq> p \<and> q \<noteq> p"
and states_diff: "p0 \<noteq> p1 \<and> q0 \<noteq> q1 \<and> x0 \<noteq> x1"
shows "[(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)] \<notin> \<L>\<^sub>\<zero>"
proof (rule ccontr)
  assume "\<not> !\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # !\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle> # \<epsilon> \<notin> \<L>\<^sub>\<zero>" 
  then have "[(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)] \<in> \<L>\<^sub>\<zero>" by simp
  then have "[(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)] \<in> \<L>\<^sub>\<zero>" by (metis append_Cons append_Nil sync_lang_app)
  have "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> [(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)] [((\<C>\<^sub>\<I>\<^sub>\<zero>)(q:= q1))(p:= p1)]" by (metis Nil_is_append_conv SyncTraces_rev \<open>!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # \<epsilon> \<in> \<L>\<^sub>\<zero>\<close> append.right_neutral not_Cons_self2
        sync_run.cases sync_run_decompose)
  have s2_rule: "\<forall> s2. (\<C>\<^sub>\<I>\<^sub>\<zero> p) \<midarrow>(?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>p s2 \<longrightarrow> s2 = p1"
  proof (rule ccontr)
    assume "\<not> (\<forall>s2. \<C>\<^sub>\<I>\<^sub>\<zero> p \<midarrow>(?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>p s2 \<longrightarrow> s2 = p1)" 
    then obtain s2 where s2_step: "\<C>\<^sub>\<I>\<^sub>\<zero> p \<midarrow>(?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>p s2" and "p1 \<noteq> s2" and "s2 \<in> {p0, p1}" by (simp add: Ap)
    then have "s2 = p0" by simp
    then have "\<C>\<^sub>\<I>\<^sub>\<zero> p \<midarrow>(?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>p p0" using s2_step by simp
    then have t1: "p0 \<midarrow>(?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)\<rightarrow>p p0" by (simp add: Ap)
    have "(p0, (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), p0) \<notin> \<R> p" using states_diff Ap by simp
    then show "False" using t1 by simp
  qed

  obtain yc C where "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> [(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)] (yc@[C])"  by (metis SyncTraces_rev \<open>!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle> # !\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle> # \<epsilon> \<in> \<L>\<^sub>\<zero>\<close> list.discI sync_run.cases)
  then  have run_decomp: "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> [(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)] yc \<and> last (\<C>\<^sub>\<I>\<^sub>\<zero>#yc) \<midarrow>\<langle>(!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), \<zero>\<rangle>\<rightarrow> C" 
    by (metis Nil_is_append_conv append.right_neutral not_Cons_self2 sync_run.simps sync_run_decompose)
  then have "length (yc) = 1" using sync_run_word_configs_len_eq[of "\<C>\<^sub>\<I>\<^sub>\<zero>" "[(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)]" yc] by simp
  then obtain C1 where "length (yc) = 1" and C1_prop: "yc = [C1]" by (metis One_nat_def Suc_length_conv length_0_conv)
  have "sync_run \<C>\<^sub>\<I>\<^sub>\<zero> [(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>)] [C1]" using C1_prop run_decomp by auto 
  then have "\<C>\<^sub>\<I>\<^sub>\<zero> \<midarrow>\<langle>(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), \<zero>\<rangle>\<rightarrow> C1" using sync_run.cases by fastforce
  then have "C1 p = p1" by (meson s2_rule sync_send_step_to_recv_step)
  have "last (\<C>\<^sub>\<I>\<^sub>\<zero>#yc) = last (\<C>\<^sub>\<I>\<^sub>\<zero>#[C1])" by (simp add: C1_prop)
  then have "last (\<C>\<^sub>\<I>\<^sub>\<zero>#yc) = C1" by simp
  then have "C1 \<midarrow>\<langle>(!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), \<zero>\<rangle>\<rightarrow> C" using run_decomp by simp
  then have  "p1 \<midarrow>(!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)\<rightarrow>p (C p)"  using \<open>C1 p = p1\<close> sync_step_output_rev(4) by blast
  then show "False" using Ap states_diff by auto
qed

lemma only_one_trans_in_Ap_to_p_lang:
  assumes "\<I> q = q0" and "\<R> q = {(q0, a, q1)}" and "q0 \<noteq> q1"
  shows "\<L> q = {\<epsilon>, [a]}"
  using assms 
proof - 
  have  "\<epsilon> \<in> \<L> q" by (meson CommunicatingAutomaton.REmpty2 CommunicatingAutomaton.Traces.simps automaton_of_peer)
  have "q0 \<midarrow>a\<rightarrow>q q1" by (simp add: assms(2))
  then have "[a] \<in> \<L> q" using trans_to_act_in_lang  using assms(1) by auto
  then have ea: "{\<epsilon>, [a]} \<subseteq> \<L> q" by (simp add: \<open>\<epsilon> \<in> \<L> q\<close>)
  have ea2: "\<L> q \<subseteq> {\<epsilon>, [a]}"
  proof (rule ccontr)
    assume "\<not> \<L> q \<subseteq> {\<epsilon>, a # \<epsilon>}" 
    then obtain w where w_def1: "w \<in> \<L> q" and we: "w \<noteq> \<epsilon>" and wa: "w \<noteq> [a]" by auto 
    then show "False" using assms wa we proof (induct w) 
      case Nil
      then show ?case by simp
    next
      case (Cons x v)
      then have "\<exists>s2 s3. (\<I> q) \<midarrow>[x]\<rightarrow>\<^sup>*q s2 \<and> s2 \<midarrow>v\<rightarrow>\<^sup>*q s3" by (metis lang_implies_prepend_run last_ConsL)
      then have "\<exists>s2 s3. (\<I> q) \<midarrow>x\<rightarrow>q s2 \<and> s2 \<midarrow>v\<rightarrow>\<^sup>*q s3" using lang_implies_trans by blast
      then obtain s2 s3 where "(\<I> q) \<midarrow>x\<rightarrow>q s2" and "s2 \<midarrow>v\<rightarrow>\<^sup>*q s3" by blast
      then have "s2 = q1"  by (simp add: assms(2))
      then have v_run: "q1 \<midarrow>v\<rightarrow>\<^sup>*q s3"  using \<open>s2 = s3 \<and> v = \<epsilon> \<and> s2 \<in> \<S> q \<or> (\<exists>xs. run_of_peer_from_state q s2 v xs \<and> last xs = s3)\<close> by auto
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
          then have "(q0, x, s2) \<in> \<R> q" 
            using \<open>\<C>\<^sub>\<I>\<^sub>\<zero> q \<midarrow>x\<rightarrow>q s2\<close> assms(1) by auto
          then show ?thesis  using False assms(2) by auto
        qed
      next
        case (Cons y ys)

        then have "q1 \<midarrow>([y]@ys)\<rightarrow>\<^sup>*q s3"  using v_run by auto
        then have "(\<exists>xs. CommunicatingAutomaton.run (\<R> q) q1 ([y]@ys) xs \<and> last xs = s3)" by simp
        then obtain xs where "CommunicatingAutomaton.run (\<R> q) q1 ([y]@ys) xs" and "last xs = s3" by auto

        then have "CommunicatingAutomaton.run (\<R> q) q1 ([y]@ys) xs \<and> [y] \<noteq> \<epsilon>" by auto
        then have "\<exists>us vs. CommunicatingAutomaton.run (\<R> q) q1 [y] us \<and> CommunicatingAutomaton.run (\<R> q) (last us) ys vs \<and> xs = us @ vs" 
using CommunicatingAutomaton.run_app[of q "\<S> q" q0 "\<M>" "(\<R> q)" q1 "[y]" ys xs] using assms(1) automaton_of_peer by blast
  then obtain us where "CommunicatingAutomaton.run (\<R> q) q1 [y] us" by blast
  then obtain sy where "q1 \<midarrow>y\<rightarrow>q sy"  by (meson lang_implies_trans)
  then show ?thesis using assms(2,3) by force
qed
qed
qed
  show ?thesis using ea ea2 by auto
qed

        


lemma CE1_infl_langs: 
 assumes Ap: "\<A> p = ({p0, p1}, p0, {(p0, (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), p1), (p0, (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), p1)})"
and Aq: "\<A> q = ({q0, q1}, q0, {(q0, (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), q1)})"
and Ax: "\<A> x = ({x0, x1}, x0, {(x0, (?\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), x1)})"
and Ms: "\<M> = {(a\<^bsup>q\<rightarrow>p\<^esup>), (b\<^bsup>p\<rightarrow>x\<^esup>)}"
and Ps: "\<P> = {p,q,x}"
  and G: "\<G> = {(q,p), (p,x)}" 
and peers_diff: "q \<noteq> x \<and> x \<noteq> p \<and> q \<noteq> p"
and states_diff: "p0 \<noteq> p1 \<and> q0 \<noteq> q1 \<and> x0 \<noteq> x1"
shows "\<forall>peer \<in> \<P>. \<L>\<^sup>* peer = \<L> peer" using assms
  sorry

lemma CE1_original_subset_cond:
assumes Ap: "\<A> p = ({p0, p1}, p0, {(p0, (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), p1), (p0, (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), p1)})"
and Aq: "\<A> q = ({q0, q1}, q0, {(q0, (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), q1)})"
and Ax: "\<A> x = ({x0, x1}, x0, {(x0, (?\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), x1)})"
and Ms: "\<M> = {(a\<^bsup>q\<rightarrow>p\<^esup>), (b\<^bsup>p\<rightarrow>x\<^esup>)}"
and Ps: "\<P> = {p,q,x}"
  and G: "\<G> = {(q,p), (p,x)}" 
and peers_diff: "q \<noteq> x \<and> x \<noteq> p \<and> q \<noteq> p"
and states_diff: "p0 \<noteq> p1 \<and> q0 \<noteq> q1 \<and> x0 \<noteq> x1"
shows "\<forall>p \<in> \<P>. \<forall> q \<in> \<P>. (((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?)"
  sorry

lemma CE1_shuffled_langs: 
 assumes Ap: "\<A> p = ({p0, p1}, p0, {(p0, (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), p1), (p0, (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), p1)})"
and Aq: "\<A> q = ({q0, q1}, q0, {(q0, (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), q1)})"
and Ax: "\<A> x = ({x0, x1}, x0, {(x0, (?\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), x1)})"
and Ms: "\<M> = {(a\<^bsup>q\<rightarrow>p\<^esup>), (b\<^bsup>p\<rightarrow>x\<^esup>)}"
and Ps: "\<P> = {p,q,x}"
  and G: "\<G> = {(q,p), (p,x)}" 
and peers_diff: "q \<noteq> x \<and> x \<noteq> p \<and> q \<noteq> p"
and states_diff: "p0 \<noteq> p1 \<and> q0 \<noteq> q1 \<and> x0 \<noteq> x1"
shows "\<forall>peer \<in> \<P>. \<L>\<^sup>*(peer) \<subseteq> \<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(peer)" by (simp add: language_shuffle_subset)

lemma CE1_not_synchronisable: 
 assumes Ap: "\<A> p = ({p0, p1}, p0, {(p0, (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), p1), (p0, (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), p1)})"
and Aq: "\<A> q = ({q0, q1}, q0, {(q0, (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), q1)})"
and Ax: "\<A> x = ({x0, x1}, x0, {(x0, (?\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), x1)})"
and Ms: "\<M> = {(a\<^bsup>q\<rightarrow>p\<^esup>), (b\<^bsup>p\<rightarrow>x\<^esup>)}"
and Ps: "\<P> = {p,q,x}"
  and G: "\<G> = {(q,p), (p,x)}" 
and peers_diff: "q \<noteq> x \<and> x \<noteq> p \<and> q \<noteq> p"
and states_diff: "p0 \<noteq> p1 \<and> q0 \<noteq> q1 \<and> x0 \<noteq> x1"
shows "\<L>\<^sub>\<zero> \<noteq> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!" using assms
proof -
  have sync: "[(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)] \<notin> \<L>\<^sub>\<zero>" using assms CE1_not_sync by simp
  have mbox: "[(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)] \<in> \<T>\<^bsub>None\<^esub>" using assms CE1_trace by simp
  then have "[(!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>)] \<in> \<T>\<^bsub>None\<^esub>\<downharpoonright>\<^sub>!" by force
  then show ?thesis using sync by blast
qed

lemma CE1_not_synchronisable2: 
 assumes Ap: "\<A> p = ({p0, p1}, p0, {(p0, (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), p1), (p0, (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), p1)})"
and Aq: "\<A> q = ({q0, q1}, q0, {(q0, (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), q1)})"
and Ax: "\<A> x = ({x0, x1}, x0, {(x0, (?\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), x1)})"
and Ms: "\<M> = {(a\<^bsup>q\<rightarrow>p\<^esup>), (b\<^bsup>p\<rightarrow>x\<^esup>)}"
and Ps: "\<P> = {p,q,x}"
  and G: "\<G> = {(q,p), (p,x)}" 
and peers_diff: "q \<noteq> x \<and> x \<noteq> p \<and> q \<noteq> p"
and states_diff: "p0 \<noteq> p1 \<and> q0 \<noteq> q1 \<and> x0 \<noteq> x1"
shows "\<not> is_synchronisable" using assms using CE1_not_synchronisable by fastforce


lemma CE1_theorem_original_rightside:
 assumes Ap: "\<A> p = ({p0, p1}, p0, {(p0, (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), p1), (p0, (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), p1)})"
and Aq: "\<A> q = ({q0, q1}, q0, {(q0, (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), q1)})"
and Ax: "\<A> x = ({x0, x1}, x0, {(x0, (?\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), x1)})"
and Ms: "\<M> = {(a\<^bsup>q\<rightarrow>p\<^esup>), (b\<^bsup>p\<rightarrow>x\<^esup>)}"
and Ps: "\<P> = {p,q,x}"
  and G: "\<G> = {(q,p), (p,x)}" 
and peers_diff: "q \<noteq> x \<and> x \<noteq> p \<and> q \<noteq> p"
and states_diff: "p0 \<noteq> p1 \<and> q0 \<noteq> q1 \<and> x0 \<noteq> x1"
shows "(\<forall>p \<in> \<P>. \<forall> q \<in> \<P>. ((is_parent_of p q) \<longrightarrow> ((((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) ))"
  sorry

lemma CE1_theorem_original_wrong:
 assumes Ap: "\<A> p = ({p0, p1}, p0, {(p0, (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), p1), (p0, (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), p1)})"
and Aq: "\<A> q = ({q0, q1}, q0, {(q0, (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), q1)})"
and Ax: "\<A> x = ({x0, x1}, x0, {(x0, (?\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), x1)})"
and Ms: "\<M> = {(a\<^bsup>q\<rightarrow>p\<^esup>), (b\<^bsup>p\<rightarrow>x\<^esup>)}"
and Ps: "\<P> = {p,q,x}"
  and G: "\<G> = {(q,p), (p,x)}" 
and peers_diff: "q \<noteq> x \<and> x \<noteq> p \<and> q \<noteq> p"
and states_diff: "p0 \<noteq> p1 \<and> q0 \<noteq> q1 \<and> x0 \<noteq> x1"
shows "(is_synchronisable \<longleftrightarrow> (\<forall>p \<in> \<P>. \<forall> q \<in> \<P>. ((is_parent_of p q) \<longrightarrow> ((((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) ))) \<Longrightarrow> False"
proof -
  assume t0: "(is_synchronisable \<longleftrightarrow> (\<forall>p \<in> \<P>. \<forall> q \<in> \<P>. ((is_parent_of p q) \<longrightarrow> ((((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) )))"
  have t1: "(\<forall>p \<in> \<P>. \<forall> q \<in> \<P>. ((is_parent_of p q) \<longrightarrow> ((((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) ))" using assms CE1_theorem_original_rightside by auto
  have t2: "\<not> is_synchronisable" using assms CE1_not_synchronisable2 by auto
  have " \<not>(is_synchronisable \<longleftrightarrow> (\<forall>p \<in> \<P>. \<forall> q \<in> \<P>. ((is_parent_of p q) \<longrightarrow> ((((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) )))"
    using t1 t2 by linarith
  then show "False" using t0 by blast
qed

lemma CE1_tree_topology:
  assumes Ap: "\<A> p = ({p0, p1}, p0, {(p0, (?\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), p1), (p0, (!\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), p1)})"
and Aq: "\<A> q = ({q0, q1}, q0, {(q0, (!\<langle>(a\<^bsup>q\<rightarrow>p\<^esup>)\<rangle>), q1)})"
and Ax: "\<A> x = ({x0, x1}, x0, {(x0, (?\<langle>(b\<^bsup>p\<rightarrow>x\<^esup>)\<rangle>), x1)})"
and Ms: "\<M> = {(a\<^bsup>q\<rightarrow>p\<^esup>), (b\<^bsup>p\<rightarrow>x\<^esup>)}"
and Ps: "\<P> = {p,q,x}"
  and G: "\<G> = {(q,p), (p,x)}" 
shows "tree_topology"
  using eps_in_mbox_execs is_in_infl_lang_rev_tree mbox_exec_to_infl_peer_word by auto

lemma theorem_original_ver: 
  assumes "tree_topology" 
  shows "(is_synchronisable \<longleftrightarrow> (\<forall>p \<in> \<P>. \<forall> q \<in> \<P>. ((is_parent_of p q) \<longrightarrow> ((((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) )))"
  using CE1_tree_topology CE1_theorem_original_wrong sorry

definition theorem_orig_rightside :: "bool"
  where "theorem_orig_rightside \<longleftrightarrow> (\<forall>p \<in> \<P>. \<forall> q \<in> \<P>. ((is_parent_of p q) \<longrightarrow> ((((\<L>\<^sub>!\<^sup>*(q))\<downharpoonright>\<^sub>{\<^sub>p\<^sub>,\<^sub>q\<^sub>})\<downharpoonright>\<^sub>!\<^sub>? \<subseteq> (\<L>\<^sup>*(p))\<downharpoonright>\<^sub>!\<^sub>?) \<and> ((\<L>\<^sup>*(p)) = (\<L>\<^sup>*\<^sub>\<squnion>\<^sub>\<squnion>(p)))) ))"








end


lemma theorem_original_ver: 
  assumes "NetworkOfCA.tree_topology \<M>" 
  shows "NetworkOfCA.is_synchronisable \<A> \<M> \<longleftrightarrow> NetworkOfCA.theorem_orig_rightside \<A> \<M>"
  sorry

theorem synchronisability_for_trees:
  assumes "NetworkOfCA.tree_topology \<M>"
  shows "(NetworkOfCA.is_synchronisable \<A> \<M> \<longleftrightarrow> NetworkOfCA.theorem_rightside \<A> \<M>)"
  using assms unfolding NetworkOfCA_def NetworkOfCA.MboxTraces_def NetworkOfCA.SyncTraces_def NetworkOfCA.theorem_rightside_def 
  sorry

end