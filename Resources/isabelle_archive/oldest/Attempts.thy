theory Attempts
  imports FormalLanguages
  imports CommunicatingAutomata
begin

subsubsection "influenced language approaches 1"

inductive path_to_root :: "'peer ⇒ 'peer list ⇒ bool" where
PTRRoot: "𝒫⇩?(p) = {} ⟹ path_to_root p [p]" |
PTRNode: "⟦𝒫⇩?(p) = {q}; path_to_root q as⟧ ⟹ path_to_root p (p # as)"

fun is_root :: "'peer topology ⇒ 'peer ⇒ bool" where
"is_root E p = ((card (E⟨→p⟩)) = 0) "

fun get_root :: "'peer topology ⇒ 'peer" where
"get_root E = (THE x. is_root E x)"

fun get_path_to_root :: "'peer ⇒  'peer list" where
"get_path_to_root p = (THE ps. path_to_root p ps)"

fun infl_lang_rec :: "'peer list ⇒ ('information, 'peer) action language" where
"infl_lang_rec [] = {}" |
"infl_lang_rec [r] = {ε}" |
"infl_lang_rec (p # q # ps) = {w | w. w ∈ ℒ(p) ∧ (w↓⇩?)↓⇩!⇩? ∈ ((infl_lang_rec (q # ps))⇂⇩! )⇂⇩!⇩? ∧ 𝒫⇩?(p) = {q}}" 

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


subsubsection "influenced language approaches 2"
text "test and test2 should do the same but I am not 100% sure (hence why I try to prove it with eqtest "

inductive test :: "'peer ⇒ ('information, 'peer) action word ⇒ bool" where
t0 : "⟦𝒫⇩?(r) = {}; w ∈ ℒ(r)⟧ ⟹ test r w" |
t1 : "⟦𝒫⇩?(r) = {}; 𝒫⇩?(q) = {r}; w ∈ ℒ(q); ((w↓⇩?)↓⇩!⇩?) ∈ ((ℒ(r))⇂⇩!⇩?) ⟧ ⟹ test q w" |
t2 : "⟦𝒫⇩?(p) = {q}; w ∈ ℒ(p); w' ∈ ℒ(q); test q w'; ((w↓⇩?)↓⇩!⇩?) = ((w'↓⇩!)↓⇩!⇩?); ((w↓⇩?)↓⇩!⇩?) ∈ (((ℒ(q))⇂⇩!)⇂⇩!⇩?)⟧ ⟹ test p w"

inductive test2 :: "'peer ⇒ ('information, 'peer) action word ⇒ bool" where
t00: "⟦𝒫⇩?(r) = {}; w ∈ ℒ(r)⟧ ⟹ test2 r w" | ―‹influenced language of root r is language of r›
t10: "⟦𝒫⇩?(r) = {}; 𝒫⇩?(q) = {r}; w ∈ ℒ(q); ((w↓⇩?)↓⇩!⇩?) ∈ ((ℒ(r))⇂⇩!⇩?) ⟧ ⟹ test2 q w" | ―‹q is direct child of root r›
t20: "⟦𝒫⇩?(p) = {q}; w ∈ ℒ(p); test2 q w'; ((w↓⇩?)↓⇩!⇩?) = ((w'↓⇩!)↓⇩!⇩?)⟧ ⟹ test2 p w" ―‹p is any node and q its parent›

lemma eeeeee : "test2 p w ⟹  w ∈ ℒ(p)" using test2.induct by simp
lemma eeeeeee : "⟦𝒫⇩?(p) = {q}; w ∈ ℒ(p); test2 q w'; ((w↓⇩?)↓⇩!⇩?) = ((w'↓⇩!)↓⇩!⇩?)⟧ ⟹ ((w↓⇩?)↓⇩!⇩?) ∈ (((ℒ(q))⇂⇩!)⇂⇩!⇩?)" 
  using eeeeee by blast
text "this means test and test2 are equivalent, test2 is just shorter"

lemma "⟦x = 2; y = x + 1; y > x; y < 5⟧ ⟹ y = 3" by auto

lemma eqtest : "test2 p w ⟹ test p w"
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
  then show ?case sorry
qed

abbreviation infl_lang2 :: "'peer ⇒ ('information, 'peer) action language" where
"infl_lang2 p ≡ {w | w. test p w}"

value "[!⟨x⟩, ?⟨y⟩, ?⟨z⟩]"
value "let w = [!⟨x⟩, ?⟨y⟩, ?⟨z⟩] in ((w↓⇩?)↓⇩!⇩?)"
value "let w' = [?⟨a⟩, !⟨y⟩, !⟨z⟩] in ((w'↓⇩!)↓⇩!⇩?)"


lemma filter_head : 
  assumes "xs ≠ []" and "x = hd xs" and "x = hd (filter f (xs))"
  shows "f x"
proof (rule ccontr)
  assume "¬ (f x)"
  then show "False"
  proof
    have "filter f [x] = []" by (simp add: ‹¬ f x›)
    moreover obtain ys where "xs = (x # ys)" by (metis assms(1,2) list.collapse)
    moreover have "filter f xs = filter f ys" by (simp add: ‹¬ f x› calculation(2))
    moreover have "x = hd (filter f ys)" by (simp add: assms(3) calculation(3))
    moreover have "filter f xs = filter f (filter f xs)" by simp
    moreover have "filter f (x # ys) = filter f (filter f (x # ys))" by simp
    moreover have "filter f xs = filter f ys" using calculation(3) by blast
    moreover have "hd (filter f ys) = hd (filter f xs)"  by (simp add: calculation(3))
    moreover have "hd (filter f ys) = hd (filter f (x # ys))" using assms(3) calculation(2,4) by argo
    moreover have "xs ≠ ys" by (simp add: calculation(2))
    ultimately show "f x" sorry
qed
qed

lemma root1 :
fixes p :: "'peer"
assumes "𝒫⇩?(p) = {} ∧ w  ∈ ℒ(p)"
shows "w↓⇩? = ε ∧ w↓⇩?  ∈ ℒ(p)"
  using assms
proof (induct w)
  case Nil
  then show ?case by simp
next
  case (Cons a w)
  then show ?case
  proof auto
    have "(a # w)  ∈ ℒ(p)" 
      by (simp add: Cons.prems)
  then have "is_output a" using assms(1) root_head_is_output by auto
  then have "[a]↓⇩? = ε" by simp
  then have "([a] @ w)↓⇩? = w↓⇩?"  by (metis append_self_conv2 filter_append)
  then have "(a # w)↓⇩? = w↓⇩?" by simp
  then have "∃s1 s2. (s1, a, s2) ∈ ℛ(p)"
    using ‹a # w ∈ ℒ p› no_word_no_trans by blast
  then obtain s1 s2 where "(s1, a, s2) ∈ ℛ(p)" by auto
  then show "(w ∈ ℒ p ⟹ w↓⇩? = ε ∧ w↓⇩? ∈ ℒ p) ⟹ 𝒫⇩? p = {} ⟹ a # w ∈ ℒ p ⟹ is_output a"using ‹is_output a› by blast
next
  have "(w ∈ ℒ p ⟹ w↓⇩? = ε ∧ w↓⇩? ∈ ℒ p) ⟹ 𝒫⇩? p = {} ⟹ a # w ∈ ℒ p ⟹ is_output a" 
    using root_head_is_not_input by blast
  then show "w↓⇩? ∈ ℒ p" using assms Cons
  proof (cases "w↓⇩?")
    case Nil
    then show ?thesis
      by (metis CommunicatingAutomaton.REmpty2 CommunicatingAutomaton.Traces.intros automaton_of_peer)
  next
    case (Cons b bs)
    then have "a # w ∈ ℒ p" by (simp add: Cons.prems)
    then have "(a # w)↓⇩? = w↓⇩?" 
      using Cons.prems NetworkOfCA.root_head_is_output NetworkOfCA_axioms by fastforce
    then have "∃s1 s2. (s1, a, s2) ∈ ℛ(p)" 
      by (meson ‹a # w ∈ ℒ p› no_word_no_trans)
    then obtain s1 s2 where "(s1, a, s2) ∈ ℛ(p)" by auto
    define b where "b = hd (w↓⇩?)"  
    then show ?thesis using assms Cons
    proof (cases "∃ s3. (s2, b, s3) ∈ ℛ(p)")
      case True
      then show ?thesis 
        by (metis (no_types, lifting) NetworkOfCA.no_input_trans_root NetworkOfCA_axioms assms b_def filter_eq_Cons_iff list.sel(1)
            local.Cons)
    next
      case False
      then show ?thesis sledgehammer
    qed
  qed
  
qed
  then have "𝒫⇩?(p) = {}" 
    using assms(1) by auto
  then have "(𝒫⇩? p = {} ⟹ w ∈ ℒ p) ⟹ w↓⇩? = ε" using Cons.hyps  by blast

  then have "w ∈ ℒ p" sledgehammer
  then have "w↓⇩? = ε" sledgehammer
  then have "(a # w)↓⇩? = ε" sledgehammer
  then show ?case sledgehammer
qed


―‹this looks for the pattern !x?y in a given word›
fun o_i_exists :: " ('information, 'peer) action word ⇒ bool" where
"o_i_exists [] = False" |
"o_i_exists [a] = False" |
"o_i_exists (m1 # m2 # ms) = ((is_output m1 ∧ is_input m2) ∨ o_i_exists (m2 # ms))"

fun shuffle_once :: "('information, 'peer) action word ⇒ ('information, 'peer) action word" where
"shuffle_once [] = []" |
"shuffle_once [a] = [a]" |
"shuffle_once (m1 # m2 # ms) = (if (is_output m1 ∧ is_input m2) then m2 # m1 # ms else m1 # shuffle_once (m2 # ms))" 

fun shuffle_n :: "('information, 'peer) action word ⇒ nat ⇒ ('information, 'peer) action language" where
"shuffle_n w 0 = {w}" |
"shuffle_n w (Suc n) = {w} ∪ shuffle_n (shuffle_once w) n"

value "shuffle_n [?⟨y⟩, !⟨x⟩, ?⟨z⟩] 3"
value "shuffle_n [!⟨b⟩, !⟨c⟩, ?⟨a⟩] 3"

value "o_i_exists [?⟨y⟩, !⟨x⟩, ?⟨z⟩]"
value "shuffle_once [?⟨y⟩, !⟨x⟩, ?⟨z⟩]"
value "shuffle_n [a] 0"


abbreviation valid_input_shuffles_of_w :: "('information, 'peer) action word ⇒ ('information, 'peer) action language" where
"valid_input_shuffles_of_w w ≡ {w' | w'. w' ∈ (shuffle_n w (length w))}"



abbreviation shuffled_lang :: "('information, 'peer) action language ⇒ ('information, 'peer) action language" where
"shuffled_lang L ≡ { w' | w w'. w ∈ L ∧ w' ∈ (shuffle_n w (length w))}"

abbreviation valid_input_shuffle 
  :: "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ bool" (infixl "⊔⊔⇩?" 60) where
  "w' ⊔⊔⇩? w ≡ w' ∈ valid_input_shuffles_of_w w"

  lemma shuffle_epsilon : "shuffle_n ε n = shuffle_n ε 0"
proof (induct n)
  case 0
  then show ?case by simp
next
  case (Suc n)
  then have "shuffle_n ε (Suc n) = {ε} ∪ shuffle_n (shuffle_once ε) n" by simp
  moreover have "shuffle_once ε = ε" by simp
  moreover have "shuffle_n ε (Suc n) = {ε} ∪ shuffle_n ε n" by simp
  then show ?case  using Suc by auto
qed

value "shuffle_n (!⟨(a⇩1⇗a⇩1→a⇩1⇖)⟩ # ?⟨(a⇩1⇗a⇩1→a⇩1⇖)⟩ # !⟨(a⇩1⇗a⇩1→a⇩1⇖)⟩ # ?⟨(a⇩1⇗a⇩1→a⇩1⇖)⟩ # ε) 4"
― ‹the issue is the shuffle always shuffles the first occurrence first, but this doesnt
create all the possible shuffles, e.g. !??! is not present›





inductive shuffle_once :: "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ bool" where
  shuffle_swap: "⟦ is_output m1; is_input m2 ⟧ ⟹ shuffle_once (m1 # m2 # ms) (m2 # m1 # ms)" |
  shuffle_cons: "⟦ shuffle_once xs ys ⟧ ⟹ shuffle_once (x # xs) (x # ys)"

lemma shuffle_once_rev :
  assumes "shuffle_once (x # xs) (x # ys)"
  shows "shuffle_once xs ys"
  using assms list.sel(3) shuffle_once.cases by fastforce

inductive shuffled :: "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ bool" where
  shuffled_refl [intro]: "shuffled w w" |
  shuffled_step: "⟦ shuffle_once w w'; shuffled w' w'' ⟧ ⟹ shuffled w w''"

lemma shuffled_rev : 
  assumes "shuffled w w''" and "w ≠ w''"
  shows "∃w'.  shuffle_once w w' ∧ shuffled w' w''"
  by (metis assms(1,2) shuffled.cases)

lemma ererer : 
  assumes "shuffled (a # w') (a # w)"
  shows "shuffled w' w"
  sorry
lemma erere2r : 
  assumes "shuffled w' w"
  shows  "shuffled (a # w') (a # w)"
  sledgehammer

abbreviation valid_input_shuffles_of_w :: "('information, 'peer) action word ⇒ ('information, 'peer) action language" where
  "valid_input_shuffles_of_w w ≡ {w'. shuffled w w'}"

abbreviation shuffled_lang :: "('information, 'peer) action language ⇒ ('information, 'peer) action language" where
  "shuffled_lang L ≡ ⋃w ∈ L. valid_input_shuffles_of_w w"

abbreviation valid_input_shuffle :: 
  "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ bool" (infixl "⊔⊔⇩?" 60) where
  "w' ⊔⊔⇩? w ≡ shuffled w w'"





inductive shuffled ::"('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ bool" where
no_shuffle : "shuffled w w" |
yes_shuffle: "⟦ is_output o_m; is_input i_m ⟧ ⟹ shuffled (xs @ [o_m] @ [i_m] @ ys) (xs @ [i_m] @ [o_m] @ ys)" |
shuffle_cons : "⟦ shuffled w w'⟧ ⟹ shuffled (a # w) (a # w')" |
shuffle_app :  "⟦ shuffled w w'; shuffled w' w''⟧ ⟹ shuffled w w''"










lemma "shuffled ε ε" sorry
lemma ex1 : "shuffled [!⟨x⟩, ?⟨y⟩, ?⟨z⟩] [?⟨y⟩, !⟨x⟩, ?⟨z⟩]"
proof -
  have "[!⟨x⟩, ?⟨y⟩, ?⟨z⟩] = [] @ [!⟨x⟩] @ [?⟨y⟩] @ [?⟨z⟩]" by auto
  moreover have "is_output (!⟨x⟩)" by auto
  moreover have "is_input (?⟨y⟩)" by auto
  moreover have "shuffled ([] @ [!⟨x⟩] @ [?⟨y⟩] @ [?⟨z⟩]) ([]@ [?⟨y⟩] @ [!⟨x⟩]  @ [?⟨z⟩])" 
    by (metis append.left_neutral append_Cons is_output.simps(1,2) shuffled.swap)
  moreover have "[]@ [?⟨y⟩] @ [!⟨x⟩]  @ [?⟨z⟩] = [?⟨y⟩, !⟨x⟩, ?⟨z⟩]" by auto
  moreover show "shuffled [!⟨x⟩, ?⟨y⟩, ?⟨z⟩] [?⟨y⟩, !⟨x⟩, ?⟨z⟩]"  using calculation(4) by fastforce
qed

lemma ex2 : "shuffled (!⟨x⟩ # ?⟨y⟩ # !⟨z⟩ # ?⟨zz⟩ # ε) (!⟨x⟩ # ?⟨y⟩ # ?⟨zz⟩ # !⟨z⟩ # ε)"
  sorry

lemma ex3 : "¬(shuffled [?⟨y⟩, !⟨x⟩] [!⟨x⟩, ?⟨y⟩])"
  sorry

inductive shuffle_once :: "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ bool" where
  shuffle_swap: "⟦ is_output m1; is_input m2 ⟧ ⟹ shuffle_once (m1 # m2 # ms) (m2 # m1 # ms)" |
  shuffle_no_swap: "shuffle_once w w" |
  shuffle_cons: "⟦ shuffle_once xs ys ⟧ ⟹ shuffle_once (x # xs) (x # ys)"

lemma shuffle_once_rev :
  assumes "shuffle_once (x # xs) (x # ys)"
  shows "shuffle_once xs ys"
  using assms list.sel(3) shuffle_once.cases by fastforce

inductive shuffled :: "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ bool" where
  shuffled_refl [intro]: "shuffled w w" |
  shuffled_step: "⟦ shuffle_once w w'; shuffled w' w'' ⟧ ⟹ shuffled w w''"

lemma shuffled_rev : 
  assumes "shuffled w w''" and "w ≠ w''"
  shows "∃w'.  shuffle_once w w' ∧ shuffled w' w''"
  by (metis assms(1,2) shuffled.cases)

lemma ererer : 
  assumes "shuffled (a # w') (a # w)"
  shows "shuffled w' w"
  sorry
lemma erere2r : 
  assumes "shuffled w' w"
  shows  "shuffled (a # w') (a # w)"
  sledgehammer

abbreviation valid_input_shuffles_of_w :: "('information, 'peer) action word ⇒ ('information, 'peer) action language" where
  "valid_input_shuffles_of_w w ≡ {w'. shuffled w w'}"

abbreviation shuffled_lang :: "('information, 'peer) action language ⇒ ('information, 'peer) action language" where
  "shuffled_lang L ≡ ⋃w ∈ L. valid_input_shuffles_of_w w"

abbreviation valid_input_shuffle :: 
  "('information, 'peer) action word ⇒ ('information, 'peer) action word ⇒ bool" (infixl "⊔⊔⇩?" 60) where
  "w' ⊔⊔⇩? w ≡ shuffled w w'"




― ‹TNsync = L0, ENsync = T0, EMbox = Tinf/None, TMbox = Linf, E = !?, T = only sends›
theorem synchronisability_for_trees:
  assumes "tree_topology" 
  shows "is_synchronisable ⟷ (∀p q. ((𝒫⇩?(p) = {q}) ⟶ (((((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩?) ⊆ ((ℒ⇧*(p))⇂⇩!⇩?)) ∧ ((ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p)))) ))" (is "?L ⟷ ?R")
proof
  (* Direction 1: is_synchronisable => language conditions *)
  assume "?L"
  show "?R"
  proof clarify
    fix p q
    assume p_parent: "𝒫⇩?(p) = {q}"
    
    have sync_def: "𝒯⇘None⇙⇂⇩! = ℒ⇩𝟬"
      using ‹?L› by simp
    
    show "(((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩?) ⊆ ((ℒ⇧*(p))⇂⇩!⇩?) ∧ (ℒ⇧*(p)) = (ℒ⇧*⇩⊔⇩⊔(p))"
    proof (rule conjI)
      (* Part 1: Prove the subset relation for traces *)
      show "((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (ℒ⇧*(p))⇂⇩!⇩?"
      proof (rule ccontr)
        assume subset_not_holds: "¬(((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})⇂⇩!⇩? ⊆ (ℒ⇧*(p))⇂⇩!⇩?)"
        (* Extract a counterexample trace *)
        then obtain v where v_def: "v ∈ ((ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩})" and
                     not_in_p: "v↓⇩!⇩? ∉ (ℒ⇧*(p))⇂⇩!⇩?" by blast
         
        (* Use Lemma 4.4 to find an execution v' in mailbox system *)
        obtain v' where v'_def: "v' ∈ 𝒯⇘∞⇙" and
                       v'_proj_q: "(v'↓⇩!)↓⇩q = v" and
                       v'_proj_p: "v'↓⇩p = ε"
          using v_def lemma4_4 sorry― ‹by metis›
          
        (* Use synchronisability to show trace is also in synchronous system *)
        have "v'↓⇩! ∈ ℒ⇘∞⇙" using v'_def by blast
        also have "ℒ⇘∞⇙ = 𝒯⇩𝟬" using sync_def by simp
        also have "𝒯⇩𝟬 = ℒ⇩𝟬" by simp
        have v'_sync: "v'↓⇩! ∈ ℒ⇩𝟬" using calculation by auto
        
        (* Since v'⇂p = ε, p must be able to receive outputs without sending *)
        have "v↓⇩!⇩? ∈ ((ℒ(p))⇂⇩?)⇂⇩!⇩?" using v'_sync v'_proj_p sorry
        have "v↓⇩!⇩? ∈ (ℒ⇩?⇧*(p))⇂⇩!⇩?" sorry
        
        (* Contradiction with our assumption *)
        show "False" using not_in_p sorry
      qed
      
      (* Part 2: Prove language equivalence *)
      show "ℒ⇧*(p) = ℒ⇧*⇩⊔⇩⊔(p)"
      proof
        (* First inclusion is by definition *)
        show "ℒ⇧*(p) ⊆ ℒ⇧*⇩⊔⇩⊔(p)" using language_shuffle_subset by auto
        (* Second inclusion needs more work *)
        show "ℒ⇧*⇩⊔⇩⊔(p) ⊆ ℒ⇧*(p)"
        proof
          fix v
          assume "v ∈ ℒ⇧*⇩⊔⇩⊔(p)"
          (* Find shortest words v and v' where v' is in language but v is shuffled *)
          then have "∃v'. v' ∈ ℒ⇧*(p) ∧ v ⊔⊔⇩? v'" using shuffle_rev by auto ― ‹in the paper it's v' _ v›
          (* Focus on specific form of these words *)
          obtain v' w a xs where  v'_def: "v' ∈ ℒ⇧*(p)" and 
                                    "v ⊔⊔⇩? v'" and
                                    v_form: "v = w # ?⟨(a⇗q→p⇖)⟩ # xs" and
                                v'_form: "v' = w # xs @ [?⟨(a⇗q→p⇖)⟩]" and
                                 xs_form: "xs = xs↓⇩!" ― ‹xs are outputs to p's children, maybe thats also necessary here›
            sorry

          (* Apply Lemma 4.4 to find execution in mailbox system *)
          obtain w' where w'_def: "w' ∈ 𝒯⇘∞⇙" and
                        w'_proj: "w'↓⇩p = w # xs @ [?⟨(a⇗q→p⇖)⟩]"
            using v'_def lemma4_4 sorry
            
          (* By construction, outputs from q to p happen before p's outputs *)
          have "∃m mm mmm. w'↓⇩! = m @ [!⟨(a⇗q→p⇖)⟩] @ mm @ xs @ mmm"
            using w'_def  w'_proj sorry
            
          (* Use synchronisability to show trace is in synchronous system *)
          have "w'↓⇩! ∈ ℒ⇘∞⇙" using w'_def by auto
          also have "ℒ⇘∞⇙ = ℒ⇩𝟬" using sync_def by simp
          also have "ℒ⇩𝟬 = 𝒯⇩𝟬" by simp
          then have w'_sync: "w'↓⇩! ∈ 𝒯⇩𝟬" by (simp add: calculation)
          (* In synchronous system, p must receive input before sending outputs *)
          have "v ∈ ℒ⇧*(p)" sorry
            
          thus "v ∈ ℒ⇧*(p)" by simp
        qed
      qed
    qed
  qed
next
  (* Direction 2: language conditions => is_synchronisable *)
  assume "?R"
  show "?L"
  proof 
    have "ℒ⇘∞⇙ = ℒ⇩𝟬"
    proof
      (* First inclusion: mailbox traces ⊆ synchronous traces *)
      show "ℒ⇘∞⇙ ⊆ ℒ⇩𝟬"
      proof
        fix w
        assume "w ∈ ℒ⇘∞⇙"
        (* Construct word w' by adding matching receive actions after each send *)
        obtain w' where w'_def: "w' = add_matching_recvs w" by simp
        
        (* Show w' is in the execution set of the mailbox system using induction *)
        have "w' ∈ 𝒯⇘∞⇙"
        proof (induction "length w")
          (* Base case: single output *)
― ‹in the paper, this is shown with w being a single output, but i dont know how to do that in isabelle :C›
          case 0
          then have "w' = add_matching_recvs ε"  by (simp add: w'_def)
          then have "w' = ε" by simp
          show ?case 
            using MREmpty MboxTraces.intros ‹w' = ε› by blast
        next
          (* Inductive case *)
          case (Suc n)
          show ?case
          proof 
            have "length w = Suc n"  by (simp add: Suc.hyps(2))
            (* Decompose w into v!a⇩q→p *)
            then obtain v a q p where w_decomp: "w = v ⋅ [!⟨(a⇗q→p⇖)⟩]" and
                                 "length v = n"
              sorry
            then have "add_matching_recvs [!⟨(a⇗q→p⇖)⟩] = [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]" by simp
            then obtain w' v' where w'_decomp : "w' = v' ⋅ [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]" 
                                and "v' = add_matching_recvs v" by blast
            (* Apply induction hypothesis to v *)
            have "v' ∈ 𝒯⇘∞⇙"
              using Suc and `length v = n` sorry
              
            ― ‹Aq is able to perform !aqp in some state after executing all the sends in v›
            have "∃st. (v ⋅ st ⋅ [!⟨(a⇗q→p⇖)⟩]) ∈ (ℒ q)⇂⇩!" sorry
            have "v'↓⇩! = v" sorry
            ― ‹Aq is able to perform !aqp in some state after executing all the sends in v'›
            then have  "∃st. (v' ⋅ st ⋅ [!⟨(a⇗q→p⇖)⟩]) ∈ (ℒ q)⇂⇩!" sorry
(* Show q can send a⇩q→p after execution v' *)
            then have "v' ⋅  [!⟨(a⇗q→p⇖)⟩] ∈ 𝒯⇘∞⇙" sorry
            then have "((v' ⋅  [!⟨(a⇗q→p⇖)⟩])↓⇩{⇩p⇩,⇩q⇩})↓⇩! = (w↓⇩{⇩p⇩,⇩q⇩})↓⇩!" sorry
            then have "((v' ⋅  [!⟨(a⇗q→p⇖)⟩])↓⇩{⇩p⇩,⇩q⇩})↓⇩! ∈ (ℒ⇩!⇧*(q))⇂⇩{⇩p⇩,⇩q⇩}" sorry
            (* Show p can receive a⇩q→p after execution v'!a⇩q→p *)
              
            then have  "w' ∈ 𝒯⇘∞⇙" sorry
          
          qed
        qed
        
        (* Use w' to show w is in synchronous system *)
        have "w' ∈ 𝒯⇘∞⇙" sorry
        hence "Nsync can simulate w' by combining sends with receives"
          by (rule synchronous_simulation)
        moreover have "w'⇂⇩! = w"
          using w'_def by simp
        ultimately show "w ∈ ℒ⇩𝟬"
          by blast
      qed
      
      (* Second inclusion: synchronous traces ⊆ mailbox traces *)
    next
      show "ℒ⇩𝟬 ⊆ ℒ⇘∞⇙"
      proof
        fix w
        assume "w ∈ ℒ⇩𝟬"
        
        (* For synchronous sends, construct mailbox execution *)
        obtain w' where w'_def: "w' is obtained from w by adding matching receive directly after sends"
          by (rule word_construction)
        
        (* Show mailbox system can simulate synchronous system *)
        have "w' ∈ 𝒯⇘∞⇙"
          using `w ∈ 𝒯⇘Nsync⇙` by (rule mailbox_simulation)
        
        thus "w ∈ ℒ⇘∞⇙"
          using w'_def by simp
      qed
    qed
    
    then show "is_synchronisable" by (simp add: is_synchronisable_def)
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
      then obtain v a q p where "(w↓⇩!) = v ⋅ [!⟨(a⇗q→p⇖)⟩]" using ‹w↓⇩! ≠ ε› decompose_send by blast
      then show ?thesis 
      proof (induct "length (w↓⇩!)") ― ‹the paper uses base case 1 but idk how to do this here, case 0 is trivial though›
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
        then obtain v' where "w' = v' ⋅ [!⟨(a⇗q→p⇖)⟩, ?⟨(a⇗q→p⇖)⟩]" by simp

        then have "v' ∈ 𝒯⇘None⇙" sledgehammer

        then show ?case sorry
      qed
    qed
  next ― ‹w in TSync›
    fix w
    show "w ∈ ℒ⇩𝟬 ⟹ ∃w'. w = w'↓⇩! ∧ w' ∈ 𝒯⇘None⇙"
    proof -
      assume "w ∈ ℒ⇩𝟬"
      ― ‹For every output in w, Nsync was able to send the respective message and directly
      receive it›
      obtain w' where "w' = add_matching_recvs w" by simp
      ― ‹then Nmbox can simulate the run of w in Nsync by sending every mes-
      sage first to the mailbox of the receiver and then receiving this message›
      then have "w' ∈ 𝒯⇘None⇙" sorry
      then have "w = w'↓⇩!" sorry
      then have "(w'↓⇩!) ∈ 𝒯⇘None⇙" sorry
      then show ?thesis using ‹w = w'↓⇩!› ‹w' ∈ 𝒯⇘None⇙› by blast
    qed
  qed
qed

end