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


end