(* Author: Kirstin Peters, Augsburg University, 2024 *)

theory FormalLanguages
  imports Main "HOL-Library.LaTeXsugar" "HOL-Library.OptionalSugar"
begin

section \<open>Formal Languages\<close>

type_synonym 'a word     = "'a list"
type_synonym 'a language = "'a word set"

subsection \<open>Words\<close>

abbreviation emptyWord :: "'a word"  ("\<epsilon>") where
  "\<epsilon> \<equiv> []"

abbreviation concat :: "'a word \<Rightarrow> 'a word \<Rightarrow> 'a word"  (infixl "\<sqdot>" 60) where
  "v\<sqdot>w \<equiv> v @ w" 

abbreviation length_of_word :: "'a word \<Rightarrow> nat"  ("|_|" [90] 60) where
  "|w| \<equiv> length w"

subsection \<open>Alphabets\<close>

locale Alphabet =
  fixes Letters :: "'a set "  ("\<Sigma>")
  assumes not_empty:      "\<Sigma> \<noteq> {}"
      and finite_letters: "finite \<Sigma>"
begin

inductive_set WordsOverAlphabet :: "'a word set"  ("\<Sigma>\<^sup>*" 100) where
EmptyWord: "\<epsilon> \<in> \<Sigma>\<^sup>*" |
Composed:  "\<lbrakk>a \<in> \<Sigma>; w \<in> \<Sigma>\<^sup>*\<rbrakk> \<Longrightarrow> (a#w) \<in> \<Sigma>\<^sup>*"

lemma word_over_alphabet_rev:
  fixes a :: "'a"
    and w :: "'a word"
  assumes "([a] \<sqdot> w) \<in> \<Sigma>\<^sup>*"
  shows "a \<in> \<Sigma>" and "w \<in> \<Sigma>\<^sup>*"
  using assms WordsOverAlphabet.cases[of "a#w"]
  by auto

lemma concat_words_over_an_alphabet:
  fixes v w :: "'a word"
  assumes "v \<in> \<Sigma>\<^sup>*"
      and "w \<in> \<Sigma>\<^sup>*"
    shows "(v \<sqdot> w) \<in> \<Sigma>\<^sup>*"
  using assms
proof (induct v)
  case EmptyWord
  assume "w \<in> \<Sigma>\<^sup>*"
  thus "(\<epsilon> \<sqdot> w) \<in> \<Sigma>\<^sup>*"
    by simp
next
  case (Composed a v)
  assume "a \<in> \<Sigma>"
  moreover assume "w \<in> \<Sigma>\<^sup>* \<Longrightarrow> (v \<sqdot> w) \<in> \<Sigma>\<^sup>*" and "w \<in> \<Sigma>\<^sup>*"
  hence "(v \<sqdot> w) \<in> \<Sigma>\<^sup>*" .
  ultimately show "((a#v) \<sqdot> w) \<in> \<Sigma>\<^sup>*"
    using WordsOverAlphabet.Composed[of a "v \<sqdot> w"]
    by simp
qed

lemma split_a_word_over_an_alphabet:
  fixes v w :: "'a word"
  assumes "(v \<sqdot> w) \<in> \<Sigma>\<^sup>*"
  shows "v \<in> \<Sigma>\<^sup>*" and "w \<in> \<Sigma>\<^sup>*"
  using assms
proof (induct v)
  case Nil
  {
    case 1
    show "\<epsilon> \<in> \<Sigma>\<^sup>*"
      using EmptyWord
      by simp
  next
    case 2
    assume "\<epsilon> \<sqdot> w \<in> \<Sigma>\<^sup>*"
    thus "w \<in> \<Sigma>\<^sup>*"
      by simp
  }
next
  case (Cons a v)
  assume "a#v \<sqdot> w \<in> \<Sigma>\<^sup>*"
  hence A1: "a \<in> \<Sigma>" and A2: "v \<sqdot> w \<in> \<Sigma>\<^sup>*"
    using word_over_alphabet_rev[of a "v \<sqdot> w"]
    by simp_all
  assume IH1: "v \<sqdot> w \<in> \<Sigma>\<^sup>* \<Longrightarrow> v \<in> \<Sigma>\<^sup>*" and IH2: "v \<sqdot> w \<in> \<Sigma>\<^sup>* \<Longrightarrow> w \<in> \<Sigma>\<^sup>*"
  {
    case 1
    from A1 A2 IH1 show "a#v \<in> \<Sigma>\<^sup>*"
      using Composed[of a v]
      by simp
  next
    case 2
    from A2 IH2 show "w \<in> \<Sigma>\<^sup>*"
      by simp
  }
qed

end
end