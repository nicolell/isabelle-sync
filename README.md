# Mechanization of Synchronizability  Theory for Communicating Automata with Mailbox Semantics 

This repository contains our mechanization into Isabelle of Theorem 4.5 and necessary related results from:
> @article{express,
  title={Synchronisability in Mailbox Communication},
  author={Di Giusto, Cinzia and Laversa, Laetitia and Peters, Kirstin},
  journal={arXiv preprint arXiv:2411.14580},
  year={2024}
}

## 📬 Repository Structure 📬

```plaintext
isabelle-sync/
│
├── 📂 Express/ # the LaTeX code for the source paper 
│
├── 📂 Formalization_Isabelle/ # the initially provided Isabelle formalization
│ ├── CommunicatingAutomata.thy 
│ └── FormalLanguages.thy 
│
├── 📂 Formalization_Isabelle_Extension/ # our extension of the initial Isabelle formalization
│ ├── 📂 Synchronizability # contains the LaTeX of theories below (except CounterExamples.thy)
│ ├── CommunicatingAutomata.thy # contains most of the Lemmas (concerning automata, systems, etc.)
│ ├── CounterExamples.thy # contains the beginnings of the formalization of our counterexamples
│ ├── Defs.thy # contains all definitions, inductives, functions, etc.
│ ├── Express.thy # contains only Lemma 4.4 and Theorem 4.5
│ └── FormalLanguages.thy # some formalization of formal languages, etc.
│
├── 📂 Resources/ # contains some of our learning materials, literature and older code
│
├── 📂 Thesis/ # contains the Master's thesis / internship report
│
└── README.md # You are here 📖

