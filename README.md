# Mechanization of Synchronizability  Theory for Communicating Automata with Mailbox Semantics 

This repository contains our mechanization into [Isabelle](https://isabelle.in.tum.de/) of Theorem 4.5 and necessary related results from:
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
│ ├── CommunicatingAutomata.thy # contains most of the Lemmas (concerning automata, systems, etc.)
│ ├── CounterExamples.thy # contains the beginnings of the formalization of our counterexamples
│ ├── Defs.thy # contains all definitions, inductives, functions, etc.
│ ├── Express.thy # contains only Lemma 4.4 and Theorem 4.5
│ └── FormalLanguages.thy # some formalization of formal languages, etc.
│
├── 📂 Latex_Exports/ # contains the LaTeX exports of both formalizations
│ ├── 📂 Extended_Formalization/ # contains the exported extension
│ │ ├── 📂 Synchronizability/ # the folder created using Isabelle's export functionality
│ │ ├── Synchronizability_latex.zip # the LaTeX code 
│ │ └── Synchronizability.pdf # the pdf compiled using the latex code above
│ ├── 📂 Original_Formalization/ # contains the exported original formalization
│ │ ├── 📂 Original/ # the folder created using Isabelle's export functionality
│ │ ├── Original_latex.zip # the LaTeX code 
│ │ └── Original.pdf # the pdf compiled using the latex code above
│
│
├── 📂 Thesis/ # contains the Master's thesis / internship report
│ ├── 📂 Short_Thesis/ # contains the Mémoire de Master for Université Côte d'Azur
│ └── TUM_final_thesis.pdf # the Master's thesis for the Technical University of Munich
│
└── README.md # You are here 📖
```

## 📫 Theory Hierarchy 📫

The dependencies of the theories are as follows:

<img 
style="display: block; margin: auto;"
src="Latex_Exports\Extended_Formalization\session_graph.jpg" alt="drawing" width="300"/>

*FormalLanguages.thy* and *Defs.thy* contain all definitions, inductives, etc. used in the remaining theories.

*CommunicatingAutomaton.thy* inhabits the majority of lemmas of the mechanization. The lemmas are divided loosely into sections, but may involve e.g. communicating automata, synchronous systems, mailbox systems, the shuffled language, and many more.

All these lemmas are then applied in *Express.thy*, which contains the formalization of Lemma 4.4 and Theorem 4.5 of the source paper. 

*CounterExamples.thy* is not included in the hierarchy (which was created using the LaTeX export feature of Isabelle), since it is not currently in a complete or correct state, and the export only works for theories with no errors. However, it should be located under *Express.thy*, as it uses Lemma 4.4 as well. 

## 📪 Some Remarks 📪

We used the 2025 version of [Isabelle](https://isabelle.in.tum.de/), although the files should work with other versions of Isabelle as well.

*CounterExamples.thy* is not currently compatible anymore with the rest of the theories (since we changed some symbols to make the LaTeX exports possible). To use it, e.g. to complete the formalization of the counterexamples in the thesis, one would first need to make the syntax compatible with the new one (from the *Defs.thy*, etc.) again.
It might be that the file structuring needs to be changed to accomodate the counterexamples (or rename some definitions), since the Counterexamples also use the subset condition, but different versions than in the final one!

Another remark, the exports in *Latex_Exports* do not generally include comments, and for the original formalization, we have commented some code (around 20 lines), because it was not compiling otherwise.