# Personal Lean Theorem Prover Code

- This repo contains examples of code written during my Fall 2023 Directed Study on topics of formal theorem proving in the Lean programming language.
- Contained are exercises from *Theorem Proving in Lean 3*, *Theorem Proving in Lean 4*, and *Functional Programming in Lean 4*.
- Note that reading tactic proofs in lean is made easier when stepping through line by line having access to tactic state.
- Lean 4 has an [interactive online editor](https://lean.math.hhu.de/) and so does Lean 3 [here](https://leanprover-community.github.io/lean-web-editor/).

## Some Highlights
- [ch8](/ch8/) contains the inductive definition of the 'aexpr' arithmetic expression type, with some proofs that basic simplifications of expressions maintain correctness on all inputs.

- [ch_10](/ch_10/) contains the formalization of a Linear Algebra homework problem in lean 3 and 4. 

- [fp-in-lean](/fp-in-lean/) has some functional programming exercises, as well as an I/O terminal application which converts an integer to roman numerals.

- [gcd_final.lean](/gcd_final.lean) contains many auxiliary lemmas about GCD and its properties, as well as a formal verification of Euclid's GCD algorithm.
