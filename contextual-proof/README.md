##  DUET 2.0 (Contextual Duet) Agda Formalization and Proofs

This project contains the source code for the formalization of Duet 1.0 in Agda, and the proofs of the fundamental property of metric preservation for Duet's sensitivity and privacy languages.

The structure of the project is as follows: 

- *lang.agda* : Duet core language formalization: terms, types, values, substitution, etc.
- *rules.agda* : Duet core language rules: typing judgements, dynamic semantics, probabilistic semantics etc.
- *logical-relations.agda* : Duet logical relations (i.e. for values, terms and value environments)
- *lemmas.agda* : useful lemmas necessary for proofs
- *proof.agda* : proof of the fundamental property of metric preservation for Duet's sensitivity language
- *proof2.agda* : cont. proof of the fundamental property of metric preservation for Duet's sensitivity language: closed terms and sensitivity type soundness at base types
- *red-proof.agda* : proof of the fundamental property of metric preservation for Duet's privacy language
- *README.md* : contains this README, which you are currently reading :) 