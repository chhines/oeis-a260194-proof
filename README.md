# Disproof of the Jump Universality Conjecture for OEIS A260194

Let the first three terms be 1 and let each subsequent term add the gcd of the current term and the term two places earlier. The positive difference 14 never occurs. This repository proves the negative answer to the question of whether every positive integer occurs.

## Statement to audit

Read Challenge.lean independently. It imports Lean core, defines the sequence with zero-based indices, and negates the entire quantified proposition. Lean index 0 corresponds to OEIS index 1. Comparator compares both the body of JumpResearch.a and the theorem JumpResearch.refutesCatalogueStatement. Its permitted axioms are propext, Classical.choice, and Quot.sound. The single deliberate hole in Challenge.lean marks the statement for comparison.

* [OEIS entry](https://oeis.org/A260194)
* [Pinned Formal Conjectures statement](https://github.com/google-deepmind/formal-conjectures/blob/2f91d251c07fbbaf9435166d47c11e884a08a6cf/FormalConjectures/OEIS/260194.lean)

## Proof

A state records the current coordinate and its two preceding jumps. If their sum is s, the new jump is gcd(current coordinate, s). The proof exhibits an inductive union of 307 sets of states defined by modular tests. Each possible jump from an admitted state is rejected by a necessary gcd condition or leads to another admitted state with an allowed jump. The allowed set excludes 14. The small initial segment and all finite certificate obligations are evaluated by Lean.

| Module | Role |
| --- | --- |
| A260194.Results | Sequence, indexing, gcd identities and periodicity lemmas |
| A260194.Checker | Soundness of the modular transition checks |
| A260194.Certificate | Finite certificate data and closed checks |
| A260194.Lift | Additional determinant-one reformulation |
| A260194.Proof | Induction from the initial state, exclusion of 14, and negative resolution |
| Solution | Exports the completed proof and prints its axiom dependencies |

## Reproduction

With Elan, Git, Python 3 and Linux bubblewrap installed, run from the repository root:

```sh
python3 scripts/check-lean-sources.py
lake exe cache get
lake build
./scripts/verify-comparator.sh
```

The Comparator script follows the pinned template and registers both bundled independent kernels. The workflow also validates the metadata, checks the licence, and generates API documentation. See PORTING.md for changes from the original Lean 4.19 proof. The registry form takes the full 40-character SHA of a public commit. [Palomar submission form](https://submit.palomar-registry.org/)

## Research significance

This result resolves a previously stated open question concerning OEIS A260194, also catalogued in Google DeepMind's Formal Conjectures project.

Beyond establishing that the positive difference 14 never occurs, the formal development proves that the sequence's jumps are bounded by 74 and are eventually periodic.

The proof uses a finite modular abstraction and an inductively closed certificate to establish global properties of an unbounded arithmetic recurrence. This approach may be relevant to the study of other GCD-driven sequences and the application of formal verification techniques to arithmetic dynamical systems.

The development does not establish a general theorem guaranteeing the applicability of this method to other recurrences.

## Provenance and review

Chhines selected the question, directed the investigation and supplied the proposed determinant-one reformulation. The OpenAI agent discovered the invariant and generated the certificate, Lean proofs, manuscript and submission port. Human contributions are recorded as research direction and input. Independent human mathematical review and editorial acceptance are unconfirmed. The project uses Apache-2.0 as supplied by the Palomar template. See NOTICE and formalization.yaml.
