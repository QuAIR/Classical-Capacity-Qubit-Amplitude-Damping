# Lean formalization: amplitude-damping strong additivity

This local-only Lean 4 project formalizes the results of `main-v1.1.tex` using
Lean-QIT and mathlib.

See `STATUS.md` for the exact boundary between checked lemmas and remaining
proof obligations.

## Reproducible environment

- Lean: `v4.30.0`
- Lean-QIT: local checkout at commit `da54e30`
- Dependency mode: local `path`; no network fetch and no `lake update`

## Proof architecture

1. `Definitions.lean`: output ensembles and average output-entropy cost.
2. `ConvexRoof.lean`: finite pure decompositions, the literal real infimum
   defining the output-entropy convex roof, and its lower-envelope theorem.
3. `Channel.lean`: the two Kraus operators of the qubit amplitude-damping
   channel and a checked proof of their trace-preserving completeness relation.
4. `FixedExcitation.lean`: excitation bounds and the checked determinant
   and entropy formulas for the output of a pure qubit input, together with
   the Jensen reduction for the roof lower bound.
5. `QubitEntropy.lean`: the checked two-level spectral formula expressing
   qubit entropy in terms of the determinant.
6. `HolevoReduction.lean`: checked reduction from strong superadditivity of
   the roof to the fixed-input and ensemble Holevo converse.
7. `Triangular/Statement.lean`: formal statement and normalization API for the
   triangular block entropy inequality.
8. Future modules will prove the logarithmic-determinant convexity lemma,
   scalar Jensen reduction, the triangular theorem, the amplitude-damping roof
   formula, and finally the EoF/channel corollaries.

The project does not use `sorry` or introduce axioms for the mathematical
claims.  Work-in-progress theorems are represented as named predicates until
their proofs are supplied.
