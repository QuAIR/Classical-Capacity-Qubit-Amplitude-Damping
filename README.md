# Lean formalization: amplitude-damping strong additivity

This local-only Lean 4 project formalizes the results of `main-v1.1.tex` using
Lean-QIT and mathlib.

## Reproducible environment

- Lean: `v4.30.0`
- Lean-QIT: local checkout at commit `da54e30`
- Dependency mode: local `path`; no network fetch and no `lake update`

## Proof architecture

1. `Definitions.lean`: output ensembles, average output-entropy cost, and an
   abstract interface for the convex roof.
2. `HolevoReduction.lean`: checked reduction from strong superadditivity of
   the roof to the fixed-input and ensemble Holevo converse.
3. `Triangular/Statement.lean`: formal statement and normalization API for the
   triangular block entropy inequality.
4. Future modules will prove the logarithmic-determinant convexity lemma,
   scalar Jensen reduction, the triangular theorem, the amplitude-damping roof
   formula, and finally the EoF/channel corollaries.

The project does not use `sorry` or introduce axioms for the mathematical
claims.  Work-in-progress theorems are represented as named predicates until
their proofs are supplied.
