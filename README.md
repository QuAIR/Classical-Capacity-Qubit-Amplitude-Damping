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
4. `QubitState.lean`: coordinate normal form and coherence bound for arbitrary
   qubit density matrices.
5. `FixedExcitation.lean`: excitation bounds and the checked determinant
   and entropy formulas for the output of a pure qubit input, together with
   the Jensen reduction for the roof lower bound.
6. `ScalarCurve.lean`: checked monotonicity and convexity of the concurrence
   entropy curve and hence of the amplitude-damping scalar curve.
7. `EqualExcitation.lean`: explicit two-pure-state equal-excitation
   decomposition, the unconditional roof upper bound, and the exact roof
   formula.
8. `QubitEntropy.lean`: the checked two-level spectral formula expressing
   qubit entropy in terms of the determinant.
9. `HolevoReduction.lean`: checked reduction from strong superadditivity of
   the roof to the fixed-input and ensemble Holevo converse.
10. `Triangular/Statement.lean`: formal statement and normalization API for the
   triangular block entropy inequality.
11. `Triangular/LogDet.lean`: checked Hilbert--Schmidt trace-square estimate,
    skew-resolvent contraction, and nonnegativity of the normalized
    log-determinant Hessian expression.
12. `Triangular/LogDetCalculus.lean`: checked derivative of complex log-modulus,
    polynomial proof of Jacobi's determinant formula, the first derivative of
    `log |det(M+tH)|`, the inverse-trace second-derivative identity, and the
    resulting convexity theorem on the full positive-definite cone.
13. `Triangular/EntropyReduction.lean`: checked Gram factorization and
    positivity of the coupling matrix `Z(P,Q,R)`, the Schur-complement
    determinant identity, and fixed-middle joint convexity of the shifted
    log-determinant integrand in `(P,R)`.
14. Future modules will finish the improper entropy-integral/dephasing
    reduction and the triangular theorem, and finally prove the EoF/channel
    corollaries.

The project does not use `sorry` or introduce axioms for the mathematical
claims.  Work-in-progress theorems are represented as named predicates until
their proofs are supplied.
