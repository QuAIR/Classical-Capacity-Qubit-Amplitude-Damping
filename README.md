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
14. `Triangular/EntropyIntegral.lean`: checked finite-cutoff spectral
    logarithm integral, cancellation at infinity for equal trace, and the
    matrix log-determinant entropy-integral limit, including singular
    positive semidefinite matrices.  It also proves block-diagonal entropy
    additivity, identifies the padded integral with the manuscript entropy
    defect, integrates pointwise convexity, and proves the full fixed-middle
    convexity theorem on the semidefinite cone.
15. `Triangular/Dephasing.lean`: checked unitary covariance of positive square
    roots and spectral entropy, invariance of the entropy defect, the finite
    diagonal-sign twirl, its exact identification with basis dephasing, and
    the Jensen proof that dephasing the two outer blocks cannot increase the
    fixed-diagonal-middle entropy defect.
16. `Triangular/ScalarCompression.lean`: checked entropy additivity for finite
    homogeneous block diagonals, positive square roots of real diagonal
    matrices, coordinatewise scalarization of the diagonal entropy coupling,
    the exact decomposition of a diagonal entropy defect into scalar defects,
    positive homogeneity, and scalar perspective Jensen when all middle
    coordinates are strictly positive.
17. `Triangular/ScalarBoundary.lean`: checked continuity of spectral entropy
    along positive-semidefinite matrix paths and the limiting argument that
    extends scalar perspective Jensen to zero middle coordinates.
18. `Triangular/TraceCompression.lean`: checked diagonal scalar compression,
    dephasing for arbitrary outer matrices, spectral diagonalization of the
    middle matrix, and the full PSD matrix trace-compression theorem.
19. `Triangular/ScalarNormalization.lean`: checked the scalar coupling
    determinant and its exact identification with the normalized qubit
    entanglement curve, the resulting scalar-defect formula, and the
    normalized entropy lower bound for the canonical square-root factor.
20. `Triangular/GramEntropy.lean`: checked equality of the two square Gram
    entropies and the exact zero-weight-safe conversion from unnormalized
    Gram entropy to `normalizedGramEntropy` for arbitrary rectangular blocks.
21. `Triangular/PolarGauge.lean`: checked the exact block-matrix gauge
    identity converting unitary polar factors of square triangular blocks to
    the canonical entropy coupling.
22. `Triangular/SquarePolar.lean`: checked the full normalized entropy
    inequality for square triangular blocks, conditional only on supplied
    unitary polar factors for the two lower-row blocks.
23. Future modules will supply the polar-factor existence and rectangular
    isometric embeddings, then derive the EoF/channel corollaries.

The project does not use `sorry` or introduce axioms for the mathematical
claims.  Work-in-progress theorems are represented as named predicates until
their proofs are supplied.
