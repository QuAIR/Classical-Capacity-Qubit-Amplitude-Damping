# Formalization status

This file distinguishes machine-checked results from theorem statements and
planned work.  A checked box means that `lake build` elaborates a proof term;
it does not mean that the corresponding result is merely assumed.

## Checked foundations

- [x] Local Lean-QIT dependency pinned at commit `da54e30` with mathlib
  `v4.30.0` (`c5ea0035`).
- [x] Qubit amplitude-damping Kraus operators and their completeness relation.
- [x] Construction of amplitude damping as a CPTP `QIT.Channel`.
- [x] Entrywise formula for the action of amplitude damping.
- [x] Finite pure-state decompositions and the real-infimum definition of the
  output-entropy convex roof.
- [x] Spectral construction of a finite pure-state decomposition for every
  finite-dimensional density state; in particular, the roof's admissible set
  is nonempty and the roof is nonnegative.
- [x] The roof is below the cost of every admissible pure decomposition.
- [x] Entropy subadditivity, derived from Lean-QIT relative-entropy
  nonnegativity and the mutual-information identity.
- [x] Fixed-input and pure-ensemble Holevo converse from strong
  superadditivity of the roof.
- [x] Pure-qubit excitation lies in `[0,1]`.
- [x] Determinant formula
  `det(A_p(|psi><psi|)) = p(1-p)q^2`.
- [x] Qubit spectral lemma: von Neumann entropy is the binary-spectrum function
  of `2 sqrt(det rho)`.
- [x] Pure-input formula `S(A_p(psi)) = g_p(q)` and the Jensen reduction of the
  roof lower bound to convexity of `g_p`.
- [x] Coordinate normal form for every qubit state, including the positivity
  bound `|rho_01|^2 <= q(1-q)`.
- [x] Explicit two-state equal-excitation decomposition for every qubit state.
- [x] Strict monotonicity and convexity of the scalar concurrence entropy
  curve, including checked first- and second-derivative formulas and the
  logarithmic curvature inequality.
- [x] Monotonicity and convexity of `g_p` for every physical damping parameter.
- [x] Unconditional upper bound `roof(A_p, rho) <= g_p(q)` and the exact
  fixed-excitation roof formula `roof(A_p, rho) = g_p(q)`.
- [x] Exact formal statement of the triangular block entropy inequality,
  including the zero-weight convention.

## Open proof obligations

- [ ] Log-determinant convexity lemma in the appendix proof.
- [ ] Dephasing/scalar Jensen reduction and the full triangular block entropy
  inequality.  At present `TriangularBlockEntropyInequality` is a proposition
  naming this target, not a theorem asserting it.
- [ ] Strong superadditivity of the amplitude-damping output-entropy roof.
- [ ] Optimization over input states and the exact one-letter Holevo formula.
- [ ] Product-ensemble lower bound and optimized strong Holevo additivity.
- [ ] Entanglement-of-formation convex roof, product-kernel support theorem,
  Choi-state cost formula, and the two-Kraus qubit-channel corollary.

## Trust boundary

There are no `sorry` proof terms and no project-defined axioms.  The project
uses Lean's standard logic together with the pinned Lean-QIT/mathlib
dependencies.  Pending statements are represented as definitions of
propositions and are listed above rather than being assumed.
