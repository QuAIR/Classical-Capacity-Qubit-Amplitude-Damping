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
- [x] Hilbert--Schmidt estimate `|Tr(X²)| ≤ ‖X‖_F²` for arbitrary complex
  square matrices.
- [x] The skew-resolvent contraction
  `((I+A)⁻¹)ᴴ(I+A)⁻¹ ≤ I` for `Aᴴ = -A`, including nonsingularity of
  `I+A`.
- [x] Nonnegativity of the normalized log-determinant Hessian expression
  `‖E‖_F² - Re Tr((((I+A)⁻¹E)²))`.
- [x] Polynomial proof of Jacobi's formula for the derivative of the
  determinant along an invertible real affine matrix path.
- [x] First-derivative formula
  `d/dt log |det(M+tH)| = Re Tr((M+tH)⁻¹H)`.
- [x] Inverse-path derivative and the resulting second-derivative identity for
  a difference of two affine matrix log-determinants.
- [x] Positive-definite square-root normalization of the Hessian and its
  pointwise nonnegativity for Hermitian directions and skew-Hermitian
  perturbations.
- [x] Nonsingularity of `G + J` for positive-definite `G` and skew-Hermitian
  `J`.
- [x] Convexity along every positive-definite line segment, including the
  closed-interval continuity and calculus endpoint obligations.
- [x] Full matrix-level log-determinant convexity lemma:
  `G ↦ log |det(G+J)| - log |det G|` is convex on the positive-definite cone.
- [x] Gram factorization `Z(P,Q,R) = LᴴL`, positivity of `Z`, and
  `Tr Z = Tr P + Tr Q + Tr R`.
- [x] The Schur-complement identity
  `det(Z(P,Q,R)+sI) = det(G_s(P,R)+J_s(Q))` for every `s > 0`.
- [x] Joint convexity in `(P,R)` of the fixed-middle shifted log-determinant
  integrand for every positive integral parameter `s`.
- [x] Exact finite-cutoff formula for the integral of the difference of two
  finite spectral log-resolvents.
- [x] Cancellation at infinity of all divergent spectral terms under the
  equal-mass/equal-trace hypothesis.
- [x] Matrix log-determinant entropy-integral limit for positive semidefinite
  matrices of equal trace, including singular matrices.
- [x] Exact pointwise identification of the padded entropy-integral
  log-determinant difference with the fixed-middle skew integrand.
- [x] Interval integrability and joint convexity of every finite truncated
  fixed-middle integral, including lower endpoint zero modulo its null set.
- [x] Functional-calculus proof that `psdEntropy` is additive on
  unequal-dimensional positive semidefinite block diagonals.
- [x] Equality between the padded entropy defect and the manuscript function
  `F(P,Q,R) = H(Z(P,Q,R)) - H(P) - H(Q) - H(R)`.
- [x] Full fixed-middle joint convexity of `F(P,Q,R)` in `(P,R)` on the
  positive semidefinite cone, obtained by passing the truncated inequalities
  through the entropy-integral limit.
- [x] Ambient-space totalization of the entropy defect and a checked finite
  Jensen inequality, ready for the sign-unitary dephasing average.
- [x] Unitary covariance of the positive square root and unitary invariance of
  the positive-semidefinite spectral entropy.
- [x] Simultaneous-unitary invariance of the entropy coupling and entropy
  defect, including invariance under stabilizers of the fixed middle block.
- [x] Exact finite sign-unitary twirl identity: averaging all diagonal sign
  conjugations removes precisely the off-diagonal entries.
- [x] Positive-semidefiniteness of basis dephasing and the Jensen inequality
  showing that dephasing both outer arguments cannot increase the entropy
  defect when the middle argument is diagonal.
- [x] Positive-semidefiniteness and spectral-entropy additivity for arbitrary
  finite homogeneous block diagonals.
- [x] Exact coordinatewise block decomposition of the entropy coupling for
  nonnegative real diagonal inputs, including the finite basis relabeling.
- [x] Exact formula expressing a diagonal entropy defect as the sum of its
  one-dimensional scalar entropy defects.
- [x] Positive homogeneity of the full matrix entropy defect, including a
  checked spectral-entropy scaling formula and exact cancellation of all
  trace corrections.
- [x] Scalar perspective identity and finite Jensen/trace-compression
  inequality when every middle scalar coordinate is strictly positive.
- [x] Continuity of spectral entropy along arbitrary continuous
  positive-semidefinite matrix paths, including singular boundary points.
- [x] Extension of scalar perspective Jensen to all nonnegative middle
  coordinates by a checked strictly-positive perturbation and limit argument.
- [x] Full matrix trace compression
  `F(P,Q,R) ≥ f(Tr P, Tr Q, Tr R)` for arbitrary finite-dimensional positive
  semidefinite matrices, using dephasing and spectral diagonalization.
- [x] Exact normalized scalar formula: the trace-one scalar coupling has
  determinant `p*r`, entropy `entanglementCurve (2*sqrt(p*r))`, and the
  corresponding scalar entropy defect has the required `xlog2` corrections.
- [x] Normalized triangular entropy lower bound for the canonical
  lower-triangular square-root factor `[[sqrt P, 0], [sqrt Q, sqrt R]]`.
- [x] Equality of `H(AᴴA)` and `H(AAᴴ)` for square matrices, and the exact
  zero-weight-safe identity converting `H(AAᴴ)` to `normalizedGramEntropy`
  plus its scalar `xlog2` correction for arbitrary rectangular matrices.
- [x] Exact polar-gauge block identity for square triangular matrices, given
  unitary polar factors for the two lower-row blocks.
- [x] Full normalized triangular entropy inequality for square blocks,
  conditional only on supplied unitary polar factors for the two lower-row
  blocks; all Gram-spectrum, unitary-invariance, and normalization corrections
  are discharged.
- [x] Existence of a unitary left polar factor for every finite square complex
  matrix, including singular matrices, via Lean-QIT's Gram-factorization and
  finite-dimensional isometry-extension theorem; consequently the square
  triangular entropy inequality is unconditional.
- [x] Rectangular-isometry invariance of positive spectral entropy, together
  with exact preservation of Frobenius norm and normalized Gram entropy under
  coordinate zero padding.
- [x] Full arbitrary-rectangular triangular block entropy inequality.  The
  proposition `TriangularBlockEntropyInequality` now has the checked theorem
  `triangularBlockEntropyInequality`.
- [x] Exact amplitude-damping specialization
  `[[sqrt(1-p) A, 0], [B, sqrt(p) A]]`, including homogeneity of normalized
  Gram entropy and the zero-weight endpoint cases.
- [x] A canonical chosen Stinespring isometry for every finite channel, with
  checked identities equating its coefficient-matrix Gram to the channel
  output on a rank-one input, its Frobenius weight to the input norm, and its
  normalized Gram entropy to pure-input output entropy.

## Open proof obligations

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
