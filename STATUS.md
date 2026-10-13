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
- [x] The convex roof is a lower envelope for arbitrary finite ensembles of
  mixed states, and the amplitude-damping product-channel Holevo converse
  holds for every finite input ensemble.
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
- [x] Pure-input qubit branch decomposition for an arbitrary auxiliary
  channel: the branch weights are exactly the qubit marginal excitation and
  its complement, and the amplitude-damping triangular coefficient bound is
  instantiated for the resulting Stinespring blocks.
- [x] Unconditional strong superadditivity of the amplitude-damping
  output-entropy roof against every finite-dimensional auxiliary channel.
- [x] Product-decomposition construction and exact roof additivity on product
  inputs when one factor is amplitude damping.
- [x] Recursive lower bound for arbitrary correlated `n`-copy inputs and exact
  IID identity `R(A_p^⊗n, ρ^⊗n) = n R(A_p, ρ)`.
- [x] Exact additivity of the associated fixed-input Holevo quantity on
  product states.
- [x] Product-ensemble lower bound and optimized strong Holevo additivity
  `χ(A_p ⊗ Φ) = χ(A_p) + χ(Φ)` for every finite-dimensional auxiliary
  channel with nonempty input system.
- [x] General one-letter variational identity equating optimized finite-
  ensemble Holevo information with the state supremum of output entropy
  minus the exact output-entropy convex roof.
- [x] Exact reduction of amplitude-damping Holevo information to the scalar
  excitation curve on `[0,1]`, including continuity, boundedness, and
  attainment of the maximum.
- [x] Exact finite-block identity
  `χ(A_p^⊗n) = n χ(A_p)` for every positive block length.
- [x] Collapse of regularized Holevo information to the single-letter
  quantity for amplitude damping.
- [x] Identification, through Lean-QIT's formal HSW theorem, of the classical
  capacity with the single-letter Holevo information.
- [x] Final bridge from classical capacity to an attained scalar maximum over
  the excitation interval `[0,1]`.
- [x] Mean-excitation constrained capacity variant (manuscript §4.4): the
  finite-block bound iterating strong superadditivity of the output-entropy
  roof over site marginals, concavity of the scalar information curve
  `F_p(q) = h₂((1-p)q) - g_p(q)`, the Jensen converse
  `χ ≤ n max_{[0,ν]} F_p` under `∑ q_i ≤ nν`, attainment at diagonal product
  inputs, the variational supremum identity, and the mixed-codeword ensemble
  version.  The operational coding layer (Fano/HSW under codeword
  constraints) follows the formal HSW theorem's unconstrained argument and is
  not repeated.
- [x] Wootters corner-formula interface: the `≤` direction of eq
  `(three-corner-eof)` packaged as the explicit hypothesis
  `woottersKernelUpperBound` (the `≥` direction is proved in
  `Concurrence.lean`), giving the corner identity in diagonal-entry and
  kernel-vector phrasings for the gauge-fixed setting of Theorem 6.
- [x] Entanglement of formation as a convex roof over finite pure-state
  decompositions, the kernel-state lower bound, rank-two product-kernel
  support for two-qubit states, and subadditivity under reassociated tensor
  products (Corollary 7, `≤` direction).
- [x] Theorem 6 (gauge-fixed): `E_F(ρ_AB) + E_F(σ_A'B') ≤ E_F(Ω)` whenever
  the two-qubit marginal has vanishing `|01⟩` population.  Pure case via the
  coefficient-matrix block factorization, the triangular block entropy
  inequality, the Wootters corner hypothesis, and Cauchy–Schwarz on the
  coherence; mixed case by branchwise propagation of the gauge condition to
  every positive-weight branch and finite-Jensen convexity of `E_F`.
- [x] MSW Stinespring roof identity (manuscript eq (msw)): for every channel
  `Φ` and input state `τ`, `roof(Φ, τ) = E_F(V τ V†)` for the canonical
  Kraus-indexed Stinespring dilation state, with no hypotheses.  The
  backward direction uses the full support argument (a branch vector outside
  the kernel pulls back through `V†` to a valid preimage branch).
- [x] Choi-state entanglement of formation (manuscript eq (31), elementary
  route): the amplitude-damping Choi state `ω_p = ½(|ψ₊⟩⟨ψ₊| + |ψ₋⟩⟨ψ₋|)` has
  a full 16-entry matrix computation, a vanishing `|01⟩` population,
  `E_F(ω_p) = entanglementCurve(√(1-p)) = h₂((1+√p)/2)`, an explicit optimal
  two-branch decomposition attaining the value (making the upper bound
  unconditional), and the endpoints `E_F(ω_0) = 1`, `E_F(ω_1) = 0`.
- [x] Invariance of `E_F` under local isometries (`V ρ V†` for
  `TwoQubit.LocalIsometry` pairs), proved for arbitrary rectangular
  isometries: `≤` by decomposition pushforward, `≥` by a range-projection
  pullback showing positive-weight branches of any decomposition of the
  image lie in the isometry's range.
- [x] Theorem 6, full form: a product kernel vector `u ⊗ v ∈ ker ρ_AB`
  implies `E_F(ρ_AB) + E_F(σ_A'B') ≤ E_F(Ω)`.  The gauge unitary sends
  `u ↦ ‖u‖·|0⟩` (and `v ↦ ‖v‖·|1⟩` via the swap), the local-unitary
  image of `Ω` is gauge-fixed, and Theorem 6 (gauge-fixed) applies; E_F
  invariance transports the conclusion back.
- [x] Corollary 7 (strong additivity of `E_F`): for a two-qubit `ρ` with a
  nonzero product kernel vector and every bipartite `σ`,
  `E_F((ρ · σ) reassociated to AA':BB') = E_F(ρ) + E_F(σ)`; in particular
  for every two-qubit state of rank at most two.  The `≤` half is the
  committed reassociation lemma; the `≥` half applies full-form Theorem 6
  to the reassociated product.
- [x] Entanglement cost layer (manuscript eq (ec-definition), (choi-cost)):
  per-side reindex invariance of `E_F`; the `n`-copy identity
  `E_F(ρ^⊗n) = n · E_F(ρ)` for product-kernel states; the regularized cost
  `entanglementCost` defined as the infimum of `E_F(ρ^⊗n)/n` over `n ≥ 1`
  (a disclosed design choice; the paper's limit form is supplied as a
  `Tendsto` theorem on the constant sequence); `E_C(ρ) = E_F(ρ)` for
  product-kernel and rank-at-most-two states; and the boxed Choi-state
  conclusion `E_F(ω_p^⊗n) = n · h₂((1+√p)/2)` and
  `E_C(ω_p) = h₂((1+√p)/2)` for all `p ∈ [0,1]`.
- [x] Corollary 8, fixed-input roof superadditivity (eq (two-kraus-roof)):
  for a qubit channel `N` admitting a Kraus family indexed by a type of
  cardinality at most two (with the Kraus-stack isometry, its qubit-
  environment padding, completeness, and the rank bridge
  `card_filter_eigenvalues_eq_rank` into the rank-two kernel-vector
  theorem), `roof(N ⊗ M)(τ) ≥ roof(N)(τ_X) + roof(M)(τ_Y)` for every
  finite-dimensional channel `M` and input state `τ`.  The engine is the
  generalized MSW identity `roof(Φ)(τ) = E_F(V τ V†)` for an ARBITRARY
  isometry dilation `V` (both directions: decomposition pushforward and
  range-projection pullback), which also subsumes the canonical-dilation
  version.
- [x] Corollary 8, Holevo additivity and capacity collapse
  (eq (two-kraus-holevo)): from the roof superadditivity packaged as an
  explicit hypothesis, `χ(N ⊗ M) = χ(N) + χ(M)` for every auxiliary channel
  with nonempty input, the `n`-copy identity in the regularized-rate
  convention, regularization collapse, and `C(N) = χ(N)` for two-Kraus
  qubit channels.

## Full-manuscript extension

The numbered checklist above records the earlier manuscript revision; it is
not a coverage claim for the expanded manuscript. The current label-by-label
status and exact external hypotheses are in [PAPER_COVERAGE.md](PAPER_COVERAGE.md).

New checked modules cover the optimal binary signal ensemble and endpoints,
arbitrary-partner operational capacity additivity, the unique scalar optimizer
and exact finite-block deficit, general single-excitation support SSA and
Stinespring consequences, explicit binary instruments and correlated product
bounds, the actual normalized channel Choi state, independently optimized
channel formation, and its tensor-power/regularization consequences.

`OperationalEntanglementCost.lean` defines finite-round LOCC protocols and
resource-assisted state preparation / parallel simulation independently of
formation. The classical state/channel regularization theorems remain explicit
hypotheses. `UnifiedCost.lean` applies them to the proven formation results.
The main entry points in `PaperTheorems.lean` discharge general subadditivity
using the proved uniform-Kraus application. Remaining coverage details are
tracked in the manuscript ledger.

## Trust boundary

Completed modules contain no `sorry` proof terms or project-defined axioms.
Standard Lean axioms and pinned Lean-QIT/mathlib results are reused. A successful
`#print axioms` audit does not certify that a theorem has no mathematical
hypotheses: those are separately recorded in [PAPER_COVERAGE.md](PAPER_COVERAGE.md).

The old `woottersKernelUpperBound` is a specialized corner upper bound, not
the full Wootters formula. `CornerFromTwoExpectations.lean` now derives it from
the proved two-Hermitian-expectation decomposition theorem. The AD one-copy
Choi formation formula has also been proved without either interface.

The two-expectation decomposition, fixed-signal HSW theorem, uniform Kraus
representation and faithful relative-entropy equality case are now proved,
and their T/H/U/K hypothesis parameters are removed from downstream results.
The U proof includes faithful purification reconstruction, singular-input
approximation, compactness, finite minimax and weighted Kraus mixing. The K
proof uses measurement data processing and strict classical KL equality.
The qubit channel/Choi formation identity is also proved for every qubit
channel. The proof uses attained concurrence roofs, flat optimal ensembles
and exact local-filter factorization, with no Q premise downstream.
Two unproved classical interfaces remain: state cost regularization (S) and
parallel channel cost regularization (P). These are explicit hypotheses,
not project-defined axioms.
Temporary development files are not counted as completed manuscript coverage.
