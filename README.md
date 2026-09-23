# Classical Capacity of the Qubit Amplitude-Damping Channel

This Lean 4 library formalizes the strong-additivity argument for the
qubit amplitude-damping channel and its consequence for the unassisted
classical capacity. The development is based on Lean-QIT and mathlib.

The main checked conclusion is that, for every physical damping parameter
`p ∈ [0,1]`, the regularized Holevo information and the HSW classical
capacity reduce to the one-letter Holevo information, which in turn is an
attained scalar maximum over the input excitation.

## Contents

- `AmplitudeDamping/Channel.lean` defines the channel from its Kraus
  operators and proves its entrywise action.
- `AmplitudeDamping/FixedExcitation.lean` through
  `AmplitudeDamping/EqualExcitation.lean` establish the exact one-qubit
  output-entropy roof formula.
- `AmplitudeDamping/Triangular/` contains the matrix-analytic triangular
  entropy inequality, including the rectangular case.
- `AmplitudeDamping/StrongSuperadditivity.lean` proves strong
  superadditivity of the output-entropy roof against an arbitrary finite
  auxiliary channel.
- `AmplitudeDamping/RoofProduct.lean` and `AmplitudeDamping/NCopy.lean`
  prove product additivity and the finite-copy recursion.
- `AmplitudeDamping/HolevoCapacity.lean` proves optimized strong Holevo
  additivity.
- `AmplitudeDamping/OneLetterCapacity.lean` and
  `AmplitudeDamping/ScalarCapacity.lean` reduce the optimization to a
  one-dimensional attained maximum.
- `AmplitudeDamping/CapacityBridge.lean` connects these results to
  Lean-QIT's block Holevo information, regularization, and formal HSW
  classical-capacity theorem.
- `AmplitudeDamping.lean` is the public root import.

`STATUS.md` records the exact boundary between machine-checked results and
work that remains outside the present library.

## Lean-QIT dependency

The project uses Lean-QIT at the pinned revision
`da54e3070298468dc884877726bc45a92c57e4b3` and Lean/mathlib `v4.30.0`.
The public Git dependency is recorded in `lakefile.toml`; no machine-specific
path is required.

## Manuscript-to-Lean correspondence

The numbering below follows `v2.tex` (September 2026). **Checked** means an
unconditional Lean proof of the indicated result. **Conditional formalization**
means Lean checks the implication from the explicit, currently unproved
`woottersKernelUpperBound` proposition. **Partial formalization** means only
the specified part or a narrower special case is checked. A Lean definition
or a proof conditional on that proposition is not a proof of the full
unconditional manuscript claim.

| Manuscript result | Principal Lean module / declaration | Status |
| --- | --- | --- |
| Theorem 4.1 (`thm:support`), finite-dimensional support criterion | [`EntanglementSSA.lean`](AmplitudeDamping/EntanglementSSA.lean), [`LocalUnitary.lean`](AmplitudeDamping/LocalUnitary.lean) | Partial formalization: the two-qubit product-kernel case is conditional; the arbitrary-dimensional theorem is absent. |
| Theorem 4.2 (`thm:triangle`), triangular block entropy inequality | [`Triangular/Rectangular.lean`](AmplitudeDamping/Triangular/Rectangular.lean), `triangularBlockEntropyInequality` | Checked. |
| Lemma 4.3 (`lem:two-moments`), two-expectation pure decomposition | — | Not formalized. |
| Corollary 4.4 (`cor:state-examples`), two-qubit product-kernel additivity and state cost | [`RankTwoKernel.lean`](AmplitudeDamping/RankTwoKernel.lean), [`EntanglementAdditivity.lean`](AmplitudeDamping/EntanglementAdditivity.lean), [`EntanglementCost.lean`](AmplitudeDamping/EntanglementCost.lean) | Conditional formalization of the E_F and regularized-cost identities; the operational state-cost bridge is absent. |
| Corollary 5.1 (`cor:stinespring`), support criterion for strong Holevo additivity | [`StinespringEOF.lean`](AmplitudeDamping/StinespringEOF.lean), [`HolevoReduction.lean`](AmplitudeDamping/HolevoReduction.lean) | Partial formalization: the MSW roof identity is checked; the general support criterion is absent. |
| Corollary 5.2 (`cor:two-kraus`), two-Kraus qubit channels | [`TwoKrausRoof.lean`](AmplitudeDamping/TwoKrausRoof.lean), [`TwoKrausCapacity.lean`](AmplitudeDamping/TwoKrausCapacity.lean) | Conditional formalization of roof/Holevo additivity and `C(N) = χ(N)`; the full capacity additivity statement is not packaged. |
| Lemma 5.3 (`lem:flat-roof`), fixed-input amplitude-damping roof | [`EqualExcitation.lean`](AmplitudeDamping/EqualExcitation.lean), `outputEntropyRoof_eq_dampingEntropyCurve_of_convex` | Checked. |
| Theorem 5.4 (`thm:damping-capacity`), classical capacity of amplitude damping | [`ScalarCapacity.lean`](AmplitudeDamping/ScalarCapacity.lean), [`CapacityBridge.lean`](AmplitudeDamping/CapacityBridge.lean) | Checked for `C(A_p) = χ(A_p)` and the attained scalar maximum; the explicit optimal-signal/coding statement is not packaged as one theorem. |
| Proposition 5.5 (`prop:deficit`), finite-block Holevo deficit and unique average input | — | Not formalized. |
| Theorem 6.1 (`thm:two-kraus-unified`), channel formation and parallel simulation additivity | [`TwoKrausCapacity.lean`](AmplitudeDamping/TwoKrausCapacity.lean), [`EntanglementCost.lean`](AmplitudeDamping/EntanglementCost.lean) | Partial formalization: the classical-capacity part is conditional and some state identities are conditional; channel formation and operational simulation are absent. |
| Corollary 6.2 (`cor:pure-output`), channels admitting a pure output | — | Not formalized. |
| Theorem 6.3 (`thm:ad-cost`), amplitude-damping channel entanglement cost | [`ChoiState.lean`](AmplitudeDamping/ChoiState.lean), [`EntanglementCost.lean`](AmplitudeDamping/EntanglementCost.lean) | Partial formalization: the Choi E_F formula and its regularized state-cost identity are conditional; the operational channel-cost identity is absent. |
| Proposition 6.4 (`prop:binary-instrument`), uniform binary Kraus bound | — | Not formalized. |
| Appendix Lemma A.1 (`lem:logdet`), log-determinant convexity | [`Triangular/LogDetCalculus.lean`](AmplitudeDamping/Triangular/LogDetCalculus.lean), `skewLogDetIncrement_convexOn_posDef` | Checked. |
| Appendix Proposition A.2 (`prop:triangle-equality`), equality conditions | — | Not formalized. |
| Appendix Lemma C.1 (`lem:uniform-kraus`), uniform Kraus representation | — | Not formalized. |
| Appendix Lemma C.2 (`lem:channel-subadditivity`), channel E_F subadditivity | — | Not formalized. |

The operational channel-simulation regularization theorem cited in §6 and
the operational state-cost theorem are not supplied by the pinned Lean-QIT
dependency. The local `entanglementCost` definition is a regularized E_F
quantity, not an operational LOCC simulation cost. The mean-excitation
constrained fixed-input and ensemble bounds are checked in
[`ExcitationConstraint.lean`](AmplitudeDamping/ExcitationConstraint.lean);
an operational constrained coding theorem is not included.

## Reproduction

Install the Lean toolchain specified in `lean-toolchain`, then run:

```bash
lake update
lake build
```

The library deliberately has no remote CI workflow; it is intended to remain
a pure Lean library whose proofs can be checked locally with Lake.

## Trust boundary

The project contains no `sorry` proof terms and introduces no project-defined
axioms. It relies on Lean's kernel, mathlib, and the pinned Lean-QIT revision.
The v2 correspondence table above identifies unfinished extensions. The
explicit `woottersKernelUpperBound` premise is tracked in the Lean statements
that use it; it is not asserted as an axiom. `STATUS.md` gives the detailed
status of the earlier formalization.
