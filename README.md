# Classical Capacity of the Qubit Amplitude-Damping Channel

A Lean 4 formalization of the manuscript's support criterion, strong
additivity results, amplitude-damping capacity and entanglement-cost formulas,
and matrix entropy inequalities, built on Lean-QIT and mathlib.

**Coverage:** all 18 active numbered manuscript statements have Lean
counterparts. Sixteen have proofs, conditional on the classical interfaces
listed below where indicated. Two classical lemmas are deliberately stated
as interfaces without proofs. This is **not** a claim that all results have
been proved without additional mathematical assumptions.

## Reading the status table

- **Proved:** machine-checked, with no additional unproved classical interface
  beyond the pinned dependencies. Physical parameters and other stated
  mathematical conditions still apply.
- **Conditional:** the complete indicated conclusion is proved from the
  explicitly listed classical interfaces.
- **Interface only:** an exact proposition is defined, but this library does
  not prove it. Downstream users must supply it as a hypothesis.
- Rows with several clauses distinguish their statuses individually.

Labels refer to the expanded manuscript identified in
[PAPER_COVERAGE.md](PAPER_COVERAGE.md), rather than potentially stale theorem
numbers. The source fingerprint, detailed correspondence, and minimal
hypotheses of the main results are recorded there.

## Status of every manuscript result

The dependency codes **T, Q, U, S, P, H, K** are defined in the next section.

| Manuscript label and result | Lean implementation / entry point | Status and remaining classical dependencies |
| --- | --- | --- |
| `thm:support` — general finite-dimensional support criterion | [SupportConsequences](AmplitudeDamping/SupportConsequences.lean): `support_criterion_of_distinguished_vectors`, `support_product_additivity_of_distinguished_vectors`, `support_operational_cost_of_distinguished_vectors`; [SupportSSA](AmplitudeDamping/SupportSSA.lean) | **Conditional:** strong superadditivity, product additivity and tensor powers use **T**; operational state cost also uses **S**. Includes intrinsic distinguished-vector support and transport to arbitrary local coordinates. |
| `thm:triangle` — triangular block entropy inequality | [Triangular/Rectangular](AmplitudeDamping/Triangular/Rectangular.lean): `triangularBlockEntropyInequality` | **Proved:** arbitrary rectangular blocks, including zero weights. |
| `lem:two-moments` — pure decomposition preserving two expectations | [TwoExpectations](AmplitudeDamping/TwoExpectations.lean): `TwoExpectationDecomposition` | **Interface only (T):** finite decomposition, positive weights, support membership and both Hermitian expectations are stated explicitly. The general classical proof is deferred. |
| `cor:state-examples` — two-qubit product-kernel and rank-two states | [CornerFromTwoExpectations](AmplitudeDamping/CornerFromTwoExpectations.lean), [EntanglementAdditivity](AmplitudeDamping/EntanglementAdditivity.lean), [EntanglementCost](AmplitudeDamping/EntanglementCost.lean), [SupportConsequences](AmplitudeDamping/SupportConsequences.lean) | **Conditional:** corner formula, state additivity and powers use **T**; operational cost also uses **S**. Rank-two product-kernel existence is **proved**. Full Wootters is not an extra hypothesis on this route. |
| `cor:stinespring` — supported dilations imply communication additivity | [SupportStinespring](AmplitudeDamping/SupportStinespring.lean): `outputEntropyRoof_prod_ge_of_supported_stinespring`, `supported_stinespring_classicalCapacity_prod_eq` | **Conditional (T):** roof superadditivity, strong Holevo additivity, single-letter capacity and arbitrary-partner operational capacity additivity. General finite input, output and environment dimensions. |
| `lem:pure-output-stinespring` — pure output iff supported dilation | [PureOutputSupport](AmplitudeDamping/PureOutputSupport.lean): `pure_output_iff_split_stinespring_support`; [PureOutputChoi](AmplitudeDamping/PureOutputChoi.lean): `pure_output_iff_choi_product_kernel` | The geometric equivalences are **proved**, including arbitrary finite environments. The resulting communication conclusions are **conditional on T**. |
| `cor:two-kraus` — qubit channels with at most two Kraus operators | [PureOutputChoi](AmplitudeDamping/PureOutputChoi.lean): `twoKraus_has_pure_output`; [TwoKrausCapacity](AmplitudeDamping/TwoKrausCapacity.lean), [CapacityAdditivity](AmplitudeDamping/CapacityAdditivity.lean) | Pure-output existence is **proved**. Roof/Holevo additivity, capacity collapse and arbitrary-partner capacity additivity are **conditional on T**; the legacy corner premise is derived from T. |
| `lem:flat-roof` — exact fixed-input AD entropy roof | [EqualExcitation](AmplitudeDamping/EqualExcitation.lean): `outputEntropyRoof_eq_dampingEntropyCurve` | **Proved:** all physical inputs and damping endpoints. |
| `thm:damping-capacity` — AD scalar capacity and optimal binary signals | [ScalarCapacity](AmplitudeDamping/ScalarCapacity.lean), [ScalarOptimizer](AmplitudeDamping/ScalarOptimizer.lean), [OptimalSignals](AmplitudeDamping/OptimalSignals.lean), [CapacityAdditivity](AmplitudeDamping/CapacityAdditivity.lean), [ProductSignalCoding](AmplitudeDamping/ProductSignalCoding.lean) | Scalar maximum, optimizer, explicit binary ensemble, endpoint capacities and arbitrary-partner capacity additivity are **proved**. The exact binary-product-codeword achievability clause is **conditional on H**. Unrestricted operational capacity uses the already-proved upstream HSW theorem. |
| `prop:deficit` — finite-block deficit, information radius and unique average input | [FiniteBlockDeficit](AmplitudeDamping/FiniteBlockDeficit.lean): `amplitudeDamping_exact_deficit_relativeEntropy`, `amplitudeDamping_relativeEntropy_radius_bound`, `amplitudeDamping_optimal_average_iff` | Exact three-term identity, all nonnegative terms, information radius and optimal-product attainment are **proved**. Uniqueness of the optimal average input for `p < 1` is **conditional on K**. |
| `thm:two-kraus-unified` — unified communication, formation and cost results | [PaperTheorems](AmplitudeDamping/PaperTheorems.lean): `Paper.twoKraus_additivity`, `Paper.twoKraus_single_letter_and_powers` | **Conditional:** communication uses **T**; general channel formation additivity uses **T + Q + U**; parallel operational cost also uses **P**, and operational Choi-state cost uses **S**. Exact finite-copy channel/state formation identities are included. |
| `cor:pure-output` — all pure-output qubit channels | [PaperTheorems](AmplitudeDamping/PaperTheorems.lean): `Paper.pure_output_additivity`, `Paper.pure_output_single_letter_and_powers` | **Conditional:** the same dependencies as the unified two-Kraus row. No Kraus-rank-two restriction: applies to every pure-output qubit channel and every finite-dimensional partner. |
| `thm:ad-cost` — AD state/channel formation and operational costs | [ADDirectCost](AmplitudeDamping/ADDirectCost.lean), [PaperTheorems](AmplitudeDamping/PaperTheorems.lean): `Paper.amplitudeDamping_cost_formula`, `Paper.amplitudeDamping_powers`, `Paper.amplitudeDamping_cost_additivity` | One-copy Choi and channel formation formulas are **proved**. Exact powers use **T**; own operational state/parallel costs use **T + S/P**, respectively. Arbitrary-partner formation additivity uses **T + U**, and parallel-cost additivity also uses **P**. **Q is unnecessary for AD; U is unnecessary for its own powers/cost formula.** |
| `prop:binary-instrument` — explicit uniform binary Kraus bound | [BinaryInstrument](AmplitudeDamping/BinaryInstrument.lean), [InstrumentProduct](AmplitudeDamping/InstrumentProduct.lean), [UniformKraus](AmplitudeDamping/UniformKraus.lean): `amplitudeDamping_tensorPower_channelFormation_le` | **Proved:** exact one-use maximum, actual two-Kraus channel realization, and uniform bound for arbitrary correlated inputs at every block length. No uniform-Kraus interface is needed for this explicit construction. |
| `lem:logdet` — skew log-determinant convexity | [Triangular/LogDetCalculus](AmplitudeDamping/Triangular/LogDetCalculus.lean): `skewLogDetIncrement_convexOn_posDef` | **Proved.** |
| `prop:triangle-equality` — equality for invertible middle block | [TriangleEquality](AmplitudeDamping/TriangleEquality.lean): `square_triangular_entropy_equality_iff`, `square_triangular_entropy_equality_iff_four_unitaries` | **Proved:** necessary and sufficient Gram conditions and the literal Kronecker normal form with arbitrary block-diagonal row/column unitaries. Strict convexity is proved, not assumed. |
| `lem:uniform-kraus` — uniform finite Kraus representation/minimax | [UniformKraus](AmplitudeDamping/UniformKraus.lean): `UniformKrausRepresentation`, `GeneralUniformKrausRepresentation` | **Interface only (U):** the manuscript's equivalent finite, uniformly ε-optimal representation statement is explicit. The general classical minimax proof is deferred. |
| `lem:channel-subadditivity` — general channel formation subadditivity | [UniformKraus](AmplitudeDamping/UniformKraus.lean): `generalChannelFormationSubadditivity_of_uniformKraus` | **Conditional on U:** the Kraus pure-decomposition bound, correlated product-instrument entropy inequality and ε-limit application are proved here. Additivity itself is not assumed. |

## Classical interfaces that remain unproved

These are hypotheses in theorem types, **not project-defined axioms**.
Their scopes are generic classical statements, not AD-specific conclusions.

| Code | Exact Lean interface | What is assumed |
| --- | --- | --- |
| **T** | [TwoExpectationDecomposition](AmplitudeDamping/TwoExpectations.lean) | Leka–Petz finite pure decomposition preserving two Hermitian expectations inside the state's support. |
| **Q** | [QubitChannelFormationIdentity](AmplitudeDamping/ChannelFormation.lean) | For every qubit-to-qubit channel, independently optimized channel formation equals the formation of its normalized Choi state. |
| **U** | [GeneralUniformKrausRepresentation](AmplitudeDamping/UniformKraus.lean) | For every finite-dimensional channel and positive tolerance, one finite Kraus representation has entropy cost uniformly within that tolerance of channel formation (BBCW Lemma 14). |
| **S** | [StateCostRegularization](AmplitudeDamping/OperationalEntanglementCost.lean) | Operational LOCC state preparation cost equals regularized state formation, including nonemptiness of achievable rates. |
| **P** | [ParallelCostRegularization](AmplitudeDamping/OperationalEntanglementCost.lean) | Operational parallel LOCC channel simulation cost equals regularized channel formation, including nonemptiness of achievable rates. |
| **H** | [ProductSignalHSW](AmplitudeDamping/ProductSignalCoding.lean) | Fixed-ensemble HSW achievability retaining actual tensor-product encoder membership and collective decoding. The public upstream capacity predicate forgets this membership. |
| **K** | [FaithfulRelativeEntropyEquality](AmplitudeDamping/FiniteBlockDeficit.lean) | With a faithful reference state, zero quantum relative entropy implies equality of states. Used only for optimal-average uniqueness. |

The pinned Lean-QIT HSW capacity characterization is already proved and is
reused. Full Wootters is not separately assumed:
`woottersKernelUpperBound_of_twoExpectations` derives the legacy corner
interface from **T**. Likewise, the main entry points discharge the generic
`GeneralChannelFormationSubadditivity` premise from **U**.

Operational costs are defined independently from finite-round LOCC protocols,
maximally entangled resources and vanishing trace/diamond-distance error.
They are not defined to equal the regularized formation quantities.

## Entry points and scope

- [AmplitudeDamping.lean](AmplitudeDamping.lean) imports the complete library.
- [PaperTheorems.lean](AmplitudeDamping/PaperTheorems.lean) groups the main
  communication, formation, operational-cost and power conclusions.
- [PAPER_COVERAGE.md](PAPER_COVERAGE.md) records detailed dependencies and the
  manuscript fingerprint; [STATUS.md](STATUS.md) retains the earlier
  foundation checklist.
- Unnumbered illustrative examples are outside the numbered-result coverage
  claim. Mean-excitation fixed-input/ensemble bounds are in
  [ExcitationConstraint.lean](AmplitudeDamping/ExcitationConstraint.lean);
  the operational constrained coding theorem remains a separate extension.

## Reproduction and verification

The project pins Lean-QIT to
`da54e3070298468dc884877726bc45a92c57e4b3` and Lean/mathlib to `v4.30.0`.
The public Git dependency is in `lakefile.toml`; no machine-specific path is
required. With the toolchain from `lean-toolchain` installed, run:

```bash
lake build
lake env lean Audit.lean
```

The complete build passes (3662 jobs). The audit checks 1433 public project
theorems and permits only `propext`, `Classical.choice` and `Quot.sound` as
transitive axioms. There are no `sorry` proof terms or project-defined axioms.
Existing foundation modules retain their style warnings; the new modules
compile without warnings.

**An axiom audit does not detect explicit theorem hypotheses.** Read the
status and interface tables above alongside the audit. The library has no
remote CI workflow; verification is performed locally with Lake.
