# Classical Capacity of the Qubit Amplitude-Damping Channel

A Lean 4 formalization of the manuscript's support criterion, strong
additivity results, amplitude-damping capacity and entanglement-cost formulas,
and matrix entropy inequalities, built on Lean-QIT and mathlib.

**Coverage:** all 18 active numbered manuscript statements have Lean
counterparts with proofs, conditional on the two classical interfaces
**S, P** where indicated below.

## Reading the status table

- **Proved:** checked with no extra classical interface beyond the pinned dependencies.
- **Conditional (codes):** checked assuming the listed interfaces.

Stated mathematical conditions still apply. Labels and detailed coverage are
recorded in [PAPER_COVERAGE.md](PAPER_COVERAGE.md).

## Status of every manuscript result

The remaining dependency codes **S, P** are defined below.

| Manuscript label and result | Lean implementation / entry point | Status |
| --- | --- | --- |
| `thm:support` — general finite-dimensional support criterion | [SupportConsequences](AmplitudeDamping/SupportConsequences.lean): `support_criterion_of_distinguished_vectors`, `support_product_additivity_of_distinguished_vectors`, `support_operational_cost_of_distinguished_vectors`; [SupportSSA](AmplitudeDamping/SupportSSA.lean) | **Proved** for formation and powers; state cost **conditional (S)**. |
| `thm:triangle` — triangular block entropy inequality | [Triangular/Rectangular](AmplitudeDamping/Triangular/Rectangular.lean): `triangularBlockEntropyInequality` | **Proved**, including rectangular blocks and zero weights. |
| `lem:two-moments` — pure decomposition preserving two expectations | [TwoExpectations](AmplitudeDamping/TwoExpectations.lean): `twoExpectationDecomposition` | **Proved** in every finite dimension. |
| `cor:state-examples` — two-qubit product-kernel and rank-two states | [CornerFromTwoExpectations](AmplitudeDamping/CornerFromTwoExpectations.lean), [EntanglementAdditivity](AmplitudeDamping/EntanglementAdditivity.lean), [EntanglementCost](AmplitudeDamping/EntanglementCost.lean), [SupportConsequences](AmplitudeDamping/SupportConsequences.lean) | **Proved** for formation and powers; state cost **conditional (S)**. |
| `cor:stinespring` — supported dilations imply communication additivity | [SupportStinespring](AmplitudeDamping/SupportStinespring.lean): `outputEntropyRoof_prod_ge_of_supported_stinespring`, `supported_stinespring_classicalCapacity_prod_eq` | **Proved**, including arbitrary-partner capacity additivity. |
| `lem:pure-output-stinespring` — pure output iff supported dilation | [PureOutputSupport](AmplitudeDamping/PureOutputSupport.lean): `pure_output_iff_split_stinespring_support`; [PureOutputChoi](AmplitudeDamping/PureOutputChoi.lean): `pure_output_iff_choi_product_kernel` | **Proved** for arbitrary finite environments. |
| `cor:two-kraus` — qubit channels with at most two Kraus operators | [PureOutputChoi](AmplitudeDamping/PureOutputChoi.lean): `twoKraus_has_pure_output`; [TwoKrausCapacity](AmplitudeDamping/TwoKrausCapacity.lean), [CapacityAdditivity](AmplitudeDamping/CapacityAdditivity.lean) | **Proved**, including arbitrary-partner capacity additivity. |
| `lem:flat-roof` — exact fixed-input AD entropy roof | [EqualExcitation](AmplitudeDamping/EqualExcitation.lean): `outputEntropyRoof_eq_dampingEntropyCurve` | **Proved**, including damping endpoints. |
| `thm:damping-capacity` — AD scalar capacity and optimal binary signals | [ScalarCapacity](AmplitudeDamping/ScalarCapacity.lean), [ScalarOptimizer](AmplitudeDamping/ScalarOptimizer.lean), [OptimalSignals](AmplitudeDamping/OptimalSignals.lean), [CapacityAdditivity](AmplitudeDamping/CapacityAdditivity.lean), [ProductSignalCoding](AmplitudeDamping/ProductSignalCoding.lean) | **Proved**, including endpoints, product-codeword achievability and arbitrary partners. |
| `prop:deficit` — finite-block deficit, information radius and unique average input | [FiniteBlockDeficit](AmplitudeDamping/FiniteBlockDeficit.lean): `amplitudeDamping_exact_deficit_relativeEntropy`, `amplitudeDamping_relativeEntropy_radius_bound`, `amplitudeDamping_optimal_average_iff` | **Proved**; optimal-average uniqueness holds for `p < 1`. |
| `thm:two-kraus-unified` — unified communication, formation and cost results | [PaperTheorems](AmplitudeDamping/PaperTheorems.lean): `Paper.twoKraus_additivity`, `Paper.twoKraus_single_letter_and_powers` | Communication and formation **proved**; parallel cost **conditional (P)**, state cost **(S)**. |
| `cor:pure-output` — all pure-output qubit channels | [PaperTheorems](AmplitudeDamping/PaperTheorems.lean): `Paper.pure_output_additivity`, `Paper.pure_output_single_letter_and_powers` | Communication and formation **proved**; parallel cost **conditional (P)**, state cost **(S)**. |
| `thm:ad-cost` — AD state/channel formation and operational costs | [ADDirectCost](AmplitudeDamping/ADDirectCost.lean), [PaperTheorems](AmplitudeDamping/PaperTheorems.lean): `Paper.amplitudeDamping_cost_formula`, `Paper.amplitudeDamping_powers`, `Paper.amplitudeDamping_cost_additivity` | Formation, powers and arbitrary partners **proved**; state cost **conditional (S)**, parallel cost **(P)**. |
| `prop:binary-instrument` — explicit uniform binary Kraus bound | [BinaryInstrument](AmplitudeDamping/BinaryInstrument.lean), [InstrumentProduct](AmplitudeDamping/InstrumentProduct.lean), [UniformKraus](AmplitudeDamping/UniformKraus.lean): `amplitudeDamping_tensorPower_channelFormation_le` | **Proved** for every block length and correlated input. |
| `lem:logdet` — skew log-determinant convexity | [Triangular/LogDetCalculus](AmplitudeDamping/Triangular/LogDetCalculus.lean): `skewLogDetIncrement_convexOn_posDef` | **Proved.** |
| `prop:triangle-equality` — equality for invertible middle block | [TriangleEquality](AmplitudeDamping/TriangleEquality.lean): `square_triangular_entropy_equality_iff`, `square_triangular_entropy_equality_iff_four_unitaries` | **Proved**, including the four-unitary normal form. |
| `lem:uniform-kraus` — uniform finite Kraus representation/minimax | [UniformKrausTheorem](AmplitudeDamping/UniformKrausTheorem.lean): `uniformKrausRepresentation`, `generalUniformKrausRepresentation` | **Proved** uniformly over all input states. |
| `lem:channel-subadditivity` — general channel formation subadditivity | [UniformKraus](AmplitudeDamping/UniformKraus.lean): `generalChannelFormationSubadditivity_of_uniformKraus` | **Proved** for arbitrary finite-dimensional channels. |

## Classical interfaces that remain unproved

These are hypotheses in theorem types, **not project-defined axioms**.
Their scopes are generic classical statements, not AD-specific conclusions.

| Code | Exact Lean interface | What is assumed |
| --- | --- | --- |
| **S** | [StateCostRegularization](AmplitudeDamping/OperationalEntanglementCost.lean) | Operational LOCC state preparation cost equals regularized state formation, including nonemptiness of achievable rates. |
| **P** | [ParallelCostRegularization](AmplitudeDamping/OperationalEntanglementCost.lean) | Operational parallel LOCC channel simulation cost equals regularized channel formation, including nonemptiness of achievable rates. |

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

The complete build passes (3692 jobs). The audit checks 1648 public project
theorems and permits only `propext`, `Classical.choice` and `Quot.sound` as
transitive axioms. There are no `sorry` proof terms or project-defined axioms.
Existing foundation modules retain their style warnings; the new modules
compile without warnings.

**Axiom checks alone do not establish that a theorem has no extra hypotheses.**
Read the status and interface tables alongside the audit. The library has no
remote CI workflow; verification is performed locally with Lake.
