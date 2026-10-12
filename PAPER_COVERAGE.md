# Manuscript coverage and classical interfaces

This ledger tracks the full manuscript, not only the original AD capacity
result. A theorem is complete only when its actual Lean statement has the
same objects, quantifiers, side conditions and conclusions as the paper.
A proposition definition is an interface, not a proved theorem. The public root imports all completed modules. Full builds and transitive
axiom audits are recorded below; explicit theorem hypotheses are audited
separately.

Source: `openprob/main.tex`, SHA-256 `1b4cebce9ab0e9284d15bb29866c0c136eff3690f97bdc1ab04f3e1222312f36`.
The source is outside this Git repository; labels below identify statements
independently of theorem-number changes. Base revision: `8e870f4`.

The 18 active numbered statements have corresponding Lean statements. The
17 proved conclusions use only the classical interfaces listed below where
needed; uniform Kraus representation is the one remaining numbered interface.
The two-expectation decomposition and fixed-signal HSW theorem are proved here.
Independent review checked quantifiers, endpoints, arbitrary partners,
operational definitions, and the literal four-unitary normal-form clause.

## Required coverage

| Manuscript label | Required conclusion | Current evidence / remaining work |
| --- | --- | --- |
| `thm:support` | Arbitrary finite-dimensional support SSA, state additivity and state cost | `SupportSSA` and `SupportConsequences` prove arbitrary finite support SSA, product additivity, tensor powers and operational state cost in original coordinates. An exact intrinsic projector-support ↔ explicit-coordinate equivalence is proved. Only operational state regularization remains an external interface. |
| `thm:triangle` | Arbitrary rectangular block inequality including zero weights | Existing `triangularBlockEntropyInequality`, checked. |
| `lem:two-moments` | Finite pure decomposition preserving two Hermitian expectations, inside support | `twoExpectationDecomposition` in `TwoExpectations.lean` proves the exact original interface in every finite dimension, with positive weights and support membership. |
| `cor:state-examples` | Product-kernel and rank-at-most-two two-qubit state results, corner formula | Product-kernel/rank-two state additivity and powers proved. `CornerFromTwoExpectations` derives the corner interface without full Wootters; `StateCostRegularization` connects operational cost. |
| `cor:stinespring` | General support roof SSA, strong Holevo and capacity additivity | `SupportStinespring` proves roof SSA, strong Holevo, own capacity collapse and arbitrary-partner capacity additivity from actual supported dilation range. |
| `lem:pure-output-stinespring` | Pure output iff suitable Stinespring support, with arbitrary environment | `PureOutputSupport` proves pure output iff explicit support coordinates for any finite environment. |
| `cor:two-kraus` | Pure output and communication consequences | Roof/Holevo/own capacity and arbitrary-partner capacity proved without extra classical interfaces; `twoKraus_has_pure_output` supplies the pure-output witness unconditionally. |
| `lem:flat-roof` | Exact roof at every physical input including endpoints | Existing `outputEntropyRoof_eq_dampingEntropyCurve`, checked. |
| `thm:damping-capacity` | Scalar max, binary optimum, product-codeword achievability, strong capacity additivity and endpoints | Scalar maximum, unique optimizer, exact binary ensemble, endpoints and arbitrary-partner capacity additivity proved. `ProductSignalCoding` retains exact binary-product-codeword witnesses using the proved fixed-ensemble `productSignalHSW` theorem, with no coding hypothesis. |
| `prop:deficit` | Exact three-term deficit, information radius, unique optimal average input for p<1 | `ScalarOptimizer` and `FiniteBlockDeficit`: exact three-term decomposition, nonnegative terms, information radius, optimizer and uniqueness. Uniqueness alone uses explicit generic `FaithfulRelativeEntropyEquality`. |
| `thm:two-kraus-unified` | Strong channel formation and parallel cost additivity, all state/channel equalities and powers | `UnifiedFormation` / `UnifiedCost` prove formation, powers, operational state/channel equalities and strong parallel cost additivity. `PaperTheorems` discharges general subadditivity using only the exact classical uniform-Kraus interface. |
| `cor:pure-output` | Unified conclusions for all pure-output qubit channels | `PureOutputChoi` proves pure output iff Choi product kernel; `Paper.pure_output_additivity` and `Paper.pure_output_single_letter_and_powers` cover all conclusions, with no Kraus rank restriction. |
| `thm:ad-cost` | AD state/channel formation and parallel cost formulas, powers and arbitrary partners | Actual Choi bridge and unconditional one-copy E_F formula proved. `amplitudeDamping_formation_powers` and `amplitudeDamping_operational_costs` cover powers and operational costs with displayed classical interfaces; `ADDirectCost` proves own powers/costs without uniform Kraus or qubit-identity premises; only operational regularization remains. Arbitrary-partner additivity uses uniform Kraus. |
| `prop:binary-instrument` | Explicit two-Kraus instrument maximum and uniform correlated-block bound | `BinaryInstrument` proves exact maximum; `InstrumentProduct` proves every block length for arbitrary correlated inputs, from generic product-instrument entropy bound. |
| `lem:logdet` | Logdet convexity | Existing `skewLogDetIncrement_convexOn_posDef`, checked. |
| `prop:triangle-equality` | Necessary/sufficient equality conditions with invertible middle block | `TriangleEquality` proves strict skew-logdet/entropy convexity and the necessary/sufficient Gram conditions without external hypotheses. `square_triangular_entropy_equality_iff_four_unitaries` also proves the literal Kronecker normal-form equivalence with arbitrary row and column block unitaries. |
| `lem:uniform-kraus` | Uniform finite Kraus representation / minimax | Exact classical finite uniform ε-optimal Kraus statement is `GeneralUniformKrausRepresentation`; its product/formation applications are proved. |
| `lem:channel-subadditivity` | General channel formation subadditivity | `generalChannelFormationSubadditivity_of_uniformKraus` proves the full arbitrary-channel inequality from the classical uniform representation lemma. |

## Classical trust boundary

- HSW capacity characterization: already supplied by pinned Lean-QIT;
  no need to re-formalize. Checked AD capacity theorem has only standard
  Lean axioms. The product-codeword clause is proved by `productSignalHSW`,
  retaining the input words through packing and maximal-error expurgation.
- State operational entanglement-cost regularization and parallel channel
  simulation regularization: permitted external classical theorems, not
  definitions of operational quantities. `OperationalEntanglementCost` defines actual resource-assisted finite-round LOCC protocols, vanishing trace/diamond error and asymptotic resource rates; both regularization interfaces are explicit.
- Wootters: existing `woottersKernelUpperBound` is a specialized corner
  conclusion, not the general Wootters formula. `woottersKernelUpperBound_of_twoExpectations` now proves it using the proved two-expectation theorem. The AD one-copy Choi formula is unconditional.
- Two-expectation decomposition (Leka–Petz): `twoExpectationDecomposition`
  proves the exact finite statement via compact convex geometry and supported
  Hermitian perturbations. T parameters are removed from downstream theorems.
- `QubitChannelFormationIdentity`: standard all-qubit-channel identity
  E_ch(N)=E_F(J_N), cited in the manuscript as BBCW Eqs. (76)–(77).
  Channel formation is independently defined by optimization over pure
  reference-input states; this identity is an explicit hypothesis only.

- `FaithfulRelativeEntropyEquality`: the standard equality condition in
  nonnegativity of quantum relative entropy with faithful reference state;
  used only for the optimal-average uniqueness direction.
- `GeneralUniformKrausRepresentation`: standard finite uniform near-optimal
  Kraus/minimax statement (BBCW Lemma 14). `UniformKraus` proves the
  correlated product-instrument bound and discharges channel subadditivity.
- `ProductSignalHSW` is now proved by `productSignalHSW`. The general proof
  retains exact tensor-product encoder membership and collective POVMs;
  both binary-signal corollaries have no H parameter.

## Minimal additional hypotheses of principal results

“None” means no extra classical interface beyond the pinned dependencies;
it does not omit physical parameter or dimension conditions.

| Result | Additional classical interfaces |
| --- | --- |
| AD capacity scalar formula, explicit optimal ensemble, arbitrary-partner capacity additivity | None |
| AD one-copy Choi E_F and independently optimized channel E_F formula | None |
| AD explicit binary instrument and correlated n-block upper bound | None |
| Triangular inequality, strictness, Gram equality and unitary normal form | None |
| Pure-output ↔ supported dilation ↔ Choi product kernel | None |
| General support SSA, state formation additivity and powers | None |
| AD exact channel/Choi formation powers | None |
| AD operational parallel cost | Parallel regularization |
| Operational supported-state cost | State regularization |
| Pure-output communication additivity | None |
| General pure-output channel formation additivity | Qubit-channel identity + uniform Kraus |
| General pure-output parallel-cost additivity | Previous row + parallel regularization |
| Binary-product-codeword achievability | None |
| Exact deficit, nonnegative terms and information radius | None |
| Uniqueness of the optimal block-average input | Faithful relative-entropy equality |

`woottersKernelUpperBound` and `GeneralChannelFormationSubadditivity` remain
useful low-level propositions, but are discharged in the main entry points.
They are not additional unproved mathematical inputs there. There are five
unproved classical interfaces in the current development, with state and
channel operational regularization counted separately.

## Verification

The complete public root passes `lake build` (3673 jobs), with no new
warnings. `lake env lean Audit.lean` audits every public project theorem's
transitive axioms (1463 theorems in this revision) and rejects anything outside
`propext`, `Classical.choice`
and `Quot.sound`. It also rejects T/H interface names in theorem hypotheses.
No project-defined axioms or `sorry` proof terms were added.
`git diff --check` passes. Old foundation modules retain their pre-existing
style warnings.

Dependency versions are unchanged from the base revision. Unnumbered
illustrative examples and further extensions are not included in this
numbered-statement coverage claim. The README provides the per-result status
table and names every remaining classical interface.
