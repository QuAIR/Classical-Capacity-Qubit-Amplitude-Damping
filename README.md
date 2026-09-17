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

| Mathematical component | Principal Lean module | Status |
| --- | --- | --- |
| Amplitude-damping channel and pure-input entropy | `Channel`, `FixedExcitation`, `QubitEntropy` | Checked |
| Exact fixed-excitation convex roof | `ScalarCurve`, `EqualExcitation` | Checked |
| Triangular block entropy inequality | `Triangular/*` | Checked |
| Strong roof superadditivity | `StrongSuperadditivity` | Checked |
| Product and finite-copy roof identities | `RoofProduct`, `NCopy` | Checked |
| Strong additivity of optimized Holevo information | `HolevoCapacity` | Checked |
| One-letter scalar capacity formula | `OneLetterCapacity`, `ScalarCapacity` | Checked |
| HSW regularization and classical-capacity bridge | `CapacityBridge` | Checked |
| Mean-excitation constrained variant | — | Not yet formalized |
| Entanglement-of-formation and Choi-state consequences | — | Not yet formalized |

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
Unfinished mathematical extensions are listed explicitly in `STATUS.md` and
are not introduced as assumptions.
