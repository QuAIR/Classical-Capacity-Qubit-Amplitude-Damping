import AmplitudeDamping
import Lean.Util.CollectAxioms

/-!
Run with `lake env lean Audit.lean` after `lake build`.

This checks transitive axiom dependencies of every public project theorem.
It is deliberately separate from the mathematical trust-boundary audit:
explicit theorem hypotheses do not appear in `collectAxioms`, so the classical
interfaces must also be inspected in `PAPER_COVERAGE.md` and theorem types.
-/
open Lean Elab Command in
run_cmd do
  let env ← getEnv
  let names := env.constants.fold (init := #[]) fun names name ci =>
    if (`AmplitudeDamping).isPrefixOf name && ci.isTheorem then names.push name else names
  for name in names do
    let axioms ← Lean.collectAxioms name
    for ax in axioms do
      unless ax == `propext || ax == `Classical.choice || ax == `Quot.sound do
        throwError "Unexpected axiom {ax} in {name}"
  logInfo m!"Audited {names.size} AmplitudeDamping theorems: only propext, Classical.choice, Quot.sound."
