import QIT.Information.Entropy.Holevo
import QIT.Information.Entropy.ConditionalEntropyConcavity

/-!
# Output-entropy costs and fixed-input Holevo quantities

The definitions in this file are the finite-ensemble layer used in the
amplitude-damping argument.  They are built on the `QIT.Ensemble`, `QIT.State`,
and `QIT.Channel` APIs from Lean-QIT.
-/

open scoped BigOperators NNReal

namespace AmplitudeDamping

open QIT

universe u v w x

noncomputable section

variable {ι : Type u} {a : Type v} {b : Type w} {c : Type x}
variable [Fintype ι]
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]

/-- Apply a quantum channel to every member of an ensemble, without changing
its classical probability distribution. -/
def outputEnsemble (Φ : Channel a b) (E : Ensemble ι a) : Ensemble ι b where
  probs := E.probs
  weights_sum := E.weights_sum
  states i := Φ.applyState (E.states i)

@[simp]
theorem outputEnsemble_probs (Φ : Channel a b) (E : Ensemble ι a) :
    (outputEnsemble Φ E).probs = E.probs := rfl

@[simp]
theorem outputEnsemble_states (Φ : Channel a b) (E : Ensemble ι a) (i : ι) :
    (outputEnsemble Φ E).states i = Φ.applyState (E.states i) := rfl

/-- Forming an ensemble average commutes with a quantum channel. -/
@[simp]
theorem outputEnsemble_averageState (Φ : Channel a b) (E : Ensemble ι a) :
    (outputEnsemble Φ E).averageState = Φ.applyState E.averageState := by
  apply State.ext
  change (∑ i, (E.probs i : ℂ) • Φ.map (E.states i).matrix) =
    Φ.map (∑ i, (E.probs i : ℂ) • (E.states i).matrix)
  simp

/-- Average output entropy of a finite signal ensemble. -/
def outputEntropyCost (Φ : Channel a b) (E : Ensemble ι a) : ℝ :=
  ∑ i, (E.probs i).toReal * (Φ.applyState (E.states i)).vonNeumann

/-- The Holevo information after applying a channel to an ensemble. -/
def ensembleHolevoAfter (Φ : Channel a b) (E : Ensemble ι a) : ℝ :=
  (outputEnsemble Φ E).holevoInformation

theorem ensembleHolevoAfter_eq (Φ : Channel a b) (E : Ensemble ι a) :
    ensembleHolevoAfter Φ E =
      (Φ.applyState E.averageState).vonNeumann - outputEntropyCost Φ E := by
  simp [ensembleHolevoAfter, Ensemble.holevoInformation_def, outputEntropyCost]

/-- A function is a lower envelope of all finite average output-entropy costs.
The convex roof has this property.  Keeping it as a predicate lets the
information-theoretic reduction remain independent of the chosen concrete
Caratheodory representation of the roof. -/
def IsOutputEntropyRoof (Φ : Channel a b) (roof : State a → ℝ) : Prop :=
  ∀ {κ : Type} [Fintype κ] (E : Ensemble κ a),
    roof E.averageState ≤ outputEntropyCost Φ E

/-- Fixed-input Holevo quantity associated with an output-entropy roof. -/
def fixedInputHolevo (roof : State a → ℝ) (Φ : Channel a b) (ρ : State a) : ℝ :=
  (Φ.applyState ρ).vonNeumann - roof ρ

/-- Strong superadditivity of an output-entropy roof for a specified pair of
channels.  This is the exact fixed-input statement used in the paper. -/
def StronglySuperadditiveFor (roofProd : State (Prod a c) → ℝ)
    (roofLeft : State a → ℝ) (roofRight : State c → ℝ) : Prop :=
  ∀ ρ : State (Prod a c),
    roofProd ρ ≥ roofLeft ρ.marginalA + roofRight ρ.marginalB

end

end AmplitudeDamping
