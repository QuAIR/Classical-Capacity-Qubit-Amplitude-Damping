import AmplitudeDamping.Definitions
import QIT.Core.Pure

/-!
# Finite pure-state decompositions and the output-entropy convex roof

The manuscript optimizes over finite pure-state ensembles.  Encoding the
classical alphabet size as a field avoids quantifying over Lean types inside a
set comprehension and permits a literal real infimum.
-/

open scoped BigOperators NNReal

namespace AmplitudeDamping

open QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

/-- A finite probability distribution whose signals are normalized pure
vectors.  Zero weights are allowed. -/
structure PureDecomposition (a : Type u) [Fintype a] [DecidableEq a] where
  card : ℕ
  probs : Fin card → ℝ≥0
  weights_sum : ∑ i, probs i = 1
  vectors : Fin card → PureVector a

namespace PureDecomposition

/-- Forget that the member states are pure. -/
def toEnsemble (E : PureDecomposition a) : Ensemble (Fin E.card) a where
  probs := E.probs
  weights_sum := E.weights_sum
  states i := (E.vectors i).state

@[simp]
theorem toEnsemble_probs (E : PureDecomposition a) :
    E.toEnsemble.probs = E.probs := rfl

@[simp]
theorem toEnsemble_states (E : PureDecomposition a) (i : Fin E.card) :
    E.toEnsemble.states i = (E.vectors i).state := rfl

/-- Average input state represented by a pure decomposition. -/
def averageState (E : PureDecomposition a) : State a :=
  E.toEnsemble.averageState

/-- Average output entropy of a pure decomposition. -/
def outputCost (Φ : Channel a b) (E : PureDecomposition a) : ℝ :=
  outputEntropyCost Φ E.toEnsemble

theorem outputCost_nonneg (Φ : Channel a b) (E : PureDecomposition a) :
    0 ≤ E.outputCost Φ := by
  unfold outputCost outputEntropyCost
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (NNReal.coe_nonneg _) (State.vonNeumann_nonneg _)

end PureDecomposition

/-- All average output-entropy costs of finite pure decompositions of `ρ`. -/
def pureOutputEntropyValues (Φ : Channel a b) (ρ : State a) : Set ℝ :=
  {x | ∃ E : PureDecomposition a,
    E.averageState = ρ ∧ x = E.outputCost Φ}

/-- The finite pure-state output-entropy convex roof. -/
def outputEntropyRoof (Φ : Channel a b) (ρ : State a) : ℝ :=
  sInf (pureOutputEntropyValues Φ ρ)

theorem pureOutputEntropyValues_bddBelow (Φ : Channel a b) (ρ : State a) :
    BddBelow (pureOutputEntropyValues Φ ρ) := by
  refine ⟨0, ?_⟩
  intro x hx
  rcases hx with ⟨E, _, rfl⟩
  exact E.outputCost_nonneg Φ

/-- The convex roof is no larger than the cost of any particular finite pure
decomposition of the same average state. -/
theorem outputEntropyRoof_le_outputCost (Φ : Channel a b)
    (E : PureDecomposition a) :
    outputEntropyRoof Φ E.averageState ≤ E.outputCost Φ := by
  apply csInf_le (pureOutputEntropyValues_bddBelow Φ E.averageState)
  exact ⟨E, rfl, rfl⟩

/-- Pure-ensemble lower-envelope property, isolated as a reusable predicate. -/
def IsPureOutputEntropyRoof (Φ : Channel a b) (roof : State a → ℝ) : Prop :=
  ∀ E : PureDecomposition a, roof E.averageState ≤ E.outputCost Φ

theorem outputEntropyRoof_isPureOutputEntropyRoof (Φ : Channel a b) :
    IsPureOutputEntropyRoof Φ (outputEntropyRoof Φ) := by
  intro E
  exact outputEntropyRoof_le_outputCost Φ E

end

end AmplitudeDamping
