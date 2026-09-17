import AmplitudeDamping.Definitions
import QIT.Core.Pure
import QIT.Symmetry.DeFinetti.RennerProjectors

/-!
# Finite pure-state decompositions and the output-entropy convex roof

The manuscript optimizes over finite pure-state ensembles.  Encoding the
classical alphabet size as a field avoids quantifying over Lean types inside a
set comprehension and permits a literal real infimum.
-/

open scoped BigOperators ComplexOrder MatrixOrder NNReal

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

/-- Finite Jensen inequality for a functional on density states. -/
def SatisfiesFiniteJensen (f : State a → ℝ) : Prop :=
  ∀ {ι : Type} [Fintype ι] (E : Ensemble ι a),
    f E.averageState ≤ ∑ i, (E.probs i).toReal * f (E.states i)

theorem outputEntropyRoof_isPureOutputEntropyRoof (Φ : Channel a b) :
    IsPureOutputEntropyRoof Φ (outputEntropyRoof Φ) := by
  intro E
  exact outputEntropyRoof_le_outputCost Φ E

/-- The spectral decomposition of a state, reindexed by a canonical finite
alphabet, as a `PureDecomposition`. -/
def spectralPureDecomposition (ρ : State a) : PureDecomposition a where
  card := Fintype.card a
  probs k :=
    ⟨ρ.pos.isHermitian.eigenvalues ((Fintype.equivFin a).symm k),
      ρ.pos.eigenvalues_nonneg _⟩
  weights_sum := by
    apply NNReal.eq
    simp only [NNReal.coe_sum, NNReal.coe_one]
    calc
      ∑ k : Fin (Fintype.card a),
          ρ.pos.isHermitian.eigenvalues ((Fintype.equivFin a).symm k) =
          ∑ i : a, ρ.pos.isHermitian.eigenvalues i := by
            exact Fintype.sum_equiv (Fintype.equivFin a).symm _ _ (fun _ => rfl)
      _ = 1 := State.sum_eigenvalues_eq_one ρ
  vectors k := ρ.spectralPureVector ((Fintype.equivFin a).symm k)

/-- The spectral pure decomposition has the original state as its average. -/
@[simp]
theorem spectralPureDecomposition_averageState (ρ : State a) :
    (spectralPureDecomposition ρ).averageState = ρ := by
  apply State.ext
  rw [PureDecomposition.averageState, Ensemble.averageState_matrix]
  change (∑ k : Fin (Fintype.card a),
      ((ρ.pos.isHermitian.eigenvalues ((Fintype.equivFin a).symm k) : ℝ) : ℂ) •
        (ρ.spectralPureVector ((Fintype.equivFin a).symm k)).state.matrix) = ρ.matrix
  calc
    (∑ k : Fin (Fintype.card a),
        ((ρ.pos.isHermitian.eigenvalues ((Fintype.equivFin a).symm k) : ℝ) : ℂ) •
          (ρ.spectralPureVector ((Fintype.equivFin a).symm k)).state.matrix) =
        ∑ i : a, ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
          (ρ.spectralPureVector i).state.matrix := by
            exact Fintype.sum_equiv (Fintype.equivFin a).symm _ _ (fun _ => rfl)
    _ = ρ.matrix := (State.matrix_eq_sum_spectralPureVector ρ).symm

theorem exists_pureDecomposition (ρ : State a) :
    ∃ E : PureDecomposition a, E.averageState = ρ :=
  ⟨spectralPureDecomposition ρ, spectralPureDecomposition_averageState ρ⟩

theorem pureOutputEntropyValues_nonempty (Φ : Channel a b) (ρ : State a) :
    (pureOutputEntropyValues Φ ρ).Nonempty := by
  let E := spectralPureDecomposition ρ
  exact ⟨E.outputCost Φ, E, spectralPureDecomposition_averageState ρ, rfl⟩

theorem outputEntropyRoof_nonneg (Φ : Channel a b) (ρ : State a) :
    0 ≤ outputEntropyRoof Φ ρ := by
  apply le_csInf (pureOutputEntropyValues_nonempty Φ ρ)
  intro x hx
  rcases hx with ⟨E, _, rfl⟩
  exact E.outputCost_nonneg Φ

end

end AmplitudeDamping
