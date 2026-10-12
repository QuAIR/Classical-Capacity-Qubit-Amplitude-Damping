import AmplitudeDamping.EntanglementFormation
import AmplitudeDamping.TwoExpectationPerturbation
import AmplitudeDamping.PureDecompositionSupport

/-!
# The two fixed expectation decomposition theorem

The finite-dimensional Leka–Petz decomposition theorem is proved using the
compact convex slice of density matrices with two fixed expectations. A
four-dimensional supported Hermitian perturbation shows that every extreme
point has rank one. Compactness and Carathéodory's theorem then give a finite
decomposition with strictly positive weights. Support containment follows
from positivity of the summands.
-/

open scoped BigOperators NNReal ComplexConjugate
namespace AmplitudeDamping
open QIT
noncomputable section
universe u v

/-- Operator expectation, with its real value used throughout. -/
def operatorExpectation {a : Type u} [Fintype a] [DecidableEq a]
    (F : Matrix a a ℂ) (ρ : State a) : ℝ := (F * ρ.matrix).trace.re

/-- Membership in the support of a positive matrix, expressed as orthogonality
to its kernel. This formulation does not choose an eigenbasis. -/
def pureVectorInStateSupport {a : Type u} [Fintype a] [DecidableEq a]
    (ψ : PureVector a) (ρ : State a) : Prop :=
  ∀ z : a → ℂ, ρ.matrix.mulVec z = 0 →
    (∑ i, star (z i) * ψ.amp i) = 0

/-- Exact finite-dimensional Leka–Petz decomposition property:
strictly positive finite probabilities, support containment,
and preservation of two (possibly noncommuting) Hermitian expectations. -/
def TwoExpectationDecomposition (a : Type u) [Fintype a] [DecidableEq a] : Prop :=
  ∀ (ρ : State a) (F G : Matrix a a ℂ), F.IsHermitian → G.IsHermitian →
    ∃ E : PureDecomposition a, E.averageState = ρ ∧
      ∀ j, 0 < (E.probs j : ℝ) ∧
        pureVectorInStateSupport (E.vectors j) ρ ∧
        operatorExpectation F (E.vectors j).state = operatorExpectation F ρ ∧
        operatorExpectation G (E.vectors j).state = operatorExpectation G ρ

/-- Every finite-dimensional density state admits a finite pure decomposition
whose positive-weight vectors lie in its support and preserve two Hermitian
expectations exactly. -/
theorem twoExpectationDecomposition (a : Type u) [Fintype a] [DecidableEq a] :
    TwoExpectationDecomposition a := by
  intro ρ F G _ _
  obtain ⟨E, hE, hcomponents⟩ := exists_pureDecomposition_of_extreme_rank_le_one ρ F G
    (rank_le_one_of_extreme_twoExpectationSlice ρ F G)
  refine ⟨E, hE, fun j => ⟨(hcomponents j).1, ?_,
    (hcomponents j).2.1, (hcomponents j).2.2⟩⟩
  intro z hz
  apply E.component_orthogonal_kernel j (hcomponents j).1 z
  simpa only [hE] using hz

/-- If the entropy of every supported pure vector depends only on two
expectations, a fixed-expectation decomposition gives the corresponding upper
bound on the literal entanglement-of-formation convex roof. -/
theorem entanglementOfFormation_le_of_two_expectations
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (ρ : State (a × b)) (F G : Matrix (a × b) (a × b) ℂ)
    (hF : F.IsHermitian) (hG : G.IsHermitian) (f : ℝ → ℝ → ℝ)
    (hpure : ∀ ψ : PureVector (a × b), pureVectorInStateSupport ψ ρ →
      ψ.state.marginalA.vonNeumann ≤
        f (operatorExpectation F ψ.state) (operatorExpectation G ψ.state)) :
    entanglementOfFormation ρ ≤
      f (operatorExpectation F ρ) (operatorExpectation G ρ) := by
  obtain ⟨E, hE, hcomponents⟩ := twoExpectationDecomposition (a × b) ρ F G hF hG
  have hw : ∑ i, (E.probs i : ℝ) = 1 := by
    exact_mod_cast E.weights_sum
  calc
    entanglementOfFormation ρ ≤ E.entanglementCost := by
      rw [← hE]
      exact entanglementOfFormation_le_entanglementCost E
    _ ≤ ∑ j, (E.probs j : ℝ) *
        f (operatorExpectation F ρ) (operatorExpectation G ρ) := by
      apply Finset.sum_le_sum
      intro j _
      have h := hpure (E.vectors j) (hcomponents j).2.1
      rw [(hcomponents j).2.2.1, (hcomponents j).2.2.2] at h
      exact mul_le_mul_of_nonneg_left h (NNReal.coe_nonneg _)
    _ = f (operatorExpectation F ρ) (operatorExpectation G ρ) := by
      rw [← Finset.sum_mul, hw, one_mul]

end
end AmplitudeDamping
