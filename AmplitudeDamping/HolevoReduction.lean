import AmplitudeDamping.Definitions
import QIT.Information.Entropy.MutualInformationDPI
import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.Limit

/-!
# From strong roof superadditivity to a Holevo converse

This file formalizes the short information-theoretic part of the manuscript:
subadditivity of the average output entropy plus strong superadditivity of the
convex roof gives the fixed-input Holevo upper bound.
-/

open scoped BigOperators

namespace AmplitudeDamping

open QIT

universe u v w x

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]
variable [Fintype d] [DecidableEq d]

/-- Von Neumann entropy is subadditive on a bipartite state. -/
theorem vonNeumann_le_marginals (ρ : State (Prod a c)) :
    ρ.vonNeumann ≤ ρ.marginalA.vonNeumann + ρ.marginalB.vonNeumann := by
  have hD : (0 : EReal) ≤
      ρ.relativeEntropy (ρ.marginalA.prod ρ.marginalB) :=
    State.relativeEntropy_nonneg ρ (ρ.marginalA.prod ρ.marginalB)
  rw [State.relativeEntropy_prod_marginals_eq_mutualInformation] at hD
  have hI : 0 ≤ QIT.mutualInformation ρ := by exact_mod_cast hD
  simpa [QIT.mutualInformation, sub_nonneg] using hI

/-- A product channel's output marginals are obtained by applying the factor
channels to the corresponding input marginals. -/
theorem output_marginals (Φ : Channel a b) (Ψ : Channel c d)
    (ρ : State (Prod a c)) :
    ((Φ.prod Ψ).applyState ρ).marginalA = Φ.applyState ρ.marginalA ∧
      ((Φ.prod Ψ).applyState ρ).marginalB = Ψ.applyState ρ.marginalB := by
  constructor
  · exact State.marginalA_applyState_prod ρ Φ Ψ
  · exact State.marginalB_applyState_prod ρ Φ Ψ

/-- The central algebraic implication in the Holevo converse. -/
theorem fixedInputHolevo_prod_le
    (roofProd : State (Prod a c) → ℝ)
    (roofLeft : State a → ℝ) (roofRight : State c → ℝ)
    (Φ : Channel a b) (Ψ : Channel c d)
    (ρ : State (Prod a c))
    (hroof : roofProd ρ ≥
      roofLeft ρ.marginalA + roofRight ρ.marginalB) :
    fixedInputHolevo roofProd (Φ.prod Ψ) ρ ≤
      fixedInputHolevo roofLeft Φ ρ.marginalA +
        fixedInputHolevo roofRight Ψ ρ.marginalB := by
  have hS := vonNeumann_le_marginals ((Φ.prod Ψ).applyState ρ)
  rw [State.marginalA_applyState_prod, State.marginalB_applyState_prod] at hS
  unfold fixedInputHolevo
  linarith

/-- Ensemble-level Holevo converse.  Every output ensemble is bounded by the
sum of the two fixed-input Holevo quantities evaluated on the marginals of its
average input. -/
theorem ensembleHolevoAfter_prod_le
    {ι : Type} [Fintype ι]
    (roofProd : State (Prod a c) → ℝ)
    (roofLeft : State a → ℝ) (roofRight : State c → ℝ)
    (Φ : Channel a b) (Ψ : Channel c d)
    (E : Ensemble ι (Prod a c))
    (hProdRoof : IsOutputEntropyRoof (Φ.prod Ψ) roofProd)
    (hroof : ∀ σ : State (Prod a c),
      roofProd σ ≥ roofLeft σ.marginalA + roofRight σ.marginalB) :
    ensembleHolevoAfter (Φ.prod Ψ) E ≤
      fixedInputHolevo roofLeft Φ E.averageState.marginalA +
        fixedInputHolevo roofRight Ψ E.averageState.marginalB := by
  rw [ensembleHolevoAfter_eq]
  have hcost := hProdRoof E
  have hfixed := fixedInputHolevo_prod_le roofProd roofLeft roofRight Φ Ψ
    E.averageState (hroof E.averageState)
  unfold fixedInputHolevo at hfixed
  unfold fixedInputHolevo
  linarith

end

end AmplitudeDamping
