import AmplitudeDamping.RoofProduct
import QIT.Information.Entropy.MutualInformationDPI
import QIT.Information.Entropy.ConditionalEntropyConcavity
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

/-- The concrete finite pure-state convex roof is a lower envelope for every
finite ensemble, not only for ensembles whose members are pure. -/
theorem outputEntropyRoof_isOutputEntropyRoof (Φ : Channel a b) :
    IsOutputEntropyRoof Φ (outputEntropyRoof Φ) := by
  intro κ _ E
  calc
    outputEntropyRoof Φ E.averageState ≤
        ∑ i, (E.probs i).toReal * outputEntropyRoof Φ (E.states i) :=
      outputEntropyRoof_satisfiesFiniteJensen Φ E
    _ ≤ ∑ i, (E.probs i).toReal *
        (Φ.applyState (E.states i)).vonNeumann := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left
          (outputEntropyRoof_le_outputEntropy Φ (E.states i))
          (NNReal.coe_nonneg _)
    _ = outputEntropyCost Φ E := rfl

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

/-- On product inputs, additivity of the roof gives exact additivity of the
fixed-input Holevo quantity.  This is the achievability/reverse-inequality
counterpart to `fixedInputHolevo_prod_le`. -/
theorem fixedInputHolevo_prod_eq_of_roof_prod
    (roofProd : State (Prod a c) → ℝ)
    (roofLeft : State a → ℝ) (roofRight : State c → ℝ)
    (Φ : Channel a b) (Ψ : Channel c d)
    (ρ : State a) (σ : State c)
    (hroof : roofProd (ρ.prod σ) = roofLeft ρ + roofRight σ) :
    fixedInputHolevo roofProd (Φ.prod Ψ) (ρ.prod σ) =
      fixedInputHolevo roofLeft Φ ρ + fixedInputHolevo roofRight Ψ σ := by
  unfold fixedInputHolevo
  rw [Channel.applyState_prod, State.vonNeumann_prod, hroof]
  ring

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

/-- Concrete pure-decomposition version of the Holevo converse for the actual
finite pure-state convex roof defined in `ConvexRoof.lean`. -/
theorem pureDecompositionHolevoAfter_prod_le
    (Φ : Channel a b) (Ψ : Channel c d)
    (E : PureDecomposition (Prod a c))
    (hroof : ∀ σ : State (Prod a c),
      outputEntropyRoof (Φ.prod Ψ) σ ≥
        outputEntropyRoof Φ σ.marginalA +
          outputEntropyRoof Ψ σ.marginalB) :
    ensembleHolevoAfter (Φ.prod Ψ) E.toEnsemble ≤
      fixedInputHolevo (outputEntropyRoof Φ) Φ E.averageState.marginalA +
        fixedInputHolevo (outputEntropyRoof Ψ) Ψ E.averageState.marginalB := by
  rw [ensembleHolevoAfter_eq]
  have hcost := outputEntropyRoof_le_outputCost (Φ.prod Ψ) E
  have hfixed := fixedInputHolevo_prod_le
    (outputEntropyRoof (Φ.prod Ψ)) (outputEntropyRoof Φ) (outputEntropyRoof Ψ)
    Φ Ψ E.averageState (hroof E.averageState)
  unfold PureDecomposition.outputCost at hcost
  unfold PureDecomposition.averageState at hcost hfixed
  unfold fixedInputHolevo at hfixed
  unfold fixedInputHolevo
  unfold PureDecomposition.averageState
  linarith

/-- For amplitude damping tensored with an arbitrary finite-dimensional
channel, the actual convex-roof fixed-input Holevo quantity is exactly
additive on product input states. -/
theorem amplitudeDamping_fixedInputHolevo_prod_eq
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Φ : Channel a b) (rho : State Qubit) (sigma : State a) :
    fixedInputHolevo
        (outputEntropyRoof ((amplitudeDamping p hp0 hp1).prod Φ))
        ((amplitudeDamping p hp0 hp1).prod Φ) (rho.prod sigma) =
      fixedInputHolevo
          (outputEntropyRoof (amplitudeDamping p hp0 hp1))
          (amplitudeDamping p hp0 hp1) rho +
        fixedInputHolevo (outputEntropyRoof Φ) Φ sigma := by
  exact fixedInputHolevo_prod_eq_of_roof_prod
    (outputEntropyRoof ((amplitudeDamping p hp0 hp1).prod Φ))
    (outputEntropyRoof (amplitudeDamping p hp0 hp1))
    (outputEntropyRoof Φ) (amplitudeDamping p hp0 hp1) Φ rho sigma
    (amplitudeDamping_outputEntropyRoof_prod_eq
      p hp0 hp1 Φ rho sigma)

/-- Concrete Holevo converse for amplitude damping tensored with an arbitrary
finite-dimensional auxiliary channel. -/
theorem amplitudeDamping_pureDecompositionHolevoAfter_prod_le
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Φ : Channel a b) (E : PureDecomposition (Prod Qubit a)) :
    ensembleHolevoAfter ((amplitudeDamping p hp0 hp1).prod Φ) E.toEnsemble ≤
      fixedInputHolevo
          (outputEntropyRoof (amplitudeDamping p hp0 hp1))
          (amplitudeDamping p hp0 hp1) E.averageState.marginalA +
        fixedInputHolevo (outputEntropyRoof Φ) Φ
          E.averageState.marginalB := by
  exact pureDecompositionHolevoAfter_prod_le
    (amplitudeDamping p hp0 hp1) Φ E
    (amplitudeDamping_outputEntropyRoof_stronglySuperadditive
      p hp0 hp1 Φ)

/-- The Holevo converse for an arbitrary finite input ensemble of amplitude
damping tensored with an arbitrary finite-dimensional auxiliary channel. -/
theorem amplitudeDamping_ensembleHolevoAfter_prod_le
    {ι : Type} [Fintype ι]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Φ : Channel a b) (E : Ensemble ι (Prod Qubit a)) :
    ensembleHolevoAfter ((amplitudeDamping p hp0 hp1).prod Φ) E ≤
      fixedInputHolevo
          (outputEntropyRoof (amplitudeDamping p hp0 hp1))
          (amplitudeDamping p hp0 hp1) E.averageState.marginalA +
        fixedInputHolevo (outputEntropyRoof Φ) Φ
          E.averageState.marginalB := by
  exact ensembleHolevoAfter_prod_le
    (outputEntropyRoof ((amplitudeDamping p hp0 hp1).prod Φ))
    (outputEntropyRoof (amplitudeDamping p hp0 hp1))
    (outputEntropyRoof Φ) (amplitudeDamping p hp0 hp1) Φ E
    (outputEntropyRoof_isOutputEntropyRoof
      ((amplitudeDamping p hp0 hp1).prod Φ))
    (amplitudeDamping_outputEntropyRoof_stronglySuperadditive
      p hp0 hp1 Φ)

end

end AmplitudeDamping
