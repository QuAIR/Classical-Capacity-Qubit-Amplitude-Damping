import AmplitudeDamping.HolevoCapacity

/-!
# One-letter variational formula

This module identifies Lean-QIT's optimized finite-ensemble Holevo
information with the supremum of the fixed-input expression defined by the
output-entropy convex roof.  For amplitude damping, the exact roof formula
then removes the ensemble optimization entirely.
-/

namespace AmplitudeDamping

open QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The state-wise one-letter optimization associated with the exact
output-entropy convex roof. -/
def roofHolevoInformation (Φ : Channel a b) : ℝ :=
  sSup (Set.range (fixedInputHolevo (outputEntropyRoof Φ) Φ))

theorem roofHolevoInformationValues_nonempty [Nonempty a]
    (Φ : Channel a b) :
    (Set.range (fixedInputHolevo (outputEntropyRoof Φ) Φ)).Nonempty := by
  let rho : State a := Classical.basisState
    (Classical.choice (inferInstance : Nonempty a))
  exact ⟨fixedInputHolevo (outputEntropyRoof Φ) Φ rho, rho, rfl⟩

theorem roofHolevoInformationValues_bddAbove (Φ : Channel a b) :
    BddAbove (Set.range (fixedInputHolevo (outputEntropyRoof Φ) Φ)) := by
  refine ⟨log2 (Fintype.card b), ?_⟩
  intro x hx
  rcases hx with ⟨rho, rfl⟩
  have hS := State.vonNeumann_le_log_card (Φ.applyState rho)
  have hroof := outputEntropyRoof_nonneg Φ rho
  unfold fixedInputHolevo
  linarith

/-- The ensemble supremum equals the state supremum of output entropy minus
the exact output-entropy convex roof. -/
theorem holevoInformation_eq_roofHolevoInformation [Nonempty a]
    (Φ : Channel a b) :
    Channel.holevoInformation.{u, v, 0} Φ = roofHolevoInformation Φ := by
  apply le_antisymm
  · unfold Channel.holevoInformation
    apply csSup_le Φ.holevoInformationValues_nonempty
    intro r hr
    rcases hr with ⟨ι, hιF, hιD, E, rfl⟩
    letI : Fintype ι := hιF
    letI : DecidableEq ι := hιD
    have hroof := outputEntropyRoof_isOutputEntropyRoof Φ E
    have hmember : fixedInputHolevo (outputEntropyRoof Φ) Φ E.averageState ≤
        roofHolevoInformation Φ := by
      apply le_csSup (roofHolevoInformationValues_bddAbove Φ)
      exact ⟨E.averageState, rfl⟩
    rw [show Φ.hswHolevoRate E = ensembleHolevoAfter Φ E by rfl,
      ensembleHolevoAfter_eq]
    unfold fixedInputHolevo at hmember
    linarith
  · unfold roofHolevoInformation
    apply csSup_le (roofHolevoInformationValues_nonempty Φ)
    intro x hx
    rcases hx with ⟨rho, rfl⟩
    exact fixedInputHolevo_le_holevoInformation Φ rho

/-- The explicit fixed-input information function for amplitude damping. -/
def amplitudeDampingStateInformation
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rho : State Qubit) : ℝ :=
  ((amplitudeDamping p hp0 hp1).applyState rho).vonNeumann -
    dampingEntropyCurve p (stateExcitation rho)

theorem amplitudeDamping_fixedInputHolevo_eq_stateInformation
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rho : State Qubit) :
    fixedInputHolevo (outputEntropyRoof (amplitudeDamping p hp0 hp1))
        (amplitudeDamping p hp0 hp1) rho =
      amplitudeDampingStateInformation p hp0 hp1 rho := by
  unfold fixedInputHolevo amplitudeDampingStateInformation
  rw [outputEntropyRoof_eq_dampingEntropyCurve]

/-- Exact one-letter reduction of amplitude-damping Holevo information to a
supremum over a single qubit average state. -/
theorem amplitudeDamping_holevoInformation_eq_stateSup
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel.holevoInformation.{0, 0, 0} (amplitudeDamping p hp0 hp1) =
      sSup (Set.range (amplitudeDampingStateInformation p hp0 hp1)) := by
  rw [holevoInformation_eq_roofHolevoInformation]
  unfold roofHolevoInformation
  congr 1
  ext x
  constructor
  · rintro ⟨rho, rfl⟩
    exact ⟨rho, (amplitudeDamping_fixedInputHolevo_eq_stateInformation
      p hp0 hp1 rho).symm⟩
  · rintro ⟨rho, rfl⟩
    exact ⟨rho, amplitudeDamping_fixedInputHolevo_eq_stateInformation
      p hp0 hp1 rho⟩

end

end AmplitudeDamping
