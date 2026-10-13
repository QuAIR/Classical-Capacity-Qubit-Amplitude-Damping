import AmplitudeDamping.Concurrence
import AmplitudeDamping.FiniteRoofMinimum
import QIT.States.Topology

/-! # Two-qubit concurrence as a finite convex roof -/

open scoped BigOperators NNReal ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT
noncomputable section

/-- Pure two-qubit concurrence, in the amplitude-determinant convention. -/
def pureConcurrence (ψ : PureVector (Qubit × Qubit)) : ℝ :=
  2 * ‖(twoQubitAmplitudeMatrix ψ).det‖

theorem pureConcurrence_mem_Icc (ψ : PureVector (Qubit × Qubit)) :
    pureConcurrence ψ ∈ Set.Icc (0 : ℝ) 1 :=
  ⟨by unfold pureConcurrence; positivity, two_norm_det_le_one ψ⟩

/-- Average concurrence of a finite pure ensemble. -/
def PureDecomposition.concurrenceCost (E : PureDecomposition (Qubit × Qubit)) : ℝ :=
  ∑ i, (E.probs i : ℝ) * pureConcurrence (E.vectors i)

theorem PureDecomposition.concurrenceCost_mem_Icc
    (E : PureDecomposition (Qubit × Qubit)) :
    E.concurrenceCost ∈ Set.Icc (0 : ℝ) 1 := by
  have hw : ∑ i, (E.probs i : ℝ) = 1 := by exact_mod_cast E.weights_sum
  constructor
  · exact Finset.sum_nonneg fun i _ => mul_nonneg (NNReal.coe_nonneg _)
      (pureConcurrence_mem_Icc _).1
  · calc
      E.concurrenceCost ≤ ∑ i, (E.probs i : ℝ) * 1 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
          (pureConcurrence_mem_Icc _).2 (NNReal.coe_nonneg _)
      _ = 1 := by simpa using hw

/-- All finite pure-ensemble concurrence costs for a fixed state. -/
def pureConcurrenceValues (ρ : State (Qubit × Qubit)) : Set ℝ :=
  {x | ∃ E : PureDecomposition (Qubit × Qubit),
    E.averageState = ρ ∧ x = E.concurrenceCost}

/-- Mixed-state concurrence is an independently defined convex roof. -/
def concurrence (ρ : State (Qubit × Qubit)) : ℝ := sInf (pureConcurrenceValues ρ)

theorem pureConcurrenceValues_nonempty (ρ : State (Qubit × Qubit)) :
    (pureConcurrenceValues ρ).Nonempty :=
  ⟨_, spectralPureDecomposition ρ, spectralPureDecomposition_averageState ρ, rfl⟩

theorem pureConcurrenceValues_bddBelow (ρ : State (Qubit × Qubit)) :
    BddBelow (pureConcurrenceValues ρ) :=
  ⟨0, by rintro x ⟨E, _, rfl⟩; exact E.concurrenceCost_mem_Icc.1⟩

theorem concurrence_le_concurrenceCost (E : PureDecomposition (Qubit × Qubit)) :
    concurrence E.averageState ≤ E.concurrenceCost :=
  csInf_le (pureConcurrenceValues_bddBelow _) ⟨E, rfl, rfl⟩

theorem concurrence_mem_Icc (ρ : State (Qubit × Qubit)) :
    concurrence ρ ∈ Set.Icc (0 : ℝ) 1 := by
  constructor
  · apply le_csInf (pureConcurrenceValues_nonempty ρ)
    rintro x ⟨E, _, rfl⟩
    exact E.concurrenceCost_mem_Icc.1
  · have h := concurrence_le_concurrenceCost (spectralPureDecomposition ρ)
    rw [spectralPureDecomposition_averageState] at h
    exact h.trans (PureDecomposition.concurrenceCost_mem_Icc _).2

/-- Jensen's inequality gives the general lower half of the concurrence formula. -/
theorem entanglementCurve_concurrence_le_entanglementOfFormation
    (ρ : State (Qubit × Qubit)) :
    entanglementCurve (concurrence ρ) ≤ entanglementOfFormation ρ := by
  apply le_csInf (pureEntanglementValues_nonempty ρ)
  rintro x ⟨E, hE, rfl⟩
  have hw : ∑ i, (E.probs i : ℝ) = 1 := by exact_mod_cast E.weights_sum
  have hj := entanglementCurve_convexOn.map_sum_le
    (fun i (_ : i ∈ Finset.univ) => NNReal.coe_nonneg (E.probs i)) hw
    (fun i (_ : i ∈ Finset.univ) => pureConcurrence_mem_Icc (E.vectors i))
  calc
    entanglementCurve (concurrence ρ) ≤ entanglementCurve E.concurrenceCost :=
      entanglementCurve_monotoneOn (concurrence_mem_Icc ρ) E.concurrenceCost_mem_Icc
        (by rw [← hE]; exact concurrence_le_concurrenceCost E)
    _ ≤ E.entanglementCost := by
      simpa only [PureDecomposition.concurrenceCost, PureDecomposition.entanglementCost,
        pure_marginalA_vonNeumann, pureConcurrence, smul_eq_mul] using hj

/-- A flat optimal concurrence ensemble also minimizes entanglement. -/
theorem entanglementOfFormation_eq_of_flat_concurrence
    (ρ : State (Qubit × Qubit)) (E : PureDecomposition (Qubit × Qubit))
    (hE : E.averageState = ρ)
    (hflat : ∀ i, 0 < (E.probs i : ℝ) →
      pureConcurrence (E.vectors i) = concurrence ρ) :
    entanglementOfFormation ρ = entanglementCurve (concurrence ρ) := by
  apply le_antisymm _ (entanglementCurve_concurrence_le_entanglementOfFormation ρ)
  have hcost : E.entanglementCost = entanglementCurve (concurrence ρ) := by
    unfold PureDecomposition.entanglementCost
    simp_rw [pure_marginalA_vonNeumann]
    calc
      _ = ∑ i, (E.probs i : ℝ) * entanglementCurve (concurrence ρ) := by
        apply Finset.sum_congr rfl
        intro i _
        by_cases hi : 0 < (E.probs i : ℝ)
        · rw [show 2 * ‖(twoQubitAmplitudeMatrix (E.vectors i)).det‖ = concurrence ρ
            from hflat i hi]
        · have hz : (E.probs i : ℝ) = 0 := le_antisymm (not_lt.mp hi) (NNReal.coe_nonneg _)
          simp [hz]
      _ = _ := by
        rw [← Finset.sum_mul]
        have hw : ∑ i, (E.probs i : ℝ) = 1 := by exact_mod_cast E.weights_sum
        rw [hw, one_mul]
  rw [← hcost, ← hE]
  exact entanglementOfFormation_le_entanglementCost E

/-- Pure concurrence is continuous on the compact space of normalized vectors. -/
theorem pureConcurrence_continuous : Continuous pureConcurrence := by
  unfold pureConcurrence
  simp_rw [twoQubitAmplitudeMatrix_det]
  have h (i : Qubit × Qubit) : Continuous (fun ψ : PureVector (Qubit × Qubit) => ψ.amp i) :=
    (continuous_apply i).comp PureVector.continuous_amp
  exact continuous_const.mul (((h (0, 0)).mul (h (1, 1))).sub
    ((h (0, 1)).mul (h (1, 0)))).norm

/-- The mixed-state concurrence infimum is attained by a finite ensemble with
strictly positive weights. -/
theorem exists_concurrence_minimizer (ρ : State (Qubit × Qubit)) :
    ∃ E : PureDecomposition (Qubit × Qubit), E.averageState = ρ ∧
      (∀ i, 0 < (E.probs i : ℝ)) ∧ E.concurrenceCost = concurrence ρ := by
  obtain ⟨E, hE, hpos, hmin⟩ :=
    exists_minimal_pureDecomposition pureConcurrence pureConcurrence_continuous ρ
  refine ⟨E, hE, hpos, le_antisymm ?_ ?_⟩
  · apply le_csInf (pureConcurrenceValues_nonempty ρ)
    rintro x ⟨D, hD, rfl⟩
    exact hmin D hD
  · rw [← hE]
    exact concurrence_le_concurrenceCost E

end
end AmplitudeDamping
