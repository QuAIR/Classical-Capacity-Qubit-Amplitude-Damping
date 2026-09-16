import AmplitudeDamping.QubitEntropy
import AmplitudeDamping.ConvexRoof
import Mathlib.Analysis.Convex.Jensen
import QIT.Information.Entropy.Entropy

/-!
# Pure qubit inputs at fixed excitation

This module begins the formalization of the manuscript's fixed-excitation
lemma.  The algebraic invariant is that the determinant of the damped pure
output depends only on the excited-state population.
-/

open scoped ComplexConjugate ComplexOrder MatrixOrder NNReal

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Excited-state population of a normalized pure qubit. -/
def excitationProbability (ψ : PureVector Qubit) : ℝ :=
  Complex.normSq (ψ.amp 1)

/-- Excited-state population of an arbitrary qubit density state. -/
def stateExcitation (ρ : State Qubit) : ℝ :=
  (ρ.matrix 1 1).re

@[simp]
theorem stateExcitation_pure (ψ : PureVector Qubit) :
    stateExcitation ψ.state = excitationProbability ψ := by
  simp [stateExcitation, excitationProbability, PureVector.state_matrix_apply,
    Complex.mul_conj]

/-- Excitation is affine under a finite pure-state decomposition. -/
theorem stateExcitation_average (E : PureDecomposition Qubit) :
    stateExcitation E.averageState =
      ∑ i, (E.probs i).toReal * excitationProbability (E.vectors i) := by
  unfold stateExcitation PureDecomposition.averageState
  rw [Ensemble.averageState_matrix]
  simp [PureDecomposition.toEnsemble, excitationProbability,
    Matrix.sum_apply, Matrix.smul_apply, rankOneMatrix_apply, Complex.mul_conj]
  apply Finset.sum_congr rfl
  intro i _
  change (((E.probs i : ℂ) * (Complex.normSq ((E.vectors i).amp 1) : ℂ)).re) = _
  norm_num

/-- Output entropy curve for pure inputs of excitation `q`. -/
def dampingEntropyCurve (p q : ℝ) : ℝ :=
  entanglementCurve (2 * Real.sqrt (p * (1 - p)) * q)

theorem qubit_normSq_sum_eq_one (ψ : PureVector Qubit) :
    Complex.normSq (ψ.amp 0) + Complex.normSq (ψ.amp 1) = 1 := by
  have h := congrArg Complex.re ψ.trace_rankOne_eq_one
  simpa [rankOneMatrix_trace, dotProduct, Complex.normSq] using h

theorem excitationProbability_nonneg (ψ : PureVector Qubit) :
    0 ≤ excitationProbability ψ :=
  Complex.normSq_nonneg _

theorem excitationProbability_le_one (ψ : PureVector Qubit) :
    excitationProbability ψ ≤ 1 := by
  have h0 := Complex.normSq_nonneg (ψ.amp 0)
  have hsum := qubit_normSq_sum_eq_one ψ
  unfold excitationProbability
  linarith

/-- The determinant of a damped pure output is `p(1-p)q²`, where `q` is the
input excitation probability. -/
theorem amplitudeDamping_pure_output_det
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ψ : PureVector Qubit) :
    Matrix.det ((amplitudeDamping p hp0 hp1).applyState ψ.state).matrix =
      ((p * (1 - p) * (excitationProbability ψ) ^ 2 : ℝ) : ℂ) := by
  rw [amplitudeDamping_applyState_matrix, Matrix.det_fin_two]
  simp only [PureVector.state_matrix_apply]
  simp
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hsq1pC : (Real.sqrt (1 - p) : ℂ) ^ 2 = ((1 - p : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt h1p
  ring_nf
  rw [hsq1pC]
  unfold excitationProbability
  push_cast
  ring_nf
  have hz :
      ψ.amp 1 * (starRingEnd ℂ) (ψ.amp 1) =
        (Complex.normSq (ψ.amp 1) : ℂ) := by
    simpa using Complex.mul_conj (ψ.amp 1)
  have hz2 :
      ψ.amp 1 ^ 2 * (starRingEnd ℂ) (ψ.amp 1) ^ 2 =
        (Complex.normSq (ψ.amp 1) : ℂ) ^ 2 := by
    rw [← mul_pow, hz]
  have hmul (c : ℂ) :
      c * ψ.amp 1 ^ 2 * (starRingEnd ℂ) (ψ.amp 1) ^ 2 =
        c * (Complex.normSq (ψ.amp 1) : ℂ) ^ 2 := by
    rw [mul_assoc, hz2]
  rw [hmul (p : ℂ), hmul ((p : ℂ) ^ 2)]

/-- The output entropy of a pure input depends only on its excitation
probability. -/
theorem amplitudeDamping_pure_output_entropy
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ψ : PureVector Qubit) :
    ((amplitudeDamping p hp0 hp1).applyState ψ.state).vonNeumann =
      dampingEntropyCurve p (excitationProbability ψ) := by
  let σ := (amplitudeDamping p hp0 hp1).applyState ψ.state
  have hdetC := amplitudeDamping_pure_output_det p hp0 hp1 ψ
  have hdet : qubitDeterminant σ =
      p * (1 - p) * (excitationProbability ψ) ^ 2 := by
    have hre := congrArg Complex.re hdetC
    have hqcast :
        (((excitationProbability ψ : ℝ) : ℂ) ^ 2).re =
          (excitationProbability ψ) ^ 2 := by
      simp [pow_two]
    simpa [qubitDeterminant, σ, hqcast] using hre
  have hcoef : 0 ≤ p * (1 - p) :=
    mul_nonneg hp0 (sub_nonneg.mpr hp1)
  have hq : 0 ≤ excitationProbability ψ := excitationProbability_nonneg ψ
  rw [qubit_vonNeumann_eq_entanglementCurve_det]
  unfold dampingEntropyCurve
  rw [hdet, Real.sqrt_mul hcoef, Real.sqrt_sq hq]
  ring_nf

/-- The cost of a pure decomposition is the probability-weighted average of
the scalar damping entropy curve. -/
theorem pureDecomposition_amplitudeDamping_outputCost
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (E : PureDecomposition Qubit) :
    E.outputCost (amplitudeDamping p hp0 hp1) =
      ∑ i, (E.probs i).toReal *
        dampingEntropyCurve p (excitationProbability (E.vectors i)) := by
  unfold PureDecomposition.outputCost outputEntropyCost
  apply Finset.sum_congr rfl
  intro i _
  rw [show E.toEnsemble.states i = (E.vectors i).state from rfl]
  rw [amplitudeDamping_pure_output_entropy]
  rfl

/-- Jensen lower bound for an arbitrary pure decomposition, conditional only
on convexity of the scalar curve.  This isolates the remaining calculus lemma
from the quantum part of the fixed-excitation proof. -/
theorem dampingEntropyCurve_le_outputCost_of_convex
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hconv : ConvexOn ℝ (Set.Icc 0 1) (dampingEntropyCurve p))
    (E : PureDecomposition Qubit) :
    dampingEntropyCurve p (stateExcitation E.averageState) ≤
      E.outputCost (amplitudeDamping p hp0 hp1) := by
  rw [pureDecomposition_amplitudeDamping_outputCost,
    stateExcitation_average]
  have hj := hconv.map_sum_le
    (t := Finset.univ)
    (w := fun i => (E.probs i).toReal)
    (p := fun i => excitationProbability (E.vectors i))
    (fun i _ => NNReal.coe_nonneg (E.probs i))
    (by
      have hw := congrArg (fun x : ℝ≥0 => (x : ℝ)) E.weights_sum
      simpa using hw)
    (fun i _ => ⟨excitationProbability_nonneg (E.vectors i),
      excitationProbability_le_one (E.vectors i)⟩)
  simpa [smul_eq_mul] using hj

/-- Jensen gives the lower bound half of the fixed-excitation roof formula.
The explicit decomposition hypothesis will later be discharged uniformly by
the spectral-decomposition module (and, for the matching upper bound, by the
two-state equal-excitation construction). -/
theorem dampingEntropyCurve_le_outputEntropyRoof_of_convex_of_decomposition
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hconv : ConvexOn ℝ (Set.Icc 0 1) (dampingEntropyCurve p))
    (ρ : State Qubit)
    (hdecomp : ∃ E : PureDecomposition Qubit, E.averageState = ρ) :
    dampingEntropyCurve p (stateExcitation ρ) ≤
      outputEntropyRoof (amplitudeDamping p hp0 hp1) ρ := by
  apply le_csInf
  · rcases hdecomp with ⟨E, hE⟩
    exact ⟨E.outputCost (amplitudeDamping p hp0 hp1), E, hE, rfl⟩
  · intro x hx
    rcases hx with ⟨E, hE, rfl⟩
    have hJ := dampingEntropyCurve_le_outputCost_of_convex p hp0 hp1 hconv E
    simpa [hE] using hJ

/-- Lower bound half of the fixed-excitation convex-roof formula. -/
theorem dampingEntropyCurve_le_outputEntropyRoof_of_convex
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hconv : ConvexOn ℝ (Set.Icc 0 1) (dampingEntropyCurve p))
    (ρ : State Qubit) :
    dampingEntropyCurve p (stateExcitation ρ) ≤
      outputEntropyRoof (amplitudeDamping p hp0 hp1) ρ :=
  dampingEntropyCurve_le_outputEntropyRoof_of_convex_of_decomposition
    p hp0 hp1 hconv ρ (exists_pureDecomposition ρ)

end

end AmplitudeDamping
