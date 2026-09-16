import AmplitudeDamping.Channel
import QIT.Information.Entropy.Entropy

/-!
# Pure qubit inputs at fixed excitation

This module begins the formalization of the manuscript's fixed-excitation
lemma.  The algebraic invariant is that the determinant of the damped pure
output depends only on the excited-state population.
-/

open scoped ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Excited-state population of a normalized pure qubit. -/
def excitationProbability (ψ : PureVector Qubit) : ℝ :=
  Complex.normSq (ψ.amp 1)

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

end

end AmplitudeDamping
