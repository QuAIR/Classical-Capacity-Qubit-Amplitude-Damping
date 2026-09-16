import AmplitudeDamping.Channel
import QIT.States.Schatten

/-!
# Coordinate lemmas for qubit states

This module records the elementary `2 × 2` facts used by the
equal-excitation decomposition.  Keeping them separate prevents the later
convex-roof argument from depending on entrywise positivity calculations.
-/

open scoped ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Excited-state population of an arbitrary qubit density state. -/
def stateExcitation (rho : State Qubit) : ℝ :=
  (rho.matrix 1 1).re

theorem stateExcitation_nonneg (rho : State Qubit) :
    0 ≤ stateExcitation rho :=
  posSemidef_diagonal_re_nonneg rho.pos 1

theorem qubit_diagonal_sum (rho : State Qubit) :
    (rho.matrix 0 0).re + (rho.matrix 1 1).re = 1 := by
  have h := congrArg Complex.re rho.trace_eq_one
  simpa [Matrix.trace, Fin.sum_univ_two] using h

theorem stateExcitation_le_one (rho : State Qubit) :
    stateExcitation rho ≤ 1 := by
  have h0 := posSemidef_diagonal_re_nonneg rho.pos 0
  have hsum := qubit_diagonal_sum rho
  unfold stateExcitation
  linarith

theorem qubit_diagonal_zero (rho : State Qubit) :
    rho.matrix 0 0 = ((1 - stateExcitation rho : ℝ) : ℂ) := by
  have hreal := rho.pos.isHermitian.coe_re_apply_self 0
  apply Complex.ext
  · have hsum := qubit_diagonal_sum rho
    simp only [Complex.ofReal_re]
    unfold stateExcitation
    linarith
  · have him : (rho.matrix 0 0).im = 0 := by
      have := congrArg Complex.im hreal
      simpa using this.symm
    simpa using him

theorem qubit_diagonal_one (rho : State Qubit) :
    rho.matrix 1 1 = ((stateExcitation rho : ℝ) : ℂ) := by
  have hreal := rho.pos.isHermitian.coe_re_apply_self 1
  simpa [stateExcitation] using hreal.symm

theorem qubit_lower_coherence (rho : State Qubit) :
    rho.matrix 1 0 = star (rho.matrix 0 1) := by
  simpa using (rho.pos.isHermitian.apply 1 0).symm

/-- Coordinate normal form of a qubit density matrix. -/
theorem qubit_state_matrix_eq (rho : State Qubit) :
    rho.matrix =
      !![((1 - stateExcitation rho : ℝ) : ℂ), rho.matrix 0 1;
         star (rho.matrix 0 1), ((stateExcitation rho : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j
  · exact qubit_diagonal_zero rho
  · rfl
  · exact qubit_lower_coherence rho
  · exact qubit_diagonal_one rho

/-- Positivity bounds the squared coherence by `q(1-q)`. -/
theorem qubit_coherence_normSq_le (rho : State Qubit) :
    Complex.normSq (rho.matrix 0 1) ≤
      stateExcitation rho * (1 - stateExcitation rho) := by
  have hdet := rho.pos.det_nonneg
  rw [Matrix.det_fin_two, qubit_diagonal_zero rho,
    qubit_diagonal_one rho, qubit_lower_coherence rho] at hdet
  have hre := (Complex.nonneg_iff.mp hdet).1
  simp only [Complex.sub_re, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, mul_zero, sub_zero] at hre
  have hcoh :
      ((rho.matrix 0 1) * star (rho.matrix 0 1)).re =
        Complex.normSq (rho.matrix 0 1) := by
    have h := congrArg Complex.re
      (@Complex.normSq_eq_conj_mul_self (rho.matrix 0 1))
    simpa [mul_comm] using h.symm
  rw [← Complex.mul_re, hcoh] at hre
  simpa [mul_comm] using hre

end

end AmplitudeDamping
