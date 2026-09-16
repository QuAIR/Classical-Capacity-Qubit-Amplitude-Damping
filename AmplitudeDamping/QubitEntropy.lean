import AmplitudeDamping.Channel
import AmplitudeDamping.Triangular.Statement

/-!
# Entropy of a qubit state from its determinant

For a trace-one positive `2 x 2` matrix, the two eigenvalues are determined by
the determinant.  This module supplies the spectral bridge needed by the
fixed-excitation calculation.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Real determinant of a qubit density matrix. -/
def qubitDeterminant (ρ : State Qubit) : ℝ :=
  ρ.matrix.det.re

theorem qubit_eigenvalues_sum (ρ : State Qubit) :
    ρ.pos.isHermitian.eigenvalues 0 + ρ.pos.isHermitian.eigenvalues 1 = 1 := by
  have h := congrArg Complex.re ρ.pos.isHermitian.trace_eq_sum_eigenvalues
  rw [ρ.trace_eq_one] at h
  simpa using h.symm

theorem qubit_eigenvalues_product (ρ : State Qubit) :
    ρ.pos.isHermitian.eigenvalues 0 * ρ.pos.isHermitian.eigenvalues 1 =
      qubitDeterminant ρ := by
  have h := congrArg Complex.re ρ.pos.isHermitian.det_eq_prod_eigenvalues
  simpa [qubitDeterminant] using h.symm

theorem qubitDeterminant_nonneg (ρ : State Qubit) :
    0 ≤ qubitDeterminant ρ := by
  rw [← qubit_eigenvalues_product]
  exact mul_nonneg (ρ.pos.eigenvalues_nonneg 0) (ρ.pos.eigenvalues_nonneg 1)

theorem qubit_discriminant_eq_sq_eigenvalue_sub (ρ : State Qubit) :
    1 - 4 * qubitDeterminant ρ =
      (ρ.pos.isHermitian.eigenvalues 0 -
        ρ.pos.isHermitian.eigenvalues 1) ^ 2 := by
  rw [← qubit_eigenvalues_product]
  have hsum := qubit_eigenvalues_sum ρ
  nlinarith

theorem binaryEntropy_one_sub (q : ℝ) :
    binaryEntropy (1 - q) = binaryEntropy q := by
  unfold binaryEntropy
  ring_nf

theorem qubit_vonNeumann_eq_binaryEntropy_eigenvalue_zero (ρ : State Qubit) :
    ρ.vonNeumann = binaryEntropy (ρ.pos.isHermitian.eigenvalues 0) := by
  have hsum := qubit_eigenvalues_sum ρ
  have h1 : ρ.pos.isHermitian.eigenvalues 1 =
      1 - ρ.pos.isHermitian.eigenvalues 0 := by
    linarith
  rw [State.vonNeumann]
  simp only [Fin.sum_univ_two]
  rw [h1]
  unfold binaryEntropy
  ring

/-- A qubit state's entropy is determined by its determinant.  The argument
`2 * sqrt(det ρ)` is the concurrence-style parameter used in the manuscript. -/
theorem qubit_vonNeumann_eq_entanglementCurve_det (ρ : State Qubit) :
    ρ.vonNeumann =
      entanglementCurve (2 * Real.sqrt (qubitDeterminant ρ)) := by
  let lam0 := ρ.pos.isHermitian.eigenvalues 0
  let lam1 := ρ.pos.isHermitian.eigenvalues 1
  have hsum : lam0 + lam1 = 1 := qubit_eigenvalues_sum ρ
  have hd : 0 ≤ qubitDeterminant ρ := qubitDeterminant_nonneg ρ
  have hsqrtDet : (Real.sqrt (qubitDeterminant ρ)) ^ 2 = qubitDeterminant ρ :=
    Real.sq_sqrt hd
  have hdisc : 1 - 4 * qubitDeterminant ρ = (lam0 - lam1) ^ 2 := by
    simpa [lam0, lam1] using qubit_discriminant_eq_sq_eigenvalue_sub ρ
  have hsqrtDisc :
      Real.sqrt (1 - (2 * Real.sqrt (qubitDeterminant ρ)) ^ 2) =
        |lam0 - lam1| := by
    have hinside :
        1 - (2 * Real.sqrt (qubitDeterminant ρ)) ^ 2 =
          (lam0 - lam1) ^ 2 := by
      nlinarith
    rw [hinside, Real.sqrt_sq_eq_abs]
  rw [qubit_vonNeumann_eq_binaryEntropy_eigenvalue_zero]
  unfold entanglementCurve
  rw [hsqrtDisc]
  by_cases horder : lam1 ≤ lam0
  · rw [abs_of_nonneg (sub_nonneg.mpr horder)]
    have harg : (1 + (lam0 - lam1)) / 2 = lam0 := by linarith
    simp [lam0, harg]
  · have horder' : lam0 ≤ lam1 := le_of_not_ge horder
    rw [abs_of_nonpos (sub_nonpos.mpr horder')]
    have harg : (1 + -(lam0 - lam1)) / 2 = lam1 := by linarith
    rw [harg]
    have hlam1 : lam1 = 1 - lam0 := by linarith
    rw [hlam1, binaryEntropy_one_sub]

end

end AmplitudeDamping
