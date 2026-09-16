import AmplitudeDamping.Triangular.TraceCompression
import AmplitudeDamping.QubitEntropy

/-!
# Scalar normalization for the triangular entropy inequality

This module identifies the normalized one-dimensional coupling entropy with
the binary-spectrum entanglement curve appearing in the final statement.
-/

open scoped BigOperators ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Relabel the two scalar blocks as the computational qubit basis. -/
def scalarQubitEquiv : Sum Unit Unit ≃ Qubit where
  toFun
    | Sum.inl _ => 0
    | Sum.inr _ => 1
  invFun i := if i = 0 then Sum.inl Unit.unit else Sum.inr Unit.unit
  left_inv x := by
    rcases x with u | u <;> cases u <;> simp
  right_inv i := by
    fin_cases i <;> simp

/-- Explicit qubit form of the scalar coupling block. -/
theorem scalarCouplingBlock_reindex
    (p q r : ℝ) :
    (scalarCouplingBlock p q r).submatrix
        scalarQubitEquiv.symm scalarQubitEquiv.symm =
      !![((p + q : ℝ) : ℂ), ((Real.sqrt q * Real.sqrt r : ℝ) : ℂ);
         ((Real.sqrt r * Real.sqrt q : ℝ) : ℂ), ((r : ℝ) : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [scalarCouplingBlock, scalarMatrix, scalarQubitEquiv,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂]

/-- The determinant of a scalar coupling block is `p*r`; the middle scalar
does not enter. -/
theorem scalarCouplingBlock_reindex_det
    (p q r : ℝ) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    ((scalarCouplingBlock p q r).submatrix
      scalarQubitEquiv.symm scalarQubitEquiv.symm).det = ((p * r : ℝ) : ℂ) := by
  rw [scalarCouplingBlock_reindex, Matrix.det_fin_two]
  change ((p + q : ℝ) : ℂ) * (r : ℂ) -
      ((Real.sqrt q * Real.sqrt r : ℝ) : ℂ) *
        ((Real.sqrt r * Real.sqrt q : ℝ) : ℂ) = ((p * r : ℝ) : ℂ)
  norm_cast
  calc
    (p + q) * r - Real.sqrt q * Real.sqrt r *
        (Real.sqrt r * Real.sqrt q) =
      (p + q) * r - (Real.sqrt q * Real.sqrt q) *
        (Real.sqrt r * Real.sqrt r) := by ring
    _ = (p + q) * r - q * r := by
      rw [Real.mul_self_sqrt hq, Real.mul_self_sqrt hr]
    _ = p * r := by ring

/-- When `p+q+r=1`, the scalar coupling block is a qubit density matrix whose
entropy is the manuscript's entanglement curve. -/
theorem scalarCouplingBlock_entropy_eq_entanglementCurve
    (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hsum : p + q + r = 1) :
    psdEntropy (scalarCouplingBlock p q r)
        (scalarCouplingBlock_posSemidef p q r hp hq hr) =
      entanglementCurve (2 * Real.sqrt (p * r)) := by
  let M : Matrix Qubit Qubit ℂ :=
    (scalarCouplingBlock p q r).submatrix
      scalarQubitEquiv.symm scalarQubitEquiv.symm
  let hM : M.PosSemidef :=
    (scalarCouplingBlock_posSemidef p q r hp hq hr).submatrix
      scalarQubitEquiv.symm
  have htrace : M.trace = 1 := by
    rw [show M =
        !![((p + q : ℝ) : ℂ), ((Real.sqrt q * Real.sqrt r : ℝ) : ℂ);
           ((Real.sqrt r * Real.sqrt q : ℝ) : ℂ), ((r : ℝ) : ℂ)] by
      exact scalarCouplingBlock_reindex p q r]
    simp
    exact_mod_cast hsum
  let rho : State Qubit := ⟨M, hM, htrace⟩
  have hdet : qubitDeterminant rho = p * r := by
    unfold qubitDeterminant rho
    change M.det.re = p * r
    rw [show M.det = ((p * r : ℝ) : ℂ) by
      exact scalarCouplingBlock_reindex_det p q r hq hr]
    simp
  calc
    psdEntropy (scalarCouplingBlock p q r)
        (scalarCouplingBlock_posSemidef p q r hp hq hr) =
        psdEntropy M hM := by
      exact (psdEntropy_reindex
        (scalarCouplingBlock p q r)
        (scalarCouplingBlock_posSemidef p q r hp hq hr)
        scalarQubitEquiv).symm
    _ = rho.vonNeumann := psdEntropy_state rho
    _ = entanglementCurve (2 * Real.sqrt (qubitDeterminant rho)) :=
      qubit_vonNeumann_eq_entanglementCurve_det rho
    _ = entanglementCurve (2 * Real.sqrt (p * r)) := by rw [hdet]

/-- Closed normalized formula for the scalar entropy defect. -/
theorem scalarEntropyDefect_eq_entanglementCurve
    (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r)
    (hsum : p + q + r = 1) :
    scalarEntropyDefect p q r hp hq hr =
      entanglementCurve (2 * Real.sqrt (p * r)) +
        QIT.xlog2 p + QIT.xlog2 q + QIT.xlog2 r := by
  have hcoupling :
      psdEntropy
          (entropyCoupling (scalarMatrix p) (scalarMatrix q) (scalarMatrix r))
          (entropyCoupling_posSemidef
            (scalarMatrix p) (scalarMatrix q) (scalarMatrix r)
            (scalarMatrix_posSemidef p hp)
            (scalarMatrix_posSemidef q hq)
            (scalarMatrix_posSemidef r hr)) =
        entanglementCurve (2 * Real.sqrt (p * r)) := by
    calc
      _ = psdEntropy (scalarCouplingBlock p q r)
          (scalarCouplingBlock_posSemidef p q r hp hq hr) :=
        psdEntropy_congr
          (scalarCouplingBlock_eq_entropyCoupling p q r hq hr).symm _ _
      _ = _ := scalarCouplingBlock_entropy_eq_entanglementCurve
        p q r hp hq hr hsum
  unfold scalarEntropyDefect entropyDefect
  rw [hcoupling, psdEntropy_scalarMatrix p hp,
    psdEntropy_scalarMatrix q hq, psdEntropy_scalarMatrix r hr]
  ring

end

end AmplitudeDamping
