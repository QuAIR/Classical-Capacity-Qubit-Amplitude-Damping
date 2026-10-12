import QIT.States.PosSqrt
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-! # Positive perturbations inside the support of a state -/

open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
namespace AmplitudeDamping
open QIT Matrix
noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

/-- A Hermitian perturbation conjugated by the square root of a state can be
scaled in both signs while retaining positivity, including for singular states. -/
theorem exists_pos_psd_sqrt_perturbation (ρ : State a)
    (X : Matrix a a ℂ) (hX : X.IsHermitian) :
    ∃ t : ℝ, 0 < t ∧
      (ρ.matrix + t • (ρ.sqrtMatrix * X * ρ.sqrtMatrix)).PosSemidef ∧
      (ρ.matrix - t • (ρ.sqrtMatrix * X * ρ.sqrtMatrix)).PosSemidef := by
  letI : CStarAlgebra (Matrix a a ℂ) := {}
  let H := ρ.sqrtMatrix * X * ρ.sqrtMatrix
  have hstar : star ρ.sqrtMatrix = ρ.sqrtMatrix := ρ.sqrtMatrix_isHermitian.eq
  have hu : H ≤ ‖X‖ • ρ.matrix := by
    simpa only [H, hstar, ρ.sqrtMatrix_mul_self] using
      (CStarAlgebra.star_left_conjugate_le_norm_smul (a := ρ.sqrtMatrix) hX.isSelfAdjoint)
  have hl : -H ≤ ‖X‖ • ρ.matrix := by
    simpa only [H, hstar, Matrix.mul_neg, Matrix.neg_mul, norm_neg, ρ.sqrtMatrix_mul_self] using
      (CStarAlgebra.star_left_conjugate_le_norm_smul (a := ρ.sqrtMatrix) hX.isSelfAdjoint.neg)
  let t : ℝ := (‖X‖ + 1)⁻¹
  have ht : 0 < t := inv_pos.mpr (by positivity)
  have hbound : t * ‖X‖ ≤ 1 := by
    dsimp [t]
    rw [inv_mul_le_iff₀ (by positivity : 0 < ‖X‖ + 1)]
    linarith
  have hscale : t • (‖X‖ • ρ.matrix) ≤ ρ.matrix := by
    rw [← mul_smul]
    simpa using smul_le_smul_of_nonneg_right hbound ρ.pos.nonneg
  have hupper : t • H ≤ ρ.matrix :=
    (smul_le_smul_of_nonneg_left hu ht.le).trans hscale
  have hlower : -(t • H) ≤ ρ.matrix := by
    simpa only [smul_neg] using (smul_le_smul_of_nonneg_left hl ht.le).trans hscale
  refine ⟨t, ht, ?_, ?_⟩
  · exact (show 0 ≤ ρ.matrix + t • H from neg_le_iff_add_nonneg.mp hlower).posSemidef
  · exact (sub_nonneg.mpr hupper).posSemidef

end
end AmplitudeDamping
