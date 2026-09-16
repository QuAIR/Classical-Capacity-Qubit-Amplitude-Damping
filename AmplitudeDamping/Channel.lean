import QIT.Core.Channel
import Mathlib.LinearAlgebra.Matrix.Notation

/-!
# The qubit amplitude-damping channel

This module gives the Kraus realization used by the manuscript.  The channel
is defined only for the physical parameter range `0 ≤ p ≤ 1`; trace
preservation is proved from the Kraus completeness relation.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Computational qubit basis. -/
abbrev Qubit := Fin 2

/-- No-jump Kraus operator of amplitude damping. -/
def amplitudeKrausZero (p : ℝ) : Matrix Qubit Qubit ℂ :=
  !![(1 : ℂ), 0; 0, (Real.sqrt (1 - p) : ℂ)]

/-- Decay Kraus operator of amplitude damping. -/
def amplitudeKrausOne (p : ℝ) : Matrix Qubit Qubit ℂ :=
  !![0, (Real.sqrt p : ℂ); 0, 0]

/-- Two-element Kraus family for amplitude damping. -/
def amplitudeKraus (p : ℝ) : Fin 2 → Matrix Qubit Qubit ℂ :=
  ![amplitudeKrausZero p, amplitudeKrausOne p]

/-- The two amplitude-damping Kraus operators obey the completeness
relation. -/
theorem amplitudeKraus_completeness (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    MatrixMap.krausAdjoint (amplitudeKraus p) (1 : CMatrix Qubit) = 1 := by
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hsqp : (Real.sqrt p) ^ 2 = p := Real.sq_sqrt hp0
  have hsq1p : (Real.sqrt (1 - p)) ^ 2 = 1 - p := Real.sq_sqrt h1p
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MatrixMap.krausAdjoint, amplitudeKraus, amplitudeKrausZero,
      amplitudeKrausOne, Matrix.mul_apply]
  norm_cast
  nlinarith [hsqp, hsq1p]

/-- Qubit amplitude damping with decay probability `p`. -/
def amplitudeDamping (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel Qubit Qubit where
  map := MatrixMap.ofKraus (amplitudeKraus p)
  completelyPositive := MatrixMap.ofKraus_completelyPositive _
  tracePreserving :=
    MatrixMap.ofKraus_isTracePreserving_of_krausAdjoint_one _
      (amplitudeKraus_completeness p hp0 hp1)
  mapsPositive := MatrixMap.ofKraus_mapsPositive _

@[simp]
theorem amplitudeDamping_map (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : CMatrix Qubit) :
    (amplitudeDamping p hp0 hp1).map X = MatrixMap.ofKraus (amplitudeKraus p) X :=
  rfl

/-- Entrywise action of amplitude damping on an arbitrary qubit matrix. -/
theorem amplitudeDamping_map_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (X : CMatrix Qubit) :
    (amplitudeDamping p hp0 hp1).map X =
      !![X 0 0 + (p : ℂ) * X 1 1,
          (Real.sqrt (1 - p) : ℂ) * X 0 1;
         (Real.sqrt (1 - p) : ℂ) * X 1 0,
          ((1 - p : ℝ) : ℂ) * X 1 1] := by
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have hsqpC : (Real.sqrt p : ℂ) ^ 2 = (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp0
  have hsq1p : (Real.sqrt (1 - p)) ^ 2 = 1 - p := Real.sq_sqrt h1p
  have hsq1pC : (Real.sqrt (1 - p) : ℂ) ^ 2 = ((1 - p : ℝ) : ℂ) := by
    exact_mod_cast hsq1p
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [amplitudeDamping, MatrixMap.ofKraus, amplitudeKraus,
      amplitudeKrausZero, amplitudeKrausOne, Matrix.mul_apply,
      Matrix.vecMul, dotProduct] <;>
    ring_nf
  · rw [hsqpC]
    ring_nf
  · rw [hsq1pC]
    push_cast
    ring

/-- Entrywise density-matrix formula for amplitude damping. -/
theorem amplitudeDamping_applyState_matrix (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ρ : State Qubit) :
    ((amplitudeDamping p hp0 hp1).applyState ρ).matrix =
      !![ρ.matrix 0 0 + (p : ℂ) * ρ.matrix 1 1,
          (Real.sqrt (1 - p) : ℂ) * ρ.matrix 0 1;
         (Real.sqrt (1 - p) : ℂ) * ρ.matrix 1 0,
          ((1 - p : ℝ) : ℂ) * ρ.matrix 1 1] :=
  amplitudeDamping_map_eq p hp0 hp1 ρ.matrix

end

end AmplitudeDamping
