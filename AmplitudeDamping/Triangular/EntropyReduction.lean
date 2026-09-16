import AmplitudeDamping.Triangular.LogDetCalculus
import Mathlib.LinearAlgebra.Matrix.SchurComplement

/-!
# Algebraic layer of the triangular entropy reduction

This module formalizes the finite-dimensional matrix structure used in Steps
1 and 2 of the triangular block entropy proof.  It proves that the coupling
matrix `Z(P,Q,R)` is a Gram matrix, records its trace, and applies the
log-determinant theorem to prove joint convexity in the two outer variables of
the shifted fixed-middle log-determinant integrand.

The entropy-integral passage and the resulting fixed-middle convexity of the
entropy defect are completed in `Triangular.EntropyIntegral`.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

universe u


noncomputable section

/-- The positive block matrix `Z(P,Q,R)` from the entropy reduction. -/
def entropyCoupling {d : Type u} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ) : Matrix (Sum d d) (Sum d d) ℂ :=
  Matrix.fromBlocks (P + Q) (QIT.psdSqrt Q * QIT.psdSqrt R)
    (QIT.psdSqrt R * QIT.psdSqrt Q) R

/-- Lower-triangular square-root factor whose Gram matrix is
`entropyCoupling P Q R`. -/
def entropyCouplingSqrtFactor {d : Type u} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ) : Matrix (Sum d d) (Sum d d) ℂ :=
  Matrix.fromBlocks (QIT.psdSqrt P) 0 (QIT.psdSqrt Q) (QIT.psdSqrt R)

/-- Exact Gram factorization of `Z(P,Q,R)`. -/
theorem entropyCoupling_eq_sqrtFactor_gram
    {d : Type u} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef) :
    (entropyCouplingSqrtFactor P Q R).conjTranspose *
        entropyCouplingSqrtFactor P Q R = entropyCoupling P Q R := by
  rw [show (entropyCouplingSqrtFactor P Q R).conjTranspose =
      Matrix.fromBlocks (QIT.psdSqrt P) (QIT.psdSqrt Q) 0
        (QIT.psdSqrt R) by
    unfold entropyCouplingSqrtFactor
    rw [Matrix.fromBlocks_conjTranspose]
    simp only [Matrix.conjTranspose_zero]
    rw [(QIT.psdSqrt_isHermitian P).eq,
      (QIT.psdSqrt_isHermitian Q).eq,
      (QIT.psdSqrt_isHermitian R).eq]]
  unfold entropyCouplingSqrtFactor
  rw [Matrix.fromBlocks_multiply]
  simp [entropyCoupling, QIT.psdSqrt_mul_self_of_posSemidef hP,
    QIT.psdSqrt_mul_self_of_posSemidef hQ,
    QIT.psdSqrt_mul_self_of_posSemidef hR]

/-- The coupling matrix is positive semidefinite. -/
theorem entropyCoupling_posSemidef
    {d : Type u} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef) :
    (entropyCoupling P Q R).PosSemidef := by
  rw [← entropyCoupling_eq_sqrtFactor_gram P Q R hP hQ hR]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- The trace of the coupling matrix is the sum of the three input traces. -/
theorem entropyCoupling_trace
    {d : Type u} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ) :
    (entropyCoupling P Q R).trace = P.trace + Q.trace + R.trace := by
  simp [entropyCoupling, Matrix.trace, Fintype.sum_sum_type,
    Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₂,
    Finset.sum_add_distrib]

/-- Positive-definite block-diagonal shift of the two outer variables. -/
def outerShift {d : Type u} [Fintype d] [DecidableEq d]
    (s : ℝ) (P R : Matrix d d ℂ) : Matrix (Sum d d) (Sum d d) ℂ :=
  Matrix.fromBlocks (P + s • 1) 0 0 (R + s • 1)

/-- The fixed skew-Hermitian middle perturbation at integral parameter `s`. -/
def middleSkew {d : Type u} [Fintype d] [DecidableEq d]
    (s : ℝ) (Q : Matrix d d ℂ) : Matrix (Sum d d) (Sum d d) ℂ :=
  let K := Real.sqrt s • QIT.psdSqrt Q
  Matrix.fromBlocks 0 K (-K) 0

/-- Positive semidefinite outer variables become positive definite after a
strictly positive scalar shift. -/
theorem outerShift_posDef
    {d : Type u} [Fintype d] [DecidableEq d]
    (s : ℝ) (hs : 0 < s) (P R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hR : R.PosSemidef) :
    (outerShift s P R).PosDef := by
  apply Matrix.fromBlocks_diagonal_posDef
  · exact Matrix.PosDef.posSemidef_add hP
      (Matrix.PosDef.smul Matrix.PosDef.one hs)
  · exact Matrix.PosDef.posSemidef_add hR
      (Matrix.PosDef.smul Matrix.PosDef.one hs)

/-- The middle block perturbation is skew-Hermitian. -/
theorem middleSkew_skewHermitian
    {d : Type u} [Fintype d] [DecidableEq d]
    (s : ℝ) (Q : Matrix d d ℂ) :
    (middleSkew s Q).conjTranspose = -middleSkew s Q := by
  let K := Real.sqrt s • QIT.psdSqrt Q
  have hK : K.conjTranspose = K := by
    dsimp [K]
    rw [Matrix.conjTranspose_smul, (QIT.psdSqrt_isHermitian Q).eq]
    simp
  rw [show middleSkew s Q = Matrix.fromBlocks 0 K (-K) 0 by rfl]
  rw [Matrix.fromBlocks_conjTranspose, hK, Matrix.fromBlocks_neg]
  simp
  exact hK

/-- Schur-complement determinant identity connecting the entropy coupling
matrix to the skew log-determinant normal form.

For `s > 0`, shifting `Z(P,Q,R)` by `sI` has the same determinant as
`outerShift s P R + middleSkew s Q`.  This is the exact algebraic identity
used to rewrite the entropy-integral integrand. -/
theorem entropyCoupling_shift_det_eq
    {d : Type u} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ) (hQ : Q.PosSemidef) (hR : R.PosSemidef)
    (s : ℝ) (hs : 0 < s) :
    (entropyCoupling P Q R + s • 1).det =
      (outerShift s P R + middleSkew s Q).det := by
  let S : Matrix d d ℂ := QIT.psdSqrt R
  let U : Matrix d d ℂ := QIT.psdSqrt Q
  let D : Matrix d d ℂ := R + s • 1
  have hD : D.PosDef := Matrix.PosDef.posSemidef_add hR
    (Matrix.PosDef.smul Matrix.PosDef.one hs)
  have hDunit : IsUnit D := (Matrix.isUnit_iff_isUnit_det D).mpr
    (isUnit_iff_ne_zero.mpr hD.det_pos.ne')
  letI : Invertible D := hDunit.invertible
  have hleft : entropyCoupling P Q R + s • 1 =
      Matrix.fromBlocks (P + Q + s • 1) (U * S) (S * U) D := by
    unfold entropyCoupling
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_add]
    simp [U, S, D]
  have hright : outerShift s P R + middleSkew s Q =
      Matrix.fromBlocks (P + s • 1) (Real.sqrt s • U)
        (-(Real.sqrt s • U)) D := by
    unfold outerShift middleSkew
    rw [Matrix.fromBlocks_add]
    simp [U, D]
  rw [hleft, hright, Matrix.det_fromBlocks₂₂, Matrix.det_fromBlocks₂₂]
  congr 1
  congr 1
  have hSS : S * S = R := QIT.psdSqrt_mul_self_of_posSemidef hR
  have hUU : U * U = Q := QIT.psdSqrt_mul_self_of_posSemidef hQ
  have hSD : S * D = D * S := by
    dsimp [D]
    rw [← hSS]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
    noncomm_ring
  have hSV : S * ⅟D = ⅟D * S :=
    (Commute.invOf_right (show Commute S D from hSD)).eq
  have hDinv : D * ⅟D = 1 := mul_invOf_self D
  have hRV : R * ⅟D + s • ⅟D = 1 := by
    calc
      R * ⅟D + s • ⅟D = (R + s • 1) * ⅟D := by
        simp [Matrix.add_mul]
      _ = D * ⅟D := by rfl
      _ = 1 := hDinv
  have hres : 1 - S * ⅟D * S = s • ⅟D := by
    have hmove : S * ⅟D * S = R * ⅟D := by
      calc
        S * ⅟D * S = S * (⅟D * S) := Matrix.mul_assoc _ _ _
        _ = S * (S * ⅟D) := by rw [hSV]
        _ = (S * S) * ⅟D := (Matrix.mul_assoc _ _ _).symm
        _ = R * ⅟D := by rw [hSS]
    rw [hmove]
    calc
      1 - R * ⅟D = (R * ⅟D + s • ⅟D) - R * ⅟D := by rw [hRV]
      _ = s • ⅟D := by noncomm_ring
  have hsqrtR : Real.sqrt s * Real.sqrt s = s := Real.mul_self_sqrt hs.le
  calc
    P + Q + s • 1 - U * S * ⅟D * (S * U) =
        P + s • 1 + U * (1 - S * ⅟D * S) * U := by
      rw [← hUU]
      noncomm_ring
    _ = P + s • 1 + s • (U * ⅟D * U) := by
      rw [hres]
      simp
    _ = P + s • 1 - √s • U * ⅟D * -(√s • U) := by
      simp only [Matrix.mul_neg, sub_neg_eq_add, Matrix.smul_mul,
        Matrix.mul_smul, smul_smul]
      rw [hsqrtR]

/-- The shifted outer block map preserves binary affine combinations. -/
theorem outerShift_convexCombination
    {d : Type u} [Fintype d] [DecidableEq d]
    (s : ℝ) (P₀ P₁ R₀ R₁ : Matrix d d ℂ) (a b : ℝ)
    (hab : a + b = 1) :
    outerShift s (a • P₀ + b • P₁) (a • R₀ + b • R₁) =
      a • outerShift s P₀ R₀ + b • outerShift s P₁ R₁ := by
  have hshift (X₀ X₁ : Matrix d d ℂ) :
      a • X₀ + b • X₁ + s • 1 =
        a • (X₀ + s • 1) + b • (X₁ + s • 1) := by
    have habc : (a : ℂ) + (b : ℂ) = 1 := by exact_mod_cast hab
    ext i j
    by_cases hij : i = j
    · subst j
      simp
      linear_combination -(s : ℂ) * habc
    · simp [hij]
  unfold outerShift
  rw [Matrix.fromBlocks_smul, Matrix.fromBlocks_smul, Matrix.fromBlocks_add]
  rw [hshift P₀ P₁, hshift R₀ R₁]
  simp

/-- The `s`-level log-determinant integrand used in the entropy integral,
with the term depending only on the fixed middle matrix omitted. -/
def fixedMiddleLogDetIntegrand
    {d : Type u} [Fintype d] [DecidableEq d]
    (s : ℝ) (Q : Matrix d d ℂ)
    (PR : Matrix d d ℂ × Matrix d d ℂ) : ℝ :=
  skewLogDetIncrement (middleSkew s Q) (outerShift s PR.1 PR.2)

/-- For every `s > 0` and fixed middle matrix `Q`, the shifted
log-determinant integrand is jointly convex in the positive semidefinite outer
variables `(P,R)`. -/
theorem fixedMiddleLogDetIntegrand_convexOn
    {d : Type u} [Fintype d] [DecidableEq d]
    (s : ℝ) (hs : 0 < s) (Q : Matrix d d ℂ) :
    ConvexOn ℝ
      ({PR : Matrix d d ℂ × Matrix d d ℂ |
        PR.1.PosSemidef ∧ PR.2.PosSemidef} :
        Set (Matrix d d ℂ × Matrix d d ℂ))
      (fixedMiddleLogDetIntegrand s Q) := by
  constructor
  · intro x hx y hy a b ha hb _hab
    exact ⟨
      (hx.1.smul ha).add (hy.1.smul hb),
      (hx.2.smul ha).add (hy.2.smul hb)⟩
  · intro x hx y hy a b ha hb hab
    have hconv := skewLogDetIncrement_convexOn_posDef
      (middleSkew s Q) (middleSkew_skewHermitian s Q)
    have hmain := hconv.2
      (outerShift_posDef s hs x.1 x.2 hx.1 hx.2)
      (outerShift_posDef s hs y.1 y.2 hy.1 hy.2)
      ha hb hab
    have houter :
        outerShift s ((a • x + b • y).1) ((a • x + b • y).2) =
          a • outerShift s x.1 x.2 + b • outerShift s y.1 y.2 := by
      change outerShift s (a • x.1 + b • y.1)
        (a • x.2 + b • y.2) = _
      exact outerShift_convexCombination s x.1 y.1 x.2 y.2 a b hab
    change skewLogDetIncrement (middleSkew s Q)
        (outerShift s ((a • x + b • y).1) ((a • x + b • y).2)) ≤ _
    rw [houter]
    exact hmain

/-- The complete fixed-middle integrand from the entropy representation.
The second term depends only on the fixed middle matrix `Q`, not on the
outer variables `(P,R)`. -/
def fixedMiddleEntropyIntegrand
    {d : Type u} [Fintype d] [DecidableEq d]
    (s : ℝ) (Q : Matrix d d ℂ)
    (PR : Matrix d d ℂ × Matrix d d ℂ) : ℝ :=
  fixedMiddleLogDetIntegrand s Q PR -
    Real.log (Complex.abs (1 + s⁻¹ • Q).det)

/-- Adding back the term depending only on `Q` preserves the joint convexity
in the two outer positive semidefinite matrices. -/
theorem fixedMiddleEntropyIntegrand_convexOn
    {d : Type u} [Fintype d] [DecidableEq d]
    (s : ℝ) (hs : 0 < s) (Q : Matrix d d ℂ) :
    ConvexOn ℝ
      ({PR : Matrix d d ℂ × Matrix d d ℂ |
        PR.1.PosSemidef ∧ PR.2.PosSemidef} :
        Set (Matrix d d ℂ × Matrix d d ℂ))
      (fixedMiddleEntropyIntegrand s Q) := by
  simpa [fixedMiddleEntropyIntegrand, sub_eq_add_neg] using
    (fixedMiddleLogDetIntegrand_convexOn s hs Q).add_const
      (-Real.log (Complex.abs (1 + s⁻¹ • Q).det))

end

end AmplitudeDamping
