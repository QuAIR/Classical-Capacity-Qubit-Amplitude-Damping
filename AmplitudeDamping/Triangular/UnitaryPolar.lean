import AmplitudeDamping.Triangular.SquarePolar
import QIT.States.Purification.GramFactorization

/-!
# Unitary polar factors for finite square matrices

The unitary factor exists even for singular matrices.  We obtain it from
Lean-QIT's finite-dimensional Gram-factorization theorem, whose isometry
extension handles the kernel automatically.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

noncomputable section

private theorem transpose_referenceIsometry_mem_unitary
    {d : Type} [Fintype d] [DecidableEq d]
    (V : ReferenceIsometry d d) :
    Matrix.transpose V.matrix ∈ Matrix.unitaryGroup d ℂ := by
  classical
  rw [Matrix.mem_unitaryGroup_iff]
  ext i j
  have h := congrFun (congrFun V.isometry j) i
  simpa [Matrix.mul_apply, Matrix.conjTranspose, Matrix.transpose,
    Matrix.one_apply, Finset.mul_sum, mul_comm, eq_comm] using h

/-- Every finite square complex matrix has a left unitary polar factor,
including in the singular case. -/
theorem exists_unitary_mul_psdSqrt
    {d : Type} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) :
    ∃ U : Matrix.unitaryGroup d ℂ,
      A = (U : Matrix d d ℂ) * QIT.psdSqrt (A.conjTranspose * A) := by
  classical
  let P : Matrix d d ℂ := QIT.psdSqrt (A.conjTranspose * A)
  have hPherm : P.IsHermitian := QIT.psdSqrt_isHermitian _
  have hPsq : P * P = A.conjTranspose * A :=
    QIT.psdSqrt_mul_self_of_posSemidef
      (Matrix.posSemidef_conjTranspose_mul_self A)
  have hGram : P * P.conjTranspose =
      A.conjTranspose * A.conjTranspose.conjTranspose := by
    rw [hPherm.eq, hPsq, Matrix.conjTranspose_conjTranspose]
  obtain ⟨V, hV⟩ :=
    ReferenceIsometry.exists_eq_mul_transpose_of_mul_conjTranspose_eq
      (A := P) (B := A.conjTranspose) hGram (Nat.le_refl _)
  let W : Matrix.unitaryGroup d ℂ :=
    ⟨Matrix.transpose V.matrix, transpose_referenceIsometry_mem_unitary V⟩
  let U : Matrix.unitaryGroup d ℂ := W⁻¹
  refine ⟨U, ?_⟩
  have h := congrArg Matrix.conjTranspose hV
  simpa [U, W, P, Matrix.conjTranspose_mul,
    Matrix.star_eq_conjTranspose, (QIT.psdSqrt_isHermitian _).eq] using h

/-- The normalized square triangular entropy inequality, now unconditional. -/
theorem square_triangular_entropy_lower_bound
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (A B D : Matrix d d ℂ)
    (hsum : frobeniusSq A + frobeniusSq B + frobeniusSq D = 1) :
    let T : Matrix (Sum d d) (Sum d d) ℂ := Matrix.fromBlocks A 0 B D
    psdEntropy (T * T.conjTranspose)
        (Matrix.posSemidef_self_mul_conjTranspose T) ≥
      entanglementCurve (2 * Real.sqrt (frobeniusSq A * frobeniusSq D)) +
        normalizedGramEntropy (frobeniusSq A) A +
        normalizedGramEntropy (frobeniusSq B) B +
        normalizedGramEntropy (frobeniusSq D) D := by
  obtain ⟨UB, hB⟩ := exists_unitary_mul_psdSqrt B
  obtain ⟨UD, hD⟩ := exists_unitary_mul_psdSqrt D
  exact square_triangular_entropy_lower_bound_of_polar A B D UB UD hB hD hsum

end

end AmplitudeDamping
