import AmplitudeDamping.Triangular.GramEntropy

/-!
# Polar gauge for square triangular blocks

This module supplies the algebraic gauge identity that connects an arbitrary
square lower-triangular block matrix to the canonical entropy coupling.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Exact polar-gauge identity, assuming unitary polar factors for the two
blocks in the lower row. -/
theorem triangular_polarGauge_identity
    {d : Type} [Fintype d] [DecidableEq d]
    (A B D : Matrix d d ℂ) (UB UD : Matrix.unitaryGroup d ℂ)
    (hB : B = (UB : Matrix d d ℂ) * QIT.psdSqrt (B.conjTranspose * B))
    (hD : D = (UD : Matrix d d ℂ) * QIT.psdSqrt (D.conjTranspose * D)) :
    let P := A.conjTranspose * A
    let Q := B.conjTranspose * B
    let S := D.conjTranspose * D
    let W : Matrix.unitaryGroup d ℂ := star UB * UD
    let R := (W : Matrix d d ℂ) * S * (W : Matrix d d ℂ).conjTranspose
    let T : Matrix (Sum d d) (Sum d d) ℂ := Matrix.fromBlocks A 0 B D
    let G : Matrix (Sum d d) (Sum d d) ℂ :=
      Matrix.fromBlocks 1 0 0 (W : Matrix d d ℂ)
    G * (T.conjTranspose * T) * G.conjTranspose = entropyCoupling P Q R := by
  dsimp only
  let Q : Matrix d d ℂ := B.conjTranspose * B
  let S : Matrix d d ℂ := D.conjTranspose * D
  let W : Matrix.unitaryGroup d ℂ := star UB * UD
  let R : Matrix d d ℂ :=
    (W : Matrix d d ℂ) * S * (W : Matrix d d ℂ).conjTranspose
  have hQ : Q.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  have hS : S.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self D
  have hR : R.PosSemidef :=
    hS.mul_mul_conjTranspose_same (W : Matrix d d ℂ)
  have hWcoe : (W : Matrix d d ℂ) =
      (UB : Matrix d d ℂ).conjTranspose * (UD : Matrix d d ℂ) := by
    simp [W, Matrix.star_eq_conjTranspose]
  have hWstar : (W : Matrix d d ℂ).conjTranspose =
      (UD : Matrix d d ℂ).conjTranspose * (UB : Matrix d d ℂ) := by
    rw [hWcoe, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
  have hBstar : B.conjTranspose =
      QIT.psdSqrt Q * (UB : Matrix d d ℂ).conjTranspose := by
    rw [hB, Matrix.conjTranspose_mul]
    simp only [Q, (QIT.psdSqrt_isHermitian Q).eq]
  have hsqrtR : QIT.psdSqrt R =
      (W : Matrix d d ℂ) * QIT.psdSqrt S *
        (W : Matrix d d ℂ).conjTranspose := by
    exact psdSqrt_unitary_conj W S hS
  have hcross : B.conjTranspose * D *
      (W : Matrix d d ℂ).conjTranspose =
        QIT.psdSqrt Q * QIT.psdSqrt R := by
    rw [hBstar, hD, hsqrtR]
    change QIT.psdSqrt Q * (UB : Matrix d d ℂ).conjTranspose *
        ((UD : Matrix d d ℂ) * QIT.psdSqrt S) *
          ((W : Matrix d d ℂ).conjTranspose) =
      QIT.psdSqrt Q *
        ((W : Matrix d d ℂ) * QIT.psdSqrt S *
          (W : Matrix d d ℂ).conjTranspose)
    rw [hWstar, hWcoe]
    noncomm_ring
  have hcrossStar : (W : Matrix d d ℂ) * D.conjTranspose * B =
      QIT.psdSqrt R * QIT.psdSqrt Q := by
    have h := congrArg Matrix.conjTranspose hcross
    simpa [Matrix.conjTranspose_mul, (QIT.psdSqrt_isHermitian Q).eq,
      (QIT.psdSqrt_isHermitian R).eq, Matrix.mul_assoc] using h
  rw [Matrix.fromBlocks_conjTranspose]
  simp only [Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply]
  rw [Matrix.fromBlocks_conjTranspose]
  simp only [Matrix.conjTranspose_zero, Matrix.conjTranspose_one,
    Matrix.fromBlocks_multiply, Matrix.one_mul, Matrix.mul_one,
    Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  rw [hcross]
  rw [← Matrix.mul_assoc, hcrossStar]
  change Matrix.fromBlocks
      (A.conjTranspose * A + Q)
      (QIT.psdSqrt Q * QIT.psdSqrt R)
      (QIT.psdSqrt R * QIT.psdSqrt Q) R =
    entropyCoupling (A.conjTranspose * A) Q R
  rfl

end

end AmplitudeDamping
