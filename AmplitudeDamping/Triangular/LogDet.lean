import AmplitudeDamping.Triangular.Statement

/-!
# The normalized log-determinant Hessian estimate

This module formalizes the matrix inequality at the analytic core of the
log-determinant convexity argument in the manuscript.  If `Aᴴ = -A` and
`C = (1 + A)⁻¹`, then left multiplication by `C` is a contraction in the
Frobenius norm.  Consequently

`0 ≤ ‖E‖_F² - Re Tr((C E)²)`.

The proof is finite-dimensional and algebraic.  In particular, it does not
assume the log-determinant convexity theorem that it is intended to support.
The remaining calculus bridge is to identify this expression with the second
directional derivative of the log-determinant functional.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

universe u

noncomputable section

/-- Scalar AM--GM estimate used entrywise in the trace-square bound. -/
theorem two_abs_mul_le_normSq_add_normSq (z w : ℂ) :
    2 * Complex.abs (z * w) ≤ Complex.normSq z + Complex.normSq w := by
  simpa [Complex.abs, Complex.norm_mul, Complex.normSq_eq_norm_sq, pow_two,
    mul_assoc] using (two_mul_le_add_sq (Complex.abs z) (Complex.abs w))

/-- The absolute trace of the square of a complex matrix is bounded by its
squared Frobenius norm: `|Tr(X²)| ≤ ‖X‖_F²`.

No Hermiticity assumption is needed.  This is the Hilbert--Schmidt estimate
used for `X = C E` in the normalized log-determinant Hessian. -/
theorem abs_trace_square_le_frobeniusSq
    {n : Type u} [Fintype n] [DecidableEq n] (X : Matrix n n ℂ) :
    Complex.abs ((X * X).trace) ≤ frobeniusSq X := by
  rw [frobeniusSq_eq_sum_normSq]
  simp only [Complex.abs, Matrix.trace]
  calc
    ‖∑ i, ∑ j, X i j * X j i‖
        ≤ ∑ i, ‖∑ j, X i j * X j i‖ := norm_sum_le _ _
    _ ≤ ∑ i, ∑ j, ‖X i j * X j i‖ := by
      exact Finset.sum_le_sum fun i _ ↦ norm_sum_le _ _
    _ ≤ ∑ i, ∑ j,
        (Complex.normSq (X i j) + Complex.normSq (X j i)) / 2 := by
      refine Finset.sum_le_sum fun i _ ↦ Finset.sum_le_sum fun j _ ↦ ?_
      have h : 2 * ‖X i j * X j i‖ ≤
          Complex.normSq (X i j) + Complex.normSq (X j i) := by
        simpa [Complex.abs] using
          two_abs_mul_le_normSq_add_normSq (X i j) (X j i)
      linarith
    _ = ∑ i, ∑ j, Complex.normSq (X i j) := by
      have hswap : (∑ i, ∑ j, Complex.normSq (X j i)) =
          ∑ i, ∑ j, Complex.normSq (X i j) := Finset.sum_comm
      simp_rw [add_div]
      simp_rw [Finset.sum_add_distrib]
      simp_rw [← Finset.sum_div]
      rw [hswap]
      ring

/-- A matrix satisfying `Cᴴ C ≤ I` acts contractively by left
multiplication in the squared Frobenius norm. -/
theorem frobeniusSq_mul_left_le
    {n : Type u} [Fintype n] [DecidableEq n]
    (C X : Matrix n n ℂ) (hC : C.conjTranspose * C ≤ 1) :
    frobeniusSq (C * X) ≤ frobeniusSq X := by
  unfold frobeniusSq
  have hmono := QIT.cMatrix_trace_mul_le_of_le_posSemidef_right
    (Matrix.posSemidef_self_mul_conjTranspose X) hC
  calc
    (Matrix.trace ((C * X) * (C * X).conjTranspose)).re =
        (Matrix.trace ((C.conjTranspose * C) *
          (X * X.conjTranspose))).re := by
      congr 1
      calc
        Matrix.trace ((C * X) * (C * X).conjTranspose) =
            Matrix.trace (C * (X * X.conjTranspose) * C.conjTranspose) := by
          congr 1
          rw [Matrix.conjTranspose_mul]
          noncomm_ring
        _ = Matrix.trace (C.conjTranspose * (C * (X * X.conjTranspose))) := by
          exact Matrix.trace_mul_comm (C * (X * X.conjTranspose)) C.conjTranspose
        _ = Matrix.trace ((C.conjTranspose * C) * (X * X.conjTranspose)) := by
          rw [Matrix.mul_assoc]
    _ ≤ (Matrix.trace (1 * (X * X.conjTranspose))).re := hmono
    _ = (Matrix.trace (X * X.conjTranspose)).re := by simp

/-- `I + A` is nonsingular for every skew-Hermitian complex matrix `A`. -/
theorem isUnit_det_one_add_skew
    {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.conjTranspose = -A) :
    IsUnit (1 + A).det := by
  have hgram : (1 + A).conjTranspose * (1 + A) =
      1 + A.conjTranspose * A := by
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hA]
    noncomm_ring
  have hgram_pos : ((1 + A).conjTranspose * (1 + A)).PosDef := by
    rw [hgram]
    exact Matrix.PosDef.add_posSemidef Matrix.PosDef.one
      (Matrix.posSemidef_conjTranspose_mul_self A)
  have hdet_ne : (1 + A).det ≠ 0 := by
    have hgram_det_ne : ((1 + A).conjTranspose * (1 + A)).det ≠ 0 :=
      hgram_pos.det_pos.ne'
    intro hzero
    apply hgram_det_ne
    rw [Matrix.det_mul, hzero, mul_zero]
  exact isUnit_iff_ne_zero.mpr hdet_ne

/-- The resolvent of a skew-Hermitian matrix is a contraction:
`((I + A)⁻¹)ᴴ (I + A)⁻¹ ≤ I` when `Aᴴ = -A`.

The proof also establishes internally that `I + A` is nonsingular, rather
than taking invertibility as an additional hypothesis. -/
theorem inverse_one_add_skew_contraction
    {n : Type u} [Fintype n] [DecidableEq n]
    (A : Matrix n n ℂ) (hA : A.conjTranspose = -A) :
    ((1 + A)⁻¹).conjTranspose * (1 + A)⁻¹ ≤ 1 := by
  let M : Matrix n n ℂ := 1 + A
  have hgram : M.conjTranspose * M = 1 + A.conjTranspose * A := by
    dsimp [M]
    rw [Matrix.conjTranspose_add, Matrix.conjTranspose_one, hA]
    noncomm_ring
  have hMdet : IsUnit M.det := by
    simpa [M] using isUnit_det_one_add_skew A hA
  have hdiff : (M.conjTranspose * M - 1).PosSemidef := by
    rw [hgram]
    simpa using Matrix.posSemidef_conjTranspose_mul_self A
  have hcong := hdiff.conjTranspose_mul_mul_same M⁻¹
  have hMinv : M * M⁻¹ = 1 := Matrix.mul_nonsing_inv M hMdet
  have hsimplify :
      (M⁻¹).conjTranspose * (M.conjTranspose * M - 1) * M⁻¹ =
        1 - (M⁻¹).conjTranspose * M⁻¹ := by
    calc
      (M⁻¹).conjTranspose * (M.conjTranspose * M - 1) * M⁻¹ =
          (M * M⁻¹).conjTranspose * (M * M⁻¹) -
            (M⁻¹).conjTranspose * M⁻¹ := by
        rw [Matrix.conjTranspose_mul]
        noncomm_ring
      _ = 1 - (M⁻¹).conjTranspose * M⁻¹ := by rw [hMinv]; simp
  rw [hsimplify] at hcong
  exact Matrix.le_iff.mpr hcong

/-- Nonnegativity of the normalized log-determinant Hessian expression for an
arbitrary contraction `C`. -/
theorem normalized_logDet_hessian_nonneg_of_contraction
    {n : Type u} [Fintype n] [DecidableEq n]
    (C E : Matrix n n ℂ) (hC : C.conjTranspose * C ≤ 1) :
    0 ≤ frobeniusSq E - ((C * E) * (C * E)).trace.re := by
  have habs := abs_trace_square_le_frobeniusSq (C * E)
  have hre : ((C * E) * (C * E)).trace.re ≤
      Complex.abs (((C * E) * (C * E)).trace) := by
    simpa [Complex.abs] using Complex.re_le_norm (((C * E) * (C * E)).trace)
  have hcontract := frobeniusSq_mul_left_le C E hC
  linarith

/-- The normalized Hessian inequality in exactly the skew-resolvent form used
by the log-determinant convexity proof. -/
theorem normalized_logDet_hessian_nonneg_of_skew
    {n : Type u} [Fintype n] [DecidableEq n]
    (A E : Matrix n n ℂ) (hA : A.conjTranspose = -A) :
    0 ≤ frobeniusSq E -
      ((((1 + A)⁻¹ * E) * ((1 + A)⁻¹ * E)).trace).re := by
  exact normalized_logDet_hessian_nonneg_of_contraction (1 + A)⁻¹ E
    (inverse_one_add_skew_contraction A hA)

/-- Positive-definite normalization of the Hessian estimate, expressed through
an invertible Hermitian square factor `S`.

This theorem is the algebraic bridge from the normalized skew-resolvent
estimate to the unnormalized matrices occurring in the log-determinant
calculation. -/
theorem logDet_hessian_nonneg_of_square_factor
    {n : Type u} [Fintype n] [DecidableEq n]
    (S H J : Matrix n n ℂ)
    (hSdet : IsUnit S.det)
    (hS : S.conjTranspose = S)
    (hH : H.conjTranspose = H)
    (hJ : J.conjTranspose = -J) :
    0 ≤ ((((S * S)⁻¹ * H) * ((S * S)⁻¹ * H)).trace).re -
      (((((S * S + J)⁻¹ * H) * ((S * S + J)⁻¹ * H)).trace).re) := by
  let R : Matrix n n ℂ := S⁻¹
  let E : Matrix n n ℂ := R * H * R
  let A : Matrix n n ℂ := R * J * R
  let C : Matrix n n ℂ := (1 + A)⁻¹
  have hSR : S * R = 1 := Matrix.mul_nonsing_inv S hSdet
  have hRS : R * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hR : R.conjTranspose = R := by
    dsimp [R]
    exact Matrix.IsHermitian.inv hS
  have hE : E.conjTranspose = E := by
    dsimp [E]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hR, hH]
    noncomm_ring
  have hA : A.conjTranspose = -A := by
    dsimp [A]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hR, hJ]
    noncomm_ring
  have hSSdet : IsUnit (S * S).det := by
    rw [Matrix.det_mul]
    exact hSdet.mul hSdet
  have hBinv : (S * S)⁻¹ = R * R := by
    apply Matrix.right_inv_eq_right_inv (Matrix.mul_nonsing_inv (S * S) hSSdet)
    calc
      (S * S) * (R * R) = S * (S * R) * R := by noncomm_ring
      _ = 1 := by rw [hSR]; simp [hSR]
  have hDdet : IsUnit (1 + A).det := isUnit_det_one_add_skew A hA
  have hDinv : (1 + A) * C = 1 := Matrix.mul_nonsing_inv (1 + A) hDdet
  have hfactor : S * (1 + A) * S = S * S + J := by
    dsimp [A]
    calc
      S * (1 + R * J * R) * S = S * S + (S * R) * J * (R * S) := by
        noncomm_ring
      _ = S * S + J := by rw [hSR, hRS]; simp
  have hshiftDet : IsUnit (S * S + J).det := by
    rw [← hfactor, Matrix.det_mul, Matrix.det_mul]
    exact (hSdet.mul hDdet).mul hSdet
  have hShiftInv : (S * S + J)⁻¹ = R * C * R := by
    apply Matrix.right_inv_eq_right_inv
      (Matrix.mul_nonsing_inv (S * S + J) hshiftDet)
    rw [← hfactor]
    calc
      (S * (1 + A) * S) * (R * C * R) =
          S * (1 + A) * (S * R) * C * R := by
        noncomm_ring
      _ = S * ((1 + A) * C) * R := by rw [hSR]; simp; noncomm_ring
      _ = S * R := by rw [hDinv]; simp
      _ = 1 := hSR
  have hbaseTrace :
      (((S * S)⁻¹ * H) * ((S * S)⁻¹ * H)).trace =
        (E * E).trace := by
    rw [hBinv]
    dsimp [E]
    calc
      ((R * R * H) * (R * R * H)).trace =
          (R * (R * H * R * R * H)).trace := by
        congr 1
        noncomm_ring
      _ = ((R * H * R * R * H) * R).trace :=
        Matrix.trace_mul_comm R (R * H * R * R * H)
      _ = ((R * H * R) * (R * H * R)).trace := by
        congr 1
        noncomm_ring
  have hshiftTrace :
      ((((S * S + J)⁻¹ * H) * ((S * S + J)⁻¹ * H)).trace) =
        ((C * E) * (C * E)).trace := by
    rw [hShiftInv]
    dsimp [E]
    calc
      ((R * C * R * H) * (R * C * R * H)).trace =
          (R * (C * R * H * R * C * R * H)).trace := by
        congr 1
        noncomm_ring
      _ = ((C * R * H * R * C * R * H) * R).trace :=
        Matrix.trace_mul_comm R (C * R * H * R * C * R * H)
      _ = ((C * (R * H * R)) * (C * (R * H * R))).trace := by
        congr 1
        noncomm_ring
  have hnorm := normalized_logDet_hessian_nonneg_of_skew A E hA
  rw [hbaseTrace, hshiftTrace]
  have hfrob : frobeniusSq E = (E * E).trace.re := by
    unfold frobeniusSq
    rw [hE]
  rw [← hfrob]
  exact hnorm

/-- Pointwise nonnegativity of the log-determinant Hessian for a positive
definite Hermitian base matrix, a Hermitian direction, and a skew-Hermitian
perturbation. -/
theorem logDet_hessian_nonneg_of_posDef
    {n : Type u} [Fintype n] [DecidableEq n]
    (G H J : Matrix n n ℂ)
    (hG : G.PosDef)
    (hH : H.conjTranspose = H)
    (hJ : J.conjTranspose = -J) :
    0 ≤ (((G⁻¹ * H) * (G⁻¹ * H)).trace).re -
      (((((G + J)⁻¹ * H) * ((G + J)⁻¹ * H)).trace).re) := by
  let S : Matrix n n ℂ := QIT.psdSqrt G
  have hS : S.conjTranspose = S := (QIT.psdSqrt_isHermitian G).eq
  have hSS : S * S = G :=
    QIT.psdSqrt_mul_self_of_posSemidef hG.posSemidef
  have hSdet_ne : S.det ≠ 0 := by
    intro hzero
    have hGdet_ne : G.det ≠ 0 := hG.det_pos.ne'
    apply hGdet_ne
    rw [← hSS, Matrix.det_mul, hzero, zero_mul]
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet_ne
  simpa [hSS] using
    logDet_hessian_nonneg_of_square_factor S H J hSdet hS hH hJ

/-- A skew-Hermitian perturbation of a positive-definite matrix is
nonsingular.  This is the invertibility input needed by the differential
log-determinant identities along positive-definite line segments. -/
theorem isUnit_det_add_skew_of_posDef
    {n : Type u} [Fintype n] [DecidableEq n]
    (G J : Matrix n n ℂ)
    (hG : G.PosDef)
    (hJ : J.conjTranspose = -J) :
    IsUnit (G + J).det := by
  let S : Matrix n n ℂ := QIT.psdSqrt G
  let R : Matrix n n ℂ := S⁻¹
  let A : Matrix n n ℂ := R * J * R
  have hS : S.conjTranspose = S := (QIT.psdSqrt_isHermitian G).eq
  have hSS : S * S = G :=
    QIT.psdSqrt_mul_self_of_posSemidef hG.posSemidef
  have hSdet_ne : S.det ≠ 0 := by
    intro hzero
    apply hG.det_pos.ne'
    rw [← hSS, Matrix.det_mul, hzero, zero_mul]
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet_ne
  have hSR : S * R = 1 := Matrix.mul_nonsing_inv S hSdet
  have hRS : R * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hR : R.conjTranspose = R := by
    dsimp [R]
    exact Matrix.IsHermitian.inv hS
  have hA : A.conjTranspose = -A := by
    dsimp [A]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hR, hJ]
    noncomm_ring
  have hfactor : S * (1 + A) * S = G + J := by
    rw [← hSS]
    dsimp [A]
    calc
      S * (1 + R * J * R) * S = S * S + (S * R) * J * (R * S) := by
        noncomm_ring
      _ = S * S + J := by rw [hSR, hRS]; simp
  rw [← hfactor, Matrix.det_mul, Matrix.det_mul]
  exact (hSdet.mul (isUnit_det_one_add_skew A hA)).mul hSdet

end

end AmplitudeDamping
