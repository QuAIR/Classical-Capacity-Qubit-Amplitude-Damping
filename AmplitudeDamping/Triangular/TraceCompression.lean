import AmplitudeDamping.Triangular.ScalarBoundary

/-!
# Trace compression for the triangular entropy defect

This module assembles scalar perspective Jensen with diagonal decomposition
and sign-unitary dephasing.  It first proves trace compression for three real
diagonal matrices, then for arbitrary positive outer matrices with a real
diagonal middle matrix.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Equality of scalar entropy defects is insensitive to the particular
nonnegativity witnesses. -/
theorem scalarEntropyDefect_congr
    {p₀ q₀ r₀ p₁ q₁ r₁ : ℝ}
    (hp : p₀ = p₁) (hq : q₀ = q₁) (hr : r₀ = r₁)
    (hp₀ : 0 ≤ p₀) (hq₀ : 0 ≤ q₀) (hr₀ : 0 ≤ r₀)
    (hp₁ : 0 ≤ p₁) (hq₁ : 0 ≤ q₁) (hr₁ : 0 ≤ r₁) :
    scalarEntropyDefect p₀ q₀ r₀ hp₀ hq₀ hr₀ =
      scalarEntropyDefect p₁ q₁ r₁ hp₁ hq₁ hr₁ := by
  subst p₁
  subst q₁
  subst r₁
  rfl

/-- Trace compression for three nonnegative real diagonal matrices. -/
theorem entropyDefect_diagonal_ge_scalar
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (p q r : d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i) :
    scalarEntropyDefect (∑ i, p i) (∑ i, q i) (∑ i, r i)
        (Finset.sum_nonneg fun i _ => hp i)
        (Finset.sum_nonneg fun i _ => hq i)
        (Finset.sum_nonneg fun i _ => hr i) ≤
      entropyDefect
        (Matrix.diagonal fun i => ((p i : ℝ) : ℂ))
        (Matrix.diagonal fun i => ((q i : ℝ) : ℂ))
        (Matrix.diagonal fun i => ((r i : ℝ) : ℂ))
        (diagonalOfReal_posSemidef p hp)
        (diagonalOfReal_posSemidef q hq)
        (diagonalOfReal_posSemidef r hr) := by
  calc
    _ ≤ ∑ i, scalarEntropyDefect (p i) (q i) (r i)
          (hp i) (hq i) (hr i) := scalarEntropyDefect_sum_le p q r hp hq hr
    _ = _ := (entropyDefect_diagonal_eq_sum_scalar p q r hp hq hr).symm

/-- A positive semidefinite matrix equals the real diagonal matrix formed from
its diagonal entries after basis dephasing. -/
theorem matrixDephase_eq_diagonal_re
    {d : Type} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) (hX : X.PosSemidef) :
    matrixDephase X =
      Matrix.diagonal fun i => ((((X i i).re : ℝ)) : ℂ) := by
  unfold matrixDephase
  congr 1
  simpa [Matrix.diag] using hX.isHermitian.coe_re_diag.symm

/-- Trace compression when the middle matrix is diagonal in the chosen basis.
The outer matrices are first dephased; scalar Jensen then compresses their
diagonal entries to their traces. -/
theorem entropyDefect_diagonalMiddle_ge_scalar
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (q : d → ℝ) (P R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hq : ∀ i, 0 ≤ q i) (hR : R.PosSemidef) :
    scalarEntropyDefect P.trace.re (∑ i, q i) R.trace.re
        (Matrix.PosSemidef.trace_nonneg hP).1
        (Finset.sum_nonneg fun i _ => hq i)
        (Matrix.PosSemidef.trace_nonneg hR).1 ≤
      entropyDefect P
        (Matrix.diagonal fun i => ((q i : ℝ) : ℂ)) R
        hP (diagonalOfReal_posSemidef q hq) hR := by
  let p : d → ℝ := fun i => (P i i).re
  let r : d → ℝ := fun i => (R i i).re
  have hp : ∀ i, 0 ≤ p i := fun i =>
    posSemidef_diagonal_re_nonneg hP i
  have hr : ∀ i, 0 ≤ r i := fun i =>
    posSemidef_diagonal_re_nonneg hR i
  have hPdiag : Matrix.diagonal (fun i => ((p i : ℝ) : ℂ)) =
      matrixDephase P := by
    symm
    simpa [p] using matrixDephase_eq_diagonal_re P hP
  have hRdiag : Matrix.diagonal (fun i => ((r i : ℝ) : ℂ)) =
      matrixDephase R := by
    symm
    simpa [r] using matrixDephase_eq_diagonal_re R hR
  have hdiagonal := entropyDefect_diagonal_ge_scalar p q r hp hq hr
  have htraceP : (∑ i, p i) = P.trace.re := by
    simp [p, Matrix.trace]
  have htraceR : (∑ i, r i) = R.trace.re := by
    simp [r, Matrix.trace]
  calc
    scalarEntropyDefect P.trace.re (∑ i, q i) R.trace.re _ _ _ =
        scalarEntropyDefect (∑ i, p i) (∑ i, q i) (∑ i, r i)
          (Finset.sum_nonneg fun i _ => hp i)
          (Finset.sum_nonneg fun i _ => hq i)
          (Finset.sum_nonneg fun i _ => hr i) := by
      exact scalarEntropyDefect_congr htraceP.symm rfl htraceR.symm
        _ _ _ _ _ _
    _ ≤ entropyDefect
        (Matrix.diagonal fun i => ((p i : ℝ) : ℂ))
        (Matrix.diagonal fun i => ((q i : ℝ) : ℂ))
        (Matrix.diagonal fun i => ((r i : ℝ) : ℂ))
        (diagonalOfReal_posSemidef p hp)
        (diagonalOfReal_posSemidef q hq)
        (diagonalOfReal_posSemidef r hr) := hdiagonal
    _ = entropyDefect (matrixDephase P)
        (Matrix.diagonal fun i => ((q i : ℝ) : ℂ)) (matrixDephase R)
        (matrixDephase_posSemidef P hP)
        (diagonalOfReal_posSemidef q hq)
        (matrixDephase_posSemidef R hR) := by
      exact entropyDefect_congr hPdiag rfl hRdiag _ _ _ _ _ _
    _ ≤ entropyDefect P
        (Matrix.diagonal fun i => ((q i : ℝ) : ℂ)) R
        hP (diagonalOfReal_posSemidef q hq) hR :=
      entropyDefect_matrixDephase_le
        (fun i => ((q i : ℝ) : ℂ)) P R hP
        (diagonalOfReal_posSemidef q hq) hR

/-- Full matrix trace compression: the entropy defect of three positive
semidefinite matrices is bounded below by the one-dimensional defect of their
traces. -/
theorem entropyDefect_ge_scalar_trace
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef) :
    scalarEntropyDefect P.trace.re Q.trace.re R.trace.re
        (Matrix.PosSemidef.trace_nonneg hP).1
        (Matrix.PosSemidef.trace_nonneg hQ).1
        (Matrix.PosSemidef.trace_nonneg hR).1 ≤
      entropyDefect P Q R hP hQ hR := by
  let U : Matrix.unitaryGroup d ℂ := star hQ.isHermitian.eigenvectorUnitary
  let P' : Matrix d d ℂ :=
    (U : Matrix d d ℂ) * P * (U : Matrix d d ℂ).conjTranspose
  let Q' : Matrix d d ℂ :=
    (U : Matrix d d ℂ) * Q * (U : Matrix d d ℂ).conjTranspose
  let R' : Matrix d d ℂ :=
    (U : Matrix d d ℂ) * R * (U : Matrix d d ℂ).conjTranspose
  let q : d → ℝ := hQ.isHermitian.eigenvalues
  let hP' : P'.PosSemidef :=
    hP.mul_mul_conjTranspose_same (U : Matrix d d ℂ)
  let hQ' : Q'.PosSemidef :=
    hQ.mul_mul_conjTranspose_same (U : Matrix d d ℂ)
  let hR' : R'.PosSemidef :=
    hR.mul_mul_conjTranspose_same (U : Matrix d d ℂ)
  have hq : ∀ i, 0 ≤ q i := fun i => hQ.eigenvalues_nonneg i
  have hdiag : Q' = Matrix.diagonal (fun i => ((q i : ℝ) : ℂ)) := by
    simpa [U, Q', q, Unitary.conjStarAlgAut_apply,
      Matrix.star_eq_conjTranspose] using
      hQ.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hU : (U : Matrix d d ℂ).conjTranspose *
      (U : Matrix d d ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have htraceP : P'.trace.re = P.trace.re := by
    change (((U : Matrix d d ℂ) * P *
      (U : Matrix d d ℂ).conjTranspose).trace).re = _
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  have htraceR : R'.trace.re = R.trace.re := by
    change (((U : Matrix d d ℂ) * R *
      (U : Matrix d d ℂ).conjTranspose).trace).re = _
    rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]
  have htraceQ : (∑ i, q i) = Q.trace.re := by
    have htrace := congrArg Complex.re
      hQ.isHermitian.trace_eq_sum_eigenvalues
    simpa [q] using htrace.symm
  have hcompressed :=
    entropyDefect_diagonalMiddle_ge_scalar q P' R' hP' hq hR'
  calc
    scalarEntropyDefect P.trace.re Q.trace.re R.trace.re _ _ _ =
        scalarEntropyDefect P'.trace.re (∑ i, q i) R'.trace.re
          (Matrix.PosSemidef.trace_nonneg hP').1
          (Finset.sum_nonneg fun i _ => hq i)
          (Matrix.PosSemidef.trace_nonneg hR').1 := by
      exact scalarEntropyDefect_congr htraceP.symm htraceQ.symm htraceR.symm
        _ _ _ _ _ _
    _ ≤ entropyDefect P'
        (Matrix.diagonal fun i => ((q i : ℝ) : ℂ)) R'
        hP' (diagonalOfReal_posSemidef q hq) hR' := hcompressed
    _ = entropyDefect P' Q' R' hP' hQ' hR' := by
      exact entropyDefect_congr rfl hdiag.symm rfl _ _ _ _ _ _
    _ = entropyDefect P Q R hP hQ hR := by
      exact entropyDefect_unitary_conj U P Q R hP hQ hR

end

end AmplitudeDamping
