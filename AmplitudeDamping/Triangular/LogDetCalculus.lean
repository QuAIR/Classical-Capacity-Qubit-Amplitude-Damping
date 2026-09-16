import AmplitudeDamping.Triangular.LogDet
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Analysis.Convex.Deriv
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
# Calculus bridge for the log-determinant argument

This module develops the one-variable differential identities needed to turn
the normalized Hessian estimate in `Triangular.LogDet` into convexity of the
matrix log-determinant functional.  The determinant derivative is proved from
the polynomial determinant expansion, so no matrix-calculus identity is
postulated.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Polynomial
  Matrix.Norms.Frobenius

namespace AmplitudeDamping

universe u

noncomputable section

/-- For a differentiable nonvanishing complex-valued real path, the
derivative of the logarithm of its modulus is the real part of its logarithmic
derivative. -/
theorem HasDerivAt.log_complex_abs
    {f : ℝ → ℂ} {f' : ℂ} {x : ℝ}
    (hf : HasDerivAt f f' x) (hne : f x ≠ 0) :
    HasDerivAt (fun y ↦ Real.log (Complex.abs (f y))) (f' / f x).re x := by
  have hsq_ne : ‖f x‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hne)
  have h := (hf.norm_sq.log hsq_ne).const_mul (1 / 2 : ℝ)
  convert h using 1
  · funext y
    simp only [Complex.abs, Real.log_pow]
    ring
  · rw [Complex.inner, Complex.div_re, Complex.normSq_eq_norm_sq]
    field_simp
    simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]

/-- Evaluation of the determinant polynomial `det(I + X K)`. -/
theorem eval_det_one_add_X_smul
    {n : Type u} [Fintype n] [DecidableEq n]
    (K : Matrix n n ℂ) (z : ℂ) :
    Polynomial.eval z (Matrix.det ((1 : Matrix n n ℂ[X]) +
      (Polynomial.X : ℂ[X]) • K.map Polynomial.C)) =
      Matrix.det (1 + z • K) := by
  simp [eval_det, ← Matrix.smul_eq_mul_diagonal]

/-- Jacobi's formula for the determinant along a real affine matrix path.

The invertibility hypothesis is local, at the point where the derivative is
taken. -/
theorem hasDerivAt_det_affine
    {n : Type u} [Fintype n] [DecidableEq n]
    (M H : Matrix n n ℂ) (t : ℝ)
    (hdet : IsUnit (M + (t : ℂ) • H).det) :
    HasDerivAt (fun s : ℝ ↦ (M + (s : ℂ) • H).det)
      ((M + (t : ℂ) • H).det *
        (((M + (t : ℂ) • H)⁻¹ * H).trace)) t := by
  let B : Matrix n n ℂ := M + (t : ℂ) • H
  let K : Matrix n n ℂ := B⁻¹ * H
  let q : ℂ[X] := Matrix.det ((1 : Matrix n n ℂ[X]) +
    (Polynomial.X : ℂ[X]) • K.map Polynomial.C)
  have hqderiv : q.derivative.eval 0 = K.trace := by
    simpa [q] using Matrix.derivative_det_one_add_X_smul K
  have hqcomplex : HasDerivAt (fun z : ℂ ↦ q.eval z) K.trace 0 := by
    simpa [hqderiv] using q.hasDerivAt (0 : ℂ)
  have hshift : HasDerivAt (fun s : ℝ ↦ ((s - t : ℝ) : ℂ)) 1 t := by
    simpa using ((hasDerivAt_id t).sub_const t).ofReal_comp
  have hqcomplex' :
      HasDerivAt (fun z : ℂ ↦ q.eval z) K.trace (((t - t : ℝ) : ℂ)) := by
    simpa using hqcomplex
  have hqreal :
      HasDerivAt (fun s : ℝ ↦ q.eval ((s - t : ℝ) : ℂ)) K.trace t := by
    simpa only [Function.comp_apply, mul_one] using hqcomplex'.comp t hshift
  have hprod := hqreal.const_mul B.det
  convert hprod using 1
  funext s
  change (M + (s : ℂ) • H).det =
    B.det * q.eval ((s - t : ℝ) : ℂ)
  rw [show q.eval ((s - t : ℝ) : ℂ) =
      (1 + ((s - t : ℝ) : ℂ) • K).det by
    exact eval_det_one_add_X_smul K _]
  rw [← Matrix.det_mul]
  congr 1
  dsimp [K]
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul,
    Matrix.mul_nonsing_inv_cancel_left B H hdet]
  dsimp [B]
  ext i j
  simp [sub_smul]

/-- First derivative of `log |det(M + t H)|` along an invertible affine
matrix path. -/
theorem hasDerivAt_log_abs_det_affine
    {n : Type u} [Fintype n] [DecidableEq n]
    (M H : Matrix n n ℂ) (t : ℝ)
    (hdet : IsUnit (M + (t : ℂ) • H).det) :
    HasDerivAt
      (fun s : ℝ ↦ Real.log (Complex.abs ((M + (s : ℂ) • H).det)))
      (((M + (t : ℂ) • H)⁻¹ * H).trace.re) t := by
  have h := HasDerivAt.log_complex_abs
    (hasDerivAt_det_affine M H t hdet) hdet.ne_zero
  convert h using 1
  congr 1
  rw [mul_comm, mul_div_cancel_right₀ _ hdet.ne_zero]

/-- Derivative of the trace of the inverse affine path.  This is the
noncommutative inverse rule followed by the continuous trace functional. -/
theorem hasDerivAt_trace_inv_mul_affine
    {n : Type u} [Fintype n] [DecidableEq n]
    (M H : Matrix n n ℂ) (t : ℝ)
    (hdet : IsUnit (M + (t : ℂ) • H).det) :
    HasDerivAt
      (fun s : ℝ ↦ (((M + (s : ℂ) • H)⁻¹ * H).trace))
      (-(((M + (t : ℂ) • H)⁻¹ * H) *
        ((M + (t : ℂ) • H)⁻¹ * H)).trace) t := by
  let B : Matrix n n ℂ := M + (t : ℂ) • H
  have hpath : HasDerivAt (fun s : ℝ ↦ M + (s : ℂ) • H) H t := by
    have hs : HasDerivAt (fun s : ℝ ↦ (s : ℂ)) 1 t :=
      (hasDerivAt_id t).ofReal_comp
    simpa using (hasDerivAt_const t M).add (hs.smul_const H)
  have hBunit : IsUnit B :=
    (Matrix.isUnit_iff_isUnit_det B).mpr (by simpa [B] using hdet)
  obtain ⟨u, hu⟩ := hBunit
  have hinvBase := hasFDerivAt_ringInverse (𝕜 := ℝ) u
  rw [hu] at hinvBase
  have hinv : HasDerivAt (fun s : ℝ ↦ (M + (s : ℂ) • H)⁻¹)
      (-(B⁻¹ * H * B⁻¹)) t := by
    have hcomp := hinvBase.comp_hasDerivAt t hpath
    simpa [Function.comp_apply, Matrix.nonsing_inv_eq_ringInverse, hu,
      ContinuousLinearMap.mulLeftRight_apply] using hcomp
  have hmul := hinv.mul_const H
  let trCLM : Matrix n n ℂ →L[ℝ] ℂ :=
    (Matrix.traceLinearMap n ℝ ℂ).toContinuousLinearMap
  have htrace := trCLM.hasFDerivAt.comp_hasDerivAt t hmul
  convert htrace using 1
  simp [trCLM, B, Matrix.nonsing_inv_eq_ringInverse]
  noncomm_ring

/-- Real-part version of `hasDerivAt_trace_inv_mul_affine`. -/
theorem hasDerivAt_re_trace_inv_mul_affine
    {n : Type u} [Fintype n] [DecidableEq n]
    (M H : Matrix n n ℂ) (t : ℝ)
    (hdet : IsUnit (M + (t : ℂ) • H).det) :
    HasDerivAt
      (fun s : ℝ ↦ (((M + (s : ℂ) • H)⁻¹ * H).trace.re))
      (-(((M + (t : ℂ) • H)⁻¹ * H) *
        ((M + (t : ℂ) • H)⁻¹ * H)).trace.re) t := by
  have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt t
    (hasDerivAt_trace_inv_mul_affine M H t hdet)
  simpa [Function.comp_apply] using h

/-- Second-derivative identity for a difference of two matrix
log-determinants.  The function differentiated here is the first derivative
of

`log |det(M₁+tH)| - log |det(M₀+tH)|`.
-/
theorem hasDerivAt_logDet_difference_firstDerivative
    {n : Type u} [Fintype n] [DecidableEq n]
    (M₁ M₀ H : Matrix n n ℂ) (t : ℝ)
    (hdet₁ : IsUnit (M₁ + (t : ℂ) • H).det)
    (hdet₀ : IsUnit (M₀ + (t : ℂ) • H).det) :
    HasDerivAt
      (fun s : ℝ ↦
        (((M₁ + (s : ℂ) • H)⁻¹ * H).trace.re) -
          (((M₀ + (s : ℂ) • H)⁻¹ * H).trace.re))
      ((((M₀ + (t : ℂ) • H)⁻¹ * H) *
          ((M₀ + (t : ℂ) • H)⁻¹ * H)).trace.re -
        (((M₁ + (t : ℂ) • H)⁻¹ * H) *
          ((M₁ + (t : ℂ) • H)⁻¹ * H)).trace.re) t := by
  convert (hasDerivAt_re_trace_inv_mul_affine M₁ H t hdet₁).sub
    (hasDerivAt_re_trace_inv_mul_affine M₀ H t hdet₀) using 1
  ring

/-- Convexity of the skew log-determinant increment along every line segment
between positive-definite matrices.

This is the one-dimensional form of the manuscript's log-determinant
convexity lemma.  It includes all endpoint and invertibility obligations:
positive definiteness is preserved along the closed segment, while the
skew-Hermitian perturbation remains nonsingular there. -/
theorem logDet_skew_increment_convexOn_segment
    {n : Type u} [Fintype n] [DecidableEq n]
    (G₀ G₁ J : Matrix n n ℂ)
    (hG₀ : G₀.PosDef) (hG₁ : G₁.PosDef)
    (hJ : J.conjTranspose = -J) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t : ℝ ↦
        Real.log (Complex.abs (((G₀ + J) + (t : ℂ) • (G₁ - G₀)).det)) -
          Real.log (Complex.abs ((G₀ + (t : ℂ) • (G₁ - G₀)).det))) := by
  let H : Matrix n n ℂ := G₁ - G₀
  let P : ℝ → Matrix n n ℂ := fun t ↦ G₀ + (t : ℂ) • H
  let f : ℝ → ℝ := fun t ↦
    Real.log (Complex.abs (((G₀ + J) + (t : ℂ) • H).det)) -
      Real.log (Complex.abs ((G₀ + (t : ℂ) • H).det))
  let f' : ℝ → ℝ := fun t ↦
    ((((G₀ + J) + (t : ℂ) • H)⁻¹ * H).trace.re) -
      (((G₀ + (t : ℂ) • H)⁻¹ * H).trace.re)
  let f'' : ℝ → ℝ := fun t ↦
    ((((G₀ + (t : ℂ) • H)⁻¹ * H) *
      ((G₀ + (t : ℂ) • H)⁻¹ * H)).trace.re) -
      (((((G₀ + J) + (t : ℂ) • H)⁻¹ * H) *
        (((G₀ + J) + (t : ℂ) • H)⁻¹ * H)).trace.re)
  have hH : H.conjTranspose = H := by
    dsimp [H]
    rw [Matrix.conjTranspose_sub, hG₁.1.eq, hG₀.1.eq]
  have hP : ∀ t ∈ Set.Icc (0 : ℝ) 1, (P t).PosDef := by
    intro t ht
    have hc := Matrix.PosDef.convexCombination hG₁ hG₀ ht.1 ht.2
    convert hc using 1
    dsimp [P, H]
    ext i j
    simp
    ring
  have hdet₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsUnit (G₀ + (t : ℂ) • H).det := by
    intro t ht
    exact isUnit_iff_ne_zero.mpr (hP t ht).det_pos.ne'
  have hdet₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsUnit ((G₀ + J) + (t : ℂ) • H).det := by
    intro t ht
    have hu := isUnit_det_add_skew_of_posDef (P t) J (hP t ht) hJ
    simpa [P, add_assoc, add_left_comm, add_comm] using hu
  have hfderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t := by
    intro t ht
    exact (hasDerivAt_log_abs_det_affine (G₀ + J) H t (hdet₁ t ht)).sub
      (hasDerivAt_log_abs_det_affine G₀ H t (hdet₀ t ht))
  have hf'deriv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f' (f'' t) t := by
    intro t ht
    exact hasDerivAt_logDet_difference_firstDerivative
      (G₀ + J) G₀ H t (hdet₁ t ht) (hdet₀ t ht)
  have hf''nonneg : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 ≤ f'' t := by
    intro t ht
    have hh := logDet_hessian_nonneg_of_posDef (P t) H J (hP t ht) hH hJ
    simpa [f'', P, add_assoc, add_left_comm, add_comm] using hh
  have hfconvex : ConvexOn ℝ (Set.Icc (0 : ℝ) 1) f := by
    apply convexOn_of_hasDerivWithinAt2_nonneg (convex_Icc (0 : ℝ) 1)
    · intro t ht
      exact (hfderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      have htIoo : 0 < t ∧ t < 1 := by simpa [interior_Icc] using ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htIoo.1.le, htIoo.2.le⟩
      exact (hfderiv t ht').hasDerivWithinAt
    · intro t ht
      have htIoo : 0 < t ∧ t < 1 := by simpa [interior_Icc] using ht
      have ht' : t ∈ Set.Icc (0 : ℝ) 1 := ⟨htIoo.1.le, htIoo.2.le⟩
      exact (hf'deriv t ht').hasDerivWithinAt
    · intro t ht
      have htIoo : 0 < t ∧ t < 1 := by simpa [interior_Icc] using ht
      apply hf''nonneg t
      exact ⟨htIoo.1.le, htIoo.2.le⟩
  simpa [f, H] using hfconvex

/-- The log-determinant increment produced by a fixed skew-Hermitian
perturbation. -/
def skewLogDetIncrement
    {n : Type u} [Fintype n] [DecidableEq n]
    (J G : Matrix n n ℂ) : ℝ :=
  Real.log (Complex.abs (G + J).det) - Real.log (Complex.abs G.det)

/-- The skew log-determinant increment is convex on the positive-definite
cone.

This is the matrix-level form of the log-determinant convexity lemma.  The
proof reduces an arbitrary binary convex combination to the segment theorem
above. -/
theorem skewLogDetIncrement_convexOn_posDef
    {n : Type u} [Fintype n] [DecidableEq n]
    (J : Matrix n n ℂ) (hJ : J.conjTranspose = -J) :
    ConvexOn ℝ ({G : Matrix n n ℂ | G.PosDef} : Set (Matrix n n ℂ))
      (skewLogDetIncrement J) := by
  constructor
  · intro x hx y hy s t hs ht hst
    have hs1 : s ≤ 1 := by linarith
    have ht_eq : t = 1 - s := by linarith
    have hpos : (s • x + (1 - s) • y).PosDef :=
      Matrix.PosDef.convexCombination hx hy hs hs1
    simpa [ht_eq] using hpos
  · intro x hx y hy s t hs ht hst
    have hseg := logDet_skew_increment_convexOn_segment x y J hx hy hJ
    have hineq := hseg.2 (show (0 : ℝ) ∈ Set.Icc 0 1 by norm_num)
      (show (1 : ℝ) ∈ Set.Icc 0 1 by norm_num) hs ht hst
    have hs_eq : s = 1 - t := by linarith
    have hpath : x + t • (y - x) = s • x + t • y := by
      rw [hs_eq]
      ext i j
      simp
      ring
    simpa [skewLogDetIncrement, smul_eq_mul, hpath, add_assoc,
      add_left_comm, add_comm] using hineq

end

end AmplitudeDamping
