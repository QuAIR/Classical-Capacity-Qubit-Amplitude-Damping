import AmplitudeDamping.Triangular.EntropyReduction
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import QIT.Information.Renyi.DirectSumMean

/-!
# Scalar entropy-integral identities

This module proves the real-analysis core of the entropy-integral formula.
For two finite nonnegative spectra with the same total mass, the truncated
integral of their logarithmic resolvent difference converges to the
difference of their unnormalized entropies.  The equal-mass hypothesis is
used explicitly to cancel all divergent terms at infinity.
-/

open MeasureTheory Filter intervalIntegral
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Topology

namespace AmplitudeDamping

noncomputable section

/-- Integral of a translated real logarithm over a finite interval. -/
theorem integral_log_add (x L : ℝ) :
    (∫ s in (0 : ℝ)..L, Real.log (s + x)) =
      (L + x) * Real.log (L + x) - x * Real.log x - L := by
  rw [intervalIntegral.integral_comp_add_right (f := Real.log) x]
  rw [integral_log]
  ring_nf

/-- The finite part left after subtracting the two divergent terms from
`(L+x) log(L+x)` tends to `x`. -/
theorem tendsto_shiftedLogRemainder (x : ℝ) (hx : 0 ≤ x) :
    Tendsto (fun L : ℝ =>
      (L + x) * Real.log (L + x) - L * Real.log L - x * Real.log L)
      atTop (𝓝 x) := by
  have hdiv : Tendsto (fun L : ℝ => x / L) atTop (𝓝 0) := by
    exact tendsto_const_nhds.div_atTop tendsto_id
  have hlog : Tendsto (fun L : ℝ => Real.log (1 + x / L)) atTop (𝓝 0) := by
    have hadd : Tendsto (fun L : ℝ => 1 + x / L) atTop (𝓝 1) := by
      simpa using
        ((tendsto_const_nhds : Tendsto (fun _ : ℝ => (1 : ℝ)) atTop (𝓝 1)).add hdiv)
    simpa using
      (Real.continuousAt_log (by norm_num : (1 : ℝ) ≠ 0)).tendsto.comp hadd
  have hmain := Real.tendsto_mul_log_one_add_div_atTop x
  have hsmall : Tendsto (fun L : ℝ => x * Real.log (1 + x / L)) atTop (𝓝 0) := by
    simpa using hlog.const_mul x
  have hcombined : Tendsto (fun L : ℝ =>
      (L + x) * Real.log (1 + x / L)) atTop (𝓝 x) := by
    convert hmain.add hsmall using 1
    · funext L
      ring
    · simp
  apply hcombined.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  have hsum : 0 < L + x := add_pos_of_pos_of_nonneg hL hx
  have hfactor : L + x = L * (1 + x / L) := by
    field_simp [hL.ne']
  have hone : 0 < 1 + x / L := by positivity
  rw [hfactor, Real.log_mul hL.ne' hone.ne']
  rw [← hfactor]
  ring_nf

/-- The shifted-log remainder used to sum the scalar asymptotics. -/
def shiftedLogRemainder (L x : ℝ) : ℝ :=
  (L + x) * Real.log (L + x) - L * Real.log L - x * Real.log L

/-- Finite sums of shifted-log remainders converge to the sum of their
finite parts. -/
theorem tendsto_shiftedLogRemainder_sum
    {ι : Type} [Fintype ι] (x : ι → ℝ) (hx : ∀ i, 0 ≤ x i) :
    Tendsto (fun L : ℝ => ∑ i, shiftedLogRemainder L (x i))
      atTop (𝓝 (∑ i, x i)) := by
  exact tendsto_finsetSum Finset.univ fun i _ => by
    unfold shiftedLogRemainder
    exact tendsto_shiftedLogRemainder (x i) (hx i)

/-- For equal-mass finite spectra, the difference of the two upper-end
logarithmic terms tends to zero. -/
theorem tendsto_sum_shiftedLog_sub
    {ι : Type} [Fintype ι] (x y : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hsum : ∑ i, x i = ∑ i, y i) :
    Tendsto (fun L : ℝ =>
      (∑ i, (L + x i) * Real.log (L + x i)) -
        ∑ i, (L + y i) * Real.log (L + y i))
      atTop (𝓝 0) := by
  have hxlim := tendsto_shiftedLogRemainder_sum x hx
  have hylim := tendsto_shiftedLogRemainder_sum y hy
  have hlim := hxlim.sub hylim
  have heq : (fun L : ℝ =>
      (∑ i, (L + x i) * Real.log (L + x i)) -
        ∑ i, (L + y i) * Real.log (L + y i)) =
      (fun L : ℝ =>
        (∑ i, shiftedLogRemainder L (x i)) -
          ∑ i, shiftedLogRemainder L (y i)) := by
    funext L
    simp only [shiftedLogRemainder, Finset.sum_sub_distrib]
    have hxmul : (∑ i, x i * Real.log L) =
        (∑ i, x i) * Real.log L := (Finset.sum_mul ..).symm
    have hymul : (∑ i, y i * Real.log L) =
        (∑ i, y i) * Real.log L := (Finset.sum_mul ..).symm
    rw [hxmul, hymul, hsum]
    ring
  rw [heq]
  simpa [hsum] using hlim

/-- Exact finite-cutoff integral formula for two finite spectra. -/
theorem truncated_spectral_log_integral
    {ι : Type} [Fintype ι] (x y : ι → ℝ) (L : ℝ) :
    (∫ s in (0 : ℝ)..L,
      (∑ i, Real.log (s + x i)) - ∑ i, Real.log (s + y i)) =
      (∑ i, ((L + x i) * Real.log (L + x i) -
        x i * Real.log (x i) - L)) -
      ∑ i, ((L + y i) * Real.log (L + y i) -
        y i * Real.log (y i) - L) := by
  have hxint (i : ι) : IntervalIntegrable
      (fun s : ℝ => Real.log (s + x i)) volume 0 L := by
    simpa using
      (intervalIntegrable_log' (a := x i) (b := L + x i)).comp_add_right (x i)
  have hyint (i : ι) : IntervalIntegrable
      (fun s : ℝ => Real.log (s + y i)) volume 0 L := by
    simpa using
      (intervalIntegrable_log' (a := y i) (b := L + y i)).comp_add_right (y i)
  have hrepl :
      (∫ s in (0 : ℝ)..L,
        (∑ i, Real.log (s + x i)) - ∑ i, Real.log (s + y i)) =
      ∫ s in (0 : ℝ)..L,
        (∑ i, (fun s : ℝ => Real.log (s + x i))) s -
          (∑ i, (fun s : ℝ => Real.log (s + y i))) s := by
    apply intervalIntegral.integral_congr
    intro s _
    simp
  rw [hrepl]
  rw [intervalIntegral.integral_sub
    (IntervalIntegrable.sum Finset.univ fun i _ => hxint i)
    (IntervalIntegrable.sum Finset.univ fun i _ => hyint i)]
  have hxformula :
      (∫ s in (0 : ℝ)..L, (∑ i, fun s : ℝ => Real.log (s + x i)) s) =
        ∑ i, ∫ s in (0 : ℝ)..L, Real.log (s + x i) := by
    simpa using intervalIntegral.integral_finsetSum
      (s := Finset.univ) (fun i _ => hxint i)
  have hyformula :
      (∫ s in (0 : ℝ)..L, (∑ i, fun s : ℝ => Real.log (s + y i)) s) =
        ∑ i, ∫ s in (0 : ℝ)..L, Real.log (s + y i) := by
    simpa using intervalIntegral.integral_finsetSum
      (s := Finset.univ) (fun i _ => hyint i)
  rw [hxformula, hyformula]
  simp_rw [integral_log_add]

/-- Entropy-integral limit for equal-mass finite nonnegative spectra. -/
theorem tendsto_truncated_spectral_log_integral
    {ι : Type} [Fintype ι] (x y : ι → ℝ)
    (hx : ∀ i, 0 ≤ x i) (hy : ∀ i, 0 ≤ y i)
    (hsum : ∑ i, x i = ∑ i, y i) :
    Tendsto (fun L : ℝ =>
      ∫ s in (0 : ℝ)..L,
        (∑ i, Real.log (s + x i)) - ∑ i, Real.log (s + y i))
      atTop (𝓝 (-(∑ i, x i * Real.log (x i)) +
        ∑ i, y i * Real.log (y i))) := by
  have hcore := tendsto_sum_shiftedLog_sub x y hx hy hsum
  have hlim := (hcore.sub_const (∑ i, x i * Real.log (x i))).add_const
    (∑ i, y i * Real.log (y i))
  have hlim' : Tendsto (fun L : ℝ =>
      ((∑ i, (L + x i) * Real.log (L + x i)) -
        ∑ i, (L + y i) * Real.log (L + y i)) -
        ∑ i, x i * Real.log (x i) + ∑ i, y i * Real.log (y i))
      atTop (𝓝 (-(∑ i, x i * Real.log (x i)) +
        ∑ i, y i * Real.log (y i))) := by
    simpa using hlim
  apply hlim'.congr'
  filter_upwards with L
  rw [truncated_spectral_log_integral x y L]
  simp only [Finset.sum_sub_distrib]
  ring

/-- Determinant of a scalar shift of a Hermitian matrix, expressed using the
unshifted eigenvalues. -/
theorem det_add_smul_one_eq_prod_eigenvalues
    {d : Type} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) (hX : X.IsHermitian) (s : ℝ) :
    (X + s • 1).det = ∏ i, ((hX.eigenvalues i + s : ℝ) : ℂ) := by
  conv_lhs => rw [hX.spectral_theorem]
  let U : Matrix d d ℂ := hX.eigenvectorUnitary
  let D : Matrix d d ℂ := Matrix.diagonal (Complex.ofReal ∘ hX.eigenvalues)
  have hU : U * U.conjTranspose = 1 := by
    simpa [U, Matrix.star_eq_conjTranspose] using
      Unitary.coe_mul_star_self hX.eigenvectorUnitary
  have hfactor : U * D * U.conjTranspose + s • 1 =
      U * (D + s • 1) * U.conjTranspose := by
    rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_smul,
      Matrix.smul_mul, Matrix.mul_one, hU]
  change (U * D * U.conjTranspose + s • 1).det = _
  rw [hfactor, Matrix.det_mul, Matrix.det_mul]
  have hdetU : U.det * U.conjTranspose.det = 1 := by
    rw [← Matrix.det_mul, hU, Matrix.det_one]
  calc
    U.det * (D + s • 1).det * U.conjTranspose.det =
        (U.det * U.conjTranspose.det) * (D + s • 1).det := by ring
    _ = (D + s • 1).det := by rw [hdetU, one_mul]
    _ = _ := by
      rw [show D + s • 1 = Matrix.diagonal
          (fun i => ((hX.eigenvalues i + s : ℝ) : ℂ)) by
        ext i j
        by_cases hij : i = j
        · subst j
          simp [D]
        · simp [D, hij]]
      simp [Matrix.det_diagonal]

/-- For a positive scalar shift, the log absolute determinant of a positive
semidefinite matrix is the sum of the shifted eigenvalue logarithms. -/
theorem log_abs_det_add_smul_one
    {d : Type} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) (hX : X.PosSemidef) (s : ℝ) (hs : 0 < s) :
    Real.log (Complex.abs (X + s • 1).det) =
      ∑ i, Real.log (s + hX.isHermitian.eigenvalues i) := by
  rw [det_add_smul_one_eq_prod_eigenvalues X hX.isHermitian s]
  have hpos (i : d) : 0 < s + hX.isHermitian.eigenvalues i :=
    add_pos_of_pos_of_nonneg hs (hX.eigenvalues_nonneg i)
  simp only [Complex.abs]
  rw [Complex.norm_prod]
  simp only [Complex.norm_real, Real.norm_eq_abs]
  have habs (i : d) : |hX.isHermitian.eigenvalues i + s| =
      s + hX.isHermitian.eigenvalues i := by
    rw [abs_of_pos]
    · ring
    · linarith [hpos i]
  simp_rw [habs]
  rw [Real.log_prod (fun i _ => (hpos i).ne')]

/-- Conversion between the base-two entropy convention and natural
logarithms, including the zero-eigenvalue case. -/
theorem xlog2_mul_log_two {x : ℝ} (hx : 0 ≤ x) :
    QIT.xlog2 x * Real.log 2 = x * Real.log x := by
  by_cases hzx : x = 0
  · simp [QIT.xlog2, hzx, Real.log_zero]
  · have hxp : 0 < x := lt_of_le_of_ne hx (Ne.symm hzx)
    simp only [QIT.xlog2, if_neg (ne_of_gt hxp), QIT.log2]
    field_simp

/-- Spectral form of the entropy-integral limit for two positive semidefinite
matrices of equal trace. -/
theorem tendsto_psdEntropy_spectral_integral
    {d : Type} [Fintype d] [DecidableEq d]
    (X Y : Matrix d d ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htrace : X.trace = Y.trace) :
    Tendsto (fun L : ℝ =>
      ∫ s in (0 : ℝ)..L,
        (∑ i, Real.log (s + hX.isHermitian.eigenvalues i)) -
          ∑ i, Real.log (s + hY.isHermitian.eigenvalues i))
      atTop (𝓝 ((psdEntropy X hX - psdEntropy Y hY) * Real.log 2)) := by
  have hsum : ∑ i, hX.isHermitian.eigenvalues i =
      ∑ i, hY.isHermitian.eigenvalues i := by
    have ht := htrace
    rw [hX.isHermitian.trace_eq_sum_eigenvalues,
      hY.isHermitian.trace_eq_sum_eigenvalues] at ht
    exact_mod_cast ht
  have hlim := tendsto_truncated_spectral_log_integral
    hX.isHermitian.eigenvalues hY.isHermitian.eigenvalues
    hX.eigenvalues_nonneg hY.eigenvalues_nonneg hsum
  convert hlim using 1
  unfold psdEntropy
  have hxlog (i : d) : QIT.xlog2 (hX.isHermitian.eigenvalues i) * Real.log 2 =
      hX.isHermitian.eigenvalues i * Real.log (hX.isHermitian.eigenvalues i) :=
    xlog2_mul_log_two (hX.eigenvalues_nonneg i)
  have hylog (i : d) : QIT.xlog2 (hY.isHermitian.eigenvalues i) * Real.log 2 =
      hY.isHermitian.eigenvalues i * Real.log (hY.isHermitian.eigenvalues i) :=
    xlog2_mul_log_two (hY.eigenvalues_nonneg i)
  simp only [sub_mul, neg_mul, Finset.sum_mul]
  simp_rw [hxlog, hylog]
  ring_nf

/-- Matrix log-determinant form of the entropy-integral limit.  Truncated
integrals are used so singular matrices and zero eigenvalues require no
invertibility assumption at the lower endpoint. -/
theorem tendsto_psdEntropy_logDet_integral
    {d : Type} [Fintype d] [DecidableEq d]
    (X Y : Matrix d d ℂ) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (htrace : X.trace = Y.trace) :
    Tendsto (fun L : ℝ =>
      ∫ s in (0 : ℝ)..L,
        Real.log (Complex.abs (X + s • 1).det) -
          Real.log (Complex.abs (Y + s • 1).det))
      atTop (𝓝 ((psdEntropy X hX - psdEntropy Y hY) * Real.log 2)) := by
  have hspectral := tendsto_psdEntropy_spectral_integral X Y hX hY htrace
  apply hspectral.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  apply intervalIntegral.integral_congr_ae
  filter_upwards with s hs
  have hspos : 0 < s := by
    have hs' : s ∈ Set.Ioc (0 : ℝ) L := by
      simpa [Set.uIoc_of_le hL.le] using hs
    exact hs'.1
  rw [log_abs_det_add_smul_one X hX s hspos,
    log_abs_det_add_smul_one Y hY s hspos]

/-- Scalar function whose functional-calculus trace is `psdEntropy`. -/
def psdEntropyCfcScalar (x : ℝ) : ℝ := -QIT.xlog2 x

/-- Functional-calculus trace representation of the entropy of an arbitrary
positive semidefinite matrix. -/
theorem psdEntropy_eq_cfc_trace
    {d : Type} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) (hX : X.PosSemidef) :
    psdEntropy X hX = ((cfc psdEntropyCfcScalar X).trace).re := by
  unfold psdEntropy
  have hcfc : cfc psdEntropyCfcScalar X =
      hX.isHermitian.cfc psdEntropyCfcScalar :=
    Matrix.IsHermitian.cfc_eq (f := psdEntropyCfcScalar) hX.isHermitian
  rw [hcfc]
  unfold Matrix.IsHermitian.cfc
  rw [Unitary.conjStarAlgAut_apply, Matrix.trace_mul_cycle,
    Unitary.coe_star_mul_self, one_mul, Matrix.trace_diagonal]
  simp only [Function.comp_apply, psdEntropyCfcScalar]
  norm_cast
  rw [Finset.sum_neg_distrib]
  simp

/-- Spectral entropy is additive on unequal-dimensional positive
semidefinite block-diagonal matrices. -/
theorem psdEntropy_fromBlocks_diagonal
    {d e : Type} [Fintype d] [DecidableEq d]
    [Fintype e] [DecidableEq e]
    (A : Matrix d d ℂ) (D : Matrix e e ℂ)
    (hA : A.PosSemidef) (hD : D.PosSemidef) :
    psdEntropy (Matrix.fromBlocks A 0 0 D)
        (Matrix.fromBlocks_diagonal_posSemidef hA hD) =
      psdEntropy A hA + psdEntropy D hD := by
  rw [psdEntropy_eq_cfc_trace, psdEntropy_eq_cfc_trace,
    psdEntropy_eq_cfc_trace]
  rw [QIT.cMatrix_cfc_fromBlocks_diagonal hA hD psdEntropyCfcScalar,
    Matrix.trace_fromBlocks_diagonal]
  simp

/-- A zero positive semidefinite matrix has zero spectral entropy. -/
@[simp]
theorem psdEntropy_zero
    {d : Type} [Fintype d] [DecidableEq d] :
    psdEntropy (0 : Matrix d d ℂ) Matrix.PosSemidef.zero = 0 := by
  rw [psdEntropy_eq_cfc_trace]
  simp [psdEntropyCfcScalar, QIT.xlog2]

/-- The coupling matrix padded by a zero block so that it has the same
dimension as the three-block reference matrix. -/
def paddedEntropyCoupling
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ) :
    Matrix (Sum d (Sum d d)) (Sum d (Sum d d)) ℂ :=
  Matrix.fromBlocks 0 0 0 (entropyCoupling P Q R)

/-- The block-diagonal reference matrix `P ⊕ Q ⊕ R`. -/
def entropyReference
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ) :
    Matrix (Sum d (Sum d d)) (Sum d (Sum d d)) ℂ :=
  Matrix.fromBlocks P 0 0 (Matrix.fromBlocks Q 0 0 R)

/-- Positivity of the zero-padded coupling matrix. -/
theorem paddedEntropyCoupling_posSemidef
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef) :
    (paddedEntropyCoupling P Q R).PosSemidef := by
  exact Matrix.fromBlocks_diagonal_posSemidef Matrix.PosSemidef.zero
    (entropyCoupling_posSemidef P Q R hP hQ hR)

/-- Positivity of the three-block reference matrix. -/
theorem entropyReference_posSemidef
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef) :
    (entropyReference P Q R).PosSemidef := by
  exact Matrix.fromBlocks_diagonal_posSemidef hP
    (Matrix.fromBlocks_diagonal_posSemidef hQ hR)

/-- The padded coupling and block-diagonal reference have the same trace. -/
theorem paddedEntropyCoupling_trace_eq_entropyReference
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ) :
    (paddedEntropyCoupling P Q R).trace =
      (entropyReference P Q R).trace := by
  simp only [paddedEntropyCoupling, entropyReference,
    Matrix.trace_fromBlocks_diagonal, Matrix.trace_zero,
    entropyCoupling_trace, zero_add]
  ring

/-- Determinant factorization of the shifted padded coupling. -/
theorem paddedEntropyCoupling_shift_det
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ) (s : ℝ) :
    (paddedEntropyCoupling P Q R + s • 1).det =
      (s • (1 : Matrix d d ℂ)).det *
        (entropyCoupling P Q R + s • 1).det := by
  rw [show paddedEntropyCoupling P Q R + s • 1 =
      Matrix.fromBlocks (s • (1 : Matrix d d ℂ)) 0 0
        (entropyCoupling P Q R + s • 1) by
    unfold paddedEntropyCoupling
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_add]
    simp]
  exact Matrix.det_fromBlocks_zero₁₂ _ _ _

/-- Determinant factorization of the shifted three-block reference. -/
theorem entropyReference_shift_det
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ) (s : ℝ) :
    (entropyReference P Q R + s • 1).det =
      (P + s • 1).det * ((Q + s • 1).det * (R + s • 1).det) := by
  rw [show entropyReference P Q R + s • 1 =
      Matrix.fromBlocks (P + s • 1) 0 0
        (Matrix.fromBlocks (Q + s • 1) 0 0 (R + s • 1)) by
    unfold entropyReference
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_add]
    simp only [smul_zero, add_zero]
    congr 1
    rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul,
      Matrix.fromBlocks_add]
    simp]
  rw [Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₁₂]

/-- Determinant factorization of the shifted outer block. -/
theorem outerShift_det
    {d : Type} [Fintype d] [DecidableEq d]
    (s : ℝ) (P R : Matrix d d ℂ) :
    (outerShift s P R).det = (P + s • 1).det * (R + s • 1).det := by
  unfold outerShift
  exact Matrix.det_fromBlocks_zero₁₂ _ _ _

/-- Pull the scalar shift out of `Q+sI` in a form suited to determinant
factorization. -/
theorem add_smul_one_eq_scalarBlock_mul
    {d : Type} [Fintype d] [DecidableEq d]
    (Q : Matrix d d ℂ) (s : ℝ) (hs : s ≠ 0) :
    Q + s • 1 =
      (s • (1 : Matrix d d ℂ)) * (1 + s⁻¹ • Q) := by
  rw [Matrix.mul_add, Matrix.mul_one]
  rw [Matrix.smul_mul, Matrix.one_mul, smul_smul]
  field_simp
  simp
  abel

/-- Elementary logarithm rule for the absolute value of a nonzero complex
product. -/
theorem log_abs_mul {x y : ℂ} (hx : x ≠ 0) (hy : y ≠ 0) :
    Real.log (Complex.abs (x * y)) =
      Real.log (Complex.abs x) + Real.log (Complex.abs y) := by
  simp only [Complex.abs, norm_mul]
  exact Real.log_mul (norm_ne_zero_iff.mpr hx) (norm_ne_zero_iff.mpr hy)

/-- The log-determinant integrand of the padded entropy formula is exactly
the fixed-middle integrand to which skew log-determinant convexity applies. -/
theorem paddedLogDetIntegrand_eq_fixedMiddle
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef)
    (s : ℝ) (hs : 0 < s) :
    Real.log (Complex.abs
        (paddedEntropyCoupling P Q R + s • 1).det) -
      Real.log (Complex.abs (entropyReference P Q R + s • 1).det) =
        fixedMiddleEntropyIntegrand s Q (P, R) := by
  let a : ℂ := (s • (1 : Matrix d d ℂ)).det
  let p : ℂ := (P + s • 1).det
  let q : ℂ := (Q + s • 1).det
  let r : ℂ := (R + s • 1).det
  let z : ℂ := (entropyCoupling P Q R + s • 1).det
  let v : ℂ := (1 + s⁻¹ • Q).det
  have hscalar : (s • (1 : Matrix d d ℂ)).PosDef :=
    Matrix.PosDef.smul Matrix.PosDef.one hs
  have hpdef : (P + s • (1 : Matrix d d ℂ)).PosDef :=
    Matrix.PosDef.posSemidef_add hP hscalar
  have hqdef : (Q + s • (1 : Matrix d d ℂ)).PosDef :=
    Matrix.PosDef.posSemidef_add hQ hscalar
  have hrdef : (R + s • (1 : Matrix d d ℂ)).PosDef :=
    Matrix.PosDef.posSemidef_add hR hscalar
  have hzdef : (entropyCoupling P Q R + s •
      (1 : Matrix (Sum d d) (Sum d d) ℂ)).PosDef :=
    Matrix.PosDef.posSemidef_add
      (entropyCoupling_posSemidef P Q R hP hQ hR)
      (Matrix.PosDef.smul Matrix.PosDef.one hs)
  have hscaledQ : (s⁻¹ • Q).PosSemidef :=
    hQ.smul (inv_nonneg.mpr hs.le)
  have hvdef : (1 + s⁻¹ • Q).PosDef :=
    Matrix.PosDef.add_posSemidef Matrix.PosDef.one hscaledQ
  have ha : a ≠ 0 := hscalar.det_pos.ne'
  have hp : p ≠ 0 := hpdef.det_pos.ne'
  have hq : q ≠ 0 := hqdef.det_pos.ne'
  have hr : r ≠ 0 := hrdef.det_pos.ne'
  have hz : z ≠ 0 := hzdef.det_pos.ne'
  have hv : v ≠ 0 := hvdef.det_pos.ne'
  have hpad : (paddedEntropyCoupling P Q R + s • 1).det = a * z := by
    exact paddedEntropyCoupling_shift_det P Q R s
  have href : (entropyReference P Q R + s • 1).det = p * (q * r) := by
    exact entropyReference_shift_det P Q R s
  have hqfactor : q = a * v := by
    dsimp only [q, a, v]
    rw [show Q + s • (1 : Matrix d d ℂ) =
        (s • (1 : Matrix d d ℂ)) * (1 + s⁻¹ • Q) from
      add_smul_one_eq_scalarBlock_mul Q s hs.ne']
    exact Matrix.det_mul _ _
  have hzfactor : z =
      (outerShift s P R + middleSkew s Q).det :=
    entropyCoupling_shift_det_eq P Q R hQ hR s hs
  have houter : (outerShift s P R).det = p * r :=
    outerShift_det s P R
  have hlogPad : Real.log (Complex.abs (a * z)) =
      Real.log (Complex.abs a) + Real.log (Complex.abs z) :=
    log_abs_mul ha hz
  have hlogRef : Real.log (Complex.abs (p * (q * r))) =
      Real.log (Complex.abs p) + Real.log (Complex.abs q) +
        Real.log (Complex.abs r) := by
    rw [log_abs_mul hp (mul_ne_zero hq hr), log_abs_mul hq hr]
    ring
  have hlogQ : Real.log (Complex.abs q) =
      Real.log (Complex.abs a) + Real.log (Complex.abs v) := by
    rw [hqfactor, log_abs_mul ha hv]
  have hlogOuter : Real.log (Complex.abs (p * r)) =
      Real.log (Complex.abs p) + Real.log (Complex.abs r) :=
    log_abs_mul hp hr
  rw [hpad, href, hlogPad, hlogRef, hlogQ]
  unfold fixedMiddleEntropyIntegrand fixedMiddleLogDetIntegrand
    skewLogDetIncrement
  rw [← hzfactor, houter, hlogOuter]
  dsimp only [v]
  ring

/-- Entropy difference between the padded coupling and the three-block
reference.  Proof irrelevance makes this independent of the supplied
positivity witnesses. -/
def paddedEntropyDefect
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef) : ℝ :=
  psdEntropy (paddedEntropyCoupling P Q R)
      (paddedEntropyCoupling_posSemidef P Q R hP hQ hR) -
    psdEntropy (entropyReference P Q R)
      (entropyReference_posSemidef P Q R hP hQ hR)

/-- The manuscript's entropy defect
`H(Z(P,Q,R)) - H(P) - H(Q) - H(R)`, in bits. -/
def entropyDefect
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef) : ℝ :=
  psdEntropy (entropyCoupling P Q R)
      (entropyCoupling_posSemidef P Q R hP hQ hR) -
    psdEntropy P hP - psdEntropy Q hQ - psdEntropy R hR

/-- Padding by zero and collecting the three reference blocks does not
change the entropy defect. -/
theorem paddedEntropyDefect_eq_entropyDefect
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef) :
    paddedEntropyDefect P Q R hP hQ hR =
      entropyDefect P Q R hP hQ hR := by
  have hpadEntropy :
      psdEntropy (paddedEntropyCoupling P Q R)
          (paddedEntropyCoupling_posSemidef P Q R hP hQ hR) =
        psdEntropy (entropyCoupling P Q R)
          (entropyCoupling_posSemidef P Q R hP hQ hR) := by
    change psdEntropy
        (Matrix.fromBlocks (0 : Matrix d d ℂ) 0 0
          (entropyCoupling P Q R)) _ = _
    rw [psdEntropy_fromBlocks_diagonal
      (0 : Matrix d d ℂ) (entropyCoupling P Q R)
      Matrix.PosSemidef.zero
      (entropyCoupling_posSemidef P Q R hP hQ hR),
      psdEntropy_zero, zero_add]
  have hrefEntropy :
      psdEntropy (entropyReference P Q R)
          (entropyReference_posSemidef P Q R hP hQ hR) =
        psdEntropy P hP + psdEntropy Q hQ + psdEntropy R hR := by
    change psdEntropy
        (Matrix.fromBlocks P 0 0 (Matrix.fromBlocks Q 0 0 R)) _ = _
    rw [psdEntropy_fromBlocks_diagonal P (Matrix.fromBlocks Q 0 0 R)
      hP (Matrix.fromBlocks_diagonal_posSemidef hQ hR),
      psdEntropy_fromBlocks_diagonal Q R hQ hR]
    ring
  unfold paddedEntropyDefect entropyDefect
  rw [hpadEntropy, hrefEntropy]
  ring

/-- The entropy integral applied to the same-dimensional padded matrices. -/
theorem tendsto_paddedEntropyDefect_logDetIntegral
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef) :
    Tendsto (fun L : ℝ =>
      ∫ s in (0 : ℝ)..L,
        Real.log (Complex.abs
          (paddedEntropyCoupling P Q R + s • 1).det) -
        Real.log (Complex.abs (entropyReference P Q R + s • 1).det))
      atTop (nhds (paddedEntropyDefect P Q R hP hQ hR * Real.log 2)) := by
  simpa [paddedEntropyDefect] using
    tendsto_psdEntropy_logDet_integral
      (paddedEntropyCoupling P Q R) (entropyReference P Q R)
      (paddedEntropyCoupling_posSemidef P Q R hP hQ hR)
      (entropyReference_posSemidef P Q R hP hQ hR)
      (paddedEntropyCoupling_trace_eq_entropyReference P Q R)

/-- On a compact interval bounded away from zero, the shifted
log-determinant of a positive semidefinite matrix is interval integrable. -/
theorem intervalIntegrable_logAbsDetShift
    {d : Type} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) (hX : X.PosSemidef)
    (epsilon L : ℝ) (hepsilon : 0 ≤ epsilon) (hL : epsilon ≤ L) :
    IntervalIntegrable
      (fun s : ℝ => Real.log (Complex.abs (X + s • 1).det))
      volume epsilon L := by
  have hi (i : d) : IntervalIntegrable
      (fun s : ℝ => Real.log (s + hX.isHermitian.eigenvalues i))
      volume epsilon L := by
    simpa [add_comm] using
      (intervalIntegrable_log'
        (a := epsilon + hX.isHermitian.eigenvalues i)
        (b := L + hX.isHermitian.eigenvalues i)).comp_add_right
          (hX.isHermitian.eigenvalues i)
  have hsum : IntervalIntegrable
      (fun s : ℝ => ∑ i, Real.log (s + hX.isHermitian.eigenvalues i))
      volume epsilon L := by
    convert IntervalIntegrable.sum Finset.univ (fun i _ => hi i) using 1
    funext s
    simp
  apply hsum.congr
  intro s hsI
  have hsI' : s ∈ Set.Ioc epsilon L := by
    simpa [Set.uIoc_of_le hL] using hsI
  symm
  exact log_abs_det_add_smul_one X hX s (lt_of_le_of_lt hepsilon hsI'.1)

/-- The fixed-middle entropy integrand is integrable on every compact
positive interval for positive semidefinite inputs. -/
theorem intervalIntegrable_fixedMiddleEntropyIntegrand
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef)
    (epsilon L : ℝ) (hepsilon : 0 ≤ epsilon) (hL : epsilon ≤ L) :
    IntervalIntegrable
      (fun s : ℝ => fixedMiddleEntropyIntegrand s Q (P, R))
      volume epsilon L := by
  have hpad := intervalIntegrable_logAbsDetShift
    (paddedEntropyCoupling P Q R)
    (paddedEntropyCoupling_posSemidef P Q R hP hQ hR)
    epsilon L hepsilon hL
  have href := intervalIntegrable_logAbsDetShift
    (entropyReference P Q R)
    (entropyReference_posSemidef P Q R hP hQ hR)
    epsilon L hepsilon hL
  apply (hpad.sub href).congr
  intro s hsI
  have hsI' : s ∈ Set.Ioc epsilon L := by
    simpa [Set.uIoc_of_le hL] using hsI
  exact paddedLogDetIntegrand_eq_fixedMiddle P Q R hP hQ hR s
    (lt_of_le_of_lt hepsilon hsI'.1)

/-- Finite positive-window integral of the fixed-middle entropy integrand. -/
def truncatedFixedMiddleEntropyIntegral
    {d : Type} [Fintype d] [DecidableEq d]
    (epsilon L : ℝ) (Q : Matrix d d ℂ)
    (PR : Matrix d d ℂ × Matrix d d ℂ) : ℝ :=
  ∫ s in epsilon..L, fixedMiddleEntropyIntegrand s Q PR

/-- Integration over a compact interval bounded away from zero preserves
the fixed-middle joint convexity in the two outer matrices. -/
theorem truncatedFixedMiddleEntropyIntegral_convexOn
    {d : Type} [Fintype d] [DecidableEq d]
    (Q : Matrix d d ℂ) (hQ : Q.PosSemidef)
    (epsilon L : ℝ) (hepsilon : 0 ≤ epsilon) (hL : epsilon ≤ L) :
    ConvexOn ℝ
      ({PR : Matrix d d ℂ × Matrix d d ℂ |
        PR.1.PosSemidef ∧ PR.2.PosSemidef} :
        Set (Matrix d d ℂ × Matrix d d ℂ))
      (truncatedFixedMiddleEntropyIntegral epsilon L Q) := by
  constructor
  · intro x hx y hy a b ha hb _hab
    exact ⟨
      (hx.1.smul ha).add (hy.1.smul hb),
      (hx.2.smul ha).add (hy.2.smul hb)⟩
  · intro x hx y hy a b ha hb hab
    change x.1.PosSemidef ∧ x.2.PosSemidef at hx
    change y.1.PosSemidef ∧ y.2.PosSemidef at hy
    have hcombo :
        ((a • x + b • y).1.PosSemidef ∧
          (a • x + b • y).2.PosSemidef) := ⟨
      (hx.1.smul ha).add (hy.1.smul hb),
      (hx.2.smul ha).add (hy.2.smul hb)⟩
    have hleft := intervalIntegrable_fixedMiddleEntropyIntegrand
      (a • x.1 + b • y.1) Q (a • x.2 + b • y.2)
      hcombo.1 hQ hcombo.2 epsilon L hepsilon hL
    have hxint := intervalIntegrable_fixedMiddleEntropyIntegrand
      x.1 Q x.2 hx.1 hQ hx.2 epsilon L hepsilon hL
    have hyint := intervalIntegrable_fixedMiddleEntropyIntegrand
      y.1 Q y.2 hy.1 hQ hy.2 epsilon L hepsilon hL
    have hright : IntervalIntegrable
        (fun s : ℝ => a * fixedMiddleEntropyIntegrand s Q x +
          b * fixedMiddleEntropyIntegrand s Q y)
        volume epsilon L :=
      (hxint.const_mul a).add (hyint.const_mul b)
    have hmono :
        (∫ s in epsilon..L,
          fixedMiddleEntropyIntegrand s Q (a • x + b • y)) ≤
      ∫ s in epsilon..L,
          (a * fixedMiddleEntropyIntegrand s Q x +
            b * fixedMiddleEntropyIntegrand s Q y) := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo hL
      · simpa using hleft
      · exact hright
      · intro s hsIoo
        have hs : 0 < s := lt_of_le_of_lt hepsilon hsIoo.1
        simpa [smul_eq_mul] using
          (fixedMiddleEntropyIntegrand_convexOn s hs Q).2 hx hy ha hb hab
    change (∫ s in epsilon..L,
        fixedMiddleEntropyIntegrand s Q (a • x + b • y)) ≤
      a * (∫ s in epsilon..L, fixedMiddleEntropyIntegrand s Q x) +
      b * (∫ s in epsilon..L, fixedMiddleEntropyIntegrand s Q y)
    calc
      _ ≤ ∫ s in epsilon..L,
          (a * fixedMiddleEntropyIntegrand s Q x +
            b * fixedMiddleEntropyIntegrand s Q y) := hmono
      _ = _ := by
        rw [intervalIntegral.integral_add
          (hxint.const_mul a) (hyint.const_mul b),
          intervalIntegral.integral_const_mul,
          intervalIntegral.integral_const_mul]

/-- The zero-to-`L` fixed-middle integrals converge to the padded entropy
defect.  The value of the displayed integrand at `s = 0` is irrelevant to
the interval integral. -/
theorem tendsto_truncatedFixedMiddleEntropyIntegral
    {d : Type} [Fintype d] [DecidableEq d]
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef) :
    Tendsto (fun L : ℝ =>
      truncatedFixedMiddleEntropyIntegral 0 L Q (P, R))
      atTop (nhds (paddedEntropyDefect P Q R hP hQ hR * Real.log 2)) := by
  have hlim := tendsto_paddedEntropyDefect_logDetIntegral P Q R hP hQ hR
  apply hlim.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with L hL
  unfold truncatedFixedMiddleEntropyIntegral
  apply intervalIntegral.integral_congr_ae
  filter_upwards with s hsI
  have hsI' : s ∈ Set.Ioc (0 : ℝ) L := by
    simpa [Set.uIoc_of_le hL.le] using hsI
  exact paddedLogDetIntegrand_eq_fixedMiddle P Q R hP hQ hR s hsI'.1

/-- Binary fixed-middle convexity of the padded entropy defect.  This is the
limit-level conclusion of Step 1 of the triangular entropy argument. -/
theorem paddedEntropyDefect_convexCombination
    {d : Type} [Fintype d] [DecidableEq d]
    (Q : Matrix d d ℂ) (hQ : Q.PosSemidef)
    (P₀ R₀ P₁ R₁ : Matrix d d ℂ)
    (hP₀ : P₀.PosSemidef) (hR₀ : R₀.PosSemidef)
    (hP₁ : P₁.PosSemidef) (hR₁ : R₁.PosSemidef)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    paddedEntropyDefect (a • P₀ + b • P₁) Q (a • R₀ + b • R₁)
        ((hP₀.smul ha).add (hP₁.smul hb)) hQ
        ((hR₀.smul ha).add (hR₁.smul hb)) ≤
      a * paddedEntropyDefect P₀ Q R₀ hP₀ hQ hR₀ +
        b * paddedEntropyDefect P₁ Q R₁ hP₁ hQ hR₁ := by
  have hcomboP : (a • P₀ + b • P₁).PosSemidef :=
    (hP₀.smul ha).add (hP₁.smul hb)
  have hcomboR : (a • R₀ + b • R₁).PosSemidef :=
    (hR₀.smul ha).add (hR₁.smul hb)
  have hlimCombo := tendsto_truncatedFixedMiddleEntropyIntegral
    (a • P₀ + b • P₁) Q (a • R₀ + b • R₁)
    hcomboP hQ hcomboR
  have hlim₀ := tendsto_truncatedFixedMiddleEntropyIntegral
    P₀ Q R₀ hP₀ hQ hR₀
  have hlim₁ := tendsto_truncatedFixedMiddleEntropyIntegral
    P₁ Q R₁ hP₁ hQ hR₁
  have hlimRight := (hlim₀.const_mul a).add (hlim₁.const_mul b)
  have hevent : (fun L : ℝ =>
      truncatedFixedMiddleEntropyIntegral 0 L Q
          (a • (P₀, R₀) + b • (P₁, R₁))) ≤ᶠ[atTop]
      (fun L : ℝ =>
        a • truncatedFixedMiddleEntropyIntegral 0 L Q (P₀, R₀) +
          b • truncatedFixedMiddleEntropyIntegral 0 L Q (P₁, R₁)) := by
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with L hL
    exact (truncatedFixedMiddleEntropyIntegral_convexOn
      Q hQ 0 L le_rfl hL).2 ⟨hP₀, hR₀⟩ ⟨hP₁, hR₁⟩ ha hb hab
  have hle := le_of_tendsto_of_tendsto hlimCombo hlimRight hevent
  have hlog : 0 < Real.log 2 := Real.log_pos (by norm_num)
  nlinarith

/-- Fixed-middle joint convexity of the manuscript entropy defect in its two
outer positive semidefinite arguments. -/
theorem entropyDefect_convexCombination
    {d : Type} [Fintype d] [DecidableEq d]
    (Q : Matrix d d ℂ) (hQ : Q.PosSemidef)
    (P₀ R₀ P₁ R₁ : Matrix d d ℂ)
    (hP₀ : P₀.PosSemidef) (hR₀ : R₀.PosSemidef)
    (hP₁ : P₁.PosSemidef) (hR₁ : R₁.PosSemidef)
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) :
    entropyDefect (a • P₀ + b • P₁) Q (a • R₀ + b • R₁)
        ((hP₀.smul ha).add (hP₁.smul hb)) hQ
        ((hR₀.smul ha).add (hR₁.smul hb)) ≤
      a * entropyDefect P₀ Q R₀ hP₀ hQ hR₀ +
        b * entropyDefect P₁ Q R₁ hP₁ hQ hR₁ := by
  simpa only [paddedEntropyDefect_eq_entropyDefect] using
    paddedEntropyDefect_convexCombination Q hQ P₀ R₀ P₁ R₁
      hP₀ hR₀ hP₁ hR₁ a b ha hb hab

/-- Totalized form of the entropy defect.  Its values outside the positive
semidefinite cone are irrelevant; totalization makes the function compatible
with mathlib's ambient-space convexity and finite Jensen APIs. -/
def entropyDefectTotal
    {d : Type} [Fintype d] [DecidableEq d]
    (Q : Matrix d d ℂ) (hQ : Q.PosSemidef)
    (PR : Matrix d d ℂ × Matrix d d ℂ) : ℝ :=
  by
    classical
    exact if hPR : PR.1.PosSemidef ∧ PR.2.PosSemidef then
      entropyDefect PR.1 Q PR.2 hPR.1 hQ hPR.2
    else 0

/-- Ambient-space `ConvexOn` packaging of fixed-middle entropy-defect
convexity, ready for finite Jensen averages. -/
theorem entropyDefectTotal_convexOn
    {d : Type} [Fintype d] [DecidableEq d]
    (Q : Matrix d d ℂ) (hQ : Q.PosSemidef) :
    ConvexOn ℝ
      ({PR : Matrix d d ℂ × Matrix d d ℂ |
        PR.1.PosSemidef ∧ PR.2.PosSemidef} :
        Set (Matrix d d ℂ × Matrix d d ℂ))
      (entropyDefectTotal Q hQ) := by
  constructor
  · intro x hx y hy a b ha hb _hab
    exact ⟨
      (hx.1.smul ha).add (hy.1.smul hb),
      (hx.2.smul ha).add (hy.2.smul hb)⟩
  · intro x hx y hy a b ha hb hab
    change x.1.PosSemidef ∧ x.2.PosSemidef at hx
    change y.1.PosSemidef ∧ y.2.PosSemidef at hy
    have hcombo :
        ((a • x + b • y).1.PosSemidef ∧
          (a • x + b • y).2.PosSemidef) := ⟨
      (hx.1.smul ha).add (hy.1.smul hb),
      (hx.2.smul ha).add (hy.2.smul hb)⟩
    have hcombo' :
        (a • x.1 + b • y.1).PosSemidef ∧
          (a • x.2 + b • y.2).PosSemidef := by
      simpa using hcombo
    have hxval : entropyDefectTotal Q hQ x =
        entropyDefect x.1 Q x.2 hx.1 hQ hx.2 := by
      simp [entropyDefectTotal, hx]
    have hyval : entropyDefectTotal Q hQ y =
        entropyDefect y.1 Q y.2 hy.1 hQ hy.2 := by
      simp [entropyDefectTotal, hy]
    have hcomboval : entropyDefectTotal Q hQ (a • x + b • y) =
        entropyDefect (a • x + b • y).1 Q (a • x + b • y).2
          hcombo.1 hQ hcombo.2 := by
      simp [entropyDefectTotal, hcombo']
    rw [hxval, hyval, hcomboval]
    simpa using entropyDefect_convexCombination Q hQ
      x.1 x.2 y.1 y.2 hx.1 hx.2 hy.1 hy.2 a b ha hb hab

/-- Finite Jensen inequality for the fixed-middle entropy defect. -/
theorem entropyDefectTotal_map_sum_le
    {d ι : Type} [Fintype d] [DecidableEq d]
    (Q : Matrix d d ℂ) (hQ : Q.PosSemidef)
    (t : Finset ι) (w : ι → ℝ)
    (X : ι → Matrix d d ℂ × Matrix d d ℂ)
    (hw : ∀ i ∈ t, 0 ≤ w i) (hsum : ∑ i ∈ t, w i = 1)
    (hX : ∀ i ∈ t, (X i).1.PosSemidef ∧ (X i).2.PosSemidef) :
    entropyDefectTotal Q hQ (∑ i ∈ t, w i • X i) ≤
      ∑ i ∈ t, w i • entropyDefectTotal Q hQ (X i) := by
  exact (entropyDefectTotal_convexOn Q hQ).map_sum_le hw hsum hX

end

end AmplitudeDamping
