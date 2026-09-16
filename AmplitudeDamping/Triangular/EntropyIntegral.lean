import AmplitudeDamping.Triangular.EntropyReduction
import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

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

end

end AmplitudeDamping
