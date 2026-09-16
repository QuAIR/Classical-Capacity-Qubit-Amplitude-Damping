import AmplitudeDamping.FixedExcitation
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import QIT.Information.Entropy.Log2Lemmas

/-!
# Scalar entropy curve

This module relates the project's bit-valued binary entropy to mathlib's
natural-logarithm binary entropy and establishes the order facts used in the
fixed-excitation argument.
-/

namespace AmplitudeDamping

open QIT

noncomputable section

/-- The bit-valued binary entropy is mathlib's binary entropy divided by
`log 2`. -/
theorem binaryEntropy_eq_binEntropy_div_log_two (q : ℝ) :
    binaryEntropy q = Real.binEntropy q / Real.log 2 := by
  rw [Real.binEntropy]
  unfold binaryEntropy
  rw [QIT.xlog2_eq_mul_log2, QIT.xlog2_eq_mul_log2]
  unfold QIT.log2
  rw [Real.log_inv, Real.log_inv]
  ring

/-- The probability argument of the binary entropy in the concurrence
formula. -/
def entanglementArgument (c : ℝ) : ℝ :=
  (1 + Real.sqrt (1 - c ^ 2)) / 2

theorem entanglementCurve_eq (c : ℝ) :
    entanglementCurve c =
      Real.binEntropy (entanglementArgument c) / Real.log 2 := by
  simp [entanglementCurve, entanglementArgument,
    binaryEntropy_eq_binEntropy_div_log_two]

theorem entanglementArgument_mem_Icc (c : ℝ) (hc : c ∈ Set.Icc (0 : ℝ) 1) :
    entanglementArgument c ∈ Set.Icc (2⁻¹ : ℝ) 1 := by
  have hcsq : c ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ hc.1 zero_le_one).2 hc.2
  have hrad : 0 ≤ 1 - c ^ 2 := by linarith
  have hs0 := Real.sqrt_nonneg (1 - c ^ 2)
  have hssq := Real.sq_sqrt hrad
  unfold entanglementArgument
  constructor <;> norm_num <;> nlinarith

theorem entanglementArgument_strictAntiOn :
    StrictAntiOn entanglementArgument (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  have hxsq_lt : x ^ 2 < y ^ 2 :=
    (sq_lt_sq₀ hx.1 hy.1).2 hxy
  have hysq : y ^ 2 ≤ (1 : ℝ) ^ 2 :=
    (sq_le_sq₀ hy.1 zero_le_one).2 hy.2
  have hyrad : 0 ≤ 1 - y ^ 2 := by
    linarith
  have hsqrt : Real.sqrt (1 - y ^ 2) < Real.sqrt (1 - x ^ 2) :=
    Real.sqrt_lt_sqrt hyrad (by linarith)
  unfold entanglementArgument
  linarith

/-- The concurrence entropy curve is strictly increasing on its physical
domain. -/
theorem entanglementCurve_strictMonoOn :
    StrictMonoOn entanglementCurve (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  rw [entanglementCurve_eq, entanglementCurve_eq]
  have harg := entanglementArgument_strictAntiOn hx hy hxy
  have hent := Real.binEntropy_strictAntiOn
    (entanglementArgument_mem_Icc y hy)
    (entanglementArgument_mem_Icc x hx) harg
  exact div_lt_div_of_pos_right hent (Real.log_pos one_lt_two)

theorem entanglementCurve_monotoneOn :
    MonotoneOn entanglementCurve (Set.Icc (0 : ℝ) 1) :=
  entanglementCurve_strictMonoOn.monotoneOn

theorem dampingCoefficient_mem_Icc
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    2 * Real.sqrt (p * (1 - p)) ∈ Set.Icc (0 : ℝ) 1 := by
  have hprod : 0 ≤ p * (1 - p) :=
    mul_nonneg hp0 (sub_nonneg.mpr hp1)
  have hs0 := Real.sqrt_nonneg (p * (1 - p))
  have hssq := Real.sq_sqrt hprod
  constructor
  · positivity
  · nlinarith [sq_nonneg (2 * p - 1)]

/-- For physical damping parameters, the fixed-excitation entropy curve is
monotone in the excitation. -/
theorem dampingEntropyCurve_monotoneOn
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    MonotoneOn (dampingEntropyCurve p) (Set.Icc (0 : ℝ) 1) := by
  intro x hx y hy hxy
  let k := 2 * Real.sqrt (p * (1 - p))
  have hk : k ∈ Set.Icc (0 : ℝ) 1 :=
    dampingCoefficient_mem_Icc p hp0 hp1
  apply entanglementCurve_monotoneOn
  · exact ⟨mul_nonneg hk.1 hx.1, mul_le_one₀ hk.2 hx.1 hx.2⟩
  · exact ⟨mul_nonneg hk.1 hy.1, mul_le_one₀ hk.2 hy.1 hy.2⟩
  · exact mul_le_mul_of_nonneg_left hxy hk.1

/-- The gap whose nonnegativity is the elementary logarithmic inequality
behind convexity of the concurrence entropy curve. -/
def logRatioGap (r : ℝ) : ℝ :=
  Real.log (1 + r) - Real.log (1 - r) - 2 * r

theorem hasDerivAt_logRatioGap {r : ℝ} (hrneg : -1 < r) (hrone : r < 1) :
    HasDerivAt logRatioGap (2 * r ^ 2 / (1 - r ^ 2)) r := by
  have hp : 1 + r ≠ 0 := by linarith
  have hm : 1 - r ≠ 0 := by linarith
  have hdenpos : 0 < 1 - r ^ 2 := by
    nlinarith [mul_pos (show 0 < 1 - r by linarith)
      (show 0 < 1 + r by linarith)]
  unfold logRatioGap
  convert
    ((((hasDerivAt_const r (1 : ℝ)).add (hasDerivAt_id r)).log hp).sub
      (((hasDerivAt_const r (1 : ℝ)).sub (hasDerivAt_id r)).log hm)).sub
      ((hasDerivAt_const r (2 : ℝ)).mul (hasDerivAt_id r)) using 1
  all_goals
    dsimp
    field_simp [hdenpos.ne']
    ring

theorem logRatioGap_nonneg {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    0 ≤ logRatioGap r := by
  have hcont : ContinuousOn logRatioGap (Set.Icc (0 : ℝ) r) := by
    intro x hx
    rcases hx with ⟨hx0, hxr⟩
    have hp : 1 + x ≠ 0 := by linarith
    have hm : 1 - x ≠ 0 := by linarith
    unfold logRatioGap
    fun_prop
  have hdiff : DifferentiableOn ℝ logRatioGap
      (interior (Set.Icc (0 : ℝ) r)) := by
    intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    exact (hasDerivAt_logRatioGap (by linarith) (by linarith)).differentiableAt.differentiableWithinAt
  have hderiv : ∀ x ∈ interior (Set.Icc (0 : ℝ) r),
      0 ≤ deriv logRatioGap x := by
    intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    rw [(hasDerivAt_logRatioGap (by linarith) (by linarith)).deriv]
    have hden : 0 < 1 - x ^ 2 := by
      have hxsq : x ^ 2 < (1 : ℝ) ^ 2 :=
        (sq_lt_sq₀ (le_of_lt hx.1) zero_le_one).2 (hx.2.trans hr1)
      nlinarith
    positivity
  have hmono := monotoneOn_of_deriv_nonneg
    (convex_Icc (0 : ℝ) r) hcont hdiff hderiv
  have h := hmono (Set.left_mem_Icc.mpr hr0) (Set.right_mem_Icc.mpr hr0) hr0
  simpa [logRatioGap] using h

/-- Elementary logarithmic inequality used in the curvature computation. -/
theorem two_mul_le_log_one_add_div_one_sub
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    2 * r ≤ Real.log ((1 + r) / (1 - r)) := by
  have hp : 1 + r ≠ 0 := by linarith
  have hm : 1 - r ≠ 0 := by linarith
  rw [Real.log_div hp hm]
  have h := logRatioGap_nonneg hr0 hr1
  unfold logRatioGap at h
  linarith

theorem entanglementCurve_continuous : Continuous entanglementCurve := by
  rw [show entanglementCurve =
      fun c => Real.binEntropy (entanglementArgument c) / Real.log 2 from
    funext entanglementCurve_eq]
  unfold entanglementArgument
  fun_prop

/-- Radius appearing in the concurrence parametrization. -/
def concurrenceRadius (c : ℝ) : ℝ := Real.sqrt (1 - c ^ 2)

def concurrenceSlope (c : ℝ) : ℝ :=
  let r := concurrenceRadius c
  c * (Real.log (1 + r) - Real.log (1 - r)) /
    (2 * r * Real.log 2)

def concurrenceCurvature (c : ℝ) : ℝ :=
  let r := concurrenceRadius c
  (Real.log (1 + r) - Real.log (1 - r) - 2 * r) /
    (2 * r ^ 3 * Real.log 2)

theorem concurrenceRadius_pos {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    0 < concurrenceRadius c := by
  unfold concurrenceRadius
  apply Real.sqrt_pos.2
  have hcsq : c ^ 2 < (1 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hc0.le zero_le_one).2 hc1
  nlinarith

theorem concurrenceRadius_lt_one {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    concurrenceRadius c < 1 := by
  have hrad : 0 ≤ 1 - c ^ 2 := by
    have hcsq : c ^ 2 ≤ (1 : ℝ) ^ 2 :=
      (sq_le_sq₀ hc0.le zero_le_one).2 hc1.le
    nlinarith
  have hrsq := Real.sq_sqrt hrad
  have hc2 : 0 < c ^ 2 := sq_pos_of_pos hc0
  have hr0 := Real.sqrt_nonneg (1 - c ^ 2)
  unfold concurrenceRadius
  nlinarith

theorem hasDerivAt_concurrenceRadius {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    HasDerivAt concurrenceRadius (-c / concurrenceRadius c) c := by
  have hrpos := concurrenceRadius_pos hc0 hc1
  have hinside : HasDerivAt (fun x : ℝ => 1 - x ^ 2) (-2 * c) c := by
    simpa [mul_comm] using
      (hasDerivAt_const c (1 : ℝ)).sub ((hasDerivAt_id c).pow 2)
  have hradpos : 0 < 1 - c ^ 2 := by
    have hcsq : c ^ 2 < (1 : ℝ) ^ 2 :=
      (sq_lt_sq₀ hc0.le zero_le_one).2 hc1
    nlinarith
  have hsqrt := hinside.sqrt hradpos.ne'
  unfold concurrenceRadius
  convert hsqrt using 1
  field_simp [hrpos.ne']

/-- First derivative formula for the concurrence entropy curve on `(0,1)`. -/
theorem hasDerivAt_entanglementCurve {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    HasDerivAt entanglementCurve (concurrenceSlope c) c := by
  let r := concurrenceRadius c
  have hrpos : 0 < r := concurrenceRadius_pos hc0 hc1
  have hr1 : r < 1 := concurrenceRadius_lt_one hc0 hc1
  have hrderiv : HasDerivAt concurrenceRadius (-c / r) c :=
    hasDerivAt_concurrenceRadius hc0 hc1
  have harg : HasDerivAt entanglementArgument (-c / (2 * r)) c := by
    unfold entanglementArgument
    convert ((hasDerivAt_const c (1 : ℝ)).add hrderiv).div_const 2 using 1
    field_simp [hrpos.ne']
    ring
  have harg0 : entanglementArgument c ≠ 0 := by
    have := Real.sqrt_nonneg (1 - c ^ 2)
    unfold entanglementArgument
    positivity
  have harg1 : entanglementArgument c ≠ 1 := by
    apply ne_of_lt
    change (1 + concurrenceRadius c) / 2 < 1
    dsimp [r] at hr1
    linarith
  have hbin := (Real.hasDerivAt_binEntropy harg0 harg1).comp c harg
  have hscaled := hbin.div_const (Real.log 2)
  rw [show entanglementCurve =
      fun x => Real.binEntropy (entanglementArgument x) / Real.log 2 from
    funext entanglementCurve_eq]
  convert hscaled using 1
  · unfold concurrenceSlope
    change
      c * (Real.log (1 + r) - Real.log (1 - r)) /
          (2 * r * Real.log 2) = _
    have hp : 1 + r ≠ 0 := by linarith
    have hm : 1 - r ≠ 0 := by linarith
    have htwo : (2 : ℝ) ≠ 0 := by norm_num
    have hrewrite0 :
        1 - entanglementArgument c = (1 - concurrenceRadius c) / 2 := by
      unfold entanglementArgument
      unfold concurrenceRadius
      ring
    have hrewrite1 :
        entanglementArgument c = (1 + concurrenceRadius c) / 2 := by
      unfold entanglementArgument
      unfold concurrenceRadius
      rfl
    rw [hrewrite0, hrewrite1]
    change
      _ = (Real.log ((1 - r) / 2) - Real.log ((1 + r) / 2)) *
        (-c / (2 * r)) / Real.log 2
    rw [Real.log_div hm htwo,
      Real.log_div hp htwo]
    field_simp [hrpos.ne', (Real.log_pos one_lt_two).ne']
    ring

/-- Second derivative formula on the open physical interval. -/
theorem hasDerivAt_concurrenceSlope {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    HasDerivAt concurrenceSlope (concurrenceCurvature c) c := by
  let r := concurrenceRadius c
  let ell := Real.log (1 + r) - Real.log (1 - r)
  have hrpos : 0 < r := concurrenceRadius_pos hc0 hc1
  have hr1 : r < 1 := concurrenceRadius_lt_one hc0 hc1
  have hp : 1 + r ≠ 0 := by linarith
  have hm : 1 - r ≠ 0 := by linarith
  have hrdef : concurrenceRadius c = r := rfl
  have hrderiv : HasDerivAt concurrenceRadius (-c / r) c :=
    hasDerivAt_concurrenceRadius hc0 hc1
  have hlogPlus : HasDerivAt
      (fun x => Real.log (1 + concurrenceRadius x))
      ((-c / r) / (1 + r)) c := by
    convert ((hasDerivAt_const c (1 : ℝ)).add hrderiv).log hp using 1
    simp [hrdef]
  have hlogMinus : HasDerivAt
      (fun x => Real.log (1 - concurrenceRadius x))
      ((c / r) / (1 - r)) c := by
    convert ((hasDerivAt_const c (1 : ℝ)).sub hrderiv).log hm using 1
    simp [hrdef]
    ring
  have hell : HasDerivAt
      (fun x => Real.log (1 + concurrenceRadius x) -
        Real.log (1 - concurrenceRadius x))
      (((-c / r) / (1 + r)) - ((c / r) / (1 - r))) c :=
    hlogPlus.sub hlogMinus
  have hraw := (((hasDerivAt_id c).mul hell).div hrderiv hrpos.ne').div_const
    (2 * Real.log 2)
  convert hraw using 1
  · funext x
    simp [concurrenceSlope]
    ring
  · unfold concurrenceCurvature
    change
      (Real.log (1 + r) - Real.log (1 - r) - 2 * r) /
          (2 * r ^ 3 * Real.log 2) = _
    have hrad : 0 ≤ 1 - c ^ 2 := by
      have hcsq : c ^ 2 ≤ (1 : ℝ) ^ 2 :=
        (sq_le_sq₀ hc0.le zero_le_one).2 hc1.le
      nlinarith
    have hrsq : r ^ 2 = 1 - c ^ 2 := by
      dsimp [r, concurrenceRadius]
      exact Real.sq_sqrt hrad
    have hlog2 : Real.log 2 ≠ 0 := (Real.log_pos one_lt_two).ne'
    simp only [one_mul, id_eq, Pi.mul_apply]
    change
      (ell - 2 * r) / (2 * r ^ 3 * Real.log 2) =
        (((ell + c *
            ((-c / r) / (1 + r) - (c / r) / (1 - r))) * r -
          (c * ell) * (-c / r)) / r ^ 2) / (2 * Real.log 2)
    have hcsq : c ^ 2 = 1 - r ^ 2 := by linarith [hrsq]
    field_simp [hrpos.ne', hp, hm, hlog2]
    rw [hcsq]
    ring

theorem concurrenceCurvature_nonneg {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) :
    0 ≤ concurrenceCurvature c := by
  let r := concurrenceRadius c
  have hrpos : 0 < r := concurrenceRadius_pos hc0 hc1
  have hr1 : r < 1 := concurrenceRadius_lt_one hc0 hc1
  have hgap := logRatioGap_nonneg hrpos.le hr1
  unfold concurrenceCurvature
  change 0 ≤
    (Real.log (1 + r) - Real.log (1 - r) - 2 * r) /
      (2 * r ^ 3 * Real.log 2)
  exact div_nonneg hgap (by positivity)

/-- Convexity of the binary-spectrum concurrence entropy on its physical
domain. -/
theorem entanglementCurve_convexOn :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) entanglementCurve := by
  apply convexOn_of_hasDerivWithinAt2_nonneg
    (convex_Icc (0 : ℝ) 1) entanglementCurve_continuous.continuousOn
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    exact (hasDerivAt_entanglementCurve hx.1 hx.2).hasDerivWithinAt
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    exact (hasDerivAt_concurrenceSlope hx.1 hx.2).hasDerivWithinAt
  · intro x hx
    simp only [interior_Icc, Set.mem_Ioo] at hx
    exact concurrenceCurvature_nonneg hx.1 hx.2

/-- The scalar curve governing pure amplitude-damping outputs is convex for
every physical damping parameter. -/
theorem dampingEntropyCurve_convexOn
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ConvexOn ℝ (Set.Icc (0 : ℝ) 1) (dampingEntropyCurve p) := by
  let k := 2 * Real.sqrt (p * (1 - p))
  have hk : k ∈ Set.Icc (0 : ℝ) 1 :=
    dampingCoefficient_mem_Icc p hp0 hp1
  refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hkx : k * x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hk.1 hx.1, mul_le_one₀ hk.2 hx.1 hx.2⟩
  have hky : k * y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hk.1 hy.1, mul_le_one₀ hk.2 hy.1 hy.2⟩
  have h := entanglementCurve_convexOn.2 hkx hky ha hb hab
  unfold dampingEntropyCurve
  change entanglementCurve (k * (a • x + b • y)) ≤
    a • entanglementCurve (k * x) + b • entanglementCurve (k * y)
  calc
    entanglementCurve (k * (a • x + b • y)) =
        entanglementCurve (a • (k * x) + b • (k * y)) := by
      congr 1
      simp [smul_eq_mul]
      ring
    _ ≤ a • entanglementCurve (k * x) + b • entanglementCurve (k * y) := h

end

end AmplitudeDamping
