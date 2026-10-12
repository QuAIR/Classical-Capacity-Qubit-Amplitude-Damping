import AmplitudeDamping.ExcitationConstraint
import AmplitudeDamping.CapacityBridge

/-! # The unique interior scalar optimizer for nonconstant amplitude damping -/
namespace AmplitudeDamping
open QIT
noncomputable section

/-- Binary entropy after nonzero attenuation is strictly concave. -/
theorem binaryEntropy_strictConcaveOn_mul_const
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun q => binaryEntropy ((1 - p) * q)) := by
  refine ⟨convex_Icc _ _, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hc : 0 < 1 - p := sub_pos.mpr hp1
  have hcx : (1 - p) * x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hc.le hx.1, mul_le_one₀ (by linarith) hx.1 hx.2⟩
  have hcy : (1 - p) * y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hc.le hy.1, mul_le_one₀ (by linarith) hy.1 hy.2⟩
  have hne : (1 - p) * x ≠ (1 - p) * y := fun h =>
    hxy (mul_left_cancel₀ hc.ne' h)
  have h := Real.strictConcave_binEntropy.2 hcx hcy hne ha hb hab
  simp only [smul_eq_mul] at h ⊢
  have heq : (1 - p) * (a * x + b * y) =
      a * ((1 - p) * x) + b * ((1 - p) * y) := by ring
  simp only [binaryEntropy_eq_binEntropy_div_log_two, heq]
  have ht := div_lt_div_of_pos_right h (Real.log_pos one_lt_two)
  convert ht using 1
  ring

/-- The information curve is strictly concave on the full physical interval. -/
theorem amplitudeDampingScalarInformation_strictConcaveOn
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    StrictConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (amplitudeDampingScalarInformation p) :=
  (binaryEntropy_strictConcaveOn_mul_const p hp0 hp1).sub_convexOn
    (dampingEntropyCurve_convexOn p hp0 hp1.le)

@[simp] theorem amplitudeDampingScalarInformation_zero (p : ℝ) :
    amplitudeDampingScalarInformation p 0 = 0 := by
  simp [amplitudeDampingScalarInformation, dampingEntropyCurve, entanglementCurve,
    binaryEntropy_eq_binEntropy_div_log_two]

@[simp] theorem amplitudeDampingScalarInformation_at_excitation_one
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    amplitudeDampingScalarInformation p 1 = 0 := by
  have h := entanglementCurve_two_sqrt_mul_one_sub_eq_binaryEntropy hp0 hp1
  simp only [amplitudeDampingScalarInformation, dampingEntropyCurve, mul_one,
    h, binaryEntropy_one_sub, sub_self]

/-- Every interior excitation gives strictly positive information when p < 1. -/
theorem amplitudeDampingScalarInformation_pos
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    0 < amplitudeDampingScalarInformation p q := by
  have h := (amplitudeDampingScalarInformation_strictConcaveOn p hp0 hp1).2
    (show (0 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
    (show (1 : ℝ) ∈ Set.Icc (0 : ℝ) 1 by simp)
    (by norm_num : (0 : ℝ) ≠ 1)
    (sub_pos.mpr hq1) hq0 (show 1 - q + q = 1 by ring)
  simpa [smul_eq_mul, amplitudeDampingScalarInformation_at_excitation_one p hp0 hp1.le] using h

/-- There is exactly one capacity-maximizing excitation, and it lies in (0,1). -/
theorem existsUnique_amplitudeDamping_scalarInformation_maximizer
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∃! q : ℝ, q ∈ Set.Ioo (0 : ℝ) 1 ∧
      IsMaxOn (amplitudeDampingScalarInformation p) (Set.Icc (0 : ℝ) 1) q := by
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (amplitudeDampingScalarInformation_continuous p).continuousOn
  have hpos : 0 < amplitudeDampingScalarInformation p q :=
    (amplitudeDampingScalarInformation_pos p hp0 hp1 (q := 1 / 2)
      (by norm_num) (by norm_num)).trans_le (hmax (by norm_num))
  have hq0 : 0 < q := lt_of_le_of_ne hq.1 (by
    intro h; rw [← h, amplitudeDampingScalarInformation_zero] at hpos; exact hpos.false)
  have hq1 : q < 1 := lt_of_le_of_ne hq.2 (by
    intro h; rw [h, amplitudeDampingScalarInformation_at_excitation_one p hp0 hp1.le] at hpos
    exact hpos.false)
  refine ⟨q, ⟨⟨hq0, hq1⟩, hmax⟩, ?_⟩
  intro r hr
  exact (amplitudeDampingScalarInformation_strictConcaveOn p hp0 hp1).eq_of_isMaxOn
    hr.2 hmax ⟨hr.1.1.le, hr.1.2.le⟩ hq

/-- The unique optimal excitation. -/
def optimalExcitation (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) : ℝ :=
  (existsUnique_amplitudeDamping_scalarInformation_maximizer p hp0 hp1).exists.choose

theorem optimalExcitation_mem_Ioo (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    optimalExcitation p hp0 hp1 ∈ Set.Ioo (0 : ℝ) 1 :=
  (existsUnique_amplitudeDamping_scalarInformation_maximizer p hp0 hp1).exists.choose_spec.1

theorem optimalExcitation_isMaxOn (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    IsMaxOn (amplitudeDampingScalarInformation p) (Set.Icc (0 : ℝ) 1)
      (optimalExcitation p hp0 hp1) :=
  (existsUnique_amplitudeDamping_scalarInformation_maximizer p hp0 hp1).exists.choose_spec.2

/-- The capacity is the information curve at its unique optimizer. -/
theorem amplitudeDamping_classicalCapacity_eq_optimalExcitation
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Channel.classicalCapacity.{0, 0, 0} (amplitudeDamping p hp0 hp1.le) =
      amplitudeDampingScalarInformation p (optimalExcitation p hp0 hp1) := by
  rw [amplitudeDamping_classicalCapacity_eq_holevoInformation,
    amplitudeDamping_holevoInformation_eq_scalarSup]
  apply le_antisymm
  · apply csSup_le (amplitudeDampingScalarInformationValues_nonempty p)
    rintro r ⟨q, hq, rfl⟩
    exact optimalExcitation_isMaxOn p hp0 hp1 hq
  · exact le_csSup (amplitudeDampingScalarInformationValues_bddAbove p hp0 hp1.le)
      ⟨_, ⟨(optimalExcitation_mem_Ioo p hp0 hp1).1.le,
        (optimalExcitation_mem_Ioo p hp0 hp1).2.le⟩, rfl⟩

/-- Derivative of the convex output-entropy curve. -/
def dampingEntropySlope (p q : ℝ) : ℝ :=
  (2 * Real.sqrt (p * (1 - p))) *
    concurrenceSlope ((2 * Real.sqrt (p * (1 - p))) * q)

theorem hasDerivAt_dampingEntropyCurve
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (dampingEntropyCurve p) (dampingEntropySlope p q) q := by
  by_cases hp : p = 0
  · subst p
    have heq : dampingEntropyCurve 0 = fun _ => entanglementCurve 0 := by
      funext x
      simp [dampingEntropyCurve]
    rw [heq]
    simpa [dampingEntropySlope] using (hasDerivAt_const q (entanglementCurve 0))
  · have hk0 : 0 < 2 * Real.sqrt (p * (1 - p)) := by positivity
    have hk1 := (dampingCoefficient_mem_Icc p hp0 hp1.le).2
    have harg0 : 0 < (2 * Real.sqrt (p * (1 - p))) * q := mul_pos hk0 hq0
    have harg1 : (2 * Real.sqrt (p * (1 - p))) * q < 1 := by nlinarith
    simpa [dampingEntropyCurve, dampingEntropySlope, mul_comm] using
      (hasDerivAt_entanglementCurve harg0 harg1).comp q
        ((hasDerivAt_id q).const_mul (2 * Real.sqrt (p * (1 - p))))

/-- Derivative of bit-valued binary entropy on the interior. -/
theorem hasDerivAt_binaryEntropy {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt binaryEntropy ((Real.log (1 - q) - Real.log q) / Real.log 2) q := by
  simpa only [← binaryEntropy_eq_binEntropy_div_log_two] using
    (Real.hasDerivAt_binEntropy hq0.ne' (ne_of_lt hq1)).div_const (Real.log 2)

/-- Stationarity balances the output entropy slope and the convex-roof slope. -/
theorem optimalExcitation_stationary
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (1 - p) *
        ((Real.log (1 - (1 - p) * optimalExcitation p hp0 hp1) -
          Real.log ((1 - p) * optimalExcitation p hp0 hp1)) / Real.log 2) =
      dampingEntropySlope p (optimalExcitation p hp0 hp1) := by
  let q := optimalExcitation p hp0 hp1
  have hq := optimalExcitation_mem_Ioo p hp0 hp1
  have hx0 : 0 < (1 - p) * q := mul_pos (sub_pos.mpr hp1) hq.1
  have hx1 : (1 - p) * q < 1 := by dsimp [q]; nlinarith [hq.2]
  have hder := ((hasDerivAt_binaryEntropy hx0 hx1).comp q
    ((hasDerivAt_id q).const_mul (1 - p))).sub
      (hasDerivAt_dampingEntropyCurve p hp0 hp1 hq.1 hq.2)
  have hloc : IsLocalMax (amplitudeDampingScalarInformation p) q :=
    (optimalExcitation_isMaxOn p hp0 hp1).isLocalMax
      (mem_interior_iff_mem_nhds.mp (by simpa only [interior_Icc] using hq))
  have hz := hloc.hasDerivAt_eq_zero hder
  dsimp [q] at hz
  nlinarith [hz]

/-- The convexity remainder at an interior reference excitation. -/
def dampingBregman (p qref q : ℝ) : ℝ :=
  dampingEntropyCurve p q - dampingEntropyCurve p qref -
    dampingEntropySlope p qref * (q - qref)

/-- Every Bregman term in the finite-block deficit is nonnegative. -/
theorem dampingBregman_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    {qref q : ℝ} (href : qref ∈ Set.Ioo (0 : ℝ) 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) : 0 ≤ dampingBregman p qref q := by
  have hc := dampingEntropyCurve_convexOn p hp0 hp1.le
  have hd := hasDerivAt_dampingEntropyCurve p hp0 hp1 href.1 href.2
  have hr : qref ∈ Set.Icc (0 : ℝ) 1 := ⟨href.1.le, href.2.le⟩
  rcases lt_trichotomy qref q with hlt | heq | hgt
  · have h := hc.le_slope_of_hasDerivAt hr hq hlt hd
    rw [slope_def_field] at h
    have h' := (le_div_iff₀ (sub_pos.mpr hlt)).mp h
    unfold dampingBregman
    linarith
  · subst q
    simp [dampingBregman]
  · have h := hc.slope_le_of_hasDerivAt hq hr hgt hd
    rw [slope_def_field] at h
    have h' := (div_le_iff₀ (sub_pos.mpr hgt)).mp h
    unfold dampingBregman
    nlinarith

end
end AmplitudeDamping
