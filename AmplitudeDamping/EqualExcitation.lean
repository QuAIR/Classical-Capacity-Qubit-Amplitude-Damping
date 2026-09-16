import AmplitudeDamping.ScalarCurve
import AmplitudeDamping.QubitState

/-!
# Equal-excitation decompositions of qubit states

Every qubit state is a convex combination of two pure states having the same
excited-state population as the original state.  Geometrically, the two pure
states are antipodal points on the fixed-latitude circle of the Bloch sphere.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder NNReal

namespace AmplitudeDamping

open QIT

noncomputable section

/-- A totalized complex phase.  At the origin we choose phase one. -/
def coherencePhase (z : ℂ) : ℂ :=
  if z = 0 then 1 else z / (‖z‖ : ℂ)

theorem coherencePhase_normSq (z : ℂ) :
    Complex.normSq (coherencePhase z) = 1 := by
  by_cases hz : z = 0
  · simp [coherencePhase, hz]
  · have hn : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    simp [coherencePhase, hz, Complex.normSq_eq_norm_sq, hn, pow_two]

theorem norm_mul_coherencePhase (z : ℂ) :
    (‖z‖ : ℂ) * coherencePhase z = z := by
  by_cases hz : z = 0
  · simp [coherencePhase, hz]
  · have hnR : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    have hnC : (‖z‖ : ℂ) ≠ 0 := by exact_mod_cast hnR
    rw [coherencePhase, if_neg hz]
    exact mul_div_cancel₀ z hnC

/-- A normalized qubit vector with excitation `q` and equatorial phase `u`.
The hypothesis on `u` says precisely that it is a complex phase. -/
def fixedExcitationVector (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (u : ℂ) (hu : Complex.normSq u = 1) : PureVector Qubit where
  amp := ![((Real.sqrt (1 - q) : ℂ) * u), (Real.sqrt q : ℂ)]
  trace_rankOne_eq_one := by
    have hs0 : (Real.sqrt (1 - q)) ^ 2 = 1 - q :=
      Real.sq_sqrt (sub_nonneg.mpr hq1)
    have hs1 : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq0
    rw [rankOneMatrix_trace]
    simp only [dotProduct, Fin.sum_univ_two, Matrix.cons_val_zero,
      Matrix.cons_val_one]
    change
      ((Real.sqrt (1 - q) : ℂ) * u) *
          (starRingEnd ℂ) ((Real.sqrt (1 - q) : ℂ) * u) +
        (Real.sqrt q : ℂ) * (starRingEnd ℂ) (Real.sqrt q : ℂ) = 1
    rw [Complex.mul_conj, Complex.mul_conj, Complex.normSq_mul,
      Complex.normSq_ofReal, Complex.normSq_ofReal, hu]
    norm_num [pow_two] at hs0 hs1 ⊢
    norm_cast
    nlinarith

@[simp]
theorem fixedExcitationVector_amp_zero
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (u : ℂ) (hu : Complex.normSq u = 1) :
    (fixedExcitationVector q hq0 hq1 u hu).amp 0 =
      (Real.sqrt (1 - q) : ℂ) * u := rfl

@[simp]
theorem fixedExcitationVector_amp_one
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (u : ℂ) (hu : Complex.normSq u = 1) :
    (fixedExcitationVector q hq0 hq1 u hu).amp 1 =
      (Real.sqrt q : ℂ) := rfl

@[simp]
theorem fixedExcitationVector_excitationProbability
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (u : ℂ) (hu : Complex.normSq u = 1) :
    excitationProbability (fixedExcitationVector q hq0 hq1 u hu) = q := by
  unfold excitationProbability
  rw [fixedExcitationVector_amp_one, Complex.normSq_ofReal,
    ← pow_two, Real.sq_sqrt hq0]

/-- Radius of the fixed-excitation coherence circle. -/
def fixedExcitationRadius (q : ℝ) : ℝ :=
  Real.sqrt (1 - q) * Real.sqrt q

theorem fixedExcitationRadius_sq (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (fixedExcitationRadius q) ^ 2 = q * (1 - q) := by
  unfold fixedExcitationRadius
  rw [mul_pow, Real.sq_sqrt (sub_nonneg.mpr hq1), Real.sq_sqrt hq0]
  ring

theorem fixedExcitationVector_state_matrix
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (u : ℂ) (hu : Complex.normSq u = 1) :
    (fixedExcitationVector q hq0 hq1 u hu).state.matrix =
      !![((1 - q : ℝ) : ℂ), ((fixedExcitationRadius q : ℝ) : ℂ) * u;
         ((fixedExcitationRadius q : ℝ) : ℂ) * star u, ((q : ℝ) : ℂ)] := by
  have hs0 : (Real.sqrt (1 - q)) ^ 2 = 1 - q :=
    Real.sq_sqrt (sub_nonneg.mpr hq1)
  have hs1 : (Real.sqrt q) ^ 2 = q := Real.sq_sqrt hq0
  ext i j
  fin_cases i <;> fin_cases j
  · change
      ((Real.sqrt (1 - q) : ℂ) * u) *
          (starRingEnd ℂ) ((Real.sqrt (1 - q) : ℂ) * u) =
        ((1 - q : ℝ) : ℂ)
    rw [Complex.mul_conj, Complex.normSq_mul, Complex.normSq_ofReal, hu]
    norm_num [pow_two] at hs0 ⊢
    exact_mod_cast hs0
  · change
      ((Real.sqrt (1 - q) : ℂ) * u) *
          (starRingEnd ℂ) (Real.sqrt q : ℂ) =
        ((fixedExcitationRadius q : ℝ) : ℂ) * u
    simp [fixedExcitationRadius]
    ring
  · change
      (Real.sqrt q : ℂ) *
          (starRingEnd ℂ) ((Real.sqrt (1 - q) : ℂ) * u) =
        ((fixedExcitationRadius q : ℝ) : ℂ) * star u
    simp [fixedExcitationRadius]
    ring
  · change
      (Real.sqrt q : ℂ) * (starRingEnd ℂ) (Real.sqrt q : ℂ) =
        ((q : ℝ) : ℂ)
    rw [Complex.mul_conj, Complex.normSq_ofReal]
    norm_num [pow_two] at hs1 ⊢
    exact_mod_cast hs1

/-- The two antipodal fixed-excitation pure states, with mixing weight
`lambda` on the positive phase. -/
def antipodalDecomposition
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (u : ℂ) (hu : Complex.normSq u = 1)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    PureDecomposition Qubit where
  card := 2
  probs := ![⟨lambda, hlambda0⟩, ⟨1 - lambda, sub_nonneg.mpr hlambda1⟩]
  weights_sum := by
    apply NNReal.eq
    rw [Fin.sum_univ_two]
    change lambda + (1 - lambda) = 1
    ring
  vectors := ![
    fixedExcitationVector q hq0 hq1 u hu,
    fixedExcitationVector q hq0 hq1 (-u) (by
      exact (Complex.normSq_neg u).trans hu)]

@[simp]
theorem antipodalDecomposition_card
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (u : ℂ) (hu : Complex.normSq u = 1)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (antipodalDecomposition q hq0 hq1 u hu
      lambda hlambda0 hlambda1).card = 2 := rfl

theorem antipodalDecomposition_excitationProbability
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (u : ℂ) (hu : Complex.normSq u = 1)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1)
    (i : Fin (antipodalDecomposition q hq0 hq1 u hu
      lambda hlambda0 hlambda1).card) :
    excitationProbability
        ((antipodalDecomposition q hq0 hq1 u hu
          lambda hlambda0 hlambda1).vectors i) = q := by
  fin_cases i
  · exact fixedExcitationVector_excitationProbability q hq0 hq1 u hu
  · exact fixedExcitationVector_excitationProbability q hq0 hq1 (-u)
      ((Complex.normSq_neg u).trans hu)

/-- Matrix of the antipodal average.  Only the coherence is attenuated, by
the real factor `2 * lambda - 1`. -/
theorem antipodalDecomposition_averageState_matrix
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (u : ℂ) (hu : Complex.normSq u = 1)
    (lambda : ℝ) (hlambda0 : 0 ≤ lambda) (hlambda1 : lambda ≤ 1) :
    (antipodalDecomposition q hq0 hq1 u hu
      lambda hlambda0 hlambda1).averageState.matrix =
      !![((1 - q : ℝ) : ℂ),
          (((2 * lambda - 1) * fixedExcitationRadius q : ℝ) : ℂ) * u;
         (((2 * lambda - 1) * fixedExcitationRadius q : ℝ) : ℂ) * star u,
          ((q : ℝ) : ℂ)] := by
  rw [PureDecomposition.averageState, Ensemble.averageState_matrix]
  change
    (∑ k : Fin 2,
      (((![⟨lambda, hlambda0⟩,
          ⟨1 - lambda, sub_nonneg.mpr hlambda1⟩] k : ℝ≥0) : ℝ) : ℂ) •
        (![fixedExcitationVector q hq0 hq1 u hu,
           fixedExcitationVector q hq0 hq1 (-u)
             ((Complex.normSq_neg u).trans hu)] k).state.matrix) = _
  rw [Fin.sum_univ_two]
  change
    ((lambda : ℂ) • (fixedExcitationVector q hq0 hq1 u hu).state.matrix) +
      (((1 - lambda : ℝ) : ℂ) •
        (fixedExcitationVector q hq0 hq1 (-u)
          ((Complex.normSq_neg u).trans hu)).state.matrix) = _
  rw [fixedExcitationVector_state_matrix,
    fixedExcitationVector_state_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp <;>
    ring

/-- Every qubit state has a two-member pure-state decomposition in which both
members have exactly the excitation of the mixed state. -/
theorem exists_twoState_equalExcitation_decomposition (rho : State Qubit) :
    ∃ E : PureDecomposition Qubit,
      E.card = 2 ∧
      E.averageState = rho ∧
      ∀ i, excitationProbability (E.vectors i) = stateExcitation rho := by
  let q : ℝ := stateExcitation rho
  let z : ℂ := rho.matrix 0 1
  let r : ℝ := fixedExcitationRadius q
  have hq0 : 0 ≤ q := stateExcitation_nonneg rho
  have hq1 : q ≤ 1 := stateExcitation_le_one rho
  have hr0 : 0 ≤ r := by
    dsimp [r]
    exact mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hrsq : r ^ 2 = q * (1 - q) :=
    fixedExcitationRadius_sq q hq0 hq1
  have hzsq : Complex.normSq z ≤ q * (1 - q) :=
    qubit_coherence_normSq_le rho
  let u : ℂ := coherencePhase z
  have hu : Complex.normSq u = 1 := coherencePhase_normSq z
  have hphase : ((‖z‖ : ℝ) : ℂ) * u = z :=
    norm_mul_coherencePhase z
  have hphaseStar : ((‖z‖ : ℝ) : ℂ) * star u = star z := by
    have h := congrArg star hphase
    simpa using h
  by_cases hr : r = 0
  · have hzsq0 : Complex.normSq z = 0 := by
      have : q * (1 - q) = 0 := by nlinarith [hrsq]
      apply le_antisymm
      · simpa [this] using hzsq
      · exact Complex.normSq_nonneg z
    have hz : z = 0 := Complex.normSq_eq_zero.mp hzsq0
    let E := antipodalDecomposition q hq0 hq1 u hu
      (1 / 2) (by norm_num) (by norm_num)
    refine ⟨E, rfl, ?_, ?_⟩
    · apply State.ext
      rw [antipodalDecomposition_averageState_matrix,
        qubit_state_matrix_eq]
      simp [q, z, r, hr, hz]
    · intro i
      exact antipodalDecomposition_excitationProbability
        q hq0 hq1 u hu (1 / 2) (by norm_num) (by norm_num) i
  · have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hr)
    have hnormsq : ‖z‖ ^ 2 ≤ r ^ 2 := by
      rw [← Complex.normSq_eq_norm_sq, hrsq]
      exact hzsq
    have hnorm_le : ‖z‖ ≤ r := by
      nlinarith [norm_nonneg z]
    let t : ℝ := ‖z‖ / r
    have ht0 : 0 ≤ t := div_nonneg (norm_nonneg z) hr0
    have ht1 : t ≤ 1 := (div_le_one hrpos).mpr hnorm_le
    let lambda : ℝ := (1 + t) / 2
    have hlambda0 : 0 ≤ lambda := by
      dsimp [lambda]
      linarith
    have hlambda1 : lambda ≤ 1 := by
      dsimp [lambda]
      linarith
    have hfactor : (2 * lambda - 1) * r = ‖z‖ := by
      dsimp [lambda, t]
      field_simp
      ring
    let E := antipodalDecomposition q hq0 hq1 u hu
      lambda hlambda0 hlambda1
    refine ⟨E, rfl, ?_, ?_⟩
    · apply State.ext
      rw [antipodalDecomposition_averageState_matrix,
        qubit_state_matrix_eq, hfactor]
      ext i j
      fin_cases i <;> fin_cases j
      · rfl
      · exact hphase
      · exact hphaseStar
      · rfl
    · intro i
      exact antipodalDecomposition_excitationProbability
        q hq0 hq1 u hu lambda hlambda0 hlambda1 i

/-- The equal-excitation decomposition gives the upper bound in the
fixed-excitation convex-roof formula, with no analytic hypothesis. -/
theorem outputEntropyRoof_le_dampingEntropyCurve
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rho : State Qubit) :
    outputEntropyRoof (amplitudeDamping p hp0 hp1) rho ≤
      dampingEntropyCurve p (stateExcitation rho) := by
  obtain ⟨E, _, hErho, hEexc⟩ :=
    exists_twoState_equalExcitation_decomposition rho
  have hcost :
      E.outputCost (amplitudeDamping p hp0 hp1) =
        dampingEntropyCurve p (stateExcitation rho) := by
    rw [pureDecomposition_amplitudeDamping_outputCost]
    simp_rw [hEexc]
    rw [← Finset.sum_mul]
    have hweights := congrArg (fun x : ℝ≥0 => (x : ℝ)) E.weights_sum
    simpa using congrArg
      (fun x : ℝ => x * dampingEntropyCurve p (stateExcitation rho)) hweights
  have hupper := outputEntropyRoof_le_outputCost
    (amplitudeDamping p hp0 hp1) E
  rw [hErho, hcost] at hupper
  exact hupper

/-- Full fixed-excitation convex-roof formula, reduced to convexity of the
one-variable damping entropy curve. -/
theorem outputEntropyRoof_eq_dampingEntropyCurve_of_convex
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (hconv : ConvexOn ℝ (Set.Icc 0 1) (dampingEntropyCurve p))
    (rho : State Qubit) :
    outputEntropyRoof (amplitudeDamping p hp0 hp1) rho =
      dampingEntropyCurve p (stateExcitation rho) := by
  apply le_antisymm
  · exact outputEntropyRoof_le_dampingEntropyCurve p hp0 hp1 rho
  · exact dampingEntropyCurve_le_outputEntropyRoof_of_convex
      p hp0 hp1 hconv rho

/-- Exact fixed-excitation convex-roof formula for amplitude damping. -/
theorem outputEntropyRoof_eq_dampingEntropyCurve
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rho : State Qubit) :
    outputEntropyRoof (amplitudeDamping p hp0 hp1) rho =
      dampingEntropyCurve p (stateExcitation rho) :=
  outputEntropyRoof_eq_dampingEntropyCurve_of_convex
    p hp0 hp1 (dampingEntropyCurve_convexOn p hp0 hp1) rho

end

end AmplitudeDamping
