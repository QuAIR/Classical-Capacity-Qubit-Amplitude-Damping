import AmplitudeDamping.OneLetterCapacity

/-!
# Scalar reduction of the amplitude-damping one-letter formula
-/

namespace AmplitudeDamping

open QIT
open scoped ComplexOrder MatrixOrder NNReal

noncomputable section

theorem qubitDeterminant_eq_excitation_sub_coherence (rho : State Qubit) :
    qubitDeterminant rho =
      stateExcitation rho * (1 - stateExcitation rho) -
        Complex.normSq (rho.matrix 0 1) := by
  unfold qubitDeterminant
  rw [Matrix.det_fin_two, qubit_diagonal_zero rho,
    qubit_diagonal_one rho, qubit_lower_coherence rho]
  simp [Complex.normSq]
  ring

theorem qubitDeterminant_le_excitation_mul_one_sub (rho : State Qubit) :
    qubitDeterminant rho ≤
      stateExcitation rho * (1 - stateExcitation rho) := by
  rw [qubitDeterminant_eq_excitation_sub_coherence]
  exact sub_le_self _ (Complex.normSq_nonneg _)

/-- On the physical interval, the concurrence entropy evaluated at the
largest determinant compatible with excitation `q` is binary entropy. -/
theorem entanglementCurve_two_sqrt_mul_one_sub_eq_binaryEntropy
    {q : ℝ} (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    entanglementCurve (2 * Real.sqrt (q * (1 - q))) = binaryEntropy q := by
  have hprod : 0 ≤ q * (1 - q) := mul_nonneg hq0 (sub_nonneg.mpr hq1)
  have hsquare : (Real.sqrt (q * (1 - q))) ^ 2 = q * (1 - q) :=
    Real.sq_sqrt hprod
  have hrad :
      1 - (2 * Real.sqrt (q * (1 - q))) ^ 2 = (1 - 2 * q) ^ 2 := by
    nlinarith
  unfold entanglementCurve
  rw [hrad, Real.sqrt_sq_eq_abs]
  by_cases hq : q ≤ 1 / 2
  · rw [abs_of_nonneg (by linarith : 0 ≤ 1 - 2 * q)]
    have harg : (1 + (1 - 2 * q)) / 2 = 1 - q := by ring
    rw [harg, binaryEntropy_one_sub]
  · rw [abs_of_nonpos (by linarith : 1 - 2 * q ≤ 0)]
    congr 1
    ring

/-- A qubit has no more entropy than the diagonal state with the same
excitation probability. -/
theorem qubit_vonNeumann_le_binaryEntropy_excitation (rho : State Qubit) :
    rho.vonNeumann ≤ binaryEntropy (stateExcitation rho) := by
  let q := stateExcitation rho
  let d := qubitDeterminant rho
  have hq0 : 0 ≤ q := stateExcitation_nonneg rho
  have hq1 : q ≤ 1 := stateExcitation_le_one rho
  have hd0 : 0 ≤ d := qubitDeterminant_nonneg rho
  have hdle : d ≤ q * (1 - q) :=
    qubitDeterminant_le_excitation_mul_one_sub rho
  have hprod : 0 ≤ q * (1 - q) := mul_nonneg hq0 (sub_nonneg.mpr hq1)
  have hsqrt : Real.sqrt d ≤ Real.sqrt (q * (1 - q)) :=
    Real.sqrt_le_sqrt hdle
  have hcdet0 : 0 ≤ 2 * Real.sqrt d := by positivity
  have hcdet1 : 2 * Real.sqrt d ≤ 1 := by
    have hdisc := qubit_discriminant_eq_sq_eigenvalue_sub rho
    have hsqd : (Real.sqrt d) ^ 2 = d := Real.sq_sqrt hd0
    have hnon : 0 ≤ 1 - 4 * qubitDeterminant rho := by
      rw [hdisc]
      positivity
    have hfour : 4 * d ≤ 1 := by
      dsimp [d]
      linarith
    nlinarith [Real.sqrt_nonneg d]
  have hcmax0 : 0 ≤ 2 * Real.sqrt (q * (1 - q)) := by positivity
  have hcmax1 : 2 * Real.sqrt (q * (1 - q)) ≤ 1 := by
    have hsqp : (Real.sqrt (q * (1 - q))) ^ 2 = q * (1 - q) :=
      Real.sq_sqrt hprod
    nlinarith [sq_nonneg (2 * q - 1),
      sq_nonneg (1 - 2 * Real.sqrt (q * (1 - q)))]
  rw [qubit_vonNeumann_eq_entanglementCurve_det]
  calc
    entanglementCurve (2 * Real.sqrt d) ≤
        entanglementCurve (2 * Real.sqrt (q * (1 - q))) :=
      entanglementCurve_monotoneOn
        ⟨hcdet0, hcdet1⟩ ⟨hcmax0, hcmax1⟩
        (mul_le_mul_of_nonneg_left hsqrt (by norm_num))
    _ = binaryEntropy q :=
      entanglementCurve_two_sqrt_mul_one_sub_eq_binaryEntropy hq0 hq1

/-- The scalar information expression from the manuscript. -/
def amplitudeDampingScalarInformation (p q : ℝ) : ℝ :=
  binaryEntropy ((1 - p) * q) - dampingEntropyCurve p q

theorem amplitudeDamping_output_excitation
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rho : State Qubit) :
    stateExcitation ((amplitudeDamping p hp0 hp1).applyState rho) =
      (1 - p) * stateExcitation rho := by
  unfold stateExcitation
  rw [amplitudeDamping_applyState_matrix]
  simp [qubit_diagonal_one]

/-- Every qubit average state is bounded by the manuscript's scalar
information curve at its excitation probability. -/
theorem amplitudeDampingStateInformation_le_scalarInformation
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rho : State Qubit) :
    amplitudeDampingStateInformation p hp0 hp1 rho ≤
      amplitudeDampingScalarInformation p (stateExcitation rho) := by
  have hS := qubit_vonNeumann_le_binaryEntropy_excitation
    ((amplitudeDamping p hp0 hp1).applyState rho)
  rw [amplitudeDamping_output_excitation] at hS
  unfold amplitudeDampingStateInformation amplitudeDampingScalarInformation
  linarith

/-- Classical probabilities `(1-q,q)` on the computational qubit basis. -/
def diagonalQubitProb (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (i : Qubit) : ℝ≥0 :=
  if i = 0 then ⟨1 - q, sub_nonneg.mpr hq1⟩ else ⟨q, hq0⟩

theorem diagonalQubitProb_sum
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∑ i, diagonalQubitProb q hq0 hq1 i = 1 := by
  rw [Fin.sum_univ_two]
  ext
  simp [diagonalQubitProb]
  change (1 - q : ℝ) + q = 1
  ring

/-- The diagonal qubit state with excitation probability `q`. -/
def diagonalQubitState (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) : State Qubit :=
  Classical.diagonalState (diagonalQubitProb q hq0 hq1)
    (diagonalQubitProb_sum q hq0 hq1)

@[simp]
theorem diagonalQubitState_excitation
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    stateExcitation (diagonalQubitState q hq0 hq1) = q := by
  simp [stateExcitation, diagonalQubitState, diagonalQubitProb]
  rfl

@[simp]
theorem diagonalQubitState_coherence
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (diagonalQubitState q hq0 hq1).matrix 0 1 = 0 := by
  exact Classical.diagonalState_apply_ne _ _ (by decide)

theorem qubit_vonNeumann_eq_binaryEntropy_of_coherence_zero
    (rho : State Qubit) (hcoh : rho.matrix 0 1 = 0) :
    rho.vonNeumann = binaryEntropy (stateExcitation rho) := by
  rw [qubit_vonNeumann_eq_entanglementCurve_det,
    qubitDeterminant_eq_excitation_sub_coherence, hcoh]
  simp only [Complex.normSq_zero, sub_zero]
  exact entanglementCurve_two_sqrt_mul_one_sub_eq_binaryEntropy
    (stateExcitation_nonneg rho) (stateExcitation_le_one rho)

/-- Diagonal average states attain the scalar information curve. -/
theorem amplitudeDampingStateInformation_diagonalQubitState
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    amplitudeDampingStateInformation p hp0 hp1
        (diagonalQubitState q hq0 hq1) =
      amplitudeDampingScalarInformation p q := by
  let rho := diagonalQubitState q hq0 hq1
  have hcoh :
      ((amplitudeDamping p hp0 hp1).applyState rho).matrix 0 1 = 0 := by
    rw [amplitudeDamping_applyState_matrix]
    simp [rho, diagonalQubitState]
  have hS := qubit_vonNeumann_eq_binaryEntropy_of_coherence_zero
    ((amplitudeDamping p hp0 hp1).applyState rho) hcoh
  rw [amplitudeDamping_output_excitation, diagonalQubitState_excitation] at hS
  unfold amplitudeDampingStateInformation amplitudeDampingScalarInformation
  rw [hS, diagonalQubitState_excitation]

/-- Values of the scalar one-variable amplitude-damping information curve on
the physical excitation interval. -/
def amplitudeDampingScalarInformationValues (p : ℝ) : Set ℝ :=
  {x | ∃ q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 ∧
    x = amplitudeDampingScalarInformation p q}

theorem amplitudeDampingScalarInformationValues_nonempty (p : ℝ) :
    (amplitudeDampingScalarInformationValues p).Nonempty := by
  exact ⟨amplitudeDampingScalarInformation p 0, 0, by simp,
    rfl⟩

theorem amplitudeDampingScalarInformationValues_bddAbove
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    BddAbove (amplitudeDampingScalarInformationValues p) := by
  rcases roofHolevoInformationValues_bddAbove
    (amplitudeDamping p hp0 hp1) with ⟨C, hC⟩
  refine ⟨C, ?_⟩
  intro x hx
  rcases hx with ⟨q, hq, rfl⟩
  let rho := diagonalQubitState q hq.1 hq.2
  exact hC ⟨rho, by
    rw [amplitudeDamping_fixedInputHolevo_eq_stateInformation,
      amplitudeDampingStateInformation_diagonalQubitState]⟩

/-- Exact scalar one-letter formula, expressed as a supremum on `0 ≤ q ≤ 1`.
The following compactness step can replace `sSup` by `max`. -/
theorem amplitudeDamping_holevoInformation_eq_scalarSup
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel.holevoInformation.{0, 0, 0} (amplitudeDamping p hp0 hp1) =
      sSup (amplitudeDampingScalarInformationValues p) := by
  rw [amplitudeDamping_holevoInformation_eq_stateSup]
  apply le_antisymm
  · apply csSup_le
    · let rho := diagonalQubitState 0 (by norm_num) (by norm_num)
      exact ⟨amplitudeDampingStateInformation p hp0 hp1 rho, rho, rfl⟩
    · intro x hx
      rcases hx with ⟨rho, rfl⟩
      have hle := amplitudeDampingStateInformation_le_scalarInformation
        p hp0 hp1 rho
      have hmem : amplitudeDampingScalarInformation p (stateExcitation rho) ∈
          amplitudeDampingScalarInformationValues p :=
        ⟨stateExcitation rho,
          ⟨stateExcitation_nonneg rho, stateExcitation_le_one rho⟩, rfl⟩
      exact hle.trans (le_csSup
        (amplitudeDampingScalarInformationValues_bddAbove p hp0 hp1) hmem)
  · apply csSup_le (amplitudeDampingScalarInformationValues_nonempty p)
    intro x hx
    rcases hx with ⟨q, hq, rfl⟩
    let rho := diagonalQubitState q hq.1 hq.2
    have hmem : amplitudeDampingStateInformation p hp0 hp1 rho ∈
        Set.range (amplitudeDampingStateInformation p hp0 hp1) := ⟨rho, rfl⟩
    have hbdd : BddAbove
        (Set.range (amplitudeDampingStateInformation p hp0 hp1)) := by
      rcases roofHolevoInformationValues_bddAbove
        (amplitudeDamping p hp0 hp1) with ⟨C, hC⟩
      refine ⟨C, ?_⟩
      intro y hy
      rcases hy with ⟨sigma, rfl⟩
      exact hC ⟨sigma,
        amplitudeDamping_fixedInputHolevo_eq_stateInformation
          p hp0 hp1 sigma⟩
    rw [← amplitudeDampingStateInformation_diagonalQubitState
      p hp0 hp1 q hq.1 hq.2]
    exact le_csSup hbdd hmem

theorem binaryEntropy_continuous : Continuous binaryEntropy := by
  have h : Continuous (fun q : ℝ => Real.binEntropy q / Real.log 2) :=
    Real.binEntropy_continuous.div_const _
  apply h.congr
  intro q
  exact (binaryEntropy_eq_binEntropy_div_log_two q).symm

theorem dampingEntropyCurve_continuous (p : ℝ) :
    Continuous (dampingEntropyCurve p) := by
  unfold dampingEntropyCurve
  exact entanglementCurve_continuous.comp
    (continuous_const.mul continuous_id)

theorem amplitudeDampingScalarInformation_continuous (p : ℝ) :
    Continuous (amplitudeDampingScalarInformation p) := by
  unfold amplitudeDampingScalarInformation
  exact (binaryEntropy_continuous.comp
    (continuous_const.mul continuous_id)).sub
      (dampingEntropyCurve_continuous p)

/-- The scalar supremum is attained, yielding the manuscript's literal
`max_{0 ≤ q ≤ 1}` capacity formula. -/
theorem exists_amplitudeDamping_scalarInformation_maximizer
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 ∧
      Channel.holevoInformation.{0, 0, 0} (amplitudeDamping p hp0 hp1) =
        amplitudeDampingScalarInformation p q := by
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    (amplitudeDampingScalarInformation_continuous p).continuousOn
  refine ⟨q, hq, ?_⟩
  rw [amplitudeDamping_holevoInformation_eq_scalarSup p hp0 hp1]
  apply le_antisymm
  · apply csSup_le (amplitudeDampingScalarInformationValues_nonempty p)
    intro x hx
    rcases hx with ⟨r, hr, rfl⟩
    exact hmax hr
  · exact le_csSup
      (amplitudeDampingScalarInformationValues_bddAbove p hp0 hp1)
      ⟨q, hq, rfl⟩

end

end AmplitudeDamping
