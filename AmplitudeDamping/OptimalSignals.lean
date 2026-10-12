import AmplitudeDamping.CapacityBridge
import QIT.Coding.Classical.HSWDirect

/-!
# Explicit optimal binary signals for amplitude damping

The signals have amplitudes `(sqrt (1-q), ± sqrt q)`, equal probabilities,
and diagonal average. Their output Holevo information is exactly the scalar
information curve, so every maximizer of that curve gives an optimal ensemble.
-/

namespace AmplitudeDamping

open QIT
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder NNReal

noncomputable section

/-- The two manuscript signals, indexed by `0` (plus) and `1` (minus). -/
def binarySignalVector (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (i : Fin 2) : PureVector Qubit where
  amp := ![(Real.sqrt (1 - q) : ℂ),
    if i = 0 then (Real.sqrt q : ℂ) else -(Real.sqrt q : ℂ)]
  trace_rankOne_eq_one := by
    have hs0 := Real.sq_sqrt (sub_nonneg.mpr hq1)
    have hs1 := Real.sq_sqrt hq0
    rw [rankOneMatrix_trace]
    fin_cases i <;>
      simp [dotProduct, Fin.sum_univ_two, Complex.mul_conj,
        Complex.normSq_ofReal] <;>
      norm_cast <;> nlinarith

@[simp]
theorem binarySignalVector_amp_zero
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (i : Fin 2) :
    (binarySignalVector q hq0 hq1 i).amp 0 = (Real.sqrt (1 - q) : ℂ) := rfl

@[simp]
theorem binarySignalVector_amp_one
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (i : Fin 2) :
    (binarySignalVector q hq0 hq1 i).amp 1 =
      if i = 0 then (Real.sqrt q : ℂ) else -(Real.sqrt q : ℂ) := rfl

@[simp]
theorem binarySignalVector_excitationProbability
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (i : Fin 2) :
    excitationProbability (binarySignalVector q hq0 hq1 i) = q := by
  fin_cases i <;>
    simp [excitationProbability, Complex.normSq_ofReal, ← pow_two,
      Real.sq_sqrt hq0]

/-- The equiprobable ensemble of the plus and minus pure signals. -/
def binarySignalEnsemble (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    Ensemble (Fin 2) Qubit where
  probs := fun _ => (1 / 2 : ℝ≥0)
  weights_sum := by norm_num [Fin.sum_univ_two]
  states := fun i => (binarySignalVector q hq0 hq1 i).state

@[simp]
theorem binarySignalEnsemble_probs
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (i : Fin 2) :
    (binarySignalEnsemble q hq0 hq1).probs i = (1 / 2 : ℝ≥0) := rfl

@[simp]
theorem binarySignalEnsemble_states
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (i : Fin 2) :
    (binarySignalEnsemble q hq0 hq1).states i =
      (binarySignalVector q hq0 hq1 i).state := rfl

/-- Averaging the opposite coherences leaves exactly `(1-q,q)` on the diagonal. -/
theorem binarySignalEnsemble_averageState
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (binarySignalEnsemble q hq0 hq1).averageState =
      diagonalQubitState q hq0 hq1 := by
  have hs0 : (Real.sqrt (1 - q) : ℂ) ^ 2 = ((1 - q : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hq1)
  have hs1 : (Real.sqrt q : ℂ) ^ 2 = (q : ℂ) := by
    exact_mod_cast Real.sq_sqrt hq0
  apply State.ext
  rw [Ensemble.averageState_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_two, binarySignalEnsemble,
      binarySignalVector, diagonalQubitState, Classical.diagonalState,
      diagonalQubitProb, Matrix.smul_apply, Matrix.sum_apply] <;>
    ring_nf <;> simp_all <;>
    norm_num [NNReal.smul_def, Complex.real_smul, NNReal.coe_mk]
  · change _ = ((1 - q : ℝ) : ℂ)
    push_cast
    ring
  · change _ = (q : ℂ)
    ring

/-- Both outputs have the fixed-excitation entropy `g_p(q)`. -/
theorem binarySignalEnsemble_output_entropy
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) (i : Fin 2) :
    ((amplitudeDamping p hp0 hp1).applyState
      ((binarySignalEnsemble q hq0 hq1).states i)).vonNeumann =
        dampingEntropyCurve p q := by
  rw [binarySignalEnsemble_states, amplitudeDamping_pure_output_entropy,
    binarySignalVector_excitationProbability]

/-- The output entropy cost is the common entropy of the two signals. -/
theorem binarySignalEnsemble_outputEntropyCost
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    outputEntropyCost (amplitudeDamping p hp0 hp1)
      (binarySignalEnsemble q hq0 hq1) = dampingEntropyCurve p q := by
  unfold outputEntropyCost
  simp_rw [binarySignalEnsemble_output_entropy]
  norm_num [Fin.sum_univ_two, binarySignalEnsemble]
  ring

/-- Exact Holevo information of the explicit binary ensemble. -/
theorem binarySignalEnsemble_holevoAfter
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ensembleHolevoAfter (amplitudeDamping p hp0 hp1)
      (binarySignalEnsemble q hq0 hq1) =
        amplitudeDampingScalarInformation p q := by
  rw [ensembleHolevoAfter_eq, binarySignalEnsemble_averageState,
    binarySignalEnsemble_outputEntropyCost]
  convert amplitudeDampingStateInformation_diagonalQubitState p hp0 hp1 q hq0 hq1
    using 1

/-- Any scalar maximizer makes the two explicit signals attain channel Holevo information. -/
theorem binarySignalEnsemble_optimal_of_isMaxOn
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmax : IsMaxOn (amplitudeDampingScalarInformation p) (Set.Icc 0 1) q) :
    ensembleHolevoAfter (amplitudeDamping p hp0 hp1)
      (binarySignalEnsemble q hq0 hq1) =
        Channel.holevoInformation.{0, 0, 0} (amplitudeDamping p hp0 hp1) := by
  rw [binarySignalEnsemble_holevoAfter, amplitudeDamping_holevoInformation_eq_scalarSup]
  apply le_antisymm
  · exact le_csSup (amplitudeDampingScalarInformationValues_bddAbove p hp0 hp1)
      ⟨q, ⟨hq0, hq1⟩, rfl⟩
  · apply csSup_le (amplitudeDampingScalarInformationValues_nonempty p)
    rintro x ⟨r, hr, rfl⟩
    exact hmax hr

/-- An optimal explicit binary ensemble exists for every physical damping parameter. -/
theorem exists_optimal_binarySignalEnsemble
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1),
      ensembleHolevoAfter (amplitudeDamping p hp0 hp1)
        (binarySignalEnsemble q hq0 hq1) =
          Channel.holevoInformation.{0, 0, 0} (amplitudeDamping p hp0 hp1) := by
  obtain ⟨q, hq, hopt⟩ := exists_amplitudeDamping_scalarInformation_maximizer p hp0 hp1
  exact ⟨q, hq.1, hq.2, (binarySignalEnsemble_holevoAfter p hp0 hp1 q hq.1 hq.2).trans
    hopt.symm⟩

/-- The existing HSW theorem gives operational achievability below this
ensemble's Holevo value. Its `IsAchievableClassicalRate` conclusion quantifies
over block encoders and collective POVMs; it does not retain the stronger
property that each encoder state is a product of these two signals. -/
theorem binarySignalEnsemble_rate_achievable
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (R : ℝ) (hR : R < amplitudeDampingScalarInformation p q) :
    Channel.IsAchievableClassicalRate.{0, 0, 0}
      (amplitudeDamping p hp0 hp1) R := by
  apply Channel.hsw_regularizedHolevoInformation_direct
  rw [amplitudeDamping_regularizedHolevoInformation_eq]
  have hle := ensembleHolevoAfter_le_holevoInformation
    (amplitudeDamping p hp0 hp1) (binarySignalEnsemble q hq0 hq1)
  rw [binarySignalEnsemble_holevoAfter] at hle
  exact lt_of_lt_of_le hR hle

/-- At a maximizing excitation every rate below classical capacity is
operationally achievable. Product-codeword membership is not asserted by this
interface; that requires strengthening the upstream coding-witness theorem. -/
theorem binarySignalEnsemble_optimal_rates_achievable
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmax : IsMaxOn (amplitudeDampingScalarInformation p) (Set.Icc 0 1) q)
    (R : ℝ) (hR : R < Channel.classicalCapacity.{0, 0, 0}
      (amplitudeDamping p hp0 hp1)) :
    Channel.IsAchievableClassicalRate.{0, 0, 0}
      (amplitudeDamping p hp0 hp1) R := by
  apply binarySignalEnsemble_rate_achievable p hp0 hp1 q hq0 hq1 R
  rw [amplitudeDamping_classicalCapacity_eq_holevoInformation,
    ← binarySignalEnsemble_optimal_of_isMaxOn p hp0 hp1 q hq0 hq1 hmax,
    binarySignalEnsemble_holevoAfter] at hR
  exact hR

/-- At full damping the scalar information vanishes for every input excitation. -/
@[simp]
theorem amplitudeDampingScalarInformation_one (q : ℝ) :
    amplitudeDampingScalarInformation 1 q = 0 := by
  simp [amplitudeDampingScalarInformation, dampingEntropyCurve, entanglementCurve,
    binaryEntropy_eq_binEntropy_div_log_two]

/-- The balanced binary ensemble carries one bit through the undamped channel. -/
@[simp]
theorem amplitudeDampingScalarInformation_zero_half :
    amplitudeDampingScalarInformation 0 (1 / 2) = 1 := by
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  simp [amplitudeDampingScalarInformation, dampingEntropyCurve, entanglementCurve,
    binaryEntropy_eq_binEntropy_div_log_two, Real.binEntropy_two_inv, hlog]

/-- Full damping has zero classical capacity. -/
theorem amplitudeDamping_classicalCapacity_one :
    Channel.classicalCapacity.{0, 0, 0}
      (amplitudeDamping 1 (by norm_num) (by norm_num)) = 0 := by
  obtain ⟨q, _, heq⟩ := amplitudeDamping_classicalCapacity_scalar_formula
    1 (by norm_num) (by norm_num)
  rw [heq, amplitudeDampingScalarInformation_one]

/-- The undamped qubit channel has classical capacity one bit. -/
theorem amplitudeDamping_classicalCapacity_zero :
    Channel.classicalCapacity.{0, 0, 0}
      (amplitudeDamping 0 (by norm_num) (by norm_num)) = 1 := by
  have hlog : Real.log (2 : ℝ) ≠ 0 := ne_of_gt (Real.log_pos (by norm_num))
  rw [amplitudeDamping_classicalCapacity_eq_holevoInformation]
  apply le_antisymm
  · unfold Channel.holevoInformation
    apply csSup_le (Channel.holevoInformationValues_nonempty _)
    intro r hr
    have h := Channel.mem_holevoInformationValues_le_log_card
      (amplitudeDamping 0 (by norm_num) (by norm_num)) hr
    simpa [Qubit, log2, hlog] using h
  · have h := ensembleHolevoAfter_le_holevoInformation
      (amplitudeDamping 0 (by norm_num) (by norm_num))
      (binarySignalEnsemble (1 / 2) (by norm_num) (by norm_num))
    rw [binarySignalEnsemble_holevoAfter, amplitudeDampingScalarInformation_zero_half] at h
    exact h

end

end AmplitudeDamping
