import AmplitudeDamping.PureAuxiliaryOutput
import AmplitudeDamping.EqualExcitation

/-!
# From the pure auxiliary bound to convex-roof terms
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder NNReal

namespace AmplitudeDamping

open QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A normalized representative of the excited branch.  At zero excited
weight, the normalized ground branch is used as an irrelevant placeholder. -/
def normalizedExcitedBranch (psi : PureVector (Prod Qubit a)) : PureVector a :=
  if hq : 0 < pureAuxiliaryExcitation psi then
    PureVector.normalize (pureExcitedBranch psi) (by
      rw [pureExcitedBranch_rankOne_trace_re]
      exact hq)
  else
    PureVector.normalize (pureGroundBranch psi) (by
      rw [pureGroundBranch_rankOne_trace_re]
      have hq0 := pureAuxiliaryExcitation_nonneg psi
      have hqz : pureAuxiliaryExcitation psi = 0 :=
        le_antisymm (le_of_not_gt hq) hq0
      linarith)

/-- A normalized representative of the ground branch.  At zero ground
weight, the normalized excited branch is used as an irrelevant placeholder. -/
def normalizedGroundBranch (psi : PureVector (Prod Qubit a)) : PureVector a :=
  if hg : 0 < 1 - pureAuxiliaryExcitation psi then
    PureVector.normalize (pureGroundBranch psi) (by
      rw [pureGroundBranch_rankOne_trace_re]
      exact hg)
  else
    PureVector.normalize (pureExcitedBranch psi) (by
      rw [pureExcitedBranch_rankOne_trace_re]
      have hq1 := pureAuxiliaryExcitation_le_one psi
      have hq : pureAuxiliaryExcitation psi = 1 := by
        have : 1 - pureAuxiliaryExcitation psi = 0 :=
          le_antisymm (le_of_not_gt hg) (sub_nonneg.mpr hq1)
        linarith
      linarith)

/-- The two normalized qubit branches, weighted by their squared norms. -/
def pureAuxiliaryBranchDecomposition
    (psi : PureVector (Prod Qubit a)) : PureDecomposition a where
  card := 2
  probs := ![
    ⟨pureAuxiliaryExcitation psi, pureAuxiliaryExcitation_nonneg psi⟩,
    ⟨1 - pureAuxiliaryExcitation psi,
      sub_nonneg.mpr (pureAuxiliaryExcitation_le_one psi)⟩]
  weights_sum := by
    apply NNReal.eq
    rw [Fin.sum_univ_two]
    change pureAuxiliaryExcitation psi +
      (1 - pureAuxiliaryExcitation psi) = 1
    ring
  vectors := ![normalizedExcitedBranch psi, normalizedGroundBranch psi]

omit [DecidableEq a] in
private theorem branch_eq_zero_of_normSq_sum_eq_zero
    (v : a → ℂ) (h : (∑ x, Complex.normSq (v x)) = 0) : v = 0 := by
  funext x
  have hall : (fun i => Complex.normSq (v i)) = 0 :=
    (Fintype.sum_eq_zero_iff_of_nonneg
      (fun i => Complex.normSq_nonneg (v i))).mp h
  have hx : Complex.normSq (v x) = 0 := congrFun hall x
  exact Complex.normSq_eq_zero.mp hx

/-- The branch decomposition averages to the auxiliary marginal. -/
theorem pureAuxiliaryBranchDecomposition_averageState
    (psi : PureVector (Prod Qubit a)) :
    (pureAuxiliaryBranchDecomposition psi).averageState =
      psi.state.marginalB := by
  let q := pureAuxiliaryExcitation psi
  have hq0 : 0 ≤ q := pureAuxiliaryExcitation_nonneg psi
  have hq1 : q ≤ 1 := pureAuxiliaryExcitation_le_one psi
  apply State.ext
  rw [PureDecomposition.averageState, Ensemble.averageState_matrix]
  change
    (∑ i : Fin 2,
      (((![⟨q, hq0⟩,
          ⟨1 - q, sub_nonneg.mpr hq1⟩] i : ℝ≥0) : ℝ) : ℂ) •
        (![normalizedExcitedBranch psi,
          normalizedGroundBranch psi] i).state.matrix) =
      psi.state.marginalB.matrix
  rw [Fin.sum_univ_two]
  change
    ((q : ℂ) • (normalizedExcitedBranch psi).state.matrix) +
      (((1 - q : ℝ) : ℂ) • (normalizedGroundBranch psi).state.matrix) =
        psi.state.marginalB.matrix
  rw [pure_marginalB_matrix_eq_branch_rankOne_sum]
  by_cases hqz : q = 0
  · have hu0 : pureExcitedBranch psi = 0 := by
      apply branch_eq_zero_of_normSq_sum_eq_zero
      exact hqz
    have hgpos : 0 < 1 - q := by linarith
    rw [hqz]
    simp only [Complex.ofReal_zero, zero_smul, sub_zero, Complex.ofReal_one,
      one_smul, zero_add]
    rw [show normalizedGroundBranch psi =
        PureVector.normalize (pureGroundBranch psi) (by
          rw [pureGroundBranch_rankOne_trace_re]
          simpa [q, hqz]) by
      simp [normalizedGroundBranch, q, hqz]]
    rw [PureVector.normalize_state_matrix,
      pureGroundBranch_rankOne_trace_re]
    simp [q, hqz, hu0]
    ext x y
    simp [rankOneMatrix_apply]
  · by_cases hgz : 1 - q = 0
    · have hv0 : pureGroundBranch psi = 0 := by
        apply branch_eq_zero_of_normSq_sum_eq_zero
        rw [pureGroundBranch_normSq_sum]
        simpa [q] using hgz
      have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
      have hqeq : q = 1 := by linarith
      rw [hqeq]
      simp only [Complex.ofReal_one, one_smul, sub_self, Complex.ofReal_zero,
        zero_smul, add_zero]
      rw [show normalizedExcitedBranch psi =
          PureVector.normalize (pureExcitedBranch psi) (by
            rw [pureExcitedBranch_rankOne_trace_re]
            simpa [q, hqeq]) by
        simp [normalizedExcitedBranch, q, hqeq]]
      rw [PureVector.normalize_state_matrix,
        pureExcitedBranch_rankOne_trace_re]
      simp [q, hqeq, hv0]
      ext x y
      simp [rankOneMatrix_apply]
    · have hqpos : 0 < q := lt_of_le_of_ne hq0 (Ne.symm hqz)
      have hgpos : 0 < 1 - q :=
        lt_of_le_of_ne (sub_nonneg.mpr hq1) (Ne.symm hgz)
      rw [show normalizedExcitedBranch psi =
          PureVector.normalize (pureExcitedBranch psi) (by
            rw [pureExcitedBranch_rankOne_trace_re]
            exact hqpos) by
        simp [normalizedExcitedBranch, q, hqpos]]
      rw [show normalizedGroundBranch psi =
          PureVector.normalize (pureGroundBranch psi) (by
            rw [pureGroundBranch_rankOne_trace_re]
            exact hgpos) by
        simp [normalizedGroundBranch, q, hgpos]]
      rw [PureVector.normalize_state_matrix,
        PureVector.normalize_state_matrix]
      rw [pureExcitedBranch_rankOne_trace_re,
        pureGroundBranch_rankOne_trace_re]
      have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hqpos.ne'
      have hgC : (1 - (q : ℂ)) ≠ 0 := by exact_mod_cast hgpos.ne'
      ext x y
      simp [Matrix.smul_apply, rankOneMatrix_apply]
      rw [show pureAuxiliaryExcitation psi = q by rfl]
      field_simp [hqC, hgC]

/-- The auxiliary output cost of the branch decomposition is precisely the
sum of the two normalized Gram entropy terms. -/
theorem pureAuxiliary_branchDecomposition
    (Phi : Channel a b) (psi : PureVector (Prod Qubit a)) :
    (pureAuxiliaryBranchDecomposition psi).averageState =
        psi.state.marginalB ∧
      (pureAuxiliaryBranchDecomposition psi).outputCost Phi =
        normalizedGramEntropy (pureAuxiliaryExcitation psi)
            (Phi.stinespringCoefficientMatrix (pureExcitedBranch psi)) +
          normalizedGramEntropy (1 - pureAuxiliaryExcitation psi)
            (Phi.stinespringCoefficientMatrix (pureGroundBranch psi)) := by
  constructor
  · exact pureAuxiliaryBranchDecomposition_averageState psi
  · let q := pureAuxiliaryExcitation psi
    have hq0 : 0 ≤ q := pureAuxiliaryExcitation_nonneg psi
    have hq1 : q ≤ 1 := pureAuxiliaryExcitation_le_one psi
    unfold PureDecomposition.outputCost outputEntropyCost
    change
      (∑ i : Fin 2,
        ((![(⟨q, hq0⟩ : ℝ≥0),
            (⟨1 - q, sub_nonneg.mpr hq1⟩ : ℝ≥0)] i : ℝ≥0) : ℝ) *
          (Phi.applyState
            (![normalizedExcitedBranch psi,
              normalizedGroundBranch psi] i).state).vonNeumann) = _
    rw [Fin.sum_univ_two]
    change
      q * (Phi.applyState (normalizedExcitedBranch psi).state).vonNeumann +
        (1 - q) *
          (Phi.applyState (normalizedGroundBranch psi).state).vonNeumann = _
    by_cases hqz : q = 0
    · have hgpos : 0 < ∑ x, Complex.normSq (pureGroundBranch psi x) := by
        rw [pureGroundBranch_normSq_sum]
        simpa [q, hqz]
      have hG :=
        Phi.normalizedGramEntropy_stinespringCoefficientMatrix_of_pos
          (pureGroundBranch psi) hgpos
      have hG' :
          normalizedGramEntropy (1 - q)
              (Phi.stinespringCoefficientMatrix (pureGroundBranch psi)) =
            (1 - q) *
              (Phi.applyState
                (PureVector.normalize (pureGroundBranch psi) (by
                  rw [pureGroundBranch_rankOne_trace_re]
                  simpa [q, hqz])).state).vonNeumann := by
        simpa [q, pureGroundBranch_normSq_sum] using hG
      have hnG : normalizedGroundBranch psi =
          PureVector.normalize (pureGroundBranch psi) (by
            rw [pureGroundBranch_rankOne_trace_re]
            simpa [q, hqz]) := by
        simp [normalizedGroundBranch, q, hqz]
      rw [hqz]
      simp only [zero_mul, sub_zero, one_mul,
        zero_add]
      rw [hnG]
      simpa [q, hqz] using hG'.symm
    · by_cases hgz : 1 - q = 0
      · have hqpos : 0 < ∑ x, Complex.normSq (pureExcitedBranch psi x) := by
          change 0 < q
          exact lt_of_le_of_ne hq0 (Ne.symm hqz)
        have hE :=
          Phi.normalizedGramEntropy_stinespringCoefficientMatrix_of_pos
            (pureExcitedBranch psi) hqpos
        have hqeq : q = 1 := by linarith
        have hE' :
            normalizedGramEntropy q
                (Phi.stinespringCoefficientMatrix (pureExcitedBranch psi)) =
              q *
                (Phi.applyState
                  (PureVector.normalize (pureExcitedBranch psi) (by
                    rw [pureExcitedBranch_rankOne_trace_re]
                    simpa [q, hqeq])).state).vonNeumann := by
          simpa [q] using hE
        have hnE : normalizedExcitedBranch psi =
            PureVector.normalize (pureExcitedBranch psi) (by
              rw [pureExcitedBranch_rankOne_trace_re]
              simpa [q, hqeq]) := by
          simp [normalizedExcitedBranch, q, hqeq]
        rw [hqeq]
        simp only [one_mul, sub_self, zero_mul,
          add_zero]
        rw [hnE]
        simpa [q, hqeq] using hE'.symm
      · have hqpos : 0 < ∑ x, Complex.normSq (pureExcitedBranch psi x) := by
          change 0 < q
          exact lt_of_le_of_ne hq0 (Ne.symm hqz)
        have hgpos : 0 < ∑ x, Complex.normSq (pureGroundBranch psi x) := by
          rw [pureGroundBranch_normSq_sum]
          exact lt_of_le_of_ne (sub_nonneg.mpr hq1) (Ne.symm hgz)
        have hE :=
          Phi.normalizedGramEntropy_stinespringCoefficientMatrix_of_pos
            (pureExcitedBranch psi) hqpos
        have hG :=
          Phi.normalizedGramEntropy_stinespringCoefficientMatrix_of_pos
            (pureGroundBranch psi) hgpos
        have hqpos' : 0 < q := by simpa using hqpos
        have hgpos' : 0 < 1 - q := by
          change 0 < 1 - pureAuxiliaryExcitation psi
          rw [← pureGroundBranch_normSq_sum]
          exact hgpos
        have hE' :
            normalizedGramEntropy q
                (Phi.stinespringCoefficientMatrix (pureExcitedBranch psi)) =
              q *
                (Phi.applyState
                  (PureVector.normalize (pureExcitedBranch psi) (by
                    rw [pureExcitedBranch_rankOne_trace_re]
                    exact hqpos')).state).vonNeumann := by
          simpa [q] using hE
        have hG' :
            normalizedGramEntropy (1 - q)
                (Phi.stinespringCoefficientMatrix (pureGroundBranch psi)) =
              (1 - q) *
                (Phi.applyState
                  (PureVector.normalize (pureGroundBranch psi) (by
                    rw [pureGroundBranch_rankOne_trace_re]
                    exact hgpos')).state).vonNeumann := by
          simpa [q, pureGroundBranch_normSq_sum] using hG
        have hnE : normalizedExcitedBranch psi =
            PureVector.normalize (pureExcitedBranch psi) (by
              rw [pureExcitedBranch_rankOne_trace_re]
              exact hqpos') := by
          simp [normalizedExcitedBranch, q, hqpos']
        have hnG : normalizedGroundBranch psi =
            PureVector.normalize (pureGroundBranch psi) (by
              rw [pureGroundBranch_rankOne_trace_re]
              exact hgpos') := by
          simp [normalizedGroundBranch, q, hgpos']
        rw [hnE, hnG]
        rw [← hE', ← hG']

/-- The pure-input strong-superadditivity inequality in convex-roof form. -/
theorem pureAuxiliary_outputEntropy_ge_roofs
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Phi : Channel a b) (psi : PureVector (Prod Qubit a)) :
    (((amplitudeDamping p hp0 hp1).prod Phi).applyState psi.state).vonNeumann ≥
      outputEntropyRoof (amplitudeDamping p hp0 hp1) psi.state.marginalA +
        outputEntropyRoof Phi psi.state.marginalB := by
  have htri := pureAuxiliary_productOutput_entropy_lower_bound
    p hp0 hp1 Phi psi
  obtain ⟨havg, hcost⟩ := pureAuxiliary_branchDecomposition Phi psi
  have hright := outputEntropyRoof_le_outputCost Phi
    (pureAuxiliaryBranchDecomposition psi)
  rw [havg, hcost] at hright
  have hleft := outputEntropyRoof_eq_dampingEntropyCurve
    p hp0 hp1 psi.state.marginalA
  rw [← pureAuxiliaryExcitation_eq_marginal] at hleft
  linarith

end

end AmplitudeDamping
