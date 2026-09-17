import AmplitudeDamping.EntanglementFormation
import AmplitudeDamping.QubitEntropy
import AmplitudeDamping.ScalarCurve

/-!
# Concurrence of pure two-qubit states and the kernel-state lower bound

For a pure two-qubit state with amplitude matrix `M`, the entropy of the
first marginal equals `entanglementCurve (2 ‖det M‖)`: the concurrence of a
pure two-qubit state is twice the modulus of the amplitude determinant, and
its entanglement entropy is the curve evaluated there.

The second result is the lower-bound half of the manuscript's Appendix B
specialization: for a two-qubit state whose `|01⟩` diagonal entry vanishes,
every positive-weight pure component of every decomposition also vanishes
there, so the convex roof is bounded below by
`entanglementCurve (2 ‖⟨00|ρ|11⟩‖)` via Jensen's inequality for the convex
curve and the triangle inequality.  The matching upper bound is Wootters'
formula; it is threaded as an explicit hypothesis by the downstream modules.
-/

open scoped BigOperators NNReal ComplexOrder Matrix

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Bridge: `star` and `starRingEnd` agree on `ℂ`, so `Complex.mul_conj`
applies to `z * star z` after a definitional `show`. -/
private theorem mul_star_self_normSq (z : ℂ) :
    z * star z = ↑(Complex.normSq z) := by
  show z * starRingEnd ℂ z = _
  rw [Complex.mul_conj]

/-- Weighted triangle inequality for complex numbers. -/
theorem norm_weighted_sum_le {ι : Type _} [Fintype ι] (p : ι → ℝ≥0)
    (v : ι → ℂ) :
    ‖∑ i, ((p i : ℝ≥0) : ℂ) * v i‖ ≤ ∑ i, (p i : ℝ) * ‖v i‖ := by
  have h := norm_sum_le Finset.univ
    (fun i => ((p i : ℝ≥0) : ℂ) * v i)
  refine h.trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul]
  have h1 : ‖((p i : ℝ≥0) : ℂ)‖ = (p i : ℝ) := by
    show ‖((p i : ℝ) : ℂ)‖ = _
    rw [Complex.norm_of_nonneg (NNReal.coe_nonneg (p i))]
  rw [h1]

/-- Amplitude matrix of a pure two-qubit vector across the natural
bipartition: `M j k = ψ (j,k)`. -/
def twoQubitAmplitudeMatrix (psi : PureVector (Prod Qubit Qubit)) :
    Matrix Qubit Qubit ℂ :=
  Matrix.of fun j k => psi.amp (j, k)

theorem twoQubitAmplitudeMatrix_apply (psi : PureVector (Prod Qubit Qubit))
    (j k : Qubit) :
    twoQubitAmplitudeMatrix psi j k = psi.amp (j, k) :=
  rfl

/-- The determinant of a two-qubit amplitude matrix. -/
theorem twoQubitAmplitudeMatrix_det (psi : PureVector (Prod Qubit Qubit)) :
    (twoQubitAmplitudeMatrix psi).det =
      psi.amp (0, 0) * psi.amp (1, 1) -
        psi.amp (0, 1) * psi.amp (1, 0) := by
  have h : (twoQubitAmplitudeMatrix psi).det =
      twoQubitAmplitudeMatrix psi 0 0 * twoQubitAmplitudeMatrix psi 1 1 -
        twoQubitAmplitudeMatrix psi 0 1 * twoQubitAmplitudeMatrix psi 1 0 :=
    Matrix.det_fin_two _
  rw [h]
  simp only [twoQubitAmplitudeMatrix_apply]

/-- The first marginal of a pure two-qubit state is `M M†`. -/
theorem pure_marginalA_matrix (psi : PureVector (Prod Qubit Qubit)) :
    psi.state.marginalA.matrix =
      (twoQubitAmplitudeMatrix psi) * (twoQubitAmplitudeMatrix psi)ᴴ := by
  ext j j'
  simp only [State.marginalA_matrix, partialTraceB, Matrix.mul_apply,
    Matrix.conjTranspose_apply, twoQubitAmplitudeMatrix_apply,
    PureVector.state_matrix_apply]

/-- Determinant of the first marginal of a pure two-qubit state. -/
theorem pure_marginalA_det (psi : PureVector (Prod Qubit Qubit)) :
    qubitDeterminant psi.state.marginalA =
      Complex.normSq (twoQubitAmplitudeMatrix psi).det := by
  rw [qubitDeterminant, pure_marginalA_matrix, Matrix.det_mul,
    Matrix.det_conjTranspose]
  simp [Complex.mul_conj, Complex.ofReal_re]

/-- The determinant bound `2 ‖det M‖ ≤ 1` for a normalized amplitude matrix. -/
theorem two_norm_det_le_one (psi : PureVector (Prod Qubit Qubit)) :
    2 * ‖(twoQubitAmplitudeMatrix psi).det‖ ≤ 1 := by
  have hnn : ∀ k, 0 ≤ psi.state.marginalA.pos.isHermitian.eigenvalues k :=
    fun k => psi.state.marginalA.pos.eigenvalues_nonneg k
  have hprodle : qubitDeterminant psi.state.marginalA ≤ 1 / 4 := by
    rw [← qubit_eigenvalues_product psi.state.marginalA]
    have hsum := qubit_eigenvalues_sum psi.state.marginalA
    nlinarith [sq_nonneg
      (psi.state.marginalA.pos.isHermitian.eigenvalues 0 -
        psi.state.marginalA.pos.isHermitian.eigenvalues 1), hnn 0, hnn 1]
  have habsnn : 0 ≤ ‖(twoQubitAmplitudeMatrix psi).det‖ := norm_nonneg _
  have hsq : ‖(twoQubitAmplitudeMatrix psi).det‖ ^ 2 =
      qubitDeterminant psi.state.marginalA := by
    rw [← Complex.normSq_eq_norm_sq, pure_marginalA_det]
  nlinarith

/-- Entanglement of a pure two-qubit state: the curve at twice the amplitude
determinant modulus. -/
theorem pure_marginalA_vonNeumann (psi : PureVector (Prod Qubit Qubit)) :
    psi.state.marginalA.vonNeumann =
      entanglementCurve (2 * ‖(twoQubitAmplitudeMatrix psi).det‖) := by
  rw [qubit_vonNeumann_eq_entanglementCurve_det, pure_marginalA_det psi]
  congr 1

/-- Entry of the average state of a pure decomposition as a weighted sum. -/
theorem pureDecomposition_averageState_matrix_entry
    (E : PureDecomposition (Prod Qubit Qubit)) (x y : Prod Qubit Qubit) :
    E.averageState.matrix x y =
      ∑ i, ((E.probs i : ℝ≥0) : ℂ) * (E.vectors i).state.matrix x y := by
  rw [PureDecomposition.averageState, Ensemble.averageState_matrix,
    Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [NNReal.smul_def]
  rfl

/-- A vanishing `|01⟩` diagonal entry forces the same entry of every
positive-weight component to vanish. -/
theorem pureDecomposition_amp_zero_of_average_zero
    (E : PureDecomposition (Prod Qubit Qubit))
    (h01 : E.averageState.matrix (0, 1) (0, 1) = 0) (i : Fin E.card) :
    (E.probs i : ℝ) * ‖(E.vectors i).amp (0, 1)‖ = 0 := by
  have hentry : ∑ i, ((E.probs i : ℝ≥0) : ℂ) *
      ((E.vectors i).state.matrix (0, 1) (0, 1)) = 0 := by
    rw [← pureDecomposition_averageState_matrix_entry, h01]
  have hreal : ∑ i, (E.probs i : ℝ) *
      Complex.normSq ((E.vectors i).amp (0, 1)) = 0 := by
    have h := hentry
    simp only [PureVector.state_matrix_apply, mul_star_self_normSq,
      ← Complex.ofReal_mul, ← Complex.ofReal_sum] at h
    exact_mod_cast h
  have hnn : ∀ i, 0 ≤ (E.probs i : ℝ) *
      Complex.normSq ((E.vectors i).amp (0, 1)) :=
    fun i => mul_nonneg (NNReal.coe_nonneg _) (Complex.normSq_nonneg _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i _ => hnn i)).1 hreal i (Finset.mem_univ i)
  have hsq : ((E.probs i : ℝ) * ‖(E.vectors i).amp (0, 1)‖) ^ 2 = 0 := by
    have h1 : ((E.probs i : ℝ) * ‖(E.vectors i).amp (0, 1)‖) ^ 2 =
        (E.probs i : ℝ) *
          ((E.probs i : ℝ) *
            Complex.normSq ((E.vectors i).amp (0, 1))) := by
      rw [mul_pow, Complex.sq_norm]
      ring
    rw [h1, hterm, mul_zero]
  exact pow_eq_zero_iff two_ne_zero |>.mp hsq

/-- Kernel-state lower bound (Appendix B, direction `≥`): the entanglement of
formation of a two-qubit state with zero `|01⟩` population is at least the
curve at twice the `⟨00|ρ|11⟩` coherence. -/
theorem entanglementOfFormation_ge_entanglementCurve
    (rho : State (Prod Qubit Qubit))
    (h01 : rho.matrix (0, 1) (0, 1) = 0) :
    entanglementCurve (2 * ‖rho.matrix (0, 0) (1, 1)‖) ≤
      entanglementOfFormation rho := by
  apply le_csInf (pureEntanglementValues_nonempty rho)
  rintro x ⟨E, havg, rfl⟩
  set w : Fin E.card → ℝ := fun i => (E.probs i : ℝ) with hwdef
  set c : Fin E.card → ℝ :=
    fun i => 2 * ‖(twoQubitAmplitudeMatrix (E.vectors i)).det‖
    with hcdef
  set t : Fin E.card → ℝ :=
    fun i => ‖(E.vectors i).amp (0, 0) * (E.vectors i).amp (1, 1)‖
    with htdef
  have h01E : E.averageState.matrix (0, 1) (0, 1) = 0 := by
    rw [havg]; exact h01
  have hzero : ∀ i, w i * ‖(E.vectors i).amp (0, 1)‖ = 0 :=
    fun i => pureDecomposition_amp_zero_of_average_zero E h01E i
  -- per-branch determinant collapse
  have hdet : ∀ i, w i * c i = w i * (2 * t i) := by
    intro i
    by_cases hw : w i = 0
    · rw [hw, zero_mul, zero_mul]
    · have hamp01 : (E.vectors i).amp (0, 1) = 0 := by
        rcases mul_eq_zero.mp (hzero i) with h1 | h1
        · exact absurd h1 hw
        · exact norm_eq_zero.mp h1
      simp only [hcdef, htdef]
      rw [twoQubitAmplitudeMatrix_det, hamp01, zero_mul, sub_zero]
  -- the coherence as a weighted sum
  have hz : rho.matrix (0, 0) (1, 1) =
      ∑ i, ((E.probs i : ℝ≥0) : ℂ) * ((E.vectors i).amp (0, 0) *
        star ((E.vectors i).amp (1, 1))) := by
    rw [← havg, pureDecomposition_averageState_matrix_entry]
    exact Finset.sum_congr rfl fun i _ => rfl
  -- triangle inequality
  have htri : ‖rho.matrix (0, 0) (1, 1)‖ ≤ ∑ i, w i * t i := by
    have h1 := norm_weighted_sum_le (fun i => E.probs i)
      (fun i => (E.vectors i).amp (0, 0) * star ((E.vectors i).amp (1, 1)))
    rw [← hz] at h1
    refine h1.trans_eq (Finset.sum_congr rfl fun i _ => ?_)
    rw [norm_mul, norm_star, ← norm_mul]
  -- weights
  have hw_nn : ∀ i ∈ (Finset.univ : Finset (Fin E.card)), 0 ≤ w i := by
    intro i _
    exact NNReal.coe_nonneg _
  have hw_sum : ∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i = 1 := by
    have h := congrArg (fun z : ℝ≥0 => (z : ℝ)) E.weights_sum
    simpa [hwdef] using h
  have hc_mem : ∀ i ∈ (Finset.univ : Finset (Fin E.card)), c i ∈ Set.Icc (0 : ℝ) 1 :=
    fun i _ => ⟨by positivity, two_norm_det_le_one (E.vectors i)⟩
  have hjensen :=
    entanglementCurve_convexOn.map_sum_le hw_nn hw_sum hc_mem
  -- cost rewrite
  have hcost : E.entanglementCost =
      ∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i * entanglementCurve (c i) := by
    rw [PureDecomposition.entanglementCost]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [pure_marginalA_vonNeumann (E.vectors i)]
  -- the Jensen midpoint
  have hmid_le : ∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i * c i ≤ 1 := by
    calc ∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i * c i ≤
        ∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i * 1 :=
      Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (hc_mem i (Finset.mem_univ i)).2
          (hw_nn i (Finset.mem_univ i))
    _ = 1 := by simp [hw_sum]
  have hmid_ge : 2 * ‖rho.matrix (0, 0) (1, 1)‖ ≤
      ∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i * c i := by
    have hsplit : ∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i * c i =
        2 * ∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i * t i := by
      calc ∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i * c i =
          ∑ i ∈ (Finset.univ : Finset (Fin E.card)), 2 * (w i * t i) :=
          Finset.sum_congr rfl fun i _ => by
            rw [hdet i]; ring
      _ = 2 * ∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i * t i :=
          (Finset.mul_sum Finset.univ (fun i => w i * t i) 2).symm
    rw [hsplit]
    linarith [htri]
  have hmid_mem : (∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i * c i) ∈
      Set.Icc (0 : ℝ) 1 :=
    ⟨Finset.sum_nonneg fun i _ => mul_nonneg (hw_nn i (Finset.mem_univ i))
      (by positivity), hmid_le⟩
  have hz_mem : (2 * ‖rho.matrix (0, 0) (1, 1)‖) ∈
      Set.Icc (0 : ℝ) 1 :=
    ⟨by positivity, le_trans hmid_ge hmid_le⟩
  -- conclude
  rw [hcost]
  calc entanglementCurve (2 * ‖rho.matrix (0, 0) (1, 1)‖) ≤
      entanglementCurve
        (∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i * c i) :=
        entanglementCurve_monotoneOn hz_mem hmid_mem hmid_ge
    _ ≤ ∑ i ∈ (Finset.univ : Finset (Fin E.card)), w i * entanglementCurve (c i) := by
        simpa only [smul_eq_mul] using hjensen

end

end AmplitudeDamping
