import AmplitudeDamping.ConcurrenceRoof
import AmplitudeDamping.QubitLocalFilter

/-! # Local filtering of the concurrence convex roof -/
open scoped BigOperators NNReal ComplexOrder MatrixOrder Matrix Kronecker
namespace AmplitudeDamping
open QIT
noncomputable section
set_option maxHeartbeats 1000000

/-- A raw rank-one amplitude family representing a normalized state can be
normalized into a finite pure ensemble without changing its homogeneous
concurrence cost. -/
theorem exists_pureDecomposition_of_rankOne_family_with
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : State (Qubit × Qubit)) (v : ι → Qubit × Qubit → ℂ)
    (hsum : ∑ i, rankOneMatrix (v i) = ρ.matrix)
    (P : PureVector (Qubit × Qubit) → Prop)
    (hP : ∀ i (hp : 0 < (rankOneMatrix (v i)).trace.re),
      P (PureVector.normalize (v i) hp)) :
    ∃ E : PureDecomposition (Qubit × Qubit), E.averageState = ρ ∧
      E.concurrenceCost = (∑ i, 2 * ‖(Matrix.of (fun j k => v i (j,k))).det‖) ∧
      ∀ i, 0 < (E.probs i : ℝ) → P (E.vectors i) := by
  classical
  let w : ι → ℝ := fun i => (rankOneMatrix (v i)).trace.re
  have hw : ∀ i, 0 ≤ w i := fun i =>
    (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos (v i))).1
  have hws : ∑ i, w i = 1 := by
    have ht := congrArg (fun X : CMatrix (Qubit × Qubit) => X.trace.re) hsum
    simpa [w, Matrix.trace_sum, ρ.trace_re_eq_one] using ht
  let q : ι → PureVector (Qubit × Qubit) := fun i =>
    if h : 0 < w i then PureVector.normalize (v i) h
    else PureVector.maximallyEntangled (Equiv.refl Qubit)
  have hvzero (i : ι) (hi : ¬ 0 < w i) : v i = 0 := by
    have hz : w i = 0 := le_antisymm (not_lt.mp hi) (hw i)
    have hm : rankOneMatrix (v i) = 0 := by
      apply (Matrix.PosSemidef.trace_eq_zero_iff (rankOneMatrix_pos (v i))).mp
      apply Complex.ext
      · exact hz
      · exact (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos (v i))).2.symm
    funext x
    have hh := congrFun (congrFun hm x) x
    change v i x * star (v i x) = 0 at hh
    exact (mul_eq_zero.mp hh).elim id (fun h => star_eq_zero.mp h)
  have hweight (i : ι) : (w i : ℂ) • (q i).state.matrix = rankOneMatrix (v i) := by
    by_cases hi : 0 < w i
    · simp only [q, dif_pos hi, PureVector.normalize_state_matrix]
      rw [smul_smul]
      have hc : (w i : ℂ) * ((w i)⁻¹ : ℝ) = 1 := by
        exact_mod_cast mul_inv_cancel₀ hi.ne'
      change ((w i : ℂ) * ((w i)⁻¹ : ℝ)) • rankOneMatrix (v i) = _
      rw [hc, one_smul]
    · have hz : w i = 0 := le_antisymm (not_lt.mp hi) (hw i)
      rw [hz, Complex.ofReal_zero, zero_smul, hvzero i hi]
      ext x y
      simp [rankOneMatrix_apply]
  let E := PureDecomposition.ofFinite
    (fun i => (⟨w i, hw i⟩ : ℝ≥0))
    (by apply NNReal.eq; simpa only [NNReal.coe_sum, NNReal.coe_mk, NNReal.coe_one] using hws) q
  refine ⟨E, ?_, ?_, ?_⟩
  · apply State.ext
    change (∑ k : Fin (Fintype.card ι),
      ((⟨w ((Fintype.equivFin ι).symm k), hw _⟩ : ℝ≥0) : ℂ) •
      (q ((Fintype.equivFin ι).symm k)).state.matrix) = ρ.matrix
    calc
      _ = ∑ i, (w i : ℂ) • (q i).state.matrix :=
        Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ (fun _ => rfl)
      _ = _ := by simp_rw [hweight]; exact hsum
  · change (∑ k : Fin (Fintype.card ι),
      w ((Fintype.equivFin ι).symm k) * pureConcurrence (q ((Fintype.equivFin ι).symm k))) = _
    rw [Fintype.sum_equiv (Fintype.equivFin ι).symm _
      (fun i => w i * pureConcurrence (q i)) (fun _ => rfl)]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : 0 < w i
    · simp only [q, dif_pos hi, pureConcurrence]
      exact twoQubitAmplitudeMatrix_normalize_weighted_concurrence (v i) hi
    · have hz : w i = 0 := le_antisymm (not_lt.mp hi) (hw i)
      rw [hz, zero_mul, hvzero i hi]
      simp [Matrix.det_fin_two]

  · intro k hk
    change 0 < w ((Fintype.equivFin ι).symm k) at hk
    change P (q ((Fintype.equivFin ι).symm k))
    simp only [q, dif_pos hk]
    exact hP _ hk

/-- Normalizing a raw family preserves its state and homogeneous cost. -/
theorem exists_pureDecomposition_of_rankOne_family
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : State (Qubit × Qubit)) (v : ι → Qubit × Qubit → ℂ)
    (hsum : ∑ i, rankOneMatrix (v i) = ρ.matrix) :
    ∃ E : PureDecomposition (Qubit × Qubit), E.averageState = ρ ∧
      E.concurrenceCost = ∑ i, 2 * ‖(Matrix.of (fun j k => v i (j,k))).det‖ := by
  obtain ⟨E, hE, hc, _⟩ := exists_pureDecomposition_of_rankOne_family_with
    ρ v hsum (fun _ => True) (fun _ _ => trivial)
  exact ⟨E, hE, hc⟩

/-- A homogeneous flatness equation on raw amplitudes becomes constant pure
concurrence on every positive-weight normalized branch. -/
theorem exists_flat_pureDecomposition_of_rankOne_family
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : State (Qubit × Qubit)) (v : ι → Qubit × Qubit → ℂ)
    (hsum : ∑ i, rankOneMatrix (v i) = ρ.matrix) (c : ℝ)
    (hflat : ∀ i, 2 * ‖(Matrix.of (fun j k => v i (j,k))).det‖ =
      (rankOneMatrix (v i)).trace.re * c) :
    ∃ E : PureDecomposition (Qubit × Qubit), E.averageState = ρ ∧
      ∀ i, 0 < (E.probs i : ℝ) → pureConcurrence (E.vectors i) = c := by
  obtain ⟨E, hE, _, hf⟩ := exists_pureDecomposition_of_rankOne_family_with
    ρ v hsum (fun ψ => pureConcurrence ψ = c) (by
      intro i hp
      have h := twoQubitAmplitudeMatrix_normalize_weighted_concurrence (v i) hp
      rw [hflat i] at h
      exact (mul_left_cancel₀ hp.ne' h))
  exact ⟨E, hE, hf⟩

/-- Filtering a finite pure ensemble transports its homogeneous concurrence
cost exactly whenever the filtered average is already normalized. -/
theorem exists_pureDecomposition_localFilter
    (A : Matrix Qubit Qubit ℂ) (E : PureDecomposition (Qubit × Qubit))
    (σ : State (Qubit × Qubit))
    (hσ : σ.matrix = (A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) * E.averageState.matrix *
      (A ⊗ₖ (1 : Matrix Qubit Qubit ℂ))ᴴ) :
    ∃ F : PureDecomposition (Qubit × Qubit), F.averageState = σ ∧
      F.concurrenceCost = ‖A.det‖ * E.concurrenceCost := by
  let K := A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)
  let w : Fin E.card → ℝ := fun i => (E.probs i : ℝ) * qubitLocalFilterWeight A (E.vectors i)
  have hw (i : Fin E.card) : 0 ≤ w i :=
    mul_nonneg (NNReal.coe_nonneg _) (qubitLocalFilterWeight_nonneg A _)
  have hm : ∑ i, (w i : ℂ) • (qubitLocalFilterVector A (E.vectors i)).state.matrix =
      σ.matrix := by
    calc
      _ = ∑ i, (E.probs i : ℂ) • (K * (E.vectors i).state.matrix * Kᴴ) := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show (w i : ℂ) = (E.probs i : ℂ) *
          (qubitLocalFilterWeight A (E.vectors i) : ℂ) by simp [w]]
        rw [← smul_smul, qubitLocalFilterVector_weighted_matrix]
      _ = K * E.averageState.matrix * Kᴴ := by
        change _ = K * (∑ i, (E.probs i : ℂ) • (E.vectors i).state.matrix) * Kᴴ
        simp only [Matrix.mul_sum, Matrix.sum_mul, Matrix.mul_smul, Matrix.smul_mul]
      _ = σ.matrix := hσ.symm
  have hws : ∑ i, w i = 1 := by
    have h := congrArg (fun X : CMatrix (Qubit × Qubit) => X.trace.re) hm
    simpa only [Matrix.trace_sum, Matrix.trace_smul, State.trace_eq_one,
      smul_eq_mul, mul_one, ← Complex.ofReal_sum, Complex.ofReal_re, Complex.one_re] using h
  let F : PureDecomposition (Qubit × Qubit) :=
    ⟨E.card, fun i => ⟨w i, hw i⟩,
      by apply NNReal.eq; simpa only [NNReal.coe_sum, NNReal.coe_mk, NNReal.coe_one] using hws,
      fun i => qubitLocalFilterVector A (E.vectors i)⟩
  refine ⟨F, State.ext hm, ?_⟩
  change (∑ i, w i * pureConcurrence (qubitLocalFilterVector A (E.vectors i))) = _
  rw [PureDecomposition.concurrenceCost, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  dsimp [w, pureConcurrence]
  rw [mul_assoc, qubitLocalFilterVector_weighted_concurrence]
  ring

/-- Concurrence is bounded above by the determinant-scaled input concurrence
under any local filter whose output is normalized. -/
theorem concurrence_localFilter_le (A : Matrix Qubit Qubit ℂ)
    (ρ σ : State (Qubit × Qubit))
    (hσ : σ.matrix = (A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) * ρ.matrix *
      (A ⊗ₖ (1 : Matrix Qubit Qubit ℂ))ᴴ) :
    concurrence σ ≤ ‖A.det‖ * concurrence ρ := by
  have hcost (E : PureDecomposition (Qubit × Qubit)) (hE : E.averageState = ρ) :
      concurrence σ ≤ ‖A.det‖ * E.concurrenceCost := by
    obtain ⟨F, hF, hc⟩ := exists_pureDecomposition_localFilter A E σ (by rwa [hE])
    rw [← hc, ← hF]
    exact concurrence_le_concurrenceCost F
  by_cases hd : ‖A.det‖ = 0
  · have h := hcost (spectralPureDecomposition ρ) (spectralPureDecomposition_averageState ρ)
    simpa [hd] using h
  · have hdpos : 0 < ‖A.det‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd)
    have hdiv : concurrence σ / ‖A.det‖ ≤ concurrence ρ := by
      apply le_csInf (pureConcurrenceValues_nonempty ρ)
      rintro x ⟨E, hE, rfl⟩
      exact (div_le_iff₀ hdpos).mpr (by simpa [mul_comm] using hcost E hE)
    exact (div_le_iff₀ hdpos).mp hdiv |>.trans_eq (mul_comm _ _)

/-- Exact homogeneous concurrence scaling for a normalized local filter,
including singular filters. -/
theorem concurrence_localFilter (A : Matrix Qubit Qubit ℂ)
    (ρ σ : State (Qubit × Qubit))
    (hσ : σ.matrix = (A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) * ρ.matrix *
      (A ⊗ₖ (1 : Matrix Qubit Qubit ℂ))ᴴ) :
    concurrence σ = ‖A.det‖ * concurrence ρ := by
  apply le_antisymm (concurrence_localFilter_le A ρ σ hσ)
  by_cases hd : A.det = 0
  · simpa [hd] using (concurrence_mem_Icc σ).1
  · have hi : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul A (isUnit_iff_ne_zero.mpr hd)
    let K := A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)
    let L := A⁻¹ ⊗ₖ (1 : Matrix Qubit Qubit ℂ)
    have hLK : L * K = 1 := by
      dsimp [L, K]
      rw [← Matrix.mul_kronecker_mul, hi, Matrix.one_mul, Matrix.one_kronecker_one]
    have hρ : ρ.matrix = L * σ.matrix * Lᴴ := by
      rw [hσ]
      change ρ.matrix = L * (K * ρ.matrix * Kᴴ) * Lᴴ
      calc
        _ = (L * K) * ρ.matrix * (L * K)ᴴ := by rw [hLK]; simp
        _ = _ := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
    have hb := concurrence_localFilter_le A⁻¹ σ ρ hρ
    rw [Matrix.det_nonsing_inv, Ring.inverse_eq_inv, norm_inv] at hb
    have hc := mul_le_mul_of_nonneg_left hb (norm_nonneg A.det)
    have hn : ‖A.det‖ ≠ 0 := norm_ne_zero_iff.mpr hd
    simpa [← mul_assoc, mul_inv_cancel₀ hn] using hc

/-- Concurrence factorization for every pure two-qubit input and qubit channel. -/
theorem concurrence_reference_channel (N : Channel Qubit Qubit)
    (ψ : PureVector (Qubit × Qubit)) :
    concurrence (((Channel.idChannel Qubit).prod N).applyState ψ.state) =
      pureConcurrence ψ * concurrence (channelChoiState N) := by
  rw [concurrence_localFilter (qubitReferenceFilter ψ) (channelChoiState N) _
    (qubitReferenceFilter_channelChoi N ψ), qubitReferenceFilter_det, norm_mul]
  norm_num [pureConcurrence]

end
end AmplitudeDamping
