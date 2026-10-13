import AmplitudeDamping.ConcurrenceFilter
import AmplitudeDamping.FlatConcurrence
import AmplitudeDamping.ConcurrencePositive
import AmplitudeDamping.ConcurrenceFlattening

/-! # Flat optimal concurrence ensembles and the two-qubit formation formula -/
open scoped BigOperators NNReal ComplexOrder MatrixOrder Matrix
namespace AmplitudeDamping
open QIT
noncomputable section
set_option maxHeartbeats 1000000

/-- The square-root-weighted amplitudes of a pure ensemble. -/
def PureDecomposition.rawAmplitudes (E : PureDecomposition (Qubit × Qubit))
    (i : Fin E.card) : Qubit × Qubit → ℂ :=
  (Real.sqrt (E.probs i : ℝ) : ℂ) • (E.vectors i).amp

/-- A weighted pure state is the rank-one kernel of its raw amplitude. -/
theorem PureDecomposition.rawAmplitudes_rankOne
    (E : PureDecomposition (Qubit × Qubit)) (i : Fin E.card) :
    rankOneMatrix (E.rawAmplitudes i) = (E.probs i : ℂ) • (E.vectors i).state.matrix := by
  have hs : (Real.sqrt (E.probs i : ℝ) : ℂ) ^ 2 = (E.probs i : ℂ) := by
    exact_mod_cast Real.sq_sqrt (NNReal.coe_nonneg (E.probs i))
  ext x y
  simp only [rawAmplitudes, rankOneMatrix_apply, Pi.smul_apply, smul_eq_mul,
    star_mul, Complex.star_def, Complex.conj_ofReal,
    PureVector.state_matrix_apply, Matrix.smul_apply]
  linear_combination ((E.vectors i).amp x * starRingEnd ℂ ((E.vectors i).amp y)) * hs

/-- The raw amplitudes reconstruct the ensemble's average density matrix. -/
theorem PureDecomposition.rawAmplitudes_sum_rankOne
    (E : PureDecomposition (Qubit × Qubit)) :
    ∑ i, rankOneMatrix (E.rawAmplitudes i) = E.averageState.matrix := by
  simp_rw [E.rawAmplitudes_rankOne]
  rfl

/-- Square-root weighting makes concurrence homogeneous in the branch weight. -/
theorem PureDecomposition.rawAmplitudes_concurrence
    (E : PureDecomposition (Qubit × Qubit)) (i : Fin E.card) :
    ‖rawConcurrence (E.rawAmplitudes i)‖ =
      (E.probs i : ℝ) * pureConcurrence (E.vectors i) := by
  have hs : (Real.sqrt (E.probs i : ℝ) : ℂ) ^ 2 = (E.probs i : ℂ) := by
    exact_mod_cast Real.sq_sqrt (NNReal.coe_nonneg (E.probs i))
  have hraw : rawConcurrence (E.rawAmplitudes i) =
      (E.probs i : ℂ) * rawConcurrence (E.vectors i).amp := by
    simp only [rawConcurrence, rawAmplitudes, Pi.smul_apply, smul_eq_mul]
    linear_combination 2 * ((E.vectors i).amp (0,0) * (E.vectors i).amp (1,1) -
      (E.vectors i).amp (0,1) * (E.vectors i).amp (1,0)) * hs
  rw [hraw, norm_mul, norm_rawConcurrence]
  have hn : ‖(E.probs i : ℂ)‖ = (E.probs i : ℝ) :=
    Complex.norm_of_nonneg (NNReal.coe_nonneg _)
  rw [hn]
  rfl

/-- Ensemble concurrence agrees with homogeneous raw-family concurrence. -/
theorem PureDecomposition.rawAmplitudes_cost
    (E : PureDecomposition (Qubit × Qubit)) :
    rawConcurrenceCost E.rawAmplitudes = E.concurrenceCost := by
  unfold rawConcurrenceCost PureDecomposition.concurrenceCost
  exact Finset.sum_congr rfl fun i _ => E.rawAmplitudes_concurrence i

/-- Every raw amplitude representation bounds the concurrence convex roof. -/
theorem concurrence_le_rawConcurrenceCost {ι : Type*} [Fintype ι] [DecidableEq ι]
    (ρ : State (Qubit × Qubit)) (v : ι → Qubit × Qubit → ℂ)
    (hsum : ∑ i, rankOneMatrix (v i) = ρ.matrix) :
    concurrence ρ ≤ rawConcurrenceCost v := by
  obtain ⟨E, hE, hc⟩ := exists_pureDecomposition_of_rankOne_family ρ v hsum
  have h := concurrence_le_concurrenceCost E
  rw [hE, hc] at h
  simpa only [rawConcurrenceCost, norm_rawConcurrence] using h

/-- Compact attainment yields a finite raw amplitude minimizer. -/
theorem exists_raw_concurrence_minimizer (ρ : State (Qubit × Qubit)) :
    ∃ (n : ℕ) (v : Fin n → Qubit × Qubit → ℂ),
      (∑ i, rankOneMatrix (v i)) = ρ.matrix ∧
      rawConcurrenceCost v = concurrence ρ := by
  obtain ⟨E, hE, _, hc⟩ := exists_concurrence_minimizer ρ
  refine ⟨E.card, E.rawAmplitudes, ?_, ?_⟩
  · rw [E.rawAmplitudes_sum_rankOne, hE]
  · rw [E.rawAmplitudes_cost, hc]

/-- A zero-cost concurrence ensemble is already flat on its supported branches. -/
theorem PureDecomposition.flat_of_concurrenceCost_zero
    (E : PureDecomposition (Qubit × Qubit)) (hc : E.concurrenceCost = 0)
    (i : Fin E.card) (hi : 0 < (E.probs i : ℝ)) : pureConcurrence (E.vectors i) = 0 := by
  have hnonneg : ∀ i, 0 ≤ (E.probs i : ℝ) * pureConcurrence (E.vectors i) :=
    fun i => mul_nonneg (NNReal.coe_nonneg _) (pureConcurrence_mem_Icc _).1
  have h := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => hnonneg i)).mp hc
    i (Finset.mem_univ i)
  exact (mul_eq_zero.mp h).resolve_left hi.ne'

/-- Every two-qubit state has a concurrence-minimizing ensemble with the same
pure concurrence on every supported branch. -/
theorem exists_flat_concurrence_minimizer (ρ : State (Qubit × Qubit)) :
    ∃ E : PureDecomposition (Qubit × Qubit), E.averageState = ρ ∧
      ∀ i, 0 < (E.probs i : ℝ) →
        pureConcurrence (E.vectors i) = concurrence ρ := by
  classical
  by_cases hzero : concurrence ρ = 0
  · obtain ⟨E, hE, _, hc⟩ := exists_concurrence_minimizer ρ
    refine ⟨E, hE, ?_⟩
    intro i hi
    rw [hzero]
    exact E.flat_of_concurrenceCost_zero (hc.trans hzero) i hi
  · have hpos : 0 < concurrence ρ :=
      lt_of_le_of_ne (concurrence_mem_Icc ρ).1 (Ne.symm hzero)
    obtain ⟨n, v, hv, hc⟩ := exists_raw_concurrence_minimizer ρ
    obtain ⟨w, a, ha, hdiag, hsum, hcost⟩ :=
      exists_positive_rawConcurrence_family v (by rwa [hc])
    have hwρ : ∑ i, rankOneMatrix (w i) = ρ.matrix := hsum.trans hv
    have hwcost : rawConcurrenceCost w = concurrence ρ := hcost.trans hc
    have hmin (u : Fin n × Bool → Qubit × Qubit → ℂ)
        (hu : ∑ i, rankOneMatrix (u i) = ∑ i, rankOneMatrix (w i)) :
        rawConcurrenceCost w ≤ rawConcurrenceCost u := by
      rw [hwcost]
      exact concurrence_le_rawConcurrenceCost ρ u (hu.trans hwρ)
    have hreal := optimal_rawConcurrence_overlap_real w a ha hdiag hmin
    have ht : ∑ i, (rankOneMatrix (w i)).trace.re = 1 := by
      have h := congrArg (fun X : CMatrix (Qubit × Qubit) => X.trace.re) hwρ
      simpa only [Matrix.trace_sum, Complex.re_sum, State.trace_re_eq_one] using h
    have hq : (∑ i, (rawConcurrence (w i)).re) = concurrence ρ := by
      calc
        _ = rawConcurrenceCost w := by
          unfold rawConcurrenceCost
          apply Finset.sum_congr rfl
          intro i _
          rw [hdiag i, Complex.ofReal_re, Complex.norm_of_nonneg (ha i).le]
        _ = _ := hwcost
    obtain ⟨u, hu, hflat⟩ := exists_flat_raw_family w (concurrence ρ)
      (concurrence_mem_Icc ρ).1 hreal (by rw [ht, mul_one]; exact hq)
    exact exists_flat_pureDecomposition_of_rankOne_family ρ u (hu.trans hwρ)
      (concurrence ρ) hflat

/-- The two-qubit entanglement of formation is the entropy curve evaluated at
its independently defined concurrence convex roof. -/
theorem entanglementOfFormation_eq_entanglementCurve_concurrence
    (ρ : State (Qubit × Qubit)) :
    entanglementOfFormation ρ = entanglementCurve (concurrence ρ) := by
  obtain ⟨E, hE, hflat⟩ := exists_flat_concurrence_minimizer ρ
  exact entanglementOfFormation_eq_of_flat_concurrence ρ E hE hflat

end
end AmplitudeDamping
