import QIT.Information.Entropy.RelativeEntropyDPI
import QIT.Information.Entropy.EntropyTensorPower
import QIT.Measurements.Projective

/-! # The equality case of relative entropy with a faithful reference

Measure in an eigenbasis of the difference of the two states. Data processing
reduces equality to the strict scalar Gibbs inequality, and the measurement
retains the full difference in this basis.
-/
open scoped BigOperators ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT Matrix
noncomputable section
universe u

private theorem gibbs_gap_pos {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) (hne : p ≠ q) :
    0 < p * Real.log p - p * Real.log q - p + q := by
  by_cases hp0 : p = 0
  · simpa [hp0] using hq
  have hpp : 0 < p := lt_of_le_of_ne hp (Ne.symm hp0)
  have hr : q / p ≠ 1 := by
    intro h
    have := (div_eq_one_iff_eq hpp.ne').mp h
    exact hne this.symm
  have hlog := Real.log_lt_sub_one_of_pos (div_pos hq hpp) hr
  rw [Real.log_div hq.ne' hpp.ne'] at hlog
  have h := mul_lt_mul_of_pos_left hlog hpp
  have hc : p * (q / p - 1) = q - p := by field_simp
  rw [hc] at h
  nlinarith

private theorem gibbs_gap_nonneg {p q : ℝ} (hp : 0 ≤ p) (hq : 0 < q) :
    0 ≤ p * Real.log p - p * Real.log q - p + q := by
  by_cases h : p = q
  · simp [h]
  · exact (gibbs_gap_pos hp hq h).le

/-- Equality in the finite scalar Gibbs inequality with positive reference masses. -/
theorem probabilities_eq_of_kl_le_zero
    {a : Type u} [Fintype a] (p q : a → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hpsum : ∑ i, p i = 1) (hqsum : ∑ i, q i = 1)
    (hkl : ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) ≤ 0) : p = q := by
  have hgap : ∑ i, (p i * Real.log (p i) - p i * Real.log (q i) - p i + q i) = 0 := by
    apply le_antisymm
    · simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, hpsum, hqsum] at *
      linarith
    · exact Finset.sum_nonneg fun i _ => gibbs_gap_nonneg (hp i) (hq i)
  funext i
  by_contra hne
  have hz := (Finset.sum_eq_zero_iff_of_nonneg
    (fun j _ => gibbs_gap_nonneg (hp j) (hq j))).mp hgap i (Finset.mem_univ i)
  exact (gibbs_gap_pos (hp i) (hq i) hne).ne' hz

/-- Diagonal states with nonpositive relative entropy and faithful reference coincide. -/
theorem diagonal_states_eq_of_relativeEntropy_le_zero
    {a : Type u} [Fintype a] [DecidableEq a]
    (ρ σ : State a) (p q : a → ℝ)
    (hρ : ρ.matrix = diagonal (fun i => (p i : ℂ)))
    (hσ : σ.matrix = diagonal (fun i => (q i : ℂ)))
    (hq : ∀ i, 0 < q i) (hrel : ρ.relativeEntropy σ ≤ 0) : ρ = σ := by
  have hp (i : a) : 0 ≤ p i := by
    have h := ρ.pos.diag_nonneg (i := i)
    simpa [hρ] using h.1
  have hspos : σ.matrix.PosDef := by
    rw [hσ]
    exact Matrix.PosDef.diagonal (by intro i; exact_mod_cast hq i)
  have hsupp := Matrix.Supports.of_right_posDef ρ.matrix σ.matrix hspos
  rw [State.relativeEntropy_eq_coe_of_supports ρ σ hsupp,
    State.relativeEntropyPSDReferenceTraceLogFinite_eq_posDef_formula ρ hspos hsupp] at hrel
  have hreal : -ρ.vonNeumann - (ρ.matrix * State.psdLog σ.matrix hspos).trace.re /
      Real.log 2 ≤ 0 := by exact_mod_cast hrel
  have hlog : State.psdLog σ.matrix hspos = diagonal (fun i => (Real.log (q i) : ℂ)) := by
    unfold State.psdLog
    rw [hσ]
    exact cfc_diagonal_ofReal q Real.log
  have hentropy : ρ.vonNeumann = -(∑ i, p i * Real.log (p i)) / Real.log 2 := by
    rw [State.vonNeumann_eq_neg_sum_xlog2_of_diagonal ρ p hρ]
    simp only [xlog2, log2]
    have hx (x : ℝ) : (if x = 0 then 0 else x * (Real.log x / Real.log 2)) =
        x * Real.log x / Real.log 2 := by split_ifs with h <;> simp [h, mul_div_assoc]
    simp_rw [hx]
    rw [← Finset.sum_div, neg_div]
  have htrace : (ρ.matrix * State.psdLog σ.matrix hspos).trace.re =
      ∑ i, p i * Real.log (q i) := by
    rw [hρ, hlog, Matrix.diagonal_mul_diagonal]
    simp [Matrix.trace, Matrix.diag]
  have hkl : ∑ i, (p i * Real.log (p i) - p i * Real.log (q i)) ≤ 0 := by
    rw [hentropy, htrace] at hreal
    have h := (div_le_iff₀ (Real.log_pos one_lt_two)).mp
      (show ((∑ i, p i * Real.log (p i)) - ∑ i, p i * Real.log (q i)) /
          Real.log 2 ≤ 0 by simpa only [neg_div, neg_neg, sub_div] using hreal)
    simpa only [Finset.sum_sub_distrib, zero_mul] using h
  have hpsum : ∑ i, p i = 1 := by
    have h := congrArg Complex.re ρ.trace_eq_one
    simpa [hρ, Matrix.trace, Matrix.diag] using h
  have hqsum : ∑ i, q i = 1 := by
    have h := congrArg Complex.re σ.trace_eq_one
    simpa [hσ, Matrix.trace, Matrix.diag] using h
  have heq := probabilities_eq_of_kl_le_zero p q hp hq hpsum hqsum hkl
  exact State.ext (by rw [hρ, hσ, heq])

end
end AmplitudeDamping
