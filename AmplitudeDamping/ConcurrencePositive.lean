import AmplitudeDamping.FlatConcurrence
import Mathlib.Analysis.Complex.Polynomial.Basic

/-! # Positive quadratic contributions in finite concurrence ensembles -/

open scoped BigOperators Matrix ComplexConjugate

namespace AmplitudeDamping
open QIT
noncomputable section

/-- A unit scalar can phase a quadratic value to its nonnegative modulus. -/
theorem exists_unit_quadratic_phase (z : ℂ) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ c ^ 2 * z = (‖z‖ : ℂ) := by
  obtain ⟨d, hd, hdz⟩ := Complex.exists_norm_eq_mul_self z
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq d (by decide : 0 < 2)
  refine ⟨c, ?_, by rw [hc]; exact hdz.symm⟩
  have hnorm := congrArg norm hc
  rw [norm_pow, hd] at hnorm
  nlinarith [norm_nonneg c]

/-- A small real rotation splits a positive quadratic contribution into two
positive contributions even when the second initially vanishes. -/
theorem exists_positive_pair_rotation (a z : ℝ) (ha : 0 < a) (hz : 0 ≤ z) :
    ∃ t : ℝ, 0 < t ∧
      0 < (a - 2 * t * z) / (1 + t ^ 2) ∧
      0 < (t ^ 2 * a + 2 * t * z) / (1 + t ^ 2) ∧
      (a - 2 * t * z) / (1 + t ^ 2) +
        (t ^ 2 * a + 2 * t * z) / (1 + t ^ 2) = a := by
  let t := a / (4 * (a + z))
  have haz : 0 < a + z := add_pos_of_pos_of_nonneg ha hz
  have ht : 0 < t := div_pos ha (by positivity)
  have htz : 2 * t * z < a := by
    dsimp [t]
    have hd : 4 * (a + z) ≠ 0 := ne_of_gt (by positivity)
    rw [show 2 * (a / (4 * (a + z))) * z = (2 * a * z) / (4 * (a + z)) by ring]
    apply (div_lt_iff₀ (show 0 < 4 * (a + z) by positivity)).2
    nlinarith
  have hden : 0 < 1 + t ^ 2 := by positivity
  refine ⟨t, ht, div_pos (by linarith) hden,
    div_pos (add_pos_of_pos_of_nonneg (mul_pos (sq_pos_of_pos ht) ha)
      (by positivity)) hden, ?_⟩
  field_simp
  ring

/-- A real two-vector rotation preserves the represented density matrix. -/
theorem rankOneMatrix_real_rotation (u v : Qubit × Qubit → ℂ)
    (c s : ℝ) (hcs : c ^ 2 + s ^ 2 = 1) :
    rankOneMatrix ((c : ℂ) • u + (-(s : ℂ)) • v) +
      rankOneMatrix ((s : ℂ) • u + (c : ℂ) • v) =
        rankOneMatrix u + rankOneMatrix v := by
  ext i j
  have hcs' : (c : ℂ) ^ 2 + (s : ℂ) ^ 2 = 1 := by exact_mod_cast hcs
  simp only [Matrix.add_apply, rankOneMatrix_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, star_add, star_mul, star_neg, Complex.star_def, Complex.conj_ofReal]
  linear_combination (u i * conj (u j) + v i * conj (v j)) * hcs'

theorem rawConcurrence_smul (c : ℂ) (v : Qubit × Qubit → ℂ) :
    rawConcurrence (c • v) = c ^ 2 * rawConcurrence v := by
  simp only [rawConcurrence, Pi.smul_apply, smul_eq_mul]
  ring

theorem concurrenceOverlap_smul_right (u v : Qubit × Qubit → ℂ) (c : ℂ) :
    concurrenceOverlap u (c • v) = c * concurrenceOverlap u v := by
  simp only [concurrenceOverlap, Pi.smul_apply, smul_eq_mul]
  ring

theorem rankOneMatrix_unit_smul (v : Qubit × Qubit → ℂ)
    (c : ℂ) (hc : ‖c‖ = 1) : rankOneMatrix (c • v) = rankOneMatrix v := by
  have hcc : c * conj c = 1 := by simpa [hc] using Complex.mul_conj' c
  ext i j
  simp only [rankOneMatrix_apply, Pi.smul_apply, smul_eq_mul, star_mul, Complex.star_def]
  linear_combination (v i * conj (v j)) * hcc

/-- Every vector admits a density-preserving phase with nonnegative real concurrence. -/
theorem exists_rawConcurrence_phase (v : Qubit × Qubit → ℂ) :
    ∃ w : Qubit × Qubit → ℂ,
      rankOneMatrix w = rankOneMatrix v ∧
      rawConcurrence w = (‖rawConcurrence v‖ : ℂ) := by
  obtain ⟨c, hc, hq⟩ := exists_unit_quadratic_phase (rawConcurrence v)
  exact ⟨c • v, rankOneMatrix_unit_smul v c hc, by rwa [rawConcurrence_smul]⟩

/-- A positive-concurrence vector and a zero-concurrence vector can be replaced
by two positive real-concurrence vectors with the same density and total cost. -/
theorem exists_positive_rawConcurrence_pair
    (u v : Qubit × Qubit → ℂ) (a : ℝ) (ha : 0 < a)
    (hu : rawConcurrence u = (a : ℂ)) (hv : rawConcurrence v = 0) :
    ∃ u' v' : Qubit × Qubit → ℂ, ∃ a' b' : ℝ,
      0 < a' ∧ 0 < b' ∧ rawConcurrence u' = (a' : ℂ) ∧
      rawConcurrence v' = (b' : ℂ) ∧ a' + b' = a ∧
      rankOneMatrix u' + rankOneMatrix v' = rankOneMatrix u + rankOneMatrix v := by
  obtain ⟨p, hp, hz⟩ := Complex.exists_norm_eq_mul_self (concurrenceOverlap u v)
  let w := p • v
  have hw : rawConcurrence w = 0 := by simp [w, rawConcurrence_smul, hv]
  have hcross : concurrenceOverlap u w = (‖concurrenceOverlap u v‖ : ℂ) := by
    rw [concurrenceOverlap_smul_right]
    exact hz.symm
  obtain ⟨t, ht, hapos, hbpos, hab⟩ :=
    exists_positive_pair_rotation a ‖concurrenceOverlap u v‖ ha (norm_nonneg _)
  let r : ℝ := (Real.sqrt (1 + t ^ 2))⁻¹
  have hden : 0 < 1 + t ^ 2 := by positivity
  have hr : r ^ 2 = (1 + t ^ 2)⁻¹ := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt hden.le]
  have hrot : r ^ 2 + (r * t) ^ 2 = 1 := by
    rw [mul_pow]
    calc
      r ^ 2 + r ^ 2 * t ^ 2 = r ^ 2 * (1 + t ^ 2) := by ring
      _ = 1 := by rw [hr, inv_mul_cancel₀ (ne_of_gt hden)]
  refine ⟨(r : ℂ) • u + (-(r * t : ℝ) : ℂ) • w,
    ((r * t : ℝ) : ℂ) • u + (r : ℂ) • w,
    (a - 2 * t * ‖concurrenceOverlap u v‖) / (1 + t ^ 2),
    (t ^ 2 * a + 2 * t * ‖concurrenceOverlap u v‖) / (1 + t ^ 2),
    hapos, hbpos, ?_, ?_, hab, ?_⟩
  · rw [rawConcurrence_linearCombination, hu, hw, hcross]
    have hr' : (r : ℂ) ^ 2 = ((1 + t ^ 2 : ℝ) : ℂ)⁻¹ := by exact_mod_cast hr
    push_cast at hr' ⊢
    linear_combination ((a : ℂ) - 2 * t * ‖concurrenceOverlap u v‖) * hr'
  · rw [rawConcurrence_linearCombination, hu, hw, hcross]
    have hr' : (r : ℂ) ^ 2 = ((1 + t ^ 2 : ℝ) : ℂ)⁻¹ := by exact_mod_cast hr
    push_cast at hr' ⊢
    linear_combination ((t : ℂ) ^ 2 * a + 2 * t * ‖concurrenceOverlap u v‖) * hr'
  · rw [rankOneMatrix_real_rotation u w r (r * t) hrot,
      rankOneMatrix_unit_smul v p hp]

/-- A positive branch can be paired with an arbitrary branch and both made
strictly positive, preserving their total concurrence cost and density. -/
theorem exists_positive_rawConcurrence_pair_general
    (u v : Qubit × Qubit → ℂ) (a : ℝ) (ha : 0 < a)
    (hu : rawConcurrence u = (a : ℂ)) :
    ∃ u' v' : Qubit × Qubit → ℂ, ∃ a' b' : ℝ,
      0 < a' ∧ 0 < b' ∧ rawConcurrence u' = (a' : ℂ) ∧
      rawConcurrence v' = (b' : ℂ) ∧ a' + b' = a + ‖rawConcurrence v‖ ∧
      rankOneMatrix u' + rankOneMatrix v' = rankOneMatrix u + rankOneMatrix v := by
  by_cases hv : rawConcurrence v = 0
  · obtain ⟨u', v', a', b', ha', hb', hu', hv', hab, hd⟩ :=
      exists_positive_rawConcurrence_pair u v a ha hu hv
    exact ⟨u', v', a', b', ha', hb', hu', hv', by simpa [hv] using hab, hd⟩
  · obtain ⟨v', hd, hq⟩ := exists_rawConcurrence_phase v
    exact ⟨u, v', a, ‖rawConcurrence v‖, ha, norm_pos_iff.mpr hv, hu, hq,
      rfl, by rw [hd]⟩

theorem rankOneMatrix_real_smul (v : Qubit × Qubit → ℂ) (r : ℝ) :
    rankOneMatrix ((r : ℂ) • v) = ((r ^ 2 : ℝ) : ℂ) • rankOneMatrix v := by
  ext i j
  simp only [rankOneMatrix_apply, Matrix.smul_apply, Pi.smul_apply,
    smul_eq_mul, star_mul, Complex.star_def, Complex.conj_ofReal, Complex.ofReal_pow]
  ring

private theorem sum_restore_zeroed {ι M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommMonoid M] (f : ι → M) (j : ι) :
    f j + (∑ i, if i = j then 0 else f i) = ∑ i, f i := by
  calc
    _ = ∑ i, ((if i = j then f i else 0) + (if i = j then 0 else f i)) := by
      rw [Finset.sum_add_distrib]
      simp
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i _
      split_ifs <;> simp

/-- Any finite raw ensemble of positive total concurrence admits a finite
refinement with strictly positive real concurrence on every branch. -/
theorem exists_positive_rawConcurrence_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Qubit × Qubit → ℂ) (hcost : 0 < rawConcurrenceCost v) :
    ∃ w : ι × Bool → Qubit × Qubit → ℂ, ∃ a : ι × Bool → ℝ,
      (∀ i, 0 < a i) ∧ (∀ i, rawConcurrence (w i) = (a i : ℂ)) ∧
      (∑ i, rankOneMatrix (w i)) = (∑ i, rankOneMatrix (v i)) ∧
      rawConcurrenceCost w = rawConcurrenceCost v := by
  obtain ⟨j, _, hj⟩ := (Finset.sum_pos_iff_of_nonneg
    (fun i (_ : i ∈ Finset.univ) => norm_nonneg (rawConcurrence (v i)))).mp hcost
  letI : Nonempty ι := ⟨j⟩
  have hn : (0 : ℝ) < Fintype.card ι := by exact_mod_cast Fintype.card_pos
  let r : ℝ := (Real.sqrt (Fintype.card ι))⁻¹
  have hr : r ^ 2 = (Fintype.card ι : ℝ)⁻¹ := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt hn.le]
  obtain ⟨u, huD, huq⟩ := exists_rawConcurrence_phase (v j)
  let u₀ : Qubit × Qubit → ℂ := (r : ℂ) • u
  let a₀ : ℝ := ‖rawConcurrence (v j)‖ / Fintype.card ι
  have ha₀ : 0 < a₀ := div_pos hj hn
  have hu₀ : rawConcurrence u₀ = (a₀ : ℂ) := by
    change rawConcurrence ((r : ℂ) • u) =
      ((‖rawConcurrence (v j)‖ / Fintype.card ι : ℝ) : ℂ)
    rw [rawConcurrence_smul, huq]
    have hr' : (r : ℂ) ^ 2 = (Fintype.card ι : ℂ)⁻¹ := by
      simpa only [Complex.ofReal_pow, Complex.ofReal_inv, Complex.ofReal_natCast]
        using congrArg Complex.ofReal hr
    rw [hr']
    push_cast
    ring
  let v₀ : ι → Qubit × Qubit → ℂ := fun i => if i = j then 0 else v i
  choose u' v' a' b' ha' hb' hqu' hqv' hab hd using
    (fun i : ι => exists_positive_rawConcurrence_pair_general u₀ (v₀ i) a₀ ha₀ hu₀)
  let w : ι × Bool → Qubit × Qubit → ℂ := fun p => if p.2 then v' p.1 else u' p.1
  let a : ι × Bool → ℝ := fun p => if p.2 then b' p.1 else a' p.1
  have hapos : ∀ p, 0 < a p := by
    rintro ⟨i, b⟩
    cases b <;> simp [a, ha', hb']
  have hwq : ∀ p, rawConcurrence (w p) = (a p : ℂ) := by
    rintro ⟨i, b⟩
    cases b <;> simp [w, a, hqu', hqv']
  refine ⟨w, a, hapos, hwq, ?_, ?_⟩
  · have hcopy : (Fintype.card ι : ℂ) • rankOneMatrix u₀ = rankOneMatrix (v j) := by
      change (Fintype.card ι : ℂ) • rankOneMatrix ((r : ℂ) • u) = _
      rw [rankOneMatrix_real_smul, smul_smul]
      have hscalar : (Fintype.card ι : ℂ) * ((r ^ 2 : ℝ) : ℂ) = 1 := by
        rw [hr, Complex.ofReal_inv]
        simp only [Complex.ofReal_natCast]
        exact mul_inv_cancel₀ (by exact_mod_cast (ne_of_gt hn))
      rw [hscalar, one_smul, huD]
    calc
      ∑ p, rankOneMatrix (w p) =
          ∑ i, (rankOneMatrix u₀ + rankOneMatrix (v₀ i)) := by
        simp only [Fintype.sum_prod_type, Fintype.sum_bool, w, Bool.false_eq_true,
          ↓reduceIte]
        apply Finset.sum_congr rfl
        intro i _
        simpa only [add_comm] using hd i
      _ = (Fintype.card ι : ℂ) • rankOneMatrix u₀ + ∑ i, rankOneMatrix (v₀ i) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ]
        simp only [Nat.cast_smul_eq_nsmul]
      _ = ∑ i, rankOneMatrix (v i) := by
        rw [hcopy]
        have hz : rankOneMatrix (0 : Qubit × Qubit → ℂ) = 0 := by
          ext i k
          simp [rankOneMatrix_apply]
        simp only [v₀, apply_ite, hz]
        exact sum_restore_zeroed (fun i => rankOneMatrix (v i)) j
  · have hcopy : (Fintype.card ι : ℝ) * a₀ = ‖rawConcurrence (v j)‖ := by
      dsimp [a₀]
      field_simp
    calc
      rawConcurrenceCost w = ∑ p, a p := by
        unfold rawConcurrenceCost
        apply Finset.sum_congr rfl
        intro i _
        rw [hwq i, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (hapos i)]
      _ = ∑ i, (a₀ + ‖rawConcurrence (v₀ i)‖) := by
        simp only [Fintype.sum_prod_type, Fintype.sum_bool, a, Bool.false_eq_true,
          ↓reduceIte]
        apply Finset.sum_congr rfl
        intro i _
        simpa only [add_comm] using hab i
      _ = (Fintype.card ι : ℝ) * a₀ + ∑ i, ‖rawConcurrence (v₀ i)‖ := by
        simp [Finset.sum_add_distrib]
      _ = rawConcurrenceCost v := by
        rw [hcopy]
        have hz : rawConcurrence (0 : Qubit × Qubit → ℂ) = 0 := by
          simp [rawConcurrence]
        simp only [v₀, apply_ite, hz, norm_zero]
        exact sum_restore_zeroed (fun i => ‖rawConcurrence (v i)‖) j

end
end AmplitudeDamping
