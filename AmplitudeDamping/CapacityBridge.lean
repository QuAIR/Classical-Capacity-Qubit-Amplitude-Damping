import AmplitudeDamping.ScalarCapacity

/-!
# From Holevo additivity to classical capacity

This module connects the project-specific strong-additivity theorem to
Lean-QIT's block Holevo information, regularized Holevo information, and HSW
classical-capacity definitions.
-/

namespace AmplitudeDamping

open QIT

noncomputable section

/-- The `(n+1)`-use Holevo information is exactly `(n+1)` times its
single-use value. -/
theorem amplitudeDamping_blockHolevoInformation_succ
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    Channel.blockHolevoInformation.{0, 0, 0}
        (amplitudeDamping p hp0 hp1) (n + 1) =
      ((n + 1 : ℕ) : ℝ) *
        Channel.holevoInformation.{0, 0, 0}
          (amplitudeDamping p hp0 hp1) := by
  induction n with
  | zero =>
      unfold Channel.blockHolevoInformation
      rw [Channel.tensorPower_succ]
      trans Channel.holevoInformation.{0, 0, 0}
          (amplitudeDamping p hp0 hp1) +
        Channel.holevoInformation.{0, 0, 0}
          (Channel.tensorPower (amplitudeDamping p hp0 hp1) 0)
      · exact amplitudeDamping_holevoInformation_prod_eq p hp0 hp1 _
      have hunit : Channel.holevoInformation.{0, 0, 0}
          (Channel.tensorPower (amplitudeDamping p hp0 hp1) 0) = 0 := by
        unfold Channel.holevoInformation
        apply le_antisymm
        · apply csSup_le
            (Channel.holevoInformationValues_nonempty
              (N := Channel.tensorPower (amplitudeDamping p hp0 hp1) 0))
          intro r hr
          have h := Channel.mem_holevoInformationValues_le_log_card
            (N := Channel.tensorPower (amplitudeDamping p hp0 hp1) 0) hr
          rw [QIT.tensorPower_card] at h
          simpa [log2] using h
        · let E : Ensemble PUnit PUnit :=
            { probs := fun _ => 1
              weights_sum := by simp
              states := fun _ => State.unit }
          apply le_csSup
            (Channel.holevoInformationValues_bddAbove
              (N := Channel.tensorPower (amplitudeDamping p hp0 hp1) 0))
          refine ⟨PUnit, inferInstance, inferInstance, E, ?_⟩
          change 0 = Ensemble.holevoInformation
            (Channel.outputEnsemble
              (Channel.tensorPower (amplitudeDamping p hp0 hp1) 0) E)
          rw [Ensemble.holevoInformation_def,
            Ensemble.averageState_singleton _ (by simp) PUnit.unit]
          simp [Channel.outputEnsemble, E]
      rw [hunit]
      norm_num
  | succ n ih =>
      unfold Channel.blockHolevoInformation at ih ⊢
      rw [Channel.tensorPower_succ]
      trans Channel.holevoInformation.{0, 0, 0}
          (amplitudeDamping p hp0 hp1) +
        Channel.holevoInformation.{0, 0, 0}
          (Channel.tensorPower (amplitudeDamping p hp0 hp1) (n + 1))
      · exact amplitudeDamping_holevoInformation_prod_eq p hp0 hp1 _
      rw [ih]
      push_cast
      ring

/-- Regularization does not change amplitude damping's Holevo information. -/
theorem amplitudeDamping_regularizedHolevoInformation_eq
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel.regularizedHolevoInformation.{0, 0, 0}
        (amplitudeDamping p hp0 hp1) =
      Channel.holevoInformation.{0, 0, 0}
        (amplitudeDamping p hp0 hp1) := by
  let N := amplitudeDamping p hp0 hp1
  have hset : Channel.regularizedHolevoRateValues.{0, 0, 0} N =
      {Channel.holevoInformation.{0, 0, 0} N} := by
    ext r
    constructor
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      rw [amplitudeDamping_blockHolevoInformation_succ]
      have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      simp [N]
    · intro hr
      simp only [Set.mem_singleton_iff] at hr
      subst r
      refine ⟨1, by norm_num, ?_⟩
      rw [amplitudeDamping_blockHolevoInformation_succ p hp0 hp1 0]
      norm_num
      simp [N]
  unfold Channel.regularizedHolevoInformation
  rw [hset]
  simp [N]

/-- The HSW classical capacity of amplitude damping is its single-letter
Holevo information. -/
theorem amplitudeDamping_classicalCapacity_eq_holevoInformation
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    Channel.classicalCapacity.{0, 0, 0}
        (amplitudeDamping p hp0 hp1) =
      Channel.holevoInformation.{0, 0, 0}
        (amplitudeDamping p hp0 hp1) := by
  rw [Channel.classicalCapacity_eq_regularizedHolevoInformation,
    amplitudeDamping_regularizedHolevoInformation_eq]

/-- Literal scalar maximum form of the classical-capacity formula. -/
theorem amplitudeDamping_classicalCapacity_scalar_formula
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ q : ℝ, q ∈ Set.Icc (0 : ℝ) 1 ∧
      Channel.classicalCapacity.{0, 0, 0}
          (amplitudeDamping p hp0 hp1) =
        amplitudeDampingScalarInformation p q := by
  obtain ⟨q, hq, hqmax⟩ :=
    exists_amplitudeDamping_scalarInformation_maximizer p hp0 hp1
  exact ⟨q, hq, (amplitudeDamping_classicalCapacity_eq_holevoInformation
    p hp0 hp1).trans hqmax⟩

end

end AmplitudeDamping
