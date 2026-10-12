import AmplitudeDamping.OptimalSignals
import AmplitudeDamping.ProductSignalHSW

/-!
# Product-signal achievability

The public Lean-QIT HSW theorem forgets encoder membership when exporting
`IsAchievableClassicalRate`. The fixed-ensemble product-state coding theorem is proved in
`ProductSignalHSW.lean` by retaining the input words through packing and expurgation. It
retains the actual encoder states and collective decoder, not just a number
called capacity. Its specialization to the paper's two explicit signals is
proved below. No coding hypothesis is required.
-/
namespace AmplitudeDamping
open QIT
noncomputable section

/-- The standard HSW direct theorem for a fixed finite ensemble, retaining
its product-codeword witnesses. The proposition is proved below using the
fixed-ensemble packing construction. -/
def ProductSignalHSW : Prop :=
  ∀ {a b ι : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype ι] [DecidableEq ι] (N : Channel a b) (E : Ensemble ι a),
    IsAchievableWithSignals N E.states (N.hswHolevoRate E)

/-- Fixed-ensemble product-signal coding follows from HSW packing and expurgation. -/
theorem productSignalHSW : ProductSignalHSW := by
  intro a b ι _ _ _ _ _ _ N E
  exact fixedEnsemble_product_code_achievable N E

/-- The restricted notion implies the usual operational coding predicate. -/
theorem IsAchievableWithSignals.unrestricted
    {a b ι : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {N : Channel a b} {signals : ι → State a} {R : ℝ}
    (h : IsAchievableWithSignals N signals R) :
    Channel.IsAchievableClassicalRate.{0,0,0} N R := by
  intro δ hδ ε hε
  obtain ⟨n₀, hn₀⟩ := h δ hδ ε hε
  refine ⟨n₀, ?_⟩
  intro n hn
  obtain ⟨M,hF,hD,hM,C,hR,hε',_⟩ := hn₀ n hn
  exact ⟨M,hF,hD,hM,C,hR,hε'⟩

/-- Rates may be decreased while keeping the same signal alphabet. -/
theorem IsAchievableWithSignals.mono
    {a b ι : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    {N : Channel a b} {signals : ι → State a} {R S : ℝ}
    (h : IsAchievableWithSignals N signals R) (hS : S ≤ R) :
    IsAchievableWithSignals N signals S := by
  intro δ hδ ε hε
  obtain ⟨n₀, hn₀⟩ := h δ hδ ε hε
  refine ⟨n₀, ?_⟩
  intro n hn
  obtain ⟨M,hF,hD,hM,C,hR,hε',hw⟩ := hn₀ n hn
  exact ⟨M,hF,hD,hM,C,by linarith,hε',hw⟩

/-- The paper's explicit two signals admit tensor-product encoders attaining
exactly their one-use Holevo rate. -/
theorem binarySignal_product_code_achievable
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsAchievableWithSignals (amplitudeDamping p hp0 hp1)
      (binarySignalEnsemble q hq0 hq1).states
      (amplitudeDampingScalarInformation p q) := by
  have h := productSignalHSW (amplitudeDamping p hp0 hp1) (binarySignalEnsemble q hq0 hq1)
  have he : (amplitudeDamping p hp0 hp1).hswHolevoRate
      (binarySignalEnsemble q hq0 hq1) = amplitudeDampingScalarInformation p q :=
    binarySignalEnsemble_holevoAfter p hp0 hp1 q hq0 hq1
  rwa [he] at h

/-- At an optimal excitation the operational capacity is attainable using
only tensor products of the two explicit pure signals. -/
theorem binarySignal_optimal_product_code_achievable
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmax : IsMaxOn (amplitudeDampingScalarInformation p) (Set.Icc 0 1) q) :
    IsAchievableWithSignals (amplitudeDamping p hp0 hp1)
      (binarySignalEnsemble q hq0 hq1).states
      (Channel.classicalCapacity.{0,0,0} (amplitudeDamping p hp0 hp1)) := by
  rw [amplitudeDamping_classicalCapacity_eq_holevoInformation,
    ← binarySignalEnsemble_optimal_of_isMaxOn p hp0 hp1 q hq0 hq1 hmax,
    binarySignalEnsemble_holevoAfter]
  exact binarySignal_product_code_achievable p hp0 hp1 q hq0 hq1
end
end AmplitudeDamping
