import AmplitudeDamping.OptimalSignals

/-!
# Product-signal achievability

The public Lean-QIT HSW theorem forgets encoder membership when exporting
`IsAchievableClassicalRate`. The standard fixed-ensemble product-state coding
theorem is therefore stated explicitly here as a classical interface. It
retains the actual encoder states and collective decoder, not just a number
called capacity. Its specialization to the paper's two explicit signals is
proved below. No AD-specific coding conclusion is assumed.
-/
namespace AmplitudeDamping
open QIT
noncomputable section

/-- Achievability while every codeword is a tensor product of the specified
signal states. The decoder is an unrestricted collective block POVM. -/
def IsAchievableWithSignals
    {a b ι : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (N : Channel a b) (signals : ι → State a) (R : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
    ∃ n₀ : ℕ, ∀ n : ℕ, n ≥ n₀ →
      ∃ (M : Type) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M)
        (C : HSWClassicalCode N n M),
        C.rate ≥ R - δ ∧ C.maxErrorAtMost ε ∧
        ∀ m : M, ∃ word : Fin n → ι,
          C.encoder m = productState (fun i => signals (word i))

/-- The standard HSW direct theorem for a fixed finite ensemble, retaining
its product-codeword witnesses. This proposition is an external classical
hypothesis; unrestricted HSW capacity itself is already proved upstream. -/
def ProductSignalHSW : Prop :=
  ∀ {a b ι : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype ι] [DecidableEq ι] (N : Channel a b) (E : Ensemble ι a),
    IsAchievableWithSignals N E.states (N.hswHolevoRate E)

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
    (hHSW : ProductSignalHSW)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    IsAchievableWithSignals (amplitudeDamping p hp0 hp1)
      (binarySignalEnsemble q hq0 hq1).states
      (amplitudeDampingScalarInformation p q) := by
  have h := hHSW (amplitudeDamping p hp0 hp1) (binarySignalEnsemble q hq0 hq1)
  have he : (amplitudeDamping p hp0 hp1).hswHolevoRate
      (binarySignalEnsemble q hq0 hq1) = amplitudeDampingScalarInformation p q :=
    binarySignalEnsemble_holevoAfter p hp0 hp1 q hq0 hq1
  rwa [he] at h

/-- At an optimal excitation the operational capacity is attainable using
only tensor products of the two explicit pure signals. -/
theorem binarySignal_optimal_product_code_achievable
    (hHSW : ProductSignalHSW)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hmax : IsMaxOn (amplitudeDampingScalarInformation p) (Set.Icc 0 1) q) :
    IsAchievableWithSignals (amplitudeDamping p hp0 hp1)
      (binarySignalEnsemble q hq0 hq1).states
      (Channel.classicalCapacity.{0,0,0} (amplitudeDamping p hp0 hp1)) := by
  rw [amplitudeDamping_classicalCapacity_eq_holevoInformation,
    ← binarySignalEnsemble_optimal_of_isMaxOn p hp0 hp1 q hq0 hq1 hmax,
    binarySignalEnsemble_holevoAfter]
  exact binarySignal_product_code_achievable hHSW p hp0 hp1 q hq0 hq1
end
end AmplitudeDamping
