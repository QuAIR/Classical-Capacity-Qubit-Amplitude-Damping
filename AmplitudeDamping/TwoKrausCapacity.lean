import AmplitudeDamping.TwoKrausRoof
import AmplitudeDamping.OneLetterCapacity
import QIT.Coding.Classical.HSWLimit
import QIT.Util.TensorPower

/-!
# Holevo additivity and capacity collapse for two-Kraus qubit channels

Manuscript §5, Corollary 8, second displayed equation.  If the qubit channel
`N` admits a Kraus representation with at most two operators, then the Holevo
information is additive against every finite-dimensional channel `M`,

`χ(N ⊗ M) = χ(N) + χ(M)`,

and the HSW classical capacity of `N` collapses to the one-letter Holevo
information, `C(N) = χ(N)`.

The two-Kraus hypothesis enters only through the roof-superadditivity
statement of `TwoKrausRoof.outputEntropyRoof_prod_ge_of_twoKraus`, packaged
here once and for all as the explicit hypothesis `hs`: for every
finite-dimensional channel `M` and every input state `τ` on `Qubit ⊗ Y`,
`roof(N)(τ_X) + roof(M)(τ_Y) ≤ roof(N ⊗ M)(τ)`.  Quantifying over auxiliary
channels of arbitrary finite dimension is exactly what the tensor-power
induction needs.

The superadditivity half of additivity is generic: product ensembles of
near-optimizing ensembles of the two factors are sent by the product channel
to product output ensembles, whose Holevo information splits exactly.  The
subadditivity half is where `hs` enters, through the generic ensemble converse
of `HolevoReduction`.  The regularization collapse follows the
`CapacityBridge` template: the `(k+1)`-fold tensor-power Holevo information is
exactly `(k+1) * χ(N)`, so the regularized block-rate set is the singleton
`{χ(N)}`.
-/

open scoped BigOperators NNReal ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

universe u v w

noncomputable section

/-! ### Strong additivity of the Holevo information -/

/-- **Generic superadditivity half.**  For any qubit channel `N` and any
finite-dimensional channel `M` with nonempty input, the Holevo information of
the product channel dominates the sum of the factors' Holevo informations:
products of near-optimizing ensembles witness it, because a product channel
sends a product ensemble to the product of the output ensembles and the Holevo
information of a product ensemble splits. -/
theorem holevoInformation_prod_ge_generic
    {y : Type u} {d : Type v} [Fintype y] [DecidableEq y]
    [Fintype d] [DecidableEq d] [Nonempty y]
    (N : Channel Qubit Qubit) (M : Channel y d) :
    Channel.holevoInformation.{0, 0, 0} N +
      Channel.holevoInformation.{u, v, 0} M ≤
      Channel.holevoInformation.{u, v, 0} (N.prod M) := by
  apply le_of_forall_pos_le_add
  intro ε hε
  have hhalf : 0 < ε / 2 := half_pos hε
  obtain ⟨ι, hιF, hιD, E, hE⟩ :=
    N.exists_hswHolevoRate_gt_of_lt_holevoInformation
      N.holevoInformationValues_nonempty (sub_lt_self _ hhalf)
  obtain ⟨κ, hκF, hκD, F, hF⟩ :=
    M.exists_hswHolevoRate_gt_of_lt_holevoInformation
      M.holevoInformationValues_nonempty (sub_lt_self _ hhalf)
  letI : Fintype ι := hιF
  letI : DecidableEq ι := hιD
  letI : Fintype κ := hκF
  letI : DecidableEq κ := hκD
  have hprod : (N.prod M).hswHolevoRate (E.prod F) ≤
      Channel.holevoInformation.{u, v, 0} (N.prod M) := by
    exact ensembleHolevoAfter_le_holevoInformation (N.prod M) (E.prod F)
  have hadd := ensembleHolevoAfter_prod_prod_eq N M E F
  change (N.prod M).hswHolevoRate (E.prod F) =
    N.hswHolevoRate E + M.hswHolevoRate F at hadd
  linarith

/-- **Corollary 8, second displayed equation: Holevo additivity.**  Under the
roof-superadditivity hypothesis `hs` for the qubit channel `N` (the packaging
of the two-Kraus hypothesis), the Holevo information of `N ⊗ M` splits as the
sum of the Holevo informations of the factors, for every finite-dimensional
auxiliary channel `M`. -/
theorem holevoInformation_prod_eq (N : Channel Qubit Qubit)
    (hs : ∀ {y₁ : Type u} {d₁ : Type v} [Fintype y₁] [DecidableEq y₁]
        [Fintype d₁] [DecidableEq d₁] (M : Channel y₁ d₁)
        (τ : State (Qubit × y₁)),
      outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB ≤
        outputEntropyRoof (N.prod M) τ)
    {y : Type u} {d : Type v} [Fintype y] [DecidableEq y]
    [Fintype d] [DecidableEq d] [Nonempty y] (M : Channel y d) :
    Channel.holevoInformation.{u, v, 0} (N.prod M) =
      Channel.holevoInformation.{0, 0, 0} N +
        Channel.holevoInformation.{u, v, 0} M := by
  apply le_antisymm
  · unfold Channel.holevoInformation
    apply csSup_le ((N.prod M).holevoInformationValues_nonempty)
    intro r hr
    rcases hr with ⟨ι, hιF, hιD, E, rfl⟩
    letI : Fintype ι := hιF
    letI : DecidableEq ι := hιD
    have hconv := ensembleHolevoAfter_prod_le
      (outputEntropyRoof (N.prod M)) (outputEntropyRoof N)
      (outputEntropyRoof M) N M E
      (outputEntropyRoof_isOutputEntropyRoof (N.prod M)) (hs M)
    have hleft := fixedInputHolevo_le_holevoInformation N
      E.averageState.marginalA
    have hright := fixedInputHolevo_le_holevoInformation M
      E.averageState.marginalB
    change ensembleHolevoAfter (N.prod M) E ≤ _
    unfold Channel.holevoInformation at hleft hright
    linarith
  · exact holevoInformation_prod_ge_generic N M

/-- **Corollary 8, second displayed equation, superadditivity half.**  If the
output-entropy convex roof of the qubit channel `N` is strongly superadditive
against every finite-dimensional auxiliary channel (the packaging of the
two-Kraus hypothesis), then the Holevo information of the product channel
dominates the sum of the Holevo informations of the factors. -/
theorem holevoInformation_prod_ge (N : Channel Qubit Qubit)
    (hs : ∀ {y₁ : Type u} {d₁ : Type v} [Fintype y₁] [DecidableEq y₁]
        [Fintype d₁] [DecidableEq d₁] (M : Channel y₁ d₁)
        (τ : State (Qubit × y₁)),
      outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB ≤
        outputEntropyRoof (N.prod M) τ)
    {y : Type u} {d : Type v} [Fintype y] [DecidableEq y]
    [Fintype d] [DecidableEq d] [Nonempty y] (M : Channel y d) :
    Channel.holevoInformation.{0, 0, 0} N +
      Channel.holevoInformation.{u, v, 0} M ≤
      Channel.holevoInformation.{u, v, 0} (N.prod M) :=
  (holevoInformation_prod_eq N hs M).ge

/-! ### The tensor-power induction -/

/-- **The n-copy Holevo identity.**  Under the roof-superadditivity hypothesis
`hs`, the `(n + 1)`-use tensor-power Holevo information of `N` is exactly
`(n + 1)` times its single-use value.  The induction peels one factor off
QIT's right-recursive tensor power `Channel.tensorPower N (n + 1) =
N.prod (Channel.tensorPower N n)` via `holevoInformation_prod_eq`; the base
case is the unit system, whose Holevo information vanishes. -/
theorem twoKraus_blockHolevoInformation_succ (N : Channel Qubit Qubit)
    (hs : ∀ {y₁ : Type} {d₁ : Type} [Fintype y₁] [DecidableEq y₁]
        [Fintype d₁] [DecidableEq d₁] (M : Channel y₁ d₁)
        (τ : State (Qubit × y₁)),
      outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB ≤
        outputEntropyRoof (N.prod M) τ)
    (n : ℕ) :
    Channel.blockHolevoInformation.{0, 0, 0} N (n + 1) =
      ((n + 1 : ℕ) : ℝ) * Channel.holevoInformation.{0, 0, 0} N := by
  induction n with
  | zero =>
      haveI : Nonempty (TensorPower Qubit 0) :=
        tensorPower_nonempty_of_nonempty 0
      unfold Channel.blockHolevoInformation
      rw [Channel.tensorPower_succ]
      trans Channel.holevoInformation.{0, 0, 0} N +
        Channel.holevoInformation.{0, 0, 0} (Channel.tensorPower N 0)
      · exact holevoInformation_prod_eq N hs _
      have hunit : Channel.holevoInformation.{0, 0, 0}
          (Channel.tensorPower N 0) = 0 := by
        unfold Channel.holevoInformation
        apply le_antisymm
        · apply csSup_le
            (Channel.holevoInformationValues_nonempty
              (N := Channel.tensorPower N 0))
          intro r hr
          have h := Channel.mem_holevoInformationValues_le_log_card
            (N := Channel.tensorPower N 0) hr
          rw [QIT.tensorPower_card] at h
          simpa [log2] using h
        · let E : Ensemble PUnit PUnit :=
            { probs := fun _ => 1
              weights_sum := by simp
              states := fun _ => State.unit }
          apply le_csSup
            (Channel.holevoInformationValues_bddAbove
              (N := Channel.tensorPower N 0))
          refine ⟨PUnit, inferInstance, inferInstance, E, ?_⟩
          change 0 = Ensemble.holevoInformation
            (Channel.outputEnsemble (Channel.tensorPower N 0) E)
          rw [Ensemble.holevoInformation_def,
            Ensemble.averageState_singleton _ (by simp) PUnit.unit]
          simp [Channel.outputEnsemble, E]
      rw [hunit]
      norm_num
  | succ n ih =>
      haveI : Nonempty (TensorPower Qubit (n + 1)) :=
        tensorPower_nonempty_of_nonempty (n + 1)
      unfold Channel.blockHolevoInformation at ih ⊢
      rw [Channel.tensorPower_succ]
      trans Channel.holevoInformation.{0, 0, 0} N +
        Channel.holevoInformation.{0, 0, 0} (Channel.tensorPower N (n + 1))
      · exact holevoInformation_prod_eq N hs _
      rw [ih]
      push_cast
      ring

/-! ### Regularization collapse -/

/-- **Corollary 8, capacity collapse: regularization is trivial.**  Under the
roof-superadditivity hypothesis `hs`, every positive block rate of `N` equals
the single-letter Holevo information, so the regularized Holevo information
collapses to it. -/
theorem twoKraus_regularizedHolevoInformation_eq (N : Channel Qubit Qubit)
    (hs : ∀ {y₁ : Type} {d₁ : Type} [Fintype y₁] [DecidableEq y₁]
        [Fintype d₁] [DecidableEq d₁] (M : Channel y₁ d₁)
        (τ : State (Qubit × y₁)),
      outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB ≤
        outputEntropyRoof (N.prod M) τ) :
    Channel.regularizedHolevoInformation.{0, 0, 0} N =
      Channel.holevoInformation.{0, 0, 0} N := by
  have hset : Channel.regularizedHolevoRateValues.{0, 0, 0} N =
      {Channel.holevoInformation.{0, 0, 0} N} := by
    ext r
    constructor
    · rintro ⟨n, hn, rfl⟩
      obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn)
      rw [twoKraus_blockHolevoInformation_succ N hs]
      have hk : ((k + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
      simp
    · intro hr
      simp only [Set.mem_singleton_iff] at hr
      subst hr
      refine ⟨1, by norm_num, ?_⟩
      rw [twoKraus_blockHolevoInformation_succ N hs 0]
      norm_num
  unfold Channel.regularizedHolevoInformation
  rw [hset]
  simp

/-- **Corollary 8, capacity collapse.**  Under the roof-superadditivity
hypothesis `hs`, the HSW classical capacity of `N` equals its single-letter
Holevo information. -/
theorem twoKraus_classicalCapacity_eq_holevoInformation (N : Channel Qubit Qubit)
    (hs : ∀ {y₁ : Type} {d₁ : Type} [Fintype y₁] [DecidableEq y₁]
        [Fintype d₁] [DecidableEq d₁] (M : Channel y₁ d₁)
        (τ : State (Qubit × y₁)),
      outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB ≤
        outputEntropyRoof (N.prod M) τ) :
    Channel.classicalCapacity.{0, 0, 0} N =
      Channel.holevoInformation.{0, 0, 0} N := by
  rw [Channel.classicalCapacity_eq_regularizedHolevoInformation,
    twoKraus_regularizedHolevoInformation_eq N hs]

/-! ### Instantiation: two-Kraus qubit channels -/

/-- **Corollary 8, second displayed equation: strong Holevo additivity for
two-Kraus qubit channels.**  If the qubit channel `N` admits a Kraus
representation with at most two operators, then for every finite-dimensional
auxiliary channel `M` the Holevo information is additive,
`χ(N ⊗ M) = χ(N) + χ(M)`.  The Wootters interface hypothesis is carried, as
everywhere in this repository. -/
theorem twoKraus_holevoInformation_prod_eq
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    (h : woottersKernelUpperBound) (hcard : Fintype.card κ ≤ 2)
    (K : κ → Matrix Qubit Qubit ℂ) (N : Channel Qubit Qubit)
    (hN : N.map = MatrixMap.ofKraus K)
    {y : Type u} {d : Type v} [Fintype y] [DecidableEq y]
    [Fintype d] [DecidableEq d] [Nonempty y] (M : Channel y d) :
    Channel.holevoInformation.{u, v, 0} (N.prod M) =
      Channel.holevoInformation.{0, 0, 0} N +
        Channel.holevoInformation.{u, v, 0} M :=
  holevoInformation_prod_eq N
    (outputEntropyRoof_prod_ge_of_twoKraus h hcard K N hN) M

/-- **Corollary 8, capacity collapse for two-Kraus qubit channels.**  If the
qubit channel `N` admits a Kraus representation with at most two operators,
its HSW classical capacity is exactly its single-letter Holevo information:
`C(N) = χ(N)`. -/
theorem twoKraus_classicalCapacity_eq
    {κ : Type w} [Fintype κ] [DecidableEq κ]
    (h : woottersKernelUpperBound) (hcard : Fintype.card κ ≤ 2)
    (K : κ → Matrix Qubit Qubit ℂ) (N : Channel Qubit Qubit)
    (hN : N.map = MatrixMap.ofKraus K) :
    Channel.classicalCapacity.{0, 0, 0} N =
      Channel.holevoInformation.{0, 0, 0} N := by
  have hs : ∀ {y₁ : Type} {d₁ : Type} [Fintype y₁] [DecidableEq y₁]
      [Fintype d₁] [DecidableEq d₁] (M : Channel y₁ d₁)
      (τ : State (Qubit × y₁)),
    outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB ≤
      outputEntropyRoof (N.prod M) τ :=
    outputEntropyRoof_prod_ge_of_twoKraus h hcard K N hN
  rw [Channel.classicalCapacity_eq_regularizedHolevoInformation,
    twoKraus_regularizedHolevoInformation_eq N hs]

end

end AmplitudeDamping
