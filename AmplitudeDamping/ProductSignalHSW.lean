/-
The source-projector assembly below adapts the Lean-QIT HSW construction.
Copyright (c) 2026 QuAIR. Released under Apache 2.0; see the dependency LICENSE.
-/
import QIT.Coding.Classical.HSWDirect

/-!
# HSW direct coding with a fixed signal alphabet

The packing construction and expurgation retain the input word map. The
spectral construction follows Lean-QIT's `WitnessAssembly.lean`, with this
extra witness carried through to the operational conclusion.
-/
namespace AmplitudeDamping
open QIT
open scoped ComplexOrder MatrixOrder NNReal
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

/-- Packing followed by expurgation preserves the specified signal alphabet. -/
private theorem codeWithSignals_of_packing
    {a b ι 𝒳 M : Type}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype 𝒳] [DecidableEq 𝒳] [Fintype M] [DecidableEq M] [Nonempty M]
    (N : Channel a b) (signals : ι → State a) {n : ℕ} {τ δ ε R : ℝ}
    (Eout : Ensemble 𝒳 (TensorPower b n)) (H : HSWPackingHypothesesSpectral Eout τ)
    (word : 𝒳 → Fin n → ι)
    (houtput : ∀ x, (N.tensorPower n).applyState
      (productState (fun i => signals (word x i))) = Eout.states x)
    (hn : 0 < n) (hinv : (1 : ℝ) / n ≤ δ / 2) (hε : 0 < ε)
    (hrate : R - δ / 2 ≤ hswMessageRate M n)
    (hpacking : 2 * (H.ε + 2 * Real.sqrt H.ε) +
      4 * ((Fintype.card M : ℝ) - 1) * (H.d / H.D) ≤ ε / 2) :
    ∃ (M' : Type) (_ : Fintype M') (_ : DecidableEq M') (_ : Nonempty M')
      (C' : HSWClassicalCode N n M'),
      C'.rate ≥ R - δ ∧ C'.maxErrorAtMost ε ∧
      ∀ m : M', ∃ w : Fin n → ι,
        C'.encoder m = productState (fun i => signals (w i)) := by
  classical
  obtain ⟨C₀, dec, hcode⟩ := PackingLemma.packingLemma_avgError (M := M)
    Eout H.P H.P_posSemidef H.P_idempotent H.P_le_one H.Px H.Px_projector
    H.d H.D H.ε H.hD_pos H.hε_nonneg H.h1 H.h2 H.h3 H.h4
  let C : HSWClassicalCode N n M :=
    { encoder := fun m => productState (fun i => signals (word (C₀ m) i))
      decoder := dec }
  have havg : C.toPackingDecoderCode.averageErrorAtMost (ε / 2) := by
    rw [PackingLemma.DecoderCode.averageErrorAtMost_iff] at hcode ⊢
    have hout : C.toPackingDecoderCode =
        (⟨fun m => Eout.states (C₀ m), dec⟩ : PackingLemma.DecoderCode M (TensorPower b n)) := by
      dsimp [HSWClassicalCode.toPackingDecoderCode, C, HSWClassicalCode.outputState]
      congr 1
      funext m
      exact houtput (C₀ m)
    rw [hout]
    exact hcode.trans hpacking
  obtain ⟨S, hcard, hgood⟩ := C.exists_goodSubset_of_averageErrorAtMost havg (by positivity)
  have hSne : S.Nonempty := Finset.card_pos.mp (by
    have hMpos := Fintype.card_pos_iff.mpr (inferInstance : Nonempty M)
    omega)
  let M' := {m : M // m ∈ S}
  letI : Nonempty M' := ⟨⟨hSne.choose, hSne.choose_spec⟩⟩
  let C' : HSWClassicalCode N n M' := C.restrictToFinset S
  have hcard' : 2 * Fintype.card M' ≥ Fintype.card M := by
    simpa [M', Fintype.card_subtype] using hcard
  have hrate' := hswMessageRate.ge_sub_inv_of_two_card_ge (M := M) (M' := M') hn hcard'
  refine ⟨M', inferInstance, inferInstance, inferInstance, C', ?_, ?_, ?_⟩
  · change R - δ ≤ hswMessageRate M' n
    linarith
  · intro m
    have h := (C.restrictToFinset_error_le S m).trans (hgood m.1 m.2)
    change (C.restrictToFinset S).error m ≤ ε
    linarith
  · intro m
    exact ⟨word (C₀ m.1), rfl⟩

variable {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Source-projector packing estimates assembled without forgetting the input words. -/
private theorem achievableWithSignals_of_finiteMassBounds
    (N : Channel a b) {ι : Type} [Fintype ι] [DecidableEq ι]
    (E₀ : Ensemble ι a)
    (h :
      ∀ δ : ℝ, 0 < δ → ∀ ε : ℝ, 0 < ε →
        ∃ N0 : ℕ, ∀ n : ℕ, n ≥ N0 →
          0 < n ∧ (1 : ℝ) / (n : ℝ) ≤ δ / 2 ∧
            ∀ (M : Type) (_ : Fintype M) (_ : DecidableEq M) (_ : Nonempty M),
              hswMessageRate M n ≥ N.hswHolevoRate E₀ - δ / 2 →
                (Fintype.card M : ℝ) - 1 ≤
                  Real.rpow 2 ((n : ℝ) * (N.hswHolevoRate E₀ - δ / 2)) →
                ∃ (δx : ℝ), ∃ (δc : ℝ),
                  ∃ (packingε : ℝ), ∃ (pruneε : ℝ),
                    0 < δx ∧ 0 < δc ∧ 0 ≤ packingε ∧ pruneε < 1 ∧
                      (Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2) ≤ pruneε ∧
                      (Fintype.card ι : ℝ) * (Fintype.card b : ℝ) /
                          ((n : ℝ) * δc ^ 2) ≤ packingε ∧
                      (∀ x :
                          ClassicalTypicality.StrongTypicalWord
                            (N.outputEnsemble E₀).indexDistribution n δx,
                        conditionalLogDeviationSecondMoment
                            (fun i : Fin n =>
                              (N.outputEnsemble E₀).states
                                (ClassicalTypicality.StrongTypicalWord.codeword
                                  (N.outputEnsemble E₀).indexDistribution δx x i)) /
                          ((n : ℝ) * δc) ^ 2 ≤ packingε) ∧
                      2 * (packingε + 2 * Real.sqrt packingε) ≤ ε / 4 ∧
                      4 * Real.rpow 2 ((n : ℝ) * (N.hswHolevoRate E₀ - δ / 2)) *
                            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
                              ((1 - pruneε) *
                                (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
                                  (N.outputEnsemble E₀).averageState).strongTypicalMassScale
                                    n ((Fintype.card ι : ℝ) * (δx + δc)))) ≤
                            ε / 4) :
    IsAchievableWithSignals N E₀.states (N.hswHolevoRate E₀) := by
  intro δ hδ ε hε
  obtain ⟨N0, hN0⟩ := h δ hδ ε hε
  refine ⟨N0, ?_⟩
  intro n hn
  obtain ⟨hn_pos, hinv_le, hpack⟩ := hN0 n hn
  obtain ⟨M, hMfin, hMdec, hMnonempty, hrate, hcard⟩ :=
    hswMessageRate.exists_finite_message_type_rate_ge_card_sub_one_le.{0} hn_pos
      (N.hswHolevoRate E₀ - δ / 2)
  letI : Fintype M := hMfin
  letI : DecidableEq M := hMdec
  letI : Nonempty M := hMnonempty
  obtain ⟨δx, δc, packingε, pruneε, hδx, hδc, hpackingε, hprune,
    hmass_large, hlarge, hmoment, hself, hcrossCap⟩ :=
      hpack M hMfin hMdec hMnonempty hrate hcard
  let p := (N.outputEnsemble E₀).indexDistribution
  let δz : ℝ := (Fintype.card ι : ℝ) * (δx + δc)
  let 𝒳 := ClassicalTypicality.StrongTypicalWord p n δx
  have hmass0 :
      1 - ((Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2)) ≤
        (ClassicalTypicality.strongTypicalMass
          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) :=
    ClassicalTypicality.strongTypicalMass_ge_one_sub_card_bound
      (p := (N.outputEnsemble E₀).indexDistribution) hn_pos hδx
  have hmass_lower :
      (1 - pruneε : ℝ) ≤
        (ClassicalTypicality.strongTypicalMass
          (n := n) (N.outputEnsemble E₀).indexDistribution δx : ℝ) := by
    have hleft :
        (1 - pruneε : ℝ) ≤
          1 - ((Fintype.card ι : ℝ) / ((n : ℝ) * δx ^ 2)) := by
      linarith
    exact le_trans hleft hmass0
  have hprune_pos : 0 < 1 - pruneε := by linarith
  have hmass_pos_real :
      0 < (ClassicalTypicality.strongTypicalMass (n := n) p δx : ℝ) :=
    lt_of_lt_of_le hprune_pos hmass_lower
  have hmass_pos : 0 < ClassicalTypicality.strongTypicalMass (n := n) p δx := by
    exact_mod_cast hmass_pos_real
  let Eout : Ensemble 𝒳 (QIT.TensorPower b n) :=
    { probs := (ClassicalTypicality.prunedStrongTypicalDistribution p δx hmass_pos).prob
      weights_sum := (ClassicalTypicality.prunedStrongTypicalDistribution
        p δx hmass_pos).sum_eq_one
      states := fun x =>
        productState fun i : Fin n =>
          (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i) }
  let σbar := (N.outputEnsemble E₀).averageState
  let scale : ℝ :=
    (HSWPackingHypothesesSpectral.stateEigenvalueDistribution σbar).strongTypicalMassScale
      n δz
  let D : ℝ := (1 - pruneε) * scale
  let P : CMatrix (QIT.TensorPower b n) :=
    HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector σbar n δz
  let Px : 𝒳 → CMatrix (QIT.TensorPower b n) := fun x =>
    conditionallyTypicalSubspaceProjector
      (fun i : Fin n =>
        (N.outputEnsemble E₀).states (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
      δc
  have hδz : 0 ≤ δz := by
    dsimp [δz]
    have hcardι : 0 ≤ (Fintype.card ι : ℝ) := by exact_mod_cast Nat.zero_le _
    have hsum : 0 ≤ δx + δc := by linarith
    exact mul_nonneg hcardι hsum
  have hscale_pos : 0 < scale := by
    dsimp [scale]
    exact (HSWPackingHypothesesSpectral.stateEigenvalueDistribution
      σbar).strongTypicalMassScale_pos n δz
  have hD_pos : 0 < D := by
    dsimp [D]
    exact mul_pos hprune_pos hscale_pos
  let H : HSWPackingHypothesesSpectral Eout δz := {
    P := P
    Px := Px
    d := (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc
    D := D
    ε := packingε
    hε_nonneg := hpackingε
    hD_pos := hD_pos
    P_posSemidef := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_posSemidef
        (N.outputEnsemble E₀).averageState n δz
    P_idempotent := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_idempotent
        (N.outputEnsemble E₀).averageState n δz
    P_le_one := by
      dsimp [P, σbar]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_le_one
        (N.outputEnsemble E₀).averageState n δz
    Px_projector := by
      intro x
      dsimp [Px]
      exact ⟨
        conditionallyTypicalSubspaceProjector_posSemidef
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_idempotent
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc,
        conditionallyTypicalSubspaceProjector_le_one
          (fun i : Fin n =>
            (N.outputEnsemble E₀).states
              (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) δc⟩
    h1 := by
      intro x
      dsimp [P, Eout, σbar, p, δz]
      exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_product_capture_of_strongTypical
        (N.outputEnsemble E₀)
        (ClassicalTypicality.StrongTypicalWord.codeword
          (N.outputEnsemble E₀).indexDistribution δx x)
        hn_pos hδx.le hδc
        (ClassicalTypicality.StrongTypicalWord.strongTypical
          (N.outputEnsemble E₀).indexDistribution δx x)
        hlarge
    h2 := by
      intro x
      dsimp [Px, Eout]
      have hown := conditionallyTypicalSubspaceProjector_ownCapture_trace
        (states := fun i : Fin n =>
          (N.outputEnsemble E₀).states
            (ClassicalTypicality.StrongTypicalWord.codeword p δx x i))
        (δ := δc) hn_pos hδc
      have hkey :
          1 - packingε ≤
            1 - conditionalLogDeviationSecondMoment
                (fun i : Fin n =>
                  (N.outputEnsemble E₀).states
                    (ClassicalTypicality.StrongTypicalWord.codeword p δx x i)) /
              ((n : ℝ) * δc) ^ 2 := by
        linarith [hmoment x]
      exact le_trans hkey hown
    h3 := by
      intro x
      dsimp [Px]
      rw [conditionallyTypicalSubspaceProjector_trace_re_eq_dimension]
      exact conditionallyTypicalSubspaceProjector_dim_le_strongTypicalDimensionEnvelope
        (E := N.outputEnsemble E₀)
        (codeword := ClassicalTypicality.StrongTypicalWord.codeword p δx x)
        hn_pos hδx.le hδc
        (ClassicalTypicality.StrongTypicalWord.strongTypical p δx x)
    h4 := by
      have hσbar :
          σbar.matrix =
            ∑ j, (p.prob j) • ((N.outputEnsemble E₀).states j).matrix := by
        dsimp [σbar, p, Ensemble.indexDistribution]
        rfl
      have hpruned :
          Eout.averageState.matrix ≤ ((1 - pruneε)⁻¹ : ℝ) • (σbar.tensorPower n).matrix := by
        exact pack4_prunedStrongTypicalReduction
          (fun j => (N.outputEnsemble E₀).states j) p σbar hσbar hmass_pos
          hmass_lower hprune Eout (by intro x; rfl) (by intro x; rfl)
      have hprojected :
          P * (σbar.tensorPower n).matrix * P ≤ ((scale : ℝ)⁻¹) • P := by
        dsimp [P, σbar, scale]
        exact HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_projectedTensorPower_le_strongTypicalMassScale
          (N.outputEnsemble E₀).averageState hn_pos hδz
      have hP_herm : P.IsHermitian := by
        dsimp [P, σbar]
        exact (HSWPackingHypothesesSpectral.sourceTypicalSubspaceProjector_posSemidef
          (N.outputEnsemble E₀).averageState n δz).isHermitian
      have hinv_nonneg : 0 ≤ (1 - pruneε)⁻¹ := inv_nonneg.mpr hprune_pos.le
      have hbase :
          P * Eout.averageState.matrix * P ≤
            (((1 - pruneε)⁻¹ : ℝ) * ((scale : ℝ)⁻¹)) • P :=
        cMatrix_projector_mul_mul_le_smul_of_le_of_projected_le
          hP_herm hinv_nonneg hpruned hprojected
      have hscalar :
          (((1 - pruneε)⁻¹ : ℝ) * ((scale : ℝ)⁻¹)) = ((D : ℝ)⁻¹) := by
        dsimp [D]
        field_simp [ne_of_gt hprune_pos, ne_of_gt hscale_pos]
      simpa [hscalar] using hbase }
  refine codeWithSignals_of_packing (M := M) N E₀.states Eout H
    (ClassicalTypicality.StrongTypicalWord.codeword p δx) ?_ hn_pos hinv_le hε hrate ?_
  · intro x
    dsimp [Eout, p]
    exact Channel.tensorPower_applyState_productState N n
      (fun i : Fin n => E₀.states
        (ClassicalTypicality.StrongTypicalWord.codeword
          (N.outputEnsemble E₀).indexDistribution δx x i))
  · have hratio_nonneg :
        0 ≤
          (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
            ((1 - pruneε) * scale) := by
      have hd_nonneg :
          0 ≤ (N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc := by
        dsimp [Ensemble.strongTypicalDimensionEnvelope]
        exact (Real.rpow_pos_of_pos (by norm_num : (0 : ℝ) < 2) _).le
      exact div_nonneg hd_nonneg hD_pos.le
    have hcross_actual :
        4 * ((Fintype.card M : ℝ) - 1) *
            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
              ((1 - pruneε) * scale)) ≤
          4 * Real.rpow 2 ((n : ℝ) * (N.hswHolevoRate E₀ - δ / 2)) *
            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
              ((1 - pruneε) * scale)) := by
      have hmul := mul_le_mul_of_nonneg_right hcard hratio_nonneg
      nlinarith
    have hcross :
        4 * ((Fintype.card M : ℝ) - 1) *
            ((N.outputEnsemble E₀).strongTypicalDimensionEnvelope n δx δc /
              ((1 - pruneε) * scale)) ≤ ε / 4 := by
      exact le_trans hcross_actual hcrossCap
    have htotal := hswPackingError_le_of_self_cross_bound hself hcross
    dsimp [H, D, scale, σbar, δz]
    exact htotal

/-- The fixed-ensemble HSW theorem, including exact product encoder membership
and maximal error for every sufficiently large block length. -/
theorem fixedEnsemble_product_code_achievable
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (N : Channel a b) (E₀ : Ensemble ι a) :
    IsAchievableWithSignals N E₀.states (N.hswHolevoRate E₀) := by
  apply achievableWithSignals_of_finiteMassBounds N E₀
  intro δ hδ ε hε
  obtain ⟨δx, δc, hδx, hδc, hcrossExp⟩ :=
    exists_hsw_crossExponentBound_slacks (E := N.outputEnsemble E₀) hδ
  obtain ⟨Ncross, hNcross⟩ :=
    exists_nat_const_mul_rpow_two_neg_mul_le (A := (8 : ℝ)) (c := δ / 4)
      (η := ε / 4) (by positivity) (by positivity)
  obtain ⟨Nsmall, hNsmall⟩ :=
    exists_nat_real_div_mul_sq_le (C := (1 : ℝ)) (η := δ / 2) (δ := (1 : ℝ))
      (by positivity) (by norm_num)
  obtain ⟨Nprune, hNprune⟩ :=
    exists_nat_real_div_mul_sq_le (C := (Fintype.card ι : ℝ)) (η := (1 / 2 : ℝ))
      (δ := δx) (by norm_num) hδx
  obtain ⟨Ncard, hNcard⟩ :=
    exists_nat_real_div_mul_sq_le
      (C := (Fintype.card ι : ℝ) * (Fintype.card b : ℝ))
      (η := hswSelfPackingEpsilon ε) (δ := δc)
      (hswSelfPackingEpsilon_pos hε) hδc
  obtain ⟨Nmoment, hNmoment⟩ :=
    exists_nat_real_div_mul_sq_le
      (C := (N.outputEnsemble E₀).logDeviationSecondMomentEnvelope)
      (η := hswSelfPackingEpsilon ε) (δ := δc)
      (hswSelfPackingEpsilon_pos hε) hδc
  let N0 := max 1 (max Nsmall (max Nprune (max Ncard (max Nmoment Ncross))))
  refine ⟨N0, ?_⟩
  intro n hn
  have hbounds : 0 < n ∧ Nsmall ≤ n ∧ Nprune ≤ n ∧ Ncard ≤ n ∧
      Nmoment ≤ n ∧ Ncross ≤ n := by
    dsimp [N0] at hn
    omega
  obtain ⟨hn_pos, hnsmall, hnprune, hncard, hnmoment, hncross⟩ := hbounds
  refine ⟨hn_pos, by simpa using hNsmall n hnsmall, ?_⟩
  intro M hMF hMD hMne _ _
  refine ⟨δx, δc, hswSelfPackingEpsilon ε, 1 / 2, hδx, hδc,
    hswSelfPackingEpsilon_nonneg hε, by norm_num,
    hNprune n hnprune, hNcard n hncard, ?_,
    hswSelfPackingEpsilon_self_bound hε, ?_⟩
  · intro x
    exact (N.outputEnsemble E₀).conditionalLogDeviationSecondMoment_codeword_ratio_le_of_envelope
      (ClassicalTypicality.StrongTypicalWord.codeword
        (N.outputEnsemble E₀).indexDistribution δx x)
      hn_pos hδc (hNmoment n hnmoment)
  · exact (hcrossExp n).trans (hNcross n hncross)

end
end AmplitudeDamping
