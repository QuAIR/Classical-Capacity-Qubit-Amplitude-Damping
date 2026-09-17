import AmplitudeDamping.HolevoReduction
import QIT.Coding.Classical.HSWLimit

/-!
# Optimized Holevo additivity

This module passes the fixed-input and ensemble inequalities to the supremum
over all finite ensembles.  We use the universe-zero instance of Lean-QIT's
Holevo-information supremum; every decomposition constructed here has a
canonical finite index type.
-/

namespace AmplitudeDamping

open QIT

universe u v w x y z

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- Applying a product channel to a product ensemble gives the product of the
two output ensembles. -/
theorem outputEnsemble_prod
    {ι : Type y} {κ : Type z} [Fintype ι] [Fintype κ]
    (Φ : Channel a b) (Ψ : Channel c d)
    (E : Ensemble ι a) (F : Ensemble κ c) :
    outputEnsemble (Φ.prod Ψ) (E.prod F) =
      (outputEnsemble Φ E).prod (outputEnsemble Ψ F) := by
  cases E
  cases F
  simp [outputEnsemble, Ensemble.prod, Channel.applyState_prod]

/-- Holevo information is exactly additive for product ensembles sent through
a product channel. -/
theorem ensembleHolevoAfter_prod_prod_eq
    {ι : Type y} {κ : Type z} [Fintype ι] [Fintype κ]
    (Φ : Channel a b) (Ψ : Channel c d)
    (E : Ensemble ι a) (F : Ensemble κ c) :
    ensembleHolevoAfter (Φ.prod Ψ) (E.prod F) =
      ensembleHolevoAfter Φ E + ensembleHolevoAfter Ψ F := by
  unfold ensembleHolevoAfter
  rw [outputEnsemble_prod, Ensemble.prod_holevoInformation]

/-- Every concrete finite-ensemble Holevo value is at most the optimized
channel Holevo information in the same ensemble universe. -/
theorem ensembleHolevoAfter_le_holevoInformation
    {ι : Type y} [Fintype ι] [DecidableEq ι]
    (Φ : Channel a b) (E : Ensemble ι a) :
    ensembleHolevoAfter Φ E ≤ Channel.holevoInformation.{u, v, y} Φ := by
  apply le_csSup Φ.holevoInformationValues_bddAbove
  exact ⟨ι, inferInstance, inferInstance, E, rfl⟩

/-- The fixed-input expression defined by the output-entropy convex roof is
bounded by the optimized channel Holevo information. -/
theorem fixedInputHolevo_le_holevoInformation
    (Φ : Channel a b) (rho : State a) :
    fixedInputHolevo (outputEntropyRoof Φ) Φ rho ≤
      Channel.holevoInformation.{u, v, 0} Φ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, hx, hxlt⟩ := Real.lt_sInf_add_pos
    (pureOutputEntropyValues_nonempty Φ rho) hε
  rcases hx with ⟨E, hErho, rfl⟩
  have hcap := ensembleHolevoAfter_le_holevoInformation Φ E.toEnsemble
  change E.toEnsemble.averageState = rho at hErho
  rw [ensembleHolevoAfter_eq, hErho] at hcap
  have hcost : E.outputCost Φ < outputEntropyRoof Φ rho + ε := by
    simpa [outputEntropyRoof] using hxlt
  unfold fixedInputHolevo
  unfold PureDecomposition.outputCost at hcost
  linarith

/-- Strong additivity of optimized Holevo information when the left factor is
a qubit amplitude-damping channel. -/
theorem amplitudeDamping_holevoInformation_prod_eq
    [Nonempty a]
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Φ : Channel a b) :
    Channel.holevoInformation.{u, v, 0}
        ((amplitudeDamping p hp0 hp1).prod Φ) =
      Channel.holevoInformation.{0, 0, 0}
          (amplitudeDamping p hp0 hp1) +
        Channel.holevoInformation.{u, v, 0} Φ := by
  apply le_antisymm
  · unfold Channel.holevoInformation
    apply csSup_le
      (((amplitudeDamping p hp0 hp1).prod Φ).holevoInformationValues_nonempty)
    intro r hr
    rcases hr with ⟨ι, hιF, hιD, E, rfl⟩
    letI : Fintype ι := hιF
    letI : DecidableEq ι := hιD
    have hconv := amplitudeDamping_ensembleHolevoAfter_prod_le
      p hp0 hp1 Φ E
    have hleft := fixedInputHolevo_le_holevoInformation
      (amplitudeDamping p hp0 hp1) E.averageState.marginalA
    have hright := fixedInputHolevo_le_holevoInformation
      Φ E.averageState.marginalB
    change ensembleHolevoAfter ((amplitudeDamping p hp0 hp1).prod Φ) E ≤ _
    unfold Channel.holevoInformation at hleft hright
    linarith
  · apply le_of_forall_pos_le_add
    intro ε hε
    have hhalf : 0 < ε / 2 := half_pos hε
    obtain ⟨ι, hιF, hιD, E, hE⟩ :=
      Channel.exists_hswHolevoRate_gt_of_lt_holevoInformation
        (amplitudeDamping p hp0 hp1)
        ((amplitudeDamping p hp0 hp1).holevoInformationValues_nonempty)
        (sub_lt_self _ hhalf)
    obtain ⟨κ, hκF, hκD, F, hF⟩ :=
      Φ.exists_hswHolevoRate_gt_of_lt_holevoInformation
        Φ.holevoInformationValues_nonempty (sub_lt_self _ hhalf)
    letI : Fintype ι := hιF
    letI : DecidableEq ι := hιD
    letI : Fintype κ := hκF
    letI : DecidableEq κ := hκD
    have hprod :
        ((amplitudeDamping p hp0 hp1).prod Φ).hswHolevoRate (E.prod F) ≤
          Channel.holevoInformation.{u, v, 0}
            ((amplitudeDamping p hp0 hp1).prod Φ) := by
      exact ensembleHolevoAfter_le_holevoInformation
        ((amplitudeDamping p hp0 hp1).prod Φ) (E.prod F)
    have hadd := ensembleHolevoAfter_prod_prod_eq
      (amplitudeDamping p hp0 hp1) Φ E F
    change ((amplitudeDamping p hp0 hp1).prod Φ).hswHolevoRate (E.prod F) =
      (amplitudeDamping p hp0 hp1).hswHolevoRate E +
        Φ.hswHolevoRate F at hadd
    linarith

end

end AmplitudeDamping
