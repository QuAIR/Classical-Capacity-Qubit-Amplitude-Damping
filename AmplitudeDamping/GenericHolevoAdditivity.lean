import AmplitudeDamping.CapacityAdditivity

/-! # Arbitrary-dimensional Holevo additivity from output-roof SSA

All channel systems are arbitrary finite types. The type universe is the
small-system universe used by the operational HSW capacity API; there is no
bound on their finite cardinalities.
-/
namespace AmplitudeDamping
open QIT
noncomputable section
variable {a b c d : Type} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

/-- Product ensembles provide the Holevo lower bound for arbitrary channels. -/
theorem generic_holevoInformation_prod_ge [Nonempty a] [Nonempty c]
    (N : Channel a b) (M : Channel c d) :
    Channel.holevoInformation.{0,0,0} N + Channel.holevoInformation.{0,0,0} M ≤
      Channel.holevoInformation.{0,0,0} (N.prod M) := by
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
      Channel.holevoInformation.{0,0,0} (N.prod M) :=
    ensembleHolevoAfter_le_holevoInformation (N.prod M) (E.prod F)
  have hadd := ensembleHolevoAfter_prod_prod_eq N M E F
  change (N.prod M).hswHolevoRate (E.prod F) =
    N.hswHolevoRate E + M.hswHolevoRate F at hadd
  linarith

/-- The output-roof inequality implies Holevo additivity without restrictions
on either channel's input or output dimension. -/
theorem generic_holevoInformation_prod_eq [Nonempty a] [Nonempty c]
    (N : Channel a b) (M : Channel c d)
    (hs : ∀ τ : State (a × c),
      outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB ≤
        outputEntropyRoof (N.prod M) τ) :
    Channel.holevoInformation.{0,0,0} (N.prod M) =
      Channel.holevoInformation.{0,0,0} N + Channel.holevoInformation.{0,0,0} M := by
  apply le_antisymm
  · unfold Channel.holevoInformation
    apply csSup_le (N.prod M).holevoInformationValues_nonempty
    rintro r ⟨ι, hιF, hιD, E, rfl⟩
    letI : Fintype ι := hιF
    letI : DecidableEq ι := hιD
    have hconv := ensembleHolevoAfter_prod_le
      (outputEntropyRoof (N.prod M)) (outputEntropyRoof N)
      (outputEntropyRoof M) N M E
      (outputEntropyRoof_isOutputEntropyRoof (N.prod M)) hs
    have hleft := fixedInputHolevo_le_holevoInformation N E.averageState.marginalA
    have hright := fixedInputHolevo_le_holevoInformation M E.averageState.marginalB
    change ensembleHolevoAfter (N.prod M) E ≤ _
    unfold Channel.holevoInformation at hleft hright
    linarith
  · exact generic_holevoInformation_prod_ge N M

end
end AmplitudeDamping
