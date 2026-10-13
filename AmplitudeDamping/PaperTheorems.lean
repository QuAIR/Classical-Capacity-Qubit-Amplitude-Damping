import AmplitudeDamping.SupportConsequences
import AmplitudeDamping.PureOutputChoi
import AmplitudeDamping.ADDirectCost
import AmplitudeDamping.ProductSignalCoding

/-!
# Main manuscript interfaces with classical hypotheses made explicit

These entry points discharge the temporary general-subadditivity premise
using the proved uniform-Kraus application. In particular, no manuscript
additivity result is taken as a premise. The AD formation formula does not
require the general qubit-channel/Choi identity, which is also proved.
-/
namespace AmplitudeDamping
open QIT
open scoped Matrix
noncomputable section

/-- The classical two-expectation theorem in every finite dimension. -/
def GeneralTwoExpectationDecomposition : Prop :=
  ∀ (a : Type) [Fintype a] [DecidableEq a], TwoExpectationDecomposition a

/-- The two-expectation theorem is available in every finite dimension. -/
theorem generalTwoExpectationDecomposition : GeneralTwoExpectationDecomposition := by
  intro a _ _
  exact twoExpectationDecomposition a

namespace Paper

/-- The general support criterion also identifies the operational state cost. -/
theorem supported_state_cost
    {a b : Type} [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (hstate : StateCostRegularization)
    (rho : State ((a ⊕ Unit) × (Unit ⊕ b))) (hs : HasSingleExcitationSupport rho) :
    operationalStateCost rho = entanglementOfFormation rho := by
  rw [hstate.eq_regularized, supported_regularized_entanglementCost_eq rho hs]

/-- All four arbitrary-partner additivity identities for a pure-output qubit
channel. The partner's own regularization is unrestricted. -/
theorem pure_output_additivity
    (hparallel : ParallelCostRegularization)
    (N : Channel Qubit Qubit) (hpure : HasPureQubitOutput N)
    {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] [Nonempty d] (M : Channel c d) :
    Channel.holevoInformation.{0,0,0} (N.prod M) =
      Channel.holevoInformation.{0,0,0} N + Channel.holevoInformation.{0,0,0} M ∧
    Channel.classicalCapacity.{0,0,0} (N.prod M) =
      Channel.classicalCapacity.{0,0,0} N + Channel.classicalCapacity.{0,0,0} M ∧
    channelEntanglementOfFormation (N.prod M) =
      channelEntanglementOfFormation N + channelEntanglementOfFormation M ∧
    parallelEntanglementCost (N.prod M) =
      parallelEntanglementCost N + parallelEntanglementCost M := by
  have hf : FormationRegularization.StrongFormationAdditive N := pure_output_strongFormation
    (generalChannelFormationSubadditivity_of_uniformKraus) N hpure
  exact ⟨pure_output_strongHolevoAdditive N hpure M,
    pure_output_classicalCapacity_prod_eq N hpure M,
    hf M, parallelEntanglementCost_prod_eq_of_strong hparallel N hf M⟩

/-- Own capacity, state/channel cost and all finite-copy identities for the
pure-output class, with standard regularization theorems kept explicit. -/
theorem pure_output_single_letter_and_powers
    (hstate : StateCostRegularization) (hparallel : ParallelCostRegularization)
    (N : Channel Qubit Qubit) (hpure : HasPureQubitOutput N) :
    Channel.classicalCapacity.{0,0,0} N = Channel.holevoInformation.{0,0,0} N ∧
    parallelEntanglementCost N = entanglementOfFormation (channelChoiState N) ∧
    operationalStateCost (channelChoiState N) = entanglementOfFormation (channelChoiState N) ∧
    channelEntanglementOfFormation N = entanglementOfFormation (channelChoiState N) ∧
    ∀ n : ℕ,
      channelEntanglementOfFormation (N.tensorPower n) =
        n * entanglementOfFormation (channelChoiState N) ∧
      entanglementOfFormation ((channelChoiState N).tensorPowerBipartite n) =
        n * entanglementOfFormation (channelChoiState N) := by
  obtain ⟨u,v,hu,hv,hk⟩ := pure_output_has_choi_product_kernel N hpure
  have hsub : GeneralChannelFormationSubadditivity := generalChannelFormationSubadditivity_of_uniformKraus
  obtain ⟨hp,hs,hq⟩ := unified_cost_of_productKernel hsub
    hstate hparallel N u v hu hv hk
  exact ⟨pure_output_classicalCapacity_eq_holevoInformation N hpure,
    hp,hs,hq,fun n => formation_powers_of_productKernel hsub
      N u v hu hv hk n⟩

/-- AD strong formation additivity uses its direct binary-instrument
certificate, so the general qubit-channel identity is unnecessary here. -/
theorem amplitudeDamping_strongFormation
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FormationRegularization.StrongFormationAdditive (amplitudeDamping p hp0 hp1) := by
  intro c d _ _ _ _ _ M
  apply le_antisymm (generalChannelFormationSubadditivity_of_uniformKraus _ _)
  apply channelFormation_prod_ge_of_choi _ M
  · rw [amplitudeDamping_channelEntanglementOfFormation_unconditional,
      channelChoiState_amplitudeDamping,
      choiState_entanglementOfFormation_eq_binaryEntropy_unconditional]
  · intro sigma
    rw [channelChoiState_amplitudeDamping]
    exact entanglementOfFormation_prod_eq
      woottersKernelUpperBound_of_twoExpectations _
      qubitKet0 qubitKet1 qubitKet0_ne_zero qubitKet1_ne_zero
      (choiState_matrix_mulVec_qubitKet0_qubitKet1 p hp0 hp1) sigma

/-- All four AD formation/cost quantities equal the explicit binary entropy,
without a general qubit-channel identity or uniform-Kraus hypothesis. -/
theorem amplitudeDamping_cost_formula
    (hstate : StateCostRegularization) (hparallel : ParallelCostRegularization)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    parallelEntanglementCost (amplitudeDamping p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) ∧
    operationalStateCost (channelChoiState (amplitudeDamping p hp0 hp1)) =
      binaryEntropy ((1 + Real.sqrt p) / 2) ∧
    entanglementOfFormation (channelChoiState (amplitudeDamping p hp0 hp1)) =
      binaryEntropy ((1 + Real.sqrt p) / 2) ∧
    channelEntanglementOfFormation (amplitudeDamping p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) :=
  amplitudeDamping_operational_costs_direct hstate hparallel p hp0 hp1

/-- Exact finite-copy channel and Choi formation identities for AD. -/
theorem amplitudeDamping_powers
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    channelEntanglementOfFormation ((amplitudeDamping p hp0 hp1).tensorPower n) =
      n * binaryEntropy ((1 + Real.sqrt p) / 2) ∧
    entanglementOfFormation
      ((channelChoiState (amplitudeDamping p hp0 hp1)).tensorPowerBipartite n) =
      n * binaryEntropy ((1 + Real.sqrt p) / 2) :=
  amplitudeDamping_formation_powers_direct p hp0 hp1 n

/-- AD arbitrary-partner formation and operational parallel-cost additivity. -/
theorem amplitudeDamping_cost_additivity
    (hparallel : ParallelCostRegularization)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] [Nonempty d] (M : Channel c d) :
    channelEntanglementOfFormation ((amplitudeDamping p hp0 hp1).prod M) =
      channelEntanglementOfFormation (amplitudeDamping p hp0 hp1) +
        channelEntanglementOfFormation M ∧
    parallelEntanglementCost ((amplitudeDamping p hp0 hp1).prod M) =
      parallelEntanglementCost (amplitudeDamping p hp0 hp1) + parallelEntanglementCost M := by
  have h : FormationRegularization.StrongFormationAdditive (amplitudeDamping p hp0 hp1) :=
    amplitudeDamping_strongFormation p hp0 hp1
  exact ⟨h M, parallelEntanglementCost_prod_eq_of_strong hparallel _ h M⟩
/-- The two-Kraus theorem follows from the proven pure-output witness. -/
theorem twoKraus_additivity
    {κ : Type*} [Fintype κ]
    (hparallel : ParallelCostRegularization)
    (N : Channel Qubit Qubit) (K : κ → Matrix Qubit Qubit ℂ)
    (hN : N.map = MatrixMap.ofKraus K) (hcard : Fintype.card κ ≤ 2)
    {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] [Nonempty d] (M : Channel c d) :
    Channel.holevoInformation.{0,0,0} (N.prod M) =
      Channel.holevoInformation.{0,0,0} N + Channel.holevoInformation.{0,0,0} M ∧
    Channel.classicalCapacity.{0,0,0} (N.prod M) =
      Channel.classicalCapacity.{0,0,0} N + Channel.classicalCapacity.{0,0,0} M ∧
    channelEntanglementOfFormation (N.prod M) =
      channelEntanglementOfFormation N + channelEntanglementOfFormation M ∧
    parallelEntanglementCost (N.prod M) =
      parallelEntanglementCost N + parallelEntanglementCost M :=
  pure_output_additivity hparallel N
    (twoKraus_has_pure_output N K hN hcard) M

/-- Capacity, operational costs and every tensor power for at most two Kraus operators. -/
theorem twoKraus_single_letter_and_powers
    {κ : Type*} [Fintype κ]
    (hstate : StateCostRegularization) (hparallel : ParallelCostRegularization)
    (N : Channel Qubit Qubit) (K : κ → Matrix Qubit Qubit ℂ)
    (hN : N.map = MatrixMap.ofKraus K) (hcard : Fintype.card κ ≤ 2) :
    Channel.classicalCapacity.{0,0,0} N = Channel.holevoInformation.{0,0,0} N ∧
    parallelEntanglementCost N = entanglementOfFormation (channelChoiState N) ∧
    operationalStateCost (channelChoiState N) = entanglementOfFormation (channelChoiState N) ∧
    channelEntanglementOfFormation N = entanglementOfFormation (channelChoiState N) ∧
    ∀ n : ℕ,
      channelEntanglementOfFormation (N.tensorPower n) =
        n * entanglementOfFormation (channelChoiState N) ∧
      entanglementOfFormation ((channelChoiState N).tensorPowerBipartite n) =
        n * entanglementOfFormation (channelChoiState N) :=
  pure_output_single_letter_and_powers hstate hparallel N
    (twoKraus_has_pure_output N K hN hcard)

end Paper
end
end AmplitudeDamping
