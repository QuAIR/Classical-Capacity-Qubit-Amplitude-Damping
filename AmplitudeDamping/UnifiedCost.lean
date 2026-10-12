import AmplitudeDamping.UnifiedFormation
import AmplitudeDamping.OperationalEntanglementCost

/-! # Operational state and channel costs for the unified channel class -/
namespace AmplitudeDamping
open QIT
open scoped Matrix
noncomputable section

/-- For a product-kernel Choi state, operational channel cost, operational
Choi-state cost, state formation and channel formation all coincide. -/
theorem unified_cost_of_productKernel
    (hqubit : QubitChannelFormationIdentity)
    (hsub : GeneralChannelFormationSubadditivity)
    (hstate : StateCostRegularization) (hparallel : ParallelCostRegularization)
    (N : Channel Qubit Qubit) (u v : Qubit → ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hk : (channelChoiState N).matrix *ᵥ (fun p => u p.1 * v p.2) = 0) :
    parallelEntanglementCost N = entanglementOfFormation (channelChoiState N) ∧
    operationalStateCost (channelChoiState N) = entanglementOfFormation (channelChoiState N) ∧
    channelEntanglementOfFormation N = entanglementOfFormation (channelChoiState N) := by
  refine ⟨?_, ?_, hqubit N⟩
  · rw [parallelEntanglementCost_eq_of_strong hparallel N
      (strongFormation_of_productKernel hqubit hsub N u v hu hv hk), hqubit]
  · rw [hstate.eq_regularized, entanglementCost_eq
      woottersKernelUpperBound_of_twoExpectations _ u v hu hv hk]

/-- The unified operational cost conclusion for a two-Kraus qubit channel. -/
theorem unified_cost_of_twoKraus
    {κ : Type*} [Fintype κ]
    (hqubit : QubitChannelFormationIdentity)
    (hsub : GeneralChannelFormationSubadditivity)
    (hstate : StateCostRegularization) (hparallel : ParallelCostRegularization)
    (N : Channel Qubit Qubit) (K : κ → Matrix Qubit Qubit ℂ)
    (hN : N.map = MatrixMap.ofKraus K) (hcard : Fintype.card κ ≤ 2) :
    parallelEntanglementCost N = entanglementOfFormation (channelChoiState N) ∧
    operationalStateCost (channelChoiState N) = entanglementOfFormation (channelChoiState N) ∧
    channelEntanglementOfFormation N = entanglementOfFormation (channelChoiState N) := by
  obtain ⟨u,v,hu,hv,hk⟩ := channelChoiState_product_kernel_of_twoKraus N K hN hcard
  exact unified_cost_of_productKernel hqubit hsub hstate hparallel N u v hu hv hk

/-- Operational parallel cost is strongly additive for two-Kraus channels. -/
theorem twoKraus_parallelCost_prod_eq
    {κ : Type*} [Fintype κ]
    (hqubit : QubitChannelFormationIdentity)
    (hsub : GeneralChannelFormationSubadditivity)
    (hparallel : ParallelCostRegularization)
    (N : Channel Qubit Qubit) (K : κ → Matrix Qubit Qubit ℂ)
    (hN : N.map = MatrixMap.ofKraus K) (hcard : Fintype.card κ ≤ 2)
    {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] [Nonempty d] (M : Channel c d) :
    parallelEntanglementCost (N.prod M) =
      parallelEntanglementCost N + parallelEntanglementCost M :=
  parallelEntanglementCost_prod_eq_of_strong hparallel N
    (strongFormation_of_twoKraus hqubit hsub N K hN hcard) M

/-- The amplitude-damping cost formula uses operationally defined costs. -/
theorem amplitudeDamping_operational_costs
    (hqubit : QubitChannelFormationIdentity)
    (hsub : GeneralChannelFormationSubadditivity)
    (hstate : StateCostRegularization) (hparallel : ParallelCostRegularization)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    parallelEntanglementCost (amplitudeDamping p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) ∧
    operationalStateCost (channelChoiState (amplitudeDamping p hp0 hp1)) =
      binaryEntropy ((1 + Real.sqrt p) / 2) ∧
    entanglementOfFormation (channelChoiState (amplitudeDamping p hp0 hp1)) =
      binaryEntropy ((1 + Real.sqrt p) / 2) ∧
    channelEntanglementOfFormation (amplitudeDamping p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  refine ⟨?_, ?_, ?_, amplitudeDamping_channelEntanglementOfFormation hqubit p hp0 hp1⟩
  · rw [parallelEntanglementCost_eq_of_strong hparallel _
      (amplitudeDamping_strongFormation hqubit hsub p hp0 hp1),
      amplitudeDamping_channelEntanglementOfFormation hqubit]
  · rw [hstate.eq_regularized, channelChoiState_amplitudeDamping]
    exact choiState_entanglementCost
      woottersKernelUpperBound_of_twoExpectations p hp0 hp1
  · rw [channelChoiState_amplitudeDamping,
      choiState_entanglementOfFormation_eq_binaryEntropy_unconditional]

/-- AD is operationally cost-additive with an arbitrary finite partner. -/
theorem amplitudeDamping_parallelCost_prod_eq
    (hqubit : QubitChannelFormationIdentity)
    (hsub : GeneralChannelFormationSubadditivity)
    (hparallel : ParallelCostRegularization)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] [Nonempty d] (M : Channel c d) :
    parallelEntanglementCost ((amplitudeDamping p hp0 hp1).prod M) =
      parallelEntanglementCost (amplitudeDamping p hp0 hp1) + parallelEntanglementCost M :=
  parallelEntanglementCost_prod_eq_of_strong hparallel _
    (amplitudeDamping_strongFormation hqubit hsub p hp0 hp1) M
end
end AmplitudeDamping
