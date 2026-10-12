import AmplitudeDamping.ChannelChoiRank
import AmplitudeDamping.CornerFromTwoExpectations
import AmplitudeDamping.ChannelFormationRegularization

/-! # Strong formation and tensor powers for product-kernel Choi states -/
namespace AmplitudeDamping
open QIT
open scoped Matrix
noncomputable section

/-- Uniform general subadditivity across all finite-dimensional partners.
`generalChannelFormationSubadditivity_of_uniformKraus` discharges this interface. -/
def GeneralChannelFormationSubadditivity : Prop :=
  ∀ {a b c d : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
    [Fintype d] [DecidableEq d],
    ChannelFormationSubadditivity (a := a) (b := b) (c := c) (d := d)

/-- A product vector in the Choi kernel implies strong channel formation
additivity, using only the displayed classical interfaces. -/
theorem strongFormation_of_productKernel
    (hclassical : TwoExpectationDecomposition (Qubit × Qubit))
    (hqubit : QubitChannelFormationIdentity)
    (hsub : GeneralChannelFormationSubadditivity)
    (N : Channel Qubit Qubit) (u v : Qubit → ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hk : (channelChoiState N).matrix *ᵥ (fun p => u p.1 * v p.2) = 0) :
    FormationRegularization.StrongFormationAdditive N := by
  intro c d _ _ _ _ _ M
  exact channelFormation_prod_eq_of_productKernel
    (woottersKernelUpperBound_of_twoExpectations hclassical) hqubit hsub N M u v hu hv hk

/-- Rank at most two suffices for every finite partner channel. -/
theorem strongFormation_of_twoKraus
    {κ : Type*} [Fintype κ]
    (hclassical : TwoExpectationDecomposition (Qubit × Qubit))
    (hqubit : QubitChannelFormationIdentity)
    (hsub : GeneralChannelFormationSubadditivity)
    (N : Channel Qubit Qubit) (K : κ → Matrix Qubit Qubit ℂ)
    (hN : N.map = MatrixMap.ofKraus K) (hcard : Fintype.card κ ≤ 2) :
    FormationRegularization.StrongFormationAdditive N := by
  obtain ⟨u,v,hu,hv,hk⟩ := channelChoiState_product_kernel_of_twoKraus N K hN hcard
  exact strongFormation_of_productKernel hclassical hqubit hsub N u v hu hv hk

/-- Both independently defined tensor-power formation quantities coincide. -/
theorem formation_powers_of_productKernel
    (hclassical : TwoExpectationDecomposition (Qubit × Qubit))
    (hqubit : QubitChannelFormationIdentity)
    (hsub : GeneralChannelFormationSubadditivity)
    (N : Channel Qubit Qubit) (u v : Qubit → ℂ)
    (hu : u ≠ 0) (hv : v ≠ 0)
    (hk : (channelChoiState N).matrix *ᵥ (fun p => u p.1 * v p.2) = 0) (n : ℕ) :
    channelEntanglementOfFormation (N.tensorPower n) =
      n * entanglementOfFormation (channelChoiState N) ∧
    entanglementOfFormation ((channelChoiState N).tensorPowerBipartite n) =
      n * entanglementOfFormation (channelChoiState N) := by
  constructor
  · rw [FormationRegularization.formation_tensorPower N
      (strongFormation_of_productKernel hclassical hqubit hsub N u v hu hv hk), hqubit]
  · exact entanglementOfFormation_tensorPowerBipartite_eq
      (woottersKernelUpperBound_of_twoExpectations hclassical) _ u v hu hv hk n

/-- AD has strong channel formation additivity, including its endpoints. -/
theorem amplitudeDamping_strongFormation
    (hclassical : TwoExpectationDecomposition (Qubit × Qubit))
    (hqubit : QubitChannelFormationIdentity)
    (hsub : GeneralChannelFormationSubadditivity)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FormationRegularization.StrongFormationAdditive (amplitudeDamping p hp0 hp1) := by
  apply strongFormation_of_productKernel hclassical hqubit hsub _
    qubitKet0 qubitKet1 qubitKet0_ne_zero qubitKet1_ne_zero
  rw [channelChoiState_amplitudeDamping]
  exact choiState_matrix_mulVec_qubitKet0_qubitKet1 p hp0 hp1

/-- Exact AD channel and Choi-state formation at every block length. -/
theorem amplitudeDamping_formation_powers
    (hclassical : TwoExpectationDecomposition (Qubit × Qubit))
    (hqubit : QubitChannelFormationIdentity)
    (hsub : GeneralChannelFormationSubadditivity)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    channelEntanglementOfFormation ((amplitudeDamping p hp0 hp1).tensorPower n) =
      n * binaryEntropy ((1 + Real.sqrt p) / 2) ∧
    entanglementOfFormation
      ((channelChoiState (amplitudeDamping p hp0 hp1)).tensorPowerBipartite n) =
      n * binaryEntropy ((1 + Real.sqrt p) / 2) := by
  constructor
  · rw [FormationRegularization.formation_tensorPower _
      (amplitudeDamping_strongFormation hclassical hqubit hsub p hp0 hp1),
      amplitudeDamping_channelEntanglementOfFormation hqubit]
  · rw [channelChoiState_amplitudeDamping]
    exact choiState_entanglementOfFormation_tensorPowerBipartite
      (woottersKernelUpperBound_of_twoExpectations hclassical) p hp0 hp1 n
end
end AmplitudeDamping
