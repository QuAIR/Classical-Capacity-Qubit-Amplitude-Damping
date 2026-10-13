import AmplitudeDamping.ChannelChoi
import AmplitudeDamping.ConcurrenceFlatRoof

/-!
# Channel entanglement of formation

This is the supremum of the state entanglement of formation after a channel
acts on one half of a pure input with an input-sized reference. It is not a
Choi-state definition. The Bell-input lower bound is proved from that
optimization. The qubit-channel identity is proved using the concurrence
convex-roof formula and exact local-filter factorization
(Berta--Brandão--Christandl--Wehner, Eqs. (76)--(77)).
-/

namespace AmplitudeDamping
open QIT
open scoped BigOperators NNReal
noncomputable section
universe u v
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A dimension bound for the finite-decomposition state roof. -/
theorem entanglementOfFormation_le_log_card (rho : State (a × b)) :
    entanglementOfFormation rho ≤ log2 (Fintype.card a) := by
  let E := spectralPureDecomposition rho
  have he : E.averageState = rho := spectralPureDecomposition_averageState rho
  calc
    entanglementOfFormation rho ≤ E.entanglementCost := by
      rw [← he]
      exact entanglementOfFormation_le_entanglementCost E
    _ ≤ ∑ i, (E.probs i).toReal * log2 (Fintype.card a) := by
      exact Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left
        (State.vonNeumann_le_log_card _) (NNReal.coe_nonneg _)
    _ = log2 (Fintype.card a) := by
      rw [← Finset.sum_mul]
      have hw : ∑ i, (E.probs i).toReal = 1 := by
        exact_mod_cast E.weights_sum
      rw [hw, one_mul]

/-- Formation cost of the reference-output state for one pure test input. -/
def channelFormationAt (N : Channel a b) (psi : PureVector (a × a)) : ℝ :=
  entanglementOfFormation (((Channel.idChannel a).prod N).applyState psi.state)

/-- All pure reference-input formation values, with reference isomorphic to input. -/
def channelFormationValues (N : Channel a b) : Set ℝ :=
  Set.range (channelFormationAt N)

/-- Channel entanglement of formation, as a genuine optimization over pure inputs. -/
def channelEntanglementOfFormation (N : Channel a b) : ℝ :=
  sSup (channelFormationValues N)

theorem channelFormationValues_bddAbove (N : Channel a b) :
    BddAbove (channelFormationValues N) := by
  refine ⟨log2 (Fintype.card a), ?_⟩
  rintro r ⟨psi, rfl⟩
  exact entanglementOfFormation_le_log_card _

theorem channelFormationValues_nonempty [Nonempty a] (N : Channel a b) :
    (channelFormationValues N).Nonempty := by
  exact ⟨_, ⟨PureVector.maximallyEntangled (Equiv.refl a), rfl⟩⟩

theorem channelFormationAt_le (N : Channel a b) (psi : PureVector (a × a)) :
    channelFormationAt N psi ≤ channelEntanglementOfFormation N := by
  exact le_csSup (channelFormationValues_bddAbove N) ⟨psi, rfl⟩

/-- Bell input witnesses the Choi-state formation lower bound. -/
theorem choi_entanglementOfFormation_le_channel [Nonempty a] (N : Channel a b) :
    entanglementOfFormation (channelChoiState N) ≤
      channelEntanglementOfFormation N := by
  exact channelFormationAt_le N (PureVector.maximallyEntangled (Equiv.refl a))

theorem channelEntanglementOfFormation_nonneg [Nonempty a] (N : Channel a b) :
    0 ≤ channelEntanglementOfFormation N :=
  (entanglementOfFormation_nonneg _).trans (choi_entanglementOfFormation_le_channel N)

/-- The qubit-channel identity, proved by `qubitChannelFormationIdentity`. -/
def QubitChannelFormationIdentity : Prop :=
  ∀ N : Channel Qubit Qubit,
    channelEntanglementOfFormation N = entanglementOfFormation (channelChoiState N)

/-- Exact formation at a pure reference input, via concurrence factorization. -/
theorem qubit_channelFormationAt_eq (N : Channel Qubit Qubit)
    (ψ : PureVector (Qubit × Qubit)) :
    channelFormationAt N ψ =
      entanglementCurve (pureConcurrence ψ * concurrence (channelChoiState N)) := by
  unfold channelFormationAt
  rw [entanglementOfFormation_eq_entanglementCurve_concurrence, concurrence_reference_channel]

/-- The Bell input maximizes formation for every qubit-to-qubit channel. -/
theorem qubit_channelFormationAt_le_choi (N : Channel Qubit Qubit)
    (ψ : PureVector (Qubit × Qubit)) :
    channelFormationAt N ψ ≤ entanglementOfFormation (channelChoiState N) := by
  rw [qubit_channelFormationAt_eq, entanglementOfFormation_eq_entanglementCurve_concurrence]
  have hp := pureConcurrence_mem_Icc ψ
  have hc := concurrence_mem_Icc (channelChoiState N)
  have hle : pureConcurrence ψ * concurrence (channelChoiState N) ≤
      concurrence (channelChoiState N) := mul_le_of_le_one_left hc.1 hp.2
  exact entanglementCurve_monotoneOn ⟨mul_nonneg hp.1 hc.1, hle.trans hc.2⟩ hc hle

/-- The original all-qubit-channel formation identity, with no external premise. -/
theorem qubitChannelFormationIdentity : QubitChannelFormationIdentity := by
  intro N
  apply le_antisymm _ (choi_entanglementOfFormation_le_channel N)
  apply csSup_le (channelFormationValues_nonempty N)
  rintro _ ⟨ψ, rfl⟩
  exact qubit_channelFormationAt_le_choi N ψ

/-- AD channel formation follows from the proved qubit identity. -/
theorem amplitudeDamping_channelEntanglementOfFormation
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    channelEntanglementOfFormation (amplitudeDamping p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  rw [qubitChannelFormationIdentity, channelChoiState_amplitudeDamping,
    choiState_entanglementOfFormation_eq_binaryEntropy_unconditional]
end
end AmplitudeDamping
