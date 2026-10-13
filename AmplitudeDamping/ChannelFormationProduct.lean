import AmplitudeDamping.ChannelFormation
import AmplitudeDamping.EntanglementAdditivity

/-!
# From Choi-state additivity to channel formation additivity

The product pure input used below is a Bell input for the distinguished
channel and an arbitrary pure reference-input state for its partner.
Consequently no existence of an optimizing partner input is assumed.
-/

namespace AmplitudeDamping
open QIT
open scoped BigOperators NNReal Matrix
noncomputable section
universe u v w x
variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- Entrywise channel action with an untouched reference system. -/
theorem referenceOutput_matrix {r : Type*} [Fintype r] [DecidableEq r]
    (N : Channel a b) (rho : State (r × a)) (i k : r) (j l : b) :
    (((Channel.idChannel r).prod N).applyState rho).matrix (i,j) (k,l) =
      ∑ s, ∑ t, rho.matrix (i,s) (k,t) * N.map (Matrix.single s t 1) j l := by
  simp [Channel.applyState, Channel.prod, MatrixMap.kron,
    Channel.idChannel, MatrixMap.ofKraus, Matrix.single_apply, ite_and]

/-- Regrouping independent reference-input states commutes with the channels. -/
theorem referenceOutput_prod (N : Channel a b) (M : Channel c d)
    (rho : State (a × a)) (sigma : State (c × c)) :
    ((Channel.idChannel (a × c)).prod (N.prod M)).applyState
        ((rho.prod sigma).reindex prodReassoc) =
      ((((Channel.idChannel a).prod N).applyState rho).prod
        (((Channel.idChannel c).prod M).applyState sigma)).reindex prodReassoc := by
  apply State.ext
  ext ⟨⟨i,k⟩,⟨j,l⟩⟩ ⟨⟨i',k'⟩,⟨j',l'⟩⟩
  have hprod (s t : a × c) :
      (N.prod M).map (Matrix.single s t 1) (j,l) (j',l') =
        N.map (Matrix.single s.1 t.1 1) j j' *
          M.map (Matrix.single s.2 t.2 1) l l' := by
    rw [single_prod_eq_kronecker_single, Channel.prod_map_kronecker]
    rfl
  rw [referenceOutput_matrix]
  simp only [State.reindex_matrix, Matrix.submatrix_apply, prodReassoc_symm_apply,
    State.prod, Fintype.sum_prod_type, hprod]
  simp only [Matrix.kronecker, Matrix.kroneckerMap_apply,
    referenceOutput_matrix]
  simp_rw [Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro w _
  ring

/-- The statement of general channel-formation subadditivity.
`UniformKraus.lean` proves it from the explicit classical uniform-representation
interface; it is not asserted here. -/
def ChannelFormationSubadditivity : Prop :=
  ∀ (N : Channel a b) (M : Channel c d),
    channelEntanglementOfFormation (N.prod M) ≤
      channelEntanglementOfFormation N + channelEntanglementOfFormation M

/-- Strong state additivity supplies the nontrivial channel lower bound. -/
theorem channelFormation_prod_ge_of_choi
    (N : Channel Qubit Qubit) (M : Channel c d) [Nonempty c]
    (hbell : channelEntanglementOfFormation N =
      entanglementOfFormation (channelChoiState N))
    (hadd : ∀ sigma : State (c × d),
      entanglementOfFormation (((channelChoiState N).prod sigma).reindex prodReassoc) =
        entanglementOfFormation (channelChoiState N) + entanglementOfFormation sigma) :
    channelEntanglementOfFormation N + channelEntanglementOfFormation M ≤
      channelEntanglementOfFormation (N.prod M) := by
  suffices h : channelEntanglementOfFormation M ≤
      channelEntanglementOfFormation (N.prod M) - channelEntanglementOfFormation N by
    linarith
  apply csSup_le (channelFormationValues_nonempty M)
  rintro r ⟨psi, rfl⟩
  let bell := PureVector.maximallyEntangled (Equiv.refl Qubit)
  have hw := channelFormationAt_le (N.prod M) ((bell.prod psi).reindex prodReassoc)
  unfold channelFormationAt at hw
  rw [PureVector.reindex_state, PureVector.prod_state, referenceOutput_prod] at hw
  change entanglementOfFormation (((channelChoiState N).prod
    (((Channel.idChannel c).prod M).applyState psi.state)).reindex prodReassoc) ≤ _ at hw
  rw [hadd, ← hbell] at hw
  exact (le_sub_iff_add_le').2 hw

/-- Strong formation additivity for a qubit channel with a product-kernel
Choi state. The qubit-channel identity is proved; the subadditivity and
corner-formula premises are supplied by the main entry points. -/
theorem channelFormation_prod_eq_of_productKernel
    (hcorner : woottersKernelUpperBound)
    (hsub : ChannelFormationSubadditivity (a := Qubit) (b := Qubit)
      (c := c) (d := d))
    (N : Channel Qubit Qubit) (M : Channel c d) [Nonempty c]
    (u v : Qubit → ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hk : (channelChoiState N).matrix *ᵥ (fun p => u p.1 * v p.2) = 0) :
    channelEntanglementOfFormation (N.prod M) =
      channelEntanglementOfFormation N + channelEntanglementOfFormation M := by
  apply le_antisymm (hsub N M)
  apply channelFormation_prod_ge_of_choi N M (qubitChannelFormationIdentity N)
  intro sigma
  exact entanglementOfFormation_prod_eq hcorner (channelChoiState N) u v hu hv hk sigma

end
end AmplitudeDamping
