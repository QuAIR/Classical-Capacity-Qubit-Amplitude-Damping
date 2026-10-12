import AmplitudeDamping.ChannelFormationProduct
import AmplitudeDamping.CapacityAdditivity
import AmplitudeDamping.EntanglementCost

/-!
# Regularizing strongly additive channel formation

Channel formation is defined by pure reference-input optimization. All
regrouping equalities below preserve that optimization, including entangled
inputs. The regularized quantity is kept distinct from operational cost.
-/
namespace AmplitudeDamping
open QIT
open scoped BigOperators NNReal Matrix
noncomputable section
namespace FormationRegularization
variable {a b c d : Type} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

/-- Formation is invariant under independent local basis relabelings. -/
theorem formation_reindex (rho : State (a × b)) (e : a ≃ c) (f : b ≃ d) :
    entanglementOfFormation (rho.reindex (e.prodCongr f)) =
      entanglementOfFormation rho := by
  apply le_antisymm (entanglementOfFormation_reindex_le rho e f)
  have h := entanglementOfFormation_reindex_le (rho.reindex (e.prodCongr f)) e.symm f.symm
  rwa [state_reindex_reindex, prodCongr_trans_prodCongr_symm, State.reindex_refl] at h

/-- Matrix-unit transport also transports reference-output states. -/
theorem referenceOutput_reindex (N : Channel a b) (M : Channel c d)
    (e : a ≃ c) (f : b ≃ d)
    (h : ∀ i j x y, M.map (Matrix.single (e i) (e j) 1) (f x) (f y) =
      N.map (Matrix.single i j 1) x y) (rho : State (a × a)) :
    ((Channel.idChannel c).prod M).applyState (rho.reindex (e.prodCongr e)) =
      (((Channel.idChannel a).prod N).applyState rho).reindex (e.prodCongr f) := by
  apply CapacityAdditivity.applyState_reindex_of_single
  intro i j x y
  simp only [CapacityAdditivity.prod_single, Equiv.prodCongr_apply]
  simp [Channel.idChannel, MatrixMap.ofKraus, Matrix.single_apply, ite_and, h]

/-- Channel formation is unchanged by input/output basis relabeling. -/
theorem formation_eq_of_reindex (N : Channel a b) (M : Channel c d)
    (e : a ≃ c) (f : b ≃ d)
    (h : ∀ i j x y, M.map (Matrix.single (e i) (e j) 1) (f x) (f y) =
      N.map (Matrix.single i j 1) x y) :
    channelEntanglementOfFormation.{0,0} M = channelEntanglementOfFormation.{0,0} N := by
  have hp (psi : PureVector (a × a)) :
      channelFormationAt M (psi.reindex (e.prodCongr e)) = channelFormationAt N psi := by
    unfold channelFormationAt
    rw [PureVector.reindex_state, referenceOutput_reindex N M e f h, formation_reindex]
  unfold channelEntanglementOfFormation channelFormationValues
  congr 1
  ext r
  constructor
  · rintro ⟨psi, rfl⟩
    refine ⟨psi.reindex (e.symm.prodCongr e.symm), ?_⟩
    have hinv : (psi.reindex (e.symm.prodCongr e.symm)).reindex (e.prodCongr e) = psi := by
      cases psi
      simp only [PureVector.reindex, Equiv.prodCongr_symm, Equiv.prodCongr_apply,
        Equiv.symm_symm, PureVector.mk.injEq]
      funext ⟨i,j⟩
      simp
    rw [← hp, hinv]
  · rintro ⟨psi, rfl⟩
    exact ⟨psi.reindex (e.prodCongr e), hp psi⟩
/-- channel formation is independent of parenthesization of three factors. -/
theorem formation_assoc {s t : Type} [Fintype s] [DecidableEq s]
    [Fintype t] [DecidableEq t]
    (N : Channel a b) (M : Channel c d) (P : Channel s t) :
    channelEntanglementOfFormation.{0,0} ((N.prod M).prod P) =
      channelEntanglementOfFormation.{0,0} (N.prod (M.prod P)) := by
  symm
  apply formation_eq_of_reindex _ _ (Equiv.prodAssoc a c s) (Equiv.prodAssoc b d t)
  intro i j x y
  simp only [CapacityAdditivity.prod_single, Equiv.prodAssoc_apply]
  ring


/-- Regrouping tensor powers preserves the entire channel's formation,
including ensembles with entangled inputs. -/
theorem formation_tensorPower_prod (N : Channel a b) (M : Channel c d) (n : ℕ) :
    channelEntanglementOfFormation.{0,0} ((N.prod M).tensorPower n) =
      channelEntanglementOfFormation.{0,0} ((N.tensorPower n).prod (M.tensorPower n)) := by
  symm
  apply formation_eq_of_reindex _ _ (CapacityAdditivity.powerProdEquiv a c n) (CapacityAdditivity.powerProdEquiv b d n)
  intro i j x y
  rw [CapacityAdditivity.prod_single]
  simp only [Channel.tensorPower_map_single_apply]
  simp only [CapacityAdditivity.powerProdEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.coe_fn_mk, Prod.map_fst, Prod.map_snd, Equiv.apply_symm_apply]
  simp_rw [CapacityAdditivity.prod_single]
  rw [Finset.prod_mul_distrib]

/-- The unit channel contributes no channel formation to a product. -/
theorem formation_unit_prod (M : Channel c d) :
    channelEntanglementOfFormation.{0,0} (Channel.unit.prod M) =
      channelEntanglementOfFormation.{0,0} M := by
  symm
  apply formation_eq_of_reindex _ _ (Equiv.punitProd c) (Equiv.punitProd d)
  intro i j x y
  rw [CapacityAdditivity.prod_single]
  rcases i with ⟨⟨⟩, i⟩
  rcases j with ⟨⟨⟩, j⟩
  rcases x with ⟨⟨⟩, x⟩
  rcases y with ⟨⟨⟩, y⟩
  simp [Channel.unit, MatrixMap.unit, Matrix.single]
  rfl


/-- Strong additivity quantifies over arbitrary finite partner channels. -/
def StrongFormationAdditive (N : Channel a b) : Prop :=
  ∀ {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] (M : Channel c d),
    channelEntanglementOfFormation.{0,0} (N.prod M) =
      channelEntanglementOfFormation.{0,0} N + channelEntanglementOfFormation.{0,0} M

/-- The trivial channel has zero formation. -/
theorem formation_unit : channelEntanglementOfFormation.{0,0} Channel.unit = 0 := by
  apply le_antisymm _ (channelEntanglementOfFormation_nonneg _)
  apply csSup_le (channelFormationValues_nonempty _)
  rintro r ⟨psi, rfl⟩
  have h := entanglementOfFormation_le_log_card
    (((Channel.idChannel PUnit).prod Channel.unit).applyState psi.state)
  simpa [channelFormationAt, log2] using h

/-- Peel all copies of the strongly additive channel, leaving its arbitrary
partner untouched. -/
theorem formation_tensorPower_prod_eq [Nonempty a] [Nonempty c]
    (N : Channel a b) (hN : StrongFormationAdditive N) (M : Channel c d) (n : ℕ) :
    channelEntanglementOfFormation.{0,0} ((N.tensorPower n).prod M) =
      (n : ℝ) * channelEntanglementOfFormation.{0,0} N +
        channelEntanglementOfFormation.{0,0} M := by
  induction n with
  | zero =>
    simpa only [Channel.tensorPower_zero, Nat.cast_zero, zero_mul, zero_add] using
      formation_unit_prod M
  | succ n ih =>
    letI : Nonempty (TensorPower a n) := tensorPower_nonempty_of_nonempty n
    rw [Channel.tensorPower_succ]
    trans channelEntanglementOfFormation.{0,0} (N.prod ((N.tensorPower n).prod M))
    · exact formation_assoc N (N.tensorPower n) M
    trans channelEntanglementOfFormation.{0,0} N +
      channelEntanglementOfFormation.{0,0} ((N.tensorPower n).prod M)
    · exact hN _
    rw [ih]
    push_cast
    ring

/-- Exact formation of a distinguished channel's tensor powers. -/
theorem formation_tensorPower [Nonempty a]
    (N : Channel a b) (hN : StrongFormationAdditive N) (n : ℕ) :
    channelEntanglementOfFormation.{0,0} (N.tensorPower n) =
      (n : ℝ) * channelEntanglementOfFormation.{0,0} N := by
  induction n with
  | zero => simpa only [Channel.tensorPower_zero, Nat.cast_zero, zero_mul] using formation_unit
  | succ n ih =>
    letI : Nonempty (TensorPower a n) := tensorPower_nonempty_of_nonempty n
    rw [Channel.tensorPower_succ]
    trans channelEntanglementOfFormation N + channelEntanglementOfFormation (N.tensorPower n)
    · exact hN _
    rw [ih, Nat.cast_succ]
    ring

/-- Rates used to regularize channel formation. -/
def formationRates (N : Channel a b) : Set ℝ :=
  {r | ∃ n : ℕ, 0 < n ∧ r = channelEntanglementOfFormation.{0,0} (N.tensorPower n) / n}

/-- Regularized formation; its operational identification is a separate theorem. -/
def regularizedFormation (N : Channel a b) : ℝ := sInf (formationRates N)

theorem formationRates_nonempty (N : Channel a b) : (formationRates N).Nonempty :=
  ⟨_, 1, Nat.one_pos, rfl⟩

theorem formationRates_bddBelow [Nonempty a] (N : Channel a b) :
    BddBelow (formationRates N) := by
  refine ⟨0, ?_⟩
  rintro r ⟨n, hn, rfl⟩
  letI : Nonempty (TensorPower a n) := tensorPower_nonempty_of_nonempty n
  exact div_nonneg (channelEntanglementOfFormation_nonneg _) (Nat.cast_nonneg _)

/-- Strong formation additivity collapses the regularization. -/
theorem regularizedFormation_eq [Nonempty a]
    (N : Channel a b) (hN : StrongFormationAdditive N) :
    regularizedFormation N = channelEntanglementOfFormation.{0,0} N := by
  have hs : formationRates N = {channelEntanglementOfFormation.{0,0} N} := by
    ext r
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [formation_tensorPower N hN]
      simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']
    · intro hr
      refine ⟨1, Nat.one_pos, ?_⟩
      rw [Set.mem_singleton_iff.mp hr, formation_tensorPower N hN]
      simp
  unfold regularizedFormation
  rw [hs, csInf_singleton]

/-- The arbitrary partner retains its full regularization. -/
theorem regularizedFormation_prod_eq [Nonempty a] [Nonempty c]
    (N : Channel a b) (hN : StrongFormationAdditive N) (M : Channel c d) :
    regularizedFormation (N.prod M) =
      channelEntanglementOfFormation.{0,0} N + regularizedFormation M := by
  have hr (n : ℕ) (hn : 0 < n) :
      channelEntanglementOfFormation.{0,0} ((N.prod M).tensorPower n) / n =
        channelEntanglementOfFormation.{0,0} N +
          channelEntanglementOfFormation.{0,0} (M.tensorPower n) / n := by
    letI : Nonempty (TensorPower c n) := tensorPower_nonempty_of_nonempty n
    rw [formation_tensorPower_prod, formation_tensorPower_prod_eq N hN, add_div]
    have hn' : (n : ℝ) ≠ 0 := (Nat.cast_pos.mpr hn).ne'
    field_simp
  apply le_antisymm
  · apply (sub_le_iff_le_add').mp
    apply le_csInf (formationRates_nonempty M)
    rintro r ⟨n, hn, rfl⟩
    apply (sub_le_iff_le_add').mpr
    rw [← hr n hn]
    exact csInf_le (formationRates_bddBelow (N.prod M)) ⟨n, hn, rfl⟩
  · apply le_csInf (formationRates_nonempty (N.prod M))
    rintro r ⟨n, hn, rfl⟩
    rw [hr n hn]
    exact add_le_add_right (csInf_le (formationRates_bddBelow M) ⟨n, hn, rfl⟩) _

end FormationRegularization
end
end AmplitudeDamping
