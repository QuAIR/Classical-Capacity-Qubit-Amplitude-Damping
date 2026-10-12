import AmplitudeDamping.CapacityBridge
import AmplitudeDamping.TwoKrausCapacity

/-! # Operational capacity additivity against an arbitrary partner

Strong single-letter Holevo additivity implies additivity of regularized,
and hence operational HSW, classical capacity. No additivity hypothesis is
placed on the partner channel: its block Holevo information remains intact.
-/

open scoped BigOperators
namespace AmplitudeDamping
open QIT
noncomputable section

namespace CapacityAdditivity

variable {a b c d : Type} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
  [Fintype d] [DecidableEq d]

/-- A change of input and output basis labels preserves Holevo information. -/
theorem holevo_eq_of_reindex (N : Channel a b) (M : Channel c d)
    (e : a ≃ c) (f : b ≃ d)
    (h : ∀ ρ : State a, M.applyState (ρ.reindex e) = (N.applyState ρ).reindex f) :
    Channel.holevoInformation.{0,0,0} M = Channel.holevoInformation.{0,0,0} N := by
  have he : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (E : Ensemble ι a),
      M.hswHolevoRate (E.reindexStates e) = N.hswHolevoRate E := by
    intro ι _ _ E
    have hout : M.outputEnsemble (E.reindexStates e) =
        (N.outputEnsemble E).reindexStates f := by
      dsimp [Channel.outputEnsemble, Ensemble.reindexStates]
      congr 1
      funext i
      exact h (E.states i)
    unfold Channel.hswHolevoRate
    rw [hout, Ensemble.reindexStates_holevoInformation]
  unfold Channel.holevoInformation
  congr 1
  ext r
  constructor
  · rintro ⟨ι, hF, hD, E, rfl⟩
    letI := hF
    letI := hD
    refine ⟨ι, hF, hD, E.reindexStates e.symm, ?_⟩
    have hinv : (E.reindexStates e.symm).reindexStates e = E := by
      cases E
      dsimp [Ensemble.reindexStates]
      congr 1
      funext i
      apply State.ext
      ext x y
      simp [State.reindex_matrix]
    simpa [hinv] using (he ι (E.reindexStates e.symm))
  · rintro ⟨ι, hF, hD, E, rfl⟩
    letI := hF
    letI := hD
    exact ⟨ι, hF, hD, E.reindexStates e, (he ι E).symm⟩

/-- Matrix-unit transport suffices for transport of arbitrary input states. -/
theorem applyState_reindex_of_single (N : Channel a b) (M : Channel c d)
    (e : a ≃ c) (f : b ≃ d)
    (h : ∀ i j x y, M.map (Matrix.single (e i) (e j) 1) (f x) (f y) =
      N.map (Matrix.single i j 1) x y) (ρ : State a) :
    M.applyState (ρ.reindex e) = (N.applyState ρ).reindex f := by
  apply State.ext
  ext x y
  change M.map (ρ.matrix.submatrix e.symm e.symm) x y =
    N.map ρ.matrix (f.symm x) (f.symm y)
  rw [MatrixMap.map_eq_sum_single, MatrixMap.map_eq_sum_single N.map]
  simp only [Matrix.sum_apply, Matrix.smul_apply, Matrix.submatrix_apply]
  symm
  apply Fintype.sum_equiv e
  intro i
  apply Fintype.sum_equiv e
  intro j
  simp only [Equiv.symm_apply_apply]
  rw [← h i j (f.symm x) (f.symm y)]
  simp

/-- Matrix coefficients of a product channel factor on matrix units. -/
theorem prod_single (N : Channel a b) (M : Channel c d)
    (i j : a × c) (x y : b × d) :
    (N.prod M).map (Matrix.single i j 1) x y =
      N.map (Matrix.single i.1 j.1 1) x.1 y.1 *
      M.map (Matrix.single i.2 j.2 1) x.2 y.2 := by
  rw [single_prod_eq_kronecker_single, Channel.prod_map_kronecker]
  rfl

/-- Holevo information is independent of parenthesization of three factors. -/
theorem holevo_assoc {s t : Type} [Fintype s] [DecidableEq s]
    [Fintype t] [DecidableEq t]
    (N : Channel a b) (M : Channel c d) (P : Channel s t) :
    Channel.holevoInformation.{0,0,0} ((N.prod M).prod P) =
      Channel.holevoInformation.{0,0,0} (N.prod (M.prod P)) := by
  symm
  apply holevo_eq_of_reindex _ _ (Equiv.prodAssoc a c s) (Equiv.prodAssoc b d t)
  apply applyState_reindex_of_single
  intro i j x y
  simp only [prod_single, Equiv.prodAssoc_apply]
  ring

/-- Regroup a block of pairs into the two blocks of coordinates. -/
def powerProdEquiv (a c : Type) [DecidableEq a] [DecidableEq c] (n : ℕ) :
    TensorPower (a × c) n ≃ TensorPower a n × TensorPower c n :=
  let split : (Fin n → a × c) ≃ (Fin n → a) × (Fin n → c) :=
    { toFun := fun z => (fun i => (z i).1, fun i => (z i).2)
      invFun := fun z i => (z.1 i, z.2 i)
      left_inv := by intro z; rfl
      right_inv := by intro z; rfl }
  (tensorPowerEquiv n).trans (split.trans
    ((tensorPowerEquiv n).symm.prodCongr (tensorPowerEquiv n).symm))

/-- Regrouping tensor powers preserves the entire channel's Holevo information,
including ensembles with entangled inputs. -/
theorem holevo_tensorPower_prod (N : Channel a b) (M : Channel c d) (n : ℕ) :
    Channel.holevoInformation.{0,0,0} ((N.prod M).tensorPower n) =
      Channel.holevoInformation.{0,0,0} ((N.tensorPower n).prod (M.tensorPower n)) := by
  symm
  apply holevo_eq_of_reindex _ _ (powerProdEquiv a c n) (powerProdEquiv b d n)
  apply applyState_reindex_of_single
  intro i j x y
  rw [prod_single]
  simp only [Channel.tensorPower_map_single_apply]
  simp only [powerProdEquiv, Equiv.trans_apply, Equiv.prodCongr_apply,
    Equiv.coe_fn_mk, Prod.map_fst, Prod.map_snd, Equiv.apply_symm_apply]
  simp_rw [prod_single]
  rw [Finset.prod_mul_distrib]

/-- The unit channel contributes no Holevo information to a product. -/
theorem holevo_unit_prod (M : Channel c d) :
    Channel.holevoInformation.{0,0,0} (Channel.unit.prod M) =
      Channel.holevoInformation.{0,0,0} M := by
  symm
  apply holevo_eq_of_reindex _ _ (Equiv.punitProd c) (Equiv.punitProd d)
  apply applyState_reindex_of_single
  intro i j x y
  rw [prod_single]
  rcases i with ⟨⟨⟩, i⟩
  rcases j with ⟨⟨⟩, j⟩
  rcases x with ⟨⟨⟩, x⟩
  rcases y with ⟨⟨⟩, y⟩
  simp [Channel.unit, MatrixMap.unit, Matrix.single]
  rfl

/-- Strong Holevo additivity is needed only for the distinguished channel. -/
def StrongHolevoAdditive (N : Channel a b) : Prop :=
  ∀ {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] (M : Channel c d),
    Channel.holevoInformation.{0,0,0} (N.prod M) =
      Channel.holevoInformation.{0,0,0} N + Channel.holevoInformation.{0,0,0} M

/-- Peel all copies of the strongly additive channel, leaving its arbitrary
partner untouched. -/
theorem holevo_tensorPower_prod_eq [Nonempty a] [Nonempty c]
    (N : Channel a b) (hN : StrongHolevoAdditive N) (M : Channel c d) (n : ℕ) :
    Channel.holevoInformation.{0,0,0} ((N.tensorPower n).prod M) =
      (n : ℝ) * Channel.holevoInformation.{0,0,0} N +
        Channel.holevoInformation.{0,0,0} M := by
  induction n with
  | zero =>
    simpa only [Channel.tensorPower_zero, Nat.cast_zero, zero_mul, zero_add] using
      holevo_unit_prod M
  | succ n ih =>
    letI : Nonempty (TensorPower a n) := tensorPower_nonempty_of_nonempty n
    rw [Channel.tensorPower_succ]
    trans Channel.holevoInformation.{0,0,0} (N.prod ((N.tensorPower n).prod M))
    · exact holevo_assoc N (N.tensorPower n) M
    trans Channel.holevoInformation.{0,0,0} N +
      Channel.holevoInformation.{0,0,0} ((N.tensorPower n).prod M)
    · exact hN _
    rw [ih]
    push_cast
    ring

/-- Exact block identity: the partner's block Holevo information is not
replaced by a single-letter value. -/
theorem blockHolevoInformation_prod_eq [Nonempty a] [Nonempty c]
    (N : Channel a b) (hN : StrongHolevoAdditive N) (M : Channel c d) (n : ℕ) :
    Channel.blockHolevoInformation.{0,0,0} (N.prod M) n =
      (n : ℝ) * Channel.holevoInformation.{0,0,0} N +
        Channel.blockHolevoInformation.{0,0,0} M n := by
  letI : Nonempty (TensorPower c n) := tensorPower_nonempty_of_nonempty n
  exact (holevo_tensorPower_prod N M n).trans (holevo_tensorPower_prod_eq N hN _ n)

/-- Taking the supremum of block rates translates the arbitrary partner's
regularized Holevo information by the distinguished channel's one-letter value. -/
theorem regularizedHolevoInformation_prod_eq [Nonempty a] [Nonempty b]
    [Nonempty c] [Nonempty d]
    (N : Channel a b) (hN : StrongHolevoAdditive N) (M : Channel c d) :
    Channel.regularizedHolevoInformation.{0,0,0} (N.prod M) =
      Channel.holevoInformation.{0,0,0} N +
        Channel.regularizedHolevoInformation.{0,0,0} M := by
  have hr (n : ℕ) (hn : 0 < n) :
      Channel.blockHolevoInformation.{0,0,0} (N.prod M) n / n =
        Channel.holevoInformation.{0,0,0} N +
          Channel.blockHolevoInformation.{0,0,0} M n / n := by
    rw [blockHolevoInformation_prod_eq N hN M n, add_div]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
    field_simp
  apply le_antisymm
  · apply csSup_le (N.prod M).regularizedHolevoRateValues_nonempty
    rintro r ⟨n, hn, rfl⟩
    rw [hr n hn]
    exact add_le_add_right
      (le_csSup M.regularizedHolevoRateValues_bddAbove ⟨n, hn, rfl⟩) _
  · apply (le_sub_iff_add_le').mp
    apply csSup_le M.regularizedHolevoRateValues_nonempty
    rintro r ⟨n, hn, rfl⟩
    apply (le_sub_iff_add_le').mpr
    rw [← hr n hn]
    exact le_csSup (N.prod M).regularizedHolevoRateValues_bddAbove ⟨n, hn, rfl⟩

/-- The zero-use channel has zero Holevo information. -/
theorem holevo_unit : Channel.holevoInformation.{0,0,0} Channel.unit = 0 := by
  apply le_antisymm
  · apply csSup_le Channel.unit.holevoInformationValues_nonempty
    intro r hr
    have h := Channel.unit.mem_holevoInformationValues_le_log_card hr
    simpa [log2] using h
  · let E : Ensemble PUnit PUnit :=
      { probs := fun _ => 1
        weights_sum := by simp
        states := fun _ => State.unit }
    apply le_csSup Channel.unit.holevoInformationValues_bddAbove
    refine ⟨PUnit, inferInstance, inferInstance, E, ?_⟩
    change 0 = Ensemble.holevoInformation (Channel.outputEnsemble Channel.unit E)
    rw [Ensemble.holevoInformation_def,
      Ensemble.averageState_singleton _ (by simp) PUnit.unit]
    simp [Channel.outputEnsemble, E]

/-- Strong additivity also collapses the distinguished channel's own blocks. -/
theorem blockHolevoInformation_eq [Nonempty a]
    (N : Channel a b) (hN : StrongHolevoAdditive N) (n : ℕ) :
    Channel.blockHolevoInformation.{0,0,0} N n =
      (n : ℝ) * Channel.holevoInformation.{0,0,0} N := by
  induction n with
  | zero =>
    simpa only [Channel.blockHolevoInformation, Channel.tensorPower_zero,
      Nat.cast_zero, zero_mul] using holevo_unit
  | succ n ih =>
    letI : Nonempty (TensorPower a n) := tensorPower_nonempty_of_nonempty n
    unfold Channel.blockHolevoInformation at ih ⊢
    rw [Channel.tensorPower_succ]
    trans Channel.holevoInformation.{0,0,0} N +
      Channel.holevoInformation.{0,0,0} (N.tensorPower n)
    · exact hN _
    rw [ih]
    push_cast
    ring

/-- Strong Holevo additivity collapses regularization for the channel itself. -/
theorem regularizedHolevoInformation_eq [Nonempty a]
    (N : Channel a b) (hN : StrongHolevoAdditive N) :
    Channel.regularizedHolevoInformation.{0,0,0} N =
      Channel.holevoInformation.{0,0,0} N := by
  have hs : Channel.regularizedHolevoRateValues.{0,0,0} N =
      {Channel.holevoInformation.{0,0,0} N} := by
    ext r
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [blockHolevoInformation_eq N hN]
      have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hn
      simp [hn']
    · intro hr
      have hr' := Set.mem_singleton_iff.mp hr
      refine ⟨1, by norm_num, ?_⟩
      rw [hr', blockHolevoInformation_eq N hN]
      simp
  unfold Channel.regularizedHolevoInformation
  rw [hs, csSup_singleton]

/-- Strong single-letter Holevo additivity implies operational classical
capacity additivity with every finite-dimensional partner. -/
theorem classicalCapacity_prod_eq [Nonempty a] [Nonempty b]
    [Nonempty c] [Nonempty d]
    (N : Channel a b) (hN : StrongHolevoAdditive N) (M : Channel c d) :
    Channel.classicalCapacity.{0,0,0} (N.prod M) =
      Channel.classicalCapacity.{0,0,0} N + Channel.classicalCapacity.{0,0,0} M := by
  rw [Channel.classicalCapacity_eq_regularizedHolevoInformation (N.prod M),
    Channel.classicalCapacity_eq_regularizedHolevoInformation N,
    Channel.classicalCapacity_eq_regularizedHolevoInformation M]
  rw [regularizedHolevoInformation_prod_eq N hN M, regularizedHolevoInformation_eq N hN]

end CapacityAdditivity

/-- Amplitude damping is operationally capacity additive with any finite
partner, even when that partner's capacity requires regularization. -/
theorem amplitudeDamping_classicalCapacity_prod_eq
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] [Nonempty d] (M : Channel c d) :
    Channel.classicalCapacity.{0,0,0} ((amplitudeDamping p hp0 hp1).prod M) =
      Channel.classicalCapacity.{0,0,0} (amplitudeDamping p hp0 hp1) +
        Channel.classicalCapacity.{0,0,0} M := by
  apply CapacityAdditivity.classicalCapacity_prod_eq
  intro c d _ _ _ _ _ M
  exact amplitudeDamping_holevoInformation_prod_eq p hp0 hp1 M

/-- Operational arbitrary-partner additivity under the strong roof
superadditivity interface used for two-Kraus qubit channels. -/
theorem classicalCapacity_prod_eq_of_roof (N : Channel Qubit Qubit)
    (hs : ∀ {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
      (M : Channel c d) (τ : State (Qubit × c)),
      outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB ≤
        outputEntropyRoof (N.prod M) τ)
    {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] [Nonempty d] (M : Channel c d) :
    Channel.classicalCapacity.{0,0,0} (N.prod M) =
      Channel.classicalCapacity.{0,0,0} N + Channel.classicalCapacity.{0,0,0} M := by
  apply CapacityAdditivity.classicalCapacity_prod_eq
  intro c d _ _ _ _ _ M
  exact holevoInformation_prod_eq N hs M

/-- Two-Kraus qubit channels are operationally capacity additive against any
finite partner, with the repository's Wootters interface explicit. -/
theorem twoKraus_classicalCapacity_prod_eq
    {κ : Type*} [Fintype κ] [DecidableEq κ]
    (h : woottersKernelUpperBound) (hcard : Fintype.card κ ≤ 2)
    (K : κ → Matrix Qubit Qubit ℂ) (N : Channel Qubit Qubit)
    (hN : N.map = MatrixMap.ofKraus K)
    {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] [Nonempty d] (M : Channel c d) :
    Channel.classicalCapacity.{0,0,0} (N.prod M) =
      Channel.classicalCapacity.{0,0,0} N + Channel.classicalCapacity.{0,0,0} M :=
  classicalCapacity_prod_eq_of_roof N
    (outputEntropyRoof_prod_ge_of_twoKraus h hcard K N hN) M

end
end AmplitudeDamping
