import AmplitudeDamping.PureOutputSupport
import AmplitudeDamping.OperationalEntanglementCost

/-! # Support consequences in arbitrary local coordinates -/
open scoped BigOperators Matrix ComplexConjugate Kronecker ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT
noncomputable section
universe u v w x y z
variable {a : Type u} {b : Type v} {p : Type w} {q : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]

/-- Product additivity concerns the original state, for arbitrary supplied
local coordinates witnessing the single-excitation support. -/
theorem support_product_additivity_of_local_coordinates
    (V : TwoQubit.LocalIsometry p (a ⊕ Unit) q (Unit ⊕ b))
    (ρ : State (p × q)) (hs : HasSingleExcitationSupport (V.applyState ρ))
    {c : Type y} {d : Type z} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (σ : State (c × d)) :
    entanglementOfFormation ((ρ.prod σ).reindex prodReassoc) =
      entanglementOfFormation ρ + entanglementOfFormation σ := by
  apply le_antisymm (entanglementOfFormation_prod_reassoc_le ρ σ)
  have h := support_criterion_of_local_coordinates V
    ((ρ.prod σ).reindex prodReassoc) (by
      rwa [reindex_prodReassoc_prodReassoc, prod_marginalA])
  simpa only [reindex_prodReassoc_prodReassoc, prod_marginalA, prod_marginalB] using h

/-- Exact finite-copy formation in the original basis. -/
theorem support_tensorPower_formation_of_local_coordinates
    (V : TwoQubit.LocalIsometry p (a ⊕ Unit) q (Unit ⊕ b))
    (ρ : State (p × q)) (hs : HasSingleExcitationSupport (V.applyState ρ))
    (n : ℕ) : entanglementOfFormation (ρ.tensorPowerBipartite n) =
      n * entanglementOfFormation ρ := by
  induction n with
  | zero => simp [entanglementOfFormation_tensorPowerBipartite_zero]
  | succ n ih =>
    have he : entanglementOfFormation (ρ.tensorPowerBipartite (n+1)) =
        entanglementOfFormation ((ρ.prod (ρ.tensorPowerBipartite n)).reindex prodReassoc) := by
      rw [tensorPowerBipartite_succ]
      rfl
    rw [he, support_product_additivity_of_local_coordinates V ρ hs, ih, Nat.cast_succ]
    ring

/-- Regularized formation in the original basis. -/
theorem support_regularized_cost_of_local_coordinates
    (V : TwoQubit.LocalIsometry p (a ⊕ Unit) q (Unit ⊕ b))
    (ρ : State (p × q)) (hs : HasSingleExcitationSupport (V.applyState ρ)) :
    entanglementCost ρ = entanglementOfFormation ρ := by
  have he : {r | ∃ n : ℕ, 0 < n ∧
      r = entanglementOfFormation (ρ.tensorPowerBipartite n) / (n : ℝ)} =
      {entanglementOfFormation ρ} := by
    ext r
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [support_tensorPower_formation_of_local_coordinates V ρ hs n,
        mul_div_cancel_left₀ _ (Nat.cast_pos.mpr hn).ne']
      exact Set.mem_singleton _
    · rintro rfl
      refine ⟨1, Nat.one_pos, ?_⟩
      simp [support_tensorPower_formation_of_local_coordinates V ρ hs 1]
  rw [entanglementCost, he, csInf_singleton]

/-- Operational state cost in the original basis, using only the displayed
standard operational regularization theorem. -/
theorem support_operational_cost_of_local_coordinates
    {p q : Type} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (hstate : StateCostRegularization)
    (V : TwoQubit.LocalIsometry p (a ⊕ Unit) q (Unit ⊕ b))
    (ρ : State (p × q)) (hs : HasSingleExcitationSupport (V.applyState ρ)) :
    operationalStateCost ρ = entanglementOfFormation ρ := by
  rw [hstate.eq_regularized, support_regularized_cost_of_local_coordinates V ρ hs]


/-- The forbidden subspace is the tensor product of the two orthogonal
complements. Its compression vanishes exactly when the state is supported
on the sum of the two distinguished-vector tensor sectors. -/
def HasSingleExcitationDirections (ρ : State (p × q))
    (u : PureVector p) (v : PureVector q) : Prop :=
  let P := Matrix.kronecker (pureComplement u) (pureComplement v)
  P * ρ.matrix * P.conjTranspose = 0

/-- Split one distinguished direction to the last coordinate. -/
def distinguishedLastMatrix (u : PureVector p) : Matrix (p ⊕ Unit) p ℂ :=
  Sum.elim (fun i j => pureComplement u i j) (fun _ j => star (u.amp j))

theorem distinguishedLastMatrix_isometry (u : PureVector p) :
    (distinguishedLastMatrix u).conjTranspose * distinguishedLastMatrix u = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
    Fintype.sum_unique, distinguishedLastMatrix, Sum.elim_inl, Sum.elim_inr, star_star]
  change ((pureComplement u).conjTranspose * pureComplement u) i j +
    u.state.matrix i j = _
  rw [pureComplement_conjTranspose, pureComplement_idempotent]
  simp [pureComplement]

/-- Concrete local isometries realizing any pair of distinguished unit
vectors. Redundant complement coordinates allow all dimensions uniformly. -/
def distinguishedSupportCoordinates (u : PureVector p) (v : PureVector q) :
    TwoQubit.LocalIsometry p (p ⊕ Unit) q (Unit ⊕ q) :=
  ⟨⟨distinguishedLastMatrix u, distinguishedLastMatrix_isometry u⟩,
    ⟨environmentSplitMatrix v, environmentSplitMatrix_isometry v⟩⟩

/-- Exact equivalence between intrinsic orthogonal-projector support and
our sum-coordinate support convention. -/
theorem singleExcitationDirections_iff_coordinates (ρ : State (p × q))
    (u : PureVector p) (v : PureVector q) :
    HasSingleExcitationDirections ρ u v ↔
      HasSingleExcitationSupport ((distinguishedSupportCoordinates u v).applyState ρ) := by
  let P := Matrix.kronecker (pureComplement u) (pureComplement v)
  have he (i : p) (j : q) :
      ((distinguishedSupportCoordinates u v).applyState ρ).matrix
        (Sum.inl i, Sum.inr j) (Sum.inl i, Sum.inr j) =
      (P * ρ.matrix * P.conjTranspose) (i,j) (i,j) := by
    simp [TwoQubit.LocalIsometry.applyState_matrix, TwoQubit.LocalIsometry.applyMatrix,
      TwoQubit.LocalIsometry.matrix, distinguishedSupportCoordinates,
      distinguishedLastMatrix, environmentSplitMatrix, Matrix.mul_apply,
      Matrix.conjTranspose_apply, Matrix.kronecker, P]
  constructor
  · intro h i j
    rw [he]
    change P * ρ.matrix * P.conjTranspose = 0 at h
    rw [h]
    rfl
  · intro h
    have hp := ρ.pos.mul_mul_conjTranspose_same P
    apply hp.trace_eq_zero_iff.mp
    simp only [Matrix.trace, Matrix.diag, Fintype.sum_prod_type]
    have hz (i : p) (j : q) : (P * ρ.matrix * P.conjTranspose) (i,j) (i,j) = 0 := by
      rw [← he]
      exact h i j
    simp only [hz, Finset.sum_const_zero]

/-- General support SSA with intrinsic distinguished-vector support. -/
theorem support_criterion_of_distinguished_vectors
    (u : PureVector p) (v : PureVector q)
    {c : Type y} {d : Type z} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (Ω : State ((p × c) × (q × d)))
    (hs : HasSingleExcitationDirections (Ω.reindex prodReassoc).marginalA u v) :
    entanglementOfFormation (Ω.reindex prodReassoc).marginalA +
      entanglementOfFormation (Ω.reindex prodReassoc).marginalB ≤
    entanglementOfFormation Ω :=
  support_criterion_of_local_coordinates (distinguishedSupportCoordinates u v) Ω
    ((singleExcitationDirections_iff_coordinates _ u v).mp hs)


/-- Intrinsic distinguished-vector support gives strong product additivity. -/
theorem support_product_additivity_of_distinguished_vectors
    (ρ : State (p × q)) (u : PureVector p) (v : PureVector q)
    (hs : HasSingleExcitationDirections ρ u v)
    {c : Type y} {d : Type z} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (σ : State (c × d)) :
    entanglementOfFormation ((ρ.prod σ).reindex prodReassoc) =
      entanglementOfFormation ρ + entanglementOfFormation σ :=
  support_product_additivity_of_local_coordinates (distinguishedSupportCoordinates u v) ρ
    ((singleExcitationDirections_iff_coordinates _ u v).mp hs) σ

/-- Intrinsic distinguished-vector support identifies regularized state cost. -/
theorem support_regularized_cost_of_distinguished_vectors
    (ρ : State (p × q)) (u : PureVector p) (v : PureVector q)
    (hs : HasSingleExcitationDirections ρ u v) :
    entanglementCost ρ = entanglementOfFormation ρ :=
  support_regularized_cost_of_local_coordinates (distinguishedSupportCoordinates u v) ρ
    ((singleExcitationDirections_iff_coordinates _ u v).mp hs)

/-- Full operational cost conclusion for arbitrary distinguished vectors. -/
theorem support_operational_cost_of_distinguished_vectors
    {p q : Type} [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (hstate : StateCostRegularization)
    (ρ : State (p × q)) (u : PureVector p) (v : PureVector q)
    (hs : HasSingleExcitationDirections ρ u v) :
    operationalStateCost ρ = entanglementOfFormation ρ := by
  rw [hstate.eq_regularized, support_regularized_cost_of_distinguished_vectors ρ u v hs]

end
end AmplitudeDamping
