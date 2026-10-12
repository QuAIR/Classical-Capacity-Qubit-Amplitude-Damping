import AmplitudeDamping.SupportedMarginal
import AmplitudeDamping.EntanglementCost

/-!
# The arbitrary-dimensional support criterion

The only external classical input is the exact two-Hermitian-expectation
finite pure decomposition theorem. The entropy formula for supported pure
states, rectangular triangular inequality, auxiliary local-discard bound,
and mixed-state convex-roof propagation are all proved in imported modules.
Local sectors may have dimension zero.
-/

open scoped BigOperators NNReal ComplexConjugate ComplexOrder MatrixOrder Matrix Kronecker
namespace AmplitudeDamping
open QIT
noncomputable section
universe u v w x
variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- Pure-extension support criterion, with no two-qubit restriction. -/
theorem supported_pure_entanglement_superadditive
    (hclassical : TwoExpectationDecomposition ((a ⊕ Unit) × (Unit ⊕ b)))
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)))
    (hs : HasSingleExcitationAmplitudes ψ) :
    entanglementOfFormation (ψ.state.reindex prodReassoc).marginalA +
      entanglementOfFormation (ψ.state.reindex prodReassoc).marginalB ≤
    ψ.state.marginalA.vonNeumann := by
  have hρ := supported_marginal_formation_upper_bound hclassical
    (ψ.state.reindex prodReassoc).marginalA ((pure_support_iff_amplitudes ψ).mpr hs)
  rw [supportProjectorA_extension_expectation, supportProjectorB_extension_expectation] at hρ
  have hσ := supported_auxiliary_entanglement_bound ψ hs
  have hT := supported_pure_extension_entropy_lower_bound ψ hs
  linarith

/-- Strong superadditivity for any finite-dimensional mixed extension whose
first marginal is supported on `C|00⟩ ⊕ A₁|0⟩ ⊕ |0⟩B₁`.

The basis ordering is `A₁ ⊕ C|0_A⟩` and `C|0_B⟩ ⊕ B₁`; arbitrary finite
sector and auxiliary dimensions, including empty sectors, are permitted. -/
theorem supported_entanglementOfFormation_superadditive
    (hclassical : TwoExpectationDecomposition ((a ⊕ Unit) × (Unit ⊕ b)))
    (Ω : State (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)))
    (hs : HasSingleExcitationSupport (Ω.reindex prodReassoc).marginalA) :
    entanglementOfFormation (Ω.reindex prodReassoc).marginalA +
      entanglementOfFormation (Ω.reindex prodReassoc).marginalB ≤
    entanglementOfFormation Ω :=
  supported_superadditivity_of_pure
    (supported_pure_entanglement_superadditive hclassical) Ω hs

/-- Strong product additivity for every supported state and every arbitrary
finite-dimensional auxiliary bipartite state. -/
theorem supported_entanglementOfFormation_product_additive
    (hclassical : TwoExpectationDecomposition ((a ⊕ Unit) × (Unit ⊕ b)))
    (ρ : State ((a ⊕ Unit) × (Unit ⊕ b))) (hs : HasSingleExcitationSupport ρ)
    (σ : State (c × d)) :
    entanglementOfFormation ((ρ.prod σ).reindex prodReassoc) =
      entanglementOfFormation ρ + entanglementOfFormation σ := by
  apply le_antisymm (entanglementOfFormation_prod_reassoc_le ρ σ)
  have h := supported_entanglementOfFormation_superadditive hclassical
    ((ρ.prod σ).reindex prodReassoc) (by
      rwa [reindex_prodReassoc_prodReassoc, prod_marginalA])
  simpa only [reindex_prodReassoc_prodReassoc, prod_marginalA, prod_marginalB] using h



/-- Every tensor power has exactly the additive formation cost. -/
theorem supported_tensorPower_formation
    (hclassical : TwoExpectationDecomposition ((a ⊕ Unit) × (Unit ⊕ b)))
    (ρ : State ((a ⊕ Unit) × (Unit ⊕ b))) (hs : HasSingleExcitationSupport ρ)
    (n : ℕ) :
    entanglementOfFormation (ρ.tensorPowerBipartite n) =
      n * entanglementOfFormation ρ := by
  induction n with
  | zero => simp [entanglementOfFormation_tensorPowerBipartite_zero]
  | succ n ih =>
    have he : entanglementOfFormation (ρ.tensorPowerBipartite (n + 1)) =
        entanglementOfFormation ((ρ.prod (ρ.tensorPowerBipartite n)).reindex prodReassoc) := by
      rw [tensorPowerBipartite_succ]
      rfl
    rw [he, supported_entanglementOfFormation_product_additive hclassical ρ hs,
      ih, Nat.cast_succ]
    ring

/-- The regularized formation cost equals the single-copy formation cost.
This uses the repository's explicit regularization definition of state cost. -/
theorem supported_regularized_entanglementCost_eq
    (hclassical : TwoExpectationDecomposition ((a ⊕ Unit) × (Unit ⊕ b)))
    (ρ : State ((a ⊕ Unit) × (Unit ⊕ b))) (hs : HasSingleExcitationSupport ρ) :
    entanglementCost ρ = entanglementOfFormation ρ := by
  have hset : {r | ∃ n : ℕ, 0 < n ∧
      r = entanglementOfFormation (ρ.tensorPowerBipartite n) / (n : ℝ)} =
      {entanglementOfFormation ρ} := by
    ext r
    constructor
    · rintro ⟨n, hn, rfl⟩
      rw [supported_tensorPower_formation hclassical ρ hs n,
        mul_div_cancel_left₀ _ (Nat.cast_pos.mpr hn).ne']
      exact Set.mem_singleton _
    · intro hr
      rcases Set.mem_singleton_iff.mp hr with rfl
      refine ⟨1, Nat.one_pos, ?_⟩
      simp [supported_tensorPower_formation hclassical ρ hs 1]
  rw [entanglementCost, hset, csInf_singleton]


section BasisTransport
universe u₁ u₂ v₁ v₂
variable {p : Type u₁} {p' : Type u₂} {q : Type v₁} {q' : Type v₂}
variable [Fintype p] [DecidableEq p] [Fintype p'] [DecidableEq p']
variable [Fintype q] [DecidableEq q] [Fintype q'] [DecidableEq q']

/-- Extend an arbitrary pair of local coordinate isometries by identities on
both auxiliary systems. This includes arbitrary orthonormal basis changes. -/
def fourfoldLocalIsometry (V : TwoQubit.LocalIsometry p p' q q') :
    TwoQubit.LocalIsometry (p × c) (p' × c) (q × d) (q' × d) where
  alice := ⟨V.alice.matrix ⊗ₖ (1 : Matrix c c ℂ),
    kronecker_isometry _ V.alice.isometry _ (by simp)⟩
  bob := ⟨V.bob.matrix ⊗ₖ (1 : Matrix d d ℂ),
    kronecker_isometry _ V.bob.isometry _ (by simp)⟩

def reassociatedLocalIsometry (V : TwoQubit.LocalIsometry p p' q q') :
    TwoQubit.LocalIsometry (p × q) (p' × q') (c × d) (c × d) where
  alice := ⟨V.matrix, V.matrix_isometry⟩
  bob := ⟨1, by simp⟩

theorem fourfoldLocalIsometry_matrix_reindex (V : TwoQubit.LocalIsometry p p' q q') :
    ((fourfoldLocalIsometry (c := c) (d := d) V).matrix).submatrix
      prodReassoc.symm prodReassoc.symm =
    (reassociatedLocalIsometry (c := c) (d := d) V).matrix := by
  ext x y
  obtain ⟨⟨i,j⟩,k,l⟩ := x
  obtain ⟨⟨i',j'⟩,k',l'⟩ := y
  change (V.alice.matrix i i' * (if k = k' then 1 else 0)) *
      (V.bob.matrix j j' * (if l = l' then 1 else 0)) =
    (V.alice.matrix i i' * V.bob.matrix j j') * (if (k,l) = (k',l') then 1 else 0)
  by_cases hk : k = k' <;> by_cases hl : l = l' <;> simp [hk, hl]

omit [Fintype p] [DecidableEq p] [Fintype p'] [DecidableEq p']
  [DecidableEq q] [DecidableEq q'] in
theorem matrix_conjugation_reindex
    (M : Matrix p q ℂ) (X : Matrix q q ℂ) (e : p ≃ p') (f : q ≃ q') :
    (M * X * M.conjTranspose).submatrix e.symm e.symm =
      M.submatrix e.symm f.symm * X.submatrix f.symm f.symm *
        (M.submatrix e.symm f.symm).conjTranspose := by
  rw [← Matrix.submatrix_mul_equiv _ _ e.symm f.symm e.symm,
    ← Matrix.submatrix_mul_equiv _ _ e.symm f.symm f.symm]
  rfl

/-- Local coordinate changes commute with four-system reassociation. -/
theorem fourfoldLocalIsometry_reassoc
    (V : TwoQubit.LocalIsometry p p' q q') (Ω : State ((p × c) × (q × d))) :
    ((fourfoldLocalIsometry V).applyState Ω).reindex prodReassoc =
      (reassociatedLocalIsometry V).applyState (Ω.reindex prodReassoc) := by
  apply State.ext
  rw [State.reindex_matrix, TwoQubit.LocalIsometry.applyState_matrix,
    TwoQubit.LocalIsometry.applyState_matrix, TwoQubit.LocalIsometry.applyMatrix,
    TwoQubit.LocalIsometry.applyMatrix, State.reindex_matrix]
  rw [matrix_conjugation_reindex _ _ prodReassoc prodReassoc,
    fourfoldLocalIsometry_matrix_reindex]

/-- The constrained marginal transforms by the original pair of isometries. -/
theorem fourfoldLocalIsometry_marginalA
    (V : TwoQubit.LocalIsometry p p' q q') (Ω : State ((p × c) × (q × d))) :
    (((fourfoldLocalIsometry V).applyState Ω).reindex prodReassoc).marginalA =
      V.applyState (Ω.reindex prodReassoc).marginalA := by
  apply State.ext
  rw [fourfoldLocalIsometry_reassoc, localIsometry_applyState_marginalA_matrix]
  rfl

/-- Local coordinate changes preserve the auxiliary marginal. -/
theorem fourfoldLocalIsometry_marginalB
    (V : TwoQubit.LocalIsometry p p' q q') (Ω : State ((p × c) × (q × d))) :
    (((fourfoldLocalIsometry V).applyState Ω).reindex prodReassoc).marginalB =
      (Ω.reindex prodReassoc).marginalB := by
  apply State.ext
  rw [fourfoldLocalIsometry_reassoc, State.marginalB_matrix,
    State.marginalB_matrix, TwoQubit.LocalIsometry.applyState_matrix,
    TwoQubit.LocalIsometry.applyMatrix]
  exact partialTraceA_conj_kronecker_left V.matrix V.matrix_isometry _

/-- Basis-independent transport of the support criterion. The supplied local
isometries are concrete coordinate maps into `A₁ ⊕ C|0_A⟩` and
`C|0_B⟩ ⊕ B₁`. In particular, local unitaries for any chosen orthonormal
bases are admitted; the conclusion concerns the original untransformed state.
No positivity of either sector dimension is required. -/
theorem support_criterion_of_local_coordinates
    (hclassical : TwoExpectationDecomposition ((a ⊕ Unit) × (Unit ⊕ b)))
    (V : TwoQubit.LocalIsometry p (a ⊕ Unit) q (Unit ⊕ b))
    (Ω : State ((p × c) × (q × d)))
    (hs : HasSingleExcitationSupport (V.applyState (Ω.reindex prodReassoc).marginalA)) :
    entanglementOfFormation (Ω.reindex prodReassoc).marginalA +
      entanglementOfFormation (Ω.reindex prodReassoc).marginalB ≤
    entanglementOfFormation Ω := by
  have h := supported_entanglementOfFormation_superadditive hclassical
    ((fourfoldLocalIsometry V).applyState Ω) (by
      rw [fourfoldLocalIsometry_marginalA]
      exact hs)
  rwa [fourfoldLocalIsometry_marginalA, fourfoldLocalIsometry_marginalB,
    entanglementOfFormation_applyState, entanglementOfFormation_applyState] at h

end BasisTransport

end
end AmplitudeDamping
