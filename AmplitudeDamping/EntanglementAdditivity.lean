import AmplitudeDamping.LocalUnitary
import AmplitudeDamping.RankTwoKernel

/-!
# Strong additivity of the entanglement of formation on products (Corollary 7)

Manuscript §5, Corollary 7 (first half).  Let `ρ_AB` be a two-qubit state
whose kernel contains a nonzero product vector `u ⊗ v`.  Then for every
finite-dimensional bipartite state `σ_A'B'`,

`E_F(ρ ⊗ σ) = E_F(ρ) + E_F(σ)`,

with the tensor product partitioned as `AA' : BB'`.

In Lean, `entanglementOfFormation` cuts a state `State (A × B)` at its
outermost product, so the manuscript's `AA' | BB'` bipartition of
`ρ_AB ⊗ σ_A'B'` is realized by reassociating the carrier with
`prodReassoc : (A ⊗ C) × (B ⊗ D) ≃ (A ⊗ B) × (C ⊗ D)`; the left-hand side
of the identity is `entanglementOfFormation ((rho.prod sigma).reindex
prodReassoc)`.  (The raw outer cut `A⊗B | A'⊗B'` of `rho.prod sigma` is a
product cut, on which `E_F` vanishes identically, so the reassociated
carrier is the only faithful rendering of the statement.)

The `≤` direction is the product-decomposition argument
(`entanglementOfFormation_prod_reassoc_le`, committed in
`BipartiteReassociation.lean`, built from `PureDecomposition.reassocProd`).
The `≥` direction applies Theorem 6 in its full product-kernel form
(`entanglementOfFormation_superadditive_of_productKernel`) to the state
`Ω := (rho.prod sigma).reindex prodReassoc` on `AA' ⊗ BB'`: the two
reassociated marginals of `Ω` are exactly `ρ` and `σ`, so the kernel
hypothesis transfers verbatim.  The rank-at-most-two form follows from
`exists_product_kernelVector_of_rank_le_two`.

This module also exports the marginal lemmas behind the transfer: the
reassociation equivalence is an involution, the marginals of a product state
across the product cut are the factors, and each marginal of a reassociated
product of bipartite states is the product of the corresponding marginals
(the mixed-state analogue of `pure_reassoc_marginalA`).
-/

open scoped BigOperators NNReal ComplexConjugate ComplexOrder MatrixOrder Matrix

namespace AmplitudeDamping

open QIT

universe u v

noncomputable section

variable {a : Type u} {c : Type v}
variable [Fintype a] [DecidableEq a]
variable [Fintype c] [DecidableEq c]

/-! ### Reassociation helpers -/

/-- Reassociating twice with `prodReassoc` is the identity: the equivalence
is an involution on fourfold tensor products. -/
theorem prodReassoc_trans_prodReassoc {α β γ δ : Type*} :
    (prodReassoc (a := α) (b := β) (c := γ) (d := δ)).trans
        (prodReassoc (a := α) (b := γ) (c := β) (d := δ)) =
      Equiv.refl ((α × γ) × (β × δ)) := by
  apply Equiv.ext
  intro x
  simp [prodReassoc]

/-- Double reassociation of a state is the identity, because `prodReassoc`
is an involution. -/
theorem reindex_prodReassoc_prodReassoc {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (ρ : State ((α × γ) × (β × δ))) :
    (ρ.reindex prodReassoc).reindex prodReassoc = ρ := by
  apply State.ext
  ext i j
  simp only [State.reindex_matrix, Matrix.submatrix_apply,
    prodReassoc_symm_apply, Prod.mk.eta]

/-- The first marginal of a product state, across the product cut, is the
first factor. -/
theorem prod_marginalA {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (rho : State (α × γ)) (sigma : State (β × δ)) :
    (rho.prod sigma).marginalA = rho := by
  apply State.ext
  exact State.partialTraceB_prod rho sigma

/-- The second marginal of a product state, across the product cut, is the
second factor. -/
theorem prod_marginalB {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (rho : State (α × γ)) (sigma : State (β × δ)) :
    (rho.prod sigma).marginalB = sigma := by
  apply State.ext
  exact State.partialTraceA_prod rho sigma

/-! ### Marginals through the reassociation -/

/-- The first marginal of a reassociated product of two bipartite states is
the product of the two first marginals: the mixed-state version of
`pure_reassoc_marginalA`.  This is a Kronecker partial-trace computation
through the reassociation. -/
theorem prod_reassoc_marginalA {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (rho : State (α × γ)) (sigma : State (β × δ)) :
    ((rho.prod sigma).reindex prodReassoc).marginalA =
      (rho.marginalA).prod (sigma.marginalA) := by
  apply State.ext
  ext i k
  rcases i with ⟨i1, i2⟩
  rcases k with ⟨k1, k2⟩
  simp only [State.marginalA_matrix, State.reindex_matrix, partialTraceB,
    Matrix.submatrix_apply, prodReassoc_symm_apply, Fintype.sum_prod_type,
    State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [Finset.sum_mul_sum]

/-- The second marginal of a reassociated product of two bipartite states is
the product of the two second marginals. -/
theorem prod_reassoc_marginalB {α β γ δ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ] [Fintype δ] [DecidableEq δ]
    (rho : State (α × γ)) (sigma : State (β × δ)) :
    ((rho.prod sigma).reindex prodReassoc).marginalB =
      (rho.marginalB).prod (sigma.marginalB) := by
  apply State.ext
  ext i k
  rcases i with ⟨i1, i2⟩
  rcases k with ⟨k1, k2⟩
  simp only [State.marginalB_matrix, State.reindex_matrix, partialTraceA,
    Matrix.submatrix_apply, prodReassoc_symm_apply, Fintype.sum_prod_type,
    State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply]
  rw [Finset.sum_mul_sum]

/-- The two reassociated marginals of the reassociated product `ρ_AB ⊗
σ_A'B'`, read across the `AA' | BB'` cut, are `ρ_AB` and `σ_A'B'`.  This is
the marginal transfer used by the superadditivity engine: the kernel
hypothesis on `ρ` and the two `E_F` terms on the left of Theorem 6 pass
through the reassociation unchanged. -/
theorem prod_reassoc_marginals (rho : State (Qubit × Qubit))
    (sigma : State (a × c)) :
    (((rho.prod sigma).reindex prodReassoc).reindex prodReassoc).marginalA =
      rho ∧
    (((rho.prod sigma).reindex prodReassoc).reindex prodReassoc).marginalB =
      sigma := by
  constructor
  · rw [reindex_prodReassoc_prodReassoc]
    exact prod_marginalA rho sigma
  · rw [reindex_prodReassoc_prodReassoc]
    exact prod_marginalB rho sigma

/-! ### Corollary 7, first half -/

/-- **Corollary 7, `≤` half.**  The entanglement of formation of `ρ_AB ⊗
σ_A'B'` across the `AA' | BB'` cut is at most the sum of the two entanglements
of formation.  This is the committed product-decomposition bound
(`PureDecomposition.reassocProd`) specialized to a two-qubit first factor. -/
theorem entanglementOfFormation_prod_le (rho : State (Qubit × Qubit))
    (sigma : State (a × c)) :
    entanglementOfFormation ((rho.prod sigma).reindex prodReassoc) ≤
      entanglementOfFormation rho + entanglementOfFormation sigma :=
  entanglementOfFormation_prod_reassoc_le rho sigma

/-- **Corollary 7, `≥` half.**  If the two-qubit state `ρ` has a nonzero
product vector `u ⊗ v` in its kernel, then the sum of the entanglements of
formation of `ρ` and `σ` is at most the entanglement of formation of the
product `ρ ⊗ σ` across the `AA' | BB'` cut.  Theorem 6 in its full
product-kernel form is applied to `Ω := (rho.prod sigma).reindex prodReassoc`
on `AA' ⊗ BB'`; the two reassociated marginals of `Ω` are `ρ` and `σ`. -/
theorem entanglementOfFormation_prod_ge (h : woottersKernelUpperBound)
    (rho : State (Qubit × Qubit)) (u v : Qubit → ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hk : rho.matrix *ᵥ (fun p => u p.1 * v p.2) = 0)
    (sigma : State (a × c)) :
    entanglementOfFormation rho + entanglementOfFormation sigma ≤
      entanglementOfFormation ((rho.prod sigma).reindex prodReassoc) := by
  obtain ⟨hmA, hmB⟩ := prod_reassoc_marginals rho sigma
  have hker :
      (((((rho.prod sigma).reindex prodReassoc).reindex prodReassoc).marginalA).matrix *ᵥ
        (fun p => u p.1 * v p.2)) = 0 := by
    rw [hmA]
    exact hk
  have hmain := entanglementOfFormation_superadditive_of_productKernel h
    ((rho.prod sigma).reindex prodReassoc) u v hu hv hker
  rwa [hmA, hmB] at hmain

/-- **Corollary 7 (first half): strong additivity on products.**  If the
two-qubit state `ρ` has a nonzero product vector `u ⊗ v` in its kernel, then
for every bipartite state `σ`, the entanglement of formation of the product
`ρ ⊗ σ` across the `AA' | BB'` cut is exactly the sum of the two entanglements
of formation. -/
theorem entanglementOfFormation_prod_eq (h : woottersKernelUpperBound)
    (rho : State (Qubit × Qubit)) (u v : Qubit → ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hk : rho.matrix *ᵥ (fun p => u p.1 * v p.2) = 0)
    (sigma : State (a × c)) :
    entanglementOfFormation ((rho.prod sigma).reindex prodReassoc) =
      entanglementOfFormation rho + entanglementOfFormation sigma :=
  le_antisymm (entanglementOfFormation_prod_le rho sigma)
    (entanglementOfFormation_prod_ge h rho u v hu hv hk sigma)

/-- **Corollary 7 (first half), rank form.**  Every two-qubit state of rank
at most two has a nonzero product vector in its kernel, so the strong
additivity of the entanglement of formation on products holds for it and
every bipartite partner. -/
theorem entanglementOfFormation_prod_eq_of_rank_le_two
    (h : woottersKernelUpperBound)
    (rho : State (Qubit × Qubit))
    (hrank : (Finset.univ.filter
        (fun i : Qubit × Qubit => rho.pos.isHermitian.eigenvalues i ≠ 0)).card
      ≤ 2)
    (sigma : State (a × c)) :
    entanglementOfFormation ((rho.prod sigma).reindex prodReassoc) =
      entanglementOfFormation rho + entanglementOfFormation sigma := by
  obtain ⟨u, v, hu, hv, hk⟩ :=
    exists_product_kernelVector_of_rank_le_two rho hrank
  exact entanglementOfFormation_prod_eq h rho u v hu hv hk sigma

end

end AmplitudeDamping
