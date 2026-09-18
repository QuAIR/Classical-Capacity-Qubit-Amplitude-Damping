import AmplitudeDamping.EntanglementAdditivity
import AmplitudeDamping.ChoiState

/-!
# Entanglement cost of the amplitude-damping Choi state (Corollary 7, second half)

Manuscript §5, lines 744-757 and 856-876.  Iterating the strong additivity of
the entanglement of formation on products (Corollary 7, first half, proved in
`EntanglementAdditivity.lean`) along the IID tensor powers of a two-qubit
state `ρ` with a nonzero product kernel vector gives

`E_F(ρ^⊗n) = n · E_F(ρ)`   for every `n ≥ 1`,

read across the `A^n | B^n` bipartition of `tensorPowerBipartite ρ n`.
Consequently the entanglement cost — the regularized quantity
`E_C(ρ) = lim_n E_F(ρ^⊗n)/n` of eq. `(ec-definition)` — equals `E_F(ρ)` for
every such state, and for the amplitude-damping Choi state `ω_p` of eq.
`(choi)` this evaluates to the boxed identity eq. `(choi-cost)`:

`E_F(ω_p^⊗n) = n · h₂((1 + √p)/2)`   and   `E_C(ω_p) = h₂((1 + √p)/2)`.

The pipeline is:

* `entanglementOfFormation_reindex`: `E_F` is invariant under relabeling the
  two sides of the bipartition separately.  Both inequalities come from
  transporting near-optimal pure decompositions along the relabeling
  (`PureDecomposition.reindexEquiv`); each branch cost is preserved because
  the branch marginal relabels per side and von Neumann entropy is
  relabeling-invariant.
* `tensorPowerBipartite_succ`: the `(n+1)`-fold IID bipartite tensor power is
  the product of one copy and the `n`-fold remainder, reassociated across the
  `A A^n | B B^n` cut — exactly the shape consumed by
  `entanglementOfFormation_prod_eq`.
* `entanglementOfFormation_tensorPowerBipartite_eq`: induction on `n`; the
  base case is the one-dimensional `n = 0` state, whose `E_F` vanishes
  because every branch marginal lives on the trivial system.
-/

open scoped BigOperators NNReal ComplexConjugate ComplexOrder MatrixOrder Matrix
open scoped Topology

open Filter

namespace AmplitudeDamping

open QIT

universe u v

noncomputable section

variable {a : Type u} {c : Type v}
variable [Fintype a] [DecidableEq a]
variable [Fintype c] [DecidableEq c]

/-! ### Relabeling tools -/

/-- Relabeling twice composes: `State.reindex` through two equivalences is the
relabeling along the composite. -/
theorem state_reindex_reindex {α β γ : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype γ] [DecidableEq γ]
    (ρ : State α) (e : α ≃ β) (f : β ≃ γ) :
    (ρ.reindex e).reindex f = ρ.reindex (e.trans f) := by
  apply State.ext
  ext i j
  rfl

/-- A per-side relabeling followed by the per-side inverse relabeling is the
identity equivalence. -/
theorem prodCongr_trans_prodCongr_symm {α β α' β' : Type*}
    (eA : α ≃ α') (eB : β ≃ β') :
    (eA.prodCongr eB).trans (eA.symm.prodCongr eB.symm) = Equiv.refl (α × β) := by
  apply Equiv.ext
  rintro ⟨x1, x2⟩
  simp [Equiv.prodCongr_apply]

/-! ### Per-side relabeling invariance of the entanglement of formation -/

/-- The branch cost of a pure vector is invariant under a per-side relabeling
of the bipartition: the marginal relabels along the first side and the von
Neumann entropy is relabeling-invariant. -/
theorem pureVector_reindex_prodCongr_marginalA_vonNeumann
    {α β α' β' : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β']
    (ψ : PureVector (α × β)) (eA : α ≃ α') (eB : β ≃ β') :
    ((ψ.reindex (eA.prodCongr eB)).state.marginalA).vonNeumann =
      (ψ.state.marginalA).vonNeumann := by
  rw [PureVector.reindex_state, State.marginalA_reindex_prodCongr,
    State.vonNeumann_reindex]

/-- The entanglement cost of a pure decomposition is preserved by
transporting it along a per-side relabeling of the bipartition. -/
theorem pureDecomposition_reindexEquiv_prodCongr_entanglementCost
    {α β α' β' : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β']
    (E : PureDecomposition (α × β)) (eA : α ≃ α') (eB : β ≃ β') :
    (E.reindexEquiv (eA.prodCongr eB)).entanglementCost = E.entanglementCost := by
  rw [PureDecomposition.reindexEquiv_entanglementCost]
  unfold PureDecomposition.entanglementCost
  exact Finset.sum_congr rfl fun i _ => by
    rw [pureVector_reindex_prodCongr_marginalA_vonNeumann]

/-- The entanglement of formation cannot increase under a per-side relabeling
of the bipartition: near-optimal decompositions transport along the
relabeling at unchanged cost. -/
theorem entanglementOfFormation_reindex_le
    {α β α' β' : Type*}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    [Fintype α'] [DecidableEq α'] [Fintype β'] [DecidableEq β']
    (ω : State (α × β)) (eA : α ≃ α') (eB : β ≃ β') :
    entanglementOfFormation (ω.reindex (Equiv.prodCongr eA eB)) ≤
      entanglementOfFormation ω := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, hx, hxlt⟩ :=
    Real.lt_sInf_add_pos (pureEntanglementValues_nonempty ω) hε
  obtain ⟨E, hEω, rfl⟩ := hx
  have hroof := entanglementOfFormation_le_entanglementCost
    (E.reindexEquiv (eA.prodCongr eB))
  rw [PureDecomposition.reindexEquiv_averageState, hEω,
    pureDecomposition_reindexEquiv_prodCongr_entanglementCost] at hroof
  have hxlt' : E.entanglementCost < entanglementOfFormation ω + ε := by
    simpa [entanglementOfFormation] using hxlt
  linarith

/-- **Per-side relabeling invariance of `E_F`.**  Relabeling the two sides of
the bipartition by independent finite basis equivalences does not change the
entanglement of formation. -/
theorem entanglementOfFormation_reindex
    {a1 a2 b1 b2 a' b' : Type*}
    [Fintype a1] [DecidableEq a1] [Fintype a2] [DecidableEq a2]
    [Fintype b1] [DecidableEq b1] [Fintype b2] [DecidableEq b2]
    [Fintype a'] [DecidableEq a'] [Fintype b'] [DecidableEq b']
    (ω : State ((a1 × a2) × (b1 × b2)))
    (eA : (a1 × a2) ≃ a') (eB : (b1 × b2) ≃ b') :
    entanglementOfFormation (ω.reindex (Equiv.prodCongr eA eB)) =
      entanglementOfFormation ω :=
  le_antisymm (entanglementOfFormation_reindex_le ω eA eB) <| by
    have hle := entanglementOfFormation_reindex_le
      (ω.reindex (eA.prodCongr eB)) eA.symm eB.symm
    rwa [state_reindex_reindex, prodCongr_trans_prodCongr_symm eA eB,
      State.reindex_refl] at hle

/-! ### IID tensor powers of a bipartite state -/

/-- The `(n+1)`-fold IID bipartite tensor power is one copy of `ρ` tensored
with the `n`-fold remainder, reassociated so that the bipartition is
`A A^n | B B^n`.  This is the shape consumed by the strong additivity of
`E_F` on products. -/
theorem tensorPowerBipartite_succ (rho : State (a × c)) (n : ℕ) :
    rho.tensorPowerBipartite (n + 1) =
      (rho.prod (rho.tensorPowerBipartite n)).reindex prodReassoc := by
  apply State.ext
  ext x y
  rcases x with ⟨⟨xA, xsA⟩, ⟨xB, xsB⟩⟩
  rcases y with ⟨⟨yA, ysA⟩, ⟨yB, ysB⟩⟩
  simp [State.tensorPowerBipartite, State.tensorPower_succ, prodReassoc,
    tensorPowerProdEquiv, State.prod, State.reindex, Matrix.kronecker,
    Matrix.kroneckerMap_apply]

/-- The entanglement of formation of the zeroth tensor power vanishes: the
carrier is the trivial system on both sides, so every decomposition branch
has a one-dimensional (zero-entropy) marginal. -/
theorem entanglementOfFormation_tensorPowerBipartite_zero (rho : State (a × c)) :
    entanglementOfFormation (rho.tensorPowerBipartite 0) = 0 := by
  refine le_antisymm ?_ (entanglementOfFormation_nonneg _)
  have hroof := entanglementOfFormation_le_entanglementCost
    (spectralPureDecomposition (rho.tensorPowerBipartite 0))
  have hcost : (spectralPureDecomposition (rho.tensorPowerBipartite 0)).entanglementCost
      = 0 := by
    have hz : ∀ i : Fin (spectralPureDecomposition (rho.tensorPowerBipartite 0)).card,
        ((spectralPureDecomposition (rho.tensorPowerBipartite 0)).vectors i).state.marginalA.vonNeumann
          = 0 :=
      fun i => State.vonNeumann_punit_eq_zero _
    simp [PureDecomposition.entanglementCost, hz]
  simpa [hcost] using hroof

/-- **Corollary 7, second half: exact `n`-copy multiplicativity.**  If the
two-qubit state `ρ` has a nonzero product vector `u ⊗ v` in its kernel, then
for every `n` the entanglement of formation of the `n`-fold IID tensor power
of `ρ`, read across the `A^n | B^n` bipartition, is exactly `n · E_F(ρ)`. -/
theorem entanglementOfFormation_tensorPowerBipartite_eq
    (h : woottersKernelUpperBound)
    (rho : State (Qubit × Qubit)) (u v : Qubit → ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hk : rho.matrix *ᵥ (fun p => u p.1 * v p.2) = 0) (n : ℕ) :
    entanglementOfFormation (rho.tensorPowerBipartite n) =
      n * entanglementOfFormation rho := by
  induction n with
  | zero =>
      rw [entanglementOfFormation_tensorPowerBipartite_zero, Nat.cast_zero,
        zero_mul]
  | succ m ih =>
      -- Regroup the `(m+1)`-fold tensor power as one copy times the rest;
      -- stated as a separate step because the regrouped carrier is only
      -- definitionally (not syntactically) the tensor-power carrier.
      have hEF : entanglementOfFormation (rho.tensorPowerBipartite (m + 1)) =
          entanglementOfFormation
            ((rho.prod (rho.tensorPowerBipartite m)).reindex prodReassoc) := by
        rw [tensorPowerBipartite_succ]
        rfl
      rw [hEF, entanglementOfFormation_prod_eq h rho u v hu hv hk, ih,
        Nat.cast_succ]
      ring

/-! ### The entanglement cost -/

/-- The entanglement cost of a bipartite state.

The paper defines `E_C(ρ)` as the limit `lim_n E_F(ρ^⊗n)/n`
(eq. `(ec-definition)`); that limit exists for the subadditive sequences
considered here.  We regularize by the infimum of the same sequence, which is
defined unconditionally; `tendsto_entanglementCost` below shows that the
limit form gives the same value for every state covered by Corollary 7,
because the sequence is then constant.  Nonemptiness is witnessed by `n = 1`. -/
def entanglementCost (rho : State (a × c)) : ℝ :=
  sInf {r | ∃ n : ℕ, 0 < n ∧
    r = entanglementOfFormation (rho.tensorPowerBipartite n) / ((n : ℕ) : ℝ)}

/-- **`E_C = E_F` for states with a product kernel vector.**  Under the
hypothesis of Corollary 7 the sequence being regularized is constant at
`E_F(ρ)`, so the entanglement cost equals the entanglement of formation. -/
theorem entanglementCost_eq (h : woottersKernelUpperBound)
    (rho : State (Qubit × Qubit)) (u v : Qubit → ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hk : rho.matrix *ᵥ (fun p => u p.1 * v p.2) = 0) :
    entanglementCost rho = entanglementOfFormation rho := by
  have hmem : entanglementOfFormation rho ∈
      {r | ∃ n : ℕ, 0 < n ∧
        r = entanglementOfFormation (rho.tensorPowerBipartite n) / ((n : ℕ) : ℝ)} := by
    refine ⟨1, Nat.one_pos, ?_⟩
    rw [entanglementOfFormation_tensorPowerBipartite_eq h rho u v hu hv hk 1]
    simp
  have hbdd : BddBelow
      {r | ∃ n : ℕ, 0 < n ∧
        r = entanglementOfFormation (rho.tensorPowerBipartite n) / ((n : ℕ) : ℝ)} := by
    refine ⟨0, ?_⟩
    rintro r ⟨n, hn, rfl⟩
    exact div_nonneg (entanglementOfFormation_nonneg _) (by positivity)
  refine le_antisymm (csInf_le hbdd hmem) (le_csInf ⟨entanglementOfFormation rho, hmem⟩ ?_)
  rintro r ⟨n, hn, rfl⟩
  rw [entanglementOfFormation_tensorPowerBipartite_eq h rho u v hu hv hk n,
    mul_div_cancel_left₀ _ (Nat.cast_pos.mpr hn).ne']

/-- The paper's limit form of the entanglement cost: under the hypothesis of
Corollary 7 the regularizing sequence is constant at `E_F(ρ)`, so it tends to
`E_F(ρ)`. -/
theorem tendsto_entanglementCost (h : woottersKernelUpperBound)
    (rho : State (Qubit × Qubit)) (u v : Qubit → ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hk : rho.matrix *ᵥ (fun p => u p.1 * v p.2) = 0) :
    Filter.Tendsto
      (fun n : ℕ =>
        entanglementOfFormation (rho.tensorPowerBipartite (n + 1)) /
          (((n : ℕ) : ℝ) + 1))
      Filter.atTop (𝓝 (entanglementOfFormation rho)) := by
  have hconst :
      (fun n : ℕ =>
        entanglementOfFormation (rho.tensorPowerBipartite (n + 1)) /
          (((n : ℕ) : ℝ) + 1)) =
        fun (_ : ℕ) => entanglementOfFormation rho := by
    funext n
    rw [entanglementOfFormation_tensorPowerBipartite_eq h rho u v hu hv hk (n + 1),
      Nat.cast_succ,
      mul_div_cancel_left₀ _ (by positivity : (0 : ℝ) < (((n : ℕ) : ℝ) + 1)).ne']
  rw [hconst]
  exact tendsto_const_nhds

/-- **`E_C = E_F` for two-qubit states of rank at most two.**  Such states
have a nonzero product kernel vector, so the previous theorem applies. -/
theorem entanglementCost_eq_of_rank_le_two (h : woottersKernelUpperBound)
    (rho : State (Qubit × Qubit))
    (hrank : (Finset.univ.filter
        (fun i : Qubit × Qubit => rho.pos.isHermitian.eigenvalues i ≠ 0)).card
      ≤ 2) :
    entanglementCost rho = entanglementOfFormation rho := by
  obtain ⟨u, v, hu, hv, hk⟩ :=
    exists_product_kernelVector_of_rank_le_two rho hrank
  exact entanglementCost_eq h rho u v hu hv hk

/-! ### The Choi state (eq. `(choi-cost)`) -/

/-- The computational basis vector `|0⟩` is nonzero. -/
theorem qubitKet0_ne_zero : qubitKet0 ≠ 0 := by
  intro hcon
  have h0 : qubitKet0 0 = (0 : Qubit → ℂ) 0 := congrFun hcon 0
  simp at h0

/-- The computational basis vector `|1⟩` is nonzero. -/
theorem qubitKet1_ne_zero : qubitKet1 ≠ 0 := by
  intro hcon
  have h0 : qubitKet1 1 = (0 : Qubit → ℂ) 1 := congrFun hcon 1
  simp at h0

/-- The product kernel-vector hypothesis of Corollary 7 for the Choi state:
`ω_p · (|0⟩ ⊗ |1⟩) = 0`. -/
theorem choiState_matrix_mulVec_qubitKet0_qubitKet1 (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix *ᵥ (fun q => qubitKet0 q.1 * qubitKet1 q.2) = 0 := by
  have h0 := choiState_ket01_kernel p hp0 hp1
  rwa [ket01_eq] at h0

/-- **Eq. `(choi-cost)`, `n`-copy form.**  The entanglement of formation of
the `n`-fold IID tensor power of the amplitude-damping Choi state `ω_p` is
`n · h₂((1 + √p)/2)`. -/
theorem choiState_entanglementOfFormation_tensorPowerBipartite
    (h : woottersKernelUpperBound) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) :
    entanglementOfFormation ((choiState p hp0 hp1).tensorPowerBipartite n) =
      n * binaryEntropy ((1 + Real.sqrt p) / 2) := by
  rw [entanglementOfFormation_tensorPowerBipartite_eq h (choiState p hp0 hp1)
    qubitKet0 qubitKet1 qubitKet0_ne_zero qubitKet1_ne_zero
    (choiState_matrix_mulVec_qubitKet0_qubitKet1 p hp0 hp1) n,
    choiState_entanglementOfFormation_eq_binaryEntropy h p hp0 hp1]

/-- **Eq. `(choi-cost)`, cost form (boxed).**  The entanglement cost of the
amplitude-damping Choi state `ω_p` is the binary entropy
`h₂((1 + √p)/2)`. -/
theorem choiState_entanglementCost (h : woottersKernelUpperBound) (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementCost (choiState p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  rw [entanglementCost_eq h (choiState p hp0 hp1)
    qubitKet0 qubitKet1 qubitKet0_ne_zero qubitKet1_ne_zero
    (choiState_matrix_mulVec_qubitKet0_qubitKet1 p hp0 hp1),
    choiState_entanglementOfFormation_eq_binaryEntropy h p hp0 hp1]

end

end AmplitudeDamping
