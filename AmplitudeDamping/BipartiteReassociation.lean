import AmplitudeDamping.Concurrence
import AmplitudeDamping.RoofProduct

/-!
# Bipartite reassociation and product additivity of E_F

A product of two bipartite states `ρ_AC ⊗ σ_BD` lives naturally on
`(A⊗C)⊗(B⊗D)`, but the entanglement of formation of the pair regards
`(A⊗B)` versus `(C⊗D)` as the split.  The equivalence `prodReassoc`
reassociates the four systems, and for pure factors the first marginal of
the reassociated product state is exactly the Kronecker product of the two
marginals, so the marginal entropy of a product branch is additive.

This yields the subadditivity (upper-bound) half of the manuscript's
Corollary 7: the entanglement of formation of the reassociated product is
at most the sum of the two entanglements of formation, built from arbitrary
near-optimal decompositions of the factors.
-/

open scoped BigOperators NNReal

namespace AmplitudeDamping

open QIT

universe u v w x

noncomputable section

/-- Reassociation `(A⊗C)⊗(B⊗D) ≃ (A⊗B)⊗(C⊗D)` of four systems. -/
def prodReassoc {a b c d : Type _} : (a × c) × (b × d) ≃ (a × b) × (c × d) where
  toFun x := ((x.1.1, x.2.1), (x.1.2, x.2.2))
  invFun y := ((y.1.1, y.2.1), (y.1.2, y.2.2))
  left_inv x := by simp
  right_inv y := by simp

@[simp]
theorem prodReassoc_apply {a b c d : Type _} (x : (a × c) × (b × d)) :
    prodReassoc x = ((x.1.1, x.2.1), (x.1.2, x.2.2)) :=
  rfl

@[simp]
theorem prodReassoc_symm_apply {a b c d : Type _} (y : (a × b) × (c × d)) :
    prodReassoc.symm y = ((y.1.1, y.2.1), (y.1.2, y.2.2)) :=
  rfl

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c]
variable [Fintype d] [DecidableEq d]

namespace PureDecomposition

/-- Reindex every pure vector of a decomposition by an equivalence on the
underlying system. -/
def reindexEquiv (E : PureDecomposition a) {β : Type _} [Fintype β]
    [DecidableEq β] (e : a ≃ β) : PureDecomposition β :=
  ofFinite (ι := Fin E.card) E.probs E.weights_sum
    (fun i => (E.vectors i).reindex e)

theorem reindexEquiv_averageState (E : PureDecomposition a) {β : Type _}
    [Fintype β] [DecidableEq β] (e : a ≃ β) :
    (E.reindexEquiv e).averageState = E.averageState.reindex e := by
  apply State.ext
  ext x y
  have h1 : ((E.reindexEquiv e).averageState).matrix x y =
      ∑ i : Fin E.card, (E.probs i) •
        (E.vectors i).state.matrix (e.symm x) (e.symm y) := by
    rw [PureDecomposition.averageState, Ensemble.averageState_matrix,
      Matrix.sum_apply]
    exact Fintype.sum_equiv (Fintype.equivFin (Fin E.card)).symm _ _
      (fun k => rfl)
  rw [h1, State.reindex_matrix, PureDecomposition.averageState,
    Ensemble.averageState_matrix, Matrix.submatrix_apply, Matrix.sum_apply]
  exact Finset.sum_congr rfl fun i _ => rfl

/-- The entanglement cost of a reindexed decomposition, branch by branch:
each component contributes its reindexed marginal entropy. -/
theorem reindexEquiv_entanglementCost (E : PureDecomposition (Prod a c))
    (e : Prod a c ≃ Prod b d) :
    (E.reindexEquiv e).entanglementCost =
      ∑ i : Fin E.card, (E.probs i).toReal *
        ((E.vectors i).reindex e).state.marginalA.vonNeumann := by
  rw [reindexEquiv, PureDecomposition.entanglementCost]
  exact Fintype.sum_equiv (Fintype.equivFin (Fin E.card)).symm _ _
    (fun _ => rfl)

end PureDecomposition

/-- The first marginal of a reassociated product pure state is the product
of the first marginals. -/
theorem pure_reassoc_marginalA (psi : PureVector (a × c))
    (phi : PureVector (b × d)) :
    ((psi.prod phi).state.reindex prodReassoc).marginalA =
      (psi.state.marginalA).prod (phi.state.marginalA) := by
  apply State.ext
  ext i k
  rcases i with ⟨i1, i2⟩
  rcases k with ⟨k1, k2⟩
  simp only [State.marginalA_matrix, State.reindex_matrix, partialTraceB,
    Matrix.submatrix_apply, prodReassoc_symm_apply, Fintype.sum_prod_type,
    State.prod, Matrix.kronecker, Matrix.kroneckerMap_apply,
    PureVector.state_matrix_apply, PureVector.prod_amp]
  rw [Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro j1 _
  apply Finset.sum_congr rfl
  intro j2 _
  rw [star_mul]
  ring

/-- Marginal entropy of a product branch is additive across the two
bipartitions. -/
theorem pure_reassoc_marginalA_vonNeumann (psi : PureVector (a × c))
    (phi : PureVector (b × d)) :
    (((psi.prod phi).reindex prodReassoc).state.marginalA).vonNeumann =
      psi.state.marginalA.vonNeumann + phi.state.marginalA.vonNeumann := by
  rw [PureVector.reindex_state, pure_reassoc_marginalA, State.vonNeumann_prod]

namespace PureDecomposition

/-- Product of two bipartite decompositions, reassociated so that the
split is `(A⊗B)` versus `(C⊗D)`. -/
def reassocProd (E : PureDecomposition (a × c))
    (F : PureDecomposition (b × d)) :
    PureDecomposition ((a × b) × (c × d)) :=
  (E.prod F).reindexEquiv prodReassoc

@[simp]
theorem reassocProd_averageState (E : PureDecomposition (a × c))
    (F : PureDecomposition (b × d)) :
    (E.reassocProd F).averageState =
      (E.averageState.prod F.averageState).reindex prodReassoc := by
  rw [reassocProd, reindexEquiv_averageState, PureDecomposition.prod_averageState]

/-- The entanglement cost of the reassociated product decomposition is
exactly additive. -/
theorem reassocProd_entanglementCost (E : PureDecomposition (a × c))
    (F : PureDecomposition (b × d)) :
    (E.reassocProd F).entanglementCost =
      E.entanglementCost + F.entanglementCost := by
  rw [reassocProd, reindexEquiv_entanglementCost]
  have hflat : ∑ i : Fin (E.prod F).card,
      ((E.prod F).probs i).toReal *
        (((E.prod F).vectors i).reindex prodReassoc).state.marginalA.vonNeumann =
    ∑ z : Prod (Fin E.card) (Fin F.card),
      (E.probs z.1 * F.probs z.2).toReal *
        (((E.vectors z.1).prod (F.vectors z.2)).reindex
          prodReassoc).state.marginalA.vonNeumann := by
    exact Fintype.sum_equiv
      (Fintype.equivFin (Prod (Fin E.card) (Fin F.card))).symm _ _
      (fun _ => rfl)
  rw [hflat]
  calc
    _ = ∑ i : Fin E.card, ∑ j : Fin F.card,
        (E.probs i).toReal * (F.probs j).toReal *
          ((E.vectors i).state.marginalA.vonNeumann +
            (F.vectors j).state.marginalA.vonNeumann) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [pure_reassoc_marginalA_vonNeumann, NNReal.coe_mul]
    _ = E.entanglementCost + F.entanglementCost := by
      let s : Fin E.card → ℝ := fun i =>
        (E.vectors i).state.marginalA.vonNeumann
      let t : Fin F.card → ℝ := fun j =>
        (F.vectors j).state.marginalA.vonNeumann
      have hEw : (∑ i, (E.probs i).toReal) = 1 := by
        have h := congrArg (fun z : ℝ≥0 => (z : ℝ)) E.weights_sum
        simpa using h
      have hFw : (∑ j, (F.probs j).toReal) = 1 := by
        have h := congrArg (fun z : ℝ≥0 => (z : ℝ)) F.weights_sum
        simpa using h
      change (∑ i, ∑ j,
        (E.probs i).toReal * (F.probs j).toReal * (s i + t j)) =
          (∑ i, (E.probs i).toReal * s i) +
            ∑ j, (F.probs j).toReal * t j
      simp_rw [mul_add, Finset.sum_add_distrib]
      have hleft :
          (∑ i, ∑ j, (E.probs i).toReal * (F.probs j).toReal * s i) =
            ∑ i, (E.probs i).toReal * s i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [show (∑ j, (E.probs i).toReal * (F.probs j).toReal * s i) =
            ((E.probs i).toReal * s i) * ∑ j, (F.probs j).toReal by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j _
          ring]
        rw [hFw, mul_one]
      have hright :
          (∑ i, ∑ j, (E.probs i).toReal * (F.probs j).toReal * t j) =
            ∑ j, (F.probs j).toReal * t j := by
        rw [Finset.sum_comm]
        apply Finset.sum_congr rfl
        intro j _
        rw [show (∑ i,
            (E.probs i).toReal * (F.probs j).toReal * t j) =
            (∑ i, (E.probs i).toReal) *
              ((F.probs j).toReal * t j) by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro i _
          ring]
        rw [hEw, one_mul]
      rw [hleft, hright]

end PureDecomposition

/-- Subadditivity of the entanglement of formation under reassociated
products: the `≤` half of Corollary 7, with no hypothesis beyond the
definitions. -/
theorem entanglementOfFormation_prod_reassoc_le
    (rho : State (a × c)) (sigma : State (b × d)) :
    entanglementOfFormation ((rho.prod sigma).reindex prodReassoc) ≤
      entanglementOfFormation rho + entanglementOfFormation sigma := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, hx, hxlt⟩ := Real.lt_sInf_add_pos
    (pureEntanglementValues_nonempty rho) (half_pos hε)
  obtain ⟨E, hErho, rfl⟩ := hx
  obtain ⟨y, hy, hylt⟩ := Real.lt_sInf_add_pos
    (pureEntanglementValues_nonempty sigma) (half_pos hε)
  obtain ⟨F, hFsigma, rfl⟩ := hy
  have hroof := entanglementOfFormation_le_entanglementCost
    (E.reassocProd F)
  rw [PureDecomposition.reassocProd_averageState, hErho, hFsigma,
    PureDecomposition.reassocProd_entanglementCost] at hroof
  have hxlt' : E.entanglementCost < entanglementOfFormation rho + ε / 2 := by
    simpa [entanglementOfFormation] using hxlt
  have hylt' : F.entanglementCost < entanglementOfFormation sigma + ε / 2 := by
    simpa [entanglementOfFormation] using hylt
  linarith

end

end AmplitudeDamping
