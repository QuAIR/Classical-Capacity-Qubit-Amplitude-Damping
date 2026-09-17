import AmplitudeDamping.StrongSuperadditivity
import QIT.Coding.Classical.HSWLimit

/-!
# Product decompositions and the reverse convex-roof inequality
-/

open scoped BigOperators NNReal

namespace AmplitudeDamping

open QIT

universe u v w x

noncomputable section

variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

namespace PureDecomposition

/-- Product of two finite pure-state decompositions. -/
def prod (E : PureDecomposition a) (F : PureDecomposition c) :
    PureDecomposition (Prod a c) :=
  ofFinite
    (ι := Prod (Fin E.card) (Fin F.card))
    (fun z => E.probs z.1 * F.probs z.2)
    (by
      rw [Fintype.sum_prod_type]
      simp_rw [← Finset.mul_sum, F.weights_sum, mul_one]
      exact E.weights_sum)
    (fun z => (E.vectors z.1).prod (F.vectors z.2))

@[simp]
theorem prod_averageState (E : PureDecomposition a)
    (F : PureDecomposition c) :
    (E.prod F).averageState = E.averageState.prod F.averageState := by
  apply State.ext
  rw [PureDecomposition.averageState, Ensemble.averageState_matrix]
  change
    (∑ k : Fin (Fintype.card (Prod (Fin E.card) (Fin F.card))),
      (((E.probs ((Fintype.equivFin
          (Prod (Fin E.card) (Fin F.card))).symm k).1 *
        F.probs ((Fintype.equivFin
          (Prod (Fin E.card) (Fin F.card))).symm k).2 : ℝ≥0) : ℂ) •
        ((E.vectors ((Fintype.equivFin
          (Prod (Fin E.card) (Fin F.card))).symm k).1).prod
          (F.vectors ((Fintype.equivFin
            (Prod (Fin E.card) (Fin F.card))).symm k).2)).state.matrix)) = _
  calc
    _ = ∑ z : Prod (Fin E.card) (Fin F.card),
        ((E.probs z.1 * F.probs z.2 : ℝ≥0) : ℂ) •
          ((E.vectors z.1).prod (F.vectors z.2)).state.matrix := by
      exact Fintype.sum_equiv
        (Fintype.equivFin (Prod (Fin E.card) (Fin F.card))).symm
        _ _ (fun _ => rfl)
    _ = (E.toEnsemble.prod F.toEnsemble).averageState.matrix := by
      rw [Ensemble.averageState_matrix]
      apply Finset.sum_congr rfl
      intro z _
      rw [PureVector.prod_state]
      rfl
    _ = (E.averageState.prod F.averageState).matrix := by
      exact congrArg State.matrix (Ensemble.prod_averageState
        E.toEnsemble F.toEnsemble)

/-- The product decomposition cost is exactly additive for the product
channel. -/
theorem prod_outputCost (Phi : Channel a b) (Psi : Channel c d)
    (E : PureDecomposition a) (F : PureDecomposition c) :
    (E.prod F).outputCost (Phi.prod Psi) =
      E.outputCost Phi + F.outputCost Psi := by
  unfold PureDecomposition.outputCost outputEntropyCost
  change
    (∑ k : Fin (Fintype.card (Prod (Fin E.card) (Fin F.card))),
      (E.probs ((Fintype.equivFin
          (Prod (Fin E.card) (Fin F.card))).symm k).1 *
        F.probs ((Fintype.equivFin
          (Prod (Fin E.card) (Fin F.card))).symm k).2).toReal *
        ((Phi.prod Psi).applyState
          ((E.vectors ((Fintype.equivFin
            (Prod (Fin E.card) (Fin F.card))).symm k).1).prod
            (F.vectors ((Fintype.equivFin
              (Prod (Fin E.card) (Fin F.card))).symm k).2)).state).vonNeumann) = _
  calc
    _ = ∑ z : Prod (Fin E.card) (Fin F.card),
        (E.probs z.1 * F.probs z.2).toReal *
          ((Phi.prod Psi).applyState
            ((E.vectors z.1).prod (F.vectors z.2)).state).vonNeumann := by
      exact Fintype.sum_equiv
        (Fintype.equivFin (Prod (Fin E.card) (Fin F.card))).symm
        _ _ (fun _ => rfl)
    _ = ∑ i : Fin E.card, ∑ j : Fin F.card,
        (E.probs i).toReal * (F.probs j).toReal *
          ((Phi.applyState (E.vectors i).state).vonNeumann +
            (Psi.applyState (F.vectors j).state).vonNeumann) := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      apply Finset.sum_congr rfl
      intro j _
      rw [PureVector.prod_state, Channel.applyState_prod,
        State.vonNeumann_prod, NNReal.coe_mul]
    _ = E.outputCost Phi + F.outputCost Psi := by
      let s : Fin E.card → ℝ := fun i =>
        (Phi.applyState (E.vectors i).state).vonNeumann
      let t : Fin F.card → ℝ := fun j =>
        (Psi.applyState (F.vectors j).state).vonNeumann
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

/-- Convex-roof output entropy is subadditive on product input states. -/
theorem outputEntropyRoof_prod_le
    (Phi : Channel a b) (Psi : Channel c d) (rho : State a) (sigma : State c) :
    outputEntropyRoof (Phi.prod Psi) (rho.prod sigma) ≤
      outputEntropyRoof Phi rho + outputEntropyRoof Psi sigma := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨x, hx, hxlt⟩ := Real.lt_sInf_add_pos
    (pureOutputEntropyValues_nonempty Phi rho) (half_pos hε)
  obtain ⟨E, hErho, rfl⟩ := hx
  obtain ⟨y, hy, hylt⟩ := Real.lt_sInf_add_pos
    (pureOutputEntropyValues_nonempty Psi sigma) (half_pos hε)
  obtain ⟨F, hFsigma, rfl⟩ := hy
  have hroof := outputEntropyRoof_le_outputCost (Phi.prod Psi) (E.prod F)
  rw [PureDecomposition.prod_averageState, hErho, hFsigma,
    PureDecomposition.prod_outputCost] at hroof
  have hxlt' : E.outputCost Phi < outputEntropyRoof Phi rho + ε / 2 := by
    simpa [outputEntropyRoof] using hxlt
  have hylt' : F.outputCost Psi < outputEntropyRoof Psi sigma + ε / 2 := by
    simpa [outputEntropyRoof] using hylt
  linarith

/-- Exact additivity on product inputs when one factor is amplitude damping. -/
theorem amplitudeDamping_outputEntropyRoof_prod_eq
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Phi : Channel a b) (rho : State Qubit) (sigma : State a) :
    outputEntropyRoof ((amplitudeDamping p hp0 hp1).prod Phi)
        (rho.prod sigma) =
      outputEntropyRoof (amplitudeDamping p hp0 hp1) rho +
        outputEntropyRoof Phi sigma := by
  apply le_antisymm
  · exact outputEntropyRoof_prod_le
      (amplitudeDamping p hp0 hp1) Phi rho sigma
  · have h := amplitudeDamping_outputEntropyRoof_stronglySuperadditive
      p hp0 hp1 Phi (rho.prod sigma)
    have hA : (rho.prod sigma).marginalA = rho := by
      apply State.ext
      exact State.partialTraceB_prod rho sigma
    have hB : (rho.prod sigma).marginalB = sigma := by
      apply State.ext
      exact State.partialTraceA_prod rho sigma
    rw [hA, hB] at h
    exact h

end

end AmplitudeDamping
