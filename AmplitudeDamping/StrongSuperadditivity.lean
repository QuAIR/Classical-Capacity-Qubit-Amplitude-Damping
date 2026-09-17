import AmplitudeDamping.PureAuxiliaryRoof

/-!
# Lifting the pure-input inequality to arbitrary states

The lift is separated from the analytic proof.  Its only general input is the
finite Jensen property of the two one-channel convex roofs.
-/

open scoped BigOperators NNReal

namespace AmplitudeDamping

open QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Ensemble of left marginals obtained from a pure decomposition of a
bipartite state. -/
def PureDecomposition.leftMarginalEnsemble
    (E : PureDecomposition (Prod Qubit a)) : Ensemble (Fin E.card) Qubit where
  probs := E.probs
  weights_sum := E.weights_sum
  states i := (E.vectors i).state.marginalA

/-- Ensemble of right marginals obtained from a pure decomposition of a
bipartite state. -/
def PureDecomposition.rightMarginalEnsemble
    (E : PureDecomposition (Prod Qubit a)) : Ensemble (Fin E.card) a where
  probs := E.probs
  weights_sum := E.weights_sum
  states i := (E.vectors i).state.marginalB

@[simp]
theorem PureDecomposition.leftMarginalEnsemble_averageState
    (E : PureDecomposition (Prod Qubit a)) :
    E.leftMarginalEnsemble.averageState = E.averageState.marginalA := by
  apply State.ext
  rw [Ensemble.averageState_matrix, State.marginalA_matrix,
    PureDecomposition.averageState, Ensemble.averageState_matrix]
  change (∑ i, (E.probs i : ℂ) • partialTraceB (E.vectors i).state.matrix) =
    partialTraceB (∑ i, (E.probs i : ℂ) • (E.vectors i).state.matrix)
  ext x y
  simp [partialTraceB, Matrix.sum_apply, Matrix.smul_apply,
    Finset.mul_sum]
  rw [Finset.sum_comm]

@[simp]
theorem PureDecomposition.rightMarginalEnsemble_averageState
    (E : PureDecomposition (Prod Qubit a)) :
    E.rightMarginalEnsemble.averageState = E.averageState.marginalB := by
  apply State.ext
  rw [Ensemble.averageState_matrix, State.marginalB_matrix,
    PureDecomposition.averageState, Ensemble.averageState_matrix]
  change (∑ i, (E.probs i : ℂ) • partialTraceA (E.vectors i).state.matrix) =
    partialTraceA (∑ i, (E.probs i : ℂ) • (E.vectors i).state.matrix)
  ext x y
  simp [partialTraceA, Matrix.sum_apply, Matrix.smul_apply]
  rw [Finset.sum_add_distrib]

/-- The pure-input bound plus finite Jensen for the factor roofs implies full
strong superadditivity of the concrete output-entropy convex roof. -/
theorem amplitudeDamping_outputEntropyRoof_stronglySuperadditive_of_finiteJensen
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Phi : Channel a b)
    (hleft : SatisfiesFiniteJensen
      (outputEntropyRoof (amplitudeDamping p hp0 hp1)))
    (hright : SatisfiesFiniteJensen (outputEntropyRoof Phi)) :
    StronglySuperadditiveFor
      (outputEntropyRoof ((amplitudeDamping p hp0 hp1).prod Phi))
      (outputEntropyRoof (amplitudeDamping p hp0 hp1))
      (outputEntropyRoof Phi) := by
  intro rho
  apply le_csInf (pureOutputEntropyValues_nonempty
    ((amplitudeDamping p hp0 hp1).prod Phi) rho)
  intro x hx
  rcases hx with ⟨E, hErho, rfl⟩
  have hpure (i : Fin E.card) :=
    pureAuxiliary_outputEntropy_ge_roofs p hp0 hp1 Phi (E.vectors i)
  have hweighted :
      (∑ i, (E.probs i).toReal *
        (outputEntropyRoof (amplitudeDamping p hp0 hp1)
            (E.vectors i).state.marginalA +
          outputEntropyRoof Phi (E.vectors i).state.marginalB)) ≤
        E.outputCost ((amplitudeDamping p hp0 hp1).prod Phi) := by
    unfold PureDecomposition.outputCost outputEntropyCost
    exact Finset.sum_le_sum fun i _ =>
      mul_le_mul_of_nonneg_left (hpure i) (NNReal.coe_nonneg _)
  have hL := hleft E.leftMarginalEnsemble
  have hR := hright E.rightMarginalEnsemble
  rw [PureDecomposition.leftMarginalEnsemble_averageState] at hL
  rw [PureDecomposition.rightMarginalEnsemble_averageState] at hR
  rw [hErho] at hL hR
  simp only [PureDecomposition.leftMarginalEnsemble,
    PureDecomposition.rightMarginalEnsemble] at hL hR
  simp_rw [mul_add] at hweighted
  rw [Finset.sum_add_distrib] at hweighted
  linarith

/-- Strong superadditivity of the output-entropy convex roof for amplitude
damping tensored with an arbitrary finite-dimensional channel. -/
theorem amplitudeDamping_outputEntropyRoof_stronglySuperadditive
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (Phi : Channel a b) :
    StronglySuperadditiveFor
      (outputEntropyRoof ((amplitudeDamping p hp0 hp1).prod Phi))
      (outputEntropyRoof (amplitudeDamping p hp0 hp1))
      (outputEntropyRoof Phi) :=
  amplitudeDamping_outputEntropyRoof_stronglySuperadditive_of_finiteJensen
    p hp0 hp1 Phi
    (outputEntropyRoof_satisfiesFiniteJensen _)
    (outputEntropyRoof_satisfiesFiniteJensen _)

end

end AmplitudeDamping
