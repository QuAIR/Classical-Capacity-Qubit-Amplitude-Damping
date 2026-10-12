import AmplitudeDamping.SupportCriterion
import AmplitudeDamping.SupportedPureEntropy
import AmplitudeDamping.TwoExpectations

/-!
# The supported marginal formation bound

The only classical input is the exact two-expectation decomposition theorem.
The sector projectors, their expectations, support inheritance and the
formation upper bound are proved for arbitrary finite sector dimensions.
-/
namespace AmplitudeDamping
open QIT
open scoped BigOperators NNReal ComplexConjugate ComplexOrder MatrixOrder
noncomputable section
universe u v w x
variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- Projection onto `A₁ ⊗ |0_B⟩`. -/
def supportProjectorA : Matrix ((a ⊕ Unit) × (Unit ⊕ b)) ((a ⊕ Unit) × (Unit ⊕ b)) ℂ :=
  Matrix.diagonal fun z => match z with
    | (Sum.inl _, Sum.inl _) => 1
    | _ => 0

/-- Projection onto `|0_A⟩ ⊗ B₁`. -/
def supportProjectorB : Matrix ((a ⊕ Unit) × (Unit ⊕ b)) ((a ⊕ Unit) × (Unit ⊕ b)) ℂ :=
  Matrix.diagonal fun z => match z with
    | (Sum.inr _, Sum.inr _) => 1
    | _ => 0

omit [Fintype a] [Fintype b] in
theorem supportProjectorA_isHermitian :
    (supportProjectorA (a := a) (b := b)).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  rintro ⟨i|i,j|j⟩ <;> simp [IsSelfAdjoint]

omit [Fintype a] [Fintype b] in
theorem supportProjectorB_isHermitian :
    (supportProjectorB (a := a) (b := b)).IsHermitian := by
  apply Matrix.isHermitian_diagonal_iff.mpr
  rintro ⟨i|i,j|j⟩ <;> simp [IsSelfAdjoint]

theorem supportProjectorA_expectation (rho : State ((a ⊕ Unit) × (Unit ⊕ b))) :
    operatorExpectation supportProjectorA rho =
      ∑ i : a, (rho.matrix (Sum.inl i, Sum.inl ()) (Sum.inl i, Sum.inl ())).re := by
  simp [operatorExpectation, supportProjectorA, Matrix.trace, Matrix.diag,
    Matrix.diagonal_mul, Fintype.sum_prod_type, Fintype.sum_sum_type]

theorem supportProjectorB_expectation (rho : State ((a ⊕ Unit) × (Unit ⊕ b))) :
    operatorExpectation supportProjectorB rho =
      ∑ j : b, (rho.matrix (Sum.inr (), Sum.inr j) (Sum.inr (), Sum.inr j)).re := by
  simp [operatorExpectation, supportProjectorB, Matrix.trace, Matrix.diag,
    Matrix.diagonal_mul, Fintype.sum_prod_type, Fintype.sum_sum_type]

theorem supportProjectorA_pure_expectation (psi : PureVector ((a ⊕ Unit) × (Unit ⊕ b))) :
    operatorExpectation supportProjectorA psi.state = supportSectorWeightA psi := by
  rw [supportProjectorA_expectation]
  simp [supportSectorWeightA, PureVector.state_matrix_apply, Complex.mul_conj]

theorem supportProjectorB_pure_expectation (psi : PureVector ((a ⊕ Unit) × (Unit ⊕ b))) :
    operatorExpectation supportProjectorB psi.state = supportSectorWeightB psi := by
  rw [supportProjectorB_expectation]
  simp [supportSectorWeightB, PureVector.state_matrix_apply, Complex.mul_conj]

/-- The manuscript's scalar upper bound for a supported mixed marginal. -/
theorem supported_marginal_formation_upper_bound
    (hclassical : TwoExpectationDecomposition ((a ⊕ Unit) × (Unit ⊕ b)))
    (rho : State ((a ⊕ Unit) × (Unit ⊕ b))) (hs : HasSingleExcitationSupport rho) :
    entanglementOfFormation rho ≤ entanglementCurve (2 * Real.sqrt
      (operatorExpectation supportProjectorA rho * operatorExpectation supportProjectorB rho)) := by
  obtain ⟨E, hE, hcomponents⟩ := hclassical rho supportProjectorA supportProjectorB
    supportProjectorA_isHermitian supportProjectorB_isHermitian
  have hbranch (j : Fin E.card) : (E.vectors j).state.marginalA.vonNeumann =
      entanglementCurve (2 * Real.sqrt (operatorExpectation supportProjectorA rho *
        operatorExpectation supportProjectorB rho)) := by
    have hz (i : a) (k : b) : (E.vectors j).amp (Sum.inl i, Sum.inr k) = 0 := by
      apply pureDecomposition_amp_zero_of_diagonal_zero E _ _ j (hcomponents j).1
      rw [hE]
      exact hs i k
    rw [supported_pure_entropy _ hz, ← supportProjectorA_pure_expectation,
      ← supportProjectorB_pure_expectation, (hcomponents j).2.2.1,
      (hcomponents j).2.2.2]
  have hw : ∑ i, (E.probs i).toReal = 1 := by exact_mod_cast E.weights_sum
  calc
    entanglementOfFormation rho ≤ E.entanglementCost := by
      rw [← hE]
      exact entanglementOfFormation_le_entanglementCost E
    _ = _ := by
      unfold PureDecomposition.entanglementCost
      simp_rw [hbranch]
      rw [← Finset.sum_mul, hw, one_mul]

theorem supportProjectorA_extension_expectation
    (psi : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) :
    operatorExpectation supportProjectorA (psi.state.reindex prodReassoc).marginalA =
      frobeniusSq (supportBlockA psi) := by
  rw [supportProjectorA_expectation]
  simp [State.marginalA_matrix, partialTraceB, State.reindex_matrix,
    prodReassoc_symm_apply, Complex.mul_conj,
    frobeniusSq_eq_sum_normSq, supportBlockA, Fintype.sum_prod_type]

theorem supportProjectorB_extension_expectation
    (psi : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) :
    operatorExpectation supportProjectorB (psi.state.reindex prodReassoc).marginalA =
      frobeniusSq (supportBlockD psi) := by
  rw [supportProjectorB_expectation]
  simp [State.marginalA_matrix, partialTraceB, State.reindex_matrix,
    prodReassoc_symm_apply, Complex.mul_conj,
    frobeniusSq_eq_sum_normSq, supportBlockD, Fintype.sum_prod_type]
  exact Finset.sum_comm

end
end AmplitudeDamping
