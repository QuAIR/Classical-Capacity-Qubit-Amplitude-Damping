import AmplitudeDamping.ChannelStinespring

/-!
# Pure bipartite inputs and the auxiliary-channel coefficient blocks
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Excited-qubit branch of a pure input on `Qubit x a`. -/
def pureExcitedBranch (psi : PureVector (Prod Qubit a)) : a → ℂ :=
  fun x => psi.amp (1, x)

/-- Ground-qubit branch of a pure input on `Qubit x a`. -/
def pureGroundBranch (psi : PureVector (Prod Qubit a)) : a → ℂ :=
  fun x => psi.amp (0, x)

/-- Squared norm of the excited branch. -/
def pureAuxiliaryExcitation (psi : PureVector (Prod Qubit a)) : ℝ :=
  ∑ x, Complex.normSq (pureExcitedBranch psi x)

@[simp]
theorem pureExcitedBranch_rankOne_trace_re
    (psi : PureVector (Prod Qubit a)) :
    (rankOneMatrix (pureExcitedBranch psi)).trace.re =
      pureAuxiliaryExcitation psi := by
  simp [rankOneMatrix_trace, dotProduct, Complex.mul_conj,
    pureAuxiliaryExcitation]

theorem pureAuxiliaryExcitation_nonneg (psi : PureVector (Prod Qubit a)) :
    0 ≤ pureAuxiliaryExcitation psi := by
  exact Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _

/-- The two qubit branches have complementary squared norms. -/
theorem pureGroundBranch_normSq_sum
    (psi : PureVector (Prod Qubit a)) :
    (∑ x, Complex.normSq (pureGroundBranch psi x)) =
      1 - pureAuxiliaryExcitation psi := by
  have hnorm :
      (∑ i : Qubit, ∑ x : a, Complex.normSq (psi.amp (i, x))) = 1 := by
    have h := congrArg Complex.re psi.trace_rankOne_eq_one
    simpa [rankOneMatrix_trace, dotProduct, Complex.mul_conj,
      Fintype.sum_prod_type] using h
  rw [Fin.sum_univ_two] at hnorm
  unfold pureGroundBranch pureAuxiliaryExcitation
  simp only [pureExcitedBranch]
  linarith

@[simp]
theorem pureGroundBranch_rankOne_trace_re
    (psi : PureVector (Prod Qubit a)) :
    (rankOneMatrix (pureGroundBranch psi)).trace.re =
      1 - pureAuxiliaryExcitation psi := by
  simp [rankOneMatrix_trace, dotProduct, Complex.mul_conj,
    pureGroundBranch_normSq_sum]

theorem pureAuxiliaryExcitation_le_one (psi : PureVector (Prod Qubit a)) :
    pureAuxiliaryExcitation psi ≤ 1 := by
  have hground : 0 ≤ ∑ x, Complex.normSq (pureGroundBranch psi x) :=
    Finset.sum_nonneg fun i _ => Complex.normSq_nonneg _
  rw [pureGroundBranch_normSq_sum] at hground
  linarith

/-- The branch weight is the excitation probability of the qubit marginal. -/
theorem pureAuxiliaryExcitation_eq_marginal
    (psi : PureVector (Prod Qubit a)) :
    pureAuxiliaryExcitation psi = stateExcitation psi.state.marginalA := by
  unfold pureAuxiliaryExcitation pureExcitedBranch stateExcitation
  rw [State.marginalA_matrix, PureVector.state_matrix]
  simp [partialTraceB, rankOneMatrix_apply, Complex.mul_conj]

/-- The auxiliary marginal of a bipartite pure vector is the sum of the two
unnormalized branch projectors. -/
theorem pure_marginalB_matrix_eq_branch_rankOne_sum
    (psi : PureVector (Prod Qubit a)) :
    psi.state.marginalB.matrix =
      rankOneMatrix (pureExcitedBranch psi) +
        rankOneMatrix (pureGroundBranch psi) := by
  ext x y
  simp [State.marginalB_matrix, partialTraceA,
    rankOneMatrix_apply, pureExcitedBranch, pureGroundBranch,
    Fin.sum_univ_two]
  ring

/-- The triangular coefficient-matrix bound for a pure bipartite input and an
arbitrary auxiliary channel.  This is the matrix core of the pure-input
strong-superadditivity step. -/
theorem pureAuxiliary_triangularCoefficient_bound
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Phi : Channel a b) (psi : PureVector (Prod Qubit a)) :
    let q := pureAuxiliaryExcitation psi
    let A := Phi.stinespringCoefficientMatrix (pureExcitedBranch psi)
    let B := Phi.stinespringCoefficientMatrix (pureGroundBranch psi)
    let M : Matrix (Sum b b) (Sum (Prod a b) (Prod a b)) ℂ :=
      Matrix.fromBlocks ((Real.sqrt (1 - p) : ℂ) • A) 0 B
        ((Real.sqrt p : ℂ) • A)
    psdEntropy (M * M.conjTranspose)
        (Matrix.posSemidef_self_mul_conjTranspose M) ≥
      dampingEntropyCurve p q +
        normalizedGramEntropy q A + normalizedGramEntropy (1 - q) B := by
  dsimp only
  let q := pureAuxiliaryExcitation psi
  let A := Phi.stinespringCoefficientMatrix (pureExcitedBranch psi)
  let B := Phi.stinespringCoefficientMatrix (pureGroundBranch psi)
  have hA : frobeniusSq A = q := by
    rw [show frobeniusSq A =
        ∑ x, Complex.normSq (pureExcitedBranch psi x) by
      exact Phi.frobeniusSq_stinespringCoefficientMatrix
        (pureExcitedBranch psi)]
    rfl
  have hB : frobeniusSq B = 1 - q := by
    rw [show frobeniusSq B =
        ∑ x, Complex.normSq (pureGroundBranch psi x) by
      exact Phi.frobeniusSq_stinespringCoefficientMatrix
        (pureGroundBranch psi)]
    exact pureGroundBranch_normSq_sum psi
  exact amplitudeDamping_triangular_entropy_lower_bound
    p q hp0 hp1 A B hA hB

end

end AmplitudeDamping
