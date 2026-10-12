import AmplitudeDamping.TwoExpectations
import AmplitudeDamping.SupportCriterion

/-!
# The corner formula from two fixed expectations

Preserving the real and imaginary parts of the `00,11` coherence in every
pure component preserves its concurrence whenever the `01` population is
zero. Thus the same classical two-expectation theorem used for general
support SSA also proves the old Wootters corner interface; the full Wootters
formula and a spin-flip spectral calculation are not needed on this route.
-/
namespace AmplitudeDamping
open QIT
open scoped BigOperators NNReal ComplexConjugate Matrix ComplexOrder MatrixOrder
noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Hermitian observable extracting the real part of one density entry. -/
def entryRealObservable (i j : a) : Matrix a a ℂ :=
  (1 / 2 : ℂ) • (Matrix.single j i 1 + Matrix.single i j 1)

/-- Hermitian observable extracting the imaginary part of one density entry. -/
def entryImagObservable (i j : a) : Matrix a a ℂ :=
  (Complex.I / 2) • (Matrix.single i j 1 - Matrix.single j i 1)

omit [Fintype a] in
theorem entryRealObservable_isHermitian (i j : a) :
    (entryRealObservable i j).IsHermitian := by
  simp [entryRealObservable, Matrix.IsHermitian,
    Matrix.conjTranspose_add, Matrix.conjTranspose_single, add_comm]

omit [Fintype a] in
theorem entryImagObservable_isHermitian (i j : a) :
    (entryImagObservable i j).IsHermitian := by
  simp [entryImagObservable, Matrix.IsHermitian, Matrix.conjTranspose_smul,
    Matrix.conjTranspose_sub, Matrix.conjTranspose_single]
  module

theorem entryRealObservable_expectation (rho : State a) (i j : a) :
    operatorExpectation (entryRealObservable i j) rho = (rho.matrix i j).re := by
  have hji : rho.matrix j i = star (rho.matrix i j) :=
    (rho.pos.isHermitian.apply j i).symm
  simp [operatorExpectation, entryRealObservable, Matrix.add_mul, Matrix.trace_add, Matrix.trace_single_mul, smul_eq_mul,
    hji, Complex.mul_re, div_eq_mul_inv]
  ring

theorem entryImagObservable_expectation (rho : State a) (i j : a) :
    operatorExpectation (entryImagObservable i j) rho = (rho.matrix i j).im := by
  have hji : rho.matrix j i = star (rho.matrix i j) :=
    (rho.pos.isHermitian.apply j i).symm
  simp [operatorExpectation, entryImagObservable, Matrix.sub_mul,
    Matrix.trace_smul, Matrix.trace_sub, Matrix.trace_single_mul, smul_eq_mul,
    hji, Complex.mul_re, div_eq_mul_inv]
  ring

/-- The existing corner interface follows from the standard two-expectation
decomposition theorem, without importing the full Wootters formula. -/
theorem woottersKernelUpperBound_of_twoExpectations : woottersKernelUpperBound := by
  intro rho hzero
  obtain ⟨E, hE, hcomponents⟩ := twoExpectationDecomposition _ rho
    (entryRealObservable (0,0) (1,1)) (entryImagObservable (0,0) (1,1))
    (entryRealObservable_isHermitian _ _) (entryImagObservable_isHermitian _ _)
  have hcoh (j : Fin E.card) :
      (E.vectors j).state.matrix (0,0) (1,1) = rho.matrix (0,0) (1,1) := by
    apply Complex.ext
    · simpa only [entryRealObservable_expectation] using (hcomponents j).2.2.1
    · simpa only [entryImagObservable_expectation] using (hcomponents j).2.2.2
  have hbranch (j : Fin E.card) : (E.vectors j).state.marginalA.vonNeumann =
      entanglementCurve (2 * ‖rho.matrix (0,0) (1,1)‖) := by
    have hz : (E.vectors j).amp (0,1) = 0 :=
      pureDecomposition_amp_zero_of_diagonal_zero E (0,1)
        (by rwa [hE]) j (hcomponents j).1
    rw [pure_marginalA_vonNeumann, twoQubitAmplitudeMatrix_det, hz, zero_mul,
      sub_zero, ← hcoh j]
    simp only [PureVector.state_matrix_apply, norm_mul, norm_star]
  have hw : ∑ i, (E.probs i).toReal = 1 := by exact_mod_cast E.weights_sum
  calc
    entanglementOfFormation rho ≤ E.entanglementCost := by
      rw [← hE]
      exact entanglementOfFormation_le_entanglementCost E
    _ = _ := by
      unfold PureDecomposition.entanglementCost
      simp_rw [hbranch]
      rw [← Finset.sum_mul, hw, one_mul]
end
end AmplitudeDamping
