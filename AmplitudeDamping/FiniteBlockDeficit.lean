import AmplitudeDamping.RelativeEntropySeparation
import AmplitudeDamping.ScalarOptimizer
import QIT.Information.Renyi.RenyiDPI.TraceLogBridge
import QIT.Channels.Diamond

/-! # Finite-block Holevo deficits

The exact deficit identity, nonnegativity of its three terms, the information-
radius bound, and attainment by the optimal product average are proved for all
blocklengths and correlated inputs. The real-valued relative entropy is identified
with QIT's support-aware `EReal` definition. Uniqueness uses the faithful-reference
equality case proved in `RelativeEntropySeparation`; the original
`FaithfulRelativeEntropyEquality` interface is discharged below.
-/

open scoped BigOperators ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT
noncomputable section

/-- Excess of the block output-entropy roof over its single-site lower bound. -/
def dampingRoofExcess (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (n : ℕ) (τ : State (TensorPower Qubit n)) : ℝ :=
  outputEntropyRoof ((amplitudeDamping p hp0 hp1).tensorPower n) τ -
    ∑ i, dampingEntropyCurve p (stateExcitation (siteStates n τ i))

/-- Iterating strong roof superadditivity makes the excess nonnegative. -/
theorem dampingRoofExcess_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ n (τ : State (TensorPower Qubit n)), 0 ≤ dampingRoofExcess p hp0 hp1 n τ := by
  intro n
  induction n with
  | zero =>
    intro τ
    simpa [dampingRoofExcess] using
      outputEntropyRoof_nonneg ((amplitudeDamping p hp0 hp1).tensorPower 0) τ
  | succ n ih =>
    intro τ
    have h := amplitudeDamping_outputEntropyRoof_stronglySuperadditive
      p hp0 hp1 ((amplitudeDamping p hp0 hp1).tensorPower n) τ
    have hi := ih τ.marginalB
    unfold dampingRoofExcess at hi ⊢
    rw [Channel.tensorPower_succ, Fin.sum_univ_succ]
    simp only [siteStates_succ, Fin.cons_zero, Fin.cons_succ]
    rw [outputEntropyRoof_eq_dampingEntropyCurve] at h
    exact sub_nonneg.mpr ((add_le_add_right (sub_nonneg.mp hi) _).trans h)

/-- The block sum of convexity remainders is nonnegative. -/
theorem dampingBregman_siteSum_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (n : ℕ) (τ : State (TensorPower Qubit n)) :
    0 ≤ ∑ i, dampingBregman p (optimalExcitation p hp0 hp1)
      (stateExcitation (siteStates n τ i)) := by
  apply Finset.sum_nonneg
  intro i _
  exact dampingBregman_nonneg p hp0 hp1 (optimalExcitation_mem_Ioo p hp0 hp1)
    ⟨stateExcitation_nonneg _, stateExcitation_le_one _⟩

/-- The optimal diagonal average input. -/
def dampingOptimalInput (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) : State Qubit :=
  diagonalQubitState (optimalExcitation p hp0 hp1)
    (optimalExcitation_mem_Ioo p hp0 hp1).1.le
    (optimalExcitation_mem_Ioo p hp0 hp1).2.le

/-- The optimal output reference. -/
def dampingOptimalOutput (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) : State Qubit :=
  (amplitudeDamping p hp0 hp1.le).applyState (dampingOptimalInput p hp0 hp1)

/-- The diagonal probability weights of a binary product reference. -/
def binaryProductWeight (s : ℝ) : (n : ℕ) → TensorPower Qubit n → ℝ
  | 0, _ => 1
  | n + 1, x => (if x.1 = 0 then 1 - s else s) * binaryProductWeight s n x.2

lemma binaryProductWeight_pos {s : ℝ} (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ n (x : TensorPower Qubit n), 0 < binaryProductWeight s n x := by
  intro n
  induction n with
  | zero => intro x; exact zero_lt_one
  | succ n ih =>
    intro x
    exact mul_pos (by split <;> linarith) (ih x.2)

lemma diagonalQubitState_tensorPower_matrix (s : ℝ) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    ∀ n, ((diagonalQubitState s hs0 hs1).tensorPower n).matrix =
      Matrix.diagonal (fun x => (binaryProductWeight s n x : ℂ)) := by
  intro n
  induction n with
  | zero =>
    ext x y
    cases x
    cases y
    simp [State.tensorPower, State.unit, binaryProductWeight]
  | succ n ih =>
    rw [State.tensorPower_succ]
    change Matrix.kronecker (diagonalQubitState s hs0 hs1).matrix
      ((diagonalQubitState s hs0 hs1).tensorPower n).matrix = _
    rw [ih]
    change Matrix.kronecker (Matrix.diagonal _) (Matrix.diagonal _) = _
    rw [Matrix.kronecker, Matrix.diagonal_kronecker_diagonal]
    congr 1
    funext x
    by_cases hx : x.1 = 0 <;> simp [binaryProductWeight, diagonalQubitProb, hx]
    all_goals left; norm_cast

lemma diagonalQubitState_tensorPower_posDef (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (n : ℕ) : ((diagonalQubitState s hs0.le hs1.le).tensorPower n).matrix.PosDef := by
  rw [diagonalQubitState_tensorPower_matrix]
  apply Matrix.PosDef.diagonal
  intro x
  exact_mod_cast binaryProductWeight_pos hs0 hs1 n x

/-- Expectation of the logarithm of a binary product reference. -/
def binaryLogExpectation (s : ℝ) (n : ℕ) (σ : State (TensorPower Qubit n)) : ℝ :=
  ∑ x, (σ.matrix x x).re * Real.log (binaryProductWeight s n x)

lemma binaryLogExpectation_eq_trace (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (n : ℕ) (σ : State (TensorPower Qubit n)) :
    binaryLogExpectation s n σ =
      (σ.matrix * State.psdLog ((diagonalQubitState s hs0.le hs1.le).tensorPower n).matrix
        (diagonalQubitState_tensorPower_posDef s hs0 hs1 n)).trace.re := by
  unfold State.psdLog
  rw [diagonalQubitState_tensorPower_matrix, QIT.cfc_diagonal_ofReal]
  simp [binaryLogExpectation, Matrix.trace, Matrix.mul_diagonal]

private lemma realPart_sum {ι : Type} [Fintype ι] (f : ι → ℂ) :
    (∑ i, f i).re = ∑ i, (f i).re :=
  map_sum Complex.reAddGroupHom f Finset.univ

lemma diagonal_expectation_add {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (σ : State (a × b)) (u : a → ℝ) (v : b → ℝ) :
    (∑ x : a × b, (σ.matrix x x).re * (u x.1 + v x.2)) =
      (∑ i, (σ.marginalA.matrix i i).re * u i) +
        ∑ j, (σ.marginalB.matrix j j).re * v j := by
  simp only [Fintype.sum_prod_type, mul_add, Finset.sum_add_distrib,
    State.marginalA_matrix, State.marginalB_matrix, partialTraceA, partialTraceB,
    realPart_sum, Finset.sum_mul]
  congr 1
  rw [Finset.sum_comm]

lemma binaryLogExpectation_succ (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1)
    (n : ℕ) (σ : State (TensorPower Qubit (n + 1))) :
    binaryLogExpectation s (n + 1) σ =
      (1 - stateExcitation σ.marginalA) * Real.log (1 - s) +
        stateExcitation σ.marginalA * Real.log s +
        binaryLogExpectation s n σ.marginalB := by
  unfold binaryLogExpectation
  have hlog (x : TensorPower Qubit (n + 1)) :
      Real.log (binaryProductWeight s (n + 1) x) =
        Real.log (if x.1 = 0 then 1 - s else s) +
          Real.log (binaryProductWeight s n x.2) := by
    apply Real.log_mul
    · split <;> linarith
    · exact (binaryProductWeight_pos hs0 hs1 n x.2).ne'
  simp_rw [hlog]
  trans (∑ i, (σ.marginalA.matrix i i).re *
      Real.log (if i = 0 then 1 - s else s)) +
      ∑ j, (σ.marginalB.matrix j j).re * Real.log (binaryProductWeight s n j)
  · exact diagonal_expectation_add σ
      (fun i => Real.log (if i = 0 then 1 - s else s))
      (fun j => Real.log (binaryProductWeight s n j))
  rw [Fin.sum_univ_two]
  simp [qubit_diagonal_zero, qubit_diagonal_one]

lemma binaryLogExpectation_eq (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) :
    ∀ n (σ : State (TensorPower Qubit n)),
      binaryLogExpectation s n σ =
        (n : ℝ) * Real.log (1 - s) +
          siteExcitationSum n σ * (Real.log s - Real.log (1 - s)) := by
  intro n
  induction n with
  | zero => intro σ; simp [binaryLogExpectation, binaryProductWeight, siteExcitationSum]
  | succ n ih =>
    intro σ
    rw [binaryLogExpectation_succ s hs0 hs1, ih, siteExcitationSum_succ]
    push_cast
    ring

/-- The finite real-valued relative entropy against a full-rank binary product. -/
def binaryProductRelativeEntropy (s : ℝ) (n : ℕ)
    (σ : State (TensorPower Qubit n)) : ℝ :=
  -σ.vonNeumann - binaryLogExpectation s n σ / Real.log 2

/-- The real-valued expression is exactly QIT's support-aware relative entropy. -/
theorem binaryProductRelativeEntropy_eq_relativeEntropy
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ)
    (σ : State (TensorPower Qubit n)) :
    (binaryProductRelativeEntropy s n σ : EReal) =
      σ.relativeEntropy ((diagonalQubitState s hs0.le hs1.le).tensorPower n) := by
  have hpd := diagonalQubitState_tensorPower_posDef s hs0 hs1 n
  rw [State.relativeEntropy_eq_coe_of_supports _ _
    (Matrix.Supports.of_right_posDef _ _ hpd)]
  congr 1
  rw [State.relativeEntropyPSDReferenceTraceLogFinite_eq_posDef_formula _ hpd]
  unfold binaryProductRelativeEntropy
  rw [binaryLogExpectation_eq_trace s hs0 hs1]

/-- Nonnegativity of relative entropy, with arbitrary possibly singular input. -/
theorem binaryProductRelativeEntropy_nonneg
    (s : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (n : ℕ)
    (σ : State (TensorPower Qubit n)) : 0 ≤ binaryProductRelativeEntropy s n σ := by
  unfold binaryProductRelativeEntropy
  rw [binaryLogExpectation_eq_trace s hs0 hs1]
  exact State.relativeEntropy_posDefReferenceTraceLog_nonneg _ _
    (diagonalQubitState_tensorPower_posDef s hs0 hs1 n)

/-- Excitation transforms independently at every site even for correlated inputs. -/
theorem amplitudeDamping_siteExcitationSum
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ n (τ : State (TensorPower Qubit n)),
      siteExcitationSum n (((amplitudeDamping p hp0 hp1).tensorPower n).applyState τ) =
        (1 - p) * siteExcitationSum n τ := by
  intro n
  induction n with
  | zero => intro τ; simp [siteExcitationSum]
  | succ n ih =>
    intro τ
    rw [siteExcitationSum_succ, siteExcitationSum_succ, Channel.tensorPower_succ]
    have hA := State.marginalA_applyState_prod τ (amplitudeDamping p hp0 hp1)
      ((amplitudeDamping p hp0 hp1).tensorPower n)
    have hB := State.marginalB_applyState_prod τ (amplitudeDamping p hp0 hp1)
      ((amplitudeDamping p hp0 hp1).tensorPower n)
    erw [hA, hB, amplitudeDamping_output_excitation, ih]
    ring

/-- The optimum output excitation is strictly between zero and one. -/
theorem optimalOutputExcitation_mem_Ioo (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    (1 - p) * optimalExcitation p hp0 hp1 ∈ Set.Ioo (0 : ℝ) 1 := by
  have hq := optimalExcitation_mem_Ioo p hp0 hp1
  constructor
  · exact mul_pos (sub_pos.mpr hp1) hq.1
  · nlinarith [hq.2]

/-- Relative entropy of the block output to the optimal product reference,
expressed as a finite real number. -/
def dampingOutputRelativeEntropy (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (n : ℕ) (τ : State (TensorPower Qubit n)) : ℝ :=
  binaryProductRelativeEntropy ((1 - p) * optimalExcitation p hp0 hp1) n
    (((amplitudeDamping p hp0 hp1.le).tensorPower n).applyState τ)

theorem dampingOutputRelativeEntropy_nonneg (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (n : ℕ) (τ : State (TensorPower Qubit n)) :
    0 ≤ dampingOutputRelativeEntropy p hp0 hp1 n τ :=
  binaryProductRelativeEntropy_nonneg _ (optimalOutputExcitation_mem_Ioo p hp0 hp1).1
    (optimalOutputExcitation_mem_Ioo p hp0 hp1).2 n _

/-- The logarithm of the product reference depends affinely on total excitation. -/
theorem dampingOutputRelativeEntropy_expansion
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (n : ℕ) (τ : State (TensorPower Qubit n)) :
    dampingOutputRelativeEntropy p hp0 hp1 n τ =
      (n : ℝ) * binaryEntropy ((1 - p) * optimalExcitation p hp0 hp1) -
        (((amplitudeDamping p hp0 hp1.le).tensorPower n).applyState τ).vonNeumann +
        dampingEntropySlope p (optimalExcitation p hp0 hp1) *
          (siteExcitationSum n τ - (n : ℝ) * optimalExcitation p hp0 hp1) := by
  have hs := optimalOutputExcitation_mem_Ioo p hp0 hp1
  have hstat := optimalExcitation_stationary p hp0 hp1
  unfold dampingOutputRelativeEntropy binaryProductRelativeEntropy
  rw [binaryLogExpectation_eq _ hs.1 hs.2, amplitudeDamping_siteExcitationSum]
  rw [← hstat, binaryEntropy_eq_binEntropy_div_log_two, Real.binEntropy]
  simp only [Real.log_inv]
  ring

lemma dampingBregman_siteSum_eq (p qref : ℝ) (n : ℕ)
    (τ : State (TensorPower Qubit n)) :
    (∑ i, dampingBregman p qref (stateExcitation (siteStates n τ i))) =
      (∑ i, dampingEntropyCurve p (stateExcitation (siteStates n τ i))) -
        (n : ℝ) * dampingEntropyCurve p qref -
        dampingEntropySlope p qref * (siteExcitationSum n τ - (n : ℝ) * qref) := by
  rw [siteExcitationSum_eq]
  simp [dampingBregman, Finset.sum_sub_distrib, ← Finset.mul_sum]

/-- Exact three-term finite-block Holevo deficit for every correlated input. -/
theorem amplitudeDamping_exact_deficit
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (n : ℕ) (τ : State (TensorPower Qubit n)) :
    (n : ℝ) * Channel.classicalCapacity.{0, 0, 0} (amplitudeDamping p hp0 hp1.le) -
        fixedInputHolevo (outputEntropyRoof ((amplitudeDamping p hp0 hp1.le).tensorPower n))
          ((amplitudeDamping p hp0 hp1.le).tensorPower n) τ =
      dampingOutputRelativeEntropy p hp0 hp1 n τ + dampingRoofExcess p hp0 hp1.le n τ +
        ∑ i, dampingBregman p (optimalExcitation p hp0 hp1)
          (stateExcitation (siteStates n τ i)) := by
  rw [amplitudeDamping_classicalCapacity_eq_optimalExcitation p hp0 hp1,
    dampingOutputRelativeEntropy_expansion, dampingBregman_siteSum_eq]
  unfold dampingRoofExcess fixedInputHolevo amplitudeDampingScalarInformation
  ring

/-- Information-radius upper bound holds for all inputs, including mixed inputs. -/
theorem amplitudeDamping_informationRadius_bound
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (n : ℕ) (τ : State (TensorPower Qubit n)) :
    dampingOutputRelativeEntropy p hp0 hp1 n τ ≤
      (n : ℝ) * Channel.classicalCapacity.{0, 0, 0} (amplitudeDamping p hp0 hp1.le) := by
  have h := amplitudeDamping_exact_deficit p hp0 hp1 n τ
  have hroof := dampingRoofExcess_nonneg p hp0 hp1.le n τ
  have hb := dampingBregman_siteSum_nonneg p hp0 hp1 n τ
  have hχ := outputEntropyRoof_le_outputEntropy
    ((amplitudeDamping p hp0 hp1.le).tensorPower n) τ
  unfold fixedInputHolevo at h
  linarith

/-- Damping sends a diagonal input to the diagonal state with attenuated excitation. -/
theorem amplitudeDamping_diagonalQubitState
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    (amplitudeDamping p hp0 hp1).applyState (diagonalQubitState q hq0 hq1) =
      diagonalQubitState ((1 - p) * q) (mul_nonneg (sub_nonneg.mpr hp1) hq0)
        (mul_le_one₀ (by linarith) hq0 hq1) := by
  apply State.ext
  rw [amplitudeDamping_applyState_matrix]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagonalQubitState, diagonalQubitProb, Classical.diagonalState] <;>
    norm_cast
  change (1 - q) + p * q = 1 - (1 - p) * q
  ring

theorem dampingOptimalOutput_eq_diagonal
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    dampingOptimalOutput p hp0 hp1 =
      diagonalQubitState ((1 - p) * optimalExcitation p hp0 hp1)
        (optimalOutputExcitation_mem_Ioo p hp0 hp1).1.le
        (optimalOutputExcitation_mem_Ioo p hp0 hp1).2.le :=
  amplitudeDamping_diagonalQubitState p hp0 hp1.le _ _ _

/-- The information-radius center has full rank at every blocklength. -/
theorem dampingOptimalOutput_tensorPower_posDef
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (n : ℕ) :
    ((dampingOptimalOutput p hp0 hp1).tensorPower n).matrix.PosDef := by
  rw [dampingOptimalOutput_eq_diagonal]
  exact diagonalQubitState_tensorPower_posDef _
    (optimalOutputExcitation_mem_Ioo p hp0 hp1).1
    (optimalOutputExcitation_mem_Ioo p hp0 hp1).2 n

/-- Identification with the manuscript's actual quantum relative entropy. -/
theorem dampingOutputRelativeEntropy_eq_relativeEntropy
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (n : ℕ) (τ : State (TensorPower Qubit n)) :
    (dampingOutputRelativeEntropy p hp0 hp1 n τ : EReal) =
      (((amplitudeDamping p hp0 hp1.le).tensorPower n).applyState τ).relativeEntropy
        ((dampingOptimalOutput p hp0 hp1).tensorPower n) := by
  rw [dampingOptimalOutput_eq_diagonal]
  exact binaryProductRelativeEntropy_eq_relativeEntropy _
    (optimalOutputExcitation_mem_Ioo p hp0 hp1).1
    (optimalOutputExcitation_mem_Ioo p hp0 hp1).2 n _

/-- The support-aware quantum relative entropy satisfies the finite-block radius bound. -/
theorem amplitudeDamping_relativeEntropy_radius_bound
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (n : ℕ) (τ : State (TensorPower Qubit n)) :
    (((amplitudeDamping p hp0 hp1.le).tensorPower n).applyState τ).relativeEntropy
        ((dampingOptimalOutput p hp0 hp1).tensorPower n) ≤
      ((n : ℝ) * Channel.classicalCapacity.{0, 0, 0}
        (amplitudeDamping p hp0 hp1.le) : ℝ) := by
  rw [← dampingOutputRelativeEntropy_eq_relativeEntropy]
  exact_mod_cast amplitudeDamping_informationRadius_bound p hp0 hp1 n τ

/-- An optimal average input has zero relative entropy to the optimal product output. -/
theorem amplitudeDamping_optimal_average_relativeEntropy_zero
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (n : ℕ) (τ : State (TensorPower Qubit n))
    (hopt : fixedInputHolevo (outputEntropyRoof ((amplitudeDamping p hp0 hp1.le).tensorPower n))
      ((amplitudeDamping p hp0 hp1.le).tensorPower n) τ =
      (n : ℝ) * Channel.classicalCapacity.{0, 0, 0} (amplitudeDamping p hp0 hp1.le)) :
    (((amplitudeDamping p hp0 hp1.le).tensorPower n).applyState τ).relativeEntropy
        ((dampingOptimalOutput p hp0 hp1).tensorPower n) = 0 := by
  rw [← dampingOutputRelativeEntropy_eq_relativeEntropy]
  have h := amplitudeDamping_exact_deficit p hp0 hp1 n τ
  have hD := dampingOutputRelativeEntropy_nonneg p hp0 hp1 n τ
  have hR := dampingRoofExcess_nonneg p hp0 hp1.le n τ
  have hB := dampingBregman_siteSum_nonneg p hp0 hp1 n τ
  have hz : dampingOutputRelativeEntropy p hp0 hp1 n τ = 0 := by linarith
  simp [hz]

/-- Literal support-aware relative-entropy form of the manuscript's deficit identity. -/
theorem amplitudeDamping_exact_deficit_relativeEntropy
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (n : ℕ) (τ : State (TensorPower Qubit n)) :
    (((n : ℝ) * Channel.classicalCapacity.{0, 0, 0} (amplitudeDamping p hp0 hp1.le) -
        fixedInputHolevo (outputEntropyRoof ((amplitudeDamping p hp0 hp1.le).tensorPower n))
          ((amplitudeDamping p hp0 hp1.le).tensorPower n) τ : ℝ) : EReal) =
      (((amplitudeDamping p hp0 hp1.le).tensorPower n).applyState τ).relativeEntropy
          ((dampingOptimalOutput p hp0 hp1).tensorPower n) +
        ((dampingRoofExcess p hp0 hp1.le n τ +
          ∑ i, dampingBregman p (optimalExcitation p hp0 hp1)
            (stateExcitation (siteStates n τ i)) : ℝ) : EReal) := by
  rw [← dampingOutputRelativeEntropy_eq_relativeEntropy,
    amplitudeDamping_exact_deficit]
  push_cast
  rw [add_assoc]

/-- A matrix map with injective factors has an injective Kronecker product. -/
lemma matrixMap_kron_injective {a b c d : Type}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (N : MatrixMap a b) (M : MatrixMap c d)
    (hN : Function.Injective N) (hM : Function.Injective M) :
    Function.Injective (MatrixMap.kron N M) := by
  obtain ⟨L, hL⟩ := N.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hN)
  obtain ⟨R, hR⟩ := M.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hM)
  have hid (X : CMatrix (a × c)) :
      MatrixMap.kron (LinearMap.id : MatrixMap a a) (LinearMap.id : MatrixMap c c) X = X := by
    ext i j
    simp [MatrixMap.kron, Matrix.single, ite_and]
  have hleft : Function.LeftInverse (MatrixMap.kron L R) (MatrixMap.kron N M) := by
    intro X
    rw [MatrixMap.kron_comp_apply_general, hL, hR, hid]
  exact hleft.injective

/-- Amplitude damping is injective as a linear map whenever p < 1. -/
theorem amplitudeDamping_map_injective (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    Function.Injective (amplitudeDamping p hp0 hp1.le).map := by
  intro X Y h
  have hc : ((1 - p : ℝ) : ℂ) ≠ 0 := by exact_mod_cast (sub_pos.mpr hp1).ne'
  have hs : (Real.sqrt (1 - p) : ℂ) ≠ 0 := by
    exact_mod_cast (Real.sqrt_pos.mpr (sub_pos.mpr hp1)).ne'
  have h11 : X 1 1 = Y 1 1 := mul_left_cancel₀ hc (by
    simpa only [amplitudeDamping_map_eq, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.head_cons] using congrArg (fun A : CMatrix Qubit => A 1 1) h)
  have h01 : X 0 1 = Y 0 1 := mul_left_cancel₀ hs (by
    simpa only [amplitudeDamping_map_eq, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.head_cons] using congrArg (fun A : CMatrix Qubit => A 0 1) h)
  have h10 : X 1 0 = Y 1 0 := mul_left_cancel₀ hs (by
    simpa only [amplitudeDamping_map_eq, Matrix.cons_val_one, Matrix.cons_val_zero,
      Matrix.head_cons] using congrArg (fun A : CMatrix Qubit => A 1 0) h)
  have h00 : X 0 0 = Y 0 0 := by
    have hh := congrArg (fun A : CMatrix Qubit => A 0 0) h
    simp only [amplitudeDamping_map_eq, h11] at hh
    exact add_right_cancel hh
  ext i j
  fin_cases i <;> fin_cases j <;> assumption

/-- Injectivity persists at every blocklength. -/
theorem amplitudeDamping_tensorPower_map_injective
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) :
    ∀ n, Function.Injective ((amplitudeDamping p hp0 hp1.le).tensorPower n).map := by
  intro n
  induction n with
  | zero => exact fun X Y h => h
  | succ n ih =>
    exact matrixMap_kron_injective _ _ (amplitudeDamping_map_injective p hp0 hp1) ih

/-- The corresponding block channel is injective on density operators. -/
theorem amplitudeDamping_tensorPower_applyState_injective
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (n : ℕ) :
    Function.Injective ((amplitudeDamping p hp0 hp1.le).tensorPower n).applyState := by
  intro ρ σ h
  apply State.ext
  exact amplitudeDamping_tensorPower_map_injective p hp0 hp1 n (congrArg State.matrix h)

/-- IID inputs have IID outputs for every channel. -/
lemma channel_applyState_tensorPower {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (N : Channel a b) (ρ : State a) :
    ∀ n, (N.tensorPower n).applyState (ρ.tensorPower n) = (N.applyState ρ).tensorPower n := by
  intro n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Channel.tensorPower_succ, State.tensorPower_succ, State.tensorPower_succ]
    erw [Channel.applyState_prod, ih]

/-- The optimal product average actually attains the block capacity. -/
theorem amplitudeDamping_optimal_average_attains
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1) (n : ℕ) :
    fixedInputHolevo (outputEntropyRoof ((amplitudeDamping p hp0 hp1.le).tensorPower n))
      ((amplitudeDamping p hp0 hp1.le).tensorPower n)
      ((dampingOptimalInput p hp0 hp1).tensorPower n) =
      (n : ℝ) * Channel.classicalCapacity.{0, 0, 0} (amplitudeDamping p hp0 hp1.le) := by
  unfold fixedInputHolevo
  rw [channel_applyState_tensorPower, State.vonNeumann_tensorPower,
    amplitudeDamping_tensorPower_roof_iid_eq]
  rw [← mul_sub]
  change (n : ℝ) * fixedInputHolevo (outputEntropyRoof (amplitudeDamping p hp0 hp1.le))
    (amplitudeDamping p hp0 hp1.le) (dampingOptimalInput p hp0 hp1) = _
  rw [amplitudeDamping_fixedInputHolevo_eq_stateInformation]
  unfold dampingOptimalInput
  rw [amplitudeDampingStateInformation_diagonalQubitState,
    amplitudeDamping_classicalCapacity_eq_optimalExcitation p hp0 hp1]

/-- Standard equality case of Klein's inequality for a faithful reference.
The original interface is proved by `faithfulRelativeEntropyEquality` below. -/
def FaithfulRelativeEntropyEquality : Prop :=
  ∀ {a : Type} [Fintype a] [DecidableEq a] (ρ σ : State a),
    σ.matrix.PosDef → ρ.relativeEntropy σ = 0 → ρ = σ

/-- The faithful-reference equality case is proved in every finite dimension. -/
theorem faithfulRelativeEntropyEquality : FaithfulRelativeEntropyEquality := by
  intro a _ _ ρ σ hσ hz
  exact faithful_relativeEntropy_eq_zero_imp_eq ρ σ hσ hz

/-- The unique optimal average input is the optimal IID diagonal state. -/
theorem amplitudeDamping_optimal_average_iff
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p < 1)
    (n : ℕ) (τ : State (TensorPower Qubit n)) :
    (fixedInputHolevo (outputEntropyRoof ((amplitudeDamping p hp0 hp1.le).tensorPower n))
      ((amplitudeDamping p hp0 hp1.le).tensorPower n) τ =
      (n : ℝ) * Channel.classicalCapacity.{0, 0, 0} (amplitudeDamping p hp0 hp1.le)) ↔
    τ = (dampingOptimalInput p hp0 hp1).tensorPower n := by
  constructor
  · intro hopt
    have hout := faithfulRelativeEntropyEquality _ _ (dampingOptimalOutput_tensorPower_posDef p hp0 hp1 n)
      (amplitudeDamping_optimal_average_relativeEntropy_zero p hp0 hp1 n τ hopt)
    apply amplitudeDamping_tensorPower_applyState_injective p hp0 hp1 n
    rw [channel_applyState_tensorPower]
    exact hout
  · rintro rfl
    exact amplitudeDamping_optimal_average_attains p hp0 hp1 n

end
end AmplitudeDamping
