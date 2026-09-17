import AmplitudeDamping.Definitions
import QIT.Core.Pure
import QIT.Symmetry.DeFinetti.RennerProjectors

/-!
# Finite pure-state decompositions and the output-entropy convex roof

The manuscript optimizes over finite pure-state ensembles.  Encoding the
classical alphabet size as a field avoids quantifying over Lean types inside a
set comprehension and permits a literal real infimum.
-/

open scoped BigOperators ComplexOrder MatrixOrder NNReal

namespace AmplitudeDamping

open QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]

/-- A finite probability distribution whose signals are normalized pure
vectors.  Zero weights are allowed. -/
structure PureDecomposition (a : Type u) [Fintype a] [DecidableEq a] where
  card : ℕ
  probs : Fin card → ℝ≥0
  weights_sum : ∑ i, probs i = 1
  vectors : Fin card → PureVector a

namespace PureDecomposition

/-- Package a pure ensemble indexed by an arbitrary finite type into the
canonical `Fin card` representation used by `PureDecomposition`. -/
def ofFinite {ι : Type w} [Fintype ι]
    (probs : ι → ℝ≥0) (weights_sum : ∑ i, probs i = 1)
    (vectors : ι → PureVector a) : PureDecomposition a where
  card := Fintype.card ι
  probs k := probs ((Fintype.equivFin ι).symm k)
  weights_sum := by
    calc
      (∑ k : Fin (Fintype.card ι), probs ((Fintype.equivFin ι).symm k)) =
          ∑ i : ι, probs i := by
        exact Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ (fun _ => rfl)
      _ = 1 := weights_sum
  vectors k := vectors ((Fintype.equivFin ι).symm k)

/-- Flatten an ensemble of states together with a pure decomposition of every
member into one finite pure decomposition. -/
def flatten {ι : Type w} [Fintype ι]
    (E : Ensemble ι a) (D : (i : ι) → PureDecomposition a) : PureDecomposition a :=
  ofFinite
    (ι := Sigma fun i => Fin (D i).card)
    (fun z => E.probs z.1 * (D z.1).probs z.2)
    (by
      change (∑ z : Sigma fun i => Fin (D i).card,
        E.probs z.1 * (D z.1).probs z.2) = 1
      rw [Fintype.sum_sigma]
      simp_rw [← Finset.mul_sum, (D _).weights_sum, mul_one]
      exact E.weights_sum)
    (fun z => (D z.1).vectors z.2)

/-- Forget that the member states are pure. -/
def toEnsemble (E : PureDecomposition a) : Ensemble (Fin E.card) a where
  probs := E.probs
  weights_sum := E.weights_sum
  states i := (E.vectors i).state

@[simp]
theorem toEnsemble_probs (E : PureDecomposition a) :
    E.toEnsemble.probs = E.probs := rfl

@[simp]
theorem toEnsemble_states (E : PureDecomposition a) (i : Fin E.card) :
    E.toEnsemble.states i = (E.vectors i).state := rfl

/-- Average input state represented by a pure decomposition. -/
def averageState (E : PureDecomposition a) : State a :=
  E.toEnsemble.averageState

/-- Average output entropy of a pure decomposition. -/
def outputCost (Φ : Channel a b) (E : PureDecomposition a) : ℝ :=
  outputEntropyCost Φ E.toEnsemble

theorem flatten_averageState {ι : Type w} [Fintype ι]
    (E : Ensemble ι a) (D : (i : ι) → PureDecomposition a)
    (hD : ∀ i, (D i).averageState = E.states i) :
    (flatten E D).averageState = E.averageState := by
  apply State.ext
  rw [PureDecomposition.averageState, Ensemble.averageState_matrix,
    Ensemble.averageState_matrix]
  change
    (∑ k : Fin (Fintype.card (Sigma fun i => Fin (D i).card)),
      (((E.probs ((Fintype.equivFin
          (Sigma fun i => Fin (D i).card)).symm k).1 *
        (D ((Fintype.equivFin
          (Sigma fun i => Fin (D i).card)).symm k).1).probs
          ((Fintype.equivFin
            (Sigma fun i => Fin (D i).card)).symm k).2 : ℝ≥0) : ℂ) •
        ((D ((Fintype.equivFin
          (Sigma fun i => Fin (D i).card)).symm k).1).vectors
          ((Fintype.equivFin
            (Sigma fun i => Fin (D i).card)).symm k).2).state.matrix)) = _
  calc
    _ = ∑ z : Sigma fun i => Fin (D i).card,
        ((E.probs z.1 * (D z.1).probs z.2 : ℝ≥0) : ℂ) •
          ((D z.1).vectors z.2).state.matrix := by
      exact Fintype.sum_equiv
        (Fintype.equivFin (Sigma fun i => Fin (D i).card)).symm
        _ _ (fun _ => rfl)
    _ = ∑ i : ι, (E.probs i : ℂ) • (D i).averageState.matrix := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      rw [PureDecomposition.averageState, Ensemble.averageState_matrix]
      ext x y
      simp [PureDecomposition.toEnsemble, Matrix.sum_apply,
        Matrix.smul_apply, Finset.mul_sum, mul_assoc]
      apply Finset.sum_congr rfl
      intro j _
      rw [NNReal.smul_def, Algebra.smul_def]
      have hcast : (algebraMap ℝ ℂ) ((D i).probs j : ℝ) =
          (((D i).probs j : ℝ) : ℂ) := rfl
      rw [hcast]
      ring
    _ = ∑ i : ι, (E.probs i : ℂ) • (E.states i).matrix := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hD i]
    _ = _ := rfl

theorem flatten_outputCost {ι : Type w} [Fintype ι]
    (Phi : Channel a b) (E : Ensemble ι a)
    (D : (i : ι) → PureDecomposition a) :
    (flatten E D).outputCost Phi =
      ∑ i, (E.probs i).toReal * (D i).outputCost Phi := by
  unfold outputCost outputEntropyCost
  change
    (∑ k : Fin (Fintype.card (Sigma fun i => Fin (D i).card)),
      (E.probs ((Fintype.equivFin
          (Sigma fun i => Fin (D i).card)).symm k).1 *
        (D ((Fintype.equivFin
          (Sigma fun i => Fin (D i).card)).symm k).1).probs
          ((Fintype.equivFin
            (Sigma fun i => Fin (D i).card)).symm k).2).toReal *
        (Phi.applyState
          ((D ((Fintype.equivFin
            (Sigma fun i => Fin (D i).card)).symm k).1).vectors
            ((Fintype.equivFin
              (Sigma fun i => Fin (D i).card)).symm k).2).state).vonNeumann) = _
  calc
    _ = ∑ z : Sigma fun i => Fin (D i).card,
        (E.probs z.1 * (D z.1).probs z.2).toReal *
          (Phi.applyState ((D z.1).vectors z.2).state).vonNeumann := by
      exact Fintype.sum_equiv
        (Fintype.equivFin (Sigma fun i => Fin (D i).card)).symm
        _ _ (fun _ => rfl)
    _ = ∑ i : ι, (E.probs i).toReal * (D i).outputCost Phi := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      unfold PureDecomposition.outputCost outputEntropyCost
      simp only [NNReal.coe_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      simp only [PureDecomposition.toEnsemble]
      ring

theorem outputCost_nonneg (Φ : Channel a b) (E : PureDecomposition a) :
    0 ≤ E.outputCost Φ := by
  unfold outputCost outputEntropyCost
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (NNReal.coe_nonneg _) (State.vonNeumann_nonneg _)

end PureDecomposition

/-- All average output-entropy costs of finite pure decompositions of `ρ`. -/
def pureOutputEntropyValues (Φ : Channel a b) (ρ : State a) : Set ℝ :=
  {x | ∃ E : PureDecomposition a,
    E.averageState = ρ ∧ x = E.outputCost Φ}

/-- The finite pure-state output-entropy convex roof. -/
def outputEntropyRoof (Φ : Channel a b) (ρ : State a) : ℝ :=
  sInf (pureOutputEntropyValues Φ ρ)

theorem pureOutputEntropyValues_bddBelow (Φ : Channel a b) (ρ : State a) :
    BddBelow (pureOutputEntropyValues Φ ρ) := by
  refine ⟨0, ?_⟩
  intro x hx
  rcases hx with ⟨E, _, rfl⟩
  exact E.outputCost_nonneg Φ

/-- The convex roof is no larger than the cost of any particular finite pure
decomposition of the same average state. -/
theorem outputEntropyRoof_le_outputCost (Φ : Channel a b)
    (E : PureDecomposition a) :
    outputEntropyRoof Φ E.averageState ≤ E.outputCost Φ := by
  apply csInf_le (pureOutputEntropyValues_bddBelow Φ E.averageState)
  exact ⟨E, rfl, rfl⟩

/-- Pure-ensemble lower-envelope property, isolated as a reusable predicate. -/
def IsPureOutputEntropyRoof (Φ : Channel a b) (roof : State a → ℝ) : Prop :=
  ∀ E : PureDecomposition a, roof E.averageState ≤ E.outputCost Φ

/-- Finite Jensen inequality for a functional on density states. -/
def SatisfiesFiniteJensen (f : State a → ℝ) : Prop :=
  ∀ {ι : Type} [Fintype ι] (E : Ensemble ι a),
    f E.averageState ≤ ∑ i, (E.probs i).toReal * f (E.states i)

theorem outputEntropyRoof_isPureOutputEntropyRoof (Φ : Channel a b) :
    IsPureOutputEntropyRoof Φ (outputEntropyRoof Φ) := by
  intro E
  exact outputEntropyRoof_le_outputCost Φ E

/-- The spectral decomposition of a state, reindexed by a canonical finite
alphabet, as a `PureDecomposition`. -/
def spectralPureDecomposition (ρ : State a) : PureDecomposition a where
  card := Fintype.card a
  probs k :=
    ⟨ρ.pos.isHermitian.eigenvalues ((Fintype.equivFin a).symm k),
      ρ.pos.eigenvalues_nonneg _⟩
  weights_sum := by
    apply NNReal.eq
    simp only [NNReal.coe_sum, NNReal.coe_one]
    calc
      ∑ k : Fin (Fintype.card a),
          ρ.pos.isHermitian.eigenvalues ((Fintype.equivFin a).symm k) =
          ∑ i : a, ρ.pos.isHermitian.eigenvalues i := by
            exact Fintype.sum_equiv (Fintype.equivFin a).symm _ _ (fun _ => rfl)
      _ = 1 := State.sum_eigenvalues_eq_one ρ
  vectors k := ρ.spectralPureVector ((Fintype.equivFin a).symm k)

/-- The spectral pure decomposition has the original state as its average. -/
@[simp]
theorem spectralPureDecomposition_averageState (ρ : State a) :
    (spectralPureDecomposition ρ).averageState = ρ := by
  apply State.ext
  rw [PureDecomposition.averageState, Ensemble.averageState_matrix]
  change (∑ k : Fin (Fintype.card a),
      ((ρ.pos.isHermitian.eigenvalues ((Fintype.equivFin a).symm k) : ℝ) : ℂ) •
        (ρ.spectralPureVector ((Fintype.equivFin a).symm k)).state.matrix) = ρ.matrix
  calc
    (∑ k : Fin (Fintype.card a),
        ((ρ.pos.isHermitian.eigenvalues ((Fintype.equivFin a).symm k) : ℝ) : ℂ) •
          (ρ.spectralPureVector ((Fintype.equivFin a).symm k)).state.matrix) =
        ∑ i : a, ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
          (ρ.spectralPureVector i).state.matrix := by
            exact Fintype.sum_equiv (Fintype.equivFin a).symm _ _ (fun _ => rfl)
    _ = ρ.matrix := (State.matrix_eq_sum_spectralPureVector ρ).symm

theorem exists_pureDecomposition (ρ : State a) :
    ∃ E : PureDecomposition a, E.averageState = ρ :=
  ⟨spectralPureDecomposition ρ, spectralPureDecomposition_averageState ρ⟩

theorem pureOutputEntropyValues_nonempty (Φ : Channel a b) (ρ : State a) :
    (pureOutputEntropyValues Φ ρ).Nonempty := by
  let E := spectralPureDecomposition ρ
  exact ⟨E.outputCost Φ, E, spectralPureDecomposition_averageState ρ, rfl⟩

theorem outputEntropyRoof_nonneg (Φ : Channel a b) (ρ : State a) :
    0 ≤ outputEntropyRoof Φ ρ := by
  apply le_csInf (pureOutputEntropyValues_nonempty Φ ρ)
  intro x hx
  rcases hx with ⟨E, _, rfl⟩
  exact E.outputCost_nonneg Φ

/-- The finite pure-state convex roof satisfies Jensen's inequality for every
finite ensemble of (possibly mixed) states. -/
theorem outputEntropyRoof_satisfiesFiniteJensen (Φ : Channel a b) :
    SatisfiesFiniteJensen (outputEntropyRoof Φ) := by
  intro ι _ E
  apply le_of_forall_pos_le_add
  intro ε hε
  have hex : ∀ i : ι, ∃ D : PureDecomposition a,
      D.averageState = E.states i ∧
        D.outputCost Φ < outputEntropyRoof Φ (E.states i) + ε := by
    intro i
    obtain ⟨x, hx, hlt⟩ := Real.lt_sInf_add_pos
      (pureOutputEntropyValues_nonempty Φ (E.states i)) hε
    rcases hx with ⟨D, hD, rfl⟩
    exact ⟨D, hD, by simpa [outputEntropyRoof] using hlt⟩
  choose D hDavg hDcost using hex
  let F := PureDecomposition.flatten E D
  have hroof : outputEntropyRoof Φ E.averageState ≤ F.outputCost Φ := by
    rw [show E.averageState = F.averageState by
      exact (PureDecomposition.flatten_averageState E D hDavg).symm]
    exact outputEntropyRoof_le_outputCost Φ F
  rw [PureDecomposition.flatten_outputCost] at hroof
  calc
    outputEntropyRoof Φ E.averageState ≤
        ∑ i, (E.probs i).toReal * (D i).outputCost Φ := hroof
    _ ≤ ∑ i, (E.probs i).toReal *
        (outputEntropyRoof Φ (E.states i) + ε) := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (le_of_lt (hDcost i))
          (NNReal.coe_nonneg _)
    _ = (∑ i, (E.probs i).toReal *
          outputEntropyRoof Φ (E.states i)) + ε := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      have hw := congrArg (fun x : ℝ≥0 => (x : ℝ)) E.weights_sum
      have hwR : (∑ i, (E.probs i : ℝ)) = 1 := by simpa using hw
      rw [hwR, one_mul]

end

end AmplitudeDamping
