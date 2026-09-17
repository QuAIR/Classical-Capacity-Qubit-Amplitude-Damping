import AmplitudeDamping.ConvexRoof

/-!
# Entanglement of formation

The entanglement of formation of a bipartite state is the convex roof of the
entropy of the first marginal over all finite pure-state decompositions
(equation (30) of the manuscript).  The definition mirrors the output-entropy
convex roof of `ConvexRoof.lean`, with the channel output replaced by the
first marginal, and satisfies the same elementary properties: nonnegativity,
the lower-envelope bound on decompositions, and finite Jensen convexity.
-/

open scoped BigOperators NNReal

namespace AmplitudeDamping

open QIT

universe u v w

noncomputable section

variable {a : Type u} {c : Type v}
variable [Fintype a] [DecidableEq a]
variable [Fintype c] [DecidableEq c]

namespace PureDecomposition

/-- Average marginal entropy of a finite pure-state decomposition of a
bipartite state: the quantity minimized in the entanglement of formation. -/
def entanglementCost (E : PureDecomposition (Prod a c)) : ℝ :=
  ∑ i, (E.probs i).toReal * ((E.vectors i).state.marginalA).vonNeumann

theorem entanglementCost_nonneg (E : PureDecomposition (Prod a c)) :
    0 ≤ E.entanglementCost := by
  unfold entanglementCost
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (NNReal.coe_nonneg _) (State.vonNeumann_nonneg _)

theorem flatten_entanglementCost {ι : Type w} [Fintype ι]
    (E : Ensemble ι (Prod a c))
    (D : (i : ι) → PureDecomposition (Prod a c)) :
    (flatten E D).entanglementCost =
      ∑ i, (E.probs i).toReal * (D i).entanglementCost := by
  unfold entanglementCost
  change
    (∑ k : Fin (Fintype.card (Sigma fun i => Fin (D i).card)),
      (E.probs ((Fintype.equivFin
          (Sigma fun i => Fin (D i).card)).symm k).1 *
        (D ((Fintype.equivFin
          (Sigma fun i => Fin (D i).card)).symm k).1).probs
          ((Fintype.equivFin
            (Sigma fun i => Fin (D i).card)).symm k).2).toReal *
        ((D ((Fintype.equivFin
              (Sigma fun i => Fin (D i).card)).symm k).1).vectors
            ((Fintype.equivFin
              (Sigma fun i => Fin (D i).card)).symm k).2).state.marginalA.vonNeumann) = _
  calc
    _ = ∑ z : Sigma fun i => Fin (D i).card,
        (E.probs z.1 * (D z.1).probs z.2).toReal *
          ((D z.1).vectors z.2).state.marginalA.vonNeumann := by
      exact Fintype.sum_equiv
        (Fintype.equivFin (Sigma fun i => Fin (D i).card)).symm
        _ _ (fun _ => rfl)
    _ = ∑ i : ι, (E.probs i).toReal * (D i).entanglementCost := by
      rw [Fintype.sum_sigma]
      apply Finset.sum_congr rfl
      intro i _
      unfold PureDecomposition.entanglementCost
      simp only [NNReal.coe_mul]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      ring

end PureDecomposition

/-- All average marginal-entropy costs of finite pure decompositions of `ρ`. -/
def pureEntanglementValues (ρ : State (Prod a c)) : Set ℝ :=
  {x | ∃ E : PureDecomposition (Prod a c),
    E.averageState = ρ ∧ x = E.entanglementCost}

/-- The entanglement of formation across the first bipartition, as a literal
infimum over finite pure-state decompositions. -/
def entanglementOfFormation (ρ : State (Prod a c)) : ℝ :=
  sInf (pureEntanglementValues ρ)

theorem pureEntanglementValues_bddBelow (ρ : State (Prod a c)) :
    BddBelow (pureEntanglementValues ρ) := by
  refine ⟨0, ?_⟩
  intro x hx
  rcases hx with ⟨E, _, rfl⟩
  exact E.entanglementCost_nonneg

/-- The entanglement of formation is no larger than the cost of any particular
finite pure-state decomposition of the same average state. -/
theorem entanglementOfFormation_le_entanglementCost
    (E : PureDecomposition (Prod a c)) :
    entanglementOfFormation E.averageState ≤ E.entanglementCost := by
  apply csInf_le (pureEntanglementValues_bddBelow E.averageState)
  exact ⟨E, rfl, rfl⟩

/-- Lower-envelope property, isolated as a reusable predicate. -/
def IsPureEntanglementRoof (roof : State (Prod a c) → ℝ) : Prop :=
  ∀ E : PureDecomposition (Prod a c),
    roof E.averageState ≤ E.entanglementCost

theorem pureEntanglementValues_nonempty (ρ : State (Prod a c)) :
    (pureEntanglementValues ρ).Nonempty := by
  let E := spectralPureDecomposition ρ
  exact ⟨E.entanglementCost, E, spectralPureDecomposition_averageState ρ, rfl⟩

theorem entanglementOfFormation_nonneg (ρ : State (Prod a c)) :
    0 ≤ entanglementOfFormation ρ := by
  apply le_csInf (pureEntanglementValues_nonempty ρ)
  intro x hx
  rcases hx with ⟨E, _, rfl⟩
  exact E.entanglementCost_nonneg

/-- The entanglement of formation satisfies Jensen's inequality for every
finite ensemble of (possibly mixed) bipartite states: it is convex. -/
theorem entanglementOfFormation_satisfiesFiniteJensen :
    SatisfiesFiniteJensen
      (fun ρ : State (Prod a c) => entanglementOfFormation ρ) := by
  intro ι _ E
  apply le_of_forall_pos_le_add
  intro ε hε
  have hex : ∀ i : ι, ∃ D : PureDecomposition (Prod a c),
      D.averageState = E.states i ∧
        D.entanglementCost < entanglementOfFormation (E.states i) + ε := by
    intro i
    obtain ⟨x, hx, hlt⟩ := Real.lt_sInf_add_pos
      (pureEntanglementValues_nonempty (E.states i)) hε
    rcases hx with ⟨D, hD, rfl⟩
    exact ⟨D, hD, by simpa [entanglementOfFormation] using hlt⟩
  choose D hDavg hDcost using hex
  let F := PureDecomposition.flatten E D
  have hroof :
      entanglementOfFormation E.averageState ≤ F.entanglementCost := by
    rw [show E.averageState = F.averageState by
      exact (PureDecomposition.flatten_averageState E D hDavg).symm]
    exact entanglementOfFormation_le_entanglementCost F
  rw [PureDecomposition.flatten_entanglementCost] at hroof
  calc
    entanglementOfFormation E.averageState ≤
        ∑ i, (E.probs i).toReal * (D i).entanglementCost := hroof
    _ ≤ ∑ i, (E.probs i).toReal *
        (entanglementOfFormation (E.states i) + ε) := by
      exact Finset.sum_le_sum fun i _ =>
        mul_le_mul_of_nonneg_left (le_of_lt (hDcost i))
          (NNReal.coe_nonneg _)
    _ = (∑ i, (E.probs i).toReal *
          entanglementOfFormation (E.states i)) + ε := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul]
      have hw := congrArg (fun x : ℝ≥0 => (x : ℝ)) E.weights_sum
      have hwR : (∑ i, (E.probs i : ℝ)) = 1 := by simpa using hw
      rw [hwR, one_mul]

end

end AmplitudeDamping
