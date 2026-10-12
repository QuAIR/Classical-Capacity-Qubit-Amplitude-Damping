import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.Analysis.Convex.Topology
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional
import Mathlib.Analysis.Normed.Module.Basic

open scoped BigOperators

namespace AmplitudeDamping

/-- In a finite-dimensional real normed space, the convex hull of a compact set is compact. -/
theorem isCompact_convexHull_of_isCompact
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {s : Set E} (hs : IsCompact s) : IsCompact (convexHull ℝ s) := by
  classical
  let C (n : ℕ) : Set E :=
    (fun p : (Fin n → ℝ) × (Fin n → E) => ∑ i, p.1 i • p.2 i) ''
      (stdSimplex ℝ (Fin n) ×ˢ Set.pi Set.univ (fun _ : Fin n => s))
  have hC (n : ℕ) : IsCompact (C n) := by
    apply ((isCompact_stdSimplex ℝ (Fin n)).prod (isCompact_univ_pi fun _ => hs)).image
    exact continuous_finsetSum _ fun i _ =>
      ((continuous_apply i).comp continuous_fst).smul
        ((continuous_apply i).comp continuous_snd)
  have heq : convexHull ℝ s = ⋃ n : Fin (Module.finrank ℝ E + 2), C n.val := by
    apply Set.Subset.antisymm
    · intro x hx
      let t := Caratheodory.minCardFinsetOfMemConvexHull hx
      have ht : (↑t : Set E) ⊆ s := Caratheodory.minCardFinsetOfMemConvexHull_subseteq hx
      have hi : AffineIndependent ℝ ((↑) : t → E) :=
        Caratheodory.affineIndependent_minCardFinsetOfMemConvexHull hx
      have hcard : Fintype.card t < Module.finrank ℝ E + 2 :=
        lt_of_le_of_lt (hi.card_le_finrank_succ.trans
          (Nat.add_le_add_right (Submodule.finrank_le _) 1)) (Nat.lt_succ_self _)
      have hxt : x ∈ convexHull ℝ (↑t : Set E) :=
        Caratheodory.mem_minCardFinsetOfMemConvexHull hx
      rw [t.convexHull_eq] at hxt
      obtain ⟨w, hw, hw1, hwx⟩ := hxt
      rw [t.centerMass_eq_of_sum_1 id hw1] at hwx
      let e := (Fintype.equivFin t).symm
      refine Set.mem_iUnion.mpr ⟨⟨Fintype.card t, hcard⟩, ?_⟩
      refine ⟨⟨fun i => w (e i), fun i => (e i : E)⟩, ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · exact fun i => hw _ (e i).property
      · rw [e.sum_comp (fun i : t => w i)]
        simpa only [Finset.univ_eq_attach, Finset.sum_attach] using hw1
      · exact fun i _ => ht (e i).property
      · change (∑ i, w (e i) • (e i : E)) = x
        rw [e.sum_comp (fun i : t => w i • (i : E))]
        change (∑ i ∈ t.attach, (fun e => w e • e) ↑i) = x
        rw [Finset.sum_attach (f := fun e => w e • e)]
        simpa using hwx
    · intro x hx
      obtain ⟨n, p, hp, rfl⟩ := Set.mem_iUnion.mp hx
      exact (convex_convexHull ℝ s).sum_mem (fun i _ => hp.1.1 i) hp.1.2
        (fun i _ => subset_convexHull ℝ s (hp.2 i (Set.mem_univ i)))
  rw [heq]
  exact isCompact_iUnion fun n => hC n.val

end AmplitudeDamping
