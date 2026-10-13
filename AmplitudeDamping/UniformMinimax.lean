import Mathlib.Topology.Sion
import Mathlib.Analysis.Convex.StdSimplex

open scoped BigOperators
open Set

namespace AmplitudeDamping.UniformMinimax

variable {E : Type*} [TopologicalSpace E] [AddCommGroup E] [Module ℝ E]
  [IsTopologicalAddGroup E] [ContinuousSMul ℝ E]

/-- A finite family of continuous concave costs admits a uniformly good mixture
whenever one member is good at each point of a compact convex domain. -/
theorem exists_mixture_finite {ι : Type*} [Fintype ι] [Nonempty ι]
    {X : Set E} (hne : X.Nonempty) (hk : IsCompact X) (hc : Convex ℝ X)
    (f : ι → E → ℝ) (hcont : ∀ i, ContinuousOn (f i) X)
    (hconc : ∀ i, ConcaveOn ℝ X (f i)) (C : ℝ)
    (hgood : ∀ x ∈ X, ∃ i, f i x < C) :
    ∃ w : ι → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ∀ x ∈ X, (∑ i, w i * f i x) < C := by
  classical
  let g : E → (ι → ℝ) → ℝ := fun x w => -(∑ i, w i * f i x)
  have hgc (w : ι → ℝ) : ContinuousOn (fun x => g x w) X := by
    exact (continuousOn_finsetSum _ (fun i _ => (hcont i).const_mul (w i))).neg
  have hgv (w : ι → ℝ) (hw : w ∈ stdSimplex ℝ ι) :
      ConvexOn ℝ X (fun x => g x w) := by
    apply ConcaveOn.neg
    refine ⟨hc, ?_⟩
    intro x hx y hy a b ha hb hab
    simp only [smul_eq_mul]
    calc
      a * ∑ i, w i * f i x + b * ∑ i, w i * f i y
          = ∑ i, w i * (a * f i x + b * f i y) := by
            simp only [Finset.mul_sum, Finset.sum_add_distrib, mul_add]
            congr 1 <;> apply Finset.sum_congr rfl <;> intros <;> ring
      _ ≤ ∑ i, w i * f i (a • x + b • y) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_mul_of_nonneg_left ((hconc i).2 hx hy ha hb hab) (hw.1 i)
  have hgwc (x : E) : Continuous (g x) := by
    exact (continuous_finsetSum _ (fun i _ => (show Continuous (fun w : ι → ℝ => w i) from continuous_apply i).mul_const (f i x))).neg
  have hgwv (x : E) : ConcaveOn ℝ (stdSimplex ℝ ι) (g x) := by
    refine ⟨convex_stdSimplex ℝ ι, ?_⟩
    intro w hw v hv a b ha hb hab
    dsimp [g]
    simp only [add_mul,
      Finset.sum_add_distrib, ← Finset.mul_sum, mul_assoc]
    ring_nf
    exact le_rfl
  obtain ⟨x₀, hx₀, w, hw, hs⟩ := Sion.exists_isSaddlePointOn'
    hne hk (fun w _ => (hgc w).lowerSemicontinuousOn)
    (fun w hw => (hgv w hw).quasiconvexOn)
    (convex_stdSimplex ℝ ι) (isCompact_stdSimplex ℝ ι)
    (fun x _ => (hgwc x).continuousOn.upperSemicontinuousOn)
    (fun x _ => (hgwv x).quasiconcaveOn) hc
    ⟨_, single_mem_stdSimplex ℝ (Classical.arbitrary ι)⟩
  refine ⟨w, hw.1, hw.2, ?_⟩
  obtain ⟨i, hi⟩ := hgood x₀ hx₀
  intro x hx
  have h := hs x hx (Pi.single i 1) (single_mem_stdSimplex ℝ i)
  simp [g, Pi.single_apply] at h
  linarith

/-- Compactness and minimax turn pointwise good choices from an arbitrary family
into one finite probability mixture that is uniformly good on the whole domain. -/
theorem exists_finite_mixture {ι : Type*}
    {X : Set E} (hne : X.Nonempty) (hk : IsCompact X) (hc : Convex ℝ X)
    (f : ι → E → ℝ) (hcont : ∀ i, ContinuousOn (f i) X)
    (hconc : ∀ i, ConcaveOn ℝ X (f i)) (C : ℝ)
    (hgood : ∀ x ∈ X, ∃ i, f i x < C) :
    ∃ s : Finset ι, ∃ w : s → ℝ, (∀ i, 0 ≤ w i) ∧ (∑ i, w i = 1) ∧
      ∀ x ∈ X, (∑ i, w i * f i.val x) < C := by
  classical
  have hempty : X ∩ ⋂ i ∈ (Set.univ : Set ι), (f i) ⁻¹' Ici C = ∅ := by
    apply Set.eq_empty_of_forall_notMem
    rintro x ⟨hx, hall⟩
    obtain ⟨i, hi⟩ := hgood x hx
    have hge : C ≤ f i x := by
      simp only [Set.mem_iInter, Set.mem_univ, forall_true_left,
        Set.mem_preimage, Set.mem_Ici] at hall
      exact hall i
    exact hi.not_ge hge
  obtain ⟨u, hu⟩ :=
    (UpperSemicontinuousOn.inter_biInter_preimage_Ici_eq_empty_iff_exists_finset hk
      (fun i (_ : i ∈ (Set.univ : Set ι)) => (hcont i).upperSemicontinuousOn)).mp hempty
  let s : Finset ι := u.image Subtype.val
  have hs : ∀ x ∈ X, ∃ i : s, f i.val x < C := by
    intro x hx
    obtain ⟨i, hi, hix⟩ := hu x hx
    exact ⟨⟨i.val, Finset.mem_image.mpr ⟨i, hi, rfl⟩⟩, hix⟩
  haveI : Nonempty s := by
    obtain ⟨x, hx⟩ := hne
    obtain ⟨i, _⟩ := hs x hx
    exact ⟨i⟩
  obtain ⟨w, hw, hwone, hbound⟩ := exists_mixture_finite hne hk hc
    (fun i : s => f i.val) (fun i => hcont i.val) (fun i => hconc i.val) C hs
  exact ⟨s, w, hw, hwone, hbound⟩

end AmplitudeDamping.UniformMinimax
