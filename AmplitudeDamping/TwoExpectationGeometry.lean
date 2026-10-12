import AmplitudeDamping.ConvexRoof
import AmplitudeDamping.RankOnePure
import AmplitudeDamping.CompactConvexHull
import QIT.States.Topology
import Mathlib.Analysis.Convex.KreinMilman
import Mathlib.Analysis.LocallyConvex.WithSeminorms

open scoped BigOperators ComplexOrder MatrixOrder NNReal
namespace AmplitudeDamping
open QIT Matrix
noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Density matrices with two specified real expectations. -/
def twoExpectationSlice (ρ : State a) (F G : Matrix a a ℂ) : Set (Matrix a a ℂ) :=
  {M | M.PosSemidef ∧ M.trace = 1 ∧
    (F * M).trace.re = (F * ρ.matrix).trace.re ∧
    (G * M).trace.re = (G * ρ.matrix).trace.re}

omit [DecidableEq a] in
private theorem continuous_matrixExpectation (F : Matrix a a ℂ) :
    Continuous (fun M : Matrix a a ℂ => (F * M).trace.re) := by
  fun_prop

theorem isCompact_twoExpectationSlice (ρ : State a) (F G : Matrix a a ℂ) :
    IsCompact (twoExpectationSlice ρ F G) := by
  have heq : twoExpectationSlice ρ F G = State.stateMatrixSet a ∩
      {M | (F * M).trace.re = (F * ρ.matrix).trace.re} ∩
      {M | (G * M).trace.re = (G * ρ.matrix).trace.re} := by
    ext M
    simp only [twoExpectationSlice, Set.mem_setOf_eq, Set.mem_inter_iff,
      State.mem_stateMatrixSet_iff, and_assoc]
  rw [heq]
  exact ((State.stateMatrixSet_isCompact (a := a)).inter_right
    (isClosed_eq (continuous_matrixExpectation F) continuous_const)).inter_right
    (isClosed_eq (continuous_matrixExpectation G) continuous_const)

theorem convex_twoExpectationSlice (ρ : State a) (F G : Matrix a a ℂ) :
    Convex ℝ (twoExpectationSlice ρ F G) := by
  intro X hX Y hY p q hp hq hpq
  refine ⟨(hX.1.smul hp).add (hY.1.smul hq), ?_, ?_, ?_⟩
  · simp only [trace_add, trace_smul, hX.2.1, hY.2.1]
    rw [← add_smul, hpq, one_smul]
  · simp only [mul_add, Matrix.mul_smul, trace_add, trace_smul, Complex.add_re,
      Complex.smul_re, hX.2.2.1, hY.2.2.1, smul_eq_mul]
    rw [← add_mul, hpq, one_mul]
  · simp only [mul_add, Matrix.mul_smul, trace_add, trace_smul, Complex.add_re,
      Complex.smul_re, hX.2.2.2, hY.2.2.2, smul_eq_mul]
    rw [← add_mul, hpq, one_mul]

/-- Rank-one extreme points imply a finite pure decomposition inside the slice. -/
theorem exists_pureDecomposition_of_extreme_rank_le_one
    (ρ : State a) (F G : Matrix a a ℂ)
    (hrank : ∀ M ∈ (twoExpectationSlice ρ F G).extremePoints ℝ, M.rank ≤ 1) :
    ∃ E : PureDecomposition a, E.averageState = ρ ∧
      ∀ j, 0 < (E.probs j : ℝ) ∧
        (F * (E.vectors j).state.matrix).trace.re = (F * ρ.matrix).trace.re ∧
        (G * (E.vectors j).state.matrix).trace.re = (G * ρ.matrix).trace.re := by
  classical
  letI : LocallyConvexSpace ℝ (Matrix a a ℂ) := NormedSpace.toLocallyConvexSpace
  let S := twoExpectationSlice ρ F G
  let f : PureVector a → Matrix a a ℂ := fun ψ => ψ.state.matrix
  have hf : Continuous f := State.continuous_matrix.comp PureVector.state_continuous
  let P : Set (Matrix a a ℂ) := f '' (f ⁻¹' S)
  have hS : IsCompact S := isCompact_twoExpectationSlice ρ F G
  have hP : IsCompact P := (hS.isClosed.preimage hf).isCompact.image hf
  have hext : S.extremePoints ℝ ⊆ P := by
    intro M hM
    have hMS : M ∈ S := extremePoints_subset hM
    let σ : State a := ⟨M, hMS.1, hMS.2.1⟩
    obtain ⟨ψ, hψ⟩ := exists_pureVector_of_rank_le_one σ (hrank M hM)
    have hmat : f ψ = M := congrArg State.matrix hψ
    exact ⟨ψ, by change f ψ ∈ S; rwa [hmat], hmat⟩
  have hρ : ρ.matrix ∈ convexHull ℝ P := by
    have hclosed : IsClosed (convexHull ℝ P) :=
      (isCompact_convexHull_of_isCompact hP).isClosed
    have hsub : S ⊆ convexHull ℝ P := by
      rw [← closure_convexHull_extremePoints hS (convex_twoExpectationSlice ρ F G)]
      exact closure_minimal (convexHull_mono hext) hclosed
    exact hsub ⟨ρ.pos, ρ.trace_eq_one, rfl, rfl⟩
  obtain ⟨ι, hι, z, w, hz, _, hwpos, hwone, hwρ⟩ :=
    eq_pos_convex_span_of_mem_convexHull hρ
  letI := hι
  choose ψ hψmem hψ using fun i => hz (Set.mem_range_self i)
  let J := PLift ι
  let v : J → PureVector a := fun i => ψ i.down
  let p : J → ℝ≥0 := fun i => ⟨w i.down, (hwpos i.down).le⟩
  have hp : ∑ i, p i = 1 := by
    apply NNReal.coe_injective
    push_cast
    exact (Equiv.plift.sum_comp w).trans hwone
  let E := PureDecomposition.ofFinite p hp v
  refine ⟨E, ?_, ?_⟩
  · apply State.ext
    change (∑ k : Fin (Fintype.card J),
      ((p ((Fintype.equivFin J).symm k) : ℝ≥0) : ℂ) •
        (v ((Fintype.equivFin J).symm k)).state.matrix) = ρ.matrix
    rw [(Fintype.equivFin J).symm.sum_comp
      (fun i : J => (p i : ℂ) • (v i).state.matrix)]
    have heach (i : J) : (p i : ℂ) • (v i).state.matrix = w i.down • z i.down := by
      change (w i.down : ℂ) • f (ψ i.down) = w i.down • z i.down
      rw [hψ]
      ext x y
      simp [Matrix.smul_apply, Complex.real_smul]
    simp_rw [heach]
    exact (Equiv.plift.sum_comp (fun i => w i • z i)).trans hwρ
  · intro j
    let i : J := (Fintype.equivFin J).symm j
    have hv : f (ψ i.down) ∈ S := hψmem i.down
    exact ⟨hwpos i.down, hv.2.2.1, hv.2.2.2⟩

end
end AmplitudeDamping
