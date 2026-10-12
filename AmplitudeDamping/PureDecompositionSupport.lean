import AmplitudeDamping.StinespringEOF

/-! # Support of positive-weight pure decomposition components -/

open scoped BigOperators ComplexConjugate
namespace AmplitudeDamping
open QIT Matrix
noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Every positive-weight component of a pure decomposition is orthogonal to
the kernel of its average state. -/
theorem PureDecomposition.component_orthogonal_kernel
    (E : PureDecomposition a) (j : Fin E.card) (hj : 0 < (E.probs j : ℝ))
    (z : a → ℂ) (hz : E.averageState.matrix.mulVec z = 0) :
    (∑ i, star (z i) * (E.vectors j).amp i) = 0 := by
  have h := star_inner_averageState_mulVec E z
  rw [hz, dotProduct_zero, ← Complex.ofReal_sum] at h
  have hsum : (∑ k : Fin E.card,
      (E.probs k : ℝ) * Complex.normSq (star (E.vectors k).amp ⬝ᵥ z)) = 0 := by
    exact Complex.ofReal_injective (by simpa only [Complex.ofReal_zero] using h.symm)
  have hnonneg (k : Fin E.card) (_ : k ∈ Finset.univ) :
      0 ≤ (E.probs k : ℝ) * Complex.normSq (star (E.vectors k).amp ⬝ᵥ z) :=
    mul_nonneg (NNReal.coe_nonneg _) (Complex.normSq_nonneg _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).mp hsum j (Finset.mem_univ j)
  have hinner : star (E.vectors j).amp ⬝ᵥ z = 0 :=
    Complex.normSq_eq_zero.mp ((mul_eq_zero.mp hterm).resolve_left hj.ne')
  have hc := congrArg star hinner
  simpa [dotProduct, star_sum, mul_comm] using hc

end
end AmplitudeDamping
