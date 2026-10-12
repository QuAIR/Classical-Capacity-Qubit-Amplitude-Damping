import AmplitudeDamping.ConvexRoof

/-! # Pure vectors for states of matrix rank at most one -/

open scoped BigOperators ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT Matrix
noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

/-- A normalized positive matrix of rank at most one is represented by a
normalized pure vector. -/
theorem exists_pureVector_of_rank_le_one (ρ : State a)
    (hrank : ρ.matrix.rank ≤ 1) : ∃ ψ : PureVector a, ψ.state = ρ := by
  classical
  let U := ρ.pos.isHermitian.eigenvectorUnitary
  let D : Matrix a a ℂ := diagonal (fun i => (ρ.pos.isHermitian.eigenvalues i : ℂ))
  have hspec : ρ.matrix = (U : Matrix a a ℂ) * D * (U⁻¹ : Matrix.unitaryGroup a ℂ) := by
    simpa [U, D, IsHermitian.spectral_theorem, Unitary.conjStarAlgAut_apply]
      using ρ.pos.isHermitian.spectral_theorem
  have hD : D = (U⁻¹ : Matrix.unitaryGroup a ℂ) * ρ.matrix * (U : Matrix a a ℂ) := by
    rw [hspec]
    simp [← Matrix.mul_assoc]
    simp [Matrix.mul_assoc]
  have hDrank : D.rank ≤ 1 := by
    rw [hD]
    exact (Matrix.rank_mul_le_left _ _).trans
      ((Matrix.rank_mul_le_right _ _).trans hrank)
  have hcard : (Finset.univ.filter fun i => ρ.pos.isHermitian.eigenvalues i ≠ 0).card ≤ 1 := by
    simpa only [D, Matrix.rank_diagonal, Complex.ofReal_ne_zero, Fintype.card_subtype] using hDrank
  have hex : ∃ i, ρ.pos.isHermitian.eigenvalues i ≠ 0 := by
    by_contra! h
    have hh := State.sum_eigenvalues_eq_one ρ
    simp [h] at hh
  obtain ⟨i, hi⟩ := hex
  have hzero (j : a) (hji : j ≠ i) : ρ.pos.isHermitian.eigenvalues j = 0 := by
    by_contra hj
    have := Finset.card_le_one.mp hcard j (by simp [hj]) i (by simp [hi])
    exact hji this
  have hiOne : ρ.pos.isHermitian.eigenvalues i = 1 := by
    have hs := State.sum_eigenvalues_eq_one ρ
    rwa [Finset.sum_eq_single i (fun j _ hji => hzero j hji) (by simp)] at hs
  refine ⟨ρ.spectralPureVector i, State.ext ?_⟩
  rw [State.matrix_eq_sum_spectralPureVector ρ,
    Finset.sum_eq_single i (fun j _ hji => by simp [hzero j hji]) (by simp), hiOne]
  simp

/-- A pure vector is orthogonal to the kernel of its associated state. -/
theorem pureVector_orthogonal_kernel (ψ : PureVector a) (z : a → ℂ)
    (hz : ψ.state.matrix.mulVec z = 0) :
    (∑ i, star (z i) * ψ.amp i) = 0 := by
  classical
  have hnonzero : ∃ i, ψ.amp i ≠ 0 := by
    by_contra! h
    have ht := ψ.trace_rankOne_eq_one
    simp [rankOneMatrix_trace, dotProduct, h] at ht
  obtain ⟨i, hi⟩ := hnonzero
  have hz' := congrFun hz i
  have hinner : (∑ j, star (ψ.amp j) * z j) = 0 := by
    have : ψ.amp i * (∑ j, star (ψ.amp j) * z j) = 0 := by
      simpa [Matrix.mulVec, dotProduct, ← Finset.mul_sum, mul_assoc] using hz'
    exact (mul_eq_zero.mp this).resolve_left hi
  have hc := congrArg star hinner
  simpa [star_sum, mul_comm] using hc

end
end AmplitudeDamping
