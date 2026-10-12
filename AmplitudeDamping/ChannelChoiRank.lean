import AmplitudeDamping.ChannelChoi
import AmplitudeDamping.TwoKrausRoof

/-! # Kraus-rank bounds for normalized Choi states -/
namespace AmplitudeDamping
open QIT
open scoped BigOperators Matrix
noncomputable section
universe u v w
variable {a : Type u} {b : Type v} {κ : Type w}
variable [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b] [Fintype κ]

/-- Vectorized Kraus operators factor the Choi matrix through the Kraus index. -/
theorem channelChoiState_rank_le_kraus_card (N : Channel a b)
    (K : κ → Matrix b a ℂ) (hN : N.map = MatrixMap.ofKraus K) :
    (channelChoiState N).matrix.rank ≤ Fintype.card κ := by
  let V : Matrix (a × b) κ ℂ := fun z k => K k z.2 z.1
  have hfactor : MatrixMap.choi (MatrixMap.ofKraus K) = V * V.conjTranspose := by
    rw [MatrixMap.choi_ofKraus]
    ext x y
    simp [Matrix.mul_apply, V, Matrix.vecMulVec, Matrix.sum_apply]
  rw [channelChoiState_matrix, hN, hfactor, ← Matrix.smul_mul]
  exact (Matrix.rank_mul_le_left _ _).trans (Matrix.rank_le_card_width _)

/-- Every two-Kraus qubit channel has a product vector in its Choi kernel. -/
theorem channelChoiState_product_kernel_of_twoKraus
    (N : Channel Qubit Qubit) (K : κ → Matrix Qubit Qubit ℂ)
    (hN : N.map = MatrixMap.ofKraus K) (hcard : Fintype.card κ ≤ 2) :
    ∃ u v : Qubit → ℂ, u ≠ 0 ∧ v ≠ 0 ∧
      (channelChoiState N).matrix *ᵥ (fun p => u p.1 * v p.2) = 0 := by
  apply exists_product_kernelVector_of_rank_le_two
  rw [card_filter_eigenvalues_eq_rank]
  exact (channelChoiState_rank_le_kraus_card N K hN).trans hcard
end
end AmplitudeDamping
