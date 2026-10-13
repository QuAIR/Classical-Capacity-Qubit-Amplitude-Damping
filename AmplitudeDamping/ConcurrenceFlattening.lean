import AmplitudeDamping.FlatConcurrence
import AmplitudeDamping.RealZeroDiagonal

open scoped BigOperators ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT Matrix
noncomputable section
set_option maxHeartbeats 1000000

/-- The concurrence quadratic form commutes with finite linear combinations. -/
theorem rawConcurrence_sum_smul {ι : Type*} [Fintype ι]
    (v : ι → Qubit × Qubit → ℂ) (c : ι → ℂ) :
    rawConcurrence (fun x => ∑ i, c i * v i x) =
      ∑ i, ∑ j, c i * c j * concurrenceOverlap (v i) (v j) := by
  have hleft (u : Qubit × Qubit → ℂ) :
      concurrenceOverlap (fun x => ∑ i, c i * v i x) u =
        ∑ i, c i * concurrenceOverlap (v i) u := by
    unfold concurrenceOverlap
    simp only [Finset.sum_mul, Finset.mul_sum, mul_add, mul_sub,
      Finset.sum_add_distrib, Finset.sum_sub_distrib]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have hright (u : Qubit × Qubit → ℂ) :
      concurrenceOverlap u (fun x => ∑ i, c i * v i x) =
        ∑ i, c i * concurrenceOverlap u (v i) := by
    rw [concurrenceOverlap_comm, hleft]
    simp_rw [concurrenceOverlap_comm u]
  rw [← concurrenceOverlap_self, hleft]
  simp_rw [hright, Finset.mul_sum, mul_assoc]

/-- Real isometric row mixing leaves the sum of rank-one states unchanged. -/
theorem sum_rankOne_real_isometry {ι κ a : Type*}
    [Fintype ι] [DecidableEq ι] [Fintype κ] [Fintype a]
    (R : Matrix κ ι ℝ) (hR : Rᵀ * R = 1) (v : ι → a → ℂ) :
    (∑ s, rankOneMatrix (fun x => ∑ i, (R s i : ℂ) * v i x)) =
      ∑ i, rankOneMatrix (v i) := by
  classical
  have hr (i j : ι) : ∑ s, (R s i : ℂ) * (R s j : ℂ) = if i = j then 1 else 0 := by
    have h := congrFun (congrFun hR i) j
    simpa [Matrix.mul_apply, Matrix.one_apply, apply_ite] using congrArg Complex.ofReal h
  ext x y
  simp only [Matrix.sum_apply, rankOneMatrix_apply, map_sum, map_mul, Complex.star_def,
    Complex.conj_ofReal, Finset.sum_mul, Finset.mul_sum]
  calc
    _ = ∑ i, ∑ j, (∑ s, (R s j : ℂ) * (R s i : ℂ)) * v j x * star (v i y) := by
      simp only [Finset.sum_mul]
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro i _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro s _
      simp only [Complex.star_def]
      ring
    _ = _ := by simp [hr]

/-- The norm Gram form of a row combination. -/
theorem rankOne_trace_sum_smul {ι : Type*} [Fintype ι]
    (v : ι → Qubit × Qubit → ℂ) (c : ι → ℝ) :
    (rankOneMatrix (fun x => ∑ i, (c i : ℂ) * v i x)).trace.re =
      ∑ i, ∑ j, c i * c j * (∑ x, v i x * star (v j x)).re := by
  have he : (rankOneMatrix (fun x => ∑ i, (c i : ℂ) * v i x)).trace =
      ∑ i, ∑ j, ((c i * c j : ℝ) : ℂ) * (∑ x, v i x * star (v j x)) := by
    conv_rhs => rw [Finset.sum_comm]
    simp only [Matrix.trace, Matrix.diag_apply, rankOneMatrix_apply,
      map_sum, map_mul, Complex.star_def, Complex.conj_ofReal,
      Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro j _
    apply Finset.sum_congr rfl
    intro x _
    simp only [Complex.ofReal_mul]
    ring
  rw [he]
  simp only [Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero]

private theorem real_congruence_diagonal {ι κ : Type*} [Fintype ι]
    (R : Matrix κ ι ℝ) (B : Matrix ι ι ℝ) (s : κ) :
    (R * B * Rᵀ) s s = ∑ i, ∑ j, R s i * R s j * B i j := by
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- A real concurrence Gram matrix can be flattened by an isometric mixing,
without changing the represented state. -/
theorem exists_flat_raw_family {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Qubit × Qubit → ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hreal : ∀ i j, (concurrenceOverlap (v i) (v j)).im = 0)
    (htrace : (∑ i, (rawConcurrence (v i)).re) =
      c * ∑ i, (rankOneMatrix (v i)).trace.re) :
    ∃ w : (ι → Bool) → Qubit × Qubit → ℂ,
      (∑ s, rankOneMatrix (w s)) = ∑ i, rankOneMatrix (v i) ∧
      ∀ s, 2 * ‖(Matrix.of fun j k => w s (j,k)).det‖ =
        (rankOneMatrix (w s)).trace.re * c := by
  let B : Matrix ι ι ℝ := fun i j => (concurrenceOverlap (v i) (v j)).re
  let G : Matrix ι ι ℝ := fun i j => (∑ x, v i x * star (v j x)).re
  have hB : B.IsSymm := by
    ext i j
    exact congrArg Complex.re (concurrenceOverlap_comm (v j) (v i))
  have hG : G.IsSymm := by
    ext i j
    simp only [G, Matrix.transpose_apply, Complex.re_sum,
      Complex.mul_re, Complex.star_def, Complex.conj_re, Complex.conj_im]
    apply Finset.sum_congr rfl
    intro x _
    ring
  have ht : B.trace = c * G.trace := by
    simpa only [Matrix.trace, Matrix.diag_apply, B, G, concurrenceOverlap_self,
      rankOneMatrix_apply] using htrace
  obtain ⟨R, hR, hdiag⟩ := RealZeroDiagonal.exists_isometry_proportional_diagonal B G hB hG c ht
  let w : (ι → Bool) → Qubit × Qubit → ℂ := fun s x => ∑ i, (R s i : ℂ) * v i x
  refine ⟨w, sum_rankOne_real_isometry R hR v, ?_⟩
  intro s
  have hq : rawConcurrence (w s) = ((R * B * Rᵀ) s s : ℂ) := by
    rw [show w s = (fun x => ∑ i, (R s i : ℂ) * v i x) from rfl,
      rawConcurrence_sum_smul, real_congruence_diagonal]
    simp only [Complex.ofReal_sum, Complex.ofReal_mul]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    apply Complex.ext
    · rfl
    · simp [B, hreal]
  have hg : (rankOneMatrix (w s)).trace.re = (R * G * Rᵀ) s s := by
    exact (rankOne_trace_sum_smul v (R s)).trans (real_congruence_diagonal R G s).symm
  rw [← norm_rawConcurrence, hq, hdiag, ← hg]
  rw [Complex.norm_of_nonneg (mul_nonneg hc (Matrix.PosSemidef.trace_nonneg
    (rankOneMatrix_pos (w s))).1)]
  exact mul_comm _ _

end
end AmplitudeDamping
