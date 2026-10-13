import Mathlib.Analysis.Matrix.Spectrum
import Mathlib.LinearAlgebra.Matrix.Symmetric

/-!
# Zero-diagonal isometric dilation of real symmetric matrices

A real symmetric matrix of trace zero admits a rectangular isometry whose
congruence has zero diagonal. The new rows are indexed by all sign patterns
on an eigenbasis. This form permits enlargement of a finite ensemble.
-/

open scoped BigOperators Matrix

namespace AmplitudeDamping
namespace RealZeroDiagonal

noncomputable section

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- The real sign represented by a Boolean. -/
def sign (b : Bool) : ℝ := if b then 1 else -1

@[simp] theorem sign_sq (b : Bool) : sign b * sign b = 1 := by
  cases b <;> norm_num [sign]

@[simp] theorem sign_not (b : Bool) : sign (!b) = -sign b := by
  cases b <;> norm_num [sign]

/-- Flip one coordinate in the set of all sign patterns. -/
def flip (i : n) : (n → Bool) ≃ (n → Bool) :=
  { toFun := fun s j => if j = i then !(s j) else s j
    invFun := fun s j => if j = i then !(s j) else s j
    left_inv := by intro s; funext j; by_cases h : j = i <;> simp [h]
    right_inv := by intro s; funext j; by_cases h : j = i <;> simp [h] }

/-- Distinct sign coordinates have vanishing correlation. -/
theorem sum_sign_mul_of_ne (i j : n) (hij : i ≠ j) :
    ∑ s : n → Bool, sign (s i) * sign (s j) = 0 := by
  have h := (flip i).sum_comp (fun s : n → Bool => sign (s i) * sign (s j))
  have heq : (∑ s : n → Bool, sign (s i) * sign (s j)) =
      -(∑ s : n → Bool, sign (s i) * sign (s j)) := by
    simpa [flip, Ne.symm hij, Finset.sum_neg_distrib] using h.symm
  linarith

/-- Sign columns, normalized to have Euclidean norm one. -/
def signIsometry : Matrix (n → Bool) n ℝ :=
  fun s i => (Real.sqrt (Fintype.card (n → Bool)))⁻¹ * sign (s i)

lemma card_signs_pos : (0 : ℝ) < Fintype.card (n → Bool) := by
  exact_mod_cast Fintype.card_pos

lemma normalization_sq :
    ((Real.sqrt (Fintype.card (n → Bool)))⁻¹) ^ 2 *
      (Fintype.card (n → Bool) : ℝ) = 1 := by
  rw [inv_pow, Real.sq_sqrt (le_of_lt card_signs_pos)]
  exact inv_mul_cancel₀ (ne_of_gt card_signs_pos)

/-- All normalized sign columns are orthonormal. -/
theorem signIsometry_transpose_mul :
    (signIsometry (n := n))ᵀ * (signIsometry (n := n)) = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.transpose_apply, signIsometry, Matrix.one_apply]
  simp_rw [show ∀ s : n → Bool,
    (Real.sqrt (Fintype.card (n → Bool)))⁻¹ * sign (s i) *
      ((Real.sqrt (Fintype.card (n → Bool)))⁻¹ * sign (s j)) =
    ((Real.sqrt (Fintype.card (n → Bool)))⁻¹) ^ 2 * (sign (s i) * sign (s j))
    from fun s => by ring]
  rw [← Finset.mul_sum]
  by_cases h : i = j
  · subst j
    simp only [sign_sq, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one,
      ↓reduceIte]
    exact normalization_sq
  · rw [sum_sign_mul_of_ne i j h, mul_zero, if_neg h]

/-- Every diagonal entry after sign mixing is the same scaled trace. -/
theorem signIsometry_diagonal (d : n → ℝ) (s : n → Bool) :
    ((signIsometry (n := n)) * Matrix.diagonal d * (signIsometry (n := n))ᵀ) s s =
      ((Real.sqrt (Fintype.card (n → Bool)))⁻¹) ^ 2 * ∑ i, d i := by
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_diagonal, Matrix.transpose_apply, signIsometry]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  have h := sign_sq (s i)
  calc
    _ = ((Real.sqrt (Fintype.card (n → Bool)))⁻¹) ^ 2 * d i *
        (sign (s i) * sign (s i)) := by ring
    _ = _ := by rw [h, mul_one]

/-- Every real symmetric trace-zero matrix has a zero-diagonal congruence
by a rectangular real isometry. The row index is always finite and nonempty. -/
theorem exists_isometry_zero_diagonal (B : Matrix n n ℝ)
    (hB : B.IsSymm) (htrace : B.trace = 0) :
    ∃ R : Matrix (n → Bool) n ℝ,
      Rᵀ * R = 1 ∧ ∀ s, (R * B * Rᵀ) s s = 0 := by
  have hh : B.IsHermitian := by
    simpa only [Matrix.IsHermitian, Matrix.conjTranspose_eq_transpose_of_trivial]
      using hB.eq
  let V : Matrix n n ℝ := hh.eigenvectorUnitary
  have hV : Vᵀ * V = 1 := Matrix.UnitaryGroup.star_mul_self hh.eigenvectorUnitary
  have hV' : V * Vᵀ = 1 := mul_eq_one_comm.mp hV
  have hd : Vᵀ * B * V = Matrix.diagonal hh.eigenvalues := by
    simpa [Unitary.conjStarAlgAut_star_apply, V, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_eq_transpose_of_trivial, Function.comp_def]
      using hh.conjStarAlgAut_star_eigenvectorUnitary
  have hsum : ∑ i, hh.eigenvalues i = 0 := by
    rw [← Matrix.trace_diagonal, ← hd, Matrix.trace_mul_cycle, hV', Matrix.one_mul]
    exact htrace
  let S : Matrix (n → Bool) n ℝ := signIsometry
  refine ⟨S * Vᵀ, ?_, ?_⟩
  · calc
      (S * Vᵀ)ᵀ * (S * Vᵀ) = V * (Sᵀ * S) * Vᵀ := by
        simp only [Matrix.transpose_mul, Matrix.transpose_transpose, Matrix.mul_assoc]
      _ = 1 := by rw [show Sᵀ * S = 1 from signIsometry_transpose_mul,
        Matrix.mul_one, hV']
  · intro s
    have heq : (S * Vᵀ) * B * (S * Vᵀ)ᵀ =
        S * Matrix.diagonal hh.eigenvalues * Sᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_transpose, ← hd]
      simp only [Matrix.mul_assoc]
    rw [heq]
    change ((signIsometry (n := n)) * Matrix.diagonal hh.eigenvalues *
      (signIsometry (n := n))ᵀ) s s = 0
    rw [signIsometry_diagonal, hsum, mul_zero]

/-- Two real symmetric forms with proportional traces can be mixed so
that their diagonal entries have the same proportion term by term. -/
theorem exists_isometry_proportional_diagonal (B G : Matrix n n ℝ)
    (hB : B.IsSymm) (hG : G.IsSymm) (c : ℝ)
    (htrace : B.trace = c * G.trace) :
    ∃ R : Matrix (n → Bool) n ℝ,
      Rᵀ * R = 1 ∧ ∀ s, (R * B * Rᵀ) s s = c * (R * G * Rᵀ) s s := by
  have hzero : (B - c • G).trace = 0 := by
    simp [htrace]
  obtain ⟨R, hR, hdiag⟩ := exists_isometry_zero_diagonal
    (B - c • G) (hB.sub (hG.smul c)) hzero
  refine ⟨R, hR, fun s => ?_⟩
  have hs := hdiag s
  simpa only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_smul, Matrix.smul_mul,
    Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, sub_eq_zero] using hs

omit [Fintype n] in
/-- A real rectangular isometry is also a complex rectangular isometry. -/
theorem complex_isometry_of_real {m : Type*} [Fintype m]
    (R : Matrix m n ℝ) (hR : Rᵀ * R = 1) :
    (R.map Complex.ofReal)ᴴ * R.map Complex.ofReal = 1 := by
  have ht : (R.map Complex.ofReal)ᴴ = Rᵀ.map Complex.ofReal := by
    ext i j
    simp
  rw [ht]
  have h := congrArg (fun M : Matrix n n ℝ => M.map Complex.ofRealHom) hR
  simpa [Matrix.map_mul, Matrix.map_one, Matrix.map_apply] using h

end

end RealZeroDiagonal
end AmplitudeDamping
