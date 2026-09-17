import AmplitudeDamping.Concurrence
import Mathlib.Analysis.RCLike.Sqrt

/-!
# Product vectors in the kernel of a two-qubit state

Every two-dimensional subspace of `ℂ² ⊗ ℂ²` contains a nonzero product
vector.  This is the kernel condition that Corollary 7 of the manuscript
verifies for two-qubit states of rank at most two: given two linearly
independent kernel vectors `k₀, k₁`, the amplitude determinant of
`s • k₀ + t • k₁` is a homogeneous quadratic in `(s, t)`, which has a
nonzero zero over the complex numbers; the corresponding combination is a
nonzero kernel vector whose amplitude determinant vanishes, and a nonzero
function with vanishing amplitude determinant factors entrywise as a
product `u i * v j`.

The spectral theorem then converts "two zero eigenvalues" (equivalently,
rank at most two) into two independent kernel vectors, so every two-qubit
state of rank at most two has a nonzero product vector in its kernel.
-/

open scoped BigOperators NNReal ComplexOrder MatrixOrder Matrix

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Complex square roots square back to their argument. -/
private theorem sq_Complex_sqrt (z : ℂ) : Complex.sqrt z ^ 2 = z := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  · rw [sqrt_eq_exp hz, pow_two, ← Complex.exp_add,
    show Complex.log z / 2 + Complex.log z / 2 = Complex.log z by ring,
    Complex.exp_log hz]

/-- A homogeneous quadratic form over the complex numbers has a nonzero
zero on the projective line. -/
theorem exists_homogeneous_quadratic_zero (a b c : ℂ) :
    ∃ s t : ℂ, (s ≠ 0 ∨ t ≠ 0) ∧
      a * s * s + b * s * t + c * t * t = 0 := by
  by_cases ha : a = 0
  · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
    simp [ha]
  · have h2a : (2 : ℂ) * a ≠ 0 := mul_ne_zero two_ne_zero ha
    obtain ⟨w, hw⟩ : ∃ w : ℂ, w * w = b * b - 4 * a * c :=
      ⟨Complex.sqrt (b * b - 4 * a * c),
        by simpa [pow_two] using sq_Complex_sqrt (b * b - 4 * a * c)⟩
    refine ⟨(-b + w) / (2 * a), 1, Or.inr one_ne_zero, ?_⟩
    have hv : (2 : ℂ) * a * ((-b + w) / (2 * a)) = -b + w :=
      mul_div_cancel₀ (-b + w) h2a
    have hexp : (2 * a) * (2 * a) *
        (a * ((-b + w) / (2 * a)) * ((-b + w) / (2 * a)) +
          b * ((-b + w) / (2 * a)) * 1 + c * 1 * 1) =
        a * ((2 * a) * ((-b + w) / (2 * a))) * ((2 * a) * ((-b + w) / (2 * a))) +
          b * ((2 * a) * ((-b + w) / (2 * a))) * (2 * a) +
          c * (2 * a) * (2 * a) := by ring
    rw [hv] at hexp
    have h0 : (2 * a) * (2 * a) *
        (a * ((-b + w) / (2 * a)) * ((-b + w) / (2 * a)) +
          b * ((-b + w) / (2 * a)) * 1 + c * 1 * 1) =
        a * (w * w - (b * b - 4 * a * c)) := by
      rw [hexp]
      ring
    rw [hw, sub_self, mul_zero] at h0
    rcases mul_eq_zero.mp h0 with h1 | h1
    · exact absurd (add_self_eq_zero.mp
        ((two_mul a).symm.trans (mul_self_eq_zero.mp h1))) ha
    · exact h1

/-- A nonzero function on the two-by-two grid whose amplitude determinant
vanishes factors entrywise as a product of two nonzero vectors. -/
theorem exists_product_factors {f : (Qubit × Qubit) → ℂ} (hf : f ≠ 0)
    (hdet : f (0, 0) * f (1, 1) = f (0, 1) * f (1, 0)) :
    ∃ u v : Qubit → ℂ, u ≠ 0 ∧ v ≠ 0 ∧ ∀ i j, f (i, j) = u i * v j := by
  by_cases h00 : f (0, 0) = 0
  · by_cases h10 : f (1, 0) = 0
    · -- the first column vanishes; use the second column
      obtain ⟨i₀, hi₀⟩ : ∃ i, f (i, 1) ≠ 0 := by
        by_contra hcon
        have hf1 : ∀ i, f (i, 1) = 0 := fun i => by
          by_contra hne
          exact hcon ⟨i, hne⟩
        refine hf (funext fun p => ?_)
        obtain ⟨x, y⟩ := p
        fin_cases x <;> fin_cases y <;> simp [h00, h10, hf1]
      refine ⟨fun i => f (i, 1), fun j => if j = 1 then (1 : ℂ) else 0,
        ?_, ?_, ?_⟩
      · intro h
        exact hi₀ (congrFun h i₀)
      · intro h
        have h1 := congrFun h 1
        simp only [Pi.zero_apply] at h1
        exact one_ne_zero h1
      · intro i j
        fin_cases j
        · fin_cases i <;> simp [h00, h10]
        · simp
    · -- f (1 0) ≠ 0 forces f (0 1) = 0
      have h01 : f (0, 1) = 0 := by
        rcases mul_eq_zero.mp (by
          rw [← hdet, h00]; simp) with h | h
        · exact h
        · exact absurd h h10
      refine ⟨fun i => f (i, 0), fun j => f (1, j) / f (1, 0), ?_, ?_, ?_⟩
      · intro h
        exact h10 (congrFun h 1)
      · intro h
        have h1 := congrFun h 0
        rw [div_self h10, Pi.zero_apply] at h1
        exact one_ne_zero h1
      · intro i j
        fin_cases i <;> fin_cases j
        · show f (0, 0) = f (0, 0) * (f (1, 0) / f (1, 0))
          rw [div_self h10, mul_one]
        · show f (0, 1) = f (0, 0) * (f (1, 1) / f (1, 0))
          rw [h01, h00, zero_mul]
        · show f (1, 0) = f (1, 0) * (f (1, 0) / f (1, 0))
          rw [div_self h10, mul_one]
        · show f (1, 1) = f (1, 0) * (f (1, 1) / f (1, 0))
          rw [mul_comm (f (1, 0)), div_mul_cancel₀ (f (1, 1)) h10]
  · -- f (0 0) ≠ 0
    refine ⟨fun i => f (i, 0), fun j => f (0, j) / f (0, 0), ?_, ?_, ?_⟩
    · intro h
      exact h00 (congrFun h 0)
    · intro h
      have h1 := congrFun h 0
      rw [div_self h00, Pi.zero_apply] at h1
      exact one_ne_zero h1
    · intro i j
      fin_cases i <;> fin_cases j
      · show f (0, 0) = f (0, 0) * (f (0, 0) / f (0, 0))
        rw [div_self h00, mul_one]
      · show f (0, 1) = f (0, 0) * (f (0, 1) / f (0, 0))
        rw [mul_comm (f (0, 0)), div_mul_cancel₀ (f (0, 1)) h00]
      · show f (1, 0) = f (1, 0) * (f (0, 0) / f (0, 0))
        rw [div_self h00, mul_one]
      · show f (1, 1) = f (1, 0) * (f (0, 1) / f (0, 0))
        rw [div_eq_mul_inv, ← mul_assoc, mul_comm (f (1, 0)) (f (0, 1)),
          ← hdet, mul_comm (f (0, 0)) (f (1, 1)), mul_assoc,
          mul_inv_cancel₀ h00, mul_one]

/-- Two linearly independent grid functions: a linear combination of them
that vanishes identically has zero coefficients. -/
theorem eq_zero_of_combine {k₀ k₁ : (Qubit × Qubit) → ℂ}
    (hind : LinearIndependent ℂ ![k₀, k₁]) {s t : ℂ}
    (h : (fun p => s * k₀ p + t * k₁ p) = 0) : s = 0 ∧ t = 0 := by
  have hh := Fintype.linearIndependent_iff.1 hind ![s, t] (by
    simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    exact h)
  exact ⟨hh 0, hh 1⟩

/-- Every two-dimensional subspace of the two-qubit grid contains a nonzero
product vector: the key span statement. -/
theorem exists_product_in_span (k₀ k₁ : (Qubit × Qubit) → ℂ)
    (hind : LinearIndependent ℂ ![k₀, k₁]) :
    ∃ u v : Qubit → ℂ, u ≠ 0 ∧ v ≠ 0 ∧
      ∃ s t : ℂ, (fun p => u p.1 * v p.2) = fun p => s * k₀ p + t * k₁ p := by
  obtain ⟨s, t, hne, hq⟩ := exists_homogeneous_quadratic_zero
    (k₀ (0, 0) * k₀ (1, 1) - k₀ (0, 1) * k₀ (1, 0))
    (k₀ (0, 0) * k₁ (1, 1) + k₁ (0, 0) * k₀ (1, 1) -
      k₀ (0, 1) * k₁ (1, 0) - k₁ (0, 1) * k₀ (1, 0))
    (k₁ (0, 0) * k₁ (1, 1) - k₁ (0, 1) * k₁ (1, 0))
  have hwne : (fun p => s * k₀ p + t * k₁ p) ≠ 0 := by
    intro hw
    obtain ⟨h1, h2⟩ := eq_zero_of_combine hind hw
    rcases hne with h | h
    · exact h h1
    · exact h h2
  have hdet2 : (fun p => s * k₀ p + t * k₁ p) (0, 0) *
        (fun p => s * k₀ p + t * k₁ p) (1, 1) =
      (fun p => s * k₀ p + t * k₁ p) (0, 1) *
        (fun p => s * k₀ p + t * k₁ p) (1, 0) := by
    show (s * k₀ (0, 0) + t * k₁ (0, 0)) * (s * k₀ (1, 1) + t * k₁ (1, 1)) =
      (s * k₀ (0, 1) + t * k₁ (0, 1)) * (s * k₀ (1, 0) + t * k₁ (1, 0))
    linear_combination hq
  obtain ⟨u, v, hu, hv, huv⟩ := exists_product_factors (f :=
    fun p => s * k₀ p + t * k₁ p) hwne hdet2
  refine ⟨u, v, hu, hv, s, t, ?_⟩
  funext p
  obtain ⟨i, j⟩ := p
  exact (huv i j).symm

/-- A state annihilating two linearly independent vectors has a nonzero
product vector in its kernel. -/
theorem exists_product_kernelVector {ρ : State (Qubit × Qubit)}
    {k₀ k₁ : (Qubit × Qubit) → ℂ} (hind : LinearIndependent ℂ ![k₀, k₁])
    (hk₀ : ρ.matrix *ᵥ k₀ = 0) (hk₁ : ρ.matrix *ᵥ k₁ = 0) :
    ∃ u v : Qubit → ℂ, u ≠ 0 ∧ v ≠ 0 ∧
      ρ.matrix *ᵥ (fun p => u p.1 * v p.2) = 0 := by
  obtain ⟨u, v, hu, hv, s, t, hspan⟩ := exists_product_in_span k₀ k₁ hind
  refine ⟨u, v, hu, hv, ?_⟩
  have hconv : (fun p => u p.1 * v p.2) = s • k₀ + t • k₁ := by
    rw [hspan]
    rfl
  rw [hconv, Matrix.mulVec_add, Matrix.mulVec_smul, Matrix.mulVec_smul,
    hk₀, hk₁, smul_zero, smul_zero, add_zero]

section Spectral

variable {a : Type _} [Fintype a] [DecidableEq a]

/-- The amplitude of a spectral pure vector is a column of the eigenvector
unitary. -/
theorem spectralPureVector_amp (ρ : State a) (i x : a) :
    (ρ.spectralPureVector i).amp x =
      (ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a) x i :=
  rfl

/-- Spectral computation on plain matrices: applying `U * diag d * U†` to
the `i`-th column of `U` scales it by `d i`. -/
private theorem col_mulVec_apply (U : CMatrix a) (d : a → ℂ)
    (hUU : star U * U = 1) (M : CMatrix a)
    (hspec : M = U * Matrix.diagonal d * star U) (i x : a) :
    (M *ᵥ (fun y => U y i)) x = d i * U x i := by
  have hcol : (fun y => U y i) = U *ᵥ (Pi.single i (1 : ℂ)) := by
    funext y
    simp [Matrix.mulVec, dotProduct, Pi.single_apply]
  have hd : Matrix.diagonal d *ᵥ (Pi.single i (1 : ℂ)) =
      d i • Pi.single i (1 : ℂ) := by
    funext j
    by_cases hj : j = i
    · subst hj
      simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
        Pi.single_apply]
    · simp [Matrix.mulVec, dotProduct, Matrix.diagonal_apply,
        Pi.single_apply, hj]
  have hcomb : M *ᵥ (fun y => U y i) = d i • (U *ᵥ Pi.single i (1 : ℂ)) := by
    rw [hcol, Matrix.mulVec_mulVec, hspec, Matrix.mul_assoc, hUU,
      Matrix.mul_one, ← Matrix.mulVec_mulVec, hd, Matrix.mulVec_smul]
  rw [hcomb]
  simp [Pi.smul_apply]

/-- Spectral vectors are eigenvectors: applying the state to a spectral
vector scales it by the eigenvalue. -/
theorem mulVec_spectralPureVector_eq (ρ : State a) (i : a) :
    ρ.matrix *ᵥ (ρ.spectralPureVector i).amp =
      ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ) •
        (ρ.spectralPureVector i).amp := by
  ext x
  exact col_mulVec_apply
    ((ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a))
    (fun j => ((ρ.pos.isHermitian.eigenvalues j : ℝ) : ℂ))
    (Unitary.coe_star_mul_self ρ.pos.isHermitian.eigenvectorUnitary)
    ρ.matrix
    (by simpa [Function.comp_def, Unitary.conjStarAlgAut_apply]
      using ρ.pos.isHermitian.spectral_theorem)
    i x

/-- Columns of the eigenvector unitary are orthonormal: the spectral
vectors realize the standard inner products. -/
theorem spectral_inner_product (ρ : State a) (i j : a) :
    ∑ x, star ((ρ.spectralPureVector i).amp x) *
        (ρ.spectralPureVector j).amp x = if i = j then (1 : ℂ) else 0 := by
  rw [show (ρ.spectralPureVector i).amp =
      fun x => (ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a) x i from rfl,
    show (ρ.spectralPureVector j).amp =
      fun x => (ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a) x j from rfl]
  have hUU : star ((ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a)) *
      ((ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a)) = 1 :=
    Unitary.coe_star_mul_self ρ.pos.isHermitian.eigenvectorUnitary
  have h1 := congrFun (congrFun hUU i) j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply,
    Pi.zero_apply] using h1

/-- Spectral vectors with distinct indices are linearly independent. -/
theorem spectralPureVector_linearIndependent (ρ : State a) {i₀ i₁ : a}
    (hne : i₀ ≠ i₁) :
    LinearIndependent ℂ ![(ρ.spectralPureVector i₀).amp,
      (ρ.spectralPureVector i₁).amp] := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hentries : ∀ x, g 0 * (ρ.spectralPureVector i₀).amp x +
      g 1 * (ρ.spectralPureVector i₁).amp x = 0 := by
    intro x
    have hx := congrFun hg x
    simpa only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      Pi.smul_apply, smul_eq_mul, Pi.add_apply, Pi.zero_apply] using hx
  have hsum₀ : ∑ x, star ((ρ.spectralPureVector i₀).amp x) *
      (g 0 * (ρ.spectralPureVector i₀).amp x +
        g 1 * (ρ.spectralPureVector i₁).amp x) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [hentries x, mul_zero]
  have hsplit₀ : g 0 * (∑ x, star ((ρ.spectralPureVector i₀).amp x) *
        (ρ.spectralPureVector i₀).amp x) +
      g 1 * (∑ x, star ((ρ.spectralPureVector i₀).amp x) *
        (ρ.spectralPureVector i₁).amp x) = 0 := by
    calc g 0 * (∑ x, star ((ρ.spectralPureVector i₀).amp x) *
          (ρ.spectralPureVector i₀).amp x) +
        g 1 * (∑ x, star ((ρ.spectralPureVector i₀).amp x) *
          (ρ.spectralPureVector i₁).amp x)
        = ∑ x, star ((ρ.spectralPureVector i₀).amp x) *
            (g 0 * (ρ.spectralPureVector i₀).amp x +
              g 1 * (ρ.spectralPureVector i₁).amp x) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          show g 0 * (star ((ρ.spectralPureVector i₀).amp x) *
                (ρ.spectralPureVector i₀).amp x) +
              g 1 * (star ((ρ.spectralPureVector i₀).amp x) *
                (ρ.spectralPureVector i₁).amp x) =
              star ((ρ.spectralPureVector i₀).amp x) *
                (g 0 * (ρ.spectralPureVector i₀).amp x +
                  g 1 * (ρ.spectralPureVector i₁).amp x)
          ring
      _ = 0 := hsum₀
  rw [spectral_inner_product ρ i₀ i₀, if_pos rfl,
    spectral_inner_product ρ i₀ i₁, if_neg hne] at hsplit₀
  simp only [mul_one, mul_zero, add_zero] at hsplit₀
  have hsum₁ : ∑ x, star ((ρ.spectralPureVector i₁).amp x) *
      (g 0 * (ρ.spectralPureVector i₀).amp x +
        g 1 * (ρ.spectralPureVector i₁).amp x) = 0 := by
    refine Finset.sum_eq_zero fun x _ => ?_
    rw [hentries x, mul_zero]
  have hsplit₁ : g 0 * (∑ x, star ((ρ.spectralPureVector i₁).amp x) *
        (ρ.spectralPureVector i₀).amp x) +
      g 1 * (∑ x, star ((ρ.spectralPureVector i₁).amp x) *
        (ρ.spectralPureVector i₁).amp x) = 0 := by
    calc g 0 * (∑ x, star ((ρ.spectralPureVector i₁).amp x) *
          (ρ.spectralPureVector i₀).amp x) +
        g 1 * (∑ x, star ((ρ.spectralPureVector i₁).amp x) *
          (ρ.spectralPureVector i₁).amp x)
        = ∑ x, star ((ρ.spectralPureVector i₁).amp x) *
            (g 0 * (ρ.spectralPureVector i₀).amp x +
              g 1 * (ρ.spectralPureVector i₁).amp x) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
          refine Finset.sum_congr rfl fun x _ => ?_
          show g 0 * (star ((ρ.spectralPureVector i₁).amp x) *
                (ρ.spectralPureVector i₀).amp x) +
              g 1 * (star ((ρ.spectralPureVector i₁).amp x) *
                (ρ.spectralPureVector i₁).amp x) =
              star ((ρ.spectralPureVector i₁).amp x) *
                (g 0 * (ρ.spectralPureVector i₀).amp x +
                  g 1 * (ρ.spectralPureVector i₁).amp x)
          ring
      _ = 0 := hsum₁
  rw [spectral_inner_product ρ i₁ i₀, if_neg (Ne.symm hne),
    spectral_inner_product ρ i₁ i₁, if_pos rfl] at hsplit₁
  simp only [mul_zero, zero_add, mul_one] at hsplit₁
  intro i
  fin_cases i
  · exact hsplit₀
  · exact hsplit₁

end Spectral

/-- A two-qubit state with two zero eigenvalues — equivalently, rank at
most two — has a nonzero product vector in its kernel. -/
theorem exists_product_kernelVector_of_two_zero_eigenvalues
    (ρ : State (Qubit × Qubit)) (i₀ i₁ : Qubit × Qubit) (hne : i₀ ≠ i₁)
    (hz₀ : ρ.pos.isHermitian.eigenvalues i₀ = 0)
    (hz₁ : ρ.pos.isHermitian.eigenvalues i₁ = 0) :
    ∃ u v : Qubit → ℂ, u ≠ 0 ∧ v ≠ 0 ∧
      ρ.matrix *ᵥ (fun p => u p.1 * v p.2) = 0 := by
  have hk₀ : ρ.matrix *ᵥ (ρ.spectralPureVector i₀).amp = 0 := by
    rw [mulVec_spectralPureVector_eq, hz₀]
    simp
  have hk₁ : ρ.matrix *ᵥ (ρ.spectralPureVector i₁).amp = 0 := by
    rw [mulVec_spectralPureVector_eq, hz₁]
    simp
  exact exists_product_kernelVector
    (spectralPureVector_linearIndependent ρ hne) hk₀ hk₁

/-- Rank-at-most-two version, phrased through the number of nonzero
eigenvalues. -/
theorem exists_product_kernelVector_of_rank_le_two
    (ρ : State (Qubit × Qubit))
    (hrank : (Finset.univ.filter
      (fun i : Qubit × Qubit => ρ.pos.isHermitian.eigenvalues i ≠ 0)).card
      ≤ 2) :
    ∃ u v : Qubit → ℂ, u ≠ 0 ∧ v ≠ 0 ∧
      ρ.matrix *ᵥ (fun p => u p.1 * v p.2) = 0 := by
  have hcomp : (Finset.univ.filter
      (fun i : Qubit × Qubit => ρ.pos.isHermitian.eigenvalues i = 0)) =
      Finset.univ \ Finset.univ.filter
        (fun i : Qubit × Qubit => ρ.pos.isHermitian.eigenvalues i ≠ 0) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_sdiff]
    constructor
    · intro h hc
      rw [h] at hc
      exact hc rfl
    · intro hne
      by_contra hc
      exact hne hc
  have hcard : Fintype.card (Qubit × Qubit) = 4 := by
    simp
  have hlt : 1 < (Finset.univ.filter
      (fun i : Qubit × Qubit => ρ.pos.isHermitian.eigenvalues i = 0)).card := by
    rw [hcomp, Finset.card_sdiff, Finset.inter_univ, Finset.card_univ,
      hcard]
    omega
  obtain ⟨i₀, i₁, hmem₀, hmem₁, hne⟩ := Finset.one_lt_card_iff.mp hlt
  have hz₀ : ρ.pos.isHermitian.eigenvalues i₀ = 0 :=
    (Finset.mem_filter.1 hmem₀).2
  have hz₁ : ρ.pos.isHermitian.eigenvalues i₁ = 0 :=
    (Finset.mem_filter.1 hmem₁).2
  exact exists_product_kernelVector_of_two_zero_eigenvalues ρ i₀ i₁ hne
    hz₀ hz₁

end

end AmplitudeDamping
