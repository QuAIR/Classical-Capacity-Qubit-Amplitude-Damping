import AmplitudeDamping.TwoExpectationGeometry
import AmplitudeDamping.PSDPerturbation
import QIT.States.PosSqrt
import Mathlib.Analysis.Convex.Extreme
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Order

/-!
# Rank-one extreme points of two-expectation slices

Two nonzero eigenvalues of the state's square root provide four independent
real Hermitian directions. Three linear constraints (trace and two real
expectations) leave a nonzero direction. Square-root conjugation allows a
small perturbation in either sign to remain positive, contradicting extremality.
-/

open scoped BigOperators ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT Matrix Unitary
noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

/-- The four real coordinates of a Hermitian two-dimensional block. -/
def hermitianBlock (i j : a) (x : Fin 4 → ℝ) : Matrix a a ℂ :=
  Matrix.single i i (x 0 : ℂ) + Matrix.single j j (x 1 : ℂ) +
  Matrix.single i j ((x 2 : ℂ) + (x 3 : ℂ) * Complex.I) +
  Matrix.single j i ((x 2 : ℂ) - (x 3 : ℂ) * Complex.I)

omit [Fintype a] in
lemma hermitianBlock_isHermitian (i j : a) (x : Fin 4 → ℝ) :
    (hermitianBlock i j x).IsHermitian := by
  unfold hermitianBlock Matrix.IsHermitian
  simp only [Matrix.conjTranspose_add, Matrix.conjTranspose_single,
    star_add, star_sub, star_mul, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I, neg_mul, sub_neg_eq_add, mul_comm]
  abel_nf

omit [Fintype a] in
lemma hermitianBlock_add (i j : a) (x y : Fin 4 → ℝ) :
    hermitianBlock i j (x + y) = hermitianBlock i j x + hermitianBlock i j y := by
  simp only [hermitianBlock, Pi.add_apply, Complex.ofReal_add, add_mul,
    sub_eq_add_neg, neg_add_rev, Matrix.single_add]
  abel_nf

omit [Fintype a] in
lemma hermitianBlock_smul (i j : a) (t : ℝ) (x : Fin 4 → ℝ) :
    hermitianBlock i j (t • x) = t • hermitianBlock i j x := by
  simp only [hermitianBlock, Pi.smul_apply, smul_eq_mul, Complex.ofReal_mul,
    smul_add, Matrix.smul_single, Complex.real_smul]
  congr 2 <;> congr 1 <;> ring

lemma exists_nonzero_three_constraints (L : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ)) :
    ∃ x, x ≠ 0 ∧ L x = 0 := by
  by_contra! h
  have hinj : Function.Injective L := by
    apply (LinearMap.ker_eq_bot).mp
    rw [LinearMap.ker_eq_bot']
    intro x hx
    by_contra hne
    exact h x hne hx
  have hd := LinearMap.finrank_le_finrank_of_injective hinj
  norm_num at hd

lemma diagonal_hermitianBlock_ne_zero (i j : a) (hij : i ≠ j)
    (d : a → ℂ) (hi : d i ≠ 0) (hj : d j ≠ 0)
    (x : Fin 4 → ℝ) (hx : x ≠ 0) :
    Matrix.diagonal d * hermitianBlock i j x * Matrix.diagonal d ≠ 0 := by
  intro hz
  have he (k l : a) := congrArg (fun M : Matrix a a ℂ => M k l) hz
  have h00 : (x 0 : ℂ) = 0 := by
    have h := he i i
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, hermitianBlock,
      Matrix.single_apply, hij, hij.symm, hi] using h
  have h11 : (x 1 : ℂ) = 0 := by
    have h := he j j
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, hermitianBlock,
      Matrix.single_apply, hij, hij.symm, hj] using h
  have h01 : (x 2 : ℂ) + (x 3 : ℂ) * Complex.I = 0 := by
    have h := he i j
    simpa [Matrix.diagonal_mul, Matrix.mul_diagonal, hermitianBlock,
      Matrix.single_apply, hij, hij.symm, hi, hj] using h
  apply hx
  funext k
  fin_cases k
  · exact_mod_cast h00
  · exact_mod_cast h11
  · simpa using congrArg Complex.re h01
  · simpa using congrArg Complex.im h01

set_option maxHeartbeats 800000 in
/-- A mixed state admits a nonzero square-root-conjugated Hermitian direction
annihilating its trace and two prescribed real trace functionals. -/
lemma exists_twoExpectation_direction (ρ : State a) (F G : Matrix a a ℂ)
    (hrank : 1 < ρ.matrix.rank) :
    ∃ X : Matrix a a ℂ, X.IsHermitian ∧
      let H := ρ.sqrtMatrix * X * ρ.sqrtMatrix
      H ≠ 0 ∧ H.trace = 0 ∧ (F * H).trace.re = 0 ∧ (G * H).trace.re = 0 := by
  let B := ρ.sqrtMatrix
  have hB : B.IsHermitian := ρ.sqrtMatrix_isHermitian
  have hBrank : 1 < B.rank := by
    have hsq : B * B = ρ.matrix := ρ.sqrtMatrix_mul_self
    have h := Matrix.rank_mul_le_left B B
    rw [hsq] at h
    exact hrank.trans_le h
  have hcard : 1 < Fintype.card {k // hB.eigenvalues k ≠ 0} := by
    rwa [← hB.rank_eq_card_non_zero_eigs]
  haveI : Nontrivial {k // hB.eigenvalues k ≠ 0} :=
    Fintype.one_lt_card_iff_nontrivial.mp hcard
  obtain ⟨i, j, hij⟩ := exists_pair_ne {k // hB.eigenvalues k ≠ 0}
  have hij' : i.val ≠ j.val := fun h => hij (Subtype.ext h)
  let U := hB.eigenvectorUnitary
  let D : Matrix a a ℂ := Matrix.diagonal (fun k => (hB.eigenvalues k : ℂ))
  let C := conjStarAlgAut ℂ (Matrix a a ℂ) U
  have hBD : B = C D := hB.spectral_theorem
  let L : (Fin 4 → ℝ) →ₗ[ℝ] Matrix a a ℂ :=
    { toFun := fun x => C (D * hermitianBlock i.val j.val x * D)
      map_add' := by
        intro x y
        simp [hermitianBlock_add, Matrix.mul_add, Matrix.add_mul, map_add]
      map_smul' := by
        intro t x
        simp only [hermitianBlock_smul, Matrix.mul_smul, Matrix.smul_mul,
          RingHom.id_apply]
        exact C.toAlgEquiv.toLinearEquiv.map_smul_of_tower t _ }
  let T : (Fin 4 → ℝ) →ₗ[ℝ] (Fin 3 → ℝ) :=
    { toFun := fun x => ![(L x).trace.re, (F * L x).trace.re, (G * L x).trace.re]
      map_add' := by
        intro x y
        ext k
        fin_cases k <;> simp [Matrix.mul_add, Matrix.trace_add]
      map_smul' := by
        intro t x
        ext k
        fin_cases k <;> simp [Matrix.trace_smul, Complex.real_smul] }
  obtain ⟨x, hx, hTx⟩ := exists_nonzero_three_constraints T
  let X := C (hermitianBlock i.val j.val x)
  have hX : X.IsHermitian := by
    exact Matrix.isHermitian_mul_mul_conjTranspose _ (hermitianBlock_isHermitian i.val j.val x)
  have hH : B * X * B = L x := by
    dsimp [L, X]
    calc
      B * C (hermitianBlock i.val j.val x) * B =
          C D * C (hermitianBlock i.val j.val x) * C D :=
        congrArg₂ (fun P Q : Matrix a a ℂ => P * C (hermitianBlock i.val j.val x) * Q)
          hBD hBD
      _ = _ := by simp only [map_mul]
  have hn : L x ≠ 0 := by
    intro hzero
    have hz : D * hermitianBlock i.val j.val x * D = 0 := C.injective (by simpa [L] using hzero)
    exact diagonal_hermitianBlock_ne_zero i.val j.val hij' _
      (by exact_mod_cast i.property) (by exact_mod_cast j.property) x hx hz
  have ht0 : (L x).trace.re = 0 := by
    simpa [T] using congrFun hTx 0
  have ht1 : (F * L x).trace.re = 0 := by
    simpa [T] using congrFun hTx 1
  have ht2 : (G * L x).trace.re = 0 := by
    simpa [T] using congrFun hTx 2
  refine ⟨X, hX, ?_⟩
  change B * X * B ≠ 0 ∧ _
  rw [hH]
  refine ⟨hn, ?_, ht1, ht2⟩
  apply Complex.ext ht0
  have hherm : (L x).IsHermitian := by
    rw [← hH]
    simpa only [hB.eq] using Matrix.isHermitian_conjTranspose_mul_mul B hX
  have him := congrArg Complex.im (congrArg Matrix.trace hherm)
  simp only [Matrix.trace_conjTranspose, Complex.star_def, Complex.conj_im] at him
  change (L x).trace.im = 0
  linarith

/-- Every extreme point of a density-matrix slice with two fixed expectations
has rank at most one. -/
theorem rank_le_one_of_extreme_twoExpectationSlice
    (ρ : State a) (F G : Matrix a a ℂ) (M : Matrix a a ℂ)
    (hM : M ∈ (twoExpectationSlice ρ F G).extremePoints ℝ) : M.rank ≤ 1 := by
  by_contra! hrank
  let σ : State a := ⟨M, hM.1.1, hM.1.2.1⟩
  obtain ⟨X, hX, hn, htr, hF, hG⟩ := exists_twoExpectation_direction σ F G hrank
  obtain ⟨t, ht, hp, hm⟩ := exists_pos_psd_sqrt_perturbation σ X hX
  let H := σ.sqrtMatrix * X * σ.sqrtMatrix
  have hplus : M + t • H ∈ twoExpectationSlice ρ F G := by
    refine ⟨hp, ?_, ?_, ?_⟩
    · simpa only [H, Matrix.trace_add, Matrix.trace_smul, htr, smul_zero, add_zero]
        using hM.1.2.1
    · simpa only [H, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
        Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hF, mul_zero, add_zero]
        using hM.1.2.2.1
    · simpa only [H, Matrix.mul_add, Matrix.mul_smul, Matrix.trace_add, Matrix.trace_smul,
        Complex.add_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hG, mul_zero, add_zero]
        using hM.1.2.2.2
  have hminus : M - t • H ∈ twoExpectationSlice ρ F G := by
    refine ⟨hm, ?_, ?_, ?_⟩
    · simpa only [H, Matrix.trace_sub, Matrix.trace_smul, htr, smul_zero, sub_zero]
        using hM.1.2.1
    · simpa only [H, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
        Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hF, mul_zero]
        using hM.1.2.2.1
    · simpa only [H, Matrix.mul_sub, Matrix.mul_smul, Matrix.trace_sub, Matrix.trace_smul,
        Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, zero_mul, sub_zero, hG, mul_zero]
        using hM.1.2.2.2
  have heq := hM.2 hplus hminus (mem_openSegment_add_sub (𝕜 := ℝ) M (t • H))
  have hz : t • H = 0 := add_left_cancel (heq.trans (add_zero M).symm)
  exact hn ((smul_eq_zero.mp hz).resolve_left ht.ne')

end
end AmplitudeDamping
