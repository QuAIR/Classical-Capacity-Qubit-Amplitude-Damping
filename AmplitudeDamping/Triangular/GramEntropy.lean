import AmplitudeDamping.Triangular.ScalarNormalization

/-!
# Entropy of the two Gram matrices

For a square coefficient matrix, `Aᴴ A` and `A Aᴴ` have the same
characteristic polynomial and hence the same spectral entropy.  This is the
first spectral bridge needed to return from the canonical coupling Gram matrix
to the manuscript's output-side Gram matrix.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

noncomputable section

/-- The two square Gram matrices of a complex matrix have equal spectral
entropy. -/
theorem psdEntropy_conjTranspose_mul_self_eq_self_mul_conjTranspose
    {d : Type} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) :
    psdEntropy (A.conjTranspose * A)
        (Matrix.posSemidef_conjTranspose_mul_self A) =
      psdEntropy (A * A.conjTranspose)
        (Matrix.posSemidef_self_mul_conjTranspose A) := by
  let hleft : (A.conjTranspose * A).PosSemidef :=
    Matrix.posSemidef_conjTranspose_mul_self A
  let hright : (A * A.conjTranspose).PosSemidef :=
    Matrix.posSemidef_self_mul_conjTranspose A
  have heigen : hleft.isHermitian.eigenvalues =
      hright.isHermitian.eigenvalues := by
    exact (Matrix.IsHermitian.eigenvalues_eq_eigenvalues_iff
      hleft.isHermitian hright.isHermitian).2
        (Matrix.charpoly_mul_comm A.conjTranspose A)
  unfold psdEntropy
  rw [heigen]

/-- Exact conversion between unnormalized Gram entropy and the manuscript's
zero-weight-safe normalized Gram entropy. -/
theorem psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2
    {r c : Type} [Fintype r] [DecidableEq r]
    [Fintype c] [DecidableEq c]
    (A : Matrix r c ℂ) :
    psdEntropy (A * A.conjTranspose)
        (Matrix.posSemidef_self_mul_conjTranspose A) =
      normalizedGramEntropy (frobeniusSq A) A -
        QIT.xlog2 (frobeniusSq A) := by
  let X : Matrix r r ℂ := A * A.conjTranspose
  let hX : X.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  let w : ℝ := frobeniusSq A
  have hw : 0 ≤ w := frobeniusSq_nonneg A
  by_cases hw0 : w = 0
  · have htrace : X.trace = 0 := by
      apply Complex.ext
      · simpa [X, w, frobeniusSq] using hw0
      · simpa using (Matrix.PosSemidef.trace_nonneg hX).2.symm
    have hXzero : X = 0 :=
      (Matrix.PosSemidef.trace_eq_zero_iff hX).mp htrace
    have hEntropy : psdEntropy X hX = 0 := by
      calc
        _ = psdEntropy (0 : Matrix r r ℂ) Matrix.PosSemidef.zero :=
          psdEntropy_congr hXzero _ _
        _ = 0 := psdEntropy_zero
    change psdEntropy X hX = normalizedGramEntropy w A - QIT.xlog2 w
    rw [hEntropy]
    simp [normalizedGramEntropy, hw0, QIT.xlog2]
  · have hwpos : 0 < w := lt_of_le_of_ne hw (Ne.symm hw0)
    let lam : r → ℝ := hX.isHermitian.eigenvalues
    have hlam : ∀ i, 0 ≤ lam i := fun i => hX.eigenvalues_nonneg i
    have hlamsum : (∑ i, lam i) = w := by
      have htrace := congrArg Complex.re
        hX.isHermitian.trace_eq_sum_eigenvalues
      simpa [lam, X, w, frobeniusSq] using htrace.symm
    have hterm (i : r) :
        w * QIT.xlog2 (lam i / w) =
          QIT.xlog2 (lam i) - (lam i / w) * QIT.xlog2 w := by
      have hprod := xlog2_mul_of_nonneg hw
        (div_nonneg (hlam i) hw)
      have hcancel : w * (lam i / w) = lam i := by
        field_simp
      rw [hcancel] at hprod
      linarith
    change psdEntropy X hX = normalizedGramEntropy w A - QIT.xlog2 w
    unfold psdEntropy normalizedGramEntropy
    rw [if_neg hw0]
    change -(∑ i, QIT.xlog2 (lam i)) =
      -w * ∑ i, QIT.xlog2 (lam i / w) - QIT.xlog2 w
    have hsumterm :
        w * ∑ i, QIT.xlog2 (lam i / w) =
          (∑ i, QIT.xlog2 (lam i)) - QIT.xlog2 w := by
      rw [Finset.mul_sum]
      simp_rw [hterm]
      rw [Finset.sum_sub_distrib]
      have hratio : (∑ i, lam i / w) = 1 := by
        rw [← Finset.sum_div, hlamsum, div_self hw0]
      rw [← Finset.sum_mul, hratio, one_mul]
    linarith

end

end AmplitudeDamping
