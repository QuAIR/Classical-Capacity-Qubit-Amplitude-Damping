import AmplitudeDamping.Triangular.PolarGauge

/-!
# The square triangular inequality from unitary polar factors

This module packages the analytic entropy bound for square blocks.  The only
remaining algebraic input is the existence of unitary polar factors for the
two lower-row blocks.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

noncomputable section

/-- The block diagonal gauge `1 ⊕ W` is unitary. -/
def lowerBlockUnitary
    {d : Type} [Fintype d] [DecidableEq d]
    (W : Matrix.unitaryGroup d ℂ) : Matrix.unitaryGroup (Sum d d) ℂ :=
  ⟨Matrix.fromBlocks 1 0 0 (W : Matrix d d ℂ), by
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_one, Matrix.conjTranspose_zero,
      Matrix.fromBlocks_multiply, Matrix.mul_one,
      Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
    have hWW : (W : Matrix d d ℂ) *
        (W : Matrix d d ℂ).conjTranspose = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using
        Matrix.mem_unitaryGroup_iff.mp W.2
    rw [hWW]
    simp⟩

/-- For a square matrix, the trace of its input Gram matrix is its squared
Frobenius norm. -/
theorem trace_conjTranspose_mul_self_re_eq_frobeniusSq
    {d : Type} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) :
    (Matrix.trace (A.conjTranspose * A)).re = frobeniusSq A := by
  rw [frobeniusSq, Matrix.trace_mul_comm]

/-- The square triangular entropy inequality, conditional only on supplied
unitary polar factors for `B` and `D`. -/
theorem square_triangular_entropy_lower_bound_of_polar
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (A B D : Matrix d d ℂ) (UB UD : Matrix.unitaryGroup d ℂ)
    (hB : B = (UB : Matrix d d ℂ) * QIT.psdSqrt (B.conjTranspose * B))
    (hD : D = (UD : Matrix d d ℂ) * QIT.psdSqrt (D.conjTranspose * D))
    (hsum : frobeniusSq A + frobeniusSq B + frobeniusSq D = 1) :
    let T : Matrix (Sum d d) (Sum d d) ℂ := Matrix.fromBlocks A 0 B D
    psdEntropy (T * T.conjTranspose)
        (Matrix.posSemidef_self_mul_conjTranspose T) ≥
      entanglementCurve (2 * Real.sqrt (frobeniusSq A * frobeniusSq D)) +
        normalizedGramEntropy (frobeniusSq A) A +
        normalizedGramEntropy (frobeniusSq B) B +
        normalizedGramEntropy (frobeniusSq D) D := by
  dsimp only
  let P : Matrix d d ℂ := A.conjTranspose * A
  let Q : Matrix d d ℂ := B.conjTranspose * B
  let S : Matrix d d ℂ := D.conjTranspose * D
  let W : Matrix.unitaryGroup d ℂ := star UB * UD
  let R : Matrix d d ℂ :=
    (W : Matrix d d ℂ) * S * (W : Matrix d d ℂ).conjTranspose
  let T : Matrix (Sum d d) (Sum d d) ℂ := Matrix.fromBlocks A 0 B D
  let G : Matrix.unitaryGroup (Sum d d) ℂ := lowerBlockUnitary W
  have hP : P.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have hQ : Q.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  have hS : S.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self D
  have hR : R.PosSemidef :=
    hS.mul_mul_conjTranspose_same (W : Matrix d d ℂ)
  have hGauge :
      (G : Matrix (Sum d d) (Sum d d) ℂ) *
          (T.conjTranspose * T) *
            (G : Matrix (Sum d d) (Sum d d) ℂ).conjTranspose =
        entropyCoupling P Q R := by
    exact triangular_polarGauge_identity A B D UB UD hB hD
  have htraceP : P.trace.re = frobeniusSq A :=
    trace_conjTranspose_mul_self_re_eq_frobeniusSq A
  have htraceQ : Q.trace.re = frobeniusSq B :=
    trace_conjTranspose_mul_self_re_eq_frobeniusSq B
  have htraceS : S.trace.re = frobeniusSq D :=
    trace_conjTranspose_mul_self_re_eq_frobeniusSq D
  have htraceR : R.trace.re = frobeniusSq D := by
    calc
      R.trace.re = S.trace.re := by
        dsimp [R]
        have hW : (W : Matrix d d ℂ).conjTranspose *
            (W : Matrix d d ℂ) = 1 := by
          simpa [Matrix.star_eq_conjTranspose] using
            Unitary.coe_star_mul_self W
        rw [Matrix.trace_mul_cycle, hW, Matrix.one_mul]
      _ = frobeniusSq D := htraceS
  have hcoupling := entropyCoupling_entropy_lower_bound_normalized
    P Q R hP hQ hR (by simpa [htraceP, htraceQ, htraceR] using hsum)
  have hTgram :
      psdEntropy (T.conjTranspose * T)
          (Matrix.posSemidef_conjTranspose_mul_self T) =
        psdEntropy (T * T.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose T) :=
    psdEntropy_conjTranspose_mul_self_eq_self_mul_conjTranspose T
  have hcouplingEq :
      psdEntropy (entropyCoupling P Q R)
          (entropyCoupling_posSemidef P Q R hP hQ hR) =
        psdEntropy (T.conjTranspose * T)
          (Matrix.posSemidef_conjTranspose_mul_self T) := by
    calc
      _ = psdEntropy
          ((G : Matrix (Sum d d) (Sum d d) ℂ) *
            (T.conjTranspose * T) *
              (G : Matrix (Sum d d) (Sum d d) ℂ).conjTranspose)
          ((Matrix.posSemidef_conjTranspose_mul_self T).mul_mul_conjTranspose_same
            (G : Matrix (Sum d d) (Sum d d) ℂ)) :=
        psdEntropy_congr hGauge.symm _ _
      _ = _ := psdEntropy_unitary_conj G _ _
  have hPentropy :
      psdEntropy P hP =
        normalizedGramEntropy (frobeniusSq A) A -
          QIT.xlog2 (frobeniusSq A) := by
    calc
      _ = psdEntropy (A * A.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose A) :=
        psdEntropy_conjTranspose_mul_self_eq_self_mul_conjTranspose A
      _ = _ := psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2 A
  have hQentropy :
      psdEntropy Q hQ =
        normalizedGramEntropy (frobeniusSq B) B -
          QIT.xlog2 (frobeniusSq B) := by
    calc
      _ = psdEntropy (B * B.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose B) :=
        psdEntropy_conjTranspose_mul_self_eq_self_mul_conjTranspose B
      _ = _ := psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2 B
  have hRentropy :
      psdEntropy R hR =
        normalizedGramEntropy (frobeniusSq D) D -
          QIT.xlog2 (frobeniusSq D) := by
    calc
      _ = psdEntropy S hS := psdEntropy_unitary_conj W S hS
      _ = psdEntropy (D * D.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose D) :=
        psdEntropy_conjTranspose_mul_self_eq_self_mul_conjTranspose D
      _ = _ := psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2 D
  rw [htraceP, htraceQ, htraceR, hPentropy, hQentropy, hRentropy] at hcoupling
  rw [hcouplingEq, hTgram] at hcoupling
  linarith

end

end AmplitudeDamping
