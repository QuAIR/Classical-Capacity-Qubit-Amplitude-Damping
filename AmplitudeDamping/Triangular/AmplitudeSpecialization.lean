import AmplitudeDamping.Triangular.Rectangular
import AmplitudeDamping.FixedExcitation

/-!
# Amplitude-damping specialization of the triangular inequality
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

universe u v

noncomputable section

/-- Scaling a coefficient matrix by the square root of a nonnegative scalar
scales its squared Frobenius norm by that scalar. -/
theorem frobeniusSq_sqrt_smul
    {r : Type u} {c : Type v} [Fintype r] [DecidableEq r]
    [Fintype c] [DecidableEq c]
    (t : ℝ) (ht : 0 ≤ t) (A : Matrix r c ℂ) :
    frobeniusSq ((Real.sqrt t : ℂ) • A) = t * frobeniusSq A := by
  unfold frobeniusSq
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  have hs : (Real.sqrt t : ℂ) * star (Real.sqrt t : ℂ) = (t : ℂ) := by
    calc
      _ = ((Real.sqrt t * Real.sqrt t : ℝ) : ℂ) := by simp
      _ = (t : ℂ) := congrArg (fun x : ℝ => (x : ℂ))
        (by simpa [pow_two] using Real.sq_sqrt ht)
  rw [hs]
  simp [Matrix.trace_smul]

theorem gram_sqrt_smul
    {r : Type u} {c : Type v} [Fintype r] [DecidableEq r]
    [Fintype c] [DecidableEq c]
    (t : ℝ) (ht : 0 ≤ t) (A : Matrix r c ℂ) :
    ((Real.sqrt t : ℂ) • A) *
        ((Real.sqrt t : ℂ) • A).conjTranspose =
      (t : ℂ) • (A * A.conjTranspose) := by
  rw [Matrix.conjTranspose_smul, Matrix.smul_mul, Matrix.mul_smul,
    smul_smul]
  have hs : (Real.sqrt t : ℂ) * star (Real.sqrt t : ℂ) = (t : ℂ) := by
    calc
      _ = ((Real.sqrt t * Real.sqrt t : ℝ) : ℂ) := by simp
      _ = (t : ℂ) := congrArg (fun x : ℝ => (x : ℂ))
        (by simpa [pow_two] using Real.sq_sqrt ht)
  rw [hs]

/-- The manuscript's normalized Gram entropy is homogeneous under square-root
scaling, including at zero weight. -/
theorem normalizedGramEntropy_sqrt_smul
    {r : Type u} {c : Type v} [Fintype r] [DecidableEq r]
    [Fintype c] [DecidableEq c]
    (t : ℝ) (ht : 0 ≤ t) (A : Matrix r c ℂ) :
    normalizedGramEntropy
        (frobeniusSq ((Real.sqrt t : ℂ) • A))
        ((Real.sqrt t : ℂ) • A) =
      t * normalizedGramEntropy (frobeniusSq A) A := by
  let X := A * A.conjTranspose
  let hX : X.PosSemidef := Matrix.posSemidef_self_mul_conjTranspose A
  have hgram := gram_sqrt_smul t ht A
  have hnorm := frobeniusSq_sqrt_smul t ht A
  have hscaled :
      psdEntropy
          (((Real.sqrt t : ℂ) • A) *
            ((Real.sqrt t : ℂ) • A).conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose
            ((Real.sqrt t : ℂ) • A)) =
        t * psdEntropy X hX - QIT.xlog2 t * frobeniusSq A := by
    calc
      _ = psdEntropy ((t : ℂ) • X)
          (hX.smul (by exact_mod_cast ht)) := psdEntropy_congr hgram _ _
      _ = t * psdEntropy X hX - QIT.xlog2 t * X.trace.re :=
        psdEntropy_real_smul t ht X hX
      _ = _ := by rfl
  have hleft := psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2
    ((Real.sqrt t : ℂ) • A)
  have hbase := psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2 A
  have hxlog := xlog2_mul_of_nonneg ht (frobeniusSq_nonneg A)
  rw [hnorm] at hleft ⊢
  calc
    normalizedGramEntropy (t * frobeniusSq A)
        ((Real.sqrt t : ℂ) • A) =
      psdEntropy
          (((Real.sqrt t : ℂ) • A) *
            ((Real.sqrt t : ℂ) • A).conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose
            ((Real.sqrt t : ℂ) • A)) +
        QIT.xlog2 (t * frobeniusSq A) := by linarith
    _ = t * psdEntropy X hX - QIT.xlog2 t * frobeniusSq A +
        (frobeniusSq A * QIT.xlog2 t +
          t * QIT.xlog2 (frobeniusSq A)) := by rw [hscaled, hxlog]
    _ = t * (psdEntropy X hX + QIT.xlog2 (frobeniusSq A)) := by ring
    _ = t * normalizedGramEntropy (frobeniusSq A) A := by
      congr 1
      linarith

/-- Sharp triangular entropy bound in the exact block form produced by an
amplitude-damping Stinespring isometry. -/
theorem amplitudeDamping_triangular_entropy_lower_bound
    {r : Type u} {c : Type v} [Fintype r] [DecidableEq r]
    [Fintype c] [DecidableEq c]
    (p q : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (A B : Matrix r c ℂ)
    (hA : frobeniusSq A = q) (hB : frobeniusSq B = 1 - q) :
    let M : Matrix (Sum r r) (Sum c c) ℂ :=
      Matrix.fromBlocks ((Real.sqrt (1 - p) : ℂ) • A) 0 B
        ((Real.sqrt p : ℂ) • A)
    psdEntropy (M * M.conjTranspose)
        (Matrix.posSemidef_self_mul_conjTranspose M) ≥
      dampingEntropyCurve p q +
        normalizedGramEntropy q A +
        normalizedGramEntropy (1 - q) B := by
  dsimp only
  have h1p : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  let A₀ := (Real.sqrt (1 - p) : ℂ) • A
  let D₀ := (Real.sqrt p : ℂ) • A
  have hA₀ : frobeniusSq A₀ = (1 - p) * q := by
    rw [show frobeniusSq A₀ = (1 - p) * frobeniusSq A by
      exact frobeniusSq_sqrt_smul (1 - p) h1p A, hA]
  have hD₀ : frobeniusSq D₀ = p * q := by
    rw [show frobeniusSq D₀ = p * frobeniusSq A by
      exact frobeniusSq_sqrt_smul p hp0 A, hA]
  have hsum : frobeniusSq A₀ + frobeniusSq B + frobeniusSq D₀ = 1 := by
    rw [hA₀, hB, hD₀]
    ring
  have htri := triangularBlockEntropyInequality A₀ B D₀ hsum
  have hnA := normalizedGramEntropy_sqrt_smul (1 - p) h1p A
  have hnD := normalizedGramEntropy_sqrt_smul p hp0 A
  rw [hA₀] at hnA
  rw [hD₀] at hnD
  change normalizedGramEntropy ((1 - p) * q) A₀ =
    (1 - p) * normalizedGramEntropy (frobeniusSq A) A at hnA
  change normalizedGramEntropy (p * q) D₀ =
    p * normalizedGramEntropy (frobeniusSq A) A at hnD
  have hcurve :
      entanglementCurve (2 * Real.sqrt (((1 - p) * q) * (p * q))) =
        dampingEntropyCurve p q := by
    unfold dampingEntropyCurve
    have hq0 : 0 ≤ q := hA ▸ frobeniusSq_nonneg A
    rw [show (1 - p) * q * (p * q) = (p * (1 - p)) * q ^ 2 by ring,
      Real.sqrt_mul (mul_nonneg hp0 h1p), Real.sqrt_sq hq0]
    ring_nf
  rw [hA₀, hD₀, hcurve, hnA, hnD, hB, hA] at htri
  dsimp [A₀, D₀] at htri ⊢
  linarith

end

end AmplitudeDamping
