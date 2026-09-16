import QIT.Information.Entropy.EntropyTensorPower
import QIT.Util.BlockMatrix

/-!
# The triangular block entropy inequality: formal statement layer

The manuscript's main analytic theorem concerns an arbitrary rectangular
lower-triangular block coefficient matrix.  This module records the normalized
positive-operator formulation that the subsequent proof modules will target.

No axiom or `sorry` is introduced here: `TriangularBlockEntropyInequality` is a
predicate naming the theorem still to be proved.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

universe u₁ u₂ v₁ v₂

noncomputable section

/-- The squared Frobenius norm, written as a real trace. -/
def frobeniusSq {r : Type u₁} {c : Type v₁}
    [Fintype r] [DecidableEq r] [Fintype c] [DecidableEq c]
    (A : Matrix r c ℂ) : ℝ :=
  (Matrix.trace (A * A.conjTranspose)).re

theorem frobeniusSq_nonneg {r : Type u₁} {c : Type v₁}
    [Fintype r] [DecidableEq r] [Fintype c] [DecidableEq c]
    (A : Matrix r c ℂ) : 0 ≤ frobeniusSq A := by
  exact (Matrix.PosSemidef.trace_nonneg
    (Matrix.posSemidef_self_mul_conjTranspose A)).1

theorem frobeniusSq_eq_sum_normSq {r : Type u₁} {c : Type v₁}
    [Fintype r] [DecidableEq r] [Fintype c] [DecidableEq c]
    (A : Matrix r c ℂ) :
    frobeniusSq A = ∑ i, ∑ j, Complex.normSq (A i j) := by
  unfold frobeniusSq
  simp [Matrix.trace, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Complex.mul_conj]

/-- Squared Frobenius norm of a lower-triangular block matrix is the sum of
the squared Frobenius norms of its three nonzero blocks. -/
theorem frobeniusSq_fromBlocks_lower
    {r₁ : Type u₁} {r₂ : Type u₂} {c₁ : Type v₁} {c₂ : Type v₂}
    [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype c₂] [DecidableEq c₂]
    (A : Matrix r₁ c₁ ℂ) (B : Matrix r₂ c₁ ℂ) (D : Matrix r₂ c₂ ℂ) :
    frobeniusSq (Matrix.fromBlocks A 0 B D) =
      frobeniusSq A + frobeniusSq B + frobeniusSq D := by
  simp only [frobeniusSq_eq_sum_normSq, Fintype.sum_sum_type]
  simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
    Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
    Finset.sum_add_distrib]
  ring

/-- Spectral entropy `-Tr X log₂ X` of a positive semidefinite matrix.

The positivity witness supplies the Hermitian eigenvalue API.  The definition
does not require `X` to have trace one. -/
def psdEntropy {r : Type u₁} [Fintype r] [DecidableEq r]
    (X : Matrix r r ℂ) (hX : X.PosSemidef) : ℝ :=
  -(∑ i, QIT.xlog2 (hX.isHermitian.eigenvalues i))

/-- On a density state, `psdEntropy` is exactly Lean-QIT's von Neumann
entropy. -/
theorem psdEntropy_state {r : Type u₁} [Fintype r] [DecidableEq r]
    (ρ : State r) : psdEntropy ρ.matrix ρ.pos = ρ.vonNeumann := rfl

/-- The manuscript's zero-weight convention for
`weight * S(A Aᴴ / weight)`, expressed directly through eigenvalues. -/
def normalizedGramEntropy {r : Type u₁} {c : Type v₁}
    [Fintype r] [DecidableEq r] [Fintype c] [DecidableEq c]
    (weight : ℝ) (A : Matrix r c ℂ) : ℝ :=
  if weight = 0 then 0
  else -weight * ∑ i,
    QIT.xlog2
      ((Matrix.posSemidef_self_mul_conjTranspose A).isHermitian.eigenvalues i /
        weight)

@[simp]
theorem normalizedGramEntropy_zero {r : Type u₁} {c : Type v₁}
    [Fintype r] [DecidableEq r] [Fintype c] [DecidableEq c]
    (A : Matrix r c ℂ) : normalizedGramEntropy 0 A = 0 := by
  simp [normalizedGramEntropy]

/-- Binary entropy, in bits. -/
def binaryEntropy (q : ℝ) : ℝ :=
  -QIT.xlog2 q - QIT.xlog2 (1 - q)

/-- The binary-spectrum entropy curve used in the triangular theorem. -/
def entanglementCurve (concurrence : ℝ) : ℝ :=
  binaryEntropy ((1 + Real.sqrt (1 - concurrence ^ 2)) / 2)

/-- Predicate expressing the triangular block entropy theorem exactly in the
coefficient-matrix language of the manuscript. -/
def TriangularBlockEntropyInequality : Prop :=
  ∀ {r₁ : Type u₁} {r₂ : Type u₂} {c₁ : Type v₁} {c₂ : Type v₂}
    [Fintype r₁] [DecidableEq r₁]
    [Fintype r₂] [DecidableEq r₂]
    [Fintype c₁] [DecidableEq c₁]
    [Fintype c₂] [DecidableEq c₂]
    (A : Matrix r₁ c₁ ℂ) (B : Matrix r₂ c₁ ℂ) (D : Matrix r₂ c₂ ℂ),
    let T : Matrix (Sum r₁ r₂) (Sum c₁ c₂) ℂ :=
      Matrix.fromBlocks A 0 B D
    let α := frobeniusSq A
    let β := frobeniusSq B
    let γ := frobeniusSq D
    α + β + γ = 1 →
      psdEntropy (T * T.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose T) ≥
        entanglementCurve (2 * Real.sqrt (α * γ)) +
          normalizedGramEntropy α A +
          normalizedGramEntropy β B +
          normalizedGramEntropy γ D

end

end AmplitudeDamping
