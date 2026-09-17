import AmplitudeDamping.Triangular.UnitaryPolar
import QIT.Information.Entropy.MutualInformationDPI

/-!
# Rectangular isometric embeddings

Spectral entropy is unchanged when a positive matrix is conjugated by a
rectangular isometry.  We also provide the coordinate inclusion matrix used
for zero padding arbitrary finite index types into a common ambient type.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

universe u v w

noncomputable section

/-- Spectral entropy is invariant under rectangular isometry conjugation. -/
theorem psdEntropy_isometry_conj
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (X : Matrix a a ℂ) (hX : X.PosSemidef) (V : Matrix b a ℂ)
    (hV : V.conjTranspose * V = (1 : Matrix a a ℂ)) :
    psdEntropy (V * X * V.conjTranspose)
        (hX.mul_mul_conjTranspose_same V) = psdEntropy X hX := by
  rw [psdEntropy_eq_neg_sum_eigenvalueMultiset,
    psdEntropy_eq_neg_sum_eigenvalueMultiset]
  congr 1
  have hpoly := Matrix.charpoly_isometry_conj (V := V) X hV
  have hP : (V * X * V.conjTranspose).charpoly ≠ 0 :=
    (Matrix.charpoly_monic _).ne_zero
  have hQ : X.charpoly ≠ 0 := (Matrix.charpoly_monic _).ne_zero
  have hroot := Matrix.roots_re_xlog2_sum_eq_of_X_pow_mul_eq
    hP hQ hpoly
  have hrootsVX :=
    (hX.mul_mul_conjTranspose_same V).isHermitian.roots_charpoly_eq_eigenvalues
  have hrootsX := hX.isHermitian.roots_charpoly_eq_eigenvalues
  rw [hrootsVX, hrootsX] at hroot
  simpa [eigenvalueMultiset, Multiset.map_map, Function.comp_def] using hroot

/-- Coordinate isometry associated to an embedding of finite index types. -/
def coordinateIsometry
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (f : a ↪ b) : Matrix b a ℂ :=
  fun i j => if i = f j then 1 else 0

theorem coordinateIsometry_apply
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (f : a ↪ b) (i : b) (j : a) :
    coordinateIsometry f i j = if i = f j then 1 else 0 := rfl

/-- A coordinate inclusion has orthonormal columns. -/
theorem coordinateIsometry_isometry
    {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (f : a ↪ b) :
    (coordinateIsometry f).conjTranspose * coordinateIsometry f =
      (1 : Matrix a a ℂ) := by
  classical
  ext i j
  simp [coordinateIsometry, Matrix.mul_apply, Matrix.one_apply]
  by_cases hij : i = j
  · subst j
    simp
  · simp [hij, Ne.symm hij]

/-- Zero-pad a rectangular matrix along coordinate embeddings. -/
def embedMatrix
    {r : Type u} {c : Type v} {d : Type w} [Fintype r] [DecidableEq r]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (fr : r ↪ d) (fc : c ↪ d) (A : Matrix r c ℂ) : Matrix d d ℂ :=
  coordinateIsometry fr * A * (coordinateIsometry fc).conjTranspose

/-- Zero padding preserves the squared Frobenius norm. -/
theorem frobeniusSq_embedMatrix
    {r : Type u} {c : Type v} {d : Type w} [Fintype r] [DecidableEq r]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (fr : r ↪ d) (fc : c ↪ d) (A : Matrix r c ℂ) :
    frobeniusSq (embedMatrix fr fc A) = frobeniusSq A := by
  let Vr := coordinateIsometry fr
  let Vc := coordinateIsometry fc
  have hr : Vr.conjTranspose * Vr = (1 : Matrix r r ℂ) :=
    coordinateIsometry_isometry fr
  have hc : Vc.conjTranspose * Vc = (1 : Matrix c c ℂ) :=
    coordinateIsometry_isometry fc
  unfold frobeniusSq embedMatrix
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]
  change (Matrix.trace ((Vr * A * Vc.conjTranspose) *
    (Vc * (A.conjTranspose * Vr.conjTranspose)))).re = _
  rw [show (Vr * A * Vc.conjTranspose) * (Vc * (A.conjTranspose * Vr.conjTranspose)) =
      Vr * (A * A.conjTranspose) * Vr.conjTranspose by
    rw [show (Vr * A * Vc.conjTranspose) * (Vc * (A.conjTranspose * Vr.conjTranspose)) =
      Vr * A * (Vc.conjTranspose * Vc) * A.conjTranspose * Vr.conjTranspose by
        simp only [Matrix.mul_assoc]]
    rw [hc]
    simp only [Matrix.mul_assoc, Matrix.mul_one]]
  rw [Matrix.trace_mul_cycle, hr, Matrix.one_mul]

/-- Zero padding preserves normalized Gram entropy. -/
theorem normalizedGramEntropy_embedMatrix
    {r : Type u} {c : Type v} {d : Type w} [Fintype r] [DecidableEq r]
    [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    (fr : r ↪ d) (fc : c ↪ d) (A : Matrix r c ℂ) :
    normalizedGramEntropy (frobeniusSq (embedMatrix fr fc A))
        (embedMatrix fr fc A) =
      normalizedGramEntropy (frobeniusSq A) A := by
  let Vr := coordinateIsometry fr
  let Vc := coordinateIsometry fc
  have hr : Vr.conjTranspose * Vr = (1 : Matrix r r ℂ) :=
    coordinateIsometry_isometry fr
  have hc : Vc.conjTranspose * Vc = (1 : Matrix c c ℂ) :=
    coordinateIsometry_isometry fc
  have hgram : embedMatrix fr fc A * (embedMatrix fr fc A).conjTranspose =
      Vr * (A * A.conjTranspose) * Vr.conjTranspose := by
    unfold embedMatrix
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    change (Vr * A * Vc.conjTranspose) *
      (Vc * (A.conjTranspose * Vr.conjTranspose)) = _
    rw [show (Vr * A * Vc.conjTranspose) *
        (Vc * (A.conjTranspose * Vr.conjTranspose)) =
      Vr * A * (Vc.conjTranspose * Vc) * A.conjTranspose * Vr.conjTranspose by
        simp only [Matrix.mul_assoc]]
    rw [hc]
    simp only [Matrix.mul_assoc, Matrix.mul_one]
  have hent :
      psdEntropy (embedMatrix fr fc A * (embedMatrix fr fc A).conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose (embedMatrix fr fc A)) =
        psdEntropy (A * A.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose A) := by
    calc
      _ = psdEntropy (Vr * (A * A.conjTranspose) * Vr.conjTranspose)
          ((Matrix.posSemidef_self_mul_conjTranspose A).mul_mul_conjTranspose_same Vr) :=
        psdEntropy_congr hgram _ _
      _ = _ := psdEntropy_isometry_conj _ _ Vr hr
  have hleft := psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2
    (embedMatrix fr fc A)
  have hright := psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2 A
  have hnorm := frobeniusSq_embedMatrix fr fc A
  calc
    normalizedGramEntropy (frobeniusSq (embedMatrix fr fc A))
        (embedMatrix fr fc A) =
      psdEntropy (embedMatrix fr fc A * (embedMatrix fr fc A).conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose (embedMatrix fr fc A)) +
        QIT.xlog2 (frobeniusSq (embedMatrix fr fc A)) := by linarith
    _ = psdEntropy (A * A.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose A) +
        QIT.xlog2 (frobeniusSq A) := by rw [hent, hnorm]
    _ = normalizedGramEntropy (frobeniusSq A) A := by linarith

end

end AmplitudeDamping
