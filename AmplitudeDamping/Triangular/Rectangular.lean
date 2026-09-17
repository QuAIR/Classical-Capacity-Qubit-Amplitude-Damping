import AmplitudeDamping.Triangular.IsometricEmbedding

/-!
# The rectangular triangular block entropy inequality

All four row/column index types are embedded into one common nonempty finite
type.  The square theorem then applies to the zero-padded blocks, while the
isometry lemmas remove the padding from every entropy term.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

universe u₁ u₂ v₁ v₂

noncomputable section

/-- The proposition in `Statement.lean` is a theorem. -/
theorem triangularBlockEntropyInequality : TriangularBlockEntropyInequality := by
  intro r₁ r₂ c₁ c₂ _ _ _ _ _ _ _ _ A B D
  dsimp only
  intro hsum
  let n := 1 + Fintype.card r₁ + Fintype.card r₂ +
    Fintype.card c₁ + Fintype.card c₂
  let d := Fin n
  have hr₁n : Fintype.card r₁ ≤ n := by dsimp [n]; omega
  have hr₂n : Fintype.card r₂ ≤ n := by dsimp [n]; omega
  have hc₁n : Fintype.card c₁ ≤ n := by dsimp [n]; omega
  have hc₂n : Fintype.card c₂ ≤ n := by dsimp [n]; omega
  let er₁ : r₁ ↪ d :=
    ⟨fun i => Fin.castLE hr₁n (Fintype.equivFin r₁ i), by
      intro x y h
      exact (Fintype.equivFin r₁).injective (Fin.castLE_injective hr₁n h)⟩
  let er₂ : r₂ ↪ d :=
    ⟨fun i => Fin.castLE hr₂n (Fintype.equivFin r₂ i), by
      intro x y h
      exact (Fintype.equivFin r₂).injective (Fin.castLE_injective hr₂n h)⟩
  let ec₁ : c₁ ↪ d :=
    ⟨fun i => Fin.castLE hc₁n (Fintype.equivFin c₁ i), by
      intro x y h
      exact (Fintype.equivFin c₁).injective (Fin.castLE_injective hc₁n h)⟩
  let ec₂ : c₂ ↪ d :=
    ⟨fun i => Fin.castLE hc₂n (Fintype.equivFin c₂ i), by
      intro x y h
      exact (Fintype.equivFin c₂).injective (Fin.castLE_injective hc₂n h)⟩
  let Vr₁ : Matrix d r₁ ℂ := coordinateIsometry er₁
  let Vr₂ : Matrix d r₂ ℂ := coordinateIsometry er₂
  let Vc₁ : Matrix d c₁ ℂ := coordinateIsometry ec₁
  let Vc₂ : Matrix d c₂ ℂ := coordinateIsometry ec₂
  let A' : Matrix d d ℂ := embedMatrix er₁ ec₁ A
  let B' : Matrix d d ℂ := embedMatrix er₂ ec₁ B
  let D' : Matrix d d ℂ := embedMatrix er₂ ec₂ D
  let T : Matrix (Sum r₁ r₂) (Sum c₁ c₂) ℂ :=
    Matrix.fromBlocks A 0 B D
  let T' : Matrix (Sum d d) (Sum d d) ℂ :=
    Matrix.fromBlocks A' 0 B' D'
  let Vr : Matrix (Sum d d) (Sum r₁ r₂) ℂ :=
    Matrix.fromBlocks Vr₁ 0 0 Vr₂
  let Vc : Matrix (Sum d d) (Sum c₁ c₂) ℂ :=
    Matrix.fromBlocks Vc₁ 0 0 Vc₂
  have hr₁ : Vr₁.conjTranspose * Vr₁ = (1 : Matrix r₁ r₁ ℂ) :=
    coordinateIsometry_isometry er₁
  have hr₂ : Vr₂.conjTranspose * Vr₂ = (1 : Matrix r₂ r₂ ℂ) :=
    coordinateIsometry_isometry er₂
  have hc₁ : Vc₁.conjTranspose * Vc₁ = (1 : Matrix c₁ c₁ ℂ) :=
    coordinateIsometry_isometry ec₁
  have hc₂ : Vc₂.conjTranspose * Vc₂ = (1 : Matrix c₂ c₂ ℂ) :=
    coordinateIsometry_isometry ec₂
  have hr : Vr.conjTranspose * Vr =
      (1 : Matrix (Sum r₁ r₂) (Sum r₁ r₂) ℂ) := by
    dsimp [Vr]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, hr₁, hr₂, Matrix.fromBlocks_one]
  have hc : Vc.conjTranspose * Vc =
      (1 : Matrix (Sum c₁ c₂) (Sum c₁ c₂) ℂ) := by
    dsimp [Vc]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add, hc₁, hc₂, Matrix.fromBlocks_one]
  have hT' : T' = Vr * T * Vc.conjTranspose := by
    dsimp [T', T, Vr, Vc, Vr₁, Vr₂, Vc₁, Vc₂,
      A', B', D', embedMatrix]
    rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
      Matrix.fromBlocks_multiply]
    simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
      add_zero, zero_add]
  have hgram : T' * T'.conjTranspose =
      Vr * (T * T.conjTranspose) * Vr.conjTranspose := by
    rw [hT', Matrix.conjTranspose_mul, Matrix.conjTranspose_mul,
      Matrix.conjTranspose_conjTranspose]
    rw [show (Vr * T * Vc.conjTranspose) *
        (Vc * (T.conjTranspose * Vr.conjTranspose)) =
      Vr * T * (Vc.conjTranspose * Vc) * T.conjTranspose * Vr.conjTranspose by
        simp only [Matrix.mul_assoc]]
    rw [hc]
    simp only [Matrix.mul_assoc, Matrix.mul_one]
  have houtput :
      psdEntropy (T' * T'.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose T') =
        psdEntropy (T * T.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose T) := by
    calc
      _ = psdEntropy (Vr * (T * T.conjTranspose) * Vr.conjTranspose)
          ((Matrix.posSemidef_self_mul_conjTranspose T).mul_mul_conjTranspose_same Vr) :=
        psdEntropy_congr hgram _ _
      _ = _ := psdEntropy_isometry_conj _ _ Vr hr
  have hA := frobeniusSq_embedMatrix er₁ ec₁ A
  have hB := frobeniusSq_embedMatrix er₂ ec₁ B
  have hD := frobeniusSq_embedMatrix er₂ ec₂ D
  have hsq := square_triangular_entropy_lower_bound A' B' D' (by
    simpa [A', B', D', hA, hB, hD] using hsum)
  have hnA := normalizedGramEntropy_embedMatrix er₁ ec₁ A
  have hnB := normalizedGramEntropy_embedMatrix er₂ ec₁ B
  have hnD := normalizedGramEntropy_embedMatrix er₂ ec₂ D
  rw [hA] at hnA
  rw [hB] at hnB
  rw [hD] at hnD
  dsimp only at hsq
  change psdEntropy (T * T.conjTranspose)
      (Matrix.posSemidef_self_mul_conjTranspose T) ≥ _
  rw [← houtput]
  simpa [T', A', B', D', hA, hB, hD, hnA, hnB, hnD] using hsq

end

end AmplitudeDamping
