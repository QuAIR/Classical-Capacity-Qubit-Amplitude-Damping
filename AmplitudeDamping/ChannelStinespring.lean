import AmplitudeDamping.Triangular.AmplitudeSpecialization
import QIT.Channels.Diamond

/-!
# A chosen Stinespring isometry for finite-dimensional channels
-/

open scoped ComplexConjugate ComplexOrder MatrixOrder

namespace QIT

universe u v

noncomputable section

namespace Channel

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The chosen Kraus family of a channel satisfies the completeness relation. -/
theorem krausAdjoint_one (Phi : Channel a b) :
    MatrixMap.krausAdjoint Phi.kraus (1 : CMatrix b) = 1 := by
  apply MatrixMap.krausAdjoint_one_of_tracePreserving
  simpa [Phi.map_eq_ofKraus] using Phi.tracePreserving

/-- A canonical finite Stinespring isometry obtained from the channel's
chosen Kraus representation.  Its environment is indexed by `a x b`. -/
def stinespringIsometry (Phi : Channel a b) :
    ReferenceIsometry a (Prod b (Prod a b)) where
  matrix := MatrixMap.krausStinespringMatrix Phi.kraus
  isometry := MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
    Phi.kraus Phi.krausAdjoint_one

@[simp]
theorem stinespringIsometry_matrix (Phi : Channel a b) :
    Phi.stinespringIsometry.matrix =
      MatrixMap.krausStinespringMatrix Phi.kraus := rfl

@[simp]
theorem stinespringIsometry_matrix_apply (Phi : Channel a b)
    (y : b) (k : Prod a b) (x : a) :
    Phi.stinespringIsometry.matrix (y, k) x = Phi.kraus k y x := rfl

/-- Coefficient matrix of the Stinespring image of an arbitrary (possibly
unnormalized) input amplitude. -/
def stinespringCoefficientMatrix (Phi : Channel a b) (v : a → ℂ) :
    Matrix b (Prod a b) ℂ :=
  fun y k => ∑ x, Phi.kraus k y x * v x

/-- The output Gram matrix of the Stinespring coefficient matrix is exactly
the channel applied to the input rank-one operator. -/
theorem stinespringCoefficientMatrix_gram (Phi : Channel a b) (v : a → ℂ) :
    Phi.stinespringCoefficientMatrix v *
        (Phi.stinespringCoefficientMatrix v).conjTranspose =
      Phi.map (rankOneMatrix v) := by
  rw [Phi.map_eq_ofKraus]
  change Phi.stinespringCoefficientMatrix v *
      (Phi.stinespringCoefficientMatrix v).conjTranspose =
    ∑ k, Phi.kraus k * rankOneMatrix v * (Phi.kraus k).conjTranspose
  ext y z
  simp only [stinespringCoefficientMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Matrix.sum_apply,
    rankOneMatrix_apply]
  apply Finset.sum_congr rfl
  intro k _
  change (∑ x, Phi.kraus k y x * v x) *
      (starRingEnd ℂ) (∑ x, Phi.kraus k z x * v x) = _
  rw [map_sum (starRingEnd ℂ)]
  simp only [map_mul, Finset.sum_mul, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  simp only [starRingEnd_apply]
  ring

/-- Trace preservation makes the squared Frobenius norm of the Stinespring
coefficient matrix equal to the squared norm of its input amplitude. -/
theorem frobeniusSq_stinespringCoefficientMatrix
    (Phi : Channel a b) (v : a → ℂ) :
    AmplitudeDamping.frobeniusSq (Phi.stinespringCoefficientMatrix v) =
      ∑ x, Complex.normSq (v x) := by
  unfold AmplitudeDamping.frobeniusSq
  rw [Phi.stinespringCoefficientMatrix_gram, Phi.tracePreserving,
    rankOneMatrix_trace]
  simp [dotProduct, Complex.mul_conj]

/-- For a normalized pure input, the normalized Gram entropy of its
Stinespring coefficient matrix is exactly the channel output entropy. -/
theorem normalizedGramEntropy_stinespringCoefficientMatrix
    (Phi : Channel a b) (psi : PureVector a) :
    AmplitudeDamping.normalizedGramEntropy
        (AmplitudeDamping.frobeniusSq
          (Phi.stinespringCoefficientMatrix psi.amp))
        (Phi.stinespringCoefficientMatrix psi.amp) =
      (Phi.applyState psi.state).vonNeumann := by
  let A := Phi.stinespringCoefficientMatrix psi.amp
  have hamp : (∑ x, Complex.normSq (psi.amp x)) = 1 := by
    have h := congrArg Complex.re psi.trace_rankOne_eq_one
    simpa [rankOneMatrix_trace, dotProduct, Complex.mul_conj] using h
  have hnorm : AmplitudeDamping.frobeniusSq A = 1 := by
    rw [show AmplitudeDamping.frobeniusSq A =
        ∑ x, Complex.normSq (psi.amp x) by
      exact Phi.frobeniusSq_stinespringCoefficientMatrix psi.amp]
    exact hamp
  have hconvert :=
    AmplitudeDamping.psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2 A
  rw [hnorm] at hconvert ⊢
  have hxlogOne : QIT.xlog2 1 = 0 := by
    norm_num [QIT.xlog2, QIT.log2]
  rw [hxlogOne, sub_zero] at hconvert
  have hgram : A * A.conjTranspose =
      (Phi.applyState psi.state).matrix := by
    exact Phi.stinespringCoefficientMatrix_gram psi.amp
  calc
    AmplitudeDamping.normalizedGramEntropy 1 A =
        AmplitudeDamping.psdEntropy (A * A.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose A) := by
      exact hconvert.symm
    _ = AmplitudeDamping.psdEntropy (Phi.applyState psi.state).matrix
          (Phi.applyState psi.state).pos :=
      AmplitudeDamping.psdEntropy_congr hgram _ _
    _ = (Phi.applyState psi.state).vonNeumann :=
      AmplitudeDamping.psdEntropy_state (Phi.applyState psi.state)

/-- For a nonzero, not necessarily normalized amplitude, normalized Gram
entropy is its squared norm times the output entropy of the normalized pure
state. -/
theorem normalizedGramEntropy_stinespringCoefficientMatrix_of_pos
    (Phi : Channel a b) (v : a → ℂ)
    (hpos : 0 < ∑ x, Complex.normSq (v x)) :
    AmplitudeDamping.normalizedGramEntropy
        (∑ x, Complex.normSq (v x))
        (Phi.stinespringCoefficientMatrix v) =
      (∑ x, Complex.normSq (v x)) *
        (Phi.applyState
          (PureVector.normalize v (by
            rw [rankOneMatrix_trace]
            simpa [dotProduct, Complex.mul_conj] using hpos)).state).vonNeumann := by
  let t : ℝ := ∑ x, Complex.normSq (v x)
  have ht : 0 ≤ t := le_of_lt hpos
  have htrace : (rankOneMatrix v).trace.re = t := by
    simp [t, rankOneMatrix_trace, dotProduct, Complex.mul_conj]
  let psi : PureVector a := PureVector.normalize v (by
    rw [htrace]
    exact hpos)
  let A := Phi.stinespringCoefficientMatrix psi.amp
  have hnorm : AmplitudeDamping.frobeniusSq A = 1 := by
    have := Phi.frobeniusSq_stinespringCoefficientMatrix psi.amp
    rw [this]
    have h := congrArg Complex.re psi.trace_rankOne_eq_one
    simpa [rankOneMatrix_trace, dotProduct, Complex.mul_conj] using h
  have hsqrt : Real.sqrt t ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr hpos)
  have hscale :
      (Real.sqrt t : ℂ) • A = Phi.stinespringCoefficientMatrix v := by
    ext y k
    simp only [A, psi, Channel.stinespringCoefficientMatrix,
      PureVector.normalize, Matrix.smul_apply, smul_eq_mul]
    rw [htrace]
    simp only [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro x _
    push_cast
    field_simp
  have hhom := AmplitudeDamping.normalizedGramEntropy_sqrt_smul t ht A
  rw [hnorm, hscale] at hhom
  have hvnorm : AmplitudeDamping.frobeniusSq
      (Phi.stinespringCoefficientMatrix v) = t := by
    exact Phi.frobeniusSq_stinespringCoefficientMatrix v
  rw [hvnorm] at hhom
  have hunit := Phi.normalizedGramEntropy_stinespringCoefficientMatrix psi
  rw [hnorm] at hunit
  change AmplitudeDamping.normalizedGramEntropy t
      (Phi.stinespringCoefficientMatrix v) = t * _
  rw [hhom, hunit]

end Channel

end

end QIT
