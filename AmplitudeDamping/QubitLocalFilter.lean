import AmplitudeDamping.ChannelChoi

/-! # Reference filters for two-qubit inputs

Every normalized two-qubit input is a local filter of the Bell vector. The
same filter converts a channel's normalized Choi matrix into its output on
that input. Determinants record the concurrence change under filtering.
-/

open scoped BigOperators NNReal ComplexOrder Matrix Kronecker
namespace AmplitudeDamping
open QIT
noncomputable section
set_option maxHeartbeats 800000

/-- The reference filter that prepares `ψ` from the normalized Bell vector. -/
def qubitReferenceFilter (ψ : PureVector (Qubit × Qubit)) : Matrix Qubit Qubit ℂ :=
  (Real.sqrt 2 : ℂ) • twoQubitAmplitudeMatrix ψ

/-- Applying a matrix to the first subsystem multiplies the amplitude matrix. -/
theorem qubit_localFilter_amp (A : Matrix Qubit Qubit ℂ)
    (v : Qubit × Qubit → ℂ) (x : Qubit × Qubit) :
    ((A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ v) x =
      (A * Matrix.of (fun i j => v (i,j))) x.1 x.2 := by
  simp [Matrix.mulVec, dotProduct, Matrix.mul_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]

/-- Explicit Bell-vector preparation by the reference filter. -/
theorem qubitReferenceFilter_bell (ψ : PureVector (Qubit × Qubit)) :
    (qubitReferenceFilter ψ ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ
      (PureVector.maximallyEntangled (Equiv.refl Qubit)).amp = ψ.amp := by
  funext x
  rw [qubit_localFilter_amp]
  have hs : (Real.sqrt 2 : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)))
  simp [Matrix.mul_apply, PureVector.maximallyEntangled_amp,
    qubitReferenceFilter, twoQubitAmplitudeMatrix_apply, mul_assoc]
  rw [mul_left_comm, mul_inv_cancel₀ hs, mul_one]

/-- The pure input matrix is a local conjugation of the Bell state. -/
theorem qubitReferenceFilter_bell_state (ψ : PureVector (Qubit × Qubit)) :
    ψ.state.matrix =
      (qubitReferenceFilter ψ ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *
        (State.maximallyEntangled (Equiv.refl Qubit)).matrix *
          (qubitReferenceFilter ψ ⊗ₖ (1 : Matrix Qubit Qubit ℂ))ᴴ := by
  change rankOneMatrix ψ.amp = _
  have h := rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose
    (qubitReferenceFilter ψ ⊗ₖ (1 : Matrix Qubit Qubit ℂ))
    (PureVector.maximallyEntangled (Equiv.refl Qubit)).amp
  rw [qubitReferenceFilter_bell] at h
  exact h

/-- Entrywise form of a filter acting on the reference subsystem. -/
theorem qubit_localFilter_matrix_apply {b : Type*} [Fintype b] [DecidableEq b]
    (A : Matrix Qubit Qubit ℂ) (X : Matrix (Qubit × b) (Qubit × b) ℂ)
    (x y : Qubit × b) :
    ((A ⊗ₖ (1 : Matrix b b ℂ)) * X * (A ⊗ₖ (1 : Matrix b b ℂ))ᴴ) x y =
      ∑ j : Qubit, ∑ i : Qubit, A x.1 i * X (i,x.2) (j,y.2) * star (A y.1 j) := by
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply, apply_ite, add_mul]

/-- A channel output on a pure two-qubit input is the locally filtered Choi
matrix. The output dimension is unrestricted. -/
theorem qubitReferenceFilter_channelChoi {b : Type*} [Fintype b] [DecidableEq b]
    (N : Channel Qubit b) (ψ : PureVector (Qubit × Qubit)) :
    (((Channel.idChannel Qubit).prod N).applyState ψ.state).matrix =
      (qubitReferenceFilter ψ ⊗ₖ (1 : Matrix b b ℂ)) *
        (channelChoiState N).matrix *
          (qubitReferenceFilter ψ ⊗ₖ (1 : Matrix b b ℂ))ᴴ := by
  ext x y
  rw [qubit_localFilter_matrix_apply, channelChoiState_matrix]
  change MatrixMap.kron (Channel.idChannel Qubit).map N.map ψ.state.matrix x y = _
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  obtain ⟨i, x⟩ := x
  obtain ⟨j, y⟩ := y
  fin_cases i <;> fin_cases j <;>
    simp [MatrixMap.kron, Channel.idChannel, MatrixMap.ofKraus,
    MatrixMap.choi, qubitReferenceFilter,
    twoQubitAmplitudeMatrix_apply, Fin.sum_univ_two,
    Matrix.single_apply, star_mul, mul_assoc] <;>
    ring_nf <;> simp only [hs] <;> ring

/-- The filtered Choi matrix has unit trace, even for a singular filter. -/
theorem qubitReferenceFilter_channelChoi_trace {b : Type*}
    [Fintype b] [DecidableEq b] (N : Channel Qubit b)
    (ψ : PureVector (Qubit × Qubit)) :
    ((qubitReferenceFilter ψ ⊗ₖ (1 : Matrix b b ℂ)) *
      (channelChoiState N).matrix *
        (qubitReferenceFilter ψ ⊗ₖ (1 : Matrix b b ℂ))ᴴ).trace = 1 := by
  rw [← qubitReferenceFilter_channelChoi N ψ]
  exact State.trace_eq_one _

/-- Determinant of the Bell-to-input filter. -/
theorem qubitReferenceFilter_det (ψ : PureVector (Qubit × Qubit)) :
    (qubitReferenceFilter ψ).det = 2 * (twoQubitAmplitudeMatrix ψ).det := by
  rw [qubitReferenceFilter, Matrix.det_smul]
  have hs : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)
  simpa using congrArg (fun z : ℂ => z * (twoQubitAmplitudeMatrix ψ).det) hs

/-- The determinant modulus of every normalized reference filter is at most one. -/
theorem qubitReferenceFilter_norm_det_le_one (ψ : PureVector (Qubit × Qubit)) :
    ‖(qubitReferenceFilter ψ).det‖ ≤ 1 := by
  rw [qubitReferenceFilter_det, norm_mul]
  norm_num
  exact two_norm_det_le_one ψ

/-- Determinants multiply under the unnormalized local filter. -/
theorem qubit_localFilter_det (A : Matrix Qubit Qubit ℂ)
    (ψ : PureVector (Qubit × Qubit)) :
    (Matrix.of (fun i j => ((A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ψ.amp) (i,j))).det =
      A.det * (twoQubitAmplitudeMatrix ψ).det := by
  have h : Matrix.of (fun i j => ((A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ψ.amp) (i,j)) =
      A * twoQubitAmplitudeMatrix ψ := by
    ext i j
    exact qubit_localFilter_amp A ψ.amp (i,j)
  rw [h, Matrix.det_mul]

/-- Normalization divides the amplitude determinant by the branch weight. -/
theorem twoQubitAmplitudeMatrix_normalize_det (v : Qubit × Qubit → ℂ)
    (hp : 0 < (rankOneMatrix v).trace.re) :
    (twoQubitAmplitudeMatrix (PureVector.normalize v hp)).det =
      (((rankOneMatrix v).trace.re)⁻¹ : ℂ) * (Matrix.of (fun i j => v (i,j))).det := by
  have hm : twoQubitAmplitudeMatrix (PureVector.normalize v hp) =
      (((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) •
        Matrix.of (fun i j => v (i,j)) := rfl
  rw [hm, Matrix.det_smul]
  have hs : (((Real.sqrt (rankOneMatrix v).trace.re)⁻¹ : ℝ) : ℂ) ^ 2 =
      (((rankOneMatrix v).trace.re)⁻¹ : ℂ) := by
    norm_cast
    rw [inv_pow, Real.sq_sqrt hp.le]
  simpa using congrArg (fun z : ℂ => z * (Matrix.of (fun i j => v (i,j))).det) hs

/-- Raw two-qubit amplitudes retain their homogeneous concurrence when
normalized and multiplied by their squared norm. -/
theorem twoQubitAmplitudeMatrix_normalize_weighted_concurrence
    (v : Qubit × Qubit → ℂ) (hp : 0 < (rankOneMatrix v).trace.re) :
    (rankOneMatrix v).trace.re *
      (2 * ‖(twoQubitAmplitudeMatrix (PureVector.normalize v hp)).det‖) =
      2 * ‖(Matrix.of (fun i j => v (i,j))).det‖ := by
  rw [twoQubitAmplitudeMatrix_normalize_det, norm_mul, norm_inv,
    Complex.norm_of_nonneg hp.le]
  field_simp [hp.ne']

/-- Probability-weighted concurrence scales by the filter's determinant. -/
theorem qubit_localFilter_weighted_concurrence (A : Matrix Qubit Qubit ℂ)
    (ψ : PureVector (Qubit × Qubit))
    (hp : 0 < (rankOneMatrix
      ((A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ψ.amp)).trace.re) :
    (rankOneMatrix ((A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ψ.amp)).trace.re *
      (2 * ‖(twoQubitAmplitudeMatrix (PureVector.normalize
        ((A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ψ.amp) hp)).det‖) =
      ‖A.det‖ * (2 * ‖(twoQubitAmplitudeMatrix ψ).det‖) := by
  rw [twoQubitAmplitudeMatrix_normalize_det, qubit_localFilter_det,
    norm_mul, norm_mul, norm_inv, Complex.norm_of_nonneg hp.le]
  field_simp [hp.ne']

/-- A zero-probability filter branch is the zero vector. -/
theorem qubit_localFilter_eq_zero_of_weight_zero (A : Matrix Qubit Qubit ℂ)
    (ψ : PureVector (Qubit × Qubit))
    (hp : (rankOneMatrix
      ((A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ψ.amp)).trace.re = 0) :
    (A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ψ.amp = 0 := by
  let v := (A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ψ.amp
  have hz : rankOneMatrix v = 0 := by
    apply (Matrix.PosSemidef.trace_eq_zero_iff (rankOneMatrix_pos v)).mp
    apply Complex.ext
    · exact hp
    · exact (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos v)).2.symm
  funext x
  have hd := congrFun (congrFun hz x) x
  change v x * star (v x) = 0 at hd
  simpa using (mul_eq_zero.mp hd).elim id (fun h => star_eq_zero.mp h)

/-- Vanishing branches also obey determinant scaling, with zero weighted
concurrence independently of the normalized placeholder chosen for the branch. -/
theorem qubit_localFilter_concurrence_zero (A : Matrix Qubit Qubit ℂ)
    (ψ : PureVector (Qubit × Qubit))
    (hp : (rankOneMatrix
      ((A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ψ.amp)).trace.re = 0) :
    ‖A.det‖ * (2 * ‖(twoQubitAmplitudeMatrix ψ).det‖) = 0 := by
  have h := qubit_localFilter_det A ψ
  rw [qubit_localFilter_eq_zero_of_weight_zero A ψ hp] at h
  have hz : A.det * (twoQubitAmplitudeMatrix ψ).det = 0 := by
    simpa [Matrix.det_fin_two] using h.symm
  have hn := congrArg norm hz
  rw [norm_mul, norm_zero] at hn
  nlinarith

/-- Probability of a local-filter branch. -/
def qubitLocalFilterWeight (A : Matrix Qubit Qubit ℂ)
    (ψ : PureVector (Qubit × Qubit)) : ℝ :=
  (rankOneMatrix ((A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ψ.amp)).trace.re

theorem qubitLocalFilterWeight_nonneg (A : Matrix Qubit Qubit ℂ)
    (ψ : PureVector (Qubit × Qubit)) : 0 ≤ qubitLocalFilterWeight A ψ :=
  (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos _)).1

/-- A total normalized filter branch. A zero-weight branch uses the original
vector as a harmless placeholder. -/
def qubitLocalFilterVector (A : Matrix Qubit Qubit ℂ)
    (ψ : PureVector (Qubit × Qubit)) : PureVector (Qubit × Qubit) :=
  if hp : 0 < qubitLocalFilterWeight A ψ then
    PureVector.normalize ((A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) *ᵥ ψ.amp) hp
  else ψ

/-- Total probability-weighted concurrence formula, including zero branches. -/
theorem qubitLocalFilterVector_weighted_concurrence (A : Matrix Qubit Qubit ℂ)
    (ψ : PureVector (Qubit × Qubit)) :
    qubitLocalFilterWeight A ψ *
      (2 * ‖(twoQubitAmplitudeMatrix (qubitLocalFilterVector A ψ)).det‖) =
      ‖A.det‖ * (2 * ‖(twoQubitAmplitudeMatrix ψ).det‖) := by
  unfold qubitLocalFilterVector
  split_ifs with hp
  · exact qubit_localFilter_weighted_concurrence A ψ hp
  · have hz : qubitLocalFilterWeight A ψ = 0 :=
      le_antisymm (not_lt.mp hp) (qubitLocalFilterWeight_nonneg A ψ)
    rw [hz, zero_mul]
    exact (qubit_localFilter_concurrence_zero A ψ hz).symm

/-- The weighted normalized branch is exactly the conjugated input matrix. -/
theorem qubitLocalFilterVector_weighted_matrix (A : Matrix Qubit Qubit ℂ)
    (ψ : PureVector (Qubit × Qubit)) :
    (qubitLocalFilterWeight A ψ : ℂ) • (qubitLocalFilterVector A ψ).state.matrix =
      (A ⊗ₖ (1 : Matrix Qubit Qubit ℂ)) * ψ.state.matrix *
        (A ⊗ₖ (1 : Matrix Qubit Qubit ℂ))ᴴ := by
  rw [PureVector.state_matrix ψ,
    ← rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  unfold qubitLocalFilterVector
  split_ifs with hp
  · rw [PureVector.normalize_state_matrix, smul_smul]
    have hc : (qubitLocalFilterWeight A ψ : ℂ) *
        ((qubitLocalFilterWeight A ψ)⁻¹ : ℝ) = 1 := by
      exact_mod_cast mul_inv_cancel₀ hp.ne'
    change ((qubitLocalFilterWeight A ψ : ℂ) *
      ((qubitLocalFilterWeight A ψ)⁻¹ : ℝ)) • _ = _
    rw [hc, one_smul]
  · have hz : qubitLocalFilterWeight A ψ = 0 :=
      le_antisymm (not_lt.mp hp) (qubitLocalFilterWeight_nonneg A ψ)
    rw [hz, Complex.ofReal_zero, zero_smul,
      qubit_localFilter_eq_zero_of_weight_zero A ψ hz]
    ext i j
    simp [rankOneMatrix_apply]

end
end AmplitudeDamping
