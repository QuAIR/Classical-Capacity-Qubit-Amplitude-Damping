import AmplitudeDamping.ScalarCapacity
import AmplitudeDamping.ChoiState
import AmplitudeDamping.Triangular.ScalarCompression
import QIT.Information.Entropy.ConditionalEntropyConcavity

/-!
# The binary Kraus instrument for amplitude damping
-/
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT
noncomputable section
set_option maxHeartbeats 1000000

/-- Sign of the two branches (`0` is plus). -/
def binaryInstrumentSign (s : Fin 2) : ℝ := if s = 0 then 1 else -1

/-- Hadamard mixing of the no-jump and jump amplitude-damping operators. -/
def binaryInstrumentKraus (p : ℝ) (s : Fin 2) : Matrix Qubit Qubit ℂ :=
  ((Real.sqrt 2 : ℂ)⁻¹) •
    (amplitudeKrausZero p + (binaryInstrumentSign s : ℂ) • amplitudeKrausOne p)

private theorem binaryInstrumentScale_sq : (Real.sqrt 2 : ℂ)⁻¹ ^ 2 = 1 / 2 := by
  rw [inv_pow]
  have h : (Real.sqrt 2 : ℂ) ^ 2 = 2 := by
    exact_mod_cast Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)
  rw [h]
  norm_num

/-- The mixed Kraus family gives exactly the same channel map. -/
theorem binaryInstrumentKraus_map (p : ℝ) (X : CMatrix Qubit) :
    MatrixMap.ofKraus (binaryInstrumentKraus p) X =
      MatrixMap.ofKraus (amplitudeKraus p) X := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [MatrixMap.ofKraus, binaryInstrumentKraus, binaryInstrumentSign,
      amplitudeKraus, amplitudeKrausZero, amplitudeKrausOne,
      Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two] <;>
    ring_nf <;> rw [binaryInstrumentScale_sq] <;> ring

/-- Unnormalized branch output. -/
def binaryInstrumentBranch (p : ℝ) (s : Fin 2) (ρ : State Qubit) : CMatrix Qubit :=
  binaryInstrumentKraus p s * ρ.matrix * (binaryInstrumentKraus p s).conjTranspose

theorem binaryInstrumentBranch_pos (p : ℝ) (s : Fin 2) (ρ : State Qubit) :
    (binaryInstrumentBranch p s ρ).PosSemidef :=
  ρ.pos.mul_mul_conjTranspose_same _

/-- The outcome probabilities depend only on the real input coherence. -/
theorem binaryInstrumentBranch_trace
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Fin 2) (ρ : State Qubit) :
    (binaryInstrumentBranch p s ρ).trace.re =
      1 / 2 + binaryInstrumentSign s * Real.sqrt p * (ρ.matrix 0 1).re := by
  have hsqp : (Real.sqrt p : ℂ) ^ 2 = (p : ℂ) := by
    exact_mod_cast Real.sq_sqrt hp0
  have hsq1p : (Real.sqrt (1 - p) : ℂ) ^ 2 = ((1 - p : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hp1)
  have htrace : (binaryInstrumentBranch p s ρ).trace =
      (1 / 2 : ℂ) + (binaryInstrumentSign s : ℂ) * (Real.sqrt p : ℂ) *
        ((ρ.matrix 0 1).re : ℂ) := by
    fin_cases s <;>
      simp [binaryInstrumentBranch, binaryInstrumentKraus, binaryInstrumentSign,
        amplitudeKrausZero, amplitudeKrausOne, Matrix.trace, Fin.sum_univ_two,
        Matrix.mul_apply, Matrix.vecMul, dotProduct, qubit_diagonal_zero,
        qubit_diagonal_one, qubit_lower_coherence] <;> ring_nf <;>
      rw [binaryInstrumentScale_sq, hsqp, hsq1p] <;>
      push_cast <;> apply Complex.ext <;> simp <;> ring
  simpa using congrArg Complex.re htrace

/-- Both branch determinants have the same input-independent scale. -/
theorem binaryInstrumentBranch_det
    (p : ℝ) (_hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Fin 2) (ρ : State Qubit) :
    Matrix.det (binaryInstrumentBranch p s ρ) =
      (((1 - p) / 4 : ℝ) : ℂ) * Matrix.det ρ.matrix := by
  have hsq1p : (Real.sqrt (1 - p) : ℂ) ^ 2 = ((1 - p : ℝ) : ℂ) := by
    exact_mod_cast Real.sq_sqrt (sub_nonneg.mpr hp1)
  rw [binaryInstrumentBranch, Matrix.det_mul, Matrix.det_mul,
    Matrix.det_conjTranspose]
  have hd : Matrix.det (binaryInstrumentKraus p s) =
      (Real.sqrt (1 - p) : ℂ) / 2 := by
    fin_cases s <;>
      simp [binaryInstrumentKraus, binaryInstrumentSign, amplitudeKrausZero,
        amplitudeKrausOne, Matrix.det_fin_two] <;>
      ring_nf <;> rw [binaryInstrumentScale_sq] <;> ring
  rw [hd]
  simp
  calc
    _ = (Real.sqrt (1 - p) : ℂ) ^ 2 / 4 * Matrix.det ρ.matrix := by ring
    _ = _ := by rw [hsq1p]; push_cast; ring

/-- The complementary qubit state, whose density matrix is `I - ρ`. -/
def qubitComplement (ρ : State Qubit) : State Qubit where
  matrix := !![ρ.matrix 1 1, -ρ.matrix 0 1; -ρ.matrix 1 0, ρ.matrix 0 0]
  pos := by
    let J : CMatrix Qubit := !![0,1;-1,0]
    have h := ρ.pos.transpose.mul_mul_conjTranspose_same J
    convert h using 1
    ext i j
    fin_cases i <;> fin_cases j <;> simp [J, Matrix.mul_apply, Matrix.vecMul, dotProduct, Fin.sum_univ_two]
  trace_eq_one := by
    simpa [Matrix.trace, Fin.sum_univ_two, add_comm] using ρ.trace_eq_one

theorem qubitComplement_matrix (ρ : State Qubit) :
    (qubitComplement ρ).matrix = 1 - ρ.matrix := by
  have ht : ρ.matrix 0 0 + ρ.matrix 1 1 = 1 := by
    simpa [Matrix.trace, Fin.sum_univ_two] using ρ.trace_eq_one
  ext i j
  fin_cases i <;> fin_cases j <;> simp [qubitComplement] <;> linear_combination ht

@[simp]
theorem qubitComplement_det (ρ : State Qubit) :
    Matrix.det (qubitComplement ρ).matrix = Matrix.det ρ.matrix := by
  simp [qubitComplement, Matrix.det_fin_two]
  ring


/-- The homogeneous, zero-safe entropy perspective of a positive matrix. -/
def entropyPerspective {d : Type*} [Fintype d] [DecidableEq d]
    (X : CMatrix d) (hX : X.PosSemidef) : ℝ :=
  psdEntropy X hX + xlog2 X.trace.re

@[simp]
theorem entropyPerspective_zero {d : Type*} [Fintype d] [DecidableEq d] :
    entropyPerspective (0 : CMatrix d) Matrix.PosSemidef.zero = 0 := by
  simp [entropyPerspective, psdEntropy_zero, xlog2]

/-- The perspective is precisely branch probability times normalized entropy. -/
theorem entropyPerspective_eq_weight_mul_entropy
    {d : Type*} [Fintype d] [DecidableEq d]
    (X : CMatrix d) (hX : X.PosSemidef) (ht : X.trace.re ≠ 0) :
    entropyPerspective X hX = X.trace.re * (State.normalizePSD X hX ht).vonNeumann := by
  have ht0 : 0 ≤ X.trace.re := (Matrix.PosSemidef.trace_nonneg hX).1
  let σ := State.normalizePSD X hX ht
  have hscale : (X.trace.re : ℂ) • σ.matrix = X := by
    ext i j
    simp [σ, State.normalizePSD_matrix, Complex.real_smul, ht]
  have h := psdEntropy_real_smul X.trace.re ht0 σ.matrix σ.pos
  rw [σ.trace_re_eq_one, mul_one] at h
  have he : psdEntropy ((X.trace.re : ℂ) • σ.matrix)
      (σ.pos.smul (by exact_mod_cast ht0)) = psdEntropy X hX :=
    psdEntropy_congr hscale _ _
  rw [he] at h
  change psdEntropy X hX + xlog2 X.trace.re = X.trace.re * psdEntropy σ.matrix σ.pos
  linarith

/-- Entropy perspective is superadditive on positive matrices. This is the
homogeneous form of von Neumann entropy concavity. -/
theorem entropyPerspective_add_ge
    {d : Type*} [Fintype d] [DecidableEq d]
    (X Y : CMatrix d) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    entropyPerspective X hX + entropyPerspective Y hY ≤
      entropyPerspective (X + Y) (hX.add hY) := by
  by_cases hx : X = 0
  · subst X
    simp
  by_cases hy : Y = 0
  · subst Y
    simp
  have tx : 0 < X.trace.re := State.posSemidef_trace_pos_of_ne_zero hX hx
  have ty : 0 < Y.trace.re := State.posSemidef_trace_pos_of_ne_zero hY hy
  have tz : 0 < (X + Y).trace.re := by
    simp only [Matrix.trace_add, Complex.add_re]
    linarith
  let σ := State.normalizePSD X hX tx.ne'
  let τ := State.normalizePSD Y hY ty.ne'
  let ω := State.normalizePSD (X + Y) (hX.add hY) tz.ne'
  let E : Ensemble (Fin 2) d :=
    { probs := ![⟨X.trace.re / (X + Y).trace.re, div_nonneg tx.le tz.le⟩,
        ⟨Y.trace.re / (X + Y).trace.re, div_nonneg ty.le tz.le⟩]
      weights_sum := by
        apply NNReal.eq
        simp only [Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
          NNReal.coe_add, NNReal.coe_one]
        change X.trace.re / (X + Y).trace.re + Y.trace.re / (X + Y).trace.re = 1
        rw [← add_div, Matrix.trace_add, Complex.add_re, div_self (ne_of_gt (add_pos tx ty))]
      states := ![σ, τ] }
  have havg : E.averageState = ω := by
    apply State.ext
    rw [Ensemble.averageState_matrix]
    ext i j
    simp [E, σ, τ, ω, State.normalizePSD_matrix, Fin.sum_univ_two,
      Matrix.smul_apply, NNReal.smul_def, Complex.real_smul, div_eq_mul_inv]
    change (((X.trace.re * (X.trace.re + Y.trace.re)⁻¹ : ℝ) : ℂ) *
      ((X.trace.re : ℂ)⁻¹ * X i j) +
      ((Y.trace.re * (X.trace.re + Y.trace.re)⁻¹ : ℝ) : ℂ) *
      ((Y.trace.re : ℂ)⁻¹ * Y i j)) =
      ((X.trace.re : ℂ) + (Y.trace.re : ℂ))⁻¹ * X i j +
      ((X.trace.re : ℂ) + (Y.trace.re : ℂ))⁻¹ * Y i j
    push_cast
    have hxC : (X.trace.re : ℂ) ≠ 0 := by exact_mod_cast tx.ne'
    have hyC : (Y.trace.re : ℂ) ≠ 0 := by exact_mod_cast ty.ne'
    field_simp
  have hc := Ensemble.vonNeumann_average_ge_sum E
  rw [havg] at hc
  have hc' := mul_le_mul_of_nonneg_left hc tz.le
  simp only [Fin.sum_univ_two] at hc'
  change (X + Y).trace.re *
    (X.trace.re / (X + Y).trace.re * σ.vonNeumann +
      Y.trace.re / (X + Y).trace.re * τ.vonNeumann) ≤
    (X + Y).trace.re * ω.vonNeumann at hc'
  rw [entropyPerspective_eq_weight_mul_entropy X hX tx.ne',
    entropyPerspective_eq_weight_mul_entropy Y hY ty.ne',
    entropyPerspective_eq_weight_mul_entropy (X + Y) (hX.add hY) tz.ne']
  convert hc' using 1; field_simp; ring


theorem entropyPerspective_congr
    {d : Type*} [Fintype d] [DecidableEq d]
    {X Y : CMatrix d} (h : X = Y) (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    entropyPerspective X hX = entropyPerspective Y hY := by subst Y; rfl

/-- Homogeneity of the zero-safe entropy perspective. -/
theorem entropyPerspective_smul
    {d : Type*} [Fintype d] [DecidableEq d]
    (c : ℝ) (hc : 0 ≤ c) (X : CMatrix d) (hX : X.PosSemidef) :
    entropyPerspective ((c : ℂ) • X) (hX.smul (by exact_mod_cast hc)) =
      c * entropyPerspective X hX := by
  unfold entropyPerspective
  rw [psdEntropy_real_smul c hc X hX]
  simp only [Matrix.trace_smul, smul_eq_mul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero]
  rw [xlog2_mul_of_nonneg hc (Matrix.PosSemidef.trace_nonneg hX).1]
  ring

/-- The determinant of a normalized positive qubit matrix. -/
theorem qubitDeterminant_normalizePSD (X : CMatrix Qubit)
    (hX : X.PosSemidef) (ht : X.trace.re ≠ 0) :
    qubitDeterminant (State.normalizePSD X hX ht) =
      X.trace.re⁻¹ ^ 2 * (Matrix.det X).re := by
  unfold qubitDeterminant
  have hm : (State.normalizePSD X hX ht).matrix = ((X.trace.re⁻¹ : ℝ) : ℂ) • X := by
    ext i j
    simp [State.normalizePSD_matrix, Complex.real_smul]
  rw [hm, Matrix.det_smul]
  change ((((X.trace.re⁻¹ : ℝ) : ℂ) ^ 2) * Matrix.det X).re = _
  rw [← Complex.ofReal_pow]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]

/-- Trace and determinant determine the entropy perspective of a qubit. -/
theorem entropyPerspective_qubit_eq_of_trace_det
    (X Y : CMatrix Qubit) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (ht : X.trace.re = Y.trace.re) (hd : Matrix.det X = Matrix.det Y) :
    entropyPerspective X hX = entropyPerspective Y hY := by
  by_cases hx : X.trace.re = 0
  · have hy : Y.trace.re = 0 := ht.symm.trans hx
    have xzero : X = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hX).mp (by
      apply Complex.ext
      · exact hx
      · exact (Matrix.PosSemidef.trace_nonneg hX).2.symm)
    have yzero : Y = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hY).mp (by
      apply Complex.ext
      · exact hy
      · exact (Matrix.PosSemidef.trace_nonneg hY).2.symm)
    subst X; subst Y; rfl
  have hy : Y.trace.re ≠ 0 := by rw [← ht]; exact hx
  rw [entropyPerspective_eq_weight_mul_entropy X hX hx,
    entropyPerspective_eq_weight_mul_entropy Y hY hy,
    qubit_vonNeumann_eq_entanglementCurve_det,
    qubit_vonNeumann_eq_entanglementCurve_det,
    qubitDeterminant_normalizePSD, qubitDeterminant_normalizePSD, ht, hd]

/-- Average normalized branch entropy of the explicit binary instrument. -/
def binaryInstrumentCost (p : ℝ) (ρ : State Qubit) : ℝ :=
  entropyPerspective (binaryInstrumentBranch p 0 ρ) (binaryInstrumentBranch_pos p 0 ρ) +
  entropyPerspective (binaryInstrumentBranch p 1 ρ) (binaryInstrumentBranch_pos p 1 ρ)

/-- Complementation exchanges the two branch spectra and preserves cost. -/
theorem binaryInstrumentCost_complement
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ : State Qubit) :
    binaryInstrumentCost p (qubitComplement ρ) = binaryInstrumentCost p ρ := by
  have hswap (s : Fin 2) :
      entropyPerspective (binaryInstrumentBranch p s (qubitComplement ρ))
        (binaryInstrumentBranch_pos p s (qubitComplement ρ)) =
      entropyPerspective (binaryInstrumentBranch p (1 - s) ρ)
        (binaryInstrumentBranch_pos p (1 - s) ρ) := by
    apply entropyPerspective_qubit_eq_of_trace_det
    · rw [binaryInstrumentBranch_trace p hp0 hp1,
        binaryInstrumentBranch_trace p hp0 hp1]
      fin_cases s <;> simp [qubitComplement, binaryInstrumentSign]
    · rw [binaryInstrumentBranch_det p hp0 hp1,
        binaryInstrumentBranch_det p hp0 hp1, qubitComplement_det]
  unfold binaryInstrumentCost
  rw [hswap, hswap]
  norm_num
  ring


/-- Maximally mixed qubit input. -/
def binaryInstrumentCenter : State Qubit :=
  diagonalQubitState (1 / 2) (by norm_num) (by norm_num)

theorem binaryInstrumentCenter_matrix :
    binaryInstrumentCenter.matrix = (1 / 2 : ℂ) • (1 : CMatrix Qubit) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    norm_num [binaryInstrumentCenter, diagonalQubitState, Classical.diagonalState,
      diagonalQubitProb]
  all_goals change ((1 / 2 : ℝ) : ℂ) = 1 / 2
  all_goals norm_num

/-- The two complementary branch matrices sum to twice the central branch. -/
theorem binaryInstrumentBranch_complement_add (p : ℝ) (s : Fin 2) (ρ : State Qubit) :
    binaryInstrumentBranch p s ρ + binaryInstrumentBranch p s (qubitComplement ρ) =
      (2 : ℂ) • binaryInstrumentBranch p s binaryInstrumentCenter := by
  have hsum : ρ.matrix + (qubitComplement ρ).matrix =
      (2 : ℂ) • binaryInstrumentCenter.matrix := by
    rw [qubitComplement_matrix, binaryInstrumentCenter_matrix, smul_smul]
    norm_num
  unfold binaryInstrumentBranch
  rw [← Matrix.add_mul, ← Matrix.mul_add, hsum, Matrix.mul_smul, Matrix.smul_mul]

/-- The complement symmetry and entropy perspective concavity place the
maximum at the maximally mixed input. -/
theorem binaryInstrumentCost_le_center
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ : State Qubit) :
    binaryInstrumentCost p ρ ≤ binaryInstrumentCost p binaryInstrumentCenter := by
  have hbranch (s : Fin 2) := entropyPerspective_add_ge
    (binaryInstrumentBranch p s ρ) (binaryInstrumentBranch p s (qubitComplement ρ))
    (binaryInstrumentBranch_pos p s ρ) (binaryInstrumentBranch_pos p s (qubitComplement ρ))
  have hupper (s : Fin 2) :
      entropyPerspective (binaryInstrumentBranch p s ρ) (binaryInstrumentBranch_pos p s ρ) +
        entropyPerspective (binaryInstrumentBranch p s (qubitComplement ρ))
          (binaryInstrumentBranch_pos p s (qubitComplement ρ)) ≤
      2 * entropyPerspective (binaryInstrumentBranch p s binaryInstrumentCenter)
        (binaryInstrumentBranch_pos p s binaryInstrumentCenter) := by
    have he := entropyPerspective_congr (binaryInstrumentBranch_complement_add p s ρ)
      ((binaryInstrumentBranch_pos p s ρ).add (binaryInstrumentBranch_pos p s (qubitComplement ρ)))
      ((binaryInstrumentBranch_pos p s binaryInstrumentCenter).smul (by norm_num : (0:ℂ) ≤ 2))
    have hh := entropyPerspective_smul 2 (by norm_num)
      (binaryInstrumentBranch p s binaryInstrumentCenter)
      (binaryInstrumentBranch_pos p s binaryInstrumentCenter)
    have h := hbranch s
    rw [he] at h
    simpa only [Complex.ofReal_ofNat] using h.trans_eq hh
  have hsym := binaryInstrumentCost_complement p hp0 hp1 ρ
  unfold binaryInstrumentCost at hsym ⊢
  linarith [hupper 0, hupper 1]

/-- Exact entropy perspective of either branch at the central input. -/
theorem binaryInstrumentBranch_center_entropy
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Fin 2) :
    entropyPerspective (binaryInstrumentBranch p s binaryInstrumentCenter)
      (binaryInstrumentBranch_pos p s binaryInstrumentCenter) =
      (1 / 2) * binaryEntropy ((1 + Real.sqrt p) / 2) := by
  have ht : (binaryInstrumentBranch p s binaryInstrumentCenter).trace.re = 1 / 2 := by
    rw [binaryInstrumentBranch_trace p hp0 hp1]
    simp [binaryInstrumentCenter]
  have htne : (binaryInstrumentBranch p s binaryInstrumentCenter).trace.re ≠ 0 := by
    rw [ht]; norm_num
  have hd : Matrix.det binaryInstrumentCenter.matrix = (1 / 4 : ℂ) := by
    rw [binaryInstrumentCenter_matrix, Matrix.det_smul]
    norm_num [Qubit]
  have hnd : qubitDeterminant (State.normalizePSD
      (binaryInstrumentBranch p s binaryInstrumentCenter)
      (binaryInstrumentBranch_pos p s binaryInstrumentCenter) htne) = (1 - p) / 4 := by
    rw [qubitDeterminant_normalizePSD, ht, binaryInstrumentBranch_det p hp0 hp1, hd]
    norm_num
    ring
  rw [entropyPerspective_eq_weight_mul_entropy _ _ htne,
    qubit_vonNeumann_eq_entanglementCurve_det, hnd, ht]
  have harg : 2 * Real.sqrt ((1 - p) / 4) = Real.sqrt (1 - p) := by
    rw [Real.sqrt_div (sub_nonneg.mpr hp1)]
    have h4 : Real.sqrt (4 : ℝ) = 2 := by
      convert Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 2) using 1; norm_num
    rw [h4]
    ring
  rw [harg, entanglementCurve_sqrt_one_sub p hp1]

/-- Value of the maximum, in bits. -/
theorem binaryInstrumentCost_center
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    binaryInstrumentCost p binaryInstrumentCenter =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  unfold binaryInstrumentCost
  rw [binaryInstrumentBranch_center_entropy p hp0 hp1,
    binaryInstrumentBranch_center_entropy p hp0 hp1]
  ring

/-- Uniform one-use bound for every input qubit, including zero branch
weights and endpoint damping parameters. -/
theorem binaryInstrumentCost_le
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ : State Qubit) :
    binaryInstrumentCost p ρ ≤ binaryEntropy ((1 + Real.sqrt p) / 2) := by
  rw [← binaryInstrumentCost_center p hp0 hp1]
  exact binaryInstrumentCost_le_center p hp0 hp1 ρ

end
end AmplitudeDamping
