import AmplitudeDamping.Triangular.EntropyIntegral
import QIT.Information.Renyi.FrankLieb.Concavity

/-!
# Dephasing layer for the triangular entropy inequality

This module begins Step 2 of the triangular entropy proof by establishing the
unitary covariance facts needed for sign-unitary dephasing.  In particular,
positive square roots transform covariantly and spectral entropy is invariant
under unitary conjugation.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Positive semidefinite square roots transform covariantly under unitary
conjugation. -/
theorem psdSqrt_unitary_conj
    {d : Type} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (X : Matrix d d ℂ)
    (hX : X.PosSemidef) :
    QIT.psdSqrt ((U : Matrix d d ℂ) * X *
        (U : Matrix d d ℂ).conjTranspose) =
      (U : Matrix d d ℂ) * QIT.psdSqrt X *
        (U : Matrix d d ℂ).conjTranspose := by
  let S : Matrix d d ℂ :=
    (U : Matrix d d ℂ) * QIT.psdSqrt X *
      (U : Matrix d d ℂ).conjTranspose
  have hU : (U : Matrix d d ℂ).conjTranspose *
      (U : Matrix d d ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  have hSsq : S * S =
      (U : Matrix d d ℂ) * X * (U : Matrix d d ℂ).conjTranspose := by
    calc
      S * S =
          (U : Matrix d d ℂ) * QIT.psdSqrt X *
            ((U : Matrix d d ℂ).conjTranspose * (U : Matrix d d ℂ)) *
              QIT.psdSqrt X * (U : Matrix d d ℂ).conjTranspose := by
        dsimp [S]
        noncomm_ring
      _ = (U : Matrix d d ℂ) *
          (QIT.psdSqrt X * QIT.psdSqrt X) *
            (U : Matrix d d ℂ).conjTranspose := by
        rw [hU]
        noncomm_ring
      _ = (U : Matrix d d ℂ) * X *
          (U : Matrix d d ℂ).conjTranspose := by
        rw [QIT.psdSqrt_mul_self_of_posSemidef hX]
  have hSpos : S.PosSemidef := by
    exact (QIT.psdSqrt_pos X).mul_mul_conjTranspose_same
      (U : Matrix d d ℂ)
  change QIT.psdSqrt ((U : Matrix d d ℂ) * X *
      (U : Matrix d d ℂ).conjTranspose) = S
  simpa [QIT.psdSqrt, S] using
    (CFC.sqrt_unique
      (a := (U : Matrix d d ℂ) * X *
        (U : Matrix d d ℂ).conjTranspose)
      (b := S) hSsq hSpos.nonneg)

/-- Closed formula used to establish continuity of the entropy functional
calculus scalar. -/
theorem psdEntropyCfcScalar_eq_neg_mul_log_div (x : ℝ) :
    psdEntropyCfcScalar x = -(x * Real.log x / Real.log 2) := by
  unfold psdEntropyCfcScalar QIT.xlog2 QIT.log2
  by_cases hx : x = 0
  · simp [hx]
  · simp [hx]
    ring

/-- Continuity of the scalar used in the functional-calculus representation
of `psdEntropy`. -/
theorem continuous_psdEntropyCfcScalar : Continuous psdEntropyCfcScalar := by
  rw [show psdEntropyCfcScalar =
      (fun x : ℝ => -(x * Real.log x / Real.log 2)) by
    funext x
    exact psdEntropyCfcScalar_eq_neg_mul_log_div x]
  exact (Real.continuous_mul_log.div_const _).neg

/-- Spectral entropy is invariant under unitary conjugation, without a
trace-one assumption. -/
theorem psdEntropy_unitary_conj
    {d : Type} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (X : Matrix d d ℂ)
    (hX : X.PosSemidef) :
    psdEntropy ((U : Matrix d d ℂ) * X *
        (U : Matrix d d ℂ).conjTranspose)
        (hX.mul_mul_conjTranspose_same (U : Matrix d d ℂ)) =
      psdEntropy X hX := by
  have hcfc : cfc psdEntropyCfcScalar
      ((U : Matrix d d ℂ) * X * (U : Matrix d d ℂ).conjTranspose) =
      (U : Matrix d d ℂ) * cfc psdEntropyCfcScalar X *
        (U : Matrix d d ℂ).conjTranspose := by
    simpa [Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      (StarAlgHomClass.map_cfc
        (Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) U)
        psdEntropyCfcScalar X
        (hf := continuous_psdEntropyCfcScalar.continuousOn)
        (hφ := by
          change Continuous fun A : Matrix d d ℂ =>
            (U : Matrix d d ℂ) * A * (U : Matrix d d ℂ).conjTranspose
          fun_prop)).symm
  rw [psdEntropy_eq_cfc_trace, psdEntropy_eq_cfc_trace, hcfc]
  have hU : (U : Matrix d d ℂ).conjTranspose *
      (U : Matrix d d ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  rw [Matrix.trace_mul_cycle, hU, Matrix.one_mul]

/-- `psdEntropy` respects equality of its matrix argument; the positivity
witnesses disappear by proof irrelevance. -/
theorem psdEntropy_congr
    {d : Type} [Fintype d] [DecidableEq d]
    {X Y : Matrix d d ℂ} (hXY : X = Y)
    (hX : X.PosSemidef) (hY : Y.PosSemidef) :
    psdEntropy X hX = psdEntropy Y hY := by
  subst Y
  rfl

/-- Block-diagonal unitary `U ⊕ U`. -/
def doubledUnitary
    {d : Type} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) : Matrix.unitaryGroup (Sum d d) ℂ :=
  ⟨Matrix.fromBlocks (U : Matrix d d ℂ) 0 0 (U : Matrix d d ℂ), by
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.conjTranspose_zero, Matrix.fromBlocks_multiply]
    have hUU : (U : Matrix d d ℂ) *
        (U : Matrix d d ℂ).conjTranspose = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Matrix.mem_unitaryGroup_iff.mp U.2
    rw [hUU]
    simp⟩

/-- The entropy coupling transforms by the doubled unitary when all three
arguments are conjugated simultaneously. -/
theorem entropyCoupling_unitary_conj
    {d : Type} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ)
    (P Q R : Matrix d d ℂ)
    (hQ : Q.PosSemidef) (hR : R.PosSemidef) :
    entropyCoupling
        ((U : Matrix d d ℂ) * P * (U : Matrix d d ℂ).conjTranspose)
        ((U : Matrix d d ℂ) * Q * (U : Matrix d d ℂ).conjTranspose)
        ((U : Matrix d d ℂ) * R * (U : Matrix d d ℂ).conjTranspose) =
      (doubledUnitary U : Matrix (Sum d d) (Sum d d) ℂ) *
        entropyCoupling P Q R *
          (doubledUnitary U : Matrix (Sum d d) (Sum d d) ℂ).conjTranspose := by
  let Uc : Matrix d d ℂ := U
  have hU : Uc.conjTranspose * Uc = 1 := by
    simpa [Uc, Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  rw [show (doubledUnitary U : Matrix (Sum d d) (Sum d d) ℂ) =
      Matrix.fromBlocks Uc 0 0 Uc by rfl]
  unfold entropyCoupling
  rw [psdSqrt_unitary_conj U Q hQ, psdSqrt_unitary_conj U R hR]
  rw [Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply,
    Matrix.fromBlocks_multiply]
  simp only [Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul,
    add_zero, zero_add]
  congr 1
  · dsimp [Uc]
    noncomm_ring
  · dsimp [Uc]
    rw [show
      ((U : Matrix d d ℂ) * QIT.psdSqrt Q *
          (U : Matrix d d ℂ).conjTranspose) *
        ((U : Matrix d d ℂ) * QIT.psdSqrt R *
          (U : Matrix d d ℂ).conjTranspose) =
        (U : Matrix d d ℂ) * QIT.psdSqrt Q *
          ((U : Matrix d d ℂ).conjTranspose * (U : Matrix d d ℂ)) *
          QIT.psdSqrt R * (U : Matrix d d ℂ).conjTranspose by
      noncomm_ring]
    rw [hU]
    noncomm_ring
  · dsimp [Uc]
    rw [show
      ((U : Matrix d d ℂ) * QIT.psdSqrt R *
          (U : Matrix d d ℂ).conjTranspose) *
        ((U : Matrix d d ℂ) * QIT.psdSqrt Q *
          (U : Matrix d d ℂ).conjTranspose) =
        (U : Matrix d d ℂ) * QIT.psdSqrt R *
          ((U : Matrix d d ℂ).conjTranspose * (U : Matrix d d ℂ)) *
          QIT.psdSqrt Q * (U : Matrix d d ℂ).conjTranspose by
      noncomm_ring]
    rw [hU]
    noncomm_ring

/-- The manuscript entropy defect is invariant under simultaneous unitary
conjugation of all three matrix arguments. -/
theorem entropyDefect_unitary_conj
    {d : Type} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ)
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef) :
    entropyDefect
        ((U : Matrix d d ℂ) * P * (U : Matrix d d ℂ).conjTranspose)
        ((U : Matrix d d ℂ) * Q * (U : Matrix d d ℂ).conjTranspose)
        ((U : Matrix d d ℂ) * R * (U : Matrix d d ℂ).conjTranspose)
        (hP.mul_mul_conjTranspose_same (U : Matrix d d ℂ))
        (hQ.mul_mul_conjTranspose_same (U : Matrix d d ℂ))
        (hR.mul_mul_conjTranspose_same (U : Matrix d d ℂ)) =
      entropyDefect P Q R hP hQ hR := by
  let UP := (U : Matrix d d ℂ) * P * (U : Matrix d d ℂ).conjTranspose
  let UQ := (U : Matrix d d ℂ) * Q * (U : Matrix d d ℂ).conjTranspose
  let UR := (U : Matrix d d ℂ) * R * (U : Matrix d d ℂ).conjTranspose
  let hUP : UP.PosSemidef := hP.mul_mul_conjTranspose_same (U : Matrix d d ℂ)
  let hUQ : UQ.PosSemidef := hQ.mul_mul_conjTranspose_same (U : Matrix d d ℂ)
  let hUR : UR.PosSemidef := hR.mul_mul_conjTranspose_same (U : Matrix d d ℂ)
  have hcoupling : entropyCoupling UP UQ UR =
      (doubledUnitary U : Matrix (Sum d d) (Sum d d) ℂ) *
        entropyCoupling P Q R *
          (doubledUnitary U : Matrix (Sum d d) (Sum d d) ℂ).conjTranspose := by
    exact entropyCoupling_unitary_conj U P Q R hQ hR
  have hcouplingEntropy :
      psdEntropy (entropyCoupling UP UQ UR)
          (entropyCoupling_posSemidef UP UQ UR hUP hUQ hUR) =
        psdEntropy (entropyCoupling P Q R)
          (entropyCoupling_posSemidef P Q R hP hQ hR) := by
    calc
      _ = psdEntropy
          ((doubledUnitary U : Matrix (Sum d d) (Sum d d) ℂ) *
            entropyCoupling P Q R *
              (doubledUnitary U : Matrix (Sum d d) (Sum d d) ℂ).conjTranspose)
          ((entropyCoupling_posSemidef P Q R hP hQ hR).mul_mul_conjTranspose_same
            (doubledUnitary U : Matrix (Sum d d) (Sum d d) ℂ)) :=
        psdEntropy_congr hcoupling _ _
      _ = _ := psdEntropy_unitary_conj (doubledUnitary U)
        (entropyCoupling P Q R)
        (entropyCoupling_posSemidef P Q R hP hQ hR)
  have hPentropy : psdEntropy UP hUP = psdEntropy P hP :=
    psdEntropy_unitary_conj U P hP
  have hQentropy : psdEntropy UQ hUQ = psdEntropy Q hQ :=
    psdEntropy_unitary_conj U Q hQ
  have hRentropy : psdEntropy UR hUR = psdEntropy R hR :=
    psdEntropy_unitary_conj U R hR
  change entropyDefect UP UQ UR hUP hUQ hUR = _
  unfold entropyDefect
  rw [hcouplingEntropy, hPentropy, hQentropy, hRentropy]

/-- The entropy defect respects equality of all three matrix arguments. -/
theorem entropyDefect_congr
    {d : Type} [Fintype d] [DecidableEq d]
    {P₀ Q₀ R₀ P₁ Q₁ R₁ : Matrix d d ℂ}
    (hP : P₀ = P₁) (hQ : Q₀ = Q₁) (hR : R₀ = R₁)
    (hP₀ : P₀.PosSemidef) (hQ₀ : Q₀.PosSemidef) (hR₀ : R₀.PosSemidef)
    (hP₁ : P₁.PosSemidef) (hQ₁ : Q₁.PosSemidef) (hR₁ : R₁.PosSemidef) :
    entropyDefect P₀ Q₀ R₀ hP₀ hQ₀ hR₀ =
      entropyDefect P₁ Q₁ R₁ hP₁ hQ₁ hR₁ := by
  subst P₁
  subst Q₁
  subst R₁
  rfl

/-- If a unitary fixes the middle matrix, simultaneous conjugation of the
two outer matrices leaves the fixed-middle entropy defect unchanged. -/
theorem entropyDefect_unitary_conj_fixedMiddle
    {d : Type} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ)
    (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef)
    (hUQ : (U : Matrix d d ℂ) * Q *
      (U : Matrix d d ℂ).conjTranspose = Q) :
    entropyDefect
        ((U : Matrix d d ℂ) * P * (U : Matrix d d ℂ).conjTranspose)
        Q
        ((U : Matrix d d ℂ) * R * (U : Matrix d d ℂ).conjTranspose)
        (hP.mul_mul_conjTranspose_same (U : Matrix d d ℂ)) hQ
        (hR.mul_mul_conjTranspose_same (U : Matrix d d ℂ)) =
      entropyDefect P Q R hP hQ hR := by
  let UP := (U : Matrix d d ℂ) * P * (U : Matrix d d ℂ).conjTranspose
  let UQ := (U : Matrix d d ℂ) * Q * (U : Matrix d d ℂ).conjTranspose
  let UR := (U : Matrix d d ℂ) * R * (U : Matrix d d ℂ).conjTranspose
  let hUP : UP.PosSemidef := hP.mul_mul_conjTranspose_same (U : Matrix d d ℂ)
  let hUQpos : UQ.PosSemidef := hQ.mul_mul_conjTranspose_same (U : Matrix d d ℂ)
  let hUR : UR.PosSemidef := hR.mul_mul_conjTranspose_same (U : Matrix d d ℂ)
  change entropyDefect UP Q UR hUP hQ hUR = _
  calc
    _ = entropyDefect UP UQ UR hUP hUQpos hUR :=
      entropyDefect_congr rfl hUQ.symm rfl hUP hQ hUR hUP hUQpos hUR
    _ = _ := entropyDefect_unitary_conj U P Q R hP hQ hR

/-- The complex sign associated with a Boolean phase choice. -/
def signValue (b : Bool) : ℂ := if b then -1 else 1

@[simp]
theorem signValue_mul_self (b : Bool) : signValue b * signValue b = 1 := by
  cases b <;> simp [signValue]

@[simp]
theorem star_signValue (b : Bool) : star (signValue b) = signValue b := by
  cases b <;> simp [signValue]

theorem signValue_eq_boolSignComplex (b : Bool) :
    signValue b = QIT.State.boolSignComplex b := rfl

/-- Diagonal unitary with independently chosen signs on the fixed basis. -/
def signUnitary
    {d : Type} [Fintype d] [DecidableEq d]
    (epsilon : d → Bool) : Matrix.unitaryGroup d ℂ :=
  ⟨Matrix.diagonal (fun i => signValue (epsilon i)), by
    rw [Matrix.mem_unitaryGroup_iff]
    simp only [Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst j
      simp
    · simp [hij]⟩

/-- Every sign unitary fixes diagonal matrices under conjugation. -/
theorem signUnitary_conj_diagonal
    {d : Type} [Fintype d] [DecidableEq d]
    (epsilon : d → Bool) (q : d → ℂ) :
    (signUnitary epsilon : Matrix d d ℂ) * Matrix.diagonal q *
        (signUnitary epsilon : Matrix d d ℂ).conjTranspose =
      Matrix.diagonal q := by
  change Matrix.diagonal (fun i => signValue (epsilon i)) *
      Matrix.diagonal q *
        (Matrix.diagonal (fun i => signValue (epsilon i))).conjTranspose =
    Matrix.diagonal q
  rw [Matrix.diagonal_conjTranspose]
  simp only [Matrix.diagonal_mul_diagonal]
  ext i j
  by_cases hij : i = j
  · subst j
    cases h : epsilon i <;> simp [signValue, h]
  · simp [hij]

/-- Sign conjugations preserve the entropy defect when the fixed middle
matrix is diagonal in the chosen basis. -/
theorem entropyDefect_signUnitary_conj_diagonalMiddle
    {d : Type} [Fintype d] [DecidableEq d]
    (epsilon : d → Bool) (q : d → ℂ)
    (P R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : (Matrix.diagonal q).PosSemidef)
    (hR : R.PosSemidef) :
    entropyDefect
        ((signUnitary epsilon : Matrix d d ℂ) * P *
          (signUnitary epsilon : Matrix d d ℂ).conjTranspose)
        (Matrix.diagonal q)
        ((signUnitary epsilon : Matrix d d ℂ) * R *
          (signUnitary epsilon : Matrix d d ℂ).conjTranspose)
        (hP.mul_mul_conjTranspose_same (signUnitary epsilon : Matrix d d ℂ))
        hQ
        (hR.mul_mul_conjTranspose_same (signUnitary epsilon : Matrix d d ℂ)) =
      entropyDefect P (Matrix.diagonal q) R hP hQ hR := by
  exact entropyDefect_unitary_conj_fixedMiddle
    (signUnitary epsilon) P (Matrix.diagonal q) R hP hQ hR
    (signUnitary_conj_diagonal epsilon q)

/-- Entrywise action of conjugation by a diagonal sign unitary. -/
theorem signUnitary_conj_apply
    {d : Type} [Fintype d] [DecidableEq d]
    (epsilon : d → Bool) (X : Matrix d d ℂ) (i j : d) :
    (((signUnitary epsilon : Matrix d d ℂ) * X *
        (signUnitary epsilon : Matrix d d ℂ).conjTranspose) i j) =
      signValue (epsilon i) * X i j * signValue (epsilon j) := by
  change
    (Matrix.diagonal (fun k => signValue (epsilon k)) * X *
      (Matrix.diagonal (fun k => signValue (epsilon k))).conjTranspose) i j = _
  rw [Matrix.diagonal_conjTranspose, Matrix.mul_diagonal,
    Matrix.diagonal_mul]
  simp

/-- The finite average over all diagonal sign conjugations.  The scalar is
real so that this expression is directly usable by the real convexity API. -/
def signTwirl
    {d : Type} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) : Matrix d d ℂ :=
  ((Fintype.card (d → Bool) : ℝ)⁻¹) •
    ∑ epsilon : d → Bool,
      (signUnitary epsilon : Matrix d d ℂ) * X *
        (signUnitary epsilon : Matrix d d ℂ).conjTranspose

/-- Sign averaging keeps diagonal entries and kills off-diagonal entries. -/
theorem signTwirl_apply
    {d : Type} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) (i j : d) :
    signTwirl X i j = if i = j then X i j else 0 := by
  classical
  by_cases hij : i = j
  · subst j
    unfold signTwirl
    simp only [Matrix.smul_apply, Matrix.sum_apply]
    simp_rw [signUnitary_conj_apply]
    have hsum :
        (∑ epsilon : d → Bool,
          signValue (epsilon i) * X i i * signValue (epsilon i)) =
            (Fintype.card (d → Bool) : ℂ) * X i i := by
      simp_rw [signValue_eq_boolSignComplex]
      calc
        _ = (∑ epsilon : d → Bool,
              QIT.State.boolSignComplex (epsilon i) *
                QIT.State.boolSignComplex (epsilon i)) * X i i := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro epsilon _
          ring
        _ = (Fintype.card (d → Bool) : ℂ) * X i i := by
          rw [QIT.State.boolSignComplex_sum_mul_eq_card]
    rw [hsum]
    simp
  · have hzero :
      (∑ epsilon : d → Bool,
        signValue (epsilon i) * X i j * signValue (epsilon j)) = 0 := by
      simp_rw [signValue_eq_boolSignComplex]
      calc
        _ = X i j *
            (∑ epsilon : d → Bool,
              QIT.State.boolSignComplex (epsilon i) *
                QIT.State.boolSignComplex (epsilon j)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro epsilon _
          ring
        _ = 0 := by
          rw [QIT.State.boolSignComplex_sum_mul_eq_zero_of_ne hij, mul_zero]
    unfold signTwirl
    simp only [Matrix.smul_apply, Matrix.sum_apply]
    simp_rw [signUnitary_conj_apply]
    simp [hij, hzero]

/-- Basis dephasing: retain exactly the diagonal entries of a matrix. -/
def matrixDephase
    {d : Type} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) : Matrix d d ℂ :=
  Matrix.diagonal fun i => X i i

@[simp]
theorem matrixDephase_apply
    {d : Type} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) (i j : d) :
    matrixDephase X i j = if i = j then X i j else 0 := by
  by_cases hij : i = j
  · subst j
    simp [matrixDephase]
  · simp [matrixDephase, hij]

/-- The diagonal sign twirl is exactly basis dephasing. -/
theorem signTwirl_eq_matrixDephase
    {d : Type} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) :
    signTwirl X = matrixDephase X := by
  ext i j
  rw [signTwirl_apply, matrixDephase_apply]

/-- Dephasing preserves positive semidefiniteness. -/
theorem matrixDephase_posSemidef
    {d : Type} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) (hX : X.PosSemidef) :
    (matrixDephase X).PosSemidef := by
  exact Matrix.PosSemidef.diagonal fun i => hX.diag_nonneg

/-- Dephasing the two outer arguments cannot increase the entropy defect when
the fixed middle argument is diagonal. -/
theorem entropyDefect_matrixDephase_le
    {d : Type} [Fintype d] [DecidableEq d]
    (q : d → ℂ) (P R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : (Matrix.diagonal q).PosSemidef)
    (hR : R.PosSemidef) :
    entropyDefect (matrixDephase P) (Matrix.diagonal q) (matrixDephase R)
        (matrixDephase_posSemidef P hP) hQ
        (matrixDephase_posSemidef R hR) ≤
      entropyDefect P (Matrix.diagonal q) R hP hQ hR := by
  classical
  let w : (d → Bool) → ℝ := fun _ =>
    (Fintype.card (d → Bool) : ℝ)⁻¹
  let X : (d → Bool) → Matrix d d ℂ × Matrix d d ℂ := fun epsilon =>
    (((signUnitary epsilon : Matrix d d ℂ) * P *
        (signUnitary epsilon : Matrix d d ℂ).conjTranspose),
      ((signUnitary epsilon : Matrix d d ℂ) * R *
        (signUnitary epsilon : Matrix d d ℂ).conjTranspose))
  have hw : ∀ epsilon ∈ (Finset.univ : Finset (d → Bool)),
      0 ≤ w epsilon := by
    intro epsilon _
    simp [w]
  have hsum : ∑ epsilon ∈ (Finset.univ : Finset (d → Bool)),
      w epsilon = 1 := by
    simp [w]
  have hX : ∀ epsilon ∈ (Finset.univ : Finset (d → Bool)),
      (X epsilon).1.PosSemidef ∧ (X epsilon).2.PosSemidef := by
    intro epsilon _
    exact ⟨
      hP.mul_mul_conjTranspose_same (signUnitary epsilon : Matrix d d ℂ),
      hR.mul_mul_conjTranspose_same (signUnitary epsilon : Matrix d d ℂ)⟩
  have havg :
      (∑ epsilon ∈ (Finset.univ : Finset (d → Bool)), w epsilon • X epsilon) =
        (signTwirl P, signTwirl R) := by
    apply Prod.ext
    · simp only [Prod.fst_sum, Prod.smul_fst]
      simp [w, X, signTwirl, Finset.smul_sum]
    · simp only [Prod.snd_sum, Prod.smul_snd]
      simp [w, X, signTwirl, Finset.smul_sum]
  have hvalue (epsilon : d → Bool) :
      entropyDefectTotal (Matrix.diagonal q) hQ (X epsilon) =
        entropyDefect P (Matrix.diagonal q) R hP hQ hR := by
    have hXP : (X epsilon).1.PosSemidef :=
      hP.mul_mul_conjTranspose_same (signUnitary epsilon : Matrix d d ℂ)
    have hXR : (X epsilon).2.PosSemidef :=
      hR.mul_mul_conjTranspose_same (signUnitary epsilon : Matrix d d ℂ)
    rw [show entropyDefectTotal (Matrix.diagonal q) hQ (X epsilon) =
        entropyDefect (X epsilon).1 (Matrix.diagonal q) (X epsilon).2
          hXP hQ hXR by
      simp [entropyDefectTotal, hXP, hXR]]
    exact entropyDefect_signUnitary_conj_diagonalMiddle
      epsilon q P R hP hQ hR
  have hjensen := entropyDefectTotal_map_sum_le
    (Matrix.diagonal q) hQ (Finset.univ : Finset (d → Bool)) w X
      hw hsum hX
  rw [havg] at hjensen
  have hleft :
      entropyDefectTotal (Matrix.diagonal q) hQ
          (signTwirl P, signTwirl R) =
        entropyDefect (matrixDephase P) (Matrix.diagonal q) (matrixDephase R)
          (matrixDephase_posSemidef P hP) hQ
          (matrixDephase_posSemidef R hR) := by
    rw [signTwirl_eq_matrixDephase, signTwirl_eq_matrixDephase]
    simp [entropyDefectTotal, matrixDephase_posSemidef P hP,
      matrixDephase_posSemidef R hR]
  rw [hleft] at hjensen
  calc
    _ ≤ ∑ epsilon ∈ (Finset.univ : Finset (d → Bool)),
        w epsilon • entropyDefectTotal (Matrix.diagonal q) hQ (X epsilon) :=
      hjensen
    _ = _ := by
      simp_rw [hvalue]
      simp [w]

end

end AmplitudeDamping
