import AmplitudeDamping.PureAuxiliary
import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm.Complement

/-!
# The triangular Gram matrix as a product-channel output

This module identifies the rectangular triangular matrix arising from a pure
input with a Kraus coefficient matrix for amplitude damping tensored with an
arbitrary auxiliary channel.  The only discrepancy is the harmless ordering
of the two qubit output and Kraus labels.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

universe u v w

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- The triangular matrix lists the excited output block before the ground
output block, whereas `Prod Qubit b` uses the computational order `0,1`. -/
def pureAuxiliaryOutputEquiv (b : Type v) : Sum b b ≃ Prod Qubit b where
  toFun
    | Sum.inl y => (1, y)
    | Sum.inr y => (0, y)
  invFun z := if z.1 = 1 then Sum.inl z.2 else Sum.inr z.2
  left_inv z := by cases z <;> simp
  right_inv z := by
    rcases z with ⟨i, y⟩
    fin_cases i <;> simp

/-- The two column blocks are respectively the no-jump and jump Kraus labels. -/
def pureAuxiliaryKrausEquiv (k : Type w) : Sum k k ≃ Prod (Fin 2) k where
  toFun
    | Sum.inl z => (0, z)
    | Sum.inr z => (1, z)
  invFun z := if z.1 = 0 then Sum.inl z.2 else Sum.inr z.2
  left_inv z := by cases z <;> simp
  right_inv z := by
    rcases z with ⟨i, y⟩
    fin_cases i <;> simp

/-- Coefficient matrix for the explicit product Kraus family. -/
def pureAuxiliaryProductCoefficientMatrix
    (p : ℝ) (Phi : Channel a b) (psi : PureVector (Prod Qubit a)) :
    Matrix (Prod Qubit b) (Prod (Fin 2) (Prod a b)) ℂ :=
  fun y k => ∑ x : Prod Qubit a,
    MatrixMap.krausProduct (amplitudeKraus p) Phi.kraus k y x * psi.amp x

theorem pureAuxiliary_triangularCoefficient_reindex
    (p : ℝ) (Phi : Channel a b) (psi : PureVector (Prod Qubit a)) :
    let A := Phi.stinespringCoefficientMatrix (pureExcitedBranch psi)
    let B := Phi.stinespringCoefficientMatrix (pureGroundBranch psi)
    let M : Matrix (Sum b b) (Sum (Prod a b) (Prod a b)) ℂ :=
      Matrix.fromBlocks ((Real.sqrt (1 - p) : ℂ) • A) 0 B
        ((Real.sqrt p : ℂ) • A)
    M.submatrix (pureAuxiliaryOutputEquiv b).symm
        (pureAuxiliaryKrausEquiv (Prod a b)).symm =
      pureAuxiliaryProductCoefficientMatrix p Phi psi := by
  dsimp only
  ext y k
  rcases y with ⟨i, y⟩
  rcases k with ⟨j, k⟩
  fin_cases i <;> fin_cases j <;>
    simp [pureAuxiliaryProductCoefficientMatrix, MatrixMap.krausProduct,
      amplitudeKraus, amplitudeKrausZero, amplitudeKrausOne,
      pureAuxiliaryOutputEquiv, pureAuxiliaryKrausEquiv,
      Matrix.kronecker, Matrix.kroneckerMap_apply,
      pureExcitedBranch, pureGroundBranch,
      Channel.stinespringCoefficientMatrix, Fintype.sum_prod_type,
      Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      Finset.mul_sum, mul_assoc]

/-- The explicit product-Kraus coefficient matrix has as its row Gram matrix
the output of the product channel on the pure input. -/
theorem pureAuxiliaryProductCoefficientMatrix_gram
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Phi : Channel a b) (psi : PureVector (Prod Qubit a)) :
    let C := pureAuxiliaryProductCoefficientMatrix p Phi psi
    C * C.conjTranspose =
      (((amplitudeDamping p hp0 hp1).prod Phi).applyState psi.state).matrix := by
  dsimp only
  change _ = MatrixMap.kron (MatrixMap.ofKraus (amplitudeKraus p))
    Phi.map (rankOneMatrix psi.amp)
  rw [Phi.map_eq_ofKraus,
    MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct]
  ext y z
  simp only [pureAuxiliaryProductCoefficientMatrix, Matrix.mul_apply,
    Matrix.conjTranspose_apply, MatrixMap.ofKraus, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply, rankOneMatrix_apply]
  apply Finset.sum_congr rfl
  intro k _
  change (∑ x, MatrixMap.krausProduct (amplitudeKraus p) Phi.kraus k y x *
      psi.amp x) *
      (starRingEnd ℂ) (∑ x, MatrixMap.krausProduct (amplitudeKraus p)
        Phi.kraus k z x * psi.amp x) = _
  rw [map_sum (starRingEnd ℂ)]
  simp only [map_mul, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
  apply Finset.sum_congr rfl
  intro x _
  apply Finset.sum_congr rfl
  intro x' _
  ring

/-- After swapping the two output blocks, the triangular row Gram matrix is
exactly the density matrix produced by the product channel. -/
theorem pureAuxiliary_triangularGram_eq_productOutput
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Phi : Channel a b) (psi : PureVector (Prod Qubit a)) :
    let A := Phi.stinespringCoefficientMatrix (pureExcitedBranch psi)
    let B := Phi.stinespringCoefficientMatrix (pureGroundBranch psi)
    let M : Matrix (Sum b b) (Sum (Prod a b) (Prod a b)) ℂ :=
      Matrix.fromBlocks ((Real.sqrt (1 - p) : ℂ) • A) 0 B
        ((Real.sqrt p : ℂ) • A)
    (M * M.conjTranspose).submatrix
        (pureAuxiliaryOutputEquiv b).symm
        (pureAuxiliaryOutputEquiv b).symm =
      (((amplitudeDamping p hp0 hp1).prod Phi).applyState psi.state).matrix := by
  dsimp only
  let M : Matrix (Sum b b) (Sum (Prod a b) (Prod a b)) ℂ :=
    Matrix.fromBlocks
      ((Real.sqrt (1 - p) : ℂ) •
        Phi.stinespringCoefficientMatrix (pureExcitedBranch psi))
      0
      (Phi.stinespringCoefficientMatrix (pureGroundBranch psi))
      ((Real.sqrt p : ℂ) •
        Phi.stinespringCoefficientMatrix (pureExcitedBranch psi))
  let C := pureAuxiliaryProductCoefficientMatrix p Phi psi
  have hMC : M.submatrix (pureAuxiliaryOutputEquiv b).symm
      (pureAuxiliaryKrausEquiv (Prod a b)).symm = C := by
    exact pureAuxiliary_triangularCoefficient_reindex p Phi psi
  calc
    (M * M.conjTranspose).submatrix
        (pureAuxiliaryOutputEquiv b).symm
        (pureAuxiliaryOutputEquiv b).symm =
      M.submatrix (pureAuxiliaryOutputEquiv b).symm
          (pureAuxiliaryKrausEquiv (Prod a b)).symm *
        (M.submatrix (pureAuxiliaryOutputEquiv b).symm
          (pureAuxiliaryKrausEquiv (Prod a b)).symm).conjTranspose := by
            rw [Matrix.conjTranspose_submatrix,
              Matrix.submatrix_mul_equiv]
    _ = C * C.conjTranspose := by rw [hMC]
    _ = (((amplitudeDamping p hp0 hp1).prod Phi).applyState
          psi.state).matrix :=
      pureAuxiliaryProductCoefficientMatrix_gram p hp0 hp1 Phi psi

/-- Pure-input output entropy bound for amplitude damping tensored with an
arbitrary finite-dimensional auxiliary channel. -/
theorem pureAuxiliary_productOutput_entropy_lower_bound
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (Phi : Channel a b) (psi : PureVector (Prod Qubit a)) :
    (((amplitudeDamping p hp0 hp1).prod Phi).applyState psi.state).vonNeumann ≥
      dampingEntropyCurve p (pureAuxiliaryExcitation psi) +
        normalizedGramEntropy (pureAuxiliaryExcitation psi)
          (Phi.stinespringCoefficientMatrix (pureExcitedBranch psi)) +
        normalizedGramEntropy (1 - pureAuxiliaryExcitation psi)
          (Phi.stinespringCoefficientMatrix (pureGroundBranch psi)) := by
  let A := Phi.stinespringCoefficientMatrix (pureExcitedBranch psi)
  let B := Phi.stinespringCoefficientMatrix (pureGroundBranch psi)
  let M : Matrix (Sum b b) (Sum (Prod a b) (Prod a b)) ℂ :=
    Matrix.fromBlocks ((Real.sqrt (1 - p) : ℂ) • A) 0 B
      ((Real.sqrt p : ℂ) • A)
  have hgram := pureAuxiliary_triangularGram_eq_productOutput
    p hp0 hp1 Phi psi
  have hent := psdEntropy_reindex (M * M.conjTranspose)
    (Matrix.posSemidef_self_mul_conjTranspose M)
    (pureAuxiliaryOutputEquiv b)
  have htri := pureAuxiliary_triangularCoefficient_bound p hp0 hp1 Phi psi
  have hreindexed :
      psdEntropy
          ((M * M.conjTranspose).submatrix
            (pureAuxiliaryOutputEquiv b).symm
            (pureAuxiliaryOutputEquiv b).symm)
          ((Matrix.posSemidef_self_mul_conjTranspose M).submatrix
            (pureAuxiliaryOutputEquiv b).symm) =
        (((amplitudeDamping p hp0 hp1).prod Phi).applyState
          psi.state).vonNeumann := by
    calc
      _ = psdEntropy
          (((amplitudeDamping p hp0 hp1).prod Phi).applyState
            psi.state).matrix
          (((amplitudeDamping p hp0 hp1).prod Phi).applyState
            psi.state).pos := psdEntropy_congr hgram _ _
      _ = _ := psdEntropy_state _
  have hout :
      (((amplitudeDamping p hp0 hp1).prod Phi).applyState
          psi.state).vonNeumann =
        psdEntropy (M * M.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose M) :=
    hreindexed.symm.trans hent
  change psdEntropy (M * M.conjTranspose)
      (Matrix.posSemidef_self_mul_conjTranspose M) ≥ _ at htri
  rw [← hout] at htri
  exact htri

end

end AmplitudeDamping
