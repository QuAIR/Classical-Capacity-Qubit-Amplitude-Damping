import AmplitudeDamping.Wootters
import AmplitudeDamping.BipartiteReassociation
import AmplitudeDamping.Triangular.Rectangular

/-!
# Strong superadditivity of the entanglement of formation (Theorem 6)

Manuscript §5, Theorem 6, in the gauge-fixed formulation: if the two-qubit
marginal `ρ_AB` of a state `Ω` on `AA' ⊗ BB'` has vanishing `|01⟩`
population, then

`E_F(ρ_AB) + E_F(σ_A'B') ≤ E_F(Ω)`,

where `ρ_AB` and `σ_A'B'` are the two marginals of the reassociated state.
The hypothesis `ρ_AB |01⟩ = 0` is the form reached from a general
product-kernel vector by local unitaries; that reduction is kept out of this
module, and every statement here takes the gauge condition explicitly.

The proof follows the paper.  For a pure `Ω = Ψ` with all `|01⟩`-branch
amplitudes zero, the coefficient matrix `T` of `Ψ` (rows `AA'`, columns
`BB'`) is lower triangular in the `qubit ⊗ X ∼ X ⊕ X` basis ordering, with
blocks `A`, `B`, `D : A' ↦ B'`.  The repository's triangular block entropy
inequality bounds the `AA'` marginal entropy below by the concurrence curve
at `2√(α γ)` plus the three normalized Gram entropies; the Wootters
corner-formula hypothesis (tracked explicitly, as in `Wootters.lean`)
identifies `E_F(ρ_AB)` with the curve at twice the `⟨00|ρ|11⟩` coherence,
which Cauchy–Schwarz bounds by the same `2√(α γ)`; and an explicit three
branch pure decomposition of `σ_A'B'` bounds `E_F(σ_A'B')` by the three
normalized Gram entropies.  The mixed case propagates the vanishing
`|01⟩` population to every positive-weight branch of an arbitrary pure
decomposition of `Ω` and applies the pure case branchwise together with
convexity (finite Jensen) of `E_F`.
-/

open scoped BigOperators NNReal ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

universe u v w₁ w₂

noncomputable section

variable {a : Type u} {c : Type v}
variable [Fintype a] [DecidableEq a]
variable [Fintype c] [DecidableEq c]

/-! ### Basis relabeling helpers -/

/-- The `qubit ⊗ X ≃ X ⊕ X` basis reordering `|0,i⟩ ↦ inl i`, `|1,i⟩ ↦ inr i`
that exposes the block structure of a coefficient matrix. -/
def qubitProdSumEquiv {a : Type u} : (Qubit × a) ≃ Sum a a where
  toFun x := if x.1 = 0 then Sum.inl x.2 else Sum.inr x.2
  invFun s := Sum.elim (fun i => (0, i)) (fun i => (1, i)) s
  left_inv x := by
    obtain ⟨q, i⟩ := x
    by_cases hq : q = 0
    · simp [hq]
    · have hq1 : q = 1 := Fin.eq_one_of_ne_zero q hq
      simp [hq, hq1]
  right_inv s := by
    cases s with
    | inl i => simp
    | inr i => simp

theorem qubitProdSumEquiv_apply_zero {x : Qubit × a} (hx : x.1 = 0) :
    qubitProdSumEquiv x = Sum.inl x.2 := by
  simp [qubitProdSumEquiv, hx]

theorem qubitProdSumEquiv_apply_one {x : Qubit × a} (hx : x.1 = 1) :
    qubitProdSumEquiv x = Sum.inr x.2 := by
  obtain ⟨q, i⟩ := x
  have hq0 : q ≠ 0 := by
    subst hx
    decide
  simp [qubitProdSumEquiv, hq0]

@[simp] theorem qubitProdSumEquiv_symm_inl (i : a) :
    qubitProdSumEquiv.symm (Sum.inl i) = (0, i) := rfl

@[simp] theorem qubitProdSumEquiv_symm_inr (i : a) :
    qubitProdSumEquiv.symm (Sum.inr i) = (1, i) := rfl

/-- Collapse a double sum of squared moduli into a single sum over the
product index. -/
theorem sum_sum_normSq_prod {α : Type w₁} {β : Type w₂}
    [Fintype α] [DecidableEq α] [Fintype β] [DecidableEq β]
    (g : α → β → ℂ) :
    ∑ i : α, ∑ j : β, Complex.normSq (g i j) =
      ∑ p : α × β, Complex.normSq (g p.1 p.2) :=
  (Fintype.sum_prod_type
    (fun p : α × β => Complex.normSq (g p.1 p.2))).symm

/-- Products commute with a simultaneous basis relabeling of both factors. -/
theorem mul_conjTranspose_reindex
    {m m' : Type u} {n n' : Type v}
    [Fintype m] [DecidableEq m] [Fintype m'] [DecidableEq m']
    [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n']
    (e : m ≃ m') (f : n ≃ n')
    (M N : Matrix m n ℂ) :
    M.reindex e f * (N.reindex e f).conjTranspose =
      (M * N.conjTranspose).reindex e e := by
  ext i' j'
  simp only [Matrix.reindex_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Matrix.submatrix_apply]
  exact Fintype.sum_equiv f.symm _ _ fun k => rfl

/-! ### Pure coefficient matrices and branch blocks -/

/-- The coefficient matrix `T` of a pure state on `AA' ⊗ BB'`: rows indexed
by `AA'`, columns by `BB'`, entries the amplitudes. -/
def pureCoefficientMatrix (ψ : PureVector ((Qubit × a) × (Qubit × c))) :
    Matrix (Qubit × a) (Qubit × c) ℂ :=
  fun s k => ψ.amp (s, k)

theorem pureCoefficientMatrix_apply
    (ψ : PureVector ((Qubit × a) × (Qubit × c))) (s : Qubit × a)
    (k : Qubit × c) :
    pureCoefficientMatrix ψ s k = ψ.amp (s, k) :=
  rfl

/-- The flattened amplitude of the branch of `Ψ` with qubit pair
`w = (q_A, q_B)`: the component of `Ψ` on `|w_A⟩|w_B⟩ ⊗ |x⟩_{A'B'}`. -/
def branchAmp (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (w : Qubit × Qubit) (x : a × c) : ℂ :=
  ψ.amp (prodReassoc.symm (w, x))

theorem branchAmp_eq (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (w : Qubit × Qubit) (i : a) (j : c) :
    branchAmp ψ w (i, j) = ψ.amp ((w.1, i), (w.2, j)) := by
  simp [branchAmp]

/-- The branch coefficient matrix `M_w : A' → B'` of the `w` branch. -/
def branchMatrix (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (w : Qubit × Qubit) : Matrix a c ℂ :=
  fun i j => branchAmp ψ w (i, j)

theorem branchMatrix_apply (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (w : Qubit × Qubit) (i : a) (j : c) :
    branchMatrix ψ w i j = ψ.amp ((w.1, i), (w.2, j)) :=
  rfl

/-- The `AA'` marginal of a pure state is the Gram matrix `T Tᴴ` of its
coefficient matrix. -/
theorem pureCoefficientMatrix_gram
    (ψ : PureVector ((Qubit × a) × (Qubit × c))) :
    ψ.state.marginalA.matrix =
      pureCoefficientMatrix ψ * (pureCoefficientMatrix ψ).conjTranspose := by
  ext s s'
  simp only [State.marginalA_matrix, partialTraceB, PureVector.state_matrix_apply,
    pureCoefficientMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply]

/-- The total squared amplitude of a pure state, as a Frobenius norm. -/
theorem pureCoefficientMatrix_frobeniusSq
    (ψ : PureVector ((Qubit × a) × (Qubit × c))) :
    frobeniusSq (pureCoefficientMatrix ψ) = 1 := by
  have hamp : ∑ s : (Qubit × a) × (Qubit × c), Complex.normSq (ψ.amp s) = 1 := by
    have h := congrArg Complex.re ψ.trace_rankOne_eq_one
    simpa [rankOneMatrix_trace, dotProduct, Complex.mul_conj] using h
  rw [frobeniusSq_eq_sum_normSq]
  calc ∑ s : Qubit × a, ∑ k : Qubit × c,
          Complex.normSq (pureCoefficientMatrix ψ s k)
      = ∑ p : (Qubit × a) × (Qubit × c), Complex.normSq (ψ.amp p) := by
        refine (sum_sum_normSq_prod _).trans ?_
        exact Finset.sum_congr rfl fun p _ => rfl
    _ = 1 := hamp

/-- The squared Frobenius norm of a branch matrix is the total squared branch
amplitude, as a single sum over `A' ⊗ B'`. -/
theorem branchMatrix_frobeniusSq
    (ψ : PureVector ((Qubit × a) × (Qubit × c))) (w : Qubit × Qubit) :
    frobeniusSq (branchMatrix ψ w) =
      ∑ x : a × c, Complex.normSq (branchAmp ψ w x) := by
  rw [frobeniusSq_eq_sum_normSq]
  exact (sum_sum_normSq_prod (branchMatrix ψ w)).trans
    (Finset.sum_congr rfl fun p _ => rfl)

/-- In the `X ⊕ X` basis ordering, the gauge-fixed coefficient matrix is
lower triangular with blocks `A`, `B`, `D`. -/
theorem pureCoefficientMatrix_reindex
    (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (hzero : ∀ i j, ψ.amp ((0, i), (1, j)) = 0) :
    (pureCoefficientMatrix ψ).reindex qubitProdSumEquiv qubitProdSumEquiv =
      Matrix.fromBlocks (branchMatrix ψ (0, 0)) 0
        (branchMatrix ψ (1, 0)) (branchMatrix ψ (1, 1)) := by
  ext s k
  rcases s with i | i <;> rcases k with j | j
  · rfl
  · exact hzero i j
  · rfl
  · rfl

/-- The `AA'` marginal entropy is the spectral entropy of the triangular
block Gram matrix. -/
theorem pure_marginalA_reindex_matrix
    (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (hzero : ∀ i j, ψ.amp ((0, i), (1, j)) = 0) :
    (ψ.state.marginalA.reindex qubitProdSumEquiv).matrix =
      Matrix.fromBlocks (branchMatrix ψ (0, 0)) 0
          (branchMatrix ψ (1, 0)) (branchMatrix ψ (1, 1)) *
        (Matrix.fromBlocks (branchMatrix ψ (0, 0)) 0
          (branchMatrix ψ (1, 0)) (branchMatrix ψ (1, 1))).conjTranspose := by
  calc (ψ.state.marginalA.reindex qubitProdSumEquiv).matrix
      = (pureCoefficientMatrix ψ *
          (pureCoefficientMatrix ψ).conjTranspose).reindex
          qubitProdSumEquiv qubitProdSumEquiv := by
        rw [State.reindex_matrix, pureCoefficientMatrix_gram]
        rfl
    _ = (pureCoefficientMatrix ψ).reindex qubitProdSumEquiv qubitProdSumEquiv *
        ((pureCoefficientMatrix ψ).reindex qubitProdSumEquiv
          qubitProdSumEquiv).conjTranspose :=
          (mul_conjTranspose_reindex qubitProdSumEquiv qubitProdSumEquiv _ _).symm
    _ = Matrix.fromBlocks (branchMatrix ψ (0, 0)) 0
          (branchMatrix ψ (1, 0)) (branchMatrix ψ (1, 1)) *
        (Matrix.fromBlocks (branchMatrix ψ (0, 0)) 0
          (branchMatrix ψ (1, 0)) (branchMatrix ψ (1, 1))).conjTranspose := by
        rw [pureCoefficientMatrix_reindex ψ hzero]

/-! ### The three-branch decomposition of the `A'B'` marginal -/

/-- The trace of a branch rank-one kernel is the branch weight. -/
theorem branchTraceRe (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (w : Qubit × Qubit) :
    (rankOneMatrix (branchAmp ψ w)).trace.re =
      frobeniusSq (branchMatrix ψ w) := by
  have hmul : ∀ z : ℂ, z * star z = ((Complex.normSq z : ℝ) : ℂ) := fun z => by
    show z * starRingEnd ℂ z = _
    rw [Complex.mul_conj]
  simp only [rankOneMatrix_trace, dotProduct, hmul]
  rw [branchMatrix_frobeniusSq, ← Complex.ofReal_sum, Complex.ofReal_re]

/-- The normalized pure vector of a nonzero branch, with an arbitrary
filler vector for zero-weight branches (whose contribution vanishes). -/
def branchVector (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (filler : PureVector (a × c)) (w : Qubit × Qubit) : PureVector (a × c) :=
  if hw : 0 < frobeniusSq (branchMatrix ψ w) then
    PureVector.normalize (branchAmp ψ w) (by rw [branchTraceRe]; exact hw)
  else filler

theorem branchVector_state_matrix (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (filler : PureVector (a × c)) (w : Qubit × Qubit)
    (hw : 0 < frobeniusSq (branchMatrix ψ w)) :
    (branchVector ψ filler w).state.matrix =
      (((frobeniusSq (branchMatrix ψ w))⁻¹ : ℝ) : ℂ) •
        rankOneMatrix (branchAmp ψ w) := by
  rw [branchVector, dif_pos hw, PureVector.normalize_state_matrix, branchTraceRe]

/-- A zero-weight branch has vanishing amplitudes. -/
theorem branchAmp_eq_zero_of_weight_zero
    (ψ : PureVector ((Qubit × a) × (Qubit × c))) (w : Qubit × Qubit)
    (hw : frobeniusSq (branchMatrix ψ w) = 0) (x : a × c) :
    branchAmp ψ w x = 0 := by
  have hsum : ∑ p : a × c, Complex.normSq (branchAmp ψ w p) = 0 := by
    rw [← branchMatrix_frobeniusSq]; exact hw
  have hnn : ∀ p ∈ Finset.univ, 0 ≤ Complex.normSq (branchAmp ψ w p) :=
    fun p _ => Complex.normSq_nonneg _
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).1 hsum x
    (Finset.mem_univ x)
  exact Complex.normSq_eq_zero.mp hterm

/-- Entries of the branch marginal, as a rescaled Gram matrix. -/
theorem branchVector_marginalA_matrix_apply
    (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (filler : PureVector (a × c)) (w : Qubit × Qubit)
    (hw : 0 < frobeniusSq (branchMatrix ψ w)) (i i' : a) :
    ((branchVector ψ filler w).state.marginalA).matrix i i' =
      (((frobeniusSq (branchMatrix ψ w))⁻¹ : ℝ) : ℂ) *
        (branchMatrix ψ w * (branchMatrix ψ w).conjTranspose) i i' := by
  have h1 : ((branchVector ψ filler w).state.marginalA).matrix =
      (((frobeniusSq (branchMatrix ψ w))⁻¹ : ℝ) : ℂ) •
        partialTraceB (rankOneMatrix (branchAmp ψ w)) := by
    rw [State.marginalA_matrix, branchVector_state_matrix ψ filler w hw,
      partialTraceB_smul]
  rw [h1]
  simp only [Matrix.smul_apply, Matrix.mul_apply, Matrix.conjTranspose_apply]
  exact congrArg _ (Finset.sum_congr rfl fun j _ => rfl)

/-- Scalar identity converting the `xlog2` correction of an inverse weight. -/
theorem xlog2_add_sq_mul_inv (t : ℝ) (ht : 0 < t) :
    QIT.xlog2 t + t * t * QIT.xlog2 t⁻¹ = 0 := by
  have hx : QIT.xlog2 t = t * QIT.log2 t := by
    rw [QIT.xlog2, if_neg (ne_of_gt ht)]
  have hy : QIT.xlog2 t⁻¹ = t⁻¹ * QIT.log2 t⁻¹ := by
    rw [QIT.xlog2, if_neg (inv_ne_zero ht.ne')]
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [hx, hy, QIT.log2, QIT.log2, Real.log_inv]
  field_simp
  ring

/-- Per-branch cost identity: the weighted branch marginal entropy is exactly
the normalized Gram entropy of the branch matrix, with the zero-weight
convention on both sides. -/
theorem branchVector_cost (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (filler : PureVector (a × c)) (w : Qubit × Qubit) :
    frobeniusSq (branchMatrix ψ w) *
        ((branchVector ψ filler w).state.marginalA).vonNeumann =
      normalizedGramEntropy (frobeniusSq (branchMatrix ψ w))
        (branchMatrix ψ w) := by
  by_cases hw : 0 < frobeniusSq (branchMatrix ψ w)
  · have hS : ((branchVector ψ filler w).state.marginalA).vonNeumann =
        psdEntropy
          ((((frobeniusSq (branchMatrix ψ w))⁻¹ : ℝ) : ℂ) •
            (branchMatrix ψ w * (branchMatrix ψ w).conjTranspose))
          ((Matrix.posSemidef_self_mul_conjTranspose (branchMatrix ψ w)).smul
            (by exact_mod_cast inv_nonneg.mpr hw.le)) := by
      calc ((branchVector ψ filler w).state.marginalA).vonNeumann
          = psdEntropy ((branchVector ψ filler w).state.marginalA).matrix
              (branchVector ψ filler w).state.marginalA.pos :=
              (psdEntropy_state _).symm
        _ = psdEntropy
              ((((frobeniusSq (branchMatrix ψ w))⁻¹ : ℝ) : ℂ) •
                (branchMatrix ψ w * (branchMatrix ψ w).conjTranspose))
              ((Matrix.posSemidef_self_mul_conjTranspose (branchMatrix ψ w)).smul
                (by exact_mod_cast inv_nonneg.mpr hw.le)) :=
              psdEntropy_congr
                (Matrix.ext fun i i' =>
                  branchVector_marginalA_matrix_apply ψ filler w hw i i') _ _
    have hsm := psdEntropy_real_smul ((frobeniusSq (branchMatrix ψ w))⁻¹)
      (inv_nonneg.mpr hw.le)
      (branchMatrix ψ w * (branchMatrix ψ w).conjTranspose)
      (Matrix.posSemidef_self_mul_conjTranspose _)
    have hgram := psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2
      (branchMatrix ψ w)
    have hscal := xlog2_add_sq_mul_inv (frobeniusSq (branchMatrix ψ w)) hw
    rw [hS, hsm]
    have hfield : frobeniusSq (branchMatrix ψ w) *
        (((frobeniusSq (branchMatrix ψ w))⁻¹ : ℝ) *
          psdEntropy (branchMatrix ψ w * (branchMatrix ψ w).conjTranspose)
            (Matrix.posSemidef_self_mul_conjTranspose _) -
          QIT.xlog2 ((frobeniusSq (branchMatrix ψ w))⁻¹) *
            (branchMatrix ψ w * (branchMatrix ψ w).conjTranspose).trace.re) =
        psdEntropy (branchMatrix ψ w * (branchMatrix ψ w).conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose _) -
        frobeniusSq (branchMatrix ψ w) *
          (QIT.xlog2 ((frobeniusSq (branchMatrix ψ w))⁻¹) *
            frobeniusSq (branchMatrix ψ w)) := by
      have hne : frobeniusSq (branchMatrix ψ w) ≠ 0 := ne_of_gt hw
      rw [show
        (branchMatrix ψ w * (branchMatrix ψ w).conjTranspose).trace.re =
          frobeniusSq (branchMatrix ψ w) from rfl]
      field_simp
    show frobeniusSq (branchMatrix ψ w) *
        (((frobeniusSq (branchMatrix ψ w))⁻¹ : ℝ) *
          psdEntropy (branchMatrix ψ w * (branchMatrix ψ w).conjTranspose)
            (Matrix.posSemidef_self_mul_conjTranspose _) -
          QIT.xlog2 ((frobeniusSq (branchMatrix ψ w))⁻¹) *
            (branchMatrix ψ w * (branchMatrix ψ w).conjTranspose).trace.re) =
        _
    rw [hfield, hgram]
    have hlast : QIT.xlog2 (frobeniusSq (branchMatrix ψ w)) +
        frobeniusSq (branchMatrix ψ w) *
          (QIT.xlog2 ((frobeniusSq (branchMatrix ψ w))⁻¹) *
            frobeniusSq (branchMatrix ψ w)) = 0 := by
      rw [← hscal]
      ring
    linarith
  · have hw0 : frobeniusSq (branchMatrix ψ w) = 0 :=
      le_antisymm (le_of_not_gt hw) (frobeniusSq_nonneg _)
    rw [hw0, zero_mul]
    simp

/-- The four branch weights sum to one. -/
theorem branchWeights_sum (ψ : PureVector ((Qubit × a) × (Qubit × c))) :
    ∑ w : Qubit × Qubit, frobeniusSq (branchMatrix ψ w) = 1 := by
  have hamp : ∑ s : (Qubit × a) × (Qubit × c), Complex.normSq (ψ.amp s) = 1 := by
    have h := congrArg Complex.re ψ.trace_rankOne_eq_one
    simpa [rankOneMatrix_trace, dotProduct, Complex.mul_conj] using h
  calc ∑ w : Qubit × Qubit, frobeniusSq (branchMatrix ψ w)
      = ∑ w : Qubit × Qubit, ∑ x : a × c,
          Complex.normSq (branchAmp ψ w x) :=
        Finset.sum_congr rfl fun w _ => branchMatrix_frobeniusSq ψ w
    _ = ∑ p : (Qubit × Qubit) × (a × c),
          Complex.normSq (branchAmp ψ p.1 p.2) :=
        sum_sum_normSq_prod (fun w x => branchAmp ψ w x)
    _ = ∑ s : (Qubit × a) × (Qubit × c), Complex.normSq (ψ.amp s) := by
        refine Fintype.sum_equiv prodReassoc _ _ fun p => ?_
        simp [branchAmp, prodReassoc_symm_apply, prodReassoc_apply]
    _ = 1 := hamp

/-! ### The σ decomposition of the `A'B'` marginal -/

/-- General entry formula for the average state of a pure decomposition. -/
theorem pureDecomposition_averageState_entry {d : Type w₁}
    [Fintype d] [DecidableEq d]
    (E : PureDecomposition d) (x y : d) :
    E.averageState.matrix x y =
      ∑ i, ((E.probs i : ℝ≥0) : ℂ) * (E.vectors i).state.matrix x y := by
  rw [PureDecomposition.averageState, Ensemble.averageState_matrix,
    Matrix.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [NNReal.smul_def]
  rfl

/-- The four-branch pure decomposition of the `A'B'` marginal of a pure
state, indexed by the qubit pair; the gauge-fixed `|01⟩` branch carries
weight zero. -/
def sigmaDecomposition (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (filler : PureVector (a × c)) : PureDecomposition (a × c) :=
  PureDecomposition.ofFinite (ι := Qubit × Qubit)
    (fun w => ⟨frobeniusSq (branchMatrix ψ w), frobeniusSq_nonneg _⟩)
    (by
      apply NNReal.coe_injective
      rw [NNReal.coe_sum]
      exact branchWeights_sum ψ)
    (branchVector ψ filler)

/-- The cost of the σ decomposition is the sum of the branch normalized
Gram entropies. -/
theorem sigmaDecomposition_entanglementCost
    (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (filler : PureVector (a × c)) :
    (sigmaDecomposition ψ filler).entanglementCost =
      ∑ w : Qubit × Qubit,
        normalizedGramEntropy (frobeniusSq (branchMatrix ψ w))
          (branchMatrix ψ w) := by
  rw [PureDecomposition.entanglementCost]
  exact Fintype.sum_equiv (Fintype.equivFin (Qubit × Qubit)).symm _ _
    fun k => branchVector_cost ψ filler _

/-- Every branch contributes exactly its flattened amplitude pair. -/
theorem sigmaDecomposition_averageState_entry
    (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (filler : PureVector (a × c)) (x y : a × c) :
    (sigmaDecomposition ψ filler).averageState.matrix x y =
      ∑ w : Qubit × Qubit,
        branchAmp ψ w x * star (branchAmp ψ w y) := by
  have hterm : ∀ w : Qubit × Qubit,
      ((⟨frobeniusSq (branchMatrix ψ w), frobeniusSq_nonneg _⟩ : ℝ≥0) : ℂ) *
          (branchVector ψ filler w).state.matrix x y =
      branchAmp ψ w x * star (branchAmp ψ w y) := by
    intro w
    by_cases hw : 0 < frobeniusSq (branchMatrix ψ w)
    · have hne : frobeniusSq (branchMatrix ψ w) ≠ 0 := ne_of_gt hw
      rw [branchVector_state_matrix ψ filler w hw, Matrix.smul_apply,
        rankOneMatrix_apply, smul_eq_mul, ← mul_assoc]
      have hc : (((⟨frobeniusSq (branchMatrix ψ w), frobeniusSq_nonneg _⟩ : ℝ≥0) : ℂ)) =
          ((frobeniusSq (branchMatrix ψ w) : ℝ) : ℂ) := rfl
      rw [hc, ← Complex.ofReal_mul, mul_inv_cancel₀ hne, Complex.ofReal_one,
        one_mul]
    · have hw0 : frobeniusSq (branchMatrix ψ w) = 0 :=
        le_antisymm (le_of_not_gt hw) (frobeniusSq_nonneg _)
      have hamp0 : branchAmp ψ w x = 0 :=
        branchAmp_eq_zero_of_weight_zero ψ w hw0 x
      simp [hw0, hamp0]
  calc (sigmaDecomposition ψ filler).averageState.matrix x y
      = ∑ w : Qubit × Qubit,
          ((⟨frobeniusSq (branchMatrix ψ w), frobeniusSq_nonneg _⟩ : ℝ≥0) : ℂ) *
            (branchVector ψ filler w).state.matrix x y := by
        rw [pureDecomposition_averageState_entry]
        exact Fintype.sum_equiv (Fintype.equivFin (Qubit × Qubit)).symm _ _
          fun k => rfl
    _ = ∑ w : Qubit × Qubit,
          branchAmp ψ w x * star (branchAmp ψ w y) :=
        Finset.sum_congr rfl fun w _ => hterm w

/-! ### Marginal entries of the reassociated bipartition -/

theorem rhoAB_matrix_apply (Ω : State ((Qubit × a) × (Qubit × c)))
    (x y : Qubit × Qubit) :
    ((Ω.reindex prodReassoc).marginalA).matrix x y =
      ∑ z : a × c,
        Ω.matrix (prodReassoc.symm (x, z)) (prodReassoc.symm (y, z)) := by
  simp only [State.marginalA_matrix, partialTraceB, State.reindex_matrix,
    Matrix.submatrix_apply]

theorem sigma_matrix_apply (Ω : State ((Qubit × a) × (Qubit × c)))
    (x y : a × c) :
    ((Ω.reindex prodReassoc).marginalB).matrix x y =
      ∑ w : Qubit × Qubit,
        Ω.matrix (prodReassoc.symm (w, x)) (prodReassoc.symm (w, y)) := by
  simp only [State.marginalB_matrix, partialTraceA, State.reindex_matrix,
    Matrix.submatrix_apply]

theorem pure_rhoAB_matrix_apply (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (x y : Qubit × Qubit) :
    ((ψ.state.reindex prodReassoc).marginalA).matrix x y =
      ∑ z : a × c, branchAmp ψ x z * star (branchAmp ψ y z) := by
  rw [rhoAB_matrix_apply]
  exact Finset.sum_congr rfl fun z _ => by
    simp [PureVector.state_matrix_apply, branchAmp]

theorem pure_sigma_matrix_apply (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (x y : a × c) :
    ((ψ.state.reindex prodReassoc).marginalB).matrix x y =
      ∑ w : Qubit × Qubit,
        branchAmp ψ w x * star (branchAmp ψ w y) := by
  rw [sigma_matrix_apply]
  exact Finset.sum_congr rfl fun w _ => by
    simp [PureVector.state_matrix_apply, branchAmp]

theorem pure_sigma_eq_decomposition
    (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (filler : PureVector (a × c)) :
    (sigmaDecomposition ψ filler).averageState =
      (ψ.state.reindex prodReassoc).marginalB := by
  apply State.ext
  ext x y
  rw [sigmaDecomposition_averageState_entry, pure_sigma_matrix_apply]

/-- The gauge condition makes the `|01⟩` entry of `ρ_AB` vanish. -/
theorem pure_rhoAB_zero_entry (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (hzero : ∀ i j, ψ.amp ((0, i), (1, j)) = 0) :
    ((ψ.state.reindex prodReassoc).marginalA).matrix (0, 1) (0, 1) = 0 := by
  rw [pure_rhoAB_matrix_apply]
  have hz : ∀ z : a × c, branchAmp ψ (0, 1) z = 0 := by
    intro z
    obtain ⟨i, j⟩ := z
    simpa [branchAmp_eq] using hzero i j
  simp only [hz, mul_zero, star_zero, Finset.sum_const_zero]

theorem pure_rhoAB_coherence (ψ : PureVector ((Qubit × a) × (Qubit × c))) :
    ((ψ.state.reindex prodReassoc).marginalA).matrix (0, 0) (1, 1) =
      ∑ z : a × c,
        branchAmp ψ (0, 0) z * star (branchAmp ψ (1, 1) z) :=
  pure_rhoAB_matrix_apply ψ (0, 0) (1, 1)

/-! ### Cauchy–Schwarz and the concurrence curve bound -/

open scoped InnerProductSpace in
/-- Cauchy–Schwarz for complex amplitude sums, in the form needed for the
coherence bound. -/
theorem complexCauchySchwarz {ι : Type w₁} [Fintype ι] (u v : ι → ℂ) :
    ‖∑ i, u i * star (v i)‖ ≤
      Real.sqrt (∑ i, Complex.normSq (u i)) *
        Real.sqrt (∑ i, Complex.normSq (v i)) := by
  set U : EuclideanSpace ℂ ι := (WithLp.toLp 2) u with hU
  set V : EuclideanSpace ℂ ι := (WithLp.toLp 2) v with hV
  have hinner : ⟪U, V⟫_ℂ = ∑ i, star (u i) * v i := by
    rw [EuclideanSpace.inner_eq_star_dotProduct]
    simp only [hU, hV, dotProduct]
    simp [mul_comm]
  have hnormU : ‖U‖ = Real.sqrt (∑ i, Complex.normSq (u i)) := by
    rw [EuclideanSpace.norm_eq, hU]
    simp [Complex.normSq_eq_norm_sq]
  have hnormV : ‖V‖ = Real.sqrt (∑ i, Complex.normSq (v i)) := by
    rw [EuclideanSpace.norm_eq, hV]
    simp [Complex.normSq_eq_norm_sq]
  have hcs := norm_inner_le_norm (𝕜 := ℂ) U V
  rw [hinner, hnormU, hnormV] at hcs
  have hstar : ∑ i, u i * star (v i) = star (∑ i, star (u i) * v i) := by
    rw [star_sum]
    exact Finset.sum_congr rfl fun i _ => by
      rw [star_mul, star_star]
      ring
  rw [hstar, norm_star]
  exact hcs

theorem coherence_norm_le (ψ : PureVector ((Qubit × a) × (Qubit × c))) :
    ‖∑ z : a × c,
        branchAmp ψ (0, 0) z * star (branchAmp ψ (1, 1) z)‖ ≤
      Real.sqrt (frobeniusSq (branchMatrix ψ (0, 0))) *
        Real.sqrt (frobeniusSq (branchMatrix ψ (1, 1))) := by
  have h := complexCauchySchwarz (branchAmp ψ (0, 0)) (branchAmp ψ (1, 1))
  rwa [← branchMatrix_frobeniusSq, ← branchMatrix_frobeniusSq] at h

theorem two_sqrt_prod_le_one (α β γ : ℝ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (hγ : 0 ≤ γ) (hsum : α + β + γ = 1) :
    2 * Real.sqrt (α * γ) ≤ 1 := by
  have h4 : α * γ ≤ 1 / 4 := by
    have h1 : 4 * α * γ ≤ (α + γ) ^ 2 := by nlinarith [sq_nonneg (α - γ)]
    have h2 : α + γ ≤ 1 := by linarith
    nlinarith
  have h1 : Real.sqrt (α * γ) ≤ 1 / 2 :=
    Real.sqrt_le_iff.mpr ⟨by norm_num, by
      have hq : ((1 : ℝ) / 2) ^ 2 = 1 / 4 := by norm_num
      rw [hq]
      exact h4⟩
  linarith

/-! ### The pure case of Theorem 6 -/

/-- **Theorem 6, pure case (gauge-fixed).**  For a pure state on `AA' ⊗ BB'`
whose `|01⟩` branch amplitudes all vanish, the sum of the entanglements of
formation of the two reassociated marginals is at most the `AA'` marginal
entropy. -/
theorem pure_entanglementOfFormation_superadditive
    (h : woottersKernelUpperBound)
    (ψ : PureVector ((Qubit × a) × (Qubit × c)))
    (hzero : ∀ i j, ψ.amp ((0, i), (1, j)) = 0) :
    entanglementOfFormation ((ψ.state.reindex prodReassoc).marginalA) +
      entanglementOfFormation ((ψ.state.reindex prodReassoc).marginalB) ≤
      ψ.state.marginalA.vonNeumann := by
  -- The gauge-fixed `|01⟩` branch has weight zero.
  have h01 : frobeniusSq (branchMatrix ψ (0, 1)) = 0 := by
    rw [branchMatrix_frobeniusSq]
    apply Finset.sum_eq_zero
    rintro ⟨i, j⟩ _
    have hz : branchAmp ψ (0, 1) (i, j) = 0 := by
      rw [branchAmp_eq]
      exact hzero i j
    simp [hz]
  -- The three live branch weights sum to one.
  have hsplit : frobeniusSq (branchMatrix ψ (0, 0)) +
      frobeniusSq (branchMatrix ψ (1, 0)) +
      frobeniusSq (branchMatrix ψ (1, 1)) = 1 := by
    have h4 := branchWeights_sum ψ
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two,
      Fin.sum_univ_two, h01, add_zero] at h4
    linarith
  -- The `ρ_AB` side: corner formula, Cauchy–Schwarz, curve monotonicity.
  have hcurve : entanglementOfFormation
      ((ψ.state.reindex prodReassoc).marginalA) ≤
      entanglementCurve (2 * Real.sqrt (frobeniusSq (branchMatrix ψ (0, 0)) *
        frobeniusSq (branchMatrix ψ (1, 1)))) := by
    have hcs := coherence_norm_le ψ
    have hle : (2 : ℝ) * ‖∑ z : a × c,
        branchAmp ψ (0, 0) z * star (branchAmp ψ (1, 1) z)‖ ≤
        2 * Real.sqrt (frobeniusSq (branchMatrix ψ (0, 0)) *
          frobeniusSq (branchMatrix ψ (1, 1))) := by
      rw [Real.sqrt_mul (frobeniusSq_nonneg (branchMatrix ψ (0, 0)))]
      exact mul_le_mul_of_nonneg_left hcs (by norm_num)
    have hone : (2 : ℝ) * Real.sqrt (frobeniusSq (branchMatrix ψ (0, 0)) *
        frobeniusSq (branchMatrix ψ (1, 1))) ≤ 1 :=
      two_sqrt_prod_le_one _ _ _ (frobeniusSq_nonneg _) (frobeniusSq_nonneg _)
        (frobeniusSq_nonneg _) hsplit
    have hmono := entanglementCurve_monotoneOn
      ⟨by positivity, hle.trans hone⟩ ⟨by positivity, hone⟩ hle
    rw [entanglementOfFormation_eq_entanglementCurve h
      ((ψ.state.reindex prodReassoc).marginalA)
      (pure_rhoAB_zero_entry ψ hzero), pure_rhoAB_coherence]
    exact hmono
  -- The `σ_A'B'` side: three-branch decomposition.
  obtain ⟨filler⟩ : ∃ F : PureVector (a × c), True := by
    by_cases hA : 0 < frobeniusSq (branchMatrix ψ (0, 0))
    · exact ⟨PureVector.normalize (branchAmp ψ (0, 0))
        (by rw [branchTraceRe]; exact hA), trivial⟩
    · by_cases hB : 0 < frobeniusSq (branchMatrix ψ (1, 0))
      · exact ⟨PureVector.normalize (branchAmp ψ (1, 0))
          (by rw [branchTraceRe]; exact hB), trivial⟩
      · have hA0 : frobeniusSq (branchMatrix ψ (0, 0)) = 0 :=
          le_antisymm (le_of_not_gt hA) (frobeniusSq_nonneg _)
        have hB0 : frobeniusSq (branchMatrix ψ (1, 0)) = 0 :=
          le_antisymm (le_of_not_gt hB) (frobeniusSq_nonneg _)
        have hγ : 0 < frobeniusSq (branchMatrix ψ (1, 1)) := by
          have hcopy := hsplit
          rw [hA0, hB0] at hcopy
          linarith [frobeniusSq_nonneg (branchMatrix ψ (1, 1))]
        exact ⟨PureVector.normalize (branchAmp ψ (1, 1))
          (by rw [branchTraceRe]; exact hγ), trivial⟩
  have hsdec := entanglementOfFormation_le_entanglementCost
    (sigmaDecomposition ψ filler)
  rw [pure_sigma_eq_decomposition, sigmaDecomposition_entanglementCost] at hsdec
  have hsumNGE : ∑ w : Qubit × Qubit,
      normalizedGramEntropy (frobeniusSq (branchMatrix ψ w))
        (branchMatrix ψ w) =
      normalizedGramEntropy (frobeniusSq (branchMatrix ψ (0, 0)))
        (branchMatrix ψ (0, 0)) +
      normalizedGramEntropy (frobeniusSq (branchMatrix ψ (1, 0)))
        (branchMatrix ψ (1, 0)) +
      normalizedGramEntropy (frobeniusSq (branchMatrix ψ (1, 1)))
        (branchMatrix ψ (1, 1)) := by
    rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two,
      Fin.sum_univ_two, h01]
    simp only [normalizedGramEntropy_zero, add_zero]
    abel
  rw [hsumNGE] at hsdec
  -- The triangular block entropy inequality.
  have htri := triangularBlockEntropyInequality
    (branchMatrix ψ (0, 0)) (branchMatrix ψ (1, 0)) (branchMatrix ψ (1, 1))
    hsplit
  -- The `AA'` marginal entropy is the entropy of the block Gram matrix.
  have hvm : ψ.state.marginalA.vonNeumann =
      psdEntropy
        (Matrix.fromBlocks (branchMatrix ψ (0, 0)) 0
          (branchMatrix ψ (1, 0)) (branchMatrix ψ (1, 1)) *
          (Matrix.fromBlocks (branchMatrix ψ (0, 0)) 0
            (branchMatrix ψ (1, 0)) (branchMatrix ψ (1, 1))).conjTranspose)
        (Matrix.posSemidef_self_mul_conjTranspose _) := by
    calc ψ.state.marginalA.vonNeumann
        = (ψ.state.marginalA.reindex qubitProdSumEquiv).vonNeumann :=
          (State.vonNeumann_reindex ψ.state.marginalA qubitProdSumEquiv).symm
      _ = psdEntropy
            ((ψ.state.marginalA.reindex qubitProdSumEquiv).matrix)
            ((ψ.state.marginalA.reindex qubitProdSumEquiv).pos) :=
          (psdEntropy_state _).symm
      _ = psdEntropy
            (Matrix.fromBlocks (branchMatrix ψ (0, 0)) 0
              (branchMatrix ψ (1, 0)) (branchMatrix ψ (1, 1)) *
              (Matrix.fromBlocks (branchMatrix ψ (0, 0)) 0
                (branchMatrix ψ (1, 0)) (branchMatrix ψ (1, 1))).conjTranspose)
            (Matrix.posSemidef_self_mul_conjTranspose _) :=
          psdEntropy_congr (pure_marginalA_reindex_matrix ψ hzero) _ _
  linarith

/-! ### The mixed case of Theorem 6 -/

/-- **Theorem 6 (gauge-fixed).**  If the two-qubit marginal `ρ_AB` of a state
`Ω` on `AA' ⊗ BB'` has vanishing `|01⟩` population, then
`E_F(ρ_AB) + E_F(σ_A'B') ≤ E_F(Ω)`, where `ρ_AB` and `σ_A'B'` are the two
marginals of the reassociated state.  The proof applies the pure case
branchwise to an arbitrary pure decomposition of `Ω` (the gauge condition
propagates to every positive-weight branch) and concludes by convexity. -/
theorem entanglementOfFormation_superadditive
    (h : woottersKernelUpperBound)
    (Ω : State ((Qubit × a) × (Qubit × c)))
    (hzero : ((Ω.reindex prodReassoc).marginalA).matrix (0, 1) (0, 1) = 0) :
    entanglementOfFormation ((Ω.reindex prodReassoc).marginalA) +
      entanglementOfFormation ((Ω.reindex prodReassoc).marginalB) ≤
      entanglementOfFormation Ω := by
  apply le_csInf (pureEntanglementValues_nonempty Ω)
  intro x hx
  rcases hx with ⟨E, hEavg, rfl⟩
  -- The two reassociated branch ensembles of the decomposition `E`.
  have hRavg : ((⟨E.probs, E.weights_sum,
      fun j => ((E.vectors j).state.reindex prodReassoc).marginalA⟩ :
      Ensemble (Fin E.card) (Qubit × Qubit))).averageState =
      (Ω.reindex prodReassoc).marginalA := by
    apply State.ext
    ext x y
    have hL : ((⟨E.probs, E.weights_sum,
        fun j => ((E.vectors j).state.reindex prodReassoc).marginalA⟩ :
        Ensemble (Fin E.card) (Qubit × Qubit))).averageState.matrix x y =
        ∑ j : Fin E.card, ((E.probs j : ℝ≥0) : ℂ) *
          (((E.vectors j).state.reindex prodReassoc).marginalA).matrix x y := by
      rw [Ensemble.averageState_matrix, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [NNReal.smul_def]
      rfl
    have hR : ((Ω.reindex prodReassoc).marginalA).matrix x y =
        ∑ z : a × c, ∑ j : Fin E.card, ((E.probs j : ℝ≥0) : ℂ) *
          ((E.vectors j).amp (prodReassoc.symm (x, z)) *
            star ((E.vectors j).amp (prodReassoc.symm (y, z)))) := by
      rw [rhoAB_matrix_apply]
      refine Finset.sum_congr rfl fun z _ => ?_
      rw [← hEavg, pureDecomposition_averageState_entry]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [PureVector.state_matrix_apply]
    have hstep : ∀ j : Fin E.card,
        ((E.probs j : ℝ≥0) : ℂ) *
            (((E.vectors j).state.reindex prodReassoc).marginalA).matrix x y =
          ∑ z : a × c, ((E.probs j : ℝ≥0) : ℂ) *
              ((E.vectors j).amp (prodReassoc.symm (x, z)) *
                star ((E.vectors j).amp (prodReassoc.symm (y, z)))) := by
      intro j
      rw [pure_rhoAB_matrix_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun z _ => rfl
    rw [hL, hR, Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_comm]
  have hSavg : ((⟨E.probs, E.weights_sum,
      fun j => ((E.vectors j).state.reindex prodReassoc).marginalB⟩ :
      Ensemble (Fin E.card) (a × c))).averageState =
      (Ω.reindex prodReassoc).marginalB := by
    apply State.ext
    ext x y
    have hL : ((⟨E.probs, E.weights_sum,
        fun j => ((E.vectors j).state.reindex prodReassoc).marginalB⟩ :
        Ensemble (Fin E.card) (a × c))).averageState.matrix x y =
        ∑ j : Fin E.card, ((E.probs j : ℝ≥0) : ℂ) *
          (((E.vectors j).state.reindex prodReassoc).marginalB).matrix x y := by
      rw [Ensemble.averageState_matrix, Matrix.sum_apply]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [NNReal.smul_def]
      rfl
    have hR : ((Ω.reindex prodReassoc).marginalB).matrix x y =
        ∑ w : Qubit × Qubit, ∑ j : Fin E.card, ((E.probs j : ℝ≥0) : ℂ) *
          ((E.vectors j).amp (prodReassoc.symm (w, x)) *
            star ((E.vectors j).amp (prodReassoc.symm (w, y)))) := by
      rw [sigma_matrix_apply]
      refine Finset.sum_congr rfl fun w _ => ?_
      rw [← hEavg, pureDecomposition_averageState_entry]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [PureVector.state_matrix_apply]
    have hstep : ∀ j : Fin E.card,
        ((E.probs j : ℝ≥0) : ℂ) *
            (((E.vectors j).state.reindex prodReassoc).marginalB).matrix x y =
          ∑ w : Qubit × Qubit, ((E.probs j : ℝ≥0) : ℂ) *
              ((E.vectors j).amp (prodReassoc.symm (w, x)) *
                star ((E.vectors j).amp (prodReassoc.symm (w, y)))) := by
      intro j
      rw [pure_sigma_matrix_apply, Finset.mul_sum]
      exact Finset.sum_congr rfl fun w _ => rfl
    rw [hL, hR, Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_comm]
  -- The vanishing `|01⟩` population, branchwise.
  have h01 : ((⟨E.probs, E.weights_sum,
      fun j => ((E.vectors j).state.reindex prodReassoc).marginalA⟩ :
      Ensemble (Fin E.card) (Qubit × Qubit))).averageState.matrix
      (0, 1) (0, 1) = 0 := by
    rw [hRavg]; exact hzero
  have hL2 : ((⟨E.probs, E.weights_sum,
      fun j => ((E.vectors j).state.reindex prodReassoc).marginalA⟩ :
      Ensemble (Fin E.card) (Qubit × Qubit))).averageState.matrix
      (0, 1) (0, 1) =
      ∑ j : Fin E.card, ((E.probs j : ℝ≥0) : ℂ) *
        (((E.vectors j).state.reindex prodReassoc).marginalA).matrix
          (0, 1) (0, 1) := by
    rw [Ensemble.averageState_matrix, Matrix.sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [NNReal.smul_def]
    rfl
  have h2 : ∑ j : Fin E.card, ((E.probs j : ℝ≥0) : ℂ) *
      (((E.vectors j).state.reindex prodReassoc).marginalA).matrix
        (0, 1) (0, 1) = 0 := by
    rw [← hL2, h01]
  have h2bA : ∑ j : Fin E.card, ∑ z : a × c,
      ((E.probs j : ℝ≥0) : ℂ) *
        (branchAmp (E.vectors j) (0, 1) z *
          star (branchAmp (E.vectors j) (0, 1) z)) = 0 := by
    have hstep : ∀ j : Fin E.card,
        ((E.probs j : ℝ≥0) : ℂ) *
            (((E.vectors j).state.reindex prodReassoc).marginalA).matrix
              (0, 1) (0, 1) =
          ∑ z : a × c, ((E.probs j : ℝ≥0) : ℂ) *
              (branchAmp (E.vectors j) (0, 1) z *
                star (branchAmp (E.vectors j) (0, 1) z)) := by
      intro j
      rw [pure_rhoAB_matrix_apply, Finset.mul_sum]
    calc ∑ j : Fin E.card, ∑ z : a × c,
          ((E.probs j : ℝ≥0) : ℂ) *
            (branchAmp (E.vectors j) (0, 1) z *
              star (branchAmp (E.vectors j) (0, 1) z))
        = ∑ j : Fin E.card, ((E.probs j : ℝ≥0) : ℂ) *
            (((E.vectors j).state.reindex prodReassoc).marginalA).matrix
              (0, 1) (0, 1) :=
          Finset.sum_congr rfl fun j _ => (hstep j).symm
      _ = 0 := h2
  have hmul : ∀ z : ℂ, z * star z = ((Complex.normSq z : ℝ) : ℂ) := fun z => by
    show z * starRingEnd ℂ z = _
    rw [Complex.mul_conj]
  have hco : ∀ j : Fin E.card, ∀ z : a × c,
      ((E.probs j : ℝ≥0) : ℂ) *
          (branchAmp (E.vectors j) (0, 1) z *
            star (branchAmp (E.vectors j) (0, 1) z)) =
        ((((E.probs j : ℝ≥0) : ℝ) *
          Complex.normSq (branchAmp (E.vectors j) (0, 1) z) : ℝ) : ℂ) := by
    intro j z
    rw [hmul _, ← Complex.ofReal_mul]
  have h5 : (((∑ j : Fin E.card, ∑ z : a × c,
      ((E.probs j : ℝ≥0) : ℝ) *
        Complex.normSq (branchAmp (E.vectors j) (0, 1) z) : ℝ)) : ℂ) = 0 := by
    simp_rw [Complex.ofReal_sum]
    calc ∑ j : Fin E.card, ∑ z : a × c,
          ((((E.probs j : ℝ≥0) : ℝ) *
            Complex.normSq (branchAmp (E.vectors j) (0, 1) z) : ℝ) : ℂ)
        = ∑ j : Fin E.card, ∑ z : a × c,
          ((E.probs j : ℝ≥0) : ℂ) *
            (branchAmp (E.vectors j) (0, 1) z *
              star (branchAmp (E.vectors j) (0, 1) z)) :=
          Finset.sum_congr rfl fun j _ =>
            Finset.sum_congr rfl fun z _ => (hco j z).symm
      _ = 0 := h2bA
  have h4 : (∑ j : Fin E.card, ∑ z : a × c,
      (((E.probs j : ℝ≥0) : ℝ) *
        Complex.normSq (branchAmp (E.vectors j) (0, 1) z) : ℝ)) = 0 :=
    Complex.ofReal_injective h5
  have hnn : ∀ j : Fin E.card, ∀ z : a × c, (0 : ℝ) ≤
      ((E.probs j : ℝ≥0) : ℝ) *
        Complex.normSq (branchAmp (E.vectors j) (0, 1) z) := fun j z =>
    mul_nonneg (NNReal.coe_nonneg _) (Complex.normSq_nonneg _)
  have hterm0 : ∀ j : Fin E.card, ∀ z : a × c,
      ((E.probs j : ℝ≥0) : ℝ) *
        Complex.normSq (branchAmp (E.vectors j) (0, 1) z) = 0 := by
    intro j z
    have houter := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Finset.sum_nonneg fun z _ => hnn j z)).mp h4
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => hnn j z)).mp (houter j (Finset.mem_univ j)) z
      (Finset.mem_univ z)
  -- Branchwise: the pure case, weighted.
  have hbranch : ∀ j : Fin E.card,
      ((E.probs j : ℝ≥0) : ℝ) *
        (entanglementOfFormation
            ((E.vectors j).state.reindex prodReassoc).marginalA +
          entanglementOfFormation
            ((E.vectors j).state.reindex prodReassoc).marginalB) ≤
      ((E.probs j : ℝ≥0) : ℝ) *
        ((E.vectors j).state.marginalA).vonNeumann := by
    intro j
    by_cases hp : ((E.probs j : ℝ≥0) : ℝ) = 0
    · rw [hp, zero_mul, zero_mul]
    · have hpz : (0 : ℝ) < ((E.probs j : ℝ≥0) : ℝ) :=
        lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm hp)
      have hg : ∀ i : a, ∀ j' : c, (E.vectors j).amp ((0, i), (1, j')) = 0 := by
        intro i j'
        have hz : ((E.probs j : ℝ≥0) : ℝ) *
            Complex.normSq (branchAmp (E.vectors j) (0, 1) (i, j')) = 0 :=
          hterm0 j (i, j')
        exact Complex.normSq_eq_zero.mp (by
          rcases mul_eq_zero.mp hz with h | h
          · exact absurd h hp
          · exact h)
      exact mul_le_mul_of_nonneg_left
        (pure_entanglementOfFormation_superadditive h (E.vectors j) hg) hpz.le
  -- Convexity (finite Jensen) on both sides.
  have hjR := entanglementOfFormation_satisfiesFiniteJensen
    (a := Qubit) (c := Qubit)
    (⟨E.probs, E.weights_sum,
      fun j => ((E.vectors j).state.reindex prodReassoc).marginalA⟩ :
      Ensemble (Fin E.card) (Qubit × Qubit))
  rw [show ((⟨E.probs, E.weights_sum,
      fun j => ((E.vectors j).state.reindex prodReassoc).marginalA⟩ :
      Ensemble (Fin E.card) (Qubit × Qubit))).averageState =
      (Ω.reindex prodReassoc).marginalA from hRavg] at hjR
  have hjS := entanglementOfFormation_satisfiesFiniteJensen
    (a := a) (c := c)
    (⟨E.probs, E.weights_sum,
      fun j => ((E.vectors j).state.reindex prodReassoc).marginalB⟩ :
      Ensemble (Fin E.card) (a × c))
  rw [show ((⟨E.probs, E.weights_sum,
      fun j => ((E.vectors j).state.reindex prodReassoc).marginalB⟩ :
      Ensemble (Fin E.card) (a × c))).averageState =
      (Ω.reindex prodReassoc).marginalB from hSavg] at hjS
  have hcost : ∑ j : Fin E.card, ((E.probs j : ℝ≥0) : ℝ) *
      ((E.vectors j).state.marginalA).vonNeumann = E.entanglementCost := rfl
  calc entanglementOfFormation ((Ω.reindex prodReassoc).marginalA) +
        entanglementOfFormation ((Ω.reindex prodReassoc).marginalB)
      ≤ (∑ j : Fin E.card, ((E.probs j : ℝ≥0) : ℝ) *
            entanglementOfFormation
              ((E.vectors j).state.reindex prodReassoc).marginalA) +
        (∑ j : Fin E.card, ((E.probs j : ℝ≥0) : ℝ) *
            entanglementOfFormation
              ((E.vectors j).state.reindex prodReassoc).marginalB) :=
        add_le_add hjR hjS
    _ = ∑ j : Fin E.card, ((E.probs j : ℝ≥0) : ℝ) *
        (entanglementOfFormation
            ((E.vectors j).state.reindex prodReassoc).marginalA +
          entanglementOfFormation
            ((E.vectors j).state.reindex prodReassoc).marginalB) := by
        rw [← Finset.sum_add_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
    _ ≤ ∑ j : Fin E.card, ((E.probs j : ℝ≥0) : ℝ) *
        ((E.vectors j).state.marginalA).vonNeumann :=
        Finset.sum_le_sum fun j _ => hbranch j
    _ = E.entanglementCost := hcost.symm

end

end AmplitudeDamping
