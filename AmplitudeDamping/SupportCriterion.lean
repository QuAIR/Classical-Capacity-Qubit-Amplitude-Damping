import AmplitudeDamping.EntanglementSSA

/-!
# Arbitrary-dimensional support: coefficient matrices and propagation

The local basis types are `A₁ ⊕ Unit` and `Unit ⊕ B₁`. Their distinguished
unit summands represent the vacuum directions. Neither `A₁` nor `B₁` is
required to be inhabited, so zero-dimensional sectors are included.

This module proves the rectangular triangular entropy estimate, the auxiliary
formation bound by normalized sector reduction and entropy concavity, and
support propagation through finite pure decompositions. The scalar marginal
bound is developed separately using the two-expectation decomposition.
-/

open scoped BigOperators NNReal ComplexConjugate ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT
noncomputable section
universe u v w x
variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- Forbidden-sector population formulation of the support constraint. -/
def HasSingleExcitationSupport (ρ : State ((a ⊕ Unit) × (Unit ⊕ b))) : Prop :=
  ∀ i : a, ∀ j : b, ρ.matrix (Sum.inl i, Sum.inr j) (Sum.inl i, Sum.inr j) = 0

/-- Pure extensions have no amplitudes in the joint non-vacuum sector. -/
def HasSingleExcitationAmplitudes
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) : Prop :=
  ∀ i : a, ∀ j : b, ∀ k : c, ∀ l : d,
    ψ.amp ((Sum.inl i, k), (Sum.inr j, l)) = 0

/-- The first rectangular block contains the `A₁ ⊗ |0_B⟩` sector. -/
def supportBlockA
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) :
    Matrix (a × c) d ℂ := fun i j => ψ.amp ((Sum.inl i.1, i.2), (Sum.inl (), j))

/-- The middle block contains the vacuum sector. -/
def supportBlockB
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) :
    Matrix c d ℂ := fun i j => ψ.amp ((Sum.inr (), i), (Sum.inl (), j))

/-- The last rectangular block contains the `|0_A⟩ ⊗ B₁` sector. -/
def supportBlockD
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) :
    Matrix c (b × d) ℂ := fun i j => ψ.amp ((Sum.inr (), i), (Sum.inr j.1, j.2))

def supportRowEquiv : ((a ⊕ Unit) × c) ≃ ((a × c) ⊕ c) where
  toFun z := match z.1 with
    | Sum.inl i => Sum.inl (i, z.2)
    | Sum.inr _ => Sum.inr z.2
  invFun z := match z with
    | Sum.inl i => (Sum.inl i.1, i.2)
    | Sum.inr i => (Sum.inr (), i)
  left_inv := by rintro ⟨i | ⟨⟩, j⟩ <;> rfl
  right_inv := by rintro (⟨i, j⟩ | j) <;> rfl

def supportColEquiv : ((Unit ⊕ b) × d) ≃ (d ⊕ (b × d)) where
  toFun z := match z.1 with
    | Sum.inl _ => Sum.inl z.2
    | Sum.inr i => Sum.inr (i, z.2)
  invFun z := match z with
    | Sum.inl i => (Sum.inl (), i)
    | Sum.inr i => (Sum.inr i.1, i.2)
  left_inv := by rintro ⟨⟨⟩ | i, j⟩ <;> rfl
  right_inv := by rintro (j | ⟨i, j⟩) <;> rfl

/-- The coefficient matrix exposed by the two local basis reorderings. -/
theorem supported_coefficient_reindex
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)))
    (hs : HasSingleExcitationAmplitudes ψ) :
    Matrix.reindex supportRowEquiv supportColEquiv
      ((fun i j => ψ.amp (i,j)) : Matrix ((a ⊕ Unit) × c) ((Unit ⊕ b) × d) ℂ) =
    Matrix.fromBlocks (supportBlockA ψ) 0 (supportBlockB ψ) (supportBlockD ψ) := by
  ext (i | i) (j | j)
  · rfl
  · exact hs i.1 j.1 i.2 j.2
  · rfl
  · rfl

/-- The supported branch norms exhaust the normalized pure vector. -/
theorem supportBlock_weights_sum
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)))
    (hs : HasSingleExcitationAmplitudes ψ) :
    frobeniusSq (supportBlockA ψ) + frobeniusSq (supportBlockB ψ) +
      frobeniusSq (supportBlockD ψ) = 1 := by
  have hnorm : ∑ s, Complex.normSq (ψ.amp s) = 1 := by
    have h := congrArg Complex.re ψ.trace_rankOne_eq_one
    simpa [rankOneMatrix_trace, dotProduct, Complex.mul_conj] using h
  have hz : ∀ i j k l, Complex.normSq (ψ.amp ((Sum.inl i, k), (Sum.inr j, l))) = 0 := by
    intro i j k l
    rw [hs i j k l, Complex.normSq_zero]
  simp only [frobeniusSq_eq_sum_normSq, supportBlockA, supportBlockB, supportBlockD,
    Fintype.sum_prod_type] at ⊢
  simpa only [Fintype.sum_prod_type, Fintype.sum_sum_type, Fintype.sum_unique,
    Finset.sum_add_distrib, hz, Finset.sum_const_zero, add_zero, zero_add] using hnorm

/-- The first marginal is the Gram matrix of the rectangular triangular
coefficient matrix, in the local sum ordering. -/
theorem supported_marginal_gram
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)))
    (hs : HasSingleExcitationAmplitudes ψ) :
    (ψ.state.marginalA.reindex supportRowEquiv).matrix =
      Matrix.fromBlocks (supportBlockA ψ) 0 (supportBlockB ψ) (supportBlockD ψ) *
      (Matrix.fromBlocks (supportBlockA ψ) 0 (supportBlockB ψ) (supportBlockD ψ)).conjTranspose := by
  let M : Matrix ((a ⊕ Unit) × c) ((Unit ⊕ b) × d) ℂ := fun i j => ψ.amp (i,j)
  have hg : ψ.state.marginalA.matrix = M * M.conjTranspose := by
    ext i j
    simp [State.marginalA_matrix, partialTraceB, PureVector.state_matrix_apply,
      M, Matrix.mul_apply, Matrix.conjTranspose_apply]
  rw [State.reindex_matrix, hg]
  change (M * M.conjTranspose).reindex supportRowEquiv supportRowEquiv = _
  rw [← mul_conjTranspose_reindex supportRowEquiv supportColEquiv]
  rw [show M.reindex supportRowEquiv supportColEquiv =
    Matrix.fromBlocks (supportBlockA ψ) 0 (supportBlockB ψ) (supportBlockD ψ) from
    supported_coefficient_reindex ψ hs]

/-- The manuscript's triangular entropy lower bound for arbitrary finite
local sectors and auxiliaries, including empty non-vacuum sectors. -/
theorem supported_pure_extension_entropy_lower_bound
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)))
    (hs : HasSingleExcitationAmplitudes ψ) :
    entanglementCurve (2 * Real.sqrt
        (frobeniusSq (supportBlockA ψ) * frobeniusSq (supportBlockD ψ))) +
      normalizedGramEntropy (frobeniusSq (supportBlockA ψ)) (supportBlockA ψ) +
      normalizedGramEntropy (frobeniusSq (supportBlockB ψ)) (supportBlockB ψ) +
      normalizedGramEntropy (frobeniusSq (supportBlockD ψ)) (supportBlockD ψ) ≤
    ψ.state.marginalA.vonNeumann := by
  have htri := triangularBlockEntropyInequality
    (supportBlockA ψ) (supportBlockB ψ) (supportBlockD ψ) (supportBlock_weights_sum ψ hs)
  have he : ψ.state.marginalA.vonNeumann =
      psdEntropy
        (Matrix.fromBlocks (supportBlockA ψ) 0 (supportBlockB ψ) (supportBlockD ψ) *
          (Matrix.fromBlocks (supportBlockA ψ) 0 (supportBlockB ψ) (supportBlockD ψ)).conjTranspose)
        (Matrix.posSemidef_self_mul_conjTranspose _) := by
    calc
      _ = (ψ.state.marginalA.reindex supportRowEquiv).vonNeumann :=
        (State.vonNeumann_reindex _ _).symm
      _ = psdEntropy (ψ.state.marginalA.reindex supportRowEquiv).matrix
          (ψ.state.marginalA.reindex supportRowEquiv).pos := rfl
      _ = _ := psdEntropy_congr (supported_marginal_gram ψ hs) _ _
  rw [he]
  exact htri


/-- A zero diagonal population of a marginal forces every corresponding
population of the joint state to vanish. No purity assumption is needed. -/
theorem joint_diagonal_zero_of_marginalA_zero
    {m : Type u} {n : Type v} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (ρ : State (m × n)) (i : m)
    (hz : ρ.marginalA.matrix i i = 0) (j : n) :
    ρ.matrix (i,j) (i,j) = 0 := by
  have hsum : ∑ k : n, (ρ.matrix (i,k) (i,k)).re = 0 := by
    simpa [State.marginalA_matrix, partialTraceB] using congrArg Complex.re hz
  have hr := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => (Complex.nonneg_iff.mp (ρ.pos.diag_nonneg (i := (i,k)))).1)).mp
      hsum j (Finset.mem_univ j)
  apply Complex.ext
  · exact hr
  · exact (Complex.nonneg_iff.mp (ρ.pos.diag_nonneg (i := (i,j)))).2.symm

/-- Every positive-weight vector in a decomposition inherits each zero
population of its average. -/
theorem pureDecomposition_amp_zero_of_diagonal_zero
    {m : Type u} [Fintype m] [DecidableEq m]
    (E : PureDecomposition m) (z : m)
    (hz : E.averageState.matrix z z = 0) (j : Fin E.card)
    (hj : 0 < (E.probs j : ℝ)) : (E.vectors j).amp z = 0 := by
  have hsum : ∑ k, (E.probs k : ℝ) * Complex.normSq ((E.vectors k).amp z) = 0 := by
    have h := congrArg Complex.re hz
    rw [pureDecomposition_averageState_entry] at h
    simpa [PureVector.state_matrix_apply, Complex.mul_conj, ← Complex.ofReal_mul,
      ← Complex.ofReal_sum] using h
  have ht := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => mul_nonneg (NNReal.coe_nonneg _) (Complex.normSq_nonneg _))).mp
      hsum j (Finset.mem_univ j)
  exact Complex.normSq_eq_zero.mp ((mul_eq_zero.mp ht).resolve_left (ne_of_gt hj))

/-- The marginal support condition propagates to every positive-weight pure
component of an arbitrary mixed extension, in all finite dimensions. -/
theorem supported_decomposition_amplitudes
    (Ω : State (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)))
    (hs : HasSingleExcitationSupport (Ω.reindex prodReassoc).marginalA)
    (E : PureDecomposition (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)))
    (hE : E.averageState = Ω) (j : Fin E.card) (hj : 0 < (E.probs j : ℝ)) :
    HasSingleExcitationAmplitudes (E.vectors j) := by
  intro i k l m
  apply pureDecomposition_amp_zero_of_diagonal_zero E _ _ j hj
  rw [hE]
  exact joint_diagonal_zero_of_marginalA_zero (Ω.reindex prodReassoc)
    (Sum.inl i, Sum.inr k) (hs i k) (l,m)

/-- For a pure extension the support condition is exactly the absence of
joint non-vacuum amplitudes. -/
theorem pure_support_iff_amplitudes
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) :
    HasSingleExcitationSupport (ψ.state.reindex prodReassoc).marginalA ↔
      HasSingleExcitationAmplitudes ψ := by
  constructor
  · intro hs i j k l
    have hz := joint_diagonal_zero_of_marginalA_zero (ψ.state.reindex prodReassoc)
      (Sum.inl i, Sum.inr j) (hs i j) (k,l)
    have hn : (Complex.normSq (ψ.amp ((Sum.inl i,k),(Sum.inr j,l))) : ℂ) = 0 := by
      simpa [State.reindex_matrix, Matrix.submatrix_apply,
        PureVector.state_matrix_apply, Complex.mul_conj] using hz
    exact Complex.normSq_eq_zero.mp (Complex.ofReal_eq_zero.mp hn)
  · intro hs i j
    change ∀ i j k l, ψ.amp ((Sum.inl i,k),(Sum.inr j,l)) = 0 at hs
    simp [State.marginalA_matrix, partialTraceB, State.reindex_matrix,
      Matrix.submatrix_apply, prodReassoc_symm_apply, hs]


/-- Averaging pure components commutes with reassociation and the first
marginal. This identity is independent of the support condition. -/
theorem reassoc_marginalA_average
    {p : Type u} {q : Type v} {r : Type w} {s : Type x}
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (E : PureDecomposition ((p × r) × (q × s))) :
    (⟨E.probs, E.weights_sum,
      fun j => ((E.vectors j).state.reindex prodReassoc).marginalA⟩ :
      Ensemble (Fin E.card) (p × q)).averageState =
    (E.averageState.reindex prodReassoc).marginalA := by
  apply State.ext
  ext i j
  simp only [Ensemble.averageState_matrix, State.marginalA_matrix,
    partialTraceB, State.reindex_matrix, Matrix.submatrix_apply,
    Matrix.sum_apply, PureDecomposition.averageState, Matrix.smul_apply]
  simp_rw [Finset.smul_sum]
  exact Finset.sum_comm

/-- Averaging pure components also commutes with the auxiliary marginal. -/
theorem reassoc_marginalB_average
    {p : Type u} {q : Type v} {r : Type w} {s : Type x}
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    [Fintype r] [DecidableEq r] [Fintype s] [DecidableEq s]
    (E : PureDecomposition ((p × r) × (q × s))) :
    (⟨E.probs, E.weights_sum,
      fun j => ((E.vectors j).state.reindex prodReassoc).marginalB⟩ :
      Ensemble (Fin E.card) (r × s)).averageState =
    (E.averageState.reindex prodReassoc).marginalB := by
  apply State.ext
  ext i j
  simp only [Ensemble.averageState_matrix, State.marginalB_matrix,
    partialTraceA, State.reindex_matrix, Matrix.submatrix_apply,
    Matrix.sum_apply, PureDecomposition.averageState, Matrix.smul_apply]
  simp_rw [Finset.smul_sum]
  exact Finset.sum_comm

/-- Mixed-state propagation of the support criterion from its pure-extension
case. The premise is explicitly the remaining pure case, not a classical
input: the theorem isolates the fully proved convex-roof argument. -/
theorem supported_superadditivity_of_pure
    (hpure : ∀ ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)),
      HasSingleExcitationAmplitudes ψ →
      entanglementOfFormation (ψ.state.reindex prodReassoc).marginalA +
        entanglementOfFormation (ψ.state.reindex prodReassoc).marginalB ≤
      ψ.state.marginalA.vonNeumann)
    (Ω : State (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)))
    (hs : HasSingleExcitationSupport (Ω.reindex prodReassoc).marginalA) :
    entanglementOfFormation (Ω.reindex prodReassoc).marginalA +
      entanglementOfFormation (Ω.reindex prodReassoc).marginalB ≤
    entanglementOfFormation Ω := by
  apply le_csInf (pureEntanglementValues_nonempty Ω)
  rintro z ⟨E, hE, rfl⟩
  have hA := entanglementOfFormation_satisfiesFiniteJensen
    (⟨E.probs, E.weights_sum,
      fun j => ((E.vectors j).state.reindex prodReassoc).marginalA⟩ :
      Ensemble (Fin E.card) ((a ⊕ Unit) × (Unit ⊕ b)))
  have hB := entanglementOfFormation_satisfiesFiniteJensen
    (⟨E.probs, E.weights_sum,
      fun j => ((E.vectors j).state.reindex prodReassoc).marginalB⟩ :
      Ensemble (Fin E.card) (c × d))
  rw [reassoc_marginalA_average, hE] at hA
  rw [reassoc_marginalB_average, hE] at hB
  apply (add_le_add hA hB).trans
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro j _
  change (E.probs j : ℝ) * _ + (E.probs j : ℝ) * _ ≤ (E.probs j : ℝ) * _
  rw [← mul_add]
  by_cases hz : (E.probs j : ℝ) = 0
  · simp [hz]
  · have hj : 0 < (E.probs j : ℝ) := lt_of_le_of_ne (NNReal.coe_nonneg _) (Ne.symm hz)
    exact mul_le_mul_of_nonneg_left
      (hpure (E.vectors j) (supported_decomposition_amplitudes Ω hs E hE j hj)) hj.le


/-- The finite convex roof is bounded above by either marginal entropy. -/
theorem entanglementOfFormation_le_marginalA_entropy
    {m : Type u} {n : Type v} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (ρ : State (m × n)) :
    entanglementOfFormation ρ ≤ ρ.marginalA.vonNeumann := by
  let E := spectralPureDecomposition ρ
  let F : Ensemble (Fin E.card) m :=
    ⟨E.probs, E.weights_sum, fun j => (E.vectors j).state.marginalA⟩
  have hF : F.averageState = ρ.marginalA := by
    rw [← spectralPureDecomposition_averageState ρ]
    apply State.ext
    ext i j
    simp only [F, Ensemble.averageState_matrix, State.marginalA_matrix,
      partialTraceB, Matrix.sum_apply, PureDecomposition.averageState, Matrix.smul_apply]
    simp_rw [Finset.smul_sum]
    exact Finset.sum_comm
  calc
    entanglementOfFormation ρ ≤ E.entanglementCost := by
      rw [← spectralPureDecomposition_averageState ρ]
      exact entanglementOfFormation_le_entanglementCost _
    _ ≤ F.averageState.vonNeumann := Ensemble.vonNeumann_average_ge_sum F
    _ = ρ.marginalA.vonNeumann := congrArg State.vonNeumann hF

theorem entanglementOfFormation_le_marginalB_entropy
    {m : Type u} {n : Type v} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (ρ : State (m × n)) :
    entanglementOfFormation ρ ≤ ρ.marginalB.vonNeumann := by
  let E := spectralPureDecomposition ρ
  let F : Ensemble (Fin E.card) n :=
    ⟨E.probs, E.weights_sum, fun j => (E.vectors j).state.marginalB⟩
  have hF : F.averageState = ρ.marginalB := by
    rw [← spectralPureDecomposition_averageState ρ]
    apply State.ext
    ext i j
    simp only [F, Ensemble.averageState_matrix, State.marginalB_matrix,
      partialTraceA, Matrix.sum_apply, PureDecomposition.averageState, Matrix.smul_apply]
    simp_rw [Finset.smul_sum]
    exact Finset.sum_comm
  calc
    entanglementOfFormation ρ ≤ E.entanglementCost := by
      rw [← spectralPureDecomposition_averageState ρ]
      exact entanglementOfFormation_le_entanglementCost _
    _ = ∑ j, (F.probs j : ℝ) * (F.states j).vonNeumann := by
      apply Finset.sum_congr rfl
      intro j _
      rw [State.pureVector_marginalA_vonNeumann_eq_marginalB]
    _ ≤ F.averageState.vonNeumann := Ensemble.vonNeumann_average_ge_sum F
    _ = ρ.marginalB.vonNeumann := congrArg State.vonNeumann hF


/-- Trace of the flattened rank-one matrix is the coefficient norm. -/
theorem rankOneMatrix_flatten_trace_re
    {m : Type u} {n : Type v} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) :
    (rankOneMatrix (fun z : m × n => M z.1 z.2)).trace.re = frobeniusSq M := by
  simp [rankOneMatrix_trace, dotProduct, Complex.mul_conj,
    frobeniusSq_eq_sum_normSq, Fintype.sum_prod_type]

/-- Normalize any nonzero rectangular coefficient matrix as a pure vector. -/
def matrixPureVector
    {m : Type u} {n : Type v} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) (hM : 0 < frobeniusSq M) :
    PureVector (m × n) :=
  PureVector.normalize (fun z => M z.1 z.2) (by
    rw [rankOneMatrix_flatten_trace_re]; exact hM)

theorem matrixPureVector_state_matrix
    {m : Type u} {n : Type v} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) (hM : 0 < frobeniusSq M) :
    (matrixPureVector M hM).state.matrix =
      (((frobeniusSq M)⁻¹ : ℝ) : ℂ) • rankOneMatrix (fun z : m × n => M z.1 z.2) := by
  rw [matrixPureVector, PureVector.normalize_state_matrix, rankOneMatrix_flatten_trace_re]

theorem matrixPureVector_marginalA_matrix
    {m : Type u} {n : Type v} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) (hM : 0 < frobeniusSq M) :
    (matrixPureVector M hM).state.marginalA.matrix =
      (((frobeniusSq M)⁻¹ : ℝ) : ℂ) • (M * M.conjTranspose) := by
  rw [State.marginalA_matrix, matrixPureVector_state_matrix, partialTraceB_smul]
  congr 1

/-- The weighted entropy of a normalized rectangular coefficient matrix. -/
theorem matrixPureVector_weight_entropy
    {m : Type u} {n : Type v} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) (hM : 0 < frobeniusSq M) :
    frobeniusSq M * (matrixPureVector M hM).state.marginalA.vonNeumann =
      normalizedGramEntropy (frobeniusSq M) M := by
  have he : (matrixPureVector M hM).state.marginalA.vonNeumann =
      psdEntropy ((((frobeniusSq M)⁻¹ : ℝ) : ℂ) • (M * M.conjTranspose))
        ((Matrix.posSemidef_self_mul_conjTranspose M).smul
          (by exact_mod_cast inv_nonneg.mpr hM.le)) := by
    exact psdEntropy_congr (matrixPureVector_marginalA_matrix M hM)
      (matrixPureVector M hM).state.marginalA.pos _
  rw [he, psdEntropy_real_smul _ (inv_nonneg.mpr hM.le) _
    (Matrix.posSemidef_self_mul_conjTranspose M)]
  have hx := xlog2_add_sq_mul_inv (frobeniusSq M) hM
  have hg := psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2 M
  change frobeniusSq M * ((frobeniusSq M)⁻¹ * _ -
    QIT.xlog2 (frobeniusSq M)⁻¹ * frobeniusSq M) = _
  rw [mul_sub, ← mul_assoc, mul_inv_cancel₀ hM.ne', one_mul, hg]
  nlinarith [hx]

/-- Zero coefficient norm means that every matrix entry vanishes. -/
theorem matrix_entry_zero_of_frobeniusSq_zero
    {m : Type u} {n : Type v} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ)
    (hM : frobeniusSq M = 0) (i : m) (j : n) : M i j = 0 := by
  rw [frobeniusSq_eq_sum_normSq] at hM
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg (M k l))).mp
      hM i (Finset.mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg
    (fun l _ => Complex.normSq_nonneg (M i l))).mp hi j (Finset.mem_univ j)
  exact Complex.normSq_eq_zero.mp hj


def discardMiddleEquiv {m : Type u} {n : Type v} {k : Type w} :
    (m × (n × k)) ≃ (n × (m × k)) where
  toFun z := (z.2.1, z.1, z.2.2)
  invFun z := (z.2.1, z.1, z.2.2)
  left_inv := by rintro ⟨i,j,k⟩; rfl
  right_inv := by rintro ⟨i,j,k⟩; rfl

/-- First sector after discarding the local `A₁` label. Zero-weight sectors
use the auxiliary marginal itself as an irrelevant filler state. -/
def supportReducedA
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) : State (c × d) :=
  if h : 0 < frobeniusSq (supportBlockA ψ) then
    ((matrixPureVector (supportBlockA ψ) h).state.reindex (Equiv.prodAssoc a c d)).marginalB
  else (ψ.state.reindex prodReassoc).marginalB

def supportReducedB
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) : State (c × d) :=
  if h : 0 < frobeniusSq (supportBlockB ψ) then
    (matrixPureVector (supportBlockB ψ) h).state
  else (ψ.state.reindex prodReassoc).marginalB

def supportReducedD
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) : State (c × d) :=
  if h : 0 < frobeniusSq (supportBlockD ψ) then
    ((matrixPureVector (supportBlockD ψ) h).state.reindex discardMiddleEquiv).marginalB
  else (ψ.state.reindex prodReassoc).marginalB

theorem weighted_matrixPureVector_entry
    {m : Type u} {n : Type v} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) (hM : 0 < frobeniusSq M)
    (i j : m × n) :
    (frobeniusSq M : ℂ) * (matrixPureVector M hM).state.matrix i j =
      M i.1 i.2 * star (M j.1 j.2) := by
  rw [matrixPureVector_state_matrix]
  simp only [Matrix.smul_apply, smul_eq_mul, rankOneMatrix_apply, Complex.ofReal_inv]
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.ofReal_ne_zero.mpr hM.ne'), one_mul]

theorem supportReducedA_weighted_entry
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) (i j : c × d) :
    (frobeniusSq (supportBlockA ψ) : ℂ) * (supportReducedA ψ).matrix i j =
      ∑ k : a, supportBlockA ψ (k,i.1) i.2 * star (supportBlockA ψ (k,j.1) j.2) := by
  by_cases h : 0 < frobeniusSq (supportBlockA ψ)
  · rw [supportReducedA, dif_pos h]
    simp only [State.marginalB_matrix, partialTraceA, State.reindex_matrix,
      Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => weighted_matrixPureVector_entry _ h _ _
  · have hz := le_antisymm (le_of_not_gt h) (frobeniusSq_nonneg (supportBlockA ψ))
    rw [hz, Complex.ofReal_zero, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [matrix_entry_zero_of_frobeniusSq_zero _ hz, zero_mul]

theorem supportReducedB_weighted_entry
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) (i j : c × d) :
    (frobeniusSq (supportBlockB ψ) : ℂ) * (supportReducedB ψ).matrix i j =
      supportBlockB ψ i.1 i.2 * star (supportBlockB ψ j.1 j.2) := by
  by_cases h : 0 < frobeniusSq (supportBlockB ψ)
  · rw [supportReducedB, dif_pos h]
    exact weighted_matrixPureVector_entry _ h _ _
  · have hz := le_antisymm (le_of_not_gt h) (frobeniusSq_nonneg (supportBlockB ψ))
    rw [hz, Complex.ofReal_zero, zero_mul,
      matrix_entry_zero_of_frobeniusSq_zero _ hz, zero_mul]

theorem supportReducedD_weighted_entry
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) (i j : c × d) :
    (frobeniusSq (supportBlockD ψ) : ℂ) * (supportReducedD ψ).matrix i j =
      ∑ k : b, supportBlockD ψ i.1 (k,i.2) * star (supportBlockD ψ j.1 (k,j.2)) := by
  by_cases h : 0 < frobeniusSq (supportBlockD ψ)
  · rw [supportReducedD, dif_pos h]
    simp only [State.marginalB_matrix, partialTraceA, State.reindex_matrix,
      Matrix.submatrix_apply]
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => weighted_matrixPureVector_entry _ h _ _
  · have hz := le_antisymm (le_of_not_gt h) (frobeniusSq_nonneg (supportBlockD ψ))
    rw [hz, Complex.ofReal_zero, zero_mul]
    symm
    apply Finset.sum_eq_zero
    intro k _
    rw [matrix_entry_zero_of_frobeniusSq_zero _ hz, zero_mul]


/-- Discarding a factor of the first party leaves the second marginal intact. -/
theorem discardLeft_marginalB
    {m : Type u} {n : Type v} {k : Type w}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] (ρ : State ((m × n) × k)) :
    ((ρ.reindex (Equiv.prodAssoc m n k)).marginalB).marginalB = ρ.marginalB := by
  apply State.ext
  ext i j
  simp only [State.marginalB_matrix, partialTraceA, State.reindex_matrix,
    Matrix.submatrix_apply, Equiv.prodAssoc_symm_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Discarding a factor of the second party leaves the first marginal intact. -/
theorem discardMiddle_marginalA
    {m : Type u} {n : Type v} {k : Type w}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] (ρ : State (m × (n × k))) :
    ((ρ.reindex discardMiddleEquiv).marginalB).marginalA = ρ.marginalA := by
  apply State.ext
  ext i j
  simp only [State.marginalA_matrix, State.marginalB_matrix, partialTraceA,
    partialTraceB, State.reindex_matrix, Matrix.submatrix_apply, Fintype.sum_prod_type]
  exact Finset.sum_comm

/-- Pure-state local discarding bound, derived from entropy concavity. -/
theorem pure_discardLeft_entanglementOfFormation_le
    {m : Type u} {n : Type v} {k : Type w}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] (φ : PureVector ((m × n) × k)) :
    entanglementOfFormation (φ.state.reindex (Equiv.prodAssoc m n k)).marginalB ≤
      φ.state.marginalA.vonNeumann := by
  have h := entanglementOfFormation_le_marginalB_entropy
    (φ.state.reindex (Equiv.prodAssoc m n k)).marginalB
  rw [discardLeft_marginalB, ← State.pureVector_marginalA_vonNeumann_eq_marginalB] at h
  exact h

/-- The right-hand local discarding version. -/
theorem pure_discardMiddle_entanglementOfFormation_le
    {m : Type u} {n : Type v} {k : Type w}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype k] [DecidableEq k] (φ : PureVector (m × (n × k))) :
    entanglementOfFormation (φ.state.reindex discardMiddleEquiv).marginalB ≤
      φ.state.marginalA.vonNeumann := by
  simpa only [discardMiddle_marginalA] using
    entanglementOfFormation_le_marginalA_entropy
      (φ.state.reindex discardMiddleEquiv).marginalB

theorem supportReducedA_weighted_entanglement_bound
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) :
    frobeniusSq (supportBlockA ψ) * entanglementOfFormation (supportReducedA ψ) ≤
      normalizedGramEntropy (frobeniusSq (supportBlockA ψ)) (supportBlockA ψ) := by
  by_cases h : 0 < frobeniusSq (supportBlockA ψ)
  · rw [supportReducedA, dif_pos h, ← matrixPureVector_weight_entropy _ h]
    exact mul_le_mul_of_nonneg_left
      (pure_discardLeft_entanglementOfFormation_le _) h.le
  · have hz := le_antisymm (le_of_not_gt h) (frobeniusSq_nonneg (supportBlockA ψ))
    simp [hz]

theorem supportReducedB_weighted_entanglement_bound
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) :
    frobeniusSq (supportBlockB ψ) * entanglementOfFormation (supportReducedB ψ) ≤
      normalizedGramEntropy (frobeniusSq (supportBlockB ψ)) (supportBlockB ψ) := by
  by_cases h : 0 < frobeniusSq (supportBlockB ψ)
  · rw [supportReducedB, dif_pos h, ← matrixPureVector_weight_entropy _ h]
    exact mul_le_mul_of_nonneg_left (entanglementOfFormation_le_marginalA_entropy _) h.le
  · have hz := le_antisymm (le_of_not_gt h) (frobeniusSq_nonneg (supportBlockB ψ))
    simp [hz]

theorem supportReducedD_weighted_entanglement_bound
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d))) :
    frobeniusSq (supportBlockD ψ) * entanglementOfFormation (supportReducedD ψ) ≤
      normalizedGramEntropy (frobeniusSq (supportBlockD ψ)) (supportBlockD ψ) := by
  by_cases h : 0 < frobeniusSq (supportBlockD ψ)
  · rw [supportReducedD, dif_pos h, ← matrixPureVector_weight_entropy _ h]
    exact mul_le_mul_of_nonneg_left
      (pure_discardMiddle_entanglementOfFormation_le _) h.le
  · have hz := le_antisymm (le_of_not_gt h) (frobeniusSq_nonneg (supportBlockD ψ))
    simp [hz]


/-- The three normalized sector reductions, with their original masses. -/
def supportAuxiliaryEnsemble
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)))
    (hs : HasSingleExcitationAmplitudes ψ) : Ensemble (Fin 3) (c × d) where
  probs := ![⟨frobeniusSq (supportBlockA ψ), frobeniusSq_nonneg _⟩,
    ⟨frobeniusSq (supportBlockB ψ), frobeniusSq_nonneg _⟩,
    ⟨frobeniusSq (supportBlockD ψ), frobeniusSq_nonneg _⟩]
  weights_sum := by
    apply NNReal.coe_injective
    simpa [Fin.sum_univ_three] using supportBlock_weights_sum ψ hs
  states := ![supportReducedA ψ, supportReducedB ψ, supportReducedD ψ]

/-- Tracing out the original local labels removes cross-sector coherence;
the three reduced branches reconstruct the auxiliary marginal exactly. -/
theorem supportAuxiliaryEnsemble_averageState
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)))
    (hs : HasSingleExcitationAmplitudes ψ) :
    (supportAuxiliaryEnsemble ψ hs).averageState =
      (ψ.state.reindex prodReassoc).marginalB := by
  apply State.ext
  ext i j
  rw [Ensemble.averageState_matrix, Fin.sum_univ_three]
  change (frobeniusSq (supportBlockA ψ) : ℂ) * (supportReducedA ψ).matrix i j +
    (frobeniusSq (supportBlockB ψ) : ℂ) * (supportReducedB ψ).matrix i j +
    (frobeniusSq (supportBlockD ψ) : ℂ) * (supportReducedD ψ).matrix i j = _
  rw [supportReducedA_weighted_entry, supportReducedB_weighted_entry,
    supportReducedD_weighted_entry]
  change ∀ i j k l, ψ.amp ((Sum.inl i,k),(Sum.inr j,l)) = 0 at hs
  simp [State.marginalB_matrix, partialTraceA, State.reindex_matrix,
    Matrix.submatrix_apply, prodReassoc_symm_apply,
    Fintype.sum_prod_type, Fintype.sum_sum_type,
    supportBlockA, supportBlockB, supportBlockD, hs, Finset.sum_add_distrib]

/-- Auxiliary formation bound in the support proof. The local discarding
comparison is proved above using entropy concavity, and the final averaging
step uses the finite convexity theorem for the literal formation roof. -/
theorem supported_auxiliary_entanglement_bound
    (ψ : PureVector (((a ⊕ Unit) × c) × ((Unit ⊕ b) × d)))
    (hs : HasSingleExcitationAmplitudes ψ) :
    entanglementOfFormation (ψ.state.reindex prodReassoc).marginalB ≤
      normalizedGramEntropy (frobeniusSq (supportBlockA ψ)) (supportBlockA ψ) +
      normalizedGramEntropy (frobeniusSq (supportBlockB ψ)) (supportBlockB ψ) +
      normalizedGramEntropy (frobeniusSq (supportBlockD ψ)) (supportBlockD ψ) := by
  have h := entanglementOfFormation_satisfiesFiniteJensen (supportAuxiliaryEnsemble ψ hs)
  rw [supportAuxiliaryEnsemble_averageState, Fin.sum_univ_three] at h
  exact h.trans (add_le_add
    (add_le_add (supportReducedA_weighted_entanglement_bound ψ)
      (supportReducedB_weighted_entanglement_bound ψ))
    (supportReducedD_weighted_entanglement_bound ψ))

end
end AmplitudeDamping
