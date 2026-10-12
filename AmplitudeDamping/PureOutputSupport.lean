import AmplitudeDamping.SupportStinespring

/-! # Pure outputs and supported Stinespring ranges

Finite environments are not restricted to qubits. An explicit isometric
coordinate map splits off a chosen environment direction, avoiding a choice
of a full orthonormal complement basis.
-/
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix NNReal Kronecker
namespace AmplitudeDamping
open QIT
noncomputable section
universe u
variable {e : Type u} [Fintype e] [DecidableEq e]

/-- Unit normalization in inner-product order. -/
theorem pureVector_inner_self (ψ : PureVector e) :
    ∑ i, star (ψ.amp i) * ψ.amp i = 1 := by
  have h := ψ.trace_rankOne_eq_one
  simpa [rankOneMatrix_trace, dotProduct, mul_comm] using h

theorem pureVector_amp_ne_zero (ψ : PureVector e) : ψ.amp ≠ 0 := by
  intro h
  have hn := pureVector_inner_self ψ
  rw [h] at hn
  simp at hn

/-- Orthogonal projection away from a normalized pure vector. -/
def pureComplement (ψ : PureVector e) : Matrix e e ℂ := 1 - ψ.state.matrix

theorem pureComplement_conjTranspose (ψ : PureVector e) :
    (pureComplement ψ).conjTranspose = pureComplement ψ := by
  rw [pureComplement, Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    ψ.state.pos.isHermitian.eq]

theorem pureComplement_idempotent (ψ : PureVector e) :
    pureComplement ψ * pureComplement ψ = pureComplement ψ := by
  simp only [pureComplement, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_one,
    Matrix.one_mul, ψ.state_matrix_mul_self, sub_self, sub_zero]

theorem pureComplement_mulVec (ψ : PureVector e) :
    (pureComplement ψ).mulVec ψ.amp = 0 := by
  have hP : ψ.state.matrix.mulVec ψ.amp = ψ.amp := by
    funext i
    simp only [Matrix.mulVec, dotProduct, PureVector.state_matrix_apply]
    rw [show (∑ j, ψ.amp i * star (ψ.amp j) * ψ.amp j) =
      ψ.amp i * ∑ j, star (ψ.amp j) * ψ.amp j by simp [Finset.mul_sum, mul_assoc],
      pureVector_inner_self, mul_one]
  rw [pureComplement, Matrix.sub_mulVec, Matrix.one_mulVec, hP, sub_self]

/-- Split off one unit environment direction. The residual coordinates are
kept in a copy of the original environment, so this is an isometry even when
the complement has dimension zero. -/
def environmentSplitMatrix (ψ : PureVector e) : Matrix (Unit ⊕ e) e ℂ :=
  Sum.elim (fun _ j => star (ψ.amp j)) (fun i j => pureComplement ψ i j)

theorem environmentSplitMatrix_isometry (ψ : PureVector e) :
    (environmentSplitMatrix ψ).conjTranspose * environmentSplitMatrix ψ = 1 := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Fintype.sum_sum_type,
    Fintype.sum_unique, environmentSplitMatrix, Sum.elim_inl, Sum.elim_inr, star_star]
  change ψ.state.matrix i j +
    ((pureComplement ψ).conjTranspose * pureComplement ψ) i j = _
  rw [pureComplement_conjTranspose, pureComplement_idempotent]
  simp [pureComplement]

theorem environmentSplitMatrix_residual_self (ψ : PureVector e) (i : e) :
    ((environmentSplitMatrix ψ).mulVec ψ.amp) (Sum.inr i) = 0 :=
  congrFun (pureComplement_mulVec ψ) i

/-- The residual environment coordinates annihilate the vector used to
construct their normalized distinguished direction. -/
theorem environmentSplitMatrix_residual_normalize
    (w : e → ℂ) (hw : 0 < (rankOneMatrix w).trace.re) (i : e) :
    ((environmentSplitMatrix (PureVector.normalize w hw)).mulVec w) (Sum.inr i) = 0 := by
  let s : ℂ := ((Real.sqrt (rankOneMatrix w).trace.re)⁻¹ : ℝ)
  have hs : s ≠ 0 := by
    dsimp [s]
    exact Complex.ofReal_ne_zero.mpr (inv_ne_zero (Real.sqrt_pos.mpr hw).ne')
  have h := environmentSplitMatrix_residual_self (PureVector.normalize w hw) i
  change ((environmentSplitMatrix (PureVector.normalize w hw)).mulVec (s • w)) (Sum.inr i) = 0 at h
  rw [Matrix.mulVec_smul, Pi.smul_apply, smul_eq_mul] at h
  exact (mul_eq_zero.mp h).resolve_left hs

/-- Any environment vector can be placed in the distinguished direction. -/
theorem exists_environmentSplit_annihilating [Nonempty e] (w : e → ℂ) :
    ∃ ψ : PureVector e, ∀ i : e,
      ((environmentSplitMatrix ψ).mulVec w) (Sum.inr i) = 0 := by
  by_cases hw : w = 0
  · refine ⟨basisPureVector (Classical.choice inferInstance), ?_⟩
    intro i
    simp [hw]
  · have hn : 0 < (rankOneMatrix w).trace.re := by
      have hex : ∃ i, w i ≠ 0 := by
        by_contra h
        push Not at h
        exact hw (funext h)
      obtain ⟨i, hi⟩ := hex
      have hpos : 0 < ∑ j, Complex.normSq (w j) :=
        Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i,
          (Complex.normSq_pos.mpr hi)⟩
      simpa [rankOneMatrix_trace, dotProduct, Complex.mul_conj] using hpos
    exact ⟨PureVector.normalize w hn, environmentSplitMatrix_residual_normalize w hn⟩


/-- A two-column matrix killing a nonzero vector has a common environment
direction for both columns. -/
theorem exists_environmentSplit_killing_matrix [Nonempty e]
    (W : Matrix e Qubit ℂ) (ψ : PureVector Qubit)
    (hW : W.mulVec ψ.amp = 0) :
    ∃ u : PureVector e, ∀ i : e, ∀ k : Qubit,
      (environmentSplitMatrix u * W) (Sum.inr i) k = 0 := by
  have he (j : e) : W j 0 * ψ.amp 0 + W j 1 * ψ.amp 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two] using congrFun hW j
  by_cases h0 : ψ.amp 0 = 0
  · have h1 : ψ.amp 1 ≠ 0 := by
      intro h1
      apply pureVector_amp_ne_zero ψ
      funext k
      fin_cases k <;> simp [h0, h1]
    have hc (j : e) : W j 1 = 0 := by
      have h := he j
      rw [h0, mul_zero, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_right h1
    obtain ⟨u, hu⟩ := exists_environmentSplit_annihilating (fun j => W j 0)
    refine ⟨u, ?_⟩
    intro i k
    fin_cases k
    · exact hu i
    · simp [Matrix.mul_apply, hc]
  · have hc (j : e) : W j 0 = W j 1 * (-ψ.amp 1 / ψ.amp 0) := by
      rw [← mul_div_assoc]
      apply (eq_div_iff h0).mpr
      have h := he j
      linear_combination h
    obtain ⟨u, hu⟩ := exists_environmentSplit_annihilating (fun j => W j 1)
    refine ⟨u, ?_⟩
    intro i k
    fin_cases k
    · change (environmentSplitMatrix u * W) (Sum.inr i) 0 = 0
      simp only [Matrix.mul_apply, hc, ← mul_assoc, ← Finset.sum_mul]
      change ((environmentSplitMatrix u).mulVec (fun j => W j 1)) (Sum.inr i) * _ = 0
      rw [hu i, zero_mul]
    · exact hu i

/-- Apply the output gauge while leaving the environment untouched. -/
def qubitOutputGauge (φ : PureVector Qubit) :
    TwoQubit.LocalIsometry Qubit Qubit e e where
  alice := ⟨qubitGaugeUnitary φ.amp,
    qubitGaugeUnitary_conjTranspose_mul φ.amp (pureVector_amp_ne_zero φ)⟩
  bob := ⟨1, by simp⟩

/-- Purity of the reduced output kills the orthogonal output branch after a
qubit basis change, without assumptions on environment dimension. -/
theorem pure_dilation_output_gauge_branch_zero
    (V : Matrix (Qubit × e) Qubit ℂ) (hV : V.conjTranspose * V = 1)
    (ψ φ : PureVector Qubit)
    (hφ : (isometryImageState V hV ψ.state).marginalA = φ.state) (j : e) :
    ((qubitOutputGauge (e := e) φ).matrix * V).mulVec ψ.amp (1,j) = 0 := by
  let χ := isometryVector V hV ψ
  let G := qubitOutputGauge (e := e) φ
  have hz : (G.applyState χ.state).marginalA.matrix 1 1 = 0 := by
    rw [localIsometry_applyState_marginalA_matrix, isometryVector_state, hφ]
    change (qubitGaugeUnitary φ.amp * rankOneMatrix φ.amp *
      (qubitGaugeUnitary φ.amp).conjTranspose) 1 1 = 0
    rw [← rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose,
      qubitGaugeUnitary_mulVec φ.amp (pureVector_amp_ne_zero φ)]
    simp [rankOneMatrix_apply, qubitKet0_one]
  have hj := joint_diagonal_zero_of_marginalA_zero (G.applyState χ.state) 1 hz j
  rw [localIsometry_applyState_pure, PureVector.state_matrix_apply] at hj
  have hnorm : Complex.normSq ((isometryVector G.matrix G.matrix_isometry χ).amp (1,j)) = 0 := by
    have h := congrArg Complex.re hj
    simpa [Complex.mul_conj] using h
  have hamp := Complex.normSq_eq_zero.mp hnorm
  simpa only [isometryVector_amp, χ, Matrix.mulVec_mulVec] using hamp

/-- Reorder the qubit output so that its vacuum is the right-hand unit
summand used by the support theorem. -/
def qubitSupportRows (U : Matrix Qubit Qubit ℂ) : Matrix (Unit ⊕ Unit) Qubit ℂ :=
  Sum.elim (fun _ j => U 1 j) (fun _ j => U 0 j)

theorem qubitSupportRows_isometry (U : Matrix Qubit Qubit ℂ)
    (hU : U.conjTranspose * U = 1) :
    (qubitSupportRows U).conjTranspose * qubitSupportRows U = 1 := by
  ext i j
  have h := congrFun (congrFun hU i) j
  simpa [Matrix.mul_apply, Matrix.conjTranspose_apply, qubitSupportRows,
    Fintype.sum_sum_type, Fin.sum_univ_two, add_comm] using h


/-- The non-vacuum output block after an output gauge. -/
def gaugedEnvironmentBlock (U : Matrix Qubit Qubit ℂ)
    (V : Matrix (Qubit × e) Qubit ℂ) : Matrix e Qubit ℂ :=
  fun j k => ((U ⊗ₖ (1 : Matrix e e ℂ)) * V) (1,j) k

theorem gaugedEnvironmentBlock_apply (U : Matrix Qubit Qubit ℂ)
    (V : Matrix (Qubit × e) Qubit ℂ) (j : e) (k : Qubit) :
    gaugedEnvironmentBlock U V j k = ∑ i : Qubit, U 1 i * V (i,j) k := by
  simp [gaugedEnvironmentBlock, Matrix.mul_apply, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type, Matrix.one_apply]

theorem supported_gauge_block_entry (U : Matrix Qubit Qubit ℂ)
    (V : Matrix (Qubit × e) Qubit ℂ) (u : PureVector e) (j : e) (k : Qubit) :
    ((qubitSupportRows U ⊗ₖ environmentSplitMatrix u) * V) (Sum.inl (), Sum.inr j) k =
      (environmentSplitMatrix u * gaugedEnvironmentBlock U V) (Sum.inr j) k := by
  simp only [Matrix.mul_apply, Fintype.sum_prod_type, Matrix.kroneckerMap_apply,
    qubitSupportRows, Sum.elim_inl, gaugedEnvironmentBlock_apply]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro l _
  ring

/-- Concrete local coordinates determined by an output unitary and one
normalized environment direction. -/
def pureOutputCoordinates (U : Matrix Qubit Qubit ℂ)
    (hU : U.conjTranspose * U = 1) (u : PureVector e) :
    TwoQubit.LocalIsometry Qubit (Unit ⊕ Unit) e (Unit ⊕ e) where
  alice := ⟨qubitSupportRows U, qubitSupportRows_isometry U hU⟩
  bob := ⟨environmentSplitMatrix u, environmentSplitMatrix_isometry u⟩

/-- A pure output supplies supported local Stinespring coordinates for any
finite environment. The target environment is `Unit ⊕ E`, an isometric
coordinate enlargement that explicitly represents the distinguished vector
and its orthogonal complement. -/
theorem pure_output_exists_split_stinespring_coordinates
    (N : Channel Qubit Qubit) (V : Matrix (Qubit × e) Qubit ℂ)
    (hV : V.conjTranspose * V = 1) (hN : StinespringRealizes N V)
    (ψ φ : PureVector Qubit) (hφ : N.applyState ψ.state = φ.state) :
    ∃ (U : Matrix Qubit Qubit ℂ) (hU : U.conjTranspose * U = 1) (u : PureVector e),
      HasSupportedStinespringRange V (pureOutputCoordinates U hU u) := by
  let χ := isometryVector V hV ψ
  letI : Nonempty e := χ.state.nonempty.map Prod.snd
  let U := qubitGaugeUnitary φ.amp
  have hU := qubitGaugeUnitary_conjTranspose_mul φ.amp (pureVector_amp_ne_zero φ)
  have houtput : (isometryImageState V hV ψ.state).marginalA = φ.state := by
    apply State.ext
    rw [State.marginalA_matrix, isometryImageState_matrix, hN]
    exact congrArg State.matrix hφ
  have hk : (gaugedEnvironmentBlock U V).mulVec ψ.amp = 0 := by
    funext j
    exact pure_dilation_output_gauge_branch_zero V hV ψ φ houtput j
  obtain ⟨u, hu⟩ := exists_environmentSplit_killing_matrix (gaugedEnvironmentBlock U V) ψ hk
  refine ⟨U, hU, u, ?_⟩
  intro i j k
  cases i
  exact (supported_gauge_block_entry U V u j k).trans (hu j k)


/-- Every scalar linear functional on a qubit has a unit vector in its kernel. -/
theorem exists_pure_qubit_annihilating (l : Qubit → ℂ) :
    ∃ ψ : PureVector Qubit, ∑ k, l k * ψ.amp k = 0 := by
  by_cases hl : l = 0
  · refine ⟨basisPureVector 0, ?_⟩
    simp [hl]
  · let w : Qubit → ℂ := ![l 1, -l 0]
    have hw : 0 < (rankOneMatrix w).trace.re := by
      have hex : ∃ i, l i ≠ 0 := by
        by_contra h
        push Not at h
        exact hl (funext h)
      obtain ⟨i, hi⟩ := hex
      have ht : 0 < Complex.normSq (l 0) + Complex.normSq (l 1) := by
        fin_cases i
        · have hp : 0 < Complex.normSq (l 0) := Complex.normSq_pos.mpr hi
          linarith [Complex.normSq_nonneg (l 1)]
        · have hp : 0 < Complex.normSq (l 1) := Complex.normSq_pos.mpr hi
          linarith [Complex.normSq_nonneg (l 0)]
      simpa [w, rankOneMatrix_trace, dotProduct, Complex.mul_conj, Fin.sum_univ_two,
        Complex.normSq_neg, add_comm] using ht
    refine ⟨PureVector.normalize w hw, ?_⟩
    simp [PureVector.normalize, w, Fin.sum_univ_two]
    ring

/-- A pure bipartite vector confined to the first qubit row has a pure output. -/
theorem pure_qubit_marginal_of_zero_second_row
    {f : Type*} [Fintype f] [DecidableEq f]
    (χ : PureVector (Qubit × f)) (hz : ∀ j, χ.amp (1,j) = 0) :
    χ.state.marginalA = (basisPureVector (0 : Qubit)).state := by
  have htrace := χ.state.marginalA.trace_eq_one
  have h00 : χ.state.marginalA.matrix 0 0 = 1 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two, State.marginalA_matrix,
      partialTraceB, PureVector.state_matrix_apply, hz] using htrace
  apply State.ext
  ext i j
  fin_cases i <;> fin_cases j
  · simpa [basisPureVector] using h00
  · simp [State.marginalA_matrix, partialTraceB, PureVector.state_matrix_apply, hz,
      basisPureVector]
  · simp [State.marginalA_matrix, partialTraceB, PureVector.state_matrix_apply, hz,
      basisPureVector]
  · simp [State.marginalA_matrix, partialTraceB, PureVector.state_matrix_apply, hz,
      basisPureVector]


/-- Existential local-isometry interface consumed directly by the support
criterion. Its witness is constructed by the preceding theorem. -/
theorem pure_output_exists_supported_stinespring_coordinates
    (N : Channel Qubit Qubit) (V : Matrix (Qubit × e) Qubit ℂ)
    (hV : V.conjTranspose * V = 1) (hN : StinespringRealizes N V)
    (ψ φ : PureVector Qubit) (hφ : N.applyState ψ.state = φ.state) :
    ∃ L : TwoQubit.LocalIsometry Qubit (Unit ⊕ Unit) e (Unit ⊕ e),
      HasSupportedStinespringRange V L := by
  obtain ⟨U, hU, u, h⟩ := pure_output_exists_split_stinespring_coordinates N V hV hN ψ φ hφ
  exact ⟨pureOutputCoordinates U hU u, h⟩

/-- Pure-output property, with explicitly normalized pure input and output. -/
def HasPureQubitOutput (N : Channel Qubit Qubit) : Prop :=
  ∃ ψ φ : PureVector Qubit, N.applyState ψ.state = φ.state

/-- Supported range coordinates force a pure output: the single remaining
non-vacuum coefficient is a scalar functional on the two-dimensional input,
so a unit vector in its kernel has a product dilation. -/
theorem supported_split_stinespring_has_pure_output
    (N : Channel Qubit Qubit) (V : Matrix (Qubit × e) Qubit ℂ)
    (hV : V.conjTranspose * V = 1) (hN : StinespringRealizes N V)
    (U : Matrix Qubit Qubit ℂ) (hU : U.conjTranspose * U = 1) (u : PureVector e)
    (hs : HasSupportedStinespringRange V (pureOutputCoordinates U hU u)) :
    HasPureQubitOutput N := by
  let G : TwoQubit.LocalIsometry Qubit Qubit e (Unit ⊕ e) :=
    { alice := ⟨U, hU⟩
      bob := ⟨environmentSplitMatrix u, environmentSplitMatrix_isometry u⟩ }
  let F := G.matrix * V
  have hF : F.conjTranspose * F = 1 := by
    simp only [F, Matrix.conjTranspose_mul]
    calc V.conjTranspose * G.matrix.conjTranspose * (G.matrix * V)
      = V.conjTranspose * (G.matrix.conjTranspose * G.matrix) * V := by
          simp only [Matrix.mul_assoc]
      _ = 1 := by rw [G.matrix_isometry, Matrix.mul_one, hV]
  obtain ⟨ψ, hψ⟩ := exists_pure_qubit_annihilating (fun k => F (1, Sum.inl ()) k)
  let χ := isometryVector F hF ψ
  have hz : ∀ j, χ.amp (1,j) = 0 := by
    intro j
    rcases j with ⟨⟩ | j
    · exact hψ
    · change ∑ k, F (1, Sum.inr j) k * ψ.amp k = 0
      have he (k : Qubit) : F (1, Sum.inr j) k =
          ((pureOutputCoordinates U hU u).matrix * V) (Sum.inl (), Sum.inr j) k := rfl
      simp only [he, hs () j, zero_mul, Finset.sum_const_zero]
  have hχ := pure_qubit_marginal_of_zero_second_row χ hz
  have hstate : χ.state = G.applyState (isometryImageState V hV ψ.state) := by
    apply State.ext
    rw [isometryVector_state_matrix, TwoQubit.LocalIsometry.applyState_matrix,
      TwoQubit.LocalIsometry.applyMatrix, isometryImageState_matrix]
    simp only [F, Matrix.conjTranspose_mul, PureVector.state_matrix, Matrix.mul_assoc]
  have hout : (isometryImageState V hV ψ.state).marginalA = N.applyState ψ.state := by
    apply State.ext
    exact hN ψ.state.matrix
  have he : U * (N.applyState ψ.state).matrix * U.conjTranspose =
      (basisPureVector (0 : Qubit)).state.matrix := by
    have hm := congrArg State.matrix hχ
    rw [hstate, localIsometry_applyState_marginalA_matrix, hout] at hm
    exact hm
  have hU' : U * U.conjTranspose = 1 := mul_eq_one_comm.mp hU
  let φ := isometryVector U.conjTranspose (by simpa using hU') (basisPureVector (0 : Qubit))
  refine ⟨ψ, φ, ?_⟩
  apply State.ext
  rw [isometryVector_state_matrix]
  change (N.applyState ψ.state).matrix =
    U.conjTranspose * (basisPureVector (0 : Qubit)).state.matrix * U.conjTranspose.conjTranspose
  rw [← he]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U.conjTranspose U, hU, Matrix.one_mul, Matrix.mul_one]

/-- Pure outputs are equivalent to supported Stinespring range coordinates,
for every finite environment. The coordinates explicitly encode suitable
unit output and environment directions. -/
theorem pure_output_iff_split_stinespring_support
    (N : Channel Qubit Qubit) (V : Matrix (Qubit × e) Qubit ℂ)
    (hV : V.conjTranspose * V = 1) (hN : StinespringRealizes N V) :
    HasPureQubitOutput N ↔
      ∃ (U : Matrix Qubit Qubit ℂ) (hU : U.conjTranspose * U = 1) (u : PureVector e),
        HasSupportedStinespringRange V (pureOutputCoordinates U hU u) := by
  constructor
  · rintro ⟨ψ, φ, hφ⟩
    exact pure_output_exists_split_stinespring_coordinates N V hV hN ψ φ hφ
  · rintro ⟨U, hU, u, hs⟩
    exact supported_split_stinespring_has_pure_output N V hV hN U hU u hs


/-- Canonical finite Stinespring stack realizes the channel on all matrices. -/
theorem canonical_stinespring_realizes (N : Channel Qubit Qubit) :
    StinespringRealizes N (MatrixMap.krausStinespringMatrix N.kraus) := by
  intro X
  rw [MatrixMap.partialTraceB_krausStinespringMatrix, ← N.map_eq_ofKraus]

/-- Pure-output qubit channels obey roof SSA against arbitrary partners.
The canonical environment is finite but has no Kraus-rank-two restriction. -/
theorem pure_output_outputEntropyRoof_prod_ge
    (N : Channel Qubit Qubit) (hpure : HasPureQubitOutput N)
    {y z : Type*} [Fintype y] [DecidableEq y] [Fintype z] [DecidableEq z]
    (M : Channel y z) (τ : State (Qubit × y)) :
    outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB ≤
      outputEntropyRoof (N.prod M) τ := by
  obtain ⟨ψ, φ, hφ⟩ := hpure
  have hV := MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
    N.kraus N.krausAdjoint_one
  obtain ⟨L, hL⟩ := pure_output_exists_supported_stinespring_coordinates N
    (MatrixMap.krausStinespringMatrix N.kraus) hV (canonical_stinespring_realizes N) ψ φ hφ
  exact outputEntropyRoof_prod_ge_of_supported_stinespring N _ hV
    (canonical_stinespring_realizes N) L hL M τ

/-- Strong Holevo additivity for the full pure-output qubit-channel class. -/
theorem pure_output_strongHolevoAdditive
    (N : Channel Qubit Qubit) (hpure : HasPureQubitOutput N) :
    CapacityAdditivity.StrongHolevoAdditive N := by
  intro y z _ _ _ _ _ M
  exact generic_holevoInformation_prod_eq N M
    (pure_output_outputEntropyRoof_prod_ge N hpure M)

/-- Pure-output qubit channels have a single-letter operational capacity. -/
theorem pure_output_classicalCapacity_eq_holevoInformation
    (N : Channel Qubit Qubit) (hpure : HasPureQubitOutput N) :
    Channel.classicalCapacity.{0,0,0} N = Channel.holevoInformation.{0,0,0} N := by
  rw [Channel.classicalCapacity_eq_regularizedHolevoInformation]
  exact CapacityAdditivity.regularizedHolevoInformation_eq N
    (pure_output_strongHolevoAdditive N hpure)

/-- Their operational capacity is additive against every arbitrary finite
partner, including partners whose own capacity requires regularization. -/
theorem pure_output_classicalCapacity_prod_eq
    (N : Channel Qubit Qubit) (hpure : HasPureQubitOutput N)
    {y z : Type} [Fintype y] [DecidableEq y] [Fintype z] [DecidableEq z]
    [Nonempty y] [Nonempty z] (M : Channel y z) :
    Channel.classicalCapacity.{0,0,0} (N.prod M) =
      Channel.classicalCapacity.{0,0,0} N + Channel.classicalCapacity.{0,0,0} M :=
  CapacityAdditivity.classicalCapacity_prod_eq N
    (pure_output_strongHolevoAdditive N hpure) M

end
end AmplitudeDamping
