import AmplitudeDamping.PureOutputSupport
import AmplitudeDamping.ChannelChoi
import AmplitudeDamping.UnifiedCost
import Mathlib.Analysis.Matrix.Order

/-! # Pure outputs and product vectors in the Choi kernel -/
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix NNReal Kronecker
namespace AmplitudeDamping
open QIT
noncomputable section

/-- The manuscript's normalized Choi product-expectation identity. Input
conjugation is explicit and depends on the basis used to define the Bell state. -/
theorem channelChoiState_product_expectation
    (N : Channel Qubit Qubit) (a b : Qubit → ℂ) :
    star (fun p : Qubit × Qubit => a p.1 * b p.2) ⬝ᵥ
        (channelChoiState N).matrix.mulVec (fun p => a p.1 * b p.2) =
      (1 / 2 : ℂ) * (star b ⬝ᵥ
        (N.map (rankOneMatrix (fun i => star (a i)))).mulVec b) := by
  rw [channelChoiState_matrix, MatrixMap.map_eq_sum_single N.map]
  simp only [dotProduct, Matrix.mulVec, Fintype.sum_prod_type, Fin.sum_univ_two,
    Matrix.smul_apply, smul_eq_mul, MatrixMap.choi, rankOneMatrix_apply,
    Matrix.sum_apply, star_mul, Pi.star_apply, star_star]
  norm_num [Qubit]
  ring

/-- A qubit state with a nonzero kernel vector is pure. The proof rotates the
kernel vector to the second coordinate, then uses trace one and positivity. -/
theorem qubit_state_pure_of_kernel (ρ : State Qubit) (b : Qubit → ℂ)
    (hb : b ≠ 0) (hk : ρ.matrix.mulVec b = 0) :
    ∃ φ : PureVector Qubit, ρ = φ.state := by
  let U := qubitGaugeUnitaryOne b
  have hU : U.conjTranspose * U = 1 := qubitGaugeUnitaryOne_conjTranspose_mul b hb
  have hU' : U * U.conjTranspose = 1 := mul_eq_one_comm.mp hU
  let σ := isometryImageState U hU ρ
  have hcol : σ.matrix.mulVec qubitKet1 = 0 := by
    rw [isometryImageState_matrix, ← Matrix.mulVec_mulVec,
      qubitGaugeUnitaryOne_conjTranspose_mulVec_ket1]
    have hn : (fun x => b x / (qubitNorm b : ℂ)) = (qubitNorm b : ℂ)⁻¹ • b := by
      funext i
      simp [div_eq_mul_inv, mul_comm]
    rw [hn, ← Matrix.mulVec_mulVec, Matrix.mulVec_smul, hk, smul_zero, Matrix.mulVec_zero]
  have hc (i : Qubit) : σ.matrix i 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_two, qubitKet1] using congrFun hcol i
  have hr (j : Qubit) : σ.matrix 1 j = 0 := by
    have hh := congrFun (congrFun σ.pos.isHermitian.eq j) 1
    simpa [Matrix.conjTranspose_apply, hc] using congrArg star hh
  have h00 : σ.matrix 0 0 = 1 := by
    simpa [Matrix.trace, Matrix.diag, Fin.sum_univ_two, hc] using σ.trace_eq_one
  have hs : σ = (basisPureVector (0 : Qubit)).state := by
    apply State.ext
    ext i j
    fin_cases i <;> fin_cases j <;> simp [basisPureVector, h00, hc, hr]
  let φ := isometryVector U.conjTranspose (by simpa using hU') (basisPureVector (0 : Qubit))
  refine ⟨φ, ?_⟩
  apply State.ext
  rw [isometryVector_state_matrix]
  change ρ.matrix = U.conjTranspose * (basisPureVector (0 : Qubit)).state.matrix * U.conjTranspose.conjTranspose
  rw [← hs, isometryImageState_matrix]
  simp only [Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
  rw [← Matrix.mul_assoc U.conjTranspose U, hU, Matrix.one_mul, Matrix.mul_one]

/-- Every nonzero vector has positive rank-one trace. -/
theorem rankOne_trace_re_pos_of_ne_zero {a : Type*} [Fintype a] [DecidableEq a]
    (v : a → ℂ) (hv : v ≠ 0) : 0 < (rankOneMatrix v).trace.re := by
  have hex : ∃ i, v i ≠ 0 := by
    by_contra h
    push Not at h
    exact hv (funext h)
  obtain ⟨i, hi⟩ := hex
  have hp : 0 < ∑ j, Complex.normSq (v j) :=
    Finset.sum_pos' (fun j _ => Complex.normSq_nonneg _) ⟨i, Finset.mem_univ i,
      Complex.normSq_pos.mpr hi⟩
  simpa [rankOneMatrix_trace, dotProduct, Complex.mul_conj] using hp


/-- A nonzero product vector in the normalized Choi state's kernel. -/
def HasChoiProductKernel (N : Channel Qubit Qubit) : Prop :=
  ∃ a b : Qubit → ℂ, a ≠ 0 ∧ b ≠ 0 ∧
    (channelChoiState N).matrix.mulVec (fun p => a p.1 * b p.2) = 0

/-- Any pure output produces a product vector in the Choi kernel. -/
theorem pure_output_has_choi_product_kernel (N : Channel Qubit Qubit)
    (hp : HasPureQubitOutput N) : HasChoiProductKernel N := by
  obtain ⟨ψ, φ, hφ⟩ := hp
  obtain ⟨b, hb⟩ := exists_pure_qubit_annihilating (fun k => star (φ.amp k))
  let a : Qubit → ℂ := fun i => star (ψ.amp i)
  have ha : a ≠ 0 := by
    intro h
    apply pureVector_amp_ne_zero ψ
    funext i
    have hi := congrFun h i
    simpa [a] using congrArg star hi
  refine ⟨a, b.amp, ha, pureVector_amp_ne_zero b, ?_⟩
  apply ((channelChoiState N).pos.dotProduct_mulVec_zero_iff _).mp
  rw [channelChoiState_product_expectation]
  have hout : N.map (rankOneMatrix (fun i => star (a i))) = φ.state.matrix := by
    simpa [a, PureVector.state_matrix] using congrArg State.matrix hφ
  rw [hout]
  have hk : φ.state.matrix.mulVec b.amp = 0 := by
    funext i
    change ∑ j, (φ.amp i * star (φ.amp j)) * b.amp j = 0
    simp only [mul_assoc, ← Finset.mul_sum, hb, mul_zero]
  rw [hk]
  simp

/-- Conversely, a product kernel vector of the Choi state gives a pure output. -/
theorem choi_product_kernel_has_pure_output (N : Channel Qubit Qubit)
    (hp : HasChoiProductKernel N) : HasPureQubitOutput N := by
  obtain ⟨a, b, ha, hb, hk⟩ := hp
  let v : Qubit → ℂ := fun i => star (a i)
  have hv : v ≠ 0 := by
    intro h
    apply ha
    funext i
    have hi := congrFun h i
    simpa [v] using congrArg star hi
  have ht := rankOne_trace_re_pos_of_ne_zero v hv
  let ψ := PureVector.normalize v ht
  have he : star b ⬝ᵥ (N.map (rankOneMatrix v)).mulVec b = 0 := by
    have hh := channelChoiState_product_expectation N a b
    rw [hk] at hh
    have hz : (1 / 2 : ℂ) * (star b ⬝ᵥ (N.map (rankOneMatrix v)).mulVec b) = 0 := by
      simpa [v] using hh.symm
    exact (mul_eq_zero.mp hz).resolve_left (by norm_num)
  have he' : star b ⬝ᵥ (N.applyState ψ.state).matrix.mulVec b = 0 := by
    change star b ⬝ᵥ (N.map ψ.state.matrix).mulVec b = 0
    rw [PureVector.normalize_state_matrix, map_smul, Matrix.smul_mulVec, dotProduct_smul, he,
      smul_zero]
  obtain ⟨φ, hφ⟩ := qubit_state_pure_of_kernel (N.applyState ψ.state) b hb
    (((N.applyState ψ.state).pos.dotProduct_mulVec_zero_iff b).mp he')
  exact ⟨ψ, φ, hφ⟩

/-- Qubit channels have a pure output exactly when their Choi kernel contains
  a nonzero product vector. No convex-roof or classical decomposition input is needed. -/
theorem pure_output_iff_choi_product_kernel (N : Channel Qubit Qubit) :
    HasPureQubitOutput N ↔ HasChoiProductKernel N :=
  ⟨pure_output_has_choi_product_kernel N, choi_product_kernel_has_pure_output N⟩


/-- At most two Kraus operators guarantee a pure output, through the
low-rank Choi product-kernel theorem. -/
theorem twoKraus_has_pure_output
    {κ : Type*} [Fintype κ]
    (N : Channel Qubit Qubit) (K : κ → Matrix Qubit Qubit ℂ)
    (hN : N.map = MatrixMap.ofKraus K) (hcard : Fintype.card κ ≤ 2) :
    HasPureQubitOutput N := by
  apply choi_product_kernel_has_pure_output N
  exact channelChoiState_product_kernel_of_twoKraus N K hN hcard

/-- Pure-output qubit channels are strongly additive for channel formation. -/
theorem pure_output_strongFormation
    (hsub : GeneralChannelFormationSubadditivity)
    (N : Channel Qubit Qubit) (hp : HasPureQubitOutput N) :
    FormationRegularization.StrongFormationAdditive N := by
  obtain ⟨u, v, hu, hv, hk⟩ := pure_output_has_choi_product_kernel N hp
  exact strongFormation_of_productKernel hsub N u v hu hv hk

/-- Pure-output extension of the operational channel and Choi-state cost identities. -/
theorem pure_output_unified_cost
    (hsub : GeneralChannelFormationSubadditivity)
    (hstate : StateCostRegularization) (hparallel : ParallelCostRegularization)
    (N : Channel Qubit Qubit) (hp : HasPureQubitOutput N) :
    parallelEntanglementCost N = entanglementOfFormation (channelChoiState N) ∧
    operationalStateCost (channelChoiState N) = entanglementOfFormation (channelChoiState N) ∧
    channelEntanglementOfFormation N = entanglementOfFormation (channelChoiState N) := by
  obtain ⟨u, v, hu, hv, hk⟩ := pure_output_has_choi_product_kernel N hp
  exact unified_cost_of_productKernel hsub hstate hparallel N u v hu hv hk

/-- Operational parallel channel cost is additive with every finite partner. -/
theorem pure_output_parallelCost_prod_eq
    (hsub : GeneralChannelFormationSubadditivity)
    (hparallel : ParallelCostRegularization)
    (N : Channel Qubit Qubit) (hp : HasPureQubitOutput N)
    {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] [Nonempty d] (M : Channel c d) :
    parallelEntanglementCost (N.prod M) =
      parallelEntanglementCost N + parallelEntanglementCost M :=
  parallelEntanglementCost_prod_eq_of_strong hparallel N
    (pure_output_strongFormation hsub N hp) M

end
end AmplitudeDamping
