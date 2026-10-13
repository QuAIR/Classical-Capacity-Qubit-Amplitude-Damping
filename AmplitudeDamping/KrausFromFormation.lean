import AmplitudeDamping.KrausCostProperties
import QIT.States.Purification.Canonical

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder NNReal
namespace AmplitudeDamping
open QIT
noncomputable section
set_option maxHeartbeats 1500000
universe u v
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- A faithful canonical purification distinguishes all linear matrix maps. -/
theorem canonicalPurification_map_injective (ρ : State a)
    (hρ : ρ.matrix.PosDef) (F G : MatrixMap a b)
    (h : MatrixMap.kron (Channel.idChannel a).map F ρ.canonicalPurification.state.matrix =
      MatrixMap.kron (Channel.idChannel a).map G ρ.canonicalPurification.state.matrix) : F = G := by
  classical
  let S := ρ.sqrtMatrix
  have hS : IsUnit S := by
    have hs : IsUnit (S * S) := by simpa [S] using hρ.isUnit
    exact isUnit_of_mul_isUnit_left hs
  have hc : F.comp (MatrixMap.ofKraus (fun _ : Unit => S)) =
      G.comp (MatrixMap.ofKraus (fun _ : Unit => S)) := by
    apply MatrixMap.choi_inj
    ext x y
    have hh := congrFun (congrFun h x) y
    rw [MatrixMap.kron_idChannel_left_apply_slice,
      MatrixMap.kron_idChannel_left_apply_slice] at hh
    have he : (fun j j' => ρ.canonicalPurification.state.matrix (x.1, j) (y.1, j')) =
        MatrixMap.ofKraus (fun _ : Unit => S) (Matrix.single x.1 y.1 1) := by
      ext j j'
      simp [MatrixMap.ofKraus, Matrix.mul_apply, Matrix.conjTranspose_apply,
        State.canonicalPurification,
        State.canonicalPurificationAmp, S, Matrix.single, eq_comm, ite_and]
    change F _ _ _ = G _ _ _
    rwa [he] at hh
  apply LinearMap.ext
  intro X
  have hh := LinearMap.congr_fun hc (S⁻¹ * X * S⁻¹.conjTranspose)
  have hi : S * S⁻¹ = 1 := Matrix.mul_nonsing_inv S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  have hi' : S⁻¹.conjTranspose * S.conjTranspose = 1 := by
    simpa using congrArg Matrix.conjTranspose hi
  have hiX : S * (S⁻¹ * X) = X := by rw [← Matrix.mul_assoc, hi, Matrix.one_mul]
  simpa only [LinearMap.comp_apply, MatrixMap.ofKraus, LinearMap.coe_mk,
    AddHom.coe_mk, Fintype.sum_unique, ← Matrix.mul_assoc, hi, Matrix.one_mul,
    Matrix.mul_assoc, hi', Matrix.mul_one, hiX] using hh


/-- Every pure decomposition of a faithful reference output is induced by a
finite Kraus representation, with exactly its decomposition cost. -/
theorem kraus_of_faithful_decomposition (N : Channel a b) (ρ : State a)
    (hρ : ρ.matrix.PosDef) (E : PureDecomposition (a × b))
    (hE : E.averageState = ((Channel.idChannel a).prod N).applyState
      ρ.canonicalPurification.state) :
    ∃ (K : Fin E.card → Matrix b a ℂ) (hK : MatrixMap.ofKraus K = N.map),
      (krausEntropyInstrument N K hK).cost ρ = E.entanglementCost := by
  classical
  let S := ρ.sqrtMatrix
  have hS : IsUnit S := by
    have hs : IsUnit (S * S) := by simpa [S] using hρ.isUnit
    exact isUnit_of_mul_isUnit_left hs
  have hi : S⁻¹ * S = 1 := Matrix.nonsing_inv_mul S ((Matrix.isUnit_iff_isUnit_det S).mp hS)
  let v : Fin E.card → a × b → ℂ := fun i x =>
    (Real.sqrt (E.probs i : ℝ) : ℂ) * (E.vectors i).amp x
  let V : Fin E.card → Matrix b a ℂ := fun i j r => v i (r, j)
  let K : Fin E.card → Matrix b a ℂ := fun i => V i * S⁻¹
  have hv (i : Fin E.card) : rankOneMatrix (v i) =
      (E.probs i : ℂ) • (E.vectors i).state.matrix := by
    have hs : (Real.sqrt (E.probs i : ℝ) : ℂ) *
        (Real.sqrt (E.probs i : ℝ) : ℂ) = (E.probs i : ℂ) := by
      norm_cast
      exact Real.mul_self_sqrt (NNReal.coe_nonneg _)
    ext x y
    simp only [rankOneMatrix_apply, v, star_mul, Complex.star_def, Complex.conj_ofReal,
      PureVector.state_matrix, Matrix.smul_apply, smul_eq_mul]
    calc
      _ = ((Real.sqrt (E.probs i : ℝ) : ℂ) * (Real.sqrt (E.probs i : ℝ) : ℂ)) *
          ((E.vectors i).amp x * starRingEnd ℂ ((E.vectors i).amp y)) := by ring
      _ = _ := by rw [hs]
  have hKv (i : Fin E.card) (x : a × b) :
      (∑ r, K i x.2 r * ρ.canonicalPurification.amp (x.1, r)) = v i x := by
    change ((V i * S⁻¹) * S) x.2 x.1 = _
    rw [Matrix.mul_assoc, hi, Matrix.mul_one]
  have hbranch (i : Fin E.card) :
      MatrixMap.kron (Channel.idChannel a).map
        (MatrixMap.ofKraus (fun _ : Unit => K i)) ρ.canonicalPurification.state.matrix =
      (E.probs i : ℂ) • (E.vectors i).state.matrix := by
    rw [PureVector.state_matrix, ← sum_referenceKraus_rankOne]
    simpa only [Fintype.sum_unique, hKv] using hv i
  have hK : MatrixMap.ofKraus K = N.map := by
    apply canonicalPurification_map_injective ρ hρ
    rw [PureVector.state_matrix, ← sum_referenceKraus_rankOne]
    simp_rw [hKv, hv]
    exact congrArg State.matrix hE
  refine ⟨K, hK, ?_⟩
  apply Finset.sum_congr rfl
  intro i _
  have hm : MatrixMap.ofKraus (fun _ : Unit => K i) ρ.matrix =
      (E.probs i : ℂ) • (E.vectors i).state.marginalB.matrix := by
    have hh := congrArg partialTraceA (hbranch i)
    rw [partialTraceA_mapKron _ _ (Channel.idChannel a).tracePreserving] at hh
    rw [show partialTraceA ρ.canonicalPurification.state.matrix = ρ.matrix from
      ρ.canonicalPurification_matrix] at hh
    exact hh.trans (by ext j k; simp [partialTraceA, State.marginalB_matrix, Finset.mul_sum])
  change entropyPerspective (MatrixMap.ofKraus (fun _ : Unit => K i) ρ.matrix) _ = _
  rw [entropyPerspective_congr hm _ ((E.vectors i).state.marginalB.pos.smul
    (by exact_mod_cast (NNReal.coe_nonneg (E.probs i)))),
    entropyPerspective_smul (E.probs i : ℝ) (NNReal.coe_nonneg _)
      (E.vectors i).state.marginalB.matrix (E.vectors i).state.marginalB.pos]
  rw [State.pureVector_marginalA_vonNeumann_eq_marginalB]
  congr 1
  unfold entropyPerspective
  rw [(E.vectors i).state.marginalB.trace_re_eq_one]
  simp only [xlog2, one_ne_zero, if_false, log2, Real.log_one, zero_div,
    mul_zero, add_zero]
  rfl

/-- Pointwise near-optimal Kraus costs at a faithful input. -/
theorem faithful_exists_krausCost_le (N : Channel a b) (ρ : State a)
    (hρ : ρ.matrix.PosDef) (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (K : Fin n → Matrix b a ℂ) (hK : MatrixMap.ofKraus K = N.map),
      (krausEntropyInstrument N K hK).cost ρ ≤ channelEntanglementOfFormation N + δ := by
  obtain ⟨x, ⟨E, hE, rfl⟩, hx⟩ := Real.lt_sInf_add_pos
    (pureEntanglementValues_nonempty (((Channel.idChannel a).prod N).applyState
      ρ.canonicalPurification.state)) hδ
  obtain ⟨K, hK, hc⟩ := kraus_of_faithful_decomposition N ρ hρ E hE
  refine ⟨E.card, K, hK, ?_⟩
  rw [hc]
  have hb := channelFormationAt_le N ρ.canonicalPurification
  change E.entanglementCost < channelFormationAt N ρ.canonicalPurification + δ at hx
  linarith


/-- At each input, a finite Kraus representation achieves the channel formation
value up to any positive tolerance. Singular inputs follow by faithful mixing. -/
theorem pointwise_exists_krausCost_le (N : Channel a b) (ρ : State a)
    (δ : ℝ) (hδ : 0 < δ) :
    ∃ (n : ℕ) (K : Fin n → Matrix b a ℂ) (hK : MatrixMap.ofKraus K = N.map),
      (krausEntropyInstrument N K hK).cost ρ ≤ channelEntanglementOfFormation N + δ := by
  letI : Nonempty a := ρ.nonempty
  let C := channelEntanglementOfFormation N
  have hC : 0 ≤ C := channelEntanglementOfFormation_nonneg N
  have hCd : 0 < C + δ := by positivity
  let ε := δ / (2 * (C + δ))
  have hε : 0 < ε := div_pos hδ (by positivity)
  have hεhalf : ε ≤ 1 / 2 := by
    apply (div_le_iff₀ (by positivity : 0 < 2 * (C + δ))).mpr
    linarith
  have hε1 : ε ≤ 1 := by linarith
  have hεprod : ε * (C + δ) = δ / 2 := by
    dsimp [ε]
    field_simp
  let σ := State.maximallyMixed a
  let τ := ρ.regularizedWithState σ ε hε.le hε1
  have hτ : τ.matrix.PosDef :=
    State.regularizedWithState_posDef_of_noise ρ σ State.maximallyMixed_posDef
      hε.le hε1 hε
  obtain ⟨n, K, hK, hc⟩ := faithful_exists_krausCost_le N τ hτ (δ / 2) (by positivity)
  refine ⟨n, K, hK, ?_⟩
  let F := krausEntropyInstrument N K hK
  have hconc := F.cost_combo_ge ρ σ τ (1 - ε) ε (by linarith) hε.le rfl
  have hn := mul_nonneg hε.le (F.cost_nonneg σ)
  have hbound : (1 - ε) * F.cost ρ ≤ (1 - ε) * (C + δ) := by
    change F.cost τ ≤ C + δ / 2 at hc
    nlinarith
  exact (mul_le_mul_iff_right₀ (by linarith : 0 < 1 - ε)).mp hbound

end
end AmplitudeDamping
