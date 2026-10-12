import AmplitudeDamping.InstrumentProduct
import AmplitudeDamping.ChannelFormationProduct
import AmplitudeDamping.UnifiedFormation
import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm.Complement

/-!
# Uniform Kraus representations and channel formation subadditivity

The only external classical interface is the finite uniform representation
lemma (BBCW Lemma 14 / manuscript Lemma `uniform-kraus`). The Kraus ensemble
upper bound and the product conditional-entropy inequality are proved here.
-/
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder NNReal
namespace AmplitudeDamping
open QIT
noncomputable section
set_option maxHeartbeats 1500000
universe u v w x y z
variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- A rank-one expansion gives an explicit upper bound on the finite convex roof. -/
theorem entanglementOfFormation_le_rankOne_perspectives
    {ι : Type y} [Fintype ι] [DecidableEq ι]
    (ρ : State (a × b)) (v : ι → a × b → ℂ)
    (hsum : ∑ i, rankOneMatrix (v i) = ρ.matrix) :
    entanglementOfFormation ρ ≤ ∑ i,
      entropyPerspective (partialTraceA (rankOneMatrix (v i)))
        (partialTraceA_posSemidef (rankOneMatrix_pos (v i))) := by
  classical
  let w : ι → ℝ := fun i => (rankOneMatrix (v i)).trace.re
  have hw : ∀ i, 0 ≤ w i := fun i => (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos (v i))).1
  have hws : ∑ i, w i = 1 := by
    have ht := congrArg (fun X : CMatrix (a × b) => X.trace.re) hsum
    simpa [w, Matrix.trace_sum, ρ.trace_re_eq_one] using ht
  obtain ⟨i₀, hi₀⟩ : ∃ i, 0 < w i := by
    by_contra h
    push Not at h
    have : ∑ i, w i ≤ 0 := Finset.sum_nonpos fun i _ => h i
    linarith
  let q : ι → PureVector (a × b) := fun i =>
    if h : 0 < w i then PureVector.normalize (v i) h
    else PureVector.normalize (v i₀) hi₀
  have hweight (i : ι) : (w i : ℂ) • (q i).state.matrix = rankOneMatrix (v i) := by
    by_cases hi : 0 < w i
    · simp only [q, dif_pos hi, PureVector.normalize_state_matrix]
      rw [smul_smul]
      have hc : (w i : ℂ) * ((w i)⁻¹ : ℝ) = 1 := by
        exact_mod_cast mul_inv_cancel₀ hi.ne'
      change ((w i : ℂ) * ((w i)⁻¹ : ℝ)) • rankOneMatrix (v i) = _
      rw [hc, one_smul]
    · have hz : w i = 0 := le_antisymm (not_lt.mp hi) (hw i)
      rw [hz, Complex.ofReal_zero, zero_smul]
      symm
      apply (Matrix.PosSemidef.trace_eq_zero_iff (rankOneMatrix_pos (v i))).mp
      apply Complex.ext
      · exact hz
      · exact (Matrix.PosSemidef.trace_nonneg (rankOneMatrix_pos (v i))).2.symm
  let E : PureDecomposition (a × b) := PureDecomposition.ofFinite
    (fun i => (⟨w i, hw i⟩ : ℝ≥0))
    (by apply NNReal.eq; simpa only [NNReal.coe_sum, NNReal.coe_mk, NNReal.coe_one] using hws) q
  have hE : E.averageState = ρ := by
    apply State.ext
    change (∑ k : Fin (Fintype.card ι),
      ((⟨w ((Fintype.equivFin ι).symm k), hw _⟩ : ℝ≥0) : ℂ) •
      (q ((Fintype.equivFin ι).symm k)).state.matrix) = ρ.matrix
    calc
      _ = ∑ i, (w i : ℂ) • (q i).state.matrix :=
        Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ (fun _ => rfl)
      _ = ∑ i, rankOneMatrix (v i) := Finset.sum_congr rfl fun i _ => hweight i
      _ = _ := hsum
  have hcost (i : ι) : w i * (q i).state.marginalA.vonNeumann =
      entropyPerspective (partialTraceA (rankOneMatrix (v i)))
        (partialTraceA_posSemidef (rankOneMatrix_pos (v i))) := by
    rw [State.pureVector_marginalA_vonNeumann_eq_marginalB]
    have hm : partialTraceA (rankOneMatrix (v i)) =
        (w i : ℂ) • (q i).state.marginalB.matrix := by
      rw [← hweight i]
      ext j k
      simp [partialTraceA, State.marginalB_matrix, Finset.mul_sum]
    rw [entropyPerspective_congr hm _ ((q i).state.marginalB.pos.smul
      (by exact_mod_cast hw i)), entropyPerspective_smul (w i) (hw i) (q i).state.marginalB.matrix
        (q i).state.marginalB.pos]
    congr 1
    unfold entropyPerspective
    rw [(q i).state.marginalB.trace_re_eq_one]
    simp only [xlog2, one_ne_zero, if_false, log2, Real.log_one, zero_div, mul_zero, add_zero]
    rfl
  calc
    entanglementOfFormation ρ = entanglementOfFormation E.averageState := congrArg _ hE.symm
    _ ≤ E.entanglementCost := entanglementOfFormation_le_entanglementCost E
    _ = ∑ i, w i * (q i).state.marginalA.vonNeumann :=
      Fintype.sum_equiv (Fintype.equivFin ι).symm _ _ (fun _ => rfl)
    _ = _ := Finset.sum_congr rfl fun i _ => hcost i

/-- The instrument that records the chosen Kraus operator. -/
def krausEntropyInstrument {ι : Type y} [Fintype ι]
    (N : Channel a b) (K : ι → Matrix b a ℂ)
    (hK : MatrixMap.ofKraus K = N.map) : EntropyInstrument a b ι where
  branch i := MatrixMap.ofKraus (fun _ : Unit => K i)
  cp i := MatrixMap.ofKraus_completelyPositive _
  totalTP := by
    have hs : (∑ i, MatrixMap.ofKraus (fun _ : Unit => K i)) = N.map := by
      rw [← hK]
      ext X j k
      simp [MatrixMap.ofKraus]
    rw [hs]
    exact N.tracePreserving

/-- A chosen Kraus family expands a pure reference input into rank-one branches. -/
theorem sum_referenceKraus_rankOne
    {ι : Type y} [Fintype ι] (K : ι → Matrix b a ℂ)
    (v : c × a → ℂ) :
    (∑ i, rankOneMatrix (fun x : c × b => ∑ r, K i x.2 r * v (x.1, r))) =
      MatrixMap.kron (Channel.idChannel c).map (MatrixMap.ofKraus K)
        (rankOneMatrix v) := by
  classical
  ext x z
  rw [MatrixMap.kron_idChannel_left_apply_slice]
  simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk,
    Matrix.sum_apply, rankOneMatrix_apply]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp [Matrix.mul_apply, Matrix.conjTranspose_apply, Finset.sum_mul,
    Finset.mul_sum, mul_assoc, mul_left_comm, mul_comm]

/-- Kraus entropy cost bounds formation for every purified input. -/
theorem channelFormationAt_le_krausCost
    {ι : Type y} [Fintype ι] [DecidableEq ι]
    (N : Channel a b) (K : ι → Matrix b a ℂ)
    (hK : MatrixMap.ofKraus K = N.map) (ψ : PureVector (a × a)) :
    channelFormationAt N ψ ≤ (krausEntropyInstrument N K hK).cost ψ.state.marginalB := by
  let v : ι → a × b → ℂ := fun i x => ∑ r, K i x.2 r * ψ.amp (x.1, r)
  have hs : ∑ i, rankOneMatrix (v i) =
      (((Channel.idChannel a).prod N).applyState ψ.state).matrix := by
    rw [show (((Channel.idChannel a).prod N).applyState ψ.state).matrix =
      MatrixMap.kron (Channel.idChannel a).map N.map (rankOneMatrix ψ.amp) from rfl,
      ← hK]
    exact sum_referenceKraus_rankOne K ψ.amp
  have h := entanglementOfFormation_le_rankOne_perspectives _ v hs
  refine h.trans_eq ?_
  apply Finset.sum_congr rfl
  intro i _
  apply entropyPerspective_congr
  have hb : rankOneMatrix (v i) = MatrixMap.kron (Channel.idChannel a).map
      (MatrixMap.ofKraus (fun _ : Unit => K i)) ψ.state.matrix := by
    simpa [v] using sum_referenceKraus_rankOne (fun _ : Unit => K i) ψ.amp
  rw [hb, partialTraceA_mapKron _ _ (Channel.idChannel a).tracePreserving]
  rfl

/-- Product Kraus costs satisfy the correlated-input inequality. -/
theorem krausCost_product_le
    {ι : Type y} {κ : Type z} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]
    (N : Channel a b) (M : Channel c d)
    (K : ι → Matrix b a ℂ) (L : κ → Matrix d c ℂ)
    (hK : MatrixMap.ofKraus K = N.map) (hL : MatrixMap.ofKraus L = M.map)
    (ρ : State (a × c)) :
    (krausEntropyInstrument (N.prod M) (MatrixMap.krausProduct K L)
      (by rw [← MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct, hK, hL]; rfl)).cost ρ ≤
      (krausEntropyInstrument N K hK).cost ρ.marginalA +
      (krausEntropyInstrument M L hL).cost ρ.marginalB := by
  have he : (krausEntropyInstrument (N.prod M) (MatrixMap.krausProduct K L)
      (by rw [← MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct, hK, hL]; rfl)).cost ρ =
      ((krausEntropyInstrument N K hK).prod (krausEntropyInstrument M L hL)).cost ρ := by
    apply Finset.sum_congr rfl
    intro i _
    apply entropyPerspective_congr
    change MatrixMap.ofKraus (fun _ : Unit => Matrix.kronecker (K i.1) (L i.2)) ρ.matrix =
      MatrixMap.kron (MatrixMap.ofKraus (fun _ : Unit => K i.1))
        (MatrixMap.ofKraus (fun _ : Unit => L i.2)) ρ.matrix
    rw [MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct]
    simp [MatrixMap.ofKraus, MatrixMap.krausProduct]
  rw [he]
  exact EntropyInstrument.cost_prod_le _ _ ρ

/-- Classical finite uniform Kraus lemma, exposed as a hypothesis. It asks for
one finite Kraus representation uniformly within any positive tolerance of the
channel formation value. No product or additivity assertion is included. -/
def UniformKrausRepresentation : Prop :=
  ∀ (N : Channel a b) (δ : ℝ), 0 < δ →
    ∃ (n : ℕ) (K : Fin n → Matrix b a ℂ) (hK : MatrixMap.ofKraus K = N.map),
      ∀ ρ : State a, (krausEntropyInstrument N K hK).cost ρ ≤
        channelEntanglementOfFormation N + δ

/-- Empty input spaces contribute the empty real supremum, hence zero;
this extension avoids imposing nonempty dimension hypotheses downstream. -/
theorem channelEntanglementOfFormation_nonneg_all (N : Channel a b) :
    0 ≤ channelEntanglementOfFormation N := by
  apply Real.sSup_nonneg
  rintro x ⟨ψ, rfl⟩
  exact entanglementOfFormation_nonneg _

/-- Uniform finite Kraus representations discharge the general channel
formation subadditivity interface. All correlated pure reference inputs are
covered; the Kraus-product entropy inequality is proved above. -/
theorem channelFormationSubadditivity_of_uniformKraus
    (hN : UniformKrausRepresentation (a := a) (b := b))
    (hM : UniformKrausRepresentation (a := c) (b := d)) :
    ChannelFormationSubadditivity (a := a) (b := b) (c := c) (d := d) := by
  intro N M
  by_cases he : Nonempty (a × c)
  · letI := he
    apply csSup_le (channelFormationValues_nonempty (N.prod M))
    rintro x ⟨ψ, rfl⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, K, hK, hKu⟩ := hN N (ε / 2) (by positivity)
    obtain ⟨m, L, hL, hLu⟩ := hM M (ε / 2) (by positivity)
    have hprod : MatrixMap.ofKraus (MatrixMap.krausProduct K L) = (N.prod M).map := by
      rw [← MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct, hK, hL]
      rfl
    have h₁ := channelFormationAt_le_krausCost (N.prod M)
      (MatrixMap.krausProduct K L) hprod ψ
    have h₂ := krausCost_product_le N M K L hK hL ψ.state.marginalB
    have h₃ := hKu ψ.state.marginalB.marginalA
    have h₄ := hLu ψ.state.marginalB.marginalB
    linarith
  · have hv : channelFormationValues (N.prod M) = ∅ := by
      ext x
      constructor
      · rintro ⟨ψ, _⟩
        exact (he (Nonempty.map Prod.fst ψ.state.nonempty)).elim
      · simp
    change sSup (channelFormationValues (N.prod M)) ≤ _
    rw [hv, Real.sSup_empty]
    exact add_nonneg (channelEntanglementOfFormation_nonneg_all N)
      (channelEntanglementOfFormation_nonneg_all M)

/-- The uniform representation theorem for all ordinary finite dimensions. -/
def GeneralUniformKrausRepresentation : Prop :=
  ∀ (a b : Type) [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b],
    UniformKrausRepresentation (a := a) (b := b)

/-- Universe-zero adapter, definitionally the general subadditivity interface
used by the formation regularization theorems. -/
theorem generalChannelFormationSubadditivity_of_uniformKraus
    (h : GeneralUniformKrausRepresentation) :
    GeneralChannelFormationSubadditivity := by
  intro a b c d _ _ _ _ _ _ _ _
  exact channelFormationSubadditivity_of_uniformKraus (h a b) (h c d)

/-- The explicit binary instrument gives the AD channel formation upper bound
without any uniform-minimax or qubit-channel identity hypothesis. -/
theorem amplitudeDamping_channelFormation_le_binaryEntropy
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    channelEntanglementOfFormation (amplitudeDamping p hp0 hp1) ≤
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  apply csSup_le (channelFormationValues_nonempty _)
  rintro x ⟨ψ, rfl⟩
  have hK : MatrixMap.ofKraus (binaryInstrumentKraus p) =
      (amplitudeDamping p hp0 hp1).map := by
    apply LinearMap.ext
    intro X
    exact binaryInstrumentKraus_map p X
  have h := channelFormationAt_le_krausCost (amplitudeDamping p hp0 hp1)
    (binaryInstrumentKraus p) hK ψ
  have hc : (krausEntropyInstrument (amplitudeDamping p hp0 hp1)
      (binaryInstrumentKraus p) hK).cost ψ.state.marginalB =
      binaryInstrumentCost p ψ.state.marginalB := by
    exact binaryEntropyInstrument_cost p hp0 hp1 ψ.state.marginalB
  rw [hc] at h
  exact h.trans (binaryInstrumentCost_le p hp0 hp1 _)

/-- Exact AD channel formation follows from the binary instrument upper bound
and the Bell-input lower bound, with no classical interface hypotheses. -/
theorem amplitudeDamping_channelEntanglementOfFormation_unconditional
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    channelEntanglementOfFormation (amplitudeDamping p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  apply le_antisymm (amplitudeDamping_channelFormation_le_binaryEntropy p hp0 hp1)
  have h := choi_entanglementOfFormation_le_channel (amplitudeDamping p hp0 hp1)
  rw [channelChoiState_amplitudeDamping,
    choiState_entanglementOfFormation_eq_binaryEntropy_unconditional] at h
  exact h

/-- Explicit tensor products of the binary Kraus operators, including the
empty product on the unit system. -/
def binaryProductKraus (p : ℝ) : (n : ℕ) → TensorPower (Fin 2) n →
    CMatrix (TensorPower Qubit n)
  | 0 => fun _ => 1
  | n + 1 => MatrixMap.krausProduct (binaryInstrumentKraus p) (binaryProductKraus p n)

/-- The explicit product Kraus family represents the memoryless AD channel. -/
theorem binaryProductKraus_map (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    MatrixMap.ofKraus (binaryProductKraus p n) =
      ((amplitudeDamping p hp0 hp1).tensorPower n).map := by
  induction n with
  | zero =>
    ext X i j
    simp [binaryProductKraus, Channel.tensorPower, Channel.unit,
      MatrixMap.unit, TensorPower, MatrixMap.ofKraus]
    change (1 • (1 * X * (1 : CMatrix (TensorPower Qubit 0)).conjTranspose) : CMatrix (TensorPower Qubit 0)) i j =
      X PUnit.unit PUnit.unit
    simp only [one_smul, Matrix.conjTranspose_one, Matrix.one_mul, Matrix.mul_one]
    cases i
    cases j
    rfl
  | succ n ih =>
    change MatrixMap.ofKraus (MatrixMap.krausProduct (binaryInstrumentKraus p)
      (binaryProductKraus p n)) = _
    rw [← MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct, ih]
    have hK : MatrixMap.ofKraus (binaryInstrumentKraus p) =
        (amplitudeDamping p hp0 hp1).map := by
      apply LinearMap.ext
      intro X
      exact binaryInstrumentKraus_map p X
    rw [hK]
    rfl

/-- Each branch of the recursive instrument has its literal tensor Kraus operator. -/
theorem binaryProductInstrument_branch
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ)
    (s : TensorPower (Fin 2) n) :
    (binaryProductInstrument p hp0 hp1 n).branch s =
      MatrixMap.ofKraus (fun _ : Unit => binaryProductKraus p n s) := by
  induction n with
  | zero =>
    ext X i j
    simp [binaryProductInstrument, unitEntropyInstrument, binaryProductKraus,
      Channel.idChannel, MatrixMap.ofKraus]
    rfl
  | succ n ih =>
    change MatrixMap.kron (MatrixMap.ofKraus (fun _ : Unit => binaryInstrumentKraus p s.1))
      ((binaryProductInstrument p hp0 hp1 n).branch s.2) = _
    rw [ih, MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct]
    ext X i j
    simp [binaryProductKraus, MatrixMap.krausProduct, MatrixMap.ofKraus]
    rfl

/-- The abstract product-instrument cost is exactly the chosen product Kraus cost. -/
theorem binaryProductKraus_cost
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ)
    (ρ : State (TensorPower Qubit n)) :
    (krausEntropyInstrument ((amplitudeDamping p hp0 hp1).tensorPower n)
      (binaryProductKraus p n) (binaryProductKraus_map p hp0 hp1 n)).cost ρ =
      (binaryProductInstrument p hp0 hp1 n).cost ρ := by
  apply Finset.sum_congr rfl
  intro s _
  apply entropyPerspective_congr
  exact (congrArg (fun F => F ρ.matrix) (binaryProductInstrument_branch p hp0 hp1 n s)).symm

/-- Uniform formation upper bound for every blocklength, using the explicit
binary product Kraus family and no general uniform-representation hypothesis. -/
theorem amplitudeDamping_tensorPower_channelFormation_le
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    channelEntanglementOfFormation ((amplitudeDamping p hp0 hp1).tensorPower n) ≤
      (n : ℝ) * binaryEntropy ((1 + Real.sqrt p) / 2) := by
  letI : Nonempty (TensorPower Qubit n) := tensorPower_nonempty_of_nonempty n
  apply csSup_le (channelFormationValues_nonempty _)
  rintro x ⟨ψ, rfl⟩
  have h := channelFormationAt_le_krausCost ((amplitudeDamping p hp0 hp1).tensorPower n)
    (binaryProductKraus p n) (binaryProductKraus_map p hp0 hp1 n) ψ
  rw [binaryProductKraus_cost] at h
  exact h.trans (binaryProductInstrument_cost_le p hp0 hp1 n _)

end
end AmplitudeDamping
