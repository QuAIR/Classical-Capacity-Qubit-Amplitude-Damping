import AmplitudeDamping.UniformKrausTheorem

/-!
# Channel formation subadditivity from the proved uniform Kraus theorem
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

/-- Uniform finite Kraus representations discharge the general channel
formation subadditivity interface. All correlated pure reference inputs are
covered; the Kraus-product entropy inequality is proved above. -/
theorem channelFormationSubadditivity_of_uniformKraus :
    ChannelFormationSubadditivity (a := a) (b := b) (c := c) (d := d) := by
  intro N M
  by_cases he : Nonempty (a × c)
  · letI := he
    apply csSup_le (channelFormationValues_nonempty (N.prod M))
    rintro x ⟨ψ, rfl⟩
    apply le_of_forall_pos_le_add
    intro ε hε
    obtain ⟨n, K, hK, hKu⟩ := uniformKrausRepresentation N (ε / 2) (by positivity)
    obtain ⟨m, L, hL, hLu⟩ := uniformKrausRepresentation M (ε / 2) (by positivity)
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

/-- Universe-zero adapter, definitionally the general subadditivity interface
used by the formation regularization theorems. -/
theorem generalChannelFormationSubadditivity_of_uniformKraus :
    GeneralChannelFormationSubadditivity := by
  intro a b c d _ _ _ _ _ _ _ _
  exact channelFormationSubadditivity_of_uniformKraus

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
