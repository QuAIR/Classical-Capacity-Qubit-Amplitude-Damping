import AmplitudeDamping.UniformKraus
import AmplitudeDamping.OperationalEntanglementCost

/-!
# Direct amplitude-damping power and operational cost formulas

The explicit binary product instrument supplies every upper bound. The
matching lower bound is obtained by iterating the Bell-input product witness
and Choi-state additivity. Thus neither the general uniform Kraus theorem nor
the general qubit-channel formation identity is required here.
-/
namespace AmplitudeDamping
open QIT
open scoped Matrix
noncomputable section

/-- The Bell-input witness gives the AD product lower bound for every partner. -/
theorem amplitudeDamping_channelFormation_prod_ge
    (hclassical : TwoExpectationDecomposition (Qubit × Qubit))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] (M : Channel c d) :
    channelEntanglementOfFormation (amplitudeDamping p hp0 hp1) +
      channelEntanglementOfFormation M ≤
      channelEntanglementOfFormation ((amplitudeDamping p hp0 hp1).prod M) := by
  apply channelFormation_prod_ge_of_choi
  · rw [amplitudeDamping_channelEntanglementOfFormation_unconditional,
      channelChoiState_amplitudeDamping,
      choiState_entanglementOfFormation_eq_binaryEntropy_unconditional]
  · intro sigma
    apply entanglementOfFormation_prod_eq
      (woottersKernelUpperBound_of_twoExpectations hclassical) _
      qubitKet0 qubitKet1 qubitKet0_ne_zero qubitKet1_ne_zero
    rw [channelChoiState_amplitudeDamping]
    exact choiState_matrix_mulVec_qubitKet0_qubitKet1 p hp0 hp1

/-- Exact channel formation of every AD tensor power, from its explicit
binary-instrument upper bound and the iterated Choi witness lower bound. -/
theorem amplitudeDamping_tensorPower_channelFormation_direct
    (hclassical : TwoExpectationDecomposition (Qubit × Qubit))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    channelEntanglementOfFormation ((amplitudeDamping p hp0 hp1).tensorPower n) =
      (n : ℝ) * binaryEntropy ((1 + Real.sqrt p) / 2) := by
  apply le_antisymm (amplitudeDamping_tensorPower_channelFormation_le p hp0 hp1 n)
  induction n with
  | zero =>
    simp only [Nat.cast_zero, zero_mul]
    exact channelEntanglementOfFormation_nonneg_all _
  | succ n ih =>
    letI : Nonempty (TensorPower Qubit n) := tensorPower_nonempty_of_nonempty n
    have h := amplitudeDamping_channelFormation_prod_ge hclassical p hp0 hp1
      ((amplitudeDamping p hp0 hp1).tensorPower n)
    rw [amplitudeDamping_channelEntanglementOfFormation_unconditional] at h
    rw [Channel.tensorPower_succ, Nat.cast_succ]
    calc
      ((n : ℝ) + 1) * binaryEntropy ((1 + Real.sqrt p) / 2) =
          binaryEntropy ((1 + Real.sqrt p) / 2) +
            (n : ℝ) * binaryEntropy ((1 + Real.sqrt p) / 2) := by ring
      _ ≤ binaryEntropy ((1 + Real.sqrt p) / 2) +
          channelEntanglementOfFormation ((amplitudeDamping p hp0 hp1).tensorPower n) :=
        add_le_add (le_refl _) ih
      _ ≤ _ := h

/-- Channel and Choi-state powers have the same exact formation value. -/
theorem amplitudeDamping_formation_powers_direct
    (hclassical : TwoExpectationDecomposition (Qubit × Qubit))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ) :
    channelEntanglementOfFormation ((amplitudeDamping p hp0 hp1).tensorPower n) =
      (n : ℝ) * binaryEntropy ((1 + Real.sqrt p) / 2) ∧
    entanglementOfFormation
      ((channelChoiState (amplitudeDamping p hp0 hp1)).tensorPowerBipartite n) =
      (n : ℝ) * binaryEntropy ((1 + Real.sqrt p) / 2) := by
  refine ⟨amplitudeDamping_tensorPower_channelFormation_direct hclassical p hp0 hp1 n, ?_⟩
  rw [channelChoiState_amplitudeDamping]
  exact choiState_entanglementOfFormation_tensorPowerBipartite
    (woottersKernelUpperBound_of_twoExpectations hclassical) p hp0 hp1 n

/-- Every nonzero-block formation rate is the same explicit scalar. -/
theorem amplitudeDamping_formationRates_direct
    (hclassical : TwoExpectationDecomposition (Qubit × Qubit))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FormationRegularization.formationRates (amplitudeDamping p hp0 hp1) =
      {binaryEntropy ((1 + Real.sqrt p) / 2)} := by
  ext r
  constructor
  · rintro ⟨n, hn, rfl⟩
    rw [amplitudeDamping_tensorPower_channelFormation_direct hclassical]
    simp [(Nat.cast_pos.mpr hn : (0 : ℝ) < n).ne']
  · intro hr
    refine ⟨1, Nat.one_pos, ?_⟩
    rw [Set.mem_singleton_iff.mp hr,
      amplitudeDamping_tensorPower_channelFormation_direct hclassical]
    simp

/-- The AD regularization collapses directly, without strong channel additivity. -/
theorem amplitudeDamping_regularizedFormation_direct
    (hclassical : TwoExpectationDecomposition (Qubit × Qubit))
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    FormationRegularization.regularizedFormation (amplitudeDamping p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  unfold FormationRegularization.regularizedFormation
  rw [amplitudeDamping_formationRates_direct hclassical, csInf_singleton]

/-- Operational parallel simulation cost, requiring only the classical
parallel regularization theorem in addition to the two-expectation lemma. -/
theorem amplitudeDamping_parallelEntanglementCost_direct
    (hclassical : TwoExpectationDecomposition (Qubit × Qubit))
    (hparallel : ParallelCostRegularization)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    parallelEntanglementCost (amplitudeDamping p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  rw [hparallel.eq_regularized, amplitudeDamping_regularizedFormation_direct hclassical]

/-- Both operational costs and both one-copy formation quantities agree,
without the general qubit identity or uniform Kraus theorem. -/
theorem amplitudeDamping_operational_costs_direct
    (hclassical : TwoExpectationDecomposition (Qubit × Qubit))
    (hstate : StateCostRegularization) (hparallel : ParallelCostRegularization)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    parallelEntanglementCost (amplitudeDamping p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) ∧
    operationalStateCost (channelChoiState (amplitudeDamping p hp0 hp1)) =
      binaryEntropy ((1 + Real.sqrt p) / 2) ∧
    entanglementOfFormation (channelChoiState (amplitudeDamping p hp0 hp1)) =
      binaryEntropy ((1 + Real.sqrt p) / 2) ∧
    channelEntanglementOfFormation (amplitudeDamping p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  refine ⟨amplitudeDamping_parallelEntanglementCost_direct hclassical hparallel p hp0 hp1,
    ?_, ?_, amplitudeDamping_channelEntanglementOfFormation_unconditional p hp0 hp1⟩
  · rw [hstate.eq_regularized, channelChoiState_amplitudeDamping]
    exact choiState_entanglementCost
      (woottersKernelUpperBound_of_twoExpectations hclassical) p hp0 hp1
  · rw [channelChoiState_amplitudeDamping,
      choiState_entanglementOfFormation_eq_binaryEntropy_unconditional]

end
end AmplitudeDamping
