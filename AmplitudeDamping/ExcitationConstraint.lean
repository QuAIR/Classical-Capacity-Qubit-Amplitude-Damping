import AmplitudeDamping.NCopy
import AmplitudeDamping.ScalarCapacity

/-!
# Capacity under an excitation constraint

Manuscript §4.4, "Finite-block bounds and an excitation constraint".
Iterating the strong superadditivity of the output-entropy convex roof
gives the finite-block bound eq. `(finite-block-bound)`: the fixed-input
Holevo quantity of `n` uses of amplitude damping on an arbitrary possibly
correlated input is at most the sum over the single-site marginals of the
scalar information curve `F_p(q) = h₂((1-p)q) - g_p(q)` evaluated at the
site excitations `q_i`.

Imposing the mean-excitation constraint `∑ q_i ≤ n ν` on the average
input state (the paper imposes the expectation bound `Tr[ρ ∑ |1⟩⟨1|] ≤ nν`
on each codeword; it transfers to the average state by linearity), the
concavity of `F_p` — binary entropy is concave while `g_p` is convex — and
Jensen's inequality bound every block length by `n` times the maximum of
`F_p` on `[0, ν]`.  Diagonal product inputs attain the bound, giving the
variational content of Corollary `(cor:energy)`, eq. `(energy-capacity)`:
the excitation-constrained per-letter value is `max_{0 ≤ q ≤ ν} F_p(q)`,
attained at a diagonal state.  An ensemble-level version covers mixed
codewords: the Holevo information of an arbitrary signal ensemble is
bounded through the same average-state constraint.

The operational coding layer of the corollary (Fano converse and HSW
achievable coding for constrained codewords) is the same argument
formalized in Lean-QIT's HSW theorem for the unconstrained capacity and is
not repeated here; the information-theoretic content below is exactly the
converse bound and the attaining inputs it needs.
-/

open scoped BigOperators

namespace AmplitudeDamping

open QIT

noncomputable section

/-! ### Concavity of the scalar information curve -/

/-- The bit-valued binary entropy is concave on `[0, 1]`. -/
theorem binaryEntropy_concaveOn :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) binaryEntropy := by
  have h : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) Real.binEntropy :=
    Real.strictConcave_binEntropy.concaveOn
  have h2 : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun q => (Real.log 2)⁻¹ • Real.binEntropy q) :=
    h.smul (le_of_lt (by positivity))
  exact h2.congr fun q _ => by
    rw [smul_eq_mul, binaryEntropy_eq_binEntropy_div_log_two]
    field_simp

/-- Precomposition with the nonnegative slope `1 - p` preserves concavity
of the binary entropy. -/
theorem binaryEntropy_concaveOn_mul_const (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun q => binaryEntropy ((1 - p) * q)) := by
  have hc : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) binaryEntropy :=
    binaryEntropy_concaveOn
  refine ⟨convex_Icc (0 : ℝ) 1, ?_⟩
  intro x hx y hy a b ha hb hab
  have hcp : (0 : ℝ) ≤ 1 - p := by linarith
  have hcp1 : 1 - p ≤ 1 := by linarith
  have hpx : (1 - p) * x ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hcp hx.1, mul_le_one₀ hcp1 hx.1 hx.2⟩
  have hpy : (1 - p) * y ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨mul_nonneg hcp hy.1, mul_le_one₀ hcp1 hy.1 hy.2⟩
  have hpc : (1 - p) * (a * x + b * y) =
      a * ((1 - p) * x) + b * ((1 - p) * y) := by ring
  simp only [smul_eq_mul]
  rw [hpc]
  simpa only [smul_eq_mul] using hc.2 hpx hpy ha hb hab

/-- The scalar information curve `F_p` is concave on `[0, 1]`: the binary
entropy is concave and the pure-output curve `g_p` is convex. -/
theorem amplitudeDampingScalarInformation_concaveOn
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (amplitudeDampingScalarInformation p) := by
  have h1 : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun q => binaryEntropy ((1 - p) * q)) :=
    binaryEntropy_concaveOn_mul_const p hp0 hp1
  have h2 : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun q => -dampingEntropyCurve p q) :=
    (dampingEntropyCurve_convexOn p hp0 hp1).neg
  refine (h1.add h2).congr fun q _ => ?_
  unfold amplitudeDampingScalarInformation
  simp only [Pi.add_apply, sub_eq_add_neg]

/-! ### The constrained one-letter value -/

/-- Values of the scalar information curve on the constrained excitation
interval `[0, ν]`. -/
def excitationConstrainedValues (p ν : ℝ) : Set ℝ :=
  (fun q => amplitudeDampingScalarInformation p q) '' Set.Icc (0 : ℝ) ν

/-- The excitation-constrained capacity value of eq. `(energy-capacity)`. -/
def excitationConstrainedCapacity (p ν : ℝ) : ℝ :=
  sSup (excitationConstrainedValues p ν)

theorem excitationConstrainedValues_nonempty (p ν : ℝ) (hν0 : 0 ≤ ν) :
    (excitationConstrainedValues p ν).Nonempty := by
  refine ⟨_, 0, ?_, rfl⟩
  exact Set.mem_Icc.mpr ⟨le_refl _, hν0⟩

/-- The constrained maximum is attained on the compact interval. -/
theorem exists_excitationConstrained_maximizer (p ν : ℝ) (hν0 : 0 ≤ ν) :
    ∃ q : ℝ, q ∈ Set.Icc (0 : ℝ) ν ∧
      ∀ r ∈ Set.Icc (0 : ℝ) ν,
        amplitudeDampingScalarInformation p r ≤
          amplitudeDampingScalarInformation p q := by
  obtain ⟨q, hq, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr hν0)
    (amplitudeDampingScalarInformation_continuous p).continuousOn
  exact ⟨q, hq, fun r hr => hmax hr⟩

theorem excitationConstrainedValues_bddAbove (p ν : ℝ) (hν0 : 0 ≤ ν) :
    BddAbove (excitationConstrainedValues p ν) := by
  obtain ⟨q, -, hmax⟩ := exists_excitationConstrained_maximizer p ν hν0
  exact ⟨_, fun r hr => by
    rcases hr with ⟨r, hrmem, rfl⟩
    exact hmax r hrmem⟩

theorem excitationConstrainedCapacity_le (p ν : ℝ) (hν0 : 0 ≤ ν)
    {q : ℝ} (hq : q ∈ Set.Icc (0 : ℝ) ν) :
    amplitudeDampingScalarInformation p q ≤
      excitationConstrainedCapacity p ν :=
  le_csSup (excitationConstrainedValues_bddAbove p ν hν0) ⟨q, hq, rfl⟩

theorem exists_excitationConstrainedCapacity_eq (p ν : ℝ) (hν0 : 0 ≤ ν) :
    ∃ q : ℝ, q ∈ Set.Icc (0 : ℝ) ν ∧
      excitationConstrainedCapacity p ν =
        amplitudeDampingScalarInformation p q := by
  obtain ⟨q, hq, hmax⟩ := exists_excitationConstrained_maximizer p ν hν0
  refine ⟨q, hq, le_antisymm ?_ ?_⟩
  · apply csSup_le (excitationConstrainedValues_nonempty p ν hν0)
    intro r hr
    rcases hr with ⟨r, hrmem, rfl⟩
    exact hmax r hrmem
  · exact le_csSup (excitationConstrainedValues_bddAbove p ν hν0)
      ⟨q, hq, rfl⟩

/-! ### Site marginals of an n-qubit input -/

/-- The single-site marginal states of an `n`-qubit input, exposed
recursively from the front of the tensor product. -/
def siteStates :
    (n : ℕ) → State (QIT.TensorPower Qubit n) → (Fin n → State Qubit)
  | 0, _ => fun i => i.elim0
  | n + 1, rho => Fin.cons rho.marginalA (siteStates n rho.marginalB)

@[simp] theorem siteStates_succ (n : ℕ)
    (rho : State (QIT.TensorPower Qubit (n + 1))) :
    siteStates (n + 1) rho =
      Fin.cons rho.marginalA (siteStates n rho.marginalB) :=
  rfl

/-- The total excitation of an `n`-qubit input: the sum of the site
excitation probabilities. -/
def siteExcitationSum :
    (n : ℕ) → State (QIT.TensorPower Qubit n) → ℝ
  | 0, _ => 0
  | n + 1, rho => stateExcitation rho.marginalA + siteExcitationSum n rho.marginalB

theorem siteExcitationSum_succ (n : ℕ)
    (tau : State (QIT.TensorPower Qubit (n + 1))) :
    siteExcitationSum (n + 1) tau =
      stateExcitation tau.marginalA + siteExcitationSum n tau.marginalB :=
  rfl

/-- The recursive total equals the sum over the site marginals. -/
theorem siteExcitationSum_eq :
    ∀ (n : ℕ) (tau : State (QIT.TensorPower Qubit n)),
      siteExcitationSum n tau =
        ∑ i, stateExcitation (siteStates n tau i) := by
  intro n
  induction n with
  | zero => intro tau; simp [siteExcitationSum]
  | succ n ih =>
      intro tau
      rw [siteExcitationSum_succ, Fin.sum_univ_succ]
      simp only [siteStates_succ, Fin.cons_zero, Fin.cons_succ]
      rw [ih tau.marginalB]

/-! ### The finite-block bound -/

private theorem punit_vonNeumann_eq_zero (tau : State PUnit) :
    tau.vonNeumann = 0 := by
  apply le_antisymm
  · have h := State.vonNeumann_le_log_card tau
    convert h using 1
    norm_num [log2]
  · exact State.vonNeumann_nonneg tau

/-- Eq. `(finite-block-bound)`: iterating strong superadditivity of the
output-entropy roof, the fixed-input Holevo quantity of `n` uses of
amplitude damping on an arbitrary correlated input is at most the sum of
the single-site state informations of its site marginals. -/
theorem amplitudeDamping_tensorPower_fixedInputHolevo_le
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ (n : ℕ) (tau : State (QIT.TensorPower Qubit n)),
      fixedInputHolevo (outputEntropyRoof
          ((amplitudeDamping p hp0 hp1).tensorPower n))
        ((amplitudeDamping p hp0 hp1).tensorPower n) tau ≤
        ∑ i, amplitudeDampingStateInformation p hp0 hp1
          (siteStates n tau i) := by
  intro n
  induction n with
  | zero =>
      intro tau
      have hS : (((amplitudeDamping p hp0 hp1).tensorPower 0).applyState
          tau).vonNeumann = 0 := punit_vonNeumann_eq_zero _
      have hR : 0 ≤ outputEntropyRoof
          ((amplitudeDamping p hp0 hp1).tensorPower 0) tau :=
        outputEntropyRoof_nonneg _ tau
      have hsum : ∑ i : Fin 0, amplitudeDampingStateInformation p hp0 hp1
          (siteStates 0 tau i) = 0 := by simp
      unfold fixedInputHolevo
      rw [hS, hsum]
      linarith
  | succ n ih =>
      intro tau
      rw [Channel.tensorPower_succ]
      have hroof : outputEntropyRoof
          ((amplitudeDamping p hp0 hp1).prod
            ((amplitudeDamping p hp0 hp1).tensorPower n)) tau ≥
        outputEntropyRoof (amplitudeDamping p hp0 hp1) tau.marginalA +
          outputEntropyRoof
            ((amplitudeDamping p hp0 hp1).tensorPower n) tau.marginalB :=
        amplitudeDamping_outputEntropyRoof_stronglySuperadditive
          p hp0 hp1 ((amplitudeDamping p hp0 hp1).tensorPower n) tau
      have hstep := fixedInputHolevo_prod_le
        (outputEntropyRoof ((amplitudeDamping p hp0 hp1).prod
          ((amplitudeDamping p hp0 hp1).tensorPower n)))
        (outputEntropyRoof (amplitudeDamping p hp0 hp1))
        (outputEntropyRoof ((amplitudeDamping p hp0 hp1).tensorPower n))
        (amplitudeDamping p hp0 hp1)
        ((amplitudeDamping p hp0 hp1).tensorPower n) tau hroof
      rw [Fin.sum_univ_succ]
      simp only [siteStates_succ, Fin.cons_zero, Fin.cons_succ]
      refine hstep.trans ?_
      rw [amplitudeDamping_fixedInputHolevo_eq_stateInformation p hp0 hp1
        tau.marginalA]
      exact add_le_add le_rfl (ih tau.marginalB)

/-- Scalar form of eq. `(finite-block-bound)`: each site term is bounded by
the scalar information curve at the site excitation. -/
theorem amplitudeDamping_tensorPower_fixedInputHolevo_le_scalar
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ)
    (tau : State (QIT.TensorPower Qubit n)) :
    ∑ i, amplitudeDampingStateInformation p hp0 hp1 (siteStates n tau i) ≤
      ∑ i, amplitudeDampingScalarInformation p
        (stateExcitation (siteStates n tau i)) :=
  Finset.sum_le_sum fun _ _ =>
    amplitudeDampingStateInformation_le_scalarInformation p hp0 hp1 _

/-- Jensen step: under the mean-excitation constraint the scalar site sum
is bounded by `n` times the constrained maximum of the curve. -/
theorem amplitudeDampingScalarInformation_siteSum_le
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (ν : ℝ) (hν0 : 0 ≤ ν)
    {n : ℕ} (hn : 1 ≤ n) (tau : State (QIT.TensorPower Qubit n))
    (hsum : ∑ i, stateExcitation (siteStates n tau i) ≤ (n : ℝ) * ν) :
    ∑ i, amplitudeDampingScalarInformation p
        (stateExcitation (siteStates n tau i)) ≤
      (n : ℝ) * excitationConstrainedCapacity p ν := by
  have hn' : (0 : ℝ) < (n : ℝ) := by exact_mod_cast Nat.lt_of_succ_le hn
  have hnn : ((n : ℝ)) ≠ 0 := ne_of_gt hn'
  have hw0 : ∀ _i ∈ (Finset.univ : Finset (Fin n)), (0 : ℝ) ≤ ((n : ℝ)⁻¹) :=
    fun _ _ => by positivity
  have hw1 : ∑ i ∈ (Finset.univ : Finset (Fin n)), ((n : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
    simp
    exact mul_inv_cancel₀ hnn
  have hqmem : ∀ i ∈ (Finset.univ : Finset (Fin n)),
      stateExcitation (siteStates n tau i) ∈ Set.Icc (0 : ℝ) 1 :=
    fun _ _ => ⟨stateExcitation_nonneg _, stateExcitation_le_one _⟩
  have hj := (amplitudeDampingScalarInformation_concaveOn p hp0 hp1).le_map_sum
    hw0 hw1 hqmem
  have hmul : ∑ i, amplitudeDampingScalarInformation p
        (stateExcitation (siteStates n tau i)) =
      (n : ℝ) * ∑ i ∈ (Finset.univ : Finset (Fin n)),
        ((n : ℝ)⁻¹) • amplitudeDampingScalarInformation p
          (stateExcitation (siteStates n tau i)) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun _ _ => ?_
    rw [smul_eq_mul, ← mul_assoc, mul_inv_cancel₀ hnn, one_mul]
  have hmid : ∑ i ∈ (Finset.univ : Finset (Fin n)), ((n : ℝ)⁻¹) •
      stateExcitation (siteStates n tau i) =
      (∑ i, stateExcitation (siteStates n tau i)) / (n : ℝ) := by
    simp only [smul_eq_mul]
    rw [← Finset.mul_sum]
    field_simp
  have hmid0 : (0 : ℝ) ≤
      (∑ i, stateExcitation (siteStates n tau i)) / (n : ℝ) :=
    div_nonneg
      (Finset.sum_nonneg fun i _ => stateExcitation_nonneg _) hn'.le
  have hmidν : (∑ i, stateExcitation (siteStates n tau i)) / (n : ℝ) ≤ ν := by
    rw [div_le_iff₀ hn']
    linarith
  have hF : amplitudeDampingScalarInformation p
      ((∑ i, stateExcitation (siteStates n tau i)) / (n : ℝ)) ≤
      excitationConstrainedCapacity p ν :=
    excitationConstrainedCapacity_le p ν hν0 ⟨hmid0, hmidν⟩
  calc ∑ i, amplitudeDampingScalarInformation p
        (stateExcitation (siteStates n tau i))
      = (n : ℝ) * ∑ i ∈ (Finset.univ : Finset (Fin n)),
          ((n : ℝ)⁻¹) • amplitudeDampingScalarInformation p
            (stateExcitation (siteStates n tau i)) := hmul
    _ ≤ (n : ℝ) * amplitudeDampingScalarInformation p
          (∑ i ∈ (Finset.univ : Finset (Fin n)), ((n : ℝ)⁻¹) •
            stateExcitation (siteStates n tau i)) :=
        mul_le_mul_of_nonneg_left hj hn'.le
    _ = (n : ℝ) * amplitudeDampingScalarInformation p
          ((∑ i, stateExcitation (siteStates n tau i)) / (n : ℝ)) := by
          rw [hmid]
    _ ≤ (n : ℝ) * excitationConstrainedCapacity p ν :=
        mul_le_mul_of_nonneg_left hF hn'.le

/-! ### The constrained capacity value, Corollary `(cor:energy)` -/

/-- Converse half of eq. `(energy-capacity)`: every `n`-block input
satisfying the mean-excitation constraint has fixed-input Holevo quantity
at most `n` times the constrained one-letter value. -/
theorem amplitudeDamping_excitationConstrained_fixedInputHolevo_le
    (p ν : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hν0 : 0 ≤ ν)
    (n : ℕ) (hn : 1 ≤ n) (tau : State (QIT.TensorPower Qubit n))
    (hcon : siteExcitationSum n tau ≤ (n : ℝ) * ν) :
    fixedInputHolevo (outputEntropyRoof
        ((amplitudeDamping p hp0 hp1).tensorPower n))
      ((amplitudeDamping p hp0 hp1).tensorPower n) tau ≤
      (n : ℝ) * excitationConstrainedCapacity p ν := by
  have h1 := amplitudeDamping_tensorPower_fixedInputHolevo_le p hp0 hp1 n tau
  have h2 := amplitudeDamping_tensorPower_fixedInputHolevo_le_scalar
    p hp0 hp1 n tau
  have h3 := amplitudeDampingScalarInformation_siteSum_le p hp0 hp1 ν hν0
    hn tau (by rw [← siteExcitationSum_eq]; exact hcon)
  exact h1.trans (h2.trans h3)

/-- Local reproof of the zeroth tensor power roof bound (the `NCopy`
version is private): the roof is squeezed between zero and the output
entropy of the trivial state. -/
private theorem tensorPower_zero_roof_eq_zero (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) (tau : State (QIT.TensorPower Qubit 0)) :
    outputEntropyRoof ((amplitudeDamping p hp0 hp1).tensorPower 0) tau = 0 := by
  apply le_antisymm
  · have h := outputEntropyRoof_le_outputEntropy
        ((amplitudeDamping p hp0 hp1).tensorPower 0) tau
    exact h.trans_eq (punit_vonNeumann_eq_zero _)
  · exact outputEntropyRoof_nonneg _ tau

/-- Exact additivity of the fixed-input Holevo quantity on IID inputs. -/
theorem amplitudeDamping_tensorPower_fixedInputHolevo_iid_eq
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (rho : State Qubit) :
    ∀ n : ℕ,
      fixedInputHolevo (outputEntropyRoof
          ((amplitudeDamping p hp0 hp1).tensorPower n))
        ((amplitudeDamping p hp0 hp1).tensorPower n) (rho.tensorPower n) =
        (n : ℝ) * fixedInputHolevo
          (outputEntropyRoof (amplitudeDamping p hp0 hp1))
          (amplitudeDamping p hp0 hp1) rho := by
  intro n
  induction n with
  | zero =>
      have hS : (((amplitudeDamping p hp0 hp1).tensorPower 0).applyState
          (rho.tensorPower 0)).vonNeumann = 0 := punit_vonNeumann_eq_zero _
      have hR : outputEntropyRoof
          ((amplitudeDamping p hp0 hp1).tensorPower 0)
          (rho.tensorPower 0) = 0 :=
        tensorPower_zero_roof_eq_zero p hp0 hp1 _
      unfold fixedInputHolevo
      rw [hS, hR]
      norm_num
  | succ n ih =>
      have hroof := amplitudeDamping_outputEntropyRoof_prod_eq p hp0 hp1
        ((amplitudeDamping p hp0 hp1).tensorPower n) rho (rho.tensorPower n)
      have hstep := fixedInputHolevo_prod_eq_of_roof_prod
        (outputEntropyRoof ((amplitudeDamping p hp0 hp1).prod
          ((amplitudeDamping p hp0 hp1).tensorPower n)))
        (outputEntropyRoof (amplitudeDamping p hp0 hp1))
        (outputEntropyRoof ((amplitudeDamping p hp0 hp1).tensorPower n))
        (amplitudeDamping p hp0 hp1)
        ((amplitudeDamping p hp0 hp1).tensorPower n)
        rho (rho.tensorPower n) hroof
      -- The identity-channel tensor power `TensorPower Qubit (n + 1)` is
      -- definitionally `Prod Qubit (TensorPower Qubit n)`, but `rw` matches
      -- syntactically, so the step is composed by defeq through `calc`.
      calc fixedInputHolevo (outputEntropyRoof
              ((amplitudeDamping p hp0 hp1).tensorPower (n + 1)))
            ((amplitudeDamping p hp0 hp1).tensorPower (n + 1))
            (rho.tensorPower (n + 1))
          = fixedInputHolevo (outputEntropyRoof (amplitudeDamping p hp0 hp1))
              (amplitudeDamping p hp0 hp1) rho +
              fixedInputHolevo
                (outputEntropyRoof
                  ((amplitudeDamping p hp0 hp1).tensorPower n))
                ((amplitudeDamping p hp0 hp1).tensorPower n)
                (rho.tensorPower n) := hstep
        _ = (((n + 1 : ℕ) : ℝ) * fixedInputHolevo
                (outputEntropyRoof (amplitudeDamping p hp0 hp1))
                (amplitudeDamping p hp0 hp1) rho) := by
              rw [ih]
              push_cast
              ring

/-- The total site excitation of an IID input is `n` times the one-site
excitation. -/
theorem siteExcitationSum_tensorPower (rho : State Qubit) :
    ∀ n : ℕ, siteExcitationSum n (rho.tensorPower n) =
      (n : ℝ) * stateExcitation rho := by
  intro n
  induction n with
  | zero => simp [siteExcitationSum]
  | succ n ih =>
      have hA : (rho.tensorPower (n + 1)).marginalA = rho := by
        rw [State.tensorPower_succ]
        apply State.ext
        exact State.partialTraceB_prod rho (rho.tensorPower n)
      have hB : (rho.tensorPower (n + 1)).marginalB = rho.tensorPower n := by
        rw [State.tensorPower_succ]
        apply State.ext
        exact State.partialTraceA_prod rho (rho.tensorPower n)
      rw [siteExcitationSum_succ, hA, hB, ih]
      push_cast
      ring

/-- Achievability half of eq. `(energy-capacity)`: diagonal product inputs
at a maximizing constrained excitation satisfy the constraint and attain
`n` times the constrained one-letter value. -/
theorem exists_amplitudeDamping_excitationConstrained_attained
    (p ν : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    (n : ℕ) :
    ∃ tau : State (QIT.TensorPower Qubit n),
      siteExcitationSum n tau ≤ (n : ℝ) * ν ∧
        fixedInputHolevo (outputEntropyRoof
            ((amplitudeDamping p hp0 hp1).tensorPower n))
          ((amplitudeDamping p hp0 hp1).tensorPower n) tau =
          (n : ℝ) * excitationConstrainedCapacity p ν := by
  obtain ⟨q, hq, hcap⟩ := exists_excitationConstrainedCapacity_eq p ν hν0
  have hq1 : q ≤ 1 := hq.2.trans hν1
  refine ⟨(diagonalQubitState q hq.1 hq1).tensorPower n, ?_, ?_⟩
  · rw [siteExcitationSum_tensorPower, diagonalQubitState_excitation]
    exact mul_le_mul_of_nonneg_left hq.2 (Nat.cast_nonneg n)
  · rw [amplitudeDamping_tensorPower_fixedInputHolevo_iid_eq p hp0 hp1
        (diagonalQubitState q hq.1 hq1) n,
      amplitudeDamping_fixedInputHolevo_eq_stateInformation p hp0 hp1
        (diagonalQubitState q hq.1 hq1),
      amplitudeDampingStateInformation_diagonalQubitState p hp0 hp1 q
        hq.1 hq1, ← hcap]

/-- Variational form of eq. `(energy-capacity)`: the supremum of the
constrained `n`-block fixed-input Holevo quantities is exactly `n` times
the constrained one-letter value. -/
theorem excitationConstrained_fixedInputHolevo_sup_eq
    (p ν : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hν0 : 0 ≤ ν) (hν1 : ν ≤ 1)
    {n : ℕ} (hn : 1 ≤ n) :
    sSup {r : ℝ | ∃ tau : State (QIT.TensorPower Qubit n),
        siteExcitationSum n tau ≤ (n : ℝ) * ν ∧
          r = fixedInputHolevo (outputEntropyRoof
              ((amplitudeDamping p hp0 hp1).tensorPower n))
            ((amplitudeDamping p hp0 hp1).tensorPower n) tau} =
      (n : ℝ) * excitationConstrainedCapacity p ν := by
  obtain ⟨tau, hcon, hval⟩ :=
    exists_amplitudeDamping_excitationConstrained_attained
      p ν hp0 hp1 hν0 hν1 n
  have hmem : ((n : ℝ) * excitationConstrainedCapacity p ν) ∈
      {r : ℝ | ∃ tau : State (QIT.TensorPower Qubit n),
        siteExcitationSum n tau ≤ (n : ℝ) * ν ∧
          r = fixedInputHolevo (outputEntropyRoof
              ((amplitudeDamping p hp0 hp1).tensorPower n))
            ((amplitudeDamping p hp0 hp1).tensorPower n) tau} :=
    ⟨tau, hcon, hval.symm⟩
  have hbd : BddAbove
      {r : ℝ | ∃ tau : State (QIT.TensorPower Qubit n),
        siteExcitationSum n tau ≤ (n : ℝ) * ν ∧
          r = fixedInputHolevo (outputEntropyRoof
              ((amplitudeDamping p hp0 hp1).tensorPower n))
            ((amplitudeDamping p hp0 hp1).tensorPower n) tau} :=
    ⟨(n : ℝ) * excitationConstrainedCapacity p ν, by
      rintro r ⟨tau, hcon', rfl⟩
      exact amplitudeDamping_excitationConstrained_fixedInputHolevo_le
        p ν hp0 hp1 hν0 n hn tau hcon'⟩
  apply le_antisymm
  · refine csSup_le ⟨_, hmem⟩ ?_
    rintro r ⟨tau, hcon', rfl⟩
    exact amplitudeDamping_excitationConstrained_fixedInputHolevo_le
      p ν hp0 hp1 hν0 n hn tau hcon'
  · exact le_csSup hbd hmem

/-- Mixed-codeword version: the Holevo information of an arbitrary finite
signal ensemble is bounded through the mean-excitation constraint on its
average input state. -/
theorem amplitudeDamping_excitationConstrained_ensembleHolevoAfter_le
    {ι : Type} [Fintype ι] {n : ℕ}
    (p ν : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (hν0 : 0 ≤ ν)
    (hn : 1 ≤ n) (E : Ensemble ι (QIT.TensorPower Qubit n))
    (havg : siteExcitationSum n E.averageState ≤ (n : ℝ) * ν) :
    ensembleHolevoAfter ((amplitudeDamping p hp0 hp1).tensorPower n) E ≤
      (n : ℝ) * excitationConstrainedCapacity p ν := by
  rw [ensembleHolevoAfter_eq]
  have hroof := outputEntropyRoof_isOutputEntropyRoof
    ((amplitudeDamping p hp0 hp1).tensorPower n) E
  have hconv := amplitudeDamping_excitationConstrained_fixedInputHolevo_le
    p ν hp0 hp1 hν0 n hn E.averageState havg
  unfold fixedInputHolevo at hconv
  linarith

end

end AmplitudeDamping
