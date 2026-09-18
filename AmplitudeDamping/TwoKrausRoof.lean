import AmplitudeDamping.LocalUnitary
import AmplitudeDamping.StinespringEOF
import AmplitudeDamping.RankTwoKernel
import QIT.Coding.EntanglementAssisted.Renyi.Sandwiched.CBNorm.Complement
import Mathlib.LinearAlgebra.Matrix.Rank

/-!
# Roof superadditivity for two-Kraus qubit channels (Corollary 8)

Manuscript §5, Corollary 8, first displayed equation: if `N` is a qubit
channel admitting a Kraus representation with at most two operators, then for
every channel `M` and every input state `τ` on `X ⊗ Y`,

`roof(N ⊗ M)(τ) ≥ roof(N)(τ_X) + roof(M)(τ_Y)`,

where `roof` is the output-entropy convex roof.

The proof stacks Stinespring isometries.  The two-Kraus hypothesis embeds the
Kraus index type of `N` into the qubit, so the `N`-stack isometry `S` already
has a qubit environment and the product stack
`U = krausStinespringMatrix (krausProduct K' M.kraus)` produces a dilation
state `Ω` of `τ` whose reassociated two-qubit marginal `S τ_X Sᴴ` has rank at
most two.  `RankTwoKernel` then provides a nonzero product kernel vector, the
full-form Theorem 6 of `LocalUnitary.lean` (under the Wootters interface
hypothesis, tracked as everywhere else in this repository) gives
`E_F(ρ_AB) + E_F(σ) ≤ E_F(Ω)`, and a generalized MSW identity — the
Stinespring dilation lemma of `StinespringEOF.lean` with the isometry
abstracted to an arbitrary isometry matrix — translates all three `E_F` terms
back to output-entropy convex roofs.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
  NNReal Kronecker

namespace AmplitudeDamping

open QIT

universe u v w w₁ w₂ w₃ w₄ w₅ w₆

noncomputable section

/-! ### Isometric image states -/

/-- The image `V ρ Vᴴ` of a state under an isometry matrix `V`. -/
def isometryImageState {a : Type u} {c : Type v}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (V : Matrix c a ℂ) (hV : V.conjTranspose * V = 1) (ρ : State a) :
    State c where
  matrix := V * ρ.matrix * V.conjTranspose
  pos := ρ.pos.mul_mul_conjTranspose_same V
  trace_eq_one := by
    calc (V * ρ.matrix * V.conjTranspose).trace
        = (V.conjTranspose * V * ρ.matrix).trace := Matrix.trace_mul_cycle _ _ _
      _ = ((1 : CMatrix a) * ρ.matrix).trace := by rw [hV]
      _ = ρ.matrix.trace := by rw [Matrix.one_mul]
      _ = 1 := ρ.trace_eq_one

theorem isometryImageState_matrix {a : Type u} {c : Type v}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (V : Matrix c a ℂ) (hV : V.conjTranspose * V = 1) (ρ : State a) :
    (isometryImageState V hV ρ).matrix = V * ρ.matrix * V.conjTranspose :=
  rfl

/-- The state of an isometric image vector is the isometric image state. -/
theorem isometryVector_state {a : Type u} {c : Type v}
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (V : Matrix c a ℂ) (hV : V.conjTranspose * V = 1) (ψ : PureVector a) :
    (isometryVector V hV ψ).state = isometryImageState V hV ψ.state := by
  apply State.ext
  rw [PureVector.state_matrix, isometryImageState_matrix]
  exact isometryVector_state_matrix V hV ψ

/-! ### The generalized MSW identity (contract 1) -/

section GeneralizedMSW

variable {a : Type u} {c : Type v}

/-- The pushforward of a pure decomposition through an isometry matrix:
same weights, conjugated branch vectors. -/
def isometryDecomposition [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (V : Matrix c a ℂ) (hV : V.conjTranspose * V = 1) (E : PureDecomposition a) :
    PureDecomposition c where
  card := E.card
  probs := E.probs
  weights_sum := E.weights_sum
  vectors i := isometryVector V hV (E.vectors i)

/-- The pushforward decomposition of `E` decomposes the isometric image of the
average state of `E`. -/
theorem isometryDecomposition_averageState [Fintype a] [DecidableEq a]
    [Fintype c] [DecidableEq c]
    (V : Matrix c a ℂ) (hV : V.conjTranspose * V = 1) (E : PureDecomposition a) :
    (isometryDecomposition V hV E).averageState =
      isometryImageState V hV E.averageState := by
  apply State.ext
  have h1 : (isometryDecomposition V hV E).averageState.matrix =
      ∑ i : Fin E.card, ((E.probs i : ℝ≥0) : ℂ) •
        (V * rankOneMatrix (E.vectors i).amp * V.conjTranspose) := by
    rw [pureDecomposition_averageState_matrix_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hp : ((isometryDecomposition V hV E).probs i) = E.probs i := rfl
    have hv : ((isometryDecomposition V hV E).vectors i).amp =
        V *ᵥ (E.vectors i).amp := rfl
    rw [hp, hv, rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  rw [h1, ← mul_sum_smul_conj, ← pureDecomposition_averageState_matrix_sum]
  rfl

/-- The pushforward correspondence preserves the cost: the entanglement cost of
the conjugated decomposition equals the output cost of the original, provided
the isometry marginal realizes the channel. -/
theorem isometryDecomposition_entanglementCost {b : Type w}
    [Fintype b] [DecidableEq b] [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (Φ : Channel a b) (V : Matrix (b × c) a ℂ) (hV : V.conjTranspose * V = 1)
    (hchan : ∀ ρ : State a, (isometryImageState V hV ρ).marginalA = Φ.applyState ρ)
    (E : PureDecomposition a) :
    (isometryDecomposition V hV E).entanglementCost = E.outputCost Φ := by
  unfold PureDecomposition.entanglementCost PureDecomposition.outputCost
    outputEntropyCost
  apply Finset.sum_congr rfl
  intro i _
  have hvec : ((isometryDecomposition V hV E).vectors i).state.marginalA =
      Φ.applyState (E.vectors i).state := by
    rw [show ((isometryDecomposition V hV E).vectors i).state =
      isometryImageState V hV (E.vectors i).state from
        isometryVector_state V hV (E.vectors i)]
    exact hchan _
  rw [hvec]
  rfl

/-- First direction of the generalized MSW identity: the entanglement of
formation of the isometric image state is at most the output-entropy convex
roof. -/
theorem entanglementOfFormation_isometryImageState_le_outputEntropyRoof
    {b : Type w} [Fintype b] [DecidableEq b]
    [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (Φ : Channel a b) (V : Matrix (b × c) a ℂ) (hV : V.conjTranspose * V = 1)
    (hchan : ∀ ρ : State a, (isometryImageState V hV ρ).marginalA = Φ.applyState ρ)
    (τ : State a) :
    entanglementOfFormation (isometryImageState V hV τ) ≤
      outputEntropyRoof Φ τ := by
  apply le_csInf (pureOutputEntropyValues_nonempty Φ τ)
  intro x hx
  rcases hx with ⟨E, hE, rfl⟩
  have hle := entanglementOfFormation_le_entanglementCost
    (isometryDecomposition V hV E)
  rw [isometryDecomposition_averageState, hE] at hle
  rwa [isometryDecomposition_entanglementCost Φ V hV hchan E] at hle

/-! ### The range projection of an abstract isometry -/

/-- The complementary projection `1 - W Wᴴ` of an isometry is Hermitian. -/
theorem one_sub_rangeProjection_conjTranspose {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) :
    (1 - W * W.conjTranspose).conjTranspose = 1 - W * W.conjTranspose := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    mul_conjTranspose_mul_hermitian W]

/-- A vector fixed by the range projection is annihilated by the complement. -/
theorem one_sub_rangeProjection_mulVec_eq_zero {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (f : m → ℂ)
    (h : (W * W.conjTranspose) *ᵥ f = f) :
    (1 - W * W.conjTranspose) *ᵥ f = 0 := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, h, sub_self]

/-- The adjoint of an isometry annihilates the complementary projection. -/
theorem conjTranspose_mul_one_sub_rangeProjection {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : W.conjTranspose * W = 1) :
    W.conjTranspose * (1 - W * W.conjTranspose) = 0 := by
  have hstep := one_sub_rangeProjection_mul W hW
  have hct : (W.conjTranspose * (1 - W * W.conjTranspose)).conjTranspose =
      (0 : Matrix n m ℂ).conjTranspose := by
    rw [Matrix.conjTranspose_zero, Matrix.conjTranspose_mul,
      one_sub_rangeProjection_conjTranspose, Matrix.conjTranspose_conjTranspose]
    exact hstep
  have hct2 := congrArg Matrix.conjTranspose hct
  simpa using hct2

/-- The isometric image state annihilates vectors orthogonal to the range:
`V τ Vᴴ (1 - V Vᴴ) = 0` since `Vᴴ (1 - V Vᴴ) = 0`. -/
theorem isometryImageState_mulVec_one_sub_rangeProjection
    {a : Type u} {c : Type v} [Fintype a] [DecidableEq a] [Fintype c] [DecidableEq c]
    (V : Matrix c a ℂ) (hV : V.conjTranspose * V = 1) (ρ : State a) (w : c → ℂ) :
    (isometryImageState V hV ρ).matrix *ᵥ
      ((1 - V * V.conjTranspose) *ᵥ w) = 0 := by
  have hzero : (isometryImageState V hV ρ).matrix *
      (1 - V * V.conjTranspose) = 0 := by
    rw [isometryImageState_matrix, Matrix.mul_assoc,
      conjTranspose_mul_one_sub_rangeProjection V hV, Matrix.mul_zero]
  rw [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]

/-- Every positive-weight branch of a pure decomposition of the isometric
image state lies in the range of the isometry. -/
theorem rangeProjection_mulVec_of_pos_weight
    {a : Type u} {b : Type w} {c : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (V : Matrix (b × c) a ℂ) (hV : V.conjTranspose * V = 1) (ρ : State a)
    (D : PureDecomposition (b × c))
    (hD : D.averageState = isometryImageState V hV ρ) (i : Fin D.card)
    (hpos : 0 < (D.probs i : ℝ)) :
    (V * V.conjTranspose) *ᵥ (D.vectors i).amp = (D.vectors i).amp := by
  have hident := star_inner_averageState_mulVec D
    ((1 - V * V.conjTranspose) *ᵥ (D.vectors i).amp)
  rw [hD, isometryImageState_mulVec_one_sub_rangeProjection, dotProduct_zero] at hident
  rw [← Complex.ofReal_sum] at hident
  have hsum : (∑ j : Fin D.card,
      ((D.probs j : ℝ) *
        Complex.normSq (star (D.vectors j).amp ⬝ᵥ
          (1 - V * V.conjTranspose) *ᵥ (D.vectors i).amp))) = 0 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_zero]
    exact hident.symm
  have hnn : ∀ j : Fin D.card, j ∈ Finset.univ →
      0 ≤ (D.probs j : ℝ) *
        Complex.normSq (star (D.vectors j).amp ⬝ᵥ
          (1 - V * V.conjTranspose) *ᵥ (D.vectors i).amp) := by
    intro j _
    exact mul_nonneg (NNReal.coe_nonneg _) (Complex.normSq_nonneg _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
  rcases mul_eq_zero.mp hterm with hp | hn
  · exact absurd hp (ne_of_gt hpos)
  · have hdot : star (D.vectors i).amp ⬝ᵥ
        (1 - V * V.conjTranspose) *ᵥ (D.vectors i).amp = 0 :=
      Complex.normSq_eq_zero.mp hn
    have hnorm : star ((1 - V * V.conjTranspose) *ᵥ (D.vectors i).amp) ⬝ᵥ
        ((1 - V * V.conjTranspose) *ᵥ (D.vectors i).amp) =
        star (D.vectors i).amp ⬝ᵥ
          (1 - V * V.conjTranspose) *ᵥ (D.vectors i).amp := by
      rw [Matrix.star_mulVec, one_sub_rangeProjection_conjTranspose,
        ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        one_sub_rangeProjection_idempotent V hV]
    have hzero : star ((1 - V * V.conjTranspose) *ᵥ (D.vectors i).amp) ⬝ᵥ
        ((1 - V * V.conjTranspose) *ᵥ (D.vectors i).amp) = 0 := by
      rw [hnorm, hdot]
    have hphi : (1 - V * V.conjTranspose) *ᵥ (D.vectors i).amp = 0 :=
      dotProduct_star_self_eq_zero.mp hzero
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hphi
    exact hphi.symm

/-- The channel output of the pullback of a range branch is the output marginal
of the original branch. -/
theorem applyState_isometryPullback_of_sub_eq_zero
    {a : Type u} {b : Type w} {c : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (Φ : Channel a b) (V : Matrix (b × c) a ℂ) (hV : V.conjTranspose * V = 1)
    (hchan : ∀ ρ : State a, (isometryImageState V hV ρ).marginalA = Φ.applyState ρ)
    (filler : PureVector a) (φ : PureVector (b × c))
    (hr : (1 - V * V.conjTranspose) *ᵥ φ.amp = 0) :
    Φ.applyState (isometryPullback V hV filler φ).state = φ.state.marginalA := by
  have hemp : (isometryVector V hV (isometryPullback V hV filler φ)).amp = φ.amp := by
    rw [isometryVector_amp, isometryPullback_range V hV filler φ hr]
  rw [(hchan (isometryPullback V hV filler φ).state).symm,
    ← isometryVector_state V hV (isometryPullback V hV filler φ),
    PureVector.state_eq_of_amp_eq hemp]

open Classical in
/-- The pullback of a pure decomposition of the isometric image state: every
positive-weight branch pulls back through the isometry adjoint to an input
pure vector; zero-weight branches are replaced by an inert placeholder. -/
def isometryPullbackDecomposition
    {a : Type u} {b : Type w} {c : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (V : Matrix (b × c) a ℂ) (hV : V.conjTranspose * V = 1) (ρ : State a)
    (D : PureDecomposition (b × c))
    (_hD : D.averageState = isometryImageState V hV ρ) :
    PureDecomposition a where
  card := D.card
  probs := D.probs
  weights_sum := D.weights_sum
  vectors := fun i =>
    if _hpos : (D.probs i : ℝ) > 0 then
      isometryPullback V hV
        (basisPureVector (Classical.choice (State.nonempty ρ))) (D.vectors i)
    else
      basisPureVector (Classical.choice (State.nonempty ρ))

theorem isometryPullbackDecomposition_averageState
    {a : Type u} {b : Type w} {c : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (V : Matrix (b × c) a ℂ) (hV : V.conjTranspose * V = 1) (ρ : State a)
    (D : PureDecomposition (b × c))
    (hD : D.averageState = isometryImageState V hV ρ) :
    (isometryPullbackDecomposition V hV ρ D hD).averageState = ρ := by
  apply State.ext
  have hbranch : ∀ i : Fin D.card,
      ((((D.probs i : ℝ≥0) : ℝ) : ℂ) •
          ((isometryPullbackDecomposition V hV ρ D hD).vectors i).state.matrix) =
        V.conjTranspose *
          ((((D.probs i : ℝ≥0) : ℝ) : ℂ) •
            rankOneMatrix (D.vectors i).amp) *
          V := by
    intro i
    by_cases hpos : (D.probs i : ℝ) > 0
    · have hvec : (isometryPullbackDecomposition V hV ρ D hD).vectors i =
          isometryPullback V hV
            (basisPureVector (Classical.choice (State.nonempty ρ))) (D.vectors i) :=
        dif_pos hpos
      have hr : (1 - V * V.conjTranspose) *ᵥ (D.vectors i).amp = 0 :=
        one_sub_rangeProjection_mulVec_eq_zero V _
          (rangeProjection_mulVec_of_pos_weight V hV ρ D hD i hpos)
      have hrank : (isometryPullback V hV
          (basisPureVector (Classical.choice (State.nonempty ρ))) (D.vectors i)).state.matrix =
          V.conjTranspose * rankOneMatrix (D.vectors i).amp * V := by
        rw [PureVector.state_matrix,
          isometryPullback_amp_of_sub_eq_zero V hV _ (D.vectors i) hr,
          rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose,
          Matrix.conjTranspose_conjTranspose]
      rw [hvec, hrank, Matrix.mul_smul, Matrix.smul_mul]
    · have hp0 : ((D.probs i : ℝ≥0) : ℝ) = 0 :=
        le_antisymm (le_of_not_gt hpos) (NNReal.coe_nonneg _)
      rw [hp0]
      simp
  rw [PureDecomposition.averageState, Ensemble.averageState_matrix]
  change (∑ i : Fin D.card,
      ((((D.probs i : ℝ≥0) : ℝ) : ℂ) •
        ((isometryPullbackDecomposition V hV ρ D hD).vectors i).state.matrix)) =
    ρ.matrix
  rw [Finset.sum_congr rfl (fun i _ => hbranch i)]
  have hsum : (∑ i : Fin D.card,
      ((((D.probs i : ℝ≥0) : ℝ) : ℂ) • rankOneMatrix (D.vectors i).amp)) =
      D.averageState.matrix := by
    rw [PureDecomposition.averageState, Ensemble.averageState_matrix]
    rfl
  calc (∑ i : Fin D.card,
        V.conjTranspose *
          ((((D.probs i : ℝ≥0) : ℝ) : ℂ) • rankOneMatrix (D.vectors i).amp) *
          V) =
      (∑ i : Fin D.card,
        V.conjTranspose *
          ((((D.probs i : ℝ≥0) : ℝ) : ℂ) • rankOneMatrix (D.vectors i).amp)) *
        V :=
    (Matrix.sum_mul Finset.univ _ _).symm
    _ = V.conjTranspose *
        (∑ i : Fin D.card,
          ((((D.probs i : ℝ≥0) : ℝ) : ℂ) • rankOneMatrix (D.vectors i).amp)) *
        V := by
          rw [Matrix.mul_sum]
    _ = ρ.matrix := by
          rw [hsum, hD, isometryImageState_matrix]
          calc V.conjTranspose *
                (V * ρ.matrix * V.conjTranspose) * V =
              (V.conjTranspose * V) * ρ.matrix *
                (V.conjTranspose * V) := by
                simp only [← Matrix.mul_assoc]
            _ = ((1 : CMatrix a) * ρ.matrix) * 1 := by rw [hV]
            _ = ρ.matrix := by rw [one_mul, mul_one]

theorem isometryPullbackDecomposition_outputCost
    {a : Type u} {b : Type w} {c : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (Φ : Channel a b) (V : Matrix (b × c) a ℂ) (hV : V.conjTranspose * V = 1)
    (hchan : ∀ ρ : State a, (isometryImageState V hV ρ).marginalA = Φ.applyState ρ)
    (ρ : State a) (D : PureDecomposition (b × c))
    (hD : D.averageState = isometryImageState V hV ρ) :
    (isometryPullbackDecomposition V hV ρ D hD).outputCost Φ = D.entanglementCost := by
  unfold PureDecomposition.outputCost PureDecomposition.entanglementCost
    outputEntropyCost
  apply Finset.sum_congr rfl
  intro i _
  show ((D.probs i).toReal *
      (Φ.applyState
        ((isometryPullbackDecomposition V hV ρ D hD).vectors i).state).vonNeumann) =
    ((D.probs i).toReal *
      ((D.vectors i).state.marginalA).vonNeumann)
  by_cases hpos : (D.probs i : ℝ) > 0
  · have hr : (1 - V * V.conjTranspose) *ᵥ (D.vectors i).amp = 0 :=
      one_sub_rangeProjection_mulVec_eq_zero V _
        (rangeProjection_mulVec_of_pos_weight V hV ρ D hD i hpos)
    have hvec : (isometryPullbackDecomposition V hV ρ D hD).vectors i =
        isometryPullback V hV
          (basisPureVector (Classical.choice (State.nonempty ρ))) (D.vectors i) :=
      dif_pos hpos
    rw [hvec, applyState_isometryPullback_of_sub_eq_zero Φ V hV hchan _ _ hr]
  · have hp0 : (D.probs i : ℝ≥0) = 0 :=
      le_antisymm (le_of_not_gt hpos) (NNReal.coe_nonneg _)
    rw [hp0]
    simp

/-- Second direction of the generalized MSW identity: the output-entropy
convex roof is at most the entanglement of formation of the isometric image
state. -/
theorem outputEntropyRoof_le_entanglementOfFormation_of_isometry
    {a : Type u} {b : Type w} {c : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (Φ : Channel a b) (V : Matrix (b × c) a ℂ) (hV : V.conjTranspose * V = 1)
    (hchan : ∀ ρ : State a, (isometryImageState V hV ρ).marginalA = Φ.applyState ρ)
    (τ : State a) :
    outputEntropyRoof Φ τ ≤
      entanglementOfFormation (isometryImageState V hV τ) := by
  apply le_csInf (pureEntanglementValues_nonempty (isometryImageState V hV τ))
  intro x hx
  rcases hx with ⟨D, hD, rfl⟩
  have hle := outputEntropyRoof_le_outputCost Φ
    (isometryPullbackDecomposition V hV τ D hD)
  rw [isometryPullbackDecomposition_averageState V hV τ D hD] at hle
  rwa [isometryPullbackDecomposition_outputCost Φ V hV hchan τ D hD] at hle

/-- **The generalized MSW identity** (contract 1): for any isometry matrix `V`
whose output marginal realizes the channel `Φ`, the output-entropy convex roof
of `Φ` at `τ` equals the entanglement of formation of the isometric image
state `V τ Vᴴ` across the output–environment split. -/
theorem outputEntropyRoof_eq_entanglementOfFormation_of_isometry
    {a : Type u} {b : Type w} {c : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype c] [DecidableEq c]
    (Φ : Channel a b) (V : Matrix (b × c) a ℂ) (hV : V.conjTranspose * V = 1)
    (hchan : ∀ ρ : State a, (isometryImageState V hV ρ).marginalA = Φ.applyState ρ)
    (τ : State a) :
    outputEntropyRoof Φ τ =
      entanglementOfFormation (isometryImageState V hV τ) :=
  (outputEntropyRoof_le_entanglementOfFormation_of_isometry Φ V hV hchan τ).antisymm
    (entanglementOfFormation_isometryImageState_le_outputEntropyRoof Φ V hV hchan τ)

end GeneralizedMSW

/-! ### The Kraus Stinespring stack (contract 2) -/

/-- The output marginal of a Kraus-stack image state is the Kraus-form output:
`Tr_E[S ρ Sᴴ] = ∑ k, K k ρ (K k)ᴴ` for the stack isometry `S` of a complete
Kraus family. -/
theorem krausStinespringMatrix_marginalA_matrix
    {a : Type u} {b : Type v} {κ : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hK : MatrixMap.krausAdjoint K (1 : CMatrix b) = 1) (ρ : State a) :
    (isometryImageState (MatrixMap.krausStinespringMatrix K)
      (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one K hK) ρ).marginalA.matrix =
      (MatrixMap.ofKraus K) ρ.matrix := by
  rw [State.marginalA_matrix, isometryImageState_matrix]
  ext y y'
  simp only [partialTraceB, Matrix.mul_apply, Matrix.conjTranspose_apply,
    MatrixMap.krausStinespringMatrix, MatrixMap.ofKraus, LinearMap.coe_mk,
    AddHom.coe_mk, Matrix.sum_apply, Finset.sum_mul]

/-! ### Embedding a two-Kraus family into the qubit (contract 3) -/

section KrausEmbedding

variable {κ : Type w} [Fintype κ] [DecidableEq κ]

/-- An embedding of a Kraus index type of cardinality at most two into the
qubit. -/
def krausIndexEmbedding (hcard : Fintype.card κ ≤ 2) : κ → Qubit :=
  fun k => Fin.castLE hcard (Fintype.equivFin κ k)

omit [DecidableEq κ] in
/-- The embedding is injective. -/
theorem krausIndexEmbedding_injective (hcard : Fintype.card κ ≤ 2) :
    Function.Injective (krausIndexEmbedding hcard) := by
  intro k₁ k₂ h
  have hval : ((Fintype.equivFin κ) k₁ : ℕ) = ((Fintype.equivFin κ) k₂) := by
    have hfin := congrArg Fin.val h
    simpa [krausIndexEmbedding, Fin.val_castLE] using hfin
  exact (Fintype.equivFin κ).injective (Fin.val_injective hval)

/-- The embedding indicator `(ι k = q)`. -/
def krausIndicator (hcard : Fintype.card κ ≤ 2) (q : Qubit) (k : κ) : ℂ :=
  if krausIndexEmbedding hcard k = q then 1 else 0

omit [DecidableEq κ] in
theorem krausIndicator_star (hcard : Fintype.card κ ≤ 2) (q : Qubit) (k : κ) :
    star (krausIndicator hcard q k) = krausIndicator hcard q k := by
  unfold krausIndicator
  by_cases h : krausIndexEmbedding hcard k = q <;> simp [h]

/-- The embedding indicators collapse: summing over the qubit picks out the
diagonal `k = k'`. -/
theorem sum_krausIndicator (hcard : Fintype.card κ ≤ 2) (k k' : κ) :
    ∑ q : Qubit, krausIndicator hcard q k * krausIndicator hcard q k' =
      if k = k' then 1 else 0 := by
  unfold krausIndicator
  by_cases hkk : k = k'
  · subst hkk
    rw [Finset.sum_eq_single (krausIndexEmbedding hcard k)]
    · simp
    · intro q _ hne
      rw [if_neg (Ne.symm hne), zero_mul]
    · intro hnot
      exact absurd (Finset.mem_univ _) hnot
  · have hne : krausIndexEmbedding hcard k ≠ krausIndexEmbedding hcard k' :=
      fun hc => hkk (krausIndexEmbedding_injective hcard hc)
    rw [if_neg hkk]
    refine Finset.sum_eq_zero ?_
    intro q _
    by_cases hq : krausIndexEmbedding hcard k = q
    · rw [if_pos hq, one_mul, if_neg (fun hc => hne (hq.trans hc.symm))]
    · rw [if_neg hq, zero_mul]

/-- Extension of a Kraus family to a qubit-indexed family via the embedding:
each extended operator sums the original operators with matching index. -/
def krausExtend {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (K : κ → Matrix b a ℂ) (hcard : Fintype.card κ ≤ 2) :
    Qubit → Matrix b a ℂ :=
  fun q => (∑ k, krausIndicator hcard q k • K k : Matrix b a ℂ)

/-- Entrywise identity: the extended family has the same Kraus output. -/
theorem MatrixMap.ofKraus_krausExtend {a : Type u} {b : Type v}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    (K : κ → Matrix b a ℂ) (hcard : Fintype.card κ ≤ 2) :
    MatrixMap.ofKraus (krausExtend K hcard) = MatrixMap.ofKraus K := by
  ext X
  have hmat : (MatrixMap.ofKraus (krausExtend K hcard)) X =
      (MatrixMap.ofKraus K) X := by
    have hconj : ∀ q : Qubit, (krausExtend K hcard q).conjTranspose =
        ∑ k' : κ, krausIndicator hcard q k' • (K k').conjTranspose := by
      intro q
      rw [krausExtend, Matrix.conjTranspose_sum]
      exact Finset.sum_congr rfl fun k' _ => by
        rw [Matrix.conjTranspose_smul, krausIndicator_star]
    have hterm : ∀ q : Qubit,
        krausExtend K hcard q * X * (krausExtend K hcard q).conjTranspose =
          ∑ k : κ, ∑ k' : κ,
            (krausIndicator hcard q k * krausIndicator hcard q k') •
              (K k * X * (K k').conjTranspose) := by
      intro q
      calc krausExtend K hcard q * X * (krausExtend K hcard q).conjTranspose
          = (∑ k : κ, krausIndicator hcard q k • K k) * X *
              (∑ k' : κ, krausIndicator hcard q k' • (K k').conjTranspose) := by
            rw [hconj q, krausExtend]
        _ = ∑ k' : κ, ∑ k : κ,
              (krausIndicator hcard q k * krausIndicator hcard q k') •
                (K k * X * (K k').conjTranspose) := by
            simp only [Matrix.sum_mul, Matrix.mul_sum]
            exact Finset.sum_congr rfl fun k' _ => Finset.sum_congr rfl fun k _ => by
              simp [Matrix.smul_mul, Matrix.mul_smul, smul_smul, mul_comm]
        _ = ∑ k : κ, ∑ k' : κ,
              (krausIndicator hcard q k * krausIndicator hcard q k') •
                (K k * X * (K k').conjTranspose) := Finset.sum_comm
    calc (MatrixMap.ofKraus (krausExtend K hcard)) X
        = ∑ q : Qubit,
            krausExtend K hcard q * X * (krausExtend K hcard q).conjTranspose := rfl
      _ = ∑ q : Qubit, ∑ k : κ, ∑ k' : κ,
            (krausIndicator hcard q k * krausIndicator hcard q k') •
              (K k * X * (K k').conjTranspose) :=
          Finset.sum_congr rfl fun q _ => hterm q
      _ = ∑ k : κ, ∑ k' : κ, ∑ q : Qubit,
            (krausIndicator hcard q k * krausIndicator hcard q k') •
              (K k * X * (K k').conjTranspose) := by
          rw [Finset.sum_comm]
          refine Finset.sum_congr rfl fun k _ => Finset.sum_comm
      _ = ∑ k : κ, ∑ k' : κ,
            (∑ q : Qubit, krausIndicator hcard q k * krausIndicator hcard q k') •
              (K k * X * (K k').conjTranspose) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
          rw [Finset.sum_smul]
      _ = ∑ k : κ, ∑ k' : κ,
            (if k = k' then (1 : ℂ) else 0) • (K k * X * (K k').conjTranspose) := by
          refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun k' _ => ?_
          rw [sum_krausIndicator hcard k k']
      _ = ∑ k : κ, K k * X * (K k).conjTranspose := by
          refine Finset.sum_congr rfl fun k _ => ?_
          rw [Finset.sum_eq_single k]
          · rw [if_pos rfl, one_smul]
          · intro k' _ hne
            rw [if_neg (fun hc => hne hc.symm), zero_smul]
          · intro hnot
            exact False.elim (hnot (Finset.mem_univ k))
      _ = (MatrixMap.ofKraus K) X := rfl
  exact congrFun (congrFun hmat _) _

end KrausEmbedding

/-! ### Product Kraus stacks -/

section KrausProduct

variable {a₁ : Type w₁} {b₁ : Type w₂} {κ₁ : Type w₃}
variable {a₂ : Type w₄} {b₂ : Type w₅} {κ₂ : Type w₆}
variable [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
variable [Fintype κ₁] [DecidableEq κ₁] [Fintype a₂] [DecidableEq a₂]
variable [Fintype b₂] [DecidableEq b₂] [Fintype κ₂] [DecidableEq κ₂]

omit [Fintype a₁] [DecidableEq κ₁] [Fintype a₂] [DecidableEq κ₂] in
/-- The product of two complete Kraus families is complete: the adjoint
identity `∑ (K₁ ⊗ K₂)† (K₁ ⊗ K₂) = 1` follows from the two factor identities
by separating the Kronecker entry sums. -/
theorem krausAdjoint_krausProduct_one
    (K₁ : κ₁ → Matrix b₁ a₁ ℂ) (K₂ : κ₂ → Matrix b₂ a₂ ℂ)
    (h₁ : MatrixMap.krausAdjoint K₁ (1 : CMatrix b₁) = 1)
    (h₂ : MatrixMap.krausAdjoint K₂ (1 : CMatrix b₂) = 1) :
    MatrixMap.krausAdjoint (MatrixMap.krausProduct K₁ K₂)
        (1 : CMatrix (b₁ × b₂)) = 1 := by
  have hsum1 : (∑ p : κ₁, Matrix.conjTranspose (K₁ p) * K₁ p) =
      (1 : CMatrix a₁) := by
    have h₁' : (∑ p : κ₁,
        Matrix.conjTranspose (K₁ p) * (1 : CMatrix b₁) * K₁ p) = 1 := h₁
    rw [← h₁']
    exact Finset.sum_congr rfl fun p _ => by rw [Matrix.mul_one]
  have hsum2 : (∑ q : κ₂, Matrix.conjTranspose (K₂ q) * K₂ q) =
      (1 : CMatrix a₂) := by
    have h₂' : (∑ q : κ₂,
        Matrix.conjTranspose (K₂ q) * (1 : CMatrix b₂) * K₂ q) = 1 := h₂
    rw [← h₂']
    exact Finset.sum_congr rfl fun q _ => by rw [Matrix.mul_one]
  have hkron : ∀ p : κ₁ × κ₂, MatrixMap.krausProduct K₁ K₂ p =
      Matrix.kronecker (K₁ p.1) (K₂ p.2) := fun p => rfl
  have hterm : ∀ p : κ₁ × κ₂,
      Matrix.conjTranspose (MatrixMap.krausProduct K₁ K₂ p) *
          (1 : CMatrix (b₁ × b₂)) * MatrixMap.krausProduct K₁ K₂ p =
        (Matrix.conjTranspose (K₁ p.1) * K₁ p.1) ⊗ₖ
          (Matrix.conjTranspose (K₂ p.2) * K₂ p.2) := by
    intro p
    have hkr : Matrix.kronecker (K₁ p.1) (K₂ p.2) =
        (K₁ p.1) ⊗ₖ (K₂ p.2) := rfl
    rw [hkron p, hkr, Matrix.conjTranspose_kronecker, Matrix.mul_one,
      ← Matrix.mul_kronecker_mul]
  ext i j
  have hentry :
      MatrixMap.krausAdjoint (MatrixMap.krausProduct K₁ K₂)
          (1 : CMatrix (b₁ × b₂)) i j =
        ∑ p : κ₁ × κ₂,
          (Matrix.conjTranspose (MatrixMap.krausProduct K₁ K₂ p) *
            (1 : CMatrix (b₁ × b₂)) * MatrixMap.krausProduct K₁ K₂ p) i j := by
    show (∑ p : κ₁ × κ₂,
        Matrix.conjTranspose (MatrixMap.krausProduct K₁ K₂ p) *
          (1 : CMatrix (b₁ × b₂)) * MatrixMap.krausProduct K₁ K₂ p) i j = _
    rw [Matrix.sum_apply]
  have hsplit : ∑ p₁ : κ₁, ∑ p₂ : κ₂,
      (Matrix.conjTranspose (K₁ p₁) * K₁ p₁) i.1 j.1 *
        (Matrix.conjTranspose (K₂ p₂) * K₂ p₂) i.2 j.2 =
      (∑ p₁ : κ₁, (Matrix.conjTranspose (K₁ p₁) * K₁ p₁) i.1 j.1) *
        (∑ p₂ : κ₂, (Matrix.conjTranspose (K₂ p₂) * K₂ p₂) i.2 j.2) := by
    simp only [← Finset.sum_mul, ← Finset.mul_sum]
  have hf1 : ∑ p : κ₁, (Matrix.conjTranspose (K₁ p) * K₁ p) i.1 j.1 =
      (1 : CMatrix a₁) i.1 j.1 := by
    have h := congrFun (congrFun hsum1 i.1) j.1
    rw [Matrix.sum_apply] at h
    exact h
  have hf2 : ∑ q : κ₂, (Matrix.conjTranspose (K₂ q) * K₂ q) i.2 j.2 =
      (1 : CMatrix a₂) i.2 j.2 := by
    have h := congrFun (congrFun hsum2 i.2) j.2
    rw [Matrix.sum_apply] at h
    exact h
  have hone : ((1 : CMatrix a₁) i.1 j.1) * ((1 : CMatrix a₂) i.2 j.2) =
      (1 : CMatrix (a₁ × a₂)) i j := by
    obtain ⟨i₁, i₂⟩ := i
    obtain ⟨j₁, j₂⟩ := j
    simp only [Matrix.one_apply]
    by_cases h₁ : i₁ = j₁ <;> by_cases h₂ : i₂ = j₂ <;>
      simp [h₁, h₂, Prod.ext_iff]
  rw [hentry]
  simp only [hterm, Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  rw [hsplit, hf1, hf2, hone]

omit [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁] [Fintype κ₁]
  [DecidableEq κ₁] [Fintype a₂] [DecidableEq a₂] [Fintype b₂] [DecidableEq b₂]
  [Fintype κ₂] [DecidableEq κ₂] in
/-- The stack isometry of a product Kraus family is the submatrix-reindexed
Kronecker product of the two stack isometries. -/
theorem krausStinespringMatrix_krausProduct
    (K₁ : κ₁ → Matrix b₁ a₁ ℂ) (K₂ : κ₂ → Matrix b₂ a₂ ℂ) :
    MatrixMap.krausStinespringMatrix (MatrixMap.krausProduct K₁ K₂) =
      (MatrixMap.krausStinespringMatrix K₁ ⊗ₖ
        MatrixMap.krausStinespringMatrix K₂).submatrix
        prodReassoc (Equiv.refl (a₁ × a₂)) := by
  ext row col
  obtain ⟨⟨o₁, o₂⟩, k₁, k₂⟩ := row
  obtain ⟨x₁, x₂⟩ := col
  rfl

end KrausProduct

/-! ### Partial trace versus conjugation: the second factor -/

/-- Conjugating both factors by isometries: `Tr_A[(A ⊗ B) X (A ⊗ B)ᴴ] =
B Tr_A[X] Bᴴ` for isometries `A`, `B`.  The mirror of
`partialTraceB_conj_kronecker`, with the traced factor second. -/
theorem partialTraceA_conj_kronecker
    {a : Type w₁} {a2 : Type w₂} {b : Type w₃} {b2 : Type w₄}
    [Fintype a] [DecidableEq a] [Fintype a2] [DecidableEq a2]
    [Fintype b] [DecidableEq b] [Fintype b2] [DecidableEq b2]
    (A : Matrix a2 a ℂ) (hA : A.conjTranspose * A = 1)
    (B : Matrix b2 b ℂ) (_hB : B.conjTranspose * B = 1)
    (X : Matrix (a × b) (a × b) ℂ) :
    partialTraceA ((A ⊗ₖ B) * X * (A ⊗ₖ B).conjTranspose) =
      B * partialTraceA X * B.conjTranspose := by
  ext z z'
  have hL : partialTraceA ((A ⊗ₖ B) * X * (A ⊗ₖ B).conjTranspose) z z' =
      ∑ i : a2, ∑ q1 : a, ∑ q2 : b,
        (∑ p1 : a, ∑ p2 : b, A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
          star (A i q1 * B z' q2) := by
    simp only [partialTraceA, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  have hR : (B * partialTraceA X * B.conjTranspose) z z' =
      ∑ q2 : b, ∑ p2 : b, ∑ p1 : a,
        B z p2 * X (p1, p2) (p1, q2) * star (B z' q2) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, partialTraceA,
      Finset.mul_sum, Finset.sum_mul]
  rw [hL, hR]
  -- The `i`-sum and the `q1`-sum collapse by orthonormality of `A`.
  have key : ∀ q2 : b,
      (∑ i : a2, ∑ q1 : a,
        (∑ p1 : a, ∑ p2 : b, A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
          star (A i q1 * B z' q2)) =
      (∑ p2 : b, ∑ p1 : a, B z p2 * X (p1, p2) (p1, q2) * star (B z' q2)) := by
    intro q2
    -- Distribute the inner sums over the product.
    calc (∑ i : a2, ∑ q1 : a,
          (∑ p1 : a, ∑ p2 : b, A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
            star (A i q1 * B z' q2))
        = ∑ i : a2, ∑ q1 : a, ∑ p1 : a, ∑ p2 : b,
            (A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
              star (A i q1 * B z' q2) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun q1 _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun p1 _ => by rw [Finset.sum_mul]
      _ = ∑ i : a2, ∑ p1 : a, ∑ q1 : a, ∑ p2 : b,
            (A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
              star (A i q1 * B z' q2) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ i : a2, ∑ p1 : a, ∑ p2 : b, ∑ q1 : a,
            (A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
              star (A i q1 * B z' q2) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun p1 _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ p1 : a, ∑ i : a2, ∑ p2 : b, ∑ q1 : a,
            (A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
              star (A i q1 * B z' q2) := by
          rw [Finset.sum_comm]
      _ = ∑ p1 : a, ∑ p2 : b, ∑ i : a2, ∑ q1 : a,
            (A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
              star (A i q1 * B z' q2) := by
          refine Finset.sum_congr rfl fun p1 _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ p1 : a, ∑ p2 : b, B z p2 * X (p1, p2) (p1, q2) * star (B z' q2) := by
          refine Finset.sum_congr rfl fun p1 _ => Finset.sum_congr rfl fun p2 _ => ?_
          have hleaf : ∀ i : a2, ∀ q1 : a,
              (A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
                  star (A i q1 * B z' q2) =
                (B z p2 * X (p1, p2) (q1, q2) * star (B z' q2)) *
                  (A i p1 * star (A i q1)) := by
            intro i q1
            rw [star_mul]
            ring
          calc (∑ i : a2, ∑ q1 : a,
                (A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
                  star (A i q1 * B z' q2))
              = ∑ i : a2, ∑ q1 : a,
                  (B z p2 * X (p1, p2) (q1, q2) * star (B z' q2)) *
                    (A i p1 * star (A i q1)) :=
                  Finset.sum_congr rfl fun i _ =>
                    Finset.sum_congr rfl fun q1 _ => hleaf i q1
            _ = ∑ q1 : a, ∑ i : a2,
                  (B z p2 * X (p1, p2) (q1, q2) * star (B z' q2)) *
                    (A i p1 * star (A i q1)) :=
                  Finset.sum_comm
            _ = ∑ q1 : a,
                  (B z p2 * X (p1, p2) (q1, q2) * star (B z' q2)) *
                    (∑ i : a2, A i p1 * star (A i q1)) := by
                  refine Finset.sum_congr rfl fun q1 _ => ?_
                  rw [← Finset.mul_sum]
            _ = ∑ q1 : a,
                  (if q1 = p1 then B z p2 * X (p1, p2) (q1, q2) * star (B z' q2)
                    else 0) := by
                  refine Finset.sum_congr rfl fun q1 _ => ?_
                  rw [columnDelta A hA p1 q1, mul_ite, mul_one, mul_zero]
            _ = B z p2 * X (p1, p2) (p1, q2) * star (B z' q2) := by
                  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ p1)]
      _ = ∑ p2 : b, ∑ p1 : a, B z p2 * X (p1, p2) (p1, q2) * star (B z' q2) :=
          Finset.sum_comm
  have hstep1 : (∑ i : a2, ∑ q1 : a, ∑ q2 : b,
        (∑ p1 : a, ∑ p2 : b, A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
          star (A i q1 * B z' q2)) =
      ∑ i : a2, ∑ q2 : b, ∑ q1 : a,
        (∑ p1 : a, ∑ p2 : b, A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
          star (A i q1 * B z' q2) := by
    refine Finset.sum_congr rfl fun i _ => Finset.sum_comm
  have hstep2 : (∑ i : a2, ∑ q2 : b, ∑ q1 : a,
        (∑ p1 : a, ∑ p2 : b, A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
          star (A i q1 * B z' q2)) =
      ∑ q2 : b, ∑ i : a2, ∑ q1 : a,
        (∑ p1 : a, ∑ p2 : b, A i p1 * B z p2 * X (p1, p2) (q1, q2)) *
          star (A i q1 * B z' q2) :=
    Finset.sum_comm
  rw [hstep1, hstep2]
  exact Finset.sum_congr rfl fun q2 _ => key q2

/-! ### Marginals of stacked isometric image states -/

/-- The first marginal of a Kronecker-isometric image state is the isometric
image of the first marginal. -/
theorem marginalA_isometryImageState_kronecker
    {a : Type w₁} {a2 : Type w₂} {b : Type w₃} {b2 : Type w₄}
    [Fintype a] [DecidableEq a] [Fintype a2] [DecidableEq a2]
    [Fintype b] [DecidableEq b] [Fintype b2] [DecidableEq b2]
    (A : Matrix a2 a ℂ) (hA : A.conjTranspose * A = 1)
    (B : Matrix b2 b ℂ) (hB : B.conjTranspose * B = 1)
    (ρ : State (a × b)) :
    (isometryImageState (A ⊗ₖ B) (kronecker_isometry A hA B hB) ρ).marginalA =
      isometryImageState A hA ρ.marginalA := by
  apply State.ext
  rw [State.marginalA_matrix, isometryImageState_matrix, isometryImageState_matrix]
  exact partialTraceB_conj_kronecker A hA B hB ρ.matrix

/-- The second marginal of a Kronecker-isometric image state is the isometric
image of the second marginal. -/
theorem marginalB_isometryImageState_kronecker
    {a : Type w₁} {a2 : Type w₂} {b : Type w₃} {b2 : Type w₄}
    [Fintype a] [DecidableEq a] [Fintype a2] [DecidableEq a2]
    [Fintype b] [DecidableEq b] [Fintype b2] [DecidableEq b2]
    (A : Matrix a2 a ℂ) (hA : A.conjTranspose * A = 1)
    (B : Matrix b2 b ℂ) (hB : B.conjTranspose * B = 1)
    (ρ : State (a × b)) :
    (isometryImageState (A ⊗ₖ B) (kronecker_isometry A hA B hB) ρ).marginalB =
      isometryImageState B hB ρ.marginalB := by
  apply State.ext
  rw [State.marginalB_matrix, isometryImageState_matrix, isometryImageState_matrix]
  exact partialTraceA_conj_kronecker A hA B hB ρ.matrix

/-! ### The product stack and reassociation -/

/-- Un-subindexing: conjugating by the `prodReassoc`-submatrix of a matrix and
then reassociating both sides is plain conjugation by the matrix. -/
theorem submatrix_prodReassoc_mul
    {b₁ : Type w₁} {κ₁ : Type w₂} {b₂ : Type w₃} {κ₂ : Type w₄} {n : Type w₅}
    [Fintype b₁] [DecidableEq b₁] [Fintype κ₁] [DecidableEq κ₁]
    [Fintype b₂] [DecidableEq b₂] [Fintype κ₂] [DecidableEq κ₂]
    [Fintype n] [DecidableEq n]
    (W : Matrix ((b₁ × κ₁) × (b₂ × κ₂)) n ℂ) (M : Matrix n n ℂ) :
    (W.submatrix prodReassoc (Equiv.refl n) * M *
        (W.submatrix prodReassoc (Equiv.refl n)).conjTranspose).submatrix
      prodReassoc.symm prodReassoc.symm =
      W * M * W.conjTranspose := by
  ext i j
  simp only [Matrix.submatrix_apply, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Equiv.apply_symm_apply, Equiv.refl_apply, Finset.sum_mul]

/-- The dilation state of the product stack, reassociated to the
`AA' ⊗ BB'` ordering, is the dilation state of the Kronecker product of the two
stack isometries. -/
theorem isometryImageState_krausProduct_reindex
    {a₁ : Type w₁} {b₁ : Type w₂} {κ₁ : Type w₃}
    {a₂ : Type w₄} {b₂ : Type w₅} {κ₂ : Type w₆}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype κ₁] [DecidableEq κ₁] [Fintype a₂] [DecidableEq a₂]
    [Fintype b₂] [DecidableEq b₂] [Fintype κ₂] [DecidableEq κ₂]
    (K₁ : κ₁ → Matrix b₁ a₁ ℂ)
    (hK₁ : MatrixMap.krausAdjoint K₁ (1 : CMatrix b₁) = 1)
    (K₂ : κ₂ → Matrix b₂ a₂ ℂ)
    (hK₂ : MatrixMap.krausAdjoint K₂ (1 : CMatrix b₂) = 1)
    (τ : State (a₁ × a₂)) :
    (isometryImageState (MatrixMap.krausStinespringMatrix
        (MatrixMap.krausProduct K₁ K₂))
      (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one _
        (krausAdjoint_krausProduct_one K₁ K₂ hK₁ hK₂)) τ).reindex prodReassoc =
      isometryImageState (MatrixMap.krausStinespringMatrix K₁ ⊗ₖ
          MatrixMap.krausStinespringMatrix K₂)
        (kronecker_isometry _
          (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one K₁ hK₁)
          _ (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one K₂ hK₂))
        τ := by
  apply State.ext
  rw [State.reindex_matrix, isometryImageState_matrix, isometryImageState_matrix,
    krausStinespringMatrix_krausProduct]
  exact submatrix_prodReassoc_mul _ τ.matrix

/-- First marginal of the reassociated product-stack dilation state: the
dilation state of the first stack isometry. -/
theorem isometryImageState_krausProduct_reindex_marginalA
    {a₁ : Type w₁} {b₁ : Type w₂} {κ₁ : Type w₃}
    {a₂ : Type w₄} {b₂ : Type w₅} {κ₂ : Type w₆}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype κ₁] [DecidableEq κ₁] [Fintype a₂] [DecidableEq a₂]
    [Fintype b₂] [DecidableEq b₂] [Fintype κ₂] [DecidableEq κ₂]
    (K₁ : κ₁ → Matrix b₁ a₁ ℂ)
    (hK₁ : MatrixMap.krausAdjoint K₁ (1 : CMatrix b₁) = 1)
    (K₂ : κ₂ → Matrix b₂ a₂ ℂ)
    (hK₂ : MatrixMap.krausAdjoint K₂ (1 : CMatrix b₂) = 1)
    (τ : State (a₁ × a₂)) :
    ((isometryImageState (MatrixMap.krausStinespringMatrix
        (MatrixMap.krausProduct K₁ K₂))
      (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one _
        (krausAdjoint_krausProduct_one K₁ K₂ hK₁ hK₂)) τ).reindex
        prodReassoc).marginalA =
      isometryImageState (MatrixMap.krausStinespringMatrix K₁)
        (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one K₁ hK₁)
        τ.marginalA := by
  rw [isometryImageState_krausProduct_reindex K₁ hK₁ K₂ hK₂]
  exact marginalA_isometryImageState_kronecker (MatrixMap.krausStinespringMatrix K₁)
    (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one K₁ hK₁)
    (MatrixMap.krausStinespringMatrix K₂)
    (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one K₂ hK₂) τ

/-- Second marginal of the reassociated product-stack dilation state: the
dilation state of the second stack isometry. -/
theorem isometryImageState_krausProduct_reindex_marginalB
    {a₁ : Type w₁} {b₁ : Type w₂} {κ₁ : Type w₃}
    {a₂ : Type w₄} {b₂ : Type w₅} {κ₂ : Type w₆}
    [Fintype a₁] [DecidableEq a₁] [Fintype b₁] [DecidableEq b₁]
    [Fintype κ₁] [DecidableEq κ₁] [Fintype a₂] [DecidableEq a₂]
    [Fintype b₂] [DecidableEq b₂] [Fintype κ₂] [DecidableEq κ₂]
    (K₁ : κ₁ → Matrix b₁ a₁ ℂ)
    (hK₁ : MatrixMap.krausAdjoint K₁ (1 : CMatrix b₁) = 1)
    (K₂ : κ₂ → Matrix b₂ a₂ ℂ)
    (hK₂ : MatrixMap.krausAdjoint K₂ (1 : CMatrix b₂) = 1)
    (τ : State (a₁ × a₂)) :
    ((isometryImageState (MatrixMap.krausStinespringMatrix
        (MatrixMap.krausProduct K₁ K₂))
      (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one _
        (krausAdjoint_krausProduct_one K₁ K₂ hK₁ hK₂)) τ).reindex
        prodReassoc).marginalB =
      isometryImageState (MatrixMap.krausStinespringMatrix K₂)
        (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one K₂ hK₂)
        τ.marginalB := by
  rw [isometryImageState_krausProduct_reindex K₁ hK₁ K₂ hK₂]
  exact marginalB_isometryImageState_kronecker (MatrixMap.krausStinespringMatrix K₁)
    (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one K₁ hK₁)
    (MatrixMap.krausStinespringMatrix K₂)
    (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one K₂ hK₂) τ

/-! ### Rank and the nonzero-eigenvalue count -/

/-- The number of nonzero eigenvalues of a state equals the rank of its
matrix: the spectral theorem writes the state as `U D Uᴴ` with unitary `U`, so
both have the rank of the diagonal `D`, which counts its nonzero entries. -/
theorem card_filter_eigenvalues_eq_rank {a : Type u} [Fintype a] [DecidableEq a]
    (ρ : State a) :
    (Finset.univ.filter (fun i => ρ.pos.isHermitian.eigenvalues i ≠ 0)).card =
      ρ.matrix.rank := by
  classical
  have hspec : ρ.matrix =
      ((ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i => ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ)) *
        star (ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a)) := by
    simpa [Function.comp_def, Unitary.conjStarAlgAut_apply]
      using ρ.pos.isHermitian.spectral_theorem
  have hUU : (star ((ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a)) *
      (ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a)) = (1 : CMatrix a) :=
    Unitary.coe_star_mul_self ρ.pos.isHermitian.eigenvectorUnitary
  -- Unitary invariance of the rank, with the spectral data abstracted so that
  -- no rewrite below touches the `ρ`-dependent eigenvalue terms.
  have hsub : ∀ (w : a → ℝ) (U : CMatrix a), star U * U = 1 →
      (Matrix.diagonal (fun i => ((w i : ℝ) : ℂ))).rank =
        (U * Matrix.diagonal (fun i => ((w i : ℝ) : ℂ)) * star U).rank := by
    intro w U hU'
    have h1 : (U * Matrix.diagonal (fun i => ((w i : ℝ) : ℂ)) * star U).rank ≤
        (Matrix.diagonal (fun i => ((w i : ℝ) : ℂ))).rank := by
      rw [Matrix.mul_assoc]
      exact le_trans (Matrix.rank_mul_le_right _ _) (Matrix.rank_mul_le_left _ _)
    have h2 : (Matrix.diagonal (fun i => ((w i : ℝ) : ℂ))).rank ≤
        (U * Matrix.diagonal (fun i => ((w i : ℝ) : ℂ)) * star U).rank := by
      have hDU' : star U * ((U * Matrix.diagonal (fun i => ((w i : ℝ) : ℂ)) *
          star U) * U) =
          Matrix.diagonal (fun i => ((w i : ℝ) : ℂ)) := by
        calc star U * ((U * Matrix.diagonal (fun i => ((w i : ℝ) : ℂ)) *
                star U) * U)
            = (star U * U) * Matrix.diagonal (fun i => ((w i : ℝ) : ℂ)) *
                (star U * U) := by
              simp only [← Matrix.mul_assoc]
          _ = (1 : CMatrix a) * Matrix.diagonal (fun i => ((w i : ℝ) : ℂ)) * 1 := by
              rw [hU']
          _ = Matrix.diagonal (fun i => ((w i : ℝ) : ℂ)) := by
              rw [Matrix.one_mul, Matrix.mul_one]
      calc (Matrix.diagonal (fun i => ((w i : ℝ) : ℂ))).rank
          = (star U * ((U * Matrix.diagonal (fun i => ((w i : ℝ) : ℂ)) *
              star U) * U)).rank := (congrArg Matrix.rank hDU').symm
        _ ≤ ((U * Matrix.diagonal (fun i => ((w i : ℝ) : ℂ)) * star U) * U).rank :=
            Matrix.rank_mul_le_right _ _
        _ ≤ (U * Matrix.diagonal (fun i => ((w i : ℝ) : ℂ)) * star U).rank :=
            Matrix.rank_mul_le_left _ _
    exact le_antisymm h2 h1
  have hcast : Fintype.card {i : a //
      ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ) ≠ 0} =
      Fintype.card (Finset.univ.filter
        (fun i => ρ.pos.isHermitian.eigenvalues i ≠ 0)) := by
    apply Fintype.card_congr
    refine ⟨fun x => ⟨(x : a),
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,
          fun h => x.2 (Complex.ofReal_eq_zero.mpr h)⟩⟩,
      fun y => ⟨(y : a),
        fun h => (Finset.mem_filter.mp y.2).2 (Complex.ofReal_eq_zero.mp h)⟩,
      fun x => Subtype.ext rfl, fun y => Subtype.ext rfl⟩
  calc (Finset.univ.filter (fun i => ρ.pos.isHermitian.eigenvalues i ≠ 0)).card
      = Fintype.card {i : a //
          ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ) ≠ 0} := by
        rw [← Fintype.card_coe]
        exact hcast.symm
    _ = (Matrix.diagonal (fun i => ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ))).rank :=
        (Matrix.rank_diagonal _).symm
    _ = ((ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a) *
        Matrix.diagonal (fun i => ((ρ.pos.isHermitian.eigenvalues i : ℝ) : ℂ)) *
        star (ρ.pos.isHermitian.eigenvectorUnitary : CMatrix a)).rank :=
        hsub _ _ hUU
    _ = ρ.matrix.rank := by rw [← hspec]

/-! ### The Kraus-stack channel condition -/

/-- The output marginal of a Kraus-stack dilation state realizes the channel
whose Kraus form is the family: the stack-level restatement of the
marginal computation of contract 2. -/
theorem krausStinespring_isometryImageState_marginalA
    {a : Type u} {b : Type v} {κ : Type w}
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
    [Fintype κ] [DecidableEq κ]
    (K : κ → Matrix b a ℂ)
    (hK : MatrixMap.krausAdjoint K (1 : CMatrix b) = 1)
    (Φ : Channel a b) (hΦ : Φ.map = MatrixMap.ofKraus K) (ρ : State a) :
    (isometryImageState (MatrixMap.krausStinespringMatrix K)
      (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one K hK) ρ).marginalA =
      Φ.applyState ρ := by
  apply State.ext
  rw [krausStinespringMatrix_marginalA_matrix K hK ρ,
    show (Φ.applyState ρ).matrix = Φ.map ρ.matrix from rfl, hΦ]

/-! ### Roof superadditivity for two-Kraus qubit channels (contract 4) -/

section Main

variable {y : Type u} {d : Type v} [Fintype y] [DecidableEq y]
variable [Fintype d] [DecidableEq d]
variable {κ : Type w} [Fintype κ] [DecidableEq κ]

/-- **Corollary 8, first displayed equation: roof superadditivity for two-Kraus
qubit channels.**  If the qubit channel `N` admits a Kraus representation with
at most two operators, then for every channel `M` and every input state `τ` on
`X ⊗ Y`, the output-entropy convex roof is superadditive:
`roof(N ⊗ M)(τ) ≥ roof(N)(τ_X) + roof(M)(τ_Y)`.

The proof embeds the Kraus index type of `N` into the qubit, stacks the two
Stinespring isometries into a product dilation `Ω` of `τ`, and notes that the
reassociated two-qubit marginal `S τ_X Sᴴ` has rank at most two because the
stack isometry `S` is a `4 × 2`-ish contraction of a qubit environment.
`RankTwoKernel` supplies a nonzero product kernel vector, the full-form
Theorem 6 gives `E_F` superadditivity for `Ω`, and the generalized MSW
identity translates all three `E_F` terms to output-entropy roofs.  The Wootters
interface hypothesis is carried, as everywhere in this repository. -/
theorem outputEntropyRoof_prod_ge_of_twoKraus
    (h : woottersKernelUpperBound)
    (hcard : Fintype.card κ ≤ 2)
    (K : κ → Matrix Qubit Qubit ℂ)
    (N : Channel Qubit Qubit)
    (hN : N.map = MatrixMap.ofKraus K)
    (M : Channel y d)
    (τ : State (Qubit × y)) :
    outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB ≤
      outputEntropyRoof (N.prod M) τ := by
  classical
  -- The qubit-extended Kraus family of `N` and its completeness.
  have hTP : MatrixMap.IsTracePreserving
      (MatrixMap.ofKraus (krausExtend K hcard)) := by
    rw [MatrixMap.ofKraus_krausExtend K hcard, ← hN]
    exact N.tracePreserving
  have hK' : MatrixMap.krausAdjoint (krausExtend K hcard) (1 : CMatrix Qubit) = 1 :=
    MatrixMap.krausAdjoint_one_of_tracePreserving _ hTP
  have hL : MatrixMap.krausAdjoint M.kraus (1 : CMatrix d) = 1 := M.krausAdjoint_one
  -- The three stack-dilation channel conditions.
  have hchanS : ∀ ρ : State Qubit,
      (isometryImageState (MatrixMap.krausStinespringMatrix (krausExtend K hcard))
        (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
          (krausExtend K hcard) hK') ρ).marginalA = N.applyState ρ :=
    krausStinespring_isometryImageState_marginalA (krausExtend K hcard) hK' N
      (hN.trans (MatrixMap.ofKraus_krausExtend K hcard).symm)
  have hchanR : ∀ ρ : State y,
      (isometryImageState (MatrixMap.krausStinespringMatrix M.kraus)
        (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one M.kraus hL)
        ρ).marginalA = M.applyState ρ :=
    krausStinespring_isometryImageState_marginalA M.kraus hL M M.map_eq_ofKraus
  have hchanU : ∀ ρ : State (Qubit × y),
      (isometryImageState (MatrixMap.krausStinespringMatrix
          (MatrixMap.krausProduct (krausExtend K hcard) M.kraus))
        (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
          (MatrixMap.krausProduct (krausExtend K hcard) M.kraus)
          (krausAdjoint_krausProduct_one (krausExtend K hcard) M.kraus hK' hL))
        ρ).marginalA = (N.prod M).applyState ρ := by
    intro ρ
    apply State.ext
    rw [krausStinespringMatrix_marginalA_matrix
        (MatrixMap.krausProduct (krausExtend K hcard) M.kraus)
        (krausAdjoint_krausProduct_one (krausExtend K hcard) M.kraus hK' hL) ρ,
      show ((N.prod M).applyState ρ).matrix =
        (MatrixMap.kron N.map M.map) ρ.matrix from rfl,
      hN, ← MatrixMap.ofKraus_krausExtend K hcard, M.map_eq_ofKraus,
      MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct]
  -- The two-qubit output marginal of the reassociated product dilation state
  -- is the dilation of `τ_X` under a stack isometry of width two.
  have hrank : (isometryImageState
      (MatrixMap.krausStinespringMatrix (krausExtend K hcard))
      (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
        (krausExtend K hcard) hK') τ.marginalA).matrix.rank ≤ 2 := by
    rw [isometryImageState_matrix]
    calc (MatrixMap.krausStinespringMatrix (krausExtend K hcard) *
        τ.marginalA.matrix *
        (MatrixMap.krausStinespringMatrix (krausExtend K hcard)).conjTranspose).rank
        ≤ (MatrixMap.krausStinespringMatrix (krausExtend K hcard) *
            τ.marginalA.matrix).rank :=
          Matrix.rank_mul_le_left _ _
      _ ≤ (MatrixMap.krausStinespringMatrix (krausExtend K hcard)).rank :=
          Matrix.rank_mul_le_left _ _
      _ ≤ Fintype.card Qubit := Matrix.rank_le_card_width _
      _ = 2 := by simp
  obtain ⟨u, v, hu, hv, hker⟩ := exists_product_kernelVector_of_rank_le_two
    (isometryImageState (MatrixMap.krausStinespringMatrix (krausExtend K hcard))
      (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
        (krausExtend K hcard) hK') τ.marginalA)
    (by rw [card_filter_eigenvalues_eq_rank]; exact hrank)
  -- The product kernel condition for Theorem 6.
  have hker' : ((isometryImageState (MatrixMap.krausStinespringMatrix
        (MatrixMap.krausProduct (krausExtend K hcard) M.kraus))
      (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
        (MatrixMap.krausProduct (krausExtend K hcard) M.kraus)
        (krausAdjoint_krausProduct_one (krausExtend K hcard) M.kraus hK' hL))
      τ).reindex prodReassoc).marginalA.matrix *ᵥ
      (fun p => u p.1 * v p.2) = 0 := by
    rw [isometryImageState_krausProduct_reindex_marginalA (krausExtend K hcard) hK'
      M.kraus hL τ]
    exact hker
  -- The three generalized-MSW translations.
  have hroofS : outputEntropyRoof N τ.marginalA =
      entanglementOfFormation (isometryImageState
        (MatrixMap.krausStinespringMatrix (krausExtend K hcard))
        (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
          (krausExtend K hcard) hK') τ.marginalA) :=
    outputEntropyRoof_eq_entanglementOfFormation_of_isometry N _ _ hchanS τ.marginalA
  have hroofR : outputEntropyRoof M τ.marginalB =
      entanglementOfFormation (isometryImageState
        (MatrixMap.krausStinespringMatrix M.kraus)
        (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one M.kraus hL)
        τ.marginalB) :=
    outputEntropyRoof_eq_entanglementOfFormation_of_isometry M _ _ hchanR τ.marginalB
  have hroofU : outputEntropyRoof (N.prod M) τ =
      entanglementOfFormation (isometryImageState
        (MatrixMap.krausStinespringMatrix
          (MatrixMap.krausProduct (krausExtend K hcard) M.kraus))
        (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
          (MatrixMap.krausProduct (krausExtend K hcard) M.kraus)
          (krausAdjoint_krausProduct_one (krausExtend K hcard) M.kraus hK' hL))
        τ) :=
    outputEntropyRoof_eq_entanglementOfFormation_of_isometry (N.prod M) _ _ hchanU τ
  -- Theorem 6 in full form.
  have hmain := entanglementOfFormation_superadditive_of_productKernel h
    (isometryImageState (MatrixMap.krausStinespringMatrix
        (MatrixMap.krausProduct (krausExtend K hcard) M.kraus))
      (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
        (MatrixMap.krausProduct (krausExtend K hcard) M.kraus)
        (krausAdjoint_krausProduct_one (krausExtend K hcard) M.kraus hK' hL))
      τ) u v hu hv hker'
  -- Assembly.
  calc outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB
      = entanglementOfFormation (isometryImageState
          (MatrixMap.krausStinespringMatrix (krausExtend K hcard))
          (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
            (krausExtend K hcard) hK') τ.marginalA) +
        entanglementOfFormation (isometryImageState
          (MatrixMap.krausStinespringMatrix M.kraus)
          (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one M.kraus hL)
          τ.marginalB) := by rw [hroofS, hroofR]
    _ = entanglementOfFormation ((isometryImageState
          (MatrixMap.krausStinespringMatrix
            (MatrixMap.krausProduct (krausExtend K hcard) M.kraus))
          (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
            (MatrixMap.krausProduct (krausExtend K hcard) M.kraus)
            (krausAdjoint_krausProduct_one (krausExtend K hcard) M.kraus hK' hL))
          τ).reindex prodReassoc).marginalA +
        entanglementOfFormation ((isometryImageState
          (MatrixMap.krausStinespringMatrix
            (MatrixMap.krausProduct (krausExtend K hcard) M.kraus))
          (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
            (MatrixMap.krausProduct (krausExtend K hcard) M.kraus)
            (krausAdjoint_krausProduct_one (krausExtend K hcard) M.kraus hK' hL))
          τ).reindex prodReassoc).marginalB := by
          rw [isometryImageState_krausProduct_reindex_marginalA
            (krausExtend K hcard) hK' M.kraus hL τ,
            isometryImageState_krausProduct_reindex_marginalB
            (krausExtend K hcard) hK' M.kraus hL τ]
    _ ≤ entanglementOfFormation (isometryImageState
          (MatrixMap.krausStinespringMatrix
            (MatrixMap.krausProduct (krausExtend K hcard) M.kraus))
          (MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one
            (MatrixMap.krausProduct (krausExtend K hcard) M.kraus)
            (krausAdjoint_krausProduct_one (krausExtend K hcard) M.kraus hK' hL))
          τ) := hmain
    _ = outputEntropyRoof (N.prod M) τ := hroofU.symm

end Main

end

end AmplitudeDamping