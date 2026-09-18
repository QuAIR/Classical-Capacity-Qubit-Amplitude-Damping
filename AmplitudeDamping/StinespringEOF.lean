import AmplitudeDamping.ChannelStinespring
import AmplitudeDamping.EntanglementFormation

/-!
# The MSW identity: output-entropy convex roof as an entanglement of formation

This module proves the Matsumoto-Shimono-Winter correspondence (manuscript
equation (msw)) for the chosen Stinespring dilation of `ChannelStinespring.lean`:
the output-entropy convex roof of a channel at an input state equals the
entanglement of formation of the dilation state across the output-environment
bipartition.

Both directions follow the paper's pure-decomposition correspondence.  The
forward map conjugates every branch of a pure decomposition of the input through
the isometry; the backward map pulls every positive-weight branch of a pure
decomposition of the dilation state back through the isometry adjoint, using
that each such branch lies in the support of `V τ V†` and hence in the image of
`V`.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder NNReal

namespace AmplitudeDamping

open QIT

universe u v

noncomputable section

variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-! ### The Stinespring dilation state -/

/-- The dilation state `V τ V†` of an input state under the chosen Stinespring
isometry: a bipartite state on the output-environment system `b × (a × b)`. -/
def dilationState (Phi : Channel a b) (tau : State a) :
    State (Prod b (Prod a b)) where
  matrix := Phi.stinespringIsometry.matrix * tau.matrix *
    Matrix.conjTranspose Phi.stinespringIsometry.matrix
  pos := tau.pos.mul_mul_conjTranspose_same _
  trace_eq_one := by
    have hV := Phi.stinespringIsometry.isometry
    calc
      (Phi.stinespringIsometry.matrix * tau.matrix *
          Matrix.conjTranspose Phi.stinespringIsometry.matrix).trace =
          (Matrix.conjTranspose Phi.stinespringIsometry.matrix *
            Phi.stinespringIsometry.matrix * tau.matrix).trace :=
        Matrix.trace_mul_cycle _ _ _
      _ = ((1 : CMatrix a) * tau.matrix).trace := by
        rw [hV]
      _ = tau.matrix.trace := by rw [Matrix.one_mul]
      _ = 1 := tau.trace_eq_one

/-- The dilation state's matrix unfolds to the isometry conjugation. -/
theorem dilationState_matrix (Phi : Channel a b) (tau : State a) :
    (dilationState Phi tau).matrix =
      Phi.stinespringIsometry.matrix * tau.matrix *
        Matrix.conjTranspose Phi.stinespringIsometry.matrix :=
  rfl

/-- The output marginal of the dilation state is the channel output state. -/
theorem dilationState_marginalA (Phi : Channel a b) (tau : State a) :
    (dilationState Phi tau).marginalA = Phi.applyState tau := by
  apply State.ext
  rw [State.marginalA_matrix, dilationState_matrix,
    show (Phi.applyState tau).matrix = Phi.map tau.matrix from rfl,
    Phi.map_eq_ofKraus]
  ext y y'
  simp only [partialTraceB, Matrix.mul_apply, Matrix.conjTranspose_apply,
    Channel.stinespringIsometry_matrix, MatrixMap.krausStinespringMatrix,
    MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply,
    Finset.sum_mul]

/-! ### Conjugated pure vectors -/

/-- The image of a pure input vector under the Stinespring isometry. -/
def stinespringPureVector (Phi : Channel a b) (psi : PureVector a) :
    PureVector (Prod b (Prod a b)) where
  amp := Phi.stinespringIsometry.matrix.mulVec psi.amp
  trace_rankOne_eq_one := by
    have hV := Phi.stinespringIsometry.isometry
    have hrank : rankOneMatrix (Phi.stinespringIsometry.matrix.mulVec psi.amp) =
        Phi.stinespringIsometry.matrix * rankOneMatrix psi.amp *
          Matrix.conjTranspose Phi.stinespringIsometry.matrix :=
      rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose _ _
    rw [hrank, Matrix.trace_mul_cycle, hV, Matrix.one_mul]
    exact psi.trace_rankOne_eq_one

/-- The amplitude of a conjugated pure vector unfolds to `V ψ`. -/
@[simp]
theorem stinespringPureVector_amp (Phi : Channel a b) (psi : PureVector a) :
    (stinespringPureVector Phi psi).amp =
      Phi.stinespringIsometry.matrix.mulVec psi.amp :=
  rfl

/-- Tracing out the environment of a conjugated rank-one kernel gives the
coefficient-matrix Gram matrix. -/
theorem partialTraceB_rankOne_stinespring
    (Phi : Channel a b) (v : a → ℂ) :
    partialTraceB (a := b) (b := Prod a b)
        (rankOneMatrix (Phi.stinespringIsometry.matrix.mulVec v)) =
      Phi.stinespringCoefficientMatrix v *
        (Phi.stinespringCoefficientMatrix v).conjTranspose := by
  ext y y'
  simp only [partialTraceB, rankOneMatrix_apply, Matrix.mul_apply,
    Matrix.conjTranspose_apply, Channel.stinespringCoefficientMatrix,
    Matrix.mulVec, dotProduct, Channel.stinespringIsometry_matrix_apply]

/-- The output marginal of a conjugated pure vector is the channel output state
of the original pure vector. -/
theorem stinespringPureVector_state_marginalA
    (Phi : Channel a b) (psi : PureVector a) :
    (stinespringPureVector Phi psi).state.marginalA =
      Phi.applyState psi.state := by
  apply State.ext
  rw [State.marginalA_matrix, PureVector.state_matrix,
    stinespringPureVector_amp, partialTraceB_rankOne_stinespring,
    Phi.stinespringCoefficientMatrix_gram]
  rfl

/-! ### The forward correspondence -/

/-- The forward image of a pure input decomposition under the Stinespring
isometry: same weights, conjugated branch vectors. -/
def stinespringDecomposition (Phi : Channel a b) (E : PureDecomposition a) :
    PureDecomposition (Prod b (Prod a b)) where
  card := E.card
  probs := E.probs
  weights_sum := E.weights_sum
  vectors := fun i => stinespringPureVector Phi (E.vectors i)

/-- The forward image of a decomposition of `τ` decomposes the dilation state
of `τ`. -/
theorem stinespringDecomposition_averageState
    (Phi : Channel a b) (E : PureDecomposition a) :
    (stinespringDecomposition Phi E).averageState =
      dilationState Phi E.averageState := by
  apply State.ext
  have hleaf : ∀ i : Fin E.card,
      ((((E.probs i : ℝ≥0) : ℝ) : ℂ) •
          (stinespringPureVector Phi (E.vectors i)).state.matrix) =
        Phi.stinespringIsometry.matrix *
          ((((E.probs i : ℝ≥0) : ℝ) : ℂ) •
            rankOneMatrix (E.vectors i).amp) *
          Matrix.conjTranspose Phi.stinespringIsometry.matrix := by
    intro i
    have hrank : (stinespringPureVector Phi (E.vectors i)).state.matrix =
        Phi.stinespringIsometry.matrix *
          rankOneMatrix (E.vectors i).amp *
          Matrix.conjTranspose Phi.stinespringIsometry.matrix := by
      show rankOneMatrix (Phi.stinespringIsometry.matrix.mulVec
        (E.vectors i).amp) = _
      exact rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose _ _
    rw [hrank, Matrix.mul_smul, Matrix.smul_mul]
  rw [dilationState_matrix, PureDecomposition.averageState,
    PureDecomposition.averageState, Ensemble.averageState_matrix,
    Ensemble.averageState_matrix]
  change (∑ i : Fin E.card,
      ((((E.probs i : ℝ≥0) : ℝ) : ℂ) •
        (stinespringPureVector Phi (E.vectors i)).state.matrix)) =
    Phi.stinespringIsometry.matrix *
      (∑ i : Fin E.card,
        ((((E.probs i : ℝ≥0) : ℝ) : ℂ) •
          rankOneMatrix (E.vectors i).amp)) *
      Matrix.conjTranspose Phi.stinespringIsometry.matrix
  rw [Finset.sum_congr rfl (fun i _ => hleaf i)]
  calc (∑ i : Fin E.card,
        Phi.stinespringIsometry.matrix *
          ((((E.probs i : ℝ≥0) : ℝ) : ℂ) •
            rankOneMatrix (E.vectors i).amp) *
          Matrix.conjTranspose Phi.stinespringIsometry.matrix) =
        (∑ i : Fin E.card,
          Phi.stinespringIsometry.matrix *
            ((((E.probs i : ℝ≥0) : ℝ) : ℂ) •
              rankOneMatrix (E.vectors i).amp)) *
        Matrix.conjTranspose Phi.stinespringIsometry.matrix :=
      (Matrix.sum_mul Finset.univ _ _).symm
    _ = (Phi.stinespringIsometry.matrix *
        ∑ i : Fin E.card,
          ((((E.probs i : ℝ≥0) : ℝ) : ℂ) •
            rankOneMatrix (E.vectors i).amp)) *
        Matrix.conjTranspose Phi.stinespringIsometry.matrix := by
          rw [Matrix.mul_sum]
    _ = Phi.stinespringIsometry.matrix *
        (∑ i : Fin E.card,
          ((((E.probs i : ℝ≥0) : ℝ) : ℂ) •
            rankOneMatrix (E.vectors i).amp)) *
        Matrix.conjTranspose Phi.stinespringIsometry.matrix := rfl

/-- The forward correspondence preserves the cost: the entanglement cost of the
conjugated decomposition equals the output cost of the original. -/
theorem stinespringDecomposition_entanglementCost
    (Phi : Channel a b) (E : PureDecomposition a) :
    (stinespringDecomposition Phi E).entanglementCost = E.outputCost Phi := by
  unfold PureDecomposition.entanglementCost PureDecomposition.outputCost
    outputEntropyCost
  apply Finset.sum_congr rfl
  intro i _
  have hvec : ((stinespringDecomposition Phi E).vectors i).state.marginalA =
      Phi.applyState (E.vectors i).state :=
    stinespringPureVector_state_marginalA Phi (E.vectors i)
  rw [hvec]
  rfl

/-- The entanglement of formation of the dilation state is bounded by the
output-entropy convex roof: the forward correspondence maps every decomposition
of the input to a decomposition of the dilation state of the same cost. -/
theorem entanglementOfFormation_dilationState_le_outputEntropyRoof
    (Phi : Channel a b) (tau : State a) :
    entanglementOfFormation (dilationState Phi tau) ≤
      outputEntropyRoof Phi tau := by
  apply le_csInf (pureOutputEntropyValues_nonempty Phi tau)
  intro x hx
  rcases hx with ⟨E, hE, rfl⟩
  have hle := entanglementOfFormation_le_entanglementCost
    (stinespringDecomposition Phi E)
  rw [stinespringDecomposition_averageState, hE] at hle
  rwa [stinespringDecomposition_entanglementCost] at hle

/-! ### The range projection of the Stinespring isometry -/

/-- The range projection `V V†` of the chosen Stinespring isometry. -/
def stinespringProjection (Phi : Channel a b) :
    Matrix (Prod b (Prod a b)) (Prod b (Prod a b)) ℂ :=
  Phi.stinespringIsometry.matrix *
    Matrix.conjTranspose Phi.stinespringIsometry.matrix

/-- The range projection of an isometry is idempotent. -/
theorem stinespringProjection_mul_self (Phi : Channel a b) :
    stinespringProjection Phi * stinespringProjection Phi =
      stinespringProjection Phi := by
  have hV := Phi.stinespringIsometry.isometry
  show Phi.stinespringIsometry.matrix *
      Matrix.conjTranspose Phi.stinespringIsometry.matrix *
    (Phi.stinespringIsometry.matrix *
      Matrix.conjTranspose Phi.stinespringIsometry.matrix) = _
  rw [Matrix.mul_assoc,
    ← Matrix.mul_assoc
      (Matrix.conjTranspose Phi.stinespringIsometry.matrix)
      Phi.stinespringIsometry.matrix
      (Matrix.conjTranspose Phi.stinespringIsometry.matrix),
    hV, Matrix.one_mul]
  rfl

/-- The range projection of an isometry is Hermitian. -/
theorem stinespringProjection_conjTranspose (Phi : Channel a b) :
    Matrix.conjTranspose (stinespringProjection Phi) =
      stinespringProjection Phi := by
  rw [stinespringProjection, Matrix.conjTranspose_mul,
    Matrix.conjTranspose_conjTranspose]

/-- The isometry adjoint annihilates the complement of the range projection. -/
theorem conjTranspose_stinespring_mul_one_sub_projection (Phi : Channel a b) :
    Matrix.conjTranspose Phi.stinespringIsometry.matrix *
      (1 - stinespringProjection Phi) = 0 := by
  have hV := Phi.stinespringIsometry.isometry
  rw [Matrix.mul_sub, Matrix.mul_one, stinespringProjection,
    ← Matrix.mul_assoc, hV, Matrix.one_mul, sub_self]

/-- The complement of the range projection is idempotent. -/
theorem one_sub_stinespringProjection_mul_self (Phi : Channel a b) :
    (1 - stinespringProjection Phi) * (1 - stinespringProjection Phi) =
      1 - stinespringProjection Phi := by
  rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one,
    stinespringProjection_mul_self]
  abel


/-- The complement of the range projection is Hermitian. -/
theorem one_sub_stinespringProjection_conjTranspose (Phi : Channel a b) :
    Matrix.conjTranspose (1 - stinespringProjection Phi) =
      1 - stinespringProjection Phi := by
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
    stinespringProjection_conjTranspose]

/-- The dilation state annihilates vectors orthogonal to the isometry range:
`V τ V† (1 - V V†) = 0` since `V† (1 - V V†) = 0`. -/
theorem dilationState_mulVec_one_sub_projection
    (Phi : Channel a b) (tau : State a)
    (w : Prod b (Prod a b) → ℂ) :
    (dilationState Phi tau).matrix.mulVec
      ((1 - stinespringProjection Phi).mulVec w) = 0 := by
  have hzero : (dilationState Phi tau).matrix *
      (1 - stinespringProjection Phi) = 0 := by
    rw [dilationState_matrix, Matrix.mul_assoc,
      conjTranspose_stinespring_mul_one_sub_projection, Matrix.mul_zero]
  rw [Matrix.mulVec_mulVec, hzero, Matrix.zero_mulVec]

/-- Quadratic form of an average state: contracting the weighted sum of
rank-one kernels of a pure decomposition with any test vector expands as a sum
of nonnegative weighted squared moduli, one term per branch. -/
theorem star_inner_averageState_mulVec {c : Type u} [Fintype c] [DecidableEq c]
    (E : PureDecomposition c) (phi : c → ℂ) :
    star phi ⬝ᵥ (E.averageState.matrix.mulVec phi) =
      ∑ j : Fin E.card,
        (((E.probs j : ℝ) *
          Complex.normSq (star (E.vectors j).amp ⬝ᵥ phi) : ℝ) : ℂ) := by
  have hM : ∀ y z : c, E.averageState.matrix y z =
      ∑ j : Fin E.card, ((E.probs j : ℝ) : ℂ) *
        ((E.vectors j).amp y * star ((E.vectors j).amp z)) := by
    intro y z
    rw [PureDecomposition.averageState, Ensemble.averageState_matrix,
      Matrix.sum_apply]
    apply Finset.sum_congr rfl
    intro j _
    show (E.probs j : ℝ≥0) • ((E.vectors j).state.matrix y z) = _
    rw [NNReal.smul_def, Algebra.smul_def]
    have hcast : (algebraMap ℝ ℂ) ((E.probs j : ℝ)) = ((E.probs j : ℝ) : ℂ) :=
      rfl
    rw [hcast, PureVector.state_matrix_apply]
  simp only [Matrix.mulVec, dotProduct, Pi.star_apply, hM]
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  have hswap : (∑ y : c, ∑ z : c,
        star (phi y) * ∑ j : Fin E.card, (((E.probs j : ℝ) : ℂ) *
          ((E.vectors j).amp y * star ((E.vectors j).amp z)) * phi z)) =
      ∑ j : Fin E.card, ∑ z : c, ∑ y : c,
        star (phi y) * (((E.probs j : ℝ) : ℂ) *
          ((E.vectors j).amp y * star ((E.vectors j).amp z)) * phi z) := by
    have step1 : (∑ y : c, ∑ z : c,
        star (phi y) * ∑ j : Fin E.card, (((E.probs j : ℝ) : ℂ) *
          ((E.vectors j).amp y * star ((E.vectors j).amp z)) * phi z)) =
      ∑ y : c, ∑ z : c, ∑ j : Fin E.card,
        star (phi y) * (((E.probs j : ℝ) : ℂ) *
          ((E.vectors j).amp y * star ((E.vectors j).amp z)) * phi z) := by
      apply Finset.sum_congr rfl
      intro y _
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.mul_sum]
    rw [step1]
    calc (∑ y : c, ∑ z : c, ∑ j : Fin E.card,
          star (phi y) * (((E.probs j : ℝ) : ℂ) *
            ((E.vectors j).amp y * star ((E.vectors j).amp z)) * phi z)) =
        ∑ z : c, ∑ y : c, ∑ j : Fin E.card,
          star (phi y) * (((E.probs j : ℝ) : ℂ) *
            ((E.vectors j).amp y * star ((E.vectors j).amp z)) * phi z) :=
      Finset.sum_comm
    _ = ∑ z : c, ∑ j : Fin E.card, ∑ y : c,
          star (phi y) * (((E.probs j : ℝ) : ℂ) *
            ((E.vectors j).amp y * star ((E.vectors j).amp z)) * phi z) := by
        apply Finset.sum_congr rfl
        intro z _
        exact Finset.sum_comm
    _ = ∑ j : Fin E.card, ∑ z : c, ∑ y : c,
          star (phi y) * (((E.probs j : ℝ) : ℂ) *
            ((E.vectors j).amp y * star ((E.vectors j).amp z)) * phi z) :=
      Finset.sum_comm
  rw [hswap]
  apply Finset.sum_congr rfl
  intro j _
  have hsplit : ∀ z : c,
      (∑ y : c, star (phi y) * (((E.probs j : ℝ) : ℂ) *
          ((E.vectors j).amp y * star ((E.vectors j).amp z)) * phi z)) =
      ((E.probs j : ℝ) : ℂ) *
        ((∑ y : c, star (phi y) * (E.vectors j).amp y) *
          star ((E.vectors j).amp z) * phi z) := by
    intro z
    have hleaf : ∀ y : c,
        star (phi y) * (((E.probs j : ℝ) : ℂ) *
          ((E.vectors j).amp y * star ((E.vectors j).amp z)) * phi z) =
        ((E.probs j : ℝ) : ℂ) *
          ((star (phi y) * (E.vectors j).amp y) *
            (star ((E.vectors j).amp z) * phi z)) := by
      intro y
      ring
    rw [Finset.sum_congr rfl (fun y _ => hleaf y), ← Finset.mul_sum,
      ← Finset.sum_mul]
    ring
  rw [Finset.sum_congr rfl (fun z _ => hsplit z)]
  have hcomm : ∀ z : c,
      (((E.probs j : ℝ) : ℂ) *
        ((∑ y : c, star (phi y) * (E.vectors j).amp y) *
          star ((E.vectors j).amp z) * phi z)) =
      ((E.probs j : ℝ) : ℂ) *
        ((star ((E.vectors j).amp z) * phi z) *
          (∑ y : c, star (phi y) * (E.vectors j).amp y)) := by
    intro z
    ring
  rw [Finset.sum_congr rfl (fun z _ => hcomm z), ← Finset.mul_sum,
    ← Finset.sum_mul]
  rw [Complex.ofReal_mul, Complex.normSq_eq_conj_mul_self]
  have hA : (∑ y : c, star (phi y) * (E.vectors j).amp y) =
      conj (∑ x : c, star ((E.vectors j).amp x) * phi x) := by
    have h1 : conj (∑ x : c, star ((E.vectors j).amp x) * phi x) =
        star (∑ x : c, star ((E.vectors j).amp x) * phi x) := rfl
    rw [h1, star_sum]
    apply Finset.sum_congr rfl
    intro x _
    rw [star_mul, star_star]
  rw [hA]
  congr 1
  exact mul_comm _ _

/-! ### The backward correspondence -/

/-- A normalized basis pure vector, used as an inert placeholder for branches of
zero weight. -/
def basisPureVector [DecidableEq a] (x : a) : PureVector a where
  amp := fun y => if y = x then 1 else 0
  trace_rankOne_eq_one := by
    show (∑ y : a,
        (if y = x then (1 : ℂ) else 0) * star (if y = x then (1 : ℂ) else 0)) = 1
    rw [Finset.sum_eq_single x]
    · simp
    · intro y _ hy
      simp [hy]
    · intro hnot
      exact False.elim (hnot (Finset.mem_univ x))

/-- Every positive-weight branch of a pure decomposition of the dilation state
lies in the range of the Stinespring isometry: positivity of `V τ V†` dominates
the branch, so the branch is orthogonal to the range complement. -/
theorem stinespringProjection_mulVec_of_pos_weight
    (Phi : Channel a b) (tau : State a)
    (D : PureDecomposition (Prod b (Prod a b)))
    (hD : D.averageState = dilationState Phi tau) (i : Fin D.card)
    (hpos : 0 < (D.probs i : ℝ)) :
    (stinespringProjection Phi).mulVec (D.vectors i).amp =
      (D.vectors i).amp := by
  have hident := star_inner_averageState_mulVec D
    ((1 - stinespringProjection Phi).mulVec (D.vectors i).amp)
  rw [hD, dilationState_mulVec_one_sub_projection, dotProduct_zero] at hident
  rw [← Complex.ofReal_sum] at hident
  have hsum : (∑ j : Fin D.card,
      ((D.probs j : ℝ) *
        Complex.normSq (star (D.vectors j).amp ⬝ᵥ
          (1 - stinespringProjection Phi).mulVec (D.vectors i).amp))) = 0 := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_zero]
    exact hident.symm
  have hnn : ∀ j : Fin D.card, j ∈ Finset.univ →
      0 ≤ (D.probs j : ℝ) *
        Complex.normSq (star (D.vectors j).amp ⬝ᵥ
          (1 - stinespringProjection Phi).mulVec (D.vectors i).amp) := by
    intro j _
    exact mul_nonneg (NNReal.coe_nonneg _) (Complex.normSq_nonneg _)
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum i (Finset.mem_univ i)
  rcases mul_eq_zero.mp hterm with hp | hn
  · exact absurd hp (ne_of_gt hpos)
  · have hdot : star (D.vectors i).amp ⬝ᵥ
        (1 - stinespringProjection Phi).mulVec (D.vectors i).amp = 0 :=
      Complex.normSq_eq_zero.mp hn
    have hnorm : star ((1 - stinespringProjection Phi).mulVec (D.vectors i).amp) ⬝ᵥ
        ((1 - stinespringProjection Phi).mulVec (D.vectors i).amp) =
        star (D.vectors i).amp ⬝ᵥ
          (1 - stinespringProjection Phi).mulVec (D.vectors i).amp := by
      rw [Matrix.star_mulVec, one_sub_stinespringProjection_conjTranspose,
        ← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec,
        one_sub_stinespringProjection_mul_self]
    have hzero : star ((1 - stinespringProjection Phi).mulVec (D.vectors i).amp) ⬝ᵥ
        ((1 - stinespringProjection Phi).mulVec (D.vectors i).amp) = 0 := by
      rw [hnorm, hdot]
    have hphi : (1 - stinespringProjection Phi).mulVec (D.vectors i).amp = 0 :=
      dotProduct_star_self_eq_zero.mp hzero
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, sub_eq_zero] at hphi
    exact hphi.symm

/-- The pullback of a pure dilation branch lying in the range of the Stinespring
isometry, through the isometry adjoint. -/
def stinespringPullbackPureVector (Phi : Channel a b)
    (psi : PureVector (Prod b (Prod a b)))
    (hrange : (stinespringProjection Phi).mulVec psi.amp = psi.amp) :
    PureVector a where
  amp := (Matrix.conjTranspose Phi.stinespringIsometry.matrix).mulVec psi.amp
  trace_rankOne_eq_one := by
    have hV := Phi.stinespringIsometry.isometry
    have hrank : rankOneMatrix
        ((Matrix.conjTranspose Phi.stinespringIsometry.matrix).mulVec psi.amp) =
        Matrix.conjTranspose Phi.stinespringIsometry.matrix *
          rankOneMatrix psi.amp * Phi.stinespringIsometry.matrix := by
      rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose,
        Matrix.conjTranspose_conjTranspose]
    have hPRP : stinespringProjection Phi * rankOneMatrix psi.amp *
        stinespringProjection Phi = rankOneMatrix psi.amp := by
      have h := rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose
        (stinespringProjection Phi) psi.amp
      rw [hrange, stinespringProjection_conjTranspose] at h
      exact h.symm
    show (rankOneMatrix
      ((Matrix.conjTranspose Phi.stinespringIsometry.matrix).mulVec psi.amp)).trace = 1
    rw [hrank,
      show (Matrix.conjTranspose Phi.stinespringIsometry.matrix *
          rankOneMatrix psi.amp * Phi.stinespringIsometry.matrix).trace =
        (Phi.stinespringIsometry.matrix *
          Matrix.conjTranspose Phi.stinespringIsometry.matrix *
          rankOneMatrix psi.amp).trace from
        Matrix.trace_mul_cycle
          (Matrix.conjTranspose Phi.stinespringIsometry.matrix)
          (rankOneMatrix psi.amp) Phi.stinespringIsometry.matrix,
      show Phi.stinespringIsometry.matrix *
          Matrix.conjTranspose Phi.stinespringIsometry.matrix *
          rankOneMatrix psi.amp =
        stinespringProjection Phi * rankOneMatrix psi.amp from rfl,
      show (stinespringProjection Phi * rankOneMatrix psi.amp).trace =
        (stinespringProjection Phi * stinespringProjection Phi *
          rankOneMatrix psi.amp).trace from by
        rw [stinespringProjection_mul_self],
      Matrix.trace_mul_cycle, Matrix.trace_mul_cycle, hPRP]
    exact psi.trace_rankOne_eq_one

/-- The pullback amplitude unfolds to `V† ψ`. -/
@[simp]
theorem stinespringPullbackPureVector_amp (Phi : Channel a b)
    (psi : PureVector (Prod b (Prod a b)))
    (hrange : (stinespringProjection Phi).mulVec psi.amp = psi.amp) :
    (stinespringPullbackPureVector Phi psi hrange).amp =
      (Matrix.conjTranspose Phi.stinespringIsometry.matrix).mulVec psi.amp :=
  rfl

/-- The isometry maps the pullback amplitude back to the original branch. -/
theorem stinespringIsometry_mulVec_pullback (Phi : Channel a b)
    (psi : PureVector (Prod b (Prod a b)))
    (hrange : (stinespringProjection Phi).mulVec psi.amp = psi.amp) :
    Phi.stinespringIsometry.matrix.mulVec
      (stinespringPullbackPureVector Phi psi hrange).amp = psi.amp := by
  rw [stinespringPullbackPureVector_amp, Matrix.mulVec_mulVec]
  show (stinespringProjection Phi).mulVec psi.amp = psi.amp
  exact hrange

/-- Pure vectors with equal amplitudes represent the same pure state. -/
theorem PureVector.state_eq_of_amp_eq {c : Type u} [Fintype c] [DecidableEq c]
    {psi chi : PureVector c} (h : psi.amp = chi.amp) : psi.state = chi.state := by
  apply State.ext
  rw [PureVector.state_matrix, PureVector.state_matrix, h]

/-- The forward conjugate of the pullback of a range branch is the original
branch. -/
theorem stinespringPureVector_state_pullback (Phi : Channel a b)
    (psi : PureVector (Prod b (Prod a b)))
    (hrange : (stinespringProjection Phi).mulVec psi.amp = psi.amp) :
    (stinespringPureVector Phi
      (stinespringPullbackPureVector Phi psi hrange)).state = psi.state := by
  refine PureVector.state_eq_of_amp_eq ?_
  rw [stinespringPureVector_amp]
  exact stinespringIsometry_mulVec_pullback Phi psi hrange

/-- The channel output of the pullback of a range branch is the output marginal
of the original branch. -/
theorem applyState_stinespringPullbackPureVector (Phi : Channel a b)
    (psi : PureVector (Prod b (Prod a b)))
    (hrange : (stinespringProjection Phi).mulVec psi.amp = psi.amp) :
    Phi.applyState (stinespringPullbackPureVector Phi psi hrange).state =
      psi.state.marginalA := by
  rw [← stinespringPureVector_state_marginalA,
    stinespringPureVector_state_pullback]

open Classical in
/-- The pullback of a pure decomposition of the dilation state: every
positive-weight branch pulls back through the isometry adjoint to an input pure
vector; zero-weight branches are replaced by an inert placeholder. -/
def stinespringPullback (Phi : Channel a b) (tau : State a)
    (D : PureDecomposition (Prod b (Prod a b)))
    (hD : D.averageState = dilationState Phi tau) :
    PureDecomposition a where
  card := D.card
  probs := D.probs
  weights_sum := D.weights_sum
  vectors := fun i =>
    if hpos : (D.probs i : ℝ) > 0 then
      stinespringPullbackPureVector Phi (D.vectors i)
        (stinespringProjection_mulVec_of_pos_weight Phi tau D hD i hpos)
    else
      basisPureVector (Classical.choice (State.nonempty tau))

/-- The pullback of a decomposition of the dilation state decomposes the input
state. -/
theorem stinespringPullback_averageState (Phi : Channel a b) (tau : State a)
    (D : PureDecomposition (Prod b (Prod a b)))
    (hD : D.averageState = dilationState Phi tau) :
    (stinespringPullback Phi tau D hD).averageState = tau := by
  apply State.ext
  have hV := Phi.stinespringIsometry.isometry
  have hbranch : ∀ i : Fin D.card,
      ((((D.probs i : ℝ≥0) : ℝ) : ℂ) •
          ((stinespringPullback Phi tau D hD).vectors i).state.matrix) =
        Matrix.conjTranspose Phi.stinespringIsometry.matrix *
          ((((D.probs i : ℝ≥0) : ℝ) : ℂ) •
            rankOneMatrix (D.vectors i).amp) *
          Phi.stinespringIsometry.matrix := by
    intro i
    by_cases hpos : (D.probs i : ℝ) > 0
    · have hvec : (stinespringPullback Phi tau D hD).vectors i =
          stinespringPullbackPureVector Phi (D.vectors i)
            (stinespringProjection_mulVec_of_pos_weight Phi tau D hD i hpos) :=
        dif_pos hpos
      have hrank : (stinespringPullbackPureVector Phi (D.vectors i)
          (stinespringProjection_mulVec_of_pos_weight Phi tau D hD i hpos)).state.matrix =
          Matrix.conjTranspose Phi.stinespringIsometry.matrix *
            rankOneMatrix (D.vectors i).amp *
            Phi.stinespringIsometry.matrix := by
        rw [PureVector.state_matrix, stinespringPullbackPureVector_amp,
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
        ((stinespringPullback Phi tau D hD).vectors i).state.matrix)) =
    tau.matrix
  rw [Finset.sum_congr rfl (fun i _ => hbranch i)]
  have hsum : (∑ i : Fin D.card,
      ((((D.probs i : ℝ≥0) : ℝ) : ℂ) • rankOneMatrix (D.vectors i).amp)) =
      D.averageState.matrix := by
    rw [PureDecomposition.averageState, Ensemble.averageState_matrix]
    rfl
  calc (∑ i : Fin D.card,
        Matrix.conjTranspose Phi.stinespringIsometry.matrix *
          ((((D.probs i : ℝ≥0) : ℝ) : ℂ) • rankOneMatrix (D.vectors i).amp) *
          Phi.stinespringIsometry.matrix) =
      (∑ i : Fin D.card,
        Matrix.conjTranspose Phi.stinespringIsometry.matrix *
          ((((D.probs i : ℝ≥0) : ℝ) : ℂ) • rankOneMatrix (D.vectors i).amp)) *
        Phi.stinespringIsometry.matrix :=
    (Matrix.sum_mul Finset.univ _ _).symm
    _ = Matrix.conjTranspose Phi.stinespringIsometry.matrix *
        (∑ i : Fin D.card,
          ((((D.probs i : ℝ≥0) : ℝ) : ℂ) • rankOneMatrix (D.vectors i).amp)) *
        Phi.stinespringIsometry.matrix := by
          rw [Matrix.mul_sum]
    _ = tau.matrix := by
          rw [hsum, hD, dilationState_matrix]
          calc Matrix.conjTranspose Phi.stinespringIsometry.matrix *
                (Phi.stinespringIsometry.matrix * tau.matrix *
                  Matrix.conjTranspose Phi.stinespringIsometry.matrix) *
                Phi.stinespringIsometry.matrix =
              (Matrix.conjTranspose Phi.stinespringIsometry.matrix *
                  Phi.stinespringIsometry.matrix) * tau.matrix *
                (Matrix.conjTranspose Phi.stinespringIsometry.matrix *
                  Phi.stinespringIsometry.matrix) := by
                simp only [← Matrix.mul_assoc]
            _ = ((1 : CMatrix a) * tau.matrix) * 1 := by rw [hV]
            _ = tau.matrix := by rw [one_mul, mul_one]

/-- The output cost of the pullback decomposition equals the entanglement cost
of the original decomposition of the dilation state. -/
theorem stinespringPullback_outputCost (Phi : Channel a b) (tau : State a)
    (D : PureDecomposition (Prod b (Prod a b)))
    (hD : D.averageState = dilationState Phi tau) :
    (stinespringPullback Phi tau D hD).outputCost Phi = D.entanglementCost := by
  unfold PureDecomposition.outputCost PureDecomposition.entanglementCost
    outputEntropyCost
  apply Finset.sum_congr rfl
  intro i _
  show ((D.probs i).toReal *
      (Phi.applyState
        ((stinespringPullback Phi tau D hD).vectors i).state).vonNeumann) =
    ((D.probs i).toReal *
      ((D.vectors i).state.marginalA).vonNeumann)
  by_cases hpos : (D.probs i : ℝ) > 0
  · have hvec : (stinespringPullback Phi tau D hD).vectors i =
        stinespringPullbackPureVector Phi (D.vectors i)
          (stinespringProjection_mulVec_of_pos_weight Phi tau D hD i hpos) :=
      dif_pos hpos
    rw [hvec, applyState_stinespringPullbackPureVector]
  · have hp0 : (D.probs i : ℝ≥0) = 0 :=
      le_antisymm (le_of_not_gt hpos) (NNReal.coe_nonneg _)
    rw [hp0]
    simp

/-- The output-entropy convex roof is bounded by the entanglement of formation
of the dilation state: every pure decomposition of the dilation state pulls back
to a decomposition of the input of the same cost. -/
theorem outputEntropyRoof_le_entanglementOfFormation
    (Phi : Channel a b) (tau : State a) :
    outputEntropyRoof Phi tau ≤
      entanglementOfFormation (dilationState Phi tau) := by
  apply le_csInf (pureEntanglementValues_nonempty (dilationState Phi tau))
  intro x hx
  rcases hx with ⟨D, hD, rfl⟩
  have hle := outputEntropyRoof_le_outputCost Phi
    (stinespringPullback Phi tau D hD)
  rw [stinespringPullback_averageState Phi tau D hD] at hle
  rwa [stinespringPullback_outputCost Phi tau D hD] at hle

/-- **The MSW identity**: the output-entropy convex roof of a channel at an
input state equals the entanglement of formation of the Stinespring dilation
state across the output-environment bipartition (manuscript equation (msw)). -/
theorem outputEntropyRoof_eq_entanglementOfFormation
    (Phi : Channel a b) (tau : State a) :
    outputEntropyRoof Phi tau =
      entanglementOfFormation (dilationState Phi tau) :=
  (outputEntropyRoof_le_entanglementOfFormation Phi tau).antisymm
    (entanglementOfFormation_dilationState_le_outputEntropyRoof Phi tau)

end

end AmplitudeDamping
