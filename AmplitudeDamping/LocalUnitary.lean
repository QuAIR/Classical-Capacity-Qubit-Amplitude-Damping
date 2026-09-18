import AmplitudeDamping.EntanglementSSA
import QIT.Nonlocality.TwoQubit

/-!
# The local-unitary reduction for Theorem 6

Manuscript §5, Theorem 6, in full: if the two-qubit marginal `ρ_AB` of a
state `Ω` on `AA' ⊗ BB'` has a nonzero *product* vector in its kernel, then

`E_F(ρ_AB) + E_F(σ_A'B') ≤ E_F(Ω)`,

where `ρ_AB` and `σ_A'B'` are the two marginals of the reassociated state.
The paper's proof begins with local unitaries that rotate the product kernel
vector to `|01⟩`, reducing to the gauge-fixed form proved in
`EntanglementSSA.lean`.  This module supplies that reduction.

Three groups of ingredients:

* local-isometry invariance of `E_F` (`entanglementOfFormation_applyState`),
  proved by transporting pure decompositions through the isometry, using the
  repository's rectangular isometry invariance of the spectral entropy
  (`psdEntropy_isometry_conj`) branchwise;
* explicit gauge unitaries on the qubit: `qubitGaugeUnitary u` sends a
  nonzero amplitude vector `u` to `‖u‖ • |0⟩`, and composition with the
  qubit swap produces a unitary sending `v` to `‖v‖ • |1⟩`;
* the assembly: conjugating `Ω` by the gauge unitaries (tensored with the
  identities on `A'`, `B'`) rotates the product kernel vector `u ⊗ v` to a
  multiple of `|01⟩`, the gauge-fixed theorem applies to the conjugated
  state, and isometry invariance transports all three `E_F` terms back.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix
  NNReal Kronecker

namespace AmplitudeDamping

open QIT QIT.TwoQubit

universe u v w₁ w₂ w₃ w₄

noncomputable section

/-! ### Partial trace versus conjugation by Kronecker products -/

/-- Orthonormality of the columns of an isometry, as a Kronecker delta. -/
theorem columnDelta {b : Type w₁} {b2 : Type w₂} [Fintype b] [DecidableEq b]
    [Fintype b2] [DecidableEq b2]
    (B : Matrix b2 b ℂ) (hB : B.conjTranspose * B = 1) (p q : b) :
    (∑ z : b2, B z p * star (B z q)) = (if q = p then 1 else 0) := by
  have h := congrFun (congrFun hB q) p
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.one_apply] at h
  rw [← h]
  exact Finset.sum_congr rfl fun z _ => mul_comm _ _

/-- Conjugating both factors by isometries: `Tr_B[(A ⊗ B) X (A ⊗ B)ᴴ] =
A Tr_B[X] Aᴴ` for isometries `A`, `B`. -/
theorem partialTraceB_conj_kronecker
    {a : Type w₁} {a2 : Type w₂} {b : Type w₃} {b2 : Type w₄}
    [Fintype a] [DecidableEq a] [Fintype a2] [DecidableEq a2]
    [Fintype b] [DecidableEq b] [Fintype b2] [DecidableEq b2]
    (A : Matrix a2 a ℂ) (_hA : A.conjTranspose * A = 1)
    (B : Matrix b2 b ℂ) (hB : B.conjTranspose * B = 1)
    (X : Matrix (a × b) (a × b) ℂ) :
    partialTraceB ((A ⊗ₖ B) * X * (A ⊗ₖ B).conjTranspose) =
      A * partialTraceB X * A.conjTranspose := by
  ext x y
  have hL : partialTraceB ((A ⊗ₖ B) * X * (A ⊗ₖ B).conjTranspose) x y =
      ∑ z : b2, ∑ q1 : a, ∑ q2 : b,
        (∑ p1 : a, ∑ p2 : b, A x p1 * B z p2 * X (p1, p2) (q1, q2)) *
          star (A y q1 * B z q2) := by
    simp only [partialTraceB, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Fintype.sum_prod_type]
  have hR : (A * partialTraceB X * A.conjTranspose) x y =
      ∑ q1 : a, ∑ p1 : a, ∑ p2 : b,
        A x p1 * X (p1, p2) (q1, p2) * star (A y q1) := by
    simp only [Matrix.mul_apply, Matrix.conjTranspose_apply, partialTraceB,
      Finset.mul_sum, Finset.sum_mul]
  rw [hL, hR]
  -- The `z`-sum and the `q2`-sum collapse by orthonormality of `B`.
  have key : ∀ q1 : a,
      (∑ z : b2, ∑ q2 : b,
        (∑ p1 : a, ∑ p2 : b, A x p1 * B z p2 * X (p1, p2) (q1, q2)) *
          star (A y q1 * B z q2)) =
      (∑ p1 : a, ∑ p2 : b, A x p1 * X (p1, p2) (q1, p2) * star (A y q1)) := by
    intro q1
    -- Distribute the inner sums over the product.
    calc (∑ z : b2, ∑ q2 : b,
          (∑ p1 : a, ∑ p2 : b, A x p1 * B z p2 * X (p1, p2) (q1, q2)) *
            star (A y q1 * B z q2))
        = ∑ z : b2, ∑ q2 : b, ∑ p1 : a, ∑ p2 : b,
            (A x p1 * B z p2 * X (p1, p2) (q1, q2)) * star (A y q1 * B z q2) := by
          refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun q2 _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun p1 _ => by rw [Finset.sum_mul]
      _ = ∑ z : b2, ∑ p1 : a, ∑ q2 : b, ∑ p2 : b,
            (A x p1 * B z p2 * X (p1, p2) (q1, q2)) * star (A y q1 * B z q2) := by
          refine Finset.sum_congr rfl fun z _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ z : b2, ∑ p1 : a, ∑ p2 : b, ∑ q2 : b,
            (A x p1 * B z p2 * X (p1, p2) (q1, q2)) * star (A y q1 * B z q2) := by
          refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun p1 _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ p1 : a, ∑ z : b2, ∑ p2 : b, ∑ q2 : b,
            (A x p1 * B z p2 * X (p1, p2) (q1, q2)) * star (A y q1 * B z q2) := by
          rw [Finset.sum_comm]
      _ = ∑ p1 : a, ∑ p2 : b, ∑ z : b2, ∑ q2 : b,
            (A x p1 * B z p2 * X (p1, p2) (q1, q2)) * star (A y q1 * B z q2) := by
          refine Finset.sum_congr rfl fun p1 _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ p1 : a, ∑ p2 : b, A x p1 * X (p1, p2) (q1, p2) * star (A y q1) := by
          refine Finset.sum_congr rfl fun p1 _ => Finset.sum_congr rfl fun p2 _ => ?_
          have hleaf : ∀ z : b2, ∀ q2 : b,
              (A x p1 * B z p2 * X (p1, p2) (q1, q2)) * star (A y q1 * B z q2) =
              (A x p1 * X (p1, p2) (q1, q2) * star (A y q1)) *
                (B z p2 * star (B z q2)) := by
            intro z q2
            rw [star_mul]
            ring
          calc (∑ z : b2, ∑ q2 : b,
                (A x p1 * B z p2 * X (p1, p2) (q1, q2)) * star (A y q1 * B z q2))
              = ∑ z : b2, ∑ q2 : b,
                  (A x p1 * X (p1, p2) (q1, q2) * star (A y q1)) *
                    (B z p2 * star (B z q2)) :=
                  Finset.sum_congr rfl fun z _ =>
                    Finset.sum_congr rfl fun q2 _ => hleaf z q2
            _ = ∑ q2 : b, ∑ z : b2,
                  (A x p1 * X (p1, p2) (q1, q2) * star (A y q1)) *
                    (B z p2 * star (B z q2)) :=
                  Finset.sum_comm
            _ = ∑ q2 : b,
                  (A x p1 * X (p1, p2) (q1, q2) * star (A y q1)) *
                    (∑ z : b2, B z p2 * star (B z q2)) := by
                  refine Finset.sum_congr rfl fun q2 _ => ?_
                  rw [← Finset.mul_sum]
            _ = ∑ q2 : b,
                  (if q2 = p2 then A x p1 * X (p1, p2) (q1, q2) * star (A y q1)
                    else 0) := by
                  refine Finset.sum_congr rfl fun q2 _ => ?_
                  rw [columnDelta B hB p2 q2, mul_ite, mul_one, mul_zero]
            _ = A x p1 * X (p1, p2) (q1, p2) * star (A y q1) := by
                  rw [Finset.sum_ite_eq', if_pos (Finset.mem_univ p2)]
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q1 _ => key q1

/-- Conjugation commutes with `0`-`1` indicator factors. -/
theorem star_mul_ite_one (a : ℂ) (c : Prop) [Decidable c] :
    star (a * (if c then 1 else 0)) = star a * (if c then 1 else 0) := by
  by_cases hc : c <;> simp [hc]

/-- Conjugating only the first factor by an isometry does not change the
second partial trace: `Tr_B[(K ⊗ 1) X (K ⊗ 1)ᴴ] = Tr_B[X]` for an isometry
`K`. -/
theorem partialTraceA_conj_kronecker_left
    {a : Type w₁} {a2 : Type w₂} {b : Type w₃}
    [Fintype a] [DecidableEq a] [Fintype a2] [DecidableEq a2]
    [Fintype b] [DecidableEq b]
    (K : Matrix a2 a ℂ) (hK : K.conjTranspose * K = 1)
    (X : Matrix (a × b) (a × b) ℂ) :
    partialTraceA ((K ⊗ₖ (1 : Matrix b b ℂ)) * X *
        (K ⊗ₖ (1 : Matrix b b ℂ)).conjTranspose) = partialTraceA X := by
  ext z z'
  have hL : partialTraceA ((K ⊗ₖ (1 : Matrix b b ℂ)) * X *
      (K ⊗ₖ (1 : Matrix b b ℂ)).conjTranspose) z z' =
      ∑ i : a2, ∑ q1 : a, ∑ j' : b,
        (∑ p1 : a, ∑ j : b,
            K i p1 * (if z = j then 1 else 0) * X (p1, j) (q1, j')) *
          star (K i q1 * (if z' = j' then 1 else 0)) := by
    simp only [partialTraceA, Matrix.mul_apply, Matrix.conjTranspose_apply,
      Matrix.kroneckerMap_apply, Matrix.one_apply, Fintype.sum_prod_type]
  have hR : partialTraceA X z z' = ∑ q1 : a, X (q1, z) (q1, z') := by
    simp only [partialTraceA]
  rw [hL, hR]
  -- The `j`-, `j'`-, and `i`-sums collapse to Kronecker deltas.
  have key : ∀ q1 : a,
      (∑ i : a2, ∑ j' : b,
        (∑ p1 : a, ∑ j : b,
            K i p1 * (if z = j then 1 else 0) * X (p1, j) (q1, j')) *
          star (K i q1 * (if z' = j' then 1 else 0))) =
      X (q1, z) (q1, z') := by
    intro q1
    -- Distribute the inner sums over the product.
    calc (∑ i : a2, ∑ j' : b,
          (∑ p1 : a, ∑ j : b,
              K i p1 * (if z = j then 1 else 0) * X (p1, j) (q1, j')) *
            star (K i q1 * (if z' = j' then 1 else 0)))
        = ∑ i : a2, ∑ j' : b, ∑ p1 : a, ∑ j : b,
            (K i p1 * (if z = j then 1 else 0) * X (p1, j) (q1, j')) *
              star (K i q1 * (if z' = j' then 1 else 0)) := by
          refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j' _ => ?_
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun p1 _ => by rw [Finset.sum_mul]
      _ = ∑ i : a2, ∑ p1 : a, ∑ j' : b, ∑ j : b,
            (K i p1 * (if z = j then 1 else 0) * X (p1, j) (q1, j')) *
              star (K i q1 * (if z' = j' then 1 else 0)) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ p1 : a, ∑ i : a2, ∑ j' : b, ∑ j : b,
            (K i p1 * (if z = j then 1 else 0) * X (p1, j) (q1, j')) *
              star (K i q1 * (if z' = j' then 1 else 0)) := by
          rw [Finset.sum_comm]
      _ = ∑ p1 : a, ∑ i : a2, ∑ j : b, ∑ j' : b,
            (K i p1 * (if z = j then 1 else 0) * X (p1, j) (q1, j')) *
              star (K i q1 * (if z' = j' then 1 else 0)) := by
          refine Finset.sum_congr rfl fun p1 _ => Finset.sum_congr rfl fun i _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ p1 : a, ∑ j : b, ∑ i : a2, ∑ j' : b,
            (K i p1 * (if z = j then 1 else 0) * X (p1, j) (q1, j')) *
              star (K i q1 * (if z' = j' then 1 else 0)) := by
          refine Finset.sum_congr rfl fun p1 _ => ?_
          rw [Finset.sum_comm]
      _ = ∑ p1 : a, ∑ j : b, ∑ j' : b, ∑ i : a2,
            (K i p1 * (if z = j then 1 else 0) * X (p1, j) (q1, j')) *
              star (K i q1 * (if z' = j' then 1 else 0)) := by
          refine Finset.sum_congr rfl fun p1 _ =>
            Finset.sum_congr rfl fun j _ => ?_
          rw [Finset.sum_comm]
      _ = X (q1, z) (q1, z') := by
          -- Collapse the `j'`-sum, then the `i`-sum, then the `j`- and `p1`-sums.
          calc (∑ p1 : a, ∑ j : b, ∑ j' : b, ∑ i : a2,
                (K i p1 * (if z = j then 1 else 0) * X (p1, j) (q1, j')) *
                  star (K i q1 * (if z' = j' then 1 else 0)))
              = ∑ p1 : a, ∑ j : b, ∑ j' : b, ∑ i : a2,
                  ((K i p1 * (if z = j then 1 else 0)) * star (K i q1)) *
                    (X (p1, j) (q1, j') * (if z' = j' then 1 else 0)) := by
                refine Finset.sum_congr rfl fun p1 _ =>
                  Finset.sum_congr rfl fun j _ =>
                  Finset.sum_congr rfl fun j' _ =>
                  Finset.sum_congr rfl fun i _ => ?_
                rw [star_mul_ite_one]
                ring
            _ = ∑ p1 : a, ∑ j : b, ∑ i : a2,
                  ((K i p1 * (if z = j then 1 else 0)) * star (K i q1)) *
                    X (p1, j) (q1, z') := by
                refine Finset.sum_congr rfl fun p1 _ =>
                  Finset.sum_congr rfl fun j _ => ?_
                rw [Finset.sum_comm]
                refine Finset.sum_congr rfl fun i _ => ?_
                rw [← Finset.mul_sum]
                simp only [mul_ite, mul_one, mul_zero]
                rw [Finset.sum_ite_eq, if_pos (Finset.mem_univ z')]
            _ = ∑ p1 : a, ∑ j : b,
                  (if z = j then 1 else 0) * X (p1, j) (q1, z') *
                    (if q1 = p1 then 1 else 0) := by
                refine Finset.sum_congr rfl fun p1 _ =>
                  Finset.sum_congr rfl fun j _ => ?_
                calc (∑ i : a2,
                      ((K i p1 * (if z = j then 1 else 0)) * star (K i q1)) *
                        X (p1, j) (q1, z'))
                    = ∑ i : a2, X (p1, j) (q1, z') *
                        ((if z = j then 1 else 0) *
                          (K i p1 * star (K i q1))) :=
                      Finset.sum_congr rfl fun i _ => by ring
                  _ = X (p1, j) (q1, z') * ((if z = j then 1 else 0) *
                        (∑ i : a2, K i p1 * star (K i q1))) := by
                      rw [← Finset.mul_sum, ← Finset.mul_sum]
                  _ = X (p1, j) (q1, z') * ((if z = j then 1 else 0) *
                        (if q1 = p1 then 1 else 0)) := by
                      rw [columnDelta K hK p1 q1]
                  _ = (if z = j then 1 else 0) * X (p1, j) (q1, z') *
                        (if q1 = p1 then 1 else 0) := by ring
            _ = X (q1, z) (q1, z') := by
                have hre : ∀ p1 : a, ∀ j : b,
                    (if z = j then 1 else 0) * X (p1, j) (q1, z') *
                      (if q1 = p1 then 1 else 0) =
                    (if q1 = p1 then 1 else 0) *
                      ((if z = j then 1 else 0) * X (p1, j) (q1, z')) :=
                  fun p1 j => by ring
                calc (∑ p1 : a, ∑ j : b,
                      (if z = j then 1 else 0) * X (p1, j) (q1, z') *
                        (if q1 = p1 then 1 else 0))
                    = ∑ p1 : a, ∑ j : b,
                        (if q1 = p1 then 1 else 0) *
                          ((if z = j then 1 else 0) * X (p1, j) (q1, z')) := by
                      refine Finset.sum_congr rfl fun p1 _ =>
                        Finset.sum_congr rfl fun j _ => ?_
                      exact hre p1 j
                  _ = ∑ p1 : a, (if q1 = p1 then 1 else 0) *
                      (∑ j : b, (if z = j then 1 else 0) * X (p1, j) (q1, z')) := by
                      refine Finset.sum_congr rfl fun p1 _ => ?_
                      rw [← Finset.mul_sum]
                  _ = X (q1, z) (q1, z') := by
                      have hj : ∀ p1 : a,
                          (∑ j : b, (if z = j then 1 else 0) *
                            X (p1, j) (q1, z')) = X (p1, z) (q1, z') := by
                        intro p1
                        rw [Finset.sum_eq_single z]
                        · rw [if_pos rfl, one_mul]
                        · intro j _ hjz
                          rw [if_neg (fun h => hjz h.symm), zero_mul]
                        · intro h
                          exact absurd (Finset.mem_univ z) h
                      simp only [hj]
                      rw [Finset.sum_eq_single q1]
                      · rw [if_pos rfl, one_mul]
                      · intro p1 _ hp
                        rw [if_neg (fun h => hp h.symm), zero_mul]
                      · intro h
                        exact absurd (Finset.mem_univ q1) h
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun q1 _ => key q1

/-! ### Pure states under isometry conjugation -/

/-- Traces through an isometry: `Tr[M B Mᴴ] = Tr[B]` when `Mᴴ M = 1`. -/
theorem trace_mul_conjTranspose_mul_of_isometry {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n] (M : Matrix m n ℂ)
    (hM : M.conjTranspose * M = 1) (B : Matrix n n ℂ) :
    (M * B * M.conjTranspose).trace = B.trace := by
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, hM, Matrix.one_mul]

/-- The image of a pure vector under an isometry matrix. -/
def isometryVector {m : Type w₁} {n : Type w₂} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) (hM : M.conjTranspose * M = 1)
    (ψ : PureVector n) : PureVector m where
  amp := M *ᵥ ψ.amp
  trace_rankOne_eq_one := by
    have h1 : (rankOneMatrix (M *ᵥ ψ.amp)).trace =
        (M * rankOneMatrix ψ.amp * M.conjTranspose).trace := by
      rw [rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
    rw [h1, trace_mul_conjTranspose_mul_of_isometry M hM _, ψ.trace_rankOne_eq_one]

theorem isometryVector_amp {m : Type w₁} {n : Type w₂} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) (hM : M.conjTranspose * M = 1)
    (ψ : PureVector n) : (isometryVector M hM ψ).amp = M *ᵥ ψ.amp :=
  rfl

/-- The state matrix of an isometric image is the conjugated rank-one
projector. -/
theorem isometryVector_state_matrix {m : Type w₁} {n : Type w₂} [Fintype m]
    [DecidableEq m] [Fintype n] [DecidableEq n] (M : Matrix m n ℂ) (hM : M.conjTranspose * M = 1)
    (ψ : PureVector n) :
    (isometryVector M hM ψ).state.matrix = M * rankOneMatrix ψ.amp * M.conjTranspose := by
  rw [PureVector.state_matrix, isometryVector_amp,
    rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]


/-- The adjoint identity for matrix--vector products in dot-product form:
`⟨u, M v⟩ = ⟨Mᴴ u, v⟩`. -/
theorem star_dotProduct_conjTranspose_mulVec
    {m : Type w₁} {n : Type w₂} [Fintype n] [DecidableEq n]
    [Fintype m] [DecidableEq m] (M : Matrix m n ℂ) (u : n → ℂ) (v : m → ℂ) :
    star u ⬝ᵥ (M.conjTranspose *ᵥ v) = star (M *ᵥ u) ⬝ᵥ v := by
  have hmv : ∀ w : m, star ((M *ᵥ u) w) = ∑ z : n, star (M w z) * star (u z) := by
    intro w
    show star (∑ z : n, M w z * u z) = _
    rw [star_sum]
    exact Finset.sum_congr rfl fun z _ => by rw [star_mul]; ring
  have hL : star u ⬝ᵥ (M.conjTranspose *ᵥ v) =
      ∑ z : n, ∑ w : m, star (u z) * (star (M w z) * v w) := by
    have h1 : star u ⬝ᵥ (M.conjTranspose *ᵥ v) =
        ∑ z : n, star (u z) * ((M.conjTranspose *ᵥ v) z) := rfl
    have h2 : ∀ z : n, star (u z) * ((M.conjTranspose *ᵥ v) z) =
        ∑ w : m, star (u z) * (star (M w z) * v w) := by
      intro z
      have h3 : (M.conjTranspose *ᵥ v) z = ∑ w : m, star (M w z) * v w := by
        simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply]
      rw [h3, Finset.mul_sum]
    rw [h1, Finset.sum_congr rfl fun z _ => h2 z]
  have hR : star (M *ᵥ u) ⬝ᵥ v =
      ∑ w : m, ∑ z : n, (star (M w z) * star (u z)) * v w := by
    have h1 : star (M *ᵥ u) ⬝ᵥ v = ∑ w : m, star ((M *ᵥ u) w) * v w := rfl
    have h2 : ∀ w : m, star ((M *ᵥ u) w) * v w =
        ∑ z : n, (star (M w z) * star (u z)) * v w := by
      intro w
      rw [hmv w, Finset.sum_mul]
    rw [h1, Finset.sum_congr rfl fun w _ => h2 w]
  rw [hL, hR, Finset.sum_comm]
  exact Finset.sum_congr rfl fun w _ =>
    Finset.sum_congr rfl fun z _ => by ring

/-- The average state of a pure decomposition, as a scalar-weighted sum of
rank-one projectors. -/
theorem pureDecomposition_averageState_matrix_sum
    {d : Type w₃} [Fintype d] [DecidableEq d]
    (E : PureDecomposition d) :
    E.averageState.matrix =
      ∑ i : Fin E.card,
        ((E.probs i : ℝ≥0) : ℂ) • rankOneMatrix (E.vectors i).amp := by
  ext x y
  rw [pureDecomposition_averageState_entry]
  simp only [Matrix.sum_apply, Matrix.smul_apply, PureVector.state_matrix,
    smul_eq_mul]

/-- Conjugation of a scalar-weighted sum of matrices distributes over the
sum. -/
theorem mul_sum_smul_conj {m : Type w₁} {n : Type w₂} {ι : Type w₃}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype ι] [DecidableEq ι]
    (W : Matrix m n ℂ) (p : ι → ℂ) (R : ι → Matrix n n ℂ) :
    W * (∑ i, p i • R i) * W.conjTranspose =
      ∑ i, p i • (W * R i * W.conjTranspose) := by
  calc W * (∑ i, p i • R i) * W.conjTranspose
      = ∑ i, W * (p i • R i) * W.conjTranspose := by
        rw [Matrix.mul_sum, Matrix.sum_mul]
    _ = ∑ i, p i • (W * R i * W.conjTranspose) :=
        Finset.sum_congr rfl fun i _ => by
          rw [Matrix.mul_smul, Matrix.smul_mul]


/-! ### Local-isometry invariance of the entanglement of formation (Step 1) -/

section LocalIsometryInv

variable {a : Type u} {a2 : Type v} {c : Type w₁} {c2 : Type w₂}
variable [Fintype a] [DecidableEq a] [Fintype a2] [DecidableEq a2]
variable [Fintype c] [DecidableEq c] [Fintype c2] [DecidableEq c2]

/-- Applying a local isometry to a pure state gives the state of the image
vector. -/
theorem localIsometry_applyState_pure (V : TwoQubit.LocalIsometry a a2 c c2)
    (ψ : PureVector (a × c)) :
    V.applyState ψ.state = (isometryVector V.matrix V.matrix_isometry ψ).state := by
  apply State.ext
  simp only [LocalIsometry.applyState_matrix, LocalIsometry.applyMatrix,
    PureVector.state_matrix, isometryVector_amp,
    rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]

/-- The first marginal of a conjugated state is the conjugated first
marginal (only Alice's factor acts). -/
theorem localIsometry_applyState_marginalA_matrix
    (V : TwoQubit.LocalIsometry a a2 c c2) (ρ : State (a × c)) :
    (V.applyState ρ).marginalA.matrix =
      V.alice.matrix * ρ.marginalA.matrix * V.alice.matrix.conjTranspose := by
  rw [State.marginalA_matrix, State.marginalA_matrix,
    LocalIsometry.applyState_matrix, LocalIsometry.applyMatrix,
    show V.matrix = V.alice.matrix ⊗ₖ V.bob.matrix from rfl]
  exact partialTraceB_conj_kronecker V.alice.matrix V.alice.isometry V.bob.matrix
    V.bob.isometry ρ.matrix

/-- The marginal entropy of an isometric image of a pure state equals the
marginal entropy of the pure state. -/
theorem isometryVector_marginalA_vonNeumann (V : TwoQubit.LocalIsometry a a2 c c2)
    (ψ : PureVector (a × c)) :
    ((isometryVector V.matrix V.matrix_isometry ψ).state.marginalA).vonNeumann =
      (ψ.state.marginalA).vonNeumann := by
  have hmat : ((isometryVector V.matrix V.matrix_isometry ψ).state.marginalA).matrix =
      V.alice.matrix * (ψ.state.marginalA).matrix * V.alice.matrix.conjTranspose := by
    rw [State.marginalA_matrix, isometryVector_state_matrix,
      show V.matrix = V.alice.matrix ⊗ₖ V.bob.matrix from rfl,
      show (ψ.state.marginalA).matrix = partialTraceB (rankOneMatrix ψ.amp) from by
        rw [State.marginalA_matrix, PureVector.state_matrix]]
    exact partialTraceB_conj_kronecker V.alice.matrix V.alice.isometry V.bob.matrix
      V.bob.isometry (rankOneMatrix ψ.amp)
  calc ((isometryVector V.matrix V.matrix_isometry ψ).state.marginalA).vonNeumann
      = psdEntropy (((isometryVector V.matrix V.matrix_isometry ψ).state.marginalA).matrix)
          ((isometryVector V.matrix V.matrix_isometry ψ).state.marginalA).pos :=
        (psdEntropy_state _).symm
    _ = psdEntropy (V.alice.matrix * (ψ.state.marginalA).matrix *
          V.alice.matrix.conjTranspose)
          ((ψ.state.marginalA).pos.mul_mul_conjTranspose_same V.alice.matrix) :=
        psdEntropy_congr hmat _ _
    _ = psdEntropy ((ψ.state.marginalA).matrix) (ψ.state.marginalA).pos :=
        psdEntropy_isometry_conj _ _ V.alice.matrix V.alice.isometry
    _ = (ψ.state.marginalA).vonNeumann := psdEntropy_state _

/-- The pushforward of a pure decomposition along a local isometry. -/
def PureDecomposition.mapIsometry (V : TwoQubit.LocalIsometry a a2 c c2)
    (E : PureDecomposition (a × c)) : PureDecomposition (a2 × c2) where
  card := E.card
  probs := E.probs
  weights_sum := E.weights_sum
  vectors i := isometryVector V.matrix V.matrix_isometry (E.vectors i)

/-- The average state of the pushforward decomposition is the image of the
average state. -/
theorem mapIsometry_averageState (V : TwoQubit.LocalIsometry a a2 c c2)
    (E : PureDecomposition (a × c)) :
    (E.mapIsometry V).averageState = V.applyState E.averageState := by
  apply State.ext
  have hpush : (E.mapIsometry V).averageState.matrix =
      ∑ i : Fin E.card, ((E.probs i : ℝ≥0) : ℂ) •
        (V.matrix * rankOneMatrix (E.vectors i).amp * V.matrix.conjTranspose) := by
    rw [pureDecomposition_averageState_matrix_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : ((E.mapIsometry V).vectors i).amp = V.matrix *ᵥ (E.vectors i).amp := rfl
    have h2 : ((E.mapIsometry V).probs i) = E.probs i := rfl
    rw [h1, h2, rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  rw [hpush, ← mul_sum_smul_conj, ← pureDecomposition_averageState_matrix_sum,
    LocalIsometry.applyState_matrix, LocalIsometry.applyMatrix]

/-- The pushforward decomposition has the same entanglement cost. -/
theorem mapIsometry_entanglementCost (V : TwoQubit.LocalIsometry a a2 c c2)
    (E : PureDecomposition (a × c)) :
    (E.mapIsometry V).entanglementCost = E.entanglementCost := by
  rw [PureDecomposition.entanglementCost, PureDecomposition.entanglementCost]
  refine Finset.sum_congr rfl fun i _ => ?_
  exact congrArg _ (isometryVector_marginalA_vonNeumann V (E.vectors i))

/-- First direction of local-isometry invariance: `E_F` cannot increase
under a local isometry. -/
theorem entanglementOfFormation_applyState_le (V : TwoQubit.LocalIsometry a a2 c c2)
    (ρ : State (a × c)) :
    entanglementOfFormation (V.applyState ρ) ≤ entanglementOfFormation ρ := by
  apply le_csInf (pureEntanglementValues_nonempty ρ)
  intro x hx
  rcases hx with ⟨E, hEavg, rfl⟩
  have hle := entanglementOfFormation_le_entanglementCost (E.mapIsometry V)
  rw [mapIsometry_averageState, mapIsometry_entanglementCost] at hle
  rw [← hEavg]
  exact hle

end LocalIsometryInv


/-! ### The range projection of an isometry (Step 1, reverse direction) -/

/-- The range projection `W Wᴴ` of an isometry is idempotent. -/
theorem mul_conjTranspose_mul_idempotent {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : W.conjTranspose * W = 1) :
    W * W.conjTranspose * (W * W.conjTranspose) = W * W.conjTranspose := by
  calc W * W.conjTranspose * (W * W.conjTranspose)
      = W * (W.conjTranspose * (W * W.conjTranspose)) :=
          Matrix.mul_assoc W W.conjTranspose (W * W.conjTranspose)
    _ = W * ((W.conjTranspose * W) * W.conjTranspose) := by rw [Matrix.mul_assoc]
    _ = W * W.conjTranspose := by rw [hW, Matrix.one_mul]

/-- The range projection `W Wᴴ` is Hermitian. -/
theorem mul_conjTranspose_mul_hermitian {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) :
    (W * W.conjTranspose).conjTranspose = W * W.conjTranspose := by
  rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]

/-- The complementary projection annihilates the isometry. -/
theorem one_sub_rangeProjection_mul {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : W.conjTranspose * W = 1) :
    (1 - W * W.conjTranspose) * W = 0 := by
  rw [Matrix.sub_mul, Matrix.mul_assoc, hW, Matrix.one_mul, Matrix.mul_one,
    sub_self]

/-- The complementary projection kills the range projection from the left. -/
theorem one_sub_rangeProjection_mul_range {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : W.conjTranspose * W = 1) :
    (1 - W * W.conjTranspose) * (W * W.conjTranspose) = 0 := by
  calc (1 - W * W.conjTranspose) * (W * W.conjTranspose)
      = ((1 - W * W.conjTranspose) * W) * W.conjTranspose := by
        rw [Matrix.mul_assoc]
    _ = (0 : Matrix m n ℂ) * W.conjTranspose := by
        rw [one_sub_rangeProjection_mul W hW]
    _ = 0 := Matrix.zero_mul _

/-- The complementary projection `1 - W Wᴴ` is positive semidefinite. -/
theorem one_sub_mul_conjTranspose_mul_posSemidef {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : W.conjTranspose * W = 1) :
    (1 - W * W.conjTranspose).PosSemidef := by
  have hherm : (1 - W * W.conjTranspose).conjTranspose = 1 - W * W.conjTranspose := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      mul_conjTranspose_mul_hermitian W]
  have hidem : (1 - W * W.conjTranspose) * (1 - W * W.conjTranspose)
      = 1 - W * W.conjTranspose := by
    rw [Matrix.mul_sub, Matrix.mul_one,
      one_sub_rangeProjection_mul_range W hW, sub_zero]
  have hform : 1 - W * W.conjTranspose =
      (1 - W * W.conjTranspose).conjTranspose * (1 - W * W.conjTranspose) := by
    rw [hherm, hidem]
  rw [hform]
  exact Matrix.posSemidef_conjTranspose_mul_self _

/-- A vector annihilated by the complementary projection is fixed by the
range projection. -/
theorem rangeProjection_mulVec_of_sub_eq_zero {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (f : m → ℂ)
    (h : (1 - W * W.conjTranspose) *ᵥ f = 0) :
    (W * W.conjTranspose) *ᵥ f = f := by
  rw [Matrix.sub_mulVec, Matrix.one_mulVec] at h
  exact (sub_eq_zero.mp h).symm

/-- Norms of an isometric pullback with a range condition: the pullback of a
vector in the range of `W` has the same squared norm as the vector. -/
theorem sum_normSq_conjTranspose_mulVec {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (f : m → ℂ)
    (hP : (W * W.conjTranspose) *ᵥ f = f) :
    ∑ z : n, Complex.normSq ((W.conjTranspose *ᵥ f) z) =
      ∑ z : m, Complex.normSq (f z) := by
  have hψstar : ∀ z : n,
      ((Complex.normSq ((W.conjTranspose *ᵥ f) z) : ℝ) : ℂ) =
      star ((W.conjTranspose *ᵥ f) z) * ((W.conjTranspose *ᵥ f) z) := by
    intro z
    show _ = starRingEnd ℂ ((W.conjTranspose *ᵥ f) z) * ((W.conjTranspose *ᵥ f) z)
    rw [Complex.normSq_eq_conj_mul_self]
  have hφstar : ∀ z : m,
      ((Complex.normSq (f z) : ℝ) : ℂ) = star (f z) * (f z) := by
    intro z
    show _ = starRingEnd ℂ (f z) * (f z)
    rw [Complex.normSq_eq_conj_mul_self]
  have hmain : ((∑ z : n, Complex.normSq ((W.conjTranspose *ᵥ f) z) : ℝ) : ℂ) =
      star (W.conjTranspose *ᵥ f) ⬝ᵥ (W.conjTranspose *ᵥ f) := by
    rw [Complex.ofReal_sum]
    show ∑ z : n, ((Complex.normSq ((W.conjTranspose *ᵥ f) z) : ℝ) : ℂ) =
        ∑ z : n, star ((W.conjTranspose *ᵥ f) z) * ((W.conjTranspose *ᵥ f) z)
    exact Finset.sum_congr rfl fun z _ => hψstar z
  have hmain2 : star (W.conjTranspose *ᵥ f) ⬝ᵥ (W.conjTranspose *ᵥ f) =
      star f ⬝ᵥ ((W * W.conjTranspose) *ᵥ f) := by
    have hstep := star_dotProduct_conjTranspose_mulVec W.conjTranspose f
      (W.conjTranspose *ᵥ f)
    rw [Matrix.conjTranspose_conjTranspose W] at hstep
    rw [← Matrix.mulVec_mulVec, ← hstep]
  have hfinal : star f ⬝ᵥ ((W * W.conjTranspose) *ᵥ f) =
      ((∑ z : m, Complex.normSq (f z) : ℝ) : ℂ) := by
    rw [hP, Complex.ofReal_sum]
    show ∑ z : m, star (f z) * (f z) = _
    exact Finset.sum_congr rfl fun z _ => (hφstar z).symm
  exact Complex.ofReal_injective (by rw [hmain, hmain2, hfinal])

/-- The squared norm of a pure vector's amplitude is one. -/
theorem sum_normSq_amp_eq_one {d : Type w₁} [Fintype d] [DecidableEq d]
    (φ : PureVector d) :
    ∑ z, Complex.normSq (φ.amp z) = 1 := by
  have h := congrArg Complex.re φ.trace_rankOne_eq_one
  simpa [rankOneMatrix_trace, dotProduct, Complex.mul_conj] using h

/-- The pullback of a range vector along an isometry is a pure vector. -/
theorem conjTranspose_mulVec_pure {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (φ : PureVector m)
    (hP : (W * W.conjTranspose) *ᵥ φ.amp = φ.amp) :
    (rankOneMatrix (W.conjTranspose *ᵥ φ.amp)).trace = 1 := by
  have hcast : ((∑ z : n, Complex.normSq ((W.conjTranspose *ᵥ φ.amp) z) : ℝ) : ℂ) = 1 := by
    rw [sum_normSq_conjTranspose_mulVec W φ.amp hP, sum_normSq_amp_eq_one φ,
      Complex.ofReal_one]
  have hprod : (W.conjTranspose *ᵥ φ.amp) ⬝ᵥ
      (fun i => star ((W.conjTranspose *ᵥ φ.amp) i)) =
      ((∑ z : n, Complex.normSq ((W.conjTranspose *ᵥ φ.amp) z) : ℝ) : ℂ) := by
    show ∑ z : n, (W.conjTranspose *ᵥ φ.amp) z *
      starRingEnd ℂ ((W.conjTranspose *ᵥ φ.amp) z) = _
    rw [Complex.ofReal_sum]
    exact Finset.sum_congr rfl fun z _ => Complex.mul_conj _
  rw [rankOneMatrix_trace, hprod, hcast]


/-- Collapsing a two-sided isometry conjugation onto the identity factor:
`Wᴴ (W R Wᴴ) W = R` for an isometry `W`. -/
theorem conjTranspose_mul_tripod {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : W.conjTranspose * W = 1) (R : Matrix n n ℂ) :
    W.conjTranspose * (W * R * W.conjTranspose) * W = R := by
  rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hW, Matrix.one_mul, Matrix.mul_assoc,
    hW, Matrix.mul_one]

/-- The complementary projection is idempotent. -/
theorem one_sub_rangeProjection_idempotent {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : W.conjTranspose * W = 1) :
    (1 - W * W.conjTranspose) * (1 - W * W.conjTranspose)
      = 1 - W * W.conjTranspose := by
  rw [Matrix.mul_sub, Matrix.mul_one, one_sub_rangeProjection_mul_range W hW,
    sub_zero]

/-- For a Hermitian idempotent `Q`, the `Q`-diagonal of a rank-one projector
is the total squared norm of `Q φ`. -/
theorem trace_mul_rankOne_eq_sum_normSq {d : Type w₁} [Fintype d] [DecidableEq d]
    (Q : Matrix d d ℂ) (hQh : Q.conjTranspose = Q) (hQ2 : Q * Q = Q)
    (φ : d → ℂ) :
    (Q * rankOneMatrix φ).trace =
      ((∑ z, Complex.normSq ((Q *ᵥ φ) z) : ℝ) : ℂ) := by
  have hprod : Q *ᵥ φ = (Q.conjTranspose * Q) *ᵥ φ := by rw [hQh, hQ2]
  have h1 : (Q * rankOneMatrix φ).trace =
      ∑ z : d, ∑ w : d, Q z w * φ w * star (φ z) := by
    have h2 : (Q * rankOneMatrix φ).trace =
        ∑ z : d, (Q * rankOneMatrix φ) z z := rfl
    have h3 : ∀ z : d, (Q * rankOneMatrix φ) z z =
        ∑ w : d, Q z w * φ w * star (φ z) := by
      intro z
      have h4 : (Q * rankOneMatrix φ) z z =
          ∑ w : d, Q z w * rankOneMatrix φ w z := rfl
      rw [h4]
      exact Finset.sum_congr rfl fun w _ => by rw [rankOneMatrix_apply]; ring
    rw [h2]
    exact Finset.sum_congr rfl fun z _ => h3 z
  have hstep2 : ∑ z : d, ∑ w : d, Q z w * φ w * star (φ z) =
      star φ ⬝ᵥ (Q *ᵥ φ) := by
    show ∑ z : d, ∑ w : d, Q z w * φ w * star (φ z) =
      ∑ z : d, star (φ z) * (Q *ᵥ φ) z
    refine Finset.sum_congr rfl fun z _ => ?_
    have hq : (Q *ᵥ φ) z = ∑ w : d, Q z w * φ w := rfl
    rw [hq, Finset.mul_sum]
    exact Finset.sum_congr rfl fun w _ => by ring
  calc (Q * rankOneMatrix φ).trace
      = ∑ z : d, ∑ w : d, Q z w * φ w * star (φ z) := h1
    _ = star φ ⬝ᵥ (Q *ᵥ φ) := hstep2
    _ = star φ ⬝ᵥ ((Q.conjTranspose * Q) *ᵥ φ) := by rw [hprod]
    _ = star φ ⬝ᵥ (Q.conjTranspose *ᵥ (Q *ᵥ φ)) := by rw [Matrix.mulVec_mulVec]
    _ = star (Q *ᵥ φ) ⬝ᵥ (Q *ᵥ φ) :=
          star_dotProduct_conjTranspose_mulVec Q φ (Q *ᵥ φ)
    _ = ((∑ z, Complex.normSq ((Q *ᵥ φ) z) : ℝ) : ℂ) := by
        rw [Complex.ofReal_sum]
        show ∑ z : d, star ((Q *ᵥ φ) z) * ((Q *ᵥ φ) z) = _
        exact Finset.sum_congr rfl fun z _ => by
          show starRingEnd ℂ ((Q *ᵥ φ) z) * ((Q *ᵥ φ) z) = _
          exact Complex.normSq_eq_conj_mul_self.symm

/-- The pullback of a pure vector along an isometry: the actual preimage when
the vector lies in the isometry's range, an arbitrary filler otherwise. -/
def isometryPullback {m : Type w₁} {n : Type w₂} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (_hW : W.conjTranspose * W = 1)
    (filler : PureVector n) (φ : PureVector m) : PureVector n :=
  if h : (1 - W * W.conjTranspose) *ᵥ φ.amp = 0 then
    ⟨W.conjTranspose *ᵥ φ.amp,
      conjTranspose_mulVec_pure W φ
        (rangeProjection_mulVec_of_sub_eq_zero W φ.amp h)⟩
  else filler

/-- In the range case, the pullback amplitude is the adjoint image. -/
theorem isometryPullback_amp_of_sub_eq_zero {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : W.conjTranspose * W = 1)
    (filler : PureVector n) (φ : PureVector m)
    (h : (1 - W * W.conjTranspose) *ᵥ φ.amp = 0) :
    (isometryPullback W hW filler φ).amp = W.conjTranspose *ᵥ φ.amp := by
  rw [isometryPullback, dif_pos h]

/-- In the range case, the isometry sends the pullback back to the original
vector. -/
theorem isometryPullback_range {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : W.conjTranspose * W = 1)
    (filler : PureVector n) (φ : PureVector m)
    (h : (1 - W * W.conjTranspose) *ᵥ φ.amp = 0) :
    W *ᵥ (isometryPullback W hW filler φ).amp = φ.amp := by
  rw [isometryPullback_amp_of_sub_eq_zero W hW filler φ h, Matrix.mulVec_mulVec,
    rangeProjection_mulVec_of_sub_eq_zero W φ.amp h]

/-- The branchwise pullback of a pure decomposition along an isometry; the
weights are unchanged. -/
def PureDecomposition.pullback {m : Type w₁} {n : Type w₂}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (W : Matrix m n ℂ) (hW : W.conjTranspose * W = 1)
    (filler : PureVector n) (F : PureDecomposition m) : PureDecomposition n where
  card := F.card
  probs := F.probs
  weights_sum := F.weights_sum
  vectors j := isometryPullback W hW filler (F.vectors j)


/-! ### Local-isometry invariance of `E_F`: the reverse direction -/

section LocalIsometryPullback

variable {a : Type u} {a2 : Type v} {c : Type w₁} {c2 : Type w₂}
variable [Fintype a] [DecidableEq a] [Fintype a2] [DecidableEq a2]
variable [Fintype c] [DecidableEq c] [Fintype c2] [DecidableEq c2]

/-- The first-marginal entropy of a pure state in the range of a local
isometry equals the first-marginal entropy of its pullback. -/
theorem pure_pullback_marginalA_vonNeumann (V : TwoQubit.LocalIsometry a a2 c c2)
    (filler : PureVector (a × c)) (φ : PureVector (a2 × c2))
    (h : (1 - V.matrix * V.matrix.conjTranspose) *ᵥ φ.amp = 0) :
    (φ.state.marginalA).vonNeumann =
      ((isometryPullback V.matrix V.matrix_isometry filler φ).state.marginalA).vonNeumann := by
  have hampφ : φ.amp =
      V.matrix *ᵥ (isometryPullback V.matrix V.matrix_isometry filler φ).amp :=
    (isometryPullback_range V.matrix V.matrix_isometry filler φ h).symm
  have hmat : (φ.state.marginalA).matrix =
      V.alice.matrix *
        ((isometryPullback V.matrix V.matrix_isometry filler φ).state.marginalA).matrix *
        V.alice.matrix.conjTranspose := by
    rw [State.marginalA_matrix, State.marginalA_matrix, PureVector.state_matrix,
      PureVector.state_matrix, hampφ,
      rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
    exact partialTraceB_conj_kronecker V.alice.matrix V.alice.isometry V.bob.matrix
      V.bob.isometry (rankOneMatrix (isometryPullback V.matrix V.matrix_isometry
        filler φ).amp)
  calc (φ.state.marginalA).vonNeumann
      = psdEntropy (φ.state.marginalA).matrix (φ.state.marginalA).pos :=
        (psdEntropy_state _).symm
    _ = psdEntropy (V.alice.matrix *
          ((isometryPullback V.matrix V.matrix_isometry filler φ).state.marginalA).matrix *
          V.alice.matrix.conjTranspose)
          (((isometryPullback V.matrix V.matrix_isometry filler φ).state.marginalA).pos.mul_mul_conjTranspose_same
            V.alice.matrix) :=
        psdEntropy_congr hmat _ _
    _ = psdEntropy
          ((isometryPullback V.matrix V.matrix_isometry filler φ).state.marginalA).matrix
          ((isometryPullback V.matrix V.matrix_isometry filler φ).state.marginalA).pos :=
        psdEntropy_isometry_conj _ _ V.alice.matrix V.alice.isometry
    _ = ((isometryPullback V.matrix V.matrix_isometry filler φ).state.marginalA).vonNeumann :=
        psdEntropy_state _

/-- **Local-isometry invariance of the entanglement of formation**, reverse
direction (Step 1).  A decomposition of the image state pulls back to a
decomposition of the original state with no larger cost, because every
positive-weight branch lies in the isometry's range. -/
theorem entanglementOfFormation_applyState_ge (V : TwoQubit.LocalIsometry a a2 c c2)
    (ρ : State (a × c)) :
    entanglementOfFormation ρ ≤ entanglementOfFormation (V.applyState ρ) := by
  apply le_csInf (pureEntanglementValues_nonempty (V.applyState ρ))
  intro x hx
  rcases hx with ⟨F, hFavg, rfl⟩
  have hW := V.matrix_isometry
  have hFmat : F.averageState.matrix =
      V.matrix * ρ.matrix * V.matrix.conjTranspose := by
    rw [hFavg, LocalIsometry.applyState_matrix, LocalIsometry.applyMatrix]
  -- A filler vector exists because the source type is nonempty.
  haveI := ρ.nonempty
  obtain ⟨filler⟩ : ∃ f : PureVector (a × c), True :=
    ⟨ρ.spectralPureVector (Classical.arbitrary (a × c)), trivial⟩
  -- The complementary projection annihilates the image state.
  have hQh : (1 - V.matrix * V.matrix.conjTranspose).conjTranspose
      = 1 - V.matrix * V.matrix.conjTranspose := by
    rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_one,
      mul_conjTranspose_mul_hermitian V.matrix]
  have hQ2 := one_sub_rangeProjection_idempotent V.matrix hW
  have hQF : (1 - V.matrix * V.matrix.conjTranspose) * F.averageState.matrix = 0 := by
    rw [hFmat, ← Matrix.mul_assoc, ← Matrix.mul_assoc,
      one_sub_rangeProjection_mul V.matrix hW, Matrix.zero_mul, Matrix.zero_mul]
  -- Expanding the average state into rank-one branches and taking traces.
  have hexp : (1 - V.matrix * V.matrix.conjTranspose) * F.averageState.matrix =
      ∑ j : Fin F.card, ((F.probs j : ℝ≥0) : ℂ) •
        ((1 - V.matrix * V.matrix.conjTranspose) *
          rankOneMatrix (F.vectors j).amp) := by
    rw [pureDecomposition_averageState_matrix_sum, Matrix.mul_sum]
    exact Finset.sum_congr rfl fun j _ => Matrix.mul_smul _ _ _
  have htr0 : ∑ j : Fin F.card, ((F.probs j : ℝ≥0) : ℂ) *
      ((1 - V.matrix * V.matrix.conjTranspose) *
        rankOneMatrix (F.vectors j).amp).trace = 0 := by
    have hz : ((1 - V.matrix * V.matrix.conjTranspose) *
        F.averageState.matrix).trace = 0 := by
      rw [hQF]; simp
    calc ∑ j : Fin F.card, ((F.probs j : ℝ≥0) : ℂ) *
        ((1 - V.matrix * V.matrix.conjTranspose) *
          rankOneMatrix (F.vectors j).amp).trace
        = ∑ j : Fin F.card, (((F.probs j : ℝ≥0) : ℂ) •
            ((1 - V.matrix * V.matrix.conjTranspose) *
              rankOneMatrix (F.vectors j).amp)).trace := by
          exact Finset.sum_congr rfl fun j _ => by
            rw [Matrix.trace_smul, smul_eq_mul]
      _ = (∑ j : Fin F.card, ((F.probs j : ℝ≥0) : ℂ) •
            ((1 - V.matrix * V.matrix.conjTranspose) *
              rankOneMatrix (F.vectors j).amp)).trace :=
            (Matrix.trace_sum _ _).symm
      _ = ((1 - V.matrix * V.matrix.conjTranspose) * F.averageState.matrix).trace := by
            rw [hexp]
      _ = 0 := hz
  -- Convert to real terms, term by term.
  have hco : ∀ j : Fin F.card,
      ((F.probs j : ℝ≥0) : ℂ) *
        ((1 - V.matrix * V.matrix.conjTranspose) *
          rankOneMatrix (F.vectors j).amp).trace =
      (((∑ z : a2 × c2, ((F.probs j : ℝ≥0) : ℝ) *
        Complex.normSq (((1 - V.matrix * V.matrix.conjTranspose) *ᵥ
          (F.vectors j).amp) z) : ℝ)) : ℂ) := by
    intro j
    rw [trace_mul_rankOne_eq_sum_normSq _ hQh hQ2 (F.vectors j).amp,
      ← Complex.ofReal_mul, Finset.mul_sum]
  have h5 : (((∑ j : Fin F.card, ∑ z : a2 × c2, ((F.probs j : ℝ≥0) : ℝ) *
      Complex.normSq (((1 - V.matrix * V.matrix.conjTranspose) *ᵥ
        (F.vectors j).amp) z) : ℝ)) : ℂ) = 0 := by
    simp_rw [Complex.ofReal_sum]
    calc ∑ j : Fin F.card, ∑ z : a2 × c2,
          ((((F.probs j : ℝ≥0) : ℝ) *
            Complex.normSq (((1 - V.matrix * V.matrix.conjTranspose) *ᵥ
              (F.vectors j).amp) z) : ℝ) : ℂ)
        = ∑ j : Fin F.card, ((F.probs j : ℝ≥0) : ℂ) *
            ((1 - V.matrix * V.matrix.conjTranspose) *
              rankOneMatrix (F.vectors j).amp).trace := by
          refine Finset.sum_congr rfl fun j _ => ?_
          rw [← Complex.ofReal_sum, ← hco j]
      _ = 0 := htr0
  have h4 : (∑ j : Fin F.card, ∑ z : a2 × c2, ((F.probs j : ℝ≥0) : ℝ) *
      Complex.normSq (((1 - V.matrix * V.matrix.conjTranspose) *ᵥ
        (F.vectors j).amp) z)) = 0 :=
    Complex.ofReal_injective h5
  have hnn : ∀ j : Fin F.card, ∀ z : a2 × c2, (0 : ℝ) ≤
      ((F.probs j : ℝ≥0) : ℝ) *
        Complex.normSq (((1 - V.matrix * V.matrix.conjTranspose) *ᵥ
          (F.vectors j).amp) z) := fun j z =>
    mul_nonneg (NNReal.coe_nonneg _) (Complex.normSq_nonneg _)
  have hterm0 : ∀ j : Fin F.card, ∀ z : a2 × c2,
      ((F.probs j : ℝ≥0) : ℝ) *
        Complex.normSq (((1 - V.matrix * V.matrix.conjTranspose) *ᵥ
          (F.vectors j).amp) z) = 0 := by
    intro j z
    have houter := (Finset.sum_eq_zero_iff_of_nonneg
      (fun j _ => Finset.sum_nonneg fun z _ => hnn j z)).mp h4
    exact (Finset.sum_eq_zero_iff_of_nonneg
      (fun z _ => hnn j z)).mp (houter j (Finset.mem_univ j)) z
      (Finset.mem_univ z)
  -- Positive-weight branches lie in the isometry's range.
  have hrange : ∀ j : Fin F.card, ((F.probs j : ℝ≥0) : ℝ) ≠ 0 →
      (1 - V.matrix * V.matrix.conjTranspose) *ᵥ (F.vectors j).amp = 0 := by
    intro j hp
    by_contra hne
    have hex : ∃ z : a2 × c2,
        ((1 - V.matrix * V.matrix.conjTranspose) *ᵥ (F.vectors j).amp) z ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hne (funext hall)
    obtain ⟨z, hz⟩ := hex
    have hterm := hterm0 j z
    rcases mul_eq_zero.mp hterm with h | h
    · exact absurd h hp
    · exact absurd (Complex.normSq_eq_zero.mp h) hz
  -- The pulled-back decomposition averages back to the original state.
  have hpush : (PureDecomposition.pullback V.matrix V.matrix_isometry filler
        F).averageState.matrix =
      ∑ j : Fin F.card, ((F.probs j : ℝ≥0) : ℂ) •
        (V.matrix.conjTranspose * rankOneMatrix (F.vectors j).amp *
          (V.matrix.conjTranspose).conjTranspose) := by
    rw [pureDecomposition_averageState_matrix_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have hGp : ((PureDecomposition.pullback V.matrix V.matrix_isometry filler F).probs j :
        ℝ≥0) = F.probs j := rfl
    by_cases hp : ((F.probs j : ℝ≥0) : ℝ) = 0
    · have hc : ((F.probs j : ℝ≥0) : ℂ) = 0 := by exact_mod_cast hp
      rw [hGp, hc, zero_smul, zero_smul]
    · have hr := hrange j hp
      have hamp : ((PureDecomposition.pullback V.matrix V.matrix_isometry filler
          F).vectors j).amp =
          V.matrix.conjTranspose *ᵥ (F.vectors j).amp :=
        isometryPullback_amp_of_sub_eq_zero V.matrix V.matrix_isometry filler
          (F.vectors j) hr
      rw [hGp, hamp,
        rankOneMatrix_mulVec_eq_mul_rankOneMatrix_mul_conjTranspose]
  have hGavg : (PureDecomposition.pullback V.matrix V.matrix_isometry filler
      F).averageState = ρ := by
    apply State.ext
    calc (PureDecomposition.pullback V.matrix V.matrix_isometry filler
          F).averageState.matrix
        = ∑ j : Fin F.card, ((F.probs j : ℝ≥0) : ℂ) •
            (V.matrix.conjTranspose * rankOneMatrix (F.vectors j).amp *
              (V.matrix.conjTranspose).conjTranspose) := hpush
      _ = V.matrix.conjTranspose * (∑ j : Fin F.card,
            ((F.probs j : ℝ≥0) : ℂ) • rankOneMatrix (F.vectors j).amp) *
            (V.matrix.conjTranspose).conjTranspose :=
            (mul_sum_smul_conj _ _ _).symm
      _ = V.matrix.conjTranspose * F.averageState.matrix *
            (V.matrix.conjTranspose).conjTranspose := by
            rw [pureDecomposition_averageState_matrix_sum]
      _ = ρ.matrix := by
            rw [Matrix.conjTranspose_conjTranspose V.matrix, hFmat,
              conjTranspose_mul_tripod V.matrix hW ρ.matrix]
  -- The pulled-back decomposition has the same entanglement cost.
  have hcostj : ∀ j : Fin F.card,
      (F.probs j).toReal * (((PureDecomposition.pullback V.matrix
        V.matrix_isometry filler F).vectors j).state.marginalA).vonNeumann =
      (F.probs j).toReal * ((F.vectors j).state.marginalA).vonNeumann := by
    intro j
    by_cases hp : (F.probs j).toReal = 0
    · rw [hp, zero_mul, zero_mul]
    · have hpc : ((F.probs j : ℝ≥0) : ℝ) ≠ 0 := by exact hp
      have hr := hrange j hpc
      rw [pure_pullback_marginalA_vonNeumann V filler (F.vectors j) hr]
      rfl
  have hGcost : (PureDecomposition.pullback V.matrix V.matrix_isometry filler
      F).entanglementCost = F.entanglementCost := by
    rw [PureDecomposition.entanglementCost, PureDecomposition.entanglementCost]
    exact Finset.sum_congr rfl fun j _ => hcostj j
  have hle := entanglementOfFormation_le_entanglementCost
    (PureDecomposition.pullback V.matrix V.matrix_isometry filler F)
  rw [hGavg] at hle
  rw [← hGcost]
  exact hle

/-- **Local-isometry invariance of the entanglement of formation** (Step 1):
`E_F` is unchanged by applying a local isometry to the state. -/
theorem entanglementOfFormation_applyState (V : TwoQubit.LocalIsometry a a2 c c2)
    (ρ : State (a × c)) :
    entanglementOfFormation (V.applyState ρ) = entanglementOfFormation ρ :=
  le_antisymm (entanglementOfFormation_applyState_le V ρ)
    (entanglementOfFormation_applyState_ge V ρ)

end LocalIsometryPullback


/-! ### Qubit gauge unitaries (Step 2) -/

/-- The computational basis vector `|0⟩` on the qubit. -/
def qubitKet0 : Qubit → ℂ := fun x => if x = 0 then 1 else 0

/-- The computational basis vector `|1⟩` on the qubit. -/
def qubitKet1 : Qubit → ℂ := fun x => if x = 1 then 1 else 0

@[simp] theorem qubitKet0_zero : qubitKet0 0 = 1 := by simp [qubitKet0]

@[simp] theorem qubitKet0_one : qubitKet0 1 = 0 := by simp [qubitKet0]

@[simp] theorem qubitKet1_zero : qubitKet1 0 = 0 := by simp [qubitKet1]

@[simp] theorem qubitKet1_one : qubitKet1 1 = 1 := by simp [qubitKet1]

/-- Real casts are self-adjoint. -/
theorem star_ofReal_cx (x : ℝ) : star ((x : ℝ) : ℂ) = ((x : ℝ) : ℂ) :=
  Complex.conj_ofReal x

/-- The computational basis vectors are real. -/
theorem star_qubitKet0 (y : Qubit) : star (qubitKet0 y) = qubitKet0 y := by
  fin_cases y <;> simp [qubitKet0]

/-- The computational basis vectors are real. -/
theorem star_qubitKet1 (y : Qubit) : star (qubitKet1 y) = qubitKet1 y := by
  fin_cases y <;> simp [qubitKet1]

/-- The Euclidean norm of a qubit amplitude vector. -/
def qubitNorm (u : Qubit → ℂ) : ℝ := Real.sqrt (∑ y, Complex.normSq (u y))

/-- The norm of an amplitude vector is nonnegative. -/
theorem qubitNorm_nonneg (u : Qubit → ℂ) : 0 ≤ qubitNorm u :=
  Real.sqrt_nonneg _

/-- A nonzero amplitude vector has positive norm. -/
theorem qubitNorm_pos (u : Qubit → ℂ) (hu : u ≠ 0) : 0 < qubitNorm u := by
  have hex : ∃ y, u y ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hu (funext hall)
  obtain ⟨y, hy⟩ := hex
  rw [qubitNorm]
  refine Real.sqrt_pos.mpr (Finset.sum_pos'
    (fun z _ => Complex.normSq_nonneg _) ⟨y, Finset.mem_univ y, ?_⟩)
  exact lt_of_le_of_ne (Complex.normSq_nonneg _)
    (fun h => hy (Complex.normSq_eq_zero.mp h.symm))

/-- The squared real-cast norm, as the two moduli. -/
theorem qubitNorm_sq_cast (u : Qubit → ℂ) :
    ((qubitNorm u : ℝ) : ℂ) * ((qubitNorm u : ℝ) : ℂ) =
      star (u 0) * u 0 + star (u 1) * u 1 := by
  have hns : ∀ z : ℂ, ((Complex.normSq z : ℝ) : ℂ) = star z * z := by
    intro z
    show ((Complex.normSq z : ℝ) : ℂ) = starRingEnd ℂ z * z
    rw [Complex.normSq_eq_conj_mul_self]
  rw [← Complex.ofReal_mul,
    show qubitNorm u = Real.sqrt (∑ y : Qubit, Complex.normSq (u y)) from rfl,
    Real.mul_self_sqrt (Finset.sum_nonneg (fun y _ => Complex.normSq_nonneg _)),
    Fin.sum_univ_two, Complex.ofReal_add, hns, hns]

/-- The explicit gauge unitary sending `u` to `‖u‖ • |0⟩`: its first row is
`conj u / ‖u‖` and its second row is `(u 1, -u 0) / ‖u‖`. -/
def qubitGaugeUnitary (u : Qubit → ℂ) : Matrix Qubit Qubit ℂ :=
  fun y x =>
    if y = 0 then star (u x) / ((qubitNorm u : ℝ) : ℂ)
    else if x = 0 then u 1 / ((qubitNorm u : ℝ) : ℂ)
    else -(u 0) / ((qubitNorm u : ℝ) : ℂ)

/-- Entries of the first row of the gauge unitary. -/
theorem qubitGaugeUnitary_zero_row (u : Qubit → ℂ) (x : Qubit) :
    qubitGaugeUnitary u 0 x = star (u x) / ((qubitNorm u : ℝ) : ℂ) :=
  if_pos rfl

/-- The `(1, 0)` entry of the gauge unitary. -/
theorem qubitGaugeUnitary_one_zero (u : Qubit → ℂ) :
    qubitGaugeUnitary u 1 0 = u 1 / ((qubitNorm u : ℝ) : ℂ) := by
  show (if (1 : Qubit) = 0 then star (u 0) / ((qubitNorm u : ℝ) : ℂ)
      else if (0 : Qubit) = 0 then u 1 / ((qubitNorm u : ℝ) : ℂ)
      else -(u 0) / ((qubitNorm u : ℝ) : ℂ)) = _
  rw [if_neg (show (1 : Qubit) ≠ 0 by decide), if_pos rfl]

/-- The `(1, 1)` entry of the gauge unitary. -/
theorem qubitGaugeUnitary_one_one (u : Qubit → ℂ) :
    qubitGaugeUnitary u 1 1 = -(u 0) / ((qubitNorm u : ℝ) : ℂ) := by
  show (if (1 : Qubit) = 0 then star (u 1) / ((qubitNorm u : ℝ) : ℂ)
      else if (1 : Qubit) = 0 then u 1 / ((qubitNorm u : ℝ) : ℂ)
      else -(u 0) / ((qubitNorm u : ℝ) : ℂ)) = _
  rw [if_neg (show (1 : Qubit) ≠ 0 by decide),
    if_neg (show (1 : Qubit) ≠ 0 by decide)]

/-- The gauge unitary is unitary. -/
theorem qubitGaugeUnitary_conjTranspose_mul (u : Qubit → ℂ) (hu : u ≠ 0) :
    (qubitGaugeUnitary u).conjTranspose * qubitGaugeUnitary u = 1 := by
  have hr : ((qubitNorm u : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (qubitNorm_pos u hu))
  have hsq := qubitNorm_sq_cast u
  ext i j
  simp only [Matrix.mul_apply, Matrix.conjTranspose_apply]
  by_cases hi : i = 0
  · subst hi
    by_cases hj : j = 0
    · subst hj
      rw [Matrix.one_apply, if_pos rfl, Fin.sum_univ_two,
        qubitGaugeUnitary_zero_row, qubitGaugeUnitary_one_zero,
        star_div₀, star_ofReal_cx, star_div₀, star_ofReal_cx, star_star,
        div_mul_div_comm, div_mul_div_comm, ← add_div, mul_comm (u 0) (star (u 0)),
        div_eq_one_iff_eq (mul_ne_zero hr hr), hsq]
    · have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hj
      subst hj1
      rw [Matrix.one_apply, if_neg (show (0 : Qubit) ≠ 1 by decide),
        Fin.sum_univ_two, qubitGaugeUnitary_zero_row, qubitGaugeUnitary_zero_row,
        qubitGaugeUnitary_one_zero, qubitGaugeUnitary_one_one, star_div₀,
        star_ofReal_cx, star_div₀, star_ofReal_cx, star_star, div_mul_div_comm,
        div_mul_div_comm, ← add_div]
      have hnum : u 0 * star (u 1) + star (u 1) * -(u 0) = 0 := by ring
      rw [hnum, zero_div]
  · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi
    subst hi1
    by_cases hj : j = 0
    · subst hj
      rw [Matrix.one_apply, if_neg (show (1 : Qubit) ≠ 0 by decide),
        Fin.sum_univ_two, qubitGaugeUnitary_zero_row, qubitGaugeUnitary_zero_row,
        qubitGaugeUnitary_one_one, qubitGaugeUnitary_one_zero, star_div₀,
        star_ofReal_cx, star_div₀, star_ofReal_cx, star_star, star_neg,
        div_mul_div_comm, div_mul_div_comm, ← add_div]
      have hnum : u 1 * star (u 0) + -(star (u 0)) * u 1 = 0 := by ring
      rw [hnum, zero_div]
    · have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hj
      subst hj1
      rw [Matrix.one_apply, if_pos rfl, Fin.sum_univ_two,
        qubitGaugeUnitary_zero_row, qubitGaugeUnitary_one_one, star_div₀,
        star_ofReal_cx, star_div₀, star_ofReal_cx, star_star, star_neg,
        div_mul_div_comm, div_mul_div_comm, ← add_div,
        div_eq_one_iff_eq (mul_ne_zero hr hr), hsq]
      ring

/-- The gauge unitary sends `u` to its norm times `|0⟩`. -/
theorem qubitGaugeUnitary_mulVec (u : Qubit → ℂ) (hu : u ≠ 0) :
    qubitGaugeUnitary u *ᵥ u = ((qubitNorm u : ℝ) : ℂ) • qubitKet0 := by
  have hsq := qubitNorm_sq_cast u
  have hr : ((qubitNorm u : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (qubitNorm_pos u hu))
  funext x
  by_cases hx : x = 0
  · subst hx
    rw [show (qubitGaugeUnitary u *ᵥ u) 0 =
        qubitGaugeUnitary u 0 0 * u 0 + qubitGaugeUnitary u 0 1 * u 1 from by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two],
      qubitGaugeUnitary_zero_row, qubitGaugeUnitary_zero_row,
      div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, ← hsq,
      mul_div_cancel_right₀ _ hr, Pi.smul_apply, smul_eq_mul, qubitKet0_zero,
      mul_one]
  · have hx1 : x = 1 := Fin.eq_one_of_ne_zero x hx
    subst hx1
    rw [show (qubitGaugeUnitary u *ᵥ u) 1 =
        qubitGaugeUnitary u 1 0 * u 0 + qubitGaugeUnitary u 1 1 * u 1 from by
        simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two],
      qubitGaugeUnitary_one_zero, qubitGaugeUnitary_one_one,
      Pi.smul_apply, smul_eq_mul, qubitKet0_one, mul_zero,
      div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div]
    have hnum : u 1 * u 0 + -(u 0) * u 1 = 0 := by ring
    rw [hnum, zero_div]

/-- The adjoint of the gauge unitary sends `|0⟩` back to the normalized
vector. -/
theorem qubitGaugeUnitary_conjTranspose_mulVec_ket0 (u : Qubit → ℂ) :
    (qubitGaugeUnitary u).conjTranspose *ᵥ qubitKet0 =
      fun x => u x / ((qubitNorm u : ℝ) : ℂ) := by
  funext x
  rw [show ((qubitGaugeUnitary u).conjTranspose *ᵥ qubitKet0) x =
      star (qubitGaugeUnitary u 0 x) * qubitKet0 0 +
        star (qubitGaugeUnitary u 1 x) * qubitKet0 1 from by
      simp only [Matrix.mulVec, dotProduct, Matrix.conjTranspose_apply,
        Fin.sum_univ_two],
    qubitKet0_zero, qubitKet0_one, mul_one, mul_zero, add_zero,
    qubitGaugeUnitary_zero_row, star_div₀, star_ofReal_cx, star_star]

/-- The qubit swap `|0⟩ ↔ |1⟩`. -/
def qubitSwap : Matrix Qubit Qubit ℂ :=
  fun y x => if x = 0 then qubitKet1 y else qubitKet0 y

/-- The first column of the swap. -/
theorem qubitSwap_apply_zero (y : Qubit) : qubitSwap y 0 = qubitKet1 y := if_pos rfl

/-- The second column of the swap. -/
theorem qubitSwap_apply_one (y : Qubit) : qubitSwap y 1 = qubitKet0 y := by
  show (if (1 : Qubit) = 0 then qubitKet1 y else qubitKet0 y) = _
  rw [if_neg (show (1 : Qubit) ≠ 0 by decide)]

/-- The swap interchanges the basis vectors: `S |0⟩ = |1⟩`. -/
theorem qubitSwap_mulVec_ket0 : qubitSwap *ᵥ qubitKet0 = qubitKet1 := by
  funext y
  rw [show (qubitSwap *ᵥ qubitKet0) y =
      qubitSwap y 0 * qubitKet0 0 + qubitSwap y 1 * qubitKet0 1 from by
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two],
    qubitSwap_apply_zero, qubitSwap_apply_one, qubitKet0_zero, qubitKet0_one,
    mul_one, mul_zero, add_zero]

/-- The swap interchanges the basis vectors: `S |1⟩ = |0⟩`. -/
theorem qubitSwap_mulVec_ket1 : qubitSwap *ᵥ qubitKet1 = qubitKet0 := by
  funext y
  rw [show (qubitSwap *ᵥ qubitKet1) y =
      qubitSwap y 0 * qubitKet1 0 + qubitSwap y 1 * qubitKet1 1 from by
      simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two],
    qubitSwap_apply_zero, qubitSwap_apply_one, qubitKet1_zero, qubitKet1_one,
    mul_zero, mul_one, zero_add]

/-- The swap is self-adjoint. -/
theorem qubitSwap_conjTranspose : qubitSwap.conjTranspose = qubitSwap := by
  ext y x
  rw [Matrix.conjTranspose_apply]
  fin_cases y <;> fin_cases x <;>
    simp [qubitSwap, qubitKet0, qubitKet1]

/-- The first row of the swap. -/
theorem qubitSwap_row_zero : qubitSwap 0 = qubitKet1 := by
  funext x
  by_cases hx : x = 0
  · subst hx
    rw [qubitSwap_apply_zero]
  · have hx1 : x = 1 := Fin.eq_one_of_ne_zero x hx
    subst hx1
    rw [qubitSwap_apply_one, qubitKet0_zero, qubitKet1_one]

/-- The second row of the swap. -/
theorem qubitSwap_row_one : qubitSwap 1 = qubitKet0 := by
  funext x
  by_cases hx : x = 0
  · subst hx
    rw [qubitSwap_apply_zero, qubitKet1_one, qubitKet0_zero]
  · have hx1 : x = 1 := Fin.eq_one_of_ne_zero x hx
    subst hx1
    rw [qubitSwap_apply_one]

/-- The swap is unitary. -/
theorem qubitSwap_conjTranspose_mul : qubitSwap.conjTranspose * qubitSwap = 1 := by
  rw [qubitSwap_conjTranspose]
  ext i j
  simp only [Matrix.mul_apply, Fin.sum_univ_two]
  by_cases hi : i = 0
  · subst hi
    by_cases hj : j = 0
    · subst hj
      rw [Matrix.one_apply, if_pos rfl, qubitSwap_apply_zero, qubitSwap_apply_one,
        qubitSwap_apply_zero, qubitKet1_zero, qubitKet0_zero, qubitKet1_one]
      norm_num
    · have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hj
      subst hj1
      rw [Matrix.one_apply, if_neg (show (0 : Qubit) ≠ 1 by decide),
        qubitSwap_apply_zero, qubitSwap_apply_one, qubitSwap_apply_one,
        qubitKet1_zero, qubitKet0_zero, qubitKet0_one]
      norm_num
  · have hi1 : i = 1 := Fin.eq_one_of_ne_zero i hi
    subst hi1
    by_cases hj : j = 0
    · subst hj
      rw [Matrix.one_apply, if_neg (show (1 : Qubit) ≠ 0 by decide),
        qubitSwap_apply_zero, qubitSwap_apply_zero, qubitSwap_apply_one,
        qubitKet1_one, qubitKet1_zero, qubitKet0_one]
      norm_num
    · have hj1 : j = 1 := Fin.eq_one_of_ne_zero j hj
      subst hj1
      rw [Matrix.one_apply, if_pos rfl, qubitSwap_apply_zero, qubitSwap_apply_one,
        qubitSwap_apply_one, qubitKet1_one, qubitKet0_zero, qubitKet0_one]
      norm_num

/-- The gauge unitary sending `v` to `‖v‖ • |1⟩`: the swap composed with the
`|0⟩` gauge unitary. -/
def qubitGaugeUnitaryOne (v : Qubit → ℂ) : Matrix Qubit Qubit ℂ :=
  qubitSwap * qubitGaugeUnitary v

/-- The `|1⟩` gauge unitary is unitary. -/
theorem qubitGaugeUnitaryOne_conjTranspose_mul (v : Qubit → ℂ) (hv : v ≠ 0) :
    (qubitGaugeUnitaryOne v).conjTranspose * qubitGaugeUnitaryOne v = 1 := by
  have hstep : (qubitGaugeUnitaryOne v).conjTranspose * qubitGaugeUnitaryOne v =
      (qubitGaugeUnitary v).conjTranspose *
        ((qubitSwap.conjTranspose * qubitSwap) * qubitGaugeUnitary v) := by
    rw [qubitGaugeUnitaryOne, Matrix.conjTranspose_mul, Matrix.mul_assoc,
      ← Matrix.mul_assoc qubitSwap.conjTranspose qubitSwap (qubitGaugeUnitary v)]
  rw [hstep, qubitSwap_conjTranspose_mul, Matrix.one_mul,
    qubitGaugeUnitary_conjTranspose_mul v hv]

/-- The `|1⟩` gauge unitary sends `v` to its norm times `|1⟩`. -/
theorem qubitGaugeUnitaryOne_mulVec (v : Qubit → ℂ) (hv : v ≠ 0) :
    qubitGaugeUnitaryOne v *ᵥ v = ((qubitNorm v : ℝ) : ℂ) • qubitKet1 := by
  rw [qubitGaugeUnitaryOne, ← Matrix.mulVec_mulVec, qubitGaugeUnitary_mulVec v hv,
    Matrix.mulVec_smul, qubitSwap_mulVec_ket0]

/-- The adjoint of the `|1⟩` gauge unitary sends `|1⟩` back to the normalized
vector. -/
theorem qubitGaugeUnitaryOne_conjTranspose_mulVec_ket1 (v : Qubit → ℂ) :
    (qubitGaugeUnitaryOne v).conjTranspose *ᵥ qubitKet1 =
      fun x => v x / ((qubitNorm v : ℝ) : ℂ) := by
  rw [qubitGaugeUnitaryOne, Matrix.conjTranspose_mul, ← Matrix.mulVec_mulVec,
    show qubitSwap.conjTranspose *ᵥ qubitKet1 = qubitKet0 from by
      rw [qubitSwap_conjTranspose, qubitSwap_mulVec_ket1],
    qubitGaugeUnitary_conjTranspose_mulVec_ket0]


/-! ### The local-unitary reduction (Step 3) -/

section Step3

variable {a : Type u} {c : Type v}
variable [Fintype a] [DecidableEq a]
variable [Fintype c] [DecidableEq c]

/-- A vector orthogonal to `|0⟩` has vanishing `|0⟩` component. -/
theorem qubitKet0_of_ne {x : Qubit} (hx : x ≠ 0) : qubitKet0 x = 0 := if_neg hx

/-- A vector orthogonal to `|1⟩` has vanishing `|1⟩` component. -/
theorem qubitKet1_of_ne {x : Qubit} (hx : x ≠ 1) : qubitKet1 x = 0 := if_neg hx

/-- Kronecker products act on product vectors factorwise. -/
theorem kronecker_mulVec_tmul
    {m : Type w₁} {n : Type w₂} {p : Type w₃} {q : Type w₄}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (M : Matrix m n ℂ) (N : Matrix p q ℂ) (w : n → ℂ) (z : q → ℂ) :
    (M ⊗ₖ N) *ᵥ (fun x : n × q => w x.1 * z x.2) =
      fun y : m × p => (M *ᵥ w) y.1 * (N *ᵥ z) y.2 := by
  funext y
  simp only [Matrix.mulVec, dotProduct, Matrix.kroneckerMap_apply,
    Fintype.sum_prod_type]
  rw [Finset.sum_mul_sum]
  exact Finset.sum_congr rfl fun x1 _ =>
    Finset.sum_congr rfl fun x2 _ => by ring

/-- The two-qubit basis vector `|01⟩` is the product `|0⟩ ⊗ |1⟩`. -/
theorem ket01_eq : (ket01 : Prod Qubit Qubit → ℂ) =
    fun p => qubitKet0 p.1 * qubitKet1 p.2 := by
  funext p
  by_cases h1 : p.1 = 0
  · by_cases h2 : p.2 = 1
    · have hp : p = (0, 1) := Prod.ext h1 h2
      subst hp
      simp
    · rw [qubitKet1_of_ne h2, mul_zero,
        ket01_of_ne (fun hp => h2 (congrArg Prod.snd hp))]
  · by_cases h2 : p.2 = 1
    · rw [qubitKet0_of_ne h1, zero_mul,
        ket01_of_ne (fun hp => h1 (congrArg Prod.fst hp))]
    · rw [qubitKet0_of_ne h1, zero_mul,
        ket01_of_ne (fun hp => h2 (congrArg Prod.snd hp))]

/-- A Kronecker product of isometries is an isometry. -/
theorem kronecker_isometry
    {m : Type w₁} {n : Type w₂} {p : Type w₃} {q : Type w₄}
    [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    [Fintype p] [DecidableEq p] [Fintype q] [DecidableEq q]
    (A : Matrix m n ℂ) (hA : A.conjTranspose * A = 1)
    (B : Matrix p q ℂ) (hB : B.conjTranspose * B = 1) :
    (A ⊗ₖ B).conjTranspose * (A ⊗ₖ B) = 1 := by
  rw [Matrix.conjTranspose_kronecker, ← Matrix.mul_kronecker_mul, hA, hB,
    Matrix.one_kronecker_one]

omit [Fintype a] [Fintype c] in
/-- Reassociating the double Kronecker gauge action: conjugating by
`(U ⊗ 1) ⊗ (V ⊗ 1)` in the `AA' ⊗ CC'` ordering is conjugating by
`(U ⊗ V) ⊗ 1` in the reassociated ordering. -/
theorem gaugeTensor_submatrix_prodReassoc
    (U : Matrix Qubit Qubit ℂ) (V : Matrix Qubit Qubit ℂ) :
    ((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ))).submatrix
        prodReassoc.symm prodReassoc.symm =
      (U ⊗ₖ V) ⊗ₖ (1 : Matrix (a × c) (a × c) ℂ) := by
  ext x y
  obtain ⟨⟨p1, p2⟩, q1, q2⟩ := x
  obtain ⟨⟨p1', p2'⟩, q1', q2'⟩ := y
  simp only [Matrix.submatrix_apply, prodReassoc_symm_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases hq : (q1, q2) = (q1', q2')
  · have he1 : q1 = q1' := congrArg Prod.fst hq
    have he2 : q2 = q2' := congrArg Prod.snd hq
    subst he1
    subst he2
    rw [if_pos rfl, if_pos rfl, if_pos rfl]
    ring
  · rw [if_neg hq, mul_zero]
    by_cases h1 : q1 = q1'
    · have h2 : q2 ≠ q2' := fun h => hq (Prod.ext h1 h)
      rw [if_neg h2]
      ring
    · rw [if_neg h1]
      ring

/-- The local isometry `(U ⊗ 1_{A'}) ⊗ (V ⊗ 1_{C'})` on a state of `AA' ⊗ CC'`
shape, built from two qubit unitaries. -/
def tensorIsometry (U : Matrix Qubit Qubit ℂ) (hU : U.conjTranspose * U = 1)
    (V : Matrix Qubit Qubit ℂ) (hV : V.conjTranspose * V = 1) :
    TwoQubit.LocalIsometry (Qubit × a) (Qubit × a) (Qubit × c) (Qubit × c) where
  alice := ⟨U ⊗ₖ (1 : Matrix a a ℂ),
    kronecker_isometry U hU (1 : Matrix a a ℂ)
      (by rw [Matrix.conjTranspose_one, Matrix.one_mul])⟩
  bob := ⟨V ⊗ₖ (1 : Matrix c c ℂ),
    kronecker_isometry V hV (1 : Matrix c c ℂ)
      (by rw [Matrix.conjTranspose_one, Matrix.one_mul])⟩

theorem tensorIsometry_matrix (U : Matrix Qubit Qubit ℂ) (hU : U.conjTranspose * U = 1)
    (V : Matrix Qubit Qubit ℂ) (hV : V.conjTranspose * V = 1) :
    (tensorIsometry U hU V hV).matrix =
      (U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ)) :=
  rfl

/-- The local isometry `W ⊗ 1` on the reassociated bipartition `AB | A'C'`. -/
def reassocIsometry (W : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ)
    (hW : W.conjTranspose * W = 1) :
    TwoQubit.LocalIsometry (Qubit × Qubit) (Qubit × Qubit) (a × c) (a × c) where
  alice := ⟨W, hW⟩
  bob := ⟨1, by rw [Matrix.conjTranspose_one, Matrix.one_mul]⟩

theorem reassocIsometry_matrix (W : Matrix (Qubit × Qubit) (Qubit × Qubit) ℂ)
    (hW : W.conjTranspose * W = 1) :
    (reassocIsometry W hW).matrix = W ⊗ₖ (1 : Matrix (a × c) (a × c) ℂ) :=
  rfl

/-- Conjugating by the tensor gauge isometries and then reassociating equals
reassociating first and then conjugating by the fused isometry. -/
theorem applyState_reindex_prodReassoc
    (U : Matrix Qubit Qubit ℂ) (hU : U.conjTranspose * U = 1)
    (V : Matrix Qubit Qubit ℂ) (hV : V.conjTranspose * V = 1)
    (Ω : State ((Qubit × a) × (Qubit × c))) :
    ((tensorIsometry U hU V hV).applyState Ω).reindex prodReassoc =
      (reassocIsometry (U ⊗ₖ V) (kronecker_isometry U hU V hV)).applyState
        (Ω.reindex prodReassoc) := by
  apply State.ext
  rw [State.reindex_matrix, LocalIsometry.applyState_matrix,
    LocalIsometry.applyState_matrix, LocalIsometry.applyMatrix,
    LocalIsometry.applyMatrix, tensorIsometry_matrix, reassocIsometry_matrix,
    State.reindex_matrix]
  have s1 :
      (((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ))) * Ω.matrix *
          ((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ))).conjTranspose).submatrix
          prodReassoc.symm prodReassoc.symm =
        (((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ))) * Ω.matrix).submatrix
          prodReassoc.symm prodReassoc.symm *
        (((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ))).conjTranspose).submatrix
          prodReassoc.symm prodReassoc.symm :=
    (Matrix.submatrix_mul_equiv
      (((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ))) * Ω.matrix)
      ((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ))).conjTranspose
      prodReassoc.symm prodReassoc.symm prodReassoc.symm).symm
  have s2 :
      (((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ))) * Ω.matrix).submatrix
          prodReassoc.symm prodReassoc.symm =
        ((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ))).submatrix
          prodReassoc.symm prodReassoc.symm *
        Ω.matrix.submatrix prodReassoc.symm prodReassoc.symm :=
    (Matrix.submatrix_mul_equiv
      ((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ))) Ω.matrix
      prodReassoc.symm prodReassoc.symm prodReassoc.symm).symm
  have s3 :
      ((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ))).conjTranspose.submatrix
          prodReassoc.symm prodReassoc.symm =
        (((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ))).submatrix
          prodReassoc.symm prodReassoc.symm).conjTranspose :=
    (Matrix.conjTranspose_submatrix
      ((U ⊗ₖ (1 : Matrix a a ℂ)) ⊗ₖ (V ⊗ₖ (1 : Matrix c c ℂ)))
      prodReassoc.symm prodReassoc.symm).symm
  rw [s1, s2, s3, gaugeTensor_submatrix_prodReassoc]

/-- The two-qubit marginal of the gauge-conjugated state is the conjugated
two-qubit marginal. -/
theorem tensorGauge_marginalA_matrix
    (U : Matrix Qubit Qubit ℂ) (hU : U.conjTranspose * U = 1)
    (V : Matrix Qubit Qubit ℂ) (hV : V.conjTranspose * V = 1)
    (Ω : State ((Qubit × a) × (Qubit × c))) :
    (((tensorIsometry U hU V hV).applyState Ω).reindex prodReassoc).marginalA.matrix =
      (U ⊗ₖ V) * ((Ω.reindex prodReassoc).marginalA).matrix *
        (U ⊗ₖ V).conjTranspose := by
  rw [applyState_reindex_prodReassoc]
  exact localIsometry_applyState_marginalA_matrix
    (reassocIsometry (U ⊗ₖ V) (kronecker_isometry U hU V hV))
    (Ω.reindex prodReassoc)

/-- The `A'B'` marginal is unchanged by the gauge conjugation. -/
theorem tensorGauge_marginalB
    (U : Matrix Qubit Qubit ℂ) (hU : U.conjTranspose * U = 1)
    (V : Matrix Qubit Qubit ℂ) (hV : V.conjTranspose * V = 1)
    (Ω : State ((Qubit × a) × (Qubit × c))) :
    (((tensorIsometry U hU V hV).applyState Ω).reindex prodReassoc).marginalB =
      (Ω.reindex prodReassoc).marginalB := by
  apply State.ext
  rw [applyState_reindex_prodReassoc, State.marginalB_matrix,
    State.marginalB_matrix, LocalIsometry.applyState_matrix,
    LocalIsometry.applyMatrix, reassocIsometry_matrix, State.reindex_matrix]
  exact partialTraceA_conj_kronecker_left (U ⊗ₖ V) (kronecker_isometry U hU V hV)
    (Ω.reindex prodReassoc).matrix

/-- The conjugated two-qubit marginal annihilates `|01⟩`: the adjoint gauge
unitaries map `|01⟩` back to the normalized kernel vector, which the original
marginal kills. -/
theorem tensorGauge_marginalA_mulVec_ket01
    (u v : Qubit → ℂ)
    (ρ : Matrix (Prod Qubit Qubit) (Prod Qubit Qubit) ℂ)
    (hk : ρ *ᵥ (fun p => u p.1 * v p.2) = 0) :
    ((qubitGaugeUnitary u ⊗ₖ qubitGaugeUnitaryOne v) * ρ *
        (qubitGaugeUnitary u ⊗ₖ qubitGaugeUnitaryOne v).conjTranspose) *ᵥ ket01 = 0 := by
  rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec,
    Matrix.conjTranspose_kronecker, ket01_eq, kronecker_mulVec_tmul,
    qubitGaugeUnitary_conjTranspose_mulVec_ket0,
    qubitGaugeUnitaryOne_conjTranspose_mulVec_ket1]
  show (qubitGaugeUnitary u ⊗ₖ qubitGaugeUnitaryOne v) *ᵥ
      (ρ *ᵥ (fun p : Qubit × Qubit =>
        (u p.1 / ((qubitNorm u : ℝ) : ℂ)) * (v p.2 / ((qubitNorm v : ℝ) : ℂ)))) = 0
  have hscale : (fun p : Qubit × Qubit =>
        (u p.1 / ((qubitNorm u : ℝ) : ℂ)) * (v p.2 / ((qubitNorm v : ℝ) : ℂ))) =
      (((qubitNorm u : ℝ) : ℂ) * ((qubitNorm v : ℝ) : ℂ))⁻¹ •
        (fun p => u p.1 * v p.2) := by
    funext p
    rw [Pi.smul_apply, smul_eq_mul, div_mul_div_comm, div_eq_inv_mul]
  rw [hscale, Matrix.mulVec_smul, hk, smul_zero, Matrix.mulVec_zero]

/-- **Theorem 6, full form (local-unitary reduction).**  If the two-qubit
marginal `ρ_AB` of a state `Ω` on `AA' ⊗ BB'` has a nonzero product vector
`u ⊗ v` in its kernel, then `E_F(ρ_AB) + E_F(σ_A'B') ≤ E_F(Ω)`.  Local
unitaries rotate `u ⊗ v` to a multiple of `|01⟩`, the gauge-fixed theorem
applies to the conjugated state, and isometry invariance transports the three
`E_F` terms back. -/
theorem entanglementOfFormation_superadditive_of_productKernel
    (h : woottersKernelUpperBound)
    (Omega : State ((Qubit × a) × (Qubit × c)))
    (u v : Qubit → ℂ) (hu : u ≠ 0) (hv : v ≠ 0)
    (hk : ((Omega.reindex prodReassoc).marginalA).matrix *ᵥ
        (fun p => u p.1 * v p.2) = 0) :
    entanglementOfFormation ((Omega.reindex prodReassoc).marginalA) +
      entanglementOfFormation ((Omega.reindex prodReassoc).marginalB) ≤
      entanglementOfFormation Omega := by
  have hU : (qubitGaugeUnitary u).conjTranspose * qubitGaugeUnitary u = 1 :=
    qubitGaugeUnitary_conjTranspose_mul u hu
  have hW : (qubitGaugeUnitaryOne v).conjTranspose * qubitGaugeUnitaryOne v = 1 :=
    qubitGaugeUnitaryOne_conjTranspose_mul v hv
  -- The conjugated state's two-qubit marginal annihilates `|01⟩`.
  have hker : (((tensorIsometry (qubitGaugeUnitary u) hU
        (qubitGaugeUnitaryOne v) hW).applyState Omega).reindex
        prodReassoc).marginalA.matrix *ᵥ ket01 = 0 := by
    rw [tensorGauge_marginalA_matrix]
    exact tensorGauge_marginalA_mulVec_ket01 u v
      ((Omega.reindex prodReassoc).marginalA).matrix hk
  have hzero : (((tensorIsometry (qubitGaugeUnitary u) hU
        (qubitGaugeUnitaryOne v) hW).applyState Omega).reindex
        prodReassoc).marginalA.matrix (0, 1) (0, 1) = 0 :=
    matrix_diagonal_of_mulVec_ket01_eq_zero hker
  -- The gauge-fixed theorem applies to the conjugated state.
  have hmain := entanglementOfFormation_superadditive h
    ((tensorIsometry (qubitGaugeUnitary u) hU (qubitGaugeUnitaryOne v) hW).applyState
      Omega) hzero
  -- Transport the three `E_F` terms back along the isometries.
  have hEFΩ : entanglementOfFormation ((tensorIsometry (qubitGaugeUnitary u) hU
        (qubitGaugeUnitaryOne v) hW).applyState Omega) =
      entanglementOfFormation Omega :=
    entanglementOfFormation_applyState _ Omega
  have hρ2 : (((tensorIsometry (qubitGaugeUnitary u) hU
        (qubitGaugeUnitaryOne v) hW).applyState Omega).reindex
        prodReassoc).marginalA =
      ((TwoQubit.LocalIsometry.mk ⟨qubitGaugeUnitary u, hU⟩
          ⟨qubitGaugeUnitaryOne v, hW⟩ :
        TwoQubit.LocalIsometry Qubit Qubit Qubit Qubit).applyState
        ((Omega.reindex prodReassoc).marginalA)) := by
    apply State.ext
    rw [tensorGauge_marginalA_matrix]
    rfl
  have hEFρ : entanglementOfFormation (((tensorIsometry (qubitGaugeUnitary u) hU
        (qubitGaugeUnitaryOne v) hW).applyState Omega).reindex
        prodReassoc).marginalA =
      entanglementOfFormation ((Omega.reindex prodReassoc).marginalA) := by
    rw [hρ2, entanglementOfFormation_applyState]
  have hEFσ : entanglementOfFormation (((tensorIsometry (qubitGaugeUnitary u) hU
        (qubitGaugeUnitaryOne v) hW).applyState Omega).reindex
        prodReassoc).marginalB =
      entanglementOfFormation ((Omega.reindex prodReassoc).marginalB) := by
    rw [tensorGauge_marginalB]
  calc entanglementOfFormation ((Omega.reindex prodReassoc).marginalA) +
        entanglementOfFormation ((Omega.reindex prodReassoc).marginalB)
      = entanglementOfFormation (((tensorIsometry (qubitGaugeUnitary u) hU
            (qubitGaugeUnitaryOne v) hW).applyState Omega).reindex
            prodReassoc).marginalA +
          entanglementOfFormation (((tensorIsometry (qubitGaugeUnitary u) hU
            (qubitGaugeUnitaryOne v) hW).applyState Omega).reindex
            prodReassoc).marginalB := by rw [hEFρ, hEFσ]
    _ ≤ entanglementOfFormation ((tensorIsometry (qubitGaugeUnitary u) hU
          (qubitGaugeUnitaryOne v) hW).applyState Omega) := hmain
    _ = entanglementOfFormation Omega := hEFΩ

end Step3


end

end AmplitudeDamping
