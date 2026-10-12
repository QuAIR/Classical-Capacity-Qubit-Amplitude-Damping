import AmplitudeDamping.SupportSSA
import AmplitudeDamping.TwoKrausRoof
import AmplitudeDamping.GenericHolevoAdditivity

/-!
# Supported Stinespring ranges

The hypothesis is range containment of a concrete Stinespring isometry after
local coordinate isometries on output and environment. No restriction is
placed on the input dimension, Kraus count, or auxiliary channel. The
two-expectation decomposition theorem is proved in this library.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Matrix NNReal Kronecker
namespace AmplitudeDamping
open QIT
noncomputable section
universe u₁ u₂ u₃ u₄ u₅ u₆ u₇
variable {x : Type u₁} {o : Type u₂} {e : Type u₃}
variable {a : Type u₄} {b : Type u₅} {y : Type u₆} {z : Type u₇}
variable [Fintype x] [DecidableEq x] [Fintype o] [DecidableEq o]
variable [Fintype e] [DecidableEq e] [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b] [Fintype y] [DecidableEq y]
variable [Fintype z] [DecidableEq z]

/-- A matrix has range in the allowed support iff all its forbidden-sector
coordinates vanish on every input basis vector. The output/environment
coordinate maps may be any local isometries, including unitary basis changes. -/
def HasSupportedStinespringRange
    (V : Matrix (o × e) x ℂ)
    (L : TwoQubit.LocalIsometry o (a ⊕ Unit) e (Unit ⊕ b)) : Prop :=
  ∀ i : a, ∀ j : b, ∀ k : x, (L.matrix * V) (Sum.inl i, Sum.inr j) k = 0

/-- The columnwise range hypothesis implies support of every dilated input
state, including mixed inputs. -/
theorem supported_isometryImageState
    (V : Matrix (o × e) x ℂ) (hV : V.conjTranspose * V = 1)
    (L : TwoQubit.LocalIsometry o (a ⊕ Unit) e (Unit ⊕ b))
    (hR : HasSupportedStinespringRange V L) (ρ : State x) :
    HasSingleExcitationSupport (L.applyState (isometryImageState V hV ρ)) := by
  intro i j
  rw [TwoQubit.LocalIsometry.applyState_matrix, TwoQubit.LocalIsometry.applyMatrix,
    isometryImageState_matrix]
  have he : L.matrix * (V * ρ.matrix * V.conjTranspose) * L.matrix.conjTranspose =
      (L.matrix * V) * ρ.matrix * (L.matrix * V).conjTranspose := by
    simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
  rw [he]
  simp only [Matrix.mul_apply, hR i j, zero_mul, Finset.sum_const_zero]

/-- Roof superadditivity for a channel represented by an arbitrary supported
Kraus stack. The Kraus representation and its range condition are concrete;
the conclusion is obtained from state SSA and the generic MSW identity. -/
theorem outputEntropyRoof_prod_ge_of_supported_kraus
    (N : Channel x o) (K : e → Matrix o x ℂ)
    (hN : N.map = MatrixMap.ofKraus K)
    (L : TwoQubit.LocalIsometry o (a ⊕ Unit) e (Unit ⊕ b))
    (hR : HasSupportedStinespringRange (MatrixMap.krausStinespringMatrix K) L)
    (M : Channel y z) (τ : State (x × y)) :
    outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB ≤
      outputEntropyRoof (N.prod M) τ := by
  have hK : MatrixMap.krausAdjoint K (1 : CMatrix o) = 1 :=
    MatrixMap.krausAdjoint_one_of_tracePreserving K (by rw [← hN]; exact N.tracePreserving)
  have hJ := M.krausAdjoint_one
  let S := MatrixMap.krausStinespringMatrix K
  let R := MatrixMap.krausStinespringMatrix M.kraus
  let U := MatrixMap.krausStinespringMatrix (MatrixMap.krausProduct K M.kraus)
  have hS : S.conjTranspose * S = 1 :=
    MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one K hK
  have hR' : R.conjTranspose * R = 1 :=
    MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one M.kraus hJ
  have hU : U.conjTranspose * U = 1 :=
    MatrixMap.krausStinespringMatrix_isometry_of_krausAdjoint_one _
      (krausAdjoint_krausProduct_one K M.kraus hK hJ)
  have hchanS : ∀ ρ : State x, (isometryImageState S hS ρ).marginalA = N.applyState ρ :=
    krausStinespring_isometryImageState_marginalA K hK N hN
  have hchanR : ∀ ρ : State y, (isometryImageState R hR' ρ).marginalA = M.applyState ρ :=
    krausStinespring_isometryImageState_marginalA M.kraus hJ M M.map_eq_ofKraus
  have hchanU : ∀ ρ : State (x × y),
      (isometryImageState U hU ρ).marginalA = (N.prod M).applyState ρ := by
    intro ρ
    apply krausStinespring_isometryImageState_marginalA
      (MatrixMap.krausProduct K M.kraus) (krausAdjoint_krausProduct_one K M.kraus hK hJ)
    change MatrixMap.kron N.map M.map = _
    rw [hN, M.map_eq_ofKraus, MatrixMap.kron_ofKraus_eq_ofKraus_krausProduct]
  have hA : ((isometryImageState U hU τ).reindex prodReassoc).marginalA =
      isometryImageState S hS τ.marginalA :=
    isometryImageState_krausProduct_reindex_marginalA K hK M.kraus hJ τ
  have hB : ((isometryImageState U hU τ).reindex prodReassoc).marginalB =
      isometryImageState R hR' τ.marginalB :=
    isometryImageState_krausProduct_reindex_marginalB K hK M.kraus hJ τ
  have h := support_criterion_of_local_coordinates L (isometryImageState U hU τ)
    (by rw [hA]; exact supported_isometryImageState S hS L hR τ.marginalA)
  rw [hA, hB] at h
  rw [outputEntropyRoof_eq_entanglementOfFormation_of_isometry N S hS hchanS,
    outputEntropyRoof_eq_entanglementOfFormation_of_isometry M R hR' hchanR,
    outputEntropyRoof_eq_entanglementOfFormation_of_isometry (N.prod M) U hU hchanU]
  exact h

/-- Exact Stinespring realization on all matrices, with trace-out over the
environment. This is a dilation condition, not an entropy-roof hypothesis. -/
def StinespringRealizes (N : Channel x o) (V : Matrix (o × e) x ℂ) : Prop :=
  ∀ X : CMatrix x, partialTraceB (V * X * V.conjTranspose) = N.map X

/-- The arbitrary-isometry formulation of the supported Stinespring theorem.
Every finite-dimensional dilation can be reshaped as a Kraus stack, so no
restriction to a chosen canonical environment is imposed. -/
theorem outputEntropyRoof_prod_ge_of_supported_stinespring
    (N : Channel x o) (V : Matrix (o × e) x ℂ)
    (_hV : V.conjTranspose * V = 1) (hN : StinespringRealizes N V)
    (L : TwoQubit.LocalIsometry o (a ⊕ Unit) e (Unit ⊕ b))
    (hR : HasSupportedStinespringRange V L)
    (M : Channel y z) (τ : State (x × y)) :
    outputEntropyRoof N τ.marginalA + outputEntropyRoof M τ.marginalB ≤
      outputEntropyRoof (N.prod M) τ := by
  let K : e → Matrix o x ℂ := fun k i j => V (i,k) j
  have hstack : MatrixMap.krausStinespringMatrix K = V := rfl
  have hmap : N.map = MatrixMap.ofKraus K := by
    ext X i j
    have he := MatrixMap.partialTraceB_krausStinespringMatrix K X
    rw [hstack, hN X] at he
    exact congrFun (congrFun he i) j
  exact outputEntropyRoof_prod_ge_of_supported_kraus N K hmap L
    (by rwa [hstack]) M τ


end

section OperationalCapacity
variable {x o e a b : Type}
variable [Fintype x] [DecidableEq x] [Fintype o] [DecidableEq o]
variable [Fintype e] [DecidableEq e] [Fintype a] [DecidableEq a]
variable [Fintype b] [DecidableEq b]
variable [Nonempty x]

/-- A supported Stinespring range makes the channel strongly Holevo additive. -/
theorem supported_stinespring_strongHolevoAdditive
    (N : Channel x o) (V : Matrix (o × e) x ℂ)
    (hV : V.conjTranspose * V = 1) (hN : StinespringRealizes N V)
    (L : TwoQubit.LocalIsometry o (a ⊕ Unit) e (Unit ⊕ b))
    (hR : HasSupportedStinespringRange V L) :
    CapacityAdditivity.StrongHolevoAdditive N := by
  intro y z _ _ _ _ _ M
  exact generic_holevoInformation_prod_eq N M
    (outputEntropyRoof_prod_ge_of_supported_stinespring N V hV hN L hR M)

/-- No regularization is needed for the classical capacity of a channel with
a supported Stinespring range. Operational capacity is the actual HSW API. -/
theorem supported_stinespring_classicalCapacity_eq_holevoInformation [Nonempty o]
    (N : Channel x o) (V : Matrix (o × e) x ℂ)
    (hV : V.conjTranspose * V = 1) (hN : StinespringRealizes N V)
    (L : TwoQubit.LocalIsometry o (a ⊕ Unit) e (Unit ⊕ b))
    (hR : HasSupportedStinespringRange V L) :
    Channel.classicalCapacity.{0,0,0} N = Channel.holevoInformation.{0,0,0} N := by
  rw [Channel.classicalCapacity_eq_regularizedHolevoInformation]
  exact CapacityAdditivity.regularizedHolevoInformation_eq N
    (supported_stinespring_strongHolevoAdditive N V hV hN L hR)

/-- Operational capacity is additive against any finite-dimensional partner,
without assuming that the partner itself has a single-letter capacity. -/
theorem supported_stinespring_classicalCapacity_prod_eq [Nonempty o]
    (N : Channel x o) (V : Matrix (o × e) x ℂ)
    (hV : V.conjTranspose * V = 1) (hN : StinespringRealizes N V)
    (L : TwoQubit.LocalIsometry o (a ⊕ Unit) e (Unit ⊕ b))
    (hR : HasSupportedStinespringRange V L)
    {y z : Type} [Fintype y] [DecidableEq y] [Fintype z] [DecidableEq z]
    [Nonempty y] [Nonempty z] (M : Channel y z) :
    Channel.classicalCapacity.{0,0,0} (N.prod M) =
      Channel.classicalCapacity.{0,0,0} N + Channel.classicalCapacity.{0,0,0} M := by
  exact CapacityAdditivity.classicalCapacity_prod_eq N
    (supported_stinespring_strongHolevoAdditive N V hV hN L hR) M

end OperationalCapacity
end AmplitudeDamping
