import AmplitudeDamping.Channel
import AmplitudeDamping.ChoiState
import QIT.States.MaximallyEntangled
import QIT.Core.Map.ChoiCharacterization

/-!
# Normalized channel Choi states

The reference system is a copy of the input.  The Choi state is defined by
applying the actual channel to half of a normalized maximally entangled state.
The amplitude-damping bridge identifies this operational construction with
the explicit matrix used in `ChoiState`.
-/

namespace AmplitudeDamping
open QIT
open scoped BigOperators NNReal ComplexOrder Matrix
noncomputable section
universe u v
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Nonempty a]
variable [Fintype b] [DecidableEq b]

/-- Normalized input-first Choi state. -/
def channelChoiState (N : Channel a b) : State (a × b) :=
  ((Channel.idChannel a).prod N).applyState
    (State.maximallyEntangled (Equiv.refl a))

/-- The normalization is the inverse input dimension. -/
theorem channelChoiState_matrix (N : Channel a b) :
    (channelChoiState N).matrix =
      (Fintype.card a : ℂ)⁻¹ • MatrixMap.choi N.map := by
  have hc : (Real.sqrt (Fintype.card a : ℝ) : ℂ) ^ 2 =
      (Fintype.card a : ℂ) := by
    exact_mod_cast Real.sq_sqrt (Nat.cast_nonneg (Fintype.card a))
  have hb : (State.maximallyEntangled (Equiv.refl a)).matrix =
      (Fintype.card a : ℂ)⁻¹ • MatrixMap.choi (LinearMap.id : MatrixMap a a) := by
    ext ⟨i,j⟩ ⟨k,l⟩
    simp only [State.maximallyEntangled_matrix, PureVector.state_matrix_apply,
      PureVector.maximallyEntangled_amp, Equiv.refl_apply, Matrix.smul_apply,
      smul_eq_mul, MatrixMap.choi, LinearMap.id_apply, Matrix.single_apply]
    by_cases hij : i = j <;> by_cases hkl : k = l <;> simp [hij, hkl]
    rw [← mul_inv, ← pow_two, hc]
  change MatrixMap.kron (Channel.idChannel a).map N.map
    (State.maximallyEntangled (Equiv.refl a)).matrix = _
  rw [hb, map_smul]
  congr 1
  ext ⟨i,j⟩ ⟨k,l⟩
  simp [MatrixMap.kron, Channel.idChannel, MatrixMap.ofKraus,
    MatrixMap.choi, Matrix.single_apply, ite_and]

/-- The explicitly evaluated AD state is the channel's actual Choi state. -/
theorem channelChoiState_amplitudeDamping
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    channelChoiState (amplitudeDamping p hp0 hp1) = choiState p hp0 hp1 := by
  apply State.ext
  rw [channelChoiState_matrix, choiState_matrix_eq]
  ext ⟨i,j⟩ ⟨k,l⟩
  change (Fintype.card Qubit : ℂ)⁻¹ *
    ((amplitudeDamping p hp0 hp1).map (Matrix.single i k 1)) j l =
      choiEntries p (i,j) (k,l)
  rw [amplitudeDamping_map_eq]
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    norm_num [Matrix.single_apply, choiEntries] <;> ring

/-- The AD Choi formation formula needs no Wootters hypothesis. -/
theorem choiState_entanglementOfFormation_eq_binaryEntropy_unconditional
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementOfFormation (choiState p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  apply le_antisymm
  · exact choiState_entanglementOfFormation_le_branchCost p hp0 hp1
  · have h := entanglementOfFormation_ge_entanglementCurve
      (choiState p hp0 hp1) (choiState_matrix_01_01 p hp0 hp1)
    rw [choiState_matrix_00_11 p hp0 hp1,
      Complex.norm_of_nonneg (by positivity : 0 ≤ Real.sqrt (1-p) / 2),
      show 2 * (Real.sqrt (1-p) / 2) = Real.sqrt (1-p) by ring,
      entanglementCurve_sqrt_one_sub p hp1] at h
    exact h
end
end AmplitudeDamping
