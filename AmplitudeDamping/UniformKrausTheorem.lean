import AmplitudeDamping.UniformMinimax
import AmplitudeDamping.KrausCostProperties
import AmplitudeDamping.KrausFromFormation

/-! # The finite uniform Kraus representation theorem

Pointwise near-optimal decompositions, continuity, concavity, compactness and
finite-dimensional minimax produce a single uniformly near-optimal Kraus family.
-/

open scoped BigOperators ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT
noncomputable section
universe u v w
variable {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b]

private structure FiniteKrausRepresentation (N : Channel a b) where
  card : ℕ
  kraus : Fin card → Matrix b a ℂ
  represents : MatrixMap.ofKraus kraus = N.map

/-- Reindexing a finite Kraus family preserves its representation and cost. -/
private theorem exists_fin_kraus_of_uniform_cost
    {ι : Type w} [Fintype ι] (N : Channel a b)
    (K : ι → Matrix b a ℂ) (hK : MatrixMap.ofKraus K = N.map) (C : ℝ)
    (hb : ∀ ρ : State a, (krausEntropyInstrument N K hK).cost ρ ≤ C) :
    ∃ (n : ℕ) (L : Fin n → Matrix b a ℂ) (hL : MatrixMap.ofKraus L = N.map),
      ∀ ρ : State a, (krausEntropyInstrument N L hL).cost ρ ≤ C := by
  classical
  let e := (Fintype.equivFin ι).symm
  let L : Fin (Fintype.card ι) → Matrix b a ℂ := fun i => K (e i)
  have hL : MatrixMap.ofKraus L = N.map := by
    rw [← hK]
    ext X j k
    simp only [MatrixMap.ofKraus, LinearMap.coe_mk, AddHom.coe_mk, Matrix.sum_apply]
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  refine ⟨Fintype.card ι, L, hL, fun ρ => ?_⟩
  have he : (krausEntropyInstrument N L hL).cost ρ =
      (krausEntropyInstrument N K hK).cost ρ := by
    unfold EntropyInstrument.cost
    exact Fintype.sum_equiv e _ _ (fun _ => rfl)
  exact he.trans_le (hb ρ)

/-- Every finite-dimensional channel has a single finite Kraus representation
whose entropy cost is within any positive tolerance of channel formation,
uniformly over all input states. -/
theorem uniformKrausRepresentation : UniformKrausRepresentation (a := a) (b := b) := by
  classical
  intro N δ hδ
  by_cases ha : Nonempty a
  · letI : Nonempty a := ha
    let ρ₀ : State a := State.maximallyMixed a
    letI : Nonempty b := (N.applyState ρ₀).nonempty
    let R := FiniteKrausRepresentation N
    let F : R → CMatrix a → ℝ := fun r =>
      (krausEntropyInstrument N r.kraus r.represents).costMatrix
    have hne : (State.stateMatrixSet a).Nonempty :=
      ⟨ρ₀.matrix, ρ₀.pos, ρ₀.trace_eq_one⟩
    have hc : Convex ℝ (State.stateMatrixSet a) :=
      (EntropyInstrument.concaveOn_costMatrix
        (krausEntropyInstrument N N.kraus N.map_eq_ofKraus.symm)).1
    have hg : ∀ X ∈ State.stateMatrixSet a,
        ∃ r : R, F r X < channelEntanglementOfFormation N + δ := by
      intro X hX
      let ρ : State a := ⟨X, hX.1, hX.2⟩
      obtain ⟨n, K, hK, hb⟩ := pointwise_exists_krausCost_le N ρ (δ / 2) (by positivity)
      refine ⟨⟨n, K, hK⟩, ?_⟩
      change (krausEntropyInstrument N K hK).costMatrix ρ.matrix < _
      rw [EntropyInstrument.costMatrix_state]
      linarith
    obtain ⟨s, weights, hw, hws, hu⟩ := UniformMinimax.exists_finite_mixture hne
      (State.stateMatrixSet_isCompact (a := a)) hc F
      (fun r => EntropyInstrument.continuousOn_costMatrix _)
      (fun r => EntropyInstrument.concaveOn_costMatrix _)
      (channelEntanglementOfFormation N + δ) hg
    let K : ∀ r : s, Fin r.val.card → Matrix b a ℂ := fun r => r.val.kraus
    have hK : ∀ r : s, MatrixMap.ofKraus (K r) = N.map := fun r => r.val.represents
    apply exists_fin_kraus_of_uniform_cost N (mixedKraus weights K)
      (mixedKraus_represents N weights hw hws K hK)
    intro ρ
    rw [mixedKraus_cost N weights hw hws K hK]
    have h := hu ρ.matrix ⟨ρ.pos, ρ.trace_eq_one⟩
    simpa only [F, EntropyInstrument.costMatrix_state] using h.le
  · apply exists_fin_kraus_of_uniform_cost N N.kraus N.map_eq_ofKraus.symm
    intro ρ
    exact (ha ρ.nonempty).elim

/-- The uniform representation theorem simultaneously for all ordinary finite dimensions. -/
theorem generalUniformKrausRepresentation : GeneralUniformKrausRepresentation := by
  intro a b _ _ _ _
  exact uniformKrausRepresentation

end
end AmplitudeDamping
