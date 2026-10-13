import AmplitudeDamping.ConvexRoof
import AmplitudeDamping.CompactConvexHull
import QIT.States.Topology

/-! # Attainment of finite pure-state roofs with continuous costs -/

open scoped BigOperators NNReal ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT
noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

/-- Real scalar form of a finite pure ensemble's average matrix. -/
theorem PureDecomposition.averageState_matrix_real (E : PureDecomposition a) :
    E.averageState.matrix = ∑ i, (E.probs i : ℝ) • (E.vectors i).state.matrix := by
  change (∑ i, (E.probs i : ℂ) • (E.vectors i).state.matrix) = _
  apply Finset.sum_congr rfl
  intro i _
  ext x y
  simp [Matrix.smul_apply, Complex.real_smul]

/-- A continuous pure-state cost attains its finite convex roof, with positive
weights. No bound on ensemble cardinality is imposed in the definition. -/
theorem exists_minimal_pureDecomposition (f : PureVector a → ℝ) (hf : Continuous f)
    (ρ : State a) :
    ∃ E : PureDecomposition a, E.averageState = ρ ∧
      (∀ i, 0 < (E.probs i : ℝ)) ∧
      ∀ D : PureDecomposition a, D.averageState = ρ →
        (∑ i, (E.probs i : ℝ) * f (E.vectors i)) ≤
          ∑ i, (D.probs i : ℝ) * f (D.vectors i) := by
  classical
  let g : PureVector a → (Matrix a a ℂ) × ℝ := fun ψ => (ψ.state.matrix, f ψ)
  have hg : Continuous g := (State.continuous_matrix.comp PureVector.state_continuous).prodMk hf
  let C := convexHull ℝ (Set.range g)
  have hc : IsCompact C := isCompact_convexHull_of_isCompact (isCompact_range hg)
  have hmem (E : PureDecomposition a) :
      (E.averageState.matrix, ∑ i, (E.probs i : ℝ) * f (E.vectors i)) ∈ C := by
    have hw : ∑ i, (E.probs i : ℝ) = 1 := by exact_mod_cast E.weights_sum
    have h := (convex_convexHull ℝ (Set.range g)).sum_mem
      (fun i (_ : i ∈ Finset.univ) => NNReal.coe_nonneg (E.probs i)) hw
      (fun i (_ : i ∈ Finset.univ) => subset_convexHull ℝ (Set.range g)
        (Set.mem_range_self (E.vectors i)))
    have heq : (∑ i, (E.probs i : ℝ) • g (E.vectors i)) =
        (E.averageState.matrix, ∑ i, (E.probs i : ℝ) * f (E.vectors i)) := by
      apply Prod.ext
      · simpa only [Prod.fst_sum, Prod.smul_fst, g] using E.averageState_matrix_real.symm
      · simp only [Prod.snd_sum, Prod.smul_snd, g, smul_eq_mul]
    rwa [heq] at h
  let S := C ∩ {z | z.1 = ρ.matrix}
  have hs : IsCompact S := hc.inter_right (isClosed_eq continuous_fst continuous_const)
  have hsne : S.Nonempty := by
    let E := spectralPureDecomposition ρ
    refine ⟨_, hmem E, ?_⟩
    exact congrArg State.matrix (spectralPureDecomposition_averageState ρ)
  obtain ⟨z, hz, hmin⟩ := hs.exists_isMinOn hsne continuous_snd.continuousOn
  obtain ⟨ι, hι, v, w, hv, _, hwpos, hwone, hwz⟩ :=
    eq_pos_convex_span_of_mem_convexHull hz.1
  letI := hι
  choose ψ hψ using fun i => hv (Set.mem_range_self i)
  let J := PLift ι
  let p : J → ℝ≥0 := fun i => ⟨w i.down, (hwpos i.down).le⟩
  let q : J → PureVector a := fun i => ψ i.down
  have hp : ∑ i, p i = 1 := by
    apply NNReal.coe_injective
    push_cast
    exact (Equiv.plift.sum_comp w).trans hwone
  let E := PureDecomposition.ofFinite p hp q
  have hsum : (E.averageState.matrix, ∑ i, (E.probs i : ℝ) * f (E.vectors i)) = z := by
    have he : (E.averageState.matrix, ∑ i, (E.probs i : ℝ) * f (E.vectors i)) =
        ∑ i : J, (p i : ℝ) • g (q i) := by
      apply Prod.ext
      · rw [E.averageState_matrix_real]
        change (∑ k, (p ((Fintype.equivFin J).symm k) : ℝ) •
          (q ((Fintype.equivFin J).symm k)).state.matrix) = _
        rw [(Fintype.equivFin J).symm.sum_comp
          (fun i : J => (p i : ℝ) • (q i).state.matrix)]
        simp only [Prod.fst_sum, Prod.smul_fst, g]
      · change (∑ k, (p ((Fintype.equivFin J).symm k) : ℝ) *
          f (q ((Fintype.equivFin J).symm k))) = _
        rw [(Fintype.equivFin J).symm.sum_comp
          (fun i : J => (p i : ℝ) * f (q i))]
        simp only [Prod.snd_sum, Prod.smul_snd, g, smul_eq_mul]
    rw [he]
    change (∑ i : J, w i.down • g (ψ i.down)) = z
    simp_rw [hψ]
    exact (Equiv.plift.sum_comp (fun i => w i • v i)).trans hwz
  have havg : E.averageState = ρ := by
    apply State.ext
    exact (congrArg Prod.fst hsum).trans hz.2
  refine ⟨E, havg, fun i => hwpos ((Fintype.equivFin J).symm i).down, ?_⟩
  intro D hD
  have hDmem : (D.averageState.matrix, ∑ i, (D.probs i : ℝ) * f (D.vectors i)) ∈ S :=
    ⟨hmem D, congrArg State.matrix hD⟩
  have h := hmin hDmem
  change z.2 ≤ _ at h
  rwa [← congrArg Prod.snd hsum] at h

end
end AmplitudeDamping
