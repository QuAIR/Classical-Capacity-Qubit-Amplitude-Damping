import AmplitudeDamping.RelativeEntropyEquality

open scoped BigOperators ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT Matrix
noncomputable section
universe u
variable {a : Type u} [Fintype a] [DecidableEq a]

/-- A spectral rank-one measurement reads the diagonal in its eigenbasis. -/
theorem spectral_effect_trace (M X : CMatrix a) (hM : M.IsHermitian) (i : a) :
    (X * (ProjectiveMeasurement.ofHermitianEigenbasis M hM).effects i).trace =
      (star (hM.eigenvectorUnitary : CMatrix a) * X *
        (hM.eigenvectorUnitary : CMatrix a)) i i := by
  rw [ProjectiveMeasurement.ofHermitianEigenbasis_effects]
  rw [← Matrix.mul_assoc, Matrix.trace_mul_comm, ← Matrix.mul_assoc,
    ← Matrix.mul_assoc]
  simp [Matrix.trace, Matrix.mul_diagonal]

/-- Every outcome of a spectral rank-one measurement has positive weight on a
faithful input. -/
theorem spectral_effect_trace_pos (M : CMatrix a) (hM : M.IsHermitian)
    (σ : State a) (hσ : σ.matrix.PosDef) (i : a) :
    0 < (σ.matrix * (ProjectiveMeasurement.ofHermitianEigenbasis M hM).effects i).trace.re := by
  rw [spectral_effect_trace]
  have hpos : (star (hM.eigenvectorUnitary : CMatrix a) * σ.matrix *
      (hM.eigenvectorUnitary : CMatrix a)).PosDef :=
    (Matrix.IsUnit.posDef_star_left_conjugate_iff
      (Unitary.isUnit_coe : IsUnit (hM.eigenvectorUnitary : CMatrix a))).mpr hσ
  exact (Complex.lt_def.mp hpos.diag_pos).1

theorem spectral_measure_state_diagonal (M : CMatrix a) (hM : M.IsHermitian)
    (ρ : State a) :
    ((Channel.measure (ProjectiveMeasurement.ofHermitianEigenbasis M hM).toPOVM).applyState ρ).matrix =
      diagonal (fun i => (((ρ.matrix *
        (ProjectiveMeasurement.ofHermitianEigenbasis M hM).effects i).trace.re : ℝ) : ℂ)) := by
  change (Channel.measure _).map ρ.matrix = _
  rw [Channel.measure_map_state_diagonal]
  apply congrArg diagonal
  funext i
  have hnonneg := ((Channel.measure
    (ProjectiveMeasurement.ofHermitianEigenbasis M hM).toPOVM).applyState ρ).pos.diag_nonneg (i := i)
  change 0 ≤ ((Channel.measure _).map ρ.matrix) i i at hnonneg
  rw [Channel.measure_map_state_diagonal, Matrix.diagonal_apply_eq] at hnonneg
  exact Complex.ext rfl hnonneg.2.symm

/-- Measuring in the eigenbasis of a state difference retains enough information
to distinguish those two states. -/
theorem spectral_measure_difference_injective (ρ σ : State a)
    (hM : (ρ.matrix - σ.matrix).IsHermitian)
    (heq : (Channel.measure
        (ProjectiveMeasurement.ofHermitianEigenbasis (ρ.matrix - σ.matrix) hM).toPOVM).applyState ρ =
      (Channel.measure
        (ProjectiveMeasurement.ofHermitianEigenbasis (ρ.matrix - σ.matrix) hM).toPOVM).applyState σ) :
    ρ = σ := by
  let P := ProjectiveMeasurement.ofHermitianEigenbasis (ρ.matrix - σ.matrix) hM
  have htrace (i : a) : (P.effects i).trace = 1 := by
    change ((ProjectiveMeasurement.ofHermitianEigenbasis _ hM).effects i).trace = 1
    rw [ProjectiveMeasurement.ofHermitianEigenbasis_effects, Matrix.trace_mul_cycle,
      Unitary.coe_star_mul_self, Matrix.one_mul]
    simp [Matrix.trace]
  have hzero (i : a) : ((ρ.matrix - σ.matrix) * P.effects i).trace = 0 := by
    have he := congrArg (fun τ : State a => τ.matrix i i) heq
    change ((Channel.measure P.toPOVM).map ρ.matrix) i i =
      ((Channel.measure P.toPOVM).map σ.matrix) i i at he
    rw [Channel.measure_map_state_diagonal, Channel.measure_map_state_diagonal] at he
    simpa [Matrix.sub_mul, Matrix.trace_sub, P] using sub_eq_zero.mpr he
  have heigen : hM.eigenvalues = 0 := by
    funext i
    have he := hzero i
    change ((ρ.matrix - σ.matrix) *
      (ProjectiveMeasurement.ofHermitianEigenbasis _ hM).effects i).trace = 0 at he
    rw [ProjectiveMeasurement.ofHermitianEigenbasis_mul_effect,
      Matrix.trace_smul] at he
    change (hM.eigenvalues i : ℂ) • (P.effects i).trace = 0 at he
    rw [htrace] at he
    simpa using he
  apply State.ext
  exact sub_eq_zero.mp (hM.eigenvalues_eq_zero_iff.mp heigen)

/-- Relative entropy with a faithful reference vanishes only for identical
states. -/
theorem faithful_relativeEntropy_eq_zero_imp_eq (ρ σ : State a)
    (hσ : σ.matrix.PosDef) (hz : ρ.relativeEntropy σ = 0) : ρ = σ := by
  let M := ρ.matrix - σ.matrix
  have hM : M.IsHermitian := ρ.pos.isHermitian.sub σ.pos.isHermitian
  let P := ProjectiveMeasurement.ofHermitianEigenbasis M hM
  let Φ := Channel.measure P.toPOVM
  have hdpi : (Φ.applyState ρ).relativeEntropy (Φ.applyState σ) ≤ 0 := by
    exact (State.relativeEntropy_dataProcessing_channel_ge ρ σ Φ).trans_eq hz
  have heq : Φ.applyState ρ = Φ.applyState σ :=
    diagonal_states_eq_of_relativeEntropy_le_zero _ _
      (fun i => (ρ.matrix * P.effects i).trace.re)
      (fun i => (σ.matrix * P.effects i).trace.re)
      (spectral_measure_state_diagonal M hM ρ)
      (spectral_measure_state_diagonal M hM σ)
      (spectral_effect_trace_pos M hM σ hσ) hdpi
  exact spectral_measure_difference_injective ρ σ hM heq

end
end AmplitudeDamping
