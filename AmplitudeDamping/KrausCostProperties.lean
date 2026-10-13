import AmplitudeDamping.KrausRepresentation
import AmplitudeDamping.Triangular.ScalarBoundary

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Topology
  Matrix.Norms.L2Operator
namespace AmplitudeDamping
open QIT Filter
noncomputable section
universe u v w x y
variable {a : Type u} {b : Type v} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b]

noncomputable local instance costCStarAlgebra (d : Type u)
    [Fintype d] [DecidableEq d] : CStarAlgebra (Matrix d d ℂ) := {}

/-- Continuity of unnormalized entropy, including the zero matrix. -/
theorem continuous_psdEntropy_along_univ
    {T : Type w} [TopologicalSpace T] [Nonempty b]
    (A : T → CMatrix b) (hA : Continuous A)
    (hpsd : ∀ x, (A x).PosSemidef) :
    Continuous fun x => psdEntropy (A x) (hpsd x) := by
  have hcfc : Continuous fun x => cfc psdEntropyCfcScalar (A x) := by
    refine hA.cfc
      (s := fun x => Metric.closedBall (0 : ℝ) (‖A x‖ + 1))
      psdEntropyCfcScalar (fun x => isCompact_closedBall _ _) ?_
      (fun _ => continuous_psdEntropyCfcScalar.continuousOn)
      (fun x => (hpsd x).isHermitian.isSelfAdjoint)
    intro x₀
    have hevent : ∀ᶠ x in 𝓝 x₀, ‖A x‖ < ‖A x₀‖ + 1 :=
      (continuous_norm.comp hA).continuousAt.eventually
        (Iio_mem_nhds (lt_add_one ‖A x₀‖))
    filter_upwards [hevent] with x hx y hy
    have hynorm : ‖y‖ ≤ ‖A x‖ := spectrum.norm_le_norm_of_mem hy
    simpa [Metric.mem_closedBall, Real.dist_0_eq_abs] using hynorm.trans hx.le
  rw [show (fun x => psdEntropy (A x) (hpsd x)) =
      (fun x => ((cfc psdEntropyCfcScalar (A x)).trace).re) by
    funext x
    exact psdEntropy_eq_cfc_trace (A x) (hpsd x)]
  fun_prop

theorem continuous_xlog2 : Continuous xlog2 := by
  have he : xlog2 = fun x : ℝ => x * Real.log x / Real.log 2 := by
    funext x
    unfold xlog2 log2
    split_ifs with h
    · simp [h]
    · ring
  rw [he]
  exact Real.continuous_mul_log.div_const _

/-- The entropy perspective is continuous along every continuous PSD family. -/
theorem continuous_entropyPerspective_along
    {T : Type w} [TopologicalSpace T] [Nonempty b]
    (A : T → CMatrix b) (hA : Continuous A)
    (hpsd : ∀ x, (A x).PosSemidef) :
    Continuous fun x => entropyPerspective (A x) (hpsd x) :=
  (continuous_psdEntropy_along_univ A hA hpsd).add
    (continuous_xlog2.comp (Complex.continuous_re.comp hA.matrix_trace))

theorem entropyPerspective_nonneg (X : CMatrix b) (hX : X.PosSemidef) :
    0 ≤ entropyPerspective X hX := by
  by_cases ht : X.trace.re = 0
  · have hz : X = 0 := (Matrix.PosSemidef.trace_eq_zero_iff hX).mp
      (Complex.ext ht (Matrix.PosSemidef.trace_nonneg hX).2.symm)
    subst X
    simp
  · rw [entropyPerspective_eq_weight_mul_entropy X hX ht]
    exact mul_nonneg (Matrix.PosSemidef.trace_nonneg hX).1
      (State.vonNeumann_nonneg _)

namespace EntropyInstrument
variable {ι : Type x} [Fintype ι]

open Classical in
def costMatrix (F : EntropyInstrument a b ι) (X : CMatrix a) : ℝ :=
  if hX : X.PosSemidef then
    ∑ i, entropyPerspective (F.branch i X)
      (MatrixMap.isCompletelyPositive_mapsPositive _ (F.cp i) _ hX)
  else 0

@[simp] theorem costMatrix_of_pos (F : EntropyInstrument a b ι)
    (X : CMatrix a) (hX : X.PosSemidef) :
    F.costMatrix X = ∑ i, entropyPerspective (F.branch i X)
      (MatrixMap.isCompletelyPositive_mapsPositive _ (F.cp i) _ hX) := by
  simp [costMatrix, hX]

@[simp] theorem costMatrix_state (F : EntropyInstrument a b ι) (ρ : State a) :
    F.costMatrix ρ.matrix = F.cost ρ := by simp [costMatrix, ρ.pos, cost]

theorem cost_nonneg (F : EntropyInstrument a b ι) (ρ : State a) : 0 ≤ F.cost ρ :=
  Finset.sum_nonneg fun _ _ => entropyPerspective_nonneg _ _

theorem continuous_cost [Nonempty b] (F : EntropyInstrument a b ι) :
    Continuous F.cost := by
  unfold cost
  apply continuous_finsetSum
  intro i _
  exact continuous_entropyPerspective_along _
    ((F.branch i).continuous_of_finiteDimensional.comp State.continuous_matrix) _

theorem continuousOn_costMatrix [Nonempty b] (F : EntropyInstrument a b ι) :
    ContinuousOn F.costMatrix (State.stateMatrixSet a) := by
  rw [continuousOn_iff_continuous_restrict]
  have he : (State.stateMatrixSet a).restrict F.costMatrix =
      fun X : State.stateMatrixSet a => F.cost ⟨X.1, X.2.1, X.2.2⟩ := by
    funext X
    exact F.costMatrix_state ⟨X.1, X.2.1, X.2.2⟩
  rw [he]
  apply F.continuous_cost.comp
  rw [continuous_induced_rng]
  exact continuous_subtype_val

/-- Homogeneity and superadditivity give cost concavity directly on matrices. -/
theorem costMatrix_combo_ge (F : EntropyInstrument a b ι)
    (X Y : CMatrix a) (hX : X.PosSemidef) (hY : Y.PosSemidef)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) :
    p * F.costMatrix X + q * F.costMatrix Y ≤
      F.costMatrix ((p : ℂ) • X + (q : ℂ) • Y) := by
  rw [costMatrix_of_pos _ _ hX, costMatrix_of_pos _ _ hY,
    costMatrix_of_pos _ _ ((hX.smul (by exact_mod_cast hp)).add
      (hY.smul (by exact_mod_cast hq))), Finset.mul_sum, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  apply Finset.sum_le_sum
  intro i _
  have hx := MatrixMap.isCompletelyPositive_mapsPositive _ (F.cp i) _ hX
  have hy := MatrixMap.isCompletelyPositive_mapsPositive _ (F.cp i) _ hY
  have h := entropyPerspective_add_ge ((p : ℂ) • F.branch i X)
    ((q : ℂ) • F.branch i Y) (hx.smul (by exact_mod_cast hp))
    (hy.smul (by exact_mod_cast hq))
  rw [entropyPerspective_smul p hp, entropyPerspective_smul q hq] at h
  simpa only [map_add, map_smul] using h

theorem cost_combo_ge (F : EntropyInstrument a b ι) (ρ σ τ : State a)
    (p q : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q)
    (hτ : τ.matrix = (p : ℂ) • ρ.matrix + (q : ℂ) • σ.matrix) :
    p * F.cost ρ + q * F.cost σ ≤ F.cost τ := by
  simpa only [← hτ, costMatrix_state] using
    F.costMatrix_combo_ge ρ.matrix σ.matrix ρ.pos σ.pos p q hp hq

theorem concaveOn_costMatrix (F : EntropyInstrument a b ι) :
    ConcaveOn ℝ (State.stateMatrixSet a) F.costMatrix := by
  constructor
  · intro X hX Y hY p q hp hq hpq
    constructor
    · exact (hX.1.smul hp).add (hY.1.smul hq)
    · simp only [Matrix.trace_add, Matrix.trace_smul, hX.2, hY.2,
        Complex.real_smul, mul_one, ← Complex.ofReal_add, hpq, Complex.ofReal_one]
  · intro X hX Y hY p q hp hq _
    have hs (r : ℝ) (Z : CMatrix a) : r • Z = (r : ℂ) • Z := by
      ext i j
      exact Complex.real_smul
    simpa only [hs, smul_eq_mul] using
      F.costMatrix_combo_ge X Y hX.1 hY.1 p q hp hq

end EntropyInstrument

/-- A finite random choice of a Kraus representation, with the choice retained. -/
def mixedKraus {J : Type w} [Fintype J] {I : J → Type x}
    [∀ j, Fintype (I j)] (w : J → ℝ)
    (K : ∀ j, I j → Matrix b a ℂ) : (Σ j, I j) → Matrix b a ℂ :=
  fun z => (Real.sqrt (w z.1) : ℂ) • K z.1 z.2

theorem mixedKraus_branch {J : Type w} [Fintype J] {I : J → Type x}
    [∀ j, Fintype (I j)] (w : J → ℝ) (hw : ∀ j, 0 ≤ w j)
    (K : ∀ j, I j → Matrix b a ℂ) (z : Σ j, I j) (X : CMatrix a) :
    MatrixMap.ofKraus (fun _ : Unit => mixedKraus w K z) X =
      (w z.1 : ℂ) • MatrixMap.ofKraus (fun _ : Unit => K z.1 z.2) X := by
  simp [MatrixMap.ofKraus, mixedKraus, Matrix.conjTranspose_smul,
    Matrix.smul_mul, Matrix.mul_smul, smul_smul, Real.mul_self_sqrt (hw z.1)]

theorem mixedKraus_represents {J : Type w} [Fintype J] {I : J → Type x}
    [∀ j, Fintype (I j)] (N : Channel a b) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hws : ∑ j, w j = 1)
    (K : ∀ j, I j → Matrix b a ℂ)
    (hK : ∀ j, MatrixMap.ofKraus (K j) = N.map) :
    MatrixMap.ofKraus (mixedKraus w K) = N.map := by
  classical
  ext X r s
  have hsum : ∑ j, (w j : ℂ) = 1 := by exact_mod_cast hws
  have he (j : J) : ∑ i, MatrixMap.ofKraus (fun _ : Unit => K j i) X = N.map X := by
    rw [← hK j]
    simp [MatrixMap.ofKraus]
  have hf : MatrixMap.ofKraus (mixedKraus w K) X =
      ∑ j, (w j : ℂ) • N.map X := by
    calc
      _ = ∑ z : Σ j, I j, MatrixMap.ofKraus (fun _ : Unit => mixedKraus w K z) X := by
        simp [MatrixMap.ofKraus]
      _ = ∑ j, ∑ i, (w j : ℂ) • MatrixMap.ofKraus (fun _ : Unit => K j i) X := by
        simp_rw [mixedKraus_branch w hw K]
        exact Fintype.sum_sigma _
      _ = _ := by simp_rw [← Finset.smul_sum, he]
  have hg : MatrixMap.ofKraus (mixedKraus w K) X = N.map X := by
    rw [hf, ← Finset.sum_smul, hsum, one_smul]
  exact congrFun (congrFun hg r) s

theorem mixedKraus_cost {J : Type w} [Fintype J] {I : J → Type x}
    [∀ j, Fintype (I j)] (N : Channel a b) (w : J → ℝ)
    (hw : ∀ j, 0 ≤ w j) (hws : ∑ j, w j = 1)
    (K : ∀ j, I j → Matrix b a ℂ)
    (hK : ∀ j, MatrixMap.ofKraus (K j) = N.map) (ρ : State a) :
    (krausEntropyInstrument N (mixedKraus w K)
      (mixedKraus_represents N w hw hws K hK)).cost ρ =
      ∑ j, w j * (krausEntropyInstrument N (K j) (hK j)).cost ρ := by
  classical
  unfold EntropyInstrument.cost
  simp only [krausEntropyInstrument]
  rw [Fintype.sum_sigma]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [entropyPerspective_congr (mixedKraus_branch w hw K ⟨j, i⟩ ρ.matrix) _
    ((MatrixMap.isCompletelyPositive_mapsPositive _
      (MatrixMap.ofKraus_completelyPositive _) _ ρ.pos).smul (by exact_mod_cast hw j))]
  exact entropyPerspective_smul (w j) (hw j) _ _

end
end AmplitudeDamping
