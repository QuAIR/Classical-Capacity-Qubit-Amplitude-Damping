import AmplitudeDamping.Triangular.ScalarCompression

/-!
# Boundary continuity for scalar entropy compression

This module extends the strictly-positive scalar perspective argument to the
semidefinite boundary.  The first ingredient is continuity of spectral entropy
along an arbitrary continuous path of positive semidefinite matrices.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Topology
  Matrix.Norms.L2Operator

namespace AmplitudeDamping

open QIT
open Filter

noncomputable section

/-- Local completion of Lean-QIT's finite-matrix non-unital `CStarAlgebra`
instance, needed only to invoke mathlib's continuity theorem for the continuous
functional calculus. -/
noncomputable local instance instCMatrixCStarAlgebraForEntropyContinuity
    (d : Type) [Fintype d] [DecidableEq d] :
    CStarAlgebra (Matrix d d ℂ) := {}

/-- Spectral entropy varies continuously along a continuous path of positive
semidefinite matrices. -/
theorem continuous_psdEntropy_along
    {X d : Type} [TopologicalSpace X]
    [Fintype d] [DecidableEq d] [Nonempty d]
    (A : X → Matrix d d ℂ) (hA : Continuous A)
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
    simpa [Metric.mem_closedBall, Real.dist_0_eq_abs] using
      (hynorm.trans hx.le)
  rw [show (fun x => psdEntropy (A x) (hpsd x)) =
      (fun x => ((cfc psdEntropyCfcScalar (A x)).trace).re) by
    funext x
    exact psdEntropy_eq_cfc_trace (A x) (hpsd x)]
  fun_prop

/-- Canonical nonnegative truncation of a real scalar. -/
def nonnegativePart (x : ℝ) : ℝ := max x 0

theorem nonnegativePart_nonneg (x : ℝ) : 0 ≤ nonnegativePart x := by
  exact le_max_right x 0

theorem continuous_nonnegativePart : Continuous nonnegativePart := by
  unfold nonnegativePart
  fun_prop

/-- A totalized scalar entropy defect.  On the nonnegative octant it is the
ordinary scalar defect, while outside that octant each coordinate is clamped
to zero.  Totalization removes proof arguments from continuity statements. -/
def scalarEntropyDefectClamped (p q r : ℝ) : ℝ :=
  scalarEntropyDefect (nonnegativePart p) (nonnegativePart q)
    (nonnegativePart r) (nonnegativePart_nonneg p)
    (nonnegativePart_nonneg q) (nonnegativePart_nonneg r)

/-- The totalized scalar defect agrees with the original one on nonnegative
arguments. -/
theorem scalarEntropyDefectClamped_eq
    (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    scalarEntropyDefectClamped p q r =
      scalarEntropyDefect p q r hp hq hr := by
  simp only [scalarEntropyDefectClamped, nonnegativePart,
    max_eq_left hp, max_eq_left hq, max_eq_left hr]

/-- For fixed outer arguments, the totalized scalar entropy defect is
continuous in its middle argument, including at zero. -/
theorem continuous_scalarEntropyDefectClamped_middle (p r : ℝ) :
    Continuous fun q => scalarEntropyDefectClamped p q r := by
  let pp : ℝ := nonnegativePart p
  let rr : ℝ := nonnegativePart r
  let qq : ℝ → ℝ := fun q => nonnegativePart q
  have hpp : 0 ≤ pp := nonnegativePart_nonneg p
  have hrr : 0 ≤ rr := nonnegativePart_nonneg r
  have hqq : ∀ q, 0 ≤ qq q := fun q => nonnegativePart_nonneg q
  have hqqcont : Continuous qq := by
    simpa [qq] using continuous_nonnegativePart
  have hscalar (f : ℝ → ℝ) (hf : Continuous f) :
      Continuous fun x => scalarMatrix (f x) := by
    unfold scalarMatrix
    fun_prop
  have hblock : Continuous fun q => scalarCouplingBlock pp (qq q) rr := by
    unfold scalarCouplingBlock
    fun_prop (disch := assumption)
  have hblockEntropy : Continuous fun q =>
      psdEntropy (scalarCouplingBlock pp (qq q) rr)
        (scalarCouplingBlock_posSemidef pp (qq q) rr hpp (hqq q) hrr) :=
    continuous_psdEntropy_along _ hblock fun q =>
      scalarCouplingBlock_posSemidef pp (qq q) rr hpp (hqq q) hrr
  have hqEntropy : Continuous fun q =>
      psdEntropy (scalarMatrix (qq q))
        (scalarMatrix_posSemidef (qq q) (hqq q)) :=
    continuous_psdEntropy_along _
      (hscalar qq continuous_nonnegativePart) fun q =>
        scalarMatrix_posSemidef (qq q) (hqq q)
  have hpEntropy : Continuous fun _q : ℝ =>
      psdEntropy (scalarMatrix pp) (scalarMatrix_posSemidef pp hpp) :=
    continuous_const
  have hrEntropy : Continuous fun _q : ℝ =>
      psdEntropy (scalarMatrix rr) (scalarMatrix_posSemidef rr hrr) :=
    continuous_const
  have hfun : (fun q => scalarEntropyDefectClamped p q r) = (fun q =>
      psdEntropy (scalarCouplingBlock pp (qq q) rr)
          (scalarCouplingBlock_posSemidef pp (qq q) rr hpp (hqq q) hrr) -
        psdEntropy (scalarMatrix pp) (scalarMatrix_posSemidef pp hpp) -
        psdEntropy (scalarMatrix (qq q))
          (scalarMatrix_posSemidef (qq q) (hqq q)) -
        psdEntropy (scalarMatrix rr) (scalarMatrix_posSemidef rr hrr)) := by
    funext q
    unfold scalarEntropyDefectClamped scalarEntropyDefect entropyDefect
    let hZ := entropyCoupling_posSemidef
      (scalarMatrix pp) (scalarMatrix (qq q)) (scalarMatrix rr)
      (scalarMatrix_posSemidef pp hpp)
      (scalarMatrix_posSemidef (qq q) (hqq q))
      (scalarMatrix_posSemidef rr hrr)
    change psdEntropy
        (entropyCoupling (scalarMatrix pp) (scalarMatrix (qq q))
          (scalarMatrix rr)) hZ - _ - _ - _ = _
    have hcoupling : psdEntropy
        (entropyCoupling (scalarMatrix pp) (scalarMatrix (qq q))
          (scalarMatrix rr)) hZ =
        psdEntropy (scalarCouplingBlock pp (qq q) rr)
          (scalarCouplingBlock_posSemidef pp (qq q) rr hpp (hqq q) hrr) := by
      exact psdEntropy_congr
        (scalarCouplingBlock_eq_entropyCoupling pp (qq q) rr
          (hqq q) hrr).symm _ _
    rw [hcoupling]
  rw [hfun]
  exact (((hblockEntropy.sub hpEntropy).sub hqEntropy).sub hrEntropy)

/-- Scalar perspective Jensen inequality on the closed nonnegative octant.
The proof perturbs every middle coordinate by `1/(n+1)`, applies the strictly
positive theorem, and passes to the limit using boundary continuity. -/
theorem scalarEntropyDefect_sum_le
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p q r : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i) :
    scalarEntropyDefect (∑ i, p i) (∑ i, q i) (∑ i, r i)
        (Finset.sum_nonneg fun i _ => hp i)
        (Finset.sum_nonneg fun i _ => hq i)
        (Finset.sum_nonneg fun i _ => hr i) ≤
      ∑ i, scalarEntropyDefect (p i) (q i) (r i)
        (hp i) (hq i) (hr i) := by
  classical
  let ps : ℝ := ∑ i, p i
  let qs : ℝ := ∑ i, q i
  let rs : ℝ := ∑ i, r i
  let δ : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  let lhs : ℝ → ℝ := fun t =>
    scalarEntropyDefectClamped ps
      (qs + (Fintype.card ι : ℝ) * t) rs
  let rhs : ℝ → ℝ := fun t =>
    ∑ i, scalarEntropyDefectClamped (p i) (q i + t) (r i)
  have hps : 0 ≤ ps := Finset.sum_nonneg fun i _ => hp i
  have hqs : 0 ≤ qs := Finset.sum_nonneg fun i _ => hq i
  have hrs : 0 ≤ rs := Finset.sum_nonneg fun i _ => hr i
  have hδpos : ∀ n, 0 < δ n := by
    intro n
    dsimp [δ]
    positivity
  have hδ : Tendsto δ atTop (𝓝 0) := by
    simpa [δ] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hlhs : Continuous lhs := by
    unfold lhs
    exact (continuous_scalarEntropyDefectClamped_middle ps rs).comp
      (continuous_const.add (continuous_const.mul continuous_id))
  have hrhs : Continuous rhs := by
    unfold rhs
    apply continuous_finsetSum
    intro i _
    exact (continuous_scalarEntropyDefectClamped_middle (p i) (r i)).comp
      (continuous_const.add continuous_id)
  have hineq : ∀ n, lhs (δ n) ≤ rhs (δ n) := by
    intro n
    have hqδ : ∀ i, 0 < q i + δ n := fun i =>
      add_pos_of_nonneg_of_pos (hq i) (hδpos n)
    have hraw := scalarEntropyDefect_sum_le_of_middle_pos
      p (fun i => q i + δ n) r hp hqδ hr
    have hqsum : (∑ i, (q i + δ n)) =
        qs + (Fintype.card ι : ℝ) * δ n := by
      simp [qs, Finset.sum_add_distrib, nsmul_eq_mul]
    unfold lhs rhs
    rw [scalarEntropyDefectClamped_eq ps
      (qs + (Fintype.card ι : ℝ) * δ n) rs hps
      (add_nonneg hqs (mul_nonneg (Nat.cast_nonneg _) (hδpos n).le)) hrs]
    simp_rw [scalarEntropyDefectClamped_eq (p := p _) (q := q _ + δ n)
      (r := r _) (hp _) (hqδ _).le (hr _)]
    simpa [ps, rs, hqsum] using hraw
  have hlhsT : Tendsto (lhs ∘ δ) atTop (𝓝 (lhs 0)) :=
    (show Tendsto lhs (𝓝 0) (𝓝 (lhs 0)) from hlhs.continuousAt).comp hδ
  have hrhsT : Tendsto (rhs ∘ δ) atTop (𝓝 (rhs 0)) :=
    (show Tendsto rhs (𝓝 0) (𝓝 (rhs 0)) from hrhs.continuousAt).comp hδ
  have hlimit : lhs 0 ≤ rhs 0 :=
    le_of_tendsto_of_tendsto' hlhsT hrhsT fun n => hineq n
  unfold lhs rhs at hlimit
  simp only [mul_zero, add_zero] at hlimit
  rw [scalarEntropyDefectClamped_eq ps qs rs hps hqs hrs] at hlimit
  have hcoord (i : ι) :
      scalarEntropyDefectClamped (p i) (q i) (r i) =
        scalarEntropyDefect (p i) (q i) (r i) (hp i) (hq i) (hr i) :=
    scalarEntropyDefectClamped_eq (p i) (q i) (r i)
      (hp i) (hq i) (hr i)
  simp_rw [hcoord] at hlimit
  simpa [ps, qs, rs] using hlimit

end

end AmplitudeDamping
