import AmplitudeDamping.Triangular.UnitaryPolar

/-! # Equality in the triangular entropy inequality

Strict skew-logdet convexity follows from an exact resolvent Frobenius-loss
identity. Strictness survives the improper entropy integral and identifies
the unique minimizer on each fixed-trace slice. The resulting triangular
equality characterization has no extra analytic assumptions.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder Kronecker
open Filter MeasureTheory
namespace AmplitudeDamping
open QIT
noncomputable section

lemma frobeniusSq_pos_of_ne_zero {d : Type} [Fintype d] [DecidableEq d]
    (E : Matrix d d ℂ) (hE : E ≠ 0) : 0 < frobeniusSq E := by
  refine lt_of_le_of_ne (frobeniusSq_nonneg E) ?_
  intro hz
  apply hE
  ext i j
  have hzero := hz.symm
  rw [frobeniusSq_eq_sum_normSq] at hzero
  have hi := (Finset.sum_eq_zero_iff_of_nonneg
    (fun k _ => Finset.sum_nonneg fun l _ => Complex.normSq_nonneg (E k l))).mp
      hzero i (Finset.mem_univ i)
  have hj := (Finset.sum_eq_zero_iff_of_nonneg
    (fun l _ => Complex.normSq_nonneg (E i l))).mp hi j (Finset.mem_univ j)
  exact Complex.normSq_eq_zero.mp hj

/-- The resolvent's lost Frobenius norm is the squared norm of `A C E`.
This gives strict contraction for invertible skew matrices. -/
lemma skew_resolvent_frobenius_loss {d : Type} [Fintype d] [DecidableEq d]
    (A E : Matrix d d ℂ) (hA : A.conjTranspose = -A) :
    frobeniusSq E - frobeniusSq ((1+A)⁻¹ * E) =
      frobeniusSq (A * (1+A)⁻¹ * E) := by
  let C := (1+A)⁻¹
  have hc : (1+A) * C = 1 := Matrix.mul_nonsing_inv _ (isUnit_det_one_add_skew A hA)
  have hgram : C.conjTranspose * C + (A*C).conjTranspose * (A*C) = 1 := by
    have hh : ((1+A)*C).conjTranspose * ((1+A)*C) = 1 := by rw [hc]; simp
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_add, Matrix.conjTranspose_one, hA] at hh
    rw [Matrix.conjTranspose_mul, hA]
    calc
      _ = C.conjTranspose * (1 + -A) * ((1+A)*C) := by noncomm_ring
      _ = 1 := hh
  have hf (X : Matrix d d ℂ) : frobeniusSq (X*E) =
      (E.conjTranspose * (X.conjTranspose * X) * E).trace.re := by
    unfold frobeniusSq
    rw [← Matrix.trace_mul_comm, Matrix.conjTranspose_mul]
    congr 2
    noncomm_ring
  have he : frobeniusSq E = (E.conjTranspose * E).trace.re := by
    unfold frobeniusSq
    rw [Matrix.trace_mul_comm]
  change frobeniusSq E - frobeniusSq (C*E) = frobeniusSq ((A*C)*E)
  rw [hf, hf, he]
  have h := congrArg (fun M : Matrix d d ℂ => (E.conjTranspose * M * E).trace.re) hgram
  simp only [Matrix.mul_add, Matrix.add_mul, Matrix.trace_add, Complex.add_re,
    Matrix.mul_one] at h
  linarith

lemma normalized_logDet_hessian_pos_of_skew {d : Type} [Fintype d] [DecidableEq d]
    (A E : Matrix d d ℂ) (hA : A.conjTranspose = -A) (hAu : IsUnit A) (hE : E ≠ 0) :
    0 < frobeniusSq E -
      ((((1+A)⁻¹ * E) * ((1+A)⁻¹ * E)).trace).re := by
  have hCu : IsUnit ((1+A)⁻¹) := by
    rw [Matrix.isUnit_iff_isUnit_det]
    rw [Matrix.det_nonsing_inv]
    simpa only [Ring.inverse_eq_inv] using (isUnit_det_one_add_skew A hA).inv
  have hACE : A*(1+A)⁻¹*E ≠ 0 := by
    intro hh
    apply hE
    exact (hAu.mul hCu).mul_right_injective (by simpa using hh)
  have hloss := skew_resolvent_frobenius_loss A E hA
  have hpos := frobeniusSq_pos_of_ne_zero _ hACE
  have habs := abs_trace_square_le_frobeniusSq ((1+A)⁻¹ * E)
  have hre := Complex.re_le_norm ((((1+A)⁻¹ * E) * ((1+A)⁻¹ * E)).trace)
  change _ ≤ Complex.abs _ at hre
  linarith

theorem logDet_hessian_pos_of_square_factor
    {n : Type} [Fintype n] [DecidableEq n]
    (S H J : Matrix n n ℂ)
    (hSdet : IsUnit S.det)
    (hS : S.conjTranspose = S)
    (hH : H.conjTranspose = H)
    (hJ : J.conjTranspose = -J) (hJu : IsUnit J) (hHne : H ≠ 0) :
    0 < ((((S * S)⁻¹ * H) * ((S * S)⁻¹ * H)).trace).re -
      (((((S * S + J)⁻¹ * H) * ((S * S + J)⁻¹ * H)).trace).re) := by
  let R : Matrix n n ℂ := S⁻¹
  let E : Matrix n n ℂ := R * H * R
  let A : Matrix n n ℂ := R * J * R
  let C : Matrix n n ℂ := (1 + A)⁻¹
  have hSR : S * R = 1 := Matrix.mul_nonsing_inv S hSdet
  have hRS : R * S = 1 := Matrix.nonsing_inv_mul S hSdet
  have hR : R.conjTranspose = R := by
    dsimp [R]
    exact Matrix.IsHermitian.inv hS
  have hE : E.conjTranspose = E := by
    dsimp [E]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hR, hH]
    noncomm_ring
  have hA : A.conjTranspose = -A := by
    dsimp [A]
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, hR, hJ]
    noncomm_ring
  have hSSdet : IsUnit (S * S).det := by
    rw [Matrix.det_mul]
    exact hSdet.mul hSdet
  have hBinv : (S * S)⁻¹ = R * R := by
    apply Matrix.right_inv_eq_right_inv (Matrix.mul_nonsing_inv (S * S) hSSdet)
    calc
      (S * S) * (R * R) = S * (S * R) * R := by noncomm_ring
      _ = 1 := by rw [hSR]; simp [hSR]
  have hDdet : IsUnit (1 + A).det := isUnit_det_one_add_skew A hA
  have hDinv : (1 + A) * C = 1 := Matrix.mul_nonsing_inv (1 + A) hDdet
  have hfactor : S * (1 + A) * S = S * S + J := by
    dsimp [A]
    calc
      S * (1 + R * J * R) * S = S * S + (S * R) * J * (R * S) := by
        noncomm_ring
      _ = S * S + J := by rw [hSR, hRS]; simp
  have hshiftDet : IsUnit (S * S + J).det := by
    rw [← hfactor, Matrix.det_mul, Matrix.det_mul]
    exact (hSdet.mul hDdet).mul hSdet
  have hShiftInv : (S * S + J)⁻¹ = R * C * R := by
    apply Matrix.right_inv_eq_right_inv
      (Matrix.mul_nonsing_inv (S * S + J) hshiftDet)
    rw [← hfactor]
    calc
      (S * (1 + A) * S) * (R * C * R) =
          S * (1 + A) * (S * R) * C * R := by
        noncomm_ring
      _ = S * ((1 + A) * C) * R := by rw [hSR]; simp; noncomm_ring
      _ = S * R := by rw [hDinv]; simp
      _ = 1 := hSR
  have hbaseTrace :
      (((S * S)⁻¹ * H) * ((S * S)⁻¹ * H)).trace =
        (E * E).trace := by
    rw [hBinv]
    dsimp [E]
    calc
      ((R * R * H) * (R * R * H)).trace =
          (R * (R * H * R * R * H)).trace := by
        congr 1
        noncomm_ring
      _ = ((R * H * R * R * H) * R).trace :=
        Matrix.trace_mul_comm R (R * H * R * R * H)
      _ = ((R * H * R) * (R * H * R)).trace := by
        congr 1
        noncomm_ring
  have hshiftTrace :
      ((((S * S + J)⁻¹ * H) * ((S * S + J)⁻¹ * H)).trace) =
        ((C * E) * (C * E)).trace := by
    rw [hShiftInv]
    dsimp [E]
    calc
      ((R * C * R * H) * (R * C * R * H)).trace =
          (R * (C * R * H * R * C * R * H)).trace := by
        congr 1
        noncomm_ring
      _ = ((C * R * H * R * C * R * H) * R).trace :=
        Matrix.trace_mul_comm R (C * R * H * R * C * R * H)
      _ = ((C * (R * H * R)) * (C * (R * H * R))).trace := by
        congr 1
        noncomm_ring
  have hRu : IsUnit R := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simpa [R, Matrix.det_nonsing_inv, Ring.inverse_eq_inv] using hSdet.inv
  have hAu : IsUnit A := (hRu.mul hJu).mul hRu
  have hEne : E ≠ 0 := by
    intro hh
    apply hHne
    have hh' := congrArg (fun X : Matrix n n ℂ => S * X * S) hh
    have he : S * E * S = H := by
      dsimp [E]
      calc
        _ = (S*R)*H*(R*S) := by noncomm_ring
        _ = H := by rw [hSR,hRS]; simp
    simpa only [he, Matrix.mul_zero, Matrix.zero_mul] using hh'
  have hnorm := normalized_logDet_hessian_pos_of_skew A E hA hAu hEne
  rw [hbaseTrace, hshiftTrace]
  have hfrob : frobeniusSq E = (E * E).trace.re := by
    unfold frobeniusSq
    rw [hE]
  rw [← hfrob]
  exact hnorm

/-- Pointwise positivity of the log-determinant Hessian for a positive
definite Hermitian base matrix, a Hermitian direction, and a skew-Hermitian
perturbation. -/
theorem logDet_hessian_pos_of_posDef
    {n : Type} [Fintype n] [DecidableEq n]
    (G H J : Matrix n n ℂ)
    (hG : G.PosDef)
    (hH : H.conjTranspose = H)
    (hJ : J.conjTranspose = -J) (hJu : IsUnit J) (hHne : H ≠ 0) :
    0 < (((G⁻¹ * H) * (G⁻¹ * H)).trace).re -
      (((((G + J)⁻¹ * H) * ((G + J)⁻¹ * H)).trace).re) := by
  let S : Matrix n n ℂ := QIT.psdSqrt G
  have hS : S.conjTranspose = S := (QIT.psdSqrt_isHermitian G).eq
  have hSS : S * S = G :=
    QIT.psdSqrt_mul_self_of_posSemidef hG.posSemidef
  have hSdet_ne : S.det ≠ 0 := by
    intro hzero
    have hGdet_ne : G.det ≠ 0 := hG.det_pos.ne'
    apply hGdet_ne
    rw [← hSS, Matrix.det_mul, hzero, zero_mul]
  have hSdet : IsUnit S.det := isUnit_iff_ne_zero.mpr hSdet_ne
  simpa [hSS] using
    logDet_hessian_pos_of_square_factor S H J hSdet hS hH hJ hJu hHne

theorem logDet_skew_increment_strictConvexOn_segment
    {n : Type} [Fintype n] [DecidableEq n]
    (G₀ G₁ J : Matrix n n ℂ)
    (hG₀ : G₀.PosDef) (hG₁ : G₁.PosDef)
    (hJ : J.conjTranspose = -J) (hJu : IsUnit J) (hne : G₀ ≠ G₁) :
    StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1)
      (fun t : ℝ ↦
        Real.log (Complex.abs (((G₀ + J) + (t : ℂ) • (G₁ - G₀)).det)) -
          Real.log (Complex.abs ((G₀ + (t : ℂ) • (G₁ - G₀)).det))) := by
  let H : Matrix n n ℂ := G₁ - G₀
  let P : ℝ → Matrix n n ℂ := fun t ↦ G₀ + (t : ℂ) • H
  let f : ℝ → ℝ := fun t ↦
    Real.log (Complex.abs (((G₀ + J) + (t : ℂ) • H).det)) -
      Real.log (Complex.abs ((G₀ + (t : ℂ) • H).det))
  let f' : ℝ → ℝ := fun t ↦
    ((((G₀ + J) + (t : ℂ) • H)⁻¹ * H).trace.re) -
      (((G₀ + (t : ℂ) • H)⁻¹ * H).trace.re)
  let f'' : ℝ → ℝ := fun t ↦
    ((((G₀ + (t : ℂ) • H)⁻¹ * H) *
      ((G₀ + (t : ℂ) • H)⁻¹ * H)).trace.re) -
      (((((G₀ + J) + (t : ℂ) • H)⁻¹ * H) *
        (((G₀ + J) + (t : ℂ) • H)⁻¹ * H)).trace.re)
  have hH : H.conjTranspose = H := by
    dsimp [H]
    rw [Matrix.conjTranspose_sub, hG₁.1.eq, hG₀.1.eq]
  have hP : ∀ t ∈ Set.Icc (0 : ℝ) 1, (P t).PosDef := by
    intro t ht
    have hc := Matrix.PosDef.convexCombination hG₁ hG₀ ht.1 ht.2
    convert hc using 1
    dsimp [P, H]
    ext i j
    simp
    ring
  have hdet₀ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsUnit (G₀ + (t : ℂ) • H).det := by
    intro t ht
    exact isUnit_iff_ne_zero.mpr (hP t ht).det_pos.ne'
  have hdet₁ : ∀ t ∈ Set.Icc (0 : ℝ) 1,
      IsUnit ((G₀ + J) + (t : ℂ) • H).det := by
    intro t ht
    have hu := isUnit_det_add_skew_of_posDef (P t) J (hP t ht) hJ
    simpa [P, add_assoc, add_left_comm, add_comm] using hu
  have hfderiv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f (f' t) t := by
    intro t ht
    exact (hasDerivAt_log_abs_det_affine (G₀ + J) H t (hdet₁ t ht)).sub
      (hasDerivAt_log_abs_det_affine G₀ H t (hdet₀ t ht))
  have hf'deriv : ∀ t ∈ Set.Icc (0 : ℝ) 1, HasDerivAt f' (f'' t) t := by
    intro t ht
    exact hasDerivAt_logDet_difference_firstDerivative
      (G₀ + J) G₀ H t (hdet₁ t ht) (hdet₀ t ht)
  have hf''pos : ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < f'' t := by
    intro t ht
    have hh := logDet_hessian_pos_of_posDef (P t) H J (hP t ht) hH hJ hJu
      (by intro hh; exact hne (sub_eq_zero.mp hh).symm)
    simpa [f'', P, add_assoc, add_left_comm, add_comm] using hh
  have hfconvex : StrictConvexOn ℝ (Set.Icc (0 : ℝ) 1) f := by
    apply strictConvexOn_of_deriv2_pos (convex_Icc (0 : ℝ) 1)
    · intro t ht
      exact (hfderiv t ht).continuousAt.continuousWithinAt
    · intro t ht
      have htIoo : t ∈ Set.Ioo (0:ℝ) 1 := by simpa [interior_Icc] using ht
      have ht' : t ∈ Set.Icc (0:ℝ) 1 := ⟨htIoo.1.le, htIoo.2.le⟩
      have heq : deriv f =ᶠ[nhds t] f' := by
        filter_upwards [isOpen_Ioo.mem_nhds htIoo] with y hy
        exact (hfderiv y ⟨hy.1.le,hy.2.le⟩).deriv
      have hh := (hf'deriv t ht').congr_of_eventuallyEq heq
      change 0 < deriv (deriv f) t
      rw [hh.deriv]
      exact hf''pos t ht'

  simpa [f, H] using hfconvex

/-- Invertible skew perturbations make the log-determinant increment strictly convex. -/
theorem skewLogDetIncrement_strictConvexOn_posDef
    {d : Type} [Fintype d] [DecidableEq d] (J : Matrix d d ℂ)
    (hJ : J.conjTranspose = -J) (hJgram : (J.conjTranspose * J).PosDef) :
    StrictConvexOn ℝ {G : Matrix d d ℂ | G.PosDef} (skewLogDetIncrement J) := by
  have hJu : IsUnit J := by
    rw [Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
    intro hz
    have hh := hJgram.det_pos.ne'
    apply hh
    rw [Matrix.det_mul, hz, mul_zero]
  refine ⟨(skewLogDetIncrement_convexOn_posDef J hJ).1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  have hseg := logDet_skew_increment_strictConvexOn_segment x y J hx hy hJ hJu hxy
  have hineq := hseg.2 (show (0:ℝ) ∈ Set.Icc 0 1 by norm_num)
    (show (1:ℝ) ∈ Set.Icc 0 1 by norm_num) (by norm_num : (0:ℝ)≠1) ha hb hab
  have ha_eq : a = 1-b := by linarith
  have hpath : x + b • (y-x) = a • x + b • y := by
    rw [ha_eq]
    module
  simpa [skewLogDetIncrement, smul_eq_mul, hpath, add_assoc,
    add_left_comm, add_comm] using hineq

lemma middleSkew_gram_posDef {d : Type} [Fintype d] [DecidableEq d]
    (s : ℝ) (hs : 0 < s) (Q : Matrix d d ℂ) (hQ : Q.PosDef) :
    ((middleSkew s Q).conjTranspose * middleSkew s Q).PosDef := by
  have heq : (middleSkew s Q).conjTranspose * middleSkew s Q =
      Matrix.fromBlocks (s • Q) 0 0 (s • Q) := by
    rw [middleSkew_skewHermitian]
    unfold middleSkew
    simp only [Matrix.fromBlocks_neg, Matrix.fromBlocks_multiply,
      neg_zero, neg_neg, Matrix.zero_mul, Matrix.mul_zero, zero_add, add_zero,
      neg_mul_neg, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [Real.mul_self_sqrt hs.le, psdSqrt_mul_self_of_posSemidef hQ.posSemidef]
    simp
  rw [heq]
  exact Matrix.fromBlocks_diagonal_posDef (hQ.smul hs) (hQ.smul hs)

lemma outerShift_injective {d : Type} [Fintype d] [DecidableEq d] (s : ℝ) :
    Function.Injective (fun PR : Matrix d d ℂ × Matrix d d ℂ => outerShift s PR.1 PR.2) := by
  intro x y h
  apply Prod.ext
  · have hh := congrArg (fun M : Matrix (Sum d d) (Sum d d) ℂ =>
      M.submatrix Sum.inl Sum.inl) h
    have hh' : x.1 + s • (1 : Matrix d d ℂ) = y.1 + s • 1 := hh
    exact add_right_cancel hh'
  · have hh := congrArg (fun M : Matrix (Sum d d) (Sum d d) ℂ =>
      M.submatrix Sum.inr Sum.inr) h
    have hh' : x.2 + s • (1 : Matrix d d ℂ) = y.2 + s • 1 := hh
    exact add_right_cancel hh'

/-- Full-rank middle matrices make the entropy integrand strictly convex. -/
theorem fixedMiddleEntropyIntegrand_strictConvexOn
    {d : Type} [Fintype d] [DecidableEq d]
    (s : ℝ) (hs : 0 < s) (Q : Matrix d d ℂ) (hQ : Q.PosDef) :
    StrictConvexOn ℝ
      {PR : Matrix d d ℂ × Matrix d d ℂ | PR.1.PosSemidef ∧ PR.2.PosSemidef}
      (fixedMiddleEntropyIntegrand s Q) := by
  have hlog : StrictConvexOn ℝ
      {PR : Matrix d d ℂ × Matrix d d ℂ | PR.1.PosSemidef ∧ PR.2.PosSemidef}
      (fixedMiddleLogDetIntegrand s Q) := by
    refine ⟨(fixedMiddleLogDetIntegrand_convexOn s hs Q).1, ?_⟩
    intro x hx y hy hxy a b ha hb hab
    have h := (skewLogDetIncrement_strictConvexOn_posDef (middleSkew s Q) (middleSkew_skewHermitian s Q)
      (middleSkew_gram_posDef s hs Q hQ)).2
        (outerShift_posDef s hs _ _ hx.1 hx.2)
        (outerShift_posDef s hs _ _ hy.1 hy.2)
        (fun h => hxy (outerShift_injective s h)) ha hb hab
    unfold fixedMiddleLogDetIntegrand
    change skewLogDetIncrement (middleSkew s Q)
      (outerShift s (a • x.1 + b • y.1) (a • x.2 + b • y.2)) < _
    rw [outerShift_convexCombination s x.1 y.1 x.2 y.2 a b hab]
    exact h
  simpa [fixedMiddleEntropyIntegrand, sub_eq_add_neg] using
    hlog.add_const (-Real.log (Complex.abs (1 + s⁻¹ • Q).det))

/-- Strictness survives the improper entropy integral: a fixed positive-window
Jensen gap is bounded above by the limiting gap. -/
theorem entropyDefectTotal_strictConvexOn
    {d : Type} [Fintype d] [DecidableEq d]
    (Q : Matrix d d ℂ) (hQ : Q.PosDef) :
    StrictConvexOn ℝ
      {PR : Matrix d d ℂ × Matrix d d ℂ | PR.1.PosSemidef ∧ PR.2.PosSemidef}
      (entropyDefectTotal Q hQ.posSemidef) := by
  refine ⟨(entropyDefectTotal_convexOn Q hQ.posSemidef).1, ?_⟩
  intro x hx y hy hxy a b ha hb hab
  change x.1.PosSemidef ∧ x.2.PosSemidef at hx
  change y.1.PosSemidef ∧ y.2.PosSemidef at hy
  let z := a • x + b • y
  have hz : z.1.PosSemidef ∧ z.2.PosSemidef :=
    ⟨(hx.1.smul ha.le).add (hy.1.smul hb.le),
      (hx.2.smul ha.le).add (hy.2.smul hb.le)⟩
  let gap (s : ℝ) := a * fixedMiddleEntropyIntegrand s Q x +
    b * fixedMiddleEntropyIntegrand s Q y - fixedMiddleEntropyIntegrand s Q z
  have hpos (s : ℝ) (hs : 0 < s) : 0 < gap s := by
    have h := (fixedMiddleEntropyIntegrand_strictConvexOn s hs Q hQ).2
      hx hy hxy ha hb hab
    simpa [gap, z, sub_pos, smul_eq_mul] using h
  have hint (L : ℝ) (hL : 0 ≤ L) : IntervalIntegrable gap volume 0 L :=
    (((intervalIntegrable_fixedMiddleEntropyIntegrand x.1 Q x.2 hx.1 hQ.posSemidef hx.2
      0 L le_rfl hL).const_mul a).add
      ((intervalIntegrable_fixedMiddleEntropyIntegrand y.1 Q y.2 hy.1 hQ.posSemidef hy.2
        0 L le_rfl hL).const_mul b)).sub
      (intervalIntegrable_fixedMiddleEntropyIntegrand z.1 Q z.2 hz.1 hQ.posSemidef hz.2
        0 L le_rfl hL)
  have hgap : 0 < ∫ s in (0 : ℝ)..1, gap s :=
    intervalIntegral.intervalIntegral_pos_of_pos_on (hint 1 zero_le_one)
      (fun s hs => hpos s hs.1) zero_lt_one
  have hlimX := tendsto_truncatedFixedMiddleEntropyIntegral x.1 Q x.2 hx.1 hQ.posSemidef hx.2
  have hlimY := tendsto_truncatedFixedMiddleEntropyIntegral y.1 Q y.2 hy.1 hQ.posSemidef hy.2
  have hlimZ := tendsto_truncatedFixedMiddleEntropyIntegral z.1 Q z.2 hz.1 hQ.posSemidef hz.2
  have hlim := ((hlimX.const_mul a).add (hlimY.const_mul b)).sub hlimZ
  have hevent : ∀ᶠ L : ℝ in atTop,
      (∫ s in (0 : ℝ)..1, gap s) ≤
        a * truncatedFixedMiddleEntropyIntegral 0 L Q x +
          b * truncatedFixedMiddleEntropyIntegral 0 L Q y -
            truncatedFixedMiddleEntropyIntegral 0 L Q z := by
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with L hL
    have hL0 : 0 ≤ L := zero_le_one.trans hL
    have hxint := intervalIntegrable_fixedMiddleEntropyIntegrand x.1 Q x.2 hx.1 hQ.posSemidef hx.2
      0 L le_rfl hL0
    have hyint := intervalIntegrable_fixedMiddleEntropyIntegrand y.1 Q y.2 hy.1 hQ.posSemidef hy.2
      0 L le_rfl hL0
    have hzint := intervalIntegrable_fixedMiddleEntropyIntegrand z.1 Q z.2 hz.1 hQ.posSemidef hz.2
      0 L le_rfl hL0
    have hmono : (∫ s in (0 : ℝ)..1, gap s) ≤ ∫ s in (0 : ℝ)..L, gap s := by
      apply intervalIntegral.integral_mono_interval le_rfl zero_le_one hL _ (hint L hL0)
      exact (ae_restrict_mem measurableSet_Ioc).mono fun s hs => (hpos s hs.1).le
    simpa only [gap, truncatedFixedMiddleEntropyIntegral,
      intervalIntegral.integral_sub ((hxint.const_mul a).add (hyint.const_mul b)) hzint,
      intervalIntegral.integral_add (hxint.const_mul a) (hyint.const_mul b),
      intervalIntegral.integral_const_mul] using hmono
  have hbound := ge_of_tendsto hlim hevent
  rw [paddedEntropyDefect_eq_entropyDefect,
    paddedEntropyDefect_eq_entropyDefect, paddedEntropyDefect_eq_entropyDefect] at hbound
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  have hval : entropyDefectTotal Q hQ.posSemidef z =
      entropyDefect z.1 Q z.2 hz.1 hQ.posSemidef hz.2 := by
    simp [entropyDefectTotal, hz]
  rw [hval]
  simp only [entropyDefectTotal, hx, hy, and_self, dite_true, smul_eq_mul]
  nlinarith

/-- Proportional diagonal blocks attain scalar trace compression. -/
lemma entropyDefect_diagonal_proportional
    {d : Type} [Fintype d] [DecidableEq d]
    (q : d → ℝ) (hq : ∀ i, 0 ≤ q i) (c r : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r) :
    entropyDefect
      (Matrix.diagonal fun i => ((c * q i : ℝ) : ℂ))
      (Matrix.diagonal fun i => ((q i : ℝ) : ℂ))
      (Matrix.diagonal fun i => ((r * q i : ℝ) : ℂ))
      (diagonalOfReal_posSemidef _ (fun i => mul_nonneg hc (hq i)))
      (diagonalOfReal_posSemidef _ hq)
      (diagonalOfReal_posSemidef _ (fun i => mul_nonneg hr (hq i))) =
      scalarEntropyDefect (c * ∑ i, q i) (∑ i, q i) (r * ∑ i, q i)
        (mul_nonneg hc (Finset.sum_nonneg fun i _ => hq i))
        (Finset.sum_nonneg fun i _ => hq i)
        (mul_nonneg hr (Finset.sum_nonneg fun i _ => hq i)) := by
  rw [entropyDefect_diagonal_eq_sum_scalar _ _ _
    (fun i => mul_nonneg hc (hq i)) hq (fun i => mul_nonneg hr (hq i))]
  have hterm (i : d) :
      scalarEntropyDefect (c * q i) (q i) (r * q i)
        (mul_nonneg hc (hq i)) (hq i) (mul_nonneg hr (hq i)) =
        q i * scalarEntropyDefect c 1 r hc zero_le_one hr := by
    simpa only [mul_one, mul_comm] using
      scalarEntropyDefect_real_smul (q i) c 1 r (hq i) hc zero_le_one hr
  simp_rw [hterm]
  rw [← Finset.sum_mul]
  symm
  simpa only [mul_one, mul_comm] using
    scalarEntropyDefect_real_smul (∑ i, q i) c 1 r
      (Finset.sum_nonneg fun i _ => hq i) hc zero_le_one hr

/-- Proportional outer matrices attain the lower bound for every PSD middle matrix. -/
theorem entropyDefect_proportional_eq
    {d : Type} [Fintype d] [DecidableEq d]
    (Q : Matrix d d ℂ) (hQ : Q.PosSemidef)
    (c r : ℝ) (hc : 0 ≤ c) (hr : 0 ≤ r) :
    entropyDefect ((c : ℂ) • Q) Q ((r : ℂ) • Q)
      (hQ.smul (by exact_mod_cast hc)) hQ (hQ.smul (by exact_mod_cast hr)) =
      scalarEntropyDefect (c * Q.trace.re) Q.trace.re (r * Q.trace.re)
        (mul_nonneg hc hQ.trace_nonneg.1) hQ.trace_nonneg.1
        (mul_nonneg hr hQ.trace_nonneg.1) := by
  let U : Matrix.unitaryGroup d ℂ := star hQ.isHermitian.eigenvectorUnitary
  let q : d → ℝ := hQ.isHermitian.eigenvalues
  have hq : ∀ i, 0 ≤ q i := hQ.eigenvalues_nonneg
  have hdiag : (U : Matrix d d ℂ) * Q * (U : Matrix d d ℂ).conjTranspose =
      Matrix.diagonal (fun i => ((q i : ℝ) : ℂ)) := by
    simpa [U, q, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose] using
      hQ.isHermitian.conjStarAlgAut_star_eigenvectorUnitary
  have hscale (c : ℝ) :
      (U : Matrix d d ℂ) * ((c : ℂ) • Q) * (U : Matrix d d ℂ).conjTranspose =
        Matrix.diagonal (fun i => ((c * q i : ℝ) : ℂ)) := by
    rw [Matrix.mul_smul, Matrix.smul_mul, hdiag]
    ext i j
    by_cases hij : i = j <;> simp [Matrix.diagonal, hij]
  have htrace : (∑ i, q i) = Q.trace.re := by
    have h := congrArg Complex.re hQ.isHermitian.trace_eq_sum_eigenvalues
    simpa [q] using h.symm
  have hval := entropyDefect_unitary_conj U ((c : ℂ) • Q) Q ((r : ℂ) • Q)
    (hQ.smul (by exact_mod_cast hc)) hQ (hQ.smul (by exact_mod_cast hr))
  calc
    _ = entropyDefect
        (Matrix.diagonal fun i => ((c * q i : ℝ) : ℂ))
        (Matrix.diagonal fun i => ((q i : ℝ) : ℂ))
        (Matrix.diagonal fun i => ((r * q i : ℝ) : ℂ))
        (diagonalOfReal_posSemidef _ (fun i => mul_nonneg hc (hq i)))
        (diagonalOfReal_posSemidef _ hq)
        (diagonalOfReal_posSemidef _ (fun i => mul_nonneg hr (hq i))) :=
      hval.symm.trans (entropyDefect_congr (hscale c) hdiag (hscale r) _ _ _ _ _ _)
    _ = _ := by
      rw [entropyDefect_diagonal_proportional q hq c r hc hr]
      exact scalarEntropyDefect_congr (congrArg (c * ·) htrace) htrace
        (congrArg (r * ·) htrace) _ _ _ _ _ _


/-- Equality in trace compression has exactly the proportional outer matrices.
The strict skew-logdet estimate and its improper-integral bridge are proved above. -/
theorem entropyDefect_eq_scalar_trace_iff
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (P Q R : Matrix d d ℂ) (hP : P.PosSemidef) (hQ : Q.PosDef)
    (hR : R.PosSemidef) :
    entropyDefect P Q R hP hQ.posSemidef hR =
      scalarEntropyDefect P.trace.re Q.trace.re R.trace.re
        hP.trace_nonneg.1 hQ.posSemidef.trace_nonneg.1 hR.trace_nonneg.1 ↔
      P = ((P.trace.re / Q.trace.re : ℝ) : ℂ) • Q ∧
      R = ((R.trace.re / Q.trace.re : ℝ) : ℂ) • Q := by
  have hqt : 0 < Q.trace.re := hQ.trace_pos.1
  let c := P.trace.re / Q.trace.re
  let r := R.trace.re / Q.trace.re
  have hc : 0 ≤ c := div_nonneg hP.trace_nonneg.1 hqt.le
  have hr : 0 ≤ r := div_nonneg hR.trace_nonneg.1 hqt.le
  let Pc : Matrix d d ℂ := (c : ℂ) • Q
  let Rc : Matrix d d ℂ := (r : ℂ) • Q
  have hPc : Pc.PosSemidef := hQ.posSemidef.smul (by exact_mod_cast hc)
  have hRc : Rc.PosSemidef := hQ.posSemidef.smul (by exact_mod_cast hr)
  have hct : c * Q.trace.re = P.trace.re := div_mul_cancel₀ _ hqt.ne'
  have hrt : r * Q.trace.re = R.trace.re := div_mul_cancel₀ _ hqt.ne'
  have htPc : Pc.trace.re = P.trace.re := by simpa [Pc, Matrix.trace_smul] using hct
  have htRc : Rc.trace.re = R.trace.re := by simpa [Rc, Matrix.trace_smul] using hrt
  have hmin : entropyDefect Pc Q Rc hPc hQ.posSemidef hRc =
      scalarEntropyDefect P.trace.re Q.trace.re R.trace.re
        hP.trace_nonneg.1 hQ.posSemidef.trace_nonneg.1 hR.trace_nonneg.1 := by
    exact (entropyDefect_proportional_eq Q hQ.posSemidef c r hc hr).trans
      (scalarEntropyDefect_congr hct rfl hrt _ _ _ _ _ _)
  constructor
  · intro heq
    have hpairs : (P, R) = (Pc, Rc) := by
      by_contra hne
      have hh := (entropyDefectTotal_strictConvexOn Q hQ).2
        (show (P, R) ∈ {PR | PR.1.PosSemidef ∧ PR.2.PosSemidef} from ⟨hP,hR⟩)
        (show (Pc, Rc) ∈ {PR | PR.1.PosSemidef ∧ PR.2.PosSemidef} from ⟨hPc,hRc⟩)
        hne (show (0:ℝ)<1/2 by norm_num) (show (0:ℝ)<1/2 by norm_num)
        (show (1/2:ℝ)+1/2=1 by norm_num)
      have hPm : ((1/2:ℝ) • P + (1/2:ℝ) • Pc).PosSemidef :=
        (hP.smul (by norm_num : (0:ℝ)≤1/2)).add (hPc.smul (by norm_num : (0:ℝ)≤1/2))
      have hRm : ((1/2:ℝ) • R + (1/2:ℝ) • Rc).PosSemidef :=
        (hR.smul (by norm_num : (0:ℝ)≤1/2)).add (hRc.smul (by norm_num : (0:ℝ)≤1/2))
      have hlow := entropyDefect_ge_scalar_trace _ Q _ hPm hQ.posSemidef hRm
      have htPm : ((1/2:ℝ) • P + (1/2:ℝ) • Pc).trace.re = P.trace.re := by
        simp [Matrix.trace_add, Matrix.trace_smul, htPc]; ring
      have htRm : ((1/2:ℝ) • R + (1/2:ℝ) • Rc).trace.re = R.trace.re := by
        simp [Matrix.trace_add, Matrix.trace_smul, htRc]; ring
      have hscalar := scalarEntropyDefect_congr htPm rfl htRm
        hPm.trace_nonneg.1 hQ.posSemidef.trace_nonneg.1 hRm.trace_nonneg.1
        hP.trace_nonneg.1 hQ.posSemidef.trace_nonneg.1 hR.trace_nonneg.1
      rw [hscalar] at hlow
      simp only [Prod.smul_fst, Prod.smul_snd, Prod.fst_add, Prod.snd_add,
        entropyDefectTotal, hP, hR, hPc, hRc, hPm, hRm, and_self, dite_true,
        smul_eq_mul] at hh
      rw [heq, hmin] at hh
      linarith
    exact ⟨congrArg Prod.fst hpairs, congrArg Prod.snd hpairs⟩
  · rintro ⟨hp, hr⟩
    exact (entropyDefect_congr hp rfl hr _ _ _ _ _ _).trans hmin


set_option maxHeartbeats 800000 in
/-- Exact conversion between triangular entropy equality and trace-defect equality. -/
theorem triangular_entropy_eq_iff_defect_of_polar
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (A B D : Matrix d d ℂ) (UB UD : Matrix.unitaryGroup d ℂ)
    (hB : B = (UB : Matrix d d ℂ) * psdSqrt (B.conjTranspose * B))
    (hD : D = (UD : Matrix d d ℂ) * psdSqrt (D.conjTranspose * D))
    (hsum : frobeniusSq A + frobeniusSq B + frobeniusSq D = 1) :
    let W : Matrix.unitaryGroup d ℂ := star UB * UD
    let R := (W : Matrix d d ℂ) * (D.conjTranspose * D) * (W : Matrix d d ℂ).conjTranspose
    let T := Matrix.fromBlocks A 0 B D
    psdEntropy (T * T.conjTranspose) (Matrix.posSemidef_self_mul_conjTranspose T) =
      entanglementCurve (2 * Real.sqrt (frobeniusSq A * frobeniusSq D)) +
        normalizedGramEntropy (frobeniusSq A) A +
        normalizedGramEntropy (frobeniusSq B) B + normalizedGramEntropy (frobeniusSq D) D ↔
    entropyDefect (A.conjTranspose * A) (B.conjTranspose * B) R
      (Matrix.posSemidef_conjTranspose_mul_self A)
      (Matrix.posSemidef_conjTranspose_mul_self B)
      ((Matrix.posSemidef_conjTranspose_mul_self D).mul_mul_conjTranspose_same (W : Matrix d d ℂ)) =
    scalarEntropyDefect (frobeniusSq A) (frobeniusSq B) (frobeniusSq D)
      (frobeniusSq_nonneg A) (frobeniusSq_nonneg B) (frobeniusSq_nonneg D) := by
  let P : Matrix d d ℂ := A.conjTranspose * A
  let Q : Matrix d d ℂ := B.conjTranspose * B
  let S : Matrix d d ℂ := D.conjTranspose * D
  let W : Matrix.unitaryGroup d ℂ := star UB * UD
  let R : Matrix d d ℂ :=
    (W : Matrix d d ℂ) * S * (W : Matrix d d ℂ).conjTranspose
  let T : Matrix (Sum d d) (Sum d d) ℂ := Matrix.fromBlocks A 0 B D
  let G : Matrix.unitaryGroup (Sum d d) ℂ := lowerBlockUnitary W
  have hP : P.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self A
  have hQ : Q.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  have hS : S.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self D
  have hR : R.PosSemidef :=
    hS.mul_mul_conjTranspose_same (W : Matrix d d ℂ)
  have hGauge :
      (G : Matrix (Sum d d) (Sum d d) ℂ) *
          (T.conjTranspose * T) *
            (G : Matrix (Sum d d) (Sum d d) ℂ).conjTranspose =
        entropyCoupling P Q R := by
    exact triangular_polarGauge_identity A B D UB UD hB hD
  have htraceP : P.trace.re = frobeniusSq A :=
    trace_conjTranspose_mul_self_re_eq_frobeniusSq A
  have htraceQ : Q.trace.re = frobeniusSq B :=
    trace_conjTranspose_mul_self_re_eq_frobeniusSq B
  have htraceS : S.trace.re = frobeniusSq D :=
    trace_conjTranspose_mul_self_re_eq_frobeniusSq D
  have htraceR : R.trace.re = frobeniusSq D := by
    calc
      R.trace.re = S.trace.re := by
        dsimp [R]
        have hW : (W : Matrix d d ℂ).conjTranspose *
            (W : Matrix d d ℂ) = 1 := by
          simpa [Matrix.star_eq_conjTranspose] using
            Unitary.coe_star_mul_self W
        rw [Matrix.trace_mul_cycle, hW, Matrix.one_mul]
      _ = frobeniusSq D := htraceS
  have hTgram :
      psdEntropy (T.conjTranspose * T)
          (Matrix.posSemidef_conjTranspose_mul_self T) =
        psdEntropy (T * T.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose T) :=
    psdEntropy_conjTranspose_mul_self_eq_self_mul_conjTranspose T
  have hcouplingEq :
      psdEntropy (entropyCoupling P Q R)
          (entropyCoupling_posSemidef P Q R hP hQ hR) =
        psdEntropy (T.conjTranspose * T)
          (Matrix.posSemidef_conjTranspose_mul_self T) := by
    calc
      _ = psdEntropy
          ((G : Matrix (Sum d d) (Sum d d) ℂ) *
            (T.conjTranspose * T) *
              (G : Matrix (Sum d d) (Sum d d) ℂ).conjTranspose)
          ((Matrix.posSemidef_conjTranspose_mul_self T).mul_mul_conjTranspose_same
            (G : Matrix (Sum d d) (Sum d d) ℂ)) :=
        psdEntropy_congr hGauge.symm _ _
      _ = _ := psdEntropy_unitary_conj G _ _
  have hPentropy :
      psdEntropy P hP =
        normalizedGramEntropy (frobeniusSq A) A -
          QIT.xlog2 (frobeniusSq A) := by
    calc
      _ = psdEntropy (A * A.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose A) :=
        psdEntropy_conjTranspose_mul_self_eq_self_mul_conjTranspose A
      _ = _ := psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2 A
  have hQentropy :
      psdEntropy Q hQ =
        normalizedGramEntropy (frobeniusSq B) B -
          QIT.xlog2 (frobeniusSq B) := by
    calc
      _ = psdEntropy (B * B.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose B) :=
        psdEntropy_conjTranspose_mul_self_eq_self_mul_conjTranspose B
      _ = _ := psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2 B
  have hRentropy :
      psdEntropy R hR =
        normalizedGramEntropy (frobeniusSq D) D -
          QIT.xlog2 (frobeniusSq D) := by
    calc
      _ = psdEntropy S hS := psdEntropy_unitary_conj W S hS
      _ = psdEntropy (D * D.conjTranspose)
          (Matrix.posSemidef_self_mul_conjTranspose D) :=
        psdEntropy_conjTranspose_mul_self_eq_self_mul_conjTranspose D
      _ = _ := psdEntropy_gram_eq_normalizedGramEntropy_sub_xlog2 D
  have hscalar := scalarEntropyDefect_eq_entanglementCurve
    (frobeniusSq A) (frobeniusSq B) (frobeniusSq D)
    (frobeniusSq_nonneg A) (frobeniusSq_nonneg B) (frobeniusSq_nonneg D) hsum
  change _ ↔ entropyDefect P Q R hP hQ hR = _
  unfold entropyDefect
  rw [hcouplingEq, hTgram, hPentropy, hQentropy, hRentropy, hscalar]
  constructor <;> intro h <;> linarith


lemma polar_outputGram {d : Type} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) (U : Matrix.unitaryGroup d ℂ)
    (hA : A = (U : Matrix d d ℂ) * psdSqrt (A.conjTranspose * A)) :
    A * A.conjTranspose =
      (U : Matrix d d ℂ) * (A.conjTranspose * A) * (U : Matrix d d ℂ).conjTranspose := by
  conv_lhs => rw [hA]
  rw [Matrix.conjTranspose_mul, (psdSqrt_isHermitian _).eq]
  rw [Matrix.mul_assoc, ← Matrix.mul_assoc (psdSqrt _) (psdSqrt _),
    psdSqrt_mul_self_of_posSemidef (Matrix.posSemidef_conjTranspose_mul_self A)]
  rw [← Matrix.mul_assoc]

/-- The polar gauge translates right-Gram proportionality to output-Gram proportionality. -/
lemma polarGauge_proportional_iff {d : Type} [Fintype d] [DecidableEq d]
    (B D : Matrix d d ℂ) (UB UD : Matrix.unitaryGroup d ℂ)
    (hB : B = (UB : Matrix d d ℂ) * psdSqrt (B.conjTranspose * B))
    (hD : D = (UD : Matrix d d ℂ) * psdSqrt (D.conjTranspose * D)) (r : ℂ) :
    let W : Matrix.unitaryGroup d ℂ := star UB * UD
    (W : Matrix d d ℂ) * (D.conjTranspose * D) * (W : Matrix d d ℂ).conjTranspose =
      r • (B.conjTranspose * B) ↔ D * D.conjTranspose = r • (B * B.conjTranspose) := by
  let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) (UB : Matrix.unitaryGroup d ℂ)
  have he (X : Matrix d d ℂ) : e X =
      (UB : Matrix d d ℂ) * X * (UB : Matrix d d ℂ).conjTranspose := by
    simp [e, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
  have hleft : e ((↑(star UB * UD) : Matrix d d ℂ) * (D.conjTranspose * D) *
      (↑(star UB * UD) : Matrix d d ℂ).conjTranspose) = D * D.conjTranspose := by
    rw [polar_outputGram D UD hD]
    have hu : (UB : Matrix d d ℂ) * (UB : Matrix d d ℂ).conjTranspose = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self UB
    simp only [he]
    change (UB : Matrix d d ℂ) *
      (((UB : Matrix d d ℂ).conjTranspose * (UD : Matrix d d ℂ)) *
      (D.conjTranspose * D) *
      ((UB : Matrix d d ℂ).conjTranspose * (UD : Matrix d d ℂ)).conjTranspose) *
      (UB : Matrix d d ℂ).conjTranspose = _
    rw [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose]
    calc
      _ = ((UB : Matrix d d ℂ) * (UB : Matrix d d ℂ).conjTranspose) *
          ((UD : Matrix d d ℂ) * (D.conjTranspose * D) * (UD : Matrix d d ℂ).conjTranspose) *
          ((UB : Matrix d d ℂ) * (UB : Matrix d d ℂ).conjTranspose) := by noncomm_ring
      _ = _ := by rw [hu]; simp
  have hright : e (r • (B.conjTranspose * B)) = r • (B * B.conjTranspose) := by
    rw [map_smul, he, ← polar_outputGram B UB hB]
  constructor
  · intro h
    have hh := congrArg (fun X => e X) h
    simpa only [hleft, hright] using hh
  · intro h
    apply e.injective
    change e _ = e _
    rw [hleft, hright, h]


/-- Necessary and sufficient Gram conditions for triangular equality with an
invertible middle block. This includes both necessity and sufficiency,
with strictness derived from the exact resolvent norm-loss identity. -/
theorem square_triangular_entropy_equality_iff
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (A B D : Matrix d d ℂ) (hBunit : IsUnit B)
    (hsum : frobeniusSq A + frobeniusSq B + frobeniusSq D = 1) :
    let T := Matrix.fromBlocks A 0 B D
    psdEntropy (T * T.conjTranspose) (Matrix.posSemidef_self_mul_conjTranspose T) =
      entanglementCurve (2 * Real.sqrt (frobeniusSq A * frobeniusSq D)) +
        normalizedGramEntropy (frobeniusSq A) A +
        normalizedGramEntropy (frobeniusSq B) B + normalizedGramEntropy (frobeniusSq D) D ↔
    A.conjTranspose * A = ((frobeniusSq A / frobeniusSq B : ℝ) : ℂ) •
        (B.conjTranspose * B) ∧
    D * D.conjTranspose = ((frobeniusSq D / frobeniusSq B : ℝ) : ℂ) •
        (B * B.conjTranspose) := by
  obtain ⟨UB,hB⟩ := exists_unitary_mul_psdSqrt B
  obtain ⟨UD,hD⟩ := exists_unitary_mul_psdSqrt D
  let W : Matrix.unitaryGroup d ℂ := star UB * UD
  let R : Matrix d d ℂ := (W : Matrix d d ℂ) * (D.conjTranspose * D) *
    (W : Matrix d d ℂ).conjTranspose
  have hP := Matrix.posSemidef_conjTranspose_mul_self A
  have hQ : (B.conjTranspose * B).PosDef := by
    apply (Matrix.posSemidef_conjTranspose_mul_self B).posDef_iff_isUnit.mpr
    have hb : IsUnit B.conjTranspose := by
      simpa [Matrix.star_eq_conjTranspose] using hBunit.star
    exact hb.mul hBunit
  have hR := (Matrix.posSemidef_conjTranspose_mul_self D).mul_mul_conjTranspose_same
    (W : Matrix d d ℂ)
  have htP := trace_conjTranspose_mul_self_re_eq_frobeniusSq A
  have htQ := trace_conjTranspose_mul_self_re_eq_frobeniusSq B
  have htR : R.trace.re = frobeniusSq D := by
    dsimp [R]
    rw [Matrix.trace_mul_cycle]
    have hw : (W : Matrix d d ℂ).conjTranspose * (W : Matrix d d ℂ) = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self W
    rw [hw, Matrix.one_mul]
    exact trace_conjTranspose_mul_self_re_eq_frobeniusSq D
  have hiff := entropyDefect_eq_scalar_trace_iff
    (A.conjTranspose * A) (B.conjTranspose * B) R hP hQ hR
  have hscalar := scalarEntropyDefect_congr htP htQ htR
    hP.trace_nonneg.1 hQ.posSemidef.trace_nonneg.1 hR.trace_nonneg.1
    (frobeniusSq_nonneg A) (frobeniusSq_nonneg B) (frobeniusSq_nonneg D)
  rw [hscalar] at hiff
  simp only [htP, htQ, htR] at hiff
  exact (triangular_entropy_eq_iff_defect_of_polar A B D UB UD hB hD hsum).trans
    (hiff.trans (and_congr_right fun _ => polarGauge_proportional_iff B D UB UD hB hD _))

/-- A block-diagonal pair of unitaries, acting on the two block rows. -/
def diagonalBlockUnitary {d : Type} [Fintype d] [DecidableEq d]
    (U V : Matrix.unitaryGroup d ℂ) : Matrix.unitaryGroup (Sum d d) ℂ :=
  ⟨Matrix.fromBlocks (U : Matrix d d ℂ) 0 0 (V : Matrix d d ℂ), by
    rw [Matrix.mem_unitaryGroup_iff]
    have hu : (U : Matrix d d ℂ) * (U : Matrix d d ℂ).conjTranspose = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
    have hv : (V : Matrix d d ℂ) * (V : Matrix d d ℂ).conjTranspose = 1 := by
      simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self V
    simp [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose,
      Matrix.fromBlocks_multiply, hu, hv]⟩

/-- Explicit matrix representation of the scalar triangular matrix tensored
with `R`: its four blocks are scalar multiples of `R`. -/
def scalarTriangularTensor {d : Type} [Fintype d] [DecidableEq d]
    (α β γ : ℝ) (R : Matrix d d ℂ) : Matrix (Sum d d) (Sum d d) ℂ :=
  Matrix.fromBlocks ((Real.sqrt α : ℂ) • R) 0
    ((Real.sqrt β : ℂ) • R) ((Real.sqrt γ : ℂ) • R)

lemma left_polar_cancel {d : Type} [Fintype d] [DecidableEq d]
    (A : Matrix d d ℂ) (U : Matrix.unitaryGroup d ℂ)
    (h : A = (U : Matrix d d ℂ) * psdSqrt (A.conjTranspose*A)) :
    (U : Matrix d d ℂ).conjTranspose * A = psdSqrt (A.conjTranspose*A) := by
  conv_lhs => rw [h]
  rw [← Matrix.mul_assoc]
  have hu : (U : Matrix d d ℂ).conjTranspose * (U : Matrix d d ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  rw [hu, Matrix.one_mul]

/-- The proportional-Gram conditions supply the manuscript's explicit block
row and column unitaries and a normalized common matrix factor. -/
theorem triangular_normalForm_of_gram
    {d : Type} [Fintype d] [DecidableEq d]
    (A B D : Matrix d d ℂ) (hβ : 0 < frobeniusSq B)
    (hA : A.conjTranspose*A = ((frobeniusSq A / frobeniusSq B : ℝ) : ℂ) •
      (B.conjTranspose*B))
    (hD : D*D.conjTranspose = ((frobeniusSq D / frobeniusSq B : ℝ) : ℂ) •
      (B*B.conjTranspose)) :
    ∃ U₁ U₂ V₂ : Matrix.unitaryGroup d ℂ, ∃ R₀ : Matrix d d ℂ,
      frobeniusSq R₀ = 1 ∧
      (diagonalBlockUnitary U₁ U₂ : Matrix (Sum d d) (Sum d d) ℂ) *
        Matrix.fromBlocks A 0 B D *
        (diagonalBlockUnitary 1 V₂ : Matrix (Sum d d) (Sum d d) ℂ) =
      scalarTriangularTensor (frobeniusSq A) (frobeniusSq B) (frobeniusSq D) R₀ := by
  obtain ⟨UA,ha⟩ := exists_unitary_mul_psdSqrt A
  obtain ⟨UB,hb⟩ := exists_unitary_mul_psdSqrt B
  obtain ⟨UD,hd⟩ := exists_unitary_mul_psdSqrt D
  let Q := B.conjTranspose * B
  let S := D.conjTranspose * D
  let W : Matrix.unitaryGroup d ℂ := star UB * UD
  have hQ : Q.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self B
  have hS : S.PosSemidef := Matrix.posSemidef_conjTranspose_mul_self D
  have hR : (W : Matrix d d ℂ) * S * (W : Matrix d d ℂ).conjTranspose =
      ((frobeniusSq D / frobeniusSq B : ℝ) : ℂ) • Q :=
    (polarGauge_proportional_iff B D UB UD hb hd _).mpr hD
  have hsqrtR := psdSqrt_unitary_conj W S hS
  rw [hR, psdSqrt_real_smul (div_nonneg (frobeniusSq_nonneg D) hβ.le) hQ] at hsqrtR
  have hac : (UA : Matrix d d ℂ).conjTranspose * A =
      (Real.sqrt (frobeniusSq A / frobeniusSq B) : ℂ) • psdSqrt Q := by
    rw [left_polar_cancel A UA ha, hA,
      psdSqrt_real_smul (div_nonneg (frobeniusSq_nonneg A) hβ.le) hQ]
  have hbc := left_polar_cancel B UB hb
  have hdc : (UB : Matrix d d ℂ).conjTranspose * D * (W : Matrix d d ℂ).conjTranspose =
      (Real.sqrt (frobeniusSq D / frobeniusSq B) : ℂ) • psdSqrt Q := by
    calc
      _ = (W : Matrix d d ℂ) * psdSqrt S * (W : Matrix d d ℂ).conjTranspose := by
        conv_lhs => rw [hd]
        change (UB : Matrix d d ℂ).conjTranspose * ((UD : Matrix d d ℂ) * psdSqrt S) * _ =
          ((UB : Matrix d d ℂ).conjTranspose * (UD : Matrix d d ℂ)) * psdSqrt S * _
        simp only [Matrix.mul_assoc]
      _ = _ := hsqrtR.symm
  let R₀ : Matrix d d ℂ := (((Real.sqrt (frobeniusSq B))⁻¹ : ℝ) : ℂ) • psdSqrt Q
  have hnorm : frobeniusSq R₀ = 1 := by
    have hg : R₀ * R₀.conjTranspose = ((frobeniusSq B)⁻¹ : ℂ) • Q := by
      simp only [R₀, Matrix.conjTranspose_smul, (psdSqrt_isHermitian Q).eq,
        Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul, Matrix.mul_smul, smul_smul,
        psdSqrt_mul_self_of_posSemidef hQ, ← Complex.ofReal_mul]
      congr 1
      rw [← pow_two, inv_pow, Real.sq_sqrt hβ.le]
      simp
    unfold frobeniusSq
    rw [hg, Matrix.trace_smul]
    have htr : Q.trace.re = frobeniusSq B := trace_conjTranspose_mul_self_re_eq_frobeniusSq B
    simp [← Complex.ofReal_inv, htr, hβ.ne']
  have hscale (x : ℝ) (hx : 0 ≤ x) : (Real.sqrt x : ℂ) • R₀ =
      (Real.sqrt (x / frobeniusSq B) : ℂ) • psdSqrt Q := by
    rw [Real.sqrt_div hx]
    simp only [R₀, smul_smul, Complex.ofReal_mul, Complex.ofReal_inv, div_eq_mul_inv]
  refine ⟨star UA, star UB, star W, R₀, hnorm, ?_⟩
  change Matrix.fromBlocks (UA : Matrix d d ℂ).conjTranspose 0 0
      (UB : Matrix d d ℂ).conjTranspose * Matrix.fromBlocks A 0 B D *
      Matrix.fromBlocks 1 0 0 (W : Matrix d d ℂ).conjTranspose = _
  simp only [Matrix.fromBlocks_multiply, Matrix.mul_zero, Matrix.zero_mul,
    Matrix.mul_one, zero_add, add_zero]
  rw [hac, hdc, hbc]
  unfold scalarTriangularTensor
  rw [hscale _ (frobeniusSq_nonneg A), hscale _ (frobeniusSq_nonneg B),
    hscale _ (frobeniusSq_nonneg D), div_self hβ.ne', Real.sqrt_one, Complex.ofReal_one, one_smul]

lemma inputGram_unitary_mul {d : Type} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (A : Matrix d d ℂ) :
    ((U : Matrix d d ℂ)*A).conjTranspose*((U : Matrix d d ℂ)*A) = A.conjTranspose*A := by
  have hu : (U : Matrix d d ℂ).conjTranspose * (U : Matrix d d ℂ) = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_star_mul_self U
  rw [Matrix.conjTranspose_mul]
  calc
    _ = A.conjTranspose * ((U : Matrix d d ℂ).conjTranspose * (U : Matrix d d ℂ)) * A := by
      noncomm_ring
    _ = _ := by rw [hu]; simp

lemma outputGram_mul_unitary {d : Type} [Fintype d] [DecidableEq d]
    (U : Matrix.unitaryGroup d ℂ) (A : Matrix d d ℂ) :
    (A*(U : Matrix d d ℂ))*(A*(U : Matrix d d ℂ)).conjTranspose = A*A.conjTranspose := by
  have hu : (U : Matrix d d ℂ) * (U : Matrix d d ℂ).conjTranspose = 1 := by
    simpa [Matrix.star_eq_conjTranspose] using Unitary.coe_mul_star_self U
  rw [Matrix.conjTranspose_mul]
  calc
    _ = A * ((U : Matrix d d ℂ) * (U : Matrix d d ℂ).conjTranspose) * A.conjTranspose := by
      noncomm_ring
    _ = _ := by rw [hu]; simp

lemma inputGram_sqrt_smul {d : Type} [Fintype d] [DecidableEq d]
    (R : Matrix d d ℂ) (x : ℝ) (hx : 0 ≤ x) :
    ((Real.sqrt x : ℂ) • R).conjTranspose * ((Real.sqrt x : ℂ) • R) =
      (x : ℂ) • (R.conjTranspose*R) := by
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul, Real.mul_self_sqrt hx]

lemma outputGram_sqrt_smul {d : Type} [Fintype d] [DecidableEq d]
    (R : Matrix d d ℂ) (x : ℝ) (hx : 0 ≤ x) :
    ((Real.sqrt x : ℂ) • R) * ((Real.sqrt x : ℂ) • R).conjTranspose =
      (x : ℂ) • (R*R.conjTranspose) := by
  simp only [Matrix.conjTranspose_smul, Complex.star_def, Complex.conj_ofReal, Matrix.smul_mul,
    Matrix.mul_smul, smul_smul, ← Complex.ofReal_mul, Real.mul_self_sqrt hx]

/-- Every block-unitary scalar tensor form satisfies both Gram relations. -/
theorem triangular_gram_of_normalForm
    {d : Type} [Fintype d] [DecidableEq d]
    (A B D : Matrix d d ℂ) (hβ : 0 < frobeniusSq B)
    (U₁ U₂ V₂ : Matrix.unitaryGroup d ℂ) (R₀ : Matrix d d ℂ)
    (hform : (diagonalBlockUnitary U₁ U₂ : Matrix (Sum d d) (Sum d d) ℂ) *
        Matrix.fromBlocks A 0 B D *
        (diagonalBlockUnitary 1 V₂ : Matrix (Sum d d) (Sum d d) ℂ) =
      scalarTriangularTensor (frobeniusSq A) (frobeniusSq B) (frobeniusSq D) R₀) :
    A.conjTranspose*A = ((frobeniusSq A / frobeniusSq B : ℝ) : ℂ) • (B.conjTranspose*B) ∧
    D*D.conjTranspose = ((frobeniusSq D / frobeniusSq B : ℝ) : ℂ) • (B*B.conjTranspose) := by
  have hf : Matrix.fromBlocks ((U₁ : Matrix d d ℂ)*A) 0 ((U₂ : Matrix d d ℂ)*B)
      ((U₂ : Matrix d d ℂ)*D*(V₂ : Matrix d d ℂ)) =
      scalarTriangularTensor (frobeniusSq A) (frobeniusSq B) (frobeniusSq D) R₀ := by
    simpa [diagonalBlockUnitary, Matrix.fromBlocks_multiply] using hform
  have ha : (U₁ : Matrix d d ℂ)*A = (Real.sqrt (frobeniusSq A) : ℂ) • R₀ :=
    congrArg (fun M : Matrix (Sum d d) (Sum d d) ℂ => M.submatrix Sum.inl Sum.inl) hf
  have hb : (U₂ : Matrix d d ℂ)*B = (Real.sqrt (frobeniusSq B) : ℂ) • R₀ :=
    congrArg (fun M : Matrix (Sum d d) (Sum d d) ℂ => M.submatrix Sum.inr Sum.inl) hf
  have hd : (U₂ : Matrix d d ℂ)*D*(V₂ : Matrix d d ℂ) =
      (Real.sqrt (frobeniusSq D) : ℂ) • R₀ :=
    congrArg (fun M : Matrix (Sum d d) (Sum d d) ℂ => M.submatrix Sum.inr Sum.inr) hf
  have hag := congrArg (fun X : Matrix d d ℂ => X.conjTranspose*X) ha
  have hbg := congrArg (fun X : Matrix d d ℂ => X.conjTranspose*X) hb
  dsimp only at hag hbg
  rw [inputGram_unitary_mul, inputGram_sqrt_smul _ _ (frobeniusSq_nonneg A)] at hag
  rw [inputGram_unitary_mul, inputGram_sqrt_smul _ _ (frobeniusSq_nonneg B)] at hbg
  constructor
  · rw [hag,hbg,smul_smul,← Complex.ofReal_mul,div_mul_cancel₀ _ hβ.ne']
  · let e := Unitary.conjStarAlgAut ℂ (Matrix d d ℂ) U₂
    have he (X : Matrix d d ℂ) : e X =
        (U₂ : Matrix d d ℂ)*X*(U₂ : Matrix d d ℂ).conjTranspose := by
      simp [e, Unitary.conjStarAlgAut_apply, Matrix.star_eq_conjTranspose]
    have hdg := congrArg (fun X : Matrix d d ℂ => X*X.conjTranspose) hd
    have hbg' := congrArg (fun X : Matrix d d ℂ => X*X.conjTranspose) hb
    dsimp only at hdg hbg'
    rw [outputGram_mul_unitary, outputGram_sqrt_smul _ _ (frobeniusSq_nonneg D)] at hdg
    rw [outputGram_sqrt_smul _ _ (frobeniusSq_nonneg B)] at hbg'
    have hout (X : Matrix d d ℂ) : ((U₂ : Matrix d d ℂ)*X)*((U₂ : Matrix d d ℂ)*X).conjTranspose =
        e (X*X.conjTranspose) := by rw [he,Matrix.conjTranspose_mul]; noncomm_ring
    rw [hout] at hdg hbg'
    apply e.injective
    change e _ = e _
    rw [map_smul, hdg,hbg',smul_smul,← Complex.ofReal_mul,div_mul_cancel₀ _ hβ.ne']

/-- Full normal-form equivalence: equality is equivalent to block-diagonal
row and column unitaries transforming `T` into `T_sc ⊗ R₀`, with unit
Frobenius norm for the common factor. -/
theorem square_triangular_entropy_equality_iff_normalForm
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (A B D : Matrix d d ℂ) (hBunit : IsUnit B)
    (hβ : 0 < frobeniusSq B)
    (hsum : frobeniusSq A + frobeniusSq B + frobeniusSq D = 1) :
    let T := Matrix.fromBlocks A 0 B D
    psdEntropy (T*T.conjTranspose) (Matrix.posSemidef_self_mul_conjTranspose T) =
      entanglementCurve (2*Real.sqrt (frobeniusSq A * frobeniusSq D)) +
        normalizedGramEntropy (frobeniusSq A) A + normalizedGramEntropy (frobeniusSq B) B +
        normalizedGramEntropy (frobeniusSq D) D ↔
    ∃ U₁ U₂ V₂ : Matrix.unitaryGroup d ℂ, ∃ R₀ : Matrix d d ℂ,
      frobeniusSq R₀ = 1 ∧
      (diagonalBlockUnitary U₁ U₂ : Matrix (Sum d d) (Sum d d) ℂ) * T *
        (diagonalBlockUnitary 1 V₂ : Matrix (Sum d d) (Sum d d) ℂ) =
      scalarTriangularTensor (frobeniusSq A) (frobeniusSq B) (frobeniusSq D) R₀ := by
  apply (square_triangular_entropy_equality_iff A B D hBunit hsum).trans
  constructor
  · rintro ⟨ha,hd⟩
    exact triangular_normalForm_of_gram A B D hβ ha hd
  · rintro ⟨U₁,U₂,V₂,R₀,_,hf⟩
    exact triangular_gram_of_normalForm A B D hβ U₁ U₂ V₂ R₀ hf

/-- The scalar triangular matrix in the normal form. -/
def scalarTriangularMatrix (α β γ : ℝ) : Matrix (Fin 2) (Fin 2) ℂ :=
  !![(Real.sqrt α : ℂ), 0; (Real.sqrt β : ℂ), (Real.sqrt γ : ℂ)]

/-- Identify the direct-sum block coordinates with the qubit tensor coordinates. -/
def triangleTensorEquiv (d : Type) : Sum d d ≃ (Fin 2 × d) where
  toFun := Sum.elim (fun i => (0,i)) (fun i => (1,i))
  invFun p := if p.1 = 0 then Sum.inl p.2 else Sum.inr p.2
  left_inv := by rintro (i|i) <;> simp
  right_inv := by rintro ⟨i,j⟩; fin_cases i <;> simp

/-- The block scalar tensor notation is exactly the usual matrix Kronecker product. -/
theorem scalarTriangularTensor_eq_kronecker
    {d : Type} [Fintype d] [DecidableEq d] (α β γ : ℝ) (R : Matrix d d ℂ) :
    Matrix.reindex (triangleTensorEquiv d) (triangleTensorEquiv d)
      (scalarTriangularTensor α β γ R) = (scalarTriangularMatrix α β γ) ⊗ₖ R := by
  ext ⟨i,x⟩ ⟨j,y⟩
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.reindex, triangleTensorEquiv, scalarTriangularTensor,
      scalarTriangularMatrix, Matrix.kroneckerMap_apply, Matrix.smul_apply]

/-- The normal-form clause with a literal Kronecker product, after identifying
block direct-sum coordinates with two-dimensional tensor coordinates. -/
theorem square_triangular_entropy_equality_iff_kronecker
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (A B D : Matrix d d ℂ) (hBunit : IsUnit B)
    (hβ : 0 < frobeniusSq B)
    (hsum : frobeniusSq A + frobeniusSq B + frobeniusSq D = 1) :
    let T := Matrix.fromBlocks A 0 B D
    psdEntropy (T*T.conjTranspose) (Matrix.posSemidef_self_mul_conjTranspose T) =
      entanglementCurve (2*Real.sqrt (frobeniusSq A * frobeniusSq D)) +
        normalizedGramEntropy (frobeniusSq A) A + normalizedGramEntropy (frobeniusSq B) B +
        normalizedGramEntropy (frobeniusSq D) D ↔
    ∃ U₁ U₂ V₂ : Matrix.unitaryGroup d ℂ, ∃ R₀ : Matrix d d ℂ,
      frobeniusSq R₀ = 1 ∧
      Matrix.reindex (triangleTensorEquiv d) (triangleTensorEquiv d)
        ((diagonalBlockUnitary U₁ U₂ : Matrix (Sum d d) (Sum d d) ℂ) * T *
          (diagonalBlockUnitary 1 V₂ : Matrix (Sum d d) (Sum d d) ℂ)) =
      (scalarTriangularMatrix (frobeniusSq A) (frobeniusSq B) (frobeniusSq D)) ⊗ₖ R₀ := by
  apply (square_triangular_entropy_equality_iff_normalForm A B D hBunit hβ hsum).trans
  constructor
  · rintro ⟨U₁,U₂,V₂,R₀,hn,hf⟩
    refine ⟨U₁,U₂,V₂,R₀,hn,?_⟩
    rw [hf, scalarTriangularTensor_eq_kronecker]
  · rintro ⟨U₁,U₂,V₂,R₀,hn,hf⟩
    refine ⟨U₁,U₂,V₂,R₀,hn,?_⟩
    apply (Matrix.reindex (triangleTensorEquiv d) (triangleTensorEquiv d)).injective
    rw [scalarTriangularTensor_eq_kronecker]
    exact hf

lemma diagonalBlockUnitary_mul {d : Type} [Fintype d] [DecidableEq d]
    (U V W X : Matrix.unitaryGroup d ℂ) :
    (diagonalBlockUnitary U V : Matrix (Sum d d) (Sum d d) ℂ) *
      (diagonalBlockUnitary W X : Matrix (Sum d d) (Sum d d) ℂ) =
    (diagonalBlockUnitary (U*W) (V*X) : Matrix (Sum d d) (Sum d d) ℂ) := by
  simp [diagonalBlockUnitary, Matrix.fromBlocks_multiply]

lemma scalarTriangularTensor_mul_diagonal {d : Type} [Fintype d] [DecidableEq d]
    (α β γ : ℝ) (R : Matrix d d ℂ) (V : Matrix.unitaryGroup d ℂ) :
    scalarTriangularTensor α β γ R *
      (diagonalBlockUnitary V V : Matrix (Sum d d) (Sum d d) ℂ) =
    scalarTriangularTensor α β γ (R * (V : Matrix d d ℂ)) := by
  simp [scalarTriangularTensor, diagonalBlockUnitary, Matrix.fromBlocks_multiply]

/-- Absorb an arbitrary first column unitary into the common tensor factor.
The new factor has the same Frobenius norm, so normalization is preserved. -/
theorem triangular_normalForm_absorb_first_column
    {d : Type} [Fintype d] [DecidableEq d]
    (A B D : Matrix d d ℂ) (U₁ U₂ V₁ V₂ : Matrix.unitaryGroup d ℂ)
    (R₀ : Matrix d d ℂ) (hn : frobeniusSq R₀ = 1)
    (hf : (diagonalBlockUnitary U₁ U₂ : Matrix (Sum d d) (Sum d d) ℂ) *
        Matrix.fromBlocks A 0 B D *
        (diagonalBlockUnitary V₁ V₂ : Matrix (Sum d d) (Sum d d) ℂ) =
      scalarTriangularTensor (frobeniusSq A) (frobeniusSq B) (frobeniusSq D) R₀) :
    frobeniusSq (R₀ * (↑(star V₁) : Matrix d d ℂ)) = 1 ∧
      (diagonalBlockUnitary U₁ U₂ : Matrix (Sum d d) (Sum d d) ℂ) *
        Matrix.fromBlocks A 0 B D *
        (diagonalBlockUnitary 1 (V₂ * star V₁) : Matrix (Sum d d) (Sum d d) ℂ) =
      scalarTriangularTensor (frobeniusSq A) (frobeniusSq B) (frobeniusSq D)
        (R₀ * (↑(star V₁) : Matrix d d ℂ)) := by
  constructor
  · unfold frobeniusSq
    rw [outputGram_mul_unitary]
    exact hn
  · have hh := congrArg (fun X : Matrix (Sum d d) (Sum d d) ℂ =>
        X * (diagonalBlockUnitary (star V₁) (star V₁) : Matrix (Sum d d) (Sum d d) ℂ)) hf
    dsimp only at hh
    rw [Matrix.mul_assoc, diagonalBlockUnitary_mul, scalarTriangularTensor_mul_diagonal] at hh
    simpa using hh

/-- The literal manuscript normal form, with arbitrary block-diagonal row
and column unitaries and a normalized common Kronecker factor. -/
theorem square_triangular_entropy_equality_iff_four_unitaries
    {d : Type} [Fintype d] [DecidableEq d] [Nonempty d]
    (A B D : Matrix d d ℂ) (hBunit : IsUnit B)
    (hβ : 0 < frobeniusSq B)
    (hsum : frobeniusSq A + frobeniusSq B + frobeniusSq D = 1) :
    let T := Matrix.fromBlocks A 0 B D
    psdEntropy (T*T.conjTranspose) (Matrix.posSemidef_self_mul_conjTranspose T) =
      entanglementCurve (2*Real.sqrt (frobeniusSq A * frobeniusSq D)) +
        normalizedGramEntropy (frobeniusSq A) A + normalizedGramEntropy (frobeniusSq B) B +
        normalizedGramEntropy (frobeniusSq D) D ↔
    ∃ U₁ U₂ V₁ V₂ : Matrix.unitaryGroup d ℂ, ∃ R₀ : Matrix d d ℂ,
      frobeniusSq R₀ = 1 ∧
      Matrix.reindex (triangleTensorEquiv d) (triangleTensorEquiv d)
        ((diagonalBlockUnitary U₁ U₂ : Matrix (Sum d d) (Sum d d) ℂ) * T *
          (diagonalBlockUnitary V₁ V₂ : Matrix (Sum d d) (Sum d d) ℂ)) =
      (scalarTriangularMatrix (frobeniusSq A) (frobeniusSq B) (frobeniusSq D)) ⊗ₖ R₀ := by
  constructor
  · intro h
    obtain ⟨U₁,U₂,V₂,R₀,hn,hf⟩ :=
      (square_triangular_entropy_equality_iff_kronecker A B D hBunit hβ hsum).mp h
    exact ⟨U₁,U₂,1,V₂,R₀,hn,hf⟩
  · rintro ⟨U₁,U₂,V₁,V₂,R₀,hn,hf⟩
    have hf' : (diagonalBlockUnitary U₁ U₂ : Matrix (Sum d d) (Sum d d) ℂ) *
        Matrix.fromBlocks A 0 B D *
        (diagonalBlockUnitary V₁ V₂ : Matrix (Sum d d) (Sum d d) ℂ) =
        scalarTriangularTensor (frobeniusSq A) (frobeniusSq B) (frobeniusSq D) R₀ := by
      apply (Matrix.reindex (triangleTensorEquiv d) (triangleTensorEquiv d)).injective
      rw [scalarTriangularTensor_eq_kronecker]
      exact hf
    have h := triangular_normalForm_absorb_first_column A B D U₁ U₂ V₁ V₂ R₀ hn hf'
    exact (square_triangular_entropy_equality_iff_normalForm A B D hBunit hβ hsum).mpr
      ⟨U₁,U₂,V₂*star V₁, R₀ * (↑(star V₁) : Matrix d d ℂ),h.1,h.2⟩

end
end AmplitudeDamping
