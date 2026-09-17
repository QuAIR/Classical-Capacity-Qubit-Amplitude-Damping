import AmplitudeDamping.Triangular.Dephasing

/-!
# Scalar compression for the triangular entropy inequality

This module develops the direct-sum and scalar homogeneity layer needed after
the diagonal dephasing reduction.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

universe u

noncomputable section

/-- Spectral entropy rewritten as a multiset sum. -/
theorem psdEntropy_eq_neg_sum_eigenvalueMultiset
    {d : Type u} [Fintype d] [DecidableEq d]
    (X : Matrix d d ℂ) (hX : X.PosSemidef) :
    psdEntropy X hX =
      -((QIT.eigenvalueMultiset hX.isHermitian).map QIT.xlog2).sum := by
  unfold psdEntropy QIT.eigenvalueMultiset
  rw [Finset.sum_eq_multiset_sum, Multiset.map_map]
  rfl

/-- A homogeneous block diagonal of positive semidefinite matrices is
positive semidefinite. -/
theorem matrixBlockDiagonal_posSemidef
    {a ι : Type} [Fintype a] [DecidableEq a]
    [Fintype ι] [DecidableEq ι]
    (blocks : ι → Matrix a a ℂ)
    (hblocks : ∀ i, (blocks i).PosSemidef) :
    (Matrix.blockDiagonal blocks).PosSemidef := by
  let e : (a × ι) ≃ (ι × a) := Equiv.prodComm a ι
  have hclassical := QIT.Classical.blockDiagonal_posSemidef blocks hblocks
  have hreindexed := hclassical.submatrix e
  have heq :
      (QIT.Classical.blockDiagonal blocks).submatrix e e =
        Matrix.blockDiagonal blocks := by
    ext ⟨x, i⟩ ⟨y, j⟩
    by_cases hij : i = j
    · subst j
      have hblock := congrFun (congrFun
        (QIT.Classical.blockDiagonal_block_self blocks i) x) y
      change QIT.Classical.blockDiagonal blocks (i, x) (i, y) =
        Matrix.blockDiagonal blocks (x, i) (y, i)
      rw [Matrix.blockDiagonal_apply_eq]
      exact hblock
    · have hblock := QIT.Classical.blockDiagonal_block_ne blocks hij
      have hentry := congrFun (congrFun hblock x) y
      change QIT.Classical.blockDiagonal blocks (i, x) (j, y) =
        Matrix.blockDiagonal blocks (x, i) (y, j)
      rw [Matrix.blockDiagonal_apply_ne blocks x y hij]
      exact hentry
  rwa [heq] at hreindexed

/-- Spectral entropy is additive over a finite homogeneous block diagonal. -/
theorem psdEntropy_blockDiagonal
    {a ι : Type} [Fintype a] [DecidableEq a]
    [Fintype ι] [DecidableEq ι]
    (blocks : ι → Matrix a a ℂ)
    (hblocks : ∀ i, (blocks i).PosSemidef) :
    psdEntropy (Matrix.blockDiagonal blocks)
        (matrixBlockDiagonal_posSemidef blocks hblocks) =
      ∑ i, psdEntropy (blocks i) (hblocks i) := by
  rw [psdEntropy_eq_neg_sum_eigenvalueMultiset]
  rw [QIT.eigenvalueMultiset_blockDiagonal blocks
    (fun i => (hblocks i).isHermitian)]
  simp_rw [psdEntropy_eq_neg_sum_eigenvalueMultiset]
  rw [Multiset.map_bind, QIT.multiset_sum_bind]
  simp [Finset.sum_neg_distrib]

/-- Positive square root of a nonnegative real diagonal matrix. -/
theorem psdSqrt_diagonal_ofReal
    {d : Type} [Fintype d] [DecidableEq d]
    (x : d → ℝ) (hx : ∀ i, 0 ≤ x i) :
    QIT.psdSqrt (Matrix.diagonal fun i => ((x i : ℝ) : ℂ)) =
      Matrix.diagonal fun i => ((Real.sqrt (x i) : ℝ) : ℂ) := by
  let S : Matrix d d ℂ :=
    Matrix.diagonal fun i => ((Real.sqrt (x i) : ℝ) : ℂ)
  have hSsq : S * S = Matrix.diagonal fun i => ((x i : ℝ) : ℂ) := by
    dsimp [S]
    rw [Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    norm_cast
    exact Real.mul_self_sqrt (hx i)
  have hSpos : S.PosSemidef := by
    refine Matrix.PosSemidef.diagonal (d := fun i =>
      ((Real.sqrt (x i) : ℝ) : ℂ)) ?_
    intro i
    change (0 : ℂ) ≤ ((Real.sqrt (x i) : ℝ) : ℂ)
    exact_mod_cast Real.sqrt_nonneg (x i)
  change QIT.psdSqrt (Matrix.diagonal fun i => ((x i : ℝ) : ℂ)) = S
  simpa [QIT.psdSqrt, S] using
    (CFC.sqrt_unique
      (a := Matrix.diagonal fun i => ((x i : ℝ) : ℂ))
      (b := S) hSsq hSpos.nonneg)

/-- A real diagonal matrix with nonnegative entries is positive semidefinite. -/
theorem diagonalOfReal_posSemidef
    {d : Type} [Fintype d] [DecidableEq d]
    (x : d → ℝ) (hx : ∀ i, 0 ≤ x i) :
    (Matrix.diagonal fun i => ((x i : ℝ) : ℂ)).PosSemidef := by
  refine Matrix.PosSemidef.diagonal
    (d := fun i => ((x i : ℝ) : ℂ)) ?_
  show ∀ i, (0 : ℂ) ≤ ((x i : ℝ) : ℂ)
  intro i
  exact_mod_cast hx i

/-- A one-dimensional real scalar as a `1 × 1` complex matrix. -/
def scalarMatrix (x : ℝ) : Matrix Unit Unit ℂ :=
  Matrix.diagonal fun _ => ((x : ℝ) : ℂ)

/-- The explicit scalar `2 × 2` coupling block. -/
def scalarCouplingBlock (p q r : ℝ) :
    Matrix (Sum Unit Unit) (Sum Unit Unit) ℂ :=
  Matrix.fromBlocks
    (scalarMatrix (p + q))
    (scalarMatrix (Real.sqrt q * Real.sqrt r))
    (scalarMatrix (Real.sqrt r * Real.sqrt q))
    (scalarMatrix r)

/-- Relabel the two copies of `d` by a scalar two-level label and a coordinate. -/
def sumToScalarProdEquiv {d : Type} :
    Sum d d ≃ (Sum Unit Unit) × d where
  toFun
    | Sum.inl i => (Sum.inl Unit.unit, i)
    | Sum.inr i => (Sum.inr Unit.unit, i)
  invFun
    | (Sum.inl _, i) => Sum.inl i
    | (Sum.inr _, i) => Sum.inr i
  left_inv x := by cases x <;> rfl
  right_inv x := by
    rcases x with ⟨s, i⟩
    rcases s with u | u <;> cases u <;> rfl

/-- For diagonal real inputs, the entropy coupling is, after a basis
relabeling, the direct sum of the scalar coupling blocks. -/
theorem entropyCoupling_diagonal_reindex_eq_blockDiagonal
    {d : Type} [Fintype d] [DecidableEq d]
    (p q r : d → ℝ) (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i) :
    (entropyCoupling
        (Matrix.diagonal fun i => ((p i : ℝ) : ℂ))
        (Matrix.diagonal fun i => ((q i : ℝ) : ℂ))
        (Matrix.diagonal fun i => ((r i : ℝ) : ℂ))).submatrix
          (sumToScalarProdEquiv (d := d)).symm
          (sumToScalarProdEquiv (d := d)).symm =
      Matrix.blockDiagonal fun i => scalarCouplingBlock (p i) (q i) (r i) := by
  unfold entropyCoupling
  rw [show QIT.psdSqrt (Matrix.diagonal fun i => ((q i : ℝ) : ℂ)) =
      Matrix.diagonal fun i => ((Real.sqrt (q i) : ℝ) : ℂ) by
    exact psdSqrt_diagonal_ofReal q hq]
  rw [show QIT.psdSqrt (Matrix.diagonal fun i => ((r i : ℝ) : ℂ)) =
      Matrix.diagonal fun i => ((Real.sqrt (r i) : ℝ) : ℂ) by
    exact psdSqrt_diagonal_ofReal r hr]
  ext ⟨s, i⟩ ⟨t, j⟩
  rcases s with u | u <;> cases u <;>
    rcases t with v | v <;> cases v
  all_goals by_cases hij : i = j
  all_goals
    simp [scalarCouplingBlock, scalarMatrix,
      sumToScalarProdEquiv, Matrix.blockDiagonal_apply, hij,
      Matrix.diagonal_mul_diagonal]

/-- Spectral entropy is invariant under a finite basis relabeling. -/
theorem psdEntropy_reindex
    {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b]
    (X : Matrix a a ℂ) (hX : X.PosSemidef) (e : a ≃ b) :
    psdEntropy (X.submatrix e.symm e.symm) (hX.submatrix e.symm) =
      psdEntropy X hX := by
  rw [psdEntropy_eq_neg_sum_eigenvalueMultiset,
    psdEntropy_eq_neg_sum_eigenvalueMultiset]
  exact congrArg (fun s : Multiset ℝ => -((s.map QIT.xlog2).sum))
    (QIT.eigenvalueMultiset_reindex X hX.isHermitian e)

/-- A scalar matrix is positive semidefinite exactly when its real entry is
nonnegative (only the forward construction is needed here). -/
theorem scalarMatrix_posSemidef (x : ℝ) (hx : 0 ≤ x) :
    (scalarMatrix x).PosSemidef := by
  refine Matrix.PosSemidef.diagonal (d := fun _ : Unit => ((x : ℝ) : ℂ)) ?_
  show ∀ _ : Unit, (0 : ℂ) ≤ ((x : ℝ) : ℂ)
  intro _
  exact_mod_cast hx

/-- Entropy of a nonnegative scalar matrix. -/
theorem psdEntropy_scalarMatrix (x : ℝ) (hx : 0 ≤ x) :
    psdEntropy (scalarMatrix x) (scalarMatrix_posSemidef x hx) =
      -QIT.xlog2 x := by
  rw [psdEntropy_eq_neg_sum_eigenvalueMultiset]
  rw [show QIT.eigenvalueMultiset
      (scalarMatrix_posSemidef x hx).isHermitian =
        Multiset.map (fun _ : Unit => x) Finset.univ.val by
    exact QIT.eigenvalueMultiset_diagonal_ofReal (fun _ : Unit => x) _]
  simp

/-- The explicit scalar block agrees with the general entropy coupling on
one-dimensional scalar matrices. -/
theorem scalarCouplingBlock_eq_entropyCoupling
    (p q r : ℝ) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    scalarCouplingBlock p q r =
      entropyCoupling (scalarMatrix p) (scalarMatrix q) (scalarMatrix r) := by
  have hsqrtq : QIT.psdSqrt
      (Matrix.diagonal fun _ : Unit => ((q : ℝ) : ℂ)) =
        Matrix.diagonal fun _ : Unit => ((Real.sqrt q : ℝ) : ℂ) := by
    exact psdSqrt_diagonal_ofReal (fun _ : Unit => q) (fun _ => hq)
  have hsqrtr : QIT.psdSqrt
      (Matrix.diagonal fun _ : Unit => ((r : ℝ) : ℂ)) =
        Matrix.diagonal fun _ : Unit => ((Real.sqrt r : ℝ) : ℂ) := by
    exact psdSqrt_diagonal_ofReal (fun _ : Unit => r) (fun _ => hr)
  unfold scalarCouplingBlock entropyCoupling
  unfold scalarMatrix
  rw [Matrix.fromBlocks_inj]
  refine ⟨?_, ?_, ?_, rfl⟩
  · ext i j
    simp
  · rw [hsqrtq, hsqrtr]
    ext i j
    simp
  · rw [hsqrtq, hsqrtr]
    ext i j
    simp

/-- Positivity of every scalar coupling block. -/
theorem scalarCouplingBlock_posSemidef
    (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    (scalarCouplingBlock p q r).PosSemidef := by
  rw [scalarCouplingBlock_eq_entropyCoupling p q r hq hr]
  exact entropyCoupling_posSemidef
    (scalarMatrix p) (scalarMatrix q) (scalarMatrix r)
    (scalarMatrix_posSemidef p hp)
    (scalarMatrix_posSemidef q hq)
    (scalarMatrix_posSemidef r hr)

/-- Entropy of a nonnegative real diagonal matrix is the sum of the scalar
entropies of its entries. -/
theorem psdEntropy_diagonal_ofReal
    {d : Type} [Fintype d] [DecidableEq d]
    (x : d → ℝ) (hx : ∀ i, 0 ≤ x i) :
    psdEntropy (Matrix.diagonal fun i => ((x i : ℝ) : ℂ))
        (diagonalOfReal_posSemidef x hx) =
      ∑ i, psdEntropy (scalarMatrix (x i))
        (scalarMatrix_posSemidef (x i) (hx i)) := by
  rw [psdEntropy_eq_neg_sum_eigenvalueMultiset]
  rw [QIT.eigenvalueMultiset_diagonal_ofReal x]
  rw [Multiset.map_map, ← Finset.sum_eq_multiset_sum]
  rw [← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro i _
  exact (psdEntropy_scalarMatrix (x i) (hx i)).symm

/-- One-dimensional specialization of the entropy defect. -/
def scalarEntropyDefect
    (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) : ℝ :=
  entropyDefect (scalarMatrix p) (scalarMatrix q) (scalarMatrix r)
    (scalarMatrix_posSemidef p hp)
    (scalarMatrix_posSemidef q hq)
    (scalarMatrix_posSemidef r hr)

/-- For nonnegative diagonal inputs, the entropy defect decomposes exactly as
the sum of its one-dimensional coordinate defects. -/
theorem entropyDefect_diagonal_eq_sum_scalar
    {d : Type} [Fintype d] [DecidableEq d]
    (p q r : d → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 ≤ q i) (hr : ∀ i, 0 ≤ r i) :
    entropyDefect
        (Matrix.diagonal fun i => ((p i : ℝ) : ℂ))
        (Matrix.diagonal fun i => ((q i : ℝ) : ℂ))
        (Matrix.diagonal fun i => ((r i : ℝ) : ℂ))
        (diagonalOfReal_posSemidef p hp)
        (diagonalOfReal_posSemidef q hq)
        (diagonalOfReal_posSemidef r hr) =
      ∑ i, scalarEntropyDefect (p i) (q i) (r i)
        (hp i) (hq i) (hr i) := by
  let P : Matrix d d ℂ := Matrix.diagonal fun i => ((p i : ℝ) : ℂ)
  let Q : Matrix d d ℂ := Matrix.diagonal fun i => ((q i : ℝ) : ℂ)
  let R : Matrix d d ℂ := Matrix.diagonal fun i => ((r i : ℝ) : ℂ)
  let hP : P.PosSemidef := diagonalOfReal_posSemidef p hp
  let hQ : Q.PosSemidef := diagonalOfReal_posSemidef q hq
  let hR : R.PosSemidef := diagonalOfReal_posSemidef r hr
  have hblocks : ∀ i,
      (scalarCouplingBlock (p i) (q i) (r i)).PosSemidef := fun i =>
    scalarCouplingBlock_posSemidef (p i) (q i) (r i)
      (hp i) (hq i) (hr i)
  have hcouplingEntropy :
      psdEntropy (entropyCoupling P Q R)
          (entropyCoupling_posSemidef P Q R hP hQ hR) =
        ∑ i, psdEntropy (scalarCouplingBlock (p i) (q i) (r i))
          (hblocks i) := by
    let e := sumToScalarProdEquiv (d := d)
    calc
      _ = psdEntropy
          ((entropyCoupling P Q R).submatrix e.symm e.symm)
          ((entropyCoupling_posSemidef P Q R hP hQ hR).submatrix e.symm) :=
        (psdEntropy_reindex (entropyCoupling P Q R)
          (entropyCoupling_posSemidef P Q R hP hQ hR) e).symm
      _ = psdEntropy
          (Matrix.blockDiagonal fun i => scalarCouplingBlock (p i) (q i) (r i))
          (matrixBlockDiagonal_posSemidef _ hblocks) := by
        apply psdEntropy_congr
        simpa [P, Q, R, e] using
          entropyCoupling_diagonal_reindex_eq_blockDiagonal p q r hq hr
      _ = _ := psdEntropy_blockDiagonal _ hblocks
  have hPentropy : psdEntropy P hP =
      ∑ i, psdEntropy (scalarMatrix (p i))
        (scalarMatrix_posSemidef (p i) (hp i)) := by
    simpa [P, hP] using psdEntropy_diagonal_ofReal p hp
  have hQentropy : psdEntropy Q hQ =
      ∑ i, psdEntropy (scalarMatrix (q i))
        (scalarMatrix_posSemidef (q i) (hq i)) := by
    simpa [Q, hQ] using psdEntropy_diagonal_ofReal q hq
  have hRentropy : psdEntropy R hR =
      ∑ i, psdEntropy (scalarMatrix (r i))
        (scalarMatrix_posSemidef (r i) (hr i)) := by
    simpa [R, hR] using psdEntropy_diagonal_ofReal r hr
  change entropyDefect P Q R hP hQ hR = _
  unfold scalarEntropyDefect entropyDefect
  rw [hcouplingEntropy, hPentropy, hQentropy, hRentropy]
  rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib,
    ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  have hblockEntropy :
      psdEntropy (scalarCouplingBlock (p i) (q i) (r i)) (hblocks i) =
        psdEntropy
          (entropyCoupling (scalarMatrix (p i)) (scalarMatrix (q i))
            (scalarMatrix (r i)))
          (entropyCoupling_posSemidef
            (scalarMatrix (p i)) (scalarMatrix (q i)) (scalarMatrix (r i))
            (scalarMatrix_posSemidef (p i) (hp i))
            (scalarMatrix_posSemidef (q i) (hq i))
            (scalarMatrix_posSemidef (r i) (hr i))) := by
    exact psdEntropy_congr
      (scalarCouplingBlock_eq_entropyCoupling (p i) (q i) (r i)
        (hq i) (hr i)) _ _
  rw [hblockEntropy]

/-- Product rule for the repository's `x log₂ x` convention on nonnegative
real arguments. -/
theorem xlog2_mul_of_nonneg
    {x y : ℝ} (_hx : 0 ≤ x) (_hy : 0 ≤ y) :
    QIT.xlog2 (x * y) =
      y * QIT.xlog2 x + x * QIT.xlog2 y := by
  by_cases hx0 : x = 0
  · simp [hx0, QIT.xlog2]
  by_cases hy0 : y = 0
  · simp [hy0, QIT.xlog2]
  have hxy0 : x * y ≠ 0 := mul_ne_zero hx0 hy0
  simp only [QIT.xlog2, if_neg hx0, if_neg hy0, if_neg hxy0, QIT.log2]
  rw [Real.log_mul hx0 hy0]
  ring

/-- Spectral entropy under multiplication by a nonnegative real scalar. -/
theorem psdEntropy_real_smul
    {d : Type} [Fintype d] [DecidableEq d]
    (c : ℝ) (hc : 0 ≤ c) (X : Matrix d d ℂ) (hX : X.PosSemidef) :
    psdEntropy ((c : ℂ) • X) (hX.smul (by exact_mod_cast hc)) =
      c * psdEntropy X hX - QIT.xlog2 c * X.trace.re := by
  let hscaled : ((c : ℂ) • X).PosSemidef := hX.smul (by exact_mod_cast hc)
  have hspectrum :
      QIT.eigenvalueMultiset hscaled.isHermitian =
        Multiset.map (fun x : ℝ => c * x)
          (QIT.eigenvalueMultiset hX.isHermitian) := by
    simpa [hscaled] using
      QIT.eigenvalueMultiset_smul_ofReal c X hX.isHermitian
  have heigen_nonneg : ∀ x ∈ QIT.eigenvalueMultiset hX.isHermitian,
      0 ≤ x := by
    intro x hxmem
    rw [QIT.eigenvalueMultiset] at hxmem
    rcases Multiset.mem_map.mp hxmem with ⟨i, _, rfl⟩
    exact hX.eigenvalues_nonneg i
  have hsum : (QIT.eigenvalueMultiset hX.isHermitian).sum = X.trace.re := by
    rw [QIT.eigenvalueMultiset, ← Finset.sum_eq_multiset_sum]
    have htrace := congrArg Complex.re hX.isHermitian.trace_eq_sum_eigenvalues
    simpa using htrace.symm
  rw [psdEntropy_eq_neg_sum_eigenvalueMultiset,
    psdEntropy_eq_neg_sum_eigenvalueMultiset, hspectrum,
    Multiset.map_map]
  have hmap :
      (Multiset.map (fun x : ℝ => QIT.xlog2 (c * x))
          (QIT.eigenvalueMultiset hX.isHermitian)).sum =
        QIT.xlog2 c * (QIT.eigenvalueMultiset hX.isHermitian).sum +
          c * (Multiset.map QIT.xlog2
            (QIT.eigenvalueMultiset hX.isHermitian)).sum := by
    calc
      _ = (Multiset.map (fun x : ℝ =>
          x * QIT.xlog2 c + c * QIT.xlog2 x)
          (QIT.eigenvalueMultiset hX.isHermitian)).sum := by
        apply congrArg Multiset.sum
        apply Multiset.map_congr rfl
        intro x hxmem
        exact xlog2_mul_of_nonneg hc (heigen_nonneg x hxmem)
      _ = _ := by
        rw [QIT.multiset_sum_add_distrib]
        have hright :
            (Multiset.map (fun x : ℝ => c * QIT.xlog2 x)
              (QIT.eigenvalueMultiset hX.isHermitian)).sum =
              (Multiset.map QIT.xlog2
                (QIT.eigenvalueMultiset hX.isHermitian)).sum * c := by
          calc
            _ = (Multiset.map (fun x : ℝ => QIT.xlog2 x * c)
                (QIT.eigenvalueMultiset hX.isHermitian)).sum := by
              apply congrArg Multiset.sum
              apply Multiset.map_congr rfl
              intro x _
              ring
            _ = _ := QIT.multiset_sum_mul_const _ _ _
        rw [QIT.multiset_sum_mul_const, hright]
        rw [Multiset.map_id']
        ring
  change -(Multiset.map (fun x : ℝ => QIT.xlog2 (c * x))
      (QIT.eigenvalueMultiset hX.isHermitian)).sum = _
  rw [hmap, hsum]
  ring

/-- The coupling matrix is positively homogeneous when all three inputs are
scaled by the same nonnegative real scalar. -/
theorem entropyCoupling_real_smul
    {d : Type} [Fintype d] [DecidableEq d]
    (c : ℝ) (hc : 0 ≤ c) (P Q R : Matrix d d ℂ)
    (hQ : Q.PosSemidef) (hR : R.PosSemidef) :
    entropyCoupling ((c : ℂ) • P) ((c : ℂ) • Q) ((c : ℂ) • R) =
      (c : ℂ) • entropyCoupling P Q R := by
  unfold entropyCoupling
  rw [QIT.psdSqrt_real_smul hc hQ, QIT.psdSqrt_real_smul hc hR]
  ext i j
  rcases i with i | i <;> rcases j with j | j
  all_goals
    simp [Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂,
      smul_smul, Real.mul_self_sqrt hc] <;> ring

/-- Positive homogeneity of the entropy defect.  The scalar entropy correction
terms cancel because the coupling and its three inputs have the same trace. -/
theorem entropyDefect_real_smul
    {d : Type} [Fintype d] [DecidableEq d]
    (c : ℝ) (hc : 0 ≤ c) (P Q R : Matrix d d ℂ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosSemidef) :
    entropyDefect ((c : ℂ) • P) ((c : ℂ) • Q) ((c : ℂ) • R)
        (hP.smul (by exact_mod_cast hc))
        (hQ.smul (by exact_mod_cast hc))
        (hR.smul (by exact_mod_cast hc)) =
      c * entropyDefect P Q R hP hQ hR := by
  let hP' : ((c : ℂ) • P).PosSemidef := hP.smul (by exact_mod_cast hc)
  let hQ' : ((c : ℂ) • Q).PosSemidef := hQ.smul (by exact_mod_cast hc)
  let hR' : ((c : ℂ) • R).PosSemidef := hR.smul (by exact_mod_cast hc)
  let Z := entropyCoupling P Q R
  let hZ : Z.PosSemidef := entropyCoupling_posSemidef P Q R hP hQ hR
  have hZeq : entropyCoupling ((c : ℂ) • P) ((c : ℂ) • Q) ((c : ℂ) • R) =
      (c : ℂ) • Z := entropyCoupling_real_smul c hc P Q R hQ hR
  have hZentropy :
      psdEntropy
          (entropyCoupling ((c : ℂ) • P) ((c : ℂ) • Q) ((c : ℂ) • R))
          (entropyCoupling_posSemidef
            ((c : ℂ) • P) ((c : ℂ) • Q) ((c : ℂ) • R) hP' hQ' hR') =
        c * psdEntropy Z hZ - QIT.xlog2 c * Z.trace.re := by
    calc
      _ = psdEntropy ((c : ℂ) • Z) (hZ.smul (by exact_mod_cast hc)) :=
        psdEntropy_congr hZeq _ _
      _ = _ := psdEntropy_real_smul c hc Z hZ
  have htrace : Z.trace.re = P.trace.re + Q.trace.re + R.trace.re := by
    rw [show Z.trace = P.trace + Q.trace + R.trace by
      exact entropyCoupling_trace P Q R]
    simp
  change entropyDefect ((c : ℂ) • P) ((c : ℂ) • Q) ((c : ℂ) • R)
      hP' hQ' hR' = _
  unfold entropyDefect
  rw [hZentropy,
    psdEntropy_real_smul c hc P hP,
    psdEntropy_real_smul c hc Q hQ,
    psdEntropy_real_smul c hc R hR,
    htrace]
  ring

/-- Scalar matrices commute with real scalar multiplication. -/
theorem scalarMatrix_mul (c x : ℝ) :
    scalarMatrix (c * x) = (c : ℂ) • scalarMatrix x := by
  ext i j
  cases i
  cases j
  simp [scalarMatrix]

/-- Positive homogeneity of the one-dimensional entropy defect. -/
theorem scalarEntropyDefect_real_smul
    (c p q r : ℝ) (hc : 0 ≤ c) (hp : 0 ≤ p)
    (hq : 0 ≤ q) (hr : 0 ≤ r) :
    scalarEntropyDefect (c * p) (c * q) (c * r)
        (mul_nonneg hc hp) (mul_nonneg hc hq) (mul_nonneg hc hr) =
      c * scalarEntropyDefect p q r hp hq hr := by
  let hP := scalarMatrix_posSemidef p hp
  let hQ := scalarMatrix_posSemidef q hq
  let hR := scalarMatrix_posSemidef r hr
  have hcC : (0 : ℂ) ≤ (c : ℂ) := by exact_mod_cast hc
  unfold scalarEntropyDefect
  calc
    _ = entropyDefect
        ((c : ℂ) • scalarMatrix p)
        ((c : ℂ) • scalarMatrix q)
        ((c : ℂ) • scalarMatrix r)
        (hP.smul hcC) (hQ.smul hcC) (hR.smul hcC) := by
      exact entropyDefect_congr
        (scalarMatrix_mul c p) (scalarMatrix_mul c q) (scalarMatrix_mul c r)
        _ _ _ _ _ _
    _ = c * entropyDefect (scalarMatrix p) (scalarMatrix q) (scalarMatrix r)
        hP hQ hR := entropyDefect_real_smul c hc
          (scalarMatrix p) (scalarMatrix q) (scalarMatrix r) hP hQ hR

/-- Perspective identity obtained from positive homogeneity when the middle
scalar is strictly positive. -/
theorem scalarEntropyDefect_perspective
    (p q r : ℝ) (hp : 0 ≤ p) (hq : 0 < q) (hr : 0 ≤ r) :
    scalarEntropyDefect p q r hp hq.le hr =
      q * scalarEntropyDefect (p / q) 1 (r / q)
        (div_nonneg hp hq.le) zero_le_one (div_nonneg hr hq.le) := by
  have hscale := scalarEntropyDefect_real_smul
    q (p / q) 1 (r / q) hq.le
    (div_nonneg hp hq.le) zero_le_one (div_nonneg hr hq.le)
  have hpq : q * (p / q) = p := by field_simp
  have hrq : q * (r / q) = r := by field_simp
  simpa [hpq, hrq] using hscale

/-- Scalar perspective Jensen inequality when every middle coordinate is
strictly positive. -/
theorem scalarEntropyDefect_sum_le_of_middle_pos
    {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
    (p q r : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i) (hr : ∀ i, 0 ≤ r i) :
    scalarEntropyDefect (∑ i, p i) (∑ i, q i) (∑ i, r i)
        (Finset.sum_nonneg fun i _ => hp i)
        (Finset.sum_nonneg fun i _ => (hq i).le)
        (Finset.sum_nonneg fun i _ => hr i) ≤
      ∑ i, scalarEntropyDefect (p i) (q i) (r i)
        (hp i) (hq i).le (hr i) := by
  classical
  let ps : ℝ := ∑ i, p i
  let qs : ℝ := ∑ i, q i
  let rs : ℝ := ∑ i, r i
  have hps : 0 ≤ ps := Finset.sum_nonneg fun i _ => hp i
  have hrs : 0 ≤ rs := Finset.sum_nonneg fun i _ => hr i
  let i0 : ι := Classical.choice inferInstance
  have hqs : 0 < qs := by
    exact Finset.sum_pos'
      (fun i _ => (hq i).le) ⟨i0, Finset.mem_univ i0, hq i0⟩
  let Q1 : Matrix Unit Unit ℂ := scalarMatrix 1
  let hQ1 : Q1.PosSemidef := scalarMatrix_posSemidef 1 zero_le_one
  let w : ι → ℝ := fun i => q i / qs
  let X : ι → Matrix Unit Unit ℂ × Matrix Unit Unit ℂ := fun i =>
    (scalarMatrix (p i / q i), scalarMatrix (r i / q i))
  have hw : ∀ i ∈ (Finset.univ : Finset ι), 0 ≤ w i := by
    intro i _
    exact div_nonneg (hq i).le hqs.le
  have hsum : ∑ i ∈ (Finset.univ : Finset ι), w i = 1 := by
    change (∑ i, q i / qs) = 1
    rw [← Finset.sum_div]
    change qs / qs = 1
    exact div_self hqs.ne'
  have hX : ∀ i ∈ (Finset.univ : Finset ι),
      (X i).1.PosSemidef ∧ (X i).2.PosSemidef := by
    intro i _
    exact ⟨
      scalarMatrix_posSemidef _ (div_nonneg (hp i) (hq i).le),
      scalarMatrix_posSemidef _ (div_nonneg (hr i) (hq i).le)⟩
  have hweightedP (i : ι) :
      w i • scalarMatrix (p i / q i) = scalarMatrix (p i / qs) := by
    ext u v
    cases u
    cases v
    simp [w, scalarMatrix]
    field_simp [hqs.ne', (hq i).ne']
  have hweightedR (i : ι) :
      w i • scalarMatrix (r i / q i) = scalarMatrix (r i / qs) := by
    ext u v
    cases u
    cases v
    simp [w, scalarMatrix]
    field_simp [hqs.ne', (hq i).ne']
  have havg :
      (∑ i ∈ (Finset.univ : Finset ι), w i • X i) =
        (scalarMatrix (ps / qs), scalarMatrix (rs / qs)) := by
    apply Prod.ext
    · simp only [Prod.fst_sum, Prod.smul_fst]
      simp_rw [show ∀ i, (X i).1 = scalarMatrix (p i / q i) by
        intro i
        rfl, hweightedP]
      ext u v
      cases u
      cases v
      simp [Matrix.sum_apply, scalarMatrix, ps, Finset.sum_div]
    · simp only [Prod.snd_sum, Prod.smul_snd]
      simp_rw [show ∀ i, (X i).2 = scalarMatrix (r i / q i) by
        intro i
        rfl, hweightedR]
      ext u v
      cases u
      cases v
      simp [Matrix.sum_apply, scalarMatrix, rs, Finset.sum_div]
  have hvalue (i : ι) :
      entropyDefectTotal Q1 hQ1 (X i) =
        scalarEntropyDefect (p i / q i) 1 (r i / q i)
          (div_nonneg (hp i) (hq i).le) zero_le_one
          (div_nonneg (hr i) (hq i).le) := by
    have hPi := scalarMatrix_posSemidef (p i / q i)
      (div_nonneg (hp i) (hq i).le)
    have hRi := scalarMatrix_posSemidef (r i / q i)
      (div_nonneg (hr i) (hq i).le)
    change entropyDefectTotal (scalarMatrix 1)
        (scalarMatrix_posSemidef 1 zero_le_one)
        (scalarMatrix (p i / q i), scalarMatrix (r i / q i)) = _
    simp [entropyDefectTotal, scalarEntropyDefect, hPi, hRi]
  have hjensen := entropyDefectTotal_map_sum_le
    Q1 hQ1 (Finset.univ : Finset ι) w X hw hsum hX
  rw [havg] at hjensen
  have hleft :
      entropyDefectTotal Q1 hQ1
          (scalarMatrix (ps / qs), scalarMatrix (rs / qs)) =
        scalarEntropyDefect (ps / qs) 1 (rs / qs)
          (div_nonneg hps hqs.le) zero_le_one (div_nonneg hrs hqs.le) := by
    have hPs := scalarMatrix_posSemidef (ps / qs) (div_nonneg hps hqs.le)
    have hRs := scalarMatrix_posSemidef (rs / qs) (div_nonneg hrs hqs.le)
    change entropyDefectTotal (scalarMatrix 1)
        (scalarMatrix_posSemidef 1 zero_le_one)
        (scalarMatrix (ps / qs), scalarMatrix (rs / qs)) = _
    simp [entropyDefectTotal, scalarEntropyDefect, hPs, hRs]
  rw [hleft] at hjensen
  simp_rw [hvalue] at hjensen
  have htotal := scalarEntropyDefect_perspective ps qs rs hps hqs hrs
  have hcoord (i : ι) :=
    scalarEntropyDefect_perspective (p i) (q i) (r i) (hp i) (hq i) (hr i)
  calc
    scalarEntropyDefect (∑ i, p i) (∑ i, q i) (∑ i, r i)
        (Finset.sum_nonneg fun i _ => hp i)
        (Finset.sum_nonneg fun i _ => (hq i).le)
        (Finset.sum_nonneg fun i _ => hr i) =
      qs * scalarEntropyDefect (ps / qs) 1 (rs / qs)
        (div_nonneg hps hqs.le) zero_le_one (div_nonneg hrs hqs.le) := by
          simpa [ps, qs, rs] using htotal
    _ ≤ qs * (∑ i ∈ (Finset.univ : Finset ι),
        w i • scalarEntropyDefect (p i / q i) 1 (r i / q i)
          (div_nonneg (hp i) (hq i).le) zero_le_one
          (div_nonneg (hr i) (hq i).le)) :=
      mul_le_mul_of_nonneg_left hjensen hqs.le
    _ = ∑ i, scalarEntropyDefect (p i) (q i) (r i)
        (hp i) (hq i).le (hr i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      have hi := hcoord i
      rw [hi]
      simp only [w, smul_eq_mul]
      field_simp [hqs.ne', (hq i).ne']

end

end AmplitudeDamping
