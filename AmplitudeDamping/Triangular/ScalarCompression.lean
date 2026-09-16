import AmplitudeDamping.Triangular.Dephasing

/-!
# Scalar compression for the triangular entropy inequality

This module develops the direct-sum and scalar homogeneity layer needed after
the diagonal dephasing reduction.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Spectral entropy rewritten as a multiset sum. -/
theorem psdEntropy_eq_neg_sum_eigenvalueMultiset
    {d : Type} [Fintype d] [DecidableEq d]
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

end

end AmplitudeDamping
