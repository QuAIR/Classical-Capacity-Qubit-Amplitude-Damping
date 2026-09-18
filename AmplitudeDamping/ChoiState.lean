import AmplitudeDamping.Wootters
import AmplitudeDamping.ScalarCurve

/-!
# The Choi state of the amplitude-damping channel

Manuscript eq. `(choi)`: the normalized Choi state of the amplitude-damping
channel, across the reference/output bipartition, is

`ω_p = (1/2) [[1, 0, 0, √(1-p)], [0, 0, 0, 0], [0, 0, p, 0], [√(1-p), 0, 0, 1-p]]`

in the basis `|00⟩, |01⟩, |10⟩, |11⟩` of `Qubit × Qubit`.  This module
realizes `ω_p` as the average of an explicit two-branch pure decomposition
with branch vectors

`ψ± = (√(1/2), 0, ±i√(p/2), √((1-p)/2))`,

which certifies positivity and unit trace elementarily, and reads off the
entry table of eq. `(choi)`; in particular `|01⟩` lies in the kernel of
`ω_p` for every physical `p`, so the Wootters corner-formula interface
hypothesis applies and gives the first half of eq. `(choi-cost)`:

`E_F(ω_p) = entanglementCurve (√(1-p)) = h₂((1 + √p)/2)`.

The two-branch decomposition itself costs exactly this value (both branch
marginals have the spectrum `(1 ± √p)/2`), so the explicit decomposition is
optimal; the branch-cost bound is recorded as
`choiState_entanglementOfFormation_le_branchCost`.
-/

open scoped BigOperators ComplexConjugate ComplexOrder Matrix MatrixOrder NNReal

namespace AmplitudeDamping

open QIT

noncomputable section

/-! ### The two branch vectors -/

/-- The amplitudes of the two Choi branch vectors `ψ±` on the computational
basis `|00⟩, |01⟩, |10⟩, |11⟩`: with `s = true`, the vector
`(√(1/2), 0, i√(p/2), √((1-p)/2))`; with `s = false`, the conjugate-sign
vector `(√(1/2), 0, -i√(p/2), √((1-p)/2))`. -/
def choiAmp (p : ℝ) (s : Bool) : Qubit × Qubit → ℂ :=
  fun x =>
    if x = (0, 0) then ((Real.sqrt (1 / 2) : ℝ) : ℂ)
    else if x = (1, 0) then
      (if s then Complex.I else -Complex.I) * ((Real.sqrt (p / 2) : ℝ) : ℂ)
    else if x = (1, 1) then ((Real.sqrt ((1 - p) / 2) : ℝ) : ℂ)
    else 0

@[simp] theorem choiAmp_zero_zero (p : ℝ) (s : Bool) :
    choiAmp p s (0, 0) = ((Real.sqrt (1 / 2) : ℝ) : ℂ) := by
  simp [choiAmp]

@[simp] theorem choiAmp_zero_one (p : ℝ) (s : Bool) :
    choiAmp p s (0, 1) = 0 := by
  simp [choiAmp]

@[simp] theorem choiAmp_one_zero_true (p : ℝ) :
    choiAmp p true (1, 0) = Complex.I * ((Real.sqrt (p / 2) : ℝ) : ℂ) := by
  simp [choiAmp]

@[simp] theorem choiAmp_one_zero_false (p : ℝ) :
    choiAmp p false (1, 0) = -Complex.I * ((Real.sqrt (p / 2) : ℝ) : ℂ) := by
  simp [choiAmp]

@[simp] theorem choiAmp_one_one (p : ℝ) (s : Bool) :
    choiAmp p s (1, 1) = ((Real.sqrt ((1 - p) / 2) : ℝ) : ℂ) := by
  simp [choiAmp]

/-- The trace of a rank-one kernel is the sum of the squared moduli. -/
theorem trace_rankOne_eq_sum_normSq {a : Type _} [Fintype a] [DecidableEq a]
    (v : a → ℂ) :
    (rankOneMatrix v).trace = ∑ x, ((Complex.normSq (v x) : ℝ) : ℂ) := by
  rw [rankOneMatrix_trace, dotProduct]
  exact Finset.sum_congr rfl fun x _ => by rw [Complex.star_def, Complex.mul_conj]

theorem choiAmp_normSq_zero_zero (p : ℝ) (s : Bool) :
    Complex.normSq (choiAmp p s (0, 0)) = 1 / 2 := by
  rw [choiAmp_zero_zero, Complex.normSq_ofReal,
    Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)]

@[simp] theorem choiAmp_normSq_zero_one (p : ℝ) (s : Bool) :
    Complex.normSq (choiAmp p s (0, 1)) = 0 := by
  rw [choiAmp_zero_one, Complex.normSq_zero]

theorem choiAmp_normSq_one_zero_true (p : ℝ) (hp0 : 0 ≤ p) :
    Complex.normSq (choiAmp p true (1, 0)) = p / 2 := by
  rw [choiAmp_one_zero_true, Complex.normSq_mul, Complex.normSq_I,
    Complex.normSq_ofReal,
    Real.mul_self_sqrt (show (0 : ℝ) ≤ p / 2 by
      exact div_nonneg hp0 (by norm_num))]
  norm_num

theorem choiAmp_normSq_one_zero_false (p : ℝ) (hp0 : 0 ≤ p) :
    Complex.normSq (choiAmp p false (1, 0)) = p / 2 := by
  rw [choiAmp_one_zero_false, Complex.normSq_mul, Complex.normSq_neg,
    Complex.normSq_I, Complex.normSq_ofReal,
    Real.mul_self_sqrt (show (0 : ℝ) ≤ p / 2 by
      exact div_nonneg hp0 (by norm_num))]
  norm_num

theorem choiAmp_normSq_one_zero (p : ℝ) (hp0 : 0 ≤ p) (s : Bool) :
    Complex.normSq (choiAmp p s (1, 0)) = p / 2 := by
  cases s
  · exact choiAmp_normSq_one_zero_false p hp0
  · exact choiAmp_normSq_one_zero_true p hp0

theorem choiAmp_normSq_one_one (p : ℝ) (hp1 : p ≤ 1) (s : Bool) :
    Complex.normSq (choiAmp p s (1, 1)) = (1 - p) / 2 := by
  rw [choiAmp_one_one, Complex.normSq_ofReal,
    Real.mul_self_sqrt (show (0 : ℝ) ≤ (1 - p) / 2 by
      exact div_nonneg (sub_nonneg.mpr hp1) (by norm_num))]

/-- Both branch vectors are normalized for physical damping parameters. -/
theorem choiAmp_normSq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Bool) :
    ∑ x : Qubit × Qubit, Complex.normSq (choiAmp p s x) = 1 := by
  rw [Fintype.sum_prod_type, Fin.sum_univ_two, Fin.sum_univ_two, Fin.sum_univ_two]
  rw [choiAmp_normSq_zero_zero, choiAmp_normSq_zero_one,
    choiAmp_normSq_one_zero p hp0 s, choiAmp_normSq_one_one p hp1 s]
  linarith

/-- The diagonal entry `⟨x|ψ±⟩⟨ψ±|x⟩` is the squared modulus. -/
theorem choiAmp_mul_star_self (p : ℝ) (s : Bool) (x : Qubit × Qubit) :
    choiAmp p s x * star (choiAmp p s x) =
      ((Complex.normSq (choiAmp p s x) : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.mul_conj]

/-- The trace-one identity turning `choiAmp` into a `PureVector`. -/
theorem choiAmp_trace_rankOne (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Bool) :
    (rankOneMatrix (choiAmp p s)).trace = 1 := by
  rw [trace_rankOne_eq_sum_normSq]
  have h2 : ((∑ x : Qubit × Qubit, Complex.normSq (choiAmp p s x) : ℝ) : ℂ) =
      ∑ x : Qubit × Qubit, ((Complex.normSq (choiAmp p s x) : ℝ) : ℂ) :=
    Complex.ofReal_sum Finset.univ
      (fun x : Qubit × Qubit => Complex.normSq (choiAmp p s x))
  rw [← h2, choiAmp_normSq p hp0 hp1 s]
  exact Complex.ofReal_one

/-- The two Choi branch vectors `ψ±` as normalized pure vectors. -/
def choiPureVector (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Bool) :
    PureVector (Qubit × Qubit) where
  amp := choiAmp p s
  trace_rankOne_eq_one := choiAmp_trace_rankOne p hp0 hp1 s

@[simp] theorem choiPureVector_amp (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Bool) :
    (choiPureVector p hp0 hp1 s).amp = choiAmp p s :=
  rfl

/-! ### The Choi state -/

/-- The scalar identity behind the `⟨00|ω_p|11⟩` corner entry. -/
theorem sqrt_half_mul_sqrt_half (p : ℝ) (hp1 : p ≤ 1) :
    Real.sqrt (1 / 2) * Real.sqrt ((1 - p) / 2) = Real.sqrt (1 - p) / 2 := by
  have h0 : (0 : ℝ) ≤ 1 / 2 := by norm_num
  have hp : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  calc Real.sqrt (1 / 2) * Real.sqrt ((1 - p) / 2) =
      Real.sqrt ((1 / 2) * ((1 - p) / 2)) := (Real.sqrt_mul h0 _).symm
    _ = Real.sqrt ((1 - p) / 4) := by congr 1; field_simp; ring
    _ = Real.sqrt (1 - p) / Real.sqrt 4 := Real.sqrt_div hp 4
    _ = Real.sqrt (1 - p) / 2 := by
      rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num,
        Real.sqrt_sq (show (0 : ℝ) ≤ 2 by norm_num)]

/-- The `⟨00|ψ±|11⟩` amplitude product of either branch. -/
theorem choiAmp_mul_00_11 (p : ℝ) (hp1 : p ≤ 1) (s : Bool) :
    choiAmp p s (0, 0) * choiAmp p s (1, 1) =
      ((Real.sqrt (1 - p) / 2 : ℝ) : ℂ) := by
  simp only [choiAmp_zero_zero, choiAmp_one_one]
  rw [← Complex.ofReal_mul, sqrt_half_mul_sqrt_half p hp1]

/-- The `⟨00|ψ±⟩⟨ψ±|11⟩` matrix entry of either branch. -/
theorem choiAmp_mul_star_00_11 (p : ℝ) (hp1 : p ≤ 1) (s : Bool) :
    choiAmp p s (0, 0) * star (choiAmp p s (1, 1)) =
      ((Real.sqrt (1 - p) / 2 : ℝ) : ℂ) := by
  simp only [choiAmp_zero_zero, choiAmp_one_one, Complex.star_def,
    Complex.conj_ofReal]
  rw [← Complex.ofReal_mul, sqrt_half_mul_sqrt_half p hp1]

/-- The transposed `⟨11|ψ±⟩⟨ψ±|00⟩` matrix entry of either branch. -/
theorem choiAmp_mul_star_11_00 (p : ℝ) (hp1 : p ≤ 1) (s : Bool) :
    choiAmp p s (1, 1) * star (choiAmp p s (0, 0)) =
      ((Real.sqrt (1 - p) / 2 : ℝ) : ℂ) := by
  simp only [choiAmp_zero_zero, choiAmp_one_one, Complex.star_def,
    Complex.conj_ofReal]
  rw [← Complex.ofReal_mul,
    mul_comm (Real.sqrt ((1 - p) / 2)) (Real.sqrt (1 / 2)),
    sqrt_half_mul_sqrt_half p hp1]

/-- The amplitudes of the two half-weight branches `2^{-1/2} ψ±` whose
rank-one kernels sum to the Choi state. -/
def choiBranchAmp (p : ℝ) (s : Bool) : Qubit × Qubit → ℂ :=
  fun x => ((Real.sqrt (1 / 2) : ℝ) : ℂ) * choiAmp p s x

/-- Rescaling by `√(1/2)` halves every rank-one kernel entry. -/
theorem choiBranchAmp_mul_star (p : ℝ) (s : Bool) (x y : Qubit × Qubit) :
    choiBranchAmp p s x * star (choiBranchAmp p s y) =
      ((1 / 2 : ℝ) : ℂ) * (choiAmp p s x * star (choiAmp p s y)) := by
  have hcc : (((Real.sqrt (1 / 2) : ℝ) : ℂ) *
      star ((Real.sqrt (1 / 2) : ℝ) : ℂ)) = ((1 / 2 : ℝ) : ℂ) := by
    have h := Complex.mul_conj ((Real.sqrt (1 / 2) : ℝ) : ℂ)
    rw [Complex.normSq_ofReal,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)] at h
    exact h
  show (((Real.sqrt (1 / 2) : ℝ) : ℂ) * choiAmp p s x) *
      star (((Real.sqrt (1 / 2) : ℝ) : ℂ) * choiAmp p s y) = _
  rw [star_mul']
  calc (((Real.sqrt (1 / 2) : ℝ) : ℂ) * choiAmp p s x) *
      (star ((Real.sqrt (1 / 2) : ℝ) : ℂ) * star (choiAmp p s y)) =
      (((Real.sqrt (1 / 2) : ℝ) : ℂ) *
        star ((Real.sqrt (1 / 2) : ℝ) : ℂ)) *
      (choiAmp p s x * star (choiAmp p s y)) := by ring
    _ = ((1 / 2 : ℝ) : ℂ) * (choiAmp p s x * star (choiAmp p s y)) := by
      rw [hcc]

/-- Each half-weight branch has trace one half. -/
theorem choiBranchAmp_normSq_sum (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Bool) :
    ∑ x : Qubit × Qubit, Complex.normSq (choiBranchAmp p s x) = 1 / 2 := by
  have h : ∀ x : Qubit × Qubit,
      Complex.normSq (choiBranchAmp p s x) =
        (1 / 2) * Complex.normSq (choiAmp p s x) := by
    intro x
    rw [choiBranchAmp, Complex.normSq_mul, Complex.normSq_ofReal,
      Real.mul_self_sqrt (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
  simp only [h]
  rw [← Finset.mul_sum, choiAmp_normSq p hp0 hp1 s]
  norm_num

theorem choiBranchAmp_trace (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (s : Bool) :
    (rankOneMatrix (choiBranchAmp p s)).trace = ((1 / 2 : ℝ) : ℂ) := by
  rw [trace_rankOne_eq_sum_normSq]
  have h2 : ((∑ x : Qubit × Qubit, Complex.normSq (choiBranchAmp p s x) : ℝ) : ℂ) =
      ∑ x : Qubit × Qubit,
        ((Complex.normSq (choiBranchAmp p s x) : ℝ) : ℂ) :=
    Complex.ofReal_sum Finset.univ
      (fun x : Qubit × Qubit => Complex.normSq (choiBranchAmp p s x))
  rw [← h2, choiBranchAmp_normSq_sum p hp0 hp1 s]

/-- The Choi state `ω_p` of the amplitude-damping channel, eq. `(choi)`: the
average of the two pure branch states `|ψ+⟩⟨ψ+|` and `|ψ-⟩⟨ψ-|` with weights
`1/2`, i.e. the sum of the rank-one kernels of the half-weight branches. -/
def choiState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) : State (Qubit × Qubit) where
  matrix := rankOneMatrix (choiBranchAmp p true) +
    rankOneMatrix (choiBranchAmp p false)
  pos := Matrix.PosSemidef.add (rankOneMatrix_pos _)
    (rankOneMatrix_pos _)
  trace_eq_one := by
    rw [Matrix.trace_add, choiBranchAmp_trace p hp0 hp1 true,
      choiBranchAmp_trace p hp0 hp1 false, ← Complex.ofReal_add]
    norm_num

/-- Entrywise, the Choi state is half the sum of the two branch kernels. -/
theorem choiState_matrix_apply (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x y : Qubit × Qubit) :
    (choiState p hp0 hp1).matrix x y =
      ((1 / 2 : ℝ) : ℂ) * (choiAmp p true x * star (choiAmp p true y) +
        choiAmp p false x * star (choiAmp p false y)) := by
  show rankOneMatrix (choiBranchAmp p true) x y +
      rankOneMatrix (choiBranchAmp p false) x y = _
  rw [rankOneMatrix_apply, rankOneMatrix_apply, choiBranchAmp_mul_star,
    choiBranchAmp_mul_star]
  ring

/-- Halving a doubled real coercion. -/
theorem choi_half (x : ℝ) :
    ((1 / 2 : ℝ) : ℂ) * (((x : ℝ) : ℂ) + ((x : ℝ) : ℂ)) = ((x : ℝ) : ℂ) := by
  rw [← Complex.ofReal_add, ← Complex.ofReal_mul]
  congr 1
  ring

/-! ### The entry table -/

/-- Entry `⟨00|ω_p|00⟩`. -/
theorem choiState_matrix_00_00 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix (0, 0) (0, 0) = ((1 / 2 : ℝ) : ℂ) := by
  rw [choiState_matrix_apply, choiAmp_mul_star_self, choiAmp_mul_star_self,
    choiAmp_normSq_zero_zero, choiAmp_normSq_zero_zero]
  exact choi_half _

/-- Entry `⟨01|ω_p|01⟩`. -/
theorem choiState_matrix_01_01 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix (0, 1) (0, 1) = 0 := by
  simp [choiState_matrix_apply, choiAmp_zero_one]

/-- Entry `⟨10|ω_p|10⟩`. -/
theorem choiState_matrix_10_10 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix (1, 0) (1, 0) = ((p / 2 : ℝ) : ℂ) := by
  rw [choiState_matrix_apply, choiAmp_mul_star_self, choiAmp_mul_star_self,
    choiAmp_normSq_one_zero_true p hp0, choiAmp_normSq_one_zero_false p hp0]
  exact choi_half _

/-- Entry `⟨11|ω_p|11⟩`. -/
theorem choiState_matrix_11_11 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix (1, 1) (1, 1) = (((1 - p) / 2 : ℝ) : ℂ) := by
  rw [choiState_matrix_apply, choiAmp_mul_star_self, choiAmp_mul_star_self,
    choiAmp_normSq_one_one p hp1, choiAmp_normSq_one_one p hp1]
  exact choi_half _

/-- Corner entry `⟨00|ω_p|11⟩`. -/
theorem choiState_matrix_00_11 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix (0, 0) (1, 1) =
      ((Real.sqrt (1 - p) / 2 : ℝ) : ℂ) := by
  rw [choiState_matrix_apply, choiAmp_mul_star_00_11 p hp1 true,
    choiAmp_mul_star_00_11 p hp1 false]
  exact choi_half _

/-- Corner entry `⟨11|ω_p|00⟩`. -/
theorem choiState_matrix_11_00 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix (1, 1) (0, 0) =
      ((Real.sqrt (1 - p) / 2 : ℝ) : ℂ) := by
  rw [choiState_matrix_apply, choiAmp_mul_star_11_00 p hp1 true,
    choiAmp_mul_star_11_00 p hp1 false]
  exact choi_half _

/-- The `±i` phases cancel in the `⟨00|–|10⟩` entry. -/
theorem choiState_matrix_00_10 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix (0, 0) (1, 0) = 0 := by
  rw [choiState_matrix_apply]
  simp only [choiAmp_zero_zero, choiAmp_one_zero_true, choiAmp_one_zero_false,
    star_neg, star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The `±i` phases cancel in the `⟨10|–|00⟩` entry. -/
theorem choiState_matrix_10_00 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix (1, 0) (0, 0) = 0 := by
  rw [choiState_matrix_apply]
  simp only [choiAmp_zero_zero, choiAmp_one_zero_true, choiAmp_one_zero_false,
    Complex.star_def, Complex.conj_ofReal]
  ring

/-- The `±i` phases cancel in the `⟨10|–|11⟩` entry. -/
theorem choiState_matrix_10_11 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix (1, 0) (1, 1) = 0 := by
  rw [choiState_matrix_apply]
  simp only [choiAmp_one_one, choiAmp_one_zero_true, choiAmp_one_zero_false,
    Complex.star_def, Complex.conj_ofReal]
  ring

/-- The `±i` phases cancel in the `⟨11|–|10⟩` entry. -/
theorem choiState_matrix_11_10 (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix (1, 1) (1, 0) = 0 := by
  rw [choiState_matrix_apply]
  simp only [choiAmp_one_one, choiAmp_one_zero_true, choiAmp_one_zero_false,
    star_neg, star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The `|01⟩` column of the Choi state vanishes. -/
theorem choiState_matrix_col_zero_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (x : Qubit × Qubit) :
    (choiState p hp0 hp1).matrix x (0, 1) = 0 := by
  rcases x with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [choiState_matrix_apply, choiAmp_zero_one]

/-- The `|01⟩` row of the Choi state vanishes. -/
theorem choiState_matrix_row_zero_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (y : Qubit × Qubit) :
    (choiState p hp0 hp1).matrix (0, 1) y = 0 := by
  rcases y with ⟨i, j⟩
  fin_cases i <;> fin_cases j <;>
    simp [choiState_matrix_apply, choiAmp_zero_one]

/-- The explicit entry table of eq. `(choi)`. -/
def choiEntries (p : ℝ) : Qubit × Qubit → Qubit × Qubit → ℂ :=
  fun x y =>
    if x = (0, 0) ∧ y = (0, 0) then ((1 / 2 : ℝ) : ℂ)
    else if x = (0, 0) ∧ y = (1, 1) then ((Real.sqrt (1 - p) / 2 : ℝ) : ℂ)
    else if x = (1, 1) ∧ y = (0, 0) then ((Real.sqrt (1 - p) / 2 : ℝ) : ℂ)
    else if x = (1, 0) ∧ y = (1, 0) then ((p / 2 : ℝ) : ℂ)
    else if x = (1, 1) ∧ y = (1, 1) then (((1 - p) / 2 : ℝ) : ℂ)
    else 0

/-- The full four-by-four entry table of the Choi state: all entries vanish
except the diagonal and the `⟨00|–|11⟩` corners. -/
theorem choiState_matrix_eq (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix = Matrix.of (choiEntries p) := by
  ext x y
  rcases x with ⟨i, j⟩
  rcases y with ⟨k, l⟩
  fin_cases i <;> fin_cases j <;> fin_cases k <;> fin_cases l <;>
    simp [choiEntries, choiState_matrix_00_00, choiState_matrix_10_10,
      choiState_matrix_11_11, choiState_matrix_00_11,
      choiState_matrix_11_00, choiState_matrix_00_10, choiState_matrix_10_00,
      choiState_matrix_10_11, choiState_matrix_11_10,
      choiState_matrix_col_zero_one, choiState_matrix_row_zero_one]

/-- The vector `|01⟩` lies in the kernel of the Choi state for every
physical damping parameter. -/
theorem choiState_ket01_kernel (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiState p hp0 hp1).matrix *ᵥ ket01 = 0 := by
  funext x
  rw [Pi.zero_apply, mulVec_ket01_apply]
  exact choiState_matrix_col_zero_one p hp0 hp1 x

/-! ### Entanglement of formation -/

/-- The scalar identity `e_conc(√(1-p)) = h₂((1+√p)/2)` behind eq.
`(choi-cost)`. -/
theorem entanglementCurve_sqrt_one_sub (p : ℝ) (hp1 : p ≤ 1) :
    entanglementCurve (Real.sqrt (1 - p)) =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  have h1 : 0 ≤ 1 - p := sub_nonneg.mpr hp1
  have h2 : 1 - (Real.sqrt (1 - p)) ^ 2 = p := by
    rw [Real.sq_sqrt h1]
    ring
  unfold entanglementCurve
  rw [h2]

/-- The entanglement of formation of the Choi state is the concurrence curve
at `√(1-p)`, the concurrence of `ω_p`, under the Wootters corner-formula
interface hypothesis. -/
theorem choiState_entanglementOfFormation (h : woottersKernelUpperBound)
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementOfFormation (choiState p hp0 hp1) =
      entanglementCurve (Real.sqrt (1 - p)) := by
  rw [entanglementOfFormation_eq_entanglementCurve_of_kernelVector h
    (choiState p hp0 hp1) (choiState_ket01_kernel p hp0 hp1),
    choiState_matrix_00_11 p hp0 hp1,
    Complex.norm_of_nonneg
      (show (0 : ℝ) ≤ Real.sqrt (1 - p) / 2 by
        exact div_nonneg (Real.sqrt_nonneg (1 - p)) (by norm_num))]
  congr 1
  ring

/-- First half of eq. `(choi-cost)`: the entanglement of formation of the
Choi state of the amplitude-damping channel is the binary entropy
`h₂((1+√p)/2)`. -/
theorem choiState_entanglementOfFormation_eq_binaryEntropy
    (h : woottersKernelUpperBound) (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementOfFormation (choiState p hp0 hp1) =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  rw [choiState_entanglementOfFormation h p hp0 hp1,
    entanglementCurve_sqrt_one_sub p hp1]

/-! ### The explicit two-branch decomposition -/

/-- The entropy of the reference marginal of either Choi branch: both branch
marginals have the spectrum `(1 ± √p)/2`, so each branch costs
`h₂((1+√p)/2)`. -/
theorem choiBranch_marginalA_vonNeumann (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (s : Bool) :
    (choiPureVector p hp0 hp1 s).state.marginalA.vonNeumann =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  rw [pure_marginalA_vonNeumann]
  have hdet : (twoQubitAmplitudeMatrix (choiPureVector p hp0 hp1 s)).det =
      ((Real.sqrt (1 - p) / 2 : ℝ) : ℂ) := by
    rw [twoQubitAmplitudeMatrix_det]
    simp only [choiPureVector_amp, choiAmp_mul_00_11 p hp1 s, choiAmp_zero_one]
    ring
  rw [hdet,
    Complex.norm_of_nonneg
      (show (0 : ℝ) ≤ Real.sqrt (1 - p) / 2 by
        exact div_nonneg (Real.sqrt_nonneg (1 - p)) (by norm_num)),
    ← entanglementCurve_sqrt_one_sub p hp1]
  congr 1
  ring

/-- The explicit two-branch pure decomposition `ω_p = ½ |ψ+⟩⟨ψ+| +
½ |ψ-⟩⟨ψ-|` of the Choi state. -/
def choiDecomposition (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    PureDecomposition (Qubit × Qubit) where
  card := 2
  probs _ := 2⁻¹
  weights_sum := by rw [Fin.sum_univ_two]; norm_num
  vectors := ![choiPureVector p hp0 hp1 true, choiPureVector p hp0 hp1 false]

theorem choiDecomposition_card (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiDecomposition p hp0 hp1).card = 2 :=
  rfl

theorem choiDecomposition_probs (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1)
    (i : Fin 2) :
    (choiDecomposition p hp0 hp1).probs i = 2⁻¹ :=
  rfl

theorem choiDecomposition_vectors_zero (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiDecomposition p hp0 hp1).vectors (0 : Fin 2) =
      choiPureVector p hp0 hp1 true :=
  rfl

theorem choiDecomposition_vectors_one (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiDecomposition p hp0 hp1).vectors (1 : Fin 2) =
      choiPureVector p hp0 hp1 false :=
  rfl

/-- The two-branch decomposition averages to the Choi state. -/
theorem choiDecomposition_averageState (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (choiDecomposition p hp0 hp1).averageState = choiState p hp0 hp1 := by
  apply State.ext
  ext x y
  rw [pureDecomposition_averageState_matrix_entry, choiState_matrix_apply]
  show ∑ i : Fin 2, (((choiDecomposition p hp0 hp1).probs i : ℝ≥0) : ℂ) *
      ((choiDecomposition p hp0 hp1).vectors i).state.matrix x y = _
  rw [Fin.sum_univ_two, choiDecomposition_probs p hp0 hp1 0,
    choiDecomposition_probs p hp0 hp1 1, choiDecomposition_vectors_zero p hp0 hp1,
    choiDecomposition_vectors_one p hp0 hp1, PureVector.state_matrix_apply,
    PureVector.state_matrix_apply]
  simp only [choiPureVector_amp]
  have hc : (((2⁻¹ : ℝ≥0) : ℂ)) = ((1 / 2 : ℝ) : ℂ) := by
    push_cast
    norm_num
  rw [hc]
  ring

/-- The average marginal-entropy cost of the two-branch decomposition is
exactly `h₂((1+√p)/2)`: the explicit decomposition is optimal. -/
theorem choiDecomposition_entanglementCost (p : ℝ) (hp0 : 0 ≤ p)
    (hp1 : p ≤ 1) :
    (choiDecomposition p hp0 hp1).entanglementCost =
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  rw [PureDecomposition.entanglementCost]
  show ∑ i : Fin 2, ((choiDecomposition p hp0 hp1).probs i).toReal *
      ((choiDecomposition p hp0 hp1).vectors i).state.marginalA.vonNeumann = _
  rw [Fin.sum_univ_two, choiDecomposition_probs p hp0 hp1 0,
    choiDecomposition_probs p hp0 hp1 1, choiDecomposition_vectors_zero p hp0 hp1,
    choiDecomposition_vectors_one p hp0 hp1,
    choiBranch_marginalA_vonNeumann p hp0 hp1 true,
    choiBranch_marginalA_vonNeumann p hp0 hp1 false]
  have hc : (2⁻¹ : ℝ≥0).toReal = 1 / 2 := by
    push_cast
    norm_num
  rw [hc]
  ring

/-- The entanglement of formation of the Choi state is at most the cost of
its explicit two-branch decomposition (which equals
`choiState_entanglementOfFormation_eq_binaryEntropy`, so the bound holds with
equality). -/
theorem choiState_entanglementOfFormation_le_branchCost (p : ℝ)
    (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    entanglementOfFormation (choiState p hp0 hp1) ≤
      binaryEntropy ((1 + Real.sqrt p) / 2) := by
  rw [← choiDecomposition_averageState p hp0 hp1,
    ← choiDecomposition_entanglementCost p hp0 hp1]
  exact entanglementOfFormation_le_entanglementCost _

/-! ### Endpoints -/

/-- At `p = 0` the Choi state is the maximally entangled `|Φ+⟩` and its
entanglement of formation is one ebit. -/
theorem choiState_entanglementOfFormation_eq_one
    (h : woottersKernelUpperBound) :
    entanglementOfFormation
      (choiState 0 (show (0 : ℝ) ≤ 0 by norm_num)
        (show (0 : ℝ) ≤ 1 by norm_num)) = 1 := by
  rw [choiState_entanglementOfFormation_eq_binaryEntropy h, Real.sqrt_zero,
    show (1 + (0 : ℝ)) / 2 = 2⁻¹ by norm_num,
    binaryEntropy_eq_binEntropy_div_log_two, Real.binEntropy_two_inv,
    div_self (Real.log_pos one_lt_two).ne']

/-- At `p = 1` the Choi state is separable and its entanglement of formation
vanishes. -/
theorem choiState_entanglementOfFormation_eq_zero
    (h : woottersKernelUpperBound) :
    entanglementOfFormation
      (choiState 1 (show (0 : ℝ) ≤ 1 by norm_num)
        (show (1 : ℝ) ≤ 1 by norm_num)) = 0 := by
  rw [choiState_entanglementOfFormation_eq_binaryEntropy h, Real.sqrt_one,
    show (1 + (1 : ℝ)) / 2 = 1 by norm_num,
    binaryEntropy_eq_binEntropy_div_log_two]
  norm_num

end

end AmplitudeDamping
