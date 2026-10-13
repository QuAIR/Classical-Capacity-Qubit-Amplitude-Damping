import AmplitudeDamping.Concurrence
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! # Stationarity of optimal concurrence ensembles

Imaginary unitary rotations of two subnormalized pure vectors preserve their
represented state. At a concurrence minimum with positive real quadratic
contributions, differentiating the pair cost forces every polarized overlap
to be real. This is the real-Gram step used by `ConcurrenceFlatRoof`.
-/

/-!
# Stationarity of finite concurrence ensembles

Homogeneous concurrence is a complex quadratic form on raw two-qubit amplitudes.
If a minimizing ensemble has positive real quadratic values on every branch,
imaginary unitary rotations of any pair force every polarized overlap to be real.
The argument uses an explicit derivative of the pair cost and preserves the
represented density matrix exactly.
-/

namespace AmplitudeDamping
open QIT
open scoped BigOperators ComplexConjugate
noncomputable section
set_option maxHeartbeats 800000

/-- Homogeneous pure concurrence before taking the complex modulus. -/
def rawConcurrence (v : Qubit × Qubit → ℂ) : ℂ :=
  2 * (v (0,0) * v (1,1) - v (0,1) * v (1,0))

/-- Symmetric bilinear polarization of the homogeneous concurrence. -/
def concurrenceOverlap (u v : Qubit × Qubit → ℂ) : ℂ :=
  u (0,0) * v (1,1) + v (0,0) * u (1,1) -
    u (0,1) * v (1,0) - v (0,1) * u (1,0)

/-- Total concurrence of a family of subnormalized pure vectors. -/
def rawConcurrenceCost {ι : Type*} [Fintype ι]
    (v : ι → Qubit × Qubit → ℂ) : ℝ := ∑ i, ‖rawConcurrence (v i)‖

theorem rawConcurrence_eq_two_det (v : Qubit × Qubit → ℂ) :
    rawConcurrence v = 2 * (Matrix.of fun i j => v (i,j)).det := by
  rw [Matrix.det_fin_two]
  rfl

theorem norm_rawConcurrence (v : Qubit × Qubit → ℂ) :
    ‖rawConcurrence v‖ = 2 * ‖(Matrix.of fun i j => v (i,j)).det‖ := by
  rw [rawConcurrence_eq_two_det, norm_mul]
  norm_num

theorem concurrenceOverlap_self (v : Qubit × Qubit → ℂ) :
    concurrenceOverlap v v = rawConcurrence v := by
  simp only [concurrenceOverlap, rawConcurrence]
  ring

theorem concurrenceOverlap_comm (u v : Qubit × Qubit → ℂ) :
    concurrenceOverlap u v = concurrenceOverlap v u := by
  simp only [concurrenceOverlap]
  ring

theorem rawConcurrence_linearCombination (u v : Qubit × Qubit → ℂ) (a b : ℂ) :
    rawConcurrence (a • u + b • v) =
      a^2 * rawConcurrence u + b^2 * rawConcurrence v +
        2*a*b*concurrenceOverlap u v := by
  simp only [rawConcurrence, concurrenceOverlap, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- An imaginary two-vector rotation preserves the represented density matrix. -/
theorem rankOneMatrix_imaginary_rotation (u v : Qubit × Qubit → ℂ)
    (c s : ℝ) (hcs : c^2+s^2=1) :
    rankOneMatrix ((c:ℂ) • u + (Complex.I*s) • v) +
      rankOneMatrix ((Complex.I*s) • u + (c:ℂ) • v) =
        rankOneMatrix u + rankOneMatrix v := by
  ext i j
  have hcs' : (c:ℂ)^2+(s:ℂ)^2=1 := by exact_mod_cast hcs
  simp only [Matrix.add_apply, rankOneMatrix_apply, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul, star_add, star_mul, Complex.star_def, Complex.conj_ofReal,
    Complex.conj_I]
  linear_combination (u i * conj (u j) + v i * conj (v j)) * hcs' -
    (s:ℂ)^2 * (u i * conj (u j) + v i * conj (v j)) * Complex.I_sq

/-- Concurrence contribution of a pair after an imaginary unitary rotation. -/
def imaginaryPairCost (a b : ℝ) (z : ℂ) (t : ℝ) : ℝ :=
  (‖(a : ℂ) - (t : ℂ)^2 * b + 2 * Complex.I * t * z‖ +
    ‖(b : ℂ) - (t : ℂ)^2 * a + 2 * Complex.I * t * z‖) / (1 + t^2)

private theorem pairNumerator_norm (a b : ℝ) (z : ℂ) (t : ℝ) :
    ‖(a : ℂ) - (t : ℂ)^2 * b + 2 * Complex.I * t * z‖ =
      Real.sqrt ((a - t^2*b - 2*t*z.im)^2 + (2*t*z.re)^2) := by
  rw [Complex.norm_def, Complex.normSq_apply]
  congr 1
  simp [Complex.sub_re, Complex.add_re, Complex.mul_re,
    Complex.sub_im, Complex.add_im, Complex.mul_im, pow_two]
  ring

private theorem pairNumerator_hasDerivAt (a b : ℝ) (z : ℂ) (ha : 0 < a) :
    HasDerivAt (fun t : ℝ =>
      ‖(a : ℂ) - (t : ℂ)^2 * b + 2 * Complex.I * t * z‖) (-2*z.im) 0 := by
  have h1 : HasDerivAt (fun t : ℝ => a - t^2*b - 2*t*z.im) (-2*z.im) 0 := by
    convert ((hasDerivAt_const (0 : ℝ) a).sub
      (((hasDerivAt_id (0 : ℝ)).pow 2).mul_const b)).sub
        (((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const z.im) using 1
    simp
  have h2 : HasDerivAt (fun t : ℝ => 2*t*z.re) (2*z.re) 0 := by
    convert ((hasDerivAt_id (0 : ℝ)).const_mul 2).mul_const z.re using 1
    simp
  have hd := ((h1.pow 2).add (h2.pow 2)).sqrt (by simpa using ne_of_gt (sq_pos_of_pos ha))
  have heq : (fun t : ℝ =>
      ‖(a : ℂ) - (t : ℂ)^2 * b + 2 * Complex.I * t * z‖) =
      (fun t : ℝ => Real.sqrt ((a-t^2*b-2*t*z.im)^2+(2*t*z.re)^2)) := by
    funext t
    exact pairNumerator_norm a b z t
  rw [heq]
  convert hd using 1
  simp [Pi.pow_apply, Pi.add_apply, Real.sqrt_sq ha.le]
  field_simp

/-- At an optimal pair with positive real diagonal overlaps, the cross overlap is real. -/
theorem imaginaryPairCost_minimizer_im_eq_zero (a b : ℝ) (z : ℂ)
    (ha : 0 < a) (hb : 0 < b)
    (hmin : ∀ t, a + b ≤ imaginaryPairCost a b z t) : z.im = 0 := by
  have hden : HasDerivAt (fun t : ℝ => 1+t^2) 0 0 := by
    convert (hasDerivAt_const (0 : ℝ) 1).add ((hasDerivAt_id (0 : ℝ)).pow 2) using 1
    simp
  have hd : HasDerivAt (imaginaryPairCost a b z) (-4*z.im) 0 := by
    convert ((pairNumerator_hasDerivAt a b z ha).add
      (pairNumerator_hasDerivAt b a z hb)).div hden (by norm_num) using 1
    simp
    ring
  have hzero : imaginaryPairCost a b z 0 = a+b := by
    simp [imaginaryPairCost, Complex.norm_real, Real.norm_eq_abs, abs_of_pos ha, abs_of_pos hb]
  have hm : IsLocalMin (imaginaryPairCost a b z) 0 :=
    Filter.Eventually.of_forall (fun t => by rw [hzero]; exact hmin t)
  have h := hm.hasDerivAt_eq_zero hd
  linarith

/-- Replace two distinct entries of a finite family. -/
def pairReplace {ι α : Type*} [DecidableEq ι] (v : ι → α) (i j : ι) (x y : α) : ι → α :=
  fun k => if k=i then x else if k=j then y else v k

theorem sum_pairReplace {ι M : Type*} [Fintype ι] [DecidableEq ι] [AddCommGroup M]
    (v : ι → M) (i j : ι) (hij : i ≠ j) (x y : M) :
    ∑ k, pairReplace v i j x y k = (∑ k, v k) - v i - v j + x + y := by
  have heq : pairReplace v i j x y = fun k =>
      v k + (if k=i then x-v i else 0) + (if k=j then y-v j else 0) := by
    funext k
    by_cases hi : k=i
    · subst k
      simp [pairReplace, hij]
    · by_cases hj : k=j
      · subst k
        simp [pairReplace, hi]
      · simp [pairReplace, hi, hj]
  rw [heq, Finset.sum_add_distrib, Finset.sum_add_distrib]
  simp only [Finset.sum_ite_eq', Finset.mem_univ, ↓reduceIte]
  abel

theorem sum_pairReplace_comp {ι α M : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup M] (f : α → M) (v : ι → α) (i j : ι) (hij : i ≠ j) (x y : α) :
    ∑ k, f (pairReplace v i j x y k) = (∑ k, f (v k))-f (v i)-f (v j)+f x+f y := by
  have heq : (fun k => f (pairReplace v i j x y k)) = pairReplace (f ∘ v) i j (f x) (f y) := by
    funext k
    simp only [pairReplace]
    split_ifs <;> rfl
  rw [heq, sum_pairReplace _ _ _ hij]
  rfl

/-- The first vector of a rationally parametrized imaginary unitary rotation. -/
def imaginaryFirst (u v : Qubit × Qubit → ℂ) (t : ℝ) : Qubit × Qubit → ℂ :=
  ((Real.sqrt (1+t^2) : ℂ)⁻¹) • (u + (Complex.I*t) • v)

/-- The second vector of the same rotation. -/
def imaginarySecond (u v : Qubit × Qubit → ℂ) (t : ℝ) : Qubit × Qubit → ℂ :=
  ((Real.sqrt (1+t^2) : ℂ)⁻¹) • ((Complex.I*t) • u + v)

private theorem imaginaryRotation_invSqrt_sq (t : ℝ) :
    ((Real.sqrt (1+t^2) : ℂ)⁻¹)^2 = (((1+t^2 : ℝ) : ℂ))⁻¹ := by
  rw [inv_pow, ← Complex.ofReal_pow, Real.sq_sqrt (by positivity)]

theorem imaginary_rotation_density (u v : Qubit × Qubit → ℂ) (t : ℝ) :
    rankOneMatrix (imaginaryFirst u v t) + rankOneMatrix (imaginarySecond u v t) =
      rankOneMatrix u + rankOneMatrix v := by
  let r := (Real.sqrt (1+t^2))⁻¹
  have hr : r^2 * (1+t^2) = 1 := by
    dsimp [r]
    rw [inv_pow, Real.sq_sqrt (by positivity)]
    exact inv_mul_cancel₀ (by positivity)
  have hcs : r^2+(r*t)^2=1 := by nlinarith [hr]
  have hfirst : imaginaryFirst u v t = (r:ℂ) • u + (Complex.I*(r*t)) • v := by
    funext k
    simp [imaginaryFirst, r, mul_add]
    ring
  have hsecond : imaginarySecond u v t = (Complex.I*(r*t)) • u + (r:ℂ) • v := by
    funext k
    simp [imaginarySecond, r, mul_add]
    ring
  rw [hfirst, hsecond]
  simpa only [Complex.ofReal_mul] using rankOneMatrix_imaginary_rotation u v r (r*t) hcs

theorem rawConcurrence_imaginaryFirst (u v : Qubit × Qubit → ℂ) (t : ℝ) :
    rawConcurrence (imaginaryFirst u v t) =
      (rawConcurrence u - (t:ℂ)^2 * rawConcurrence v +
        2*Complex.I*t*concurrenceOverlap u v) / ((1+t^2 : ℝ):ℂ) := by
  have heq : imaginaryFirst u v t =
      ((Real.sqrt (1+t^2) : ℂ)⁻¹) • u +
      (((Real.sqrt (1+t^2) : ℂ)⁻¹)*Complex.I*t) • v := by
    funext k
    simp [imaginaryFirst, mul_add]
    ring
  rw [heq, rawConcurrence_linearCombination]
  ring_nf
  rw [imaginaryRotation_invSqrt_sq, Complex.I_sq]
  push_cast
  ring

theorem rawConcurrence_imaginarySecond (u v : Qubit × Qubit → ℂ) (t : ℝ) :
    rawConcurrence (imaginarySecond u v t) =
      (rawConcurrence v - (t:ℂ)^2 * rawConcurrence u +
        2*Complex.I*t*concurrenceOverlap u v) / ((1+t^2 : ℝ):ℂ) := by
  have heq : imaginarySecond u v t = imaginaryFirst v u t := by
    simp [imaginarySecond, imaginaryFirst, add_comm]
  rw [heq, rawConcurrence_imaginaryFirst, concurrenceOverlap_comm v u]


theorem rawConcurrence_imaginary_pair_cost (u v : Qubit × Qubit → ℂ)
    (a b : ℝ) (hu : rawConcurrence u = (a:ℂ)) (hv : rawConcurrence v = (b:ℂ)) (t : ℝ) :
    ‖rawConcurrence (imaginaryFirst u v t)‖ + ‖rawConcurrence (imaginarySecond u v t)‖ =
      imaginaryPairCost a b (concurrenceOverlap u v) t := by
  rw [rawConcurrence_imaginaryFirst, rawConcurrence_imaginarySecond, hu, hv]
  simp only [norm_div, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by positivity : (0:ℝ)<1+t^2), imaginaryPairCost]
  rw [add_div]

/-- Optimality under density-preserving replacements forces a real concurrence Gram matrix
once all its diagonal entries have been made strictly positive real numbers. -/
theorem optimal_rawConcurrence_overlap_real {ι : Type*} [Fintype ι] [DecidableEq ι]
    (v : ι → Qubit × Qubit → ℂ) (a : ι → ℝ)
    (ha : ∀ i, 0 < a i) (hdiag : ∀ i, rawConcurrence (v i) = (a i : ℂ))
    (hmin : ∀ w : ι → Qubit × Qubit → ℂ,
      (∑ i, rankOneMatrix (w i)) = (∑ i, rankOneMatrix (v i)) →
        rawConcurrenceCost v ≤ rawConcurrenceCost w) :
    ∀ i j, (concurrenceOverlap (v i) (v j)).im = 0 := by
  intro i j
  by_cases hij : i=j
  · subst j
    rw [concurrenceOverlap_self, hdiag]
    simp
  apply imaginaryPairCost_minimizer_im_eq_zero (a i) (a j)
    (concurrenceOverlap (v i) (v j)) (ha i) (ha j)
  intro t
  let x := imaginaryFirst (v i) (v j) t
  let y := imaginarySecond (v i) (v j) t
  let w := pairReplace v i j x y
  have hdensity : (∑ k, rankOneMatrix (w k)) = ∑ k, rankOneMatrix (v k) := by
    change (∑ k, rankOneMatrix (pairReplace v i j x y k)) = _
    rw [sum_pairReplace_comp rankOneMatrix v i j hij x y]
    have hpair : rankOneMatrix x + rankOneMatrix y = rankOneMatrix (v i)+rankOneMatrix (v j) :=
      imaginary_rotation_density (v i) (v j) t
    calc
      _ = (∑ k, rankOneMatrix (v k)) +
          (rankOneMatrix x+rankOneMatrix y) - (rankOneMatrix (v i)+rankOneMatrix (v j)) := by abel
      _ = _ := by rw [hpair]; abel
  have hcost : rawConcurrenceCost w = rawConcurrenceCost v - a i - a j +
      imaginaryPairCost (a i) (a j) (concurrenceOverlap (v i) (v j)) t := by
    change (∑ k, ‖rawConcurrence (pairReplace v i j x y k)‖) = _
    rw [sum_pairReplace_comp (fun u => ‖rawConcurrence u‖) v i j hij x y]
    rw [hdiag i, hdiag j, Complex.norm_real, Complex.norm_real,
      Real.norm_eq_abs, Real.norm_eq_abs, abs_of_pos (ha i), abs_of_pos (ha j)]
    have hp := rawConcurrence_imaginary_pair_cost (v i) (v j) (a i) (a j) (hdiag i) (hdiag j) t
    change ‖rawConcurrence x‖+‖rawConcurrence y‖ = _ at hp
    dsimp only [rawConcurrenceCost]
    linarith
  have hm := hmin w hdensity
  rw [hcost] at hm
  linarith

end
end AmplitudeDamping
