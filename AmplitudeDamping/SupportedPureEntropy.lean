import AmplitudeDamping.QubitEntropy
import QIT.Information.Entropy.Entropy

/-!
# Entropy of pure states in the single-excitation support

Compress the second non-vacuum branch into one qubit coordinate. This preserves
the first marginal even when either sector is empty. The other marginal of the
compressed pure state is a qubit with determinant equal to the product of the
two sector populations.
-/

open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT
noncomputable section
universe u v
variable {a : Type u} {b : Type v}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]

/-- Population of the first non-vacuum branch of a supported pure state. -/
def supportSectorWeightA (ψ : PureVector ((a ⊕ Unit) × (Unit ⊕ b))) : ℝ :=
  ∑ i : a, Complex.normSq (ψ.amp (Sum.inl i, Sum.inl ()))

/-- Population of the second non-vacuum branch of a supported pure state. -/
def supportSectorWeightB (ψ : PureVector ((a ⊕ Unit) × (Unit ⊕ b))) : ℝ :=
  ∑ j : b, Complex.normSq (ψ.amp (Sum.inr (), Sum.inr j))

theorem supportSectorWeightA_nonneg
    (ψ : PureVector ((a ⊕ Unit) × (Unit ⊕ b))) : 0 ≤ supportSectorWeightA ψ :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

theorem supportSectorWeightB_nonneg
    (ψ : PureVector ((a ⊕ Unit) × (Unit ⊕ b))) : 0 ≤ supportSectorWeightB ψ :=
  Finset.sum_nonneg fun _ _ => Complex.normSq_nonneg _

/-- Supported branch weights and the vacuum weight sum to one. -/
theorem supportedPure_weights_sum
    (ψ : PureVector ((a ⊕ Unit) × (Unit ⊕ b)))
    (hs : ∀ i : a, ∀ j : b, ψ.amp (Sum.inl i, Sum.inr j) = 0) :
    supportSectorWeightA ψ + Complex.normSq (ψ.amp (Sum.inr (), Sum.inl ())) +
      supportSectorWeightB ψ = 1 := by
  have h := congrArg Complex.re ψ.trace_rankOne_eq_one
  simpa [rankOneMatrix_trace, dotProduct, Fintype.sum_prod_type,
    Fintype.sum_sum_type, Complex.mul_conj, hs, supportSectorWeightA,
    supportSectorWeightB, add_assoc] using h

/-- Amplitudes of the compression of the second sector into one coordinate. -/
def supportedCompressionAmp
    (ψ : PureVector ((a ⊕ Unit) × (Unit ⊕ b))) : (a ⊕ Unit) × Qubit → ℂ :=
  fun x => if x.2 = 0 then ψ.amp (x.1, Sum.inl ()) else
    match x.1 with
    | Sum.inl _ => 0
    | Sum.inr _ => (Real.sqrt (supportSectorWeightB ψ) : ℂ)

/-- Normalized compression; no division by a sector weight is used. -/
def supportedCompression
    (ψ : PureVector ((a ⊕ Unit) × (Unit ⊕ b)))
    (hs : ∀ i : a, ∀ j : b, ψ.amp (Sum.inl i, Sum.inr j) = 0) :
    PureVector ((a ⊕ Unit) × Qubit) where
  amp := supportedCompressionAmp ψ
  trace_rankOne_eq_one := by
    have hnorm := supportedPure_weights_sum ψ hs
    have hsqrt := Real.sq_sqrt (supportSectorWeightB_nonneg ψ)
    rw [rankOneMatrix_trace]
    simp only [dotProduct, Fintype.sum_prod_type, Fintype.sum_sum_type,
      Fin.sum_univ_two]
    simp [supportedCompressionAmp, Complex.mul_conj, ← pow_two, ← Complex.ofReal_sum]
    norm_cast
    simpa [supportSectorWeightA, hsqrt, add_assoc] using hnorm

/-- Compression preserves the first reduced density matrix. -/
theorem supportedCompression_marginalA
    (ψ : PureVector ((a ⊕ Unit) × (Unit ⊕ b)))
    (hs : ∀ i : a, ∀ j : b, ψ.amp (Sum.inl i, Sum.inr j) = 0) :
    (supportedCompression ψ hs).state.marginalA = ψ.state.marginalA := by
  have hsqrt : (Real.sqrt (supportSectorWeightB ψ) : ℂ) ^ 2 =
      (supportSectorWeightB ψ : ℂ) := by
    exact_mod_cast Real.sq_sqrt (supportSectorWeightB_nonneg ψ)
  have hu (i : Unit) : i = () := Subsingleton.elim _ _
  apply State.ext
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [State.marginalA_matrix, partialTraceB, PureVector.state_matrix_apply,
      supportedCompression, supportedCompressionAmp, Fin.sum_univ_two,
      Fintype.sum_sum_type, hs, Complex.mul_conj,
      hu, ← pow_two, hsqrt]
  simp [supportSectorWeightB]

/-- The qubit marginal of the compressed state, explicitly. -/
theorem supportedCompression_marginalB_matrix
    (ψ : PureVector ((a ⊕ Unit) × (Unit ⊕ b)))
    (hs : ∀ i : a, ∀ j : b, ψ.amp (Sum.inl i, Sum.inr j) = 0) :
    (supportedCompression ψ hs).state.marginalB.matrix =
      !![((supportSectorWeightA ψ : ℂ) +
          (Complex.normSq (ψ.amp (Sum.inr (), Sum.inl ())) : ℂ)),
          ψ.amp (Sum.inr (), Sum.inl ()) * (Real.sqrt (supportSectorWeightB ψ) : ℂ);
         (Real.sqrt (supportSectorWeightB ψ) : ℂ) *
          star (ψ.amp (Sum.inr (), Sum.inl ())),
          (supportSectorWeightB ψ : ℂ)] := by
  have hsqrt := Real.sq_sqrt (supportSectorWeightB_nonneg ψ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [State.marginalB_matrix, partialTraceA, PureVector.state_matrix_apply,
      supportedCompression, supportedCompressionAmp, Fintype.sum_sum_type,
      Complex.mul_conj, supportSectorWeightA, Complex.normSq_ofReal,
      ← pow_two, hsqrt, Complex.ofReal_sum]

/-- The compressed qubit determinant is the product of the two sector weights. -/
theorem supportedCompression_qubitDeterminant
    (ψ : PureVector ((a ⊕ Unit) × (Unit ⊕ b)))
    (hs : ∀ i : a, ∀ j : b, ψ.amp (Sum.inl i, Sum.inr j) = 0) :
    qubitDeterminant (supportedCompression ψ hs).state.marginalB =
      supportSectorWeightA ψ * supportSectorWeightB ψ := by
  have hsqrt : (Real.sqrt (supportSectorWeightB ψ) : ℂ) ^ 2 =
      (supportSectorWeightB ψ : ℂ) := by
    exact_mod_cast Real.sq_sqrt (supportSectorWeightB_nonneg ψ)
  unfold qubitDeterminant
  rw [supportedCompression_marginalB_matrix, Matrix.det_fin_two]
  have heq :
      ((supportSectorWeightA ψ : ℂ) +
        (Complex.normSq (ψ.amp (Sum.inr (), Sum.inl ())) : ℂ)) *
          (supportSectorWeightB ψ : ℂ) -
        (ψ.amp (Sum.inr (), Sum.inl ()) * (Real.sqrt (supportSectorWeightB ψ) : ℂ)) *
          ((Real.sqrt (supportSectorWeightB ψ) : ℂ) *
            star (ψ.amp (Sum.inr (), Sum.inl ()))) =
      (supportSectorWeightA ψ : ℂ) * (supportSectorWeightB ψ : ℂ) := by
    have hn : ψ.amp (Sum.inr (), Sum.inl ()) *
        star (ψ.amp (Sum.inr (), Sum.inl ())) =
          (Complex.normSq (ψ.amp (Sum.inr (), Sum.inl ())) : ℂ) := by
      simpa using Complex.mul_conj (ψ.amp (Sum.inr (), Sum.inl ()))
    calc
      _ = (supportSectorWeightA ψ : ℂ) * (supportSectorWeightB ψ : ℂ) +
          (Complex.normSq (ψ.amp (Sum.inr (), Sum.inl ())) : ℂ) *
            (supportSectorWeightB ψ : ℂ) -
          (ψ.amp (Sum.inr (), Sum.inl ()) * star (ψ.amp (Sum.inr (), Sum.inl ()))) *
            (Real.sqrt (supportSectorWeightB ψ) : ℂ) ^ 2 := by ring
      _ = _ := by rw [hsqrt, hn]; ring
  simpa only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero] using congrArg Complex.re heq

/-- Exact supported pure-state entropy, in arbitrary finite dimensions,
including empty non-vacuum sectors. -/
theorem supported_pure_entropy
    (ψ : PureVector ((a ⊕ Unit) × (Unit ⊕ b)))
    (hs : ∀ i : a, ∀ j : b, ψ.amp (Sum.inl i, Sum.inr j) = 0) :
    ψ.state.marginalA.vonNeumann =
      entanglementCurve (2 * Real.sqrt (supportSectorWeightA ψ * supportSectorWeightB ψ)) := by
  rw [← supportedCompression_marginalA ψ hs,
    State.pureVector_marginalA_vonNeumann_eq_marginalB,
    qubit_vonNeumann_eq_entanglementCurve_det, supportedCompression_qubitDeterminant]

end
end AmplitudeDamping
