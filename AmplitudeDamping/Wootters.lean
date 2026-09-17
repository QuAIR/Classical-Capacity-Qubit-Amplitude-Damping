import AmplitudeDamping.Concurrence

/-!
# Wootters' corner formula as an interface hypothesis

The manuscript's Appendix B evaluates Wootters' formula
`E_F(ρ) = e_conc(c(ρ))` (W. K. Wootters, Phys. Rev. Lett. 80, 2245 (1998);
manuscript eq. `(wootters)`) on two-qubit states whose `|01⟩` population
vanishes: with `z = ⟨00|ρ|11⟩` the concurrence reduces to `c(ρ) = 2 ‖z‖`,
giving the corner identity eq. `(three-corner-eof)`,

`E_F(ρ) = entanglementCurve (2 * ‖⟨00|ρ|11⟩‖)`  whenever `⟨01|ρ|01⟩ = 0`.

Its `≥` direction is proved elementarily in `Concurrence.lean`
(`entanglementOfFormation_ge_entanglementCurve`).  The `≤` direction rests
on Wootters' concurrence formula for arbitrary two-qubit states, which lies
outside the scope of this development; it therefore enters as an explicit
hypothesis `woottersKernelUpperBound`, in the style of Lean-QIT's
`allickiFannesWinter_statement`.  Every downstream result invoking the
corner identity (strong superadditivity, Corollary 7, the Choi-state
computation) takes this hypothesis as a parameter, so the trust boundary is
tracked through the whole dependency chain.

This module also fixes the kernel-vector phrasing `ρ *ᵥ ket01 = 0` of the
gauge-fixed hypothesis of Theorem 6 and relates it to the diagonal-entry
phrasing used by `Concurrence.lean`: for a positive semidefinite state the
two are equivalent, and only the trivial direction (kernel vector forces
vanishing diagonal entry) is needed downstream.
-/

open scoped BigOperators NNReal ComplexOrder Matrix

namespace AmplitudeDamping

open QIT

noncomputable section

/-- The computational basis vector `|01⟩` on two qubits. -/
def ket01 : Prod Qubit Qubit → ℂ := fun p => if p = (0, 1) then 1 else 0

theorem ket01_apply (p : Prod Qubit Qubit) :
    ket01 p = if p = (0, 1) then 1 else 0 :=
  rfl

@[simp] theorem ket01_self : ket01 (0, 1) = 1 := by
  simp [ket01]

theorem ket01_of_ne {p : Prod Qubit Qubit} (h : p ≠ (0, 1)) : ket01 p = 0 := by
  simp [ket01, h]

/-- Applying a matrix to `|01⟩` selects its `(0, 1)` column. -/
theorem mulVec_ket01_apply (M : Matrix (Prod Qubit Qubit) (Prod Qubit Qubit) ℂ)
    (x : Prod Qubit Qubit) :
    (M *ᵥ ket01) x = M x (0, 1) := by
  simp [Matrix.mulVec, dotProduct, ket01]

/-- A matrix annihilating `|01⟩` has a vanishing `|01⟩` diagonal entry. -/
theorem matrix_diagonal_of_mulVec_ket01_eq_zero
    {M : Matrix (Prod Qubit Qubit) (Prod Qubit Qubit) ℂ}
    (h : M *ᵥ ket01 = 0) :
    M (0, 1) (0, 1) = 0 := by
  have hx := congrFun h (0, 1)
  rwa [mulVec_ket01_apply, Pi.zero_apply] at hx

/-- **Interface hypothesis** (trust boundary): the `≤` direction of the
manuscript's eq. `(three-corner-eof)`.  For a two-qubit state whose `|01⟩`
population vanishes, the entanglement of formation is at most the
concurrence curve at twice the `⟨00|ρ|11⟩`` coherence.  This follows from
Wootters' formula via the spin-flip spectrum computation of Appendix B; the
`≥` direction is `entanglementOfFormation_ge_entanglementCurve`. -/
def woottersKernelUpperBound : Prop :=
  ∀ rho : State (Prod Qubit Qubit),
    rho.matrix (0, 1) (0, 1) = 0 →
    entanglementOfFormation rho ≤
      entanglementCurve (2 * ‖rho.matrix (0, 0) (1, 1)‖)

/-- The corner identity eq. `(three-corner-eof)` in diagonal-entry phrasing:
for states with vanishing `|01⟩` population the entanglement of formation
equals the concurrence curve at twice the `⟨00|ρ|11⟩` coherence, given the
Wootters upper-bound hypothesis. -/
theorem entanglementOfFormation_eq_entanglementCurve
    (h : woottersKernelUpperBound) (rho : State (Prod Qubit Qubit))
    (h01 : rho.matrix (0, 1) (0, 1) = 0) :
    entanglementOfFormation rho =
      entanglementCurve (2 * ‖rho.matrix (0, 0) (1, 1)‖) :=
  le_antisymm (h rho h01) (entanglementOfFormation_ge_entanglementCurve rho h01)

/-- The corner identity eq. `(three-corner-eof)` in kernel-vector phrasing:
the gauge-fixed hypothesis of Theorem 6 is that `|01⟩` lies in the kernel
of `ρ`. -/
theorem entanglementOfFormation_eq_entanglementCurve_of_kernelVector
    (h : woottersKernelUpperBound) (rho : State (Prod Qubit Qubit))
    (hk : rho.matrix *ᵥ ket01 = 0) :
    entanglementOfFormation rho =
      entanglementCurve (2 * ‖rho.matrix (0, 0) (1, 1)‖) :=
  entanglementOfFormation_eq_entanglementCurve h rho
    (matrix_diagonal_of_mulVec_ket01_eq_zero hk)

end

end AmplitudeDamping
