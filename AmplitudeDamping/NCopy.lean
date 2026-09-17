import AmplitudeDamping.StrongSuperadditivity

/-!
# The recursive n-copy consequence
-/

namespace AmplitudeDamping

open QIT

noncomputable section

/-- Sum of the one-copy convex-roof terms of the recursively exposed single
sites of an `n`-qubit state. -/
def amplitudeDampingMarginalRoofSum
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (n : ℕ) → State (QIT.TensorPower Qubit n) → ℝ
  | 0, _ => 0
  | n + 1, rho =>
      outputEntropyRoof (amplitudeDamping p hp0 hp1) rho.marginalA +
        amplitudeDampingMarginalRoofSum p hp0 hp1 n rho.marginalB

/-- For every number of copies and every possibly correlated input, the
convex-roof output entropy of the tensor-power amplitude-damping channel is at
least the sum of the one-site convex roofs of its recursive marginals. -/
theorem amplitudeDamping_tensorPower_roof_lower_bound
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∀ (n : ℕ) (rho : State (QIT.TensorPower Qubit n)),
      outputEntropyRoof ((amplitudeDamping p hp0 hp1).tensorPower n) rho ≥
        amplitudeDampingMarginalRoofSum p hp0 hp1 n rho := by
  intro n
  induction n with
  | zero =>
      intro rho
      simpa [amplitudeDampingMarginalRoofSum] using
        outputEntropyRoof_nonneg
          ((amplitudeDamping p hp0 hp1).tensorPower 0) rho
  | succ n ih =>
      intro rho
      have hstep :=
        amplitudeDamping_outputEntropyRoof_stronglySuperadditive
          p hp0 hp1 ((amplitudeDamping p hp0 hp1).tensorPower n) rho
      have htail := ih rho.marginalB
      rw [Channel.tensorPower_succ]
      change
        outputEntropyRoof
            ((amplitudeDamping p hp0 hp1).prod
              ((amplitudeDamping p hp0 hp1).tensorPower n)) rho ≥
          outputEntropyRoof (amplitudeDamping p hp0 hp1) rho.marginalA +
            amplitudeDampingMarginalRoofSum p hp0 hp1 n rho.marginalB
      linarith

end

end AmplitudeDamping
