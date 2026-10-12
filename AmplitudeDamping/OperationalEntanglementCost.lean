import AmplitudeDamping.ChannelFormationRegularization
import QIT.Protocols.LOCC.Core

/-!
# Operational entanglement costs and their classical regularization interfaces

Protocols are finite trees of local instruments with communicated outcomes.
Their depth and alphabet sizes may grow with block length. Shared resources
are maximally entangled states of arbitrary Schmidt rank. Channel error is
half the diamond norm, so correlated inputs and arbitrary references are
included. No adaptive interleaving of calls to the target channel occurs.

The state (Hayden--Horodecki--Terhal) and parallel channel (Berta--Brandão--
Christandl--Wehner) regularization theorems are explicit hypotheses. The
operational quantities below are defined from protocols, independently of
formation; they are not abbreviations for the conclusions of those theorems.
-/
namespace AmplitudeDamping
open QIT Filter
open scoped BigOperators Topology
noncomputable section

/-- Finite-round LOCC, represented by a tree of local instruments. A branch's
continuation can depend on the communicated classical result. Intermediate
local spaces and the number of outcomes may change at each node. -/
inductive IsFiniteLOCC :
    {a b c d : Type} → [Fintype a] → [DecidableEq a] →
    [Fintype b] → [DecidableEq b] → [Fintype c] → [DecidableEq c] →
    [Fintype d] → [DecidableEq d] → Channel (a × b) (c × d) → Prop
  | local {a b c d : Type} [Fintype a] [DecidableEq a]
      [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
      [Fintype d] [DecidableEq d]
      (N : Channel a c) (M : Channel b d) : IsFiniteLOCC (N.prod M)
  | alice {a b c d e : Type} [Fintype a] [DecidableEq a]
      [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
      [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
      (k : ℕ) (I : FiniteInstrument a e (Fin k))
      (next : Fin k → Channel (e × b) (c × d))
      (hnext : ∀ i, IsFiniteLOCC (next i))
      (N : Channel (a × b) (c × d))
      (hmap : N.map = ∑ i, (next i).map.comp
        (MatrixMap.kron (I.branch i) (Channel.idChannel b).map)) : IsFiniteLOCC N
  | bob {a b c d e : Type} [Fintype a] [DecidableEq a]
      [Fintype b] [DecidableEq b] [Fintype c] [DecidableEq c]
      [Fintype d] [DecidableEq d] [Fintype e] [DecidableEq e]
      (k : ℕ) (I : FiniteInstrument b e (Fin k))
      (next : Fin k → Channel (a × e) (c × d))
      (hnext : ∀ i, IsFiniteLOCC (next i))
      (N : Channel (a × b) (c × d))
      (hmap : N.map = ∑ i, (next i).map.comp
        (MatrixMap.kron (Channel.idChannel a).map (I.branch i))) : IsFiniteLOCC N

variable {a b : Type} [Fintype a] [DecidableEq a]
  [Fintype b] [DecidableEq b]

/-- A state preparation protocol consuming a maximally entangled resource. -/
structure StatePreparation (a b : Type) [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (m : ℕ) where
  resource_pos : 0 < m
  protocol : Channel (Fin m × Fin m) (a × b)
  localOperations : IsFiniteLOCC protocol

/-- The prepared state, without assuming any accuracy. -/
def StatePreparation.output {m : ℕ} (P : StatePreparation a b m) : State (a × b) :=
  letI : NeZero m := ⟨P.resource_pos.ne'⟩
  P.protocol.applyState (State.maximallyEntangled (Equiv.refl (Fin m)))

/-- A parallel simulation. Alice receives the entire input block and her half
of the resource; Bob receives its other half and must produce the output. -/
structure ParallelSimulation (a b : Type) [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (m : ℕ) where
  resource_pos : 0 < m
  simulated : Channel a b
  protocol : Channel ((a × Fin m) × Fin m) (PUnit × b)
  localOperations : IsFiniteLOCC protocol
  realization : ∀ (rho : State a) (h : 0 < m),
    letI : NeZero m := ⟨h.ne'⟩
    simulated.applyState rho =
      (protocol.applyState
        ((rho.prod (State.maximallyEntangled (Equiv.refl (Fin m)))).reindex
          (Equiv.prodAssoc a (Fin m) (Fin m)).symm)).marginalB

/-- An asymptotic upper bound on the resource rate. This eventual-ε form
expresses the limsup bound without conventions for unbounded real sequences. -/
def ResourceRateAtMost (m : ℕ → ℕ) (R : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∀ᶠ n in atTop,
    log2 (m n : ℝ) / ((n : ℝ) + 1) ≤ R + ε

/-- Achievability for asymptotic LOCC state preparation. -/
def IsAchievableStateCost (rho : State (a × b)) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ (m : ℕ → ℕ)
    (P : ∀ n, StatePreparation (TensorPower a (n+1)) (TensorPower b (n+1)) (m n)),
    ResourceRateAtMost m R ∧
    Tendsto (fun n => (P n).output.normalizedTraceDistance
      (rho.tensorPowerBipartite (n+1))) atTop (𝓝 0)

/-- State cost defined operationally, separately from `entanglementCost`. -/
def operationalStateCost (rho : State (a × b)) : ℝ :=
  sInf {R | IsAchievableStateCost rho R}

/-- Achievability for uniform, parallel channel simulation by LOCC. -/
def IsAchievableParallelCost [Nonempty a] (N : Channel a b) (R : ℝ) : Prop :=
  0 ≤ R ∧ ∃ (m : ℕ → ℕ)
    (P : ∀ n, ParallelSimulation (TensorPower a (n+1)) (TensorPower b (n+1)) (m n)),
    ResourceRateAtMost m R ∧
    Tendsto (fun n =>
      letI : Nonempty (TensorPower a (n+1)) := tensorPower_nonempty_of_nonempty (n+1)
      (P n).simulated.diamondTraceDistance (N.tensorPower (n+1))) atTop (𝓝 0)

/-- Parallel channel cost from resource-assisted LOCC protocols. -/
def parallelEntanglementCost [Nonempty a] (N : Channel a b) : ℝ :=
  sInf {R | IsAchievableParallelCost N R}

/-- Classical state-cost regularization theorem, with operational semantics
fixed above. It is a hypothesis, not an axiom or a definition of cost. -/
structure StateCostRegularization : Prop where
  achievable_nonempty : ∀ {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (rho : State (a × b)),
    ∃ R, IsAchievableStateCost rho R
  eq_regularized : ∀ {a b : Type} [Fintype a] [DecidableEq a]
    [Fintype b] [DecidableEq b] (rho : State (a × b)),
    operationalStateCost rho = entanglementCost rho

/-- Classical parallel channel simulation theorem, including finiteness of
its achievable-rate set so real infima cannot hide an empty feasible set. -/
structure ParallelCostRegularization : Prop where
  achievable_nonempty : ∀ {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b] (N : Channel a b),
    ∃ R, IsAchievableParallelCost N R
  eq_regularized : ∀ {a b : Type} [Fintype a] [DecidableEq a] [Nonempty a]
    [Fintype b] [DecidableEq b] [Nonempty b] (N : Channel a b),
    parallelEntanglementCost N = FormationRegularization.regularizedFormation N

/-- Strong formation additivity identifies the operational one-channel cost. -/
theorem parallelEntanglementCost_eq_of_strong [Nonempty a] [Nonempty b]
    (hclassical : ParallelCostRegularization) (N : Channel a b)
    (hN : FormationRegularization.StrongFormationAdditive N) :
    parallelEntanglementCost N = channelEntanglementOfFormation N := by
  rw [hclassical.eq_regularized, FormationRegularization.regularizedFormation_eq N hN]

/-- Strong operational cost additivity needs no partner additivity assumption. -/
theorem parallelEntanglementCost_prod_eq_of_strong [Nonempty a] [Nonempty b]
    {c d : Type} [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]
    [Nonempty c] [Nonempty d]
    (hclassical : ParallelCostRegularization) (N : Channel a b)
    (hN : FormationRegularization.StrongFormationAdditive N) (M : Channel c d) :
    parallelEntanglementCost (N.prod M) =
      parallelEntanglementCost N + parallelEntanglementCost M := by
  rw [hclassical.eq_regularized, FormationRegularization.regularizedFormation_prod_eq N hN,
    ← hclassical.eq_regularized M, parallelEntanglementCost_eq_of_strong hclassical N hN]
end
end AmplitudeDamping
