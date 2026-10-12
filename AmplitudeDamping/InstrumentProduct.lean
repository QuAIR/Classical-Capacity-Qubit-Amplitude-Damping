import AmplitudeDamping.BinaryInstrument
import QIT.Information.AlickiFannesWinter
import QIT.Channels.Diamond

/-!
# Entropy costs of product instruments
-/
open scoped BigOperators ComplexConjugate ComplexOrder MatrixOrder
namespace AmplitudeDamping
open QIT
noncomputable section
set_option maxHeartbeats 1000000
universe u v w x y z
variable {a : Type u} {b : Type v} {c : Type w} {d : Type x}
variable [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b]
variable [Fintype c] [DecidableEq c] [Fintype d] [DecidableEq d]

/-- Subadditivity of the homogeneous entropy on a bipartite positive matrix. -/
theorem entropyPerspective_partialTrace_le
    (X : CMatrix (a × b)) (hX : X.PosSemidef) :
    entropyPerspective X hX ≤
      entropyPerspective (partialTraceB X) (partialTraceB_posSemidef hX) +
      entropyPerspective (partialTraceA X) (partialTraceA_posSemidef hX) := by
  by_cases hx : X = 0
  · subst X
    have ha : partialTraceB (0 : CMatrix (a × b)) = 0 := by ext i j; simp [partialTraceB]
    have hb : partialTraceA (0 : CMatrix (a × b)) = 0 := by ext i j; simp [partialTraceA]
    rw [entropyPerspective_congr ha _ Matrix.PosSemidef.zero,
      entropyPerspective_congr hb _ Matrix.PosSemidef.zero]
    simp
  have ht : 0 < X.trace.re := State.posSemidef_trace_pos_of_ne_zero hX hx
  have hta : (partialTraceB X).trace.re ≠ 0 := by rw [partialTraceB_trace]; exact ht.ne'
  have htb : (partialTraceA X).trace.re ≠ 0 := by rw [partialTraceA_trace]; exact ht.ne'
  let ρ := State.normalizePSD X hX ht.ne'
  have ha : State.normalizePSD (partialTraceB X) (partialTraceB_posSemidef hX) hta =
      ρ.marginalA := by
    apply State.ext
    ext i j
    simp [ρ, State.normalizePSD_matrix, State.marginalA_matrix, partialTraceB,
      partialTraceB_trace, Matrix.smul_apply, Finset.mul_sum, Complex.real_smul]
  have hb : State.normalizePSD (partialTraceA X) (partialTraceA_posSemidef hX) htb =
      ρ.marginalB := by
    apply State.ext
    ext i j
    simp [ρ, State.normalizePSD_matrix, State.marginalB_matrix, partialTraceA,
      partialTraceA_trace, Matrix.smul_apply, Finset.mul_sum, Complex.real_smul]
  rw [entropyPerspective_eq_weight_mul_entropy _ _ ht.ne',
    entropyPerspective_eq_weight_mul_entropy _ _ hta,
    entropyPerspective_eq_weight_mul_entropy _ _ htb,
    ha, hb, partialTraceB_trace, partialTraceA_trace]
  have h := State.mutualInformation_nonneg ρ
  unfold QIT.mutualInformation at h
  have hm := mul_le_mul_of_nonneg_left (show ρ.vonNeumann ≤
      ρ.marginalA.vonNeumann + ρ.marginalB.vonNeumann by linarith) ht.le
  simpa only [mul_add] using hm

/-- Grouping positive branches can only increase their total perspective. -/
theorem sum_entropyPerspective_le
    {ι : Type y} [DecidableEq ι] (t : Finset ι)
    (X : ι → CMatrix a) (hX : ∀ i, (X i).PosSemidef) :
    (∑ i ∈ t, entropyPerspective (X i) (hX i)) ≤
      entropyPerspective (∑ i ∈ t, X i)
        (Matrix.posSemidef_sum t (fun i _ => hX i)) := by
  induction t using Finset.induction_on with
  | empty => simp
  | @insert i t hi ih =>
    simp only [Finset.sum_insert hi]
    exact (add_le_add (le_refl (entropyPerspective (X i) (hX i))) ih).trans
      (entropyPerspective_add_ge (X i) (∑ j ∈ t, X j) (hX i)
        (Matrix.posSemidef_sum t (fun j _ => hX j)))

/-- Kronecker products of maps are linear in the first map. -/
def mapKronLeft (G : MatrixMap c d) :
    MatrixMap a b →ₗ[ℂ] MatrixMap (a × c) (b × d) where
  toFun F := MatrixMap.kron F G
  map_add' F H := by
    ext X i j
    simp [MatrixMap.kron, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' k F := by
    ext X i j
    simp [MatrixMap.kron, Finset.mul_sum, mul_assoc, mul_left_comm]

/-- Kronecker products of maps are linear in the second map. -/
def mapKronRight (F : MatrixMap a b) :
    MatrixMap c d →ₗ[ℂ] MatrixMap (a × c) (b × d) where
  toFun G := MatrixMap.kron F G
  map_add' G H := by
    ext X i j
    simp [MatrixMap.kron, mul_add, Finset.sum_add_distrib]
  map_smul' k G := by
    ext X i j
    simp [MatrixMap.kron, Finset.mul_sum, mul_assoc, mul_left_comm]

/-- A trace-preserving right map disappears under the right partial trace. -/
theorem partialTraceB_mapKron
    (F : MatrixMap a b) (G : MatrixMap c d) (hG : MatrixMap.IsTracePreserving G)
    (X : CMatrix (a × c)) :
    partialTraceB (MatrixMap.kron F G X) = F (partialTraceB X) := by
  have heq : (MatrixMap.partialTraceB (a := b) (b := d)).comp (MatrixMap.kron F G) =
      F.comp (MatrixMap.partialTraceB (a := a) (b := c)) := by
    apply LinearMap.ext
    intro Y
    rw [MatrixMap.map_eq_sum_single ((MatrixMap.partialTraceB b d).comp (MatrixMap.kron F G)) Y,
      MatrixMap.map_eq_sum_single (F.comp (MatrixMap.partialTraceB a c)) Y]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    obtain ⟨i,k⟩ := i
    obtain ⟨j,l⟩ := j
    simp only [LinearMap.comp_apply, MatrixMap.partialTraceB,
      single_prod_eq_kronecker_single, MatrixMap.kron_apply_kronecker,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [partialTraceB_kronecker, partialTraceB_kronecker, hG]
    exact (map_smul F (Matrix.single k l (1 : ℂ)).trace (Matrix.single i j 1)).symm
  exact LinearMap.congr_fun heq X

/-- The symmetric partial-trace identity. -/
theorem partialTraceA_mapKron
    (F : MatrixMap a b) (G : MatrixMap c d) (hF : MatrixMap.IsTracePreserving F)
    (X : CMatrix (a × c)) :
    partialTraceA (MatrixMap.kron F G X) = G (partialTraceA X) := by
  have heq : (MatrixMap.partialTraceA (a := b) (b := d)).comp (MatrixMap.kron F G) =
      G.comp (MatrixMap.partialTraceA (a := a) (b := c)) := by
    apply LinearMap.ext
    intro Y
    rw [MatrixMap.map_eq_sum_single ((MatrixMap.partialTraceA b d).comp (MatrixMap.kron F G)) Y,
      MatrixMap.map_eq_sum_single (G.comp (MatrixMap.partialTraceA a c)) Y]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    congr 1
    obtain ⟨i,k⟩ := i
    obtain ⟨j,l⟩ := j
    simp only [LinearMap.comp_apply, MatrixMap.partialTraceA,
      single_prod_eq_kronecker_single, MatrixMap.kron_apply_kronecker,
      LinearMap.coe_mk, AddHom.coe_mk]
    rw [partialTraceA_kronecker, partialTraceA_kronecker, hF]
    exact (map_smul G (Matrix.single i j (1 : ℂ)).trace (Matrix.single k l 1)).symm
  exact LinearMap.congr_fun heq X


/-- Finite CP branches whose sum preserves trace. -/
structure EntropyInstrument (a : Type u) (b : Type v) (ι : Type y)
    [Fintype a] [DecidableEq a] [Fintype b] [DecidableEq b] [Fintype ι] where
  branch : ι → MatrixMap a b
  cp : ∀ i, MatrixMap.IsCompletelyPositive (branch i)
  totalTP : MatrixMap.IsTracePreserving (∑ i, branch i)

namespace EntropyInstrument
variable {ι : Type y} {κ : Type z} [Fintype ι] [Fintype κ]

def cost (F : EntropyInstrument a b ι) (ρ : State a) : ℝ :=
  ∑ i, entropyPerspective (F.branch i ρ.matrix)
    (MatrixMap.isCompletelyPositive_mapsPositive (F.branch i) (F.cp i) _ ρ.pos)

def prod (F : EntropyInstrument a b ι) (G : EntropyInstrument c d κ) :
    EntropyInstrument (a × c) (b × d) (ι × κ) where
  branch z := MatrixMap.kron (F.branch z.1) (G.branch z.2)
  cp z := MatrixMap.isCompletelyPositive_kron _ _ (F.cp z.1) (G.cp z.2)
  totalTP := by
    have heq : (∑ z : ι × κ, MatrixMap.kron (F.branch z.1) (G.branch z.2)) =
        MatrixMap.kron (∑ i, F.branch i) (∑ j, G.branch j) := by
      rw [Fintype.sum_prod_type]
      calc
        _ = ∑ i, mapKronRight (F.branch i) (∑ j, G.branch j) := by
          apply Finset.sum_congr rfl
          intro i _
          exact (map_sum (mapKronRight (F.branch i)) G.branch Finset.univ).symm
        _ = _ := (map_sum (mapKronLeft (∑ j, G.branch j)) F.branch Finset.univ).symm
    rw [heq]
    exact MatrixMap.isTracePreserving_kron _ _ F.totalTP G.totalTP

/-- A product instrument's total conditional entropy cost is bounded by
the two local costs, even when the input is correlated. -/
theorem cost_prod_le [DecidableEq ι] [DecidableEq κ]
    (F : EntropyInstrument a b ι) (G : EntropyInstrument c d κ)
    (ρ : State (a × c)) :
    (F.prod G).cost ρ ≤ F.cost ρ.marginalA + G.cost ρ.marginalB := by
  let Z (i : ι) (j : κ) := MatrixMap.kron (F.branch i) (G.branch j) ρ.matrix
  have hz (i : ι) (j : κ) : (Z i j).PosSemidef :=
    MatrixMap.isCompletelyPositive_mapsPositive _
      (MatrixMap.isCompletelyPositive_kron _ _ (F.cp i) (G.cp j)) _ ρ.pos
  have ha (i : ι) : (∑ j, partialTraceB (Z i j)) = F.branch i ρ.marginalA.matrix := by
    have hm := congrArg (fun H : MatrixMap (a × c) (b × d) =>
      (MatrixMap.partialTraceB b d) (H ρ.matrix))
      (map_sum (mapKronRight (F.branch i)) G.branch Finset.univ)
    have hh := partialTraceB_mapKron (F.branch i) (∑ j, G.branch j) G.totalTP ρ.matrix
    simpa only [map_sum, LinearMap.sum_apply, mapKronRight, LinearMap.coe_mk,
      AddHom.coe_mk, MatrixMap.partialTraceB, State.marginalA_matrix] using hm.symm.trans hh
  have hb (j : κ) : (∑ i, partialTraceA (Z i j)) = G.branch j ρ.marginalB.matrix := by
    have hm := congrArg (fun H : MatrixMap (a × c) (b × d) =>
      (MatrixMap.partialTraceA b d) (H ρ.matrix))
      (map_sum (mapKronLeft (G.branch j)) F.branch Finset.univ)
    have hh := partialTraceA_mapKron (∑ i, F.branch i) (G.branch j) F.totalTP ρ.matrix
    simpa only [map_sum, LinearMap.sum_apply, mapKronLeft, LinearMap.coe_mk,
      AddHom.coe_mk, MatrixMap.partialTraceA, State.marginalB_matrix] using hm.symm.trans hh
  have hau (i : ι) :
      (∑ j, entropyPerspective (partialTraceB (Z i j)) (partialTraceB_posSemidef (hz i j))) ≤
      entropyPerspective (F.branch i ρ.marginalA.matrix)
        (MatrixMap.isCompletelyPositive_mapsPositive _ (F.cp i) _ ρ.marginalA.pos) := by
    have h := sum_entropyPerspective_le Finset.univ (fun j => partialTraceB (Z i j))
      (fun j => partialTraceB_posSemidef (hz i j))
    exact h.trans_eq (entropyPerspective_congr (ha i) _ _)
  have hbu (j : κ) :
      (∑ i, entropyPerspective (partialTraceA (Z i j)) (partialTraceA_posSemidef (hz i j))) ≤
      entropyPerspective (G.branch j ρ.marginalB.matrix)
        (MatrixMap.isCompletelyPositive_mapsPositive _ (G.cp j) _ ρ.marginalB.pos) := by
    have h := sum_entropyPerspective_le Finset.univ (fun i => partialTraceA (Z i j))
      (fun i => partialTraceA_posSemidef (hz i j))
    exact h.trans_eq (entropyPerspective_congr (hb j) _ _)
  change (∑ z : ι × κ, entropyPerspective (Z z.1 z.2) (hz z.1 z.2)) ≤ _
  rw [Fintype.sum_prod_type]
  calc
    _ ≤ ∑ i, ∑ j,
        (entropyPerspective (partialTraceB (Z i j)) (partialTraceB_posSemidef (hz i j)) +
         entropyPerspective (partialTraceA (Z i j)) (partialTraceA_posSemidef (hz i j))) := by
      apply Finset.sum_le_sum
      intro i _
      apply Finset.sum_le_sum
      intro j _
      exact entropyPerspective_partialTrace_le (Z i j) (hz i j)
    _ = (∑ i, ∑ j, entropyPerspective (partialTraceB (Z i j)) (partialTraceB_posSemidef (hz i j))) +
        (∑ j, ∑ i, entropyPerspective (partialTraceA (Z i j)) (partialTraceA_posSemidef (hz i j))) := by
      simp_rw [Finset.sum_add_distrib]
      rw [Finset.sum_comm (f := fun i j => entropyPerspective (partialTraceA (Z i j))
        (partialTraceA_posSemidef (hz i j)))]
    _ ≤ F.cost ρ.marginalA + G.cost ρ.marginalB :=
      add_le_add (Finset.sum_le_sum (fun i _ => hau i))
        (Finset.sum_le_sum (fun j _ => hbu j))

end EntropyInstrument


/-- The binary Kraus family as a trace-preserving finite instrument. -/
def binaryEntropyInstrument (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    EntropyInstrument Qubit Qubit (Fin 2) where
  branch s := MatrixMap.ofKraus (fun _ : Unit => binaryInstrumentKraus p s)
  cp s := MatrixMap.ofKraus_completelyPositive _
  totalTP := by
    have heq : (∑ s : Fin 2,
        MatrixMap.ofKraus (fun _ : Unit => binaryInstrumentKraus p s)) =
        (amplitudeDamping p hp0 hp1).map := by
      apply LinearMap.ext
      intro X
      rw [show (amplitudeDamping p hp0 hp1).map X =
        MatrixMap.ofKraus (amplitudeKraus p) X from rfl,
        ← binaryInstrumentKraus_map]
      simp [MatrixMap.ofKraus]
    rw [heq]
    exact (amplitudeDamping p hp0 hp1).tracePreserving

@[simp]
theorem binaryEntropyInstrument_cost
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (ρ : State Qubit) :
    (binaryEntropyInstrument p hp0 hp1).cost ρ = binaryInstrumentCost p ρ := by
  simp [EntropyInstrument.cost, binaryEntropyInstrument, MatrixMap.ofKraus,
    binaryInstrumentCost, binaryInstrumentBranch, Fin.sum_univ_two]

/-- The empty product instrument on the one-dimensional system. -/
def unitEntropyInstrument : EntropyInstrument PUnit PUnit PUnit where
  branch _ := (Channel.idChannel PUnit).map
  cp _ := (Channel.idChannel PUnit).completelyPositive
  totalTP := by simpa using (Channel.idChannel PUnit).tracePreserving

@[simp]
theorem unitEntropyInstrument_cost (ρ : State PUnit) : unitEntropyInstrument.cost ρ = 0 := by
  unfold EntropyInstrument.cost unitEntropyInstrument
  simp only [Finset.univ_unique, Finset.sum_singleton]
  have hm : (Channel.idChannel PUnit).map ρ.matrix = ρ.matrix := by
    simp [Channel.idChannel, MatrixMap.ofKraus]
  rw [entropyPerspective_congr hm _ ρ.pos]
  change ρ.vonNeumann + xlog2 ρ.matrix.trace.re = 0
  simp [ρ.trace_re_eq_one, xlog2, log2, State.vonNeumann_punit_eq_zero]

/-- The product of `n` copies of the binary amplitude-damping instrument. -/
def binaryProductInstrument (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    (n : ℕ) → EntropyInstrument (TensorPower Qubit n) (TensorPower Qubit n)
      (TensorPower (Fin 2) n)
  | 0 => unitEntropyInstrument
  | n + 1 => (binaryEntropyInstrument p hp0 hp1).prod (binaryProductInstrument p hp0 hp1 n)

/-- Uniform entropy-cost bound for every correlated input at every blocklength. -/
theorem binaryProductInstrument_cost_le
    (p : ℝ) (hp0 : 0 ≤ p) (hp1 : p ≤ 1) (n : ℕ)
    (ρ : State (TensorPower Qubit n)) :
    (binaryProductInstrument p hp0 hp1 n).cost ρ ≤
      (n : ℝ) * binaryEntropy ((1 + Real.sqrt p) / 2) := by
  induction n with
  | zero =>
    simp only [binaryProductInstrument, Nat.cast_zero, zero_mul]
    exact le_of_eq (unitEntropyInstrument_cost ρ)
  | succ n ih =>
    change ((binaryEntropyInstrument p hp0 hp1).prod
      (binaryProductInstrument p hp0 hp1 n)).cost ρ ≤ _
    have h := EntropyInstrument.cost_prod_le (binaryEntropyInstrument p hp0 hp1)
      (binaryProductInstrument p hp0 hp1 n) ρ
    rw [binaryEntropyInstrument_cost] at h
    have ha := binaryInstrumentCost_le p hp0 hp1 ρ.marginalA
    have hb := ih ρ.marginalB
    push_cast
    nlinarith

end
end AmplitudeDamping
