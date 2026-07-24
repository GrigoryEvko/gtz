/-
# Compactness of the collared configuration class

The EQ compactness leg's missing hypothesis (SS118 GAP 2, discharged in the
A7 round-2 workflow, both audits SOUND — here made kernel-proven): the
collared class — Parseval configurations with a weight floor and the
all-heavy leverage floor — is a COMPACT subset of the finite-dimensional
configuration space. Closed because every constraint is a non-strict
polynomial condition; bounded because Parseval caps every weighted leverage
at one (`t_c · ℓ_c ≤ 1`), so the weight floor caps every leverage and hence
every atom entry, while the weight simplex caps the weights. The leverage
ceiling is re-proved hypothesis-parameterized (on raw atom/weight pairs, no
`WeightedDesign` structure) so the boundedness argument runs on the ambient
product space; `design_mem_collaredSet` bridges back to designs.
-/
import Mathlib
import Gtz.Basic
import Gtz.MarginTransfer
import Gtz.LeverageBound

namespace Gtz

open Matrix

/-- The collared configuration set: atom families with weights satisfying
Parseval, the weight-sum normalization, the weight floor, and the all-heavy
leverage floor, as a subset of the finite-dimensional product space. -/
def collaredSet (m k : ℕ) (weightFloor : ℝ) :
    Set ((Fin m → Fin k → ℝ) × (Fin m → ℝ)) :=
  { config |
      (∑ c, config.2 c • atomMatrix (config.1 c)) = 1
      ∧ (∑ c, config.2 c) = 1
      ∧ (∀ c, weightFloor ≤ config.2 c)
      ∧ ∀ c, 1 ≤ leverageOf (config.1 c) }

/-- Every collared all-heavy design's configuration lies in the set. -/
theorem design_mem_collaredSet {m k : ℕ} (D : WeightedDesign m k)
    {weightFloor : ℝ} (hweights : ∀ c, weightFloor ≤ D.weight c)
    (hheavy : ∀ c, 1 ≤ leverageOf (D.atom c)) :
    (D.atom, D.weight) ∈ collaredSet m k weightFloor :=
  ⟨D.isParseval, D.weight_sum_one, hweights, hheavy⟩

/-- The leverage ceiling, hypothesis-parameterized (the raw-pair mirror of
`weighted_leverage_le_one`): Parseval with nonnegative weights caps every
weighted leverage at one. -/
theorem weighted_leverage_le_one_of_parseval {m k : ℕ}
    {atoms : Fin m → Fin k → ℝ} {weights : Fin m → ℝ}
    (hparseval : ∑ c, weights c • atomMatrix (atoms c) = 1)
    (hnonneg : ∀ c, 0 ≤ weights c) (chosen : Fin m) :
    weights chosen * leverageOf (atoms chosen) ≤ 1 := by
  set probe := atoms chosen with hprobe
  have hform : probe ⬝ᵥ ((∑ c, weights c • atomMatrix (atoms c)) *ᵥ probe)
      = ∑ c, weights c * (atoms c ⬝ᵥ probe) ^ 2 := by
    rw [Matrix.sum_mulVec, dotProduct_sum]
    exact Finset.sum_congr rfl fun c _ => by
      rw [Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, atom_form_eq_sq]
  have hidentity : probe ⬝ᵥ ((∑ c, weights c • atomMatrix (atoms c)) *ᵥ probe)
      = probe ⬝ᵥ probe := by
    rw [hparseval, Matrix.one_mulVec]
  have hsingle : weights chosen * (atoms chosen ⬝ᵥ probe) ^ 2
      ≤ ∑ c, weights c * (atoms c ⬝ᵥ probe) ^ 2 :=
    Finset.single_le_sum (f := fun c => weights c * (atoms c ⬝ᵥ probe) ^ 2)
      (fun c _ => mul_nonneg (hnonneg c) (sq_nonneg _)) (Finset.mem_univ chosen)
  have hkey : weights chosen * (probe ⬝ᵥ probe) ^ 2 ≤ probe ⬝ᵥ probe := by
    calc weights chosen * (probe ⬝ᵥ probe) ^ 2
        = weights chosen * (atoms chosen ⬝ᵥ probe) ^ 2 := by rw [hprobe]
      _ ≤ ∑ c, weights c * (atoms c ⬝ᵥ probe) ^ 2 := hsingle
      _ = probe ⬝ᵥ probe := by rw [← hform, hidentity]
  have hselfNonneg : 0 ≤ probe ⬝ᵥ probe := by
    simp only [dotProduct]
    exact Finset.sum_nonneg fun index _ => mul_self_nonneg _
  have hlevDot : leverageOf (atoms chosen) = probe ⬝ᵥ probe := by
    rw [hprobe, leverageOf_eq_dotProduct]
  rw [hlevDot]
  rcases eq_or_lt_of_le hselfNonneg with hzero | hpos
  · rw [← hzero, mul_zero]
    exact zero_le_one
  · have hcancel : weights chosen * (probe ⬝ᵥ probe) * (probe ⬝ᵥ probe)
        ≤ 1 * (probe ⬝ᵥ probe) := by
      rw [one_mul]
      nlinarith [hkey]
    exact le_of_mul_le_mul_right hcancel hpos

/-- The leverage ceiling at a weight floor, raw-pair form: every leverage is
at most `1/weightFloor`. -/
theorem leverage_le_inv_floor_of_parseval {m k : ℕ}
    {atoms : Fin m → Fin k → ℝ} {weights : Fin m → ℝ}
    (hparseval : ∑ c, weights c • atomMatrix (atoms c) = 1)
    {weightFloor : ℝ} (hfloor : 0 < weightFloor)
    (hweights : ∀ c, weightFloor ≤ weights c) (chosen : Fin m) :
    leverageOf (atoms chosen) ≤ 1 / weightFloor := by
  have hnonneg : ∀ c, 0 ≤ weights c := fun c => le_trans hfloor.le (hweights c)
  have hshare := weighted_leverage_le_one_of_parseval hparseval hnonneg chosen
  have hlevNonneg : 0 ≤ leverageOf (atoms chosen) :=
    Finset.sum_nonneg fun i _ => sq_nonneg _
  have hfloorShare : weightFloor * leverageOf (atoms chosen)
      ≤ weights chosen * leverageOf (atoms chosen) :=
    mul_le_mul_of_nonneg_right (hweights chosen) hlevNonneg
  rw [le_div_iff₀ hfloor, mul_comm]
  linarith

/-- Each squared atom entry is bounded by the leverage. -/
theorem atom_entry_sq_le_leverage {k : ℕ} (g : Fin k → ℝ) (i : Fin k) :
    g i ^ 2 ≤ leverageOf g :=
  Finset.single_le_sum (fun j _ => sq_nonneg (g j)) (Finset.mem_univ i)

/-- On the weight simplex, every nonnegative weight is at most one. -/
theorem weight_le_one_of_sum_one {m : ℕ} {weights : Fin m → ℝ}
    (hsum : ∑ c, weights c = 1) (hnonneg : ∀ c, 0 ≤ weights c)
    (chosen : Fin m) : weights chosen ≤ 1 := by
  calc weights chosen ≤ ∑ c, weights c :=
        Finset.single_le_sum (fun c _ => hnonneg c) (Finset.mem_univ chosen)
    _ = 1 := hsum

/-- **The collared class is closed**: every defining constraint is a
non-strict polynomial condition, so the set is an intersection of preimages
of closed sets under continuous maps. -/
theorem isClosed_collaredSet (m k : ℕ) (weightFloor : ℝ) :
    IsClosed (collaredSet m k weightFloor) := by
  have hatomEntryCont : ∀ (c : Fin m) (i : Fin k),
      Continuous fun config : (Fin m → Fin k → ℝ) × (Fin m → ℝ)
        => config.1 c i :=
    fun c i => by fun_prop
  have hweightCont : ∀ c : Fin m,
      Continuous fun config : (Fin m → Fin k → ℝ) × (Fin m → ℝ)
        => config.2 c :=
    fun c => by fun_prop
  have hparsevalCont :
      Continuous fun config : (Fin m → Fin k → ℝ) × (Fin m → ℝ)
        => ∑ c, config.2 c • atomMatrix (config.1 c) := by
    refine continuous_matrix fun i j => ?_
    simp only [Matrix.sum_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, smul_eq_mul]
    exact continuous_finsetSum _ fun c _ =>
      (hweightCont c).mul ((hatomEntryCont c i).mul (hatomEntryCont c j))
  have hparsevalClosed :
      IsClosed {config : (Fin m → Fin k → ℝ) × (Fin m → ℝ) |
        (∑ c, config.2 c • atomMatrix (config.1 c)) = 1} :=
    isClosed_eq hparsevalCont continuous_const
  have hsumClosed :
      IsClosed {config : (Fin m → Fin k → ℝ) × (Fin m → ℝ) |
        (∑ c, config.2 c) = 1} :=
    isClosed_eq (continuous_finsetSum _ fun c _ => hweightCont c)
      continuous_const
  have hfloorClosed :
      IsClosed {config : (Fin m → Fin k → ℝ) × (Fin m → ℝ) |
        ∀ c, weightFloor ≤ config.2 c} := by
    rw [Set.setOf_forall]
    exact isClosed_iInter fun c =>
      isClosed_le continuous_const (hweightCont c)
  have hheavyClosed :
      IsClosed {config : (Fin m → Fin k → ℝ) × (Fin m → ℝ) |
        ∀ c, 1 ≤ leverageOf (config.1 c)} := by
    rw [Set.setOf_forall]
    refine isClosed_iInter fun c => isClosed_le continuous_const ?_
    simp only [leverageOf]
    exact continuous_finsetSum _ fun i _ => (hatomEntryCont c i).pow 2
  exact hparsevalClosed.inter (hsumClosed.inter
    (hfloorClosed.inter hheavyClosed))

/-- **The collared class is compact** (SS131 B2, kernel-proven): closed by
`isClosed_collaredSet` and bounded because the Parseval leverage ceiling
caps every atom entry by `√(1/weightFloor)` while the weight simplex caps
every weight by one — closed + bounded in a finite-dimensional space. -/
theorem isCompact_collaredSet (m k : ℕ) {weightFloor : ℝ}
    (hfloor : 0 < weightFloor) :
    IsCompact (collaredSet m k weightFloor) := by
  refine Metric.isCompact_of_isClosed_isBounded
    (isClosed_collaredSet m k weightFloor) ?_
  rw [isBounded_iff_forall_norm_le]
  refine ⟨max (Real.sqrt (1 / weightFloor)) 1, ?_⟩
  rintro ⟨atoms, weights⟩ ⟨hparseval, hsum, hweights, _hheavy⟩
  have hnonneg : ∀ c, 0 ≤ weights c := fun c => le_trans hfloor.le (hweights c)
  have hatomsNorm : ‖atoms‖ ≤ Real.sqrt (1 / weightFloor) := by
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro c
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    refine Real.sqrt_le_sqrt ?_
    exact le_trans (atom_entry_sq_le_leverage (atoms c) i)
      (leverage_le_inv_floor_of_parseval hparseval hfloor hweights c)
  have hweightsNorm : ‖weights‖ ≤ 1 := by
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro c
    rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg c)]
    exact weight_le_one_of_sum_one hsum hnonneg c
  calc ‖((atoms, weights) : (Fin m → Fin k → ℝ) × (Fin m → ℝ))‖
      = max ‖atoms‖ ‖weights‖ := rfl
    _ ≤ max (Real.sqrt (1 / weightFloor)) 1 :=
        max_le_max hatomsNorm hweightsNorm

end Gtz
