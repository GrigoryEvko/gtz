/-
# The pivot budget: strict domination read off the pivots alone

`Gtz.posDef_subsetSum_of_crossPivotSlack` proves strict domination from the
absolute cross pivots between the omitted labels.  Cross pivots are off-diagonal
data, and no stratum of the campaign carries them as hypotheses.  Pivots are
diagonal data, and every stratum carries those.

This file removes the cross pivots.  The landed idempotent law
`Gtz.sum_erase_coweight_mul_fullPivotGram_sq` says that the whole off-diagonal
row energy of a label is its own pivot defect,

  `∑_{b ≠ a} (1 - w_b) * F_ab ^ 2 = π_a * (1 - (1 - w_a) * π_a)`,

so Cauchy–Schwarz turns a bound on that one number into a bound on the sum of
absolute cross pivots.  The criterion becomes an inequality in the pivot of one
label, its own weight, the largest weight, and the omitted count.

## PROVED here, kernel-checked, unconditional

* `Gtz.sum_ite_eq_sum_erase` — the bookkeeping that turns the guarded sum of the
  dominance criterion into a sum over the erased set.
* `Gtz.sq_absRowOff_le_card_mul_energy` — Cauchy–Schwarz on the absolute row.
* `Gtz.weightCap_mul_sum_erase_sq_le_pivotDefect` — **the energy transfer.**  The
  bare off-diagonal energy over ANY set of omitted labels is bounded by the
  landed pivot defect, once the weights carry a cap.
* `Gtz.posDef_subsetSum_of_pivotBudget` — **THE PIVOT BUDGET.**  A selection is
  strictly dominating when every omitted label `a` satisfies

    `(k - 1) * π_a * (1 - (1 - w_a) * π_a) < (1 - maxWeight) * (1 - π_a) ^ 2`,

  with `k` the omitted count.  No cross pivot appears.
* `Gtz.dominates_of_quarterPivotQuarter` — **the quarter-cap card-three cell.**
  When every weight is at most one quarter, any three omitted labels of pivot at
  most one quarter leave a dominating selection.  The threshold has room: the
  budget closes at `1 / 4` with the value `1 / 16` to spare, and it fails only
  after about `0.2566`.

## A weight cap must be at least one over the size

The weights of a `Gtz.WeightedDesign m k` are positive and sum to one, so some
weight is at least `1 / m` and a cap below `1 / m` is contradictory.  At size
six the smallest satisfiable cap is `1 / 6`, attained at the uniform design.
**A card-three cell written at the cap `1 / 10` would be vacuous at size six**,
which is why the specialization below uses `1 / 4`.  This also explains why the
campaign may take `∃ heavyLabel, 1 / 10 ≤ weight heavyLabel` as a free
hypothesis at size six: it is a pigeonhole, not an assumption.

The general budget carries the cap as a parameter, so a stratum that knows a
sharper cap gets a sharper threshold.  At cap `1 / 6` the budget closes up to
about `0.2812`, and at cap `1 / 2` up to about `0.1835`.
-/
import Gtz.Design.ComplementDiagonalDominance
import Gtz.Design.PivotGramIdempotent
import Gtz.Reduction.DescentLadder
import Gtz.Design.ComplementLeverageLaw

namespace Gtz

open Finset Matrix

variable {m k : ℕ}

/-! ## Bookkeeping -/

/-- A sum guarded by `if b = a then 0` is a sum over the erased set. -/
theorem sum_ite_eq_sum_erase (f : Fin m → ℝ) (omitted : Finset (Fin m)) (a : Fin m) :
    ∑ b ∈ omitted, (if b = a then 0 else f b) = ∑ b ∈ omitted.erase a, f b := by
  classical
  rw [← Finset.filter_ne' omitted a, Finset.sum_filter]
  exact Finset.sum_congr rfl fun b _ => by by_cases hba : b = a <;> simp [hba]

/-! ## Cauchy–Schwarz on the absolute row -/

/-- **The absolute row is controlled by the row energy.**  Cauchy–Schwarz against
the constant one, so the count of the erased set is the only other input. -/
theorem sq_absRowOff_le_card_mul_energy (D : WeightedDesign m k)
    (omitted : Finset (Fin m)) (a : Fin m) :
    (∑ b ∈ omitted.erase a, |fullPivotGram D a b|) ^ 2
      ≤ (omitted.erase a).card * ∑ b ∈ omitted.erase a, fullPivotGram D a b ^ 2 := by
  classical
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq (omitted.erase a)
    (fun _ => (1 : ℝ)) (fun b => |fullPivotGram D a b|)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, sq_abs] at hcs
  exact hcs

/-! ## The energy transfer

The landed idempotent law measures the off-diagonal energy over ALL other
labels, weighted by the co-weights.  A cap on the weights turns that into a
bound on the bare energy over any subset of them.
-/

/-- **The energy transfer.**  With every weight at most `maxWeight`, the bare
off-diagonal energy of a label over any omitted set is bounded by the landed
pivot defect, scaled by the co-weight floor. -/
theorem weightCap_mul_sum_erase_sq_le_pivotDefect (D : WeightedDesign m k) (hm : 2 ≤ m)
    (maxWeight : ℝ) (hcap : ∀ b, D.weight b ≤ maxWeight)
    (omitted : Finset (Fin m)) (a : Fin m) :
    (1 - maxWeight) * ∑ b ∈ omitted.erase a, fullPivotGram D a b ^ 2
      ≤ pivot D Finset.univ a * (1 - (1 - D.weight a) * pivot D Finset.univ a) := by
  classical
  have hweightLt : ∀ b, D.weight b < 1 := fun b => design_weight_lt_one D hm b
  -- Below the cap the co-weight floor is a valid coefficient at every label.
  have hstep : (1 - maxWeight) * ∑ b ∈ omitted.erase a, fullPivotGram D a b ^ 2
      ≤ ∑ b ∈ omitted.erase a, (1 - D.weight b) * fullPivotGram D a b ^ 2 := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun b _ =>
      mul_le_mul_of_nonneg_right (by linarith [hcap b]) (sq_nonneg _)
  -- Enlarging the index set only adds nonnegative terms.
  have hgrow : ∑ b ∈ omitted.erase a, (1 - D.weight b) * fullPivotGram D a b ^ 2
      ≤ ∑ b ∈ Finset.univ.erase a, (1 - D.weight b) * fullPivotGram D a b ^ 2 := by
    refine Finset.sum_le_sum_of_subset_of_nonneg ?_ fun b _ _ =>
      mul_nonneg (by linarith [hweightLt b]) (sq_nonneg _)
    intro b hb
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hb).1, Finset.mem_univ b⟩
  rw [← sum_erase_coweight_mul_fullPivotGram_sq D hm a]
  linarith

/-! ## The pivot budget -/

/-- **THE PIVOT BUDGET.**  A selection is strictly dominating as soon as every
omitted label satisfies one inequality in its own pivot, its own weight, the
weight cap and the omitted count.

Nothing off-diagonal appears.  The proof spends Cauchy–Schwarz, the energy
transfer and the diagonal-dominance kill, in that order. -/
theorem posDef_subsetSum_of_pivotBudget (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (huniv : (subsetSum D Finset.univ - 1).PosDef)
    (maxWeight : ℝ) (hcap : ∀ b, D.weight b ≤ maxWeight) (hcapLt : maxWeight < 1)
    (selected : Finset (Fin m))
    (hpivotLt : ∀ a ∈ selectedᶜ, pivot D Finset.univ a < 1)
    (hbudget : ∀ a ∈ selectedᶜ,
      ((selectedᶜ.erase a).card : ℝ)
          * (pivot D Finset.univ a
              * (1 - (1 - D.weight a) * pivot D Finset.univ a))
        < (1 - maxWeight) * (1 - pivot D Finset.univ a) ^ 2) :
    (subsetSum D selected - 1).PosDef := by
  classical
  refine posDef_subsetSum_of_crossPivotSlack D selected huniv fun a ha => ?_
  rw [sum_ite_eq_sum_erase, fullPivotGram_diag]
  set rowAbs := ∑ b ∈ selectedᶜ.erase a, |fullPivotGram D a b| with hrowAbs
  set energy := ∑ b ∈ selectedᶜ.erase a, fullPivotGram D a b ^ 2 with henergy
  set pivotA := pivot D Finset.univ a with hpivotA
  have hrowNonneg : 0 ≤ rowAbs :=
    Finset.sum_nonneg fun b _ => abs_nonneg _
  have hdefect : 1 - pivotA > 0 := sub_pos.mpr (hpivotLt a ha)
  have hcapPos : 0 < 1 - maxWeight := sub_pos.mpr hcapLt
  have hcs := sq_absRowOff_le_card_mul_energy D selectedᶜ a
  have htransfer := weightCap_mul_sum_erase_sq_le_pivotDefect D hm maxWeight hcap selectedᶜ a
  have hcardNonneg : (0 : ℝ) ≤ ((selectedᶜ.erase a).card : ℝ) := Nat.cast_nonneg _
  -- Multiply Cauchy–Schwarz by the co-weight floor and feed in the transfer.
  have hchain : (1 - maxWeight) * rowAbs ^ 2
      ≤ ((selectedᶜ.erase a).card : ℝ)
        * (pivotA * (1 - (1 - D.weight a) * pivotA)) := by
    calc (1 - maxWeight) * rowAbs ^ 2
        ≤ (1 - maxWeight) * (((selectedᶜ.erase a).card : ℝ) * energy) :=
          mul_le_mul_of_nonneg_left hcs hcapPos.le
      _ = ((selectedᶜ.erase a).card : ℝ) * ((1 - maxWeight) * energy) := by ring
      _ ≤ ((selectedᶜ.erase a).card : ℝ)
            * (pivotA * (1 - (1 - D.weight a) * pivotA)) :=
          mul_le_mul_of_nonneg_left htransfer hcardNonneg
  have hsq : rowAbs ^ 2 < (1 - pivotA) ^ 2 := by
    have := hbudget a ha
    nlinarith [hchain, hcapPos]
  nlinarith [hsq, hrowNonneg, hdefect]

/-! ## The quarter-cap cell

At omitted count three and weight cap `q` the budget reads
`2 π (1 - (1 - q) π) < (1 - q) (1 - π) ^ 2`.  At `q = 1 / 4` that clears to
`0 < 3 - 14 π + 9 π ^ 2`, and the exact factorization

  `3 - 14 π + 9 π ^ 2 = 1 / 16 + 9 (1 / 4 - π) (47 / 36 - π)`

shows the threshold `1 / 4` holds with `1 / 16` to spare.
-/

/-- **THE QUARTER-CAP CARD-THREE CELL.**  Every weight at most one quarter,
three omitted labels, every omitted pivot at most one quarter: the selection
dominates.  No line pattern, no blind spot, no candidate list.

The cap is satisfiable at every size four and up, and at size six it is well
above the pigeonhole floor `1 / 6`. -/
theorem posDef_subsetSum_of_quarterPivotQuarter (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (huniv : (subsetSum D Finset.univ - 1).PosDef)
    (hcap : ∀ b, D.weight b ≤ 1 / 4)
    (selected : Finset (Fin m)) (hcard : selectedᶜ.card = 3)
    (hpivot : ∀ a ∈ selectedᶜ, pivot D Finset.univ a ≤ 1 / 4) :
    (subsetSum D selected - 1).PosDef := by
  classical
  refine posDef_subsetSum_of_pivotBudget D hm huniv (1 / 4) hcap (by norm_num) selected
    (fun a ha => lt_of_le_of_lt (hpivot a ha) (by norm_num)) fun a ha => ?_
  have hcardErase : (selectedᶜ.erase a).card = 2 := by
    rw [Finset.card_erase_of_mem ha, hcard]
  rw [hcardErase]
  have hnn : 0 ≤ pivot D Finset.univ a := pivot_nonneg D Finset.univ huniv a
  have hle : pivot D Finset.univ a ≤ 1 / 4 := hpivot a ha
  have hweight : D.weight a ≤ 1 / 4 := hcap a
  have hweightPos : 0 < D.weight a := D.weight_pos a
  have hfar : (0 : ℝ) ≤ 47 / 36 - pivot D Finset.univ a := by linarith
  push_cast
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) hfar,
    mul_nonneg (mul_nonneg hnn hnn) hweightPos.le,
    mul_nonneg hnn hnn, sq_nonneg (pivot D Finset.univ a)]

/-- **The consumable weak form of the quarter-cap cell.** -/
theorem dominates_of_quarterPivotQuarter (D : WeightedDesign m 3) (hm : 2 ≤ m)
    (huniv : (subsetSum D Finset.univ - 1).PosDef)
    (hcap : ∀ b, D.weight b ≤ 1 / 4)
    (selected : Finset (Fin m)) (hcard : selectedᶜ.card = 3)
    (hpivot : ∀ a ∈ selectedᶜ, pivot D Finset.univ a ≤ 1 / 4) :
    Dominates D selected :=
  (posDef_subsetSum_of_quarterPivotQuarter D hm huniv hcap selected hcard
    hpivot).posSemidef

end Gtz
