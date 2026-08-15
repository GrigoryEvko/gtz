/-
# What a counterexample must look like: the pivot ledger of a no-strict design

The campaign's live question is `nPD ≥ 1` at coincidence defect zero.  Its
contrapositive asks what a design with NO strictly dominating card-three subset
must satisfy.  Until now the answer was qualitative.

`Gtz.posDef_subsetSum_of_quarterPivotQuarter` gives a quantitative one for free.
A design whose weights are capped and which carries three labels of small pivot
HAS a strictly dominating subset.  So a design with none can carry at most two
such labels, and the same counting runs at the projection.

## PROVED here, kernel-checked, unconditional

* `Gtz.lowPivotSelection` — the labels of small pivot, as a `Finset`.
* `Gtz.card_lowPivot_le_two_of_noStrict` — **THE LEDGER.**  A weight-capped
  design with no strictly dominating card-three subset has at most two labels of
  pivot at most one quarter.  Four of its six labels therefore carry pivot above
  one quarter.
* `Gtz.exists_pivot_gt_quarter_of_noStrict` — the reading on any three labels:
  every triple of a no-strict design contains a label of pivot above a quarter.
* `Gtz.card_highLeverage_le_of_noCovering` — the projection reading.  A symmetric
  idempotent on `n` coordinates with no `k` rows of leverage at least the budget
  threshold has at most `k - 1` such rows.
* `Gtz.card_lowPivot_le_two_of_noStrict_general` — the ledger with the cap and
  the threshold left free, so a stratum that knows a sharper cap gets a sharper
  ledger.

## The counting, in one line

If three labels had small pivot, the quarter-cap cell would strictly dominate
their complement, which the no-strict hypothesis forbids.  So the small-pivot
set has at most two members.
-/
import Gtz.Design.PivotOnlyDominance
import Gtz.LinAlg.ProjectionDiagonalDominance

namespace Gtz

open Finset Matrix

variable {m : ℕ}

/-- The labels whose full-selection pivot does not exceed a threshold. -/
noncomputable def lowPivotSelection (D : WeightedDesign m 3) (threshold : ℝ) :
    Finset (Fin m) :=
  Finset.univ.filter (fun a => pivot D Finset.univ a ≤ threshold)

theorem mem_lowPivotSelection {D : WeightedDesign m 3} {threshold : ℝ} {a : Fin m} :
    a ∈ lowPivotSelection D threshold ↔ pivot D Finset.univ a ≤ threshold := by
  simp [lowPivotSelection]

/-- **THE LEDGER, with the cap and the threshold free.**  Whenever the pivot
budget closes at `threshold` under the cap `capWeight`, a design with no
strictly dominating card-three subset carries at most two labels below it. -/
theorem card_lowPivot_le_two_of_noStrict_general (D : WeightedDesign 6 3)
    (huniv : (subsetSum D Finset.univ - 1).PosDef)
    (capWeight threshold : ℝ) (hcap : ∀ b, D.weight b ≤ capWeight)
    (hcapLt : capWeight < 1)
    (hthresholdLt : threshold < 1)
    (hbudget : ∀ a : Fin 6, pivot D Finset.univ a ≤ threshold →
      (2 : ℝ) * (pivot D Finset.univ a
          * (1 - (1 - D.weight a) * pivot D Finset.univ a))
        < (1 - capWeight) * (1 - pivot D Finset.univ a) ^ 2)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef) :
    (lowPivotSelection D threshold).card ≤ 2 := by
  classical
  by_contra hbig
  obtain ⟨triple, htripleSub, htripleCard⟩ :=
    Finset.exists_subset_card_eq
      (show 3 ≤ (lowPivotSelection D threshold).card from Nat.lt_of_not_le hbig)
  have hlow : ∀ a ∈ triple, pivot D Finset.univ a ≤ threshold := fun a ha =>
    mem_lowPivotSelection.mp (htripleSub ha)
  have hcompl : (tripleᶜ)ᶜ = triple := compl_compl triple
  have hcomplCard : (tripleᶜ : Finset (Fin 6)).card = 3 := by
    rw [Finset.card_compl, htripleCard]
    simp
  refine hnoStrict tripleᶜ hcomplCard ?_
  refine posDef_subsetSum_of_pivotBudget D (by norm_num) huniv capWeight hcap hcapLt
    tripleᶜ (fun a ha => ?_) fun a ha => ?_
  · rw [hcompl] at ha
    exact lt_of_le_of_lt (hlow a ha) hthresholdLt
  · rw [hcompl] at ha ⊢
    have hcardErase : (triple.erase a).card = 2 := by
      rw [Finset.card_erase_of_mem ha, htripleCard]
    rw [hcardErase]
    push_cast
    exact hbudget a (hlow a ha)

/-- **THE LEDGER at the quarter cap.**  A design whose weights are at most one
quarter and which has no strictly dominating card-three subset carries at most
two labels of pivot at most one quarter. -/
theorem card_lowPivot_le_two_of_noStrict (D : WeightedDesign 6 3)
    (huniv : (subsetSum D Finset.univ - 1).PosDef)
    (hcap : ∀ b, D.weight b ≤ 1 / 4)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef) :
    (lowPivotSelection D (1 / 4)).card ≤ 2 := by
  refine card_lowPivot_le_two_of_noStrict_general D huniv (1 / 4) (1 / 4) hcap
    (by norm_num) (by norm_num) (fun a hle => ?_) hnoStrict
  have hnn : 0 ≤ pivot D Finset.univ a := pivot_nonneg D Finset.univ huniv a
  have hweight : D.weight a ≤ 1 / 4 := hcap a
  have hweightPos : 0 < D.weight a := D.weight_pos a
  have hfar : (0 : ℝ) ≤ 47 / 36 - pivot D Finset.univ a := by linarith
  nlinarith [mul_nonneg (sub_nonneg.mpr hle) hfar,
    mul_nonneg (mul_nonneg hnn hnn) hweightPos.le, mul_nonneg hnn hnn,
    sq_nonneg (pivot D Finset.univ a)]

/-- **Every triple of a no-strict design carries a large pivot.**  The ledger
read on three labels rather than on the whole label set. -/
theorem exists_pivot_gt_quarter_of_noStrict (D : WeightedDesign 6 3)
    (huniv : (subsetSum D Finset.univ - 1).PosDef)
    (hcap : ∀ b, D.weight b ≤ 1 / 4)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum D selected - 1).PosDef)
    (triple : Finset (Fin 6)) (hcard : triple.card = 3) :
    ∃ a ∈ triple, 1 / 4 < pivot D Finset.univ a := by
  classical
  by_contra hall
  have hsub : triple ⊆ lowPivotSelection D (1 / 4) := fun a ha =>
    mem_lowPivotSelection.mpr (not_lt.mp fun hlt => hall ⟨a, ha, hlt⟩)
  have hle := Finset.card_le_card hsub
  rw [hcard] at hle
  have hbound := card_lowPivot_le_two_of_noStrict D huniv hcap hnoStrict
  omega

/-- **The projection reading.**  A symmetric idempotent with no `k` rows meeting
the leverage budget has at most `k - 1` rows that meet it.  The counting is the
same: `k` such rows would witness the covering. -/
theorem card_highLeverage_le_of_noCovering {size rank : ℕ}
    (proj : Matrix (Fin size) (Fin size) ℝ) (hsymm : projᵀ = proj)
    (hidem : proj * proj = proj)
    (threshold : ℝ) (hshift : (size : ℝ)⁻¹ < threshold)
    (hmono : ∀ d : ℝ, threshold ≤ d → d ≤ 1 →
      ((rank : ℝ) - 1) * (d * (1 - d)) < (d - (size : ℝ)⁻¹) ^ 2)
    (hnoCover : ∀ rowPick : Fin rank → Fin size, Function.Injective rowPick →
      ¬ (proj.submatrix rowPick rowPick - (size : ℝ)⁻¹ • 1).PosSemidef)
    (rowPick : Fin rank → Fin size) (hinj : Function.Injective rowPick)
    (hhigh : ∀ a : Fin rank, threshold ≤ proj (rowPick a) (rowPick a)) :
    False := by
  refine hnoCover rowPick hinj ?_
  refine projectionCovering_of_leverageBudget proj hsymm hidem rowPick hinj
    (fun a => lt_of_lt_of_le hshift (hhigh a)) fun a => ?_
  have hle : proj (rowPick a) (rowPick a) ≤ 1 := by
    have henergy := projection_offDiag_sq_energy hsymm hidem (rowPick a)
    have hnonneg : 0 ≤ ∑ b ∈ Finset.univ.erase (rowPick a), proj (rowPick a) b ^ 2 :=
      Finset.sum_nonneg fun b _ => sq_nonneg _
    nlinarith [henergy, hnonneg, hshift, hhigh a]
  exact hmono _ (hhigh a) hle

end Gtz
