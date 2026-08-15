import Gtz.Design.CardFourStallEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The type split of a stalled four-edge selection

A STALL is a positive definite selection whose every label carries ladder pivot
at least one.  This module gives the stall its two structural readings and the
entry point of the case tree the card-four statement needs.

* `stall_iff_minimal_posDef` — a stall is exactly a MINIMAL positive definite
  set.  Erasing one label already tests every proper subset, because a positive
  definite subset survives inside any larger selection.
* `exists_outside_pivot_ge_one_of_cardFour_stall` — a stalled four-edge
  selection carries an outside label of pivot at least one.  The unified stall
  law prices the two outside pivots at weighted average one, and a weighted
  average is attained.
* `chartLadderPivot_insert_ge_half_of_cardFour_stall` — that label, once
  inserted, keeps pivot in `[1/2, 1)`.  The five-edge selection built from a
  stall and its priced outside label is therefore positive definite and is not
  stalled at that label.
* `kFourCardFour_matchingCompl_or_triangle` — the type split.  A four-edge
  selection either has a perfect matching for its complement (type A, the
  selection is a four-cycle) or it contains one of the four triangles (type B).
-/

namespace Gtz

open Matrix

/-! ## A stall is a minimal positive definite set -/

/-- A stall refuses every one-label erasure.  This is the erasure equivalence
read through the negation. -/
theorem stall_iff_no_posDef_erase {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (selected : Finset (Fin size))
    (hpd : (directionChartGap direction mass weight selected).PosDef) :
    (∀ label ∈ selected,
        1 ≤ chartLadderPivot direction mass weight selected label)
      ↔ ∀ label ∈ selected,
          ¬ (directionChartGap direction mass weight
            (selected.erase label)).PosDef := by
  constructor
  · intro hstall label hmem hposDef
    have hlt := (posDef_directionChartGap_erase_iff direction mass weight hmass
      hweight selected hmem hpd).mp hposDef
    exact absurd (hstall label hmem) (not_le.mpr hlt)
  · intro hmin label hmem
    by_contra hlt
    push Not at hlt
    exact hmin label hmem
      ((posDef_directionChartGap_erase_iff direction mass weight hmass hweight
        selected hmem hpd).mpr hlt)

/-- **A STALL IS A MINIMAL POSITIVE DEFINITE SET.**  A positive definite
selection is stalled exactly when no proper subset of it is positive definite.

One-label erasures already decide the question: a positive definite proper
subset sits inside the erasure at any label it omits, and positive definiteness
travels up. -/
theorem stall_iff_minimal_posDef {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (selected : Finset (Fin size))
    (hpd : (directionChartGap direction mass weight selected).PosDef) :
    (∀ label ∈ selected,
        1 ≤ chartLadderPivot direction mass weight selected label)
      ↔ ∀ smaller ⊂ selected,
          ¬ (directionChartGap direction mass weight smaller).PosDef := by
  rw [stall_iff_no_posDef_erase direction mass weight hmass hweight selected hpd]
  constructor
  · intro hmin smaller hsub hposDef
    obtain ⟨label, hmemSel, hnotMem⟩ := Finset.exists_of_ssubset hsub
    refine hmin label hmemSel ?_
    refine posDef_directionChartGap_of_subset direction mass weight hmass hweight
      ?_ hposDef
    intro x hx
    exact Finset.mem_erase.mpr ⟨fun hxlabel => hnotMem (hxlabel ▸ hx),
      hsub.subset hx⟩
  · intro hmin label hmem
    exact hmin _ (Finset.erase_ssubset hmem)

/-! ## The priced outside label of a four-edge stall -/

/-- **THE PRICED OUTSIDE LABEL.**  A stalled four-edge selection carries an
outside label whose pivot is at least one.

The unified stall law prices the two outside pivots at weighted average one, and
a weighted average is attained by one of its terms. -/
theorem exists_outside_pivot_ge_one_of_cardFour_stall
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (hcard : selected.card = 4)
    (hpd : (directionChartGap direction point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot direction point.mass point.weight selected label) :
    ∃ outside ∈ selectedᶜ,
      1 ≤ chartLadderPivot direction point.mass point.weight selected outside := by
  by_contra hall
  push Not at hall
  have hprice := card_four_stall direction point selected hcard hpd hstall
  have hne : selectedᶜ.Nonempty := by
    rw [← Finset.card_pos, Finset.card_compl, hcard]
    simp
  have hneg : ∑ label ∈ selectedᶜ, point.weight label
      * (chartLadderPivot direction point.mass point.weight selected label - 1)
      < ∑ _label ∈ selectedᶜ, (0 : ℝ) := by
    refine Finset.sum_lt_sum_of_nonempty hne fun label hmem => ?_
    have hlt := hall label hmem
    have hw := point.weight_pos label
    nlinarith
  rw [Finset.sum_const_zero] at hneg
  linarith

/-- The five-edge selection built from a stall and any outside label is positive
definite. -/
theorem posDef_insert_of_posDef (direction : Fin 6 → (Fin 3 → ℝ))
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hpd : (directionChartGap direction point.mass point.weight
      selected).PosDef) (outside : Fin 6) :
    (directionChartGap direction point.mass point.weight
      (insert outside selected)).PosDef :=
  posDef_directionChartGap_of_subset direction point.mass point.weight
    point.mass_pos point.weight_pos (Finset.subset_insert _ _) hpd

/-- **THE PRICED LABEL AFTER INSERTION.**  The priced outside label of a stalled
four-edge selection carries, after insertion, a pivot in `[1/2, 1)`.

The five-edge selection is therefore positive definite and is not stalled at that
label, so the descent from it returns exactly the four-edge stall. -/
theorem chartLadderPivot_insert_ge_half_of_cardFour_stall
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (hcard : selected.card = 4)
    (hpd : (directionChartGap direction point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ selected,
      1 ≤ chartLadderPivot direction point.mass point.weight selected label) :
    ∃ outside ∈ selectedᶜ,
      1 / 2 ≤ chartLadderPivot direction point.mass point.weight
          (insert outside selected) outside
        ∧ chartLadderPivot direction point.mass point.weight
          (insert outside selected) outside < 1 := by
  obtain ⟨outside, hmem, hge⟩ := exists_outside_pivot_ge_one_of_cardFour_stall
    direction point selected hcard hpd hstall
  refine ⟨outside, hmem, ?_⟩
  exact chartLadderPivot_insert_self_mem_Ico direction point.mass point.weight
    point.mass_pos point.weight_pos selected (Finset.mem_compl.mp hmem) hpd hge

/-! ## The type split -/

/-- **THE TYPE SPLIT.**  A four-edge selection of `K4` either has a perfect
matching for its complement — type A, the selection is a four-cycle and each of
its three-subsets is a spanning tree — or it contains one of the four triangles,
which is type B. -/
theorem kFourCardFour_matchingCompl_or_triangle (selected : Finset (Fin 6))
    (hcard : selected.card = 4) :
    (selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3})
      ∨ ({0, 1, 2} ⊆ selected ∨ {0, 3, 4} ⊆ selected ∨ {1, 3, 5} ⊆ selected
        ∨ {2, 4, 5} ⊆ selected) := by
  revert hcard
  revert selected
  decide

end Gtz
