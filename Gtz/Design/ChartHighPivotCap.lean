import Gtz.Design.DeflatedPairCriterion
import Gtz.Design.KFourDescentLadder
import Gtz.Wave.ThreeLinesPivotThirdWiring

/-!
# The high-pivot cap at a chart point

A label is HIGH at a chart point when its full-selection pivot is one or more.
This file bounds how many labels can be high, and reads off what that costs the
labels which are not.

The deficiency budget `∑ (1 - weight) * fullPivot = 3` is the whole engine.  A
high label spends at least its own deficiency `1 - weight`, the weights are a
probability vector, and three is a small number.

The design-level analogue `card_le_rank_of_forall_pivot_univ_ge_one`
(Gtz/Design/ComplementLeverageLaw.lean) is landed and is NOT reusable here: it
quantifies over `WeightedDesign`, which carries Parseval and ties mass to
weight, while a `DirectionChartPoint` carries neither.  The proof below runs on
the chart budget alone.
-/

namespace Gtz

open Finset

variable {size : ℕ}

section ChartCap

variable (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)

/-- The labels whose full-selection pivot reaches one. -/
noncomputable def chartHighPivotLabels : Finset (Fin 6) :=
  Finset.univ.filter fun label => 1 ≤ fullPivot direction point.mass point.weight label

theorem mem_chartHighPivotLabels_iff (label : Fin 6) :
    label ∈ chartHighPivotLabels direction point ↔
      1 ≤ fullPivot direction point.mass point.weight label := by
  simp [chartHighPivotLabels]

/-- Each chart deficiency is positive. -/
theorem chartDeficiency_pos (label : Fin 6) : 0 < 1 - point.weight label :=
  sub_pos.mpr (chartPoint_weight_lt_one point label)

/-- The boost of a chart point is nonnegative, so the pivot is. -/
theorem chartBoost_nonneg (label : Fin 6) :
    0 ≤ point.mass label / point.weight label :=
  le_of_lt (div_pos (point.mass_pos label) (point.weight_pos label))

theorem chartFullPivot_nonneg
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef)
    (label : Fin 6) :
    0 ≤ fullPivot direction point.mass point.weight label :=
  fullPivot_nonneg_of_boost direction point.mass point.weight huniv label
    (chartBoost_nonneg point label)

/-- Every deficiency-weighted pivot term is nonnegative. -/
theorem chartDeficiencyTerm_nonneg
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef)
    (label : Fin 6) :
    0 ≤ (1 - point.weight label) * fullPivot direction point.mass point.weight label :=
  mul_nonneg (le_of_lt (chartDeficiency_pos point label))
    (chartFullPivot_nonneg direction point huniv label)

/-- **The budget spent by a set of labels.**  Dropping the labels outside a set
only lowers the deficiency-weighted pivot sum, which the whole budget pins at
three. -/
theorem sum_subset_deficiency_mul_fullPivot_le_three
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef)
    (labels : Finset (Fin 6)) :
    ∑ c ∈ labels, (1 - point.weight c) * fullPivot direction point.mass point.weight c ≤ 3 := by
  rw [← sum_deficiency_mul_fullPivot_eq_three direction point huniv]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ labels)
    fun c _ _ => chartDeficiencyTerm_nonneg direction point huniv c

/-- **A high label spends its own deficiency.**  On the high set the budget term
is at least `1 - weight`. -/
theorem sum_high_deficiency_le
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef)
    (labels : Finset (Fin 6))
    (hhigh : ∀ c ∈ labels, 1 ≤ fullPivot direction point.mass point.weight c) :
    ∑ c ∈ labels, (1 - point.weight c) ≤ 3 := by
  refine le_trans ?_ (sum_subset_deficiency_mul_fullPivot_le_three direction point huniv labels)
  refine Finset.sum_le_sum fun c hc => ?_
  have hd : 0 < 1 - point.weight c := chartDeficiency_pos point c
  have := hhigh c hc
  nlinarith [hd, this]

/-- The weight of any set is at most one. -/
theorem sum_weight_le_one (labels : Finset (Fin 6)) :
    ∑ c ∈ labels, point.weight c ≤ 1 := by
  rw [← point.weight_sum_one]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ labels)
    fun c _ _ => le_of_lt (point.weight_pos c)

/-- The weight of a proper set is strictly less than one. -/
theorem sum_weight_lt_one_of_ne_univ (labels : Finset (Fin 6))
    (hne : labels ≠ Finset.univ) :
    ∑ c ∈ labels, point.weight c < 1 := by
  obtain ⟨missing, hmissing⟩ : ∃ x, x ∉ labels := by
    by_contra hall
    push Not at hall
    exact hne (Finset.eq_univ_of_forall hall)
  rw [← point.weight_sum_one]
  refine Finset.sum_lt_sum_of_subset (Finset.subset_univ labels) (Finset.mem_univ missing)
    hmissing (point.weight_pos missing) ?_
  exact fun c _ _ => le_of_lt (point.weight_pos c)

/-- **THE CAP.  At most three labels of a chart point carry pivot one or more.**

The deficiency budget is three.  A set of `n` high labels spends at least
`n - (its weight)`, and its weight never reaches one unless it is everything.
So `n - 1 ≤ 3` outright, and the value four is excluded because a four-element
set leaves two labels of positive weight outside it. -/
theorem card_chartHighPivotLabels_le_three
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef) :
    (chartHighPivotLabels direction point).card ≤ 3 := by
  set H := chartHighPivotLabels direction point with hHdef
  have hhigh : ∀ c ∈ H, 1 ≤ fullPivot direction point.mass point.weight c := by
    intro c hc
    exact (mem_chartHighPivotLabels_iff direction point c).mp hc
  have hbudget : ∑ c ∈ H, (1 - point.weight c) ≤ 3 :=
    sum_high_deficiency_le direction point huniv H hhigh
  have hsplit : ∑ c ∈ H, (1 - point.weight c)
      = (H.card : ℝ) - ∑ c ∈ H, point.weight c := by
    rw [Finset.sum_sub_distrib]
    simp
  by_contra hcontra
  push Not at hcontra
  have hfour : 4 ≤ H.card := hcontra
  have hne : H ≠ Finset.univ := by
    intro hall
    have : ∑ c ∈ H, (1 - point.weight c) = 6 - 1 := by
      rw [hsplit, hall]
      simp [point.weight_sum_one]
    rw [this] at hbudget
    norm_num at hbudget
  have hlt : ∑ c ∈ H, point.weight c < 1 := sum_weight_lt_one_of_ne_univ point H hne
  rw [hsplit] at hbudget
  have : (4 : ℝ) ≤ (H.card : ℝ) := by exact_mod_cast hfour
  linarith

/-- **The exclusion, in positive form.**  A positive definite selection contains
every high label.  This consumes the landed
`fullPivot_lt_one_of_posDef_compl` and states its contrapositive at the chart. -/
theorem chartHigh_subset_of_posDef_compl
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef)
    (omitted : Finset (Fin 6))
    (hcompl : (directionChartGap direction point.mass point.weight
      (Finset.univ \ omitted)).PosDef) :
    ∀ c ∈ omitted, c ∉ chartHighPivotLabels direction point := by
  intro c hc hmem
  have hlt : fullPivot direction point.mass point.weight c < 1 :=
    fullPivot_lt_one_of_posDef_compl direction point.mass point.weight omitted
      (fun label _ => div_pos (point.mass_pos label) (point.weight_pos label))
      huniv hcompl hc
  have hge : 1 ≤ fullPivot direction point.mass point.weight c :=
    (mem_chartHighPivotLabels_iff direction point c).mp hmem
  linarith

/-- **Every positive definite selection contains every high label.**  The
omitted set of a positive definite selection is high-free, and the complement of
the complement is the selection itself. -/
theorem chartHigh_subset_of_posDef
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef)
    (selected : Finset (Fin 6))
    (hpos : (directionChartGap direction point.mass point.weight selected).PosDef) :
    chartHighPivotLabels direction point ⊆ selected := by
  intro c hc
  by_contra hnot
  have hmem : c ∈ Finset.univ \ selected := by
    simp [Finset.mem_sdiff, hnot]
  have hback : Finset.univ \ (Finset.univ \ selected) = selected := by
    rw [Finset.sdiff_sdiff_self_left, Finset.univ_inter]
  have hcompl : (directionChartGap direction point.mass point.weight
      (Finset.univ \ (Finset.univ \ selected))).PosDef := by
    rw [hback]; exact hpos
  exact chartHigh_subset_of_posDef_compl direction point huniv (Finset.univ \ selected)
    hcompl c hmem hc

/-- **A selection of card three exists only when at most three labels are high.**
The cap and the containment together: a positive definite card-three selection
carries the whole high set inside it. -/
theorem card_chartHigh_le_card_of_posDef
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef)
    (selected : Finset (Fin 6))
    (hpos : (directionChartGap direction point.mass point.weight selected).PosDef) :
    (chartHighPivotLabels direction point).card ≤ selected.card :=
  Finset.card_le_card (chartHigh_subset_of_posDef direction point huniv selected hpos)

/-- **The low-label budget.**  Whatever the high labels spend, the rest of the
budget is what remains, and the high labels spend at least their own count minus
their weight. -/
theorem sum_low_deficiency_mul_fullPivot_le
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef) :
    ∑ c ∈ Finset.univ \ chartHighPivotLabels direction point,
        (1 - point.weight c) * fullPivot direction point.mass point.weight c
      ≤ 3 - ((chartHighPivotLabels direction point).card : ℝ)
          + ∑ c ∈ chartHighPivotLabels direction point, point.weight c := by
  set H := chartHighPivotLabels direction point with hHdef
  have hhigh : ∀ c ∈ H, 1 ≤ fullPivot direction point.mass point.weight c := by
    intro c hc
    exact (mem_chartHighPivotLabels_iff direction point c).mp hc
  have htotal : ∑ c, (1 - point.weight c) * fullPivot direction point.mass point.weight c = 3 :=
    sum_deficiency_mul_fullPivot_eq_three direction point huniv
  have hsplit : ∑ c ∈ H, (1 - point.weight c) * fullPivot direction point.mass point.weight c
      + ∑ c ∈ Finset.univ \ H, (1 - point.weight c)
          * fullPivot direction point.mass point.weight c = 3 := by
    rw [← htotal, add_comm]
    exact Finset.sum_sdiff (Finset.subset_univ H)
  have hhighspend : (H.card : ℝ) - ∑ c ∈ H, point.weight c
      ≤ ∑ c ∈ H, (1 - point.weight c) * fullPivot direction point.mass point.weight c := by
    have hform : ∑ c ∈ H, (1 - point.weight c)
        = (H.card : ℝ) - ∑ c ∈ H, point.weight c := by
      rw [Finset.sum_sub_distrib]; simp
    rw [← hform]
    refine Finset.sum_le_sum fun c hc => ?_
    have hd : 0 < 1 - point.weight c := chartDeficiency_pos point c
    have := hhigh c hc
    nlinarith [hd, this]
  linarith

end ChartCap

end Gtz
