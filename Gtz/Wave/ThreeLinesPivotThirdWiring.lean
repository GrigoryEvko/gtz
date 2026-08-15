/-
# The pivot-third cell of the three-lines chart

The pivot-third dominance law is a certificate cell, and this file spends it
against A2.  The A2 residual is narrowed by one more region: the chart points
that carry three labels of full pivot below one third.

The cell is not a restatement of the four cells already spent.  The budget cells
are allocated Cauchy--Schwarz inequalities at two FIXED triples, the reading
cover asks for one triple that carries a maximal reading at EVERY probe, and the
seven orbit trace cells are one-inequality traces.  The pivot-third cell reads
the resolvent instead, and it selects its own triple.

The file also records what the cell costs.  The deficiency-weighted pivot of a
chart point is exactly three, so a firing cell forces more than two of that
three onto the selected triple.  The corpus already proves that three labels
always carry pivot below one, so the region this cell leaves open is precisely
the band where the three low pivots sit between one third and one.
-/
import Gtz.Design.PivotThirdDominance
import Gtz.Wave.ThreeLinesMovedOrbitTraceWiring

namespace Gtz

open Finset Matrix

/-! ## 1. The deficiency-weighted pivot of a chart point -/

/-- **The deficiency-weighted pivot is exactly three.**  The chart leverage of a
label is its deficiency times its pivot, and the leverages sum to the rank. -/
theorem sum_deficiency_mul_fullPivot_eq_three {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (point : DirectionChartPoint size)
    (huniv : (directionChartGap direction point.mass point.weight Finset.univ).PosDef) :
    ∑ c, (1 - point.weight c) * fullPivot direction point.mass point.weight c = 3 := by
  rw [← sum_chartLeverage_eq_three direction point.mass point.weight huniv]
  refine Finset.sum_congr rfl fun c _ => ?_
  exact (chartLeverage_eq_one_sub_weight_mul_fullPivot direction point.mass point.weight
    (ne_of_gt (point.weight_pos c))).symm

/-- Every deficiency of a chart point is at most one. -/
theorem deficiency_le_one {size : ℕ} (point : DirectionChartPoint size) (c : Fin size) :
    1 - point.weight c ≤ 1 := by
  have := point.weight_pos c
  linarith

/-- Every deficiency of a chart point is nonnegative once the weights are a
probability vector and the label count is at least two. -/
theorem deficiency_nonneg_of_sum_one {size : ℕ} (point : DirectionChartPoint size)
    (c : Fin size) (hother : ∃ d, d ≠ c) :
    0 ≤ 1 - point.weight c := by
  classical
  obtain ⟨d, hd⟩ := hother
  have hsplit : point.weight c + ∑ e ∈ Finset.univ.erase c, point.weight e = 1 := by
    rw [Finset.add_sum_erase _ _ (Finset.mem_univ c)]
    exact point.weight_sum_one
  have hrest : 0 ≤ ∑ e ∈ Finset.univ.erase c, point.weight e :=
    Finset.sum_nonneg fun e _ => (point.weight_pos e).le
  linarith

/-! ## 2. The cell -/

/-- **The pivot-third cell of the three-lines chart.**  A card-three selection
whose three omitted labels all carry a full pivot below one third. -/
def ThreeLinesPivotThirdCellFires (slide : ℝ) (point : DirectionChartPoint 6) : Prop :=
  ∃ selected : Finset (Fin 6), selected.card = 3 ∧
    ∀ a ∈ selectedᶜ,
      fullPivot (threeLinesDirection slide) point.mass point.weight a < 1 / 3

/-- A card-three selection of six labels omits exactly three. -/
theorem card_compl_of_card_three {selected : Finset (Fin 6)} (hcard : selected.card = 3) :
    selectedᶜ.card = 3 := by
  have hc := Finset.card_compl selected
  rw [hcard] at hc
  simpa using hc

/-- **The cell supplies its strict triple.**  The pivot-third dominance law fires
at the three-lines chart, whose full-selection gap is unconditionally positive
definite. -/
theorem exists_posDef_threeLines_of_pivotThirdCellFires (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesPivotThirdCellFires slide point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef := by
  obtain ⟨selected, hcard, hpivot⟩ := hcell
  refine ⟨selected, hcard, ?_⟩
  exact posDef_directionChartGap_of_pivotThird (threeLinesDirection slide)
    point.mass point.weight selected
    (fun label => div_pos (point.mass_pos label) (point.weight_pos label))
    (posDef_directionChartGap_univ_threeLines slide point)
    (card_compl_of_card_three hcard) hpivot

/-! ## 3. What the cell costs

A firing cell is not free.  The deficiency-weighted pivot of every chart point is
exactly three, and three labels below one third contribute less than one of it,
so the selected triple must carry more than two.
-/

/-- **The concentration law of the pivot-third cell.**  When the cell fires at a
selection, that selection carries more than two of the three units of
deficiency-weighted pivot. -/
theorem two_lt_sum_selected_deficiency_mul_pivot (slide : ℝ)
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hcard : selected.card = 3)
    (hpivot : ∀ a ∈ selectedᶜ,
      fullPivot (threeLinesDirection slide) point.mass point.weight a < 1 / 3) :
    2 < ∑ c ∈ selected,
      (1 - point.weight c) * fullPivot (threeLinesDirection slide) point.mass point.weight c := by
  classical
  set direction := threeLinesDirection slide with hdir
  have huniv := posDef_directionChartGap_univ_threeLines slide point
  set piv : Fin 6 → ℝ := fun c => fullPivot direction point.mass point.weight c with hpiv
  have hother : ∀ c : Fin 6, ∃ d, d ≠ c := fun c => exists_ne c
  have hdefNonneg : ∀ c : Fin 6, 0 ≤ 1 - point.weight c := fun c =>
    deficiency_nonneg_of_sum_one point c (hother c)
  have hpivNonneg : ∀ c : Fin 6, 0 ≤ piv c := fun c =>
    fullPivot_nonneg_of_boost direction point.mass point.weight huniv c
      (div_pos (point.mass_pos c) (point.weight_pos c)).le
  have htotal : ∑ c, (1 - point.weight c) * piv c = 3 :=
    sum_deficiency_mul_fullPivot_eq_three direction point huniv
  have hsplit : ∑ c ∈ selected, (1 - point.weight c) * piv c
      + ∑ c ∈ selectedᶜ, (1 - point.weight c) * piv c = 3 := by
    rw [← htotal]
    exact (Finset.sum_add_sum_compl selected _)
  -- The omitted contribution is under one.
  have homit : ∑ c ∈ selectedᶜ, (1 - point.weight c) * piv c < 1 := by
    have hterm : ∀ c ∈ selectedᶜ, (1 - point.weight c) * piv c ≤ 1 * (1 / 3 : ℝ) := by
      intro c hc
      refine mul_le_mul (deficiency_le_one point c) (hpivot c hc).le (hpivNonneg c) ?_
      norm_num
    have hbound := Finset.sum_le_sum hterm
    rw [Finset.sum_const, card_compl_of_card_three hcard] at hbound
    have hstrict : ∃ c ∈ selectedᶜ, (1 - point.weight c) * piv c < 1 * (1 / 3 : ℝ) := by
      have hne : selectedᶜ.Nonempty := by
        rw [← Finset.card_pos, card_compl_of_card_three hcard]
        norm_num
      obtain ⟨c, hc⟩ := hne
      refine ⟨c, hc, ?_⟩
      have hlt := hpivot c hc
      have hdc := hdefNonneg c
      have hpc := hpivNonneg c
      nlinarith [hlt, hdc, hpc, deficiency_le_one point c]
    obtain ⟨c, hcmem, hclt⟩ := hstrict
    have hsum := Finset.sum_lt_sum (fun d hd => hterm d hd) ⟨c, hcmem, hclt⟩
    rw [Finset.sum_const, card_compl_of_card_three hcard] at hsum
    simp only [nsmul_eq_mul] at hsum
    push_cast at hsum
    linarith [hsum]
  linarith [hsplit, homit]

/-! ## 4. The narrowed A2 residual -/

/-- **The A2 residual with the pivot-third cell also spent.** -/
def ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitPivotThirdBlindOffLines :
    Prop :=
  ∀ slide : ℝ, ∀ hadmissible : IsAdmissibleThreeLinesParameter slide, 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      ¬ ThreeLinesBudgetCellFires slide point →
      ¬ ThreeLinesReadingCoverCellFires slide point →
      ¬ ThreeLinesSevenOrbitTraceAtlasCellFires slide hadmissible.1 point →
      ¬ ThreeLinesPivotThirdCellFires slide point →
      (∃ selected : Finset (Fin 6), ThreeLinesOffLinesWeakTriple slide point selected) →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef

/-- Dropping the extra blindness hypothesis is free. -/
theorem pivotThirdBlind_of_sevenOrbitBlind
    (hblind :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitPivotThirdBlindOffLines :=
  fun slide hadmissible hfundamental point hbudget hreading horbit _ hweak =>
    hblind slide hadmissible hfundamental point hbudget hreading horbit hweak

/-- **Spending the cell.**  The narrowed residual reconstructs the preceding one,
by dispatching every point at which the pivot-third cell fires. -/
theorem sevenOrbitBlind_of_pivotThirdBlind
    (hblind :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitPivotThirdBlindOffLines) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines := by
  intro slide hadmissible hfundamental point hbudget hreading horbit hweak
  rcases Classical.em (ThreeLinesPivotThirdCellFires slide point) with hcell | hcell
  · exact exists_posDef_threeLines_of_pivotThirdCellFires slide point hcell
  · exact hblind slide hadmissible hfundamental point hbudget hreading horbit hcell hweak

/-- The narrowed residual is equivalent to the preceding one. -/
theorem chartTieFreeThreeLines_pivotThirdBlind_iff_sevenOrbitBlind :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitPivotThirdBlindOffLines ↔
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines :=
  ⟨sevenOrbitBlind_of_pivotThirdBlind, pivotThirdBlind_of_sevenOrbitBlind⟩

/-- **The narrowed residual is exactly public A2.**  Spending one more cell is a
formula sharpening, not a strengthening. -/
theorem chartTieFreeThreeLines_pivotThirdBlind_iff :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitPivotThirdBlindOffLines ↔
      ChartTieFreeThreeLinesFundamentalDomain :=
  chartTieFreeThreeLines_pivotThirdBlind_iff_sevenOrbitBlind.trans
    chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_iff

/-! ## 5. The band the cell leaves open

The corpus proves that three labels always carry pivot below one.  The cell needs
three labels below one third.  The open region is therefore the band where the
three lowest pivots sit at or above one third.
-/

/-- **The blind region of the pivot-third cell, stated exactly.**  If the cell
does not fire, then every card-three selection has an omitted label whose pivot
reaches one third. -/
theorem exists_pivot_ge_third_of_not_pivotThirdCellFires (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hcell : ¬ ThreeLinesPivotThirdCellFires slide point)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    ∃ a ∈ selectedᶜ,
      1 / 3 ≤ fullPivot (threeLinesDirection slide) point.mass point.weight a := by
  by_contra hcon
  refine hcell ⟨selected, hcard, fun a ha => ?_⟩
  by_contra hge
  exact hcon ⟨a, ha, le_of_not_gt hge⟩

/-- **The band, from the corpus side.**  Three labels always carry pivot below
one, so at a blind point three labels carry pivot in the half-open band from one
third to one. -/
theorem three_le_card_fullPivot_lt_one_threeLines (slide : ℝ)
    (point : DirectionChartPoint 6) :
    3 ≤ (Finset.univ.filter
      (fun i => fullPivot (threeLinesDirection slide) point.mass point.weight i < 1)).card :=
  three_le_card_fullPivot_lt_one (threeLinesDirection slide) point
    (posDef_directionChartGap_univ_threeLines slide point)

end Gtz
