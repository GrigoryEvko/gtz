/-
# The design-form variational principle: the interior chart minimiser IS a design

The two halves shipped separately and nobody composed them.
`Gtz.exists_interior_minimiser_of_not_gtzWeighted`
(`Gtz/Reduction/ChartAttainment.lean`) produces, from a failure of the weighted
target and the two smaller chart rungs, a CHART POINT that minimises the chart
objective over the whole closed domain, has strictly negative value, admits no
dominating selection, and has all weights strictly positive.
`Gtz.chartPointHasDesign` (`Gtz/Reduction/ChartPointFactorisation.lean`)
factorises every positive-weight chart point through a weighted design.  The
paper's Theorem `thm:variational` (`sections/07-compactness.tex`) concludes one
step further than either: the minimiser "is the chart point of a design", the
design admits no dominating subset IN THE DESIGN SENSE, and it minimises the
objective over all designs.  This file is that one step, taken in kernel.

Nothing here is new mathematics: it is the composition of three shipped
theorems (`exists_interior_minimiser_of_not_gtzWeighted`,
`chartPointHasDesign`, `dominates_iff_chartDominates`) plus, at `(6, 3)`, the
discharge of both chart-rung hypotheses through
`Gtz.chartGtz_iff_gtzWeighted` and the shipped `Gtz.gtzWeighted_of_le_five` --
so the `(6, 3)` instance carries NO hypothesis beyond the failure itself.

WHAT THIS DOES NOT BUY: no cell is closed, no stationarity is produced, and the
minimality is of the CHART objective; the design objective's minimisers may
differ (the recorded objective mismatch stands).
-/
import Mathlib
import Gtz.Reduction.ChartAttainment
import Gtz.Reduction.ChartPointFactorisation

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

variable {size rank : ℕ}

/-- **The design-form interior minimiser.**  Given the two smaller chart rungs,
a failure of `Gtz.GtzWeighted (size + 1) (rank + 1)` is realised at a WEIGHTED
DESIGN whose chart point minimises the chart objective over the entire closed
chart domain, carries strictly negative objective value, and admits no
dominating `(rank + 1)`-subset in the design sense.  This is the paper's
Theorem `thm:variational` stated at the design, not merely at the chart
point. -/
theorem exists_design_minimiser_of_not_gtzWeighted
    (hsameRank : ChartGtz size (rank + 1)) (hdropRank : ChartGtz size rank)
    (hfail : ¬ GtzWeighted (size + 1) (rank + 1)) :
    ∃ design : WeightedDesign (size + 1) (rank + 1),
      (∀ point : ChartPoint (size + 1) (rank + 1),
        chartObjective (chartPointOfDesign design) ≤ chartObjective point)
      ∧ chartObjective (chartPointOfDesign design) < 0
      ∧ ∀ selected : Finset (Fin (size + 1)), selected.card = rank + 1 →
          ¬ Dominates design selected := by
  obtain ⟨minimiser, hminimal, hnegative, hnoSelection, hpositive⟩ :=
    exists_interior_minimiser_of_not_gtzWeighted hsameRank hdropRank hfail
  obtain ⟨design, hdesignChart⟩ :=
    chartPointHasDesign (size + 1) (rank + 1) minimiser hpositive
  refine ⟨design, ?_, ?_, ?_⟩
  · intro point
    rw [hdesignChart]
    exact hminimal point
  · rw [hdesignChart]
    exact hnegative
  · intro selected hcard hdominates
    refine hnoSelection selected hcard ?_
    rw [← hdesignChart]
    exact (dominates_iff_chartDominates design selected hcard).mp hdominates

/-- The design-form minimiser minimises, in particular, over all designs: the
chart objective at its chart point is at most the chart objective at every
other design's chart point.  A specialisation of the full-domain minimality,
recorded because the paper's statement quantifies over designs. -/
theorem exists_design_minimiser_over_designs_of_not_gtzWeighted
    (hsameRank : ChartGtz size (rank + 1)) (hdropRank : ChartGtz size rank)
    (hfail : ¬ GtzWeighted (size + 1) (rank + 1)) :
    ∃ design : WeightedDesign (size + 1) (rank + 1),
      (∀ other : WeightedDesign (size + 1) (rank + 1),
        chartObjective (chartPointOfDesign design)
          ≤ chartObjective (chartPointOfDesign other))
      ∧ chartObjective (chartPointOfDesign design) < 0
      ∧ ∀ selected : Finset (Fin (size + 1)), selected.card = rank + 1 →
          ¬ Dominates design selected := by
  obtain ⟨design, hminimal, hnegative, hnoSelection⟩ :=
    exists_design_minimiser_of_not_gtzWeighted hsameRank hdropRank hfail
  exact ⟨design, fun other => hminimal (chartPointOfDesign other), hnegative,
    hnoSelection⟩

/-- The rung `Gtz.ChartGtz 5 3`, discharged: `m = 5` is inside the decided
range, and the closed chart statement is the weighted statement. -/
theorem chartGtz_five_three : ChartGtz 5 3 :=
  (chartGtz_iff_gtzWeighted 5 3).mpr
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num))

/-- The rung `Gtz.ChartGtz 5 2`, discharged the same way. -/
theorem chartGtz_five_two : ChartGtz 5 2 :=
  (chartGtz_iff_gtzWeighted 5 2).mpr
    (gtzWeighted_of_le_five 5 2 (by norm_num) (by norm_num))

/-- **The `(6, 3)` design-form variational principle, hypothesis-free.**  If
`Gtz.GtzWeighted 6 3` fails, then some weighted `(6, 3)` design minimises the
chart objective over the whole closed chart domain, with strictly negative
value and no dominating triple.  Both chart rungs of the generic statement are
theorems at this cell, so nothing conditions this beyond the failure itself:
the paper's Theorem `thm:variational` at its entry cell, in kernel, at the
design. -/
theorem exists_design_minimiser_of_not_gtzWeighted_sixThree
    (hfail : ¬ GtzWeighted 6 3) :
    ∃ design : WeightedDesign 6 3,
      (∀ point : ChartPoint 6 3,
        chartObjective (chartPointOfDesign design) ≤ chartObjective point)
      ∧ chartObjective (chartPointOfDesign design) < 0
      ∧ ∀ selected : Finset (Fin 6), selected.card = 3 →
          ¬ Dominates design selected :=
  exists_design_minimiser_of_not_gtzWeighted
    (size := 5) (rank := 2) chartGtz_five_three chartGtz_five_two hfail

end Gtz
