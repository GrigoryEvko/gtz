/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Mathlib
import Gtz.Reduction.StressWalk
import Gtz.Reduction.AllHeavyMinimiser
import Gtz.Reduction.NaimarkLeverage
import Gtz.Reduction.LineCountReduction
import Gtz.Quantitative.SixThreeCruxPropagation

/-!
# What the deleted antecedent buys downstream

`Gtz.gtzWeighted_seven_three_of_six_three` (Gtz/Reduction/StressWalk.lean) made
`(6,3)` and `(7,3)` equivalent, and `Gtz.rank_three_iff_six_three` made either of
them equivalent to the whole of rank three.  `Gtz/Quantitative/SixThreeCruxPropagation.lean`
spent that on the two termini of the exclusion campaign.  This module spends it on
everything else the tree had phrased at `(7,3)`, at a pair of cells, or at a
dichotomy.  Every theorem here is a composition; nothing is re-derived, and the
originals are left exactly as they stand.

## WHAT LANDS

* `Gtz.exists_allHeavy_minimiser_of_not_rank_three_sharp` — the shipped
  `Gtz.exists_allHeavy_minimiser_of_not_rank_three` is a DICHOTOMY, offering a
  minimising counterexample at `(6,3)` OR at `(7,3)`.  It collapses: the `(6,3)`
  branch alone suffices, because the `(7,3)` branch's escape hatch was exactly the
  missing arrow.  A counterexample hunt no longer has two shapes to look for.
* `Gtz.gtzWeighted_six_three_iff_seven_four` — a THIRD cell joins the equivalence
  class.  `Gtz.gtzWeighted_seven_four_of_seven_three` sends rank three up to the
  rank-four Naimark partner at the same size; the spike descent
  `Gtz.gtzWeighted_of_spike` sends `(7,4)` back down to `(6,3)`.  Before the walk
  that loop did not close, and the tree's lowest rank-four entry into rank three
  was `Gtz.gtzWeightedAll_three_of_eight_four`.  It is now `(7,4)`, one size lower,
  and it is an equivalence rather than an implication.
* `Gtz.gtzWeightedAll_three_of_doublyHeavy_six_three` — the doubly-heavy narrowing
  moves from `(7,3)` to `(6,3)`.  `Gtz.gtzWeightedHeavy_six_three_of_doublyHeavy`
  was already in the tree and already at size six; what it lacked was a way to
  reach all of rank three from there, since `Gtz.rank_three_of_heavy_top` starts at
  seven.  `Gtz.rank_three_of_heavy_six_three` supplies it.  The residual stratum
  shrinks from thirty-five triples to twenty.
* `Gtz.gtzWeightedAll_three_of_sixLines` — the same for the line-count residual.
  `Gtz.exists_dominating_of_hasAtMostLines_five_rankThree` is size-generic, so the
  residual can be posed at size six directly instead of at seven.
* `Gtz.isEmpty_sevenThreeCrux_of_isEmpty_sixThreeCrux` and its contrapositive
  `Gtz.nonempty_sixThreeCrux_of_nonempty_sevenThreeCrux` — cruxes DESCEND.  A
  `(7,3)` crux forces a `(6,3)` crux, so the wall cell is not merely the smaller of
  two targets, it is the only one.

## WHAT THIS DOES NOT DO

Nothing here touches `IsEmpty Gtz.SixThreeCrux`, which is the wall and is open.
The converse descent — a `(6,3)` crux forcing a `(7,3)` crux — is NOT proved and
does not follow from what is here: `Gtz.nonempty_sevenThreeCrux_of_not_gtzWeighted_seven_three`
carries `Gtz.GtzWeighted 6 3` as a hypothesis, so it cannot be run at a design that
refutes it.  The crux relation is an implication in one direction only.

`Gtz.GtzWeightedHeavy 6 3 → Gtz.GtzWeightedHeavy 7 3` is NOT a consequence of the
walk and is not attempted: the walk scales atoms by `sqrt W ≤ 1`, so leverages
shrink and all-heaviness is not transported.  What IS available, and is what the
heavy statements below use, is `Gtz.rank_three_of_heavy_six_three`, which reruns
the shipped deflation induction under the sharpened Veronese cap and never moves
all-heaviness along a walk.
-/

namespace Gtz

/-! ## 1. The all-heavy minimiser dichotomy collapses

`Gtz.exists_allHeavy_minimiser_of_not_rank_three` splits on `Gtz.GtzWeighted 6 3`
and hands back a minimiser at whichever size survives.  With the arrow in hand the
`(7,3)` branch is unreachable: failing rank three IS failing `(6,3)`. -/

/-- **A rank-three counterexample is realised at `(6,3)`, full stop.**  Sharpens
`Gtz.exists_allHeavy_minimiser_of_not_rank_three` from a two-size dichotomy to a
single size. -/
theorem exists_allHeavy_minimiser_of_not_rank_three_sharp (hfail : ¬ GtzWeightedAll 3) :
    ∃ design : WeightedDesign 6 3,
      AllHeavy design
      ∧ (∀ selected : Finset (Fin 6), selected.card = 3 → ¬ Dominates design selected)
      ∧ (∀ point : ChartPoint 6 3,
          chartObjective (chartPointOfDesign design) ≤ chartObjective point)
      ∧ chartObjective (chartPointOfDesign design) < 0 :=
  exists_allHeavy_minimiser_sixThree fun h63 => hfail (gtzWeightedAll_three_of_six_three h63)

/-! ## 2. The rank-four Naimark partner joins the equivalence class

Naimark duality at `m = 7` exchanges rank three with rank four, and the spike
descent brings rank four back down one size.  The two together close a loop that
the missing arrow used to break. -/

/-- The spike descent one size below the tree's previous entry point. -/
theorem gtzWeighted_six_three_of_seven_four (h74 : GtzWeighted 7 4) : GtzWeighted 6 3 :=
  gtzWeighted_of_spike (by norm_num) (by norm_num) h74

/-- **`(7,4)` IS `(6,3)`.**  Up by `Gtz.gtzWeighted_seven_four_of_seven_three` through
the walk's arrow, back down by the spike.  A third cell in the rank-three
equivalence class, and the first one at another rank. -/
theorem gtzWeighted_six_three_iff_seven_four : GtzWeighted 6 3 ↔ GtzWeighted 7 4 :=
  ⟨fun h63 => gtzWeighted_seven_four_of_seven_three (gtzWeighted_seven_three_of_six_three h63),
    gtzWeighted_six_three_of_seven_four⟩

/-- `(7,4)` carries all of rank three — one size below
`Gtz.gtzWeightedAll_three_of_eight_four`. -/
theorem gtzWeightedAll_three_of_seven_four (h74 : GtzWeighted 7 4) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three (gtzWeighted_six_three_of_seven_four h74)

/-- The 1997 statement at rank three from the rank-four partner cell. -/
theorem gtz_original_rank_three_of_seven_four (h74 : GtzWeighted 7 4) :
    ∀ n, 0 < n → GtzOriginal n 3 :=
  original_of_weighted 3 (gtzWeightedAll_three_of_seven_four h74)

/-! ## 3. The doubly-heavy stratum, at twenty triples instead of thirty-five

`Gtz.gtzWeightedHeavy_six_three_of_doublyHeavy` was already stated at size six; it
had nowhere to go, because the only heavy-to-rank arrow started at seven. -/

/-- **The doubly-heavy `(6,3)` stratum carries all of rank three.**  Sharpens
`Gtz.gtzWeightedAll_three_of_doublyHeavy_seven_three` by one size: the residual
narrowing is now posed on twenty triples rather than thirty-five. -/
theorem gtzWeightedAll_three_of_doublyHeavy_six_three
    (hnarrow : ∀ D : WeightedDesign 6 3, AllHeavy D →
      HasStrictlyDominatingCoSingletons D →
        ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    GtzWeightedAll 3 :=
  rank_three_of_heavy_six_three (gtzWeightedHeavy_six_three_of_doublyHeavy hnarrow)

/-- The 1997 statement at rank three from the doubly-heavy `(6,3)` stratum. -/
theorem gtz_original_rank_three_of_doublyHeavy_six_three
    (hnarrow : ∀ D : WeightedDesign 6 3, AllHeavy D →
      HasStrictlyDominatingCoSingletons D →
        ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    ∀ n, 0 < n → GtzOriginal n 3 :=
  original_of_weighted 3 (gtzWeightedAll_three_of_doublyHeavy_six_three hnarrow)

/-! ## 4. The line-count residual, at size six

`Gtz.exists_dominating_of_hasAtMostLines_five_rankThree` takes the size as an
argument, so the reduction runs at six exactly as it ran at seven; what changes is
that the leftover is now a statement about the cell that decides the rank. -/

/-- The line-count reduction posed at `(6,3)`.  Sharpens
`Gtz.gtzWeighted_seven_three_of_sixLines` by one size. -/
theorem gtzWeighted_six_three_of_sixLines
    (hresidual : ∀ D : WeightedDesign 6 3, ¬ HasAtMostLines D 5 →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    GtzWeighted 6 3 := by
  intro D
  by_cases hlines : HasAtMostLines D 5
  · exact exists_dominating_of_hasAtMostLines_five_rankThree 6 D hlines
  · exact hresidual D hlines

/-- The all-heavy reading of the same residual. -/
theorem gtzWeightedHeavy_six_three_of_sixLines
    (hresidual : ∀ D : WeightedDesign 6 3, AllHeavy D → ¬ HasAtMostLines D 5 →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    GtzWeightedHeavy 6 3 := by
  intro D hheavy
  by_cases hlines : HasAtMostLines D 5
  · exact exists_dominating_of_hasAtMostLines_five_rankThree 6 D hlines
  · exact hresidual D hheavy hlines

/-- **The six-line residual at size six carries all of rank three.**  The reduction
swallows every `(6,3)` design on at most five lines; what is left is the generic
stratum, and discharging it there now settles the rank. -/
theorem gtzWeightedAll_three_of_sixLines
    (hresidual : ∀ D : WeightedDesign 6 3, AllHeavy D → ¬ HasAtMostLines D 5 →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) :
    GtzWeightedAll 3 :=
  rank_three_of_heavy_six_three (gtzWeightedHeavy_six_three_of_sixLines hresidual)

/-! ## 5. Cruxes descend

The arrow read at the level of the crux objects themselves.  Only one direction is
available; see the module header. -/

/-- **A `(7,3)` crux cannot survive an empty `(6,3)` crux.** -/
theorem isEmpty_sevenThreeCrux_of_isEmpty_sixThreeCrux (hempty : IsEmpty SixThreeCrux) :
    IsEmpty SevenThreeCrux :=
  isEmpty_sevenThreeCrux_of_gtzWeighted_six_three
    (gtzWeighted_six_three_of_isEmpty_sixThreeCrux hempty)

/-- The contrapositive, which is the form a counterexample hunt reads: any `(7,3)`
crux is accompanied by a `(6,3)` crux, so hunting at the smaller cell loses
nothing. -/
theorem nonempty_sixThreeCrux_of_nonempty_sevenThreeCrux (hseven : Nonempty SevenThreeCrux) :
    Nonempty SixThreeCrux := by
  by_contra hnone
  exact (isEmpty_sevenThreeCrux_of_isEmpty_sixThreeCrux (not_nonempty_iff.mp hnone)).false
    hseven.some

end Gtz
