/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Quantitative.SixThreeCrux
import Gtz.Quantitative.SixThreeExclusionFrontier
import Gtz.Reduction.StressWalk

/-!
# `IsEmpty Gtz.SevenThreeCrux` is derivable, so the terminus loses an antecedent

The rank-three assembly shipped with TWO open antecedents.  Both
`Gtz.gtzWeightedAll_three_of_isEmpty_cruxes` and the terminus
`Gtz.gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidate` asked
for the `(6,3)` cell AND, separately, for `IsEmpty Gtz.SevenThreeCrux`.  The
second was open because the tree had no arrow `(6,3) → (7,3)`: the only
candidate, `Gtz.gtzWeighted_seven_three_of_six_three_of_heavy`, still demanded
`Gtz.GtzWeightedHeavy 7 3` as a hypothesis.

`Gtz.gtzWeighted_seven_three_of_six_three` supplies that arrow, so this file
discharges the second antecedent everywhere it appeared.  Every theorem here is
a composition; the mathematics is in `Gtz/Reduction/StressWalk.lean`.

## WHAT LANDS

* `Gtz.isEmpty_sevenThreeCrux_of_gtzWeighted_six_three` — a `(7,3)` crux cannot
  coexist with the `(6,3)` cell, so `IsEmpty Gtz.SevenThreeCrux` is DERIVED
  rather than assumed.
* `Gtz.gtzWeightedAll_three_of_isEmpty_sixThreeCrux` — the two-crux assembly
  `Gtz.gtzWeightedAll_three_of_isEmpty_cruxes` on ONE crux.
* `Gtz.gtzWeightedAll_three_of_forall_not_isSixThreeRefutationCandidate_sharp`
  and `Gtz.gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidate_sharp`
  — the two termini of the exclusion campaign, each on the `(6,3)` box search
  ALONE.  These are the statements the search consumes.

The two frontier iffs that need no crux vocabulary, `Gtz.rank_three_iff_six_three`
and `Gtz.liftingLemma_two_iff_six_three`, are in `Gtz/Reduction/StressWalk.lean`
with the flagship rather than here, so a consumer of the reduction alone need
not import the crux stack.

## WHAT THIS DOES NOT DO

NOTHING HERE APPROACHES `IsEmpty Gtz.SixThreeCrux`, which is still the wall and
is still open.  The frontier does not shrink in difficulty; it shrinks in COUNT,
from two objects to one.  The `(7,3)` crux is not refuted here either — it is
shown to be a consequence of the `(6,3)` cell, so anyone hunting a rank-three
counterexample may now hunt at `(6,3)` exclusively and lose nothing.
-/

namespace Gtz

/-- A `(7,3)` crux cannot coexist with the `(6,3)` cell. -/
theorem isEmpty_sevenThreeCrux_of_gtzWeighted_six_three (h63 : GtzWeighted 6 3) :
    IsEmpty SevenThreeCrux :=
  ⟨fun crux => not_gtzWeighted_seven_three_of_sevenThreeCrux crux
    (gtzWeighted_seven_three_of_six_three h63)⟩

/-- The two-crux assembly `Gtz.gtzWeightedAll_three_of_isEmpty_cruxes` on ONE
crux. -/
theorem gtzWeightedAll_three_of_isEmpty_sixThreeCrux
    (hsixEmpty : IsEmpty SixThreeCrux) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three (gtzWeighted_six_three_of_isEmpty_sixThreeCrux hsixEmpty)

/-- **WHAT EMPTYING THE BOX BUYS, ON THE BOX ALONE.**  Sharpens
`Gtz.gtzWeightedAll_three_of_forall_not_isSixThreeRefutationCandidate` by
deleting its `IsEmpty Gtz.SevenThreeCrux` hypothesis. -/
theorem gtzWeightedAll_three_of_forall_not_isSixThreeRefutationCandidate_sharp
    (hnone : ∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidate design) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidate hnone)

/-- **THE TERMINUS, ON THE `(6,3)` BOX SEARCH ALONE.**  Sharpens
`Gtz.gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidate` by
deleting its `IsEmpty Gtz.SevenThreeCrux` hypothesis: a `(6,3)` search that
empties the box now settles rank three of the 1997 conjecture outright. -/
theorem gtzOriginal_rank_three_of_forall_not_isSixThreeRefutationCandidate_sharp
    (hnone : ∀ design : WeightedDesign 6 3, ¬ IsSixThreeRefutationCandidate design)
    (atomCount : ℕ) (hpos : 0 < atomCount) : GtzOriginal atomCount 3 :=
  gtz_original_rank_three_of_six_three
    (gtzWeighted_six_three_of_forall_not_isSixThreeRefutationCandidate hnone)
    atomCount hpos

end Gtz
