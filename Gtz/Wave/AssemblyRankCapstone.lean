import Gtz.Wave.RankFourRungAssembly
import Gtz.Wave.RankFiveRungAssembly
import Gtz.Wave.RankSixRungAssembly

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The assembly-rank capstone — the cell modulo eleven named closures

The three rung assemblies each close one assembly rank modulo their
named closures: five at rank four, three at rank five, three at rank
six.  This file composes them along the rank spine.  The result is the
campaign endgame statement: the ELEVEN named closure propositions
jointly prove the `(6,3)` cell, and through the landed reduction they
close rank three at every size.

The eleven closures, by rung:

1. Rank four: `RankFourSupportTwoClosed`, `RankFourSharedPrivateClosed`,
   `RankFourKFourClosed`, `RankFourCycleIndependentClosed`,
   `RankFourBothParallelClosed`.
2. Rank five: `RankFiveSupportTwoClosed`, `RankFiveSharedPrivateClosed`,
   `RankFiveDenseClosed`.
3. Rank six: `RankSixSupportTwoClosed`, `RankSixSharedPrivateClosed`,
   `RankSixDenseClosed`.

The support-two closures of the three rungs share ONE residual (the
outer sharer, through the three refined bridges), and the shared-private
closures share one hypothesis list.  Thus the effective certificate
count is below eleven: one outer-sharer certificate discharges three
closures, and one shared-private certificate pattern discharges three
more.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.gtzWeighted_six_three_of_closures` — **THE CELL MODULO THE
  CLOSURES.**
* `Gtz.gtzWeightedAll_three_of_closures` — **THE RANK-THREE PAYOFF
  MODULO THE CLOSURES.**

## Vacuity

The closures are vacuous if `Gtz.GtzWeighted 6 3` holds, and the
composition is then trivial.  The statements here are conditional and
consume no axiom beyond the classical set.
-/

namespace Gtz

/-- **THE CELL MODULO THE CLOSURES.**  The eleven named closure
propositions jointly prove the `(6,3)` cell: each rung assembly closes
its assembly rank, and the rank spine leaves no rank to a
counterexample. -/
theorem gtzWeighted_six_three_of_closures
    (hfourOne : RankFourSupportTwoClosed)
    (hfourTwo : RankFourSharedPrivateClosed)
    (hfourKFour : RankFourKFourClosed)
    (hfourCycle : RankFourCycleIndependentClosed)
    (hfourParallel : RankFourBothParallelClosed)
    (hfiveOne : RankFiveSupportTwoClosed)
    (hfiveTwo : RankFiveSharedPrivateClosed)
    (hfiveDense : RankFiveDenseClosed)
    (hsixOne : RankSixSupportTwoClosed)
    (hsixTwo : RankSixSharedPrivateClosed)
    (hsixDense : RankSixDenseClosed) :
    GtzWeighted 6 3 := by
  refine gtzWeighted_six_three_of_forall_isSixThreeAssemblyRankExcluded ?_
  intro assemblyRank hfloor hceiling
  interval_cases assemblyRank
  · exact isSixThreeAssemblyRankExcluded_four_of_closures hfourOne hfourTwo
      hfourKFour hfourCycle hfourParallel
  · exact isSixThreeAssemblyRankExcluded_five_of_closures hfiveOne hfiveTwo
      hfiveDense
  · exact isSixThreeAssemblyRankExcluded_six_of_closures hsixOne hsixTwo
      hsixDense

/-- **THE RANK-THREE PAYOFF MODULO THE CLOSURES.**  The eleven closures
close rank three at every size, through the landed reduction of the
general cell to the `(6,3)` one. -/
theorem gtzWeightedAll_three_of_closures
    (hfourOne : RankFourSupportTwoClosed)
    (hfourTwo : RankFourSharedPrivateClosed)
    (hfourKFour : RankFourKFourClosed)
    (hfourCycle : RankFourCycleIndependentClosed)
    (hfourParallel : RankFourBothParallelClosed)
    (hfiveOne : RankFiveSupportTwoClosed)
    (hfiveTwo : RankFiveSharedPrivateClosed)
    (hfiveDense : RankFiveDenseClosed)
    (hsixOne : RankSixSupportTwoClosed)
    (hsixTwo : RankSixSharedPrivateClosed)
    (hsixDense : RankSixDenseClosed) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_closures hfourOne hfourTwo hfourKFour hfourCycle
      hfourParallel hfiveOne hfiveTwo hfiveDense hsixOne hsixTwo hsixDense)

end Gtz
