/-
# `AllFiveOnPath`: the five on-path Props as ONE named object, wired to the capstone

## The defect this file repairs

Eighteen theorems in `Gtz/Wave/` are named `Gtz.allFiveOnPath_of_*`.  Each one
concludes the same five-Prop conjunction, and each one spells that conjunction
out.  **The conjunction had no name.**  Nothing can consume an anonymous
conjunction cleanly, and every one of the eighteen doors is an orphan.

`Gtz.AllFiveOnPath` names it.  `Gtz.gtzWeightedAll_three_of_allFiveOnPath` takes
it to rank-three GTZ at every size, entirely inside `Gtz`.  Every one of the
eighteen doors reaches the capstone through this file.

## The chain, and where each step came from

`Skeleton.Obligations` assembles the same five into the hinge.  This file
replicates that assembly with the five Props as HYPOTHESES rather than axioms,
so the tree carries it without the scaffold.  The enumeration input is
`Gtz.linearSpaceListIsComplete_six` (Gtz/Design/LinePatternSixCasesTwo.lean:1535),
which is landed and unconditional.

| Entry | Route to `Gtz.StressFreeStratumIsTieFree` |
|---|---|
| line-free | `Gtz.heavyNeedleResidual_iff_stressFreeStratumIsTieFree` |
| one line | pattern heavy-weak-to-strict, then the cover property, then the relabel bridge |
| two meeting lines | the same three steps at its own pattern |
| three lines | the fundamental-domain iff, then the chart, then the cover |
| `M(K4)` | the refined iff, then the knife band, then the chart, then the cover |

## #VACUITY — read this file with the level-one law beside it

`Gtz.gtzWeightedAll_three_of_consolidatedStrictTripleDesign`
(Gtz/Wave/WiringDoorLedger.lean) shows that fifteen of the eighteen doors funnel
through a Prop that ALREADY gives rank-three GTZ.  A door of that lane is not a
reduction of the cell.  This file makes the eighteen doors reachable.  It does
not make any of them cheap.

## What this file does NOT prove

`Gtz.AllFiveOnPath` and `Gtz.StressFreeHingeHoldsSixThree` are NOT proved
equivalent here.  Only the line-free entry carries a converse
(`Gtz.heavyNeedleResidual_iff_stressFreeStratumIsTieFree`).  The one-line and
two-meeting-lines entries pass through
`Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree`, which runs one way only,
because the stress-free stratum is smaller than the full stratum.  A converse
would need `StratumIsTieFree` back from `StressFreeStratumIsTieFree`, and that
statement is not in the tree.
-/
import Gtz.Wave.WiringResidualEquivalence
import Gtz.Wave.OneLineSurvivorWiring
import Gtz.Wave.TenthHeavyLineResidualWiring
import Gtz.Wave.ThreeLinesMovedOrbitTraceWiring
import Gtz.Wave.KFourStarAllMaxHeavyWiring
import Gtz.Design.RigidityBridge
import Gtz.Design.KFourChartClosure
import Gtz.Design.LineClassObstructions

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ### 1.  The name -/

/-- **THE FIVE ON-PATH REGISTRY PROPS, AS ONE OBJECT.**  Eighteen theorems named
`Gtz.allFiveOnPath_of_*` conclude exactly this conjunction with no name for it. -/
def AllFiveOnPath : Prop :=
  BaseTripleTightLineFreeOffConicHeavyNeedleResidual
    ∧ OneLineTenthHeavyJointBlindLineSparse
    ∧ TwoMeetingLinesTenthHeavyJointBlindTransversal
    ∧ ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines
    ∧ KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict

/-! ### 2.  One class at a time -/

/-- Entry `#1`, the line-free cell.  The tree already carries this as an
equivalence. -/
theorem stressFreeStratumIsTieFree_lineFree_of_onPath
    (hresidual : BaseTripleTightLineFreeOffConicHeavyNeedleResidual) :
    StressFreeStratumIsTieFree (lineFamilyPattern ([] : List (List (Fin 6)))) :=
  heavyNeedleResidual_iff_stressFreeStratumIsTieFree.mp hresidual

/-- Entry `#2`, one three-point line. -/
theorem stressFreeStratumIsTieFree_oneLine_of_onPath
    (hresidual : OneLineTenthHeavyJointBlindLineSparse) :
    StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  stressFreeStratumIsTieFree_of_stratumIsTieFree _
    (stratumIsTieFree_of_tightDominatedCoverProperty
      ((patternTightDominatedCoverProperty_iff_heavyWeakToStrict _).mpr
        (patternHeavyWeakToStrict_oneLine_of_tenthHeavyJointBlindLineSparse hresidual)))

/-- Entry `#3`, two meeting three-point lines. -/
theorem stressFreeStratumIsTieFree_twoMeetingLines_of_onPath
    (hresidual : TwoMeetingLinesTenthHeavyJointBlindTransversal) :
    StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  stressFreeStratumIsTieFree_of_stratumIsTieFree _
    (stratumIsTieFree_of_tightDominatedCoverProperty
      ((patternTightDominatedCoverProperty_iff_heavyWeakToStrict _).mpr
        (patternHeavyWeakToStrict_twoMeetingLines_of_tenthHeavyJointBlindTransversal hresidual)))

/-- Entry `#4`, three three-point lines.  The covering half is the unconditional
`Gtz.parameterizedChartCovers_threeLinesDirection`. -/
theorem stressFreeStratumIsTieFree_threeLines_of_onPath
    (hresidual :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines) :
    StressFreeStratumIsTieFree
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5]]) :=
  stressFreeStratumIsTieFree_threeLines_of_chart
    (chartTieFreeThreeLines_of_fundamentalDomain
      (chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_iff.mp
        hresidual))

/-- Entry `#5`, `M(K4)`.  The covering half is the unconditional
`Gtz.directionChartCoversPrimitiveStratum_kFourDirection`. -/
theorem stressFreeStratumIsTieFree_graphicKFour_of_onPath
    (hresidual : KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict) :
    StressFreeStratumIsTieFree
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]) :=
  stressFreeStratumIsTieFree_graphicKFour_of_chart
    (directionChartIsTieFree_kFour_of_knifeBandWeakToStrict
      (kFourKnifeBandWeakToStrict_of_refined
        (kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_iff.mp hresidual)))

/-! ### 3.  The assembly -/

/-- The five entries of `Gtz.stressFreeResidualFamiliesSix`, all at once. -/
theorem residualFamiliesTieFree_of_allFiveOnPath (hall : AllFiveOnPath) :
    ∀ lines ∈ stressFreeResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines) := by
  obtain ⟨hlineFree, hOneLine, hTwoMeeting, hThreeLines, hKFour⟩ := hall
  intro lines hlines
  simp only [stressFreeResidualFamiliesSix, List.mem_cons, List.not_mem_nil,
    or_false] at hlines
  rcases hlines with rfl | rfl | rfl | rfl | rfl
  · exact stressFreeStratumIsTieFree_lineFree_of_onPath hlineFree
  · exact stressFreeStratumIsTieFree_oneLine_of_onPath hOneLine
  · exact stressFreeStratumIsTieFree_twoMeetingLines_of_onPath hTwoMeeting
  · exact stressFreeStratumIsTieFree_threeLines_of_onPath hThreeLines
  · exact stressFreeStratumIsTieFree_graphicKFour_of_onPath hKFour

/-- **THE STRESS-FREE ARM OF THE `(6,3)` HINGE, FROM THE FIVE ON-PATH PROPS.** -/
theorem stressFreeHingeHoldsSixThree_of_allFiveOnPath (hall : AllFiveOnPath) :
    StressFreeHingeHoldsSixThree :=
  stressFreeResidualFamilies_tieFree_iff_stressFreeHinge.mp
    (residualFamiliesTieFree_of_allFiveOnPath hall)

/-- **THE `(6,3)` CELL, FROM THE FIVE ON-PATH PROPS.** -/
theorem gtzWeighted_six_three_of_allFiveOnPath (hall : AllFiveOnPath) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_stressFreeHinge (stressFreeHingeHoldsSixThree_of_allFiveOnPath hall)

/-- **RANK-THREE GTZ AT EVERY SIZE, FROM THE FIVE ON-PATH PROPS.**  Every one of
the eighteen `Gtz.allFiveOnPath_of_*` doors reaches this theorem. -/
theorem gtzWeightedAll_three_of_allFiveOnPath (hall : AllFiveOnPath) : GtzWeightedAll 3 :=
  rank_three_iff_six_three.mpr (gtzWeighted_six_three_of_allFiveOnPath hall)

/-! ### 4.  The two routes meet -/

/-- The five on-path Props deliver the single Prop of the second route.  With
`Gtz.baseTripleTightLineFreeOffConicHeavyNeedleResidual_of_noStressResidual`
beside it, the first entry of the conjunction and the residual are equivalent. -/
theorem noStressResidual_six_of_allFiveOnPath (hall : AllFiveOnPath) : NoStressResidual 6 :=
  noStressResidual_six_of_stressFreeHinge (stressFreeHingeHoldsSixThree_of_allFiveOnPath hall)

/-- The second route delivers entry `#1` of the conjunction.  The converse
FAILS: entry `#1` constrains the line-free class only, and the other four
classes carry their own content. -/
theorem baseTripleTight_of_noStressResidual (hresidual : NoStressResidual 6) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual :=
  baseTripleTightLineFreeOffConicHeavyNeedleResidual_of_noStressResidual hresidual

end Gtz
