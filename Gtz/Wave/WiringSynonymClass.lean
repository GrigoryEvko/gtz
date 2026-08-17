/-
# THE SYNONYM CLASS OF THE `(6,3)` FRONTIER

## Read this file before you name a new Prop

This campaign has one open statement and roughly twenty names for it.  Fork
after fork has landed a "sharpened" form, and fork after fork has then proved
that form equivalent to what it sharpened.  This file collects the equivalences
in one place and closes the ones that were left half-open.

**#VACUITY — the master rule.**  An intermediate that is iff-equivalent to its
target records nothing.  Before you name a Prop, look for it in the table below.

## THE CLASS.  Every entry is the same mathematics

The junction of every route is `Gtz.StressFreeHingeHoldsSixThree`
(Gtz/Reduction/TrichotomyLedger.lean:629).  These spellings are PROVED equal to
it, or equal to one of its five conjuncts.

| # | Spelling | The equivalence, by name |
|---|---|---|
| 1 | `Gtz.StressFreeHingeHoldsSixThree` | the junction itself |
| 2 | no stress-free `(6,3)` design is a tie | `Gtz.stressFreeHingeHoldsSixThree_iff_no_stressFree_tie` |
| 3 | `Gtz.NoStressResidual 6` | `Gtz.noStressResidual_six_iff_stressFreeHingeHoldsSixThree` |
| 4 | the five residual families are tie-free | `Gtz.stressFreeResidualFamilies_tieFree_iff_stressFreeHinge` |
| 5 | `Gtz.AllFiveOnPath` | `Gtz.stressFreeHingeHoldsSixThree_of_allFiveOnPath`, one way |

Inside conjunct one, the line-free class:

| # | Spelling | The equivalence |
|---|---|---|
| 6 | `Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual` | registry entry |
| 7 | `Gtz.StressFreeStratumIsTieFree (lineFamilyPattern [])` | `Gtz.heavyNeedleResidual_iff_stressFreeStratumIsTieFree` |
| 8 | `Gtz.BaseTripleTightLineFreeOffConicWeakToStrict` | `Gtz.baseTripleTightLineFreeOffConicHeavyNeedleResidual_iff` |

Inside conjunct two, the one-line class.  FOUR spellings, ONE statement.
`Gtz.oneLineOnPath_iff_stratumIsTieFree` below collapses them:

| # | Spelling |
|---|---|
| 9 | `Gtz.OneLineTenthHeavyJointBlindLineSparse` |
| 10 | `Gtz.PatternHeavyWeakToStrict (lineFamilyPattern [[0,1,2]])` |
| 11 | `Gtz.PatternTightDominatedCoverProperty (lineFamilyPattern [[0,1,2]])` |
| 12 | `Gtz.StratumIsTieFree (lineFamilyPattern [[0,1,2]])` |

Conjunct three repeats the same four at its own pattern, collapsed by
`Gtz.twoMeetingLinesOnPath_iff_stratumIsTieFree`.  Conjunct four collapses by
`Gtz.chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_iff`.
Conjunct five collapses by `Gtz.kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_iff`.

Downstream of the junction, three more spellings that are one statement:

| # | Spelling | The equivalence |
|---|---|---|
| 13 | `Gtz.GtzWeighted 6 3` | `Gtz.rank_three_iff_six_three` |
| 14 | `Gtz.GtzWeightedAll 3` | the same |
| 15 | `Gtz.GtzOriginal n 3` | `Gtz.original_of_weighted` |

## #VACUITY — spellings that add a hypothesis the object already carries

| Door | Why it records nothing |
|---|---|
| `Gtz.hingeConclusion_sixThree_of_heavyTie` | heaviness is free at `(6,3)` through `Gtz.leverage_one_le_of_isTie_sixThree`.  `Gtz.heavyTie_hingeConclusion_iff_hingeHoldsAtSize_six_three` proves the iff |
| `Gtz.hingeHoldsAtSize_of_heavyBranch` | the same at a general size, modulo the predecessor |
| `Gtz.exists_dominating_of_noStressResidual` | its conclusion is the WEAK form, which the hinge already gives.  `Gtz.exists_dominating_of_stressFreeHinge` proves it with the residual dropped |

## #DUPLICATION — the same theorem landed twice under names that do not collide

| Pair | Sites |
|---|---|
| light-atom strict dominator | `Gtz.exists_posDef_of_lightAtom` (Gtz/Design/StratumEmptinessLedger.lean:509) and `Gtz.posDef_of_strictly_light_atom` (Gtz/Reduction/Deflation.lean:207) |
| light-atom tie refutation | `Gtz.not_isTie_of_lightAtom` (:544) and `Gtz.not_isTie_of_strictly_light_atom` (Gtz/Wave/WedgeLeakCriterion.lean:1310) |
| the leverage floor | `Gtz.leverage_one_le_of_isTie` (:557) and `Gtz.forall_one_le_leverage_of_isTie` (Gtz/Wave/WedgeLeakCriterion.lean:1333).  `Gtz.lightAtomFloors_agree` records the pair |
| the light-heavy dichotomy | `Gtz.hinge_of_predecessor_on_strictlyLightBranch` (Gtz/Wave/WedgeLeakCriterion.lean:1349) and `Gtz.obligationSubThresholdBandHinge_of_heavyTie` (Gtz/Wave/LightAtomTieFloor.lean:108) split one dichotomy and neither cites the other |
| the `M(K4)` design, THREE copies | `Gtz.kFourDesign`, `Gtz.coordinateDiagonalDesign` and `Gtz.graphicKFourDesign`.  Only the first pair is linked, by `rfl` |
| byte-identical designs | `Gtz.r4WitnessDesign` (Gtz/Design/TightAntecedentMining.lean:289) and `Gtz.swapWitnessDesign` (Gtz/Design/TightSwapObstructions.lean:395) |

## #BOGUS — doors whose hypothesis this tree already refutes

| Door | Refuter |
|---|---|
| `Gtz.gtzWeighted_six_three_of_livePivotPlaneCover` (Gtz/Wave/HeavyPivotFoil.lean:297) | `Gtz.not_atomLivePivotPlaneCoverClosed` (Gtz/Wave/PlaneRouteFoil.lean:348) |
| `Gtz.gtzWeighted_six_three_of_dropScalar` (Gtz/Wave/QuadCoverSelection.lean:1504) | `Gtz.not_atomQuadDropScalarClosed` (Gtz/Wave/QuadDropSign.lean:710) |

`Gtz.unopenableAtomDoors` records the pair.

## #BOGUS-READING — a refutation that does NOT say what its name suggests

`Gtz.not_relaxedStressFreeHinge_of_diamond`
(Gtz/Design/StressFreeClosureFailure.lean:612) is hypothesis-free and reads as a
kill of the stress-free hinge at `(6,3)`.  It is not one.  Its weight clause is
`0 <= weight`, NOT `0 < weight`.  The witness is the `(5,3)` diamond padded with
a sixth atom of weight zero, and `Gtz.WeightedDesign` carries `weight_pos` as a
field.  `Gtz.StressFreeHingeHoldsSixThree` is OPEN.
-/
import Gtz.Wave.WiringAllFiveOnPath
import Gtz.Wave.WiringDoorLedger
import Gtz.Wave.WiringJointEntrance
import Gtz.Design.ChartProgrammeAssembly
import Gtz.Wave.LivePairTieRefuter

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ### The four-spelling collapse of conjunct two -/

/-- **FOUR NAMES, ONE STATEMENT.**  The one-line registry Prop, the pattern
weak-to-strict form, the tight-dominated cover property and class tie-freeness
are all the same statement. -/
theorem oneLineOnPath_iff_stratumIsTieFree :
    OneLineTenthHeavyJointBlindLineSparse
      ↔ StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  oneLineTenthHeavyJointBlindLineSparse_iff.trans
    ((patternTightDominatedCoverProperty_iff_heavyWeakToStrict _).symm.trans
      patternTightDominatedCoverProperty_iff_stratumIsTieFree)

/-- **FOUR NAMES, ONE STATEMENT**, at the two-meeting-lines pattern. -/
theorem twoMeetingLinesOnPath_iff_stratumIsTieFree :
    TwoMeetingLinesTenthHeavyJointBlindTransversal
      ↔ StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  twoMeetingLinesTenthHeavyJointBlindTransversal_iff.trans
    ((patternTightDominatedCoverProperty_iff_heavyWeakToStrict _).symm.trans
      patternTightDominatedCoverProperty_iff_stratumIsTieFree)

/-! ### #BOGUS — the two live-pair doors to the hinge, both dead

`Gtz.stressFreeHingeHoldsSixThree_of_livePairTie` (Gtz/Design/ChartProgrammeAssembly.lean:354)
asks for a residual that `Gtz.not_livePairTieResidual` (Gtz/Wave/LivePairTieRefuter.lean:183)
refutes verbatim.  The refutation was landed and never wired to the door.

`Gtz.stressFreeHingeHoldsSixThree_of_heavyLivePairTie`
(Gtz/Wave/ChartProgrammeHeavyResidual.lean:91) adds a tenth-heavy filter.  The
same refuter clears the filter, because it carries weight `23/96` at label zero. -/

/-- **THE TENTH-HEAVY LIVE-PAIR RESIDUAL IS ALSO FALSE.**  The heavy filter does
not rescue the door: the landed refuter already satisfies it. -/
theorem not_heavyLivePairTieResidual :
    ¬ (∀ design : WeightedDesign 6 3,
        (∃ label : Fin 6, 1 / 10 ≤ design.weight label) →
        (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
        ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
          IsLivePair design pivotLabel pairFirst →
          ∃ pairSecond : Fin 6, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
            ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) := by
  intro hresidual
  obtain ⟨pairSecond, hpivot, hfirst, hpos⟩ :=
    hresidual livePairTieRefuterDesign
      ⟨0, by norm_num [livePairTieRefuterDesign, livePairTieRefuterWeight]⟩
      livePairTieRefuter_dominates 0 3 (by decide) livePairTieRefuter_isLivePair
  exact livePairTieRefuter_no_completion pairSecond hpivot hfirst hpos

/-- **BOTH LIVE-PAIR DOORS TO THE STRESS-FREE HINGE ARE DEAD.**  Neither can
open, and neither refutation was wired to the door it kills. -/
theorem unopenableLivePairDoors :
    ¬ (∀ design : WeightedDesign 6 3,
        (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
        ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
          IsLivePair design pivotLabel pairFirst →
          ∃ pairSecond, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
            ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond)
      ∧ ¬ (∀ design : WeightedDesign 6 3,
        (∃ label : Fin 6, 1 / 10 ≤ design.weight label) →
        (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
        ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
          IsLivePair design pivotLabel pairFirst →
          ∃ pairSecond : Fin 6, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
            ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) :=
  ⟨not_livePairTieResidual, not_heavyLivePairTieResidual⟩

/-! ### ROUTE A AND ROUTE B ARE ONE ROUTE

The ledger of this campaign prices two routes to `Gtz.StressFreeHingeHoldsSixThree`.
Route A pays five separate closures, one per matroid class, and arrives through
`Gtz.stressFreeHingeHoldsSixThree_of_residualFamilies`.  Route B pays one
statement, `Gtz.NoStressResidual 6`, and arrives through
`Gtz.stressFreeHingeHoldsSixThree_of_noStressResidual`.

**The two prices are equal.**  The theorem below closes the loop in kernel.  The
other two arms of the trichotomy are already spent inside both routes, by
`Gtz.twoPoleStratumSelection_six_unconditional` and
`Gtz.balancedStratumSelection_six_holds`, so neither route carries them as cost. -/

/-- **ROUTE A EQUALS ROUTE B.**  The conjunction of the five on-path registry
Props and the single Prop of the second route are one statement.  Route B is not
a cheaper target, and route A is not five independent targets. -/
theorem allFiveOnPath_iff_noStressResidual_six :
    AllFiveOnPath ↔ NoStressResidual 6 :=
  ⟨noStressResidual_six_of_allFiveOnPath,
    fun hresidual =>
      allFiveOnPath_iff_hingeHoldsAtSize_six_three.mpr
        (hingeHoldsAtSize_sixThree_of_stressFreeHinge
          twoPoleStratumSelection_six_unconditional
          (balancedStratumCapstone_of_balancedStratumSelection
            balancedStratumSelection_six_holds)
          (noStressResidual_six_iff_stressFreeHingeHoldsSixThree.mp hresidual))⟩

/-- **THE WHOLE LEDGER, AS ONE EQUIVALENCE CLASS.**  Route A, route B, the hinge
at the deciding cell, and the emptiness of the stress-free tie locus. -/
theorem routeA_iff_routeB_iff_hinge :
    (AllFiveOnPath ↔ NoStressResidual 6)
      ∧ (NoStressResidual 6 ↔ StressFreeHingeHoldsSixThree)
        ∧ (AllFiveOnPath ↔ HingeHoldsAtSize 6 3)
          ∧ (NoStressResidual 6 ↔
              ∀ design : WeightedDesign 6 3,
                (∀ stress : Fin 6 → ℝ,
                  (∑ c, stress c • atomMatrix (design.atom c)) = 0 → stress = 0) →
                  ¬ IsTie design) :=
  ⟨allFiveOnPath_iff_noStressResidual_six,
    noStressResidual_six_iff_stressFreeHingeHoldsSixThree,
      allFiveOnPath_iff_hingeHoldsAtSize_six_three,
        noStressResidual_six_iff_no_stressFree_tie⟩

/-! ### The three shapes of the answer are one shape -/

/-- The second route, the five-class split and the hinge all reach the same
capstone.  No route is a shortcut. -/
theorem gtzWeightedAll_three_of_anyRoute :
    (NoStressResidual 6 → GtzWeightedAll 3)
      ∧ (AllFiveOnPath → GtzWeightedAll 3)
      ∧ (StressFreeHingeHoldsSixThree → GtzWeightedAll 3)
      ∧ (ConsolidatedStrictTripleDesign → GtzWeightedAll 3) :=
  ⟨gtzWeightedAll_three_of_noStressResidual,
    gtzWeightedAll_three_of_allFiveOnPath,
    fun hinge => rank_three_iff_six_three.mpr (gtzWeighted_six_three_of_stressFreeHinge hinge),
    gtzWeightedAll_three_of_consolidatedStrictTripleDesign⟩

end Gtz
