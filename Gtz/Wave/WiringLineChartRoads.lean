/-
# The chart roads to the one-line and two-meeting-lines classes

**CORRECTION, 2026-08-17.**  The registry entry at `Skeleton/Obligations.lean:207`
says that the two generic chart forms want a chart that nobody has built for the
one-line pattern.  The entry at `Skeleton/Obligations.lean:259` says that no
chart is in the tree for the two-meeting-lines pattern.  Both claims are FALSE,
and both ATTACK fields, at `:208` and at `:260`, send a fork to build an object
that the kernel already carries.

The two charts are in the kernel.  The two covering halves are UNCONDITIONAL
theorems with zero hypotheses:

* `Gtz.parameterizedChartCovers_oneLineDirection`
  (Gtz/Design/OneLineCovering.lean:400)
* `Gtz.parameterizedChartCovers_twoMeetingLinesDirection`
  (Gtz/Design/TwoMeetingLinesCovering.lean:283)

Each one already has its consumer in the same module
(`Gtz.stressFreeStratumIsTieFree_oneLine_of_chart` at
Gtz/Design/OneLineCovering.lean:460 and
`Gtz.stressFreeStratumIsTieFree_twoMeetingLines_of_chart` at
Gtz/Design/TwoMeetingLinesCovering.lean:336).

The corrected position: these two classes sit in exactly the same place as the
three-lines class and the K4 class.  Only the ANALYTIC half is open.  The open
content is tie-freeness of a three-parameter chart and of a two-parameter chart,
at every admissible parameter.  No chart construction remains.

## The collapse of the two stratum spellings

`Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree`
(Gtz/Design/LineClassObstructions.lean:147) runs one way only.
`Gtz.StressFreeStratumIsTieFree` carries a stress-free hypothesis on the design,
so it speaks about a SMALLER set of designs than `Gtz.StratumIsTieFree`.

At a pattern whose stratum is UNIFORMLY stress-free that hypothesis costs
nothing, and the converse is free.  Both patterns of this file have such a
stratum:

* `Gtz.stratumIsStressFree_oneThreePointLine`
  (Gtz/Reduction/TrichotomyLedger.lean:485)
* `Gtz.stratumIsStressFree_twoMeetingLines`
  (Gtz/Reduction/TrichotomyLedger.lean:491)

So the two spellings collapse to ONE Prop at each of the two patterns, and the
on-path frontier at these two entries is a single statement in five names.

## Trap ledger

**Equivalence.**  The two chart roads are NOT equivalences.
`Gtz.DirectionChartIsTieFree` quantifies over every `Gtz.DirectionChartPoint`,
whose mass and weight obey positivity and one sum law and NO Parseval law, while
`Gtz.WeightedDesign` carries `isParseval` as a field.  The chart hypothesis
therefore reaches chart points that no design of the stratum reads, and it is a
priori STRICTLY stronger than its conclusion.  The tree holds no converse.

The collapse theorems below ARE equivalences, and the equivalence is their whole
content.  They record the identification of two Props that the tree previously
related in one direction only.

**Unsatisfiable antecedent.**  The antecedent of each chart road is the open
analytic half, and this file exhibits no inhabitant of it.  What the file does
exhibit is an inhabitant of the ADMISSIBILITY predicate at each pattern
(`Gtz.isAdmissibleOneLineParameter_two_three_four` and
`Gtz.isAdmissibleTwoMeetingLinesParameter_two_three`).  Without those the chart
hypothesis could hold by an empty parameter range, and each road would prove its
class outright for a bad reason.  The parameter ranges are inhabited, so the
chart demand is a real demand.

The antecedent of each collapse theorem is a stress-freeness statement that is a
landed theorem at both patterns, so those antecedents are inhabited outright.

## What this file does NOT do

It retires NO axiom.  `Skeleton/Obligations.lean` keeps all seven.  Every road
here is conditional, and each open hypothesis is the ANALYTIC half of a class.
The file corrects two registry claims, lands one missing converse, and
characterizes the hinge.  It proves no class statement unconditionally.
-/
import Gtz.Design.OneLineCovering
import Gtz.Design.TwoMeetingLinesCovering
import Gtz.Reduction.TrichotomyLedger
import Gtz.Wave.WiringSynonymClass

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

/-! ## The converse bridge, and the collapse of the two stratum spellings -/

/-- **THE MISSING CONVERSE.**  A uniformly stress-free stratum pays the
stress-free hypothesis of `Gtz.StressFreeStratumIsTieFree` for free, so class
tie-freeness returns plain stratum tie-freeness.  The relabel quantifier costs
nothing at the identity permutation. -/
theorem stratumIsTieFree_of_stressFreeStratumIsTieFree (pattern : LinePattern 6)
    (hstress : StratumIsStressFree pattern)
    (hfree : StressFreeStratumIsTieFree pattern) : StratumIsTieFree pattern :=
  fun design hpattern =>
    hfree design 1 (hstress design hpattern)
      (fun leftLabel midLabel rightLabel hleftMid hleftRight hmidRight => by
        simpa using hpattern leftLabel midLabel rightLabel hleftMid hleftRight hmidRight)

/-- **THE COLLAPSE.**  On a uniformly stress-free stratum the two spellings of
tie-freeness are one Prop. -/
theorem stratumIsTieFree_iff_stressFreeStratumIsTieFree (pattern : LinePattern 6)
    (hstress : StratumIsStressFree pattern) :
    StratumIsTieFree pattern ↔ StressFreeStratumIsTieFree pattern :=
  ⟨stressFreeStratumIsTieFree_of_stratumIsTieFree pattern,
    stratumIsTieFree_of_stressFreeStratumIsTieFree pattern hstress⟩

/-- The collapse at the one-line pattern. -/
theorem oneLine_stratumIsTieFree_iff_stressFreeStratumIsTieFree :
    StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]])
      ↔ StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  stratumIsTieFree_iff_stressFreeStratumIsTieFree _ stratumIsStressFree_oneThreePointLine

/-- The collapse at the two-meeting-lines pattern. -/
theorem twoMeetingLines_stratumIsTieFree_iff_stressFreeStratumIsTieFree :
    StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])
      ↔ StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  stratumIsTieFree_iff_stressFreeStratumIsTieFree _ stratumIsStressFree_twoMeetingLines

/-! ## Five names, one statement

`Gtz.oneLineOnPath_iff_stratumIsTieFree` collapsed four names of the one-line
class.  The converse above adds the fifth, which is the class Prop that every
chart consumer in the tree produces. -/

/-- **FIVE NAMES, ONE STATEMENT** at the one-line pattern.  The registry Prop of
the on-path axiom and the chart consumer's own conclusion are the same Prop. -/
theorem oneLineOnPath_iff_stressFreeStratumIsTieFree :
    OneLineTenthHeavyJointBlindLineSparse
      ↔ StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  oneLineOnPath_iff_stratumIsTieFree.trans
    oneLine_stratumIsTieFree_iff_stressFreeStratumIsTieFree

/-- **FIVE NAMES, ONE STATEMENT** at the two-meeting-lines pattern. -/
theorem twoMeetingLinesOnPath_iff_stressFreeStratumIsTieFree :
    TwoMeetingLinesTenthHeavyJointBlindTransversal
      ↔ StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  twoMeetingLinesOnPath_iff_stratumIsTieFree.trans
    twoMeetingLines_stratumIsTieFree_iff_stressFreeStratumIsTieFree

/-! ## The two chart roads

Each road composes an UNCONDITIONAL covering theorem with its consumer and with
the five-name collapse.  The registry says that neither road is available. -/

/-- **THE SECOND ROUTE TO THE ONE-LINE AXIOM.**  Tie-freeness of the
three-parameter `#2` chart at every admissible parameter gives the registry Prop
of `obligationHeavyWeakToStrictOneLine` outright. -/
theorem oneLineOnPath_of_chart
    (hchart : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param)) :
    OneLineTenthHeavyJointBlindLineSparse :=
  oneLineOnPath_iff_stressFreeStratumIsTieFree.mpr
    (stressFreeStratumIsTieFree_oneLine_of_chart hchart)

/-- **THE SECOND ROUTE TO THE TWO-MEETING-LINES AXIOM.**  Tie-freeness of the
two-parameter `#3` chart at every admissible parameter gives the registry Prop of
`obligationHeavyWeakToStrictTwoMeetingLines` outright. -/
theorem twoMeetingLinesOnPath_of_chart
    (hchart : ∀ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param →
      DirectionChartIsTieFree (twoMeetingLinesDirection param)) :
    TwoMeetingLinesTenthHeavyJointBlindTransversal :=
  twoMeetingLinesOnPath_iff_stressFreeStratumIsTieFree.mpr
    (stressFreeStratumIsTieFree_twoMeetingLines_of_chart hchart)

/-- The one-line chart road also returns plain stratum tie-freeness. -/
theorem oneLine_stratumIsTieFree_of_chart
    (hchart : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param)) :
    StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  oneLine_stratumIsTieFree_iff_stressFreeStratumIsTieFree.mpr
    (stressFreeStratumIsTieFree_oneLine_of_chart hchart)

/-- The two-meeting-lines chart road also returns plain stratum tie-freeness. -/
theorem twoMeetingLines_stratumIsTieFree_of_chart
    (hchart : ∀ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param →
      DirectionChartIsTieFree (twoMeetingLinesDirection param)) :
    StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  twoMeetingLines_stratumIsTieFree_iff_stressFreeStratumIsTieFree.mpr
    (stressFreeStratumIsTieFree_twoMeetingLines_of_chart hchart)

/-! ## Non-vacuity of the two admissible parameter ranges

A chart road whose parameter range is empty proves its class for a bad reason.
Both ranges carry an explicit rational point, so neither road is empty. -/

/-- The one-line admissible range is inhabited. -/
theorem isAdmissibleOneLineParameter_two_three_four :
    IsAdmissibleOneLineParameter ((2 : ℝ), (3 : ℝ), (4 : ℝ)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num,
    by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- The two-meeting-lines admissible range is inhabited. -/
theorem isAdmissibleTwoMeetingLinesParameter_two_three :
    IsAdmissibleTwoMeetingLinesParameter ((2 : ℝ), (3 : ℝ)) := by
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num, by norm_num⟩

/-- Neither chart road is vacuous: each admissible range carries a point. -/
theorem bothChartRangesInhabited :
    (∃ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param) ∧
      ∃ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param :=
  ⟨⟨_, isAdmissibleOneLineParameter_two_three_four⟩,
    ⟨_, isAdmissibleTwoMeetingLinesParameter_two_three⟩⟩

/-! ## The corrected registry position

The two entries are chart-equipped.  The pair below is the exact statement that
`Skeleton/Obligations.lean:207` and `Skeleton/Obligations.lean:259` deny. -/

/-- **THE CORRECTION, IN KERNEL FORM.**  One chart hypothesis at each of the two
patterns discharges BOTH on-path registry Props at once. -/
theorem bothLineClassesOnPath_of_charts
    (hOneLine : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param))
    (hTwoMeetingLines : ∀ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param →
      DirectionChartIsTieFree (twoMeetingLinesDirection param)) :
    OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal :=
  ⟨oneLineOnPath_of_chart hOneLine, twoMeetingLinesOnPath_of_chart hTwoMeetingLines⟩

/-! ## The four-fold collapse at a stress-free stratum

`Gtz.patternTightDominatedCoverProperty_iff_heavyWeakToStrict` and
`Gtz.patternTightDominatedCoverProperty_iff_stratumIsTieFree` are BOTH generic in
the pattern.  The converse above adds the fourth name.  At a uniformly
stress-free stratum the four Props are one Prop. -/

/-- **FOUR NAMES, ONE STATEMENT, AT ANY UNIFORMLY STRESS-FREE STRATUM.**  The
uniform weak-to-strict Prop and the class Prop that every chart consumer produces
are the same statement. -/
theorem heavyWeakToStrict_iff_stressFreeStratumIsTieFree (pattern : LinePattern 6)
    (hstress : StratumIsStressFree pattern) :
    PatternHeavyWeakToStrict pattern ↔ StressFreeStratumIsTieFree pattern :=
  (patternTightDominatedCoverProperty_iff_heavyWeakToStrict pattern).symm.trans
    (patternTightDominatedCoverProperty_iff_stratumIsTieFree.trans
      (stratumIsTieFree_iff_stressFreeStratumIsTieFree pattern hstress))

/-- The collapse at entry `#2`. -/
theorem oneLine_heavyWeakToStrict_iff :
    PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2]])
      ↔ StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  heavyWeakToStrict_iff_stressFreeStratumIsTieFree _ stratumIsStressFree_oneThreePointLine

/-- The collapse at entry `#3`. -/
theorem twoMeetingLines_heavyWeakToStrict_iff :
    PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])
      ↔ StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  heavyWeakToStrict_iff_stressFreeStratumIsTieFree _ stratumIsStressFree_twoMeetingLines

/-- The collapse at entry `#4`. -/
theorem threeLines_heavyWeakToStrict_iff :
    PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5]])
      ↔ StressFreeStratumIsTieFree
          (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5]]) :=
  heavyWeakToStrict_iff_stressFreeStratumIsTieFree _ stratumIsStressFree_threeLines

/-- The collapse at entry `#5`. -/
theorem graphicKFour_heavyWeakToStrict_iff :
    PatternHeavyWeakToStrict
        (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]])
      ↔ StressFreeStratumIsTieFree
          (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]) :=
  heavyWeakToStrict_iff_stressFreeStratumIsTieFree _ stratumIsStressFree_graphicKFour

/-! ## The `(6,3)` hinge, characterized

The residual list has five entries.  Four of them carry a uniformly stress-free
stratum, and the collapse above rewrites each one as the uniform Prop
`Gtz.PatternHeavyWeakToStrict`.  Entry `#1`, the line-free cell, is the ONLY
entry where the stress-free hypothesis carries content: six points with no three
collinear lie on a conic along a codimension-one sublocus
(`Gtz.stratumStressHasFullSupport_lineFree`), so that stratum is not uniformly
stress-free and no collapse is available there. -/

/-- The four nonempty residual families, in the uniform weak-to-strict spelling.
Each conjunct replaces one bespoke registry Prop by a pattern instance of ONE
size-generic Prop. -/
def FourNonemptyStrataWeakToStrict : Prop :=
  PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2]])
    ∧ PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])
    ∧ PatternHeavyWeakToStrict
        (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5]])
    ∧ PatternHeavyWeakToStrict
        (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]])

/-- **THE HINGE, CHARACTERIZED.**  The stress-free `(6,3)` hinge is EQUIVALENT to
the line-free class statement together with four instances of one uniform Prop.
The tree carried the forward direction only. -/
theorem stressFreeHinge_iff_lineFreeClass_and_fourStrata :
    StressFreeHingeHoldsSixThree
      ↔ StressFreeStratumIsTieFree (lineFamilyPattern ([] : List (List (Fin 6))))
          ∧ FourNonemptyStrataWeakToStrict := by
  constructor
  · intro hinge
    have hclasses := stressFreeResidualFamilies_tieFree_iff_stressFreeHinge.mpr hinge
    exact ⟨hclasses _ (by decide),
      oneLine_heavyWeakToStrict_iff.mpr (hclasses _ (by decide)),
      twoMeetingLines_heavyWeakToStrict_iff.mpr (hclasses _ (by decide)),
      threeLines_heavyWeakToStrict_iff.mpr (hclasses _ (by decide)),
      graphicKFour_heavyWeakToStrict_iff.mpr (hclasses _ (by decide))⟩
  · rintro ⟨hlineFree, hOneLine, hTwoMeeting, hThreeLines, hKFour⟩
    refine stressFreeResidualFamilies_tieFree_iff_stressFreeHinge.mp ?_
    intro lines hlines
    simp only [stressFreeResidualFamiliesSix, List.mem_cons, List.not_mem_nil,
      or_false] at hlines
    rcases hlines with rfl | rfl | rfl | rfl | rfl
    · exact hlineFree
    · exact oneLine_heavyWeakToStrict_iff.mp hOneLine
    · exact twoMeetingLines_heavyWeakToStrict_iff.mp hTwoMeeting
    · exact threeLines_heavyWeakToStrict_iff.mp hThreeLines
    · exact graphicKFour_heavyWeakToStrict_iff.mp hKFour

/-- **THE HINGE, IN REGISTRY FORM.**  The same characterization with entry `#1`
spelled as the registry Prop of `obligationBaseTripleTightUThreeSix`. -/
theorem stressFreeHinge_iff_registryLineFree_and_fourStrata :
    StressFreeHingeHoldsSixThree
      ↔ BaseTripleTightLineFreeOffConicHeavyNeedleResidual
          ∧ FourNonemptyStrataWeakToStrict :=
  stressFreeHinge_iff_lineFreeClass_and_fourStrata.trans
    (and_congr_left' heavyNeedleResidual_iff_stressFreeStratumIsTieFree.symm)

/-- **RANK-THREE GTZ AT EVERY SIZE**, from the line-free residual and the four
uniform Props. -/
theorem gtzWeightedAll_three_of_registryLineFree_and_fourStrata
    (hlineFree : BaseTripleTightLineFreeOffConicHeavyNeedleResidual)
    (hfour : FourNonemptyStrataWeakToStrict) : GtzWeightedAll 3 :=
  rank_three_iff_six_three.mpr
    (gtzWeighted_six_three_of_stressFreeHinge
      (stressFreeHinge_iff_registryLineFree_and_fourStrata.mpr ⟨hlineFree, hfour⟩))

/-- The certificate-free residual joins the characterization. -/
theorem noStressResidual_six_iff_registryLineFree_and_fourStrata :
    NoStressResidual 6
      ↔ BaseTripleTightLineFreeOffConicHeavyNeedleResidual
          ∧ FourNonemptyStrataWeakToStrict :=
  noStressResidual_six_iff_stressFreeHingeHoldsSixThree.trans
    stressFreeHinge_iff_registryLineFree_and_fourStrata

/-! ## Three of the five on-path Props are consequences of the hinge

`Gtz.stressFreeHingeHoldsSixThree_of_allFiveOnPath` takes the five registry Props
to the hinge.  The converse never landed, and
`Gtz/Wave/WiringAllFiveOnPath.lean` records the exact reason: a converse wants
`Gtz.StratumIsTieFree` back from `Gtz.StressFreeStratumIsTieFree`, and that
statement was not in the tree.  It is in the tree now
(`Gtz.stratumIsTieFree_of_stressFreeStratumIsTieFree`), and it closes the
converse at three of the five entries.

**#CIRCULARITY — THIS RETIRES NO AXIOM.  READ THIS BEFORE YOU QUOTE THE SECTION.**
`Gtz.threeOnPathProps_of_stressFreeHinge` derives three registry Props FROM the
hinge.  The hinge is EQUIVALENT to the conjunction of all five class statements
(`Gtz.stressFreeHinge_iff_lineFreeClass_and_fourStrata`), and three of those five
are the very Props the theorem concludes.  So the derivation is circular for the
purpose of retirement, and it discharges nothing.

To retire an axiom a fork must prove its Prop UNCONDITIONALLY.  This file proves
no class statement unconditionally, and it leaves all seven registry axioms
standing.  What the section records is REDUNDANCY: entries `#1`, `#2` and `#3`
of `Gtz.AllFiveOnPath` add nothing to the hinge that the conjunction already
carries.  A fork that wants the cell must still prove the analytic half. -/

/-- Entry `#2` of the conjunction follows FROM the hinge. -/
theorem oneLineOnPath_of_stressFreeHinge (hinge : StressFreeHingeHoldsSixThree) :
    OneLineTenthHeavyJointBlindLineSparse :=
  oneLineOnPath_iff_stressFreeStratumIsTieFree.mpr
    (stressFreeResidualFamilies_tieFree_iff_stressFreeHinge.mpr hinge _ (by decide))

/-- Entry `#3` of the conjunction follows FROM the hinge. -/
theorem twoMeetingLinesOnPath_of_stressFreeHinge (hinge : StressFreeHingeHoldsSixThree) :
    TwoMeetingLinesTenthHeavyJointBlindTransversal :=
  twoMeetingLinesOnPath_iff_stressFreeStratumIsTieFree.mpr
    (stressFreeResidualFamilies_tieFree_iff_stressFreeHinge.mpr hinge _ (by decide))

/-- Entry `#1` of the conjunction follows FROM the hinge. -/
theorem baseTripleTightLineFree_of_stressFreeHinge (hinge : StressFreeHingeHoldsSixThree) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual :=
  heavyNeedleResidual_iff_stressFreeStratumIsTieFree.mpr
    (stressFreeResidualFamilies_tieFree_iff_stressFreeHinge.mpr hinge _ (by decide))

/-- **THREE OF THE FIVE ON-PATH PROPS CARRY NO CONTENT BEYOND THE HINGE.**  Each
of the first three conjuncts of `Gtz.AllFiveOnPath` follows from the hinge that
the conjunction was assembled to prove. -/
theorem threeOnPathProps_of_stressFreeHinge (hinge : StressFreeHingeHoldsSixThree) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual
      ∧ OneLineTenthHeavyJointBlindLineSparse
      ∧ TwoMeetingLinesTenthHeavyJointBlindTransversal :=
  ⟨baseTripleTightLineFree_of_stressFreeHinge hinge,
    oneLineOnPath_of_stressFreeHinge hinge,
    twoMeetingLinesOnPath_of_stressFreeHinge hinge⟩

/-- **THE FIVE-PROP CONJUNCTION, CHARACTERIZED.**  `Gtz.AllFiveOnPath` is the
hinge together with the two CHART-flavored Props, and nothing more.  Entries
`#1`, `#2` and `#3` are redundant inside the conjunction.  Entries `#4` and `#5`
survive because each one demands tie-freeness of a chart at every
`Gtz.DirectionChartPoint`, and such a point obeys no Parseval law. -/
theorem allFiveOnPath_iff_hinge_and_twoChartProps :
    AllFiveOnPath
      ↔ StressFreeHingeHoldsSixThree
          ∧ ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines
          ∧ KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  constructor
  · intro hall
    exact ⟨stressFreeHingeHoldsSixThree_of_allFiveOnPath hall,
      hall.2.2.2.1, hall.2.2.2.2⟩
  · rintro ⟨hinge, hThreeLines, hKFour⟩
    obtain ⟨hlineFree, hOneLine, hTwoMeeting⟩ := threeOnPathProps_of_stressFreeHinge hinge
    exact ⟨hlineFree, hOneLine, hTwoMeeting, hThreeLines, hKFour⟩

/-- **THE `(6,3)` CELL FROM THE HINGE AND THE TWO CHART PROPS.**  Every one of the
eighteen `Gtz.allFiveOnPath_of_*` doors is reachable from this triple. -/
theorem gtzWeightedAll_three_of_hinge_and_twoChartProps
    (hinge : StressFreeHingeHoldsSixThree)
    (hThreeLines :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines)
    (hKFour : KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_allFiveOnPath
    (allFiveOnPath_iff_hinge_and_twoChartProps.mpr ⟨hinge, hThreeLines, hKFour⟩)

/-! ## The whole stress-free frontier, from four charts

The four nonempty entries are ALL chart-equipped.  Entries `#2` and `#3` carry
the two charts that the registry denies.  Entries `#4` and `#5` carry the two
charts the registry acknowledges.  So the analytic content of the stress-free
branch, outside the line-free cell, is tie-freeness of four explicit chart
families. -/

/-- **THE FOUR-CHART ROAD TO THE HINGE.**  Tie-freeness of the four charts, plus
the line-free residual, gives the stress-free `(6,3)` hinge. -/
theorem stressFreeHinge_of_lineFree_and_fourCharts
    (hlineFree : BaseTripleTightLineFreeOffConicHeavyNeedleResidual)
    (hOneLine : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param))
    (hTwoMeetingLines : ∀ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param →
      DirectionChartIsTieFree (twoMeetingLinesDirection param))
    (hThreeLines : ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide →
      DirectionChartIsTieFree (threeLinesDirection slide))
    (hKFour : DirectionChartIsTieFree kFourDirection) :
    StressFreeHingeHoldsSixThree :=
  stressFreeHinge_iff_registryLineFree_and_fourStrata.mpr
    ⟨hlineFree,
      oneLine_heavyWeakToStrict_iff.mpr
        (stressFreeStratumIsTieFree_oneLine_of_chart hOneLine),
      twoMeetingLines_heavyWeakToStrict_iff.mpr
        (stressFreeStratumIsTieFree_twoMeetingLines_of_chart hTwoMeetingLines),
      threeLines_heavyWeakToStrict_iff.mpr
        (stressFreeStratumIsTieFree_threeLines_of_chart hThreeLines),
      graphicKFour_heavyWeakToStrict_iff.mpr
        (stressFreeStratumIsTieFree_graphicKFour_of_chart hKFour)⟩

/-- **RANK-THREE GTZ FROM FOUR CHARTS AND THE LINE-FREE RESIDUAL.**  This is the
whole `(6,3)` cell in five hypotheses, four of which are chart statements. -/
theorem gtzWeightedAll_three_of_lineFree_and_fourCharts
    (hlineFree : BaseTripleTightLineFreeOffConicHeavyNeedleResidual)
    (hOneLine : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param))
    (hTwoMeetingLines : ∀ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param →
      DirectionChartIsTieFree (twoMeetingLinesDirection param))
    (hThreeLines : ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide →
      DirectionChartIsTieFree (threeLinesDirection slide))
    (hKFour : DirectionChartIsTieFree kFourDirection) :
    GtzWeightedAll 3 :=
  rank_three_iff_six_three.mpr
    (gtzWeighted_six_three_of_stressFreeHinge
      (stressFreeHinge_of_lineFree_and_fourCharts hlineFree hOneLine hTwoMeetingLines
        hThreeLines hKFour))

end Gtz
