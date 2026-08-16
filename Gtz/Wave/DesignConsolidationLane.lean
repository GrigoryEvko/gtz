import Gtz.Wave.ConsolidatedStrictTriple

/-!
# The design-level consolidation lane

`Gtz.ConsolidatedStrictTriple` implies all five on-path registry obligations.
Three of those five — A1, the one-line survivor and the tenth-heavy two meeting
lines — quantify over `Gtz.WeightedDesign 6 3` rather than over
`Gtz.DirectionChartPoint 6`.  Their wirings in `Gtz.Wave.ConsolidatedStrictTriple`
read the chart statement exactly once each, and only through
`Gtz.consolidatedStrictTripleDesign_of_consolidatedStrictTriple`.

This file states those three wirings against
`Gtz.ConsolidatedStrictTripleDesign` directly.  The design statement is strictly
weaker than the chart statement, so the three obligations cost less than the
campaign has been paying for them.

## What the weakening buys

A `Gtz.DirectionChartPoint 6` carries a mass vector and a weight vector, so
after `weight_sum_one` it has eleven free coordinates.  A design enters the
chart with mass equal to weight (`Gtz.designChartPoint`), which leaves five.
The boost `mass / weight` is identically one on the image.  The design lane is
therefore the boost-one slice of the chart lane, and the two chart-level
obligations A2 and A3 are the part that genuinely needs the larger object.

## What it does not buy

Nothing here proves the design statement.  A weakening concentrates debt at a
smaller statement, it does not discharge it.  The registry count is unchanged
by this file.
-/

namespace Gtz

open Finset

/-- **A1 follows from the design statement alone.**  The A1 residual lists
eighteen hypotheses and concludes `False`.  One of them says no card-three
selection is strictly dominating, and the empty line pattern makes the design
primitive. -/
theorem baseTripleTightLineFreeOffConicHeavyNeedleResidual_of_consolidatedStrictTripleDesign
    (hdesign : ConsolidatedStrictTripleDesign) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual := by
  intro design _tightDir _weakDir hlineFree _hoffConic _hdominates _htightNe _htight
    _hweakNe _hweak _htightSeparated _hheavyBase _hbaseUpper _hdiscriminant
    _hbaseNotStrict _hbaseResidual _hnoLight _hheavy hnoStrict _hcapLower _hcapUpper
    _hprobe
  obtain ⟨selected, hcard, hposDef⟩ :=
    hdesign design (isPrimitiveDesign_of_emptyPattern design hlineFree)
  exact hnoStrict selected hcard hposDef

/-- **The one-line survivor follows from the design statement alone.**  The line
makes the design primitive and the landed normal-blind restriction puts the
strict subset in the ten-candidate list. -/
theorem oneLineTenthHeavyJointBlindLineSparse_of_consolidatedStrictTripleDesign
    (hdesign : ConsolidatedStrictTripleDesign) :
    OneLineTenthHeavyJointBlindLineSparse := by
  intro design hpattern _hheavy _hweightHeavy _hcapBlind hlineBlind _hweak
  obtain ⟨selected, hcard, hposDef⟩ :=
    hdesign design (isPrimitiveDesign_of_oneLinePattern design hpattern)
  exact planeBranchTenCandidate_of_oneLine_strictTriple_of_normalBlind design hpattern
    hlineBlind selected hcard hposDef

/-- **The tenth-heavy two meeting lines follows from the design statement
alone.**  The two lines make the design primitive and the landed two-normal
restriction puts the strict subset on one of the four transversals. -/
theorem twoMeetingLinesTenthHeavyJointBlindTransversal_of_consolidatedStrictTripleDesign
    (hdesign : ConsolidatedStrictTripleDesign) :
    TwoMeetingLinesTenthHeavyJointBlindTransversal := by
  intro design hpattern _hheavy _hweightHeavy _hcapBlind _hweak
    normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
    hblindFirst hblindSecond
  obtain ⟨selected, hcard, hposDef⟩ :=
    hdesign design (isPrimitiveDesign_of_twoMeetingLinesPattern design hpattern)
  have hshape := twoMeetingLines_strictTriple_eq_transversal_of_bothLineNormalBlind
    design normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
    hblindFirst hblindSecond selected hcard hposDef
  rcases hshape with h135 | h145 | h235 | h245
  · exact Or.inl (by simpa only [h135] using hposDef)
  · exact Or.inr (Or.inl (by simpa only [h145] using hposDef))
  · exact Or.inr (Or.inr (Or.inl (by simpa only [h235] using hposDef)))
  · exact Or.inr (Or.inr (Or.inr (by simpa only [h245] using hposDef)))

/-- **The lane, as one statement.**  The design consolidation discharges the
three design-level obligations together. -/
theorem designLane_of_consolidatedStrictTripleDesign
    (hdesign : ConsolidatedStrictTripleDesign) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal :=
  ⟨baseTripleTightLineFreeOffConicHeavyNeedleResidual_of_consolidatedStrictTripleDesign hdesign,
    oneLineTenthHeavyJointBlindLineSparse_of_consolidatedStrictTripleDesign hdesign,
    twoMeetingLinesTenthHeavyJointBlindTransversal_of_consolidatedStrictTripleDesign hdesign⟩

/-- **The chart lane factors through the design lane at these three.**  Stated so
a reader can see that nothing is lost by targeting the weaker statement. -/
theorem designLane_of_consolidatedStrictTriple
    (hconsolidated : ConsolidatedStrictTriple) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual ∧
      OneLineTenthHeavyJointBlindLineSparse ∧
      TwoMeetingLinesTenthHeavyJointBlindTransversal :=
  designLane_of_consolidatedStrictTripleDesign
    (consolidatedStrictTripleDesign_of_consolidatedStrictTriple hconsolidated)

end Gtz
