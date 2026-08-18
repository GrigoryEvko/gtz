/-
# The chart programme, assembled

Every entry of `Gtz.stressFreeResidualFamiliesSix` now carries a chart and a
covering.  Until entry `#1` was charted the five reductions could not be spent
together, because a missing cell blocks the list quantifier.  They can be spent
together at this commit, and that is what this file does.

## The atlas

The five cells and their charts, with the moduli count `4 - k` at `k` lines:

  entry `#1`, `[]`, four parameters, `Gtz.lineFreeDirection`,
  entry `#2`, one line, three parameters, `Gtz.oneLineDirection`,
  entry `#3`, two meeting lines, two parameters, `Gtz.twoMeetingLinesDirection`,
  entry `#4`, three lines, one parameter, `Gtz.threeLinesDirection`,
  entry `#5`, `M(K4)`, no parameter, `Gtz.kFourDirection`.

`Gtz.StressFreeChartPoint` is the disjoint union of the five parameter spaces,
`Gtz.StressFreeChartPoint.direction` sends a point to its six directions, and
`Gtz.StressFreeChartPoint.IsAdmissible` names the admissible region of the piece
the point lies in.  The atlas has total dimension four, and it is a finite
description of an infinite family of matroids.

## What the assembly buys

`Gtz.stressFreeHingeHoldsSixThree_of_atlas` reduces the rank-three residual of
GTZ to ONE universally quantified statement:

  every admissible point of the atlas has a tie-free direction chart.

The design-level quantifier is gone.  What remains quantifies over four real
parameters and six fixed rational vectors, and the pattern side of the problem
is fully discharged.  The enumeration input `Gtz.LinearSpaceListIsComplete` is
the only other hypothesis, and it is combinatorial.

`Gtz.stressFreeResidualFamiliesSix_tieFree_of_charts` is the same content with
the five charts kept apart, for consumers that discharge them one at a time.
-/
import Gtz.Design.LineFreeCovering
import Gtz.Design.OneLineCovering
import Gtz.Design.TwoMeetingLinesCovering
import Gtz.Design.OneDeterminantReduction

namespace Gtz

open Matrix

/-! ## The five charts, kept apart -/

/-- **THE FIVE-CHART RESIDUAL.**  Tie-freeness of the five charts at every
admissible parameter gives the tree's residual obligation at every entry of
`Gtz.stressFreeResidualFamiliesSix` at once.  Entry `#1` is the piece that was
missing before the line-free chart landed. -/
theorem stressFreeResidualFamiliesSix_tieFree_of_charts
    (hLineFree : ∀ param : ℝ × ℝ × ℝ × ℝ, IsAdmissibleLineFreeParameter param →
      DirectionChartIsTieFree (lineFreeDirection param))
    (hOneLine : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param))
    (hTwoMeetingLines : ∀ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param →
      DirectionChartIsTieFree (twoMeetingLinesDirection param))
    (hThreeLines : ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide →
      DirectionChartIsTieFree (threeLinesDirection slide))
    (hGraphicKFour : DirectionChartIsTieFree kFourDirection) :
    ∀ lines ∈ stressFreeResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines) := by
  intro lines hlines
  simp only [stressFreeResidualFamiliesSix, List.mem_cons, List.not_mem_nil,
    or_false] at hlines
  rcases hlines with rfl | rfl | rfl | rfl | rfl
  · exact stressFreeStratumIsTieFree_lineFree_of_chart hLineFree
  · exact stressFreeStratumIsTieFree_oneLine_of_chart hOneLine
  · exact stressFreeStratumIsTieFree_twoMeetingLines_of_chart hTwoMeetingLines
  · exact stressFreeStratumIsTieFree_threeLines_of_chart hThreeLines
  · exact stressFreeStratumIsTieFree_graphicKFour_of_chart hGraphicKFour

/-- **THE RANK-THREE HINGE FROM FIVE CHARTS.**  The standing enumeration input
plus tie-freeness of the five charts gives the stress-free hinge at six labels
and rank three.  No design-level quantifier survives on the chart side. -/
theorem stressFreeHingeHoldsSixThree_of_fiveCharts
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hLineFree : ∀ param : ℝ × ℝ × ℝ × ℝ, IsAdmissibleLineFreeParameter param →
      DirectionChartIsTieFree (lineFreeDirection param))
    (hOneLine : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param))
    (hTwoMeetingLines : ∀ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param →
      DirectionChartIsTieFree (twoMeetingLinesDirection param))
    (hThreeLines : ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide →
      DirectionChartIsTieFree (threeLinesDirection slide))
    (hGraphicKFour : DirectionChartIsTieFree kFourDirection) :
    StressFreeHingeHoldsSixThree :=
  stressFreeHingeHoldsSixThree_of_residualFamilies hcomplete
    (stressFreeResidualFamiliesSix_tieFree_of_charts hLineFree hOneLine
      hTwoMeetingLines hThreeLines hGraphicKFour)

/-! ## The atlas, as one object -/

/-- A point of the five-piece atlas of the stress-free residual: an entry of
`Gtz.stressFreeResidualFamiliesSix` together with a parameter for its chart. -/
inductive StressFreeChartPoint where
  /-- Entry `#1`, the line-free cell, four parameters. -/
  | lineFree (param : ℝ × ℝ × ℝ × ℝ) : StressFreeChartPoint
  /-- Entry `#2`, one three-point line, three parameters. -/
  | oneLine (param : ℝ × ℝ × ℝ) : StressFreeChartPoint
  /-- Entry `#3`, two meeting three-point lines, two parameters. -/
  | twoMeetingLines (param : ℝ × ℝ) : StressFreeChartPoint
  /-- Entry `#4`, three three-point lines, one parameter. -/
  | threeLines (slide : ℝ) : StressFreeChartPoint
  /-- Entry `#5`, `M(K4)`, rigid. -/
  | graphicKFour : StressFreeChartPoint

/-- The six directions of an atlas point. -/
def StressFreeChartPoint.direction : StressFreeChartPoint → (Fin 6 → (Fin 3 → ℝ))
  | .lineFree param => lineFreeDirection param
  | .oneLine param => oneLineDirection param
  | .twoMeetingLines param => twoMeetingLinesDirection param
  | .threeLines slide => threeLinesDirection slide
  | .graphicKFour => kFourDirection

/-- The admissible region of the piece an atlas point lies in.  The `M(K4)`
piece is a single rigid point, so its region is everything. -/
def StressFreeChartPoint.IsAdmissible : StressFreeChartPoint → Prop
  | .lineFree param => IsAdmissibleLineFreeParameter param
  | .oneLine param => IsAdmissibleOneLineParameter param
  | .twoMeetingLines param => IsAdmissibleTwoMeetingLinesParameter param
  | .threeLines slide => IsAdmissibleThreeLinesParameter slide
  | .graphicKFour => True

/-- The moduli count of the piece an atlas point lies in.  The five values are
`4, 3, 2, 1, 0`, one for each line count `k` of the entry, and the count is
`4 - k` at every entry. -/
def StressFreeChartPoint.moduli : StressFreeChartPoint → ℕ
  | .lineFree _ => 4
  | .oneLine _ => 3
  | .twoMeetingLines _ => 2
  | .threeLines _ => 1
  | .graphicKFour => 0

/-- The line count of the entry an atlas point lies in. -/
def StressFreeChartPoint.lineCount : StressFreeChartPoint → ℕ
  | .lineFree _ => 0
  | .oneLine _ => 1
  | .twoMeetingLines _ => 2
  | .threeLines _ => 3
  | .graphicKFour => 4

/-- **THE MODULI LADDER.**  Each line of the pattern costs exactly one modulus,
across the whole atlas.  Four lines leave a rigid point, and no lines leave the
widest cell. -/
theorem StressFreeChartPoint.moduli_add_lineCount (point : StressFreeChartPoint) :
    point.moduli + point.lineCount = 4 := by
  cases point <;> rfl

set_option maxHeartbeats 1000000 in
/-- **THE RANK-THREE HINGE FROM ONE ATLAS STATEMENT.**  The stress-free hinge at
six labels and rank three follows from the enumeration input plus a SINGLE
universally quantified statement over a five-piece atlas of total dimension
four.  This is the whole chart programme, spent at once. -/
theorem stressFreeHingeHoldsSixThree_of_atlas
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hatlas : ∀ point : StressFreeChartPoint, point.IsAdmissible →
      DirectionChartIsTieFree point.direction) :
    StressFreeHingeHoldsSixThree :=
  stressFreeHingeHoldsSixThree_of_fiveCharts hcomplete
    (fun param hparam => hatlas (.lineFree param) hparam)
    (fun param hparam => hatlas (.oneLine param) hparam)
    (fun param hparam => hatlas (.twoMeetingLines param) hparam)
    (fun slide hslide => hatlas (.threeLines slide) hslide)
    (hatlas .graphicKFour trivial)

/-- The same, in residual-list form, for consumers that read the list. -/
theorem stressFreeResidualFamiliesSix_tieFree_of_atlas
    (hatlas : ∀ point : StressFreeChartPoint, point.IsAdmissible →
      DirectionChartIsTieFree point.direction) :
    ∀ lines ∈ stressFreeResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines) :=
  stressFreeResidualFamiliesSix_tieFree_of_charts
    (fun param hparam => hatlas (.lineFree param) hparam)
    (fun param hparam => hatlas (.oneLine param) hparam)
    (fun param hparam => hatlas (.twoMeetingLines param) hparam)
    (fun slide hslide => hatlas (.threeLines slide) hslide)
    (hatlas .graphicKFour trivial)

/-! ## Controls

The assembly would be worthless if the atlas were empty, if a piece were
unreachable, or if the five pieces did not exhaust the residual list. -/

/-- Every entry of the residual list is the pattern of exactly one atlas piece,
and the five pieces exhaust the list. -/
theorem stressFreeResidualFamiliesSix_eq_five :
    stressFreeResidualFamiliesSix
      = [ ([] : List (List (Fin 6)))
        , [[0, 1, 2]]
        , [[0, 1, 2], [0, 3, 4]]
        , [[0, 1, 2], [0, 3, 4], [1, 3, 5]]
        , [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]] ] := rfl

/-- The atlas is not a single point: the four positive-dimensional pieces carry
different moduli counts, so no two of them can be merged. -/
theorem StressFreeChartPoint.moduli_pairwise_ne :
    (StressFreeChartPoint.lineFree (0, 0, 0, 0)).moduli
        ≠ (StressFreeChartPoint.oneLine (0, 0, 0)).moduli
      ∧ (StressFreeChartPoint.oneLine (0, 0, 0)).moduli
        ≠ (StressFreeChartPoint.twoMeetingLines (0, 0)).moduli
      ∧ (StressFreeChartPoint.twoMeetingLines (0, 0)).moduli
        ≠ (StressFreeChartPoint.threeLines 0).moduli
      ∧ (StressFreeChartPoint.threeLines 0).moduli
        ≠ StressFreeChartPoint.graphicKFour.moduli := by
  refine ⟨by decide, by decide, by decide, by decide⟩

/-- The rigid piece is admissible with no side condition, so the atlas has at
least one point in every piece that needs none. -/
theorem StressFreeChartPoint.graphicKFour_isAdmissible :
    StressFreeChartPoint.graphicKFour.IsAdmissible := trivial

/-! ## The moment hypothesis, discharged on the whole atlas

`Gtz.posDef_massMoment_of_spanningTriple` turns a spanning triple of labels into
a positive definite mass moment matrix.  Every one of the five charts carries the
three coordinate axes among its six directions, so every one of the five gets the
moment hypothesis with NO admissibility side condition.  The corpus already
carried the `M(K4)` and three-lines cases.  The three remaining cases are here,
and the line-free one is the piece that could not exist before. -/

/-- The line-free chart's moment matrix is positive definite at every chart
point and every parameter: its labels zero, one and two are the coordinate
axes. -/
theorem posDef_massMoment_lineFreeDirection (param : ℝ × ℝ × ℝ × ℝ)
    (point : DirectionChartPoint 6) :
    (∑ label, point.mass label • atomMatrix (lineFreeDirection param label)).PosDef := by
  refine posDef_massMoment_of_spanningTriple (lineFreeDirection param) point.mass
    point.mass_pos 0 1 2 fun probeVec hfirst hsecond hthird => ?_
  simp only [lineFreeDirection, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hfirst hsecond hthird
  exact eq_zero_of_coordinates_eq_zero (by linarith) (by linarith) (by linarith)

/-- The one-line chart's moment matrix is positive definite at every chart point
and every parameter: its labels zero, one and three are the coordinate axes.

**#UNSPENT-KEY (tagged 2026-08-17, MEASURED).**  This lemma is the free
adapter that carries the whole mass-leverage handle onto the one-line chart, and
nobody has spent it that way.

`Gtz.chartMassMoment direction mass = ∑ label, mass label • atomMatrix
(direction label)` holds by `rfl` (`Gtz.chartMassMoment_eq`,
Gtz/Wave/ThreeLinesSlideElimination.lean:67).  So this theorem IS a proof of
`(chartMassMoment (oneLineDirection param) point.mass).PosDef`, with no glue and
no admissibility hypothesis.  That is the SOLE structural hypothesis of every
direction-generic leverage result:

* `Gtz.three_le_card_overLevered` (ThreeLinesSlideElimination.lean:283) — at
  least three labels are over-levered, at every chart point.
* `Gtz.weight_lt_chartMassLeverage_of_posDef_gap` (:341) — every label of a
  strictly dominating triple is over-levered.
* `Gtz.posDef_directionChartGap_of_dualStrict` (:428) — domination from one
  inequality, one completed square for each label.
* `Gtz.posDef_directionChartGap_of_leverageTrace` (:1223) — a triple whose
  leverage total beats two plus each of its three weights dominates strictly.
* `Gtz.sum_leverage_le_two_of_dependent` (:1182) — a dependent triple caps at
  two, which makes the line `{0,1,2}` invisible to the trace cell.

The three-lines chart spends all five through the one-term bridge
`Gtz.posDef_chartMassMoment_threeLines` (:864), which is literally
`posDef_massMoment_threeLinesDirection slide point`.  The one-line twin of that
bridge, and of the closure `Gtz.exists_posDef_threeLines_of_overLevered_triple`
(:1409), do NOT exist.  Each is a transcription with `threeLinesDirection slide`
replaced by `oneLineDirection param`.

TWO CAVEATS BEFORE ANYONE SPENDS THIS.  First,
`Gtz/Wave/ThreeLinesSlideElimination.lean` carries NO axiom pin in
`Gtz/Audit.lean`, although that file imports it at :1190.  So the module DOES
build, and the tree-wide zero-axiom guarantee still does not cover it.  Read its
header tag.  (SELF-CORRECTION, 2026-08-17: an earlier revision of this paragraph
said the module "is imported by NOTHING" and called it unbuilt.  That was FALSE.
The import sits in `Gtz.lean:6285` and in `Gtz/Audit.lean:1190`, committed at
2fbdf5d.  The false reading came from `rg` calls that ran outside the repository
root with `2>/dev/null` set, which turned three path errors into three silent
"zero hits".  Never measure a consumer count with stderr suppressed.)  Second,
that module cannot reach
`Gtz.oneLineDirection` through its own imports, so the composition belongs in a
NEW module that imports both.  No cycle results, because nothing imports the
leverage module today. -/
theorem posDef_massMoment_oneLineDirection (param : ℝ × ℝ × ℝ)
    (point : DirectionChartPoint 6) :
    (∑ label, point.mass label • atomMatrix (oneLineDirection param label)).PosDef := by
  refine posDef_massMoment_of_spanningTriple (oneLineDirection param) point.mass
    point.mass_pos 0 1 3 fun probeVec hfirst hsecond hthird => ?_
  simp only [oneLineDirection, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hfirst hsecond hthird
  exact eq_zero_of_coordinates_eq_zero (by linarith) (by linarith) (by linarith)

/-- The two-meeting-lines chart's moment matrix is positive definite at every
chart point and every parameter: its labels zero, one and three are the
coordinate axes. -/
theorem posDef_massMoment_twoMeetingLinesDirection (param : ℝ × ℝ)
    (point : DirectionChartPoint 6) :
    (∑ label, point.mass label
      • atomMatrix (twoMeetingLinesDirection param label)).PosDef := by
  refine posDef_massMoment_of_spanningTriple (twoMeetingLinesDirection param) point.mass
    point.mass_pos 0 1 3 fun probeVec hfirst hsecond hthird => ?_
  simp only [twoMeetingLinesDirection, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hfirst hsecond hthird
  exact eq_zero_of_coordinates_eq_zero (by linarith) (by linarith) (by linarith)

/-- **THE MOMENT HYPOTHESIS HOLDS ON THE WHOLE ATLAS**, at every point of every
piece, with no admissibility side condition anywhere. -/
theorem posDef_massMoment_atlas (point : StressFreeChartPoint)
    (chartPoint : DirectionChartPoint 6) :
    (∑ label, chartPoint.mass label • atomMatrix (point.direction label)).PosDef := by
  cases point with
  | lineFree param => exact posDef_massMoment_lineFreeDirection param chartPoint
  | oneLine param => exact posDef_massMoment_oneLineDirection param chartPoint
  | twoMeetingLines param =>
      exact posDef_massMoment_twoMeetingLinesDirection param chartPoint
  | threeLines slide => exact posDef_massMoment_threeLinesDirection slide chartPoint
  | graphicKFour => exact posDef_massMoment_kFourDirection chartPoint

/-! ## The atlas dissolves into one design-level statement

With the moment hypothesis free on every piece, the chart side of the problem
carries no content of its own.  What the whole five-piece atlas needs is the
design-level weak-to-strict upgrade, and that statement mentions no chart, no
parameter and no pattern. -/

/-- **THE ATLAS FROM ONE DESIGN-LEVEL UPGRADE.**  Every admissible point of the
atlas is tie-free as soon as every weakly dominated design carries a strictly
dominating triple. -/
theorem directionChartIsTieFree_atlas_of_designUpgrade
    (hupgrade : ∀ design : WeightedDesign 6 3,
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef)
    (point : StressFreeChartPoint) :
    DirectionChartIsTieFree point.direction :=
  directionChartIsTieFree_of_momentPosDef_of_designUpgrade point.direction
    (posDef_massMoment_atlas point) hupgrade

/-- The line-free chart alone, for consumers that work one cell at a time. -/
theorem directionChartIsTieFree_lineFree_of_designUpgrade (param : ℝ × ℝ × ℝ × ℝ)
    (hupgrade : ∀ design : WeightedDesign 6 3,
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    DirectionChartIsTieFree (lineFreeDirection param) :=
  directionChartIsTieFree_atlas_of_designUpgrade hupgrade (.lineFree param)

/-- The one-line chart alone. -/
theorem directionChartIsTieFree_oneLine_of_designUpgrade (param : ℝ × ℝ × ℝ)
    (hupgrade : ∀ design : WeightedDesign 6 3,
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    DirectionChartIsTieFree (oneLineDirection param) :=
  directionChartIsTieFree_atlas_of_designUpgrade hupgrade (.oneLine param)

/-- The two-meeting-lines chart alone. -/
theorem directionChartIsTieFree_twoMeetingLines_of_designUpgrade (param : ℝ × ℝ)
    (hupgrade : ∀ design : WeightedDesign 6 3,
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    DirectionChartIsTieFree (twoMeetingLinesDirection param) :=
  directionChartIsTieFree_atlas_of_designUpgrade hupgrade (.twoMeetingLines param)

/-- The residual list from one design-level upgrade. -/
theorem stressFreeResidualFamiliesSix_tieFree_of_designUpgrade
    (hupgrade : ∀ design : WeightedDesign 6 3,
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    ∀ lines ∈ stressFreeResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines) :=
  stressFreeResidualFamiliesSix_tieFree_of_atlas
    fun point _ => directionChartIsTieFree_atlas_of_designUpgrade hupgrade point

/-- **THE RANK-THREE HINGE FROM ONE DESIGN-LEVEL UPGRADE.**  The stress-free
hinge at six labels and rank three follows from the enumeration input plus the
statement that every weakly dominated design carries a strictly dominating
triple.  No chart, no parameter and no pattern survives in the hypothesis. -/
theorem stressFreeHingeHoldsSixThree_of_designUpgrade
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hupgrade : ∀ design : WeightedDesign 6 3,
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef) :
    StressFreeHingeHoldsSixThree :=
  stressFreeHingeHoldsSixThree_of_atlas hcomplete
    fun point _ => directionChartIsTieFree_atlas_of_designUpgrade hupgrade point

/-- **THE RANK-THREE HINGE FROM ONE DETERMINANT SIGN.**  The sharpest form: at
every weakly dominated design, every live pair completes to a strictly positive
tie leg.  This spends the whole chart programme, the five coverings and the
moment discharge together, and leaves one sign of one discriminant.

**#BOGUS — THIS DOOR CANNOT OPEN.**  `Gtz.not_livePairTieResidual`
(Gtz/Wave/LivePairTieRefuter.lean:183) refutes the residual verbatim, at an exact
rational design that is itself strictly dominated.  Its heavy twin
`Gtz.stressFreeHingeHoldsSixThree_of_heavyLivePairTie`
(Gtz/Wave/ChartProgrammeHeavyResidual.lean:91) dies to the same witness, because
that witness carries weight `23/96` at label zero.
`Gtz.unopenableLivePairDoors` (Gtz/Wave/WiringSynonymClass.lean) records both. -/
theorem stressFreeHingeHoldsSixThree_of_livePairTie
    (hcomplete : LinearSpaceListIsComplete 6 linePatternListSix)
    (hresidual : ∀ design : WeightedDesign 6 3,
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
        IsLivePair design pivotLabel pairFirst →
        ∃ pairSecond : Fin 6, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
          ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) :
    StressFreeHingeHoldsSixThree :=
  stressFreeHingeHoldsSixThree_of_atlas hcomplete
    fun point _ => directionChartIsTieFree_of_momentPosDef_of_livePairTie point.direction
      (posDef_massMoment_atlas point) hresidual

end Gtz
