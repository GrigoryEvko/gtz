import Gtz.Design.UnsignedTraceCell
import Gtz.Wave.ThreeLinesUnsignedCycleWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spend the unsigned trace cells in the three-lines residual

The generic unsigned trace theorem was first consumed only by the K4 gauge
star.  The two three-lines expansions already landed for the vertex triple
`{0,1,3}` and the free triple `{2,4,5}` satisfy the same interface.  This file
specializes the one-inequality trace certificate at both triples and removes
their union from the exact A2 residual.

The resulting formula is equivalent to the preceding unsigned-minor-blind A2
formula.  A trace cell gives an explicit strict triple; outside both trace
cells the new residual applies.  No total coverage statement is asserted.
-/

namespace Gtz

open Matrix Finset

/-! ## The two trace cells -/

/-- The one-inequality unsigned trace certificate at the vertex triple
`{0,1,3}`. -/
def ThreeLinesUnsignedVertexTraceCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) : Prop :=
  ∃ slideBound floorZero floorOne floorThree : ℝ,
    |slide| ≤ slideBound ∧
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1) ∧
    floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3) ∧
    0 < floorZero ∧ 0 < floorOne ∧ 0 < floorThree ∧
    point.mass 2 * (floorOne * floorThree + floorZero * floorThree)
        + point.mass 4 * (floorOne * floorThree + floorZero * floorOne)
        + point.mass 5 * (floorZero * floorThree
          + slideBound ^ 2 * (floorZero * floorOne))
      < floorZero * (floorOne * floorThree)

/-- The one-inequality unsigned trace certificate at the free triple
`{2,4,5}`.  The three demand variables clear the common `(slide+1)^2`
denominator exactly as in the landed unsigned-minor cell. -/
def ThreeLinesUnsignedFreeTraceCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) : Prop :=
  ∃ slideBound demandZero demandOne demandThree floorTwo floorFour floorFive : ℝ,
    |slide| ≤ slideBound ∧
    point.mass 0 ≤ demandZero * (slide + 1) ^ 2 ∧
    point.mass 1 ≤ demandOne * (slide + 1) ^ 2 ∧
    point.mass 3 ≤ demandThree * (slide + 1) ^ 2 ∧
    floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorTwo ∧ 0 < floorFour ∧ 0 < floorFive ∧
    demandZero * (floorFour * floorFive
          + slideBound ^ 2 * (floorTwo * floorFive) + floorTwo * floorFour)
        + demandOne * (slideBound ^ 2 * (floorFour * floorFive)
          + slideBound ^ 2 * (floorTwo * floorFive) + floorTwo * floorFour)
        + demandThree * (floorFour * floorFive + floorTwo * floorFive
          + floorTwo * floorFour)
      < floorTwo * (floorFour * floorFive)

/-- Either newly available three-lines trace cell fires. -/
def ThreeLinesUnsignedTraceCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) : Prop :=
  ThreeLinesUnsignedVertexTraceCellFires slide point ∨
    ThreeLinesUnsignedFreeTraceCellFires slide point

/-- The two preceding unsigned-minor cells together with the two new trace
cells. -/
def ThreeLinesExpandedUnsignedCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) : Prop :=
  ThreeLinesUnsignedCycleCellFires slide point ∨
    ThreeLinesUnsignedTraceCellFires slide point

/-! ## Trace dispatchers -/

/-- The vertex trace cell supplies the strict vertex triple. -/
theorem posDef_threeLines_vertexCell_of_unsignedTraceFires (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesUnsignedVertexTraceCellFires slide point) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({0, 1, 3} : Finset (Fin 6))).PosDef := by
  obtain ⟨slideBound, floorZero, floorOne, floorThree, hslideBound,
    hfloorZero, hfloorOne, hfloorThree, hposZero, hposOne, hposThree, htrace⟩ := hcell
  refine posDef_directionChartGap_of_unsignedCycleTrace (threeLinesDirection slide)
    point.mass point.weight point.mass_pos point.weight_pos
    (selA := 0) (selB := 1) (selC := 3) (outA := 2) (outB := 4) (outC := 5)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (threeLinesDirection_span slide)
    (scaleA := 1) (scaleB := 1) (scaleC := 1) one_ne_zero one_ne_zero one_ne_zero
    (threeLines_expansion_insertTwo slide) (threeLines_expansion_insertFour slide)
    (threeLines_expansion_insertFive slide)
    (fAA := 1) (fAB := 1) (fAC := 0) (fBA := 1) (fBB := 0) (fBC := 1)
    (fCA := 0) (fCB := 1) (fCC := slideBound)
    (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hslideBound
    (demandA := point.mass 2) (demandB := point.mass 4) (demandC := point.mass 5)
    (le_of_eq (by ring)) (le_of_eq (by ring)) (le_of_eq (by ring))
    hfloorZero hfloorOne hfloorThree hposZero hposOne hposThree ?_
  simpa using htrace

/-- The free trace cell supplies the strict free triple. -/
theorem posDef_threeLines_freeCell_of_unsignedTraceFires (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesUnsignedFreeTraceCellFires slide point) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({2, 4, 5} : Finset (Fin 6))).PosDef := by
  obtain ⟨slideBound, demandZero, demandOne, demandThree,
    floorTwo, floorFour, floorFive, hslideBound,
    hdemandZero, hdemandOne, hdemandThree, hfloorTwo, hfloorFour, hfloorFive,
    hposTwo, hposFour, hposFive, htrace⟩ := hcell
  have hsucc : slide + 1 ≠ 0 := fun hzero => hadmissible.2 (by linarith)
  refine posDef_directionChartGap_of_unsignedCycleTrace (threeLinesDirection slide)
    point.mass point.weight point.mass_pos point.weight_pos
    (selA := 2) (selB := 4) (selC := 5) (outA := 0) (outB := 1) (outC := 3)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide)
    (threeLinesDirection_span slide)
    (scaleA := slide + 1) (scaleB := slide + 1) (scaleC := slide + 1)
    hsucc hsucc hsucc
    (threeLines_expansion_vertexZero slide) (threeLines_expansion_vertexOne slide)
    (threeLines_expansion_vertexThree slide)
    (fAA := 1) (fAB := slideBound) (fAC := 1)
    (fBA := slideBound) (fBB := slideBound) (fBC := 1)
    (fCA := 1) (fCB := 1) (fCC := 1)
    (by norm_num) hslideBound (by norm_num) hslideBound
    (by simpa using hslideBound) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
    hdemandZero hdemandOne hdemandThree hfloorTwo hfloorFour hfloorFive
    hposTwo hposFour hposFive ?_
  simpa using htrace

/-- Either trace cell supplies an explicit strict card-three chart gap. -/
theorem exists_posDef_threeLines_of_unsignedTraceCellFires (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesUnsignedTraceCellFires slide point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef := by
  rcases hcell with hvertex | hfree
  · exact ⟨{0, 1, 3}, by decide,
      posDef_threeLines_vertexCell_of_unsignedTraceFires slide point hvertex⟩
  · exact ⟨{2, 4, 5}, by decide,
      posDef_threeLines_freeCell_of_unsignedTraceFires slide hadmissible point hfree⟩

/-- Any cell in the expanded unsigned atlas supplies a strict triple. -/
theorem exists_posDef_threeLines_of_expandedUnsignedCellFires (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesExpandedUnsignedCellFires slide point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef := by
  rcases hcell with hminor | htrace
  · exact exists_posDef_threeLines_of_unsignedCycleCellFires
      slide hadmissible point hminor
  · exact exists_posDef_threeLines_of_unsignedTraceCellFires
      slide hadmissible point htrace

/-! ## The exact smaller A2 residual -/

/-- A2 outside the allocated budget cell, max-reading cell, all four unsigned
cells, and the three dependent line triples. -/
def ChartTieFreeThreeLinesFundamentalDomainBudgetReadingTraceBlindOffLines : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      ¬ ThreeLinesBudgetCellFires slide point →
      ¬ ThreeLinesReadingCoverCellFires slide point →
      ¬ ThreeLinesExpandedUnsignedCellFires slide point →
      (∃ selected : Finset (Fin 6), ThreeLinesOffLinesWeakTriple slide point selected) →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef

/-- Spend both trace cells and reconstruct the preceding unsigned-minor-blind
A2 residual. -/
theorem chartTieFreeThreeLinesUnsignedBlindOffLines_of_traceBlind
    (hblind : ChartTieFreeThreeLinesFundamentalDomainBudgetReadingTraceBlindOffLines) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines := by
  intro slide hadmissible hfundamental point hbudgetBlind hreadingBlind
    hminorBlind hweak
  rcases Classical.em (ThreeLinesExpandedUnsignedCellFires slide point) with
    hcell | hcell
  · exact exists_posDef_threeLines_of_expandedUnsignedCellFires
      slide hadmissible point hcell
  · exact hblind slide hadmissible hfundamental point hbudgetBlind hreadingBlind hcell hweak

/-- The preceding unsigned-minor-blind residual restricts to the complement of
the expanded unsigned atlas. -/
theorem traceBlindThreeLinesFundamentalDomain_of_unsignedBlind
    (hblind : ChartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingTraceBlindOffLines := by
  intro slide hadmissible hfundamental point hbudgetBlind hreadingBlind
    hnotExpanded hweak
  have hnotMinor : ¬ ThreeLinesUnsignedCycleCellFires slide point := by
    intro hminor
    exact hnotExpanded (Or.inl hminor)
  exact hblind slide hadmissible hfundamental point hbudgetBlind hreadingBlind
    hnotMinor hweak

/-- Removing both trace cells is an exact formula sharpening. -/
theorem chartTieFreeThreeLinesFundamentalDomainBudgetReadingTraceBlindOffLines_iff_unsignedBlind :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingTraceBlindOffLines ↔
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines :=
  ⟨chartTieFreeThreeLinesUnsignedBlindOffLines_of_traceBlind,
    traceBlindThreeLinesFundamentalDomain_of_unsignedBlind⟩

/-- The trace-blind residual remains equivalent to the public A2 statement. -/
theorem chartTieFreeThreeLinesFundamentalDomainBudgetReadingTraceBlindOffLines_iff :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingTraceBlindOffLines ↔
      ChartTieFreeThreeLinesFundamentalDomain :=
  chartTieFreeThreeLinesFundamentalDomainBudgetReadingTraceBlindOffLines_iff_unsignedBlind.trans
    chartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines_iff

end Gtz
