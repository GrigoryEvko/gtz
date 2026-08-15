import Gtz.Design.UnsignedCycleCells
import Gtz.Wave.ThreeLinesOffLinesWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spend the unsigned-cycle cells in the three-lines residual

The unsigned-cycle engine also has two three-lines instances, at the vertex
triple `{0, 1, 3}` and the free triple `{2, 4, 5}`.  Their hypotheses are
allocation-free leading-minor inequalities in the chart moduli.  This file
packages those hypotheses, dispatches each cell to its named strict triple,
and removes both cells from the already budget-, reading-, and line-blind A2
residual.

The new formula also omits the `1 / 10` chart-heavy antecedent.  That premise
is automatic for every six-label chart point because the positive weights sum
to one.  Both directions to the preceding A2 formula and to the public chart
statement are proved.  No inhabitant of the final complement is asserted.
-/

namespace Gtz

open Matrix Finset

/-! ## Named unsigned-cycle cells -/

/-- The exact allocation-free minor hypotheses for the vertex triple
`{0, 1, 3}`. -/
def ThreeLinesUnsignedVertexCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) : Prop :=
  ∃ slideBound floorZero floorOne floorThree : ℝ,
    |slide| ≤ slideBound ∧
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1) ∧
    floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3) ∧
    0 < floorZero - (point.mass 2 + point.mass 4) ∧
    0 < (floorZero - (point.mass 2 + point.mass 4))
        * (floorOne - (point.mass 2 + point.mass 5)) - point.mass 2 ^ 2 ∧
    0 < (floorZero - (point.mass 2 + point.mass 4))
          * (floorOne - (point.mass 2 + point.mass 5))
          * (floorThree - (point.mass 4 + point.mass 5 * slideBound ^ 2))
        - (floorZero - (point.mass 2 + point.mass 4))
          * (point.mass 5 * slideBound) ^ 2
        - point.mass 2 ^ 2
          * (floorThree - (point.mass 4 + point.mass 5 * slideBound ^ 2))
        - 2 * point.mass 2 * point.mass 4 * (point.mass 5 * slideBound)
        - point.mass 4 ^ 2 * (floorOne - (point.mass 2 + point.mass 5))

/-- The exact allocation-free minor hypotheses for the free triple
`{2, 4, 5}`. -/
def ThreeLinesUnsignedFreeCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) : Prop :=
  ∃ slideBound demandZero demandOne demandThree
      floorTwo floorFour floorFive
      entryAA entryAB entryAC entryBB entryBC entryCC : ℝ,
    |slide| ≤ slideBound ∧
    point.mass 0 ≤ demandZero * (slide + 1) ^ 2 ∧
    point.mass 1 ≤ demandOne * (slide + 1) ^ 2 ∧
    point.mass 3 ≤ demandThree * (slide + 1) ^ 2 ∧
    floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    entryAA = floorTwo
      - (demandZero + demandOne * slideBound ^ 2 + demandThree) ∧
    entryBB = floorFour
      - (demandZero * slideBound ^ 2 + demandOne * slideBound ^ 2 + demandThree) ∧
    entryCC = floorFive - (demandZero + demandOne + demandThree) ∧
    entryAB = -(demandZero * slideBound + demandOne * slideBound ^ 2 + demandThree) ∧
    entryAC = -(demandZero + demandOne * slideBound + demandThree) ∧
    entryBC = -(demandZero * slideBound + demandOne * slideBound + demandThree) ∧
    0 < entryAA ∧
    0 < entryAA * entryBB - entryAB ^ 2 ∧
    0 < entryAA * entryBB * entryCC - entryAA * entryBC ^ 2
      - entryAB ^ 2 * entryCC + 2 * entryAB * entryAC * entryBC
      - entryAC ^ 2 * entryBB

/-- Either allocation-free three-lines cycle cell fires. -/
def ThreeLinesUnsignedCycleCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) : Prop :=
  ThreeLinesUnsignedVertexCellFires slide point ∨
    ThreeLinesUnsignedFreeCellFires slide point

/-! ## Cell dispatchers -/

/-- The unsigned vertex cell supplies the strict vertex triple. -/
theorem posDef_threeLines_vertexCell_of_unsignedFires (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesUnsignedVertexCellFires slide point) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({0, 1, 3} : Finset (Fin 6))).PosDef := by
  obtain ⟨slideBound, floorZero, floorOne, floorThree, hslideBound,
    hfloorZero, hfloorOne, hfloorThree, hcorner, hminorTwo, hminorDet⟩ := hcell
  exact posDef_threeLines_vertexCellMinors slide point.mass point.weight
    point.mass_pos point.weight_pos hslideBound hfloorZero hfloorOne hfloorThree
    hcorner hminorTwo hminorDet

/-- The unsigned free cell supplies the strict free triple. -/
theorem posDef_threeLines_freeCell_of_unsignedFires (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesUnsignedFreeCellFires slide point) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({2, 4, 5} : Finset (Fin 6))).PosDef := by
  obtain ⟨slideBound, demandZero, demandOne, demandThree,
    floorTwo, floorFour, floorFive, entryAA, entryAB, entryAC, entryBB, entryBC, entryCC,
    hslideBound, hdemandZero, hdemandOne, hdemandThree,
    hfloorTwo, hfloorFour, hfloorFive,
    hentryAA, hentryBB, hentryCC, hentryAB, hentryAC, hentryBC,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact posDef_threeLines_freeCellMinors slide hadmissible.2 point.mass point.weight
    point.mass_pos point.weight_pos hslideBound
    hdemandZero hdemandOne hdemandThree hfloorTwo hfloorFour hfloorFive
    hentryAA hentryBB hentryCC hentryAB hentryAC hentryBC
    hcorner hminorTwo hminorDet

/-- Either unsigned cell supplies an explicit strict card-three chart gap. -/
theorem exists_posDef_threeLines_of_unsignedCycleCellFires (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesUnsignedCycleCellFires slide point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef := by
  rcases hcell with hvertex | hfree
  · exact ⟨{0, 1, 3}, by decide,
      posDef_threeLines_vertexCell_of_unsignedFires slide point hvertex⟩
  · exact ⟨{2, 4, 5}, by decide,
      posDef_threeLines_freeCell_of_unsignedFires slide hadmissible point hfree⟩

/-! ## The exact smaller A2 residual -/

/-- The A2 residual after both unsigned cells have fired.  It remains outside
the allocated budget and max-reading cells, and its weak witness is one of the
seventeen off-line triples.  The chart-heavy premise is omitted as automatic. -/
def ChartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      ¬ ThreeLinesBudgetCellFires slide point →
      ¬ ThreeLinesReadingCoverCellFires slide point →
      ¬ ThreeLinesUnsignedCycleCellFires slide point →
      (∃ selected : Finset (Fin 6), ThreeLinesOffLinesWeakTriple slide point selected) →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef

/-- Spend the two unsigned cells and reconstruct the preceding off-lines A2
residual. -/
theorem chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines_of_unsignedBlind
    (hblind :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines) :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines := by
  intro slide hadmissible hfundamental point _hheavy hbudgetBlind hreadingBlind hweak
  rcases Classical.em (ThreeLinesUnsignedCycleCellFires slide point) with hcell | hcell
  · exact exists_posDef_threeLines_of_unsignedCycleCellFires
      slide hadmissible point hcell
  · exact hblind slide hadmissible hfundamental point hbudgetBlind hreadingBlind hcell hweak

/-- The preceding off-lines formula restricts to the unsigned-cell complement.
The chart weight sum supplies its formerly explicit heavy witness. -/
theorem unsignedBlindThreeLinesFundamentalDomain_of_offLines
    (hoffLines :
      ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines := by
  intro slide hadmissible hfundamental point hbudgetBlind hreadingBlind
    _hunsignedBlind hweak
  exact hoffLines slide hadmissible hfundamental point
    (directionChartPoint_exists_tenthHeavy point) hbudgetBlind hreadingBlind hweak

/-- Removing both unsigned cells and the redundant chart-heavy gate is exactly
equivalent to the preceding off-lines A2 formula. -/
theorem chartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines_iff_offLines :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines ↔
      ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines :=
  ⟨chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines_of_unsignedBlind,
    unsignedBlindThreeLinesFundamentalDomain_of_offLines⟩

/-- The final unsigned-cell-blind formula is equivalent to the public A2
statement. -/
theorem chartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines_iff :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines ↔
      ChartTieFreeThreeLinesFundamentalDomain :=
  chartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines_iff_offLines.trans
    chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines_iff

/-- The unsigned-cell-blind residual reconstructs the public A2 statement. -/
theorem chartTieFreeThreeLinesFundamentalDomain_of_unsignedBlind
    (hblind :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingUnsignedBlindOffLines) :
    ChartTieFreeThreeLinesFundamentalDomain :=
  chartTieFreeThreeLinesFundamentalDomain_of_offLines
    (chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines_of_unsignedBlind
      hblind)

end Gtz
