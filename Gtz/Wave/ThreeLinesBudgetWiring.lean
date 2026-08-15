import Gtz.Design.BudgetCoverCriterion

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spend the two budget cells in the three-lines registry residual

`Gtz.posDef_threeLines_vertexCell` and `Gtz.posDef_threeLines_freeCell`
turn nine positive allocation variables into strict chart gaps.  This file
names those two semialgebraic cells and removes them from the live A2
obligation.

The remaining proposition is equivalent to the preceding tenth-heavy A2
residual: a point inside either cell is closed by the budget certificate, and
a point outside both cells is handed to the new residual.  Thus this is a
formula sharpening, not a stronger sufficient condition.
-/

namespace Gtz

open Matrix Finset

/-- A positive `3 x 3` allocation used by both canonical three-lines cells. -/
structure ThreeLinesPositiveAllocation where
  uAA : ℝ
  uAB : ℝ
  uAC : ℝ
  uBA : ℝ
  uBB : ℝ
  uBC : ℝ
  uCA : ℝ
  uCB : ℝ
  uCC : ℝ
  uAA_pos : 0 < uAA
  uAB_pos : 0 < uAB
  uAC_pos : 0 < uAC
  uBA_pos : 0 < uBA
  uBB_pos : 0 < uBB
  uBC_pos : 0 < uBC
  uCA_pos : 0 < uCA
  uCB_pos : 0 < uCB
  uCC_pos : 0 < uCC

/-- The vertex cell is the exact collection of allocation inequalities consumed
by `Gtz.posDef_threeLines_vertexCell`. -/
def ThreeLinesVertexBudgetCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) : Prop :=
  ∃ allocation : ThreeLinesPositiveAllocation,
    point.mass 2 *
        (allocation.uAB * allocation.uAC + allocation.uAA * allocation.uAC)
      ≤ allocation.uAA * allocation.uAB * allocation.uAC ∧
    point.mass 4 *
        (allocation.uBB * allocation.uBC + allocation.uBA * allocation.uBB)
      ≤ allocation.uBA * allocation.uBB * allocation.uBC ∧
    point.mass 5 *
        (allocation.uCA * allocation.uCC +
          slide ^ 2 * (allocation.uCA * allocation.uCB))
      ≤ allocation.uCA * allocation.uCB * allocation.uCC ∧
    (allocation.uAA + allocation.uBA + allocation.uCA) * point.weight 0
      < point.mass 0 * (1 - point.weight 0) ∧
    (allocation.uAB + allocation.uBB + allocation.uCB) * point.weight 1
      < point.mass 1 * (1 - point.weight 1) ∧
    (allocation.uAC + allocation.uBC + allocation.uCC) * point.weight 3
      < point.mass 3 * (1 - point.weight 3)

/-- The free cell is the exact collection of allocation inequalities consumed
by `Gtz.posDef_threeLines_freeCell`. -/
def ThreeLinesFreeBudgetCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) : Prop :=
  ∃ allocation : ThreeLinesPositiveAllocation,
    point.mass 0 *
        (allocation.uAB * allocation.uAC +
          slide ^ 2 * (allocation.uAA * allocation.uAC) +
          allocation.uAA * allocation.uAB)
      ≤ (slide + 1) ^ 2 * (allocation.uAA * allocation.uAB * allocation.uAC) ∧
    point.mass 1 *
        (slide ^ 2 * (allocation.uBB * allocation.uBC) +
          slide ^ 2 * (allocation.uBA * allocation.uBC) +
          allocation.uBA * allocation.uBB)
      ≤ (slide + 1) ^ 2 * (allocation.uBA * allocation.uBB * allocation.uBC) ∧
    point.mass 3 *
        (allocation.uCB * allocation.uCC + allocation.uCA * allocation.uCC +
          allocation.uCA * allocation.uCB)
      ≤ (slide + 1) ^ 2 * (allocation.uCA * allocation.uCB * allocation.uCC) ∧
    (allocation.uAA + allocation.uBA + allocation.uCA) * point.weight 2
      < point.mass 2 * (1 - point.weight 2) ∧
    (allocation.uAB + allocation.uBB + allocation.uCB) * point.weight 4
      < point.mass 4 * (1 - point.weight 4) ∧
    (allocation.uAC + allocation.uBC + allocation.uCC) * point.weight 5
      < point.mass 5 * (1 - point.weight 5)

/-- Either canonical allocated Cauchy--Schwarz cell fires. -/
def ThreeLinesBudgetCellFires (slide : ℝ) (point : DirectionChartPoint 6) : Prop :=
  ThreeLinesVertexBudgetCellFires slide point ∨
    ThreeLinesFreeBudgetCellFires slide point

/-- The vertex allocation predicate produces the strict vertex triple. -/
theorem posDef_threeLines_vertexCell_of_fires (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesVertexBudgetCellFires slide point) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({0, 1, 3} : Finset (Fin 6))).PosDef := by
  obtain ⟨allocation, hbudgetTwo, hbudgetFour, hbudgetFive,
      hloadZero, hloadOne, hloadThree⟩ := hcell
  exact posDef_threeLines_vertexCell slide point.mass point.weight
    point.mass_pos point.weight_pos
    allocation.uAA_pos allocation.uAB_pos allocation.uAC_pos
    allocation.uBA_pos allocation.uBB_pos allocation.uBC_pos
    allocation.uCA_pos allocation.uCB_pos allocation.uCC_pos
    hbudgetTwo hbudgetFour hbudgetFive hloadZero hloadOne hloadThree

/-- The free allocation predicate produces the strict free triple. -/
theorem posDef_threeLines_freeCell_of_fires (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesFreeBudgetCellFires slide point) :
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      ({2, 4, 5} : Finset (Fin 6))).PosDef := by
  obtain ⟨allocation, hbudgetZero, hbudgetOne, hbudgetThree,
      hloadTwo, hloadFour, hloadFive⟩ := hcell
  exact posDef_threeLines_freeCell slide hadmissible.2 point.mass point.weight
    point.mass_pos point.weight_pos
    allocation.uAA_pos allocation.uAB_pos allocation.uAC_pos
    allocation.uBA_pos allocation.uBB_pos allocation.uBC_pos
    allocation.uCA_pos allocation.uCB_pos allocation.uCC_pos
    hbudgetZero hbudgetOne hbudgetThree hloadTwo hloadFour hloadFive

/-- Either budget cell supplies an explicit strict card-three chart gap. -/
theorem exists_posDef_threeLines_of_budgetCellFires (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesBudgetCellFires slide point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef := by
  rcases hcell with hvertex | hfree
  · exact ⟨{0, 1, 3}, by decide,
      posDef_threeLines_vertexCell_of_fires slide point hvertex⟩
  · exact ⟨{2, 4, 5}, by decide,
      posDef_threeLines_freeCell_of_fires slide hadmissible point hfree⟩

/-- The exact A2 residual after the all-light theorem, the parameter
fundamental domain, and both allocated budget cells have fired. -/
def ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      (∃ heavyLabel : Fin 6, 1 / 10 ≤ point.weight heavyLabel) →
      ¬ ThreeLinesBudgetCellFires slide point →
      (∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosSemidef) →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef

/-- Spend the two budget cells and reconstruct the preceding tenth-heavy A2
residual. -/
theorem chartTieFreeThreeLinesFundamentalDomainTenthHeavy_of_budgetBlind
    (hblind : ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind) :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavy := by
  intro slide hadmissible hfundamental point hheavy hweak
  by_cases hcell : ThreeLinesBudgetCellFires slide point
  · exact exists_posDef_threeLines_of_budgetCellFires slide hadmissible point hcell
  · exact hblind slide hadmissible hfundamental point hheavy hcell hweak

/-- The preceding tenth-heavy A2 residual restricts to the budget-blind
region. -/
theorem budgetBlindThreeLinesFundamentalDomain_of_tenthHeavy
    (hheavy : ChartTieFreeThreeLinesFundamentalDomainTenthHeavy) :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind := by
  intro slide hadmissible hfundamental point hweightHeavy _hcell hweak
  exact hheavy slide hadmissible hfundamental point hweightHeavy hweak

/-- Removing the two budget cells is an exact formula sharpening of A2. -/
theorem chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind_iff_tenthHeavy :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind ↔
      ChartTieFreeThreeLinesFundamentalDomainTenthHeavy :=
  ⟨chartTieFreeThreeLinesFundamentalDomainTenthHeavy_of_budgetBlind,
    budgetBlindThreeLinesFundamentalDomain_of_tenthHeavy⟩

/-- The budget-blind residual reconstructs the original public A2 statement. -/
theorem chartTieFreeThreeLinesFundamentalDomain_of_budgetBlind
    (hblind : ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind) :
    ChartTieFreeThreeLinesFundamentalDomain :=
  chartTieFreeThreeLinesFundamentalDomain_of_tenthHeavy
    (chartTieFreeThreeLinesFundamentalDomainTenthHeavy_of_budgetBlind hblind)

/-- The original public A2 statement restricts to the budget-blind residual. -/
theorem budgetBlindThreeLinesFundamentalDomain_of_chartTieFree
    (hchart : ChartTieFreeThreeLinesFundamentalDomain) :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind :=
  budgetBlindThreeLinesFundamentalDomain_of_tenthHeavy
    (tenthHeavyThreeLinesFundamentalDomain_of_chartTieFree hchart)

/-- The final budget-blind A2 formula is equivalent to its public statement. -/
theorem chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind_iff :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind ↔
      ChartTieFreeThreeLinesFundamentalDomain :=
  ⟨chartTieFreeThreeLinesFundamentalDomain_of_budgetBlind,
    budgetBlindThreeLinesFundamentalDomain_of_chartTieFree⟩

end Gtz
