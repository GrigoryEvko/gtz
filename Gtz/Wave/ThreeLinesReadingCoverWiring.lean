import Gtz.Wave.ThreeLinesBudgetWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spend the reading-cover cell in the three-lines residual

The allocated budget cells and the chart reading-cover criterion are different
strict-gap producers.  The former assigns coordinate budgets to one of two
canonical triples.  The latter asks for a card-three set containing a maximal
kappa reading at every probe and then uses the weighted-mean reading law.

This file names the reading-cover cell and removes it from the already
budget-blind A2 obligation.  No disjointness between the cells is claimed or
needed: splitting first on the budget cells and then on the reading-cover cell
gives an exact formula equivalence with the public A2 statement.
-/

namespace Gtz

open Matrix Finset

/-- A chart point enters the reading-cover cell when one card-three selection
contains a maximal kappa reading at every probe. -/
def ThreeLinesReadingCoverCellFires (slide : ℝ)
    (point : DirectionChartPoint 6) : Prop :=
  ∃ selected : Finset (Fin 6), selected.card = 3 ∧
    ∀ probe : Fin 3 → ℝ, ∃ good ∈ selected, ∀ label,
      point.mass label / point.weight label
          * (threeLinesDirection slide label ⬝ᵥ probe) ^ 2
        ≤ point.mass good / point.weight good
          * (threeLinesDirection slide good ⬝ᵥ probe) ^ 2

/-- The reading-cover cell supplies its selected strict card-three gap. -/
theorem exists_posDef_threeLines_of_readingCoverCellFires (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hcell : ThreeLinesReadingCoverCellFires slide point) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosDef := by
  obtain ⟨selected, hcard, hcover⟩ := hcell
  exact ⟨selected, hcard,
    posDef_directionChartGap_threeLines_of_readingCover slide point hcard hcover⟩

/-- The exact A2 residual after the all-light theorem, parameter inversion,
both allocated budget cells, and the reading-cover cell have fired. -/
def ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      (∃ heavyLabel : Fin 6, 1 / 10 ≤ point.weight heavyLabel) →
      ¬ ThreeLinesBudgetCellFires slide point →
      ¬ ThreeLinesReadingCoverCellFires slide point →
      (∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosSemidef) →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef

/-- Spend the reading-cover cell and reconstruct the preceding budget-blind A2
residual. -/
theorem chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind_of_budgetReadingBlind
    (hblind : ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind) :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind := by
  intro slide hadmissible hfundamental point hheavy hbudgetBlind hweak
  by_cases hreading : ThreeLinesReadingCoverCellFires slide point
  · exact exists_posDef_threeLines_of_readingCoverCellFires slide point hreading
  · exact hblind slide hadmissible hfundamental point hheavy hbudgetBlind hreading hweak

/-- The budget-blind residual restricts to points outside the reading-cover
cell. -/
theorem budgetReadingBlindThreeLinesFundamentalDomain_of_budgetBlind
    (hblind : ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind) :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind := by
  intro slide hadmissible hfundamental point hheavy hbudgetBlind _hreading hweak
  exact hblind slide hadmissible hfundamental point hheavy hbudgetBlind hweak

/-- Removing the reading-cover cell is an exact sharpening of the budget-blind
A2 formula. -/
theorem chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind_iff_budgetBlind :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind ↔
      ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind :=
  ⟨chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind_of_budgetReadingBlind,
    budgetReadingBlindThreeLinesFundamentalDomain_of_budgetBlind⟩

/-- The combined blind residual reconstructs the original public A2
statement. -/
theorem chartTieFreeThreeLinesFundamentalDomain_of_budgetReadingBlind
    (hblind : ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind) :
    ChartTieFreeThreeLinesFundamentalDomain :=
  chartTieFreeThreeLinesFundamentalDomain_of_budgetBlind
    (chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetBlind_of_budgetReadingBlind hblind)

/-- The original public A2 statement restricts to the combined blind
residual. -/
theorem budgetReadingBlindThreeLinesFundamentalDomain_of_chartTieFree
    (hchart : ChartTieFreeThreeLinesFundamentalDomain) :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind :=
  budgetReadingBlindThreeLinesFundamentalDomain_of_budgetBlind
    (budgetBlindThreeLinesFundamentalDomain_of_chartTieFree hchart)

/-- The final budget-and-reading-blind A2 formula is equivalent to its public
statement. -/
theorem chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind_iff :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind ↔
      ChartTieFreeThreeLinesFundamentalDomain :=
  ⟨chartTieFreeThreeLinesFundamentalDomain_of_budgetReadingBlind,
    budgetReadingBlindThreeLinesFundamentalDomain_of_chartTieFree⟩

end Gtz
