import Gtz.Wave.ThreeLinesReadingCoverWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Remove the three dependent lines from the A2 weak antecedent

The three-lines chart has twenty card-three subsets, but its three named lines
can never even be positive semidefinite: a normal-axis probe reads a strictly
negative sum of outside masses.  This file spends those three landed
exclusions after the budget and max-reading cells have fired.

The resulting A2 residual asks for weak domination only through one of the
seventeen off-line triples.  Both directions back to the preceding residual
and to the public chart statement are proved, so this is an exact finite
antecedent reduction.
-/

namespace Gtz

open Matrix Finset

/-- A weak card-three chart witness distinct from each of the three dependent
lines. -/
def ThreeLinesOffLinesWeakTriple (slide : ℝ) (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) : Prop :=
  selected.card = 3 ∧
    selected ≠ ({0, 1, 2} : Finset (Fin 6)) ∧
    selected ≠ ({0, 3, 4} : Finset (Fin 6)) ∧
    selected ≠ ({1, 3, 5} : Finset (Fin 6)) ∧
    (directionChartGap (threeLinesDirection slide) point.mass point.weight
      selected).PosSemidef

/-- Every weak card-three witness on the three-lines chart is one of the
seventeen off-line triples. -/
theorem exists_threeLinesOffLinesWeakTriple_of_exists_weak (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hweak : ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosSemidef) :
    ∃ selected : Finset (Fin 6), ThreeLinesOffLinesWeakTriple slide point selected := by
  obtain ⟨selected, hcard, hpos⟩ := hweak
  have hweightNe : ∀ label, point.weight label ≠ 0 :=
    fun label => ne_of_gt (point.weight_pos label)
  have hfirst : selected ≠ ({0, 1, 2} : Finset (Fin 6)) := by
    intro hselected
    subst selected
    exact (directionChartGap_threeLines_firstLine_not_posSemidef slide point.mass point.weight
      hweightNe (point.mass_pos 3) (point.mass_pos 4) (le_of_lt (point.mass_pos 5))) hpos
  have hsecond : selected ≠ ({0, 3, 4} : Finset (Fin 6)) := by
    intro hselected
    subst selected
    exact (directionChartGap_threeLines_secondLine_not_posSemidef slide point.mass point.weight
      hweightNe (point.mass_pos 1) (point.mass_pos 2) (point.mass_pos 5)) hpos
  have hthird : selected ≠ ({1, 3, 5} : Finset (Fin 6)) := by
    intro hselected
    subst selected
    exact (directionChartGap_threeLines_thirdLine_not_posSemidef slide point.mass point.weight
      hweightNe (point.mass_pos 0) (point.mass_pos 2) (point.mass_pos 4)) hpos
  exact ⟨selected, hcard, hfirst, hsecond, hthird, hpos⟩

/-- Forgetting the three exclusions recovers an ordinary weak card-three
witness. -/
theorem exists_weak_of_exists_threeLinesOffLinesWeakTriple (slide : ℝ)
    (point : DirectionChartPoint 6)
    (hweak : ∃ selected : Finset (Fin 6), ThreeLinesOffLinesWeakTriple slide point selected) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection slide) point.mass point.weight
        selected).PosSemidef := by
  obtain ⟨selected, hcard, _hfirst, _hsecond, _hthird, hpos⟩ := hweak
  exact ⟨selected, hcard, hpos⟩

/-- The exact A2 residual after all-light points, parameter inversion, the two
budget cells, the reading-cover cell, and all three dependent weak witnesses
have been removed. -/
def ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      (∃ heavyLabel : Fin 6, 1 / 10 ≤ point.weight heavyLabel) →
      ¬ ThreeLinesBudgetCellFires slide point →
      ¬ ThreeLinesReadingCoverCellFires slide point →
      (∃ selected : Finset (Fin 6), ThreeLinesOffLinesWeakTriple slide point selected) →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef

/-- Spend the three line exclusions and reconstruct the preceding combined
blind residual. -/
theorem chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind_of_offLines
    (hoffLines :
      ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines) :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind := by
  intro slide hadmissible hfundamental point hheavy hbudgetBlind hreadingBlind hweak
  exact hoffLines slide hadmissible hfundamental point hheavy hbudgetBlind hreadingBlind
    (exists_threeLinesOffLinesWeakTriple_of_exists_weak slide point hweak)

/-- The preceding combined blind residual restricts to the off-lines weak
antecedent. -/
theorem offLinesThreeLinesFundamentalDomain_of_budgetReadingBlind
    (hblind : ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind) :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines := by
  intro slide hadmissible hfundamental point hheavy hbudgetBlind hreadingBlind hweak
  exact hblind slide hadmissible hfundamental point hheavy hbudgetBlind hreadingBlind
    (exists_weak_of_exists_threeLinesOffLinesWeakTriple slide point hweak)

/-- Removing the three impossible weak witnesses is exactly equivalent to the
preceding combined blind A2 formula. -/
theorem chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines_iff_combined :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines ↔
      ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind :=
  ⟨chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind_of_offLines,
    offLinesThreeLinesFundamentalDomain_of_budgetReadingBlind⟩

/-- The off-lines residual reconstructs the original public A2 statement. -/
theorem chartTieFreeThreeLinesFundamentalDomain_of_offLines
    (hoffLines :
      ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines) :
    ChartTieFreeThreeLinesFundamentalDomain :=
  chartTieFreeThreeLinesFundamentalDomain_of_budgetReadingBlind
    (chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlind_of_offLines hoffLines)

/-- The original public A2 statement restricts to the off-lines residual. -/
theorem offLinesThreeLinesFundamentalDomain_of_chartTieFree
    (hchart : ChartTieFreeThreeLinesFundamentalDomain) :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines :=
  offLinesThreeLinesFundamentalDomain_of_budgetReadingBlind
    (budgetReadingBlindThreeLinesFundamentalDomain_of_chartTieFree hchart)

/-- The final off-lines A2 formula is equivalent to its public statement. -/
theorem chartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines_iff :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavyBudgetReadingBlindOffLines ↔
      ChartTieFreeThreeLinesFundamentalDomain :=
  ⟨chartTieFreeThreeLinesFundamentalDomain_of_offLines,
    offLinesThreeLinesFundamentalDomain_of_chartTieFree⟩

end Gtz
