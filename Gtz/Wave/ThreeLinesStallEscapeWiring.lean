import Gtz.Design.ThreeLinesDescentPort
import Gtz.Design.ThreeLinesFamilyWeld

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Wire card-four stall escape into the three-lines obligation

`ThreeLinesDescentPort` proves that every three-lines chart point carries a
positive-definite triple or a stalled positive-definite four-set.  This module
identifies the exact object-level closure needed on the second branch.

The first section is direction-generic.  For any six-label chart, a
positive-definite triple is equivalent to a positive-definite four-set with one
sub-one deletion pivot.  If the directions span, the landed descent dichotomy
then proves that weak-to-strict chart tie-freeness is equivalent to escaping
every stalled four-set at a point that carries a weak triple.

The second section instantiates the equivalence on the fundamental domain of
the three-lines chart and wires it to both the family weld and the exact A2
registry residual.  This is an interface reduction, not a claim that the stall
escape has already been proved.
-/

namespace Gtz

open Finset Matrix

/-! ## Card three versus a non-stalled card four, generically -/

/-- A positive-definite triple can be enlarged by any missing label.  The
enlarged four-set stays positive definite, and its new label has deletion pivot
strictly below one because erasing it returns the original triple. -/
theorem exists_nonStalledCardFour_of_cardThree_posDef
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} (hcard : selected.card = 3)
    (hpd : (directionChartGap direction point.mass point.weight
      selected).PosDef) :
    ∃ enlarged : Finset (Fin 6), enlarged.card = 4 ∧
      (directionChartGap direction point.mass point.weight enlarged).PosDef ∧
      ∃ added ∈ enlarged,
        chartLadderPivot direction point.mass point.weight enlarged added < 1 := by
  obtain ⟨added, hadded⟩ : ∃ added : Fin 6, added ∉ selected := by
    by_contra hall
    push Not at hall
    have huniv : selected = Finset.univ := Finset.eq_univ_iff_forall.mpr hall
    rw [huniv, Finset.card_univ, Fintype.card_fin] at hcard
    omega
  have henlarged : (directionChartGap direction point.mass point.weight
      (insert added selected)).PosDef :=
    posDef_directionChartGap_of_subset direction point.mass point.weight
      point.mass_pos point.weight_pos (Finset.subset_insert _ _) hpd
  refine ⟨insert added selected, ?_, henlarged, added,
    Finset.mem_insert_self _ _, ?_⟩
  · rw [Finset.card_insert_of_notMem hadded, hcard]
  · exact (posDef_directionChartGap_erase_iff direction point.mass point.weight
      point.mass_pos point.weight_pos _ (Finset.mem_insert_self added selected)
      henlarged).mp (by rwa [Finset.erase_insert hadded])

/-- A non-stalled positive-definite four-set erases directly to a
positive-definite triple.  No matroid classification is needed. -/
theorem exists_cardThree_posDef_of_nonStalledCardFour
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} (hcard : selected.card = 4)
    (hpd : (directionChartGap direction point.mass point.weight
      selected).PosDef)
    {label : Fin 6} (hmem : label ∈ selected)
    (hlt : chartLadderPivot direction point.mass point.weight selected label < 1) :
    ∃ triple : Finset (Fin 6), triple.card = 3 ∧
      (directionChartGap direction point.mass point.weight triple).PosDef := by
  refine ⟨selected.erase label, ?_, ?_⟩
  · rw [Finset.card_erase_of_mem hmem, hcard]
  · exact (posDef_directionChartGap_erase_iff direction point.mass point.weight
      point.mass_pos point.weight_pos selected hmem hpd).mpr hlt

/-- **THE GENERIC CARD-FOUR EQUIVALENCE.**  A six-label chart carries a
positive-definite triple exactly when it carries a non-stalled
positive-definite four-set. -/
theorem exists_cardThree_posDef_iff_exists_nonStalledCardFour
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6) :
    (∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap direction point.mass point.weight selected).PosDef)
      ↔ ∃ selected : Finset (Fin 6), selected.card = 4 ∧
        (directionChartGap direction point.mass point.weight selected).PosDef ∧
        ∃ label ∈ selected,
          chartLadderPivot direction point.mass point.weight selected label < 1 := by
  constructor
  · rintro ⟨selected, hcard, hpd⟩
    exact exists_nonStalledCardFour_of_cardThree_posDef direction point hcard hpd
  · rintro ⟨selected, hcard, hpd, label, hmem, hlt⟩
    exact exists_cardThree_posDef_of_nonStalledCardFour direction point hcard hpd
      hmem hlt

/-! ## The exact weak-antecedent stall escape -/

/-- At every chart point carrying a weak triple, every stalled
positive-definite four-set can be accompanied by a non-stalled one.  Keeping
the weak antecedent makes this exactly the tie-freeness target rather than the
stronger antecedent-free strict-selection statement. -/
def DirectionChartCardFourStallEscape
    (direction : Fin 6 → (Fin 3 → ℝ)) : Prop :=
  ∀ point : DirectionChartPoint 6,
    (∃ weak : Finset (Fin 6), weak.card = 3 ∧
      (directionChartGap direction point.mass point.weight weak).PosSemidef) →
    ∀ stalled : Finset (Fin 6), stalled.card = 4 →
      (directionChartGap direction point.mass point.weight stalled).PosDef →
      (∀ label ∈ stalled,
        1 ≤ chartLadderPivot direction point.mass point.weight stalled label) →
      ∃ escaped : Finset (Fin 6), escaped.card = 4 ∧
        (directionChartGap direction point.mass point.weight escaped).PosDef ∧
        ∃ label ∈ escaped,
          chartLadderPivot direction point.mass point.weight escaped label < 1

/-- **THE GENERIC STALL-ESCAPE IDENTIFICATION.**  For a spanning direction
family, weak-to-strict chart tie-freeness is exactly weak-antecedent card-four
stall escape.

The forward implication enlarges the strict triple supplied by tie-freeness.
The reverse implication uses the generic descent dichotomy: its strict branch
is done, and its stalled branch invokes the escape before erasing once. -/
theorem directionChartCardFourStallEscape_iff_isTieFree_of_span
    (direction : Fin 6 → (Fin 3 → ℝ))
    (hspan : ∀ probe : Fin 3 → ℝ,
      (∀ label, direction label ⬝ᵥ probe = 0) → probe = 0) :
    DirectionChartCardFourStallEscape direction ↔
      DirectionChartIsTieFree direction := by
  constructor
  · intro hescape point hweak
    rcases cardThree_or_cardFour_stall_of_span direction point hspan with
      hstrict | ⟨stalled, hcard, hpd, hstall⟩
    · exact hstrict
    · exact (exists_cardThree_posDef_iff_exists_nonStalledCardFour direction
        point).mpr (hescape point hweak stalled hcard hpd hstall)
  · intro hfree point hweak _stalled _hcard _hpd _hstall
    exact (exists_cardThree_posDef_iff_exists_nonStalledCardFour direction
      point).mp (hfree point hweak)

/-! ## Three-lines instantiation and registry consumer -/

/-- The exact stall-escape target on the fundamental domain of the three-lines
chart. -/
def ThreeLinesFundamentalStallEscape : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    DirectionChartCardFourStallEscape (threeLinesDirection slide)

/-- Fundamental-domain stall escape is exactly public A2. -/
theorem threeLinesFundamentalStallEscape_iff_chartTieFree :
    ThreeLinesFundamentalStallEscape ↔
      ChartTieFreeThreeLinesFundamentalDomain := by
  constructor
  · intro hescape slide hadmissible hfundamental
    exact (directionChartCardFourStallEscape_iff_isTieFree_of_span
      (threeLinesDirection slide) (threeLinesDirection_span slide)).mp
        (hescape slide hadmissible hfundamental)
  · intro hfree slide hadmissible hfundamental
    exact (directionChartCardFourStallEscape_iff_isTieFree_of_span
      (threeLinesDirection slide) (threeLinesDirection_span slide)).mpr
        (hfree slide hadmissible hfundamental)

/-- The stall-escape interface supplies the dischargeable whitened-family form. -/
theorem threeLinesFamilySelection_of_fundamentalStallEscape
    (hescape : ThreeLinesFundamentalStallEscape) : ThreeLinesFamilySelection := by
  intro slide hadmissible hfundamental point D _hweight htransfer hweak
  have hfree : DirectionChartIsTieFree (threeLinesDirection slide) :=
    (threeLinesFundamentalStallEscape_iff_chartTieFree.mp hescape) slide
      hadmissible hfundamental
  obtain ⟨weak, hweakCard, hweakDom⟩ := hweak
  obtain ⟨strict, hstrictCard, hstrict⟩ := hfree point
    ⟨weak, hweakCard, (htransfer weak).2.mp hweakDom⟩
  exact ⟨strict, hstrictCard, (htransfer strict).1.mpr hstrict⟩

/-- **THE A2 REGISTRY JOINT.**  Fundamental-domain stall escape discharges the
exact residual registered in `Skeleton.Obligations`. -/
theorem
    chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_of_stallEscape
    (hescape : ThreeLinesFundamentalStallEscape) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines :=
  chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_iff.mpr
    (threeLinesFundamentalStallEscape_iff_chartTieFree.mp hescape)

/-- **SCOPE AUDIT.**  The new object-level target is exactly equivalent to the
current A2 registry residual, not merely sufficient for it. -/
theorem threeLinesFundamentalStallEscape_iff_registryResidual :
    ThreeLinesFundamentalStallEscape ↔
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines := by
  rw [threeLinesFundamentalStallEscape_iff_chartTieFree,
    chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_iff]

end Gtz
