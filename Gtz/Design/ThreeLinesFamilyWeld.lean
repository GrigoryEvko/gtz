import Gtz.Design.OneDeterminantReduction
import Gtz.Wave.ThreeLinesMovedOrbitTraceWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The three-lines family weld

The generic whitening weld `Gtz.exists_design_of_chartPoint` realizes every
chart point as a weighted design, but its design-side consumer quantifies over
all designs, and the global strict selection is false: the sharp extremal
design has thirteen ties and no strict triple.  This module lands the
dischargeable family form for the three-lines chart, the analogue of the K4
family weld.

* `ThreeLinesFamilySelection` — strict selection quantified over the whitened
  family of the fundamental domain only, with the weak antecedent kept.
* `chartTieFreeThreeLinesFundamentalDomain_of_familySelection` — the family
  form alone proves the full fundamental-domain statement.
* `chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_of_familySelection`
  — **the registry joint**: the family form discharges the committed A2 axiom
  verbatim through the landed equivalence.
* `whitenedThreeLines_lineTriple_not_dominates` — no realizing design lets a
  dependent line triple dominate.  Every dominator of the family is off-lines,
  so the family selection only ever fights on the seventeen off-line triples.
-/

namespace Gtz

open Matrix

/-! ## The family selection -/

/-- **The family selection.**  Strict selection quantified over the whitened
three-lines family of the fundamental domain, with the weak antecedent kept:
every design that realizes a fundamental-domain chart point through the
whitening equivalence and carries a weak card-three dominator has a strict
card-three subset.  The global form of this hypothesis is false at the sharp
extremal design, and the family form is the dischargeable one. -/
def ThreeLinesFamilySelection : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6, ∀ D : WeightedDesign 6 3,
      D.weight = point.weight →
      (∀ C : Finset (Fin 6),
        ((subsetSum D C - 1).PosDef
            ↔ (directionChartGap (threeLinesDirection slide) point.mass point.weight
                C).PosDef)
          ∧ (Dominates D C
            ↔ (directionChartGap (threeLinesDirection slide) point.mass point.weight
                C).PosSemidef)) →
      (∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ (subsetSum D C - 1).PosDef

/-- The global weak-to-strict selection implies the family selection. -/
theorem threeLinesFamilySelection_of_designSelection
    (hsel : ∀ D : WeightedDesign 6 3,
      (∃ C : Finset (Fin 6), C.card = 3 ∧ Dominates D C) →
      ∃ C : Finset (Fin 6), C.card = 3 ∧ (subsetSum D C - 1).PosDef) :
    ThreeLinesFamilySelection :=
  fun _ _ _ _ D _ _ hweak => hsel D hweak

/-- The family selection proves chart tie-freeness at every fundamental-domain
slide. -/
theorem directionChartIsTieFree_threeLines_of_familySelection
    (hsel : ThreeLinesFamilySelection) (slide : ℝ)
    (hadmissible : IsAdmissibleThreeLinesParameter slide)
    (hfundamental : 1 ≤ |slide|) :
    DirectionChartIsTieFree (threeLinesDirection slide) := by
  intro point hweak
  obtain ⟨D, hweight, htransfer⟩ :=
    exists_design_of_chartPoint (threeLinesDirection slide) point
      (posDef_massMoment_threeLinesDirection slide point)
  obtain ⟨weakSet, hweakCard, hweakPsd⟩ := hweak
  obtain ⟨C, hcard, hpd⟩ :=
    hsel slide hadmissible hfundamental point D hweight htransfer
      ⟨weakSet, hweakCard, (htransfer weakSet).2.mpr hweakPsd⟩
  exact ⟨C, hcard, (htransfer C).1.mp hpd⟩

/-- The family selection proves the full fundamental-domain statement. -/
theorem chartTieFreeThreeLinesFundamentalDomain_of_familySelection
    (hsel : ThreeLinesFamilySelection) :
    ChartTieFreeThreeLinesFundamentalDomain :=
  fun slide hadmissible hfundamental =>
    directionChartIsTieFree_threeLines_of_familySelection hsel slide hadmissible
      hfundamental

/-- **The registry joint.**  The family selection discharges the committed A2
axiom verbatim, through the landed equivalence with the public statement. -/
theorem
    chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_of_familySelection
    (hsel : ThreeLinesFamilySelection) :
    ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines :=
  chartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines_iff.mpr
    (chartTieFreeThreeLinesFundamentalDomain_of_familySelection hsel)

/-! ## The family fights off the lines only -/

/-- No realizing design lets a dependent line triple dominate: the three
line triples transfer their chart exclusions to the design side. -/
theorem whitenedThreeLines_lineTriple_not_dominates (slide : ℝ)
    (point : DirectionChartPoint 6) (D : WeightedDesign 6 3)
    (htransfer : ∀ C : Finset (Fin 6),
      ((subsetSum D C - 1).PosDef
          ↔ (directionChartGap (threeLinesDirection slide) point.mass point.weight
              C).PosDef)
        ∧ (Dominates D C
          ↔ (directionChartGap (threeLinesDirection slide) point.mass point.weight
              C).PosSemidef)) :
    ¬ Dominates D {0, 1, 2} ∧ ¬ Dominates D {0, 3, 4} ∧ ¬ Dominates D {1, 3, 5} := by
  have hweightNe : ∀ label, point.weight label ≠ 0 :=
    fun label => (point.weight_pos label).ne'
  refine ⟨fun hdom => ?_, fun hdom => ?_, fun hdom => ?_⟩
  · exact directionChartGap_threeLines_firstLine_not_posSemidef slide point.mass
      point.weight hweightNe (point.mass_pos 3) (point.mass_pos 4)
      (point.mass_pos 5).le (((htransfer {0, 1, 2}).2).mp hdom)
  · exact directionChartGap_threeLines_secondLine_not_posSemidef slide point.mass
      point.weight hweightNe (point.mass_pos 1) (point.mass_pos 2)
      (point.mass_pos 5) (((htransfer {0, 3, 4}).2).mp hdom)
  · exact directionChartGap_threeLines_thirdLine_not_posSemidef slide point.mass
      point.weight hweightNe (point.mass_pos 0) (point.mass_pos 2)
      (point.mass_pos 4) (((htransfer {1, 3, 5}).2).mp hdom)

/-- Every dominator of a realizing design is off the three dependent lines.
The family selection only ever fights on the seventeen off-line triples. -/
theorem whitenedThreeLines_dominator_offLines (slide : ℝ)
    (point : DirectionChartPoint 6) (D : WeightedDesign 6 3)
    (htransfer : ∀ C : Finset (Fin 6),
      ((subsetSum D C - 1).PosDef
          ↔ (directionChartGap (threeLinesDirection slide) point.mass point.weight
              C).PosDef)
        ∧ (Dominates D C
          ↔ (directionChartGap (threeLinesDirection slide) point.mass point.weight
              C).PosSemidef))
    (C : Finset (Fin 6)) (hdom : Dominates D C) :
    C ≠ {0, 1, 2} ∧ C ≠ {0, 3, 4} ∧ C ≠ {1, 3, 5} := by
  obtain ⟨hfirst, hsecond, hthird⟩ :=
    whitenedThreeLines_lineTriple_not_dominates slide point D htransfer
  refine ⟨fun hC => hfirst (hC ▸ hdom), fun hC => hsecond (hC ▸ hdom),
    fun hC => hthird (hC ▸ hdom)⟩

end Gtz
