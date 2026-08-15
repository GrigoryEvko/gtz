import Gtz.Design.ThreeLinesDescentPort
import Gtz.Design.TwoMeetingLinesTransversal
import Gtz.Reduction.StressSignSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The descent port: the full-selection descent at every design

The descent stack is direction-generic.  `posDef_directionChartGap_univ_of_span`
and the trichotomy below it take the direction family as a parameter and use
exactly one property of it: that the six directions leave no probe unread.
The three-lines port spends that observation once, at the three-lines chart.

This module spends it at the widest chart there is.  A weighted design is
already a chart point of ITS OWN atom family: take the direction family to be
`design.atom` and take BOTH the mass and the weight to be `design.weight`.
Then every mass ratio `m_c / w_c` collapses to one, the subtracted total is
Parseval, and the chart gap becomes the design's own gap `subsetSum - 1`.

Two consequences, and the second is the reason the module exists.

The span hypothesis is FREE.  Parseval forces the atoms of a weighted design
to span, which is the landed `weightedDesign_atoms_span`.  No chart has to be
built, no projective moduli have to be absorbed, and no realization has to be
exhibited.

The descent therefore holds at EVERY design of EVERY stratum, with no pattern
hypothesis at all.  The registry records that two residual patterns have no
chart and that building one is their attack; for the purpose of the descent
that construction is not needed, because the design supplies the chart.

What the port does NOT do is decide the strata.  The card-three branch is the
conclusion, and the card-four stall branch is exactly the open content: at the
trivial chart the stall escape is the rank-three statement itself.  The value
here is that the dichotomy, and the pivot apparatus that comes with it, become
available at strata that until now carried only sufficient-condition criteria.

The results:

* `designChartPoint` — the chart point a design reads off itself;
* `directionChartGap_designChartPoint` — the gap dictionary, an equality;
* `designAtom_span` — the span hypothesis, discharged by Parseval;
* `posDef_directionChartGap_univ_designChartPoint` — the chart route agrees
  with the landed generic `posDef_subsetSum_univ_sub_one`;
* `design_cardThree_or_cardFour_stall` — the dichotomy at every design;
* `exists_dominates_cardThree_of_no_cardFour_stall` — the consumable form,
  landing `Dominates` on a card-three subset.
-/

namespace Gtz

open Finset Matrix

/-! ## The chart a design reads off itself -/

/-- **The trivial chart point.**  A design is a chart point of its own atom
family, with the mass equal to the weight.  Every mass ratio is then one. -/
def designChartPoint {size : ℕ} (design : WeightedDesign size 3) :
    DirectionChartPoint size where
  mass := design.weight
  weight := design.weight
  mass_pos := design.weight_pos
  weight_pos := design.weight_pos
  weight_sum_one := design.weight_sum_one

/-- **The gap dictionary.**  At the trivial chart the chart gap IS the
design's gap.  The selected sum loses its ratios because mass equals weight,
and the subtracted total is Parseval. -/
theorem directionChartGap_designChartPoint {size : ℕ} (design : WeightedDesign size 3)
    (selected : Finset (Fin size)) :
    directionChartGap design.atom (designChartPoint design).mass
        (designChartPoint design).weight selected
      = subsetSum design selected - 1 := by
  rw [directionChartGap, subsetSum]
  congr 1
  · refine Finset.sum_congr rfl fun label _ => ?_
    show (design.weight label / design.weight label) • atomMatrix (design.atom label)
      = atomMatrix (design.atom label)
    rw [div_self (design.weight_pos label).ne', one_smul]
  · exact design.isParseval

/-- **The span hypothesis is free.**  Parseval forces the atoms to span, so a
design needs no chart construction to inherit the descent. -/
theorem designAtom_span {size : ℕ} (design : WeightedDesign size 3) :
    ∀ probe : Fin 3 → ℝ, (∀ label, design.atom label ⬝ᵥ probe = 0) → probe = 0 :=
  fun _probe hprobe => weightedDesign_atoms_span design hprobe

/-! ## The descent at every design -/

/-- **The generic full-selection law agrees with the chart's.**  The design
level already carries `posDef_subsetSum_univ_sub_one`, generic in size and
rank.  This records that the chart route reproves it, so the two entry points
to the descent agree and either may be spent. -/
theorem posDef_directionChartGap_univ_designChartPoint (design : WeightedDesign 6 3) :
    (directionChartGap design.atom (designChartPoint design).mass
      (designChartPoint design).weight Finset.univ).PosDef := by
  rw [directionChartGap_designChartPoint design Finset.univ]
  exact posDef_subsetSum_univ_sub_one design (by norm_num)

/-- **THE DESCENT AT EVERY DESIGN.**  Every weighted `(6,3)` design carries a
strictly dominating card-three subset, or a stalled positive definite
card-four subset.  No pattern hypothesis, no chart construction, no
realization: the design is its own chart. -/
theorem design_cardThree_or_cardFour_stall (design : WeightedDesign 6 3) :
    (∃ sel : Finset (Fin 6), sel.card = 3 ∧ (subsetSum design sel - 1).PosDef)
    ∨ (∃ sel : Finset (Fin 6), sel.card = 4
        ∧ (subsetSum design sel - 1).PosDef
        ∧ ∀ label ∈ sel, 1 ≤ chartLadderPivot design.atom
            (designChartPoint design).mass (designChartPoint design).weight sel label) := by
  have hdescent := cardThree_or_cardFour_stall_of_span design.atom
    (designChartPoint design) (designAtom_span design)
  rcases hdescent with ⟨sel, hcard, hpd⟩ | ⟨sel, hcard, hpd, hstall⟩
  · refine Or.inl ⟨sel, hcard, ?_⟩
    rwa [directionChartGap_designChartPoint design sel] at hpd
  · refine Or.inr ⟨sel, hcard, ?_, hstall⟩
    rwa [directionChartGap_designChartPoint design sel] at hpd

/-- **The consumable form.**  A design with no stalled card-four subset
carries a STRICTLY dominating card-three subset.  This is exactly the shape
the registry's stratum residuals ask for, with the stall branch as the only
remaining content. -/
theorem exists_posDef_cardThree_of_no_cardFour_stall (design : WeightedDesign 6 3)
    (hno : ∀ sel : Finset (Fin 6), sel.card = 4 → (subsetSum design sel - 1).PosDef →
      ∃ label ∈ sel, chartLadderPivot design.atom (designChartPoint design).mass
        (designChartPoint design).weight sel label < 1) :
    ∃ sel : Finset (Fin 6), sel.card = 3 ∧ (subsetSum design sel - 1).PosDef := by
  rcases design_cardThree_or_cardFour_stall design with ⟨sel, hcard, hpd⟩ | ⟨sel, hcard, hpd, hstall⟩
  · exact ⟨sel, hcard, hpd⟩
  · obtain ⟨label, hmem, hlt⟩ := hno sel hcard hpd
    exact absurd (hstall label hmem) (not_le.mpr hlt)

/-- The weak form: the same hypothesis lands `Dominates`, which is the shape
`GtzWeighted 6 3` consumes. -/
theorem exists_dominates_cardThree_of_no_cardFour_stall (design : WeightedDesign 6 3)
    (hno : ∀ sel : Finset (Fin 6), sel.card = 4 → (subsetSum design sel - 1).PosDef →
      ∃ label ∈ sel, chartLadderPivot design.atom (designChartPoint design).mass
        (designChartPoint design).weight sel label < 1) :
    ∃ sel : Finset (Fin 6), sel.card = 3 ∧ Dominates design sel := by
  obtain ⟨sel, hcard, hpd⟩ := exists_posDef_cardThree_of_no_cardFour_stall design hno
  exact ⟨sel, hcard, hpd.posSemidef⟩

/-! ## The two-meeting-lines reroute -/

/-- **THE TWO-MEETING-LINES REROUTE.**  Under the obligation's own blind-spot
hypotheses, a design with no stalled card-four subset satisfies the four-way
transversal disjunction outright.

The descent supplies SOME strictly dominating triple; the landed localization
`twoMeetingLines_strictTriple_eq_transversal_of_bothLineNormalBlind` forces
that triple to be one of the four transversals, because every other triple
carries a flat pair on one of the two lines and would fire the lift criterion
the blind-spot hypothesis says is silent.  No criterion, no selection rule,
and no coverage estimate enters. -/
theorem twoMeetingLines_transversalStrict_of_no_cardFour_stall
    (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst {0, 1, 2})
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond {0, 3, 4})
    (hno : ∀ sel : Finset (Fin 6), sel.card = 4 → (subsetSum design sel - 1).PosDef →
      ∃ label ∈ sel, chartLadderPivot design.atom (designChartPoint design).mass
        (designChartPoint design).weight sel label < 1) :
    TwoMeetingLinesTransversalStrict design := by
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_cardThree_of_no_cardFour_stall design hno
  rcases twoMeetingLines_strictTriple_eq_transversal_of_bothLineNormalBlind design
    normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond
    hblindFirst hblindSecond selected hcard hposDef with
    heq | heq | heq | heq
  · exact Or.inl (heq ▸ hposDef)
  · exact Or.inr (Or.inl (heq ▸ hposDef))
  · exact Or.inr (Or.inr (Or.inl (heq ▸ hposDef)))
  · exact Or.inr (Or.inr (Or.inr (heq ▸ hposDef)))

end Gtz
