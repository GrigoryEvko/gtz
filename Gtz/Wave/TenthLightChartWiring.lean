import Gtz.Design.OneDeterminantReduction
import Gtz.Design.KFourBandLiveness
import Gtz.Wave.ProjectionDictionary

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The tenth-light closure wired into the chart obligations

`Gtz.exists_design_of_chartPoint` whitens every chart point with a positive
definite total moment into a genuine weighted design while preserving the weak
and strict gap conditions of every subset.  Both live direction charts have
positive definite total moment matrices.  The unconditional real tenth floor
can therefore be spent on the chart side too: if all six chart weights are
strictly below `1 / 10`, some card-three chart gap is positive definite.

This module factors that closed region out of the two chart obligations still
visible in the `(6,3)` registry.  The three-lines obligation survives only at a
tenth-heavy point in its fundamental domain.  The K4 knife band survives only
at a tenth-heavy point outside both landed atlas cells.  IFF theorems record
that these are formula sharpenings, not stronger assumptions.
-/

namespace Gtz

open Matrix Finset

/-! ## The generic chart-light closure -/

/-- A positive-moment six-point chart whose weights are all below one tenth
has a strictly positive card-three gap.  Whitening supplies a genuine design,
the projection dictionary selects the triple, and the chart dictionary pulls
the strict gap back through the same invertible congruence. -/
theorem exists_posDef_directionChartGap_of_weights_lt_tenth
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (hmoment : (∑ label, point.mass label • atomMatrix (direction label)).PosDef)
    (hlight : ∀ label, point.weight label < 1 / 10) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap direction point.mass point.weight selected).PosDef := by
  obtain ⟨design, hweight, htransfer⟩ :=
    exists_design_of_chartPoint direction point hmoment
  have hdesignLight : ∀ label, design.weight label < 1 / 10 := by
    intro label
    rw [hweight]
    exact hlight label
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_triple_of_weights_lt_tenth design hdesignLight
  exact ⟨selected, hcard, (htransfer selected).1.mp hposDef⟩

/-- Contrapositive chart form: if no card-three gap is positive definite, the
chart point has a tenth-heavy label.  This is the direct chart analogue of
`Gtz.exists_weight_ge_tenth_of_no_strict_triple`. -/
theorem exists_chartWeight_ge_tenth_of_no_strictTriple
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (hmoment : (∑ label, point.mass label • atomMatrix (direction label)).PosDef)
    (hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (directionChartGap direction point.mass point.weight selected).PosDef) :
    ∃ heavyLabel : Fin 6, 1 / 10 ≤ point.weight heavyLabel := by
  by_contra hhasHeavy
  have hlight : ∀ label, point.weight label < 1 / 10 := by
    intro label
    exact lt_of_not_ge fun hge => hhasHeavy ⟨label, hge⟩
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_directionChartGap_of_weights_lt_tenth direction point hmoment hlight
  exact hnoStrict selected hcard hposDef

/-- The exact residual left after the chart-light closure: weak-to-strict is
required only at chart points carrying a tenth-heavy label. -/
def DirectionChartTenthHeavyWeakToStrict
    (direction : Fin 6 → (Fin 3 → ℝ)) : Prop :=
  ∀ point : DirectionChartPoint 6,
    (∃ heavyLabel : Fin 6, 1 / 10 ≤ point.weight heavyLabel) →
    (∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap direction point.mass point.weight selected).PosSemidef) →
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap direction point.mass point.weight selected).PosDef

/-- Spend the all-light theorem and leave only the tenth-heavy chart residual. -/
theorem directionChartIsTieFree_of_tenthHeavyWeakToStrict
    (direction : Fin 6 → (Fin 3 → ℝ))
    (hmoment : ∀ point : DirectionChartPoint 6,
      (∑ label, point.mass label • atomMatrix (direction label)).PosDef)
    (hheavy : DirectionChartTenthHeavyWeakToStrict direction) :
    DirectionChartIsTieFree direction := by
  intro point hweak
  by_cases hhasHeavy : ∃ heavyLabel : Fin 6, 1 / 10 ≤ point.weight heavyLabel
  · exact hheavy point hhasHeavy hweak
  · apply exists_posDef_directionChartGap_of_weights_lt_tenth direction point
      (hmoment point)
    intro label
    exact lt_of_not_ge fun hge => hhasHeavy ⟨label, hge⟩

/-- The original chart statement trivially supplies its tenth-heavy
restriction. -/
theorem tenthHeavyWeakToStrict_of_directionChartIsTieFree
    (direction : Fin 6 → (Fin 3 → ℝ))
    (hchart : DirectionChartIsTieFree direction) :
    DirectionChartTenthHeavyWeakToStrict direction := by
  intro point _hheavy hweak
  exact hchart point hweak

/-- At every positive-moment six-point chart the tenth-heavy formulation is
kernel-equivalent to the original tie-free statement. -/
theorem directionChartTenthHeavyWeakToStrict_iff
    (direction : Fin 6 → (Fin 3 → ℝ))
    (hmoment : ∀ point : DirectionChartPoint 6,
      (∑ label, point.mass label • atomMatrix (direction label)).PosDef) :
    DirectionChartTenthHeavyWeakToStrict direction ↔
      DirectionChartIsTieFree direction :=
  ⟨directionChartIsTieFree_of_tenthHeavyWeakToStrict direction hmoment,
    tenthHeavyWeakToStrict_of_directionChartIsTieFree direction⟩

/-! ## The three-lines consumer -/

/-- The surviving three-lines residual: only the involution fundamental domain
and only chart points with a tenth-heavy label. -/
def ChartTieFreeThreeLinesFundamentalDomainTenthHeavy : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    DirectionChartTenthHeavyWeakToStrict (threeLinesDirection slide)

/-- The tenth-heavy fundamental-domain residual reconstructs the former A2
statement by whitening every all-light chart point. -/
theorem chartTieFreeThreeLinesFundamentalDomain_of_tenthHeavy
    (hheavy : ChartTieFreeThreeLinesFundamentalDomainTenthHeavy) :
    ChartTieFreeThreeLinesFundamentalDomain := by
  intro slide hadmissible hfundamental
  exact directionChartIsTieFree_of_tenthHeavyWeakToStrict
    (threeLinesDirection slide) (posDef_massMoment_threeLinesDirection slide)
    (hheavy slide hadmissible hfundamental)

/-- The former A2 statement restricts to the surviving heavy region. -/
theorem tenthHeavyThreeLinesFundamentalDomain_of_chartTieFree
    (hchart : ChartTieFreeThreeLinesFundamentalDomain) :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavy := by
  intro slide hadmissible hfundamental
  exact tenthHeavyWeakToStrict_of_directionChartIsTieFree
    (threeLinesDirection slide) (hchart slide hadmissible hfundamental)

/-- The sharpened and former A2 formulations are equivalent. -/
theorem chartTieFreeThreeLinesFundamentalDomainTenthHeavy_iff :
    ChartTieFreeThreeLinesFundamentalDomainTenthHeavy ↔
      ChartTieFreeThreeLinesFundamentalDomain :=
  ⟨chartTieFreeThreeLinesFundamentalDomain_of_tenthHeavy,
    tenthHeavyThreeLinesFundamentalDomain_of_chartTieFree⟩

/-! ## The K4 consumer -/

/-- The surviving K4 knife band after spending Layer A, the exchange star and
the chart-light theorem.  Both quantifiers remain on spanning trees. -/
noncomputable def KFourKnifeBandRefinedTenthHeavyWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    (∃ heavyLabel : Fin 6, 1 / 10 ≤ point.weight heavyLabel) →
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef) →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- The tenth-heavy knife-band residual reconstructs the former A3 statement.
In the all-light branch the generic chart closure supplies a strict card-three
gap; K4's dependent-triple exclusion forces that subset to be a spanning tree. -/
theorem kFourKnifeBandRefined_of_tenthHeavy
    (hheavy : KFourKnifeBandRefinedTenthHeavyWeakToStrict) :
    KFourKnifeBandRefinedWeakToStrict := by
  intro point hnotLayerA hnotExchange hweak
  by_cases hhasHeavy : ∃ heavyLabel : Fin 6, 1 / 10 ≤ point.weight heavyLabel
  · exact hheavy point hnotLayerA hnotExchange hhasHeavy hweak
  · have hlight : ∀ label, point.weight label < 1 / 10 := by
      intro label
      exact lt_of_not_ge fun hge => hhasHeavy ⟨label, hge⟩
    obtain ⟨selected, hcard, hposDef⟩ :=
      exists_posDef_directionChartGap_of_weights_lt_tenth kFourDirection point
        (posDef_massMoment_kFourDirection point) hlight
    rcases cardThreeSubset_isSpanningTreeOrDependentTriple selected hcard with
      htree | hdependent
    · exact ⟨selected, htree, hposDef⟩
    · exact absurd hposDef.posSemidef
        (kFourDependentTriple_gap_not_posSemidef point selected hdependent)

/-- The former A3 statement trivially supplies its tenth-heavy restriction. -/
theorem tenthHeavyKFourKnifeBandRefined_of_refined
    (hrefined : KFourKnifeBandRefinedWeakToStrict) :
    KFourKnifeBandRefinedTenthHeavyWeakToStrict := by
  intro point hnotLayerA hnotExchange _hheavy hweak
  exact hrefined point hnotLayerA hnotExchange hweak

/-- The sharpened and former A3 formulations are equivalent. -/
theorem kFourKnifeBandRefinedTenthHeavy_iff :
    KFourKnifeBandRefinedTenthHeavyWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  ⟨kFourKnifeBandRefined_of_tenthHeavy,
    tenthHeavyKFourKnifeBandRefined_of_refined⟩

/-! ## Exact non-vacuity of the sharpened K4 region -/

/-- The canonical band inhabitant is visibly tenth-heavy. -/
theorem bandResidualWitnessPoint_tenthHeavy :
    ∃ heavyLabel : Fin 6, 1 / 10 ≤ bandResidualWitnessPoint.weight heavyLabel := by
  refine ⟨0, ?_⟩
  change 1 / 10 ≤ bandResidualWitnessWeight 0
  norm_num [bandResidualWitnessWeight]

/-- The canonical band point satisfies every antecedent of the newly narrowed
K4 residual.  Its weak tree is obtained from the independently landed strict
tree, so the tenth-heavy region is demonstrably inhabited after both atlas
exclusions. -/
theorem bandResidualWitnessPoint_in_tenthHeavyKnifeBand :
    ¬ KFourLayerACellFires bandResidualWitnessPoint ∧
      ¬ KFourExchangeStarCellFires bandResidualWitnessPoint ∧
      (∃ heavyLabel : Fin 6, 1 / 10 ≤ bandResidualWitnessPoint.weight heavyLabel) ∧
      ∃ tree ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection bandResidualWitnessPoint.mass
          bandResidualWitnessPoint.weight tree).PosSemidef := by
  refine ⟨bandResidualWitnessPoint_notLayerACellFires,
    bandResidualWitnessPoint_notExchangeStarCellFires,
    bandResidualWitnessPoint_tenthHeavy, ?_⟩
  obtain ⟨tree, htree, hposDef⟩ := bandResidualWitnessPoint_hasStrictTree
  exact ⟨tree, htree, hposDef.posSemidef⟩

end Gtz
