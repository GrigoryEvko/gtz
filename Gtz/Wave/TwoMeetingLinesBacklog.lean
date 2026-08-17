/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Wave.ThreeLinesSlideElimination
import Gtz.Wave.WiringLineChartRoads
import Gtz.Wave.FlatPairWeakSeed
import Gtz.Design.ChartProgrammeAssembly
import Gtz.Design.TwoMeetingLinesNeedle
import Gtz.Design.TwoMeetingLinesParsevalCap
import Gtz.Design.TwoMeetingLinesRigidity
import Gtz.Design.OrthogonalConicAndTwinRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The two-meeting-lines backlog: the leverage twin, the slab hole, and the collapse

This module spends the landed corpus of the class whose line pattern is
`[[0,1,2],[0,3,4]]`.  Every input is landed elsewhere.  The content here is
composition, one sharp band, one containment and one refutation.

## What each section does

Section 1 transcribes the mass-leverage layer of the three-lines chart onto the
two-meeting-lines chart.  The three direction-generic laws are
`Gtz.three_le_card_overLevered`, `Gtz.weight_lt_chartMassLeverage_of_posDef_gap`
and `Gtz.posDef_directionChartGap_of_leverageTrace`.  The one missing bridge was
the moment law at this chart, and its body is one term.  The section closes the
over-levered stratum here, which is the twin of
`Gtz.exists_posDef_threeLines_of_overLevered_triple`.

Section 2 composes the two slab closures of the class.  The first result is that
the disjunction COLLAPSES: the complement-leverage slab is contained in the
weighted-complement slab, so the second slab alone carries the whole coverage.
The second result bands the first slab: on the heavy stratum it needs a weight
cap below one quarter, while every design forces a cap of at least one sixth.
The third result is a refutation.  The landed rational witness
`Gtz.twinFailureDesign` fires the pattern, heaviness and a weak dominator, and it
escapes BOTH slabs at every admissible cap.  So the slabs do not cover the
residual, and the uncovered part is inhabited in kernel.

Section 3 lands the end-to-end chart road to the registry Prop itself.  The tree
carried the road to the on-path spelling only.

Section 4 lands the five-name collapse.  Four of the five Iff steps were landed
in three different modules.  The fifth step, the one that names the registry
Prop, was not composed with them anywhere.

Section 5 certifies inhabitants and spends the rigidity kernel.

## Equivalence discipline

Section 1 is a strict reduction on each theorem, never an equivalence.  Section 2
holds one equivalence, the slab collapse, and one refutation.  Section 3 is a
wiring composition.  Section 4 is an equivalence and adds NO strength: it renames
one statement five ways.  Section 5 is a kernel witness.
-/

namespace Gtz

open Matrix

/-! ## 1.  The mass-leverage layer at the two-meeting-lines chart

The chart is `Gtz.twoMeetingLinesDirection`.  Its labels zero, one and three are
the three coordinate axes, at every parameter.  That single fact drives the whole
section: it gives the moment law, the bracket and the three dual probes. -/

/-- **The bridge.**  The mass moment of the two-meeting-lines chart is positive
definite at every chart point and every parameter.  No admissibility is used. -/
theorem posDef_chartMassMoment_twoMeetingLines (param : ℝ × ℝ)
    (point : DirectionChartPoint 6) :
    (chartMassMoment (twoMeetingLinesDirection param) point.mass).PosDef :=
  posDef_massMoment_twoMeetingLinesDirection param point

/-- **The counting law at this chart.**  At every chart point at least three
labels are over-levered.  Strict reduction, not an equivalence. -/
theorem three_le_card_overLevered_twoMeetingLines (param : ℝ × ℝ)
    (point : DirectionChartPoint 6) :
    3 ≤ (Finset.univ.filter
      (fun label => point.weight label
        < chartMassLeverage (twoMeetingLinesDirection param) point.mass label)).card :=
  three_le_card_overLevered (twoMeetingLinesDirection param) point
    (posDef_chartMassMoment_twoMeetingLines param point)

/-- **The leverage veto at this chart.**  Every label of a strictly dominating
triple that carries a blind probe is over-levered. -/
theorem weight_lt_chartMassLeverage_twoMeetingLines (param : ℝ × ℝ)
    (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (pivotLabel : Fin 6) (hmem : pivotLabel ∈ selected)
    (probe : Fin 3 → ℝ)
    (hblind : ∀ other ∈ selected, other ≠ pivotLabel →
      twoMeetingLinesDirection param other ⬝ᵥ probe = 0)
    (hlive : twoMeetingLinesDirection param pivotLabel ⬝ᵥ probe ≠ 0)
    (hgap : (directionChartGap (twoMeetingLinesDirection param) point.mass point.weight
      selected).PosDef) :
    point.weight pivotLabel
      < chartMassLeverage (twoMeetingLinesDirection param) point.mass pivotLabel :=
  weight_lt_chartMassLeverage_of_posDef_gap (twoMeetingLinesDirection param) point.mass
    point.weight point.mass_pos point.weight_pos
    (posDef_chartMassMoment_twoMeetingLines param point) selected pivotLabel hmem probe
    hblind hlive hgap

/-- **THE OVER-LEVERED STRATUM CLOSES AT THIS CHART.**  If exactly three labels
of a chart point are over-levered, and those three are independent, then that
triple is strictly dominating.  This is the twin of
`Gtz.exists_posDef_threeLines_of_overLevered_triple`.  Strict reduction. -/
theorem exists_posDef_twoMeetingLines_of_overLevered_triple (param : ℝ × ℝ)
    (point : DirectionChartPoint 6) (first second third : Fin 6)
    (hfirstSecond : first ≠ second) (hfirstThird : first ≠ third) (hsecondThird : second ≠ third)
    (hbracket : tripleBracket (twoMeetingLinesDirection param first)
      (twoMeetingLinesDirection param second) (twoMeetingLinesDirection param third) ≠ 0)
    (hfilter : Finset.univ.filter (fun label => point.weight label
        < chartMassLeverage (twoMeetingLinesDirection param) point.mass label)
      = {first, second, third}) :
    (directionChartGap (twoMeetingLinesDirection param) point.mass point.weight
      ({first, second, third} : Finset (Fin 6))).PosDef := by
  have hmoment := posDef_chartMassMoment_twoMeetingLines param point
  exact posDef_directionChartGap_of_leverageTrace (twoMeetingLinesDirection param) point.mass
    point.weight point.mass_pos point.weight_pos hmoment first second third
    hfirstSecond hfirstThird hsecondThird hbracket
    (two_add_weight_lt_sum_leverage_of_overLevered_triple (twoMeetingLinesDirection param) point
      hmoment first second third hfirstSecond hfirstThird hsecondThird hfilter first (by simp))
    (two_add_weight_lt_sum_leverage_of_overLevered_triple (twoMeetingLinesDirection param) point
      hmoment first second third hfirstSecond hfirstThird hsecondThird hfilter second (by simp))
    (two_add_weight_lt_sum_leverage_of_overLevered_triple (twoMeetingLinesDirection param) point
      hmoment first second third hfirstSecond hfirstThird hsecondThird hfilter third (by simp))

/-! ### The bracket hypothesis is inhabited

The chart basis `{0,1,3}` is the standard frame at every parameter, so its
bracket is one.  The antecedent of the closure above is therefore never empty on
its independence clause. -/

/-- The chart basis triple has bracket one, at every parameter. -/
theorem tripleBracket_twoMeetingLines_basis (param : ℝ × ℝ) :
    tripleBracket (twoMeetingLinesDirection param 0) (twoMeetingLinesDirection param 1)
      (twoMeetingLinesDirection param 3) = 1 := by
  simp [tripleBracket_eq, twoMeetingLinesDirection]

/-- So the independence clause of the over-levered closure is inhabited. -/
theorem tripleBracket_twoMeetingLines_basis_ne_zero (param : ℝ × ℝ) :
    tripleBracket (twoMeetingLinesDirection param 0) (twoMeetingLinesDirection param 1)
      (twoMeetingLinesDirection param 3) ≠ 0 := by
  rw [tripleBracket_twoMeetingLines_basis]
  norm_num

/-! ### The veto, made concrete on the chart basis

The three dual probes of the chart basis are the three coordinate vectors.  Each
one is blind to two basis labels and live on the third.  So the veto fires on
`{0,1,3}` with no side condition at all. -/

/-- **THE VETO ON THE CHART BASIS.**  If the chart basis triple dominates
strictly at a chart point, then all three of its labels are over-levered.  This
is the intersection of the veto with the counting law, in kernel. -/
theorem basisTriple_subset_overLevered_twoMeetingLines (param : ℝ × ℝ)
    (point : DirectionChartPoint 6)
    (hgap : (directionChartGap (twoMeetingLinesDirection param) point.mass point.weight
      ({0, 1, 3} : Finset (Fin 6))).PosDef) :
    point.weight 0
        < chartMassLeverage (twoMeetingLinesDirection param) point.mass 0
      ∧ point.weight 1
        < chartMassLeverage (twoMeetingLinesDirection param) point.mass 1
      ∧ point.weight 3
        < chartMassLeverage (twoMeetingLinesDirection param) point.mass 3 := by
  refine ⟨?_, ?_, ?_⟩
  · refine weight_lt_chartMassLeverage_twoMeetingLines param point _ 0 (by decide)
      ![1, 0, 0] ?_ ?_ hgap
    · intro other hmem hne
      have hcases : other = 0 ∨ other = 1 ∨ other = 3 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
      rcases hcases with rfl | rfl | rfl
      · exact absurd rfl hne
      · norm_num [twoMeetingLinesDirection, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons]
      · norm_num [twoMeetingLinesDirection, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons]
    · norm_num [twoMeetingLinesDirection, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
  · refine weight_lt_chartMassLeverage_twoMeetingLines param point _ 1 (by decide)
      ![0, 1, 0] ?_ ?_ hgap
    · intro other hmem hne
      have hcases : other = 0 ∨ other = 1 ∨ other = 3 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
      rcases hcases with rfl | rfl | rfl
      · norm_num [twoMeetingLinesDirection, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons]
      · exact absurd rfl hne
      · norm_num [twoMeetingLinesDirection, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons]
    · norm_num [twoMeetingLinesDirection, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]
  · refine weight_lt_chartMassLeverage_twoMeetingLines param point _ 3 (by decide)
      ![0, 0, 1] ?_ ?_ hgap
    · intro other hmem hne
      have hcases : other = 0 ∨ other = 1 ∨ other = 3 := by
        simpa [Finset.mem_insert, Finset.mem_singleton] using hmem
      rcases hcases with rfl | rfl | rfl
      · norm_num [twoMeetingLinesDirection, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons]
      · norm_num [twoMeetingLinesDirection, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
          Matrix.tail_cons]
      · exact absurd rfl hne
    · norm_num [twoMeetingLinesDirection, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
        Matrix.tail_cons]

/-! ## 2.  The two slabs, their collapse, their band, and the hole

The class carries two landed slab closures.  Each one discharges the whole
residual conclusion while it consumes NONE of the residual's own hypotheses.
This section names both, composes them, and measures what they leave. -/

/-- The light-complement slab of `Gtz.twoMeetingLinesResidual_of_min_complLeverage_lt`. -/
def TwoMeetingLinesComplLeverageSlab (design : WeightedDesign 6 3) (cap : ℝ) : Prop :=
  cap * (leverageOf (design.atom 0)
      + min (leverageOf (design.atom 1)) (leverageOf (design.atom 2))
      + min (leverageOf (design.atom 3)) (leverageOf (design.atom 4))) < 1 - cap

/-- The weighted-complement slab of
`Gtz.twoMeetingLinesResidual_of_min_weightedCompl_lt`. -/
def TwoMeetingLinesWeightedComplSlab (design : WeightedDesign 6 3) (cap : ℝ) : Prop :=
  design.weight 0 * leverageOf (design.atom 0)
    + min (design.weight 1 * leverageOf (design.atom 1))
          (design.weight 2 * leverageOf (design.atom 2))
    + min (design.weight 3 * leverageOf (design.atom 3))
          (design.weight 4 * leverageOf (design.atom 4)) < 1 - cap

/-- The joint coverage of the two slabs. -/
def TwoMeetingLinesSlabCovered (design : WeightedDesign 6 3) (cap : ℝ) : Prop :=
  TwoMeetingLinesComplLeverageSlab design cap ∨ TwoMeetingLinesWeightedComplSlab design cap

/-- A capped weight against a nonnegative leverage never beats the cap. -/
theorem min_weightedLeverage_le_cap_mul_min_leverage {cap leftWeight rightWeight
    leftLeverage rightLeverage : ℝ}
    (hleftCap : leftWeight ≤ cap) (hrightCap : rightWeight ≤ cap)
    (hleftNonneg : 0 ≤ leftLeverage) (hrightNonneg : 0 ≤ rightLeverage) :
    min (leftWeight * leftLeverage) (rightWeight * rightLeverage)
      ≤ cap * min leftLeverage rightLeverage := by
  rcases le_total leftLeverage rightLeverage with hle | hle
  · rw [min_eq_left hle]
    exact le_trans (min_le_left _ _) (mul_le_mul_of_nonneg_right hleftCap hleftNonneg)
  · rw [min_eq_right hle]
    exact le_trans (min_le_right _ _) (mul_le_mul_of_nonneg_right hrightCap hrightNonneg)

/-- **THE SLAB COLLAPSE, ONE DIRECTION.**  Every design in the light-complement
slab lies in the weighted-complement slab.  The weight of a label never exceeds
the cap, and leverages are sums of squares. -/
theorem twoMeetingLinesWeightedComplSlab_of_complLeverageSlab
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hslab : TwoMeetingLinesComplLeverageSlab design cap) :
    TwoMeetingLinesWeightedComplSlab design cap := by
  have hzero : design.weight 0 * leverageOf (design.atom 0)
      ≤ cap * leverageOf (design.atom 0) :=
    mul_le_mul_of_nonneg_right (hcap 0) (leverageOf_nonneg _)
  have hone := min_weightedLeverage_le_cap_mul_min_leverage (hcap 1) (hcap 2)
    (leverageOf_nonneg (design.atom 1)) (leverageOf_nonneg (design.atom 2))
  have hthree := min_weightedLeverage_le_cap_mul_min_leverage (hcap 3) (hcap 4)
    (leverageOf_nonneg (design.atom 3)) (leverageOf_nonneg (design.atom 4))
  have hexpand : cap * (leverageOf (design.atom 0)
        + min (leverageOf (design.atom 1)) (leverageOf (design.atom 2))
        + min (leverageOf (design.atom 3)) (leverageOf (design.atom 4)))
      = cap * leverageOf (design.atom 0)
        + cap * min (leverageOf (design.atom 1)) (leverageOf (design.atom 2))
        + cap * min (leverageOf (design.atom 3)) (leverageOf (design.atom 4)) := by
    ring
  rw [TwoMeetingLinesComplLeverageSlab, hexpand] at hslab
  rw [TwoMeetingLinesWeightedComplSlab]
  linarith

/-- **THE JOINT COVERAGE IS ONE SLAB.**  The disjunction of the two landed slabs
is the weighted-complement slab alone.  This is an EQUIVALENCE, and it says that
the first slab adds nothing to the second. -/
theorem twoMeetingLinesSlabCovered_iff_weightedComplSlab
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap) :
    TwoMeetingLinesSlabCovered design cap ↔ TwoMeetingLinesWeightedComplSlab design cap := by
  constructor
  · rintro (hcompl | hweighted)
    · exact twoMeetingLinesWeightedComplSlab_of_complLeverageSlab design hcap hcompl
    · exact hweighted
  · intro hweighted
    exact Or.inr hweighted

/-! ### The band of the first slab

Every weight cap of a `(6,3)` design is at least one sixth, because six capped
weights must sum to one.  On the heavy stratum the first slab forces a cap below
one quarter.  So the first slab lives in a band of width one twelfth. -/

/-- Six capped weights that sum to one force a cap of at least one sixth. -/
theorem one_le_six_mul_cap (design : WeightedDesign 6 3) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap) : (1 : ℝ) ≤ 6 * cap := by
  have hone : ∑ label : Fin 6, design.weight label = 1 := design.weight_sum_one
  rw [Fin.sum_univ_six] at hone
  have h0 := hcap 0
  have h1 := hcap 1
  have h2 := hcap 2
  have h3 := hcap 3
  have h4 := hcap 4
  have h5 := hcap 5
  linarith

/-- **THE FIRST SLAB NEEDS A CAP BELOW ONE QUARTER.**  On the heavy stratum the
three complement leverages total at least three, so the slab inequality forces
four caps below one. -/
theorem cap_lt_quarter_of_complLeverageSlab (design : WeightedDesign 6 3) {cap : ℝ}
    (hcapPos : 0 < cap)
    (hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (hslab : TwoMeetingLinesComplLeverageSlab design cap) :
    cap < 1 / 4 := by
  have hzero := hheavy 0
  have hone : (1 : ℝ) ≤ min (leverageOf (design.atom 1)) (leverageOf (design.atom 2)) :=
    le_min (hheavy 1) (hheavy 2)
  have hthree : (1 : ℝ) ≤ min (leverageOf (design.atom 3)) (leverageOf (design.atom 4)) :=
    le_min (hheavy 3) (hheavy 4)
  rw [TwoMeetingLinesComplLeverageSlab] at hslab
  nlinarith [hslab, hcapPos, hzero, hone, hthree]

/-- **THE BAND, IN ONE STATEMENT.**  On the heavy stratum the light-complement
slab is confined to caps in the half-open band from one sixth to one quarter. -/
theorem complLeverageSlab_band (design : WeightedDesign 6 3) {cap : ℝ}
    (hcap : ∀ label, design.weight label ≤ cap)
    (hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (hslab : TwoMeetingLinesComplLeverageSlab design cap) :
    1 / 6 ≤ cap ∧ cap < 1 / 4 := by
  have hsix := one_le_six_mul_cap design hcap
  have hcapPos : 0 < cap := by
    have hpos := design.weight_pos 0
    have hle := hcap 0
    linarith
  exact ⟨by linarith, cap_lt_quarter_of_complLeverageSlab design hcapPos hheavy hslab⟩

/-! ### The two slabs, spent inside the residual's own antecedent -/

/-- **THE COMPOSED SLAB CLOSURE.**  Inside the full antecedent of the registry
residual, either slab gives the residual's conclusion.  Strict reduction. -/
theorem twoMeetingLinesTransversalStrict_of_slabCovered
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (hweightHeavy : ∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel)
    (hcapBlind : IsCapBlindSpot design)
    (hweak : ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator)
    (hcovered : TwoMeetingLinesSlabCovered design cap) :
    TwoMeetingLinesTransversalStrict design := by
  rcases hcovered with hcompl | hweighted
  · exact twoMeetingLinesResidual_of_min_complLeverage_lt design hcap hcompl hpattern hheavy
      hweightHeavy hcapBlind hweak
  · exact twoMeetingLinesResidual_of_min_weightedCompl_lt design hcap hweighted hheavy
      hweightHeavy hweak

/-- **THE SAME CONCLUSION AS TWELVE POLYNOMIAL INEQUALITIES.**  The landed
criterion `Gtz.twoMeetingLinesTransversalStrict_iff_invariants` rewrites the whole
residual conclusion in the leverage sum, the pair-area sum and the bracket. -/
theorem twoMeetingLines_invariants_of_slabCovered
    (design : WeightedDesign 6 3) {cap : ℝ} (hcap : ∀ label, design.weight label ≤ cap)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (hweightHeavy : ∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel)
    (hcapBlind : IsCapBlindSpot design)
    (hweak : ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator)
    (hcovered : TwoMeetingLinesSlabCovered design cap) :
    ((0 < tripleLeverageSum (design.atom 1) (design.atom 3) (design.atom 5) - 3
        ∧ 0 < triplePairAreaSum (design.atom 1) (design.atom 3) (design.atom 5)
            - 2 * tripleLeverageSum (design.atom 1) (design.atom 3) (design.atom 5) + 3
        ∧ 0 < atomBracket design 1 3 5 ^ 2
            - triplePairAreaSum (design.atom 1) (design.atom 3) (design.atom 5)
            + tripleLeverageSum (design.atom 1) (design.atom 3) (design.atom 5) - 1)
      ∨ (0 < tripleLeverageSum (design.atom 1) (design.atom 4) (design.atom 5) - 3
        ∧ 0 < triplePairAreaSum (design.atom 1) (design.atom 4) (design.atom 5)
            - 2 * tripleLeverageSum (design.atom 1) (design.atom 4) (design.atom 5) + 3
        ∧ 0 < atomBracket design 1 4 5 ^ 2
            - triplePairAreaSum (design.atom 1) (design.atom 4) (design.atom 5)
            + tripleLeverageSum (design.atom 1) (design.atom 4) (design.atom 5) - 1)
      ∨ (0 < tripleLeverageSum (design.atom 2) (design.atom 3) (design.atom 5) - 3
        ∧ 0 < triplePairAreaSum (design.atom 2) (design.atom 3) (design.atom 5)
            - 2 * tripleLeverageSum (design.atom 2) (design.atom 3) (design.atom 5) + 3
        ∧ 0 < atomBracket design 2 3 5 ^ 2
            - triplePairAreaSum (design.atom 2) (design.atom 3) (design.atom 5)
            + tripleLeverageSum (design.atom 2) (design.atom 3) (design.atom 5) - 1)
      ∨ (0 < tripleLeverageSum (design.atom 2) (design.atom 4) (design.atom 5) - 3
        ∧ 0 < triplePairAreaSum (design.atom 2) (design.atom 4) (design.atom 5)
            - 2 * tripleLeverageSum (design.atom 2) (design.atom 4) (design.atom 5) + 3
        ∧ 0 < atomBracket design 2 4 5 ^ 2
            - triplePairAreaSum (design.atom 2) (design.atom 4) (design.atom 5)
            + tripleLeverageSum (design.atom 2) (design.atom 4) (design.atom 5) - 1)) :=
  (twoMeetingLinesTransversalStrict_iff_invariants design).mp
    (twoMeetingLinesTransversalStrict_of_slabCovered design hcap hpattern hheavy hweightHeavy
      hcapBlind hweak hcovered)

/-! ### The hole: a landed witness escapes both slabs

`Gtz.twinFailureDesign` fires the pattern, heaviness and a weak dominator.  Its
leverages are `2, 2, 2, 9, 9, 6` and its weights are ninetieths.  The largest
weight is one third, so every admissible cap is at least one third.  The band
above already kills the first slab there.  The second slab dies on an exact
arithmetic reading. -/

/-- The six leverages of the landed witness, exactly. -/
theorem twinFailure_leverage_values :
    leverageOf (twinFailureDesign.atom 0) = 2 ∧ leverageOf (twinFailureDesign.atom 1) = 2
      ∧ leverageOf (twinFailureDesign.atom 2) = 2 ∧ leverageOf (twinFailureDesign.atom 3) = 9
      ∧ leverageOf (twinFailureDesign.atom 4) = 9 ∧ leverageOf (twinFailureDesign.atom 5) = 6 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [leverageOf, Fin.sum_univ_three, twinFailureDesign, twinFailureAtom,
      Matrix.cons_val_two]

/-- The five weights the slabs read, exactly. -/
theorem twinFailure_weight_values :
    twinFailureDesign.weight 0 = 1 / 3 ∧ twinFailureDesign.weight 1 = 1 / 5
      ∧ twinFailureDesign.weight 2 = 3 / 10 ∧ twinFailureDesign.weight 3 = 2 / 45
      ∧ twinFailureDesign.weight 4 = 1 / 15 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> norm_num [twinFailureDesign, twinFailureWeight]

/-- Every admissible cap of the witness is at least one third. -/
theorem twinFailure_third_le_cap {cap : ℝ}
    (hcap : ∀ label, twinFailureDesign.weight label ≤ cap) : (1 : ℝ) / 3 ≤ cap := by
  obtain ⟨hw0, -, -, -, -⟩ := twinFailure_weight_values
  have hzero := hcap 0
  rw [hw0] at hzero
  exact hzero

/-- **THE WITNESS ESCAPES THE FIRST SLAB.** -/
theorem twinFailure_not_complLeverageSlab {cap : ℝ}
    (hcap : ∀ label, twinFailureDesign.weight label ≤ cap) :
    ¬ TwoMeetingLinesComplLeverageSlab twinFailureDesign cap := by
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := twinFailure_leverage_values
  have hcapLarge := twinFailure_third_le_cap hcap
  rw [TwoMeetingLinesComplLeverageSlab, h0, h1, h2, h3, h4, min_self, min_self]
  intro hcontra
  linarith

/-- **THE WITNESS ESCAPES THE SECOND SLAB.**  Its weighted complement reads
twenty-two fifteenths, and the ceiling is at most two thirds. -/
theorem twinFailure_not_weightedComplSlab {cap : ℝ}
    (hcap : ∀ label, twinFailureDesign.weight label ≤ cap) :
    ¬ TwoMeetingLinesWeightedComplSlab twinFailureDesign cap := by
  obtain ⟨h0, h1, h2, h3, h4, -⟩ := twinFailure_leverage_values
  obtain ⟨hw0, hw1, hw2, hw3, hw4⟩ := twinFailure_weight_values
  have hcapLarge := twinFailure_third_le_cap hcap
  have hzero : twinFailureDesign.weight 0 * leverageOf (twinFailureDesign.atom 0) = 2 / 3 := by
    rw [hw0, h0]; norm_num
  have hone : (2 : ℝ) / 5
      ≤ min (twinFailureDesign.weight 1 * leverageOf (twinFailureDesign.atom 1))
            (twinFailureDesign.weight 2 * leverageOf (twinFailureDesign.atom 2)) := by
    refine le_min ?_ ?_
    · rw [hw1, h1]; norm_num
    · rw [hw2, h2]; norm_num
  have hthree : (2 : ℝ) / 5
      ≤ min (twinFailureDesign.weight 3 * leverageOf (twinFailureDesign.atom 3))
            (twinFailureDesign.weight 4 * leverageOf (twinFailureDesign.atom 4)) := by
    refine le_min ?_ ?_
    · rw [hw3, h3]; norm_num
    · rw [hw4, h4]; norm_num
  rw [TwoMeetingLinesWeightedComplSlab, hzero]
  intro hcontra
  linarith

/-- **THE SLABS DO NOT COVER THE RESIDUAL.**  There is a design that fires the
pattern, fires heaviness, carries a weak dominator, and lies outside the joint
slab coverage at EVERY admissible cap.  So the composed closure above leaves a
nonempty hole, and the axiom does not fall to the two slabs. -/
theorem exists_twoMeetingLines_heavy_weaklyDominated_outside_slabs :
    ∃ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) ∧
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) ∧
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) ∧
      ∀ cap : ℝ, (∀ label, design.weight label ≤ cap) →
        ¬ TwoMeetingLinesSlabCovered design cap :=
  ⟨twinFailureDesign, twinFailureDesign_hasLinePattern, twinFailureDesign_allHeavy,
    twinFailureDesign_hasWeakDominator, fun _cap hcap hcovered => by
      rcases hcovered with hcompl | hweighted
      · exact twinFailure_not_complLeverageSlab hcap hcompl
      · exact twinFailure_not_weightedComplSlab hcap hweighted⟩

/-! ## 3.  The chart road, run to the registry Prop

The registry text said that no chart exists for this pattern.  That clause is
false.  The covering half is unconditional and it does not use primitivity.  The
tree carried the road as far as the on-path spelling only.  The step below runs
it to the Prop the registry axiom actually states. -/

/-- **THE END-TO-END CHART ROAD.**  Tie-freeness of the two-parameter chart at
every admissible parameter gives the registry Prop of this class.  Wiring
composition, and the only open half is the analytic one. -/
theorem twoMeetingLinesSeededTransversal_of_chart
    (hchart : ∀ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param →
      DirectionChartIsTieFree (twoMeetingLinesDirection param)) :
    TwoMeetingLinesSeededTransversal :=
  twoMeetingLinesSeededTransversal_iff.mpr (twoMeetingLinesOnPath_of_chart hchart)

/-- **THE SAME ROAD, ALL FIVE SPELLINGS AT ONCE.** -/
theorem twoMeetingLines_allSpellings_of_chart
    (hchart : ∀ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param →
      DirectionChartIsTieFree (twoMeetingLinesDirection param)) :
    TwoMeetingLinesSeededTransversal
      ∧ TwoMeetingLinesTenthHeavyJointBlindTransversal
      ∧ StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])
      ∧ StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])
      ∧ PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) := by
  have honPath := twoMeetingLinesOnPath_of_chart hchart
  have hstratum := twoMeetingLinesOnPath_iff_stratumIsTieFree.mp honPath
  have hstressFree := twoMeetingLines_stratumIsTieFree_iff_stressFreeStratumIsTieFree.mp hstratum
  exact ⟨twoMeetingLinesSeededTransversal_iff.mpr honPath, honPath, hstratum, hstressFree,
    twoMeetingLines_heavyWeakToStrict_iff.mpr hstressFree⟩

/-! ## 4.  The five-name collapse

The stratum is uniformly stress-free, by `Gtz.stratumIsStressFree_twoMeetingLines`.
So `Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree` is NOT one-way here, and
the tree already carries the converse and two of the other Iff steps.  What no
module carries is the step that names the registry Prop.  The ring below closes
it, and it adds NO strength: it is one statement under five names. -/

/-- **FIVE NAMES, ONE STATEMENT.**  Each adjacent pair of spellings of this class
is an equivalence.  The first Iff is the one that names the registry Prop, and it
was composed with the others nowhere. -/
theorem twoMeetingLines_fiveNames_collapse :
    (TwoMeetingLinesSeededTransversal ↔ TwoMeetingLinesTenthHeavyJointBlindTransversal)
      ∧ (TwoMeetingLinesTenthHeavyJointBlindTransversal
          ↔ StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
      ∧ (StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])
          ↔ StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
      ∧ (StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])
          ↔ PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])) :=
  ⟨twoMeetingLinesSeededTransversal_iff, twoMeetingLinesOnPath_iff_stratumIsTieFree,
    twoMeetingLines_stratumIsTieFree_iff_stressFreeStratumIsTieFree,
    twoMeetingLines_heavyWeakToStrict_iff.symm⟩

/-- **THE HEADLINE COLLAPSE.**  The registry Prop of this class is the uniform
weak-to-strict Prop at its own pattern.  Equivalence, no strength added. -/
theorem twoMeetingLinesSeededTransversal_iff_heavyWeakToStrict :
    TwoMeetingLinesSeededTransversal
      ↔ PatternHeavyWeakToStrict (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  twoMeetingLinesSeededTransversal_iff.trans
    (twoMeetingLinesOnPath_iff_stratumIsTieFree.trans
      (twoMeetingLines_stratumIsTieFree_iff_stressFreeStratumIsTieFree.trans
        twoMeetingLines_heavyWeakToStrict_iff.symm))

/-- The stress-free hypothesis that powers the third Iff, named here so that the
collapse carries its own reason. -/
theorem twoMeetingLines_stratum_is_stressFree :
    StratumIsStressFree (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  stratumIsStressFree_twoMeetingLines

/-! ## 5.  Inhabitants, and the rigidity kernel spent

The traps demand an inhabitant for every antecedent, or a plain statement that
none was found.  This section supplies what is in kernel. -/

/-- **THE RESIDUAL ANTECEDENT IS INHABITED ON ITS THREE DESIGN CLAUSES.**  The
landed witness fires the pattern, heaviness and the weak dominator, and it also
satisfies the residual's conclusion through the mixed triple `{2,4,5}`. -/
theorem twinFailureDesign_fires_antecedent_and_conclusion :
    HasLinePattern twinFailureDesign
        (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])
      ∧ (∀ label : Fin 6, 1 ≤ leverageOf (twinFailureDesign.atom label))
      ∧ (∃ dominator : Finset (Fin 6), dominator.card = 3
          ∧ Dominates twinFailureDesign dominator)
      ∧ TwoMeetingLinesTransversalStrict twinFailureDesign :=
  ⟨twinFailureDesign_hasLinePattern, twinFailureDesign_allHeavy,
    twinFailureDesign_hasWeakDominator,
    Or.inr (Or.inr (Or.inr twinFailure_mixedTripleGap_posDef))⟩

/-- The admissible parameter range of the chart is inhabited, so the chart
hypothesis of section 3 is not vacuous on its parameter clause. -/
theorem twoMeetingLines_chartRange_inhabited :
    ∃ param : ℝ × ℝ, IsAdmissibleTwoMeetingLinesParameter param :=
  ⟨_, isAdmissibleTwoMeetingLinesParameter_two_three⟩

/-! ### The angle identity, spent

`Gtz.twoMeetingLines_angle_identity` runs on exactly the two unit normals the
registry residual hands over, and it had no consumer.  The reading below is its
sharpest one-line consequence: perpendicular line planes kill one Parseval
defect outright. -/

/-- **PERPENDICULAR LINE PLANES KILL A DEFECT.**  If the two line normals are
orthogonal, then one line's private pair carries the whole squared normal of the
other line.  Strict reduction from the landed angle identity. -/
theorem twoMeetingLines_perpendicular_forces_defect (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hperpendicular : normalFirst ⬝ᵥ normalSecond = 0) :
    normalFirst ⬝ᵥ normalFirst
        = design.weight 3 * (design.atom 3 ⬝ᵥ normalFirst) ^ 2
          + design.weight 4 * (design.atom 4 ⬝ᵥ normalFirst) ^ 2
      ∨ normalSecond ⬝ᵥ normalSecond
        = design.weight 1 * (design.atom 1 ⬝ᵥ normalSecond) ^ 2
          + design.weight 2 * (design.atom 2 ⬝ᵥ normalSecond) ^ 2 := by
  have hidentity := twoMeetingLines_angle_identity design normalFirst normalSecond
    horthFirst horthSecond
  have hzero : (normalFirst ⬝ᵥ normalFirst
        - design.weight 3 * (design.atom 3 ⬝ᵥ normalFirst) ^ 2
        - design.weight 4 * (design.atom 4 ⬝ᵥ normalFirst) ^ 2)
      * (normalSecond ⬝ᵥ normalSecond
        - design.weight 1 * (design.atom 1 ⬝ᵥ normalSecond) ^ 2
        - design.weight 2 * (design.atom 2 ⬝ᵥ normalSecond) ^ 2) = 0 := by
    rw [← hidentity, hperpendicular]
    norm_num
  rcases mul_eq_zero.mp hzero with hleft | hright
  · left; linarith
  · right; linarith

/-! ## 6.  NEW MATHEMATICS: the transversal gap is positive definite on the
shared-atom plane

Everything before this section is composition.  This section is new.

The shared atom `0` lies on both lines, so it is orthogonal to both line normals.
The two normals therefore span the plane orthogonal to the shared atom.  The
theorem below says that ONE named transversal has a strictly positive gap form on
that WHOLE plane, at every design of the stratum.  No weight cap, no heaviness, no
weak dominator and no chart are used.  Only the line pattern and the two normals
enter.

The mechanism is a two-by-two determinant.  Write the gap of the transversal in
the basis of the two normals.  Its two diagonal entries are the two Parseval
defects, and each one is strictly positive because the maximal private reading
carries more than its own weighted share.  Its off-diagonal entry is EXACTLY
`(1 - w5)` times the product of the two open readings, because the meeting
identity eliminates the angle.  The discriminant then factors, and every leftover
term carries a reading that the line pattern forbids to vanish.

WHAT THIS LEAVES.  A symmetric three-by-three form that is positive definite on a
plane has at most one nonpositive eigenvalue.  So the whole class residual is now
ONE scalar: the determinant of the same named gap.  That is the sharpest reduction
this class carries. -/

/-- A reading that vanishes at a line normal makes a forbidden triple dependent.
The line pattern then refutes it.  This is the source of every nonvanishing fact
in this section. -/
theorem twoMeetingLines_reading_ne_zero_of_pattern (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normal : Fin 3 → ℝ) (hnormalNe : normal ≠ 0)
    (lineLeft lineRight target : Fin 6)
    (hleftRight : lineLeft ≠ lineRight) (hleftTarget : lineLeft ≠ target)
    (hrightTarget : lineRight ≠ target)
    (hforbidden : ¬ lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]
      lineLeft lineRight target)
    (hleftOrth : design.atom lineLeft ⬝ᵥ normal = 0)
    (hrightOrth : design.atom lineRight ⬝ᵥ normal = 0) :
    design.atom target ⬝ᵥ normal ≠ 0 := by
  intro hzero
  refine hforbidden ((hpattern lineLeft lineRight target hleftRight hleftTarget
    hrightTarget).mp ?_)
  simpa [atomBracket] using
    tripleBracket_eq_zero_of_commonOrthogonal hnormalNe hleftOrth hrightOrth hzero

/-- The scalar core of the plane positivity.  A binary quadratic form with a
positive leading entry and a negative discriminant is positive away from the
origin. -/
theorem quadratic_form_pos_of_disc {diagFirst diagSecond offDiag first second : ℝ}
    (hdiagPos : 0 < diagFirst) (hdisc : offDiag ^ 2 < diagFirst * diagSecond)
    (hnonzero : first ≠ 0 ∨ second ≠ 0) :
    0 < first ^ 2 * diagFirst + second ^ 2 * diagSecond + 2 * first * second * offDiag := by
  rcases eq_or_ne second 0 with rfl | hsecond
  · have hfirst : first ≠ 0 := by
      rcases hnonzero with h | h
      · exact h
      · exact absurd rfl h
    have hsq : 0 < first ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hfirst))
    nlinarith [hdiagPos, hsq]
  · have hsq : 0 < second ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hsecond))
    nlinarith [sq_nonneg (diagFirst * first + offDiag * second), hdiagPos,
      mul_pos (sub_pos.mpr hdisc) hsq]

/-- **THE FIRST NORMAL SEES ALL THREE OFF-LINE ATOMS.**  At a normal of the first
line the two private atoms of the second line and the open atom all read nonzero.
The pattern alone forces it. -/
theorem twoMeetingLines_firstNormal_readings_ne_zero (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normalFirst : Fin 3 → ℝ) (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0) :
    design.atom 3 ⬝ᵥ normalFirst ≠ 0 ∧ design.atom 4 ⬝ᵥ normalFirst ≠ 0
      ∧ design.atom 5 ⬝ᵥ normalFirst ≠ 0 := by
  have hne := ne_zero_of_dotProduct_self_eq_one hunitFirst
  have hzero := horthFirst 0 (by decide)
  have hone := horthFirst 1 (by decide)
  refine ⟨?_, ?_, ?_⟩ <;>
    exact twoMeetingLines_reading_ne_zero_of_pattern design hpattern normalFirst hne
      0 1 _ (by decide) (by decide) (by decide) (by decide) hzero hone

/-- **THE SECOND NORMAL SEES ALL THREE OFF-LINE ATOMS.**  The mirror statement at
a normal of the second line. -/
theorem twoMeetingLines_secondNormal_readings_ne_zero (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normalSecond : Fin 3 → ℝ) (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0) :
    design.atom 1 ⬝ᵥ normalSecond ≠ 0 ∧ design.atom 2 ⬝ᵥ normalSecond ≠ 0
      ∧ design.atom 5 ⬝ᵥ normalSecond ≠ 0 := by
  have hne := ne_zero_of_dotProduct_self_eq_one hunitSecond
  have hzero := horthSecond 0 (by decide)
  have hthree := horthSecond 3 (by decide)
  refine ⟨?_, ?_, ?_⟩ <;>
    exact twoMeetingLines_reading_ne_zero_of_pattern design hpattern normalSecond hne
      0 3 _ (by decide) (by decide) (by decide) (by decide) hzero hthree

/-- **THE TWO LINE PLANES ARE NEVER PERPENDICULAR.**  The meeting identity turns
the two nonvanishing open readings into a nonzero angle.  So the deficit product
of `Gtz.twoMeetingLines_angle_identity` is strictly positive on the whole
stratum. -/
theorem twoMeetingLines_normals_not_perpendicular (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0) :
    normalFirst ⬝ᵥ normalSecond ≠ 0 := by
  obtain ⟨-, -, hopenFirst⟩ := twoMeetingLines_firstNormal_readings_ne_zero design hpattern
    normalFirst hunitFirst horthFirst
  obtain ⟨-, -, hopenSecond⟩ := twoMeetingLines_secondNormal_readings_ne_zero design hpattern
    normalSecond hunitSecond horthSecond
  rw [← twoMeetingLines_meeting_identity design normalFirst normalSecond horthFirst horthSecond]
  exact mul_ne_zero (ne_of_gt (design.weight_pos 5)) (mul_ne_zero hopenFirst hopenSecond)

/-! ### The gap form of a transversal on the plane of the two normals -/

/-- The gap form of the transversal `{first, second, 5}` at a combination of the
two normals, written out.  The first label dies at the first normal and the
second label dies at the second normal, so only three squares survive. -/
theorem twoMeetingLines_transversal_planeForm (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (firstLabel secondLabel : Fin 6)
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstOpen : firstLabel ≠ 5)
    (hsecondOpen : secondLabel ≠ 5)
    (hfirstOrth : design.atom firstLabel ⬝ᵥ normalFirst = 0)
    (hsecondOrth : design.atom secondLabel ⬝ᵥ normalSecond = 0)
    (weightFirst weightSecond : ℝ) :
    (weightFirst • normalFirst + weightSecond • normalSecond)
        ⬝ᵥ ((subsetSum design ({firstLabel, secondLabel, 5} : Finset (Fin 6)) - 1)
          *ᵥ (weightFirst • normalFirst + weightSecond • normalSecond))
      = weightFirst ^ 2 * ((design.atom secondLabel ⬝ᵥ normalFirst) ^ 2
            + (design.atom 5 ⬝ᵥ normalFirst) ^ 2 - 1)
        + weightSecond ^ 2 * ((design.atom firstLabel ⬝ᵥ normalSecond) ^ 2
            + (design.atom 5 ⬝ᵥ normalSecond) ^ 2 - 1)
        + 2 * weightFirst * weightSecond
            * ((design.atom 5 ⬝ᵥ normalFirst) * (design.atom 5 ⬝ᵥ normalSecond)
              - normalFirst ⬝ᵥ normalSecond) := by
  classical
  set probe := weightFirst • normalFirst + weightSecond • normalSecond with hprobe
  have hread : ∀ label : Fin 6, design.atom label ⬝ᵥ probe
      = weightFirst * (design.atom label ⬝ᵥ normalFirst)
        + weightSecond * (design.atom label ⬝ᵥ normalSecond) := by
    intro label
    rw [hprobe, dotProduct_add, dotProduct_smul, dotProduct_smul, smul_eq_mul, smul_eq_mul]
  have hcross : normalSecond ⬝ᵥ normalFirst = normalFirst ⬝ᵥ normalSecond :=
    dotProduct_comm _ _
  have hself : probe ⬝ᵥ probe = weightFirst ^ 2 + weightSecond ^ 2
      + 2 * weightFirst * weightSecond * (normalFirst ⬝ᵥ normalSecond) := by
    rw [hprobe]
    simp only [add_dotProduct, dotProduct_add, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hunitFirst, hunitSecond, hcross]
    ring
  have hnotMemFirst : firstLabel ∉ ({secondLabel, 5} : Finset (Fin 6)) := by
    simp [hfirstSecond, hfirstOpen]
  have hnotMemSecond : secondLabel ∉ ({(5 : Fin 6)} : Finset (Fin 6)) := by
    simp [hsecondOpen]
  have hsum : (∑ label ∈ ({firstLabel, secondLabel, 5} : Finset (Fin 6)),
        (design.atom label ⬝ᵥ probe) ^ 2)
      = (design.atom firstLabel ⬝ᵥ probe) ^ 2 + (design.atom secondLabel ⬝ᵥ probe) ^ 2
        + (design.atom 5 ⬝ᵥ probe) ^ 2 := by
    rw [Finset.sum_insert hnotMemFirst, Finset.sum_insert hnotMemSecond,
      Finset.sum_singleton, add_assoc]
  rw [Matrix.sub_mulVec, dotProduct_sub, dotProduct_subsetSum_mulVec_of_finset,
    Matrix.one_mulVec, hsum, hself, hread firstLabel, hread secondLabel, hread 5,
    hfirstOrth, hsecondOrth]
  ring

/-- **THE DIAGONAL ENTRIES ARE STRICTLY POSITIVE.**  At the first normal the whole
Parseval energy sits on the second line's privates and the open atom.  The maximal
private reading beats its own weighted share, so the transversal that carries it
has a strictly positive gap there.  NO weight cap is used, which is what
separates this from `Gtz.exists_transversal_gap_pos_at_lineOneNormal`. -/
theorem twoMeetingLines_firstDefect_pos (design : WeightedDesign 6 3)
    (normalFirst : Fin 3 → ℝ) (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (secondLabel : Fin 6)
    (hthreeMax : (design.atom 3 ⬝ᵥ normalFirst) ^ 2
      ≤ (design.atom secondLabel ⬝ᵥ normalFirst) ^ 2)
    (hfourMax : (design.atom 4 ⬝ᵥ normalFirst) ^ 2
      ≤ (design.atom secondLabel ⬝ᵥ normalFirst) ^ 2)
    (hsecondNe : design.atom secondLabel ⬝ᵥ normalFirst ≠ 0) :
    (1 - design.weight 3 - design.weight 4) * (design.atom secondLabel ⬝ᵥ normalFirst) ^ 2
        + (1 - design.weight 5) * (design.atom 5 ⬝ᵥ normalFirst) ^ 2
      ≤ (design.atom secondLabel ⬝ᵥ normalFirst) ^ 2
        + (design.atom 5 ⬝ᵥ normalFirst) ^ 2 - 1 := by
  have hlaw := twoMeetingLines_firstNormal_unitLaw design normalFirst horthFirst
  rw [hunitFirst] at hlaw
  have hthreePos := design.weight_pos 3
  have hfourPos := design.weight_pos 4
  nlinarith [hlaw, mul_le_mul_of_nonneg_left hthreeMax hthreePos.le,
    mul_le_mul_of_nonneg_left hfourMax hfourPos.le]

/-- The mirror bound at the second normal. -/
theorem twoMeetingLines_secondDefect_pos (design : WeightedDesign 6 3)
    (normalSecond : Fin 3 → ℝ) (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (firstLabel : Fin 6)
    (honeMax : (design.atom 1 ⬝ᵥ normalSecond) ^ 2
      ≤ (design.atom firstLabel ⬝ᵥ normalSecond) ^ 2)
    (htwoMax : (design.atom 2 ⬝ᵥ normalSecond) ^ 2
      ≤ (design.atom firstLabel ⬝ᵥ normalSecond) ^ 2)
    (hfirstNe : design.atom firstLabel ⬝ᵥ normalSecond ≠ 0) :
    (1 - design.weight 1 - design.weight 2) * (design.atom firstLabel ⬝ᵥ normalSecond) ^ 2
        + (1 - design.weight 5) * (design.atom 5 ⬝ᵥ normalSecond) ^ 2
      ≤ (design.atom firstLabel ⬝ᵥ normalSecond) ^ 2
        + (design.atom 5 ⬝ᵥ normalSecond) ^ 2 - 1 := by
  have hlaw := twoMeetingLines_secondNormal_unitLaw design normalSecond horthSecond
  rw [hunitSecond] at hlaw
  have honePos := design.weight_pos 1
  have htwoPos := design.weight_pos 2
  nlinarith [hlaw, mul_le_mul_of_nonneg_left honeMax honePos.le,
    mul_le_mul_of_nonneg_left htwoMax htwoPos.le]

/-- The three weight complements that drive the discriminant are strictly
positive, because six positive weights sum to one. -/
theorem twoMeetingLines_weightComplements_pos (design : WeightedDesign 6 3) :
    0 < 1 - design.weight 3 - design.weight 4
      ∧ 0 < 1 - design.weight 1 - design.weight 2
      ∧ 0 < 1 - design.weight 5 := by
  have hone : ∑ label : Fin 6, design.weight label = 1 := design.weight_sum_one
  rw [Fin.sum_univ_six] at hone
  have h0 := design.weight_pos 0
  have h1 := design.weight_pos 1
  have h2 := design.weight_pos 2
  have h3 := design.weight_pos 3
  have h4 := design.weight_pos 4
  have h5 := design.weight_pos 5
  exact ⟨by linarith, by linarith, by linarith⟩

/-- **THE HEADLINE.  THE MAXIMAL TRANSVERSAL GAP IS POSITIVE DEFINITE ON THE PLANE
OF THE TWO NORMALS.**

That plane is the plane orthogonal to the shared atom, because the shared atom
lies on both lines.  The statement carries NO weight cap, NO heaviness, NO weak
dominator and NO chart.  It holds at every design of the stratum, at every pair
of unit line normals, and at every nonzero combination of them.

The proof is a two-by-two discriminant.  The two diagonal defects are bounded
below by the maximal private readings, the off-diagonal entry is exactly the
open-reading product scaled by `1 - w5` after the meeting identity eliminates the
angle, and the leftover of the discriminant is a sum of three products of
readings that the line pattern forbids to vanish. -/
theorem twoMeetingLines_transversalGap_pos_on_normalPlane (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (firstLabel secondLabel : Fin 6)
    (hfirstMem : firstLabel = 1 ∨ firstLabel = 2)
    (hsecondMem : secondLabel = 3 ∨ secondLabel = 4)
    (honeMax : (design.atom 1 ⬝ᵥ normalSecond) ^ 2
      ≤ (design.atom firstLabel ⬝ᵥ normalSecond) ^ 2)
    (htwoMax : (design.atom 2 ⬝ᵥ normalSecond) ^ 2
      ≤ (design.atom firstLabel ⬝ᵥ normalSecond) ^ 2)
    (hthreeMax : (design.atom 3 ⬝ᵥ normalFirst) ^ 2
      ≤ (design.atom secondLabel ⬝ᵥ normalFirst) ^ 2)
    (hfourMax : (design.atom 4 ⬝ᵥ normalFirst) ^ 2
      ≤ (design.atom secondLabel ⬝ᵥ normalFirst) ^ 2)
    (coeffFirst coeffSecond : ℝ) (hnonzero : coeffFirst ≠ 0 ∨ coeffSecond ≠ 0) :
    0 < (coeffFirst • normalFirst + coeffSecond • normalSecond)
      ⬝ᵥ ((subsetSum design ({firstLabel, secondLabel, 5} : Finset (Fin 6)) - 1)
        *ᵥ (coeffFirst • normalFirst + coeffSecond • normalSecond)) := by
  obtain ⟨hthreeNe, hfourNe, hopenFirstNe⟩ :=
    twoMeetingLines_firstNormal_readings_ne_zero design hpattern normalFirst hunitFirst horthFirst
  obtain ⟨honeNe, htwoNe, hopenSecondNe⟩ :=
    twoMeetingLines_secondNormal_readings_ne_zero design hpattern normalSecond hunitSecond
      horthSecond
  obtain ⟨hcompFirst, hcompSecond, hcompOpen⟩ := twoMeetingLines_weightComplements_pos design
  -- the two selected readings are nonzero, and the two selected labels are legal
  have hsecondNe : design.atom secondLabel ⬝ᵥ normalFirst ≠ 0 := by
    rcases hsecondMem with rfl | rfl
    · exact hthreeNe
    · exact hfourNe
  have hfirstNe : design.atom firstLabel ⬝ᵥ normalSecond ≠ 0 := by
    rcases hfirstMem with rfl | rfl
    · exact honeNe
    · exact htwoNe
  have hfirstOrth : design.atom firstLabel ⬝ᵥ normalFirst = 0 := by
    rcases hfirstMem with rfl | rfl
    · exact horthFirst 1 (by decide)
    · exact horthFirst 2 (by decide)
  have hsecondOrth : design.atom secondLabel ⬝ᵥ normalSecond = 0 := by
    rcases hsecondMem with rfl | rfl
    · exact horthSecond 3 (by decide)
    · exact horthSecond 4 (by decide)
  have hfirstSecond : firstLabel ≠ secondLabel := by
    rcases hfirstMem with rfl | rfl <;> rcases hsecondMem with rfl | rfl <;> decide
  have hfirstOpen : firstLabel ≠ 5 := by rcases hfirstMem with rfl | rfl <;> decide
  have hsecondOpen : secondLabel ≠ 5 := by rcases hsecondMem with rfl | rfl <;> decide
  -- the four squared readings are strictly positive
  have hsqA : 0 < (design.atom secondLabel ⬝ᵥ normalFirst) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hsecondNe))
  have hsqB : 0 < (design.atom firstLabel ⬝ᵥ normalSecond) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hfirstNe))
  have hsqOpenA : 0 < (design.atom 5 ⬝ᵥ normalFirst) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hopenFirstNe))
  have hsqOpenB : 0 < (design.atom 5 ⬝ᵥ normalSecond) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hopenSecondNe))
  -- the two diagonal lower bounds, and their strict positivity
  have hlowFirst := twoMeetingLines_firstDefect_pos design normalFirst hunitFirst horthFirst
    secondLabel hthreeMax hfourMax hsecondNe
  have hlowSecond := twoMeetingLines_secondDefect_pos design normalSecond hunitSecond
    horthSecond firstLabel honeMax htwoMax hfirstNe
  have hboundFirstPos : 0 < (1 - design.weight 3 - design.weight 4)
        * (design.atom secondLabel ⬝ᵥ normalFirst) ^ 2
      + (1 - design.weight 5) * (design.atom 5 ⬝ᵥ normalFirst) ^ 2 :=
    add_pos (mul_pos hcompFirst hsqA) (mul_pos hcompOpen hsqOpenA)
  have hboundSecondPos : 0 < (1 - design.weight 1 - design.weight 2)
        * (design.atom firstLabel ⬝ᵥ normalSecond) ^ 2
      + (1 - design.weight 5) * (design.atom 5 ⬝ᵥ normalSecond) ^ 2 :=
    add_pos (mul_pos hcompSecond hsqB) (mul_pos hcompOpen hsqOpenB)
  have hdiagFirstPos : 0 < (design.atom secondLabel ⬝ᵥ normalFirst) ^ 2
      + (design.atom 5 ⬝ᵥ normalFirst) ^ 2 - 1 := lt_of_lt_of_le hboundFirstPos hlowFirst
  -- the meeting identity turns the off-diagonal entry into a pure reading product
  have hmeet := twoMeetingLines_meeting_identity design normalFirst normalSecond
    horthFirst horthSecond
  have hoff : (design.atom 5 ⬝ᵥ normalFirst) * (design.atom 5 ⬝ᵥ normalSecond)
        - normalFirst ⬝ᵥ normalSecond
      = (1 - design.weight 5)
        * ((design.atom 5 ⬝ᵥ normalFirst) * (design.atom 5 ⬝ᵥ normalSecond)) := by
    rw [← hmeet]; ring
  -- the discriminant, with its three surviving reading products
  have hdisc : ((design.atom 5 ⬝ᵥ normalFirst) * (design.atom 5 ⬝ᵥ normalSecond)
        - normalFirst ⬝ᵥ normalSecond) ^ 2
      < ((design.atom secondLabel ⬝ᵥ normalFirst) ^ 2
          + (design.atom 5 ⬝ᵥ normalFirst) ^ 2 - 1)
        * ((design.atom firstLabel ⬝ᵥ normalSecond) ^ 2
          + (design.atom 5 ⬝ᵥ normalSecond) ^ 2 - 1) := by
    rw [hoff]
    have hprod := mul_le_mul hlowFirst hlowSecond hboundSecondPos.le hdiagFirstPos.le
    nlinarith [hprod, hcompFirst, hcompSecond, hcompOpen, hsqA, hsqB, hsqOpenA, hsqOpenB,
      mul_pos (mul_pos hcompFirst hcompSecond) (mul_pos hsqA hsqB),
      mul_pos (mul_pos hcompFirst hcompOpen) (mul_pos hsqA hsqOpenB),
      mul_pos (mul_pos hcompOpen hcompSecond) (mul_pos hsqOpenA hsqB)]
  rw [twoMeetingLines_transversal_planeForm design normalFirst normalSecond hunitFirst
    hunitSecond firstLabel secondLabel hfirstSecond hfirstOpen hsecondOpen hfirstOrth
    hsecondOrth coeffFirst coeffSecond]
  exact quadratic_form_pos_of_disc hdiagFirstPos hdisc hnonzero

/-- **THE MAXIMAL TRANSVERSAL EXISTS.**  Choosing each label by its maximal
reading at the opposite normal gives one of the four transversals of the class,
and its gap is positive definite on the plane of the two normals. -/
theorem exists_twoMeetingLines_transversal_pos_on_normalPlane (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (normalFirst normalSecond : Fin 3 → ℝ)
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (horthFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (horthSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0) :
    ∃ firstLabel secondLabel : Fin 6,
      (firstLabel = 1 ∨ firstLabel = 2) ∧ (secondLabel = 3 ∨ secondLabel = 4) ∧
      ∀ coeffFirst coeffSecond : ℝ, coeffFirst ≠ 0 ∨ coeffSecond ≠ 0 →
        0 < (coeffFirst • normalFirst + coeffSecond • normalSecond)
          ⬝ᵥ ((subsetSum design ({firstLabel, secondLabel, 5} : Finset (Fin 6)) - 1)
            *ᵥ (coeffFirst • normalFirst + coeffSecond • normalSecond)) := by
  rcases le_total ((design.atom 1 ⬝ᵥ normalSecond) ^ 2)
      ((design.atom 2 ⬝ᵥ normalSecond) ^ 2) with hfirstPick | hfirstPick <;>
    rcases le_total ((design.atom 3 ⬝ᵥ normalFirst) ^ 2)
      ((design.atom 4 ⬝ᵥ normalFirst) ^ 2) with hsecondPick | hsecondPick
  · exact ⟨2, 4, Or.inr rfl, Or.inr rfl, fun cf cs hne =>
      twoMeetingLines_transversalGap_pos_on_normalPlane design hpattern normalFirst normalSecond
        hunitFirst hunitSecond horthFirst horthSecond 2 4 (Or.inr rfl) (Or.inr rfl)
        hfirstPick le_rfl hsecondPick le_rfl cf cs hne⟩
  · exact ⟨2, 3, Or.inr rfl, Or.inl rfl, fun cf cs hne =>
      twoMeetingLines_transversalGap_pos_on_normalPlane design hpattern normalFirst normalSecond
        hunitFirst hunitSecond horthFirst horthSecond 2 3 (Or.inr rfl) (Or.inl rfl)
        hfirstPick le_rfl le_rfl hsecondPick cf cs hne⟩
  · exact ⟨1, 4, Or.inl rfl, Or.inr rfl, fun cf cs hne =>
      twoMeetingLines_transversalGap_pos_on_normalPlane design hpattern normalFirst normalSecond
        hunitFirst hunitSecond horthFirst horthSecond 1 4 (Or.inl rfl) (Or.inr rfl)
        le_rfl hfirstPick hsecondPick le_rfl cf cs hne⟩
  · exact ⟨1, 3, Or.inl rfl, Or.inl rfl, fun cf cs hne =>
      twoMeetingLines_transversalGap_pos_on_normalPlane design hpattern normalFirst normalSecond
        hunitFirst hunitSecond horthFirst horthSecond 1 3 (Or.inl rfl) (Or.inl rfl)
        le_rfl hfirstPick le_rfl hsecondPick cf cs hne⟩

end Gtz


