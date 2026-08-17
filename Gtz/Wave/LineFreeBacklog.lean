/-
# The line-free backlog, wired

`Gtz/Wave/AllHeavyWedgeCollapse.lean` and `Gtz/Wave/A1NeedleCramerFloor.lean`
each carry a DIRECT PRODUCER of the registry axiom
`Skeleton.obligationBaseTripleTightUThreeSix`, and neither module has an outward
consumer.  Four more landed laws sit one step away from an instance that nobody
took.  This file consumes all six.

## What each section does

**1.  The two direct producers, named and composed.**  Each of the two closes
`Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual`.  Section 1 names the
two cells, carries each to the class statement
`Gtz.StressFreeStratumIsTieFree (lineFamilyPattern [])`, and carries each to
`Gtz.GtzWeightedAll 3` against the other four on-path Props.

**2.  The cost of the wedge cell, measured.**  The engine
`Gtz.posDef_iff_wedgeBalance_of_dominates` is an EQUIVALENCE at every weak
dominator.  The balance is a FAITHFUL test, so an attack on it loses nothing.
It is a REFORMULATION with fewer hypotheses, and NOT a reduction in strength.
Section 2 makes the price explicit: `Gtz.BaseTripleWedgeBalanceCell` carries no
line pattern and no conic hypothesis, so it already hands back a strict triple
at EVERY design that weakly dominates at the base triple.  That is a LEVEL-ONE
Prop.  The bracket cell of section 1 does not share the defect, because its
hypothesis names the line-free off-conic stratum.

**3.  `hspan` is free at entry `#1`.**  `Gtz.lineFreeDirection_span` proves the
spanning hypothesis of `Gtz.posDef_directionChartGap_lineFree_of_coverCell` with
no hypothesis at all.  It lives DOWNSTREAM of its consumer, so the two never met.

**4.  The base residual at all twenty triples.**  The landed reading is pinned at
`{0,1,2}`.  Line-freeness is bracket nonvanishing at EVERY distinct triple, so
the residual is positive definite at every card-three base set.

**5.  The chart leverage laws at the line-free chart.**  The counting law and the
leverage veto quantify over an arbitrary direction family.  The three-lines
instances are landed and the line-free instances were not.  Each costs one moment
step.

**6.  The `|H| = 3` branch, joined to the axiom.**  A `(6,3)` design carries at
least three strictly heavy atoms with no hypothesis.  At exactly three the
selection disappears, and the axiom splits by the heavy count into a balance cell
and a wide cell.

**7.  A duplication repaired.**  `Gtz.three_le_card_strictlyHeavy_of_isTie_sixThree`
spends `Gtz.IsTie` and forty-nine lines for a count that
`Gtz.rank_le_card_strictlyHeavySet` gives at every rank and size with no
hypothesis.  Section 7 proves the strong law implies the weak one.  The weak one
stays, because other proofs consume it.

**8.  The ten nontrivial brackets of the line-free chart.**  The three-lines chart
landed all twenty brackets as named theorems.  The line-free chart landed only the
ten trivial ones.  Section 8 lands the ten that carry the walls.

## Inhabitation

`Gtz.uniformWitnessDesign` is line-free and off-conic, so every hypothesis of the
form "line-free and off-conic" in this file is satisfiable.
`Gtz.isAdmissibleLineFreeParameter_two_three_five_seven` inhabits the chart
region, and `Gtz.icosaApproximantChartPoint` inhabits `Gtz.DirectionChartPoint 6`.
-/
import Gtz.Wave.AllHeavyWedgeCollapse
import Gtz.Wave.A1NeedleCramerFloor
import Gtz.Wave.WiringAllFiveOnPath
import Gtz.Wave.TieStratumClassification
import Gtz.Wave.ThreeLinesSlideElimination
import Gtz.Design.LineFreeModuli
import Gtz.Design.UThreeSixDisjunction
import Gtz.Design.UniformWitnessRefutation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Finset Matrix

/-! ## 1.  The two direct producers of the registry axiom

Both cells below close `Gtz.BaseTripleTightLineFreeOffConicHeavyNeedleResidual`,
which is the Prop that `Skeleton.obligationBaseTripleTightUThreeSix` asserts.
The producers are landed.  What was missing is a name for each hypothesis and a
route onward. -/

/-- **THE WEDGE CELL.**  One wedge balance at the base triple, against the first
coordinate axis, at every design that weakly dominates there and carries no
strict card-three witness.  This is the hypothesis of
`Gtz.baseTripleTightLineFreeOffConicHeavyNeedleResidual_of_baseTripleWedgeBalance`.
Read section 2 before you spend a fork on it. -/
def BaseTripleWedgeBalanceCell : Prop :=
  ∀ design : WeightedDesign 6 3,
    Dominates design ({0, 1, 2} : Finset (Fin 6)) →
    (∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef) →
    ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ ![1, 0, 0] = 0 → probeVec ≠ 0 →
      WedgeBalanceAt design ({0, 1, 2} : Finset (Fin 6)) ![1, 0, 0] probeVec

/-- **THE BRACKET CELL.**  Every line-free off-conic `(6,3)` design carries one
triple whose squared bracket beats its pair-area sum.  This is the hypothesis of
`Gtz.heavyNeedleResidual_of_bracketDominantCell`.  Unlike the wedge cell it names
the stratum, so it constrains the line-free class alone. -/
def BracketDominantLineFreeCell : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    ∃ firstLabel secondLabel thirdLabel : Fin 6,
      firstLabel ≠ secondLabel ∧ firstLabel ≠ thirdLabel ∧ secondLabel ≠ thirdLabel ∧
      triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
          (design.atom thirdLabel)
        < atomBracket design firstLabel secondLabel thirdLabel ^ 2

/-- **THE WEDGE CELL CLOSES THE REGISTRY AXIOM.**  A wiring composition over the
landed producer. -/
theorem heavyNeedleResidual_of_baseTripleWedgeBalanceCell
    (hcell : BaseTripleWedgeBalanceCell) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual :=
  baseTripleTightLineFreeOffConicHeavyNeedleResidual_of_baseTripleWedgeBalance hcell

/-- **THE BRACKET CELL CLOSES THE REGISTRY AXIOM.**  A wiring composition over the
landed producer. -/
theorem heavyNeedleResidual_of_bracketDominantLineFreeCell
    (hcell : BracketDominantLineFreeCell) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual :=
  heavyNeedleResidual_of_bracketDominantCell hcell

/-- **THE WEDGE CELL GIVES THE CLASS STATEMENT.**  Entry `#1` of
`Gtz.stressFreeResidualFamiliesSix` is tie-free.  The step from the axiom to the
class statement is the landed equivalence
`Gtz.heavyNeedleResidual_iff_stressFreeStratumIsTieFree`. -/
theorem stressFreeStratumIsTieFree_lineFree_of_baseTripleWedgeBalanceCell
    (hcell : BaseTripleWedgeBalanceCell) :
    StressFreeStratumIsTieFree (lineFamilyPattern ([] : List (List (Fin 6)))) :=
  heavyNeedleResidual_iff_stressFreeStratumIsTieFree.mp
    (heavyNeedleResidual_of_baseTripleWedgeBalanceCell hcell)

/-- **THE BRACKET CELL GIVES THE CLASS STATEMENT.** -/
theorem stressFreeStratumIsTieFree_lineFree_of_bracketDominantCell
    (hcell : BracketDominantLineFreeCell) :
    StressFreeStratumIsTieFree (lineFamilyPattern ([] : List (List (Fin 6)))) :=
  heavyNeedleResidual_iff_stressFreeStratumIsTieFree.mp
    (heavyNeedleResidual_of_bracketDominantLineFreeCell hcell)

/-- **THE WEDGE CELL REACHES RANK THREE, AGAINST THE OTHER FOUR CLASSES.**
`Gtz.gtzWeightedAll_three_of_allFiveOnPath` needs all five on-path Props.  This
file supplies entry `#1` and takes the other four as hypotheses, because no
producer of them exists here. -/
theorem gtzWeightedAll_three_of_baseTripleWedgeBalanceCell
    (hcell : BaseTripleWedgeBalanceCell)
    (hOneLine : OneLineTenthHeavyJointBlindLineSparse)
    (hTwoMeeting : TwoMeetingLinesTenthHeavyJointBlindTransversal)
    (hThreeLines :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines)
    (hKFour : KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_allFiveOnPath
    ⟨heavyNeedleResidual_of_baseTripleWedgeBalanceCell hcell, hOneLine, hTwoMeeting,
      hThreeLines, hKFour⟩

/-- **THE BRACKET CELL REACHES RANK THREE, AGAINST THE OTHER FOUR CLASSES.** -/
theorem gtzWeightedAll_three_of_bracketDominantCell
    (hcell : BracketDominantLineFreeCell)
    (hOneLine : OneLineTenthHeavyJointBlindLineSparse)
    (hTwoMeeting : TwoMeetingLinesTenthHeavyJointBlindTransversal)
    (hThreeLines :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines)
    (hKFour : KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_allFiveOnPath
    ⟨heavyNeedleResidual_of_bracketDominantLineFreeCell hcell, hOneLine, hTwoMeeting,
      hThreeLines, hKFour⟩

/-! ## 2.  What the wedge cell really costs

`Gtz.posDef_iff_wedgeBalance_of_dominates` is an EQUIVALENCE at every weak
dominator, so the balance is a faithful test of strict domination.  Nothing is
lost by an attack on the balance, and nothing is gained either: the two Props are
interderivable at a weak dominator.

The price is elsewhere, and it is large.  `Gtz.BaseTripleWedgeBalanceCell`
carries NO line pattern and NO conic hypothesis, so its conclusion applies at
every `(6,3)` design that weakly dominates at the base triple.  The theorem below
reads that price off: the cell hands back a STRICT card-three witness at every
such design.  That is the whole `(6,3)` question at the base-pinned locus, and it
is strictly more than the line-free class asks for.

The bracket cell of section 1 does NOT share the defect.  Its hypothesis quantifies
over line-free off-conic designs only. -/

/-- **THE WEDGE CELL IS A LEVEL-ONE PROP.**  It gives a strict card-three witness
at EVERY design that weakly dominates at the base triple, line-free or not.  Any
brief that presents it as a line-free residual is wrong. -/
theorem exists_posDef_cardThree_of_baseTripleWedgeBalanceCell
    (hcell : BaseTripleWedgeBalanceCell) (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6))) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  by_contra hnone
  have hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
      ¬ (subsetSum design selected - 1).PosDef := by
    intro selected hcard hposDef
    exact hnone ⟨selected, hcard, hposDef⟩
  exact hnoStrict ({0, 1, 2} : Finset (Fin 6)) (by decide)
    (posDef_of_dominates_of_wedgeBalance design ({0, 1, 2} : Finset (Fin 6)) hdominates
      ![1, 0, 0] dotProduct_firstAxis (hcell design hdominates hnoStrict))

/-- **NO TIE WEAKLY DOMINATES AT THE BASE TRIPLE, UNDER THE WEDGE CELL.**  The same
price, read on the tie locus. -/
theorem not_isTie_of_baseTripleWedgeBalanceCell (hcell : BaseTripleWedgeBalanceCell)
    (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6))) :
    ¬ IsTie design := by
  intro htie
  obtain ⟨selected, hcard, hposDef⟩ :=
    exists_posDef_cardThree_of_baseTripleWedgeBalanceCell hcell design hdominates
  exact htie.2 selected hcard hposDef

/-- **THE BALANCE IS A FAITHFUL TEST AT THE BASE TRIPLE.**  Recorded here so that
no consumer mistakes the reformulation for a reduction.  At a weak dominator the
wedge balance and strict domination are the SAME statement. -/
theorem posDef_baseTriple_iff_wedgeBalance_of_dominates (design : WeightedDesign 6 3)
    (hdominates : Dominates design ({0, 1, 2} : Finset (Fin 6))) :
    (subsetSum design ({0, 1, 2} : Finset (Fin 6)) - 1).PosDef
      ↔ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ ![1, 0, 0] = 0 → probeVec ≠ 0 →
          WedgeBalanceAt design ({0, 1, 2} : Finset (Fin 6)) ![1, 0, 0] probeVec :=
  posDef_iff_wedgeBalance_of_dominates design ({0, 1, 2} : Finset (Fin 6)) hdominates
    ![1, 0, 0] dotProduct_firstAxis

/-! ## 3.  The spanning hypothesis at entry `#1`, discharged

`Gtz.posDef_directionChartGap_lineFree_of_coverCell` asks for a probe that no
chart direction annihilates.  `Gtz.lineFreeDirection_span` proves exactly that,
with no hypothesis, because labels zero, one and two ARE the coordinate axes.
The producer sits in `Gtz/Design/LineFreeModuli.lean`, which imports its own
consumer, so the two could not meet before this file. -/

/-- **THE COVER CELL AT ENTRY `#1`, WITH NO SPANNING HYPOTHESIS.**  Every label
of the chart whose cover cost against the basis triple is at most one makes the
basis triple strictly dominating. -/
theorem posDef_directionChartGap_lineFree_of_coverCell_spanFree
    (param : ℝ × ℝ × ℝ × ℝ) (mass weight : Fin 6 → ℝ) (hmass : ∀ label, 0 < mass label)
    (hweight : ∀ label, 0 < weight label) (hsum : ∑ label, weight label = 1)
    (hcell : GeneralCoverCellFires (fun label => mass label / weight label)
      lineFreeSelected (lineFreeCoeff param)) :
    (directionChartGap (lineFreeDirection param) mass weight lineFreeSelected).PosDef :=
  posDef_directionChartGap_lineFree_of_coverCell param mass weight hmass hweight hsum
    (lineFreeDirection_span param) hcell

/-! ## 4.  The base residual at all twenty triples

`Gtz.posDef_baseResidual_baseTriple_of_lineFree` is pinned at `{0,1,2}`.  Line
freeness is bracket nonvanishing at EVERY distinct triple, and
`Gtz.posDef_baseResidual_iff_tripleBracket_ne_zero_of_disjointPick` reads the
residual at any base set through any disjoint pick.  So the pin is removable. -/

/-- **THE RESIDUAL AT ANY BASE SET, THROUGH ANY DISJOINT PICK.**  Line-freeness
alone gives the positive definite residual. -/
theorem posDef_baseResidual_of_lineFree_of_disjointPick (design : WeightedDesign 6 3)
    (hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (baseSet : Finset (Fin 6)) (hcard : baseSet.card = 3)
    (pick : Fin 3 → Fin 6) (hinjective : Function.Injective pick)
    (houtside : ∀ slotIndex, pick slotIndex ∉ baseSet) :
    (baseResidual design baseSet).PosDef := by
  refine (posDef_baseResidual_iff_tripleBracket_ne_zero_of_disjointPick design baseSet pick
    hinjective houtside (by omega)).mpr ?_
  exact atomBracket_ne_zero_of_lineFree design hlineFree
    (fun hsame => (by decide : (0 : Fin 3) ≠ 1) (hinjective hsame))
    (fun hsame => (by decide : (0 : Fin 3) ≠ 2) (hinjective hsame))
    (fun hsame => (by decide : (1 : Fin 3) ≠ 2) (hinjective hsame))

/-- **THE BASE RESIDUAL AT ALL TWENTY TRIPLES.**  On the line-free stratum every
card-three base set leaves a positive definite residual, because its complement is
a basis.  The landed reading was pinned at `{0,1,2}` alone. -/
theorem posDef_baseResidual_cardThree_of_lineFree (design : WeightedDesign 6 3)
    (hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (baseSet : Finset (Fin 6)) (hcard : baseSet.card = 3) :
    (baseResidual design baseSet).PosDef := by
  classical
  have hcompl : baseSetᶜ.card = 3 := by
    have hcardCompl := Finset.card_compl baseSet
    rw [hcard, Fintype.card_fin] at hcardCompl
    omega
  set pick : Fin 3 → Fin 6 := fun slot => ((baseSetᶜ.orderIsoOfFin hcompl) slot : Fin 6)
    with hpick
  have hinjective : Function.Injective pick := fun leftSlot rightSlot hvalue =>
    (baseSetᶜ.orderIsoOfFin hcompl).injective (Subtype.ext hvalue)
  have houtside : ∀ slotIndex : Fin 3, pick slotIndex ∉ baseSet := fun slotIndex =>
    Finset.mem_compl.mp ((baseSetᶜ.orderIsoOfFin hcompl) slotIndex).2
  exact posDef_baseResidual_of_lineFree_of_disjointPick design hlineFree baseSet hcard pick
    hinjective houtside

/-- **THE COMPLEMENT FRAME AT ALL TWENTY TRIPLES.**  The three complement atoms of
any card-three base set are orthonormal for the residual-inverse metric. -/
theorem complementFrame_cardThree_of_lineFree (design : WeightedDesign 6 3)
    (hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    (baseSet : Finset (Fin 6)) (hcard : baseSet.card = 3) :
    IsInverseMetricOrthonormalOn design baseSetᶜ (baseResidual design baseSet) :=
  complementFrame_sixThree design baseSet hcard
    (posDef_baseResidual_cardThree_of_lineFree design hlineFree baseSet hcard)

/-! ## 5.  The chart leverage laws at the line-free chart

`Gtz.three_le_card_overLevered` and `Gtz.weight_lt_chartMassLeverage_of_posDef_gap`
quantify over an arbitrary direction family and ask for one thing: a positive
definite mass moment.  The three-lines instances are landed.  Labels zero, one and
two of the line-free chart are the coordinate axes, so the moment step is one
term. -/

/-- **THE MASS MOMENT OF THE LINE-FREE CHART IS POSITIVE DEFINITE.**  At every
chart point and every parameter, admissible or not.  Labels zero, one and two are
the coordinate axes. -/
theorem posDef_chartMassMoment_lineFree (param : ℝ × ℝ × ℝ × ℝ)
    (point : DirectionChartPoint 6) :
    (chartMassMoment (lineFreeDirection param) point.mass).PosDef := by
  refine posDef_massMoment_of_spanningTriple (lineFreeDirection param) point.mass
    point.mass_pos 0 1 2 fun probeVec hfirst hsecond hthird => ?_
  simp only [lineFreeDirection, dotProduct, Fin.sum_univ_three, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons] at hfirst hsecond hthird
  exact eq_zero_of_coordinates_eq_zero (by linarith) (by linarith) (by linarith)

/-- **THE COUNTING LAW AT THE LINE-FREE CHART.**  At every chart point at least
three labels carry mass leverage above their own weight. -/
theorem three_le_card_overLevered_lineFree (param : ℝ × ℝ × ℝ × ℝ)
    (point : DirectionChartPoint 6) :
    3 ≤ (Finset.univ.filter
      (fun label => point.weight label
        < chartMassLeverage (lineFreeDirection param) point.mass label)).card :=
  three_le_card_overLevered (lineFreeDirection param) point
    (posDef_chartMassMoment_lineFree param point)

/-- **THE LEVERAGE VETO AT THE LINE-FREE CHART.**  A label of a strictly dominating
triple carries mass leverage above its own weight. -/
theorem weight_lt_chartMassLeverage_lineFree (param : ℝ × ℝ × ℝ × ℝ)
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6)) (pivotLabel : Fin 6)
    (hmem : pivotLabel ∈ selected) (probe : Fin 3 → ℝ)
    (hblind : ∀ other ∈ selected, other ≠ pivotLabel →
      lineFreeDirection param other ⬝ᵥ probe = 0)
    (hlive : lineFreeDirection param pivotLabel ⬝ᵥ probe ≠ 0)
    (hgap : (directionChartGap (lineFreeDirection param) point.mass point.weight
      selected).PosDef) :
    point.weight pivotLabel
      < chartMassLeverage (lineFreeDirection param) point.mass pivotLabel :=
  weight_lt_chartMassLeverage_of_posDef_gap (lineFreeDirection param) point.mass point.weight
    point.mass_pos point.weight_pos (posDef_chartMassMoment_lineFree param point) selected
    pivotLabel hmem probe hblind hlive hgap

/-! ## 6.  The `|H| = 3` branch, joined to the registry axiom

`Gtz.three_le_card_strictlyHeavySet_sixThree` counts at least three strictly heavy
atoms with no hypothesis.  At exactly three,
`Gtz.exists_posDef_cardThree_iff_wedgeBalance_strictlyHeavySet` removes the
selection entirely.  The axiom splits by the heavy count.  Nothing in the tree
joined the two sides. -/

/-- **THE NARROW BRANCH.**  Every line-free off-conic design with exactly three
strictly heavy atoms balances at that one triple. -/
def LineFreeHeavyTripleBalanceCell : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    (strictlyHeavySet design).card = 3 →
    ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ ![1, 0, 0] = 0 → probeVec ≠ 0 →
      WedgeBalanceAt design (strictlyHeavySet design) ![1, 0, 0] probeVec

/-- **THE WIDE BRANCH.**  No line-free off-conic design with four or more strictly
heavy atoms is a tie. -/
def LineFreeWideHeavySetCell : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))) →
    HasNoCommonQuadric design.atom →
    4 ≤ (strictlyHeavySet design).card → ¬ IsTie design

/-- **THE SPLIT BY THE HEAVY COUNT CLOSES THE REGISTRY AXIOM.**  The count is at
least three with no hypothesis, so the two branches are exhaustive.  On the narrow
branch the strictly heavy set IS the only candidate triple, and the balance decides
it. -/
theorem heavyNeedleResidual_of_heavyCountSplit
    (hnarrow : LineFreeHeavyTripleBalanceCell) (hwide : LineFreeWideHeavySetCell) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual := by
  refine heavyNeedleResidual_of_pinnedStratumTieFree ?_
  intro design hlineFree hoffConic htie
  by_cases hcard : (strictlyHeavySet design).card = 3
  · obtain ⟨selected, hselCard, hposDef⟩ :=
      (exists_posDef_cardThree_iff_wedgeBalance_strictlyHeavySet design hcard
        ![1, 0, 0] dotProduct_firstAxis).mpr (hnarrow design hlineFree hoffConic hcard)
    exact htie.2 selected hselCard hposDef
  · have hfour : 4 ≤ (strictlyHeavySet design).card := by
      have hthree := three_le_card_strictlyHeavySet_sixThree design
      omega
    exact hwide design hlineFree hoffConic hfour htie

/-- **THE NARROW BRANCH IS AN EQUIVALENCE.**  At exactly three strictly heavy
atoms, a line-free off-conic design fails to be a tie exactly when its heavy
triple balances.  Neither direction loses information. -/
theorem not_isTie_iff_wedgeBalance_strictlyHeavySet_of_cardThree
    (design : WeightedDesign 6 3) (hcard : (strictlyHeavySet design).card = 3)
    (hweak : ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) :
    ¬ IsTie design
      ↔ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ ![1, 0, 0] = 0 → probeVec ≠ 0 →
          WedgeBalanceAt design (strictlyHeavySet design) ![1, 0, 0] probeVec := by
  rw [← exists_posDef_cardThree_iff_wedgeBalance_strictlyHeavySet design hcard
    ![1, 0, 0] dotProduct_firstAxis]
  constructor
  · intro hnotTie
    by_contra hnone
    refine hnotTie ⟨hweak, fun selected hselCard hposDef => hnone ⟨selected, hselCard, hposDef⟩⟩
  · rintro ⟨selected, hselCard, hposDef⟩ htie
    exact htie.2 selected hselCard hposDef

/-! ## 7.  A duplication repaired

`Gtz.three_le_card_strictlyHeavy_of_isTie_sixThree`
(Gtz/Wave/TieStratumClassification.lean) spends `Gtz.IsTie` and forty-nine lines
of harmonic bookkeeping.  `Gtz.rank_le_card_strictlyHeavySet`
(Gtz/Wave/AllHeavyWedgeCollapse.lean) gives the same count at every rank and every
size with NO hypothesis at all, in fourteen lines of Parseval bookkeeping.

The weak copy is on the consumed path.  The strong one had no consumer.  The two
theorems below show the strong law covers the weak one exactly.  The weak copy
stays where it is, because other proofs cite it. -/

/-- **THE COUNT WITH NO HYPOTHESIS.**  The heavy set of
`Gtz.three_le_card_strictlyHeavy_of_isTie_sixThree` is `Gtz.strictlyHeavySet` by
definition, and the rank law counts it at every design. -/
theorem three_le_card_strictlyHeavy_sixThree_unconditional (design : WeightedDesign 6 3) :
    3 ≤ (Finset.univ.filter fun label => 1 < leverageOf (design.atom label)).card :=
  rank_le_card_strictlyHeavySet design (by norm_num)

/-- **THE STRONG LAW COVERS THE WEAK COPY.**  The `Gtz.IsTie` hypothesis of the
consumed copy is inert: the same count holds at every `(6,3)` design. -/
theorem three_le_card_strictlyHeavy_of_isTie_sixThree_of_rankLaw
    (design : WeightedDesign 6 3) (_htie : IsTie design) :
    3 ≤ (Finset.univ.filter fun label => 1 < leverageOf (design.atom label)).card :=
  three_le_card_strictlyHeavy_sixThree_unconditional design

/-- The two spellings of the heavy set agree. -/
theorem strictlyHeavySet_eq_filter {m k : ℕ} (design : WeightedDesign m k) :
    strictlyHeavySet design
      = Finset.univ.filter fun label => 1 < leverageOf (design.atom label) := rfl

/-! ## 8.  The ten nontrivial brackets of the line-free chart

`Gtz.lineFreeChartCoefficients` lands ten bracket values, and every one of them is
`1` or a bare parameter.  The other ten carry the fourteen walls, and they appear
only inside the proof of `Gtz.isAdmissibleLineFreeParameter_of_brackets`, each one
discharged by a `simp only` and a `linarith`.  The three-lines chart landed all
twenty of its brackets as named theorems.  These ten are the same brick.

Each value below is the wall named in the header of
`Gtz/Design/LineFreeModuli.lean`, in the sign that the chart produces. -/

section BracketTable

variable (param : ℝ × ℝ × ℝ × ℝ)

/-- `[034] = b - a`.  The wall `b = a` kills this triple. -/
theorem lineFreeBracket_zeroThreeFour :
    tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 3)
      (lineFreeDirection param 4) = param.2.1 - param.1 := by
  simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-- `[035] = d - c`.  The wall `d = c` kills this triple. -/
theorem lineFreeBracket_zeroThreeFive :
    tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 3)
      (lineFreeDirection param 5) = param.2.2.2 - param.2.2.1 := by
  simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-- `[045] = ad - bc`.  The minor wall kills this triple. -/
theorem lineFreeBracket_zeroFourFive :
    tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 4)
      (lineFreeDirection param 5)
      = param.1 * param.2.2.2 - param.2.1 * param.2.2.1 := by
  simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-- `[134] = 1 - b`.  The wall `b = 1` kills this triple. -/
theorem lineFreeBracket_oneThreeFour :
    tripleBracket (lineFreeDirection param 1) (lineFreeDirection param 3)
      (lineFreeDirection param 4) = 1 - param.2.1 := by
  simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-- `[135] = 1 - d`.  The wall `d = 1` kills this triple. -/
theorem lineFreeBracket_oneThreeFive :
    tripleBracket (lineFreeDirection param 1) (lineFreeDirection param 3)
      (lineFreeDirection param 5) = 1 - param.2.2.2 := by
  simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-- `[145] = b - d`.  The wall `b = d` kills this triple. -/
theorem lineFreeBracket_oneFourFive :
    tripleBracket (lineFreeDirection param 1) (lineFreeDirection param 4)
      (lineFreeDirection param 5) = param.2.1 - param.2.2.2 := by
  simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-- `[234] = a - 1`.  The wall `a = 1` kills this triple. -/
theorem lineFreeBracket_twoThreeFour :
    tripleBracket (lineFreeDirection param 2) (lineFreeDirection param 3)
      (lineFreeDirection param 4) = param.1 - 1 := by
  simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-- `[235] = c - 1`.  The wall `c = 1` kills this triple. -/
theorem lineFreeBracket_twoThreeFive :
    tripleBracket (lineFreeDirection param 2) (lineFreeDirection param 3)
      (lineFreeDirection param 5) = param.2.2.1 - 1 := by
  simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-- `[245] = c - a`.  The wall `c = a` kills this triple. -/
theorem lineFreeBracket_twoFourFive :
    tripleBracket (lineFreeDirection param 2) (lineFreeDirection param 4)
      (lineFreeDirection param 5) = param.2.2.1 - param.1 := by
  simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

/-- `[345] = (ad - bc) - (d - b) + (c - a)`.  The cubic wall kills this triple. -/
theorem lineFreeBracket_threeFourFive :
    tripleBracket (lineFreeDirection param 3) (lineFreeDirection param 4)
      (lineFreeDirection param 5)
      = param.1 * param.2.2.2 - param.2.1 * param.2.2.1
        - param.2.2.2 + param.2.1 + param.2.2.1 - param.1 := by
  simp only [lineFreeDirection, tripleBracket_eq, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons] <;> ring

end BracketTable

/-- **THE TEN WALLS ARE THE TEN BRACKETS.**  At an admissible parameter each of the
ten nontrivial brackets is nonzero, one wall for each triple.  With
`Gtz.lineFreeChartCoefficients` beside it, all twenty brackets of the chart carry
a named value. -/
theorem lineFreeChartNontrivialCoefficients_ne_zero (param : ℝ × ℝ × ℝ × ℝ)
    (hadmissible : IsAdmissibleLineFreeParameter param) :
    tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 3)
        (lineFreeDirection param 4) ≠ 0
      ∧ tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 3)
        (lineFreeDirection param 5) ≠ 0
      ∧ tripleBracket (lineFreeDirection param 0) (lineFreeDirection param 4)
        (lineFreeDirection param 5) ≠ 0
      ∧ tripleBracket (lineFreeDirection param 1) (lineFreeDirection param 3)
        (lineFreeDirection param 4) ≠ 0
      ∧ tripleBracket (lineFreeDirection param 1) (lineFreeDirection param 3)
        (lineFreeDirection param 5) ≠ 0
      ∧ tripleBracket (lineFreeDirection param 1) (lineFreeDirection param 4)
        (lineFreeDirection param 5) ≠ 0
      ∧ tripleBracket (lineFreeDirection param 2) (lineFreeDirection param 3)
        (lineFreeDirection param 4) ≠ 0
      ∧ tripleBracket (lineFreeDirection param 2) (lineFreeDirection param 3)
        (lineFreeDirection param 5) ≠ 0
      ∧ tripleBracket (lineFreeDirection param 2) (lineFreeDirection param 4)
        (lineFreeDirection param 5) ≠ 0
      ∧ tripleBracket (lineFreeDirection param 3) (lineFreeDirection param 4)
        (lineFreeDirection param 5) ≠ 0 := by
  obtain ⟨_hfourMidNe, hfourMidNeOne, _hfourLastNe, hfourLastNeOne,
    _hfiveMidNe, hfiveMidNeOne, _hfiveLastNe, hfiveLastNeOne,
    hfourDiffNe, hfiveDiffNe, hlastDiffNe, hmidDiffNe,
    hminorNe, hcubicNe⟩ := hadmissible
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [lineFreeBracket_zeroThreeFour]; exact hfourDiffNe
  · rw [lineFreeBracket_zeroThreeFive]; exact hfiveDiffNe
  · rw [lineFreeBracket_zeroFourFive]; exact hminorNe
  · rw [lineFreeBracket_oneThreeFour]
    intro hzero
    exact hfourLastNeOne (by linarith)
  · rw [lineFreeBracket_oneThreeFive]
    intro hzero
    exact hfiveLastNeOne (by linarith)
  · rw [lineFreeBracket_oneFourFive]; exact hlastDiffNe
  · rw [lineFreeBracket_twoThreeFour]
    intro hzero
    exact hfourMidNeOne (by linarith)
  · rw [lineFreeBracket_twoThreeFive]
    intro hzero
    exact hfiveMidNeOne (by linarith)
  · rw [lineFreeBracket_twoFourFive]; exact hmidDiffNe
  · rw [lineFreeBracket_threeFourFive]; exact hcubicNe

/-! ## 9.  Inhabitation of the antecedents

An open condition needs a witness before anyone spends a fork on it.  Every
hypothesis in this file that names the line-free off-conic stratum is satisfiable,
and the witness is landed. -/

/-- The line-free off-conic stratum of `(6,3)` is inhabited.  So the antecedents of
sections 1, 4 and 6 are not vacuous. -/
theorem exists_lineFree_offConic_sixThree :
    ∃ design : WeightedDesign 6 3,
      HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))
        ∧ HasNoCommonQuadric design.atom :=
  ⟨uniformWitnessDesign, uniformWitnessDesign_hasLinePattern,
    uniformWitnessDesign_hasNoCommonQuadric⟩

/-- The admissible chart region is inhabited.  So the antecedents of sections 3, 5
and 8 are not vacuous. -/
theorem exists_isAdmissibleLineFreeParameter :
    ∃ param : ℝ × ℝ × ℝ × ℝ, IsAdmissibleLineFreeParameter param :=
  ⟨((2 : ℝ), (3 : ℝ), (5 : ℝ), (7 : ℝ)), isAdmissibleLineFreeParameter_two_three_five_seven⟩

/-- The chart point type of section 5 is inhabited.  The uniform point of the
icosahedral approximant carries mass one and weight one sixth at every label. -/
theorem exists_directionChartPoint_six : ∃ point : DirectionChartPoint 6, True :=
  ⟨icosaApproximantChartPoint, trivial⟩

/-- **THE WHOLE LINE-FREE CHART LANE IS NON-VACUOUS AT ONCE.**  The counting law of
section 5 fires at an admissible parameter and a real chart point. -/
theorem three_le_card_overLevered_lineFree_at_witness :
    3 ≤ (Finset.univ.filter
      (fun label => icosaApproximantChartPoint.weight label
        < chartMassLeverage (lineFreeDirection ((2 : ℝ), (3 : ℝ), (5 : ℝ), (7 : ℝ)))
            icosaApproximantChartPoint.mass label)).card :=
  three_le_card_overLevered_lineFree ((2 : ℝ), (3 : ℝ), (5 : ℝ), (7 : ℝ))
    icosaApproximantChartPoint

end Gtz
