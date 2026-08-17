/-
# The one-line backlog, wired

Entry `#2` of `Gtz.stressFreeResidualFamiliesSix` is the pattern `[[0,1,2]]`.
Its chart is `Gtz.oneLineDirection`, a three-parameter family.  Six landed groups
of results stop one step short of an instance at this pattern.  This file takes
all six steps, and it takes four more that a second review named.

## What each section does

**1.  The free moment discharge.**  `Gtz.posDef_massMoment_oneLineDirection`
proves the sole structural hypothesis of the direction-generic leverage toolkit,
by `rfl` against `Gtz.chartMassMoment_eq`.  Nothing consumed it.  Section 1 lands
the counting law and the leverage veto at `Gtz.oneLineDirection`, and fires the
counting law at an explicit admissible parameter and an explicit chart point.

**2.  The weak-dominator bridge.**  A tie supplies a WEAK dominator only.  The
strictly heavy handles `Gtz.subset_strictlyHeavySet_of_posDef` and
`Gtz.eq_strictlyHeavySet_of_posDef_of_card_eq_three` both ask for `PosDef`, so
they confine the conclusion and not the hypothesis.
`Gtz.flatPair_mem_strictlyHeavySet_of_dominates` is the one place where a WEAK
dominator feeds the strictly heavy set.  Section 2 reads it at the one-line
pattern, where the pattern itself supplies the unit normal.

**3.  The chart route, end to end.**  `Gtz.parameterizedChartCovers_oneLineDirection`
carries no hypothesis, and `Gtz.oneLineOnPath_of_chart` turns chart tie-freeness
into the registry Prop.  Section 3 composes that with the other four on-path
Props and reaches rank-three GTZ at every size.  The one open half of this class
is then visibly the analytic one.

**4.  The stratum is uniformly stress-free, and the collapse is landed.**
`Gtz.oneLine_stratumIsTieFree_iff_stressFreeStratumIsTieFree` already makes
`Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree` an equivalence here, and
`Gtz.oneLineOnPath_iff_stressFreeStratumIsTieFree` already collapses five names.
Section 4 does not repeat either.  It adds the SIXTH name, the flat-split
residual, and the chart hypothesis above all six.

**5.  Three buried theorems, spent.**  `Gtz/Wave/OneLineWedgeFlatSplit.lean` and
`Gtz/Wave/OneLineCombinedSharpDeterminant.lean` carry 3277 lines between them and
almost no outward consumer.  Section 5 spends the three whose conclusion is
nearest to positive definiteness of a gap at this pattern.

**6.  Inhabitation.**  `Gtz.oneLineSampleDesign` is an exact-rational design of
this stratum with two strictly dominating triples.  Section 6 certifies the
antecedents of sections 2 and 5 against it.

**7.  The two surviving polynomial inequalities.**  Under all-heavy plus one
strictly heavy member, the three-invariant decision of strict domination loses
its first invariant.  Section 7 states the residue as an equivalence in TWO
polynomial inequalities.

**8.  The in-plane half is a theorem.**  `Gtz.gtz_rank_two` is proved, and
`Gtz.inPlaneRestriction` makes the restriction to a plane frame a genuine
rank-two design.  Section 8 hands back a covering pair in the line's own plane.

**9.  The boundary is diamond-free.**  Section 9 pins that in kernel form.

## Two traps, checked at every declaration

EQUIVALENCE.  Each docstring says whether the statement is an equivalence, a
strict reduction, or a wiring composition.  Sections 4 and 7 are equivalences and
add no strength.

UNSATISFIABLE ANTECEDENT.  Section 6 exhibits an inhabitant of every hypothesis
group this file introduces, with one exception that the section names.
-/
import Gtz.Wave.AllHeavyWedgeCollapse
import Gtz.Wave.OneLineCombinedSharpDeterminant
import Gtz.Wave.ThreeLinesSlideElimination
import Gtz.Wave.WiringAllFiveOnPath
import Gtz.Wave.WiringLineChartRoads
import Gtz.Design.ChartProgrammeAssembly
import Gtz.Design.LineClassObstructions
import Gtz.Design.LineFreeConicBridge
import Gtz.Design.StressFreeMatroidStratification
import Gtz.Design.InPlaneRestriction
import Gtz.Design.NearPencilStrictDomination
import Gtz.LinAlg.PsdKit
import Gtz.Reduction.BalancedStratumClosure

set_option linter.style.longLine false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## 1.  The free moment discharge at the one-line chart

`Gtz.three_le_card_overLevered` and `Gtz.weight_lt_chartMassLeverage_of_posDef_gap`
quantify over an arbitrary direction family and ask for one thing: a positive
definite mass moment.  Labels zero, one and three of `Gtz.oneLineDirection` are
the coordinate axes, so the moment holds at every parameter, admissible or not,
and at every chart point. -/

/-- **THE MASS MOMENT OF THE ONE-LINE CHART IS POSITIVE DEFINITE.**  A wiring
composition.  `Gtz.chartMassMoment_eq` holds by `rfl`, so
`Gtz.posDef_massMoment_oneLineDirection` IS this statement. -/
theorem posDef_chartMassMoment_oneLine (param : ℝ × ℝ × ℝ) (point : DirectionChartPoint 6) :
    (chartMassMoment (oneLineDirection param) point.mass).PosDef := by
  rw [chartMassMoment_eq]
  exact posDef_massMoment_oneLineDirection param point

/-- **THE COUNTING LAW AT THE ONE-LINE CHART.**  A wiring composition.  At every
chart point at least three labels carry mass leverage above their own weight.  No
admissibility, no line pattern and no design. -/
theorem three_le_card_overLevered_oneLine (param : ℝ × ℝ × ℝ)
    (point : DirectionChartPoint 6) :
    3 ≤ (Finset.univ.filter
      (fun label => point.weight label
        < chartMassLeverage (oneLineDirection param) point.mass label)).card :=
  three_le_card_overLevered (oneLineDirection param) point
    (posDef_chartMassMoment_oneLine param point)

/-- **THE LEVERAGE VETO AT THE ONE-LINE CHART.**  A wiring composition.  A label
of a strictly dominating triple carries mass leverage above its own weight, as
soon as one probe reads that label and no other selected label. -/
theorem weight_lt_chartMassLeverage_oneLine (param : ℝ × ℝ × ℝ)
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6)) (pivotLabel : Fin 6)
    (hmem : pivotLabel ∈ selected) (probe : Fin 3 → ℝ)
    (hblind : ∀ other ∈ selected, other ≠ pivotLabel →
      oneLineDirection param other ⬝ᵥ probe = 0)
    (hlive : oneLineDirection param pivotLabel ⬝ᵥ probe ≠ 0)
    (hgap : (directionChartGap (oneLineDirection param) point.mass point.weight
      selected).PosDef) :
    point.weight pivotLabel
      < chartMassLeverage (oneLineDirection param) point.mass pivotLabel :=
  weight_lt_chartMassLeverage_of_posDef_gap (oneLineDirection param) point.mass point.weight
    point.mass_pos point.weight_pos (posDef_chartMassMoment_oneLine param point) selected
    pivotLabel hmem probe hblind hlive hgap

/-- The counting law fires at an admissible parameter and a real chart point, so
section 1 is not vacuous. -/
theorem three_le_card_overLevered_oneLine_at_witness :
    3 ≤ (Finset.univ.filter
      (fun label => icosaApproximantChartPoint.weight label
        < chartMassLeverage (oneLineDirection ((2 : ℝ), (3 : ℝ), (4 : ℝ)))
            icosaApproximantChartPoint.mass label)).card :=
  three_le_card_overLevered_oneLine ((2 : ℝ), (3 : ℝ), (4 : ℝ)) icosaApproximantChartPoint

/-! ## 2.  The weak-dominator bridge at the one-line pattern

`Gtz.flatPair_mem_strictlyHeavySet_of_dominates` asks for a unit normal that two
of the three members of a card-three WEAK dominator read as zero.  At the
one-line pattern the line normal is exactly such a vector, and
`Gtz.oneLine_exists_unitNormal` supplies it from the pattern alone. -/

/-- The unit line normal is nonzero. -/
theorem ne_zero_of_dotProduct_self_eq_one {vec : Fin 3 → ℝ} (hunit : vec ⬝ᵥ vec = 1) :
    vec ≠ 0 := by
  intro hzero
  rw [hzero] at hunit
  simp at hunit

/-- **THE LINE PAIR OF A WEAK DOMINATOR IS STRICTLY HEAVY.**  A wiring
composition, with the normal still an input.  Both line members enter
`Gtz.strictlyHeavySet`, and the dominator is only WEAK. -/
theorem oneLine_linePair_mem_strictlyHeavySet_of_dominates (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {lineFirst lineSecond freeLabel : Fin 6}
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstFree : lineFirst ≠ freeLabel)
    (hSecondFree : lineSecond ≠ freeLabel)
    (hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (hindependent : 0 < leverageOf (design.atom lineFirst) * leverageOf (design.atom lineSecond)
      - gapPairingOf design lineFirst lineSecond ^ 2)
    (hpairing : design.atom lineFirst ⬝ᵥ design.atom lineSecond ≠ 0)
    (hdominates : Dominates design {lineFirst, lineSecond, freeLabel}) :
    lineFirst ∈ strictlyHeavySet design ∧ lineSecond ∈ strictlyHeavySet design :=
  flatPair_mem_strictlyHeavySet_of_dominates design hFirstSecond hFirstFree hSecondFree
    unitNormal hunit (hlineFlat lineFirst hFirstMem) (hlineFlat lineSecond hSecondMem)
    hheavy hindependent hpairing hdominates

/-- **THE SAME, WITH THE NORMAL REMOVED.**  A strict reduction of the hypothesis
list: the pattern supplies the normal, so the caller names no vector.  The
conclusion is the leverage reading of the membership. -/
theorem oneLine_linePair_strictlyHeavy_of_pattern (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    {lineFirst lineSecond freeLabel : Fin 6}
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstFree : lineFirst ≠ freeLabel)
    (hSecondFree : lineSecond ≠ freeLabel)
    (hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (hindependent : 0 < leverageOf (design.atom lineFirst) * leverageOf (design.atom lineSecond)
      - gapPairingOf design lineFirst lineSecond ^ 2)
    (hpairing : design.atom lineFirst ⬝ᵥ design.atom lineSecond ≠ 0)
    (hdominates : Dominates design {lineFirst, lineSecond, freeLabel}) :
    1 < leverageOf (design.atom lineFirst) ∧ 1 < leverageOf (design.atom lineSecond) := by
  obtain ⟨unitNormal, hunit, hlineFlat⟩ := oneLine_exists_unitNormal design hpattern
  obtain ⟨hfirst, hsecond⟩ := oneLine_linePair_mem_strictlyHeavySet_of_dominates design hunit
    hlineFlat hFirstMem hSecondMem hFirstSecond hFirstFree hSecondFree hheavy hindependent
    hpairing hdominates
  exact ⟨(mem_strictlyHeavySet_iff design lineFirst).mp hfirst,
    (mem_strictlyHeavySet_iff design lineSecond).mp hsecond⟩

/-- **THE PAIR MINOR OF THE LINE PAIR, WITH THE NORMAL REMOVED.**  A wiring
composition that spends `Gtz.oneLine_dominator_linePair_gapExcess_nonneg`, which
had no outward consumer. -/
theorem oneLine_linePair_gapExcess_nonneg_of_pattern (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    {lineFirst lineSecond freeLabel : Fin 6}
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstFree : lineFirst ≠ freeLabel)
    (hSecondFree : lineSecond ≠ freeLabel)
    (hindependent : 0 < leverageOf (design.atom lineFirst) * leverageOf (design.atom lineSecond)
      - gapPairingOf design lineFirst lineSecond ^ 2)
    (hdominates : Dominates design {lineFirst, lineSecond, freeLabel}) :
    0 ≤ pairGapExcessOf design lineFirst lineSecond := by
  obtain ⟨unitNormal, hunit, hlineFlat⟩ := oneLine_exists_unitNormal design hpattern
  exact oneLine_dominator_linePair_gapExcess_nonneg design hunit hlineFlat hFirstMem hSecondMem
    hFirstSecond hFirstFree hSecondFree hindependent hdominates

/-- **THE THIRD MEMBER READS THE NORMAL AT UNIT SQUARE.**  A wiring composition.
A weak dominator holding two line labels forces its free member to a normal
reading of square at least one. -/
theorem oneLine_freeNormalSq_of_dominates_linePair (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {lineFirst lineSecond freeLabel : Fin 6}
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstFree : lineFirst ≠ freeLabel) (hSecondFree : lineSecond ≠ freeLabel)
    (hdominates : Dominates design {lineFirst, lineSecond, freeLabel}) :
    1 ≤ (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 :=
  one_le_freeNormalSq_of_dominates design hFirstFree hSecondFree unitNormal hunit
    (hlineFlat lineFirst hFirstMem) (hlineFlat lineSecond hSecondMem) hdominates

/-- **THE LINE COUNT OF A WEAK DOMINATOR, WITH THE NORMAL REMOVED.**  A wiring
composition.  A card-three weak dominator never holds all three line labels. -/
theorem oneLine_dominator_lineCount_le_two_of_pattern (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    {dominator : Finset (Fin 6)} (hcard : dominator.card = 3)
    (hdominates : Dominates design dominator) :
    (dominator ∩ ({0, 1, 2} : Finset (Fin 6))).card ≤ 2 := by
  obtain ⟨unitNormal, hunit, hlineFlat⟩ := oneLine_exists_unitNormal design hpattern
  exact oneLine_dominator_lineCount_le_two design (ne_zero_of_dotProduct_self_eq_one hunit)
    hlineFlat hcard hdominates

/-- A card-three subset of `Fin 6` that misses the line IS the free triple.  Pure
combinatorics, no design. -/
theorem oneLine_eq_freeTriple_of_lineCount_zero {dominator : Finset (Fin 6)}
    (hcard : dominator.card = 3)
    (hempty : dominator ∩ ({0, 1, 2} : Finset (Fin 6)) = ∅) :
    dominator = ({3, 4, 5} : Finset (Fin 6)) := by
  classical
  have hsub : dominator ⊆ (({0, 1, 2} : Finset (Fin 6)))ᶜ := by
    intro label hlabel
    rw [Finset.mem_compl]
    intro hmem
    have hin : label ∈ dominator ∩ ({0, 1, 2} : Finset (Fin 6)) :=
      Finset.mem_inter.mpr ⟨hlabel, hmem⟩
    rw [hempty] at hin
    exact absurd hin (Finset.notMem_empty label)
  rw [oneLine_lineSet_compl] at hsub
  exact Finset.eq_of_subset_of_card_le hsub (by rw [hcard]; decide)

/-- **THE LINE COUNT TRICHOTOMY.**  A wiring composition.  Every card-three weak
dominator of a one-line design meets the line in zero, one or two labels, and the
zero case names the free triple outright. -/
theorem oneLine_dominator_lineCount_trichotomy (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    {dominator : Finset (Fin 6)} (hcard : dominator.card = 3)
    (hdominates : Dominates design dominator) :
    dominator = ({3, 4, 5} : Finset (Fin 6))
      ∨ (dominator ∩ ({0, 1, 2} : Finset (Fin 6))).card = 1
      ∨ (dominator ∩ ({0, 1, 2} : Finset (Fin 6))).card = 2 := by
  classical
  have hbound := oneLine_dominator_lineCount_le_two_of_pattern design hpattern hcard hdominates
  rcases Nat.lt_or_ge (dominator ∩ ({0, 1, 2} : Finset (Fin 6))).card 1 with hzero | hone
  · refine Or.inl (oneLine_eq_freeTriple_of_lineCount_zero hcard ?_)
    exact Finset.card_eq_zero.mp (by omega)
  · rcases Nat.lt_or_ge (dominator ∩ ({0, 1, 2} : Finset (Fin 6))).card 2 with hlt | hge
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

/-- **A TIE CARRIES THE TRICHOTOMY.**  A wiring composition.  The tie supplies
the weak dominator, and the trichotomy classifies it. -/
theorem oneLine_tie_dominator_lineCount_trichotomy (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (htie : IsTie design) :
    ∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator
      ∧ (dominator = ({3, 4, 5} : Finset (Fin 6))
        ∨ (dominator ∩ ({0, 1, 2} : Finset (Fin 6))).card = 1
        ∨ (dominator ∩ ({0, 1, 2} : Finset (Fin 6))).card = 2) := by
  obtain ⟨dominator, hcard, hdominates⟩ := htie.1
  exact ⟨dominator, hcard, hdominates,
    oneLine_dominator_lineCount_trichotomy design hpattern hcard hdominates⟩

/-- **THE LINE ITSELF NEVER DOMINATES.**  A wiring composition of
`Gtz.not_dominates_of_atomBracket_eq_zero` at the pattern.  So a weak dominator
is one of NINETEEN basis triples, and never the twentieth. -/
theorem oneLine_not_dominates_lineTriple (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    ¬ Dominates design {(0 : Fin 6), 1, 2} :=
  not_dominates_of_atomBracket_eq_zero design 0 1 2
    ((hpattern 0 1 2 (by decide) (by decide) (by decide)).mpr (by decide))

/-! ## 3.  The chart route, end to end

The registry says the two generic chart forms need a chart nobody built for this
pattern.  That reading is out of date.  `Gtz.oneLineDirection` is landed,
`Gtz.parameterizedChartCovers_oneLineDirection` carries ZERO hypotheses, and
`Gtz.oneLineOnPath_of_chart` turns chart tie-freeness into the registry Prop.
The composition below shows that the only open half of this class is analytic. -/

/-- **THE FIVE ON-PATH PROPS, WITH ENTRY `#2` REPLACED BY ITS CHART.**  A wiring
composition. -/
theorem allFiveOnPath_of_oneLineChart
    (hchart : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param))
    (hlineFree : BaseTripleTightLineFreeOffConicHeavyNeedleResidual)
    (hTwoMeeting : TwoMeetingLinesTenthHeavyJointBlindTransversal)
    (hThreeLines :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines)
    (hKFour : KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict) :
    AllFiveOnPath :=
  ⟨hlineFree, oneLineOnPath_of_chart hchart, hTwoMeeting, hThreeLines, hKFour⟩

/-- **RANK-THREE GTZ AT EVERY SIZE, WITH ENTRY `#2` CARRIED BY ITS CHART.**  A
wiring composition.  The one-line class contributes exactly one analytic
statement about a three-parameter family of six fixed vectors. -/
theorem gtzWeightedAll_three_of_oneLineChart
    (hchart : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param))
    (hlineFree : BaseTripleTightLineFreeOffConicHeavyNeedleResidual)
    (hTwoMeeting : TwoMeetingLinesTenthHeavyJointBlindTransversal)
    (hThreeLines :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines)
    (hKFour : KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_allFiveOnPath
    (allFiveOnPath_of_oneLineChart hchart hlineFree hTwoMeeting hThreeLines hKFour)

/-- **THE ORIGINAL THEOREM AT RANK THREE, WITH ENTRY `#2` CARRIED BY ITS CHART.**
A wiring composition, and the longest road this file walks. -/
theorem forall_gtzOriginal_rank_three_of_oneLineChart
    (hchart : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param))
    (hlineFree : BaseTripleTightLineFreeOffConicHeavyNeedleResidual)
    (hTwoMeeting : TwoMeetingLinesTenthHeavyJointBlindTransversal)
    (hThreeLines :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines)
    (hKFour : KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict) :
    ∀ sizeParam : ℕ, 0 < sizeParam → GtzOriginal sizeParam 3 :=
  forall_gtzOriginal_rank_three_of_stressFreeHingeAlone
    (stressFreeHingeHoldsSixThree_of_allFiveOnPath
      (allFiveOnPath_of_oneLineChart hchart hlineFree hTwoMeeting hThreeLines hKFour))

/-- The chart parameter range is inhabited, so section 3 is not vacuous. -/
theorem exists_isAdmissibleOneLineParameter :
    ∃ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param :=
  ⟨((2 : ℝ), (3 : ℝ), (4 : ℝ)), isAdmissibleOneLineParameter_two_three_four⟩

/-! ## 4.  The sixth name

`Gtz.oneLineOnPath_iff_stratumIsTieFree` collapses four names, and
`Gtz.oneLineOnPath_iff_stressFreeStratumIsTieFree` adds the fifth.  The collapse
of `Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree` into an equivalence at
this pattern is `Gtz.oneLine_stratumIsTieFree_iff_stressFreeStratumIsTieFree`,
and its stress-free input is `Gtz.stratumIsStressFree_oneThreePointLine`.  Both
are landed, and this section repeats neither.

What it adds is the flat-split residual, a SIXTH spelling that lives in
`Gtz/Wave/OneLineWedgeFlatSplit.lean` and never met the collapse. -/

/-- **THE SIXTH NAME.**  An equivalence.  It collapses one more spelling and adds
no strength. -/
theorem oneLineFlatSplitResidual_iff_stressFreeStratumIsTieFree :
    OneLineFlatSplitResidual
      ↔ StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  oneLineFlatSplitResidual_iff.trans oneLineOnPath_iff_stressFreeStratumIsTieFree

/-- **THE SIXTH NAME, AGAINST THE PLAIN STRATUM SPELLING.**  An equivalence. -/
theorem oneLineFlatSplitResidual_iff_stratumIsTieFree :
    OneLineFlatSplitResidual ↔ StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  oneLineFlatSplitResidual_iff_stressFreeStratumIsTieFree.trans
    oneLine_stratumIsTieFree_iff_stressFreeStratumIsTieFree.symm

/-- **SIX NAMES, ONE STATEMENT.**  An equivalence in three links.  Nothing in the
chain is a reduction. -/
theorem oneLine_sixNames_one_statement :
    (OneLineFlatSplitResidual ↔ OneLineTenthHeavyJointBlindLineSparse)
      ∧ (OneLineTenthHeavyJointBlindLineSparse
          ↔ StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
      ∧ (StratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]])
          ↔ StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :=
  ⟨oneLineFlatSplitResidual_iff, oneLineOnPath_iff_stratumIsTieFree,
    oneLine_stratumIsTieFree_iff_stressFreeStratumIsTieFree⟩

/-- **THE CHART HYPOTHESIS SITS ABOVE ALL SIX NAMES.**  A wiring composition. -/
theorem oneLineFlatSplitResidual_of_chart
    (hchart : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param)) :
    OneLineFlatSplitResidual :=
  oneLineFlatSplitResidual_iff.mpr (oneLineOnPath_of_chart hchart)

/-! ## 5.  Three buried theorems, spent

Each of the three below scored ZERO outward consumers before this file
(MEASURED, with `Gtz/Audit.lean` excluded from the count, because that file
names every declaration once).  Each has a conclusion that bears on positive
definiteness of a gap at this pattern. -/

/-- **A MIXED WEAK DOMINATOR BECOMES STRICT ON TWO SIGNS.**  A wiring
composition, and the shortest route from a WEAK card-three dominator holding
exactly one line label to a STRICT one.

It spends `Gtz.oneLine_wedgeBalanceAt_of_lineReading_gt_leak`, which had no
outward consumer, against `Gtz.posDef_of_dominates_of_wedgeBalance`, whose
leverage threshold a weak dominator pays for free.  No surplus beyond the
normal one, no leverage floor and no blind spot appear. -/
theorem oneLine_posDef_of_mixedWeakDominator (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (selected : Finset (Fin 6)) (hdominates : Dominates design selected)
    {lineLabel : Fin 6} (hinter : selected ∩ ({0, 1, 2} : Finset (Fin 6)) = {lineLabel})
    (hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
    (hreading : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      flatLeak design ({0, 1, 2} : Finset (Fin 6)) probeVec
        < (design.atom lineLabel ⬝ᵥ probeVec) ^ 2)
    (hsharp : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      0 ≤ sharpBalanceValue design selected ({0, 1, 2} : Finset (Fin 6)) unitNormal probeVec) :
    (subsetSum design selected - 1).PosDef :=
  posDef_of_dominates_of_wedgeBalance design selected hdominates unitNormal hunit
    fun probeVec hperp hne =>
      oneLine_wedgeBalanceAt_of_lineReading_gt_leak design selected unitNormal probeVec hunit
        hlineFlat hinter hsurplus (hreading probeVec hperp hne) (hsharp probeVec hperp hne)

/-- **THE SAME, CARRIED TO THE CLASS.**  A wiring composition.  The two signs at
one mixed weak dominator retire the whole flat-split selector at the line
normal. -/
theorem oneLine_lineFlatSplitSelectorAt_of_mixedWeakDominator (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hdominates : Dominates design selected)
    {lineLabel : Fin 6} (hinter : selected ∩ ({0, 1, 2} : Finset (Fin 6)) = {lineLabel})
    (hsurplus : 1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
    (hreading : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      flatLeak design ({0, 1, 2} : Finset (Fin 6)) probeVec
        < (design.atom lineLabel ⬝ᵥ probeVec) ^ 2)
    (hsharp : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      0 ≤ sharpBalanceValue design selected ({0, 1, 2} : Finset (Fin 6)) unitNormal probeVec) :
    LineFlatSplitSelectorAt design unitNormal :=
  lineFlatSplitSelectorAt_of_exists_posDef_cardThree design hunit hlineFlat
    ⟨selected, hcard, oneLine_posDef_of_mixedWeakDominator design hunit hlineFlat selected
      hdominates hinter hsurplus hreading hsharp⟩

/-- **RANK-THREE GTZ FROM THE WEDGE MINOR SELECTOR AT THE TWO LINE CLASSES.**  A
wiring composition that spends `Gtz.oneLine_and_twoMeetingLines_of_wedgeMinorSelector`,
which had no outward consumer.

CAUTION, and it is the module's own verdict: `Gtz.wedgeMinorSelector_iff_exists_strictTriple`
proves the unrestricted selector EQUAL to the strict half it produces, so the
unrestricted form relocates the problem and does not shrink it.  The hypothesis
below is NOT that form.  It names the one-line and two-meeting-lines antecedent
region, exactly as the two registry Props do. -/
theorem gtzWeightedAll_three_of_oneLineWedgeMinorSelector
    (hselector : ∀ design : WeightedDesign 6 3, ∀ unitNormal : Fin 3 → ℝ,
      unitNormal ⬝ᵥ unitNormal = 1 →
      (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ unitNormal = 0) →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (1 < ∑ label ∈ selected, (design.atom label ⬝ᵥ unitNormal) ^ 2)
        ∧ 0 < wedgeMinor design selected unitNormal
        ∧ ∃ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 ∧ probeVec ≠ 0
            ∧ 0 < wedgeBalanceValue design selected unitNormal probeVec)
    (hlineFree : BaseTripleTightLineFreeOffConicHeavyNeedleResidual)
    (hThreeLines :
      ChartTieFreeThreeLinesFundamentalDomainBudgetReadingSevenOrbitTraceBlindOffLines)
    (hKFour : KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict) :
    GtzWeightedAll 3 := by
  obtain ⟨hOneLine, hTwoMeeting⟩ := oneLine_and_twoMeetingLines_of_wedgeMinorSelector hselector
  exact gtzWeightedAll_three_of_allFiveOnPath
    ⟨hlineFree, hOneLine, hTwoMeeting, hThreeLines, hKFour⟩

/-! ## 6.  Inhabitation

`Gtz.oneLineSampleDesign` is an exact-rational design of this stratum.  Its line
atoms are `(1,0,0)`, `(0,1,0)` and `(1,1,0)`, and its free atoms are `(-2,-2,1)`,
`(-1,1,2)` and `(2,-1,2)`.  Its leverages are `1, 1, 2, 9, 6, 9`. -/

/-- The sample is all-heavy, with equality at the two coordinate line atoms. -/
theorem oneLineSampleDesign_allHeavy :
    ∀ label : Fin 6, 1 ≤ leverageOf (oneLineSampleDesign.atom label) := by
  intro label
  fin_cases label <;>
    simp [leverageOf, oneLineSampleDesign, oneLineSampleAtom, Fin.sum_univ_three] <;> norm_num

/-- Exactly three of the sample's atoms are strictly heavy, so the sample sits at
the sharp end of `Gtz.three_le_card_strictlyHeavySet_sixThree`. -/
theorem oneLineSampleDesign_strictlyHeavy_freeTriple :
    ∀ freeLabel ∈ ({3, 4, 5} : Finset (Fin 6)),
      1 < leverageOf (oneLineSampleDesign.atom freeLabel) := by
  intro freeLabel hmem
  fin_cases freeLabel <;>
    first
      | exact absurd hmem (by decide)
      | norm_num [leverageOf, oneLineSampleDesign, oneLineSampleAtom, Fin.sum_univ_three,
          Matrix.cons_val_two, Matrix.tail_cons]

/-- The sample's mixed triple `{2,4,5}` meets the line in exactly one label. -/
theorem oneLineSample_mixedTriple_inter :
    ({2, 4, 5} : Finset (Fin 6)) ∩ ({0, 1, 2} : Finset (Fin 6)) = {2} := by decide

/-- The sample's mixed triple is a WEAK dominator, so the antecedent of section 5
is not vacuous.  `Gtz.oneLineSample_mixedTripleGap_posDef` shows it is a STRICT
one, which is why the two sign hypotheses of section 5 are satisfiable there. -/
theorem oneLineSampleDesign_dominates_mixedTriple :
    Dominates oneLineSampleDesign {2, 4, 5} :=
  oneLineSample_mixedTripleGap_posSemidef

/-- **THE ANTECEDENT OF SECTION 5 IS INHABITED.**  One design carries the
pattern, all-heavy leverages, a card-three weak dominator and the exact line
count that section 5 asks for. -/
theorem oneLineSample_inhabits_mixedBranch :
    HasLinePattern oneLineSampleDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2]])
      ∧ (∀ label : Fin 6, 1 ≤ leverageOf (oneLineSampleDesign.atom label))
      ∧ ({2, 4, 5} : Finset (Fin 6)).card = 3
      ∧ Dominates oneLineSampleDesign {2, 4, 5}
      ∧ ({2, 4, 5} : Finset (Fin 6)) ∩ ({0, 1, 2} : Finset (Fin 6)) = {2} :=
  ⟨oneLineSampleDesign_hasLinePattern, oneLineSampleDesign_allHeavy, by decide,
    oneLineSampleDesign_dominates_mixedTriple, oneLineSample_mixedTriple_inter⟩

/-- **THE ANTECEDENT OF SECTION 2 IS INHABITED IN ITS ZERO-COUNT BRANCH.**  The
sample's free triple weakly dominates and misses the line, so the trichotomy's
first branch fires at a real design. -/
theorem oneLineSample_inhabits_freeBranch :
    Dominates oneLineSampleDesign {3, 4, 5}
      ∧ ({3, 4, 5} : Finset (Fin 6)) ∩ ({0, 1, 2} : Finset (Fin 6)) = ∅ :=
  ⟨oneLineSampleDesign_dominates_freeTriple, by decide⟩

/-- The trichotomy fires at the sample, in its first branch. -/
theorem oneLineSample_trichotomy_at_freeTriple :
    ({3, 4, 5} : Finset (Fin 6)) = ({3, 4, 5} : Finset (Fin 6))
      ∨ (({3, 4, 5} : Finset (Fin 6)) ∩ ({0, 1, 2} : Finset (Fin 6))).card = 1
      ∨ (({3, 4, 5} : Finset (Fin 6)) ∩ ({0, 1, 2} : Finset (Fin 6))).card = 2 :=
  oneLine_dominator_lineCount_trichotomy oneLineSampleDesign
    oneLineSampleDesign_hasLinePattern (by decide) oneLineSampleDesign_dominates_freeTriple

/-- The sample is not a tie, so this stratum has an inhabitant with the class
conclusion already true. -/
theorem oneLineSample_not_isTie : ¬ IsTie oneLineSampleDesign :=
  oneLineSampleDesign_not_isTie

/-! ## 7.  The two surviving polynomial inequalities

`Gtz.subsetSum_posDef_iff_tripleInvariants` decides strict domination of a
card-three subset by THREE coordinate-free polynomial inequalities in the
leverages, the pair cross-norms and the bracket.
`Gtz.subsetSum_posDef_of_heavy_of_minorSum_of_det` discharges the FIRST from
heaviness plus one strictly heavy member.

The equivalence below removes the first invariant from both sides at once, so it
states the exact residue.  It is an equivalence, and it adds no strength. -/

/-- **THE RESIDUE IS TWO POLYNOMIAL INEQUALITIES.**  An equivalence.  Under
all-heavy leverages and one strictly heavy member, the three-invariant decision
of strict domination loses its trace invariant.  What survives is the second
elementary symmetric test and the determinant test. -/
theorem subsetSum_posDef_iff_twoInvariants_of_heavy {size : ℕ}
    (design : WeightedDesign size 3) (firstLabel secondLabel thirdLabel : Fin size)
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel)
    (hheavy : ∀ label : Fin size, 1 ≤ leverageOf (design.atom label))
    (hstrict : 1 < leverageOf (design.atom firstLabel)) :
    (subsetSum design ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)) - 1).PosDef
      ↔ (0 < triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
                (design.atom thirdLabel)
              - 2 * tripleLeverageSum (design.atom firstLabel) (design.atom secondLabel)
                  (design.atom thirdLabel) + 3
          ∧ 0 < atomBracket design firstLabel secondLabel thirdLabel ^ 2
                - triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
                    (design.atom thirdLabel)
                + tripleLeverageSum (design.atom firstLabel) (design.atom secondLabel)
                    (design.atom thirdLabel) - 1) := by
  constructor
  · intro hposDef
    obtain ⟨_htrace, hminorSum, hdet⟩ :=
      (subsetSum_posDef_iff_tripleInvariants design firstLabel secondLabel thirdLabel
        hfirstSecond hfirstThird hsecondThird).mp hposDef
    exact ⟨hminorSum, hdet⟩
  · rintro ⟨hminorSum, hdet⟩
    exact subsetSum_posDef_of_heavy_of_minorSum_of_det design firstLabel secondLabel thirdLabel
      hfirstSecond hfirstThird hsecondThird hheavy hstrict hminorSum hdet

/-- **THE RESIDUE AT THE ONE-LINE PATTERN.**  An equivalence.  Every hypothesis
outside the two inequalities is either the pattern or all-heavy. -/
theorem oneLine_subsetSum_posDef_iff_twoInvariants (design : WeightedDesign 6 3)
    (firstLabel secondLabel thirdLabel : Fin 6)
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel)
    (hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (hstrict : 1 < leverageOf (design.atom firstLabel)) :
    (subsetSum design ({firstLabel, secondLabel, thirdLabel} : Finset (Fin 6)) - 1).PosDef
      ↔ (0 < triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
                (design.atom thirdLabel)
              - 2 * tripleLeverageSum (design.atom firstLabel) (design.atom secondLabel)
                  (design.atom thirdLabel) + 3
          ∧ 0 < atomBracket design firstLabel secondLabel thirdLabel ^ 2
                - triplePairAreaSum (design.atom firstLabel) (design.atom secondLabel)
                    (design.atom thirdLabel)
                + tripleLeverageSum (design.atom firstLabel) (design.atom secondLabel)
                    (design.atom thirdLabel) - 1) :=
  subsetSum_posDef_iff_twoInvariants_of_heavy design firstLabel secondLabel thirdLabel
    hfirstSecond hfirstThird hsecondThird hheavy hstrict

/-- **THE TWO INEQUALITIES FIRE AT THE SAMPLE.**  The strictly heavy member is
atom three, of leverage nine, and the triple is the free one.  So section 7 is
not vacuous. -/
theorem oneLineSample_twoInvariants_at_freeTriple :
    0 < triplePairAreaSum (oneLineSampleDesign.atom 3) (oneLineSampleDesign.atom 4)
          (oneLineSampleDesign.atom 5)
        - 2 * tripleLeverageSum (oneLineSampleDesign.atom 3) (oneLineSampleDesign.atom 4)
            (oneLineSampleDesign.atom 5) + 3
      ∧ 0 < atomBracket oneLineSampleDesign 3 4 5 ^ 2
            - triplePairAreaSum (oneLineSampleDesign.atom 3) (oneLineSampleDesign.atom 4)
                (oneLineSampleDesign.atom 5)
            + tripleLeverageSum (oneLineSampleDesign.atom 3) (oneLineSampleDesign.atom 4)
                (oneLineSampleDesign.atom 5) - 1 := by
  refine (oneLine_subsetSum_posDef_iff_twoInvariants oneLineSampleDesign 3 4 5 (by decide)
    (by decide) (by decide) oneLineSampleDesign_allHeavy ?_).mp ?_
  · exact oneLineSampleDesign_strictlyHeavy_freeTriple 3 (by decide)
  · exact oneLineSample_freeTripleGap_posDef

/-! ## 8.  The in-plane half is a theorem

`Gtz.gtz_rank_two` is proved for every size.  `Gtz.inPlaneRestriction` makes the
restriction of a rank-three design to an orthonormal plane frame a genuine
rank-two design, and `Gtz.exists_inPlane_dominating_pair` hands back a pair that
covers that plane.  At the one-line pattern the plane orthogonal to the line
normal is the natural frame, and nothing in the tree read the pair there. -/

/-- The two rows of an orthonormal plane frame are unit and orthogonal. -/
theorem planeFrame_rows_orthonormal {plane : Matrix (Fin 2) (Fin 3) ℝ}
    (hframe : plane * planeᵀ = 1) :
    plane 0 ⬝ᵥ plane 0 = 1 ∧ plane 1 ⬝ᵥ plane 1 = 1 ∧ plane 0 ⬝ᵥ plane 1 = 0 := by
  have hentry : ∀ rowIndex colIndex : Fin 2,
      plane rowIndex ⬝ᵥ plane colIndex = (1 : Matrix (Fin 2) (Fin 2) ℝ) rowIndex colIndex := by
    intro rowIndex colIndex
    rw [← hframe]
    simp [Matrix.mul_apply, Matrix.transpose_apply, dotProduct]
  refine ⟨?_, ?_, ?_⟩
  · rw [hentry 0 0, Matrix.one_apply_eq]
  · rw [hentry 1 1, Matrix.one_apply_eq]
  · rw [hentry 0 1, Matrix.one_apply_ne (by decide)]

/-- **A COVERING PAIR IN THE LINE'S OWN PLANE.**  A wiring composition of a
PROVED rank-two theorem.  At every one-line design there are two atoms whose
squared readings cover every combination of an orthonormal frame of the plane
orthogonal to the line normal.  No tie, no heaviness and no dominator appear. -/
theorem oneLine_exists_inPlane_dominating_pair (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    ∃ unitNormal basisFirst basisSecond : Fin 3 → ℝ,
      unitNormal ⬝ᵥ unitNormal = 1
        ∧ (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
            design.atom lineLabel ⬝ᵥ unitNormal = 0)
        ∧ basisFirst ⬝ᵥ basisFirst = 1 ∧ basisSecond ⬝ᵥ basisSecond = 1
        ∧ basisFirst ⬝ᵥ basisSecond = 0
        ∧ ∃ pairFirst pairSecond : Fin 6, pairFirst ≠ pairSecond ∧
            ∀ alpha beta : ℝ,
              (alpha • basisFirst + beta • basisSecond)
                  ⬝ᵥ (alpha • basisFirst + beta • basisSecond)
                ≤ (design.atom pairFirst ⬝ᵥ (alpha • basisFirst + beta • basisSecond)) ^ 2
                  + (design.atom pairSecond
                      ⬝ᵥ (alpha • basisFirst + beta • basisSecond)) ^ 2 := by
  obtain ⟨lineNormal, hunit, hlineFlat⟩ := oneLine_exists_unitNormal design hpattern
  obtain ⟨plane, unitNormal, _unitScale, hframe, hparallel, _hscaleNe, hunitSq,
    _hkills, _hresolve⟩ :=
    exists_planeFrame_of_ne_zero lineNormal (ne_zero_of_dotProduct_self_eq_one hunit)
  obtain ⟨hfirstUnit, hsecondUnit, horth⟩ := planeFrame_rows_orthonormal hframe
  refine ⟨unitNormal, plane 0, plane 1, hunitSq, ?_, hfirstUnit, hsecondUnit, horth,
    exists_inPlane_dominating_pair design (plane 0) (plane 1) hfirstUnit hsecondUnit horth⟩
  intro lineLabel hmem
  rw [hparallel, dotProduct_smul, smul_eq_mul, hlineFlat lineLabel hmem, mul_zero]

/-! ## 9.  The boundary of this class is diamond-free

`Gtz.diamondFreeResidualFamiliesSix` holds exactly two of the five survivors, and
the one-line family is one of them.  So no five-label restriction of this pattern
carries the diamond matroid, and no positive-dimensional `(5,3)` tie family sits
on its weight-zero boundary.  That is what makes a uniform-in-parameter argument
plausible here and refuted at the two-meeting-lines class. -/

/-- **THE ONE-LINE FAMILY IS DIAMOND-FREE.**  A kernel reading of the landed
seam. -/
theorem oneLineFamily_mem_diamondFreeResidualFamiliesSix :
    ([[(0 : Fin 6), 1, 2]] : List (List (Fin 6))) ∈ diamondFreeResidualFamiliesSix := by decide

/-- **THE SEAM AT THIS CLASS, IN BOTH DIRECTIONS.**  The one-line pattern carries
no shared line pair, and it is not in the diamond-carrying list. -/
theorem oneLine_not_hasSharedLinePairRestriction_and_not_diamondCarrying :
    ¬ HasSharedLinePairRestriction (lineFamilyPattern [[(0 : Fin 6), 1, 2]])
      ∧ ([[(0 : Fin 6), 1, 2]] : List (List (Fin 6)))
          ∉ diamondCarryingResidualFamiliesSix :=
  ⟨not_hasSharedLinePairRestriction_oneThreePointLine, by decide⟩

/-- **THE TWO EASY CLASSES, TOGETHER.**  A wiring composition.  Tie-freeness of
the line-free class and of the one-line class discharges the whole diamond-free
half of the seam split. -/
theorem diamondFreeResidualFamiliesSix_tieFree_of_two
    (hlineFree : StressFreeStratumIsTieFree (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hOneLine : StressFreeStratumIsTieFree (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    ∀ lines ∈ diamondFreeResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines) := by
  intro lines hlines
  simp only [diamondFreeResidualFamiliesSix, List.mem_cons, List.not_mem_nil,
    or_false] at hlines
  rcases hlines with rfl | rfl
  · exact hlineFree
  · exact hOneLine

/-- **THE DIAMOND-FREE HALF FROM THE ONE-LINE CHART.**  A wiring composition.
The chart hypothesis of section 3 discharges the one-line half of the seam
outright. -/
theorem diamondFreeResidualFamiliesSix_tieFree_of_oneLineChart
    (hlineFree : StressFreeStratumIsTieFree (lineFamilyPattern ([] : List (List (Fin 6)))))
    (hchart : ∀ param : ℝ × ℝ × ℝ, IsAdmissibleOneLineParameter param →
      DirectionChartIsTieFree (oneLineDirection param)) :
    ∀ lines ∈ diamondFreeResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines) :=
  diamondFreeResidualFamiliesSix_tieFree_of_two hlineFree
    (stressFreeStratumIsTieFree_oneLine_of_chart hchart)

/-! ## 10.  NEW.  The two-line branch collapses to one inequality

Everything above is wiring.  This section is not.

`Gtz.posDef_iff_normalSurplus_and_wedgeBalance` decides strict domination of ANY
subset against ANY unit normal by a surplus and a border minor.  At a card-three
subset holding TWO line atoms the border minor COLLAPSES, and the collapse is the
content of this section.

Write `h` for the free member's normal reading and `q` for an in-plane probe.
The two line atoms read the normal as zero, so the cross sum is the single term
`(a_F . q) h` and the surplus is `h^2`.  The border minor reads

  `(a_F . q)^2 h^2 < (h^2 - 1) * ((a_1 . q)^2 + (a_2 . q)^2 + (a_F . q)^2 - q.q)`.

The free member's own in-plane reading appears on BOTH sides with the same
coefficient `h^2`, so it cancels exactly:

  `(a_F . q)^2 < (h^2 - 1) * ((a_1 . q)^2 + (a_2 . q)^2 - q.q)`.

The free atom's in-plane reading is no longer divided by anything, and the line
pair now faces the identity ALONE.  The landed flat-split machinery covers the
singleton intersection and the free triple.  It does not cover this branch.

MEASURED: `Gtz/Wave/OneLineWedgeFlatSplit.lean` carries
`Gtz.sharpBalanceValue_of_pair_singleton` for a card-three subset meeting the
line in ONE label, and `Gtz.oneLine_freeTriple_flatSplit` for the subset meeting
it in NONE.  No declaration in the tree reads the branch that meets it in TWO. -/

/-- The sum of a function over an explicit card-three set, in the argument order
that section 10 uses. -/
theorem oneLine_sum_over_triple {size : ℕ} {firstLabel secondLabel thirdLabel : Fin size}
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) (value : Fin size → ℝ) :
    ∑ label ∈ ({firstLabel, secondLabel, thirdLabel} : Finset (Fin size)), value label
      = value firstLabel + value secondLabel + value thirdLabel := by
  classical
  rw [Finset.sum_insert (by simp [hfirstSecond, hfirstThird]),
    Finset.sum_insert (by simp [hsecondThird]), Finset.sum_singleton, add_assoc]

/-- **NEW.  THE TWO-LINE BRANCH, DECIDED BY ONE INEQUALITY.**  An equivalence,
and it is not a restatement of a landed one: the free member's in-plane reading
cancels, so the line pair faces the identity alone and the free member enters
only through its height and one undivided square.

Read the right side as a competition.  The line pair must beat the identity in
the plane, and the excess it wins, amplified by the free member's height surplus,
must beat that member's own in-plane reading. -/
theorem oneLine_posDef_linePair_iff (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {lineFirst lineSecond freeLabel : Fin 6}
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstFree : lineFirst ≠ freeLabel)
    (hSecondFree : lineSecond ≠ freeLabel) :
    (subsetSum design ({lineFirst, lineSecond, freeLabel} : Finset (Fin 6)) - 1).PosDef
      ↔ (1 < (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2
        ∧ ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
            (design.atom freeLabel ⬝ᵥ probeVec) ^ 2
              < ((design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 - 1)
                * ((design.atom lineFirst ⬝ᵥ probeVec) ^ 2
                    + (design.atom lineSecond ⬝ᵥ probeVec) ^ 2 - probeVec ⬝ᵥ probeVec)) := by
  classical
  have hfirstFlat : design.atom lineFirst ⬝ᵥ unitNormal = 0 := hlineFlat lineFirst hFirstMem
  have hsecondFlat : design.atom lineSecond ⬝ᵥ unitNormal = 0 := hlineFlat lineSecond hSecondMem
  have hsurplusSum : ∑ label ∈ ({lineFirst, lineSecond, freeLabel} : Finset (Fin 6)),
      (design.atom label ⬝ᵥ unitNormal) ^ 2
      = (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 := by
    rw [oneLine_sum_over_triple hFirstSecond hFirstFree hSecondFree
      (fun label => (design.atom label ⬝ᵥ unitNormal) ^ 2), hfirstFlat, hsecondFlat]
    ring
  constructor
  · intro hposDef
    obtain ⟨hsurplus, hcover⟩ := normalSurplus_borderMinors_of_posDef design
      ({lineFirst, lineSecond, freeLabel} : Finset (Fin 6)) unitNormal hunit hposDef
    rw [hsurplusSum] at hsurplus
    refine ⟨hsurplus, fun probeVec horthogonal hprobeNe => ?_⟩
    have hstep := hcover probeVec horthogonal hprobeNe
    rw [hsurplusSum,
      oneLine_sum_over_triple hFirstSecond hFirstFree hSecondFree
        (fun label => (design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ unitNormal)),
      oneLine_sum_over_triple hFirstSecond hFirstFree hSecondFree
        (fun label => (design.atom label ⬝ᵥ probeVec) ^ 2),
      hfirstFlat, hsecondFlat] at hstep
    nlinarith [hstep]
  · rintro ⟨hsurplus, hcover⟩
    refine posDef_of_normalSurplus_planeCover design
      ({lineFirst, lineSecond, freeLabel} : Finset (Fin 6)) unitNormal hunit
      (by rw [hsurplusSum]; exact hsurplus) fun probeVec horthogonal hprobeNe => ?_
    have hstep := hcover probeVec horthogonal hprobeNe
    rw [hsurplusSum,
      oneLine_sum_over_triple hFirstSecond hFirstFree hSecondFree
        (fun label => (design.atom label ⬝ᵥ probeVec) * (design.atom label ⬝ᵥ unitNormal)),
      oneLine_sum_over_triple hFirstSecond hFirstFree hSecondFree
        (fun label => (design.atom label ⬝ᵥ probeVec) ^ 2),
      hfirstFlat, hsecondFlat]
    nlinarith [hstep]

/-! ## 11.  NEW.  What the collapse forces, and what it buys

Two consequences fall out of section 10, one on each side. -/

/-- **NEW.  A STRICT TWO-LINE DOMINATOR FORCES A STRICTLY COVERING LINE PAIR.**
A necessary condition, and it is strictly stronger than the landed weak plane
law `Gtz.planePair_dominates_inPlane_of_dominates`, which gives the same
inequality without the strictness.

The mechanism is the cancellation of section 10.  The right side of the collapsed
inequality must exceed a square, so it is positive, and the height factor is
positive as well. -/
theorem oneLine_linePair_covers_strictly_of_posDef (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {lineFirst lineSecond freeLabel : Fin 6}
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstFree : lineFirst ≠ freeLabel)
    (hSecondFree : lineSecond ≠ freeLabel)
    (hposDef : (subsetSum design ({lineFirst, lineSecond, freeLabel} : Finset (Fin 6))
      - 1).PosDef) :
    ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      probeVec ⬝ᵥ probeVec
        < (design.atom lineFirst ⬝ᵥ probeVec) ^ 2
          + (design.atom lineSecond ⬝ᵥ probeVec) ^ 2 := by
  obtain ⟨hsurplus, hcover⟩ := (oneLine_posDef_linePair_iff design hunit hlineFlat hFirstMem
    hSecondMem hFirstSecond hFirstFree hSecondFree).mp hposDef
  intro probeVec horthogonal hprobeNe
  have hstep := hcover probeVec horthogonal hprobeNe
  nlinarith [hstep, sq_nonneg (design.atom freeLabel ⬝ᵥ probeVec)]

/-- The in-plane reading of an atom is bounded by its in-plane leverage.  Cauchy
and Schwarz against the component of the atom orthogonal to the normal. -/
theorem sq_dotProduct_le_inPlaneLeverage {size : ℕ} (design : WeightedDesign size 3)
    (label : Fin size) {unitNormal probeVec : Fin 3 → ℝ}
    (hunit : unitNormal ⬝ᵥ unitNormal = 1) (horthogonal : probeVec ⬝ᵥ unitNormal = 0) :
    (design.atom label ⬝ᵥ probeVec) ^ 2
      ≤ (leverageOf (design.atom label) - (design.atom label ⬝ᵥ unitNormal) ^ 2)
        * (probeVec ⬝ᵥ probeVec) := by
  have hnormalProbe : unitNormal ⬝ᵥ probeVec = 0 := by
    rw [dotProduct_comm]; exact horthogonal
  have hnormalAtom : unitNormal ⬝ᵥ design.atom label = design.atom label ⬝ᵥ unitNormal :=
    dotProduct_comm _ _
  have hread : (design.atom label - (design.atom label ⬝ᵥ unitNormal) • unitNormal)
      ⬝ᵥ probeVec = design.atom label ⬝ᵥ probeVec := by
    rw [sub_dotProduct, smul_dotProduct, smul_eq_mul, hnormalProbe, mul_zero, sub_zero]
  have hself : (design.atom label - (design.atom label ⬝ᵥ unitNormal) • unitNormal)
      ⬝ᵥ (design.atom label - (design.atom label ⬝ᵥ unitNormal) • unitNormal)
      = leverageOf (design.atom label) - (design.atom label ⬝ᵥ unitNormal) ^ 2 := by
    simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
      hunit, hnormalAtom]
    rw [leverageOf_eq_dotProduct_self]
    ring
  have hcs := dotProduct_sq_le_mul
    (design.atom label - (design.atom label ⬝ᵥ unitNormal) • unitNormal) probeVec
  rw [hread, hself] at hcs
  exact hcs

/-- **NEW.  THE MARGIN CRITERION.**  A producer of strict domination at the
two-line branch, from three scalars and one uniform plane bound.

`margin` is how much the line pair beats the identity in the plane.  The free
member contributes its height surplus and its in-plane leverage, which is its
leverage minus the square of its height.  The criterion is a single product
comparison, with no probe left in it. -/
theorem oneLine_posDef_linePair_of_margin (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {lineFirst lineSecond freeLabel : Fin 6}
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstFree : lineFirst ≠ freeLabel)
    (hSecondFree : lineSecond ≠ freeLabel)
    (margin : ℝ)
    (hmargin : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      margin * (probeVec ⬝ᵥ probeVec)
        ≤ (design.atom lineFirst ⬝ᵥ probeVec) ^ 2
          + (design.atom lineSecond ⬝ᵥ probeVec) ^ 2 - probeVec ⬝ᵥ probeVec)
    (hheight : 1 < (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2)
    (hbudget : leverageOf (design.atom freeLabel)
        - (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2
      < ((design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 - 1) * margin) :
    (subsetSum design ({lineFirst, lineSecond, freeLabel} : Finset (Fin 6)) - 1).PosDef := by
  refine (oneLine_posDef_linePair_iff design hunit hlineFlat hFirstMem hSecondMem hFirstSecond
    hFirstFree hSecondFree).mpr ⟨hheight, fun probeVec horthogonal hprobeNe => ?_⟩
  have hlengthPos : 0 < probeVec ⬝ᵥ probeVec := dotProduct_self_pos hprobeNe
  have hcs := sq_dotProduct_le_inPlaneLeverage design freeLabel hunit horthogonal
  have hcoverStep := hmargin probeVec horthogonal hprobeNe
  have hheightPos : 0 < (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 - 1 := by linarith
  nlinarith [hcs, hcoverStep, hbudget, hlengthPos, hheightPos]

/-! ## 12.  NEW.  What a tie must pay on the two-line branch

Section 11 is a producer.  Its contrapositive is a refusal, and the refusal is a
quantitative statement about every free atom of a tie.

A tie has no strict dominator at all, so the margin criterion must fail at EVERY
line pair and EVERY free member at once.  With the line pair fixed, the failure
reads as a lower bound on each free atom's in-plane leverage. -/

/-- **NEW.  THE TIE PAYS THE MARGIN AT EVERY FREE ATOM.**  A strict reduction of
the tie hypothesis to a numerical inequality with no probe and no matrix.

If a tie's line pair beats the identity in the plane by `margin`, then every
free atom that clears unit height carries in-plane leverage at least its height
surplus times that margin.  The bound grows with the height, so a tall free atom
must also be wide. -/
theorem oneLine_tie_inPlaneLeverage_ge_of_margin (design : WeightedDesign 6 3)
    (htie : IsTie design)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {lineFirst lineSecond freeLabel : Fin 6}
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstFree : lineFirst ≠ freeLabel)
    (hSecondFree : lineSecond ≠ freeLabel)
    (margin : ℝ)
    (hmargin : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      margin * (probeVec ⬝ᵥ probeVec)
        ≤ (design.atom lineFirst ⬝ᵥ probeVec) ^ 2
          + (design.atom lineSecond ⬝ᵥ probeVec) ^ 2 - probeVec ⬝ᵥ probeVec)
    (hheight : 1 < (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2) :
    ((design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 - 1) * margin
      ≤ leverageOf (design.atom freeLabel)
        - (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 := by
  by_contra hsmall
  push Not at hsmall
  exact htie.2 ({lineFirst, lineSecond, freeLabel} : Finset (Fin 6))
    (by rw [Finset.card_insert_of_notMem (by simp [hFirstSecond, hFirstFree]),
      Finset.card_insert_of_notMem (by simp [hSecondFree]), Finset.card_singleton])
    (oneLine_posDef_linePair_of_margin design hunit hlineFlat hFirstMem hSecondMem hFirstSecond
      hFirstFree hSecondFree margin hmargin hheight hsmall)

/-- **NEW.  THE TIE REFUSES A STRICTLY COVERING LINE PAIR ABOVE ITS FREE WIDTH.**
The same statement with the line pair's excess written against the free atom's
leverage alone.  A tie with a tall free atom of small leverage forces the line
pair to sit close to the identity in the plane. -/
theorem oneLine_tie_margin_le_of_height (design : WeightedDesign 6 3)
    (htie : IsTie design)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {lineFirst lineSecond freeLabel : Fin 6}
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstFree : lineFirst ≠ freeLabel)
    (hSecondFree : lineSecond ≠ freeLabel)
    (margin : ℝ)
    (hmargin : ∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
      margin * (probeVec ⬝ᵥ probeVec)
        ≤ (design.atom lineFirst ⬝ᵥ probeVec) ^ 2
          + (design.atom lineSecond ⬝ᵥ probeVec) ^ 2 - probeVec ⬝ᵥ probeVec)
    (hheight : 1 < (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2) :
    margin * ((design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 - 1)
      ≤ leverageOf (design.atom freeLabel)
        - (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 := by
  have hbound := oneLine_tie_inPlaneLeverage_ge_of_margin design htie hunit hlineFlat hFirstMem
    hSecondMem hFirstSecond hFirstFree hSecondFree margin hmargin hheight
  linarith [hbound]

/-- **NEW.  THE TWO-LINE BRANCH IS DECIDED, WITH THE NORMAL REMOVED.**  The
pattern supplies the normal, so the criterion of section 11 needs no vector
input beyond the probe bound. -/
theorem oneLine_not_isTie_of_linePairMargin_of_pattern (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    {lineFirst lineSecond freeLabel : Fin 6}
    (hFirstMem : lineFirst ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hSecondMem : lineSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
    (hFirstSecond : lineFirst ≠ lineSecond) (hFirstFree : lineFirst ≠ freeLabel)
    (hSecondFree : lineSecond ≠ freeLabel)
    (hproducer : ∀ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1 →
      (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ unitNormal = 0) →
      ∃ margin : ℝ,
        (∀ probeVec : Fin 3 → ℝ, probeVec ⬝ᵥ unitNormal = 0 → probeVec ≠ 0 →
          margin * (probeVec ⬝ᵥ probeVec)
            ≤ (design.atom lineFirst ⬝ᵥ probeVec) ^ 2
              + (design.atom lineSecond ⬝ᵥ probeVec) ^ 2 - probeVec ⬝ᵥ probeVec)
        ∧ 1 < (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2
        ∧ leverageOf (design.atom freeLabel)
            - (design.atom freeLabel ⬝ᵥ unitNormal) ^ 2
          < ((design.atom freeLabel ⬝ᵥ unitNormal) ^ 2 - 1) * margin) :
    ¬ IsTie design := by
  intro htie
  obtain ⟨unitNormal, hunit, hlineFlat⟩ := oneLine_exists_unitNormal design hpattern
  obtain ⟨margin, hmargin, hheight, hbudget⟩ := hproducer unitNormal hunit hlineFlat
  exact htie.2 ({lineFirst, lineSecond, freeLabel} : Finset (Fin 6))
    (by rw [Finset.card_insert_of_notMem (by simp [hFirstSecond, hFirstFree]),
      Finset.card_insert_of_notMem (by simp [hSecondFree]), Finset.card_singleton])
    (oneLine_posDef_linePair_of_margin design hunit hlineFlat hFirstMem hSecondMem hFirstSecond
      hFirstFree hSecondFree margin hmargin hheight hbudget)

/-! ## 13.  The two-line branch is inhabited in kernel

`Gtz.oneLineSampleDesign` carries a weak dominator that MISSES the line, so it
inhabits the zero-count branch only.  The two-line branch needs a different
witness, and the tree already owns one.

`Gtz.tightLlfDesign` realizes the one-line pattern, is all-heavy, and weakly
dominates at `{0, 1, 3}`, which holds the line labels zero and one together with
the free label three.  Its line normal is the third axis.  So every hypothesis
of sections 2, 10, 11 and 12 outside the margin comparison is satisfiable. -/

/-- The third axis is a unit vector. -/
theorem thirdAxis_unit : (![0, 0, 1] : Fin 3 → ℝ) ⬝ᵥ ![0, 0, 1] = 1 := by
  norm_num [dotProduct, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons]

/-- The tight witness reads the third axis as zero along its line. -/
theorem tightLlf_lineFlat :
    ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      tightLlfDesign.atom lineLabel ⬝ᵥ (![0, 0, 1] : Fin 3 → ℝ) = 0 := by
  intro lineLabel hmem
  fin_cases lineLabel <;>
    first
      | exact absurd hmem (by decide)
      | norm_num [tightLlfDesign, tightLlfAtom, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_two, Matrix.tail_cons]

/-- **THE TWO-LINE BRANCH IS NOT VACUOUS.**  One design carries the pattern,
all-heavy leverages and a card-three WEAK dominator that holds two line labels
and one free label. -/
theorem tightLlf_inhabits_twoLineBranch :
    HasLinePattern tightLlfDesign (lineFamilyPattern [[(0 : Fin 6), 1, 2]])
      ∧ (∀ label : Fin 6, 1 ≤ leverageOf (tightLlfDesign.atom label))
      ∧ Dominates tightLlfDesign {0, 1, 3}
      ∧ ({0, 1, 3} : Finset (Fin 6)) ∩ ({0, 1, 2} : Finset (Fin 6)) = {0, 1} :=
  ⟨tightLlfDesign_hasLinePattern, tightLlfDesign_isHeavy, tightLlfDesign_dominates, by decide⟩

/-- **THE WEAK-DOMINATOR BRIDGE FIRES AT THE TIGHT WITNESS.**  Section 2 is not
vacuous: both line members of the weak dominator are strictly heavy. -/
theorem tightLlf_linePair_strictlyHeavy :
    1 < leverageOf (tightLlfDesign.atom 0) ∧ 1 < leverageOf (tightLlfDesign.atom 1) :=
  oneLine_linePair_strictlyHeavy_of_pattern tightLlfDesign tightLlfDesign_hasLinePattern
    (by decide) (by decide) (by decide) (by decide) (by decide) tightLlfDesign_isHeavy
    (by norm_num [leverageOf, gapPairingOf, tightLlfDesign, tightLlfAtom, dotProduct,
      Fin.sum_univ_three, Matrix.cons_val_two, Matrix.tail_cons])
    (by norm_num [tightLlfDesign, tightLlfAtom, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_two, Matrix.tail_cons])
    tightLlfDesign_dominates

/-- The tight witness clears unit height at its free member, so the height
hypothesis of sections 11 and 12 is satisfiable.  Its third atom reads the line
normal at three. -/
theorem tightLlf_freeHeight :
    1 < (tightLlfDesign.atom 3 ⬝ᵥ (![0, 0, 1] : Fin 3 → ℝ)) ^ 2 := by
  norm_num [tightLlfDesign, tightLlfAtom, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_two, Matrix.tail_cons]

end Gtz
