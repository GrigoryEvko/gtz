import Gtz.Design.OneDeterminantReduction
import Gtz.Design.TieCensusCompletion
import Gtz.Design.StratumEmptinessLedger
import Gtz.Ties.NonUniformLeverageTie
import Gtz.Wave.ChartProgrammeHeavyResidual
import Gtz.Wave.LivePairTieRefuter
import Gtz.Wave.WiringResidualEquivalence
import Gtz.Reduction.BalancedStratumClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The direction-generic roads into `Gtz.DirectionChartIsTieFree`, and the repair

The registry records one direction-generic producer of
`Gtz.DirectionChartIsTieFree`.  There are six.  This file audits every one of
them in kernel, kills the three that cannot fire, and repairs the strongest of
the three corpses into a road that reaches the rank-three hinge with no chart
programme at all.

## Part 1, the corpses

Three generic roads carry a hypothesis that is FALSE at size six.

* `Gtz.directionChartIsTieFree_of_momentPosDef_of_designUpgrade` asks every
  weakly dominated `(6,3)` design for a strictly dominating triple.  That is
  the statement `Gtz.DesignUpgradeSixThree`, and `Gtz.sixSplitDiamondDesign` is
  an exact `(6,3)` tie, so the statement is false.
* `Gtz.directionChartIsTieFree_atlas_of_heavyDesignUpgrade` asks the same of
  designs that carry a weight of one tenth or more.  Every design of six labels
  carries such a weight, so the heavy form is the plain form and dies with it.
* `Gtz.directionChartIsTieFree_of_momentPosDef_of_livePairTie` asks for a
  positive tie leg at every live pair.  `Gtz.not_livePairTieResidual` refutes
  that hypothesis verbatim at size six.

Each refutation transports to the hinge-level sibling in
`Gtz.stressFreeHingeHoldsSixThree_of_designUpgrade` and in
`Gtz.stressFreeHingeHoldsSixThree_of_heavyDesignUpgrade`.

## Part 2, the strict-triple form is false as a generic statement

`Gtz.DirectionChartHasStrictTriple` holds at no rank-one direction family, so
no direction-generic producer of it can exist.  This is the exact calibration
the registry asserts without a witness.  It says nothing about
`Gtz.kFourDirection`, where the statement stays intact.

## Part 3 and Part 4, the repair

The design upgrade fails only because it over-quantifies.  Every `(6,3)` tie the
tree owns carries a PARALLEL PAIR, so the upgrade is refuted only by designs
that are not primitive.  Restricting it to primitive designs removes every known
refuter and keeps all of its consequences:

* the chart road returns, because a design manufactured from a chart point is
  primitive as soon as the direction family is pairwise non-parallel, and
  `Gtz.kFourDirection` is (Part 3)
* the rank-three hinge follows DIRECTLY, with no chart, no covering, no moment
  discharge and no `Gtz.LinearSpaceListIsComplete` input, because the hinge
  concludes `Gtz.HasParallelPair` and a stress-free design is primitive
  (Part 4).

Part 4 is the shortest route to `Gtz.StressFreeHingeHoldsSixThree` in the tree.
It replaces the refuted `Gtz.stressFreeHingeHoldsSixThree_of_designUpgrade`,
which needs the enumeration input as well.

## Part 5, non-refutation

`Gtz.completedSixThreeTieCensus` proves that seven owned `(6,3)` tie families
carry a parallel pair.  It omits `Gtz.nonUniformLeverageTieDesign`, the tree's
only tie fixture with unequal leverages.  Part 5 supplies the missing entry, so
no `(6,3)` tie in the tree refutes the primitive upgrade.
-/

namespace Gtz

open Matrix Finset

/-! ## Part 1: the three dead antecedents -/

/-- The hypothesis of `Gtz.directionChartIsTieFree_of_momentPosDef_of_designUpgrade`
at size six, and of `Gtz.directionChartIsTieFree_atlas_of_designUpgrade`. -/
def DesignUpgradeSixThree : Prop :=
  ∀ design : WeightedDesign 6 3,
    (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef

/-- The hypothesis of `Gtz.directionChartIsTieFree_atlas_of_heavyDesignUpgrade`. -/
def HeavyDesignUpgradeSixThree : Prop :=
  ∀ design : WeightedDesign 6 3,
    (∃ label : Fin 6, 1 / 10 ≤ design.weight label) →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
        ∃ selected : Finset (Fin 6), selected.card = 3
          ∧ (subsetSum design selected - 1).PosDef

/-- The hypothesis of `Gtz.directionChartIsTieFree_of_momentPosDef_of_livePairTie`
at size six. -/
def LivePairTieUpgradeSixThree : Prop :=
  ∀ design : WeightedDesign 6 3,
    (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
        IsLivePair design pivotLabel pairFirst →
          ∃ pairSecond : Fin 6, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
            ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond

/-- **#BOGUS.  THE DESIGN UPGRADE IS FALSE AT SIZE SIX.**  `Gtz.sixSplitDiamondDesign`
is weakly dominated and no card-three subset dominates it strictly, so the
upgrade fails at an exact rational design.  The witness carries a parallel pair
and is not primitive, which is why the repair in Part 3 survives it. -/
theorem not_designUpgradeSixThree : ¬ DesignUpgradeSixThree := by
  intro hupgrade
  obtain ⟨selected, hcard, hposDef⟩ :=
    hupgrade sixSplitDiamondDesign sixSplitDiamondDesign_isTie.1
  exact sixSplitDiamondDesign_isTie.2 selected hcard hposDef

/-- **#BOGUS, and #DUPLICATION of `Gtz.DesignUpgradeSixThree`.**  The tenth floor
buys nothing at six labels: every probability vector on six labels has a entry of
at least one sixth, and one sixth is more than one tenth.  So the heavy upgrade
carries the same content and the same refuter. -/
theorem not_heavyDesignUpgradeSixThree : ¬ HeavyDesignUpgradeSixThree := by
  intro hupgrade
  refine not_designUpgradeSixThree fun design hweak => ?_
  by_cases hheavy : ∃ label : Fin 6, 1 / 10 ≤ design.weight label
  · exact hupgrade design hheavy hweak
  · exact absurd (fun label => lt_of_not_ge fun hge => hheavy ⟨label, hge⟩)
      (not_forall_weight_lt_tenth design)

/-- The heavy upgrade and the plain upgrade are the same statement at six
labels.  This is the #DUPLICATION, stated as an equivalence. -/
theorem heavyDesignUpgradeSixThree_iff_designUpgradeSixThree :
    HeavyDesignUpgradeSixThree ↔ DesignUpgradeSixThree := by
  constructor
  · intro hupgrade design hweak
    by_cases hheavy : ∃ label : Fin 6, 1 / 10 ≤ design.weight label
    · exact hupgrade design hheavy hweak
    · exact absurd (fun label => lt_of_not_ge fun hge => hheavy ⟨label, hge⟩)
        (not_forall_weight_lt_tenth design)
  · exact fun hupgrade design _ hweak => hupgrade design hweak

/-- **#BOGUS.  THE LIVE-PAIR TIE UPGRADE IS FALSE AT SIZE SIX.**  This is
`Gtz.not_livePairTieResidual` (Gtz/Wave/LivePairTieRefuter.lean:183), which
refutes the hypothesis verbatim at `Gtz.livePairTieRefuterDesign`. -/
theorem not_livePairTieUpgradeSixThree : ¬ LivePairTieUpgradeSixThree :=
  not_livePairTieResidual

/-- **THE THREE GENERIC DESIGN-SIDE ROADS ARE ALL CORPSES AT SIZE SIX.**  No
proof of any of these three hypotheses exists, so none of the chart producers
that consume them can ever fire. -/
theorem genericChartDesignRoads_haveDeadAntecedents :
    ¬ DesignUpgradeSixThree ∧ ¬ HeavyDesignUpgradeSixThree
      ∧ ¬ LivePairTieUpgradeSixThree :=
  ⟨not_designUpgradeSixThree, not_heavyDesignUpgradeSixThree,
    not_livePairTieUpgradeSixThree⟩

/-! ## Part 2: the strict-triple form is false at a rank-one direction family -/

/-- A chart point with unit masses and uniform weights.  Six labels, so each
weight is one sixth. -/
noncomputable def flatChartPoint : DirectionChartPoint 6 where
  mass := fun _ => 1
  weight := fun _ => 1 / 6
  mass_pos := fun _ => by norm_num
  weight_pos := fun _ => by norm_num
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num

/-- A rank-one direction family: every label carries the first coordinate axis.
This is the degenerate, non-spanning family the registry names. -/
def flatDirection : Fin 6 → (Fin 3 → ℝ) := fun _ => ![1, 0, 0]

/-- Every flat direction is orthogonal to the second coordinate axis. -/
theorem flatDirection_dotProduct_probe (label : Fin 6) :
    flatDirection label ⬝ᵥ ![0, 1, 0] = 0 := by
  simp [flatDirection, dotProduct, Fin.sum_univ_three]

/-- The second coordinate axis is not the zero probe. -/
theorem probe_ne_zero : (![0, 1, 0] : Fin 3 → ℝ) ≠ 0 := by
  intro hzero
  have hentry := congrFun hzero 1
  norm_num at hentry

/-- **THE GENERIC STRICT-TRIPLE FORM IS KERNEL-FALSE.**  At a rank-one direction
family every chart gap annihilates the probe orthogonal to the common axis, so
no card-three selection is positive definite at any chart point.  This is the
exact refutation the registry asserts without a witness.

It says NOTHING about `Gtz.kFourDirection`, whose six directions span.  What it
proves is that no DIRECTION-GENERIC producer of
`Gtz.DirectionChartHasStrictTriple` can exist, so every producer of the strict
form must name its direction family. -/
theorem not_directionChartHasStrictTriple_flatDirection :
    ¬ DirectionChartHasStrictTriple flatDirection := by
  intro hstrict
  obtain ⟨selected, -, hposDef⟩ := hstrict flatChartPoint
  have hvalue : (![0, 1, 0] : Fin 3 → ℝ) ⬝ᵥ (directionChartGap flatDirection
      flatChartPoint.mass flatChartPoint.weight selected *ᵥ ![0, 1, 0]) = 0 := by
    rw [dotProduct_directionChartGap_mulVec flatDirection flatChartPoint.mass
      flatChartPoint.weight (fun label => (flatChartPoint.weight_pos label).ne') selected]
    simp [flatDirection, dotProduct, Fin.sum_univ_three]
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 probe_ne_zero
  rw [star_trivial, hvalue] at hpos
  exact lt_irrefl 0 hpos

/-- **NO DIRECTION-GENERIC PRODUCER OF THE STRICT FORM CAN EXIST.**  The
statement fails at one explicit family, so it is not a theorem schema over
direction families. -/
theorem not_forall_directionChartHasStrictTriple :
    ¬ ∀ direction : Fin 6 → (Fin 3 → ℝ), DirectionChartHasStrictTriple direction :=
  fun hall => not_directionChartHasStrictTriple_flatDirection (hall flatDirection)

/-! ## Part 3: the repair on the chart side -/

/-- A direction family with no two members proportional.  This is
`Gtz.IsPrimitiveDesign` read on a family of fixed vectors. -/
def DirectionFamilyIsPrimitive {size : ℕ} (direction : Fin size → (Fin 3 → ℝ)) : Prop :=
  ∀ keptLabel dropLabel : Fin size, keptLabel ≠ dropLabel →
    ∀ ratio : ℝ, direction dropLabel ≠ ratio • direction keptLabel

/-- The six K4 edge directions in list form. -/
theorem kFourDirection_eq (label : Fin 6) :
    kFourDirection label
      = ![![1, -1, 0], ![1, 0, -1], ![0, 1, -1], ![1, 0, 0], ![0, 1, 0], ![0, 0, 1]]
          label := by
  fin_cases label <;> rfl

/-- **THE K4 CHART FAMILY IS PRIMITIVE.**  Its six edge vectors are pairwise
non-proportional: each pair is separated by one coordinate. -/
theorem kFourDirection_isPrimitive : DirectionFamilyIsPrimitive kFourDirection := by
  intro keptLabel dropLabel hdistinct ratio hparallel
  rw [kFourDirection_eq, kFourDirection_eq] at hparallel
  have hzeroth := congrFun hparallel 0
  have hfirst := congrFun hparallel 1
  have hsecond := congrFun hparallel 2
  clear hparallel
  fin_cases keptLabel <;> fin_cases dropLabel
  all_goals (try exact absurd rfl hdistinct)
  all_goals (try norm_num [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    at hzeroth)
  all_goals (try norm_num [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    at hfirst)
  all_goals (try norm_num [Pi.smul_apply, smul_eq_mul, Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons]
    at hsecond)
  all_goals linarith

/-- **THE MANUFACTURED CHART DESIGN IS PRIMITIVE.**  This strengthens
`Gtz.exists_design_of_chartPoint`: when the direction family is pairwise
non-proportional, the design that carries the chart point is primitive.  The
whitener is invertible and every chart scale is strictly positive, so
proportionality of two atoms would descend to proportionality of two
directions.

The extra conclusion is what repairs the design-upgrade road: the upgrade is
refuted only by designs with a parallel pair, and no design manufactured from a
primitive chart family has one. -/
theorem exists_primitiveDesign_of_chartPoint {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ))
    (hfamily : DirectionFamilyIsPrimitive direction)
    (point : DirectionChartPoint size)
    (hmoment : (∑ label, point.mass label • atomMatrix (direction label)).PosDef) :
    ∃ design : WeightedDesign size 3, IsPrimitiveDesign design ∧
      ∀ selected : Finset (Fin size),
        ((subsetSum design selected - 1).PosDef
            ↔ (directionChartGap direction point.mass point.weight selected).PosDef)
          ∧ (Dominates design selected
            ↔ (directionChartGap direction point.mass point.weight selected).PosSemidef) := by
  classical
  have hmassNonneg : ∀ label, 0 ≤ point.mass label := fun label => (point.mass_pos label).le
  have hframe : frameOperatorOfAtoms (chartAtomFamily direction point.mass point.weight)
      point.weight = ∑ label, point.mass label • atomMatrix (direction label) :=
    frameOperatorOfAtoms_chartAtomFamily direction point.mass point.weight hmassNonneg
      point.weight_pos
  obtain ⟨congruence, hunit, hcongruence⟩ := exists_congruence_to_one (hframe ▸ hmoment)
  have hwhiten : congruenceᵀ * (∑ label, point.weight label
      • atomMatrix (chartAtomFamily direction point.mass point.weight label))
      * congruence = 1 := hcongruence
  have hunitTranspose : IsUnit (congruenceᵀ).det := by
    rw [Matrix.det_transpose]; exact hunit
  have hinjective : ∀ leftVec rightVec : Fin 3 → ℝ,
      congruenceᵀ *ᵥ leftVec = congruenceᵀ *ᵥ rightVec → leftVec = rightVec := by
    intro leftVec rightVec himage
    have hpull : (congruenceᵀ)⁻¹ *ᵥ (congruenceᵀ *ᵥ leftVec)
        = (congruenceᵀ)⁻¹ *ᵥ (congruenceᵀ *ᵥ rightVec) := by rw [himage]
    rwa [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunitTranspose, Matrix.one_mulVec,
      Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunitTranspose,
      Matrix.one_mulVec] at hpull
  refine ⟨whitenedFamilyDesign (chartAtomFamily direction point.mass point.weight) point.weight
      point.weight_pos point.weight_sum_one congruence hwhiten, ?_, fun selected => ?_⟩
  · intro keptLabel dropLabel ratio hdistinct hparallel
    have hdropScalePos :
        0 < Real.sqrt (point.mass dropLabel / point.weight dropLabel) :=
      Real.sqrt_pos.mpr (div_pos (point.mass_pos dropLabel) (point.weight_pos dropLabel))
    have himage : congruenceᵀ *ᵥ (chartAtomFamily direction point.mass point.weight dropLabel)
        = congruenceᵀ *ᵥ (ratio • chartAtomFamily direction point.mass point.weight keptLabel) := by
      rw [Matrix.mulVec_smul]
      exact hparallel
    have hraw : chartAtomFamily direction point.mass point.weight dropLabel
        = ratio • chartAtomFamily direction point.mass point.weight keptLabel :=
      hinjective _ _ himage
    rw [chartAtomFamily, chartAtomFamily, smul_smul] at hraw
    refine hfamily keptLabel dropLabel hdistinct
      ((Real.sqrt (point.mass dropLabel / point.weight dropLabel))⁻¹
        * (ratio * Real.sqrt (point.mass keptLabel / point.weight keptLabel))) ?_
    rw [← smul_smul, ← hraw, smul_smul, inv_mul_cancel₀ hdropScalePos.ne', one_smul]
  · have hmomentEq : subsetSum (whitenedFamilyDesign
          (chartAtomFamily direction point.mass point.weight) point.weight point.weight_pos
          point.weight_sum_one congruence hwhiten) selected
        = congruenceᵀ * subsetSumOfAtoms (chartAtomFamily direction point.mass point.weight)
            selected * congruence := by
      rw [whitenedDesign_subsetSum_eq, sum_atomMatrix_conj, subsetSumOfAtoms]
    have hgapEq : subsetSum (whitenedFamilyDesign
          (chartAtomFamily direction point.mass point.weight) point.weight point.weight_pos
          point.weight_sum_one congruence hwhiten) selected - 1
        = congruenceᵀ * directionChartGap direction point.mass point.weight selected
            * congruence := by
      rw [hmomentEq, ← hcongruence,
        directionChartGap_eq_frameGap direction point.mass point.weight hmassNonneg
          point.weight_pos selected,
        frameOperatorOfAtoms, Matrix.mul_assoc congruenceᵀ, Matrix.mul_assoc congruenceᵀ,
        ← Matrix.mul_sub, ← Matrix.sub_mul, ← Matrix.mul_assoc]
    have hsymmetric : (directionChartGap direction point.mass point.weight selected)ᵀ
        = directionChartGap direction point.mass point.weight selected :=
      directionChartGap_transpose direction point.mass point.weight selected
    refine ⟨?_, ?_⟩
    · rw [hgapEq]
      exact (posDef_congr_right hsymmetric hunit).symm
    · show (subsetSum _ selected - 1).PosSemidef ↔ _
      rw [hgapEq]
      exact (posSemidef_congr_right hsymmetric hunit).symm

/-- The design-side upgrade, restricted to PRIMITIVE designs.  This is the
repaired form of `Gtz.DesignUpgradeSixThree`.  Its refuters must be primitive,
and `Gtz.completedSixThreeTieCensus` together with Part 5 shows that no `(6,3)`
tie the tree owns is. -/
def PrimitiveUpgradeSixThree : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
    (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin 6), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef

/-- The same statement at an arbitrary size, for the generic chart road. -/
def PrimitiveUpgradeAtSize (size : ℕ) : Prop :=
  ∀ design : WeightedDesign size 3, IsPrimitiveDesign design →
    (∃ dominator : Finset (Fin size), dominator.card = 3 ∧ Dominates design dominator) →
      ∃ selected : Finset (Fin size), selected.card = 3
        ∧ (subsetSum design selected - 1).PosDef

/-- The refuted upgrade implies the repaired one, because it quantifies over
more designs. -/
theorem primitiveUpgradeSixThree_of_designUpgradeSixThree
    (hupgrade : DesignUpgradeSixThree) : PrimitiveUpgradeSixThree :=
  fun design _hprimitive hweak => hupgrade design hweak

/-- **THE REPAIR IS A WEAKENING, NOT A SIDEWAYS MOVE.**  The dead hypothesis
implies the repaired one, and the dead hypothesis is dead.  So the repair
removes exactly the designs that carry the refutation and asks for nothing
new. -/
theorem primitiveUpgrade_isWeakerThan_refutedDesignUpgrade :
    (DesignUpgradeSixThree → PrimitiveUpgradeSixThree) ∧ ¬ DesignUpgradeSixThree :=
  ⟨primitiveUpgradeSixThree_of_designUpgradeSixThree, not_designUpgradeSixThree⟩

/-- **THE REPAIRED GENERIC CHART ROAD.**  A chart whose moment matrix is positive
definite and whose direction family is pairwise non-proportional is tie-free as
soon as the PRIMITIVE design upgrade holds.

This is `Gtz.directionChartIsTieFree_of_momentPosDef_of_designUpgrade` with the
refuted quantifier repaired.  The chart supplies the primitivity itself, so the
repair costs the consumer nothing. -/
theorem directionChartIsTieFree_of_momentPosDef_of_primitiveUpgrade {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ))
    (hfamily : DirectionFamilyIsPrimitive direction)
    (hmoment : ∀ point : DirectionChartPoint size,
      (∑ label, point.mass label • atomMatrix (direction label)).PosDef)
    (hupgrade : PrimitiveUpgradeAtSize size) :
    DirectionChartIsTieFree direction := by
  intro point hweak
  obtain ⟨design, hprimitive, htransfer⟩ :=
    exists_primitiveDesign_of_chartPoint direction hfamily point (hmoment point)
  obtain ⟨dominator, hcard, hdominates⟩ := hweak
  obtain ⟨selected, hcardSelected, hposDef⟩ :=
    hupgrade design hprimitive ⟨dominator, hcard, (htransfer dominator).2.mpr hdominates⟩
  exact ⟨selected, hcardSelected, (htransfer selected).1.mp hposDef⟩

/-- **THE K4 CHART OBLIGATION FROM THE PRIMITIVE UPGRADE.**  The moment
hypothesis is already discharged by `Gtz.posDef_massMoment_kFourDirection`, and
the K4 edge family is primitive, so the whole K4 chart closes on the repaired
design statement alone. -/
theorem directionChartIsTieFree_kFour_of_primitiveUpgrade
    (hupgrade : PrimitiveUpgradeSixThree) :
    DirectionChartIsTieFree kFourDirection :=
  directionChartIsTieFree_of_momentPosDef_of_primitiveUpgrade kFourDirection
    kFourDirection_isPrimitive posDef_massMoment_kFourDirection hupgrade

/-- **THE M(K4) CLASS STATEMENT FROM THE PRIMITIVE UPGRADE.**  The covering half
is the unconditional `Gtz.directionChartCoversPrimitiveStratum_kFourDirection`,
so entry `#5` of `Gtz.stressFreeResidualFamiliesSix` closes here. -/
theorem stressFreeStratumIsTieFree_graphicKFour_of_primitiveUpgrade
    (hupgrade : PrimitiveUpgradeSixThree) :
    StressFreeStratumIsTieFree
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]]) :=
  stressFreeStratumIsTieFree_graphicKFour_of_chart
    (directionChartIsTieFree_kFour_of_primitiveUpgrade hupgrade)

/-- The three-lines chart family also has a positive definite moment matrix at
every slide, so the repaired road reaches it as soon as the family is
primitive. -/
theorem directionChartIsTieFree_threeLines_of_primitiveUpgrade (slide : ℝ)
    (hfamily : DirectionFamilyIsPrimitive (threeLinesDirection slide))
    (hupgrade : PrimitiveUpgradeSixThree) :
    DirectionChartIsTieFree (threeLinesDirection slide) :=
  directionChartIsTieFree_of_momentPosDef_of_primitiveUpgrade (threeLinesDirection slide)
    hfamily (posDef_massMoment_threeLinesDirection slide) hupgrade

/-! ## Part 4: the rank-three hinge, with no chart at all -/

/-- The design-side upgrade restricted to STRESS-FREE designs. -/
def StressFreeUpgradeSixThree : Prop :=
  ∀ design : WeightedDesign 6 3,
    (∀ stress : Fin 6 → ℝ,
      (∑ label, stress label • atomMatrix (design.atom label)) = 0 → stress = 0) →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
        ∃ selected : Finset (Fin 6), selected.card = 3
          ∧ (subsetSum design selected - 1).PosDef

/-- **THE RANK-THREE HINGE FROM THE PRIMITIVE UPGRADE, DIRECTLY.**  No chart, no
covering, no moment discharge and no enumeration input.

The hinge CONCLUDES `Gtz.HasParallelPair`, and a stress-free design is primitive
(`Gtz.isPrimitiveDesign_of_stressFree`), so the primitive upgrade answers the
hinge at exactly the designs the hinge quantifies over.  This is the shortest
route to `Gtz.StressFreeHingeHoldsSixThree` in the tree, and it replaces the
refuted `Gtz.stressFreeHingeHoldsSixThree_of_designUpgrade`, which needs
`Gtz.LinearSpaceListIsComplete` as well. -/
theorem stressFreeHingeHoldsSixThree_of_primitiveUpgrade
    (hupgrade : PrimitiveUpgradeSixThree) : StressFreeHingeHoldsSixThree := by
  intro design hstressFree htie
  obtain ⟨selected, hcard, hposDef⟩ :=
    hupgrade design (isPrimitiveDesign_of_stressFree design hstressFree) htie.1
  exact absurd hposDef (htie.2 selected hcard)

/-- The primitive upgrade is at least as strong as the stress-free upgrade,
because a stress-free design is primitive. -/
theorem stressFreeUpgradeSixThree_of_primitiveUpgrade
    (hupgrade : PrimitiveUpgradeSixThree) : StressFreeUpgradeSixThree :=
  fun design hstressFree hweak =>
    hupgrade design (isPrimitiveDesign_of_stressFree design hstressFree) hweak

/-- **THE STRESS-FREE UPGRADE IS THE HINGE.**  This is an EQUIVALENCE, and it
records no progress by itself.  It is the honest floor of the repair: the
primitive upgrade is a strengthening of this statement, and this statement is
the hinge restated. -/
theorem stressFreeHingeHoldsSixThree_iff_stressFreeUpgrade :
    StressFreeUpgradeSixThree ↔ StressFreeHingeHoldsSixThree := by
  constructor
  · intro hupgrade design hstressFree htie
    obtain ⟨selected, hcard, hposDef⟩ := hupgrade design hstressFree htie.1
    exact absurd hposDef (htie.2 selected hcard)
  · intro hhinge design hstressFree hweak
    by_contra hnoStrict
    have htie : IsTie design :=
      ⟨hweak, fun selected hcard hposDef => hnoStrict ⟨selected, hcard, hposDef⟩⟩
    exact (isPrimitiveDesign_iff_not_hasParallelPair design).mp
      (isPrimitiveDesign_of_stressFree design hstressFree)
      (hhinge design hstressFree htie)

/-- **THE WHOLE FIVE-CLASS RESIDUAL FROM THE PRIMITIVE UPGRADE.**  The hinge
implies every class statement, so the primitive upgrade closes the residual list
in one step. -/
theorem stressFreeResidualFamiliesSix_tieFree_of_primitiveUpgrade
    (hupgrade : PrimitiveUpgradeSixThree) :
    ∀ lines ∈ stressFreeResidualFamiliesSix,
      StressFreeStratumIsTieFree (lineFamilyPattern lines) :=
  fun lines _hmem =>
    stressFreeStratumIsTieFree_of_stressFreeHinge
      (stressFreeHingeHoldsSixThree_of_primitiveUpgrade hupgrade) (lineFamilyPattern lines)

/-! ## Part 5: the whole of rank three from one design-level sentence -/

/-- The tie-emptiness reading of the primitive upgrade: no primitive `(6,3)`
design is a tie.  This is the shortest true statement the campaign can aim at,
and Part 6 shows that nothing in the tree refutes it. -/
def NoPrimitiveTieSixThree : Prop :=
  ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design → ¬ IsTie design

/-- **THE PRIMITIVE UPGRADE IS TIE-EMPTINESS.**  An equivalence, and a
reformulation only.  It is the reading that makes the target one sentence:
"no primitive `(6,3)` design is a tie". -/
theorem primitiveUpgradeSixThree_iff_noPrimitiveTie :
    PrimitiveUpgradeSixThree ↔ NoPrimitiveTieSixThree := by
  constructor
  · intro hupgrade design hprimitive htie
    obtain ⟨selected, hcard, hposDef⟩ := hupgrade design hprimitive htie.1
    exact htie.2 selected hcard hposDef
  · intro hno design hprimitive hweak
    by_contra hnoStrict
    exact hno design hprimitive
      ⟨hweak, fun selected hcard hposDef => hnoStrict ⟨selected, hcard, hposDef⟩⟩

/-- **THE WEIGHTED THEOREM AT `(6,3)` FROM THE PRIMITIVE UPGRADE.** -/
theorem gtzWeighted_six_three_of_primitiveUpgrade
    (hupgrade : PrimitiveUpgradeSixThree) : GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_stressFreeHinge
    (stressFreeHingeHoldsSixThree_of_primitiveUpgrade hupgrade)

/-- **THE STRESS RESIDUAL AT SIX LABELS FROM THE PRIMITIVE UPGRADE.** -/
theorem noStressResidual_six_of_primitiveUpgrade
    (hupgrade : PrimitiveUpgradeSixThree) : NoStressResidual 6 :=
  noStressResidual_six_of_stressFreeHinge
    (stressFreeHingeHoldsSixThree_of_primitiveUpgrade hupgrade)

/-- **THE WHOLE OF RANK THREE, AT EVERY SIZE, FROM ONE DESIGN-LEVEL SENTENCE.**
The original theorem at rank three and every positive size follows from the
statement that no primitive `(6,3)` design is a tie.

No chart, no covering, no moment discharge, no line-pattern enumeration and no
registry axiom occur in the hypothesis.  It is eleven positive reals and six
vectors of a single design, with one word of matroid input: no two atoms are
proportional. -/
theorem forall_gtzOriginal_rank_three_of_primitiveUpgrade
    (hupgrade : PrimitiveUpgradeSixThree) :
    ∀ sizeParam : ℕ, 0 < sizeParam → GtzOriginal sizeParam 3 :=
  forall_gtzOriginal_rank_three_of_stressFreeHingeAlone
    (stressFreeHingeHoldsSixThree_of_primitiveUpgrade hupgrade)

/-- The same capstone from the tie-emptiness reading, which is the form a prover
should attack. -/
theorem forall_gtzOriginal_rank_three_of_noPrimitiveTie
    (hno : NoPrimitiveTieSixThree) :
    ∀ sizeParam : ℕ, 0 < sizeParam → GtzOriginal sizeParam 3 :=
  forall_gtzOriginal_rank_three_of_primitiveUpgrade
    (primitiveUpgradeSixThree_iff_noPrimitiveTie.mpr hno)

/-! ## Part 6: no owned `(6,3)` tie refutes the primitive upgrade -/

/-- The light atoms four and three of `Gtz.nonUniformLeverageTieDesign` are
literally equal, so the fixture carries a parallel pair with ratio one. -/
theorem nonUniformLeverageTieDesign_hasParallelPair :
    HasParallelPair nonUniformLeverageTieDesign :=
  ⟨3, 4, 1, by decide, by
    rw [one_smul]
    rfl⟩

/-- `Gtz.nonUniformLeverageTieDesign` is not primitive, so it does not refute the
primitive upgrade.  It is the one `(6,3)` tie fixture that
`Gtz.completedSixThreeTieCensus` omits, and the tree's only tie with unequal
leverages. -/
theorem not_isPrimitiveDesign_nonUniformLeverageTieDesign :
    ¬ IsPrimitiveDesign nonUniformLeverageTieDesign := by
  intro hprimitive
  exact (isPrimitiveDesign_iff_not_hasParallelPair nonUniformLeverageTieDesign).mp
    hprimitive nonUniformLeverageTieDesign_hasParallelPair

/-- **THE COMPLETED CENSUS, WITH THE OMITTED FIXTURE.**  Every `(6,3)` tie the
tree owns carries a parallel pair.  The first conjunct is the shipped census and
the second is the fixture it omits. -/
theorem everyOwnedSixThreeTie_hasParallelPair :
    (HasParallelPair uniformTieDesign
      ∧ HasParallelPair (bundledCycleDesign bundlingSixThreeHeavy (by norm_num))
      ∧ HasParallelPair (bundledCycleDesign bundlingSixThreePaired (by norm_num))
      ∧ HasParallelPair chartSplitSixDesign
      ∧ HasParallelPair sixSplitDiamondDesign
      ∧ HasParallelPair (paddedTetraDesign 2)
      ∧ ∀ (splitA splitB : ℝ) (hAPos : 0 < splitA) (hALt : splitA < 1/4)
          (hBPos : 0 < splitB) (hBLt : splitB < 1/4),
            HasParallelPair (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt))
      ∧ HasParallelPair nonUniformLeverageTieDesign :=
  ⟨completedSixThreeTieCensus, nonUniformLeverageTieDesign_hasParallelPair⟩

/-- **NO OWNED `(6,3)` TIE IS PRIMITIVE.**  Both refuters of
`Gtz.DesignUpgradeSixThree` that the tree names carry a parallel pair, so
neither touches `Gtz.PrimitiveUpgradeSixThree`.  This is the non-refutation
record for the repair: the statement Part 4 consumes is refuted by nothing in
the tree. -/
theorem ownedSixThreeTies_areNotPrimitive :
    ¬ IsPrimitiveDesign sixSplitDiamondDesign
      ∧ ¬ IsPrimitiveDesign uniformTieDesign
      ∧ ¬ IsPrimitiveDesign nonUniformLeverageTieDesign :=
  ⟨fun hprimitive =>
      (isPrimitiveDesign_iff_not_hasParallelPair sixSplitDiamondDesign).mp hprimitive
        sixSplitDiamondDesign_hasParallelPair,
    fun hprimitive =>
      (isPrimitiveDesign_iff_not_hasParallelPair uniformTieDesign).mp hprimitive
        uniformTieDesign_hasParallelPair,
    not_isPrimitiveDesign_nonUniformLeverageTieDesign⟩

end Gtz
