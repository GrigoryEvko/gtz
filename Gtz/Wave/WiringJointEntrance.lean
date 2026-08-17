/-
# The two joint entrances, priced: the offset door IS the cell, the pair door is empty

Two Props reach all five on-path registry obligations at once, and neither had a
producer or a refuter.  This module settles both, in opposite directions.

## 1.  The offset door is the `(6,3)` hinge, exactly

`Gtz.OffsetDominatesSomewhere` (Gtz/Wave/OffsetUpperBound.lean:260) asks three
polynomial inequalities at one pivot of one design.  The tree carried the forward
arrow only.  Section 3 lands the backward arrow and closes the loop:

    Gtz.offsetDominatesSomewhere_iff_hingeHoldsAtSize_six_three

The backward step needs the weak dominator that the hinge itself supplies, the
order embedding of a card-three subset, and the landed block dictionary.  Section
4 carries the same equivalence to `Gtz.AllFiveOnPath`, so the five registry
obligations of `Skeleton/Obligations.lean` and three scalar inequalities are ONE
statement.  Nothing between them is cheaper than anything else.

**TRAP ONE, ANSWERED FOR THE OFFSET DOOR.**  The answer is yes.  The Prop is
equivalent to `Gtz.HingeHoldsAtSize 6 3`, and the equivalence is a kernel fact of
this module, not an estimate.  Read it beside
`Gtz.gtzWeightedAll_three_of_consolidatedStrictTripleDesign`
(Gtz/Wave/WiringDoorLedger.lean:96), the level-one law: a selector door of the
shape `∀ design, IsPrimitiveDesign design → ∃ …` is at least the whole rank-three
conjecture.  For this door it is not merely at least.  It is equal.

## 2.  The two-local pair door is EMPTY

`Gtz.PairPartialGapSomewhere` (Gtz/Wave/ThirdLabelSelection.lean:426) reads two
labels.  Section 5 closes `Gtz.pairPartialGap` in a form the corpus did not have:

    pairPartialGap D a b
      = -e_a * ( e_b * w_a * (1 - P a a - e_a)
               + e_a * w_b * (1 - P b b - e_b)
               + 2 * (P a b) ^ 2 * (w_a + w_b) )

with `e_a` the excess at `a` and `w_a` the weight there.  Every quartic term
cancels.  The corpus carried the expression only as a sum of two moments.

The sign follows at once.  A pivot of positive excess and a partner of positive
pair minor make the whole bracket nonnegative as soon as
`P a a + e_a <= 1` and `P b b + e_b <= 1`, so the partial gap is nonpositive
there.  The door therefore FORCES a label with `2 * P l l - w_l > 1`.

The `K4` graphic point carries `P l l = 1/2` and `w_l = 1/6` at every label, so
its every label reads `5/6`.  Section 6 refutes the door outright:

    Gtz.not_pairPartialGapSomewhere

**TRAP TWO, ANSWERED FOR THE PAIR DOOR.**  The antecedent is unsatisfiable.
`Gtz.allFiveOnPath_of_pairPartialGap` and
`Gtz.consolidatedStrictTriple_of_pairPartialGap` cannot open.  The exact value at
the `K4` point is `-1/162 - (2/9) * (P a b) ^ 2`, negative at all thirty ordered
pairs, and the module records it.

## 3.  The third-inequality door is empty as well

`Gtz.allFiveOnPath_of_thirdInequality` (Gtz/Wave/ThirdLabelSelection.lean:186) is
the narrowest lane the tree carries.  Its module tells the reader that the
antecedent is free of the vacuity defect.  Section 6b refutes that antecedent.  The door quantifies
over EVERY qualified pivot pair, and the three matching pairs of the `K4` graphic
point qualify and fail at all four of their third labels.  The squared offset
reads `9/1296` against a minor product of `7/1296`.

## 4.  The doors split at the SAME design

Section 7 fires the offset door at the same `K4` graphic design that kills the
other two, on the pairwise meeting edges `0`, `2` and `4`.  So the gap between the
entrances is not a matter of degree.  One is the conjecture and two are false, and
one design witnesses all three facts.

## 5.  A universal total behind the two refutations

Section 5b reads the load `2 * P l l - w l` of a label.  The six diagonals total
the rank and the six weights total one, so the six loads total `5` at EVERY design
of the cell.  The two-local door asks one label to pass `1` while six of them
share `5`.  The flat locus, where every diagonal reads one half, carries load
`1 - w l` at every label and kills the door outright.

## 6.  What this module also lands

`Gtz.sq_projectionOfDesign_of_parallel` reads a parallel pair as equality in
Cauchy-Schwarz on the projection form, and
`Gtz.isPrimitiveDesign_of_sq_projection_lt` turns strictness into primitivity.
That criterion needs no atom coordinates.  It replaces a thirty-six case atom
computation by two scalar bounds.
-/
import Gtz.Wave.ThirdLabelSelection
import Gtz.Wave.ThresholdCellDominance
import Gtz.Wave.WiringAllFiveOnPath
import Gtz.Wave.WiringDoorLedger
import Gtz.Reduction.RankThreeFromStressFreeResidual

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {size rank : ℕ}

/-! ### 1.  The two doors, wired to the capstone

`Gtz.AllFiveOnPath` (Gtz/Wave/WiringAllFiveOnPath.lean:70) names the five-Prop
conjunction that the two doors conclude.  The doors spell the conjunction out.
The name is a `def` for exactly that conjunction, so the composition needs no
adapter. -/

/-- The offset criterion delivers the named five-Prop conjunction. -/
theorem allFiveOnPath_of_offsetDominates (hoffset : OffsetDominatesSomewhere) :
    AllFiveOnPath :=
  allFiveOnPath_of_offsetDominatesSomewhere hoffset

/-- The two-local criterion delivers the named five-Prop conjunction. -/
theorem allFiveOnPath_of_pairPartialGapSomewhere (hpair : PairPartialGapSomewhere) :
    AllFiveOnPath :=
  allFiveOnPath_of_pairPartialGap hpair

/-- **RANK-THREE GTZ AT EVERY SIZE, FROM THE OFFSET CRITERION.**  Three polynomial
inequalities at one pivot of one design reach the capstone. -/
theorem gtzWeightedAll_three_of_offsetDominatesSomewhere
    (hoffset : OffsetDominatesSomewhere) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_allFiveOnPath (allFiveOnPath_of_offsetDominates hoffset)

/-- **RANK-THREE GTZ AT EVERY SIZE, FROM THE TWO-LOCAL CRITERION.**  Section 6
refutes the hypothesis, so this door cannot open.  It stays here as the ledger
entry that names the door and its price together. -/
theorem gtzWeightedAll_three_of_pairPartialGap (hpair : PairPartialGapSomewhere) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_allFiveOnPath (allFiveOnPath_of_pairPartialGapSomewhere hpair)

/-! ### 2.  A primitivity criterion in projection coordinates

`Gtz.IsPrimitiveDesign` reads the atoms.  The projection form reads the same
information, because a parallel pair is exactly the equality case of
Cauchy-Schwarz on that form.  Both theorems below hold at every size and rank. -/

/-- **A PARALLEL PAIR IS EQUALITY IN CAUCHY-SCHWARZ ON THE PROJECTION FORM.**  The
weights and the common scalar all cancel, so no positivity and no rank enter. -/
theorem sq_projectionOfDesign_of_parallel (design : WeightedDesign size rank)
    {keptLabel dropLabel : Fin size} {ratio : ℝ}
    (hparallel : design.atom dropLabel = ratio • design.atom keptLabel) :
    projectionOfDesign design keptLabel dropLabel ^ 2
      = projectionOfDesign design keptLabel keptLabel
        * projectionOfDesign design dropLabel dropLabel := by
  have hcross : design.atom keptLabel ⬝ᵥ design.atom dropLabel
      = ratio * (design.atom keptLabel ⬝ᵥ design.atom keptLabel) := by
    rw [hparallel]
    simp only [dotProduct_smul, smul_eq_mul]
  have hself : design.atom dropLabel ⬝ᵥ design.atom dropLabel
      = ratio ^ 2 * (design.atom keptLabel ⬝ᵥ design.atom keptLabel) := by
    rw [hparallel]
    simp only [smul_dotProduct, dotProduct_smul, smul_eq_mul]
    ring
  rw [projectionOfDesign_apply, projectionOfDesign_apply, projectionOfDesign_apply,
    hcross, hself]
  ring

/-- **STRICT CAUCHY-SCHWARZ IS PRIMITIVITY.**  A design whose every off-diagonal
projection entry falls strictly below the geometric mean of its two diagonals
carries no parallel pair.  The criterion reads only the projection form. -/
theorem isPrimitiveDesign_of_sq_projection_lt (design : WeightedDesign size rank)
    (hstrict : ∀ first second : Fin size, first ≠ second →
      projectionOfDesign design first second ^ 2
        < projectionOfDesign design first first * projectionOfDesign design second second) :
    IsPrimitiveDesign design := fun keptLabel dropLabel _ratio hdistinct hparallel =>
  absurd (sq_projectionOfDesign_of_parallel design hparallel)
    (ne_of_lt (hstrict keptLabel dropLabel hdistinct))

/-! ### 3.  THE OFFSET DOOR IS THE HINGE

The forward arrow is landed.  The backward arrow needs three landed steps that
nobody composed: the weak dominator the hinge supplies, the order embedding of a
card-three subset, and the block dictionary
`Gtz.posDef_blockGapAt_iff_subsetSum`. -/

/-- **THE HINGE PRODUCES A STRICT TRIPLE AT EVERY PRIMITIVE `(6,3)` DESIGN.**  The
hinge gives rank three at every size, so the design owns a weak dominator.  A
primitive design with a weak dominator and no strict one is a tie, and the hinge
hands a tie a parallel pair, which primitivity forbids. -/
theorem exists_posDef_subsetSum_of_hinge (hhinge : HingeHoldsAtSize 6 3)
    (design : WeightedDesign 6 3) (hprimitive : IsPrimitiveDesign design) :
    ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef := by
  by_cases hsome : ∃ selected : Finset (Fin 6), selected.card = 3
      ∧ (subsetSum design selected - 1).PosDef
  · exact hsome
  · exfalso
    have hnoStrict : ∀ selected : Finset (Fin 6), selected.card = 3 →
        ¬ (subsetSum design selected - 1).PosDef :=
      fun selected hcard hposDef => hsome ⟨selected, hcard, hposDef⟩
    obtain ⟨weakDominator, hcard, hdominates⟩ :=
      rank_three_iff_six_three.mp (gtzWeightedAll_three_of_hinge hhinge) design
    exact (isPrimitiveDesign_iff_not_hasParallelPair design).mp hprimitive
      (hhinge design ⟨⟨weakDominator, hcard, hdominates⟩, hnoStrict⟩)

/-- **THE HINGE SELECTS A POSITIVE DEFINITE GAP BLOCK.**  The order embedding of
the strict triple is the injective pick the block vocabulary asks for, and its
image is the triple again. -/
theorem blockGapAt_posDef_of_hinge (hhinge : HingeHoldsAtSize 6 3) :
    ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
        (blockGapAt (projectionOfDesign design) design.weight pick).PosDef := by
  intro design hprimitive
  obtain ⟨selected, hcard, hposDef⟩ := exists_posDef_subsetSum_of_hinge hhinge design hprimitive
  refine ⟨selected.orderEmbOfFin hcard, (selected.orderEmbOfFin hcard).injective, ?_⟩
  rw [posDef_blockGapAt_iff_subsetSum design (selected.orderEmbOfFin hcard).injective,
    image_orderEmbOfFin hcard]
  exact hposDef

/-- **THE HINGE PRODUCES THE OFFSET CRITERION.**  The landed faithfulness of the
door carries the block selection back into offset coordinates with no loss. -/
theorem offsetDominatesSomewhere_of_hinge (hhinge : HingeHoldsAtSize 6 3) :
    OffsetDominatesSomewhere :=
  offsetDominatesSomewhere_iff_blockGapSelects.mpr (blockGapAt_posDef_of_hinge hhinge)

/-- **THE OFFSET CRITERION PRODUCES THE HINGE.**  A tie with a parallel pair
satisfies the hinge at once.  A tie without one is primitive, and the criterion
then exhibits a positive definite gap block, which no tie admits. -/
theorem hingeHoldsAtSize_six_three_of_offsetDominatesSomewhere
    (hoffset : OffsetDominatesSomewhere) : HingeHoldsAtSize 6 3 := by
  intro design htie
  by_cases hpair : HasParallelPair design
  · exact hpair
  · exfalso
    obtain ⟨pick, hinjective, hposDef⟩ :=
      blockGapAt_posDef_of_offsetDominatesSomewhere hoffset design
        ((isPrimitiveDesign_iff_not_hasParallelPair design).mpr hpair)
    exact not_isTie_of_posDef_blockGapAt design hinjective hposDef htie

/-- **THE OFFSET DOOR IS THE `(6,3)` HINGE.**  Three polynomial inequalities at
one pivot of one design, with no determinant, no root and no division, are
EQUIVALENT to the frontier of the rank-three campaign.  A producer for the door
is a proof of the conjecture, and a proof of the conjecture is a producer. -/
theorem offsetDominatesSomewhere_iff_hingeHoldsAtSize_six_three :
    OffsetDominatesSomewhere ↔ HingeHoldsAtSize 6 3 :=
  ⟨hingeHoldsAtSize_six_three_of_offsetDominatesSomewhere, offsetDominatesSomewhere_of_hinge⟩

/-- The same statement against the landed block vocabulary. -/
theorem blockGapSelects_iff_hingeHoldsAtSize_six_three :
    (∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
        ∃ pick : Fin 3 → Fin 6, Function.Injective pick ∧
          (blockGapAt (projectionOfDesign design) design.weight pick).PosDef)
      ↔ HingeHoldsAtSize 6 3 :=
  ⟨fun hselect => hingeHoldsAtSize_six_three_of_offsetDominatesSomewhere
      (offsetDominatesSomewhere_iff_blockGapSelects.mpr hselect),
    blockGapAt_posDef_of_hinge⟩

/-- **THE HINGE IS THE CONSOLIDATED DESIGN SELECTOR.**  The level-one Prop of
`Gtz/Wave/WiringDoorLedger.lean` is reached here through the offset lane, and the
strict triple is the one the hinge itself supplies. -/
theorem consolidatedStrictTripleDesign_of_hinge_viaOffset (hhinge : HingeHoldsAtSize 6 3) :
    ConsolidatedStrictTripleDesign :=
  fun design hprimitive => exists_posDef_subsetSum_of_hinge hhinge design hprimitive

/-- **THE OFFSET DOOR IS THE LEVEL-ONE SELECTOR PROP.**  The mission of this lane
asked whether the entrance records anything beyond the selector that fifteen of
the eighteen `Gtz.allFiveOnPath_of_*` doors funnel through.  It records nothing:
the two Props are equivalent. -/
theorem consolidatedStrictTripleDesign_iff_offsetDominatesSomewhere :
    ConsolidatedStrictTripleDesign ↔ OffsetDominatesSomewhere :=
  ⟨fun hselector => offsetDominatesSomewhere_of_hinge
      (hingeHoldsAtSize_six_three_of_consolidatedStrictTripleDesign hselector),
    fun hoffset => consolidatedStrictTripleDesign_of_hinge_viaOffset
      (hingeHoldsAtSize_six_three_of_offsetDominatesSomewhere hoffset)⟩

/-- The chart-side selector joins the same class. -/
theorem consolidatedStrictTriple_iff_offsetDominatesSomewhere :
    ConsolidatedStrictTriple ↔ OffsetDominatesSomewhere :=
  consolidatedStrictTriple_iff_consolidatedStrictTripleDesign.trans
    consolidatedStrictTripleDesign_iff_offsetDominatesSomewhere

/-! ### 4.  THE FIVE REGISTRY OBLIGATIONS ARE THE OFFSET CRITERION

`Gtz.AllFiveOnPath` names the conjunction of the five on-path registry Props.
The route from the hinge back to that conjunction runs through this module's own
lane and through no selector. -/

/-- The five registry Props reach the hinge through the single stress residual. -/
theorem hingeHoldsAtSize_six_three_of_allFiveOnPath (hall : AllFiveOnPath) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_sixThree_of_noStressResidual (noStressResidual_six_of_allFiveOnPath hall)

/-- **THE HINGE DISCHARGES ALL FIVE REGISTRY PROPS, THROUGH THE OFFSET LANE.** -/
theorem allFiveOnPath_of_hinge (hhinge : HingeHoldsAtSize 6 3) : AllFiveOnPath :=
  allFiveOnPath_of_offsetDominates (offsetDominatesSomewhere_of_hinge hhinge)

/-- **THE FIVE REGISTRY OBLIGATIONS ARE THE `(6,3)` HINGE.**  The five axioms of
`Skeleton/Obligations.lean` are not five independent assumptions above the
frontier.  They are the frontier. -/
theorem allFiveOnPath_iff_hingeHoldsAtSize_six_three :
    AllFiveOnPath ↔ HingeHoldsAtSize 6 3 :=
  ⟨hingeHoldsAtSize_six_three_of_allFiveOnPath, allFiveOnPath_of_hinge⟩

/-- **THE FIVE REGISTRY OBLIGATIONS ARE THREE SCALAR INEQUALITIES.**  The main
statement of this module.  A producer must supply, at every primitive `(6,3)`
design, one pivot of positive excess, one partner of positive shifted pair minor,
and one further label whose squared offset falls below the product of the two
minors.  That is the whole of the five on-path registry axioms. -/
theorem allFiveOnPath_iff_offsetDominatesSomewhere :
    AllFiveOnPath ↔ OffsetDominatesSomewhere :=
  allFiveOnPath_iff_hingeHoldsAtSize_six_three.trans
    offsetDominatesSomewhere_iff_hingeHoldsAtSize_six_three.symm

/-- **THE FIRST REGISTRY OBLIGATION, FROM THE OFFSET CRITERION.**  The line-free
`U(3,6)` residual is the Prop that `Skeleton.obligationBaseTripleTightUThreeSix`
asserts.  It is the first conjunct of the five. -/
theorem baseTripleTightLineFree_of_offsetDominatesSomewhere
    (hoffset : OffsetDominatesSomewhere) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual :=
  (allFiveOnPath_of_offsetDominates hoffset).1

/-- **THE FIRST REGISTRY OBLIGATION, FROM THE HINGE.**  The same conjunct through
the backward arrow of section 3. -/
theorem baseTripleTightLineFree_of_hinge (hhinge : HingeHoldsAtSize 6 3) :
    BaseTripleTightLineFreeOffConicHeavyNeedleResidual :=
  (allFiveOnPath_of_hinge hhinge).1

/-- **RANK-THREE GTZ AT EVERY SIZE, FROM THE FIVE REGISTRY OBLIGATIONS.**  The
price of the five axioms, stated as the number a planner needs. -/
theorem gtzWeightedAll_three_of_allFiveOnPath_viaHinge (hall : AllFiveOnPath) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_hinge (hingeHoldsAtSize_six_three_of_allFiveOnPath hall)

/-! ### 5.  THE TWO-LOCAL LAW

`Gtz.pairPartialGap` is the pivot excess times the sum of the four triple
determinants at a selected pair.  The corpus carried it as a minor product less
an offset second moment.  The two quartic parts cancel, and what remains factors
through the two weights. -/

/-- **THE TWO-LOCAL LAW.**  The partial gap at a pivot pair equals the pivot
excess times a bracket built from the two excesses, the two weights, the two
diagonals and the single off-diagonal entry.  Pure algebra, no positivity and no
weight hypothesis. -/
theorem pairPartialGap_eq_weightedForm (design : WeightedDesign size 3)
    {first second : Fin size} (hne : first ≠ second) :
    pairPartialGap design first second
      = -diagonalShiftForm design first first
          * (diagonalShiftForm design second second * design.weight first
                * (1 - projectionOfDesign design first first
                    - diagonalShiftForm design first first)
              + diagonalShiftForm design first first * design.weight second
                  * (1 - projectionOfDesign design second second
                      - diagonalShiftForm design second second)
              + 2 * projectionOfDesign design first second ^ 2
                  * (design.weight first + design.weight second)) := by
  rw [pairPartialGap, pairMinorAt, diagonalShiftForm_diag, diagonalShiftForm_diag,
    diagonalShiftForm_offDiag design hne]
  ring

/-- The scalar sign law behind the two-local law. -/
theorem pairPartialGapScalar_nonpos {pivotExcess partnerExcess pivotWeight partnerWeight
    pivotRoom partnerRoom offDiagonal : ℝ}
    (hpivot : 0 < pivotExcess) (hpartner : 0 ≤ partnerExcess)
    (hpivotWeight : 0 < pivotWeight) (hpartnerWeight : 0 < partnerWeight)
    (hpivotRoom : 0 ≤ pivotRoom) (hpartnerRoom : 0 ≤ partnerRoom) :
    -pivotExcess * (partnerExcess * pivotWeight * pivotRoom
        + pivotExcess * partnerWeight * partnerRoom
        + 2 * offDiagonal ^ 2 * (pivotWeight + partnerWeight)) ≤ 0 := by
  have hone : 0 ≤ partnerExcess * pivotWeight * pivotRoom :=
    mul_nonneg (mul_nonneg hpartner hpivotWeight.le) hpivotRoom
  have htwo : 0 ≤ pivotExcess * partnerWeight * partnerRoom :=
    mul_nonneg (mul_nonneg hpivot.le hpartnerWeight.le) hpartnerRoom
  have hthree : 0 ≤ 2 * offDiagonal ^ 2 * (pivotWeight + partnerWeight) :=
    mul_nonneg (by positivity) (by linarith)
  nlinarith [hone, htwo, hthree, hpivot]

/-- **THE TWO-LOCAL GAP IS NONPOSITIVE WHERE THE ROW HAS ROOM.**  If the pivot
excess is positive, the partner excess is nonnegative and each of the two labels
satisfies `P l l + excess l <= 1`, then the partial gap cannot be positive.  The
off-diagonal entry only makes it more negative. -/
theorem pairPartialGap_nonpos_of_room (design : WeightedDesign size 3)
    {first second : Fin size} (hne : first ≠ second)
    (hpivot : 0 < diagonalShiftForm design first first)
    (hpartner : 0 ≤ diagonalShiftForm design second second)
    (hpivotRoom : projectionOfDesign design first first
      + diagonalShiftForm design first first ≤ 1)
    (hpartnerRoom : projectionOfDesign design second second
      + diagonalShiftForm design second second ≤ 1) :
    pairPartialGap design first second ≤ 0 := by
  rw [pairPartialGap_eq_weightedForm design hne]
  exact pairPartialGapScalar_nonpos hpivot hpartner (design.weight_pos first)
    (design.weight_pos second) (by linarith) (by linarith)

/-- A positive pair minor at a pivot of positive excess forces a positive partner
excess, because the squared off-diagonal entry is nonnegative. -/
theorem partnerExcess_pos_of_pairMinor_pos (design : WeightedDesign size rank)
    {first second : Fin size} (hpivot : 0 < diagonalShiftForm design first first)
    (hminor : 0 < pairMinorAt (diagonalShiftForm design) first second) :
    0 < diagonalShiftForm design second second := by
  rw [pairMinorAt] at hminor
  nlinarith [hminor, hpivot, sq_nonneg (diagonalShiftForm design first second)]

/-- **THE TWO-LOCAL DOOR FORCES AN OVERFULL LABEL.**  The exact structural price of
`Gtz.PairPartialGapSomewhere`: at every primitive `(6,3)` design some label reads
`2 * P l l - w l > 1`.  A design whose every label falls at or below one refutes
the door. -/
theorem exists_overfull_label_of_pairPartialGap (hpair : PairPartialGapSomewhere)
    (design : WeightedDesign 6 3) (hprimitive : IsPrimitiveDesign design) :
    ∃ label : Fin 6, 1 < projectionOfDesign design label label
      + diagonalShiftForm design label label := by
  by_cases hex : ∃ label : Fin 6, 1 < projectionOfDesign design label label
      + diagonalShiftForm design label label
  · exact hex
  · exfalso
    have hroom : ∀ label : Fin 6, projectionOfDesign design label label
        + diagonalShiftForm design label label ≤ 1 :=
      fun label => not_lt.mp fun hlt => hex ⟨label, hlt⟩
    obtain ⟨first, second, hne, hpivot, hminor, hgap⟩ := hpair design hprimitive
    have hpartner : 0 < diagonalShiftForm design second second :=
      partnerExcess_pos_of_pairMinor_pos design hpivot hminor
    have hnonpos := pairPartialGap_nonpos_of_room design hne hpivot hpartner.le
      (hroom first) (hroom second)
    linarith

/-! ### 5b.  THE LOAD OF A LABEL, AND ITS UNIVERSAL TOTAL

Section 5 measures a label by `P l l + excess l`, which is `2 * P l l - w l`.  The
six diagonals total the rank and the six weights total one, so the six loads total
`2 * 3 - 1 = 5` at EVERY design of the cell.  No design data survives.  The door
of section 5 asks one label to pass `1` while six of them share `5`. -/

/-- **THE LOAD TOTAL IS A UNIVERSAL CONSTANT.**  Summed over the six labels the
load is `5`, for every weighted design of six atoms in rank three. -/
theorem sum_labelLoad_eq_five (design : WeightedDesign 6 3) :
    ∑ label : Fin 6, (projectionOfDesign design label label
      + diagonalShiftForm design label label) = 5 := by
  have hdiag : ∑ label : Fin 6, projectionOfDesign design label label = (3 : ℝ) := by
    rw [sum_projectionDiagonal_eq_rank design]; norm_num
  have hshift : ∑ label : Fin 6, diagonalShiftForm design label label = (2 : ℝ) := by
    rw [sum_diagonalShiftForm_diag design]; norm_num
  rw [Finset.sum_add_distrib, hdiag, hshift]
  norm_num

/-- **EVERY DESIGN OWNS AN UNDERFULL LABEL.**  Six loads that total `5` cannot all
pass `5/6`, so the door of section 5 never fires at the average label. -/
theorem exists_label_load_le_five_sixths (design : WeightedDesign 6 3) :
    ∃ label : Fin 6, projectionOfDesign design label label
      + diagonalShiftForm design label label ≤ 5 / 6 := by
  by_cases hex : ∃ label : Fin 6, projectionOfDesign design label label
      + diagonalShiftForm design label label ≤ 5 / 6
  · exact hex
  · exfalso
    have hgt : ∀ label : Fin 6, (5 : ℝ) / 6 < projectionOfDesign design label label
        + diagonalShiftForm design label label :=
      fun label => not_le.mp fun hle => hex ⟨label, hle⟩
    have hlt : ∑ _label : Fin 6, (5 : ℝ) / 6
        < ∑ label : Fin 6, (projectionOfDesign design label label
            + diagonalShiftForm design label label) :=
      Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ fun label _ => hgt label
    rw [sum_labelLoad_eq_five design, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hlt
    norm_num at hlt

/-- **THE TWO-LOCAL DOOR IS DEAD ON THE WHOLE SUBCRITICAL LOCUS.**  A design whose
every label carries load at most `1` refutes `Gtz.PairPartialGapSomewhere`.  The
`K4` graphic point is one member of that locus, and section 6 uses it. -/
theorem not_pairPartialGapSomewhere_of_room (design : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign design)
    (hroom : ∀ label : Fin 6, projectionOfDesign design label label
      + diagonalShiftForm design label label ≤ 1) :
    ¬ PairPartialGapSomewhere := by
  intro hpair
  obtain ⟨label, hoverfull⟩ := exists_overfull_label_of_pairPartialGap hpair design hprimitive
  exact absurd hoverfull (not_lt.mpr (hroom label))

/-- **THE TWO-LOCAL DOOR IS DEAD ON THE WHOLE FLAT LOCUS.**  A design whose every
projection diagonal reads one half carries load `1 - w l` at every label, and every
weight is strictly positive.  No weight hypothesis and no primitivity of the flat
point beyond the one supplied enter. -/
theorem not_pairPartialGapSomewhere_of_flatDiagonal (design : WeightedDesign 6 3)
    (hprimitive : IsPrimitiveDesign design)
    (hflat : ∀ label : Fin 6, projectionOfDesign design label label = 1 / 2) :
    ¬ PairPartialGapSomewhere := by
  refine not_pairPartialGapSomewhere_of_room design hprimitive fun label => ?_
  rw [diagonalShiftForm_diag, hflat]
  linarith [design.weight_pos label]

/-! ### 6.  THE `K4` GRAPHIC POINT KILLS THE TWO-LOCAL DOOR

`Gtz.graphicKFourDesign` carries `P l l = 1/2` and weight `1/6` at every label,
so every label reads `5/6` against the threshold `1` of section 5.  The design is
primitive, and section 2 proves that from the projection form alone. -/

/-- The weight of the `K4` graphic design is uniform. -/
theorem weight_graphicKFour (label : Fin 6) : graphicKFourDesign.weight label = 1 / 6 := rfl

/-- Every projection diagonal of the `K4` graphic design is one half. -/
theorem projectionOfDesign_graphicKFour_diag (label : Fin 6) :
    projectionOfDesign graphicKFourDesign label label = 1 / 2 := by
  rw [projectionOfDesign_graphicKFour]
  fin_cases label <;> simp [kFourEdgeVector, Fin.sum_univ_three] <;> norm_num

/-- Every excess of the `K4` graphic design is one third. -/
theorem diagonalShiftForm_graphicKFour_diag (label : Fin 6) :
    diagonalShiftForm graphicKFourDesign label label = 1 / 3 := by
  rw [diagonalShiftForm_diag, projectionOfDesign_graphicKFour_diag, weight_graphicKFour]
  norm_num

/-- **THE OFF-DIAGONAL ENTRIES OF THE `K4` GRAPHIC POINT ARE SMALL.**  Every
squared off-diagonal projection entry is at most `1/16`, against a diagonal
product of `1/4`. -/
theorem sq_projectionOfDesign_graphicKFour_off {first second : Fin 6} (hne : first ≠ second) :
    projectionOfDesign graphicKFourDesign first second ^ 2 ≤ 1 / 16 := by
  rw [projectionOfDesign_graphicKFour]
  revert hne
  fin_cases first <;> fin_cases second <;>
    simp [kFourEdgeVector, Fin.sum_univ_three] <;> norm_num

/-- **THE `K4` GRAPHIC DESIGN IS PRIMITIVE.**  Section 2 reads primitivity off the
projection form, so no atom coordinate and no scalar cancellation is involved. -/
theorem isPrimitiveDesign_graphicKFour : IsPrimitiveDesign graphicKFourDesign := by
  refine isPrimitiveDesign_of_sq_projection_lt graphicKFourDesign fun first second hne => ?_
  have hsmall := sq_projectionOfDesign_graphicKFour_off hne
  rw [projectionOfDesign_graphicKFour_diag, projectionOfDesign_graphicKFour_diag]
  linarith

/-- **THE TWO-LOCAL GAP AT THE `K4` GRAPHIC POINT, EXACTLY.**  The value is
`-1/162 - (2/9) * (P a b) ^ 2` at every ordered pair of distinct labels, so the
off-diagonal entry only deepens the deficit. -/
theorem pairPartialGap_graphicKFour {first second : Fin 6} (hne : first ≠ second) :
    pairPartialGap graphicKFourDesign first second
      = -(1 / 162) - 2 / 9 * projectionOfDesign graphicKFourDesign first second ^ 2 := by
  rw [pairPartialGap_eq_weightedForm graphicKFourDesign hne]
  simp only [diagonalShiftForm_graphicKFour_diag, projectionOfDesign_graphicKFour_diag,
    weight_graphicKFour]
  ring

/-- Every one of the thirty ordered pairs of the `K4` graphic point carries a
strictly negative partial gap. -/
theorem pairPartialGap_graphicKFour_neg {first second : Fin 6} (hne : first ≠ second) :
    pairPartialGap graphicKFourDesign first second < 0 := by
  rw [pairPartialGap_graphicKFour hne]
  nlinarith [sq_nonneg (projectionOfDesign graphicKFourDesign first second)]

/-- **THE TWO-LOCAL DOOR CANNOT OPEN.**  `Gtz.PairPartialGapSomewhere` is FALSE,
with no hypothesis left.  The `K4` graphic design is primitive, and its every
label reads `5/6` against the threshold of section 5. -/
theorem not_pairPartialGapSomewhere : ¬ PairPartialGapSomewhere :=
  not_pairPartialGapSomewhere_of_flatDiagonal graphicKFourDesign isPrimitiveDesign_graphicKFour
    projectionOfDesign_graphicKFour_diag

/-- The same refutation read on the exact value rather than on the threshold. -/
theorem not_pairPartialGapSomewhere_of_value : ¬ PairPartialGapSomewhere := by
  intro hpair
  obtain ⟨first, second, hne, _, _, hgap⟩ :=
    hpair graphicKFourDesign isPrimitiveDesign_graphicKFour
  exact absurd hgap (not_lt.mpr (pairPartialGap_graphicKFour_neg hne).le)

/-- **TWO DOORS TO ALL FIVE REGISTRY OBLIGATIONS THAT CANNOT OPEN.**
`Gtz.allFiveOnPath_of_pairPartialGap` (Gtz/Wave/ThirdLabelSelection.lean:435) and
`Gtz.consolidatedStrictTriple_of_pairPartialGap` (:451) carry the refuted Prop.
Neither reaches the registry from anywhere. -/
theorem pairPartialGapDoors_are_unopenable :
    ¬ PairPartialGapSomewhere
      ∧ (PairPartialGapSomewhere → AllFiveOnPath)
      ∧ (PairPartialGapSomewhere → ConsolidatedStrictTriple) :=
  ⟨not_pairPartialGapSomewhere, allFiveOnPath_of_pairPartialGapSomewhere,
    consolidatedStrictTriple_of_pairPartialGap⟩

/-! ### 6b.  THE THIRD-INEQUALITY DOOR IS EMPTY TOO

`Gtz.allFiveOnPath_of_thirdInequality` (Gtz/Wave/ThirdLabelSelection.lean:186)
reaches the five obligations from the third inequality alone, at a pivot and a
partner that every design already owns.  Its module docstring tells the reader
that the antecedent is free of the vacuity defect.  The antecedent is FALSE.

The door quantifies over EVERY pivot pair of excess at least `1/3` and positive
pair minor, not over one selected pair.  At the `K4` graphic point the three
matching pairs `(0,1)`, `(2,3)` and `(4,5)` qualify, and no third label rescues
them.  The pivot pairing vanishes there, so the offset reads `1/12` at every
third, its square reads `9/1296`, and the minor product reads `7/1296`. -/

/-- The matching pair of the `K4` graphic design has a vanishing pairing. -/
theorem projectionOfDesign_graphicKFour_matchingPair :
    projectionOfDesign graphicKFourDesign 0 1 = 0 := by
  rw [projectionOfDesign_graphicKFour]
  norm_num [kFourEdgeVector, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_four]

/-- The pair minor at the matching pair reads `1/9`. -/
theorem pairMinorAt_graphicKFour_matchingPair :
    pairMinorAt (diagonalShiftForm graphicKFourDesign) 0 1 = 1 / 9 := by
  rw [pairMinorAt, diagonalShiftForm_offDiag graphicKFourDesign (by decide : (0 : Fin 6) ≠ 1),
    projectionOfDesign_graphicKFour_matchingPair]
  simp only [diagonalShiftForm_graphicKFour_diag]
  norm_num

/-- Every label outside the matching pair `(0,1)` pairs with each of its two
members at magnitude one quarter. -/
theorem sq_projectionOfDesign_graphicKFour_matchingRow (third : Fin 6)
    (hzero : third ≠ 0) (hone : third ≠ 1) :
    projectionOfDesign graphicKFourDesign 0 third ^ 2 = 1 / 16
      ∧ projectionOfDesign graphicKFourDesign 1 third ^ 2 = 1 / 16 := by
  have hentry : ∀ first second : Fin 6, projectionOfDesign graphicKFourDesign first second
      = 1 / 4 * ∑ coord, kFourEdgeVector first coord * kFourEdgeVector second coord :=
    projectionOfDesign_graphicKFour
  revert hzero hone
  fin_cases third <;>
    simp [hentry, kFourEdgeVector, Fin.sum_univ_three] <;> norm_num

/-- **THE THIRD-INEQUALITY DOOR CANNOT OPEN.**  The antecedent of
`Gtz.allFiveOnPath_of_thirdInequality` is FALSE, with no hypothesis left.  The
`K4` graphic design qualifies at its matching pair `(0,1)`, and all four remaining
labels miss by `2/1296`. -/
theorem not_forall_thirdInequality :
    ¬ ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
        ∀ label partner : Fin 6, partner ≠ label →
          (1 : ℝ) / 3 ≤ diagonalShiftForm design label label →
          0 < pairMinorAt (diagonalShiftForm design) label partner →
          ∃ third : Fin 6, third ≠ label ∧ third ≠ partner ∧
            shiftOffsetAt design label partner third ^ 2
              < pairMinorAt (diagonalShiftForm design) label partner
                * pairMinorAt (diagonalShiftForm design) label third := by
  intro hthird
  obtain ⟨third, hthirdZero, hthirdOne, hsq⟩ :=
    hthird graphicKFourDesign isPrimitiveDesign_graphicKFour 0 1 (by decide)
      (le_of_eq (diagonalShiftForm_graphicKFour_diag 0).symm)
      (by rw [pairMinorAt_graphicKFour_matchingPair]; norm_num)
  obtain ⟨hrowZero, hrowOne⟩ :=
    sq_projectionOfDesign_graphicKFour_matchingRow third hthirdZero hthirdOne
  have hminorThird : pairMinorAt (diagonalShiftForm graphicKFourDesign) 0 third = 7 / 144 := by
    rw [pairMinorAt, diagonalShiftForm_offDiag graphicKFourDesign hthirdZero.symm]
    simp only [diagonalShiftForm_graphicKFour_diag]
    rw [hrowZero]
    norm_num
  have hoffsetValue : shiftOffsetAt graphicKFourDesign 0 1 third
      = 1 / 3 * projectionOfDesign graphicKFourDesign 1 third := by
    rw [shiftOffsetAt, offsetAt,
      diagonalShiftForm_offDiag graphicKFourDesign hthirdOne.symm,
      diagonalShiftForm_offDiag graphicKFourDesign (by decide : (0 : Fin 6) ≠ 1),
      diagonalShiftForm_offDiag graphicKFourDesign hthirdZero.symm,
      projectionOfDesign_graphicKFour_matchingPair, diagonalShiftForm_graphicKFour_diag]
    ring
  have hoffset : shiftOffsetAt graphicKFourDesign 0 1 third ^ 2 = 1 / 144 := by
    rw [hoffsetValue]
    linear_combination (1 : ℝ) / 9 * hrowOne
  rw [hoffset, pairMinorAt_graphicKFour_matchingPair, hminorThird] at hsq
  norm_num at hsq

/-- **THREE DOORS TO ALL FIVE REGISTRY OBLIGATIONS THAT CANNOT OPEN.**  The
two-local pair door, its consolidated twin, and the third-inequality door.  Each
one type-checks and reads as an asset.  None of them reaches the registry. -/
theorem unopenableJointDoors :
    ¬ PairPartialGapSomewhere
      ∧ ¬ ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
          ∀ label partner : Fin 6, partner ≠ label →
            (1 : ℝ) / 3 ≤ diagonalShiftForm design label label →
            0 < pairMinorAt (diagonalShiftForm design) label partner →
            ∃ third : Fin 6, third ≠ label ∧ third ≠ partner ∧
              shiftOffsetAt design label partner third ^ 2
                < pairMinorAt (diagonalShiftForm design) label partner
                  * pairMinorAt (diagonalShiftForm design) label third :=
  ⟨not_pairPartialGapSomewhere, not_forall_thirdInequality⟩

/-! ### 7.  THE OFFSET DOOR FIRES AT THE SAME DESIGN

The three edges `0`, `2` and `4` of the `K4` graphic design pairwise meet, and
each of their three pairings reads `1/4`.  The shifted block on that triple is
`!![1/3, 1/4, 1/4; 1/4, 1/3, 1/4; 1/4, 1/4, 1/3]`, whose three leading minors are
`1/3`, `7/144` and `5/864`. -/

/-- The three pairings of the meeting triple of the `K4` graphic design. -/
theorem projectionOfDesign_graphicKFour_meetingTriple :
    projectionOfDesign graphicKFourDesign 0 2 = 1 / 4
      ∧ projectionOfDesign graphicKFourDesign 0 4 = 1 / 4
      ∧ projectionOfDesign graphicKFourDesign 2 4 = 1 / 4 := by
  refine ⟨?_, ?_, ?_⟩ <;>
    rw [projectionOfDesign_graphicKFour] <;>
    norm_num [kFourEdgeVector, Fin.sum_univ_three, Matrix.cons_val_two, Matrix.cons_val_four]

/-- The two shifted pair minors of the meeting triple read `7/144`. -/
theorem pairMinorAt_graphicKFour_meetingTriple :
    pairMinorAt (diagonalShiftForm graphicKFourDesign) 0 2 = 7 / 144
      ∧ pairMinorAt (diagonalShiftForm graphicKFourDesign) 0 4 = 7 / 144 := by
  obtain ⟨hzeroTwo, hzeroFour, _⟩ := projectionOfDesign_graphicKFour_meetingTriple
  constructor
  · rw [pairMinorAt, diagonalShiftForm_offDiag graphicKFourDesign (by decide : (0 : Fin 6) ≠ 2),
      hzeroTwo]
    simp only [diagonalShiftForm_graphicKFour_diag]
    norm_num
  · rw [pairMinorAt, diagonalShiftForm_offDiag graphicKFourDesign (by decide : (0 : Fin 6) ≠ 4),
      hzeroFour]
    simp only [diagonalShiftForm_graphicKFour_diag]
    norm_num

/-- The offset of the meeting triple reads `1/48`. -/
theorem shiftOffsetAt_graphicKFour_meetingTriple :
    shiftOffsetAt graphicKFourDesign 0 2 4 = 1 / 48 := by
  obtain ⟨hzeroTwo, hzeroFour, htwoFour⟩ := projectionOfDesign_graphicKFour_meetingTriple
  rw [shiftOffsetAt, offsetAt,
    diagonalShiftForm_offDiag graphicKFourDesign (by decide : (2 : Fin 6) ≠ 4),
    diagonalShiftForm_offDiag graphicKFourDesign (by decide : (0 : Fin 6) ≠ 2),
    diagonalShiftForm_offDiag graphicKFourDesign (by decide : (0 : Fin 6) ≠ 4),
    htwoFour, hzeroTwo, hzeroFour]
  simp only [diagonalShiftForm_graphicKFour_diag]
  norm_num

/-- **THE OFFSET CRITERION HOLDS AT THE `K4` GRAPHIC DESIGN.**  The squared offset
is `9/20736` and the minor product is `49/20736`, so the margin is `5/2592`.  The
same design refutes the two-local door of section 6. -/
theorem offsetDominatesAt_graphicKFour :
    ∃ first second third : Fin 6,
      first ≠ second ∧ third ≠ first ∧ third ≠ second ∧
      0 < diagonalShiftForm graphicKFourDesign first first ∧
      0 < pairMinorAt (diagonalShiftForm graphicKFourDesign) first second ∧
      shiftOffsetAt graphicKFourDesign first second third ^ 2
        < pairMinorAt (diagonalShiftForm graphicKFourDesign) first second
          * pairMinorAt (diagonalShiftForm graphicKFourDesign) first third := by
  obtain ⟨hminorTwo, hminorFour⟩ := pairMinorAt_graphicKFour_meetingTriple
  refine ⟨0, 2, 4, by decide, by decide, by decide, ?_, ?_, ?_⟩
  · rw [diagonalShiftForm_graphicKFour_diag]; norm_num
  · rw [hminorTwo]; norm_num
  · rw [shiftOffsetAt_graphicKFour_meetingTriple, hminorTwo, hminorFour]; norm_num

/-- **THE `K4` GRAPHIC DESIGN IS NOT A TIE.**  Unconditional, from the three
scalar inequalities of the offset criterion. -/
theorem not_isTie_graphicKFour : ¬ IsTie graphicKFourDesign := by
  obtain ⟨first, second, third, hne, hthirdFirst, hthirdSecond, hpivot, hminor, hsq⟩ :=
    offsetDominatesAt_graphicKFour
  exact not_isTie_of_offsetDominatesAt graphicKFourDesign hne hthirdFirst hthirdSecond
    hpivot hminor hsq

/-! ### 8.  THE LEDGER -/

/-- **THE JOINT ENTRANCE LEDGER.**  The two Props of this lane, priced against the
frontier and against each other.

* The offset criterion IS `Gtz.HingeHoldsAtSize 6 3`, and so are the five on-path
  registry obligations.
* The two-local criterion is FALSE, and its two doors cannot open.
* The third-inequality criterion is FALSE as well.
* One design, `Gtz.graphicKFourDesign`, witnesses all three facts.

A campaign that moves between the offset criterion, the five class obligations
and the hinge buys formula size and nothing else. -/
theorem jointEntranceLedger :
    (OffsetDominatesSomewhere ↔ HingeHoldsAtSize 6 3)
      ∧ (AllFiveOnPath ↔ HingeHoldsAtSize 6 3)
        ∧ (AllFiveOnPath ↔ OffsetDominatesSomewhere)
          ∧ (ConsolidatedStrictTripleDesign ↔ OffsetDominatesSomewhere)
            ∧ (OffsetDominatesSomewhere → GtzWeightedAll 3)
              ∧ (¬ PairPartialGapSomewhere
                ∧ ¬ ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
                    ∀ label partner : Fin 6, partner ≠ label →
                      (1 : ℝ) / 3 ≤ diagonalShiftForm design label label →
                      0 < pairMinorAt (diagonalShiftForm design) label partner →
                      ∃ third : Fin 6, third ≠ label ∧ third ≠ partner ∧
                        shiftOffsetAt design label partner third ^ 2
                          < pairMinorAt (diagonalShiftForm design) label partner
                            * pairMinorAt (diagonalShiftForm design) label third)
                ∧ ¬ IsTie graphicKFourDesign :=
  ⟨offsetDominatesSomewhere_iff_hingeHoldsAtSize_six_three,
    allFiveOnPath_iff_hingeHoldsAtSize_six_three,
      allFiveOnPath_iff_offsetDominatesSomewhere,
        consolidatedStrictTripleDesign_iff_offsetDominatesSomewhere,
          gtzWeightedAll_three_of_offsetDominatesSomewhere,
            unopenableJointDoors,
              not_isTie_graphicKFour⟩

/-- **THE RANK-THREE FRONTIER, IN THREE SCALAR INEQUALITIES.**  The whole cost of
rank-three GTZ at every size, stated with no chart, no selector, no pattern list
and no residual vocabulary.  A producer supplies, at every primitive `(6,3)`
design, one pivot of positive excess, one partner of positive shifted pair minor,
and one further label whose squared offset falls below the product of the two
minors. -/
theorem gtzWeightedAll_three_of_threeInequalities
    (hthree : ∀ design : WeightedDesign 6 3, IsPrimitiveDesign design →
      ∃ first second third : Fin 6,
        first ≠ second ∧ third ≠ first ∧ third ≠ second ∧
        0 < diagonalShiftForm design first first ∧
        0 < pairMinorAt (diagonalShiftForm design) first second ∧
        shiftOffsetAt design first second third ^ 2
          < pairMinorAt (diagonalShiftForm design) first second
            * pairMinorAt (diagonalShiftForm design) first third) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_offsetDominatesSomewhere hthree

end Gtz
