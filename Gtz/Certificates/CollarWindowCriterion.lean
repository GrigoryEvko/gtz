import Mathlib

/-!
# Bridge (i): the collar window criterion over an ordered field

The kernel-replay layer (`Gtz.Certificates.CollarChartReplay`) certifies, at
every rational point of a chart cube, an INTEGER SIGN PACKAGE: positive
`H11` / `M2` threshold products, a directed kernel vector on the beta slots
(boundary-ray semantics: `0 <= dir * slotValue`, zeros allowed), and a
strict margin chain `0 < RN * thrDen * margin`.  This file turns that sign
package into the mathematical collar statement

    rho_star(w)  <  rho_G*(w)

over an arbitrary ordered field, where

  * `rho_star` is the MINIMUM over the valid through-trees of the threshold
    `thrNum / thrDen`, and
  * `rho_G*` is the MAXIMUM over the admissible Gordan aggregates of the
    ratio `ratioNum / ratioDen`.

Both index sets are finite and nonempty, so `max > min` is exactly
"some aggregate ratio beats some valid threshold" -- no completeness of the
field and no supremum machinery is needed.

The one structural input the Int package does NOT carry is the identity of
`RN` and `RD` as the Gordan sums

    RN = sum_C alpha_C,        RD = sum_C alpha_C * t_C   (t_C >= 0),

which is what makes the ratio positive and lets the checker's `RN`-indexed
margin sign be read as a statement about `RD`.  That identity is supplied
here as the `IsGordanAggregate` hypothesis and is discharged in the
dictionary layer (bridge (iii)); `couplingsAreNonneg` holds because every
`t_C = (v_5 . u_C)^2 / (u_C^T B u_C)` is a square over a positive.

Nothing in this file is specific to `Real`: it is stated for
`[Field K] [LinearOrder K] [IsStrictOrderedRing K]`, hence applies to the
rational points directly and to the real cube after bridge (iv).
-/

namespace GtzCollarWindow

universe u

/-- The threshold record of one through-tree at one point: the through-tree
gap's top-left entry `H11 = spanNum / spanDen`, its two-by-two block
determinant `M2 = massNum / massDen`, and the crossing threshold
`thr = thrNum / thrDen`. -/
structure ThroughTreeRecord (K : Type u) where
  spanNum : K
  spanDen : K
  massNum : K
  massDen : K
  thrNum : K
  thrDen : K

/-- The Gordan-aggregate record of one dictionary candidate at one point:
the five beta slots (the nonnegative left-kernel ray of the crossing
system), the crossing couplings `t_C`, and the ratio `RN / RD`. -/
structure GordanAggregateRecord (K : Type u) where
  slots : List K
  couplings : List K
  ratioNum : K
  ratioDen : K

section OrderedRing

variable {K : Type u} [CommRing K] [LinearOrder K] [IsStrictOrderedRing K]

/-- Sum of the beta slots -- the Gordan numerator. -/
def slotSum : List K → K
  | [] => 0
  | slot :: restSlots => slot + slotSum restSlots

/-- Coupling-weighted sum of the beta slots -- the Gordan denominator. -/
def coupledSum : List K → List K → K
  | [], _ => 0
  | _ :: _, [] => 0
  | slot :: restSlots, coupling :: restCouplings =>
      slot * coupling + coupledSum restSlots restCouplings

/-- Boundary-ray cone membership: every slot is weakly on one side.  Zeros
are allowed -- a boundary ray of the nonnegative left-kernel cone is still a
valid Gordan aggregate, which is exactly the rung-15 relaxation the guarded
pairs exploit. -/
def SlotsAreDirected (slots : List K) (direction : K) : Prop :=
  (direction = 1 ∨ direction = -1) ∧ ∀ slot ∈ slots, 0 ≤ direction * slot

/-- The structural content of "this record is a Gordan aggregate of the
crossing system": its ratio is the quotient of the plain slot sum by the
coupling-weighted slot sum, and the couplings are nonnegative. -/
structure IsGordanAggregate (aggregate : GordanAggregateRecord K) : Prop where
  ratioNumIsSlotSum : aggregate.ratioNum = slotSum aggregate.slots
  ratioDenIsCoupledSum :
    aggregate.ratioDen = coupledSum aggregate.slots aggregate.couplings
  couplingsAreNonneg : ∀ coupling ∈ aggregate.couplings, 0 ≤ coupling

theorem directedSlotSumIsNonneg {slots : List K} {direction : K}
    (directed : SlotsAreDirected slots direction) :
    0 ≤ direction * slotSum slots := by
  obtain ⟨_, slotsNonneg⟩ := directed
  induction slots with
  | nil => simp [slotSum]
  | cons slot restSlots inductiveStep =>
      have headNonneg : 0 ≤ direction * slot :=
        slotsNonneg slot (List.mem_cons_self ..)
      have tailNonneg : 0 ≤ direction * slotSum restSlots :=
        inductiveStep fun other otherMem =>
          slotsNonneg other (List.mem_cons_of_mem slot otherMem)
      have expand : direction * slotSum (slot :: restSlots)
          = direction * slot + direction * slotSum restSlots := by
        simp [slotSum, mul_add]
      rw [expand]
      exact add_nonneg headNonneg tailNonneg

theorem coupledSumIsNonnegOfDirectedSlots {direction : K} :
    ∀ (slots couplings : List K),
      (∀ slot ∈ slots, 0 ≤ direction * slot) →
      (∀ coupling ∈ couplings, 0 ≤ coupling) →
      0 ≤ direction * coupledSum slots couplings := by
  intro slots
  induction slots with
  | nil => intro couplings _ _; simp [coupledSum]
  | cons slot restSlots inductiveStep =>
      intro couplings slotsNonneg couplingsNonneg
      cases couplings with
      | nil => simp [coupledSum]
      | cons coupling restCouplings =>
          have headNonneg : 0 ≤ direction * (slot * coupling) := by
            have slotNonneg : 0 ≤ direction * slot :=
              slotsNonneg slot (List.mem_cons_self ..)
            have couplingNonneg : 0 ≤ coupling :=
              couplingsNonneg coupling (List.mem_cons_self ..)
            have reassociate : direction * (slot * coupling)
                = (direction * slot) * coupling := by ring
            rw [reassociate]
            exact mul_nonneg slotNonneg couplingNonneg
          have tailNonneg :
              0 ≤ direction * coupledSum restSlots restCouplings :=
            inductiveStep restCouplings
              (fun other otherMem =>
                slotsNonneg other (List.mem_cons_of_mem slot otherMem))
              (fun other otherMem =>
                couplingsNonneg other (List.mem_cons_of_mem coupling otherMem))
          have expand :
              direction * coupledSum (slot :: restSlots)
                  (coupling :: restCouplings)
                = direction * (slot * coupling)
                  + direction * coupledSum restSlots restCouplings := by
            simp [coupledSum, mul_add]
          rw [expand]
          exact add_nonneg headNonneg tailNonneg

theorem directedCoupledSumIsNonneg {slots couplings : List K} {direction : K}
    (directed : SlotsAreDirected slots direction)
    (couplingsNonneg : ∀ coupling ∈ couplings, 0 ≤ coupling) :
    0 ≤ direction * coupledSum slots couplings :=
  coupledSumIsNonnegOfDirectedSlots slots couplings directed.2 couplingsNonneg

/-- THE MISSING SIGN FACT, supplied by the Gordan structure: numerator and
denominator of an in-cone aggregate have the SAME sign, so the Gordan ratio
is positive.  This is what licenses reading the checker's `RN`-indexed
margin sign as a statement about `RD`. -/
theorem ratioNumMulRatioDenIsPositive {aggregate : GordanAggregateRecord K}
    {direction : K}
    (isAggregate : IsGordanAggregate aggregate)
    (directed : SlotsAreDirected aggregate.slots direction)
    (ratioNumIsNonzero : aggregate.ratioNum ≠ 0)
    (ratioDenIsNonzero : aggregate.ratioDen ≠ 0) :
    0 < aggregate.ratioNum * aggregate.ratioDen := by
  have directionIsUnit : direction = 1 ∨ direction = -1 := directed.1
  have directionSquare : direction * direction = 1 := by
    rcases directionIsUnit with unit | unit <;> rw [unit] <;> ring
  have directionNonzero : direction ≠ 0 := by
    rcases directionIsUnit with unit | unit <;> rw [unit] <;> simp
  have numeratorNonneg : 0 ≤ direction * aggregate.ratioNum := by
    rw [isAggregate.ratioNumIsSlotSum]
    exact directedSlotSumIsNonneg directed
  have denominatorNonneg : 0 ≤ direction * aggregate.ratioDen := by
    rw [isAggregate.ratioDenIsCoupledSum]
    exact directedCoupledSumIsNonneg directed isAggregate.couplingsAreNonneg
  have numeratorPos : 0 < direction * aggregate.ratioNum :=
    lt_of_le_of_ne numeratorNonneg
      (Ne.symm (mul_ne_zero directionNonzero ratioNumIsNonzero))
  have denominatorPos : 0 < direction * aggregate.ratioDen :=
    lt_of_le_of_ne denominatorNonneg
      (Ne.symm (mul_ne_zero directionNonzero ratioDenIsNonzero))
  have productForm : aggregate.ratioNum * aggregate.ratioDen
      = (direction * aggregate.ratioNum) * (direction * aggregate.ratioDen) := by
    have expand : (direction * aggregate.ratioNum)
        * (direction * aggregate.ratioDen)
        = (direction * direction)
          * (aggregate.ratioNum * aggregate.ratioDen) := by ring
    rw [expand, directionSquare, one_mul]
  rw [productForm]
  exact mul_pos numeratorPos denominatorPos

/-- The checker's margin sign is indexed by `RN`; the mathematical
comparison is indexed by `RD`.  Given that the two share a sign, the
cross-multiplied window inequality follows. -/
theorem crossInequalityOfMarginSign {ratioNum ratioDen thrDen margin : K}
    (ratioSign : 0 < ratioNum * ratioDen)
    (marginSign : 0 < ratioNum * thrDen * margin) :
    0 < margin * (ratioDen * thrDen) := by
  have ratioNumIsNonzero : ratioNum ≠ 0 := by
    intro isZero
    rw [isZero, zero_mul] at ratioSign
    exact lt_irrefl 0 ratioSign
  have squarePos : 0 < ratioNum * ratioNum := by
    rcases lt_trichotomy ratioNum 0 with negative | zero | positive
    · exact mul_pos_of_neg_of_neg negative negative
    · exact absurd zero ratioNumIsNonzero
    · exact mul_pos positive positive
  have combined : 0 < (margin * (ratioDen * thrDen)) * (ratioNum * ratioNum) := by
    have regroup : (ratioNum * thrDen * margin) * (ratioNum * ratioDen)
        = (margin * (ratioDen * thrDen)) * (ratioNum * ratioNum) := by ring
    rw [← regroup]
    exact mul_pos marginSign ratioSign
  by_contra crossNotPos
  have crossNonpos : margin * (ratioDen * thrDen) ≤ 0 := not_lt.mp crossNotPos
  have scaled : (margin * (ratioDen * thrDen)) * (ratioNum * ratioNum)
      ≤ 0 * (ratioNum * ratioNum) :=
    mul_le_mul_of_nonneg_right crossNonpos (le_of_lt squarePos)
  rw [zero_mul] at scaled
  exact absurd combined (not_lt.mpr scaled)

end OrderedRing

section OrderedField

variable {K : Type u} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

/-- The threshold of a through-tree record. -/
def ThroughTreeRecord.threshold (record : ThroughTreeRecord K) : K :=
  record.thrNum / record.thrDen

/-- The Gordan ratio of an aggregate record. -/
def GordanAggregateRecord.ratio (aggregate : GordanAggregateRecord K) : K :=
  aggregate.ratioNum / aggregate.ratioDen

/-- Validity of a through-tree at a point: `H11 > 0` and `M2 > 0`, in the
denominator-cleared form the checker certifies. -/
def ThroughTreeRecord.IsValidAt (record : ThroughTreeRecord K) : Prop :=
  0 < record.spanNum * record.spanDen ∧ 0 < record.massNum * record.massDen

omit [IsStrictOrderedRing K] in
theorem thrDenIsNonzeroOfMarginSign {ratioNum thrDen margin : K}
    (marginSign : 0 < ratioNum * thrDen * margin) : thrDen ≠ 0 := by
  intro isZero
  rw [isZero, mul_zero, zero_mul] at marginSign
  exact lt_irrefl 0 marginSign

/-- THE WINDOW CRITERION, guarded-candidate form.  A directed boundary-ray
aggregate with a strict margin against a through-tree beats that
through-tree's threshold. -/
theorem thresholdLtRatioOfSignPackage {aggregate : GordanAggregateRecord K}
    {record : ThroughTreeRecord K} {direction margin : K}
    (isAggregate : IsGordanAggregate aggregate)
    (directed : SlotsAreDirected aggregate.slots direction)
    (ratioNumIsNonzero : aggregate.ratioNum ≠ 0)
    (ratioDenIsNonzero : aggregate.ratioDen ≠ 0)
    (marginIsCross :
      margin = aggregate.ratioNum * record.thrDen
        - record.thrNum * aggregate.ratioDen)
    (marginSign : 0 < aggregate.ratioNum * record.thrDen * margin) :
    record.threshold < aggregate.ratio := by
  have thrDenIsNonzero : record.thrDen ≠ 0 :=
    thrDenIsNonzeroOfMarginSign marginSign
  have ratioSign : 0 < aggregate.ratioNum * aggregate.ratioDen :=
    ratioNumMulRatioDenIsPositive isAggregate directed ratioNumIsNonzero
      ratioDenIsNonzero
  have crossPositive : 0 < margin * (aggregate.ratioDen * record.thrDen) :=
    crossInequalityOfMarginSign ratioSign marginSign
  have differenceForm :
      aggregate.ratio - record.threshold
        = margin / (aggregate.ratioDen * record.thrDen) := by
    unfold GordanAggregateRecord.ratio ThroughTreeRecord.threshold
    rw [marginIsCross]
    field_simp
  have quotientPositive : 0 < margin / (aggregate.ratioDen * record.thrDen) := by
    rcases mul_pos_iff.mp crossPositive with ⟨marginPos, denPos⟩ | ⟨marginNeg, denNeg⟩
    · exact div_pos marginPos denPos
    · exact div_pos_iff.mpr (Or.inr ⟨marginNeg, denNeg⟩)
  have differencePositive : 0 < aggregate.ratio - record.threshold := by
    rw [differenceForm]; exact quotientPositive
  linarith

/-- THE WINDOW CRITERION, free-win form.  A valid through-tree whose
threshold is negative dominates for every nonnegative crossing ratio: the
collar window is open with nothing on the aggregate side to prove. -/
theorem thresholdIsNegativeOfFreeWin {record : ThroughTreeRecord K}
    (freeWin : record.thrNum * record.thrDen < 0) :
    record.threshold < 0 := by
  have thrDenIsNonzero : record.thrDen ≠ 0 := by
    intro isZero
    rw [isZero, mul_zero] at freeWin
    exact lt_irrefl 0 freeWin
  unfold ThroughTreeRecord.threshold
  rcases mul_neg_iff.mp freeWin with ⟨numPos, denNeg⟩ | ⟨numNeg, denPos⟩
  · exact div_neg_of_pos_of_neg numPos denNeg
  · exact div_neg_of_neg_of_pos numNeg denPos

/-- Every in-cone aggregate has a strictly positive Gordan ratio, so a free
win really does open the window. -/
theorem ratioIsPositive {aggregate : GordanAggregateRecord K} {direction : K}
    (isAggregate : IsGordanAggregate aggregate)
    (directed : SlotsAreDirected aggregate.slots direction)
    (ratioNumIsNonzero : aggregate.ratioNum ≠ 0)
    (ratioDenIsNonzero : aggregate.ratioDen ≠ 0) :
    0 < aggregate.ratio := by
  have ratioSign : 0 < aggregate.ratioNum * aggregate.ratioDen :=
    ratioNumMulRatioDenIsPositive isAggregate directed ratioNumIsNonzero
      ratioDenIsNonzero
  unfold GordanAggregateRecord.ratio
  rcases mul_pos_iff.mp ratioSign with ⟨numPos, denPos⟩ | ⟨numNeg, denNeg⟩
  · exact div_pos numPos denPos
  · exact div_pos_iff.mpr (Or.inr ⟨numNeg, denNeg⟩)

/-! ## `rho_star` and `rho_G*` as extrema over the finite dictionaries -/

/-- `rho_star(w)`: the minimum threshold over a nonempty list of valid
through-trees. -/
def rhoStar (headRecord : ThroughTreeRecord K)
    (restRecords : List (ThroughTreeRecord K)) : K :=
  restRecords.foldr (fun record accumulated => min record.threshold accumulated)
    headRecord.threshold

/-- `rho_G*(w)`: the maximum Gordan ratio over a nonempty list of
admissible aggregates. -/
def rhoGStar (headAggregate : GordanAggregateRecord K)
    (restAggregates : List (GordanAggregateRecord K)) : K :=
  restAggregates.foldr
    (fun aggregate accumulated => max aggregate.ratio accumulated)
    headAggregate.ratio

omit [IsStrictOrderedRing K] in
theorem rhoStarLeThreshold {headRecord : ThroughTreeRecord K}
    {restRecords : List (ThroughTreeRecord K)} {record : ThroughTreeRecord K}
    (recordMem : record ∈ headRecord :: restRecords) :
    rhoStar headRecord restRecords ≤ record.threshold := by
  induction restRecords with
  | nil =>
      have recordIsHead : record = headRecord := by simpa using recordMem
      rw [recordIsHead]
      exact le_refl _
  | cons nextRecord furtherRecords inductiveStep =>
      have unfoldFold : rhoStar headRecord (nextRecord :: furtherRecords)
          = min nextRecord.threshold (rhoStar headRecord furtherRecords) := rfl
      rw [unfoldFold]
      rcases List.mem_cons.mp recordMem with recordIsHead | recordInTail
      · refine le_trans (min_le_right _ _) (inductiveStep ?_)
        exact List.mem_cons.mpr (Or.inl recordIsHead)
      · rcases List.mem_cons.mp recordInTail with recordIsNext | recordDeeper
        · rw [recordIsNext]
          exact min_le_left _ _
        · refine le_trans (min_le_right _ _) (inductiveStep ?_)
          exact List.mem_cons.mpr (Or.inr recordDeeper)

omit [IsStrictOrderedRing K] in
theorem ratioLeRhoGStar {headAggregate : GordanAggregateRecord K}
    {restAggregates : List (GordanAggregateRecord K)}
    {aggregate : GordanAggregateRecord K}
    (aggregateMem : aggregate ∈ headAggregate :: restAggregates) :
    aggregate.ratio ≤ rhoGStar headAggregate restAggregates := by
  induction restAggregates with
  | nil =>
      have aggregateIsHead : aggregate = headAggregate := by
        simpa using aggregateMem
      rw [aggregateIsHead]
      exact le_refl _
  | cons nextAggregate furtherAggregates inductiveStep =>
      have unfoldFold : rhoGStar headAggregate
            (nextAggregate :: furtherAggregates)
          = max nextAggregate.ratio
              (rhoGStar headAggregate furtherAggregates) := rfl
      rw [unfoldFold]
      rcases List.mem_cons.mp aggregateMem with aggregateIsHead | aggregateInTail
      · refine le_trans (inductiveStep ?_) (le_max_right _ _)
        exact List.mem_cons.mpr (Or.inl aggregateIsHead)
      · rcases List.mem_cons.mp aggregateInTail with aggregateIsNext | deeper
        · rw [aggregateIsNext]
          exact le_max_left _ _
        · refine le_trans (inductiveStep ?_) (le_max_right _ _)
          exact List.mem_cons.mpr (Or.inr deeper)

/-- THE HEADLINE, guarded-candidate form: the sign package at a point opens
the collar window there, `rho_star(w) < rho_G*(w)`. -/
theorem windowIsOpenOfCandidate
    {headAggregate : GordanAggregateRecord K}
    {restAggregates : List (GordanAggregateRecord K)}
    {headRecord : ThroughTreeRecord K}
    {restRecords : List (ThroughTreeRecord K)}
    {aggregate : GordanAggregateRecord K} {record : ThroughTreeRecord K}
    {direction margin : K}
    (aggregateMem : aggregate ∈ headAggregate :: restAggregates)
    (recordMem : record ∈ headRecord :: restRecords)
    (recordIsValid : record.IsValidAt)
    (isAggregate : IsGordanAggregate aggregate)
    (directed : SlotsAreDirected aggregate.slots direction)
    (ratioNumIsNonzero : aggregate.ratioNum ≠ 0)
    (ratioDenIsNonzero : aggregate.ratioDen ≠ 0)
    (marginIsCross :
      margin = aggregate.ratioNum * record.thrDen
        - record.thrNum * aggregate.ratioDen)
    (marginSign : 0 < aggregate.ratioNum * record.thrDen * margin) :
    rhoStar headRecord restRecords < rhoGStar headAggregate restAggregates := by
  have _ := recordIsValid
  have thresholdLtRatio : record.threshold < aggregate.ratio :=
    thresholdLtRatioOfSignPackage isAggregate directed ratioNumIsNonzero
      ratioDenIsNonzero marginIsCross marginSign
  exact lt_of_le_of_lt (rhoStarLeThreshold recordMem)
    (lt_of_lt_of_le thresholdLtRatio (ratioLeRhoGStar aggregateMem))

/-- THE HEADLINE, free-win form: a valid through-tree with a negative
threshold opens the window against any in-cone aggregate. -/
theorem windowIsOpenOfFreeWin
    {headAggregate : GordanAggregateRecord K}
    {restAggregates : List (GordanAggregateRecord K)}
    {headRecord : ThroughTreeRecord K}
    {restRecords : List (ThroughTreeRecord K)}
    {aggregate : GordanAggregateRecord K} {record : ThroughTreeRecord K}
    {direction : K}
    (aggregateMem : aggregate ∈ headAggregate :: restAggregates)
    (recordMem : record ∈ headRecord :: restRecords)
    (recordIsValid : record.IsValidAt)
    (freeWin : record.thrNum * record.thrDen < 0)
    (isAggregate : IsGordanAggregate aggregate)
    (directed : SlotsAreDirected aggregate.slots direction)
    (ratioNumIsNonzero : aggregate.ratioNum ≠ 0)
    (ratioDenIsNonzero : aggregate.ratioDen ≠ 0) :
    rhoStar headRecord restRecords < rhoGStar headAggregate restAggregates := by
  have _ := recordIsValid
  have thresholdNegative : record.threshold < 0 :=
    thresholdIsNegativeOfFreeWin freeWin
  have ratioPositive : 0 < aggregate.ratio :=
    ratioIsPositive isAggregate directed ratioNumIsNonzero ratioDenIsNonzero
  have belowZero : rhoStar headRecord restRecords < 0 :=
    lt_of_le_of_lt (rhoStarLeThreshold recordMem) thresholdNegative
  have aboveZero : 0 < rhoGStar headAggregate restAggregates :=
    lt_of_lt_of_le ratioPositive (ratioLeRhoGStar aggregateMem)
  exact lt_trans belowZero aboveZero

/-! ## Homogeneous rescaling: the chart layer works with the homogenized
representatives, whose values at the integer point `(den, n1..n4)` differ
from the true weight-point values by a positive power of `den`.  All the
hypotheses above are sign conditions on products, and they are stable under
matched positive rescaling of numerator and denominator. -/

theorem signPackageIsRescalingStable {ratioNum ratioDen thrNum thrDen : K}
    {numeratorScale denominatorScale : K}
    (numeratorScalePos : 0 < numeratorScale)
    (denominatorScalePos : 0 < denominatorScale)
    (marginSign : 0 < ratioNum * thrDen
      * (ratioNum * thrDen - thrNum * ratioDen)) :
    0 < (numeratorScale * ratioNum) * (denominatorScale * thrDen)
      * ((numeratorScale * ratioNum) * (denominatorScale * thrDen)
        - (numeratorScale * thrNum) * (denominatorScale * ratioDen)) := by
  have direct :
      (numeratorScale * ratioNum) * (denominatorScale * thrDen)
        * ((numeratorScale * ratioNum) * (denominatorScale * thrDen)
          - (numeratorScale * thrNum) * (denominatorScale * ratioDen))
      = (numeratorScale * numeratorScale * (denominatorScale * denominatorScale))
        * (ratioNum * thrDen * (ratioNum * thrDen - thrNum * ratioDen)) := by
    ring
  rw [direct]
  exact mul_pos (mul_pos (mul_pos numeratorScalePos numeratorScalePos)
    (mul_pos denominatorScalePos denominatorScalePos)) marginSign

end OrderedField

end GtzCollarWindow
