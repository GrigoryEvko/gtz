import Gtz.Wave.OneLineWedgeFlatSplit

/-!
# The weak dominator, seeded: the flat-pair pinch on the two line classes

The two chartless registry residuals of the `(6, 3)` rank-three capstone,
`Gtz.OneLineTenthHeavyJointBlindLineSparse` and
`Gtz.TwoMeetingLinesTenthHeavyJointBlindTransversal`, both hand over a card-three
WEAK dominator and then never read it.  This module reads it.

Four things meet here.

* **The matroid split.**  A card-three subset of `Fin 6` either holds two labels
  of a line, or it is one of the four transversals of the two meeting lines.  The
  split is exact and it is decided.
* **The pair minor.**  A weak dominator whose first two members lie on a line has
  a NONNEGATIVE pair gap minor.  The landed producer needs the two atoms to be
  independent, and the line pattern supplies that independence through the open
  label, which lies on no line.
* **The cap.**  `Gtz.IsCapBlindSpot` bounds the very same minor from above.  The
  two bounds pinch it into an explicit interval.
* **The blind arm.**  At a positive minor the two corners are strictly heavy, so
  `Gtz.IsLinePairLiftBlindAt` fires and returns one polynomial inequality at
  EVERY label of the design.

The output is `Gtz.TwoMeetingLinesWeakSeed` and `Gtz.OneLineWeakSeed`, and the
two seeded residuals are proved EQUIVALENT to the registry formulas.  A prover of
either seeded form receives the whole pinch for free.

The transversal arm closes outright: a weak transversal with a nonvanishing gap
determinant IS a strict transversal, so that arm of the two-meeting-lines
residual is exactly one determinant sign.
-/

namespace Gtz

open Matrix

/-! ## 1. Cauchy-Schwarz in three slots, and the bracket cap

The pair Gram determinant of two vectors in `ℝ³` is the squared length of their
wedge, and the triple bracket is that wedge read against the third vector.  So
Cauchy-Schwarz caps the squared bracket by the pair Gram determinant times the
third leverage, and a nonzero bracket forces an independent pair. -/

/-- Cauchy-Schwarz on three coordinates, with the Lagrange remainder supplied as
three explicit squares. -/
theorem sq_sum_three_le_mul (leftZero leftOne leftTwo rightZero rightOne rightTwo : ℝ) :
    (leftZero * rightZero + leftOne * rightOne + leftTwo * rightTwo) ^ 2
      ≤ (leftZero ^ 2 + leftOne ^ 2 + leftTwo ^ 2)
        * (rightZero ^ 2 + rightOne ^ 2 + rightTwo ^ 2) := by
  nlinarith [sq_nonneg (leftZero * rightOne - leftOne * rightZero),
    sq_nonneg (leftZero * rightTwo - leftTwo * rightZero),
    sq_nonneg (leftOne * rightTwo - leftTwo * rightOne)]

/-- **THE BRACKET CAP.**  The squared triple bracket never exceeds the pair Gram
determinant of the first two vectors times the leverage of the third.  No
hypothesis, and the proof is the Lagrange identity followed by Cauchy-Schwarz. -/
theorem sq_tripleBracket_le_pairGramDet_mul_leverage (leftVec midVec rightVec : Fin 3 → ℝ) :
    tripleBracket leftVec midVec rightVec ^ 2
      ≤ (leverageOf leftVec * leverageOf midVec - (leftVec ⬝ᵥ midVec) ^ 2)
        * leverageOf rightVec := by
  have hleft : leverageOf leftVec = leftVec 0 ^ 2 + leftVec 1 ^ 2 + leftVec 2 ^ 2 := by
    simp only [leverageOf, Fin.sum_univ_three]
  have hmid : leverageOf midVec = midVec 0 ^ 2 + midVec 1 ^ 2 + midVec 2 ^ 2 := by
    simp only [leverageOf, Fin.sum_univ_three]
  have hright : leverageOf rightVec = rightVec 0 ^ 2 + rightVec 1 ^ 2 + rightVec 2 ^ 2 := by
    simp only [leverageOf, Fin.sum_univ_three]
  have hcross : leftVec ⬝ᵥ midVec
      = leftVec 0 * midVec 0 + leftVec 1 * midVec 1 + leftVec 2 * midVec 2 := by
    simp only [dotProduct, Fin.sum_univ_three]
  have hgram : leverageOf leftVec * leverageOf midVec - (leftVec ⬝ᵥ midVec) ^ 2
      = (leftVec 1 * midVec 2 - leftVec 2 * midVec 1) ^ 2
        + (leftVec 2 * midVec 0 - leftVec 0 * midVec 2) ^ 2
        + (leftVec 0 * midVec 1 - leftVec 1 * midVec 0) ^ 2 := by
    rw [hleft, hmid, hcross]
    ring
  have hbracket : tripleBracket leftVec midVec rightVec
      = (leftVec 1 * midVec 2 - leftVec 2 * midVec 1) * rightVec 0
        + (leftVec 2 * midVec 0 - leftVec 0 * midVec 2) * rightVec 1
        + (leftVec 0 * midVec 1 - leftVec 1 * midVec 0) * rightVec 2 := by
    rw [tripleBracket_eq]
    ring
  rw [hgram, hbracket, hright]
  exact sq_sum_three_le_mul _ _ _ _ _ _

/-! ## 2. The line pattern supplies pairwise independence

A line family that misses a label cannot make any bracket through that label
vanish.  So the open label certifies every pair of the design as independent, and
the flat-pair producers of section 10 of `Gtz.Wave.OneLineWedgeFlatSplit` lose
their only side condition. -/

/-- **THE OPEN LABEL KILLS EVERY BRACKET THROUGH IT.**  If no line of the family
holds the open label, then no bracket ending at it vanishes. -/
theorem atomBracket_ne_zero_of_hasLinePattern_of_open {size : ℕ}
    (design : WeightedDesign size 3) {lines : List (List (Fin size))}
    (hpattern : HasLinePattern design (lineFamilyPattern lines))
    {leftLabel midLabel openLabel : Fin size}
    (hopen : ∀ line ∈ lines, openLabel ∉ line)
    (hLeftMid : leftLabel ≠ midLabel) (hLeftOpen : leftLabel ≠ openLabel)
    (hMidOpen : midLabel ≠ openLabel) :
    atomBracket design leftLabel midLabel openLabel ≠ 0 := by
  intro hzero
  obtain ⟨line, hline, -, -, hmem⟩ :=
    (hpattern leftLabel midLabel openLabel hLeftMid hLeftOpen hMidOpen).mp hzero
  exact hopen line hline hmem

/-- **THE PATTERN FORCES AN INDEPENDENT PAIR.**  With an open label off every
line, the pair Gram determinant of any two other labels is strictly positive.
This is the independence side condition of the weak flat-pair producer, and the
line pattern pays it. -/
theorem pairGramDet_pos_of_hasLinePattern_of_open {size : ℕ}
    (design : WeightedDesign size 3) {lines : List (List (Fin size))}
    (hpattern : HasLinePattern design (lineFamilyPattern lines))
    {leftLabel midLabel openLabel : Fin size}
    (hopen : ∀ line ∈ lines, openLabel ∉ line)
    (hLeftMid : leftLabel ≠ midLabel) (hLeftOpen : leftLabel ≠ openLabel)
    (hMidOpen : midLabel ≠ openLabel) :
    0 < leverageOf (design.atom leftLabel) * leverageOf (design.atom midLabel)
      - gapPairingOf design leftLabel midLabel ^ 2 := by
  have hbracket := atomBracket_ne_zero_of_hasLinePattern_of_open design hpattern hopen
    hLeftMid hLeftOpen hMidOpen
  have hcap := sq_tripleBracket_le_pairGramDet_mul_leverage (design.atom leftLabel)
    (design.atom midLabel) (design.atom openLabel)
  have hbracketVec : tripleBracket (design.atom leftLabel) (design.atom midLabel)
      (design.atom openLabel) ≠ 0 := hbracket
  have hsq : 0 < tripleBracket (design.atom leftLabel) (design.atom midLabel)
      (design.atom openLabel) ^ 2 :=
    lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hbracketVec))
  have hlev : 0 ≤ leverageOf (design.atom openLabel) := by
    unfold leverageOf
    positivity
  have hgap : gapPairingOf design leftLabel midLabel
      = design.atom leftLabel ⬝ᵥ design.atom midLabel := rfl
  rw [hgap]
  by_contra hnonpos
  push Not at hnonpos
  nlinarith [hcap, hsq, hlev,
    mul_nonneg (neg_nonneg.mpr hnonpos) hlev]

/-! ## 3. The matroid split of a card-three subset

Two decided statements.  On one three-point line a card-three subset meets the
line in three, two, one or zero labels.  On two meeting lines a card-three subset
either holds a flat pair on one of them, or it is one of the four transversals,
and nothing else is possible. -/

/-- The open label of the one-line class lies on no line. -/
theorem oneLine_open_three : ∀ line ∈ [[(0 : Fin 6), 1, 2]], (3 : Fin 6) ∉ line := by decide

/-- The open label of the two-meeting-lines class lies on no line. -/
theorem twoMeetingLines_open_five :
    ∀ line ∈ [[(0 : Fin 6), 1, 2], [0, 3, 4]], (5 : Fin 6) ∉ line := by decide

/-- No label of the first line is the two-meeting-lines open label. -/
theorem lineOne_mem_ne_five :
    ∀ label : Fin 6, label ∈ ({0, 1, 2} : Finset (Fin 6)) → label ≠ 5 := by decide

/-- No label of the second line is the two-meeting-lines open label. -/
theorem lineTwo_mem_ne_five :
    ∀ label : Fin 6, label ∈ ({0, 3, 4} : Finset (Fin 6)) → label ≠ 5 := by decide

/-- No label of the one-line set is the one-line open label. -/
theorem lineOne_mem_ne_three :
    ∀ label : Fin 6, label ∈ ({0, 1, 2} : Finset (Fin 6)) → label ≠ 3 := by decide

set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 40000 in
/-- **THE ONE-LINE SPLIT, DECIDED.**  A card-three subset of `Fin 6` is the line
itself, or it holds a flat pair and one free label, or it holds one line label and
a free pair, or it is the free triple.  The four cases are exhaustive. -/
theorem oneLine_cardThree_split (selected : Finset (Fin 6)) (hcard : selected.card = 3) :
    selected = ({0, 1, 2} : Finset (Fin 6))
      ∨ (∃ pairFirst ∈ selected, ∃ pairSecond ∈ selected, ∃ freeLabel ∈ selected,
          selected = {pairFirst, pairSecond, freeLabel}
            ∧ pairFirst ≠ pairSecond ∧ pairFirst ≠ freeLabel ∧ pairSecond ≠ freeLabel
            ∧ pairFirst ∈ ({0, 1, 2} : Finset (Fin 6))
            ∧ pairSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
      ∨ (∃ lineLabel ∈ selected, ∃ freeFirst ∈ selected, ∃ freeSecond ∈ selected,
          selected = {lineLabel, freeFirst, freeSecond}
            ∧ lineLabel ≠ freeFirst ∧ lineLabel ≠ freeSecond ∧ freeFirst ≠ freeSecond
            ∧ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6))
            ∧ freeFirst ∈ ({3, 4, 5} : Finset (Fin 6))
            ∧ freeSecond ∈ ({3, 4, 5} : Finset (Fin 6)))
      ∨ selected = ({3, 4, 5} : Finset (Fin 6)) := by
  revert hcard
  revert selected
  decide

set_option synthInstance.maxSize 4000 in
set_option synthInstance.maxHeartbeats 1000000 in
set_option maxRecDepth 40000 in
/-- **THE TWO-MEETING-LINES SPLIT, DECIDED.**  A card-three subset of `Fin 6`
holds two labels of the first line, or two labels of the second line, or it is one
of the four transversals.  The four transversals are exactly the subsets with no
flat pair, because a subset that avoids both flat pairs must exclude the shared
label, include the open label, and take one private label from each line.  The
three arms hold ten, six and four of the twenty subsets. -/
theorem twoMeetingLines_cardThree_split (selected : Finset (Fin 6))
    (hcard : selected.card = 3) :
    (∃ pairFirst ∈ selected, ∃ pairSecond ∈ selected, ∃ freeLabel ∈ selected,
        selected = {pairFirst, pairSecond, freeLabel}
          ∧ pairFirst ≠ pairSecond ∧ pairFirst ≠ freeLabel ∧ pairSecond ≠ freeLabel
          ∧ pairFirst ∈ ({0, 1, 2} : Finset (Fin 6))
          ∧ pairSecond ∈ ({0, 1, 2} : Finset (Fin 6)))
      ∨ (∃ pairFirst ∈ selected, ∃ pairSecond ∈ selected, ∃ freeLabel ∈ selected,
        selected = {pairFirst, pairSecond, freeLabel}
          ∧ pairFirst ≠ pairSecond ∧ pairFirst ≠ freeLabel ∧ pairSecond ≠ freeLabel
          ∧ pairFirst ∈ ({0, 3, 4} : Finset (Fin 6))
          ∧ pairSecond ∈ ({0, 3, 4} : Finset (Fin 6)))
      ∨ selected = ({1, 3, 5} : Finset (Fin 6)) ∨ selected = ({1, 4, 5} : Finset (Fin 6))
      ∨ selected = ({2, 3, 5} : Finset (Fin 6)) ∨ selected = ({2, 4, 5} : Finset (Fin 6)) := by
  revert hcard
  revert selected
  decide

/-! ## 4. The line itself never dominates

The count-three case of the one-line split is refused outright.  Three coplanar
atoms leave the common normal uncovered, so their sum never reaches the
identity. -/

/-- A unit vector is nonzero. -/
theorem ne_zero_of_dotProduct_self_eq_one {rank : ℕ} {probe : Fin rank → ℝ}
    (hunit : probe ⬝ᵥ probe = 1) : probe ≠ 0 := by
  intro hzero
  rw [hzero] at hunit
  simp at hunit

/-- **THE LINE IS NOT A DOMINATOR.**  No weak card-three dominator equals the
three-point line, because the line's common normal reads zero at every member. -/
theorem oneLine_dominator_ne_lineSet (design : WeightedDesign 6 3)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {selected : Finset (Fin 6)} (hdominates : Dominates design selected) :
    selected ≠ ({0, 1, 2} : Finset (Fin 6)) := by
  intro hequal
  subst hequal
  exact not_dominates_of_coplanar_triple design (Finset.Subset.refl _) (le_refl _)
    unitNormal (ne_zero_of_dotProduct_self_eq_one hunit) hlineFlat hdominates

/-! ## 5. A positive pair minor forces two strictly heavy corners

Heaviness supplies only `1 ≤ leverageOf`, so both gap excesses are nonnegative.
A positive pair minor then forces their product above a square, and a nonnegative
factor with positive product is itself positive. -/

/-- **THE MINOR CARRIES THE CORNERS.**  Under heaviness a positive pair gap minor
makes both of its atoms STRICTLY heavy.  This is the missing strictness that the
lift criterion's first guard asks for. -/
theorem pos_heavyExcess_of_pos_pairGapExcessOf {size : ℕ} (design : WeightedDesign size 3)
    (hheavy : ∀ label : Fin size, 1 ≤ leverageOf (design.atom label))
    (pairFirst pairSecond : Fin size)
    (hminor : 0 < pairGapExcessOf design pairFirst pairSecond) :
    0 < heavyExcess design pairFirst ∧ 0 < heavyExcess design pairSecond := by
  have hfirst : 0 ≤ heavyExcess design pairFirst := by
    have hlev := hheavy pairFirst
    unfold heavyExcess
    linarith
  have hsecond : 0 ≤ heavyExcess design pairSecond := by
    have hlev := hheavy pairSecond
    unfold heavyExcess
    linarith
  have hexpand : pairGapExcessOf design pairFirst pairSecond
      = heavyExcess design pairFirst * heavyExcess design pairSecond
        - gapPairingOf design pairFirst pairSecond ^ 2 := by
    unfold pairGapExcessOf gapExcessOf heavyExcess
    ring
  rw [hexpand] at hminor
  refine ⟨?_, ?_⟩
  · nlinarith [sq_nonneg (gapPairingOf design pairFirst pairSecond), hfirst, hsecond, hminor]
  · nlinarith [sq_nonneg (gapPairingOf design pairFirst pairSecond), hfirst, hsecond, hminor]

/-! ## 5b. The degenerate leg is rigid

A vanishing pair gap minor is not a dead end.  It splits again on the first
corner.  A strictly heavy corner pins the third atom onto the pair's first-touch
plane, and that plane already holds the line normal.  A corner that is not
strictly heavy sits at UNIT leverage, and a unit-leverage label joins no strict
dominator at all. -/

/-- A card-three literal, rotated.  Finset literals are ordered notation, and the
first-touch producers read the pivot in the first slot. -/
theorem triple_rotate {index : Type*} [DecidableEq index] (first second third : index) :
    ({first, second, third} : Finset index) = {third, first, second} := by
  ext label
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **THE FIRST-TOUCH NORMAL OF A FLAT PAIR LIES IN THE LINE PLANE.**  It is a
combination of the two atoms, and each of them reads the line normal at zero. -/
theorem firstTouchNormal_dotProduct_normal_eq_zero {size : ℕ}
    (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond : Fin size)
    (hFirstFlat : design.atom pairFirst ⬝ᵥ normalVec = 0)
    (hSecondFlat : design.atom pairSecond ⬝ᵥ normalVec = 0) :
    firstTouchNormal design pairFirst pairSecond ⬝ᵥ normalVec = 0 := by
  rw [firstTouchNormal_dotProduct, hFirstFlat, hSecondFlat]
  ring

/-- **THE DEGENERATE LEG PINS THE THIRD ATOM.**  At a vanishing flat-pair minor
with a strictly heavy first corner, the weak dominator's third atom lies on the
first-touch plane of the pair.  That plane already holds the line normal, so the
third atom is confined to a plane the pair alone fixes. -/
theorem freeAtom_on_firstTouchPlane_of_boundary {size : ℕ} (design : WeightedDesign size 3)
    (normalVec : Fin 3 → ℝ) {pairFirst pairSecond freeLabel : Fin size}
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstFree : pairFirst ≠ freeLabel)
    (hSecondFree : pairSecond ≠ freeLabel)
    (hFirstFlat : design.atom pairFirst ⬝ᵥ normalVec = 0)
    (hSecondFlat : design.atom pairSecond ⬝ᵥ normalVec = 0)
    (hheavyFirst : 0 < heavyExcess design pairFirst)
    (hboundary : pairGapExcessOf design pairFirst pairSecond = 0)
    (hdominates : Dominates design {pairFirst, pairSecond, freeLabel}) :
    firstTouchNormal design pairFirst pairSecond ⬝ᵥ design.atom freeLabel = 0
      ∧ firstTouchNormal design pairFirst pairSecond ⬝ᵥ normalVec = 0 := by
  refine ⟨?_, firstTouchNormal_dotProduct_normal_eq_zero design normalVec pairFirst pairSecond
    hFirstFlat hSecondFlat⟩
  refine firstTouchNormal_dotProduct_eq_zero_of_dominates design hFirstFree.symm
    hSecondFree.symm hFirstSecond hheavyFirst hboundary ?_
  rwa [triple_rotate] at hdominates

/-- **A UNIT-LEVERAGE LABEL JOINS NO STRICT DOMINATOR.**  Every member of a strict
card-three dominator is strictly heavy, so one label at unit leverage poisons every
subset that holds it. -/
theorem not_posDef_of_mem_of_leverage_eq_one {size : ℕ} (design : WeightedDesign size 3)
    {selected : Finset (Fin size)} (hcard : selected.card = 3)
    {unitLabel : Fin size} (hmem : unitLabel ∈ selected)
    (hunitLeverage : leverageOf (design.atom unitLabel) = 1) :
    ¬ (subsetSum design selected - 1).PosDef := by
  intro hposDef
  have hstrict := one_lt_leverage_of_mem_of_posDef design selected hcard hmem hposDef
  rw [hunitLeverage] at hstrict
  exact lt_irrefl 1 hstrict

/-- **THE LIGHT CORNER OF A DEGENERATE MINOR IS A UNIT-LEVERAGE LABEL.**  Under
heaviness a vanishing pair minor whose first corner is not strictly heavy forces
that corner to unit leverage AND the two atoms to be orthogonal. -/
theorem unitLeverage_and_orthogonal_of_boundary {size : ℕ} (design : WeightedDesign size 3)
    (pairFirst pairSecond : Fin size)
    (hboundary : pairGapExcessOf design pairFirst pairSecond = 0)
    (hlight : heavyExcess design pairFirst = 0) :
    leverageOf (design.atom pairFirst) = 1
      ∧ design.atom pairFirst ⬝ᵥ design.atom pairSecond = 0 := by
  have hlev : leverageOf (design.atom pairFirst) = 1 := by
    unfold heavyExcess at hlight
    linarith
  refine ⟨hlev, ?_⟩
  have hexpand : pairGapExcessOf design pairFirst pairSecond
      = heavyExcess design pairFirst * heavyExcess design pairSecond
        - gapPairingOf design pairFirst pairSecond ^ 2 := by
    unfold pairGapExcessOf gapExcessOf heavyExcess
    ring
  rw [hexpand, hlight, zero_mul, zero_sub, neg_eq_zero] at hboundary
  have hgap : gapPairingOf design pairFirst pairSecond
      = design.atom pairFirst ⬝ᵥ design.atom pairSecond := rfl
  rw [← hgap]
  exact sq_eq_zero_iff.mp hboundary

/-! ## 6. The shadow bridge

`Gtz.shadowGapDeterminant_eq_pairGapExcessOf_of_flatPair` translates the lift
criterion's shadow vocabulary into the Gram vocabulary at a flat pair.  Read
through it, the weak flat-pair producer becomes a statement about the criterion's
own second guard. -/

/-- **THE WEAK SHADOW GUARD.**  A weak card-three dominator whose first two
members are flat against a unit normal has a NONNEGATIVE shadow-gap determinant.
This is the weak counterpart of `Gtz.shadowGap_pos_of_posDef_tripleGap_of_flatPair`,
and it needs no strict domination anywhere. -/
theorem shadowGapDeterminant_nonneg_of_dominates_flatPair {size : ℕ}
    (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    {flatFirst flatSecond freeLabel : Fin size}
    (hFirstSecond : flatFirst ≠ flatSecond) (hFirstFree : flatFirst ≠ freeLabel)
    (hSecondFree : flatSecond ≠ freeLabel)
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hFirstFlat : design.atom flatFirst ⬝ᵥ normalVec = 0)
    (hSecondFlat : design.atom flatSecond ⬝ᵥ normalVec = 0)
    (hindependent : 0 < leverageOf (design.atom flatFirst) * leverageOf (design.atom flatSecond)
      - gapPairingOf design flatFirst flatSecond ^ 2)
    (hdominates : Dominates design {flatFirst, flatSecond, freeLabel}) :
    0 ≤ shadowGapDeterminant design normalVec flatFirst flatSecond := by
  have hFirstReading : normalReading design normalVec flatFirst = 0 := hFirstFlat
  have hSecondReading : normalReading design normalVec flatSecond = 0 := hSecondFlat
  rw [shadowGapDeterminant_eq_pairGapExcessOf_of_flatPair design normalVec flatFirst flatSecond
    hFirstReading hSecondReading]
  exact pairGapExcessOf_nonneg_of_dominates_flatPair design hFirstSecond hFirstFree hSecondFree
    normalVec hunit hFirstFlat hSecondFlat hindependent hdominates

/-! ## 7. The blind arm

Blindness is a negated conjunction.  With the first two conjuncts in hand the
third is refused, and the refusal is one polynomial inequality per third
label. -/

/-- **THE BLIND SPOT PAYS AN INEQUALITY.**  Where the lift criterion is blind
along the pairs of a line, a live pair forces its lift leverage above the third
label's squared normal reading times the shadow-gap determinant.  The label is
arbitrary, so ONE live pair returns a family of inequalities. -/
theorem liftLeverage_ge_of_linePairLiftBlindAt (design : WeightedDesign 6 3)
    {normalVec : Fin 3 → ℝ} {lineTriple : Finset (Fin 6)}
    (hblind : IsLinePairLiftBlindAt design normalVec lineTriple)
    {pairFirst pairSecond thirdLabel : Fin 6}
    (hFirstMem : pairFirst ∈ lineTriple) (hSecondMem : pairSecond ∈ lineTriple)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hcorner : 0 < shadowPairing design normalVec pairFirst pairFirst - 1)
    (hminor : 0 < shadowGapDeterminant design normalVec pairFirst pairSecond) :
    normalReading design normalVec thirdLabel ^ 2
        * shadowGapDeterminant design normalVec pairFirst pairSecond
      ≤ liftLeverage design normalVec pairFirst pairSecond thirdLabel := by
  by_contra hstrict
  push Not at hstrict
  exact hblind pairFirst hFirstMem pairSecond hSecondMem thirdLabel hFirstSecond hFirstThird
    hSecondThird ⟨hcorner, hminor, hstrict⟩

/-! ## 8. The cap, and the pinch

`Gtz.IsCapBlindSpot` is written in the `heavyExcess` and `atomPairing` vocabulary.
That vocabulary and the `gapExcessOf` and `gapPairingOf` vocabulary name the same
two scalars, so the cap reads directly on the pair gap minor. -/

/-- **THE CAP READS THE PAIR MINOR.**  The pair-cap blind spot is a ceiling on the
pair gap minor, written in the Gram vocabulary. -/
theorem pairGapExcessOf_le_of_capBlindSpot {size : ℕ} (design : WeightedDesign size 3)
    (hcapBlind : IsCapBlindSpot design) {pairFirst pairSecond : Fin size}
    (hdistinct : pairFirst ≠ pairSecond) :
    2 * (design.weight pairFirst + design.weight pairSecond)
        * pairGapExcessOf design pairFirst pairSecond
      ≤ (1 - design.weight pairSecond) * heavyExcess design pairFirst
        + (1 - design.weight pairFirst) * heavyExcess design pairSecond := by
  have hcap := hcapBlind pairFirst pairSecond hdistinct
  have hexpand : pairGapExcessOf design pairFirst pairSecond
      = heavyExcess design pairFirst * heavyExcess design pairSecond
        - atomPairing design pairFirst pairSecond ^ 2 := by
    unfold pairGapExcessOf gapExcessOf gapPairingOf heavyExcess atomPairing
    ring
  rw [hexpand]
  exact hcap

/-- **THE PINCH.**  The pair gap minor of a pair, bounded below by zero and above
by the cap.  The two bounds together confine it to an explicit interval whose
width is decided by the two weights and the two gap excesses. -/
def PairGapExcessPinch {size : ℕ} (design : WeightedDesign size 3)
    (pairFirst pairSecond : Fin size) : Prop :=
  0 ≤ pairGapExcessOf design pairFirst pairSecond
    ∧ 2 * (design.weight pairFirst + design.weight pairSecond)
          * pairGapExcessOf design pairFirst pairSecond
        ≤ (1 - design.weight pairSecond) * heavyExcess design pairFirst
          + (1 - design.weight pairFirst) * heavyExcess design pairSecond

/-- **THE THREE LEGS OF A FLAT PAIR.**  A flat pair inside a weak dominator
occupies one of three positions, and each leg carries its own rigidity.

* The LIVE leg has a positive minor.  Blindness then pays one polynomial
  inequality at EVERY label of the design.
* The PINNED leg has a degenerate minor and a strictly heavy corner.  The third
  atom lies on the pair's first-touch plane, and the line normal lies there too.
* The UNIT leg has a light corner.  That corner sits at unit leverage, the two
  atoms are orthogonal, and the corner joins NO strict card-three dominator. -/
def FlatPairTrichotomy (design : WeightedDesign 6 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond freeLabel : Fin 6) : Prop :=
  (0 < pairGapExcessOf design pairFirst pairSecond
      ∧ ∀ thirdLabel : Fin 6, pairFirst ≠ thirdLabel → pairSecond ≠ thirdLabel →
          normalReading design normalVec thirdLabel ^ 2
              * pairGapExcessOf design pairFirst pairSecond
            ≤ liftLeverage design normalVec pairFirst pairSecond thirdLabel)
    ∨ (pairGapExcessOf design pairFirst pairSecond = 0
      ∧ 0 < heavyExcess design pairFirst
      ∧ firstTouchNormal design pairFirst pairSecond ⬝ᵥ design.atom freeLabel = 0
      ∧ firstTouchNormal design pairFirst pairSecond ⬝ᵥ normalVec = 0)
    ∨ (leverageOf (design.atom pairFirst) = 1
      ∧ design.atom pairFirst ⬝ᵥ design.atom pairSecond = 0
      ∧ ∀ selected : Finset (Fin 6), selected.card = 3 → pairFirst ∈ selected →
          ¬ (subsetSum design selected - 1).PosDef)

/-- The pinch, with the trichotomy attached.  The pair minor lies in the pinched
interval, and the pair occupies one of the three legs. -/
def FlatPairBlindPinch (design : WeightedDesign 6 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond : Fin 6) : Prop :=
  PairGapExcessPinch design pairFirst pairSecond
    ∧ ∃ freeLabel : Fin 6, pairFirst ≠ freeLabel ∧ pairSecond ≠ freeLabel
        ∧ FlatPairTrichotomy design normalVec pairFirst pairSecond freeLabel

/-! ## 9. The flat-pair core

Everything above meets here.  The pattern pays independence, the weak producer
pays the floor, the cap pays the ceiling, and a positive minor opens the blind
arm. -/

/-- **THE FLAT-PAIR SEED.**  A weak card-three dominator whose first two members
lie on a line of the pattern returns a pinched pair minor and, at a nondegenerate
minor, one inequality at every label.  No strict domination is assumed anywhere,
and the only geometric input is the open label. -/
theorem flatPairBlindPinch_of_dominates (design : WeightedDesign 6 3)
    {lines : List (List (Fin 6))}
    (hpattern : HasLinePattern design (lineFamilyPattern lines))
    (hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (hcapBlind : IsCapBlindSpot design)
    {openLabel : Fin 6} (hopen : ∀ line ∈ lines, openLabel ∉ line)
    {normalVec : Fin 3 → ℝ} {lineSet : Finset (Fin 6)}
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ lineLabel ∈ lineSet, design.atom lineLabel ⬝ᵥ normalVec = 0)
    (hblind : IsLinePairLiftBlindAt design normalVec lineSet)
    {pairFirst pairSecond freeLabel : Fin 6}
    (hFirstMem : pairFirst ∈ lineSet) (hSecondMem : pairSecond ∈ lineSet)
    (hFirstOpen : pairFirst ≠ openLabel) (hSecondOpen : pairSecond ≠ openLabel)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstFree : pairFirst ≠ freeLabel)
    (hSecondFree : pairSecond ≠ freeLabel)
    (hdominates : Dominates design {pairFirst, pairSecond, freeLabel}) :
    FlatPairBlindPinch design normalVec pairFirst pairSecond := by
  have hFirstFlat : design.atom pairFirst ⬝ᵥ normalVec = 0 := hflat pairFirst hFirstMem
  have hSecondFlat : design.atom pairSecond ⬝ᵥ normalVec = 0 := hflat pairSecond hSecondMem
  have hFirstReading : normalReading design normalVec pairFirst = 0 := hFirstFlat
  have hSecondReading : normalReading design normalVec pairSecond = 0 := hSecondFlat
  have hindependent := pairGramDet_pos_of_hasLinePattern_of_open design hpattern hopen
    hFirstSecond hFirstOpen hSecondOpen
  have hfloor : 0 ≤ pairGapExcessOf design pairFirst pairSecond :=
    pairGapExcessOf_nonneg_of_dominates_flatPair design hFirstSecond hFirstFree hSecondFree
      normalVec hunit hFirstFlat hSecondFlat hindependent hdominates
  have hceiling := pairGapExcessOf_le_of_capBlindSpot design hcapBlind hFirstSecond
  refine ⟨⟨hfloor, hceiling⟩, freeLabel, hFirstFree, hSecondFree, ?_⟩
  rcases eq_or_lt_of_le hfloor with hzero | hpos
  · have hboundary : pairGapExcessOf design pairFirst pairSecond = 0 := hzero.symm
    have hexcessNonneg : 0 ≤ heavyExcess design pairFirst := by
      have hlev := hheavy pairFirst
      unfold heavyExcess
      linarith
    rcases eq_or_lt_of_le hexcessNonneg with hlight | hheavyFirst
    · obtain ⟨hlev, horth⟩ := unitLeverage_and_orthogonal_of_boundary design pairFirst
        pairSecond hboundary hlight.symm
      exact Or.inr (Or.inr ⟨hlev, horth, fun selected hcard hmem =>
        not_posDef_of_mem_of_leverage_eq_one design hcard hmem hlev⟩)
    · obtain ⟨hpin, hplane⟩ := freeAtom_on_firstTouchPlane_of_boundary design normalVec
        hFirstSecond hFirstFree hSecondFree hFirstFlat hSecondFlat hheavyFirst hboundary
        hdominates
      exact Or.inr (Or.inl ⟨hboundary, hheavyFirst, hpin, hplane⟩)
  · refine Or.inl ⟨hpos, fun thirdLabel hFirstThird hSecondThird => ?_⟩
    have hcorner : 0 < shadowPairing design normalVec pairFirst pairFirst - 1 := by
      rw [shadowPairing_self_eq_leverageOf_of_normalReading_eq_zero design normalVec pairFirst
        hFirstReading]
      have hheavyFirst :=
        (pos_heavyExcess_of_pos_pairGapExcessOf design hheavy pairFirst pairSecond hpos).1
      unfold heavyExcess at hheavyFirst
      linarith
    have hminor : 0 < shadowGapDeterminant design normalVec pairFirst pairSecond := by
      rw [shadowGapDeterminant_eq_pairGapExcessOf_of_flatPair design normalVec pairFirst
        pairSecond hFirstReading hSecondReading]
      exact hpos
    have hlift := liftLeverage_ge_of_linePairLiftBlindAt design hblind hFirstMem hSecondMem
      hFirstSecond hFirstThird hSecondThird hcorner hminor
    rwa [shadowGapDeterminant_eq_pairGapExcessOf_of_flatPair design normalVec pairFirst
      pairSecond hFirstReading hSecondReading] at hlift

/-! ## 10. The transversal arm closes on one determinant

A weak dominator that already IS a transversal needs only a nonvanishing gap
determinant to become the strict transversal the residual asks for.  So that
whole arm of the two-meeting-lines residual is one polynomial sign. -/

/-- **THE TRANSVERSAL ARM IS ONE DETERMINANT SIGN.**  A weakly dominating
transversal with a nonzero gap determinant dominates STRICTLY, and it is one of
the four disjuncts the residual names. -/
theorem twoMeetingLinesTransversalStrict_of_weakTransversal
    (design : WeightedDesign 6 3) {transversal : Finset (Fin 6)}
    (hnamed : transversal = ({1, 3, 5} : Finset (Fin 6))
      ∨ transversal = ({1, 4, 5} : Finset (Fin 6))
      ∨ transversal = ({2, 3, 5} : Finset (Fin 6))
      ∨ transversal = ({2, 4, 5} : Finset (Fin 6)))
    (hdominates : Dominates design transversal)
    (hdet : (subsetSum design transversal - 1).det ≠ 0) :
    TwoMeetingLinesTransversalStrict design := by
  have hposDef := hdominates.posDef_iff_det_ne_zero.mpr hdet
  rcases hnamed with hcase | hcase | hcase | hcase
  · exact Or.inl (by rwa [hcase] at hposDef)
  · exact Or.inr (Or.inl (by rwa [hcase] at hposDef))
  · exact Or.inr (Or.inr (Or.inl (by rwa [hcase] at hposDef)))
  · exact Or.inr (Or.inr (Or.inr (by rwa [hcase] at hposDef)))

/-! ## 11. The two-meeting-lines seed

The split of section 3 sends the weak dominator to one of three places.  Two of
them are flat pairs and receive the whole pinch.  The third is a weakly
dominating transversal, which section 10 turns into one determinant sign. -/

/-- **WHAT A WEAK DOMINATOR LEAVES ON TWO MEETING LINES.**  Either a pinched flat
pair on the first line, or a pinched flat pair on the second line, or a weakly
dominating transversal. -/
def TwoMeetingLinesWeakSeed (design : WeightedDesign 6 3)
    (normalFirst normalSecond : Fin 3 → ℝ) : Prop :=
  (∃ pairFirst ∈ ({0, 1, 2} : Finset (Fin 6)), ∃ pairSecond ∈ ({0, 1, 2} : Finset (Fin 6)),
      pairFirst ≠ pairSecond ∧ FlatPairBlindPinch design normalFirst pairFirst pairSecond)
    ∨ (∃ pairFirst ∈ ({0, 3, 4} : Finset (Fin 6)), ∃ pairSecond ∈ ({0, 3, 4} : Finset (Fin 6)),
      pairFirst ≠ pairSecond ∧ FlatPairBlindPinch design normalSecond pairFirst pairSecond)
    ∨ (∃ transversal : Finset (Fin 6),
      (transversal = ({1, 3, 5} : Finset (Fin 6))
        ∨ transversal = ({1, 4, 5} : Finset (Fin 6))
        ∨ transversal = ({2, 3, 5} : Finset (Fin 6))
        ∨ transversal = ({2, 4, 5} : Finset (Fin 6)))
      ∧ Dominates design transversal)

/-- **THE SEED PRODUCER.**  Every card-three weak dominator of a two-meeting-lines
design leaves the seed.  This is the whole content of the residual's weak
antecedent, and until this theorem the antecedent had no consumer. -/
theorem twoMeetingLines_weakSeed_of_dominates (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]))
    (hheavy : ∀ label : Fin 6, 1 ≤ leverageOf (design.atom label))
    (hcapBlind : IsCapBlindSpot design)
    {normalFirst normalSecond : Fin 3 → ℝ}
    (hunitFirst : normalFirst ⬝ᵥ normalFirst = 1)
    (hunitSecond : normalSecond ⬝ᵥ normalSecond = 1)
    (hflatFirst : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalFirst = 0)
    (hflatSecond : ∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalSecond = 0)
    (hblindFirst : IsLinePairLiftBlindAt design normalFirst ({0, 1, 2} : Finset (Fin 6)))
    (hblindSecond : IsLinePairLiftBlindAt design normalSecond ({0, 3, 4} : Finset (Fin 6)))
    {dominator : Finset (Fin 6)} (hcard : dominator.card = 3)
    (hdominates : Dominates design dominator) :
    TwoMeetingLinesWeakSeed design normalFirst normalSecond := by
  rcases twoMeetingLines_cardThree_split dominator hcard with
    hfirstLine | hsecondLine | htransversal
  · obtain ⟨pairFirst, -, pairSecond, -, freeLabel, -, hshape, hFirstSecond, hFirstFree,
      hSecondFree, hFirstMem, hSecondMem⟩ := hfirstLine
    refine Or.inl ⟨pairFirst, hFirstMem, pairSecond, hSecondMem, hFirstSecond, ?_⟩
    refine flatPairBlindPinch_of_dominates design hpattern hheavy hcapBlind
      twoMeetingLines_open_five hunitFirst hflatFirst hblindFirst hFirstMem hSecondMem
      (lineOne_mem_ne_five pairFirst hFirstMem) (lineOne_mem_ne_five pairSecond hSecondMem)
      hFirstSecond hFirstFree hSecondFree ?_
    rwa [hshape] at hdominates
  · obtain ⟨pairFirst, -, pairSecond, -, freeLabel, -, hshape, hFirstSecond, hFirstFree,
      hSecondFree, hFirstMem, hSecondMem⟩ := hsecondLine
    refine Or.inr (Or.inl ⟨pairFirst, hFirstMem, pairSecond, hSecondMem, hFirstSecond, ?_⟩)
    refine flatPairBlindPinch_of_dominates design hpattern hheavy hcapBlind
      twoMeetingLines_open_five hunitSecond hflatSecond hblindSecond hFirstMem hSecondMem
      (lineTwo_mem_ne_five pairFirst hFirstMem) (lineTwo_mem_ne_five pairSecond hSecondMem)
      hFirstSecond hFirstFree hSecondFree ?_
    rwa [hshape] at hdominates
  · exact Or.inr (Or.inr ⟨dominator, htransversal, hdominates⟩)

/-! ## 12. The seeded two-meeting-lines residual, and the registry bridge

The seeded residual carries the raw weak dominator AND the seed.  So it is
EQUIVALENT to the registry formula, and a prover of it receives the pinch, the
blind inequalities and the transversal arm for free. -/

/-- The two-meeting-lines residual with the seed attached to its antecedent. -/
def TwoMeetingLinesSeededTransversal : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) →
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
    (∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel) →
    IsCapBlindSpot design →
    (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
    ∀ normalFirst normalSecond : Fin 3 → ℝ,
      normalFirst ⬝ᵥ normalFirst = 1 → normalSecond ⬝ᵥ normalSecond = 1 →
      (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ normalFirst = 0) →
      (∀ lineLabel ∈ ({0, 3, 4} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ normalSecond = 0) →
      IsLinePairLiftBlindAt design normalFirst ({0, 1, 2} : Finset (Fin 6)) →
      IsLinePairLiftBlindAt design normalSecond ({0, 3, 4} : Finset (Fin 6)) →
      TwoMeetingLinesWeakSeed design normalFirst normalSecond →
      TwoMeetingLinesTransversalStrict design

/-- **THE SEEDED RESIDUAL CLOSES THE REGISTRY FORMULA.**  The seed is derived
from the antecedent, so no strength is added. -/
theorem twoMeetingLinesTenthHeavyJointBlindTransversal_of_seeded
    (hresidual : TwoMeetingLinesSeededTransversal) :
    TwoMeetingLinesTenthHeavyJointBlindTransversal := by
  intro design hpattern hheavy hweightHeavy hcapBlind hweak normalFirst normalSecond
    hunitFirst hunitSecond horthFirst horthSecond hblindFirst hblindSecond
  obtain ⟨dominator, hcard, hdominates⟩ := hweak
  exact hresidual design hpattern hheavy hweightHeavy hcapBlind ⟨dominator, hcard, hdominates⟩
    normalFirst normalSecond hunitFirst hunitSecond horthFirst horthSecond hblindFirst
    hblindSecond
    (twoMeetingLines_weakSeed_of_dominates design hpattern hheavy hcapBlind hunitFirst
      hunitSecond horthFirst horthSecond hblindFirst hblindSecond hcard hdominates)

/-- **THE CONVERSE.**  Dropping the seed recovers the seeded form, so the two
formulas are interderivable and the door carries no hidden vacuity. -/
theorem seeded_of_twoMeetingLinesTenthHeavyJointBlindTransversal
    (hresidual : TwoMeetingLinesTenthHeavyJointBlindTransversal) :
    TwoMeetingLinesSeededTransversal := by
  intro design hpattern hheavy hweightHeavy hcapBlind hweak normalFirst normalSecond
    hunitFirst hunitSecond horthFirst horthSecond hblindFirst hblindSecond _hseed
  exact hresidual design hpattern hheavy hweightHeavy hcapBlind hweak normalFirst normalSecond
    hunitFirst hunitSecond horthFirst horthSecond hblindFirst hblindSecond

/-- **THE TWO-MEETING-LINES DOOR IS EXACT.** -/
theorem twoMeetingLinesSeededTransversal_iff :
    TwoMeetingLinesSeededTransversal ↔ TwoMeetingLinesTenthHeavyJointBlindTransversal :=
  ⟨twoMeetingLinesTenthHeavyJointBlindTransversal_of_seeded,
    seeded_of_twoMeetingLinesTenthHeavyJointBlindTransversal⟩

/-! ## 13. The one-line seed

The one-line residual carries no pair-lift blindness, so the blind arm is absent.
The split, the independence, the floor and the cap all survive, and the count-one
case pays the free pair's normal budget. -/

/-- **WHAT A WEAK DOMINATOR LEAVES ON ONE LINE.**  Either a pinched flat pair on
the line, or one line label with a free pair carrying the whole squared normal, or
the free triple itself.  The line is never a dominator, so the count-three case is
absent. -/
def OneLineWeakSeed (design : WeightedDesign 6 3) (unitNormal : Fin 3 → ℝ) : Prop :=
  (∃ pairFirst ∈ ({0, 1, 2} : Finset (Fin 6)), ∃ pairSecond ∈ ({0, 1, 2} : Finset (Fin 6)),
      pairFirst ≠ pairSecond ∧ PairGapExcessPinch design pairFirst pairSecond)
    ∨ (∃ freeFirst ∈ ({3, 4, 5} : Finset (Fin 6)), ∃ freeSecond ∈ ({3, 4, 5} : Finset (Fin 6)),
      freeFirst ≠ freeSecond
        ∧ 1 ≤ (design.atom freeFirst ⬝ᵥ unitNormal) ^ 2
            + (design.atom freeSecond ⬝ᵥ unitNormal) ^ 2)
    ∨ Dominates design ({3, 4, 5} : Finset (Fin 6))

/-- **THE ONE-LINE SEED PRODUCER.**  Every card-three weak dominator of a one-line
design leaves the seed. -/
theorem oneLine_weakSeed_of_dominates (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]))
    (hcapBlind : IsCapBlindSpot design)
    {unitNormal : Fin 3 → ℝ} (hunit : unitNormal ⬝ᵥ unitNormal = 1)
    (hlineFlat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ unitNormal = 0)
    {dominator : Finset (Fin 6)} (hcard : dominator.card = 3)
    (hdominates : Dominates design dominator) :
    OneLineWeakSeed design unitNormal := by
  rcases oneLine_cardThree_split dominator hcard with hline | hflatPair | hfreePair | hfreeTriple
  · exact absurd hline (oneLine_dominator_ne_lineSet design hunit hlineFlat hdominates)
  · obtain ⟨pairFirst, -, pairSecond, -, freeLabel, -, hshape, hFirstSecond, hFirstFree,
      hSecondFree, hFirstMem, hSecondMem⟩ := hflatPair
    have htriple : Dominates design {pairFirst, pairSecond, freeLabel} := by
      rwa [hshape] at hdominates
    have hindependent := pairGramDet_pos_of_hasLinePattern_of_open design hpattern
      oneLine_open_three hFirstSecond (lineOne_mem_ne_three pairFirst hFirstMem)
      (lineOne_mem_ne_three pairSecond hSecondMem)
    have hfloor : 0 ≤ pairGapExcessOf design pairFirst pairSecond :=
      pairGapExcessOf_nonneg_of_dominates_flatPair design hFirstSecond hFirstFree hSecondFree
        unitNormal hunit (hlineFlat pairFirst hFirstMem) (hlineFlat pairSecond hSecondMem)
        hindependent htriple
    exact Or.inl ⟨pairFirst, hFirstMem, pairSecond, hSecondMem, hFirstSecond,
      ⟨hfloor, pairGapExcessOf_le_of_capBlindSpot design hcapBlind hFirstSecond⟩⟩
  · obtain ⟨lineLabel, -, freeFirst, -, freeSecond, -, hshape, hLineFirst, hLineSecond,
      hFreeDistinct, hlineMem, hFirstMem, hSecondMem⟩ := hfreePair
    have htriple : Dominates design {lineLabel, freeFirst, freeSecond} := by
      rwa [hshape] at hdominates
    exact Or.inr (Or.inl ⟨freeFirst, hFirstMem, freeSecond, hSecondMem, hFreeDistinct,
      oneLine_dominator_freePair_normal_sum design hunit hlineFlat hlineMem hLineFirst
        hLineSecond hFreeDistinct htriple⟩)
  · exact Or.inr (Or.inr (by rwa [hfreeTriple] at hdominates))

/-! ## 14. The seeded one-line residual, and the registry bridge -/

/-- The one-line residual with the seed attached to its antecedent. -/
def OneLineSeededLineSparse : Prop :=
  ∀ design : WeightedDesign 6 3,
    HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) →
    (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
    (∃ heavyLabel : Fin 6, 1 / 10 ≤ design.weight heavyLabel) →
    IsCapBlindSpot design →
    IsOneLineNormalBlindSpot design →
    (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
    (∀ unitNormal : Fin 3 → ℝ, unitNormal ⬝ᵥ unitNormal = 1 →
      (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ unitNormal = 0) →
      OneLineWeakSeed design unitNormal) →
    PlaneBranchTenCandidate design

/-- **THE SEEDED ONE-LINE RESIDUAL CLOSES THE REGISTRY FORMULA.** -/
theorem oneLineTenthHeavyJointBlindLineSparse_of_seeded
    (hresidual : OneLineSeededLineSparse) :
    OneLineTenthHeavyJointBlindLineSparse := by
  intro design hpattern hheavy hweightHeavy hcapBlind hlineBlind hweak
  obtain ⟨dominator, hcard, hdominates⟩ := hweak
  refine hresidual design hpattern hheavy hweightHeavy hcapBlind hlineBlind
    ⟨dominator, hcard, hdominates⟩ ?_
  intro unitNormal hunit hlineFlat
  exact oneLine_weakSeed_of_dominates design hpattern hcapBlind hunit hlineFlat hcard
    hdominates

/-- **THE CONVERSE.**  Dropping the seed recovers the seeded form. -/
theorem seeded_of_oneLineTenthHeavyJointBlindLineSparse
    (hresidual : OneLineTenthHeavyJointBlindLineSparse) :
    OneLineSeededLineSparse := by
  intro design hpattern hheavy hweightHeavy hcapBlind hlineBlind hweak _hseed
  exact hresidual design hpattern hheavy hweightHeavy hcapBlind hlineBlind hweak

/-- **THE ONE-LINE DOOR IS EXACT.** -/
theorem oneLineSeededLineSparse_iff :
    OneLineSeededLineSparse ↔ OneLineTenthHeavyJointBlindLineSparse :=
  ⟨oneLineTenthHeavyJointBlindLineSparse_of_seeded,
    seeded_of_oneLineTenthHeavyJointBlindLineSparse⟩

/-! ## 15. One producer retires both line axioms

A design-level producer that reads only the seed retires the one-line residual and
the two-meeting-lines residual together, because the seed is derived from the same
antecedent in both classes. -/

/-- **BOTH LINE AXIOMS FROM ONE SEEDED SELECTOR.**  A selector that turns the
flat-split seed into a strict card-three witness closes the two chartless
residuals at once. -/
theorem oneLine_and_twoMeetingLines_of_seededSelector
    (hselector : ∀ design : WeightedDesign 6 3, ∀ unitNormal : Fin 3 → ℝ,
      unitNormal ⬝ᵥ unitNormal = 1 →
      (∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
        design.atom lineLabel ⬝ᵥ unitNormal = 0) →
      (∀ label : Fin 6, 1 ≤ leverageOf (design.atom label)) →
      IsCapBlindSpot design →
      (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
      LineFlatSplitSelectorAt design unitNormal) :
    OneLineSeededLineSparse ∧ TwoMeetingLinesSeededTransversal := by
  refine ⟨?_, ?_⟩
  · refine seeded_of_oneLineTenthHeavyJointBlindLineSparse ?_
    refine oneLineTenthHeavyJointBlindLineSparse_of_flatSplitResidual ?_
    intro design _hpattern hheavy _hweightHeavy hcapBlind _hlineBlind hweak unitNormal hunit
      hlineFlat
    exact hselector design unitNormal hunit hlineFlat hheavy hcapBlind hweak
  · refine seeded_of_twoMeetingLinesTenthHeavyJointBlindTransversal ?_
    refine twoMeetingLinesTenthHeavyJointBlindTransversal_of_flatSplitResidual ?_
    intro design _hpattern hheavy _hweightHeavy hcapBlind hweak normalFirst normalSecond
      hunitFirst _hunitSecond horthFirst _horthSecond _hblindFirst _hblindSecond
    exact hselector design normalFirst hunitFirst horthFirst hheavy hcapBlind hweak

end Gtz
