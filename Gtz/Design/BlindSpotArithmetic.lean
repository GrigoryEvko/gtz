import Gtz.Design.OneLineLiftCertificate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-
# The arithmetic content of the line-normal blind spot

`Gtz.IsOneLineNormalBlindSpot` is a NEGATIVE hypothesis: at every unit normal
flat against the whole line, and at every ordered triple of labels, the guarded
lift criterion does NOT fire.  A prover receives a negation, and a negation of a
conjunction of three strict inequalities is not usable arithmetic.

This file converts it.  The conversion needs one scalar collapse that the tree
did not have.  At a pair the normal is flat against, the two heights vanish, so
the lift demand IS the shadow-gap determinant, the lift reading IS the third
height times that determinant, and the whole lift margin factors:

  liftMargin = d * (h_x ^ 2 * d - liftLeverage),   d := shadowGapDeterminant.

The tree already carried this collapse AT the two members of the pair
(`Gtz.liftMargin_at_pairFirst_of_flatPair` and its mirror, which return `0`).
It did not carry it at a THIRD label, which is the only case that decides a
triple.  With the factorisation the blind spot becomes one inequality:

  d > 0  =>  h_x ^ 2 * d <= liftLeverage.

Nothing here is one-line specific.  The hypotheses are "these two labels read
zero at this normal", so the same lemmas serve every line pattern, at every
line normal.
-/

namespace Gtz

variable {size : ℕ}

/-! ## Part 1: the scalar collapse at a flat pair -/

/-- The lift demand of a flat pair is exactly its shadow-gap determinant.  Both
height terms of `Gtz.liftDemandOf` carry a factor of a vanishing height. -/
theorem liftDemand_of_flatPair (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond : Fin size)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0) :
    liftDemandOf (shadowPairing design normalVec pairFirst pairFirst)
        (shadowPairing design normalVec pairFirst pairSecond)
        (shadowPairing design normalVec pairSecond pairSecond)
        (normalReading design normalVec pairFirst)
        (normalReading design normalVec pairSecond)
      = shadowGapDeterminant design normalVec pairFirst pairSecond := by
  simp only [liftDemandOf, shadowGapDeterminant, hFirstFlat, hSecondFlat]
  ring

/-- The lift reading of a third label over a flat pair is the third label's own
normal reading, scaled by the pair's shadow-gap determinant. -/
theorem liftReading_of_flatPair (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0) :
    liftReadingOf (shadowPairing design normalVec pairFirst pairFirst)
        (shadowPairing design normalVec pairFirst pairSecond)
        (shadowPairing design normalVec pairSecond pairSecond)
        (shadowPairing design normalVec pairFirst thirdLabel)
        (shadowPairing design normalVec pairSecond thirdLabel)
        (normalReading design normalVec pairFirst)
        (normalReading design normalVec pairSecond)
        (normalReading design normalVec thirdLabel)
      = normalReading design normalVec thirdLabel
        * shadowGapDeterminant design normalVec pairFirst pairSecond := by
  simp only [liftReadingOf, shadowGapDeterminant, hFirstFlat, hSecondFlat]
  ring

/-- **THE FLAT-PAIR FACTORISATION.**  At a pair the normal is flat against, the
lift margin of any third label factors through the pair's shadow-gap
determinant.  This is the collapse the tree was missing at a third label, and it
is what turns the blind spot into an inequality. -/
theorem liftMargin_of_flatPair (design : WeightedDesign size 3) (normalVec : Fin 3 → ℝ)
    (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0) :
    liftMargin design normalVec pairFirst pairSecond thirdLabel
      = shadowGapDeterminant design normalVec pairFirst pairSecond
        * (normalReading design normalVec thirdLabel ^ 2
            * shadowGapDeterminant design normalVec pairFirst pairSecond
          - liftLeverageOf (shadowPairing design normalVec pairFirst pairFirst)
              (shadowPairing design normalVec pairFirst pairSecond)
              (shadowPairing design normalVec pairSecond pairSecond)
              (shadowPairing design normalVec pairFirst thirdLabel)
              (shadowPairing design normalVec pairSecond thirdLabel)
              (shadowPairing design normalVec thirdLabel thirdLabel)) := by
  simp only [liftMargin, liftMarginOf, liftReadingOf, liftDemandOf, shadowGapDeterminant,
    hFirstFlat, hSecondFlat]
  ring

/-! ## Part 2: the blind spot, read as an inequality -/

/-- **THE ARITHMETIC CONTENT, GENERIC.**  A vanishing lift margin at a flat pair
whose shadow-gap determinant is positive is exactly the inequality
`h_x ^ 2 * d <= liftLeverage`.  No pattern, no design hypothesis. -/
theorem liftLeverage_ge_of_liftMargin_nonpos_of_flatPair (design : WeightedDesign size 3)
    (normalVec : Fin 3 → ℝ) (pairFirst pairSecond thirdLabel : Fin size)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0)
    (hdet : 0 < shadowGapDeterminant design normalVec pairFirst pairSecond)
    (hmargin : liftMargin design normalVec pairFirst pairSecond thirdLabel ≤ 0) :
    normalReading design normalVec thirdLabel ^ 2
        * shadowGapDeterminant design normalVec pairFirst pairSecond
      ≤ liftLeverageOf (shadowPairing design normalVec pairFirst pairFirst)
          (shadowPairing design normalVec pairFirst pairSecond)
          (shadowPairing design normalVec pairSecond pairSecond)
          (shadowPairing design normalVec pairFirst thirdLabel)
          (shadowPairing design normalVec pairSecond thirdLabel)
          (shadowPairing design normalVec thirdLabel thirdLabel) := by
  rw [liftMargin_of_flatPair design normalVec pairFirst pairSecond thirdLabel hFirstFlat
    hSecondFlat] at hmargin
  nlinarith [hmargin, hdet]

/-- **THE ONE-LINE BLIND SPOT, AS ARITHMETIC.**  At the line normal, every line
pair is flat, so the blind spot's negated conjunction becomes one inequality on
the design's own invariants: whenever the pair's shadow corner and its
shadow-gap determinant are positive, every third label obeys
`h_x ^ 2 * d <= liftLeverage`.  The two positive guards are exactly the two
hypotheses the blind spot negates alongside the margin. -/
theorem oneLine_liftLeverage_ge_of_normalBlindSpot (design : WeightedDesign 6 3)
    (hblind : IsOneLineNormalBlindSpot design) {normalVec : Fin 3 → ℝ}
    (hunit : normalVec ⬝ᵥ normalVec = 1)
    (hflat : ∀ lineLabel ∈ ({0, 1, 2} : Finset (Fin 6)),
      design.atom lineLabel ⬝ᵥ normalVec = 0)
    (pairFirst pairSecond thirdLabel : Fin 6)
    (hFirstSecond : pairFirst ≠ pairSecond) (hFirstThird : pairFirst ≠ thirdLabel)
    (hSecondThird : pairSecond ≠ thirdLabel)
    (hFirstFlat : normalReading design normalVec pairFirst = 0)
    (hSecondFlat : normalReading design normalVec pairSecond = 0)
    (hcorner : 0 < shadowPairing design normalVec pairFirst pairFirst - 1)
    (hdet : 0 < shadowGapDeterminant design normalVec pairFirst pairSecond) :
    normalReading design normalVec thirdLabel ^ 2
        * shadowGapDeterminant design normalVec pairFirst pairSecond
      ≤ liftLeverageOf (shadowPairing design normalVec pairFirst pairFirst)
          (shadowPairing design normalVec pairFirst pairSecond)
          (shadowPairing design normalVec pairSecond pairSecond)
          (shadowPairing design normalVec pairFirst thirdLabel)
          (shadowPairing design normalVec pairSecond thirdLabel)
          (shadowPairing design normalVec thirdLabel thirdLabel) := by
  have hnot := hblind normalVec hunit hflat pairFirst pairSecond thirdLabel hFirstSecond
    hFirstThird hSecondThird
  have hmargin : liftMargin design normalVec pairFirst pairSecond thirdLabel ≤ 0 := by
    by_contra hpos
    exact hnot ⟨hcorner, hdet, not_le.mp hpos⟩
  exact liftLeverage_ge_of_liftMargin_nonpos_of_flatPair design normalVec pairFirst pairSecond
    thirdLabel hFirstFlat hSecondFlat hdet hmargin

end Gtz
