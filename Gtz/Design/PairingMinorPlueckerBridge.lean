import Gtz.Design.ChartlessKill
import Gtz.Design.UThreeSixDisjunction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

namespace Gtz

open Matrix

/-!
# Pairing minors as the Pluecker bridge for a live pair

Fix two row vectors `leftVec`, `rightVec`.  Every further vector `probeVec`
gives a two-component column of pairings with those rows.  The determinant of
two such columns is `pairingMinor` below.

The central identity says that three pairing columns can all be collinear only
if either the fixed pair is dependent or the three probe vectors are dependent.
It is the Cauchy--Binet/Pluecker relation that connects line-freeness to the
strict covariance needed by the live-pair completion calculus.
-/

/-- The determinant of the two pairing columns cut out by a fixed pair. -/
def pairingMinor (leftVec rightVec firstVec secondVec : Fin 3 → ℝ) : ℝ :=
  (leftVec ⬝ᵥ firstVec) * (rightVec ⬝ᵥ secondVec)
    - (leftVec ⬝ᵥ secondVec) * (rightVec ⬝ᵥ firstVec)

/-- The Gram determinant of a pair of vectors. -/
def pairArea (leftVec rightVec : Fin 3 → ℝ) : ℝ :=
  (leftVec ⬝ᵥ leftVec) * (rightVec ⬝ᵥ rightVec)
    - (leftVec ⬝ᵥ rightVec) ^ 2

/-- **Pairing-minor Pluecker identity.**  The Gram area of the fixed pair times
the bracket of three probes is an alternating sum of pairing minors times the
three brackets containing the fixed pair. -/
theorem pairArea_mul_tripleBracket
    (leftVec rightVec firstVec secondVec thirdVec : Fin 3 → ℝ) :
    pairArea leftVec rightVec * tripleBracket firstVec secondVec thirdVec
      = pairingMinor leftVec rightVec firstVec secondVec
          * tripleBracket leftVec rightVec thirdVec
        - pairingMinor leftVec rightVec firstVec thirdVec
          * tripleBracket leftVec rightVec secondVec
        + pairingMinor leftVec rightVec secondVec thirdVec
          * tripleBracket leftVec rightVec firstVec := by
  simp only [pairArea, pairingMinor, tripleBracket_eq, dotProduct, Fin.sum_univ_three]
  ring

/-- If both the fixed pair and the probe triple are independent, at least two
probe vectors have non-collinear pairing columns. -/
theorem exists_pairingMinor_ne_zero
    {leftVec rightVec firstVec secondVec thirdVec : Fin 3 → ℝ}
    (hpair : pairArea leftVec rightVec ≠ 0)
    (htriple : tripleBracket firstVec secondVec thirdVec ≠ 0) :
    pairingMinor leftVec rightVec firstVec secondVec ≠ 0
      ∨ pairingMinor leftVec rightVec firstVec thirdVec ≠ 0
      ∨ pairingMinor leftVec rightVec secondVec thirdVec ≠ 0 := by
  by_cases hfirstSecond : pairingMinor leftVec rightVec firstVec secondVec ≠ 0
  · exact Or.inl hfirstSecond
  by_cases hfirstThird : pairingMinor leftVec rightVec firstVec thirdVec ≠ 0
  · exact Or.inr (Or.inl hfirstThird)
  refine Or.inr (Or.inr ?_)
  intro hsecondThird
  have hid := pairArea_mul_tripleBracket leftVec rightVec firstVec secondVec thirdVec
  have hzero : pairArea leftVec rightVec * tripleBracket firstVec secondVec thirdVec = 0 := by
    simpa [not_ne_iff.mp hfirstSecond, not_ne_iff.mp hfirstThird, hsecondThird] using hid
  exact (mul_ne_zero hpair htriple) hzero

/-- A live pair has strictly positive ordinary Gram area.  Its shifted Gram
minor is positive and both diagonal excesses are positive, so undoing the
diagonal shift only increases the determinant. -/
theorem pairArea_pos_of_isLivePair {m : ℕ} (design : WeightedDesign m 3)
    {leftLabel rightLabel : Fin m}
    (hlive : IsLivePair design leftLabel rightLabel) :
    0 < pairArea (design.atom leftLabel) (design.atom rightLabel) := by
  rcases hlive with ⟨hleft, hright, hpair⟩
  simp only [gapExcessOf] at hleft hright
  simp only [pairGapExcessOf, gapExcessOf, gapPairingOf] at hpair
  simp only [pairArea, ← leverageOf_eq_dotProduct]
  nlinarith

/-- A live pair and a nonzero atom bracket force a nonzero pairing-column
minor among that triple. -/
theorem exists_atom_pairingMinor_ne_zero_of_isLivePair {m : ℕ}
    (design : WeightedDesign m 3)
    {leftLabel rightLabel firstLabel secondLabel thirdLabel : Fin m}
    (hlive : IsLivePair design leftLabel rightLabel)
    (htriple : atomBracket design firstLabel secondLabel thirdLabel ≠ 0) :
    pairingMinor (design.atom leftLabel) (design.atom rightLabel)
        (design.atom firstLabel) (design.atom secondLabel) ≠ 0
      ∨ pairingMinor (design.atom leftLabel) (design.atom rightLabel)
          (design.atom firstLabel) (design.atom thirdLabel) ≠ 0
      ∨ pairingMinor (design.atom leftLabel) (design.atom rightLabel)
          (design.atom secondLabel) (design.atom thirdLabel) ≠ 0 := by
  apply exists_pairingMinor_ne_zero
  · exact (pairArea_pos_of_isLivePair design hlive).ne'
  · simpa only [atomBracket] using htriple

/-- The weighted covariance determinant of three pairing columns is positive
as soon as their weights are positive and one column minor is nonzero. -/
theorem weighted_pairing_covariance_three_pos
    (weightFirst weightSecond weightThird : ℝ)
    (leftVec rightVec firstVec secondVec thirdVec : Fin 3 → ℝ)
    (hweightFirst : 0 < weightFirst) (hweightSecond : 0 < weightSecond)
    (hweightThird : 0 < weightThird)
    (hminor : pairingMinor leftVec rightVec firstVec secondVec ≠ 0
      ∨ pairingMinor leftVec rightVec firstVec thirdVec ≠ 0
      ∨ pairingMinor leftVec rightVec secondVec thirdVec ≠ 0) :
    0 <
      (weightFirst * (leftVec ⬝ᵥ firstVec) ^ 2
          + weightSecond * (leftVec ⬝ᵥ secondVec) ^ 2
          + weightThird * (leftVec ⬝ᵥ thirdVec) ^ 2)
        * (weightFirst * (rightVec ⬝ᵥ firstVec) ^ 2
          + weightSecond * (rightVec ⬝ᵥ secondVec) ^ 2
          + weightThird * (rightVec ⬝ᵥ thirdVec) ^ 2)
        - (weightFirst * (leftVec ⬝ᵥ firstVec) * (rightVec ⬝ᵥ firstVec)
          + weightSecond * (leftVec ⬝ᵥ secondVec) * (rightVec ⬝ᵥ secondVec)
          + weightThird * (leftVec ⬝ᵥ thirdVec) * (rightVec ⬝ᵥ thirdVec)) ^ 2 := by
  rw [weightedLagrange_three]
  simp only [pairingMinor] at hminor
  rcases hminor with hminor | hminor | hminor
  · have hpos : 0 < weightFirst * weightSecond
        * ((leftVec ⬝ᵥ firstVec) * (rightVec ⬝ᵥ secondVec)
          - (leftVec ⬝ᵥ secondVec) * (rightVec ⬝ᵥ firstVec)) ^ 2 :=
      mul_pos (mul_pos hweightFirst hweightSecond) (sq_pos_of_ne_zero hminor)
    have hnonnegFirstThird : 0 ≤ weightFirst * weightThird
        * ((leftVec ⬝ᵥ firstVec) * (rightVec ⬝ᵥ thirdVec)
          - (leftVec ⬝ᵥ thirdVec) * (rightVec ⬝ᵥ firstVec)) ^ 2 :=
      mul_nonneg (mul_nonneg hweightFirst.le hweightThird.le) (sq_nonneg _)
    have hnonnegSecondThird : 0 ≤ weightSecond * weightThird
        * ((leftVec ⬝ᵥ secondVec) * (rightVec ⬝ᵥ thirdVec)
          - (leftVec ⬝ᵥ thirdVec) * (rightVec ⬝ᵥ secondVec)) ^ 2 :=
      mul_nonneg (mul_nonneg hweightSecond.le hweightThird.le) (sq_nonneg _)
    linarith
  · have hnonnegFirstSecond : 0 ≤ weightFirst * weightSecond
        * ((leftVec ⬝ᵥ firstVec) * (rightVec ⬝ᵥ secondVec)
          - (leftVec ⬝ᵥ secondVec) * (rightVec ⬝ᵥ firstVec)) ^ 2 :=
      mul_nonneg (mul_nonneg hweightFirst.le hweightSecond.le) (sq_nonneg _)
    have hpos : 0 < weightFirst * weightThird
        * ((leftVec ⬝ᵥ firstVec) * (rightVec ⬝ᵥ thirdVec)
          - (leftVec ⬝ᵥ thirdVec) * (rightVec ⬝ᵥ firstVec)) ^ 2 :=
      mul_pos (mul_pos hweightFirst hweightThird) (sq_pos_of_ne_zero hminor)
    have hnonnegSecondThird : 0 ≤ weightSecond * weightThird
        * ((leftVec ⬝ᵥ secondVec) * (rightVec ⬝ᵥ thirdVec)
          - (leftVec ⬝ᵥ thirdVec) * (rightVec ⬝ᵥ secondVec)) ^ 2 :=
      mul_nonneg (mul_nonneg hweightSecond.le hweightThird.le) (sq_nonneg _)
    linarith
  · have hnonnegFirstSecond : 0 ≤ weightFirst * weightSecond
        * ((leftVec ⬝ᵥ firstVec) * (rightVec ⬝ᵥ secondVec)
          - (leftVec ⬝ᵥ secondVec) * (rightVec ⬝ᵥ firstVec)) ^ 2 :=
      mul_nonneg (mul_nonneg hweightFirst.le hweightSecond.le) (sq_nonneg _)
    have hnonnegFirstThird : 0 ≤ weightFirst * weightThird
        * ((leftVec ⬝ᵥ firstVec) * (rightVec ⬝ᵥ thirdVec)
          - (leftVec ⬝ᵥ thirdVec) * (rightVec ⬝ᵥ firstVec)) ^ 2 :=
      mul_nonneg (mul_nonneg hweightFirst.le hweightThird.le) (sq_nonneg _)
    have hpos : 0 < weightSecond * weightThird
        * ((leftVec ⬝ᵥ secondVec) * (rightVec ⬝ᵥ thirdVec)
          - (leftVec ⬝ᵥ thirdVec) * (rightVec ⬝ᵥ secondVec)) ^ 2 :=
      mul_pos (mul_pos hweightSecond hweightThird) (sq_pos_of_ne_zero hminor)
    linarith

/-- **Line-free live-pair covariance.**  For any live pair in a line-free
`(6,3)` design, the weighted pairing columns of any three distinct labels have
strictly positive covariance determinant. -/
theorem weighted_atom_pairing_covariance_three_pos_of_lineFree
    (design : WeightedDesign 6 3)
    (hlineFree : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6)))))
    {leftLabel rightLabel firstLabel secondLabel thirdLabel : Fin 6}
    (hlive : IsLivePair design leftLabel rightLabel)
    (hfirstSecond : firstLabel ≠ secondLabel) (hfirstThird : firstLabel ≠ thirdLabel)
    (hsecondThird : secondLabel ≠ thirdLabel) :
    0 <
      (design.weight firstLabel
            * (design.atom leftLabel ⬝ᵥ design.atom firstLabel) ^ 2
          + design.weight secondLabel
            * (design.atom leftLabel ⬝ᵥ design.atom secondLabel) ^ 2
          + design.weight thirdLabel
            * (design.atom leftLabel ⬝ᵥ design.atom thirdLabel) ^ 2)
        * (design.weight firstLabel
            * (design.atom rightLabel ⬝ᵥ design.atom firstLabel) ^ 2
          + design.weight secondLabel
            * (design.atom rightLabel ⬝ᵥ design.atom secondLabel) ^ 2
          + design.weight thirdLabel
            * (design.atom rightLabel ⬝ᵥ design.atom thirdLabel) ^ 2)
        - (design.weight firstLabel
              * (design.atom leftLabel ⬝ᵥ design.atom firstLabel)
              * (design.atom rightLabel ⬝ᵥ design.atom firstLabel)
          + design.weight secondLabel
              * (design.atom leftLabel ⬝ᵥ design.atom secondLabel)
              * (design.atom rightLabel ⬝ᵥ design.atom secondLabel)
          + design.weight thirdLabel
              * (design.atom leftLabel ⬝ᵥ design.atom thirdLabel)
              * (design.atom rightLabel ⬝ᵥ design.atom thirdLabel)) ^ 2 := by
  apply weighted_pairing_covariance_three_pos
  · exact design.weight_pos firstLabel
  · exact design.weight_pos secondLabel
  · exact design.weight_pos thirdLabel
  · exact exists_atom_pairingMinor_ne_zero_of_isLivePair design hlive
      (atomBracket_ne_zero_of_lineFree design hlineFree
        hfirstSecond hfirstThird hsecondThird)

end Gtz
