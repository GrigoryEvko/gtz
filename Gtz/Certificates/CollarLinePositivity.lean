import Mathlib
import Gtz.Certificates.CollarMarginIdentities

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The line tube window positivity (GTZ collar, rung-15 sign layer, pilot)

The committed `Gtz.Certificates.CollarMarginIdentities` is the IDENTITY
layer of the M(K4) collar: 43 theorems, every payload identity of the
shape `polyEval Lhs = polyEval Rhs` over `Int`.  This file is the pilot
of the SIGN layer.  It consumes the committed factorization theorem
`lineWindowMarginFactorization` (never restates it) and proves the
rung-15 line lemma conclusion in the kernel:

  ON THE WHOLE LINE TUBE  0 < s <= 1/8,  0 < c <= 1  THE WINDOW IS OPEN:
  the through-star (1,3) threshold lies strictly below the Gordan ratio
  of the support-(0,2,3,5,6) ray, both restricted to the double-tie line
  w = (s, c s, s, c s)   (fiber_line_lemma.log (iv)).

Route: the committed identity is a forall-`Int` statement; `Int` is an
infinite integral domain, so the two sparse polynomials are formally
equal (`MvPolynomial.funext`) and the identity transfers to every
rational point.  The sign chain is then factor-by-factor with exact
rational endpoints: `40 c s^2 > 0`, `2s - 1 < 0`, `2cs - 1 < 0`, and the
quartic factor is trapped below `5/8 - 1 < 0` on the tube; the
denominator pair carries `RD < 0 < thrDen`, so the margin quotient is
positive.

Second (structural) piece: the LINE PIVOT SIGN LAW.  The committed
pivot core `pivotCoreB` restricts on the double-tie line to
`4 c s^3 (1 - c)` -- nonnegative on the tube and vanishing exactly on
the named degeneracy locus c = 1 (the diagonal contact), the mechanism
that anchored the 14b tubes.
-/

namespace GtzCollarLinePositivity

open GtzCollarMargins

/-! ## Rational evaluation semantics for the committed sparse calculus -/

/-- Rational-point evaluation of one committed sparse term. -/
def termEvalRat (term : Term) (rimOne rimTwo rimThree rimFour : ℚ) : ℚ :=
  (term.coeff : ℚ) * rimOne ^ term.monomial.expOne
    * rimTwo ^ term.monomial.expTwo
    * rimThree ^ term.monomial.expThree
    * rimFour ^ term.monomial.expFour

/-- Rational-point evaluation of a committed sparse polynomial. -/
def polyEvalRat : Poly → ℚ → ℚ → ℚ → ℚ → ℚ
  | [], _, _, _, _ => 0
  | term :: rest, rimOne, rimTwo, rimThree, rimFour =>
      termEvalRat term rimOne rimTwo rimThree rimFour
        + polyEvalRat rest rimOne rimTwo rimThree rimFour

theorem polyEvalRat_append (front back : Poly)
    (rimOne rimTwo rimThree rimFour : ℚ) :
    polyEvalRat (front ++ back) rimOne rimTwo rimThree rimFour
      = polyEvalRat front rimOne rimTwo rimThree rimFour
        + polyEvalRat back rimOne rimTwo rimThree rimFour := by
  induction front with
  | nil => simp [polyEvalRat]
  | cons head rest restHolds =>
      simp only [List.cons_append, polyEvalRat, restHolds]
      ring

theorem polyEvalRat_neg (poly : Poly)
    (rimOne rimTwo rimThree rimFour : ℚ) :
    polyEvalRat (polyNeg poly) rimOne rimTwo rimThree rimFour
      = -(polyEvalRat poly rimOne rimTwo rimThree rimFour) := by
  induction poly with
  | nil => rfl
  | cons head rest restHolds =>
      simp only [polyNeg, List.map_cons, polyEvalRat, termEvalRat,
        Int.cast_neg] at restHolds ⊢
      rw [restHolds]
      ring

theorem termEvalRat_termMul (leftTerm rightTerm : Term)
    (rimOne rimTwo rimThree rimFour : ℚ) :
    termEvalRat (termMul leftTerm rightTerm) rimOne rimTwo rimThree rimFour
      = termEvalRat leftTerm rimOne rimTwo rimThree rimFour
        * termEvalRat rightTerm rimOne rimTwo rimThree rimFour := by
  simp only [termEvalRat, termMul, monomialMul, pow_add, Int.cast_mul]
  ring

theorem polyEvalRat_mulTerm (scaler : Term) (poly : Poly)
    (rimOne rimTwo rimThree rimFour : ℚ) :
    polyEvalRat (polyMulTerm scaler poly) rimOne rimTwo rimThree rimFour
      = termEvalRat scaler rimOne rimTwo rimThree rimFour
        * polyEvalRat poly rimOne rimTwo rimThree rimFour := by
  induction poly with
  | nil => simp [polyEvalRat, polyMulTerm]
  | cons head rest restHolds =>
      simp only [polyMulTerm, List.map_cons, polyEvalRat] at restHolds ⊢
      rw [termEvalRat_termMul, restHolds]
      ring

theorem polyEvalRat_mul (leftPoly rightPoly : Poly)
    (rimOne rimTwo rimThree rimFour : ℚ) :
    polyEvalRat (polyMul leftPoly rightPoly) rimOne rimTwo rimThree rimFour
      = polyEvalRat leftPoly rimOne rimTwo rimThree rimFour
        * polyEvalRat rightPoly rimOne rimTwo rimThree rimFour := by
  induction leftPoly with
  | nil => simp [polyEvalRat, polyMul]
  | cons head rest restHolds =>
      simp only [polyMul, polyEvalRat]
      rw [polyEvalRat_append, polyEvalRat_mulTerm, restHolds]
      ring

/-! ## The Int-to-rational transfer bridge

A committed identity is a forall-`Int` statement.  `Int` is an infinite
integral domain, so agreement at every integer point forces the two
sparse polynomials to be formally equal, and formal equality evaluates
anywhere -- in particular at every rational point of the tube. -/

/-- The committed sparse term as a formal 4-variable integer polynomial. -/
noncomputable def termToMv (term : Term) : MvPolynomial (Fin 4) Int :=
  MvPolynomial.C term.coeff
    * MvPolynomial.X 0 ^ term.monomial.expOne
    * MvPolynomial.X 1 ^ term.monomial.expTwo
    * MvPolynomial.X 2 ^ term.monomial.expThree
    * MvPolynomial.X 3 ^ term.monomial.expFour

/-- The committed sparse polynomial as a formal integer polynomial. -/
noncomputable def polyToMv : Poly → MvPolynomial (Fin 4) Int
  | [] => 0
  | term :: rest => termToMv term + polyToMv rest

theorem intPow_eq_pow (base : Int) (exponent : Nat) :
    intPow base exponent = base ^ exponent := by
  induction exponent with
  | zero => simp [intPow]
  | succ exponentPred priorHolds => rw [intPow, priorHolds, pow_succ]

theorem polyToMv_evalInt (poly : Poly) (point : Fin 4 → Int) :
    MvPolynomial.eval point (polyToMv poly)
      = polyEval poly (point 0) (point 1) (point 2) (point 3) := by
  induction poly with
  | nil => simp [polyToMv, polyEval]
  | cons head rest restHolds =>
      simp only [polyToMv, map_add, restHolds, polyEval]
      congr 1
      simp [termToMv, termEval, intPow_eq_pow, map_mul, map_pow,
        MvPolynomial.eval_X, Int.mul_assoc]

theorem polyToMv_aevalRat (poly : Poly) (point : Fin 4 → ℚ) :
    MvPolynomial.aeval point (polyToMv poly)
      = polyEvalRat poly (point 0) (point 1) (point 2) (point 3) := by
  induction poly with
  | nil => simp [polyToMv, polyEvalRat]
  | cons head rest restHolds =>
      simp only [polyToMv, map_add, restHolds, polyEvalRat]
      congr 1
      simp [termToMv, termEvalRat, map_mul, map_pow,
        MvPolynomial.aeval_X, eq_intCast, mul_assoc]

/-- THE TRANSFER BRIDGE: a committed forall-`Int` identity between two
sparse polynomials holds at every rational point. -/
theorem polyEvalRat_eq_of_int_identity {lhsPoly rhsPoly : Poly}
    (intIdentity : ∀ pointOne pointTwo pointThree pointFour : Int,
      polyEval lhsPoly pointOne pointTwo pointThree pointFour
        = polyEval rhsPoly pointOne pointTwo pointThree pointFour)
    (rimOne rimTwo rimThree rimFour : ℚ) :
    polyEvalRat lhsPoly rimOne rimTwo rimThree rimFour
      = polyEvalRat rhsPoly rimOne rimTwo rimThree rimFour := by
  have formalEq : polyToMv lhsPoly = polyToMv rhsPoly := by
    apply MvPolynomial.funext
    intro point
    rw [polyToMv_evalInt, polyToMv_evalInt]
    exact intIdentity (point 0) (point 1) (point 2) (point 3)
  have aevalEq := congrArg
    (MvPolynomial.aeval ![rimOne, rimTwo, rimThree, rimFour]) formalEq
  rw [polyToMv_aevalRat, polyToMv_aevalRat] at aevalEq
  simpa using aevalEq

/-! ## The line window objects (the committed payload, read over `ℚ`)

The line chart puts the tie scale `s` in exponent slot 1 and the tie
ratio `c` in slot 2 (CollarMarginIdentities, "double-tie line lemma"
block); slots 3-4 are unused and evaluated at 0. -/

/-- The Gordan ratio of the support-(0,2,3,5,6) ray on the double-tie
line, as the committed rational function RN/RD. -/
def lineGordanRatio (scale ratio : ℚ) : ℚ :=
  polyEvalRat lineRatioNum scale ratio 0 0
    / polyEvalRat lineRatioDen scale ratio 0 0

/-- The through-star (1,3) threshold on the double-tie line, as the
committed rational function thrNum/thrDen. -/
def lineThreshold (scale ratio : ℚ) : ℚ :=
  polyEvalRat lineThrNum scale ratio 0 0
    / polyEvalRat lineThrDen scale ratio 0 0

/-- The committed margin cross-difference, read over `ℚ`: the recorded
`lineWindowMarginLhs` IS `RN * thrDen - thrNum * RD`. -/
theorem lineWindowMarginLhsEval (scale ratio : ℚ) :
    polyEvalRat lineWindowMarginLhs scale ratio 0 0
      = polyEvalRat lineRatioNum scale ratio 0 0
          * polyEvalRat lineThrDen scale ratio 0 0
        - polyEvalRat lineThrNum scale ratio 0 0
          * polyEvalRat lineRatioDen scale ratio 0 0 := by
  simp only [lineWindowMarginLhs, polyAdd]
  rw [polyEvalRat_append, polyEvalRat_neg, polyEvalRat_mul, polyEvalRat_mul]
  ring

/-- The committed factorization theorem `lineWindowMarginFactorization`,
transported to every rational point of the line chart and with the
seven committed factor lists multiplied out:

  RN thrDen - thrNum RD
    = 40 c s^2 (2s - 1)(2cs - 1)(4c^2 s^2 + 4c s^2 + 2cs + 2s - 1).

This CONSUMES the committed `Int` identity through the transfer bridge;
the ring step below only evaluates the committed `lineWindowMarginRhs`
factor lists, it does not re-prove the factorization. -/
theorem lineWindowMarginFactorizationRat (scale ratio : ℚ) :
    polyEvalRat lineWindowMarginLhs scale ratio 0 0
      = 40 * ratio * scale ^ 2 * (2 * scale - 1) * (2 * ratio * scale - 1)
        * (4 * ratio ^ 2 * scale ^ 2 + 4 * ratio * scale ^ 2
            + 2 * ratio * scale + 2 * scale - 1) := by
  rw [polyEvalRat_eq_of_int_identity lineWindowMarginFactorization
    scale ratio 0 0]
  simp only [lineWindowMarginRhs, polyEvalRat_mul]
  simp only [polyEvalRat, termEvalRat, tm]
  push_cast
  ring

/-! ## The factor sign chain on the tube 0 < s <= 1/8, 0 < c <= 1 -/

theorem lineTubeHeadFactorIsPositive (scale ratio : ℚ)
    (scaleIsPositive : 0 < scale) (ratioIsPositive : 0 < ratio) :
    0 < 40 * ratio * scale ^ 2 := by positivity

theorem lineTubeHalfWallIsNegative (scale : ℚ)
    (scaleIsSmall : scale ≤ 1 / 8) :
    2 * scale - 1 < 0 := by linarith

theorem lineTubeDiagonalWallIsNegative (scale ratio : ℚ)
    (scaleIsPositive : 0 < scale) (scaleIsSmall : scale ≤ 1 / 8)
    (ratioIsBounded : ratio ≤ 1) :
    2 * ratio * scale - 1 < 0 := by
  have ratioScaleIsBelowScale : ratio * scale ≤ scale :=
    mul_le_of_le_one_left scaleIsPositive.le ratioIsBounded
  linarith

/-- The quartic factor is trapped: on the tube its positive part is at
most `4/64 + 4/64 + 1/4 + 1/4 = 5/8 < 1`. -/
theorem lineTubeQuarticFactorIsNegative (scale ratio : ℚ)
    (scaleIsPositive : 0 < scale) (scaleIsSmall : scale ≤ 1 / 8)
    (ratioIsPositive : 0 < ratio) (ratioIsBounded : ratio ≤ 1) :
    4 * ratio ^ 2 * scale ^ 2 + 4 * ratio * scale ^ 2
      + 2 * ratio * scale + 2 * scale - 1 < 0 := by
  have productIsPositive : 0 < ratio * scale :=
    mul_pos ratioIsPositive scaleIsPositive
  have productIsSmall : ratio * scale ≤ 1 / 8 :=
    le_trans (mul_le_of_le_one_left scaleIsPositive.le ratioIsBounded)
      scaleIsSmall
  have squareIsSmall : ratio * scale * (ratio * scale) ≤ 1 / 8 * (1 / 8) :=
    mul_le_mul productIsSmall productIsSmall productIsPositive.le
      (by norm_num)
  have mixedIsSmall : ratio * scale * scale ≤ 1 / 8 * (1 / 8) :=
    mul_le_mul productIsSmall scaleIsSmall scaleIsPositive.le (by norm_num)
  nlinarith [squareIsSmall, mixedIsSmall, productIsSmall, scaleIsSmall]

/-- RD on the line is `-6 c s^3 - 6 c^2 s^3` (committed bytes), strictly
negative on the tube. -/
theorem lineRatioDenIsNegativeOnTube (scale ratio : ℚ)
    (scaleIsPositive : 0 < scale) (ratioIsPositive : 0 < ratio) :
    polyEvalRat lineRatioDen scale ratio 0 0 < 0 := by
  have closedForm : polyEvalRat lineRatioDen scale ratio 0 0
      = -(6 * ratio * scale ^ 3) - 6 * ratio ^ 2 * scale ^ 3 := by
    simp only [lineRatioDen, polyEvalRat, termEvalRat, tm]
    push_cast
    ring
  rw [closedForm]
  have linearPartIsPositive : 0 < 6 * ratio * scale ^ 3 := by positivity
  have squarePartIsPositive : 0 < 6 * ratio ^ 2 * scale ^ 3 := by positivity
  linarith

/-- thrDen on the line is `1 - 2s - 2cs + 2cs^2 + 2c^2 s^2` (committed
bytes), at least `1/2` on the tube. -/
theorem lineThrDenIsPositiveOnTube (scale ratio : ℚ)
    (scaleIsPositive : 0 < scale) (scaleIsSmall : scale ≤ 1 / 8)
    (ratioIsPositive : 0 < ratio) (ratioIsBounded : ratio ≤ 1) :
    0 < polyEvalRat lineThrDen scale ratio 0 0 := by
  have closedForm : polyEvalRat lineThrDen scale ratio 0 0
      = 1 - 2 * scale - 2 * ratio * scale + 2 * ratio * scale ^ 2
        + 2 * ratio ^ 2 * scale ^ 2 := by
    simp only [lineThrDen, polyEvalRat, termEvalRat, tm]
    push_cast
    ring
  rw [closedForm]
  have productIsSmall : ratio * scale ≤ 1 / 8 :=
    le_trans (mul_le_of_le_one_left scaleIsPositive.le ratioIsBounded)
      scaleIsSmall
  have mixedIsNonneg : 0 ≤ 2 * ratio * scale ^ 2 := by positivity
  have squareIsNonneg : 0 ≤ 2 * ratio ^ 2 * scale ^ 2 := by positivity
  linarith

/-! ## THE PILOT THEOREM: the window is open on the whole line tube -/

/-- LINE TUBE WINDOW POSITIVITY (rung-15 line lemma (iv), kernel form).
On the whole line tube `0 < s <= 1/8`, `0 < c <= 1` the through-star
(1,3) threshold lies strictly below the Gordan ratio of the
support-(0,2,3,5,6) ray: the window margin `r - thrA` is positive.
Sits directly on the committed `lineWindowMarginFactorization`. -/
theorem lineWindowIsOpenOnTube (scale ratio : ℚ)
    (scaleIsPositive : 0 < scale) (scaleIsSmall : scale ≤ 1 / 8)
    (ratioIsPositive : 0 < ratio) (ratioIsBounded : ratio ≤ 1) :
    lineThreshold scale ratio < lineGordanRatio scale ratio := by
  have ratioDenIsNegative :=
    lineRatioDenIsNegativeOnTube scale ratio scaleIsPositive ratioIsPositive
  have thrDenIsPositive := lineThrDenIsPositiveOnTube scale ratio
    scaleIsPositive scaleIsSmall ratioIsPositive ratioIsBounded
  have marginNumeratorIsNegative :
      polyEvalRat lineRatioNum scale ratio 0 0
          * polyEvalRat lineThrDen scale ratio 0 0
        - polyEvalRat lineThrNum scale ratio 0 0
          * polyEvalRat lineRatioDen scale ratio 0 0 < 0 := by
    rw [← lineWindowMarginLhsEval, lineWindowMarginFactorizationRat]
    have headIsPositive := lineTubeHeadFactorIsPositive scale ratio
      scaleIsPositive ratioIsPositive
    have halfWallIsNegative := lineTubeHalfWallIsNegative scale scaleIsSmall
    have diagonalWallIsNegative := lineTubeDiagonalWallIsNegative scale ratio
      scaleIsPositive scaleIsSmall ratioIsBounded
    have quarticIsNegative := lineTubeQuarticFactorIsNegative scale ratio
      scaleIsPositive scaleIsSmall ratioIsPositive ratioIsBounded
    have firstProductIsNegative :
        40 * ratio * scale ^ 2 * (2 * scale - 1) < 0 :=
      mul_neg_of_pos_of_neg headIsPositive halfWallIsNegative
    have secondProductIsPositive :
        0 < 40 * ratio * scale ^ 2 * (2 * scale - 1)
          * (2 * ratio * scale - 1) :=
      mul_pos_of_neg_of_neg firstProductIsNegative diagonalWallIsNegative
    exact mul_neg_of_pos_of_neg secondProductIsPositive quarticIsNegative
  have denominatorIsNegative :
      polyEvalRat lineRatioDen scale ratio 0 0
        * polyEvalRat lineThrDen scale ratio 0 0 < 0 :=
    mul_neg_of_neg_of_pos ratioDenIsNegative thrDenIsPositive
  have differenceIsPositive :
      0 < lineGordanRatio scale ratio - lineThreshold scale ratio := by
    unfold lineGordanRatio lineThreshold
    rw [div_sub_div _ _ (ne_of_lt ratioDenIsNegative)
      (ne_of_gt thrDenIsPositive)]
    have crossFormsAgree :
        polyEvalRat lineRatioNum scale ratio 0 0
            * polyEvalRat lineThrDen scale ratio 0 0
          - polyEvalRat lineRatioDen scale ratio 0 0
            * polyEvalRat lineThrNum scale ratio 0 0
        = polyEvalRat lineRatioNum scale ratio 0 0
            * polyEvalRat lineThrDen scale ratio 0 0
          - polyEvalRat lineThrNum scale ratio 0 0
            * polyEvalRat lineRatioDen scale ratio 0 0 := by ring
    rw [crossFormsAgree]
    exact div_pos_of_neg_of_neg marginNumeratorIsNegative
      denominatorIsNegative
  exact sub_pos.mp differenceIsPositive

/-! ## The line pivot sign law (structural piece)

The committed pivot core `K_B = a b (w1 - w4) - mu` restricts on the
double-tie line `w = (s, cs, s, cs)` to `4 c s^3 (1 - c)`
(fiber_line_lemma.log (vi)): nonnegative on the tube and vanishing
EXACTLY at the diagonal contact `c = 1`. -/

/-- The named degeneracy locus of the line pivot law: the diagonal
contact `c = 1`, where the double-tie line meets the equal-rim-rates
diagonal and the K_B pivot degenerates. -/
def IsAtDiagonalContact (ratio : ℚ) : Prop := ratio = 1

/-- The line restriction of the committed `pivotCoreB`:
`K_B(s, cs, s, cs) = 4 c s^3 (1 - c)`. -/
theorem linePivotCoreBFactorization (scale ratio : ℚ) :
    polyEvalRat pivotCoreB scale (ratio * scale) scale (ratio * scale)
      = 4 * ratio * scale ^ 3 * (1 - ratio) := by
  simp only [pivotCoreB, polyAdd, muInvariant, branchSumA, branchSumB]
  rw [polyEvalRat_append, polyEvalRat_neg, polyEvalRat_mul, polyEvalRat_mul]
  simp only [polyEvalRat, termEvalRat, tm]
  push_cast
  ring

/-- LINE PIVOT SIGN LAW, nonnegative half: `K_B >= 0` on the whole line
tube (`0 < s`, `0 < c <= 1`). -/
theorem linePivotCoreBIsNonnegativeOnTube (scale ratio : ℚ)
    (scaleIsPositive : 0 < scale) (ratioIsPositive : 0 < ratio)
    (ratioIsBounded : ratio ≤ 1) :
    0 ≤ polyEvalRat pivotCoreB scale (ratio * scale) scale
      (ratio * scale) := by
  rw [linePivotCoreBFactorization]
  have headIsNonneg : 0 ≤ 4 * ratio * scale ^ 3 := by positivity
  have tailIsNonneg : 0 ≤ 1 - ratio := by linarith
  exact mul_nonneg headIsNonneg tailIsNonneg

/-- LINE PIVOT SIGN LAW, strict half: `K_B > 0` strictly off the
diagonal contact. -/
theorem linePivotCoreBIsPositiveOffDiagonal (scale ratio : ℚ)
    (scaleIsPositive : 0 < scale) (ratioIsPositive : 0 < ratio)
    (ratioIsBelowOne : ratio < 1) :
    0 < polyEvalRat pivotCoreB scale (ratio * scale) scale
      (ratio * scale) := by
  rw [linePivotCoreBFactorization]
  have headIsPositive : 0 < 4 * ratio * scale ^ 3 := by positivity
  have tailIsPositive : 0 < 1 - ratio := by linarith
  exact mul_pos headIsPositive tailIsPositive

/-- LINE PIVOT SIGN LAW, degeneracy half: on the open line (`0 < s`,
`0 < c`) the pivot vanishes IFF the point sits on the diagonal contact
locus `c = 1`. -/
theorem linePivotCoreBVanishesIffDiagonalContact (scale ratio : ℚ)
    (scaleIsPositive : 0 < scale) (ratioIsPositive : 0 < ratio) :
    polyEvalRat pivotCoreB scale (ratio * scale) scale (ratio * scale) = 0
      ↔ IsAtDiagonalContact ratio := by
  rw [linePivotCoreBFactorization]
  unfold IsAtDiagonalContact
  constructor
  · intro productIsZero
    rcases mul_eq_zero.mp productIsZero with headIsZero | tailIsZero
    · exfalso
      have headIsPositive : 0 < 4 * ratio * scale ^ 3 := by positivity
      exact absurd headIsZero (ne_of_gt headIsPositive)
    · linarith
  · intro ratioIsOne
    rw [ratioIsOne]
    ring

end GtzCollarLinePositivity
