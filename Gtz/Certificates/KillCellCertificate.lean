import Mathlib

/-!
# Kill inequality, dominance cell (1, 2): an exact certificate

At the canonical (5,3) diamond tie the first-order obstruction is the
kill inequality

  `min (yᵀ A_A y) (yᵀ A_B y) ≤ 60 * max_ij yᵀ B_ij y`,

whose proof splits over the ten dominance cells
`C_ij = {y | b_ij y ≥ b_kl y for every pair kl}`, each halved by the
sign of `q_B - q_A`.  On each of the resulting twenty cells a
positive multiple of the cell target is a nonnegative combination of
the cell's defining quadrics plus a sum of squares.

This file carries that certificate for the cell of edge pair (1, 2)
with the `B` ellipsoid as target, in the shape

  `weightForm * targetForm
     = Σ multiplierₖ * dominanceₖ + sosRemainder`,

an identity of rational polynomials, closed by `ring`.  Every
multiplier and the remainder are written as sums of squares with
nonnegative rational coefficients -- the exact LDL factorisations of
the certificate's Gram blocks -- so their nonnegativity is
`positivity`.  The weight is positive definite, hence strictly
positive off the origin; three LDL orderings supply one usable
decomposition per nonzero coordinate.  So the target is nonnegative
wherever every dominance quadric is, which is exactly the cell.

All forms are scaled by positive rationals to integer coefficients;
that changes no sign.  The other nineteen cells follow this pattern
verbatim, with the two `(0,2)` and `(3,4)` A-form cells needing
quartic multipliers instead of quadratic ones.
-/

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

namespace KillCellCertificate

/-- The cell target `60 * b_12 - q_B`, scaled by `1`. -/
def targetForm (y1 y2 y3 : ℚ) : ℚ :=
  100 * y1 * y2 + 90 * y1 * y3 - 60 * y2 ^ 2 - 20 * y2 * y3

/-- Dominance quadric 0: `b_12 - b_01`, scaled by `1`. -/
def dominance0 (y1 y2 y3 : ℚ) : ℚ :=
  2 * y1 * y2 - 2 * y2 * y3

/-- Dominance quadric 1: `b_12 - b_02`, scaled by `24`. -/
def dominance1 (y1 y2 y3 : ℚ) : ℚ :=
  24 * y1 * y2 - 25 * y2 ^ 2 - 24 * y2 * y3

/-- Dominance quadric 2: `b_12 - b_03`, scaled by `6`. -/
def dominance2 (y1 y2 y3 : ℚ) : ℚ :=
  3 * y1 ^ 2 + 16 * y1 * y2 + 12 * y1 * y3 + 4 * y2 * y3

/-- Dominance quadric 3: `b_12 - b_04`, scaled by `6`. -/
def dominance3 (y1 y2 y3 : ℚ) : ℚ :=
  8 * y1 * y2 + 12 * y1 * y3 - 5 * y2 ^ 2 + 2 * y2 * y3 + 3 * y3 ^ 2

/-- Dominance quadric 4: `b_12 - b_13`, scaled by `3`. -/
def dominance4 (y1 y2 y3 : ℚ) : ℚ :=
  2 * y1 ^ 2 + 10 * y1 * y2 + 10 * y1 * y3 + 10 * y2 * y3 + 8 * y3 ^ 2

/-- Dominance quadric 5: `b_12 - b_14`, scaled by `3`. -/
def dominance5 (y1 y2 y3 : ℚ) : ℚ :=
  8 * y1 ^ 2 + 16 * y1 * y2 + 10 * y1 * y3 + 4 * y2 * y3 + 2 * y3 ^ 2

/-- Dominance quadric 6: `b_12 - b_23`, scaled by `6`. -/
def dominance6 (y1 y2 y3 : ℚ) : ℚ :=
  3 * y1 ^ 2 + 14 * y1 * y2 + 12 * y1 * y3 - 5 * y2 ^ 2 - 4 * y2 * y3

/-- Dominance quadric 7: `b_12 - b_24`, scaled by `6`. -/
def dominance7 (y1 y2 y3 : ℚ) : ℚ :=
  16 * y1 * y2 + 12 * y1 * y3 + 4 * y2 * y3 + 3 * y3 ^ 2

/-- Dominance quadric 8: `b_12 - b_34`, scaled by `24`. -/
def dominance8 (y1 y2 y3 : ℚ) : ℚ :=
  15 * y1 ^ 2 + 54 * y1 * y2 + 30 * y1 * y3 - 25 * y2 ^ 2 + 6 * y2 * y3 + 15 * y3 ^ 2

/-- The certificate weight: a positive definite quadratic form, in
its exact LDL sum-of-squares form (elimination order 1, 2, 3, so the
last term is a positive multiple of `y3 ^ 2`). -/
def weightForm (y1 y2 y3 : ℚ) : ℚ :=
  7728 * (y1 + (110 / 161) * y2 + (60 / 161) * y3) ^ 2
  + (230640 / 161) * (y2 + (2673 / 1922) * y3) ^ 2
  + (5862044 / 961) * (y3) ^ 2

/-- The same weight, eliminated in the order 3, 2, 1: the last term
is now a positive multiple of `y1 ^ 2`. -/
def weightFormFromThird (y1 y2 y3 : ℚ) : ℚ :=
  9944 * ((360 / 1243) * y1 + (45 / 113) * y2 + y3) ^ 2
  + (391320 / 113) * ((3892 / 3261) * y1 + y2) ^ 2
  + (23448176 / 11957) * (y1) ^ 2

/-- The same weight, eliminated in the order 1, 3, 2: the last term
is a positive multiple of `y2 ^ 2`. -/
def weightFormFromSecond (y1 y2 y3 : ℚ) : ℚ :=
  7728 * (y1 + (110 / 161) * y2 + (60 / 161) * y3) ^ 2
  + (1428184 / 161) * ((40095 / 178523) * y2 + y3) ^ 2
  + (175861320 / 178523) * (y2) ^ 2

/-- Multiplier for dominance quadric 0, as a sum of squares. -/
def multiplier0 (y1 y2 y3 : ℚ) : ℚ :=
  60360 * (y1 - (459 / 503) * y2 - (483 / 503) * y3) ^ 2
  + (612720 / 503) * (y2 + (2641 / 5106) * y3) ^ 2
  + (986040 / 851) * (y3) ^ 2

/-- Multiplier for dominance quadric 1, as a sum of squares. -/
def multiplier1 (y1 y2 y3 : ℚ) : ℚ :=
  7810 * (y1 + (587 / 781) * y2 + (101 / 71) * y3) ^ 2
  + (2115030 / 781) * (y2 - (14080 / 211503) * y3) ^ 2
  + (20861015 / 211503) * (y3) ^ 2

/-- Multiplier for dominance quadric 2, as a sum of squares. -/
def multiplier2 (_y1 y2 y3 : ℚ) : ℚ :=
  570 * (y2 - (580 / 57) * y3) ^ 2
  + (880220 / 57) * (y3) ^ 2

/-- Multiplier for dominance quadric 3, as a sum of squares. -/
def multiplier3 (y1 y2 _y3 : ℚ) : ℚ :=
  57840 * (y1 + (689 / 723) * y2) ^ 2
  + (153340 / 723) * (y2) ^ 2

/-- Multiplier for dominance quadric 4, as a sum of squares. -/
def multiplier4 (_y1 y2 _y3 : ℚ) : ℚ :=
  240 * (y2) ^ 2

/-- Multiplier for dominance quadric 5, as a sum of squares. -/
def multiplier5 (_y1 y2 _y3 : ℚ) : ℚ :=
  240 * (y2) ^ 2

/-- Multiplier for dominance quadric 6, as a sum of squares. -/
def multiplier6 (_y1 y2 y3 : ℚ) : ℚ :=
  120 * (y2) ^ 2
  + 120 * (y3) ^ 2

/-- Multiplier for dominance quadric 7, as a sum of squares. -/
def multiplier7 (y1 y2 _y3 : ℚ) : ℚ :=
  120 * (y1) ^ 2
  + 120 * (y2) ^ 2

/-- Multiplier for dominance quadric 8, as a sum of squares. -/
def multiplier8 (_y1 y2 _y3 : ℚ) : ℚ :=
  30 * (y2) ^ 2

/-- The sum-of-squares remainder: a quartic, in its exact LDL form
over the six quadratic monomials. -/
def sosRemainder (y1 y2 y3 : ℚ) : ℚ :=
  140650 * (y2 ^ 2 - (62 / 14065) * y1 * y2 + (816 / 14065) * y1 * y3 - (248 / 14065) * y2 * y3) ^ 2
  + (361434682 / 2813) * (y1 * y2 - (18008868 / 180717341) * y1 * y3 - (15376 / 180717341) * y2 * y3) ^ 2
  + (21510900344700 / 180717341) * (y1 * y3 + (11679384316 / 215109003447) * y2 * y3) ^ 2
  + (28878463774103395 / 215109003447) * (y2 * y3) ^ 2

theorem weightFormFromThird_eq (y1 y2 y3 : ℚ) :
    weightFormFromThird y1 y2 y3 = weightForm y1 y2 y3 := by
  unfold weightFormFromThird weightForm; ring

theorem weightFormFromSecond_eq (y1 y2 y3 : ℚ) :
    weightFormFromSecond y1 y2 y3 = weightForm y1 y2 y3 := by
  unfold weightFormFromSecond weightForm; ring

/-- **The certificate identity.**  A polynomial identity over `ℚ`;
`ring` closes it, and it is the entire mathematical content of this
cell's proof. -/
theorem certificate_identity (y1 y2 y3 : ℚ) :
    weightForm y1 y2 y3 * targetForm y1 y2 y3
      = multiplier0 y1 y2 y3 * dominance0 y1 y2 y3 +
        multiplier1 y1 y2 y3 * dominance1 y1 y2 y3 +
        multiplier2 y1 y2 y3 * dominance2 y1 y2 y3 +
        multiplier3 y1 y2 y3 * dominance3 y1 y2 y3 +
        multiplier4 y1 y2 y3 * dominance4 y1 y2 y3 +
        multiplier5 y1 y2 y3 * dominance5 y1 y2 y3 +
        multiplier6 y1 y2 y3 * dominance6 y1 y2 y3 +
        multiplier7 y1 y2 y3 * dominance7 y1 y2 y3 +
        multiplier8 y1 y2 y3 * dominance8 y1 y2 y3 +
        sosRemainder y1 y2 y3 := by
  unfold weightForm targetForm sosRemainder
  unfold multiplier0 multiplier1 multiplier2 multiplier3 multiplier4 multiplier5 multiplier6 multiplier7 multiplier8
  unfold dominance0 dominance1 dominance2 dominance3 dominance4 dominance5 dominance6 dominance7 dominance8
  ring

theorem multiplier0_nonneg (y1 y2 y3 : ℚ) :
    0 ≤ multiplier0 y1 y2 y3 := by
  unfold multiplier0
  positivity

theorem multiplier1_nonneg (y1 y2 y3 : ℚ) :
    0 ≤ multiplier1 y1 y2 y3 := by
  unfold multiplier1
  positivity

theorem multiplier2_nonneg (y1 y2 y3 : ℚ) :
    0 ≤ multiplier2 y1 y2 y3 := by
  unfold multiplier2
  positivity

theorem multiplier3_nonneg (y1 y2 y3 : ℚ) :
    0 ≤ multiplier3 y1 y2 y3 := by
  unfold multiplier3
  positivity

theorem multiplier4_nonneg (y1 y2 y3 : ℚ) :
    0 ≤ multiplier4 y1 y2 y3 := by
  unfold multiplier4
  positivity

theorem multiplier5_nonneg (y1 y2 y3 : ℚ) :
    0 ≤ multiplier5 y1 y2 y3 := by
  unfold multiplier5
  positivity

theorem multiplier6_nonneg (y1 y2 y3 : ℚ) :
    0 ≤ multiplier6 y1 y2 y3 := by
  unfold multiplier6
  positivity

theorem multiplier7_nonneg (y1 y2 y3 : ℚ) :
    0 ≤ multiplier7 y1 y2 y3 := by
  unfold multiplier7
  positivity

theorem multiplier8_nonneg (y1 y2 y3 : ℚ) :
    0 ≤ multiplier8 y1 y2 y3 := by
  unfold multiplier8
  positivity

theorem sosRemainder_nonneg (y1 y2 y3 : ℚ) :
    0 ≤ sosRemainder y1 y2 y3 := by
  unfold sosRemainder
  positivity

theorem weightForm_pos_of_ne_zero (y1 y2 y3 : ℚ)
    (hne : y1 ≠ 0 ∨ y2 ≠ 0 ∨ y3 ≠ 0) : 0 < weightForm y1 y2 y3 := by
  rcases hne with hy | hy | hy
  · rw [← weightFormFromThird_eq]
    unfold weightFormFromThird
    have hsq : 0 < y1 ^ 2 := pow_two_pos_of_ne_zero hy
    positivity
  · rw [← weightFormFromSecond_eq]
    unfold weightFormFromSecond
    have hsq : 0 < y2 ^ 2 := pow_two_pos_of_ne_zero hy
    positivity
  · unfold weightForm
    have hsq : 0 < y3 ^ 2 := pow_two_pos_of_ne_zero hy
    positivity

/-- **The cell theorem.**  Wherever every dominance quadric of the
cell is nonnegative and the direction is nonzero, the cell target is
nonnegative -- that is, the kill inequality holds on this cell. -/
theorem targetForm_nonneg_on_cell (y1 y2 y3 : ℚ)
    (hne : y1 ≠ 0 ∨ y2 ≠ 0 ∨ y3 ≠ 0)
    (h0 : 0 ≤ dominance0 y1 y2 y3)
    (h1 : 0 ≤ dominance1 y1 y2 y3)
    (h2 : 0 ≤ dominance2 y1 y2 y3)
    (h3 : 0 ≤ dominance3 y1 y2 y3)
    (h4 : 0 ≤ dominance4 y1 y2 y3)
    (h5 : 0 ≤ dominance5 y1 y2 y3)
    (h6 : 0 ≤ dominance6 y1 y2 y3)
    (h7 : 0 ≤ dominance7 y1 y2 y3)
    (h8 : 0 ≤ dominance8 y1 y2 y3)
    : 0 ≤ targetForm y1 y2 y3 := by
  have hweight : 0 < weightForm y1 y2 y3 :=
    weightForm_pos_of_ne_zero y1 y2 y3 hne
  have hsos : 0 ≤ sosRemainder y1 y2 y3 := sosRemainder_nonneg _ _ _
  have hterm0 : 0 ≤ multiplier0 y1 y2 y3 * dominance0 y1 y2 y3 :=
    mul_nonneg (multiplier0_nonneg _ _ _) h0
  have hterm1 : 0 ≤ multiplier1 y1 y2 y3 * dominance1 y1 y2 y3 :=
    mul_nonneg (multiplier1_nonneg _ _ _) h1
  have hterm2 : 0 ≤ multiplier2 y1 y2 y3 * dominance2 y1 y2 y3 :=
    mul_nonneg (multiplier2_nonneg _ _ _) h2
  have hterm3 : 0 ≤ multiplier3 y1 y2 y3 * dominance3 y1 y2 y3 :=
    mul_nonneg (multiplier3_nonneg _ _ _) h3
  have hterm4 : 0 ≤ multiplier4 y1 y2 y3 * dominance4 y1 y2 y3 :=
    mul_nonneg (multiplier4_nonneg _ _ _) h4
  have hterm5 : 0 ≤ multiplier5 y1 y2 y3 * dominance5 y1 y2 y3 :=
    mul_nonneg (multiplier5_nonneg _ _ _) h5
  have hterm6 : 0 ≤ multiplier6 y1 y2 y3 * dominance6 y1 y2 y3 :=
    mul_nonneg (multiplier6_nonneg _ _ _) h6
  have hterm7 : 0 ≤ multiplier7 y1 y2 y3 * dominance7 y1 y2 y3 :=
    mul_nonneg (multiplier7_nonneg _ _ _) h7
  have hterm8 : 0 ≤ multiplier8 y1 y2 y3 * dominance8 y1 y2 y3 :=
    mul_nonneg (multiplier8_nonneg _ _ _) h8
  have hproduct : 0 ≤ weightForm y1 y2 y3 * targetForm y1 y2 y3 := by
    rw [certificate_identity]
    linarith
  exact nonneg_of_mul_nonneg_right hproduct hweight

end KillCellCertificate

end Gtz
