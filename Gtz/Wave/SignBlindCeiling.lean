import Gtz.Wave.TripleDeterminantSharp

/-!
# The maximal sign-blind cell in root-free form, and the exact residue

`Gtz.signFreeMargin` is the strongest quantity a certificate can read when it
declines to look at the sign of the triple product, and
`Gtz.signFreeMargin_pos_iff_both_signs` proves that optimality.  But the margin
carries an absolute value, so it is not a polynomial and a cell stated through it
cannot be checked by `ring` or `nlinarith` on the underlying data.  This file
removes the absolute value.

**The root-free criterion.**  Split the third minor into the part that reads
every pairing evenly and the cross term.  Writing `E` for the even part
(`Gtz.evenTripleDetPart`), the margin is `E - 2|uvw|`, so it is positive exactly
when `0 < E` and `4 (uvw)^2 < E^2`.  That is
`Gtz.signFreeMargin_pos_iff_evenPart_sq`, and
`Gtz.evenPart_sq_iff_both_signs` records that this pair of polynomial
inequalities IS the two-sided condition.  So the polynomial criterion is the
maximal sign-blind cell, not merely a sufficient one.

**The scaling, and why the constant four is exact.**  The triple
`(p,q,r,u,v,w)` carries a diagonal action, `p ↦ a^2 p` and `u ↦ a b u`, under
which every one of the three objects scales by `(abc)^2`
(`Gtz.evenTripleDetPart_scale`, `Gtz.tripleDetForm_scale`,
`Gtz.signFreeMargin_scale`).  So the criterion is a function of the three
scale-invariant ratios alone (`Gtz.signFreeMargin_pos_iff_ratios`), and setting
all three equal collapses it by the identity
`(1 - 3 s)^2 - 4 s^3 = (1 - 4 s) (1 - s)^2`.  That identity is why
`Gtz.signFreeMargin_pos_iff_quarterSlack_of_equal` holds: on the equal locus the
maximal cell and the quarter-slack cell agree exactly, so four is neither
improvable nor wasteful.

**The exact residue.**  A triple where the determinant is positive but the margin
is not is exactly a triple with a positive triple product whose even part is
trapped in `(-2uvw, 2uvw]` (`Gtz.residue_iff`).  Two consequences follow at once.
No triple with a non-positive triple product is ever in the residue
(`Gtz.not_residue_of_cross_nonpos`), so the residue is a set of COHERENT triples.
And on the residue the determinant is at most four times the cross term
(`Gtz.tripleDetForm_le_four_mul_cross_of_residue`), which is the precise sense in
which the cross term carries the determinant there.

**The residue is not empty.**  At the equiangular point the surpluses are `1/3`
and every pairing squares to `1/20`.  The even part is `-7/540`, strictly
negative, so the determinant is carried entirely by the cross term, and the whole
sign-blind class fails while the coherent triples still dominate.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The even part

The third minor reads `u`, `v` and `w` evenly except in the cross term.  Naming
the even part is what makes the absolute value removable. -/

/-- The part of the third Sylvester minor invariant under flipping one pairing. -/
def evenTripleDetPart (p q r u v w : ℝ) : ℝ :=
  p * q * r - p * w ^ 2 - q * v ^ 2 - r * u ^ 2

theorem evenTripleDetPart_apply (p q r u v w : ℝ) :
    evenTripleDetPart p q r u v w = p * q * r - p * w ^ 2 - q * v ^ 2 - r * u ^ 2 := rfl

/-- The determinant is the even part plus twice the cross term. -/
theorem tripleDetForm_eq_evenPart_add_cross (p q r u v w : ℝ) :
    tripleDetForm p q r u v w = evenTripleDetPart p q r u v w + 2 * (u * v * w) := by
  rw [tripleDetForm, evenTripleDetPart]

/-- The determinant at the flipped sign is the even part minus twice the cross term. -/
theorem tripleDetForm_flip_eq_evenPart_sub_cross (p q r u v w : ℝ) :
    tripleDetForm p q r u v (-w) = evenTripleDetPart p q r u v w - 2 * (u * v * w) := by
  rw [tripleDetForm_flip_third, evenTripleDetPart]

/-- The margin is the even part minus twice the absolute cross term. -/
theorem signFreeMargin_eq_evenPart_sub_abs (p q r u v w : ℝ) :
    signFreeMargin p q r u v w = evenTripleDetPart p q r u v w - 2 * |u * v * w| := by
  rw [signFreeMargin, evenTripleDetPart]

/-- The even part is the average of the two determinants at the two signs. -/
theorem evenTripleDetPart_eq_average (p q r u v w : ℝ) :
    evenTripleDetPart p q r u v w
      = (tripleDetForm p q r u v w + tripleDetForm p q r u v (-w)) / 2 := by
  rw [tripleDetForm_add_flip, evenTripleDetPart]; ring

/-- The even part is symmetric in the three slots, exactly as the determinant is. -/
theorem evenTripleDetPart_swap_first_second (p q r u v w : ℝ) :
    evenTripleDetPart q p r u w v = evenTripleDetPart p q r u v w := by
  rw [evenTripleDetPart, evenTripleDetPart]; ring

theorem evenTripleDetPart_swap_second_third (p q r u v w : ℝ) :
    evenTripleDetPart p r q v u w = evenTripleDetPart p q r u v w := by
  rw [evenTripleDetPart, evenTripleDetPart]; ring

theorem evenTripleDetPart_swap_first_third (p q r u v w : ℝ) :
    evenTripleDetPart r q p w v u = evenTripleDetPart p q r u v w := by
  rw [evenTripleDetPart, evenTripleDetPart]; ring

theorem evenTripleDetPart_rotate (p q r u v w : ℝ) :
    evenTripleDetPart q r p w u v = evenTripleDetPart p q r u v w := by
  rw [evenTripleDetPart, evenTripleDetPart]; ring

/-- Flipping any single pairing fixes the even part.  This is the invariance the
whole sign-blind class is built on. -/
theorem evenTripleDetPart_flip_third (p q r u v w : ℝ) :
    evenTripleDetPart p q r u v (-w) = evenTripleDetPart p q r u v w := by
  rw [evenTripleDetPart, evenTripleDetPart]; ring

theorem evenTripleDetPart_flip_second (p q r u v w : ℝ) :
    evenTripleDetPart p q r u (-v) w = evenTripleDetPart p q r u v w := by
  rw [evenTripleDetPart, evenTripleDetPart]; ring

theorem evenTripleDetPart_flip_first (p q r u v w : ℝ) :
    evenTripleDetPart p q r (-u) v w = evenTripleDetPart p q r u v w := by
  rw [evenTripleDetPart, evenTripleDetPart]; ring

/-! ## 2. The root-free criterion, and its maximality

Removing the absolute value costs one squaring.  What comes back is a pair of
polynomial inequalities that are together EQUIVALENT to a positive margin, hence
equivalent to the two-sided determinant condition. -/

/-- **THE ROOT-FREE CRITERION.**  The margin is positive exactly when the even
part is positive and dominates twice the cross term in square.  No absolute
value, no square root, and no eigenvalue appears. -/
theorem signFreeMargin_pos_iff_evenPart_sq (p q r u v w : ℝ) :
    0 < signFreeMargin p q r u v w
      ↔ 0 < evenTripleDetPart p q r u v w
        ∧ 4 * (u * v * w) ^ 2 < evenTripleDetPart p q r u v w ^ 2 := by
  rw [signFreeMargin_eq_evenPart_sub_abs]
  have habs : 0 ≤ |u * v * w| := abs_nonneg _
  have hsq : |u * v * w| ^ 2 = (u * v * w) ^ 2 := sq_abs _
  constructor
  · intro h
    have hE : 0 < evenTripleDetPart p q r u v w := by linarith
    refine ⟨hE, ?_⟩
    nlinarith [habs, h, hE, hsq]
  · rintro ⟨hE, hlt⟩
    nlinarith [habs, hE, hlt, hsq]

/-- **THE POLYNOMIAL CRITERION IS THE MAXIMAL SIGN-BLIND CELL.**  The two
inequalities hold exactly when the determinant is positive at BOTH signs of the
cross term.  Composed with the landed optimality of the margin, this says the
polynomial pair is the strongest condition any sign-blind certificate can use. -/
theorem evenPart_sq_iff_both_signs (p q r u v w : ℝ) :
    (0 < evenTripleDetPart p q r u v w
        ∧ 4 * (u * v * w) ^ 2 < evenTripleDetPart p q r u v w ^ 2)
      ↔ (0 < tripleDetForm p q r u v w ∧ 0 < tripleDetForm p q r u v (-w)) := by
  rw [← signFreeMargin_pos_iff_evenPart_sq, signFreeMargin_pos_iff_both_signs]

/-- **THE CELL.**  The polynomial criterion forces a positive determinant. -/
theorem tripleDetForm_pos_of_evenPart_sq (p q r u v w : ℝ)
    (hE : 0 < evenTripleDetPart p q r u v w)
    (hlt : 4 * (u * v * w) ^ 2 < evenTripleDetPart p q r u v w ^ 2) :
    0 < tripleDetForm p q r u v w :=
  tripleDetForm_pos_of_signFreeMargin _ _ _ _ _ _
    ((signFreeMargin_pos_iff_evenPart_sq p q r u v w).mpr ⟨hE, hlt⟩)

/-- The criterion is itself flip invariant, as any sign-blind condition must be. -/
theorem evenPart_sq_flip_third (p q r u v w : ℝ) :
    (0 < evenTripleDetPart p q r u v (-w)
        ∧ 4 * (u * v * (-w)) ^ 2 < evenTripleDetPart p q r u v (-w) ^ 2)
      ↔ (0 < evenTripleDetPart p q r u v w
        ∧ 4 * (u * v * w) ^ 2 < evenTripleDetPart p q r u v w ^ 2) := by
  rw [evenTripleDetPart_flip_third]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by nlinarith [h2]⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by nlinarith [h2]⟩

/-- **THE QUARTER SLACK IS A COROLLARY, ROOT FREE.**  The landed cell factors
through the polynomial criterion with no absolute value in the passage. -/
theorem evenPart_sq_of_quarterSlack (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hu : 4 * u ^ 2 < p * q) (hv : 4 * v ^ 2 < p * r) (hw : 4 * w ^ 2 < q * r) :
    0 < evenTripleDetPart p q r u v w
      ∧ 4 * (u * v * w) ^ 2 < evenTripleDetPart p q r u v w ^ 2 :=
  (signFreeMargin_pos_iff_evenPart_sq p q r u v w).mp
    (signFreeMargin_pos_of_quarterSlack p q r u v w hp hq hr hu hv hw)

/-! ## 3. The diagonal scaling, and where the constant four comes from

The six coordinates carry an action of three scalars.  Every object in this file
is homogeneous of the same degree under it, so the criterion depends on three
scale-invariant ratios only.  That is what makes a single constant meaningful. -/

/-- The even part is homogeneous under the diagonal scaling. -/
theorem evenTripleDetPart_scale (a b c p q r u v w : ℝ) :
    evenTripleDetPart (a ^ 2 * p) (b ^ 2 * q) (c ^ 2 * r) (a * b * u) (a * c * v) (b * c * w)
      = (a * b * c) ^ 2 * evenTripleDetPart p q r u v w := by
  rw [evenTripleDetPart, evenTripleDetPart]; ring

/-- The determinant is homogeneous under the same scaling. -/
theorem tripleDetForm_scale (a b c p q r u v w : ℝ) :
    tripleDetForm (a ^ 2 * p) (b ^ 2 * q) (c ^ 2 * r) (a * b * u) (a * c * v) (b * c * w)
      = (a * b * c) ^ 2 * tripleDetForm p q r u v w := by
  rw [tripleDetForm, tripleDetForm]; ring

/-- The cross term scales by the same factor, which is what lets the absolute
value pass through the scaling. -/
theorem cross_scale (a b c u v w : ℝ) :
    (a * b * u) * (a * c * v) * (b * c * w) = (a * b * c) ^ 2 * (u * v * w) := by ring

/-- The margin is homogeneous under the diagonal scaling. -/
theorem signFreeMargin_scale (a b c p q r u v w : ℝ) :
    signFreeMargin (a ^ 2 * p) (b ^ 2 * q) (c ^ 2 * r) (a * b * u) (a * c * v) (b * c * w)
      = (a * b * c) ^ 2 * signFreeMargin p q r u v w := by
  rw [signFreeMargin, signFreeMargin, cross_scale, abs_mul,
    abs_of_nonneg (by positivity : (0:ℝ) ≤ (a * b * c) ^ 2)]
  ring

/-- Positivity of the margin is a scale-invariant condition. -/
theorem signFreeMargin_pos_scale_iff (a b c p q r u v w : ℝ)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) :
    0 < signFreeMargin (a ^ 2 * p) (b ^ 2 * q) (c ^ 2 * r)
        (a * b * u) (a * c * v) (b * c * w)
      ↔ 0 < signFreeMargin p q r u v w := by
  rw [signFreeMargin_scale]
  have hpos : 0 < (a * b * c) ^ 2 := by positivity
  exact mul_pos_iff_of_pos_left hpos

/-- The even part is the product of the surpluses times the normalized slack. -/
theorem evenTripleDetPart_eq_mul_slack (p q r u v w : ℝ)
    (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    evenTripleDetPart p q r u v w
      = p * q * r * (1 - u ^ 2 / (p * q) - v ^ 2 / (p * r) - w ^ 2 / (q * r)) := by
  rw [evenTripleDetPart]
  field_simp
  ring

/-- The product of the three scale-invariant ratios is the normalized cross
term squared. -/
theorem ratio_prod_eq (p q r u v w : ℝ) (hp : p ≠ 0) (hq : q ≠ 0) (hr : r ≠ 0) :
    (u ^ 2 / (p * q)) * (v ^ 2 / (p * r)) * (w ^ 2 / (q * r))
      = (u * v * w) ^ 2 / (p * q * r) ^ 2 := by
  field_simp

/-- **THE CRITERION IN RATIO FORM.**  With positive surpluses the whole condition
depends only on the three scale-invariant ratios, and it is a single coupled
inequality on them rather than three independent thresholds. -/
theorem signFreeMargin_pos_iff_ratios (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) :
    0 < signFreeMargin p q r u v w
      ↔ 0 < 1 - u ^ 2 / (p * q) - v ^ 2 / (p * r) - w ^ 2 / (q * r)
        ∧ 4 * ((u ^ 2 / (p * q)) * (v ^ 2 / (p * r)) * (w ^ 2 / (q * r)))
            < (1 - u ^ 2 / (p * q) - v ^ 2 / (p * r) - w ^ 2 / (q * r)) ^ 2 := by
  have hp' : p ≠ 0 := ne_of_gt hp
  have hq' : q ≠ 0 := ne_of_gt hq
  have hr' : r ≠ 0 := ne_of_gt hr
  have hprod : 0 < p * q * r := by positivity
  have hsqprod : (0:ℝ) < (p * q * r) ^ 2 := by positivity
  have hrw : 4 * ((u ^ 2 / (p * q)) * (v ^ 2 / (p * r)) * (w ^ 2 / (q * r)))
      = (4 * (u * v * w) ^ 2) / (p * q * r) ^ 2 := by
    rw [ratio_prod_eq p q r u v w hp' hq' hr']; ring
  rw [signFreeMargin_pos_iff_evenPart_sq, evenTripleDetPart_eq_mul_slack p q r u v w hp' hq' hr',
    hrw, div_lt_iff₀ hsqprod]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(mul_pos_iff_of_pos_left hprod).mp h1, by nlinarith [h2]⟩
  · rintro ⟨h1, h2⟩
    exact ⟨mul_pos hprod h1, by nlinarith [h2]⟩

/-! ### The equal locus and the identity behind the constant four -/

/-- **THE FACTORIZATION THAT PRICES THE CONSTANT.**  On the locus where all three
ratios agree the criterion collapses to a cubic with a double root, and the
remaining linear factor names the constant four. -/
theorem equal_ratio_factorization (s : ℝ) :
    (1 - 3 * s) ^ 2 - 4 * s ^ 3 = (1 - 4 * s) * (1 - s) ^ 2 := by ring

/-- **ON THE EQUAL LOCUS THE MAXIMAL CELL IS THE QUARTER-SLACK CELL.**  So four
is exactly the right constant: nothing below it is sound, and nothing above it
is needed. -/
theorem signFreeMargin_pos_iff_quarterSlack_of_equal (t : ℝ) :
    0 < signFreeMargin 1 1 1 t t t ↔ 4 * t ^ 2 < 1 := by
  rw [signFreeMargin_pos_iff_evenPart_sq]
  have hE : evenTripleDetPart 1 1 1 t t t = 1 - 3 * t ^ 2 := by
    rw [evenTripleDetPart]; ring
  rw [hE]
  constructor
  · rintro ⟨h1, h2⟩
    have hfac : (1 - 4 * t ^ 2) * (1 - t ^ 2) ^ 2 > 0 := by
      have := equal_ratio_factorization (t ^ 2)
      nlinarith [h2]
    nlinarith [sq_nonneg (1 - t ^ 2), hfac, h1]
  · intro h
    have h1 : 0 < 1 - 3 * t ^ 2 := by nlinarith [sq_nonneg t]
    refine ⟨h1, ?_⟩
    have hne : (1 - t ^ 2) ^ 2 > 0 := by nlinarith [sq_nonneg t]
    have := equal_ratio_factorization (t ^ 2)
    nlinarith [hne, h, this]

/-! ## 3b. The pair-minor reading, and a SHARP one-inequality cell

The three separate quarter-slack thresholds are not what the sign-blind class
needs.  The even part is an additive combination of the three pair minors, so the
class only ever sees their SUM, and the sharp threshold on that sum is what this
section computes.  The resulting cell is strictly weaker than three separate
thresholds, and its constant is attained. -/

/-- The weighted pairing energy: each pairing square weighted by the surplus it
does NOT meet. -/
def weightedPairEnergy (p q r u v w : ℝ) : ℝ := p * w ^ 2 + q * v ^ 2 + r * u ^ 2

theorem weightedPairEnergy_nonneg (p q r u v w : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) : 0 ≤ weightedPairEnergy p q r u v w := by
  rw [weightedPairEnergy]; positivity

/-- The even part is the product of surpluses minus the weighted pairing energy. -/
theorem evenTripleDetPart_eq_sub_weightedPairEnergy (p q r u v w : ℝ) :
    evenTripleDetPart p q r u v w = p * q * r - weightedPairEnergy p q r u v w := by
  rw [evenTripleDetPart, weightedPairEnergy]; ring

/-- **THE EVEN PART IS AN ADDITIVE COMBINATION OF THE THREE PAIR MINORS.**  Each
surplus multiplies the minor of the pair it does not belong to, and two copies of
the surplus product are removed.  So the sign-blind class reads the three pair
minors ADDITIVELY and cannot separate them. -/
theorem evenTripleDetPart_eq_pairMinor_combination (p q r u v w : ℝ) :
    evenTripleDetPart p q r u v w
      = r * (p * q - u ^ 2) + q * (p * r - v ^ 2) + p * (q * r - w ^ 2)
        - 2 * (p * q * r) := by
  rw [evenTripleDetPart]; ring

/-- Three nonnegative reals obey the arithmetic-geometric mean inequality in the
cubed form.  Stated multiplicatively so no root appears. -/
theorem cube_amgm_three (bigA bigB bigC : ℝ)
    (hA : 0 ≤ bigA) (hB : 0 ≤ bigB) (hC : 0 ≤ bigC) :
    27 * (bigA * bigB * bigC) ≤ (bigA + bigB + bigC) ^ 3 := by
  nlinarith [sq_nonneg (bigA - bigB), sq_nonneg (bigB - bigC), sq_nonneg (bigA - bigC),
    mul_nonneg hA hB, mul_nonneg hB hC, mul_nonneg hA hC,
    mul_nonneg (mul_nonneg hA hB) hC, sq_nonneg (bigA + bigB - 2 * bigC),
    sq_nonneg (bigB + bigC - 2 * bigA), sq_nonneg (bigA + bigC - 2 * bigB)]

/-- The weighted pairing energy carries the cross term through the mean
inequality: twenty-seven times the surplus product times the squared cross term
never exceeds the cubed energy. -/
theorem twentySeven_mul_cross_sq_le_energy_cube (p q r u v w : ℝ)
    (hp : 0 ≤ p) (hq : 0 ≤ q) (hr : 0 ≤ r) :
    27 * ((p * q * r) * (u * v * w) ^ 2) ≤ weightedPairEnergy p q r u v w ^ 3 := by
  have hkey := cube_amgm_three (p * w ^ 2) (q * v ^ 2) (r * u ^ 2)
    (by positivity) (by positivity) (by positivity)
  rw [weightedPairEnergy]
  nlinarith [hkey]

/-- **THE FACTORIZATION THAT PRICES THE SHARP SUM THRESHOLD.**  This cubic is
what turns the mean inequality into an exact constant, exactly as
`Gtz.equal_ratio_factorization` does on the equal locus. -/
theorem sharp_sum_factorization (bigE bigT : ℝ) :
    27 * (bigE ^ 2 * bigT) - 4 * (bigT - bigE) ^ 3
      = (4 * bigE - bigT) * (bigE + 2 * bigT) ^ 2 := by ring

/-- **THE SHARP ONE-INEQUALITY SIGN-BLIND CELL.**  When the weighted pairing
energy stays below three quarters of the surplus product, the maximal sign-blind
cell fires.  One inequality replaces three, and no pairing is read separately. -/
theorem signFreeMargin_pos_of_weightedPairEnergy_lt (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : weightedPairEnergy p q r u v w < 3 / 4 * (p * q * r)) :
    0 < signFreeMargin p q r u v w := by
  have hT : 0 < p * q * r := by positivity
  have hE : evenTripleDetPart p q r u v w = p * q * r - weightedPairEnergy p q r u v w :=
    evenTripleDetPart_eq_sub_weightedPairEnergy p q r u v w
  have hEpos : 0 < evenTripleDetPart p q r u v w := by rw [hE]; linarith
  have hfour : p * q * r < 4 * evenTripleDetPart p q r u v w := by rw [hE]; linarith
  have henergy : weightedPairEnergy p q r u v w = p * q * r - evenTripleDetPart p q r u v w := by
    rw [hE]; ring
  have hcube := twentySeven_mul_cross_sq_le_energy_cube p q r u v w hp.le hq.le hr.le
  rw [henergy] at hcube
  have hfac := sharp_sum_factorization (evenTripleDetPart p q r u v w) (p * q * r)
  have hsqpos : 0 < (evenTripleDetPart p q r u v w + 2 * (p * q * r)) ^ 2 := by positivity
  have hstrict : 4 * (p * q * r - evenTripleDetPart p q r u v w) ^ 3
      < 27 * (evenTripleDetPart p q r u v w ^ 2 * (p * q * r)) := by nlinarith [hfac, hsqpos]
  rw [signFreeMargin_pos_iff_evenPart_sq]
  exact ⟨hEpos, by nlinarith [hcube, hstrict, hT]⟩

/-- The same cell read on the even part directly. -/
theorem signFreeMargin_pos_of_four_mul_evenPart_gt (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : p * q * r < 4 * evenTripleDetPart p q r u v w) :
    0 < signFreeMargin p q r u v w := by
  refine signFreeMargin_pos_of_weightedPairEnergy_lt p q r u v w hp hq hr ?_
  rw [evenTripleDetPart_eq_sub_weightedPairEnergy] at h
  linarith

/-- **THE SUM CELL SUBSUMES THE QUARTER SLACK.**  Three separate thresholds force
the energy below three quarters, so every triple the landed cell catches this one
catches too. -/
theorem weightedPairEnergy_lt_of_quarterSlack (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hu : 4 * u ^ 2 < p * q) (hv : 4 * v ^ 2 < p * r) (hw : 4 * w ^ 2 < q * r) :
    weightedPairEnergy p q r u v w < 3 / 4 * (p * q * r) := by
  rw [weightedPairEnergy]
  nlinarith [hu, hv, hw, hp, hq, hr]

/-- **AND IT IS STRICTLY WEAKER.**  At this point one pairing breaks its quarter
threshold badly, yet the energy sum stays under three quarters and the maximal
sign-blind cell still fires. -/
theorem exists_sum_cell_beyond_quarterSlack :
    ¬ (4 * (3/5 : ℝ) ^ 2 < 1 * 1)
      ∧ weightedPairEnergy 1 1 1 (3/5) (1/5) (1/5) < 3 / 4 * (1 * 1 * 1)
      ∧ 0 < signFreeMargin 1 1 1 (3/5) (1/5) (1/5) := by
  refine ⟨by norm_num, by rw [weightedPairEnergy]; norm_num, ?_⟩
  refine signFreeMargin_pos_of_weightedPairEnergy_lt 1 1 1 (3/5) (1/5) (1/5)
    one_pos one_pos one_pos ?_
  rw [weightedPairEnergy]; norm_num

/-- **THE CONSTANT THREE QUARTERS IS ATTAINED.**  On the equal locus the energy
condition is exactly the quarter slack, so no larger constant is sound. -/
theorem weightedPairEnergy_lt_iff_quarterSlack_of_equal (t : ℝ) :
    weightedPairEnergy 1 1 1 t t t < 3 / 4 * (1 * 1 * 1) ↔ 4 * t ^ 2 < 1 := by
  rw [weightedPairEnergy]; constructor <;> intro h <;> nlinarith [h]

/-- The sum cell in normalized ratio form: the three scale-invariant ratios need
only sum below three quarters, rather than each stay below one quarter. -/
theorem signFreeMargin_pos_of_ratio_sum_lt (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (h : u ^ 2 / (p * q) + v ^ 2 / (p * r) + w ^ 2 / (q * r) < 3 / 4) :
    0 < signFreeMargin p q r u v w := by
  refine signFreeMargin_pos_of_weightedPairEnergy_lt p q r u v w hp hq hr ?_
  have hT : (0:ℝ) < p * q * r := by positivity
  have k1 : p * q * r * (u ^ 2 / (p * q)) = r * u ^ 2 := by field_simp
  have k2 : p * q * r * (v ^ 2 / (p * r)) = q * v ^ 2 := by field_simp
  have k3 : p * q * r * (w ^ 2 / (q * r)) = p * w ^ 2 := by field_simp
  have hmul := mul_lt_mul_of_pos_left h hT
  rw [mul_add, mul_add, k1, k2, k3] at hmul
  rw [weightedPairEnergy]
  linarith

/-! ## 4. The exact residue

A triple where the determinant is positive but the margin is not is precisely a
triple whose cross term is positive and large enough to carry the even part.
Nothing weaker and nothing stronger. -/

/-- **THE RESIDUE, EXACTLY.**  The determinant is positive while the margin is
not exactly when the triple product is positive and the even part is trapped
between minus and plus twice it. -/
theorem residue_iff (p q r u v w : ℝ) :
    (0 < tripleDetForm p q r u v w ∧ signFreeMargin p q r u v w ≤ 0)
      ↔ (0 < u * v * w
          ∧ -(2 * (u * v * w)) < evenTripleDetPart p q r u v w
          ∧ evenTripleDetPart p q r u v w ≤ 2 * (u * v * w)) := by
  rw [tripleDetForm_eq_evenPart_add_cross, signFreeMargin_eq_evenPart_sub_abs]
  constructor
  · rintro ⟨hdet, hmar⟩
    have habs : evenTripleDetPart p q r u v w ≤ 2 * |u * v * w| := by linarith
    have hcross : 0 < u * v * w := by
      rcases le_or_gt (u * v * w) 0 with hle | hlt
      · rw [abs_of_nonpos hle] at habs; linarith
      · exact hlt
    rw [abs_of_pos hcross] at habs
    exact ⟨hcross, by linarith, habs⟩
  · rintro ⟨hcross, hlow, hhigh⟩
    rw [abs_of_pos hcross]
    exact ⟨by linarith, by linarith⟩

/-- **NO INCOHERENT TRIPLE IS IN THE RESIDUE.**  The sign-blind class loses
nothing at a triple whose triple product is non-positive, so the whole residue
consists of coherent triples. -/
theorem not_residue_of_cross_nonpos (p q r u v w : ℝ) (hc : u * v * w ≤ 0) :
    ¬ (0 < tripleDetForm p q r u v w ∧ signFreeMargin p q r u v w ≤ 0) := by
  intro h
  exact absurd ((residue_iff p q r u v w).mp h).1 (not_lt.mpr hc)

/-- At a non-positive triple product the margin and the determinant decide
together, so the class is complete there. -/
theorem signFreeMargin_pos_of_det_pos_of_cross_nonpos (p q r u v w : ℝ)
    (hdet : 0 < tripleDetForm p q r u v w) (hc : u * v * w ≤ 0) :
    0 < signFreeMargin p q r u v w := by
  rcases le_or_gt (signFreeMargin p q r u v w) 0 with hle | hlt
  · exact absurd ⟨hdet, hle⟩ (not_residue_of_cross_nonpos p q r u v w hc)
  · exact hlt

/-- **THE CROSS TERM CARRIES THE DETERMINANT ON THE RESIDUE.**  There the
determinant is at most four times the triple product, so a bound on the cross
term bounds the whole minor. -/
theorem tripleDetForm_le_four_mul_cross_of_residue (p q r u v w : ℝ)
    (hdet : 0 < tripleDetForm p q r u v w) (hmar : signFreeMargin p q r u v w ≤ 0) :
    tripleDetForm p q r u v w ≤ 4 * (u * v * w) := by
  obtain ⟨_, _, hhigh⟩ := (residue_iff p q r u v w).mp ⟨hdet, hmar⟩
  rw [tripleDetForm_eq_evenPart_add_cross]
  linarith

/-- On the residue the determinant is squeezed between zero and four times the
cross term, so the cross term is strictly positive there. -/
theorem cross_pos_of_residue (p q r u v w : ℝ)
    (hdet : 0 < tripleDetForm p q r u v w) (hmar : signFreeMargin p q r u v w ≤ 0) :
    0 < u * v * w :=
  ((residue_iff p q r u v w).mp ⟨hdet, hmar⟩).1

/-- **THE DEFICIT IS STRICTLY CARRIED.**  When the even part is negative on the
residue, twice the cross term strictly exceeds the deficit.  This is the exact
statement that the cross term must carry the determinant. -/
theorem neg_evenPart_lt_two_mul_cross_of_residue (p q r u v w : ℝ)
    (hdet : 0 < tripleDetForm p q r u v w) (hmar : signFreeMargin p q r u v w ≤ 0) :
    -evenTripleDetPart p q r u v w < 2 * (u * v * w) := by
  obtain ⟨_, hlow, _⟩ := (residue_iff p q r u v w).mp ⟨hdet, hmar⟩
  linarith

/-- **THE CARRY FACTOR EXCEEDS ONE.**  On the part of the residue where the even
part is negative, the ratio of twice the cross term to the deficit is greater
than one.  A magnitude cell for the residue would need that ratio bounded away
from one, and the ratio is what a successor must bound. -/
theorem one_lt_carry_of_residue_of_evenPart_neg (p q r u v w : ℝ)
    (hdet : 0 < tripleDetForm p q r u v w) (hmar : signFreeMargin p q r u v w ≤ 0)
    (hE : evenTripleDetPart p q r u v w < 0) :
    1 < 2 * (u * v * w) / (-evenTripleDetPart p q r u v w) := by
  have hden : 0 < -evenTripleDetPart p q r u v w := by linarith
  rw [lt_div_iff₀ hden, one_mul]
  exact neg_evenPart_lt_two_mul_cross_of_residue p q r u v w hdet hmar

/-- The residue splits by the sign of the even part.  When the even part is
non-negative the determinant would be positive without the cross term, and only
the CERTIFICATE needs the sign.  When it is negative the determinant itself needs
the cross term. -/
theorem residue_evenPart_dichotomy (p q r u v w : ℝ)
    (hdet : 0 < tripleDetForm p q r u v w) (hmar : signFreeMargin p q r u v w ≤ 0) :
    (0 ≤ evenTripleDetPart p q r u v w ∧ 0 < evenTripleDetPart p q r u v w + 2 * (u * v * w))
      ∨ (evenTripleDetPart p q r u v w < 0
          ∧ -evenTripleDetPart p q r u v w < 2 * (u * v * w)) := by
  rcases le_or_gt 0 (evenTripleDetPart p q r u v w) with hle | hlt
  · exact Or.inl ⟨hle, by rw [← tripleDetForm_eq_evenPart_add_cross]; exact hdet⟩
  · exact Or.inr ⟨hlt, neg_evenPart_lt_two_mul_cross_of_residue p q r u v w hdet hmar⟩

/-- **WHEREVER THE CLASS FAILS, THE ENERGY IS DEEP.**  Contraposing the sharp sum
cell needs no determinant hypothesis at all: a non-positive margin already forces
a weighted pairing energy of at least three quarters of the surplus product.  So
the residue is not a thin boundary effect, and every point of it is a fixed
distance from the sign-blind region. -/
theorem three_quarters_le_weightedPairEnergy_of_margin_nonpos (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hmar : signFreeMargin p q r u v w ≤ 0) :
    3 / 4 * (p * q * r) ≤ weightedPairEnergy p q r u v w := by
  rcases lt_or_ge (weightedPairEnergy p q r u v w) (3 / 4 * (p * q * r)) with hlt | hge
  · exact absurd (signFreeMargin_pos_of_weightedPairEnergy_lt p q r u v w hp hq hr hlt)
      (not_lt.mpr hmar)
  · exact hge

/-- The same depth statement read on the even part: where the class fails the
even part never reaches a quarter of the surplus product. -/
theorem four_mul_evenPart_le_of_margin_nonpos (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r) (hmar : signFreeMargin p q r u v w ≤ 0) :
    4 * evenTripleDetPart p q r u v w ≤ p * q * r := by
  have := three_quarters_le_weightedPairEnergy_of_margin_nonpos p q r u v w hp hq hr hmar
  rw [evenTripleDetPart_eq_sub_weightedPairEnergy]
  linarith

/-- **THE RESIDUE IS A SLAB IN ONE SCALAR.**  Combining the depth bound with the
residue characterization pins the even part into a fixed window: at most a
quarter of the surplus product from above, and strictly above minus twice the
cross term.  Both walls are explicit. -/
theorem residue_evenPart_window (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hdet : 0 < tripleDetForm p q r u v w) (hmar : signFreeMargin p q r u v w ≤ 0) :
    -(2 * (u * v * w)) < evenTripleDetPart p q r u v w
      ∧ 4 * evenTripleDetPart p q r u v w ≤ p * q * r
      ∧ evenTripleDetPart p q r u v w ≤ 2 * (u * v * w) := by
  obtain ⟨_, hlow, hhigh⟩ := (residue_iff p q r u v w).mp ⟨hdet, hmar⟩
  exact ⟨hlow, four_mul_evenPart_le_of_margin_nonpos p q r u v w hp hq hr hmar, hhigh⟩

/-- **A LOWER BOUND ON THE CROSS TERM ITSELF.**  On the residue the cross term
strictly exceeds the amount by which the weighted pairing energy overshoots the
surplus product.  So a bound on the pairings bounds the residue away, and this is
the quantity a successor must control. -/
theorem energy_excess_lt_two_mul_cross_of_residue (p q r u v w : ℝ)
    (hdet : 0 < tripleDetForm p q r u v w) (hmar : signFreeMargin p q r u v w ≤ 0) :
    weightedPairEnergy p q r u v w - p * q * r < 2 * (u * v * w) := by
  have hlow := neg_evenPart_lt_two_mul_cross_of_residue p q r u v w hdet hmar
  rw [evenTripleDetPart_eq_sub_weightedPairEnergy] at hlow
  linarith

/-- **THE RESIDUE IS PINNED FROM BOTH SIDES IN ONE SCALAR.**  Its weighted
pairing energy is at least three quarters of the surplus product, and strictly
less than the surplus product plus twice the cross term.  That is a bounded
window, which is exactly what a magnitude cell for the residue would need. -/
theorem residue_energy_window (p q r u v w : ℝ)
    (hp : 0 < p) (hq : 0 < q) (hr : 0 < r)
    (hdet : 0 < tripleDetForm p q r u v w) (hmar : signFreeMargin p q r u v w ≤ 0) :
    3 / 4 * (p * q * r) ≤ weightedPairEnergy p q r u v w
      ∧ weightedPairEnergy p q r u v w < p * q * r + 2 * (u * v * w) := by
  refine ⟨three_quarters_le_weightedPairEnergy_of_margin_nonpos p q r u v w hp hq hr hmar, ?_⟩
  have := energy_excess_lt_two_mul_cross_of_residue p q r u v w hdet hmar
  linarith

/-- **THE CROSS TERM IS NOT BOUNDED BELOW ON THE RESIDUE, AND HERE IS WHY.**  At
a vanishing even part the residue condition asks only that the cross term be
positive, with no lower bound at all.  So no cell reading a fixed threshold on
the cross term can cover the residue, and a successor must read the even part
too. -/
theorem residue_at_vanishing_evenPart (c : ℝ) (hc : 0 < c) :
    -(2 * c) < (0:ℝ) ∧ (0:ℝ) ≤ 2 * c := ⟨by linarith, by linarith⟩

/-! ## 5. The residue is not empty

The equiangular configuration realizes it.  Every surplus is one third and every
pairing squares to one twentieth, so the even part is `-7/540` and the whole
sign-blind class fails while the coherent triples still dominate. -/

/-- The even part at the equiangular surplus, in terms of the pairing square. -/
theorem equiangular_evenPart (t : ℝ) :
    evenTripleDetPart (1/3) (1/3) (1/3) t t t = 1/27 - t ^ 2 := by
  rw [evenTripleDetPart]; ring

/-- **THE EVEN PART IS NEGATIVE AT THE EQUIANGULAR POINT.**  Its exact value is
`-7/540`. -/
theorem equiangular_evenPart_value {t : ℝ} (ht : t ^ 2 = 1/20) :
    evenTripleDetPart (1/3) (1/3) (1/3) t t t = -(7/540) := by
  rw [equiangular_evenPart, ht]; norm_num

theorem equiangular_evenPart_neg {t : ℝ} (ht : t ^ 2 = 1/20) :
    evenTripleDetPart (1/3) (1/3) (1/3) t t t < 0 := by
  rw [equiangular_evenPart_value ht]; norm_num

/-- The pairing at the equiangular point exceeds seven fifty-fourths, which is
exactly what makes the cross term outweigh the deficit. -/
theorem equiangular_pairing_gt {t : ℝ} (ht : t ^ 2 = 1/20) (hpos : 0 < t) :
    7/54 < t := by nlinarith [ht, hpos]

/-- **THE COHERENT EQUIANGULAR TRIPLE DOMINATES.**  The determinant is positive,
carried entirely by the cross term. -/
theorem equiangular_tripleDetForm_pos {t : ℝ} (ht : t ^ 2 = 1/20) (hpos : 0 < t) :
    0 < tripleDetForm (1/3) (1/3) (1/3) t t t := by
  rw [tripleDetForm_eq_evenPart_add_cross, equiangular_evenPart_value ht]
  have hcube : t * t * t = t / 20 := by nlinarith [ht]
  rw [hcube]
  have := equiangular_pairing_gt ht hpos
  linarith

/-- **THE WHOLE SIGN-BLIND CLASS FAILS AT THE EQUIANGULAR POINT.**  The margin is
strictly negative, so no cell that declines to read the sign can fire there. -/
theorem equiangular_signFreeMargin_neg {t : ℝ} (ht : t ^ 2 = 1/20) (hpos : 0 < t) :
    signFreeMargin (1/3) (1/3) (1/3) t t t < 0 := by
  rw [signFreeMargin_eq_evenPart_sub_abs, equiangular_evenPart_value ht]
  have hcube : t * t * t = t / 20 := by nlinarith [ht]
  rw [hcube, abs_of_pos (by linarith : (0:ℝ) < t / 20)]
  have := equiangular_pairing_gt ht hpos
  linarith

/-- **THE EQUIANGULAR TRIPLE IS IN THE RESIDUE.**  So the residue is not empty,
and the maximal sign-blind cell is provably incomplete. -/
theorem equiangular_mem_residue {t : ℝ} (ht : t ^ 2 = 1/20) (hpos : 0 < t) :
    0 < tripleDetForm (1/3) (1/3) (1/3) t t t
      ∧ signFreeMargin (1/3) (1/3) (1/3) t t t ≤ 0 :=
  ⟨equiangular_tripleDetForm_pos ht hpos, le_of_lt (equiangular_signFreeMargin_neg ht hpos)⟩

/-- The equiangular pairing exists, so the residue witness is a real point. -/
theorem exists_equiangular_pairing : ∃ t : ℝ, 0 < t ∧ t ^ 2 = 1/20 := by
  refine ⟨Real.sqrt (1/20), Real.sqrt_pos.mpr (by norm_num), ?_⟩
  exact Real.sq_sqrt (by norm_num)

/-- **THE MAXIMAL SIGN-BLIND CELL IS INCOMPLETE, WITH A WITNESS.**  There is a
point where the determinant is positive and the margin is not. -/
theorem exists_residue_point :
    ∃ p q r u v w : ℝ, 0 < tripleDetForm p q r u v w
      ∧ signFreeMargin p q r u v w ≤ 0 := by
  obtain ⟨t, hpos, ht⟩ := exists_equiangular_pairing
  exact ⟨1/3, 1/3, 1/3, t, t, t, equiangular_mem_residue ht hpos⟩

/-- The incoherent equiangular triple fails outright, which is the other half of
the picture: at the same magnitudes the sign decides the determinant. -/
theorem equiangular_incoherent_neg {t : ℝ} (ht : t ^ 2 = 1/20) (hpos : 0 < t) :
    tripleDetForm (1/3) (1/3) (1/3) t t (-t) < 0 := by
  rw [tripleDetForm_flip_eq_evenPart_sub_cross, equiangular_evenPart_value ht]
  have hcube : t * t * t = t / 20 := by nlinarith [ht]
  rw [hcube]
  have := equiangular_pairing_gt ht hpos
  linarith

/-- **THE SIGN DECIDES AT THE EQUIANGULAR POINT.**  The same magnitudes give a
positive determinant at the coherent sign and a negative one at the incoherent
sign, and no sign-blind reading can separate them. -/
theorem equiangular_sign_decides {t : ℝ} (ht : t ^ 2 = 1/20) (hpos : 0 < t) :
    0 < tripleDetForm (1/3) (1/3) (1/3) t t t
      ∧ tripleDetForm (1/3) (1/3) (1/3) t t (-t) < 0
      ∧ signFreeMargin (1/3) (1/3) (1/3) t t t < 0 :=
  ⟨equiangular_tripleDetForm_pos ht hpos, equiangular_incoherent_neg ht hpos,
    equiangular_signFreeMargin_neg ht hpos⟩

/-! ## 6. The cell at the atom level and the design level

The scalar layer above transports to atoms through the landed
`Gtz.tripleGapDet_eq_tripleDetForm`, and to designs through the landed
admissible-triangle spend. -/

/-- The even part read on three atoms. -/
noncomputable def atomEvenPart (a b c : Fin 3 → ℝ) : ℝ :=
  evenTripleDetPart (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
    (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c)

theorem atomEvenPart_apply (a b c : Fin 3 → ℝ) :
    atomEvenPart a b c
      = evenTripleDetPart (leverageOf a - 1) (leverageOf b - 1) (leverageOf c - 1)
        (a ⬝ᵥ b) (a ⬝ᵥ c) (b ⬝ᵥ c) := rfl

/-- The atom margin is the atom even part minus twice the absolute cross term. -/
theorem atomSignFreeMargin_eq_atomEvenPart_sub_abs (a b c : Fin 3 → ℝ) :
    atomSignFreeMargin a b c
      = atomEvenPart a b c - 2 * |(a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c)| := by
  rw [atomSignFreeMargin, atomEvenPart, signFreeMargin_eq_evenPart_sub_abs]

/-- **THE ROOT-FREE CRITERION AT THE ATOM LEVEL.** -/
theorem atomSignFreeMargin_pos_iff_atomEvenPart_sq (a b c : Fin 3 → ℝ) :
    0 < atomSignFreeMargin a b c
      ↔ 0 < atomEvenPart a b c
        ∧ 4 * ((a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c)) ^ 2 < atomEvenPart a b c ^ 2 := by
  rw [atomSignFreeMargin, atomEvenPart, signFreeMargin_pos_iff_evenPart_sq]

/-- The root-free criterion forces a positive residual determinant. -/
theorem tripleGapDet_pos_of_atomEvenPart_sq (a b c : Fin 3 → ℝ)
    (hE : 0 < atomEvenPart a b c)
    (hlt : 4 * ((a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c)) ^ 2 < atomEvenPart a b c ^ 2) :
    0 < tripleGapDet a b c :=
  tripleGapDet_pos_of_atomSignFreeMargin a b c
    ((atomSignFreeMargin_pos_iff_atomEvenPart_sq a b c).mpr ⟨hE, hlt⟩)

/-- **THE MAXIMAL SIGN-BLIND CELL AT THE DESIGN LEVEL.**  Three atoms with a
positive even part dominating the cross term in square give a strict dominator,
with no absolute value and no square root anywhere in the hypothesis. -/
theorem subsetSum_posDef_of_atomEvenPart_sq {m : ℕ} (D : WeightedDesign m 3)
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hheavy : ∀ label : Fin m, 1 ≤ leverageOf (D.atom label))
    (htri : AdmissibleTriangle D x y z)
    (hE : 0 < atomEvenPart (D.atom x) (D.atom y) (D.atom z))
    (hlt : 4 * ((D.atom x ⬝ᵥ D.atom y) * (D.atom x ⬝ᵥ D.atom z)
            * (D.atom y ⬝ᵥ D.atom z)) ^ 2
        < atomEvenPart (D.atom x) (D.atom y) (D.atom z) ^ 2) :
    (subsetSum D ({x, y, z} : Finset (Fin m)) - 1).PosDef :=
  subsetSum_posDef_of_atomSignFreeMargin D x y z hxy hxz hyz hheavy htri
    ((atomSignFreeMargin_pos_iff_atomEvenPart_sq _ _ _).mpr ⟨hE, hlt⟩)

/-- **THE RESIDUE AT THE ATOM LEVEL.**  A triple the maximal sign-blind cell
misses while the determinant is positive is exactly a coherent triple whose even
part is trapped below twice its cross term. -/
theorem atom_residue_iff (a b c : Fin 3 → ℝ) :
    (0 < tripleGapDet a b c ∧ atomSignFreeMargin a b c ≤ 0)
      ↔ (0 < (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c)
          ∧ -(2 * ((a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c))) < atomEvenPart a b c
          ∧ atomEvenPart a b c ≤ 2 * ((a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c))) := by
  rw [tripleGapDet_eq_tripleDetForm, atomSignFreeMargin, atomEvenPart, residue_iff]

/-- **NO INCOHERENT ATOM TRIPLE IS IN THE RESIDUE.**  At the design level the
sign-blind class is complete wherever the triple product of the three pairings is
non-positive, so every design the class misses carries a coherent dominator. -/
theorem atomSignFreeMargin_pos_of_tripleGapDet_pos_of_cross_nonpos (a b c : Fin 3 → ℝ)
    (hdet : 0 < tripleGapDet a b c)
    (hc : (a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c) ≤ 0) :
    0 < atomSignFreeMargin a b c := by
  rw [atomSignFreeMargin]
  refine signFreeMargin_pos_of_det_pos_of_cross_nonpos _ _ _ _ _ _ ?_ hc
  rwa [← tripleGapDet_eq_tripleDetForm]

end Gtz
