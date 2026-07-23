/-
# Theorem V: the moment covector of a tight cluster triangle

The covector whose existence the chord/completeness layer rests on — and which
`TightGraph` currently takes as a hypothesis. At a pairwise-tight triangle of
clusters there is a moment vector `ξ` with

  `⟨ξ, u_X⟩ = ν_X − 1/2`  for each cluster `X`,

so that the conic relation `ν = 1/2 + ⟨ξ,u⟩` holds at all three.

MECHANIZATION FINDING (the informal proof hides this): tightness of the three
pairs does NOT by itself give the covector. Eliminating the geometry leaves a
PRODUCT of two factors, exactly one of which vanishes:

  `spreadRelation ν = 2ν_Aν_Bν_C + ν_Aν_B + ν_Aν_C + ν_Bν_C − 1`   (the cyclic,
     "the three directions surround the origin" branch — the family), and
  `coSpreadRelation ν = 2ν_Aν_Bν_C − ν_Aν_B − ν_Aν_C − ν_Bν_C + 1` (the
     half-plane branch).

The informal argument works in the angle parameterization `p + q + r = π`,
which silently ASSUMES the cyclic branch. Here the branch is SELECTED, not
assumed, and the selector is elementary: in co-leverage coordinates
`x = 1 − ν = 1/ℓ`,

  `coSpreadRelation = xy(1−z) + xz(1−y) + yz`,   equivalently
  `coSpreadRelation · ℓ_Aℓ_Bℓ_C = ℓ_A + ℓ_B + ℓ_C − 2`,

which is STRICTLY POSITIVE as soon as the three leverages sum past two — so the
half-plane branch is impossible for genuine atoms and the spread relation must
hold. That replaces the informal trigonometric "acuteness is forced" step with
a two-line inequality.
-/
import Mathlib
import Gtz.PsdKit
import Gtz.Pushoff

namespace Gtz

open Matrix

/-! ### The two branches -/

/-- The **spread relation**: the cyclic branch, satisfied by every genuine
tight cluster triangle. -/
def spreadRelation (firstConic secondConic thirdConic : ℝ) : ℝ :=
  2 * firstConic * secondConic * thirdConic + firstConic * secondConic
    + firstConic * thirdConic + secondConic * thirdConic - 1

/-- The **co-spread relation**: the half-plane branch, which genuine atoms
cannot satisfy. -/
def coSpreadRelation (firstConic secondConic thirdConic : ℝ) : ℝ :=
  2 * firstConic * secondConic * thirdConic - firstConic * secondConic
    - firstConic * thirdConic - secondConic * thirdConic + 1

/-- In co-leverage coordinates `x = 1 − ν` the co-spread relation is a sum of
three products — visibly positive when the co-leverages are in the unit
interval. -/
theorem coSpreadRelation_eq_coLeverage (firstCo secondCo thirdCo : ℝ) :
    coSpreadRelation (1 - firstCo) (1 - secondCo) (1 - thirdCo)
      = firstCo * secondCo * (1 - thirdCo) + firstCo * thirdCo * (1 - secondCo)
        + secondCo * thirdCo := by
  simp only [coSpreadRelation]
  ring

/-- **The branch selector, leverage form**: scaled by the leverage product, the
co-spread relation is `ℓ_A + ℓ_B + ℓ_C − 2`. -/
theorem coSpreadRelation_mul_leverages (firstLev secondLev thirdLev : ℝ)
    (hfirst : firstLev ≠ 0) (hsecond : secondLev ≠ 0) (hthird : thirdLev ≠ 0) :
    coSpreadRelation (1 - 1 / firstLev) (1 - 1 / secondLev) (1 - 1 / thirdLev)
        * (firstLev * secondLev * thirdLev)
      = firstLev + secondLev + thirdLev - 2 := by
  simp only [coSpreadRelation]
  field_simp
  ring

/-- **The half-plane branch is impossible for genuine atoms**: leverages above
one make the co-spread relation strictly positive. -/
theorem coSpreadRelation_pos_of_heavy {firstLev secondLev thirdLev : ℝ}
    (hfirst : 1 < firstLev) (hsecond : 1 < secondLev) (hthird : 1 < thirdLev) :
    0 < coSpreadRelation (1 - 1 / firstLev) (1 - 1 / secondLev)
      (1 - 1 / thirdLev) := by
  have hfirstPos : (0 : ℝ) < firstLev := by linarith
  have hsecondPos : (0 : ℝ) < secondLev := by linarith
  have hthirdPos : (0 : ℝ) < thirdLev := by linarith
  have hscaled := coSpreadRelation_mul_leverages firstLev secondLev thirdLev
    (ne_of_gt hfirstPos) (ne_of_gt hsecondPos) (ne_of_gt hthirdPos)
  have hprodPos : 0 < firstLev * secondLev * thirdLev := by positivity
  nlinarith [hscaled, hprodPos]

/-! ### The elimination: tightness forces one of the two branches -/

/-- **The branch identity.** For a triangle whose third direction decomposes as
`u_C = s·u_A + t·u_B`, the three tightness relations plus the unit length of
`u_C` force the PRODUCT of the two branch relations to vanish (up to the
nonvanishing factor `16 ν_Aν_B(ν_Aν_B − 1)`). Everything is polynomial: the
hypotheses are the two tightness equations read through the decomposition and
the unit-length equation. -/
theorem branchProduct_eq_zero {firstCoord secondCoord pairing firstConic
    secondConic thirdConic : ℝ}
    (hpairing : pairing = 2 * firstConic * secondConic - 1)
    (htightFirst : firstCoord + secondCoord * pairing
      = 2 * thirdConic * firstConic - 1)
    (htightSecond : firstCoord * pairing + secondCoord
      = 2 * thirdConic * secondConic - 1)
    (hunit : firstCoord ^ 2 + 2 * firstCoord * secondCoord * pairing
      + secondCoord ^ 2 = 1) :
    16 * firstConic * secondConic * (firstConic * secondConic - 1)
        * coSpreadRelation firstConic secondConic thirdConic
        * spreadRelation firstConic secondConic thirdConic
      = 0 := by
  subst hpairing
  set alongFirst : ℝ := 2 * thirdConic * firstConic - 1 with halongFirst
  set alongSecond : ℝ := 2 * thirdConic * secondConic - 1 with halongSecond
  set gram : ℝ := 2 * firstConic * secondConic - 1 with hgram
  -- Solve the two linear tightness equations for the decomposition coefficients.
  have hsolveFirst : (1 - gram ^ 2) * firstCoord
      = alongFirst - alongSecond * gram := by
    linear_combination htightFirst - gram * htightSecond
  have hsolveSecond : (1 - gram ^ 2) * secondCoord
      = alongSecond - alongFirst * gram := by
    linear_combination htightSecond - gram * htightFirst
  -- Substituting into the unit-length equation eliminates the coefficients and
  -- leaves exactly the product of the two branch relations.
  have helim : (alongFirst - alongSecond * gram) ^ 2
      + 2 * (alongFirst - alongSecond * gram)
        * (alongSecond - alongFirst * gram) * gram
      + (alongSecond - alongFirst * gram) ^ 2 - (1 - gram ^ 2) ^ 2 = 0 := by
    linear_combination (1 - gram ^ 2) ^ 2 * hunit
      + (-((1 - gram ^ 2) * firstCoord) - alongFirst
        + 2 * alongFirst * gram ^ 2 - alongSecond * gram) * hsolveFirst
      + (-((1 - gram ^ 2) * secondCoord) - alongSecond + alongFirst * gram
        - 2 * gram * ((1 - gram ^ 2) * firstCoord)) * hsolveSecond
  simp only [coSpreadRelation, spreadRelation, halongFirst, halongSecond,
    hgram] at *
  linear_combination helim

/-- **Theorem V, the branch selection**: at a tight cluster triangle of genuine
(heavy) atoms, the spread relation holds. The half-plane branch is excluded by
the leverage sum, so the cyclic branch is forced — no acuteness assumption. -/
theorem spreadRelation_eq_zero_of_tight {firstCoord secondCoord pairing
    firstLev secondLev thirdLev : ℝ}
    (hfirstLev : 1 < firstLev) (hsecondLev : 1 < secondLev)
    (hthirdLev : 1 < thirdLev)
    (hpairing : pairing = 2 * (1 - 1 / firstLev) * (1 - 1 / secondLev) - 1)
    (htightFirst : firstCoord + secondCoord * pairing
      = 2 * (1 - 1 / thirdLev) * (1 - 1 / firstLev) - 1)
    (htightSecond : firstCoord * pairing + secondCoord
      = 2 * (1 - 1 / thirdLev) * (1 - 1 / secondLev) - 1)
    (hunit : firstCoord ^ 2 + 2 * firstCoord * secondCoord * pairing
      + secondCoord ^ 2 = 1) :
    spreadRelation (1 - 1 / firstLev) (1 - 1 / secondLev) (1 - 1 / thirdLev)
      = 0 := by
  have hproduct := branchProduct_eq_zero hpairing htightFirst htightSecond hunit
  have hco := coSpreadRelation_pos_of_heavy hfirstLev hsecondLev hthirdLev
  have hfirstConicPos : (0 : ℝ) < 1 - 1 / firstLev := by
    have : 1 / firstLev < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    linarith
  have hsecondConicPos : (0 : ℝ) < 1 - 1 / secondLev := by
    have : 1 / secondLev < 1 := by
      rw [div_lt_one (by linarith)]; linarith
    linarith
  -- Heaviness also caps each conic value below one, so the product is below
  -- one and the gap factor cannot vanish.
  have hfirstConicLt : 1 - 1 / firstLev < 1 := by
    have : (0 : ℝ) < 1 / firstLev := by positivity
    linarith
  have hsecondConicLt : 1 - 1 / secondLev < 1 := by
    have : (0 : ℝ) < 1 / secondLev := by positivity
    linarith
  have hgap : (1 - 1 / firstLev) * (1 - 1 / secondLev) - 1 ≠ 0 := by
    have hlt : (1 - 1 / firstLev) * (1 - 1 / secondLev) < 1 := by
      nlinarith [hfirstConicPos, hsecondConicPos, hfirstConicLt, hsecondConicLt]
    exact ne_of_lt (by linarith)
  have hfactor : (16 : ℝ) * (1 - 1 / firstLev) * (1 - 1 / secondLev)
      * ((1 - 1 / firstLev) * (1 - 1 / secondLev) - 1)
      * coSpreadRelation (1 - 1 / firstLev) (1 - 1 / secondLev)
        (1 - 1 / thirdLev) ≠ 0 := by
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ ?_) ?_) hgap)
      (ne_of_gt hco)
    · norm_num
    · exact ne_of_gt hfirstConicPos
    · exact ne_of_gt hsecondConicPos
  exact (mul_eq_zero.mp hproduct).resolve_left hfactor

/-! ### The covector itself -/

/-- **Theorem V, the propagation step**: once the spread relation holds, the
covector fitted to the first two clusters automatically fits the third. The
decomposition `u_C = s·u_A + t·u_B` turns the desired conic relation at `C`
into the linear identity `s(ν_A − 1/2) + t(ν_B − 1/2) = ν_C − 1/2`, and the
two tightness equations determine `s, t` uniquely; the residual is exactly
`−2(ν_A − 1)(ν_B − 1)` times the spread relation. So a single `ξ` solving the
two-cluster system is the covector of the whole triangle — which is precisely
what the chord and completeness arguments consume. -/
theorem thirdConic_of_spread {firstCoord secondCoord pairing firstConic
    secondConic thirdConic : ℝ}
    (hfirstNe : firstConic ≠ 0) (hsecondNe : secondConic ≠ 0)
    (hproductNe : firstConic * secondConic ≠ 1)
    (hpairing : pairing = 2 * firstConic * secondConic - 1)
    (htightFirst : firstCoord + secondCoord * pairing
      = 2 * thirdConic * firstConic - 1)
    (htightSecond : firstCoord * pairing + secondCoord
      = 2 * thirdConic * secondConic - 1)
    (hspread : spreadRelation firstConic secondConic thirdConic = 0) :
    firstCoord * (firstConic - 1/2) + secondCoord * (secondConic - 1/2)
      = thirdConic - 1/2 := by
  subst hpairing
  simp only [spreadRelation] at hspread
  set gram : ℝ := 2 * firstConic * secondConic - 1 with hgram
  -- Cramer's rule on the two tightness equations.
  have hsolveFirst : (1 - gram ^ 2) * firstCoord
      = (2 * thirdConic * firstConic - 1)
        - (2 * thirdConic * secondConic - 1) * gram := by
    linear_combination htightFirst - gram * htightSecond
  have hsolveSecond : (1 - gram ^ 2) * secondCoord
      = (2 * thirdConic * secondConic - 1)
        - (2 * thirdConic * firstConic - 1) * gram := by
    linear_combination htightSecond - gram * htightFirst
  -- The Gram determinant `1 − gram²` is `4ν_Aν_B(1 − ν_Aν_B)`, nonzero exactly
  -- when the two directions are independent.
  have hdet : (1 : ℝ) - gram ^ 2 ≠ 0 := by
    have hfactor : (1 : ℝ) - gram ^ 2
        = 4 * firstConic * secondConic * (1 - firstConic * secondConic) := by
      rw [hgram]; ring
    rw [hfactor]
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero ?_ hfirstNe) hsecondNe) ?_
    · norm_num
    · exact sub_ne_zero.mpr (Ne.symm hproductNe)
  -- The scaled discrepancy is a multiple of the spread relation.
  have hkey : (1 - gram ^ 2)
      * (firstCoord * (firstConic - 1/2) + secondCoord * (secondConic - 1/2)
        - (thirdConic - 1/2)) = 0 := by
    rw [hgram]
    rw [hgram] at hsolveFirst hsolveSecond
    linear_combination (firstConic - 1/2) * hsolveFirst
      + (secondConic - 1/2) * hsolveSecond
      - 2 * (firstConic - 1) * (secondConic - 1) * hspread
  have hzero := (mul_eq_zero.mp hkey).resolve_left hdet
  linarith

end Gtz
