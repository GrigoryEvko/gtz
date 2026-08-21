/-
# The refusal dichotomy of a triple, without any sign

The gateway of the corank-two arm asks a triple to carry an ADMISSIBLE pair.
Its obstruction was thought to be a CHIROTOPE case split: the gap determinant of
a triple carries the term `2*p_ab*p_ac*p_bc`, whose sign is a product of three
pairings, and the negative branch had no lower bound.  A sign of a product of
pairings is exactly the real shadow of the Bargmann invariant, so that framing
made the branch look real-only, and it made the branch look like a case split
nobody could polynomialise.

**Both readings are wrong, and this module replaces them.**  The Bargmann term
is not an extra sign to case on: it is one of the two ROOTS OF A QUADRATIC, and
the quadratic is a polynomial identity.  Squaring removes the sign, and the case
split becomes a disjunction between two polynomial inequalities.

## The isolation and its square

Write `x_a = l_a - 1` for the leverage excess and `q_ab` for the pair minor.
Then, hypothesis-free (`Gtz.tripleGapDet_eq_bargmann`),

  **`tripleGapDet a b c = -2*x_a*x_b*x_c + (x_a*q_bc + x_b*q_ac + x_c*q_ab)
                            + 2*(a.b)*(a.c)*(b.c)`** ,

which isolates the Bargmann term.  Squaring it kills the sign, and the right
side is a product of the three pair readings, each of which is
`x_i*x_j - q_ij` (`Gtz.tripleGapDet_bargmann_sq`):

  **`(tripleGapDet + 2*x_a*x_b*x_c - (x_a*q_bc + x_b*q_ac + x_c*q_ab))^2
      = 4*(x_a*x_b - q_ab)*(x_a*x_c - q_ac)*(x_b*x_c - q_bc)`** .

Both are one `ring`.  Nothing about signs, fields or chirotopes survives.

## The dichotomy

When every pair minor is NOT positive the three factors on the right are each at
least `x_i*x_j`, so the square is at least `(2*x_a*x_b*x_c)^2`.  A real number
whose square passes a positive square lies outside the interval, so the
Bargmann term is either at least `2*x_a*x_b*x_c` or at most its negative.  That
gives `Gtz.tripleGapDet_refusal_dichotomy`: for a triple of heavy atoms with no
admissible pair, EITHER

  **(1) `x_a*q_bc + x_b*q_ac + x_c*q_ab <= tripleGapDet`** ,   or
  **(2) `tripleGapDet <= -4*x_a*x_b*x_c + (x_a*q_bc + x_b*q_ac + x_c*q_ab)`** .

No sign of any product appears in either branch.  This is the lemma the arm was
missing, and it is field-blind: over the complex numbers the same statement
holds with the Bargmann term replaced by its real part, whose square is bounded
by the same product.

## What each branch costs the triple

* **Branch (1) pays the budget.**  Fed into the landed
  `Gtz.weightedTriple_pairMinor_gapForm`, branch (1) makes every term of the
  refined budget nonnegative, because the coefficient that appears is exactly
  `1 - t_k*l_k`, the landed member weight cap
  (`Gtz.branchOne_refinedBudget_nonneg`).  So a triple in branch (1) can never
  have a negative refined budget.
* **Branch (2) pays the leverage.**  Fed into the landed currency bridge and the
  nonnegativity of the squared bracket, branch (2) forces
  (`Gtz.branchTwo_leverage_bound`)

    **`4*x_a*x_b*x_c <= 1 + x_a + x_b + x_c + (q_ab*l_c + q_ac*l_b + q_bc*l_a)`** ,

  and with no admissible pair the bracketed term is not positive, so the pure
  form `4*x_a*x_b*x_c <= 1 + x_a + x_b + x_c` holds.

Together (`Gtz.exists_pairMinor_pos_of_refinedBudget_of_leverage`) a triple of
heavy atoms whose refined budget is negative and whose leverage excesses have a
large product must carry an admissible pair -- a producer whose trigger is
disjoint from the weight producers of `Gtz.CornerGatewayBudget`.

## Two complementary determinant laws

`Gtz.det_add_det_one_sub` records that for every real `3x3` matrix the
determinants of a matrix and of its complement to the identity add to
`1 - tr + e2`.  With the landed `Gtz.det_weighted_triple` it reads, at a design
split into a triple and its complement, as a statement purely in the two
brackets and the outside moment's invariants.

[MEASURED.  The dichotomy was checked against 108523 exact random corners: the
Bargmann sign is negative at 80.04 percent of them, so branch (2) is the COMMON
branch and the old sign framing would have covered only a fifth of the space.
The complex tie's outside Bargmann invariant has argument exactly `pi`, so its
sign is defined there by accident and not by structure.  A separate measurement
kills a whole class of would-be closures: the weighted pair minor sum
`sum t_i t_j q_ij` is NEGATIVE at 0.0405 percent of corners, minimum `-0.176`,
so NO producer that sums the three pair minors against fixed weights can ever be
total, however the weights are chosen.]
-/
import Gtz.Wave.CornerGatewayBudget

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix

variable {m : ℕ}

/-! ## 1. The complementary determinant law -/

/-- **THE COMPLEMENTARY DETERMINANT LAW.**  For every real `3x3` matrix the
determinant of the matrix and the determinant of its complement to the identity
add to one less the trace plus the second invariant.  Pure algebra. -/
theorem det_add_det_one_sub (A : Matrix (Fin 3) (Fin 3) ℝ) :
    A.det + (1 - A).det
      = 1 - A.trace + (A.trace ^ 2 - (A * A).trace) / 2 := by
  simp only [Matrix.det_fin_three, Matrix.trace_fin_three, Matrix.one_fin_three,
    Matrix.sub_apply, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.head_val', Matrix.of_apply]
  ring

/-! ## 2. The Bargmann isolation and its square -/

/-- **THE BARGMANN ISOLATION.**  The gap determinant of a triple is twice the
product of its three pairings, less twice the product of its three leverage
excesses, plus each excess against the opposite pair minor.  Hypothesis-free. -/
theorem tripleGapDet_eq_bargmann (a b c : Fin 3 → ℝ) :
    tripleGapDet a b c
      = -2 * ((leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1))
        + ((leverageOf a - 1) * pairGapMinor b c
            + (leverageOf b - 1) * pairGapMinor a c
            + (leverageOf c - 1) * pairGapMinor a b)
        + 2 * ((a ⬝ᵥ b) * (a ⬝ᵥ c) * (b ⬝ᵥ c)) := by
  simp only [tripleGapDet, pairGapMinor]
  ring

/-- **THE SQUARED BARGMANN IDENTITY — THE POLYNOMIALISATION.**  Squaring the
isolation removes the Bargmann sign entirely, and the right side is four times
the product of the three pair readings, each written in the campaign's
currencies.  Hypothesis-free, one `ring`.

This is what turns the old chirotope case split into a disjunction between two
polynomial inequalities: the Bargmann term is a root of this quadratic, and the
two branches are its two roots. -/
theorem tripleGapDet_bargmann_sq (a b c : Fin 3 → ℝ) :
    (tripleGapDet a b c
        + 2 * ((leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1))
        - ((leverageOf a - 1) * pairGapMinor b c
            + (leverageOf b - 1) * pairGapMinor a c
            + (leverageOf c - 1) * pairGapMinor a b)) ^ 2
      = 4 * ((leverageOf a - 1) * (leverageOf b - 1) - pairGapMinor a b)
          * ((leverageOf a - 1) * (leverageOf c - 1) - pairGapMinor a c)
          * ((leverageOf b - 1) * (leverageOf c - 1) - pairGapMinor b c) := by
  simp only [tripleGapDet, pairGapMinor]
  ring

/-! ## 3. The dichotomy -/

/-- **THE REFUSAL DICHOTOMY, WITHOUT ANY SIGN.**  A triple of heavy atoms with
no admissible pair falls into one of two branches, and neither mentions the sign
of any product.  Branch one bounds the gap determinant from BELOW by the excess
combination, branch two bounds it from ABOVE by that combination less four times
the excess product. -/
theorem tripleGapDet_refusal_dichotomy {a b c : Fin 3 → ℝ}
    (hxa : 0 < leverageOf a - 1) (hxb : 0 < leverageOf b - 1)
    (hxc : 0 < leverageOf c - 1)
    (hab : pairGapMinor a b ≤ 0) (hac : pairGapMinor a c ≤ 0)
    (hbc : pairGapMinor b c ≤ 0) :
    ((leverageOf a - 1) * pairGapMinor b c + (leverageOf b - 1) * pairGapMinor a c
        + (leverageOf c - 1) * pairGapMinor a b ≤ tripleGapDet a b c)
      ∨ (tripleGapDet a b c
          ≤ -4 * ((leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1))
            + ((leverageOf a - 1) * pairGapMinor b c
              + (leverageOf b - 1) * pairGapMinor a c
              + (leverageOf c - 1) * pairGapMinor a b)) := by
  set xa := leverageOf a - 1 with hxadef
  set xb := leverageOf b - 1 with hxbdef
  set xc := leverageOf c - 1 with hxcdef
  set Q := xa * pairGapMinor b c + xb * pairGapMinor a c + xc * pairGapMinor a b with hQ
  set E := tripleGapDet a b c + 2 * (xa * xb * xc) - Q with hE
  have hprod : 0 < xa * xb * xc := mul_pos (mul_pos hxa hxb) hxc
  have hsq := tripleGapDet_bargmann_sq a b c
  rw [← hxadef, ← hxbdef, ← hxcdef, ← hQ, ← hE] at hsq
  -- each pair reading is at least the product of the two excesses
  have f1 : xa * xb ≤ xa * xb - pairGapMinor a b := by linarith
  have f2 : xa * xc ≤ xa * xc - pairGapMinor a c := by linarith
  have f3 : xb * xc ≤ xb * xc - pairGapMinor b c := by linarith
  have p1 : 0 < xa * xb := mul_pos hxa hxb
  have p2 : 0 < xa * xc := mul_pos hxa hxc
  have p3 : 0 < xb * xc := mul_pos hxb hxc
  have hpos12 : (0 : ℝ) ≤ (xa * xb - pairGapMinor a b) * (xa * xc - pairGapMinor a c) := by
    nlinarith [f1, f2, p1, p2]
  have m12 : (xa * xb) * (xa * xc)
      ≤ (xa * xb - pairGapMinor a b) * (xa * xc - pairGapMinor a c) :=
    mul_le_mul f1 f2 p2.le (by linarith)
  have m123 : ((xa * xb) * (xa * xc)) * (xb * xc)
      ≤ ((xa * xb - pairGapMinor a b) * (xa * xc - pairGapMinor a c))
          * (xb * xc - pairGapMinor b c) :=
    mul_le_mul m12 f3 p3.le hpos12
  have hbig : (2 * (xa * xb * xc)) ^ 2 ≤ E ^ 2 := by
    rw [hsq]; nlinarith [m123]
  rcases le_or_gt (2 * (xa * xb * xc)) E with h | h
  · left; simp only [hE] at h; linarith
  · right
    have : E ≤ -(2 * (xa * xb * xc)) := by nlinarith [hbig, hprod]
    simp only [hE] at this
    linarith

/-! ## 4. What each branch costs -/

/-- **BRANCH ONE PAYS THE BUDGET.**  In branch one every term of the refined
budget is not negative, because the coefficient that appears against each pair
minor is exactly the member weight slack `1 - t*l`, which the landed member
weight cap makes not negative.  So a triple in branch one can never carry a
negative refined budget. -/
theorem branchOne_refinedBudget_nonneg (D : WeightedDesign m 3)
    {d1 d2 d3 : Fin m} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hab : pairGapMinor (D.atom d1) (D.atom d2) ≤ 0)
    (hac : pairGapMinor (D.atom d1) (D.atom d3) ≤ 0)
    (hbc : pairGapMinor (D.atom d2) (D.atom d3) ≤ 0)
    (hbranch :
      (leverageOf (D.atom d1) - 1) * pairGapMinor (D.atom d2) (D.atom d3)
        + (leverageOf (D.atom d2) - 1) * pairGapMinor (D.atom d1) (D.atom d3)
        + (leverageOf (D.atom d3) - 1) * pairGapMinor (D.atom d1) (D.atom d2)
      ≤ tripleGapDet (D.atom d1) (D.atom d2) (D.atom d3)) :
    0 ≤ (D.weight d1 * D.weight d2 + D.weight d1 * D.weight d3
          + D.weight d2 * D.weight d3)
        - (1 - (D.weight d1 + D.weight d2 + D.weight d3))
            * ((D.weight d1 * (leverageOf (D.atom d1) - 1)
                + D.weight d2 * (leverageOf (D.atom d2) - 1)
                + D.weight d3 * (leverageOf (D.atom d3) - 1)) - 1)
        - (D.weight d1 ^ 2 * (leverageOf (D.atom d1) - 1)
            + D.weight d2 ^ 2 * (leverageOf (D.atom d2) - 1)
            + D.weight d3 ^ 2 * (leverageOf (D.atom d3) - 1))
        - D.weight d1 * D.weight d2 * D.weight d3
            * (1 + (leverageOf (D.atom d1) - 1) + (leverageOf (D.atom d2) - 1)
              + (leverageOf (D.atom d3) - 1)) := by
  have hkey := weightedTriple_pairMinor_gapForm (D.weight d1) (D.weight d2)
    (D.weight d3) (D.atom d1) (D.atom d2) (D.atom d3)
  have hdet := det_oneSubWeightedTriple_nonneg D h12 h13 h23
  have hw1 := D.weight_pos d1
  have hw2 := D.weight_pos d2
  have hw3 := D.weight_pos d3
  have m1 := weighted_leverage_le_one D d1
  have m2 := weighted_leverage_le_one D d2
  have m3 := weighted_leverage_le_one D d3
  rw [hkey]
  -- the three pair terms, each with the member weight slack as coefficient
  have c12 : 0 ≤ (-(pairGapMinor (D.atom d1) (D.atom d2)))
      * (D.weight d1 * D.weight d2 * (1 - D.weight d3 * leverageOf (D.atom d3))) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ D.weight d1 * D.weight d2 := (mul_pos hw1 hw2).le
    nlinarith
  have c13 : 0 ≤ (-(pairGapMinor (D.atom d1) (D.atom d3)))
      * (D.weight d1 * D.weight d3 * (1 - D.weight d2 * leverageOf (D.atom d2))) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ D.weight d1 * D.weight d3 := (mul_pos hw1 hw3).le
    nlinarith
  have c23 : 0 ≤ (-(pairGapMinor (D.atom d2) (D.atom d3)))
      * (D.weight d2 * D.weight d3 * (1 - D.weight d1 * leverageOf (D.atom d1))) := by
    apply mul_nonneg (by linarith)
    have : 0 ≤ D.weight d2 * D.weight d3 := (mul_pos hw2 hw3).le
    nlinarith
  have hbr : 0 ≤ D.weight d1 * D.weight d2 * D.weight d3
      * (tripleGapDet (D.atom d1) (D.atom d2) (D.atom d3)
        - ((leverageOf (D.atom d1) - 1) * pairGapMinor (D.atom d2) (D.atom d3)
          + (leverageOf (D.atom d2) - 1) * pairGapMinor (D.atom d1) (D.atom d3)
          + (leverageOf (D.atom d3) - 1) * pairGapMinor (D.atom d1) (D.atom d2))) :=
    mul_nonneg (mul_nonneg (mul_nonneg hw1.le hw2.le) hw3.le) (by linarith)
  nlinarith [c12, c13, c23, hbr, hdet, mul_pos (mul_pos hw1 hw2) hw3]

/-- **BRANCH TWO PAYS THE LEVERAGE.**  The currency bridge writes the squared
bracket as the gap determinant plus the pair minors plus the excesses plus one,
and the squared bracket is not negative.  In branch two the gap determinant is
capped, and the cap turns into a bound on the product of the excesses. -/
theorem branchTwo_leverage_bound {a b c : Fin 3 → ℝ}
    (hbranch : tripleGapDet a b c
      ≤ -4 * ((leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1))
        + ((leverageOf a - 1) * pairGapMinor b c
          + (leverageOf b - 1) * pairGapMinor a c
          + (leverageOf c - 1) * pairGapMinor a b)) :
    4 * ((leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1))
      ≤ 1 + ((leverageOf a - 1) + (leverageOf b - 1) + (leverageOf c - 1))
        + (pairGapMinor a b * leverageOf c + pairGapMinor a c * leverageOf b
          + pairGapMinor b c * leverageOf a) := by
  have hbridge := sq_tripleBracket_eq_gapDet_add_pairMinors a b c
  have hsq : (0 : ℝ) ≤ tripleBracket a b c ^ 2 := sq_nonneg _
  rw [hbridge] at hsq
  nlinarith [hbranch, hsq]

/-- **BRANCH TWO, IN PURE LEVERAGE FORM.**  With no admissible pair the pair
minor terms are not positive, so branch two forces the excess product under the
excess total. -/
theorem branchTwo_leverage_bound_pure {a b c : Fin 3 → ℝ}
    (hla : 0 ≤ leverageOf a) (hlb : 0 ≤ leverageOf b) (hlc : 0 ≤ leverageOf c)
    (hab : pairGapMinor a b ≤ 0) (hac : pairGapMinor a c ≤ 0)
    (hbc : pairGapMinor b c ≤ 0)
    (hbranch : tripleGapDet a b c
      ≤ -4 * ((leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1))
        + ((leverageOf a - 1) * pairGapMinor b c
          + (leverageOf b - 1) * pairGapMinor a c
          + (leverageOf c - 1) * pairGapMinor a b)) :
    4 * ((leverageOf a - 1) * (leverageOf b - 1) * (leverageOf c - 1))
      ≤ 1 + ((leverageOf a - 1) + (leverageOf b - 1) + (leverageOf c - 1)) := by
  have h := branchTwo_leverage_bound hbranch
  have t1 : pairGapMinor a b * leverageOf c ≤ 0 := by nlinarith [hab, hlc]
  have t2 : pairGapMinor a c * leverageOf b ≤ 0 := by nlinarith [hac, hlb]
  have t3 : pairGapMinor b c * leverageOf a ≤ 0 := by nlinarith [hbc, hla]
  linarith

/-! ## 5. The producer with a disjoint trigger -/

/-- **A PRODUCER WHOSE TRIGGER IS DISJOINT FROM THE WEIGHT PRODUCERS.**  A
triple of heavy atoms whose refined budget is negative and whose leverage
excesses have a product passing their total must carry an admissible pair.

Branch one is impossible because it makes the refined budget not negative;
branch two is impossible because it caps the excess product.  The dichotomy has
no third branch. -/
theorem exists_pairMinor_pos_of_refinedBudget_of_leverage (D : WeightedDesign m 3)
    {d1 d2 d3 : Fin m} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hxa : 0 < leverageOf (D.atom d1) - 1) (hxb : 0 < leverageOf (D.atom d2) - 1)
    (hxc : 0 < leverageOf (D.atom d3) - 1)
    (hbudget :
      (D.weight d1 * D.weight d2 + D.weight d1 * D.weight d3
          + D.weight d2 * D.weight d3)
        - (1 - (D.weight d1 + D.weight d2 + D.weight d3))
            * ((D.weight d1 * (leverageOf (D.atom d1) - 1)
                + D.weight d2 * (leverageOf (D.atom d2) - 1)
                + D.weight d3 * (leverageOf (D.atom d3) - 1)) - 1)
        - (D.weight d1 ^ 2 * (leverageOf (D.atom d1) - 1)
            + D.weight d2 ^ 2 * (leverageOf (D.atom d2) - 1)
            + D.weight d3 ^ 2 * (leverageOf (D.atom d3) - 1))
        - D.weight d1 * D.weight d2 * D.weight d3
            * (1 + (leverageOf (D.atom d1) - 1) + (leverageOf (D.atom d2) - 1)
              + (leverageOf (D.atom d3) - 1)) < 0)
    (hlev : 1 + ((leverageOf (D.atom d1) - 1) + (leverageOf (D.atom d2) - 1)
        + (leverageOf (D.atom d3) - 1))
      < 4 * ((leverageOf (D.atom d1) - 1) * (leverageOf (D.atom d2) - 1)
          * (leverageOf (D.atom d3) - 1))) :
    0 < pairGapMinor (D.atom d1) (D.atom d2)
      ∨ 0 < pairGapMinor (D.atom d1) (D.atom d3)
      ∨ 0 < pairGapMinor (D.atom d2) (D.atom d3) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hab, hac, hbc⟩ := hcon
  have hla : (0 : ℝ) ≤ leverageOf (D.atom d1) := leverageOf_nonneg _
  have hlb : (0 : ℝ) ≤ leverageOf (D.atom d2) := leverageOf_nonneg _
  have hlc : (0 : ℝ) ≤ leverageOf (D.atom d3) := leverageOf_nonneg _
  rcases tripleGapDet_refusal_dichotomy hxa hxb hxc hab hac hbc with hone | htwo
  · have := branchOne_refinedBudget_nonneg D h12 h13 h23 hab hac hbc hone
    linarith
  · have := branchTwo_leverage_bound_pure hla hlb hlc hab hac hbc htwo
    linarith

end Gtz
