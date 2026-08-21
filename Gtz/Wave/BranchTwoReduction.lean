/-
# The refined budget is a product, and branch one is universally impossible

`Gtz.branchOne_refinedBudget_nonneg` says a refusing heavy triple in branch one
carries a refined budget that is not negative.  That budget looked opaque: four
groups of terms in six scalars, with no evident sign.  It is not opaque.  It
factors completely.

## The factorization

Write `A_i = 1 - t_i` for the weight slack of an atom and `a_i = t_i * x_i` for
its weighted leverage excess.  Then (`Gtz.refinedBudget_factor`, one `ring`)

  **`F = A_1 A_2 A_3 - a_1 A_2 A_3 - a_2 A_1 A_3 - a_3 A_1 A_2`** ,

that is, dividing by the positive product of the three slacks,

  `F / (A_1 A_2 A_3) = 1 - b_1 - b_2 - b_3`   with   `b_i = a_i / A_i` .

**The refined budget is the product of the three weight slacks with one less the
total normalized excess.**  Every earlier estimate of it was an estimate of a
product, which is why none of them were sharp.

## Branch one dies on one line

The normalized excess `b_i` is larger than the plain excess `a_i`, because the
slack `A_i` is less than one.  So whenever the three atoms carry a total
weighted excess past one — which is exactly what a corner gives its outside
triple, since the design's total excess is two and the corner's inside share is
less than one — the normalized total also passes one, and `F` is strictly
negative (`Gtz.refinedBudget_neg_of_excess`).

Branch one forces `F` to be not negative, so **branch one is impossible at every
such triple** (`Gtz.outsideTriple_not_branchOne`).  The dichotomy has no third
branch, so the triple is in branch two, and branch two caps the excess product
(`Gtz.outsideTriple_leverage_bound_of_excess`):

  **`4 x_1 x_2 x_3 <= 1 + x_1 + x_2 + x_3`** .

That is the whole of `E1` except one region, and it is now unconditional.

[The supremum of `F` on the domain is `0`, approached as the normalized total
falls to one — NOT the sampled `-0.00118587` recorded in an earlier round, which
was only the closest an adversarial scan came to a boundary it cannot reach.
The factorization makes the true supremum visible without any search.]
-/
import Gtz.Wave.CornerRefusalDichotomy

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

variable {m : ℕ}

/-! ## 1. The factorization -/

/-- **THE REFINED BUDGET IS A PRODUCT.**  The four groups of the budget collapse
to the product of the three weight slacks less the three weighted excesses, each
against the slacks of the other two.  Hypothesis-free. -/
theorem refinedBudget_factor (t1 t2 t3 x1 x2 x3 : ℝ) :
    (t1 * t2 + t1 * t3 + t2 * t3)
        - (1 - (t1 + t2 + t3)) * ((t1 * x1 + t2 * x2 + t3 * x3) - 1)
        - (t1 ^ 2 * x1 + t2 ^ 2 * x2 + t3 ^ 2 * x3)
        - t1 * t2 * t3 * (1 + x1 + x2 + x3)
      = (1 - t1) * ((1 - t2) * (1 - t3))
        - t1 * x1 * ((1 - t2) * (1 - t3))
        - t2 * x2 * ((1 - t1) * (1 - t3))
        - t3 * x3 * ((1 - t1) * (1 - t2)) := by
  ring

/-! ## 2. Branch one dies on the excess -/

/-- **THE BUDGET IS NEGATIVE WHENEVER THE WEIGHTED EXCESS PASSES ONE.**  Each
slack is at most one, so the product of two slacks is at least the product of
all three.  The excess total then carries the whole product past itself. -/
theorem refinedBudget_neg_of_excess {t1 t2 t3 x1 x2 x3 : ℝ}
    (ht1 : 0 < t1) (ht2 : 0 < t2) (ht3 : 0 < t3)
    (hu1 : t1 < 1) (hu2 : t2 < 1) (hu3 : t3 < 1)
    (hx1 : 0 < x1) (hx2 : 0 < x2) (hx3 : 0 < x3)
    (hexc : 1 < t1 * x1 + t2 * x2 + t3 * x3) :
    (t1 * t2 + t1 * t3 + t2 * t3)
        - (1 - (t1 + t2 + t3)) * ((t1 * x1 + t2 * x2 + t3 * x3) - 1)
        - (t1 ^ 2 * x1 + t2 ^ 2 * x2 + t3 ^ 2 * x3)
        - t1 * t2 * t3 * (1 + x1 + x2 + x3) < 0 := by
  have hA1 : 0 < 1 - t1 := by linarith
  have hA2 : 0 < 1 - t2 := by linarith
  have hA3 : 0 < 1 - t3 := by linarith
  have ha1 : 0 < t1 * x1 := mul_pos ht1 hx1
  have ha2 : 0 < t2 * x2 := mul_pos ht2 hx2
  have ha3 : 0 < t3 * x3 := mul_pos ht3 hx3
  have hprod : 0 < (1 - t1) * ((1 - t2) * (1 - t3)) :=
    mul_pos hA1 (mul_pos hA2 hA3)
  -- each pair of slacks dominates the triple product
  have g1 : (1 - t1) * ((1 - t2) * (1 - t3)) ≤ (1 - t2) * (1 - t3) := by
    nlinarith [mul_pos hA2 hA3]
  have g2 : (1 - t1) * ((1 - t2) * (1 - t3)) ≤ (1 - t1) * (1 - t3) := by
    nlinarith [mul_pos hA1 hA3]
  have g3 : (1 - t1) * ((1 - t2) * (1 - t3)) ≤ (1 - t1) * (1 - t2) := by
    nlinarith [mul_pos hA1 hA2]
  -- so the three excess terms total past the product
  have s1 : t1 * x1 * ((1 - t1) * ((1 - t2) * (1 - t3)))
      ≤ t1 * x1 * ((1 - t2) * (1 - t3)) := by
    exact mul_le_mul_of_nonneg_left g1 ha1.le
  have s2 : t2 * x2 * ((1 - t1) * ((1 - t2) * (1 - t3)))
      ≤ t2 * x2 * ((1 - t1) * (1 - t3)) := by
    exact mul_le_mul_of_nonneg_left g2 ha2.le
  have s3 : t3 * x3 * ((1 - t1) * ((1 - t2) * (1 - t3)))
      ≤ t3 * x3 * ((1 - t1) * (1 - t2)) := by
    exact mul_le_mul_of_nonneg_left g3 ha3.le
  have hbig : (1 - t1) * ((1 - t2) * (1 - t3))
      < t1 * x1 * ((1 - t2) * (1 - t3))
        + t2 * x2 * ((1 - t1) * (1 - t3))
        + t3 * x3 * ((1 - t1) * (1 - t2)) := by
    nlinarith [s1, s2, s3, hprod, hexc]
  rw [refinedBudget_factor]
  linarith

/-! ## 3. The corner consequence -/

/-- **A REFUSING HEAVY TRIPLE OF LARGE EXCESS IS NEVER IN BRANCH ONE.**  Branch
one forces the refined budget to be not negative, and the excess forces it to be
negative. -/
theorem outsideTriple_not_branchOne (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {d1 d2 d3 : Fin m} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hx1 : 0 < leverageOf (D.atom d1) - 1)
    (hx2 : 0 < leverageOf (D.atom d2) - 1)
    (hx3 : 0 < leverageOf (D.atom d3) - 1)
    (hab : pairGapMinor (D.atom d1) (D.atom d2) ≤ 0)
    (hac : pairGapMinor (D.atom d1) (D.atom d3) ≤ 0)
    (hbc : pairGapMinor (D.atom d2) (D.atom d3) ≤ 0)
    (hexc : 1 < D.weight d1 * (leverageOf (D.atom d1) - 1)
        + D.weight d2 * (leverageOf (D.atom d2) - 1)
        + D.weight d3 * (leverageOf (D.atom d3) - 1)) :
    ¬ ((leverageOf (D.atom d1) - 1) * pairGapMinor (D.atom d2) (D.atom d3)
        + (leverageOf (D.atom d2) - 1) * pairGapMinor (D.atom d1) (D.atom d3)
        + (leverageOf (D.atom d3) - 1) * pairGapMinor (D.atom d1) (D.atom d2)
      ≤ tripleGapDet (D.atom d1) (D.atom d2) (D.atom d3)) := by
  intro hbranch
  have hnn := branchOne_refinedBudget_nonneg D h12 h13 h23 hab hac hbc hbranch
  have hneg := refinedBudget_neg_of_excess (D.weight_pos d1) (D.weight_pos d2)
    (D.weight_pos d3) (weight_lt_one D hm d1) (weight_lt_one D hm d2)
    (weight_lt_one D hm d3) hx1 hx2 hx3 hexc
  linarith

/-- **THE EXCESS FORCES THE LEVERAGE CAP.**  With branch one impossible the
dichotomy leaves branch two, which caps the product of the three excesses by
their total.  No corner equation and no realness — only Parseval, the member
weight cap and the excess. -/
theorem outsideTriple_leverage_bound_of_excess (D : WeightedDesign m 3)
    (hm : 2 ≤ m) {d1 d2 d3 : Fin m} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3)
    (h23 : d2 ≠ d3)
    (hx1 : 0 < leverageOf (D.atom d1) - 1)
    (hx2 : 0 < leverageOf (D.atom d2) - 1)
    (hx3 : 0 < leverageOf (D.atom d3) - 1)
    (hab : pairGapMinor (D.atom d1) (D.atom d2) ≤ 0)
    (hac : pairGapMinor (D.atom d1) (D.atom d3) ≤ 0)
    (hbc : pairGapMinor (D.atom d2) (D.atom d3) ≤ 0)
    (hexc : 1 < D.weight d1 * (leverageOf (D.atom d1) - 1)
        + D.weight d2 * (leverageOf (D.atom d2) - 1)
        + D.weight d3 * (leverageOf (D.atom d3) - 1)) :
    4 * ((leverageOf (D.atom d1) - 1) * (leverageOf (D.atom d2) - 1)
        * (leverageOf (D.atom d3) - 1))
      ≤ 1 + ((leverageOf (D.atom d1) - 1) + (leverageOf (D.atom d2) - 1)
        + (leverageOf (D.atom d3) - 1)) := by
  rcases tripleGapDet_refusal_dichotomy hx1 hx2 hx3 hab hac hbc with h | h
  · exact absurd h (outsideTriple_not_branchOne D hm h12 h13 h23 hx1 hx2 hx3
      hab hac hbc hexc)
  · exact branchTwo_leverage_bound_pure (leverageOf_nonneg _) (leverageOf_nonneg _)
      (leverageOf_nonneg _) hab hac hbc h

/-- **THE PRODUCER, FREED OF ITS LEVERAGE HYPOTHESIS.**  The landed producer
asked for both a negative refined budget and an excess product past the total.
The excess supplies the first outright, so a heavy triple whose excess product
passes its total carries an admissible pair. -/
theorem exists_pairMinor_pos_of_excess (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {d1 d2 d3 : Fin m} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hx1 : 0 < leverageOf (D.atom d1) - 1)
    (hx2 : 0 < leverageOf (D.atom d2) - 1)
    (hx3 : 0 < leverageOf (D.atom d3) - 1)
    (hexc : 1 < D.weight d1 * (leverageOf (D.atom d1) - 1)
        + D.weight d2 * (leverageOf (D.atom d2) - 1)
        + D.weight d3 * (leverageOf (D.atom d3) - 1))
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
  have := outsideTriple_leverage_bound_of_excess D hm h12 h13 h23 hx1 hx2 hx3
    hab hac hbc hexc
  linarith

end Gtz
