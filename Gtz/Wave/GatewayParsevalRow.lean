/-
# Condition (A) of the rank-one case, unconditionally

`Gtz.exists_pairMinor_pos_of_excess` closes the gateway from TWO hypotheses: the
outside triple carries weighted excess past one, and its excess product passes
its excess total.  The second hypothesis was the whole residual — the lane's
five rounds of linear programming, and
`Gtz.gateway_no_handelman_certificate`, were spent on it.

**This module removes it.**  A weighted design of rank three whose three atoms
have every pair minor nonpositive and weighted excess total past one does not
exist, so such a triple always carries an admissible pair
(`Gtz.exists_pairMinor_pos_of_excess_gt_one`).  At a corner the outside triple
carries exactly `2 - s` with `s < 1`, so condition (A) holds there with nothing
assumed.

## Parseval, read at one atom of the triple

The whole new ingredient is one line.  Read Parseval at the probe `g_k` and keep
only the three terms of the triple:

  `sum_{i in T} t_i <g_i, g_k>^2  <=  l_k` .

Multiply by `t_k`.  The diagonal term is `(t_k l_k)^2 = x_k^2`, and each
off-diagonal term is bounded below by the pair minor being nonpositive,
`t_i t_k <g_i,g_k>^2 >= a_i a_k`.  So with `E` the weighted excess total,

  **`x_k^2 + a_k (E - a_k) <= x_k`** ,   that is
  **`a_k (E - 1) <= t_k (c_k - a_k)`**   (`Gtz.inadmissible_row_excess_bound`),

writing `a_k = t_k(l_k - 1)`, `x_k = t_k l_k = a_k + t_k` and `c_k = 1 - x_k`.
The second form is the useful one and the two are one `ring` apart.

## Why that finishes

Suppose `E > 1`.  The left side is then strictly positive at every atom of the
triple, so `c_k > a_k` at EVERY atom: no atom carries more excess than cap
slack.  That is exactly the LIGHT case of `Gtz.gateway_excess_le_one_of_light`,
whose only other input is `0 <= branchDetOutside` — and the landed
`Gtz.outsideTriple_leverage_bound_of_excess` supplies that unconditionally from
the same hypotheses, since `branchDetOutside` is `t_1t_2t_3` times
`1 + sum x - 4 prod x` (`Gtz.branchDetOutside_eq_leverageForm`).  So `E <= 1`,
contradicting `E > 1`.

The heavy case of `Gtz.gateway_excess_le_one` is therefore never reached at a
design, and with it the first determinant `branchDetComplement`, which is a
generator of the box but NOT a consequence of Parseval.  The box was carrying a
hypothesis the design never had to supply, and the row bound replaces it.

[MEASURED before proving: over 152,383 triples with every pair minor
nonpositive, drawn from designs of sizes four to eight, the row bound never
failed.  Calibrated on the `(5,3)` diamond, whose leverages come back
`(2, 13/4, 13/4, 13/4, 13/4)` and whose ten pair minors come back
`0.75` four times, `2` twice and `4.5` four times — every one positive, so the
diamond carries no inadmissible pair at all.]
-/
import Gtz.Wave.GatewayExcessBound
import Gtz.Wave.PairMinorBudget
import Gtz.Wave.KOneAnchor

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace Gtz

variable {m : ℕ}

/-! ## 1. Parseval, restricted to three atoms -/

/-! ## 2. The row bound of an inadmissible triple -/

/-- **THE ROW BOUND.**  At an atom whose two pair minors inside the triple are
nonpositive, the weighted excess total is capped by that atom's own weight and
cap slack.  Parseval at the atom, and nothing else.

Only the two pair minors AT the atom are used, so the third pair is free. -/
theorem inadmissible_row_excess_bound (D : WeightedDesign m 3) {d1 d2 d3 : Fin m}
    (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hq12 : pairGapMinor (D.atom d1) (D.atom d2) ≤ 0)
    (hq13 : pairGapMinor (D.atom d1) (D.atom d3) ≤ 0) :
    D.weight d1 * (leverageOf (D.atom d1) - 1)
        * (D.weight d1 * (leverageOf (D.atom d1) - 1)
            + D.weight d2 * (leverageOf (D.atom d2) - 1)
            + D.weight d3 * (leverageOf (D.atom d3) - 1) - 1)
      ≤ D.weight d1
          * (1 - D.weight d1 * leverageOf (D.atom d1)
              - D.weight d1 * (leverageOf (D.atom d1) - 1)) := by
  have hw1 := D.weight_pos d1
  have hw2 := D.weight_pos d2
  have hw3 := D.weight_pos d3
  have hpar := parseval_triple_reading_le D (D.atom d1) h12 h13 h23
  rw [dotProduct_self_eq_leverage] at hpar
  have hp12 : D.weight d1 * (leverageOf (D.atom d1) - 1)
        * (D.weight d2 * (leverageOf (D.atom d2) - 1))
      ≤ D.weight d1 * (D.weight d2 * (D.atom d2 ⬝ᵥ D.atom d1) ^ 2) := by
    rw [pairGapMinor, dotProduct_comm (D.atom d1) (D.atom d2)] at hq12
    nlinarith [mul_pos hw1 hw2, hq12]
  have hp13 : D.weight d1 * (leverageOf (D.atom d1) - 1)
        * (D.weight d3 * (leverageOf (D.atom d3) - 1))
      ≤ D.weight d1 * (D.weight d3 * (D.atom d3 ⬝ᵥ D.atom d1) ^ 2) := by
    rw [pairGapMinor, dotProduct_comm (D.atom d1) (D.atom d3)] at hq13
    nlinarith [mul_pos hw1 hw3, hq13]
  have hscale := mul_le_mul_of_nonneg_left hpar hw1.le
  nlinarith [hscale, hp12, hp13]

/-- **AN EXCESS PAST ONE MAKES EVERY ATOM LIGHT.**  With the total past one the
row bound has a strictly positive left side, so the cap slack beats the excess
at that atom. -/
theorem excess_gt_one_cap_slack (D : WeightedDesign m 3) {d1 d2 d3 : Fin m}
    (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hx1 : 1 < leverageOf (D.atom d1))
    (hq12 : pairGapMinor (D.atom d1) (D.atom d2) ≤ 0)
    (hq13 : pairGapMinor (D.atom d1) (D.atom d3) ≤ 0)
    (hexc : 1 < D.weight d1 * (leverageOf (D.atom d1) - 1)
        + D.weight d2 * (leverageOf (D.atom d2) - 1)
        + D.weight d3 * (leverageOf (D.atom d3) - 1)) :
    2 * (D.weight d1 * (leverageOf (D.atom d1) - 1)) + D.weight d1 < 1 := by
  have hw1 := D.weight_pos d1
  have hrow := inadmissible_row_excess_bound D h12 h13 h23 hq12 hq13
  have hpos : 0 < D.weight d1 * (leverageOf (D.atom d1) - 1) :=
    mul_pos hw1 (by linarith)
  nlinarith [hrow, hpos, hw1, mul_pos hw1 hw1]

/-! ## 3. The landed excess bound, scaled to the box -/

/-- The second determinant of the box is the weight product against the landed
unweighted excess bound. -/
theorem branchDetOutside_eq_leverageForm (t1 t2 t3 x1 x2 x3 : ℝ) :
    branchDetOutside (t1 * x1) (t2 * x2) (t3 * x3) t1 t2 t3
      = t1 * t2 * t3 * (1 + (x1 + x2 + x3) - 4 * (x1 * x2 * x3)) := by
  unfold branchDetOutside; ring

/-- **THE SECOND DETERMINANT, AT A DESIGN.**  The landed
`Gtz.outsideTriple_leverage_bound_of_excess` is exactly the box's second
determinant condition, once scaled by the three weights. -/
theorem branchDetOutside_nonneg_of_excess (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {d1 d2 d3 : Fin m} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hx1 : 1 < leverageOf (D.atom d1)) (hx2 : 1 < leverageOf (D.atom d2))
    (hx3 : 1 < leverageOf (D.atom d3))
    (hq12 : pairGapMinor (D.atom d1) (D.atom d2) ≤ 0)
    (hq13 : pairGapMinor (D.atom d1) (D.atom d3) ≤ 0)
    (hq23 : pairGapMinor (D.atom d2) (D.atom d3) ≤ 0)
    (hexc : 1 < D.weight d1 * (leverageOf (D.atom d1) - 1)
        + D.weight d2 * (leverageOf (D.atom d2) - 1)
        + D.weight d3 * (leverageOf (D.atom d3) - 1)) :
    0 ≤ branchDetOutside
          (D.weight d1 * (leverageOf (D.atom d1) - 1))
          (D.weight d2 * (leverageOf (D.atom d2) - 1))
          (D.weight d3 * (leverageOf (D.atom d3) - 1))
          (D.weight d1) (D.weight d2) (D.weight d3) := by
  have hbound := outsideTriple_leverage_bound_of_excess D hm h12 h13 h23
    (by linarith) (by linarith) (by linarith) hq12 hq13 hq23 hexc
  have hwprod : 0 < D.weight d1 * D.weight d2 * D.weight d3 :=
    mul_pos (mul_pos (D.weight_pos d1) (D.weight_pos d2)) (D.weight_pos d3)
  rw [branchDetOutside_eq_leverageForm (D.weight d1) (D.weight d2) (D.weight d3)
    (leverageOf (D.atom d1) - 1) (leverageOf (D.atom d2) - 1)
    (leverageOf (D.atom d3) - 1)]
  exact mul_nonneg hwprod.le (by linarith)

/-! ## 4. Condition (A), with nothing assumed -/

/-- **CONDITION (A).**  Three atoms of a design of rank three whose weighted
leverage excesses total more than one carry an admissible pair.

This is `Gtz.exists_pairMinor_pos_of_excess` with its second hypothesis
discharged.  At a corner the inside share is strictly less than one and the
total excess is two, so the outside triple always meets the hypothesis. -/
theorem exists_pairMinor_pos_of_excess_gt_one (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {d1 d2 d3 : Fin m} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hx1 : 1 < leverageOf (D.atom d1)) (hx2 : 1 < leverageOf (D.atom d2))
    (hx3 : 1 < leverageOf (D.atom d3))
    (hexc : 1 < D.weight d1 * (leverageOf (D.atom d1) - 1)
        + D.weight d2 * (leverageOf (D.atom d2) - 1)
        + D.weight d3 * (leverageOf (D.atom d3) - 1)) :
    0 < pairGapMinor (D.atom d1) (D.atom d2)
      ∨ 0 < pairGapMinor (D.atom d1) (D.atom d3)
      ∨ 0 < pairGapMinor (D.atom d2) (D.atom d3) := by
  by_contra hcon
  push_neg at hcon
  obtain ⟨hq12, hq13, hq23⟩ := hcon
  have hw1 := D.weight_pos d1
  have hw2 := D.weight_pos d2
  have hw3 := D.weight_pos d3
  have hcap1 := excess_gt_one_cap_slack D h12 h13 h23 hx1 hq12 hq13 hexc
  have hcap2 := excess_gt_one_cap_slack D (Ne.symm h12) h23 h13 hx2
    (by rw [pairGapMinor_comm]; exact hq12) hq23 (by linarith)
  have hcap3 := excess_gt_one_cap_slack D (Ne.symm h13) (Ne.symm h23) h12 hx3
    (by rw [pairGapMinor_comm]; exact hq13) (by rw [pairGapMinor_comm]; exact hq23)
    (by linarith)
  have hM := branchDetOutside_nonneg_of_excess D hm h12 h13 h23 hx1 hx2 hx3
    hq12 hq13 hq23 hexc
  have hlight := gateway_excess_le_one_of_light
    (a1 := D.weight d1 * (leverageOf (D.atom d1) - 1))
    (a2 := D.weight d2 * (leverageOf (D.atom d2) - 1))
    (a3 := D.weight d3 * (leverageOf (D.atom d3) - 1))
    (t1 := D.weight d1) (t2 := D.weight d2) (t3 := D.weight d3)
    (mul_pos hw1 (by linarith)).le (mul_pos hw2 (by linarith)).le
    (mul_pos hw3 (by linarith)).le
    (by nlinarith [mul_pos hw1 (by linarith : (0:ℝ) < leverageOf (D.atom d1) - 1)])
    (by nlinarith [mul_pos hw2 (by linarith : (0:ℝ) < leverageOf (D.atom d2) - 1)])
    (by nlinarith [mul_pos hw3 (by linarith : (0:ℝ) < leverageOf (D.atom d3) - 1)])
    (by linarith) (by linarith) (by linarith) hM
  linarith

/-- **THE GATEWAY AT A CORNER.**  Written against the inside share: a corner
gives its outside triple the total excess less that share, and the share is
below one, so the outside triple carries an admissible pair. -/
theorem exists_pairMinor_pos_of_insideShare (D : WeightedDesign m 3) (hm : 2 ≤ m)
    {d1 d2 d3 : Fin m} (h12 : d1 ≠ d2) (h13 : d1 ≠ d3) (h23 : d2 ≠ d3)
    (hx1 : 1 < leverageOf (D.atom d1)) (hx2 : 1 < leverageOf (D.atom d2))
    (hx3 : 1 < leverageOf (D.atom d3)) (insideShare : ℝ)
    (hshare : insideShare < 1)
    (houtside : D.weight d1 * (leverageOf (D.atom d1) - 1)
        + D.weight d2 * (leverageOf (D.atom d2) - 1)
        + D.weight d3 * (leverageOf (D.atom d3) - 1) = 2 - insideShare) :
    0 < pairGapMinor (D.atom d1) (D.atom d2)
      ∨ 0 < pairGapMinor (D.atom d1) (D.atom d3)
      ∨ 0 < pairGapMinor (D.atom d2) (D.atom d3) :=
  exists_pairMinor_pos_of_excess_gt_one D hm h12 h13 h23 hx1 hx2 hx3 (by linarith)

end Gtz
