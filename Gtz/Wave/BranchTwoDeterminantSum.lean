/-
# The two determinant conditions of `E1`, added

`Gtz.BranchTwoReduction` reduced `E1` to a statement about one symmetric matrix.
Writing `M` for the weighted outside Gram, `t_i` for the weights, `A_i = 1 - t_i`
for the weight slacks and `a_i = M_ii - t_i` for the weighted leverage excesses,
the two halves of the refusal dichotomy are the two determinant conditions

  `0 <= det (1 - M)`   and   `0 <= det M` ,

and the target is `a_1 + a_2 + a_3 <= 1`.  Each condition is a cubic in the
excesses, and the cubic term is the same in both up to sign.

## The sum is linear

Adding them cancels the cubic exactly (`Gtz.branchTwo_determinant_sum`):

  **`det (1 - M) + det M
      = (A_1 A_2 A_3 + t_1 t_2 t_3) - Σ_i a_i * (1 - t_j - t_k)`**

with `{i,j,k} = {1,2,3}`.  The coefficient of `a_i` is `A_j A_k - t_j t_k`, which
collapses to `1 - t_j - t_k`; the constant is the two extreme products.  So the
two determinant conditions together give one LINEAR inequality in the excesses
(`Gtz.branchTwo_excess_linear_bound`):

  **`Σ_i a_i * (1 - t_j - t_k) <= A_1 A_2 A_3 + t_1 t_2 t_3`** .

That is the whole content the pair of determinants shares, in one line and with
no case on the Bargmann sign.

## What the linear bound does not do

It does not close `E1`, and the reason is recorded here so that no successor
spends a round on it.  The coefficient `1 - t_j - t_k` is not bounded below by
the constant, and it can be negative; maximising `Σ a_i` against the linear
bound and the pair constraints alone reaches `1.0671` (an explicit linear
program, `scratchpad/f58/lin.py`).  **Dropping the cubic loses exactly the part
that makes the bound tight**, so the two determinant conditions must be used
SEPARATELY, and any relaxation that adds them is provably too weak.

## The centre is where the cubic bites

At the symmetric point `b_i = a_i / A_i = 1/2` — the only point where all three
pair constraints are tight (`Gtz.pairTight_forces_center`) — the first
determinant condition holds with equality while

  `Σ_i a_i = (3 - t_1 - t_2 - t_3) / 2 > 1` ,

so the target FAILS there on the pair constraints and the first determinant
alone.  What rules the point out is the second determinant, whose numerator over
the positive `2 t_1 t_2 t_3` is exactly `t_1 + t_2 + t_3 - 1`
(`Gtz.centerPoint_detM_numerator`) — negative on the domain.  So the second
condition is not decoration: it is the only thing standing at the centre, and it
is what an earlier round's `b = (1/2,1/2,1/2)` double root was detecting.

[MEASURED, and it CORRECTS the recorded reading that the maximiser has all three
pair constraints tight: it does not.  All three tight forces the centre, where
the second determinant fails.  A direct search over the exact system in the
`(a,t)` variables reaches `Σ a = 0.99714` at `b = (0.362, 0.172, 0.619)`, with
no pair constraint tight — `scratchpad/f58/at.py`.  The supremum is still `1`
and was never exceeded.]
-/
import Gtz.Wave.BranchTwoReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

/-! ## 1. The two determinant conditions -/

/-- The first determinant of the reduction, `det (1 - M)`, in the excesses and
the weight slacks: the product of the slacks, less each excess against the other
two slacks, plus four times the excess product. -/
noncomputable def branchDetComplement (a1 a2 a3 t1 t2 t3 : ℝ) : ℝ :=
  (1 - t1) * (1 - t2) * (1 - t3)
    - (a1 * ((1 - t2) * (1 - t3)) + a2 * ((1 - t1) * (1 - t3))
      + a3 * ((1 - t1) * (1 - t2)))
    + 4 * (a1 * a2 * a3)

/-- The second determinant of the reduction, `det M`, in the same variables: the
weight product, plus each excess against the other two weights, less four times
the excess product. -/
noncomputable def branchDetOutside (a1 a2 a3 t1 t2 t3 : ℝ) : ℝ :=
  t1 * t2 * t3 + (a1 * (t2 * t3) + a2 * (t1 * t3) + a3 * (t1 * t2))
    - 4 * (a1 * a2 * a3)

/-! ## 2. The sum is linear -/

/-- **THE TWO DETERMINANTS ADD TO A LINEAR FORM.**  The excess product cancels,
the coefficient of each excess collapses to one less the other two weights, and
the constant is the slack product plus the weight product. -/
theorem branchTwo_determinant_sum (a1 a2 a3 t1 t2 t3 : ℝ) :
    branchDetComplement a1 a2 a3 t1 t2 t3 + branchDetOutside a1 a2 a3 t1 t2 t3
      = ((1 - t1) * (1 - t2) * (1 - t3) + t1 * t2 * t3)
        - (a1 * (1 - t2 - t3) + a2 * (1 - t1 - t3) + a3 * (1 - t1 - t2)) := by
  unfold branchDetComplement branchDetOutside
  ring

/-- **THE LINEAR BOUND.**  Both determinant conditions together cap the excesses
against the two extreme products, with no case on the Bargmann sign. -/
theorem branchTwo_excess_linear_bound {a1 a2 a3 t1 t2 t3 : ℝ}
    (hcomp : 0 ≤ branchDetComplement a1 a2 a3 t1 t2 t3)
    (hout : 0 ≤ branchDetOutside a1 a2 a3 t1 t2 t3) :
    a1 * (1 - t2 - t3) + a2 * (1 - t1 - t3) + a3 * (1 - t1 - t2)
      ≤ (1 - t1) * (1 - t2) * (1 - t3) + t1 * t2 * t3 := by
  have hsum := branchTwo_determinant_sum a1 a2 a3 t1 t2 t3
  linarith

/-- The coefficient of each excess in the linear bound is the difference of the
two products it does not carry. -/
theorem branchTwo_coefficient_eq (t2 t3 : ℝ) :
    (1 - t2) * (1 - t3) - t2 * t3 = 1 - t2 - t3 := by ring

/-! ## 3. The centre, and why the second determinant is load bearing -/

/-- **ALL THREE PAIR CONSTRAINTS TIGHT FORCES THE CENTRE.**  The pair constraint
of a pair is tightness of `b_i + b_j = 1` in the normalized excesses, so all
three together pin every normalized excess to one half. -/
theorem pairTight_forces_center {b1 b2 b3 : ℝ}
    (h12 : b1 + b2 = 1) (h13 : b1 + b3 = 1) (h23 : b2 + b3 = 1) :
    b1 = 1 / 2 ∧ b2 = 1 / 2 ∧ b3 = 1 / 2 :=
  ⟨by linarith, by linarith, by linarith⟩

/-- **THE FIRST DETERMINANT VANISHES AT THE CENTRE.**  With every excess at half
its slack, the complement determinant is exactly zero. -/
theorem centerPoint_detComplement_zero (t1 t2 t3 : ℝ) :
    branchDetComplement ((1 - t1) / 2) ((1 - t2) / 2) ((1 - t3) / 2) t1 t2 t3
      = 0 := by
  unfold branchDetComplement
  ring

/-- **THE CENTRE BREAKS THE TARGET.**  Its excesses total more than one whenever
the weights do not, which is the standing hypothesis of the stratum. -/
theorem centerPoint_excess_sum (t1 t2 t3 : ℝ) :
    (1 - t1) / 2 + (1 - t2) / 2 + (1 - t3) / 2
      = (3 - (t1 + t2 + t3)) / 2 := by ring

/-- The centre's excess total passes one exactly when the weights fall short of
one — so on the stratum the target fails at the centre. -/
theorem centerPoint_excess_gt_one {t1 t2 t3 : ℝ} (hsum : t1 + t2 + t3 < 1) :
    1 < (1 - t1) / 2 + (1 - t2) / 2 + (1 - t3) / 2 := by
  rw [centerPoint_excess_sum]
  linarith

/-- **THE SECOND DETERMINANT AT THE CENTRE IS THE WEIGHT SHORTFALL, HALVED.**
Every weight product cancels: the value is exactly one half of the amount by
which the three weights fall short of one. -/
theorem centerPoint_detOutside_eq (t1 t2 t3 : ℝ) :
    branchDetOutside ((1 - t1) / 2) ((1 - t2) / 2) ((1 - t3) / 2) t1 t2 t3
      = (t1 + t2 + t3 - 1) / 2 := by
  unfold branchDetOutside
  ring

/-- **THE CENTRE FAILS THE SECOND DETERMINANT.**  On the stratum the second
determinant is strictly negative at the centre, so the centre is not a point of
the system at all — the excess total there is irrelevant. -/
theorem centerPoint_detOutside_neg {t1 t2 t3 : ℝ} (hsum : t1 + t2 + t3 < 1) :
    branchDetOutside ((1 - t1) / 2) ((1 - t2) / 2) ((1 - t3) / 2) t1 t2 t3 < 0 := by
  rw [centerPoint_detOutside_eq]
  linarith

end Gtz
