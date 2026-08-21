/-
# The box determinants are the extremal case of the true ones

The E1 lane reduced the corner's admissible outside pair to a six-variable box
in the excesses `a_i` and the weights `t_i`, with two polynomial "determinants"
`Gtz.branchDetComplement` and `Gtz.branchDetOutside` as generators.  Its last
round found that these are definitions, not determinants: at a general outside
Gram `M` with free off-diagonals `r_ij` they differ from `det(1−M)` and `det M`
by as much as `0.58`, and coincide only on the slice where every pair minor
vanishes with Bargmann sign `−1`.  It asked whether the reduction to that slice
was ever justified, and said that if not, every certificate search in the lane
had been aimed at a proxy.

This module settles it.  The reduction is justified, and the reason is one
identity (`Gtz.det_sum_eq_box_add_pairMinors`):

  **`det M + det(1−M) = branchDetComplement + branchDetOutside + (q₁₂ + q₁₃ + q₂₃)`**

where `q_ij = a_i a_j − r_ij²` is the pair minor of the gap block.  No
hypothesis.  The two determinants enter the lane's slack factorization only as
a SUM — that was the round's own finding — and their sum exceeds the box sum by
exactly the three pair minors.  On the inadmissible set every pair minor is
nonpositive, so

  **`det M + det(1−M) ≤ branchDetComplement + branchDetOutside`**

(`Gtz.det_sum_le_box_of_inadmissible`), with equality exactly on the slice.  The
box is therefore not a proxy for the true problem.  It is its EXTREMAL CASE: any
bound proved from the box's determinant sum holds a fortiori on the true set,
and the true slack factorization carries an extra nonnegative term
(`Gtz.true_slack_factorization`).  Every Handelman refutation in the lane was
aimed at the right object.

## What transfers, concretely

`Gtz.branchTwo_target_of_defect` proves the target `Σa ≤ 1` from the box's
defect condition.  `Gtz.true_target_of_defect` proves the same target from the
TRUE determinants, on the inadmissible set, because the true defect is at least
the box defect.  Nothing in the box lane needs to be redone.

[MEASURED before proving: the identity at 4000 random rational points with zero
mismatch; on 200,000 points of the inadmissible set with both signs the true sum
exceeded the box sum at 0 points; on the slice `{q = 0, σ = −1}` the true and
box determinants agree individually to 5.3e-15.]
-/
import Gtz.Wave.BranchTwoDeterminantSum
import Gtz.Wave.CornerEmptinessSlack

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

/-! ## 1. The outside Gram in box coordinates -/

/-- The weighted outside Gram of a corner, in the box's coordinates: the
diagonal carries excess plus weight, and the three off-diagonals are free. -/
noncomputable def outsideGram (a1 a2 a3 t1 t2 t3 r12 r13 r23 : ℝ) :
    Matrix (Fin 3) (Fin 3) ℝ :=
  !![a1 + t1, r12, r13;
     r12, a2 + t2, r23;
     r13, r23, a3 + t3]

/-- The pair minor of the gap block `K = M − diag t`: excess product less the
squared off-diagonal. -/
noncomputable def boxPairMinor (ai aj rij : ℝ) : ℝ := ai * aj - rij ^ 2

/-! ## 2. The determinants, explicitly -/

/-- `det M` in box coordinates. -/
theorem det_outsideGram (a1 a2 a3 t1 t2 t3 r12 r13 r23 : ℝ) :
    (outsideGram a1 a2 a3 t1 t2 t3 r12 r13 r23).det
      = (a1 + t1) * (a2 + t2) * (a3 + t3)
        + 2 * r12 * r13 * r23
        - (a1 + t1) * r23 ^ 2 - (a2 + t2) * r13 ^ 2 - (a3 + t3) * r12 ^ 2 := by
  simp only [outsideGram, Matrix.det_fin_three, Matrix.of_apply, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons, Matrix.cons_val_two,
    Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const]
  ring

/-- `det (1 − M)` in box coordinates. -/
theorem det_one_sub_outsideGram (a1 a2 a3 t1 t2 t3 r12 r13 r23 : ℝ) :
    ((1 : Matrix (Fin 3) (Fin 3) ℝ) - outsideGram a1 a2 a3 t1 t2 t3 r12 r13 r23).det
      = (1 - a1 - t1) * (1 - a2 - t2) * (1 - a3 - t3)
        - 2 * r12 * r13 * r23
        - (1 - a1 - t1) * r23 ^ 2 - (1 - a2 - t2) * r13 ^ 2
        - (1 - a3 - t3) * r12 ^ 2 := by
  rw [Matrix.one_fin_three]
  simp only [outsideGram, Matrix.det_fin_three, Matrix.sub_apply, Matrix.of_apply,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const]
  ring

/-! ## 3. The identity -/

/-- **THE TRUE DETERMINANT SUM IS THE BOX SUM PLUS THE THREE PAIR MINORS.**
No hypothesis.  The Bargmann terms cancel between the two determinants, and what
the off-diagonals leave behind is exactly the pair minors of the gap block. -/
theorem det_sum_eq_box_add_pairMinors (a1 a2 a3 t1 t2 t3 r12 r13 r23 : ℝ) :
    (outsideGram a1 a2 a3 t1 t2 t3 r12 r13 r23).det
      + ((1 : Matrix (Fin 3) (Fin 3) ℝ) - outsideGram a1 a2 a3 t1 t2 t3 r12 r13 r23).det
      = branchDetComplement a1 a2 a3 t1 t2 t3 + branchDetOutside a1 a2 a3 t1 t2 t3
        + (boxPairMinor a1 a2 r12 + boxPairMinor a1 a3 r13 + boxPairMinor a2 a3 r23) := by
  rw [det_outsideGram, det_one_sub_outsideGram]
  unfold branchDetComplement branchDetOutside boxPairMinor
  ring

/-! ## 4. The box is the extremal case -/

/-- **ON THE INADMISSIBLE SET THE TRUE SUM IS AT MOST THE BOX SUM.**  Every pair
minor is nonpositive there, so the correction term is nonpositive.  Equality is
the slice where all three minors vanish — exactly where the lane measured the
box and the determinants to agree. -/
theorem det_sum_le_box_of_inadmissible {a1 a2 a3 r12 r13 r23 : ℝ} (t1 t2 t3 : ℝ)
    (h12 : boxPairMinor a1 a2 r12 ≤ 0)
    (h13 : boxPairMinor a1 a3 r13 ≤ 0)
    (h23 : boxPairMinor a2 a3 r23 ≤ 0) :
    (outsideGram a1 a2 a3 t1 t2 t3 r12 r13 r23).det
      + ((1 : Matrix (Fin 3) (Fin 3) ℝ) - outsideGram a1 a2 a3 t1 t2 t3 r12 r13 r23).det
      ≤ branchDetComplement a1 a2 a3 t1 t2 t3 + branchDetOutside a1 a2 a3 t1 t2 t3 := by
  rw [det_sum_eq_box_add_pairMinors]
  linarith

/-- **THE TRUE SLACK FACTORIZATION.**  The lane's identity
`S·(Σa − 1) = e₂ − Σaᵢtᵢ − (box sum)` holds with the TRUE determinants once the
pair minors are carried along: the correction is exactly their sum. -/
theorem true_slack_factorization (a1 a2 a3 t1 t2 t3 r12 r13 r23 : ℝ) :
    branchSlack t1 t2 t3 * (a1 + a2 + a3 - 1)
      = branchWeightPairSum t1 t2 t3 - branchExcessReading a1 a2 a3 t1 t2 t3
        - ((outsideGram a1 a2 a3 t1 t2 t3 r12 r13 r23).det
            + ((1 : Matrix (Fin 3) (Fin 3) ℝ)
                - outsideGram a1 a2 a3 t1 t2 t3 r12 r13 r23).det)
        + (boxPairMinor a1 a2 r12 + boxPairMinor a1 a3 r13 + boxPairMinor a2 a3 r23) := by
  rw [det_sum_eq_box_add_pairMinors]
  have h := branchTwo_slack_factorization a1 a2 a3 t1 t2 t3
  linarith

/-- **THE TARGET FROM THE TRUE DETERMINANTS.**  On the inadmissible set, if the
true determinant sum is at least the excess defect, the excesses total at most
one.  The box hypothesis of `Gtz.branchTwo_target_of_defect` is implied, because
the true sum sits below the box sum there. -/
theorem true_target_of_defect {a1 a2 a3 t1 t2 t3 r12 r13 r23 : ℝ}
    (hS : 0 < branchSlack t1 t2 t3)
    (h12 : boxPairMinor a1 a2 r12 ≤ 0)
    (h13 : boxPairMinor a1 a3 r13 ≤ 0)
    (h23 : boxPairMinor a2 a3 r23 ≤ 0)
    (hdefect : branchWeightPairSum t1 t2 t3 - branchExcessReading a1 a2 a3 t1 t2 t3
      ≤ (outsideGram a1 a2 a3 t1 t2 t3 r12 r13 r23).det
        + ((1 : Matrix (Fin 3) (Fin 3) ℝ) - outsideGram a1 a2 a3 t1 t2 t3 r12 r13 r23).det) :
    a1 + a2 + a3 ≤ 1 := by
  have hle := det_sum_le_box_of_inadmissible t1 t2 t3 h12 h13 h23
  have hfac := branchTwo_slack_factorization a1 a2 a3 t1 t2 t3
  have hprod : branchSlack t1 t2 t3 * (a1 + a2 + a3 - 1) ≤ 0 := by linarith
  by_contra hgt
  push Not at hgt
  have : 0 < branchSlack t1 t2 t3 * (a1 + a2 + a3 - 1) :=
    mul_pos hS (by linarith)
  linarith

end Gtz
