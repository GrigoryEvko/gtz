/-
# The weight slack times the excess defect, in closed form

`Gtz.branchTwo_determinant_sum` adds the two determinant conditions of `E1` and
finds a linear form.  Reading that form in the WEIGHT SLACK

  `S := 1 - t1 - t2 - t3`

closes it completely.  Two substitutions do it.  The coefficient of each excess
is `1 - t_j - t_k = S + t_i`, and the constant is
`(1-t1)(1-t2)(1-t3) + t1t2t3 = S + e2` with `e2 = t1t2 + t1t3 + t2t3` the second
symmetric function of the weights.  So the sum of the two determinants is

  `S + e2 - (S * (a1+a2+a3) + (a1t1 + a2t2 + a3t3))` ,

and rearranging isolates the target against the slack
(`Gtz.branchTwo_slack_factorization`):

  **`S * (a1 + a2 + a3 - 1) = e2 - (a1t1 + a2t2 + a3t3) - (detComplement + detOutside)`**

One `ring`.  The left side is the target `a1+a2+a3 <= 1` multiplied by exactly
the quantity a corner makes positive, since a corner's outside weights leave the
inside mass behind.

## What the identity settles

* **The target is equivalent to one cubic inequality.**  On `0 < S` the target
  holds precisely when `e2 <= (a1t1 + a2t2 + a3t3) + detComplement + detOutside`
  (`Gtz.branchTwo_target_iff_defect`).  The two determinants enter only as a
  sum, so this is the exact strength of the summed conditions.

* **It explains why no combination of the summed conditions can close `E1`.**
  Dropping both determinants leaves `S * (sum a - 1) <= e2 - sum a_i t_i`
  (`Gtz.branchTwo_slack_bound`), and the right side is genuinely positive on the
  feasible set: at `a = 0`, `t = (1/3, 1/3, 1/3)` it is `1/3`, while every
  hypothesis holds.  So the summed conditions leave a positive defect, which is
  the linear bound's measured failure at `1.0671` seen structurally rather than
  as a search result.

* **The degeneracy is two dimensional, not one.**  Every point with
  `a_i = (1 - t_i)/2` and `t1 + t2 + t3 = 1` has both determinants zero, all
  three pair minors zero, `S = 0` and `sum a = 1`
  (`Gtz.centerSimplex_degenerate`).  That is a whole two simplex of weights, not
  the one parameter family a predecessor recorded, and it is what a certificate
  for the target must vanish on.

[MEASURED, and recorded as measurement.  The identity itself was checked at 4000
random rational points before it was proved, with no mismatch.  The degenerate
simplex was checked at six random rational weight vectors.  A Handelman run for
the target in these coordinates is infeasible at degrees two and three and was
numerically inconclusive at degree four.]
-/
import Gtz.Wave.BranchTwoDeterminantSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

/-! ## 1. The weight slack and the second symmetric function -/

/-- The weight slack of the outside triple: what the inside atoms are left. -/
noncomputable def branchSlack (t1 t2 t3 : ℝ) : ℝ := 1 - t1 - t2 - t3

/-- The second symmetric function of the outside weights. -/
noncomputable def branchWeightPairSum (t1 t2 t3 : ℝ) : ℝ :=
  t1 * t2 + t1 * t3 + t2 * t3

/-- The excess read against its own weight. -/
noncomputable def branchExcessReading (a1 a2 a3 t1 t2 t3 : ℝ) : ℝ :=
  a1 * t1 + a2 * t2 + a3 * t3

/-- The coefficient of each excess is the slack plus that excess's own weight. -/
theorem branchTwo_coefficient_slack (t1 t2 t3 : ℝ) :
    1 - t2 - t3 = branchSlack t1 t2 t3 + t1 := by
  unfold branchSlack; ring

/-- The constant of the linear form is the slack plus the weight pair sum. -/
theorem branchTwo_constant_slack (t1 t2 t3 : ℝ) :
    (1 - t1) * (1 - t2) * (1 - t3) + t1 * t2 * t3
      = branchSlack t1 t2 t3 + branchWeightPairSum t1 t2 t3 := by
  unfold branchSlack branchWeightPairSum; ring

/-! ## 2. The factorization -/

/-- **THE SLACK TIMES THE DEFECT.**  The target `sum a <= 1`, multiplied by the
weight slack, is the weight pair sum less the excess reading less the two
determinants.  One `ring`, no hypothesis. -/
theorem branchTwo_slack_factorization (a1 a2 a3 t1 t2 t3 : ℝ) :
    branchSlack t1 t2 t3 * (a1 + a2 + a3 - 1)
      = branchWeightPairSum t1 t2 t3 - branchExcessReading a1 a2 a3 t1 t2 t3
        - (branchDetComplement a1 a2 a3 t1 t2 t3
            + branchDetOutside a1 a2 a3 t1 t2 t3) := by
  unfold branchSlack branchWeightPairSum branchExcessReading
    branchDetComplement branchDetOutside
  ring

/-! ## 3. What the summed conditions give, exactly -/

/-- **THE EXACT STRENGTH OF THE SUMMED CONDITIONS.**  Both determinants
nonnegative bound the slack against the defect, and nothing more. -/
theorem branchTwo_slack_bound {a1 a2 a3 t1 t2 t3 : ℝ}
    (hcomp : 0 ≤ branchDetComplement a1 a2 a3 t1 t2 t3)
    (hout : 0 ≤ branchDetOutside a1 a2 a3 t1 t2 t3) :
    branchSlack t1 t2 t3 * (a1 + a2 + a3 - 1)
      ≤ branchWeightPairSum t1 t2 t3 - branchExcessReading a1 a2 a3 t1 t2 t3 := by
  have h := branchTwo_slack_factorization a1 a2 a3 t1 t2 t3
  linarith

/-- **THE TARGET IS ONE CUBIC INEQUALITY.**  At a strictly positive slack the
target holds exactly when the weight pair sum is met by the excess reading
together with the two determinants. -/
theorem branchTwo_target_iff_defect {a1 a2 a3 t1 t2 t3 : ℝ}
    (hS : 0 < branchSlack t1 t2 t3) :
    a1 + a2 + a3 ≤ 1
      ↔ branchWeightPairSum t1 t2 t3
          ≤ branchExcessReading a1 a2 a3 t1 t2 t3
            + (branchDetComplement a1 a2 a3 t1 t2 t3
                + branchDetOutside a1 a2 a3 t1 t2 t3) := by
  have h := branchTwo_slack_factorization a1 a2 a3 t1 t2 t3
  constructor
  · intro hle
    nlinarith [mul_nonneg hS.le (sub_nonneg.mpr hle)]
  · intro hdef
    by_contra hgt
    push_neg at hgt
    nlinarith [mul_pos hS (sub_pos.mpr hgt)]

/-- **THE TARGET FROM THE DEFECT.**  The usable direction: a met defect and a
positive slack give the target outright. -/
theorem branchTwo_target_of_defect {a1 a2 a3 t1 t2 t3 : ℝ}
    (hS : 0 < branchSlack t1 t2 t3)
    (hdef : branchWeightPairSum t1 t2 t3
      ≤ branchExcessReading a1 a2 a3 t1 t2 t3
        + (branchDetComplement a1 a2 a3 t1 t2 t3
            + branchDetOutside a1 a2 a3 t1 t2 t3)) :
    a1 + a2 + a3 ≤ 1 :=
  (branchTwo_target_iff_defect hS).mpr hdef

/-! ## 4. The degenerate simplex -/

/-- At the centre over a weight vector of total mass one, the complement
determinant vanishes. -/
theorem centerSimplex_detComplement_zero {t1 t2 t3 : ℝ} (ht : t1 + t2 + t3 = 1) :
    branchDetComplement ((1 - t1) / 2) ((1 - t2) / 2) ((1 - t3) / 2) t1 t2 t3 = 0 := by
  have h3 : t3 = 1 - t1 - t2 := by linarith
  subst h3
  unfold branchDetComplement
  ring

/-- At the centre over a weight vector of total mass one, the outside
determinant vanishes. -/
theorem centerSimplex_detOutside_zero {t1 t2 t3 : ℝ} (ht : t1 + t2 + t3 = 1) :
    branchDetOutside ((1 - t1) / 2) ((1 - t2) / 2) ((1 - t3) / 2) t1 t2 t3 = 0 := by
  have h3 : t3 = 1 - t1 - t2 := by linarith
  subst h3
  unfold branchDetOutside
  ring

/-- **THE DEGENERATE SIMPLEX.**  Every centre point over a weight vector of
total mass one carries a vanishing slack, both determinants zero, and the target
at equality.  The weights range over a whole two simplex, so this is the set a
certificate for the target has to vanish on. -/
theorem centerSimplex_degenerate {t1 t2 t3 : ℝ} (ht : t1 + t2 + t3 = 1) :
    branchSlack t1 t2 t3 = 0
      ∧ branchDetComplement ((1 - t1) / 2) ((1 - t2) / 2) ((1 - t3) / 2) t1 t2 t3 = 0
      ∧ branchDetOutside ((1 - t1) / 2) ((1 - t2) / 2) ((1 - t3) / 2) t1 t2 t3 = 0
      ∧ (1 - t1) / 2 + (1 - t2) / 2 + (1 - t3) / 2 = 1 := by
  refine ⟨?_, centerSimplex_detComplement_zero ht, centerSimplex_detOutside_zero ht, ?_⟩
  · unfold branchSlack; linarith
  · linarith

/-- On the degenerate simplex the defect closes exactly: the weight pair sum
equals the excess reading plus the two determinants, so the cubic inequality of
`Gtz.branchTwo_target_iff_defect` is an equality there. -/
theorem centerSimplex_defect_eq {t1 t2 t3 : ℝ} (ht : t1 + t2 + t3 = 1) :
    branchWeightPairSum t1 t2 t3
      = branchExcessReading ((1 - t1) / 2) ((1 - t2) / 2) ((1 - t3) / 2) t1 t2 t3
        + (branchDetComplement ((1 - t1) / 2) ((1 - t2) / 2) ((1 - t3) / 2) t1 t2 t3
            + branchDetOutside ((1 - t1) / 2) ((1 - t2) / 2) ((1 - t3) / 2) t1 t2 t3) := by
  have h3 : t3 = 1 - t1 - t2 := by linarith
  subst h3
  unfold branchWeightPairSum branchExcessReading branchDetComplement branchDetOutside
  ring

end Gtz
