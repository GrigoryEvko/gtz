/-
# The cap-boundary constant C_B and its monotonicity (residual 8, H1b sub-piece)

Residual 8's H1b leg reduces the GAP-S family argmax to ONE explicit function — the
cap-boundary constant

    C_B(L) = 4(L−1)(2L³ − L² − 8L + 8)/(2L−3)²,

the corner-limit value of the X-channel face (direction-independent). Its
cap-boundary monotonicity — that among two-at-cap designs the higher-leverage cap
dominates — is ONE named sub-piece of the H1b argmax wall, here PROVEN in full.

`capBoundaryConstant_hasDerivAt` gives the explicit derivative
`C_B'(L) = 4(L−2)(8L³ − 14L² − L + 8)/(2L−3)³`; `capBoundaryConstant_monotone`
concludes `MonotoneOn C_B [2, ∞)` from the derivative sign (the cubic factor has no
real root ≥ 0, so both factors of the numerator are nonnegative and the denominator
positive on `L ≥ 2`). `capBoundaryConstant_at_five` cross-checks the closed form
against the workflow's exact-verified `C_B(5) = 3088/49`, and
`capBoundaryConstant_derivNumerator_nonneg` is the standalone numerator certificate.

Residual 8's H1b stays OPEN: the genuinely hard part is that the two-at-cap corner
dominates all INTERIOR family points, which remains numerically-verified only (13
caps). This file closes the cap-boundary-monotonicity sub-piece completely.
-/
import Mathlib

namespace Gtz

open Set

/-- **The cap-boundary constant** `C_B(L) = 4(L−1)(2L³ − L² − 8L + 8)/(2L−3)²` —
the GAP-S corner-limit face value, direction-independent (residual 8 H1b's single
explicit function). -/
noncomputable def capBoundaryConstant (leverage : ℝ) : ℝ :=
  4 * (leverage - 1) * (2 * leverage ^ 3 - leverage ^ 2 - 8 * leverage + 8)
    / (2 * leverage - 3) ^ 2

/-- Cross-check against the workflow's exact-verified value `C_B(5) = 3088/49`
(`16·193/49`), confirming the closed form is transcribed correctly. -/
theorem capBoundaryConstant_at_five : capBoundaryConstant 5 = 3088 / 49 := by
  unfold capBoundaryConstant
  norm_num

/-- **The monotonicity certificate**: the numerator of `C_B'(L)`, namely
`4(L−2)(8L³ − 14L² − L + 8)`, is nonnegative for `L ≥ 2`. The cubic factor is
positive on `L ≥ 2` (its only real root is negative), and `L − 2 ≥ 0`. -/
theorem capBoundaryConstant_derivNumerator_nonneg {leverage : ℝ} (hlev : 2 ≤ leverage) :
    0 ≤ 4 * (leverage - 2) * (8 * leverage ^ 3 - 14 * leverage ^ 2 - leverage + 8) := by
  have hfactor : (0 : ℝ) ≤ leverage - 2 := by linarith
  have hcubic : (0 : ℝ) ≤ 8 * leverage ^ 3 - 14 * leverage ^ 2 - leverage + 8 := by
    nlinarith [mul_nonneg hfactor (sq_nonneg leverage), sq_nonneg (leverage - 2), hlev]
  have hlead : (0 : ℝ) ≤ 4 * (leverage - 2) := by linarith
  exact mul_nonneg hlead hcubic

/-- **The explicit derivative** of `C_B`:
`C_B'(L) = 4(L−2)(8L³ − 14L² − L + 8)/(2L−3)³` wherever `2L − 3 ≠ 0`. Built from the
product/quotient rules; the derivative value is matched to the factored form by
`field_simp; ring`. -/
theorem capBoundaryConstant_hasDerivAt {leverage : ℝ} (hne : (2 * leverage - 3) ≠ 0) :
    HasDerivAt capBoundaryConstant
      (4 * (leverage - 2) * (8 * leverage ^ 3 - 14 * leverage ^ 2 - leverage + 8)
        / (2 * leverage - 3) ^ 3) leverage := by
  have e1 : HasDerivAt (fun y : ℝ => 4 * (y - 1)) 4 leverage := by
    simpa using ((hasDerivAt_id leverage).sub_const 1).const_mul (4 : ℝ)
  have a1 : HasDerivAt (fun y : ℝ => 2 * y ^ 3) (2 * (3 * leverage ^ 2)) leverage := by
    simpa using (hasDerivAt_pow 3 leverage).const_mul (2 : ℝ)
  have a2 : HasDerivAt (fun y : ℝ => y ^ 2) (2 * leverage) leverage := by
    simpa using hasDerivAt_pow 2 leverage
  have a3 : HasDerivAt (fun y : ℝ => 8 * y) 8 leverage := by
    simpa using (hasDerivAt_id leverage).const_mul (8 : ℝ)
  have e2 : HasDerivAt (fun y : ℝ => 2 * y ^ 3 - y ^ 2 - 8 * y + 8)
      (2 * (3 * leverage ^ 2) - 2 * leverage - 8) leverage := by
    simpa using ((a1.sub a2).sub a3).add_const (8 : ℝ)
  have hd : HasDerivAt (fun y : ℝ => 2 * y - 3) 2 leverage := by
    simpa using ((hasDerivAt_id leverage).const_mul (2 : ℝ)).sub_const 3
  have hquot : HasDerivAt capBoundaryConstant _ leverage :=
    (e1.mul e2).div (hd.pow 2) (pow_ne_zero 2 hne)
  convert hquot using 1
  simp only [Pi.mul_apply]
  norm_num
  field_simp
  ring

/-- **The cap-boundary monotonicity** (residual 8 H1b sub-piece, PROVEN): `C_B` is
monotone increasing on `[2, ∞)`. Its derivative
`4(L−2)(8L³ − 14L² − L + 8)/(2L−3)³` is nonnegative there — numerator by
`capBoundaryConstant_derivNumerator_nonneg`, denominator positive since `2L−3 > 0`. -/
theorem capBoundaryConstant_monotone : MonotoneOn capBoundaryConstant (Ici 2) := by
  have hcont : ContinuousOn capBoundaryConstant (Ici 2) := fun leverage hlev =>
    (capBoundaryConstant_hasDerivAt
      (by simp only [mem_Ici] at hlev; nlinarith [hlev])).continuousAt.continuousWithinAt
  have hdiff : DifferentiableOn ℝ capBoundaryConstant (interior (Ici 2)) := by
    rw [interior_Ici]
    exact fun leverage hlev => (capBoundaryConstant_hasDerivAt
      (by simp only [mem_Ioi] at hlev; nlinarith [hlev])).differentiableAt.differentiableWithinAt
  refine monotoneOn_of_deriv_nonneg (convex_Ici 2) hcont hdiff ?_
  intro leverage hlev
  rw [interior_Ici, mem_Ioi] at hlev
  have hne : (2 * leverage - 3) ≠ 0 := by nlinarith [hlev]
  rw [(capBoundaryConstant_hasDerivAt hne).deriv]
  have hfac : (0 : ℝ) ≤ leverage - 2 := by linarith
  have hcubic : (0 : ℝ) ≤ 8 * leverage ^ 3 - 14 * leverage ^ 2 - leverage + 8 := by
    nlinarith [mul_nonneg hfac (sq_nonneg leverage), sq_nonneg (leverage - 2), hlev]
  apply div_nonneg
  · nlinarith [hfac, hcubic]
  · have : (0 : ℝ) < 2 * leverage - 3 := by linarith
    positivity

end Gtz
