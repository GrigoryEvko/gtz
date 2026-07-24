/-
# The cap-boundary constant C_B and its monotonicity certificate (residual 8, H1b sub-piece)

Residual 8's H1b leg reduces the GAP-S family argmax to ONE explicit function — the
cap-boundary constant

    C_B(L) = 4(L−1)(2L³ − L² − 8L + 8)/(2L−3)²,

the corner-limit value of the X-channel face (direction-independent). Its
cap-boundary monotonicity — that among two-at-cap designs the higher-leverage cap
dominates — is ONE named sub-piece of the H1b argmax wall.

This file lands that sub-piece's exact algebraic certificate. `C_B'(L)` has
numerator `4(L−2)(8L³ − 14L² − L + 8)` and denominator `(2L−3)³`; the cubic factor
has no real root ≥ 0 (its only real root is negative), so on `L ≥ 2` both factors
of the numerator are nonnegative and the denominator is positive — hence C_B is
increasing on `[2, ∞)`. `capBoundaryConstant_derivNumerator_nonneg` is that
numerator positivity, the monotonicity certificate; `capBoundaryConstant_at_five`
cross-checks the closed form against the workflow's exact-verified `C_B(5) = 3088/49`.

NOT closed here: the full `MonotoneOn` wrapper (a real-analysis packaging of this
certificate) and — the genuinely hard part of H1b — that the two-at-cap corner
dominates all INTERIOR family points, which remains numerically-verified only (13
caps). So residual 8's H1b stays OPEN; this lands one named algebraic sub-piece.
-/
import Mathlib

namespace Gtz

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

/-- **The monotonicity certificate** (residual 8 H1b sub-piece): the numerator of
`C_B'(L)`, namely `4(L−2)(8L³ − 14L² − L + 8)`, is nonnegative for `L ≥ 2`. Since
the derivative's denominator `(2L−3)³` is positive there, `C_B'(L) ≥ 0`, so C_B is
increasing on `[2, ∞)` — the cap-boundary monotonicity of the family argmax. The
cubic factor is positive on `L ≥ 2` (its only real root is negative), and `L − 2 ≥ 0`. -/
theorem capBoundaryConstant_derivNumerator_nonneg {leverage : ℝ} (hlev : 2 ≤ leverage) :
    0 ≤ 4 * (leverage - 2) * (8 * leverage ^ 3 - 14 * leverage ^ 2 - leverage + 8) := by
  have hfactor : (0 : ℝ) ≤ leverage - 2 := by linarith
  have hcubic : (0 : ℝ) ≤ 8 * leverage ^ 3 - 14 * leverage ^ 2 - leverage + 8 := by
    nlinarith [mul_nonneg hfactor (sq_nonneg leverage), sq_nonneg (leverage - 2), hlev]
  have hlead : (0 : ℝ) ≤ 4 * (leverage - 2) := by linarith
  exact mul_nonneg hlead hcubic

end Gtz
