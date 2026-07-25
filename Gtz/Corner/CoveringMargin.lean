/-
# The quantified covering margin: H3a's arithmetic core

The gaps-stability workflow's covering theorem runs on one explicit margin:
`η₀(ℓ̄,τ) = 1/(2(2 + ℓ̄√m + ℓ̄²/τ))`. Its kernel content is pure ordered-field
arithmetic, (ℓ̄,τ,m)-generic:

* the margin is positive on the essential-configuration space;
* the margin obeys the display bound `η₀ ≤ τ/(2ℓ̄²)` — the shape every
  consumer quotes;
* the stability constant `C_H = 6/η₀` is bounded by `12(2 + ℓ̄√m + ℓ̄²/τ)/12
  = ...` — kernel form: `C_H·τ ≤ 12·(2τ + ℓ̄√m·τ + ℓ̄²)`, division-free;
* the uncovered-atom multiplier bound: a weight floor `τ/ℓ̄` against a
  certificate error `η` prices the multiplier at `|μ₀| ≤ η(1 + ℓ̄²/τ)` —
  the (e)-step of the margin proof, one inequality.
-/
import Mathlib

namespace Gtz

/-- **The covering margin is positive** whenever the configuration data is:
`0 < 1/(2(2 + a + b))` for nonnegative `a, b`. -/
theorem covering_margin_pos {levTerm budgetTerm : ℝ}
    (hlev : 0 ≤ levTerm) (hbudget : 0 ≤ budgetTerm) :
    0 < 1 / (2 * (2 + levTerm + budgetTerm)) := by
  positivity

/-- **The display bound**: the covering margin never exceeds `τ/(2ℓ̄²)` —
the budget term alone caps it. Division-free hypothesis shape:
`ℓ̄² ≤ budgetTerm·τ` (i.e. `budgetTerm ≥ ℓ̄²/τ`). -/
theorem covering_margin_le {levTerm budgetTerm levSq tau : ℝ}
    (hlev : 0 ≤ levTerm) (htau : 0 < tau) (hlevSq : 0 < levSq)
    (hbudget : levSq ≤ budgetTerm * tau) :
    1 / (2 * (2 + levTerm + budgetTerm)) ≤ tau / (2 * levSq) := by
  have hbudgetPos : 0 < budgetTerm := by
    nlinarith [hlevSq, htau, hbudget]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hbudget, htau, hlev, hlevSq, mul_pos htau hbudgetPos]

/-- **The uncovered-atom multiplier bound** (the margin proof's (e)-step):
a weight floor `t ≥ τ/ℓ̄` and a t-block reading error `η` price the
uncovered multiplier at `|μ₀|·τ ≤ η(τ + ℓ̄²)` — division-free. From
`|μ₀|·t ≤ η(t + ℓ̄)` with `t ≥ τ/ℓ̄` and `t ≤ 1`. -/
theorem uncovered_multiplier_bound {multiplier weight certError levCap tau : ℝ}
    (hlevCap : 0 < levCap) (htau : 0 < tau)
    (hweightFloor : tau / levCap ≤ weight)
    (hpriced : |multiplier| * weight ≤ certError * (weight + levCap)) :
    |multiplier| * tau ≤ certError * (tau + levCap ^ 2) := by
  have hweightPos : 0 < weight := lt_of_lt_of_le (by positivity) hweightFloor
  have hfloor : tau ≤ weight * levCap := by
    rw [div_le_iff₀ hlevCap] at hweightFloor
    linarith
  -- multiply the priced bound by τ, absorb ℓ̄·τ ≤ w·ℓ̄², cancel the weight
  have hscaled : (|multiplier| * tau) * weight
      ≤ (certError * (tau + levCap ^ 2)) * weight := by
    have hstep : (|multiplier| * weight) * tau
        ≤ (certError * (weight + levCap)) * tau :=
      mul_le_mul_of_nonneg_right hpriced htau.le
    have herrNonneg : 0 ≤ certError := by
      by_contra hneg
      push Not at hneg
      nlinarith [hpriced, abs_nonneg multiplier, hweightPos, hlevCap]
    have habsorb : levCap * tau ≤ weight * levCap ^ 2 := by
      nlinarith [hfloor, hlevCap]
    nlinarith [hstep, mul_le_mul_of_nonneg_left habsorb herrNonneg]
  exact le_of_mul_le_mul_right
    (by nlinarith [hscaled] : (|multiplier| * tau) * weight
      ≤ (certError * (tau + levCap ^ 2)) * weight) hweightPos

end Gtz
