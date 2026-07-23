/-
# Theorem EQ, the transferable halves: the law bounds and is bounded

The funneling-law workflow's Theorem EQ says the law ⟺ collared GTZ +
zero-set confinement on a compact class. The two implications that are pure
logic — no compactness, no semialgebraic wrapper — live here, generic over
any margin function `phi` (read: `Φ − 1`) and any distance `dist` (read:
`dist_𝒯`):

* **the law implies the floor**: a Łojasiewicz-type bound
  `phi ≥ c·dist^α` with `c > 0` forces `phi ≥ 0` outright wherever `dist ≥ 0`
  — the law subsumes collared GTZ on its domain;
* **the law confines the zero set**: at `phi = 0` the same bound forces
  `dist = 0` (for `α`-powers preserving positivity) — zero-margin designs
  sit ON the reference variety;
* **the converse needs quantitative inputs**: from a floor `phi ≥ 0` alone
  no law follows (the compactness half is genuinely harder) — but from a
  LINEAR modulus at the zero set (`phi ≥ ρ·dist` near it, the tube law) plus
  an off-tube gap (`phi ≥ gap > 0` at `dist ≥ r`), the two-piece law
  assembles with the explicit constant `min ρ (gap/D)` on a bounded domain.
-/
import Mathlib

namespace Gtz

/-- **The law subsumes the floor**: `phi ≥ c·distᵃ` with `c > 0`, `dist ≥ 0`
gives `phi ≥ 0`. One line, recorded because every consumer quotes it. -/
theorem law_implies_floor {phi dist lawConst : ℝ} {alpha : ℕ}
    (hlaw : lawConst * dist ^ alpha ≤ phi)
    (hconst : 0 < lawConst) (hdist : 0 ≤ dist) : 0 ≤ phi :=
  le_trans (by positivity) hlaw

/-- **The law confines the zero set**: at `phi = 0` the bound forces
`dist = 0` — zero-margin designs sit on the reference variety. -/
theorem law_confines_zero_set {phi dist lawConst : ℝ} {alpha : ℕ}
    (hlaw : lawConst * dist ^ alpha ≤ phi)
    (hconst : 0 < lawConst) (hdist : 0 ≤ dist)
    (halpha : alpha ≠ 0) (hzero : phi = 0) : dist = 0 := by
  by_contra hne
  have hdistPos : 0 < dist := lt_of_le_of_ne hdist (Ne.symm hne)
  have hpowPos : 0 < dist ^ alpha := pow_pos hdistPos alpha
  nlinarith [hlaw, mul_pos hconst hpowPos]

/-- **The two-piece assembly**: a linear tube law near the variety
(`dist ≤ tubeRadius → phi ≥ tubeRate·dist`) plus an off-tube gap
(`dist ≥ tubeRadius → phi ≥ offGap`) assemble into one global linear law
`phi ≥ lawConst·dist` on a bounded domain `dist ≤ domainCap`, with the
explicit constant `lawConst = min tubeRate (offGap/domainCap)`. This is the
compactness half's SHAPE — what the wrapper must produce, with the constant
chain visible. -/
theorem two_piece_law_assembly {phi dist tubeRate tubeRadius offGap
    domainCap : ℝ}
    (htubeRate : 0 < tubeRate) (hoffGap : 0 < offGap)
    (hdomainCap : 0 < domainCap)
    (hdist : 0 ≤ dist) (hdomain : dist ≤ domainCap)
    (htube : dist ≤ tubeRadius → tubeRate * dist ≤ phi)
    (hoff : tubeRadius ≤ dist → offGap ≤ phi) :
    min tubeRate (offGap / domainCap) * dist ≤ phi := by
  rcases le_or_gt dist tubeRadius with hin | hout
  · calc min tubeRate (offGap / domainCap) * dist
        ≤ tubeRate * dist :=
          mul_le_mul_of_nonneg_right (min_le_left _ _) hdist
      _ ≤ phi := htube hin
  · have hoffPhi := hoff hout.le
    calc min tubeRate (offGap / domainCap) * dist
        ≤ (offGap / domainCap) * dist :=
          mul_le_mul_of_nonneg_right (min_le_right _ _) hdist
      _ ≤ (offGap / domainCap) * domainCap :=
          mul_le_mul_of_nonneg_left hdomain (by positivity)
      _ = offGap := by field_simp
      _ ≤ phi := hoffPhi

/-- **The tube law shape**: first-order rate minus second-order curvature —
`phi ≥ rate·dist − curv·dist²` yields the LINEAR law `phi ≥ (rate/2)·dist`
on the explicit radius `dist ≤ rate/(2·curv)`. The Stiemke-tube assembly
(rate 0.206, curvature C₂) in its generic division-free form. -/
theorem tube_law_from_rate_curvature {phi dist rate curv : ℝ}
    (hrate : 0 < rate) (hcurv : 0 < curv) (hdist : 0 ≤ dist)
    (hradius : dist * (2 * curv) ≤ rate)
    (hexpansion : rate * dist - curv * dist ^ 2 ≤ phi) :
    (rate / 2) * dist ≤ phi := by
  have hcurvTerm : curv * dist ^ 2 ≤ (rate / 2) * dist := by
    have hstep : dist * (curv * dist) ≤ dist * (rate / 2) := by
      refine mul_le_mul_of_nonneg_left ?_ hdist
      nlinarith [hradius]
    nlinarith [hstep]
  linarith [hexpansion, hcurvTerm]

/-- **The first-order-model tube expansion**: the reverse-triangle bridge
that PRODUCES `tube_law_from_rate_curvature`'s hypothesis from a Jacobian
singular floor. In any normed space, if the value splits as
`value = linearPart + remainder` with the linear part floored by the
singular value (`rate·dist ≤ ‖linearPart‖`) and the remainder bounded by
the curvature (`‖remainder‖ ≤ curv·dist²`), then the value's norm obeys the
first-order expansion `rate·dist − curv·dist² ≤ ‖value‖`. This is exactly
how `σ₉(F_tan) ≥ 1/5` (the certified singular floor) feeds the tube law:
the margin `‖F(x)‖` inherits the linear rate up to the second-order
remainder. -/
theorem linear_model_tube_expansion {normedSpace : Type*}
    [NormedAddCommGroup normedSpace] {value linearPart remainder : normedSpace}
    {rate curv dist : ℝ}
    (hsplit : value = linearPart + remainder)
    (hlinearFloor : rate * dist ≤ ‖linearPart‖)
    (hremainderBound : ‖remainder‖ ≤ curv * dist ^ 2) :
    rate * dist - curv * dist ^ 2 ≤ ‖value‖ := by
  have hreverse : ‖linearPart‖ - ‖remainder‖ ≤ ‖value‖ := by
    rw [hsplit]
    have htri := norm_sub_norm_le linearPart (-remainder)
    rw [sub_neg_eq_add, norm_neg] at htri
    exact htri
  linarith [hreverse, hlinearFloor, hremainderBound]

end Gtz
