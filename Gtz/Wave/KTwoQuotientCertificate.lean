/-
# The quotient floor as a linear certificate for the two-zero corner

`Gtz.k2ChartTarget_pos_iff_crossMass` reads the corner as one comparison,
`ω·(A + B) < q·A`, between the erased cross mass `ω = P·td·G` and the second
outside energy `q = te(1+ee)`, weighted by

  `A = T·(1−ty)(1−tz)` ,   `B = (T+1)·Vn` ,   `T = ty + tz` ,

which carry ONLY the two plane weights and the plane angle.  This module
supplies the three missing structures of that comparison.

## 1. The plane data collapses from three scalars to two

Write `m := (1−X)·tz + X·ty` for the mixed plane reading and `p := ty·tz` for
the plane product.  Then EVERY plane quantity of the chart is a polynomial in
`T`, `m` and `p` alone (`Gtz.k2_planeForm_eq`, `Gtz.k2_outsideGap_eq`,
`Gtz.k2_erasedReading_eq`), and the pair `(m, p)` is subject to exactly one
inequality, whose defect is a square:

  `m·(T − m) − p = X·(1 − X)·(ty − tz)²`   (`Gtz.k2_planeSplit_defect`).

So the plane angle enters only through `m`, and only through the range it is
allowed to sweep.

## 2. The threshold has a uniform, angle-free floor

The comparison is `ω/q < A/(A + B)`.  That threshold is bounded below by a
quantity carrying no plane data at all:

  `2·A − (1 − T)·(A + B) = (T + 1)·D` ,
  `D := (1 − X)·tz(1 − tz) + X·ty(1 − ty) > 0`

(`Gtz.k2_thresholdFloor_identity`), hence `A/(A+B) > (1 − T)/2` always.  The
consequence is a SPLIT-FREE sufficient condition with an explicit margin
(`Gtz.k2ChartTarget_margin_identity`):

  `TGT − (q(T+1)/2)·D = (A + B)·((1 − T)·q − 2·ω)/2` ,

so `2·ω ≤ (1 − T)·q` forces `TGT ≥ (q(T+1)/2)·D > 0` with no floor consulted.
[MEASURED: this half-mass test carries 84.7% of the corner region on its own,
and its failure locus is exactly where the mirror quotient is the live floor.
It is NOT the whole corner — max `2ω/((1−T)q) = 1.194` — so the quotient floor
is genuinely needed.  `scratchpad/corank1/f26sym/f44split.jl`.]

## 3. The quotient floor is AFFINE in the erased scale, and that eliminates it

`Gtz.k2ChartQuotient` is degree eight and opaque, but it is degree ONE in `P`
(`Gtz.k2ChartQuotient_affine`):

  `Q1 = P·α + β` ,

with both parts in closed form — `α` linear in `X` with an angle-free part that
factors completely (`Gtz.k2ChartQuotientSlope_xZero`, manifestly negative), and
`β` fully factored and free of `X`.  Since the target is also degree one in `P`,
multiplying the target by `−α` clears `P` from the pair, and what remains is an
identity with NO erased scale anywhere (`Gtz.k2Chart_quotient_certificate`):

  **`(−α)·TGT = CERT + td·G·(A + B)·Q1`** ,
  `CERT := q·(−α)·A − td·G·β·(A + B)` .

This is the certificate the search for this corner never found, and it explains
why: every dictionary in the hunt multiplied the target by a POSITIVE MONOMIAL
combination, while the correct multiplier `−α` is a specific degree-eight
polynomial that no monomial dictionary contains.  The infeasibility at every
rung was a statement about the multiplier space, not about the target.

With the identity in hand the corner needs only two sign conditions, both free
of `P`.  The second is `CERT > 0`.  The first is NOT `α < 0`: that is not a
domain fact, and hypothesising it would make the residual false.  It is the
floor read at the scale where the corner slack vanishes,

  `Ω := q·α + td·G·β < 0` ,

from which `α < 0` FOLLOWS by the affine mean value read backwards
(`Gtz.k2ChartQuotientSlope_neg_of_womBoundary`): the floor is nonnegative at the
scale in hand and negative at the larger boundary scale, so its slope is
negative.

[MEASURED, and the distinction is the point.  On the plain domain with the
angle at most one half, `Ω < 0` holds at 100.0000% of 12640325 points while
`α < 0` holds at only 99.80145% of the same points.  `CERT > 0` holds at
100.0000% of those 12640325 points, and at 100.0000% of 272541 points of the
full corner region.  `f44om.jl`, `f44fix.jl`, `f44weak.jl`, `f44test.jl`.]

## 4. The tight ray, expanded rather than sampled

The hard limit is `tz → 0`, `X → 0`, where the threshold falls to its floor.
There `α = −2·td·te·G` and the certificate factors completely
(`Gtz.k2ChartCrossCert_ray`):

  `CERT = 2·T·td·te²·(1+ee)·G·(1 − td − te)·(1 + ed + ee)` ,

every factor a strict positive of the chart — `1 − td − te > 0` is the weight
budget, and `1 + ed + ee > 0` because `T > 0` forces one excess positive while
both exceed `−1`.  Equivalently the supremum of `ω/q` permitted by the floor on
that ray is `(td + te − ed(1−te) − ee(1−td))/2`, and it sits below the threshold
`(1−T)/2` by exactly

  `(1 + ed + ee)(1 − td − te)/2` .

So the ray carries a STRICT margin in closed form: the corner is not tangent
there, and the normalization the margin wants is named by the margin itself
rather than guessed.  [This replaces the sampled reading `max ω/q = 0.4953 →
0.4919 → 0.4890 as the regime narrows`, which was a limit being sampled instead
of expanded.  `f44ray.py`, `f44closed.py`.]
-/
import Gtz.Wave.KTwoTargetFactored

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000

namespace Gtz

/-! ## 1. The plane split collapses to two scalars -/

/-- **THE PLANE SPLIT HAS ONE DEFECT, AND IT IS A SQUARE.**  With the mixed
plane reading `m = (1−X)tz + X·ty` and the plane product `p = ty·tz`, the pair
`(m, p)` is admissible exactly to the extent that `p ≤ m(T − m)`, and the gap
is the square of the weight difference, tilted by the angle. -/
theorem k2_planeSplit_defect (ty tz X : ℝ) :
    ((1-X)*tz + X*ty) * ((ty + tz) - ((1-X)*tz + X*ty)) - ty*tz
      = X*(1-X)*(ty - tz)^2 := by
  ring

/-- The plane form is the excess total minus the mixed reading minus the
plane product.  No angle survives beyond `m`. -/
theorem k2_planeForm_eq (ty tz X : ℝ) :
    X*tz + (1-X)*ty - ty*tz = (ty + tz) - ((1-X)*tz + X*ty) - ty*tz := by
  ring

/-- The outside gap product is a polynomial in the excess total and the plane
product. -/
theorem k2_outsideGap_eq (ty tz : ℝ) :
    (1-ty)*(1-tz) = 1 - (ty + tz) + ty*tz := by
  ring

/-- The erased axis reading is one minus the mixed plane reading.  This is the
identity that removes the angle from the gap determinant clause. -/
theorem k2_erasedReading_eq (ty tz X : ℝ) :
    (1-X)*(1-tz) + X*(1-ty) = 1 - ((1-X)*tz + X*ty) := by
  ring

/-- The weighted gap `A` in the two collapsed scalars. -/
theorem k2_crossMassGap_eq (ty tz : ℝ) :
    (ty + tz)*((1-ty)*(1-tz)) = (ty + tz)*(1 - (ty + tz) + ty*tz) := by
  ring

/-! ## 2. The uniform threshold floor -/

/-- The angle-free floor quantity of the plane: a convex combination of the two
weight gaps, with the plane angle as the mixing parameter. -/
def k2ChartPlaneGap (ty tz X : ℝ) : ℝ :=
  (1-X)*(tz*(1-tz)) + X*(ty*(1-ty))

/-- **THE THRESHOLD FLOOR IDENTITY.**  Twice the weighted gap, minus the weight
complement times the total, is the shifted total times the plane gap.  One
`ring`, and it is what makes `(1 − T)/2` a lower bound for the corner
threshold `A/(A + B)` at every split and every angle. -/
theorem k2_thresholdFloor_identity (ty tz X : ℝ) :
    2*((ty + tz)*((1-ty)*(1-tz)))
        - (1 - (ty + tz))
          * ((ty + tz)*((1-ty)*(1-tz)) + (ty + tz + 1)*(X*tz + (1-X)*ty - ty*tz))
      = (ty + tz + 1) * k2ChartPlaneGap ty tz X := by
  unfold k2ChartPlaneGap
  ring

/-- The plane gap is strictly positive on the open weight square. -/
theorem k2ChartPlaneGap_pos {ty tz X : ℝ}
    (hty : 0 < ty) (hty1 : ty < 1) (htz : 0 < tz) (htz1 : tz < 1)
    (hX : 0 ≤ X) (hX1 : X ≤ 1) :
    0 < k2ChartPlaneGap ty tz X := by
  have hA : 0 < tz*(1-tz) := mul_pos htz (by linarith)
  have hB : 0 < ty*(1-ty) := mul_pos hty (by linarith)
  unfold k2ChartPlaneGap
  rcases le_or_gt X (1/2) with hh | hh
  · have h1 : (0:ℝ) ≤ 1/2 - X := by linarith
    nlinarith [mul_nonneg h1 hA.le, mul_nonneg hX hB.le]
  · have h1 : (0:ℝ) ≤ X - 1/2 := by linarith
    have h2 : (0:ℝ) ≤ 1 - X := by linarith
    nlinarith [mul_nonneg h1 hB.le, mul_nonneg h2 hA.le]

/-! ## 3. The split-free sufficient condition, with its margin -/

/-- **THE SPLIT-FREE MARGIN IDENTITY.**  The target, minus the plane gap priced
at half the second outside energy times the shifted total, is the weighted total
times the half-mass slack `(1 − T)·q − 2·ω`.  One `ring` after the factored
form.  So a corner whose erased cross mass is at most half the weight
complement of the second outside energy has a target bounded below by an
explicit strict positive, with NO quotient floor consulted. -/
theorem k2ChartTarget_margin_identity (ed ee P td te ty tz X : ℝ)
    (hE : td*ed + te*ee = ty + tz) :
    k2ChartTarget ed ee P td te ty tz X
        - te*(1+ee) * (ty + tz + 1) / 2 * k2ChartPlaneGap ty tz X
      = ((ty + tz)*((1-ty)*(1-tz)) + (ty + tz + 1)*(X*tz + (1-X)*ty - ty*tz))
        * ((1 - (ty + tz))*(te*(1+ee)) - 2*(P*td*(td*(1+ed) + te*(1+ee)))) / 2 := by
  rw [k2ChartTarget_factored ed ee P td te ty tz X hE]
  unfold k2ChartPlaneGap
  ring

/-- **THE HALF-MASS TEST CLOSES THE CORNER WITH NO FLOOR.**  If the erased cross
mass is at most half of the weight complement times the second outside energy,
the target is at least the plane gap priced at that energy — strictly
positive. -/
theorem k2ChartTarget_pos_of_crossMass_half {ed ee P td te ty tz X : ℝ}
    (hE : td*ed + te*ee = ty + tz)
    (hty : 0 < ty) (hty1 : ty < 1) (htz : 0 < tz) (htz1 : tz < 1)
    (hX : 0 ≤ X) (hX1 : X ≤ 1)
    (hq : 0 < te*(1+ee))
    (hbase : 0 ≤ (ty + tz)*((1-ty)*(1-tz))
        + (ty + tz + 1)*(X*tz + (1-X)*ty - ty*tz))
    (hhalf : 2*(P*td*(td*(1+ed) + te*(1+ee))) ≤ (1 - (ty + tz))*(te*(1+ee))) :
    0 < k2ChartTarget ed ee P td te ty tz X := by
  have hgap := k2ChartPlaneGap_pos hty hty1 htz htz1 hX hX1
  have hid := k2ChartTarget_margin_identity ed ee P td te ty tz X hE
  have hT : 0 < ty + tz + 1 := by linarith
  nlinarith [mul_nonneg hbase (by linarith :
      (0:ℝ) ≤ (1 - (ty + tz))*(te*(1+ee)) - 2*(P*td*(td*(1+ed) + te*(1+ee)))),
    mul_pos (mul_pos hq hT) hgap]

/-! ## 4. The quotient floor is affine in the erased scale -/

/-- The slope of the quotient floor in the erased scale.  Linear in the plane
angle: the angle-free part is a product of chart positives with a minus sign,
and the angle part is a sum of two positives. -/
def k2ChartQuotientSlope (ed ee td te tz X : ℝ) : ℝ :=
  -(1-tz) * (td*(1+ed) + te*(1+ee)) * (tz*(td*(1+ed) + te*(1+ee)) + 2*td*te)
    + X * ( td*te*(td*(1+ed) + te*(1+ee))
              * (2 - td - te + ed*(1-te) + ee*(1-td))
            + 2*tz * ( td^2*(1-te)*(1+ed) + te^2*(1-td)*(1+ee) ) )

/-- The constant part of the quotient floor in the erased scale.  Fully
factored, and free of the plane angle. -/
def k2ChartQuotientBase (ed ee td te tz : ℝ) : ℝ :=
  te^2*(1+ee)*(1-tz) * ( ed*(te + tz - 1) + ee*(td + tz - 1) + td + te + 2*tz )

/-- **THE QUOTIENT FLOOR IS DEGREE ONE IN THE ERASED SCALE.**  The eighty-seven
term degree-eight quotient is the erased scale times the slope, plus the base.
One `ring`. -/
theorem k2ChartQuotient_affine (ed ee P td te tz X : ℝ) :
    k2ChartQuotient ed ee P td te tz X
      = P * k2ChartQuotientSlope ed ee td te tz X
        + k2ChartQuotientBase ed ee td te tz := by
  unfold k2ChartQuotient k2ChartQuotientSlope k2ChartQuotientBase
  ring

/-- At zero plane angle the slope is a product of chart positives with a minus
sign. -/
theorem k2ChartQuotientSlope_xZero (ed ee td te tz : ℝ) :
    k2ChartQuotientSlope ed ee td te tz 0
      = -((1-tz) * (td*(1+ed) + te*(1+ee))
          * (tz*(td*(1+ed) + te*(1+ee)) + 2*td*te)) := by
  unfold k2ChartQuotientSlope
  ring

/-- **THE SLOPE IS NEGATIVE AT ZERO ANGLE.**  Every factor is a chart positive,
so the quotient floor caps the erased scale from above there. -/
theorem k2ChartQuotientSlope_neg_of_xZero {ed ee td te tz : ℝ}
    (htd : 0 < td) (hte : 0 < te) (htz1 : tz < 1) (htz : 0 ≤ tz)
    (hG : 0 < td*(1+ed) + te*(1+ee)) :
    k2ChartQuotientSlope ed ee td te tz 0 < 0 := by
  rw [k2ChartQuotientSlope_xZero]
  have h1 : 0 < 1 - tz := by linarith
  have h2 : 0 < tz*(td*(1+ed) + te*(1+ee)) + 2*td*te := by nlinarith
  nlinarith [mul_pos (mul_pos h1 hG) h2]

/-- The quotient floor read at the scale where the erased cross mass exhausts
the second outside energy.  This is `td·G` times the floor evaluated at
`P = q/(td·G)`, the scale at which the corner slack `Wom` vanishes, and it
carries no erased scale. -/
def k2ChartQuotientWomBoundary (ed ee td te tz X : ℝ) : ℝ :=
  te*(1+ee) * k2ChartQuotientSlope ed ee td te tz X
    + td*(td*(1+ed) + te*(1+ee)) * k2ChartQuotientBase ed ee td te tz

/-- The boundary reading at zero plane angle, factored into the outside data
and one bracket. -/
theorem k2ChartQuotientWomBoundary_xZero (ed ee td te tz : ℝ) :
    k2ChartQuotientWomBoundary ed ee td te tz 0
      = (1-tz) * (td*(1+ed) + te*(1+ee)) * (te*(1+ee))
        * ( td*te*(ed*(te + tz - 1) + ee*(td + tz - 1) + td + te + 2*tz)
            - tz*(td*(1+ed) + te*(1+ee)) - 2*td*te ) := by
  unfold k2ChartQuotientWomBoundary k2ChartQuotientSlope k2ChartQuotientBase
  ring

/-- **THE SLOPE SIGN IS FORCED BY THE BOUNDARY READING, WITH NO MEASUREMENT.**
The floor is affine in the erased scale.  If it is nonnegative at the scale in
hand, and negative at the larger scale where the second outside energy is
exhausted, then its slope is negative.  This is the affine mean value read
backwards, and it replaces a hypothesis on the slope by one on a quantity that
carries no erased scale.

[This distinction is not cosmetic.  The boundary reading is negative at
100.0000% of 12640325 sampled points of the plain domain, while the slope
itself is negative at only 99.80145% of the same points — so the slope sign is
NOT a domain fact, and hypothesising it directly would have made the residual
false.  `scratchpad/corank1/f26sym/f44om.jl`, `f44fix.jl`.] -/
theorem k2ChartQuotientSlope_neg_of_womBoundary {ed ee P td te tz X : ℝ}
    (hP : 0 < P)
    (hc : 0 < td*(td*(1+ed) + te*(1+ee)))
    (hWom : 0 < te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))
    (hQ1 : 0 ≤ k2ChartQuotient ed ee P td te tz X)
    (hOm : k2ChartQuotientWomBoundary ed ee td te tz X < 0) :
    k2ChartQuotientSlope ed ee td te tz X < 0 := by
  rw [k2ChartQuotient_affine] at hQ1
  unfold k2ChartQuotientWomBoundary at hOm
  by_contra hcon
  have hcon' : 0 ≤ k2ChartQuotientSlope ed ee td te tz X := not_lt.mp hcon
  nlinarith [mul_nonneg (le_of_lt hc) hQ1, mul_nonneg hcon' (le_of_lt hWom)]

/-! ## 5. The certificate: the erased scale is eliminated -/

/-- The certificate remainder: the second outside energy against the negated
slope on the weighted gap, minus the erased mass factor against the base on the
weighted total.  It carries NO erased scale. -/
def k2ChartCrossCert (ed ee td te ty tz X : ℝ) : ℝ :=
  te*(1+ee) * (-(k2ChartQuotientSlope ed ee td te tz X))
      * ((ty + tz)*((1-ty)*(1-tz)))
    - td*(td*(1+ed) + te*(1+ee)) * k2ChartQuotientBase ed ee td te tz
      * ((ty + tz)*((1-ty)*(1-tz))
          + (ty + tz + 1)*(X*tz + (1-X)*ty - ty*tz))

/-- **THE CERTIFICATE IDENTITY.**  The target times the negated slope is the
certificate remainder plus a manifestly signed multiple of the quotient floor.
The erased scale cancels identically: it enters the target and the floor with
the same coefficient, and the slope is exactly the factor that clears it.

This is the multiplier the corner hunt never had.  A monomial dictionary
multiplies the target by positive monomials, and no such product can equal a
degree-eight polynomial with a sign that varies over the chart. -/
theorem k2Chart_quotient_certificate (ed ee P td te ty tz X : ℝ)
    (hE : td*ed + te*ee = ty + tz) :
    (-(k2ChartQuotientSlope ed ee td te tz X))
        * k2ChartTarget ed ee P td te ty tz X
      = k2ChartCrossCert ed ee td te ty tz X
        + td*(td*(1+ed) + te*(1+ee))
          * ((ty + tz)*((1-ty)*(1-tz))
              + (ty + tz + 1)*(X*tz + (1-X)*ty - ty*tz))
          * k2ChartQuotient ed ee P td te tz X := by
  rw [k2ChartTarget_factored ed ee P td te ty tz X hE,
    k2ChartQuotient_affine ed ee P td te tz X]
  unfold k2ChartCrossCert k2ChartQuotientSlope k2ChartQuotientBase
  ring

/-- **THE CORNER FROM THE CERTIFICATE.**  A negative slope, a positive
certificate remainder and the quotient floor force the target positive.  The
erased scale appears in no hypothesis. -/
theorem k2ChartTarget_pos_of_crossCert {ed ee P td te ty tz X : ℝ}
    (hE : td*ed + te*ee = ty + tz)
    (hslope : k2ChartQuotientSlope ed ee td te tz X < 0)
    (hcert : 0 < k2ChartCrossCert ed ee td te ty tz X)
    (htd : 0 < td) (hG : 0 < td*(1+ed) + te*(1+ee))
    (hbase : 0 ≤ (ty + tz)*((1-ty)*(1-tz))
        + (ty + tz + 1)*(X*tz + (1-X)*ty - ty*tz))
    (hQ1 : 0 ≤ k2ChartQuotient ed ee P td te tz X) :
    0 < k2ChartTarget ed ee P td te ty tz X := by
  have hid := k2Chart_quotient_certificate ed ee P td te ty tz X hE
  have hmul : 0 ≤ td*(td*(1+ed) + te*(1+ee))
      * ((ty + tz)*((1-ty)*(1-tz))
          + (ty + tz + 1)*(X*tz + (1-X)*ty - ty*tz))
      * k2ChartQuotient ed ee P td te tz X := by
    apply mul_nonneg
    · exact mul_nonneg (le_of_lt (mul_pos htd hG)) hbase
    · exact hQ1
  have hpos : 0 < (-(k2ChartQuotientSlope ed ee td te tz X))
      * k2ChartTarget ed ee P td te ty tz X := by
    rw [hid]; linarith
  by_contra hcon
  push_neg at hcon
  nlinarith [hpos, hslope, hcon]

/-! ## 6. The tight ray -/

/-- **THE CERTIFICATE ON THE TIGHT RAY, FACTORED.**  At zero plane weight and
zero plane angle the remainder is a product of six chart quantities.  The two
that carry the content are the weight budget `1 − td − te` and the excess sum
`1 + ed + ee`, and both are strict positives of the corner: the budget because
the four weights of the chart total less than one, the excess sum because the
excess total is positive, which forces one of the two excesses positive while
both exceed `−1`. -/
theorem k2ChartCrossCert_ray (ed ee td te : ℝ) :
    k2ChartCrossCert ed ee td te (td*ed + te*ee) 0 0
      = 2*(td*ed + te*ee) * td * te^2 * (1+ee) * (td*(1+ed) + te*(1+ee))
        * (1 - td - te) * (1 + ed + ee) := by
  unfold k2ChartCrossCert k2ChartQuotientSlope k2ChartQuotientBase
  ring

/-- **THE EXCESS SUM IS POSITIVE AT EVERY CORNER.**  A positive excess total
forces one excess positive, and the other exceeds `−1`. -/
theorem k2Chart_excessSum_pos {ed ee td te : ℝ}
    (htd : 0 < td) (hte : 0 < te)
    (hed : -1 < ed) (hee : -1 < ee)
    (hT : 0 < td*ed + te*ee) :
    0 < 1 + ed + ee := by
  rcases le_or_gt ed 0 with h | h
  · have h1 : td*ed ≤ 0 := by nlinarith
    have h2 : 0 < te*ee := by linarith
    have h3 : 0 < ee := by nlinarith
    linarith
  · linarith

/-- **THE RAY CARRIES A STRICT MARGIN.**  On the tight ray the certificate
remainder is strictly positive, so the corner holds there with room. -/
theorem k2ChartCrossCert_ray_pos {ed ee td te : ℝ}
    (htd : 0 < td) (hte : 0 < te)
    (hed : -1 < ed) (hee : -1 < ee)
    (hT : 0 < td*ed + te*ee)
    (hbudget : td + te < 1)
    (hG : 0 < td*(1+ed) + te*(1+ee)) :
    0 < k2ChartCrossCert ed ee td te (td*ed + te*ee) 0 0 := by
  rw [k2ChartCrossCert_ray]
  have hsum := k2Chart_excessSum_pos htd hte hed hee hT
  have hb : 0 < 1 - td - te := by linarith
  have hq : 0 < 1 + ee := by linarith
  have h1 : 0 < 2*(td*ed + te*ee) * td := by positivity
  have h2 : 0 < te^2 * (1+ee) := by positivity
  nlinarith [mul_pos (mul_pos h1 h2) (mul_pos (mul_pos hG hb) hsum)]

/-! ## 7. The remainder is affine in the angle and quadratic in the plane weight -/

/-- **THE REMAINDER IS AFFINE IN THE PLANE ANGLE.**  The slope is affine in the
angle, the base carries none, the weighted gap carries none, and the weighted
total is affine, so the remainder interpolates linearly between its two
endpoints on the low-angle half. -/
theorem k2ChartCrossCert_xInterp (ed ee td te ty tz X : ℝ) :
    k2ChartCrossCert ed ee td te ty tz X
      = (1 - 2*X) * k2ChartCrossCert ed ee td te ty tz 0
        + 2*X * k2ChartCrossCert ed ee td te ty tz (1/2) := by
  unfold k2ChartCrossCert k2ChartQuotientSlope k2ChartQuotientBase
  ring

/-- **THE LOW-ANGLE HALF NEEDS ONLY ITS TWO ENDPOINTS.**  Affine on an interval,
positive at both ends, positive throughout. -/
theorem k2ChartCrossCert_pos_of_endpoints {ed ee td te ty tz X : ℝ}
    (hX : 0 ≤ X) (hX2 : X ≤ 1/2)
    (h0 : 0 < k2ChartCrossCert ed ee td te ty tz 0)
    (h1 : 0 < k2ChartCrossCert ed ee td te ty tz (1/2)) :
    0 < k2ChartCrossCert ed ee td te ty tz X := by
  rw [k2ChartCrossCert_xInterp]
  have hA : (0:ℝ) ≤ 1 - 2*X := by linarith
  nlinarith [mul_nonneg hA h0.le, mul_nonneg hX h1.le]

/-- The middle coefficient of the zero-angle remainder in the plane weight.
It is the one quantity of the whole corner whose sign is not read off the
chart. -/
def k2ChartCrossCertMid (ed ee td te : ℝ) : ℝ :=
  -ed^3*td^3 - 3*ed^2*ee*td^2*te - ed^2*td^3 - 3*ed^2*td^2*te + ed^2*td^2
    - 3*ed*ee^2*td*te^2 - 4*ed*ee*td^2*te - 4*ed*ee*td*te^2 + 2*ed*ee*td*te
    - 2*ed*td^2*te + ed*td^2 + ed*td*te^2 - ee^3*te^3 - 3*ee^2*td*te^2
    - ee^2*te^3 + ee^2*te^2 + ee*td^2*te - 2*ee*td*te^2 + ee*te^2
    + td^2*te + td*te^2

/-- **THE ZERO-ANGLE REMAINDER, IN FULL.**  On the excess surface the remainder
at zero plane angle is the outside data times a QUADRATIC in the plane weight
`tz`, whose constant term is the tight-ray value and whose leading term is a
sum of two chart positives.  Only the middle coefficient is unsigned, so the
zero-angle branch of the corner is a single discriminant question in the four
outside scalars. -/
theorem k2ChartCrossCert_xZero (ed ee td te tz : ℝ) :
    k2ChartCrossCert ed ee td te (td*ed + te*ee - tz) tz 0
      = te*(1+ee) * (1-tz)^2 * (td*(1+ed) + te*(1+ee))
        * ( 2*td*te*(td*ed + te*ee)*(1 + ed + ee)*(1 - td - te)
            + tz * k2ChartCrossCertMid ed ee td te
            + tz^2 * ( (td*ed + te*ee)*(td*(1+ed) + te*(1+ee))
                        + td*te*(2 + ed + ee) ) ) := by
  unfold k2ChartCrossCert k2ChartQuotientSlope k2ChartQuotientBase
    k2ChartCrossCertMid
  ring

/-- The leading coefficient of the zero-angle remainder is a sum of two chart
positives. -/
theorem k2ChartCrossCert_leadCoeff_pos {ed ee td te : ℝ}
    (htd : 0 < td) (hte : 0 < te) (hed : -1 < ed) (hee : -1 < ee)
    (hT : 0 < td*ed + te*ee) (hG : 0 < td*(1+ed) + te*(1+ee)) :
    0 < (td*ed + te*ee)*(td*(1+ed) + te*(1+ee)) + td*te*(2 + ed + ee) := by
  have h1 : 0 < (td*ed + te*ee)*(td*(1+ed) + te*(1+ee)) := mul_pos hT hG
  have h2 : 0 < td*te*(2 + ed + ee) := by
    apply mul_pos (mul_pos htd hte); linarith
  linarith

/-- **THE ZERO-ANGLE BRANCH IS FREE WHEN THE MIDDLE COEFFICIENT IS NONNEGATIVE.**
The quadratic then has every coefficient nonnegative and a strictly positive
constant term, so it is positive at every positive plane weight, and the
outside prefactor is a product of chart positives.

[MEASURED: this covers 93.3996% of the four-scalar arena outright.  Of the
remainder, 1.3983% has its vertex at or past the plane total, and 5.2021% has a
strictly positive discriminant.  NOTHING falls outside those three cases —
0.0% of 24222982 points.  `scratchpad/corank1/f26sym/f44p1.jl`,
`f44vertex.jl`.] -/
theorem k2ChartCrossCert_xZero_pos_of_midNonneg {ed ee td te tz : ℝ}
    (htd : 0 < td) (hte : 0 < te) (hed : -1 < ed) (hee : -1 < ee)
    (htz : 0 < tz) (htz1 : tz < 1)
    (hT : 0 < td*ed + te*ee)
    (hbudget : td + te < 1)
    (hmid : 0 ≤ k2ChartCrossCertMid ed ee td te) :
    0 < k2ChartCrossCert ed ee td te (td*ed + te*ee - tz) tz 0 := by
  rw [k2ChartCrossCert_xZero]
  have hG : 0 < td*(1+ed) + te*(1+ee) := by nlinarith
  have hsum := k2Chart_excessSum_pos htd hte hed hee hT
  have hb : 0 < 1 - td - te := by linarith
  have hee1 : 0 < 1 + ee := by linarith
  have hq : 0 < te*(1+ee) := mul_pos hte hee1
  have hsq : 0 < (1-tz)^2 := pow_pos (by linarith) 2
  have hp0 : 0 < 2*td*te*(td*ed + te*ee)*(1 + ed + ee)*(1 - td - te) :=
    mul_pos (mul_pos (mul_pos (mul_pos (by linarith : (0:ℝ) < 2*td) hte) hT)
      hsum) hb
  have hp2 := k2ChartCrossCert_leadCoeff_pos htd hte hed hee hT hG
  have hmidterm : 0 ≤ tz * k2ChartCrossCertMid ed ee td te :=
    mul_nonneg htz.le hmid
  have hlead : 0 < tz^2 * ((td*ed + te*ee)*(td*(1+ed) + te*(1+ee))
      + td*te*(2 + ed + ee)) := mul_pos (pow_pos htz 2) hp2
  have hbr : 0 < 2*td*te*(td*ed + te*ee)*(1 + ed + ee)*(1 - td - te)
      + tz * k2ChartCrossCertMid ed ee td te
      + tz^2 * ((td*ed + te*ee)*(td*(1+ed) + te*(1+ee))
          + td*te*(2 + ed + ee)) := by linarith
  exact mul_pos (mul_pos (mul_pos hq hsq) hG) hbr

/-- **THE ZERO-ANGLE REMAINDER IS A SUM OF TWO PRODUCTS OF CHART POSITIVES.**
The quadratic of `Gtz.k2ChartCrossCert_xZero` regroups, on the excess surface,
into two terms in which every factor is a positive of the corner:

  `tz·(1 − ty)·(T·G + td·te)`  and
  `td·te·(2T − tz)·(1 − td − te − tz)·(1 + ed + ee)` .

The middle coefficient of the quadratic never has to be signed, and no
discriminant is needed.  The regrouping is the identity `Ξ = (1 − T) − E` with
`E = (1 − td − te − tz)(1 + ed + ee) − tz`, which exposes the excess sum as the
carrier of the whole zero-angle branch. -/
theorem k2ChartCrossCert_xZero_split (ed ee td te tz : ℝ) :
    k2ChartCrossCert ed ee td te (td*ed + te*ee - tz) tz 0
      = te*(1+ee) * (1-tz)^2 * (td*(1+ed) + te*(1+ee))
        * ( tz * (1 - (td*ed + te*ee) + tz)
              * ((td*ed + te*ee)*(td*(1+ed) + te*(1+ee)) + td*te)
            + td*te * (2*(td*ed + te*ee) - tz)
              * (1 - td - te - tz) * (1 + ed + ee) ) := by
  unfold k2ChartCrossCert k2ChartQuotientSlope k2ChartQuotientBase
  ring

/-- **THE ZERO-ANGLE BRANCH OF THE CORNER IS CLOSED, UNCONDITIONALLY.**  Every
factor of the split is a positive of the corner: the plane weight, the weight
complement of the retained plane atom, the excess total against the outside
mass, the plane total against the plane weight, the weight budget, and the
excess sum.

This supersedes the three-case reading of the branch.  The case split into a
nonnegative middle coefficient, a vertex past the plane total, and a positive
discriminant was an artifact of the quadratic form: in the regrouped form no
case survives.  [The measured split was 93.3996% / 1.3983% / 5.2021%, and the
discriminant — positive at only 76.67% of the arena — was never the right
question.] -/
theorem k2ChartCrossCert_xZero_pos {ed ee td te tz : ℝ}
    (htd : 0 < td) (hte : 0 < te) (hed : -1 < ed) (hee : -1 < ee)
    (htz : 0 < tz)
    (hT : 0 < td*ed + te*ee)
    (hty : tz < td*ed + te*ee)
    (hbudget : td + te + (td*ed + te*ee) < 1) :
    0 < k2ChartCrossCert ed ee td te (td*ed + te*ee - tz) tz 0 := by
  rw [k2ChartCrossCert_xZero_split]
  have hG : 0 < td*(1+ed) + te*(1+ee) := by nlinarith
  have hsum := k2Chart_excessSum_pos htd hte hed hee hT
  have hee1 : 0 < 1 + ee := by linarith
  have hq : 0 < te*(1+ee) := mul_pos hte hee1
  have hbud : 0 < 1 - td - te - tz := by linarith
  have htz1 : 0 < 1 - tz := by nlinarith
  have hsq : 0 < (1-tz)^2 := pow_pos htz1 2
  have hgap : 0 < 1 - (td*ed + te*ee) + tz := by linarith
  have htwo : 0 < 2*(td*ed + te*ee) - tz := by linarith
  have hmass : 0 < (td*ed + te*ee)*(td*(1+ed) + te*(1+ee)) + td*te := by
    have := mul_pos hT hG
    have h2 := mul_pos htd hte
    linarith
  have hL : 0 < tz * (1 - (td*ed + te*ee) + tz)
      * ((td*ed + te*ee)*(td*(1+ed) + te*(1+ee)) + td*te) :=
    mul_pos (mul_pos htz hgap) hmass
  have hR : 0 < td*te * (2*(td*ed + te*ee) - tz)
      * (1 - td - te - tz) * (1 + ed + ee) :=
    mul_pos (mul_pos (mul_pos (mul_pos htd hte) htwo) hbud) hsum
  exact mul_pos (mul_pos (mul_pos hq hsq) hG) (by linarith)

/-- The excess balance of the corner: the negated slope against the excess
total, less the outside mass against the weighted total. -/
def k2ChartCrossDelta (ed ee td te ty tz X : ℝ) : ℝ :=
  (-(k2ChartQuotientSlope ed ee td te tz X)) * (ty + tz)
    - td*te*(td*(1+ed) + te*(1+ee))
      * ((ty + tz)*((1-ty)*(1-tz))
          + (ty + tz + 1)*(X*tz + (1-X)*ty - ty*tz))

/-- **THE REMAINDER IS THE EXCESS BALANCE PLUS ONE MANIFESTLY POSITIVE TERM.**
Substituting `Ξ = (1 − T) − E` with `E + tz = (1 − td − te − tz)(1 + ed + ee)`
splits the remainder into the weight complement of the retained plane atom
against the excess balance, plus a product in which every factor is a chart
positive.  The whole corner is therefore carried by the single quantity
`Gtz.k2ChartCrossDelta`.

[At zero plane angle the balance is a product of five chart positives
(`Gtz.k2ChartCrossDelta_xZero`), which is what closes that branch.  It does NOT
stay positive at larger angles: MEASURED 93.1005% over the domain and only
81.9154% at the half angle, worst value −3.30e-2 at `(ed,ee,td,te,tz) =
(0.8328, 3.7979, 0.20546, 0.12956, 9.267e-6)`.  So this split is exactly tight
at zero angle and TOO LOSSY at the half angle — the half-angle endpoint needs a
different regrouping, not this one.  `scratchpad/corank1/f26sym/f44dl.jl`.] -/
theorem k2ChartCrossCert_delta_split (ed ee td te tz X : ℝ) :
    k2ChartCrossCert ed ee td te (td*ed + te*ee - tz) tz X
      = te*(1+ee) * (1-tz)
        * ( (1 - (td*ed + te*ee - tz))
              * k2ChartCrossDelta ed ee td te (td*ed + te*ee - tz) tz X
            + td*te*(td*(1+ed) + te*(1+ee))
              * ((td*ed + te*ee)*((1 - (td*ed + te*ee - tz))*(1-tz))
                  + (td*ed + te*ee + 1)
                    * (X*tz + (1-X)*(td*ed + te*ee - tz)
                        - (td*ed + te*ee - tz)*tz))
              * (1 - td - te - tz) * (1 + ed + ee) ) := by
  unfold k2ChartCrossCert k2ChartCrossDelta k2ChartQuotientSlope
    k2ChartQuotientBase
  ring

/-- **THE EXCESS BALANCE AT ZERO ANGLE IS A PRODUCT OF FIVE CHART POSITIVES.**
The two middle factors are the outside mass less each plane weight, both of
which the chart carries as positive. -/
theorem k2ChartCrossDelta_xZero (ed ee td te tz : ℝ) :
    k2ChartCrossDelta ed ee td te (td*ed + te*ee - tz) tz 0
      = tz * (1-tz) * (td*ed + te*ee + td) * (td*ed + te*ee + te)
        * (td*(1+ed) + te*(1+ee)) := by
  unfold k2ChartCrossDelta k2ChartQuotientSlope
  ring

/-! ## 8. The residual: one endpoint, five scalars -/

/-- **THE RESIDUAL OF THE WHOLE LOW-ANGLE CORNER, AT ONE ANGLE.**  The
remainder is affine in the plane angle and its zero-angle endpoint is closed
unconditionally, so nothing is left but the half-angle endpoint.  Five scalars,
no erased scale, no quotient, no plane angle.

[MEASURED positive at 100.0000% of 12637451 points of the plain domain, with
infimum zero on the degenerate ray `td, te, tz → 0` — so the proof must be a
product of chart positives, exactly as the zero-angle endpoint turned out to
be.  `scratchpad/corank1/f26sym/f44end.jl`.] -/
def K2ChartCrossCertHalfAngle : Prop :=
  ∀ ed ee td te tz : ℝ,
    0 < td → 0 < te → 0 < tz → (-1 : ℝ) < ed → (-1 : ℝ) < ee →
    tz < td*ed + te*ee →
    td + te + (td*ed + te*ee) < 1 →
    0 < k2ChartCrossCert ed ee td te (td*ed + te*ee - tz) tz (1/2)

/-- **THE HALF-ANGLE ENDPOINT CARRIES THE WHOLE LOW-ANGLE HALF.**  Affine in the
angle, closed at zero angle, so one endpoint decides every angle up to a
half. -/
theorem k2ChartCrossCert_pos_of_halfAngle (h : K2ChartCrossCertHalfAngle)
    {ed ee td te tz X : ℝ}
    (htd : 0 < td) (hte : 0 < te) (hed : -1 < ed) (hee : -1 < ee)
    (htz : 0 < tz) (hX : 0 ≤ X) (hX2 : X ≤ 1/2)
    (hT : 0 < td*ed + te*ee)
    (hty : tz < td*ed + te*ee)
    (hbudget : td + te + (td*ed + te*ee) < 1) :
    0 < k2ChartCrossCert ed ee td te (td*ed + te*ee - tz) tz X :=
  k2ChartCrossCert_pos_of_endpoints hX hX2
    (k2ChartCrossCert_xZero_pos htd hte hed hee htz hT hty hbudget)
    (h ed ee td te tz htd hte htz hed hee hty hbudget)

/-- The residue of the half-angle endpoint above its tight-ray lower bound,
with the halving cleared.  It vanishes to first order in the plane weight at
the tight ray, and it is the last unsigned object of the low-angle corner. -/
def k2ChartCrossHalfResidue (ed ee td te tz : ℝ) : ℝ :=
    ed^4*td^4*te + 2*ed^4*td^4*tz - 2*ed^4*td^4 + ed^3*ee*td^4*te +
    3*ed^3*ee*td^3*te^2 + 8*ed^3*ee*td^3*te*tz - 8*ed^3*ee*td^3*te +
    5*ed^3*td^4*te + 4*ed^3*td^4*tz - 2*ed^3*td^4 + 4*ed^3*td^3*te^2 +
    6*ed^3*td^3*te*tz - 8*ed^3*td^3*te - 2*ed^3*td^3*tz^2 + 2*ed^3*td^3 +
    3*ed^2*ee^2*td^3*te^2 + 3*ed^2*ee^2*td^2*te^3 + 12*ed^2*ee^2*td^2*te^2*tz
    - 12*ed^2*ee^2*td^2*te^2 + 4*ed^2*ee*td^4*te + 15*ed^2*ee*td^3*te^2 +
    14*ed^2*ee*td^3*te*tz - 12*ed^2*ee*td^3*te + 8*ed^2*ee*td^2*te^3 +
    16*ed^2*ee*td^2*te^2*tz - 18*ed^2*ee*td^2*te^2 - 6*ed^2*ee*td^2*te*tz^2 +
    6*ed^2*ee*td^2*te + 7*ed^2*td^4*te + 2*ed^2*td^4*tz + 10*ed^2*td^3*te^2 +
    8*ed^2*td^3*te*tz - 12*ed^2*td^3*te - 4*ed^2*td^3*tz^2 - 2*ed^2*td^3*tz +
    2*ed^2*td^3 + 3*ed^2*td^2*te^3 + 2*ed^2*td^2*te^2*tz - 4*ed^2*td^2*te^2 -
    6*ed^2*td^2*te*tz^2 + 2*ed^2*td^2*te*tz + 4*ed^2*td^2*te +
    3*ed*ee^3*td^2*te^3 + ed*ee^3*td*te^4 + 8*ed*ee^3*td*te^3*tz -
    8*ed*ee^3*td*te^3 + 8*ed*ee^2*td^3*te^2 + 15*ed*ee^2*td^2*te^3 +
    16*ed*ee^2*td^2*te^2*tz - 18*ed*ee^2*td^2*te^2 + 4*ed*ee^2*td*te^4 +
    14*ed*ee^2*td*te^3*tz - 12*ed*ee^2*td*te^3 - 6*ed*ee^2*td*te^2*tz^2 +
    6*ed*ee^2*td*te^2 + 3*ed*ee*td^4*te + 17*ed*ee*td^3*te^2 +
    4*ed*ee*td^3*te*tz - 4*ed*ee*td^3*te + 17*ed*ee*td^2*te^3 +
    16*ed*ee*td^2*te^2*tz - 24*ed*ee*td^2*te^2 - 10*ed*ee*td^2*te*tz^2 +
    6*ed*ee*td^2*te + 3*ed*ee*td*te^4 + 4*ed*ee*td*te^3*tz - 4*ed*ee*td*te^3 -
    10*ed*ee*td*te^2*tz^2 + 6*ed*ee*td*te^2 + 3*ed*td^4*te + 6*ed*td^3*te^2 -
    4*ed*td^3*te - 2*ed*td^3*tz^2 - 2*ed*td^3*tz + 3*ed*td^2*te^3 -
    2*ed*td^2*te^2*tz - 4*ed*td^2*te^2 - 10*ed*td^2*te*tz^2 + 2*ed*td^2*te*tz
    + 4*ed*td^2*te - 2*ed*td*te^3*tz - 4*ed*td*te^2*tz^2 + ee^4*td*te^4 +
    2*ee^4*te^4*tz - 2*ee^4*te^4 + 4*ee^3*td^2*te^3 + 5*ee^3*td*te^4 +
    6*ee^3*td*te^3*tz - 8*ee^3*td*te^3 + 4*ee^3*te^4*tz - 2*ee^3*te^4 -
    2*ee^3*te^3*tz^2 + 2*ee^3*te^3 + 3*ee^2*td^3*te^2 + 10*ee^2*td^2*te^3 +
    2*ee^2*td^2*te^2*tz - 4*ee^2*td^2*te^2 + 7*ee^2*td*te^4 +
    8*ee^2*td*te^3*tz - 12*ee^2*td*te^3 - 6*ee^2*td*te^2*tz^2 +
    2*ee^2*td*te^2*tz + 4*ee^2*td*te^2 + 2*ee^2*te^4*tz - 4*ee^2*te^3*tz^2 -
    2*ee^2*te^3*tz + 2*ee^2*te^3 + 3*ee*td^3*te^2 - 2*ee*td^3*te*tz +
    6*ee*td^2*te^3 - 2*ee*td^2*te^2*tz - 4*ee*td^2*te^2 - 4*ee*td^2*te*tz^2 +
    3*ee*td*te^4 - 4*ee*td*te^3 - 10*ee*td*te^2*tz^2 + 2*ee*td*te^2*tz +
    4*ee*td*te^2 - 2*ee*te^3*tz^2 - 2*ee*te^3*tz - 2*td^3*te*tz -
    4*td^2*te^2*tz - 4*td^2*te*tz^2 - 2*td*te^3*tz - 4*td*te^2*tz^2

/-- **THE HALF-ANGLE ENDPOINT, SPLIT AT ITS TIGHT-RAY VALUE.**  Twice the
endpoint is the outside data times twice the tight-ray product, plus the plane
weight times the residue.  The tight-ray product carries the SAME factors that
close the zero-angle branch -- the excess sum and the weight budget -- and the
residue vanishes when the plane weight does.

[MEASURED by adversarial descent, 250 restarts of 200000 steps: the residue,
normalised by the tight-ray product, has infimum 0.7097 -- BOUNDED AWAY FROM
ZERO.  This is the first quantity of this corner whose normalised margin does
not vanish, so a bounded-below certificate is possible here where it was
provably impossible for the remainder itself.
`scratchpad/corank1/f26sym/f44remtest.jl`.] -/
theorem k2ChartCrossCert_half_split (ed ee td te tz : ℝ) :
    2 * k2ChartCrossCert ed ee td te (td*ed + te*ee - tz) tz (1/2)
      = te*(1+ee) * (1-tz)
        * ( 2 * (td*te*(td*ed + te*ee)*(td*(1+ed) + te*(1+ee))
                  * (1 + ed + ee) * (1 - td - te - tz))
            + tz * k2ChartCrossHalfResidue ed ee td te tz ) := by
  unfold k2ChartCrossCert k2ChartCrossHalfResidue k2ChartQuotientSlope
    k2ChartQuotientBase
  ring

/-- **THE HALF-ANGLE ENDPOINT FROM A SINGLE NONNEGATIVITY.**  The tight-ray
product is a product of chart positives, so the endpoint is positive as soon as
the residue is nonnegative.  This is the whole low-angle corner reduced to one
sign, on a quantity whose normalised margin does NOT vanish. -/
theorem k2ChartCrossCert_half_pos_of_residue {ed ee td te tz : ℝ}
    (htd : 0 < td) (hte : 0 < te) (hed : -1 < ed) (hee : -1 < ee)
    (htz : 0 < tz)
    (hT : 0 < td*ed + te*ee)
    (hty : tz < td*ed + te*ee)
    (hbudget : td + te + (td*ed + te*ee) < 1)
    (hres : 0 ≤ k2ChartCrossHalfResidue ed ee td te tz) :
    0 < k2ChartCrossCert ed ee td te (td*ed + te*ee - tz) tz (1/2) := by
  have hG : 0 < td*(1+ed) + te*(1+ee) := by nlinarith
  have hsum := k2Chart_excessSum_pos htd hte hed hee hT
  have hee1 : 0 < 1 + ee := by linarith
  have hq : 0 < te*(1+ee) := mul_pos hte hee1
  have hbud : 0 < 1 - td - te - tz := by linarith
  have htz1 : 0 < 1 - tz := by nlinarith
  have hbase : 0 < td*te*(td*ed + te*ee)*(td*(1+ed) + te*(1+ee))
      * (1 + ed + ee) * (1 - td - te - tz) :=
    mul_pos (mul_pos (mul_pos (mul_pos (mul_pos htd hte) hT) hG) hsum) hbud
  have hkey := k2ChartCrossCert_half_split ed ee td te tz
  have hrt : 0 ≤ tz * k2ChartCrossHalfResidue ed ee td te tz :=
    mul_nonneg htz.le hres
  nlinarith [hkey, mul_pos hq htz1, mul_pos (mul_pos hq htz1) hbase,
    mul_nonneg (mul_pos hq htz1).le hrt]

/-! ## 9. The scale-free residual -/

/-- **THE TWO-ZERO CORNER, REDUCED TO TWO SCALE-FREE SIGNS.**  On the low-angle
half the corner needs only that the quotient slope is negative and the
certificate remainder positive.  Both statements are free of the erased scale
`P`, so the residual carries six chart variables where the target carried
eight, and it carries no quotient.

[MEASURED: the remainder is positive at 100.0000% of 272541 feasible corner
points on the low-angle half, and wherever it is positive the slope is negative
— 461751 of 461751.  `scratchpad/corank1/f26sym/f44test.jl`.] -/
def K2ChartCrossCertPositivity : Prop :=
  ∀ ed ee td te ty tz X : ℝ,
    0 < ty → 0 < tz → 0 < td → 0 < te →
    0 ≤ X → X ≤ 1/2 → (-1 : ℝ) < ed → (-1 : ℝ) < ee →
    td + te + ty + tz < 1 →
    0 < td*ed + te*ee →
    td*ed + te*ee = ty + tz →
    k2ChartQuotientWomBoundary ed ee td te tz X < 0
      ∧ 0 < k2ChartCrossCert ed ee td te ty tz X

/-- **THE LOW-ANGLE CORNER FOLLOWS FROM THE SCALE-FREE RESIDUAL.**  Everything
between the residual and the target is the certificate identity. -/
theorem k2ChartTargetPositivityXHalf_of_crossCert
    (h : K2ChartCrossCertPositivity) :
    ∀ ed ee P td te ty tz X : ℝ,
      0 < ty → 0 < tz → 0 < td → 0 < te → 0 < P →
      0 ≤ X → X ≤ 1/2 → (-1 : ℝ) < ed → (-1 : ℝ) < ee →
      td*ed + te*ee = ty + tz →
      td + te + ty + tz < 1 →
      0 < X*tz + (1-X)*ty - ty*tz →
      0 < te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)) →
      0 ≤ k2ChartQuotient ed ee P td te tz X →
      0 < k2ChartTarget ed ee P td te ty tz X := by
  intro ed ee P td te ty tz X hty htz htd hte hP hX hX2 hed hee hE hbudget hVn
    hWom hQ1
  have hT : 0 < td*ed + te*ee := by rw [hE]; linarith
  obtain ⟨hOm, hcert⟩ := h ed ee td te ty tz X hty htz htd hte hX hX2 hed hee
    hbudget hT hE
  have hG : 0 < td*(1+ed) + te*(1+ee) := by nlinarith
  have hc : 0 < td*(td*(1+ed) + te*(1+ee)) := mul_pos htd hG
  have hslope := k2ChartQuotientSlope_neg_of_womBoundary hP hc hWom hQ1 hOm
  have hty1 : ty < 1 := by linarith
  have htz1 : tz < 1 := by linarith
  have hp1 : 0 < ty + tz := by linarith
  have hp2 : 0 < (1-ty)*(1-tz) := mul_pos (by linarith) (by linarith)
  have hp3 : 0 < ty + tz + 1 := by linarith
  have hbase : 0 ≤ (ty + tz)*((1-ty)*(1-tz))
      + (ty + tz + 1)*(X*tz + (1-X)*ty - ty*tz) := by
    nlinarith [mul_pos hp1 hp2, mul_pos hp3 hVn]
  exact k2ChartTarget_pos_of_crossCert hE hslope hcert htd hG hbase hQ1

end Gtz
