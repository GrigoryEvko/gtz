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
of `P`: `α < 0` and `CERT > 0`.  [MEASURED on the low-angle half that the landed
`Gtz.K2ChartTargetPositivityXHalf` reduces the whole corner to: `CERT > 0` at
100.0000% of 272541 feasible corner points, and `CERT > 0` implies `α < 0` at
every one of 461751 points where it holds.  `f44test.jl`.]

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

/-! ## 7. The residual -/

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
    k2ChartQuotientSlope ed ee td te tz X < 0
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
      0 ≤ k2ChartQuotient ed ee P td te tz X →
      0 < k2ChartTarget ed ee P td te ty tz X := by
  intro ed ee P td te ty tz X hty htz htd hte _hP hX hX2 hed hee hE hbudget hVn hQ1
  have hT : 0 < td*ed + te*ee := by rw [hE]; linarith
  obtain ⟨hslope, hcert⟩ := h ed ee td te ty tz X hty htz htd hte hX hX2 hed hee
    hbudget hT hE
  have hG : 0 < td*(1+ed) + te*(1+ee) := by nlinarith
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
