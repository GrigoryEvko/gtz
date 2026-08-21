/-
# The three remaining chart slacks are their refusal determinants

`Gtz.k2ChartRefusalY_eq_gapDet` identified one of the four chart slacks with
the gap determinant of its triple.  This module does the other three, by the
same recipe and with the same two design inputs — the collinearity and the
plane rank relation `Gtz.k2Plane_star_eq_zero`.

Unlike the mixed refusal that keeps `y`, these three carry the second plane
atom, so their difference from the determinant depends on the plane pair's
second coordinate pair.  That dependence is only through `z₁²`, `z₁z₂` and
`z₂²`, so multiplying by the plane weight and substituting the three plane
readings of Parseval clears it in one step.  The residue is the rank relation
times a chart quotient, exactly as before:

  `CapD : ed·(1+ty−tz)`,  `CapE : t_e·ee·(1+ty−tz)`,  `RefusalZ : t_e·(1+ed+ee)` .

With the four identities of this module and its sibling, every chart slack is
nonnegative exactly when its triple is refused, so the chart kill transports to
the design as soon as the frame is constructed.

[The cofactors were generated exactly, `scratchpad/f51/gen3.json`.]
-/
import Gtz.Wave.KTwoBridgeRefusalY

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

namespace Gtz

/-- **THE SLACK `CapD` IS ITS REFUSAL DETERMINANT.**  the excess cap of the first outside atom, the refusal of `{y,z,d}`,
times a strictly positive clearing factor. -/
theorem k2ChartCapD_eq_gapDet (y1 y2 z1 z2 al be p v ty tz td te : ℝ)
    (htz : tz ≠ 0)
    (h1 : ty*y1^2 + tz*z1^2 + td*p^2 + te*v^2 = 1)
    (h2 : ty*(y1*y2) + tz*(z1*z2) = 0)
    (h3 : ty*y2^2 + tz*z2^2 = 1)
    (hcol : td*al*p + te*be*v = 0) :
    k2ChartCapD (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2)
      = -(ty*tz*te*be^2) *
        (al^2*y1^2*z2^2 - al^2*y1^2 - 2*al^2*y1*y2*z1*z2 + al^2*y2^2*z1^2
         - al^2*y2^2 - al^2*z1^2 - al^2*z2^2 + al^2 - p^2*y2^2 - p^2*z2^2
         + p^2 - y1^2*z2^2 + y1^2 + 2*y1*y2*z1*z2 - y2^2*z1^2 + y2^2 +
         z1^2 + z2^2 - 1) := by
  have hstar := k2Plane_star_eq_zero y1 y2 z1 z2 ty tz td te p v h1 h2 h3
  have key : tz * (k2ChartCapD (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2)
      + (ty*tz*te*be^2) *
        (al^2*y1^2*z2^2 - al^2*y1^2 - 2*al^2*y1*y2*z1*z2 + al^2*y2^2*z1^2
         - al^2*y2^2 - al^2*z1^2 - al^2*z2^2 + al^2 - p^2*y2^2 - p^2*z2^2
         + p^2 - y1^2*z2^2 + y1^2 + 2*y1*y2*z1*z2 - y2^2*z1^2 + y2^2 +
         z1^2 + z2^2 - 1)) = 0 := by
    unfold k2ChartCapD
    linear_combination
      (al^2*be^2*te*ty*tz*y2^2 - al^2*be^2*te*ty*tz - be^2*te*ty*tz*y2^2 +
       be^2*te*ty*tz) * h1
      + (-2*al^2*be^2*te*ty*tz*y1*y2 + 2*be^2*te*ty*tz*y1*y2) * h2
      + (al^2*be^2*te*ty*tz*y1^2 - al^2*be^2*te*ty*tz - be^2*p^2*te*ty*tz
         - be^2*te*ty*tz*y1^2 + be^2*te*ty*tz) * h3
      + (al^2*be^2*te*ty*tz - al^2*be^2*te*tz^2 + al^2*be^2*te*tz -
         be^2*te*ty*tz + be^2*te*tz^2 - be^2*te*tz) * hstar
      + (-al^3*p*td*ty^2*tz*y2^2 + al^3*p*td*ty*tz^2*y2^2 - al^3*p*td*tz^2
         + al^3*p*td*tz + al^2*be*te*ty^2*tz*v*y2^2 -
         al^2*be*te*ty*tz^2*v*y2^2 + al^2*be*te*tz^2*v - al^2*be*te*tz*v +
         al*p*td*ty^2*tz*y2^2 - al*p*td*ty*tz^2*y2^2 + al*p*td*tz^2 -
         al*p*td*tz - be*te*ty^2*tz*v*y2^2 + be*te*ty*tz^2*v*y2^2 -
         be*te*tz^2*v + be*te*tz*v) * hcol
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h htz
  · linarith [h]

/-- **THE SLACK `CapE` IS ITS REFUSAL DETERMINANT.**  the excess cap of the second outside atom, the refusal of `{y,z,e}`,
times a strictly positive clearing factor. -/
theorem k2ChartCapE_eq_gapDet (y1 y2 z1 z2 al be p v ty tz td te : ℝ)
    (htz : tz ≠ 0)
    (h1 : ty*y1^2 + tz*z1^2 + td*p^2 + te*v^2 = 1)
    (h2 : ty*(y1*y2) + tz*(z1*z2) = 0)
    (h3 : ty*y2^2 + tz*z2^2 = 1)
    (hcol : td*al*p + te*be*v = 0) :
    k2ChartCapE (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2)
      = -(ty*tz*te^2*be^2) *
        (be^2*y1^2*z2^2 - be^2*y1^2 - 2*be^2*y1*y2*z1*z2 + be^2*y2^2*z1^2
         - be^2*y2^2 - be^2*z1^2 - be^2*z2^2 + be^2 - v^2*y2^2 - v^2*z2^2
         + v^2 - y1^2*z2^2 + y1^2 + 2*y1*y2*z1*z2 - y2^2*z1^2 + y2^2 +
         z1^2 + z2^2 - 1) := by
  have hstar := k2Plane_star_eq_zero y1 y2 z1 z2 ty tz td te p v h1 h2 h3
  have key : tz * (k2ChartCapE (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2)
      + (ty*tz*te^2*be^2) *
        (be^2*y1^2*z2^2 - be^2*y1^2 - 2*be^2*y1*y2*z1*z2 + be^2*y2^2*z1^2
         - be^2*y2^2 - be^2*z1^2 - be^2*z2^2 + be^2 - v^2*y2^2 - v^2*z2^2
         + v^2 - y1^2*z2^2 + y1^2 + 2*y1*y2*z1*z2 - y2^2*z1^2 + y2^2 +
         z1^2 + z2^2 - 1)) = 0 := by
    unfold k2ChartCapE
    linear_combination
      (be^4*te^2*ty*tz*y2^2 - be^4*te^2*ty*tz - be^2*te^2*ty*tz*y2^2 +
       be^2*te^2*ty*tz) * h1
      + (-2*be^4*te^2*ty*tz*y1*y2 + 2*be^2*te^2*ty*tz*y1*y2) * h2
      + (be^4*te^2*ty*tz*y1^2 - be^4*te^2*ty*tz - be^2*te^2*ty*tz*v^2 -
         be^2*te^2*ty*tz*y1^2 + be^2*te^2*ty*tz) * h3
      + (be^4*te^2*ty*tz - be^4*te^2*tz^2 + be^4*te^2*tz - be^2*te^2*ty*tz
         + be^2*te^2*tz^2 - be^2*te^2*tz) * hstar
      + (-al*be^2*p*td*te*ty^2*tz*y2^2 + al*be^2*p*td*te*ty*tz^2*y2^2 -
         al*be^2*p*td*te*tz^2 + al*be^2*p*td*te*tz +
         al*p*td*te*ty^2*tz*y2^2 - al*p*td*te*ty*tz^2*y2^2 +
         al*p*td*te*tz^2 - al*p*td*te*tz - al*p*td*ty^2*tz*y2^2 +
         al*p*td*ty*tz^2*y2^2 - al*p*td*ty*tz^2 + al*p*td*ty*tz +
         be^3*te^2*ty^2*tz*v*y2^2 - be^3*te^2*ty*tz^2*v*y2^2 +
         be^3*te^2*tz^2*v - be^3*te^2*tz*v - be*te^2*ty^2*tz*v*y2^2 +
         be*te^2*ty*tz^2*v*y2^2 - be*te^2*tz^2*v + be*te^2*tz*v +
         be*te*ty^2*tz*v*y2^2 - be*te*ty*tz^2*v*y2^2 + be*te*ty*tz^2*v -
         be*te*ty*tz*v) * hcol
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h htz
  · linarith [h]

/-- **THE SLACK `RefusalZ` IS ITS REFUSAL DETERMINANT.**  the mixed refusal that keeps the plane atom `z`,
times a strictly positive clearing factor. -/
theorem k2ChartRefusalZ_eq_gapDet (y1 y2 z1 z2 al be p v ty tz td te : ℝ)
    (htz : tz ≠ 0)
    (h1 : ty*y1^2 + tz*z1^2 + td*p^2 + te*v^2 = 1)
    (h2 : ty*(y1*y2) + tz*(z1*z2) = 0)
    (h3 : ty*y2^2 + tz*z2^2 = 1)
    (hcol : td*al*p + te*be*v = 0) :
    k2ChartRefusalZ (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2)
      = -(tz*te^2*be^2) *
        (al^2*v^2*z2^2 - al^2*v^2 - al^2*z1^2 - al^2*z2^2 + al^2 -
         2*al*be*p*v*z2^2 + 2*al*be*p*v + be^2*p^2*z2^2 - be^2*p^2 -
         be^2*z1^2 - be^2*z2^2 + be^2 - p^2*z2^2 + p^2 - v^2*z2^2 + v^2 +
         z1^2 + z2^2 - 1) := by
  have hstar := k2Plane_star_eq_zero y1 y2 z1 z2 ty tz td te p v h1 h2 h3
  have key : tz * (k2ChartRefusalZ (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2)
      + (tz*te^2*be^2) *
        (al^2*v^2*z2^2 - al^2*v^2 - al^2*z1^2 - al^2*z2^2 + al^2 -
         2*al*be*p*v*z2^2 + 2*al*be*p*v + be^2*p^2*z2^2 - be^2*p^2 -
         be^2*z1^2 - be^2*z2^2 + be^2 - p^2*z2^2 + p^2 - v^2*z2^2 + v^2 +
         z1^2 + z2^2 - 1)) = 0 := by
    unfold k2ChartRefusalZ
    linear_combination
      (-al^2*be^2*te^2*tz - be^4*te^2*tz + be^2*te^2*tz) * h1
      + (0) * h2
      + (al^2*be^2*te^2*tz*v^2 - al^2*be^2*te^2*tz - 2*al*be^3*p*te^2*tz*v
         + be^4*p^2*te^2*tz - be^4*te^2*tz - be^2*p^2*te^2*tz -
         be^2*te^2*tz*v^2 + be^2*te^2*tz) * h3
      + (al^2*be^2*te^2*tz + be^4*te^2*tz - be^2*te^2*tz) * hstar
      + (-al^3*p*td*te*ty*tz*y2^2 + al^3*p*td*ty*tz*y2^2 + al^3*p*td*tz^2
         - al^3*p*td*tz + al^2*be*te^2*ty*tz*v*y2^2 -
         al^2*be*te*ty*tz*v*y2^2 - al^2*be*te*tz^2*v + al^2*be*te*tz*v -
         al*be^2*p*td*te*ty*tz*y2^2 + 2*al*be^2*p*te*ty*tz*y2^2 +
         2*al*be^2*p*te*tz^2 - 2*al*be^2*p*te*tz + al*p*td*te*ty*tz*y2^2 -
         al*p*td*ty*tz*y2^2 - al*p*td*tz^2 + al*p*td*tz +
         be^3*te^2*ty*tz*v*y2^2 - be*te^2*ty*tz*v*y2^2 +
         be*te*ty*tz*v*y2^2 + be*te*tz^2*v - be*te*tz*v) * hcol
  rcases mul_eq_zero.mp key with h | h
  · exact absurd h htz
  · linarith [h]

end Gtz
