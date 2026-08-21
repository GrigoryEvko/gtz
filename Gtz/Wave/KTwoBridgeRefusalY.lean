/-
# The chart slack IS the refusal determinant

`Gtz.k2Chart_kill` empties the `(5,3)` two-zero chart by showing its four
POLYNOMIAL slacks cannot all be nonnegative.  For that to kill a design, each
slack must BE the corresponding refusal, and this module proves it for the
mixed refusal that keeps the plane atom `y`.

## The frame

`Gtz.k2FiveAxis_collinear` puts the two outside plane parts on one line, so a
two-zero configuration admits coordinates in which

  `g_x = (0,0,1)`,  `g_y = (y₁,y₂,0)`,  `g_z = (z₁,z₂,0)`,
  `g_d = (p,0,α)`,  `g_e = (v,0,β)` ,

the axis last, the shared outside line first.  In these coordinates the chart
reads off directly: the outside excesses are `ed = α²−1` and `ee = β²−1`, the
erased scale is `P = p²` — the squared plane part of `d` — and the plane angle
is `X = t_y·y₂²`, the `y`-share of the transverse probe.

## The two relations

Only two facts about the design are used, and both are Parseval:

* **the collinearity** `t_d·α·p + t_e·β·v = 0` (`Gtz.k2FiveAxis_collinear`
  read at the shared line);
* **the plane rank relation** `Gtz.k2Plane_star_eq_zero`, which is the
  elimination of the `z` coordinates from the three plane readings of Parseval.
  It says the plane pair really does resolve what the outside leaves,

    `(t_y·y₁y₂)² = (1 − t_d p² − t_e v² − t_y y₁²)·(1 − t_y y₂²)` ,

  and it is proved by rewriting each side as a `z`-expression: the left is
  `(t_z·z₁z₂)²` and the right is `(t_z z₁²)·(t_z z₂²)`.

## The identity

`Gtz.k2ChartRefusalY_eq_gapDet` then states, as one `linear_combination`,

  **`k2ChartRefusalY … = − t_y·t_e²·β² · det(S_{y,d,e} − 1)`** ,

with the clearing factor a product of weights and `1+ee`, so it is strictly
positive on the chart domain.  Hence the slack is nonnegative EXACTLY when the
triple `{y,d,e}` is refused (`Gtz.k2ChartRefusalY_nonneg_iff_gapDet_nonpos`).

The cofactor of the rank relation is `−t_e²β²(1+ed+ee)`, and `1+ed+ee` is the
chart's excess sum, positive by the landed `Gtz.k2Chart_excessSum_pos`.

[MEASURED first, `scratchpad/f51/`: the chart map was recovered from designs
before any algebra — `X` reproduced the construction's own rotation parameter
to `1e-16` over six trials and `P` to `3e-15` over fourteen, and all four
slack-to-determinant ratios were exact positive monomials over 200 designs at
`1e-13`.  The other three identities lie in the same ideal (Groebner, exact);
only this one is transcribed here.]
-/
import Gtz.Wave.KTwoBridgeNormalForm
import Gtz.Wave.KTwoChartIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

/-! ## 1. The plane rank relation -/

/-- **THE PLANE RANK RELATION.**  Eliminating the plane pair's coordinates from
the three plane readings of Parseval leaves one relation among the remaining
data.  It is the statement that the plane pair resolves exactly what the
outside line leaves behind. -/
theorem k2Plane_star_eq_zero (y1 y2 z1 z2 ty tz td te p v : ℝ)
    (h1 : ty*y1^2 + tz*z1^2 + td*p^2 + te*v^2 = 1)
    (h2 : ty*(y1*y2) + tz*(z1*z2) = 0)
    (h3 : ty*y2^2 + tz*z2^2 = 1) :
    (ty*(y1*y2))^2 - (1 - td*p^2 - te*v^2 - ty*y1^2)*(1 - ty*y2^2) = 0 := by
  have a1 : (1:ℝ) - td*p^2 - te*v^2 - ty*y1^2 = tz*z1^2 := by linarith
  have a3 : (1:ℝ) - ty*y2^2 = tz*z2^2 := by linarith
  have a2 : ty*(y1*y2) = -(tz*(z1*z2)) := by linarith
  rw [a1, a3, a2]
  ring

/-! ## 2. The slack is the determinant -/

/-- **THE MIXED REFUSAL SLACK IS THE REFUSAL DETERMINANT.**  In the two-zero
frame the chart slack `k2ChartRefusalY` equals the gap determinant of the
triple `{y,d,e}` times a strictly positive clearing factor, up to sign.

Only the collinearity and the plane rank relation are used. -/
theorem k2ChartRefusalY_eq_gapDet (y1 y2 al be p v ty tz td te : ℝ)
    (hcol : td*al*p + te*be*v = 0)
    (hstar : (ty*(y1*y2))^2
        - (1 - td*p^2 - te*v^2 - ty*y1^2)*(1 - ty*y2^2) = 0) :
    k2ChartRefusalY (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2)
      = -(ty*te^2*be^2) *
        (al^2*v^2*y2^2 - al^2*v^2 - al^2*y1^2 - al^2*y2^2 + al^2
          - 2*al*be*p*v*y2^2 + 2*al*be*p*v + be^2*p^2*y2^2 - be^2*p^2
          - be^2*y1^2 - be^2*y2^2 + be^2 - p^2*y2^2 + p^2 - v^2*y2^2 + v^2
          + y1^2 + y2^2 - 1) := by
  unfold k2ChartRefusalY
  linear_combination
    (-al^2*be^2*te^2 - be^4*te^2 + be^2*te^2) * hstar
    + (al^3*p*td*te*ty*y2^2 - al^3*p*td*te - al^3*p*td*ty*y2^2 + al^3*p*td*ty
        - al^2*be*te^2*ty*v*y2^2 + al^2*be*te^2*v + al^2*be*te*ty*v*y2^2
        - al^2*be*te*ty*v + al*be^2*p*td*te*ty*y2^2 - al*be^2*p*td*te
        - 2*al*be^2*p*te*ty*y2^2 + 2*al*be^2*p*te*ty - al*p*td*te*ty*y2^2
        + al*p*td*te + al*p*td*ty*y2^2 - al*p*td*ty - be^3*te^2*ty*v*y2^2
        + be^3*te^2*v + be*te^2*ty*v*y2^2 - be*te^2*v - be*te*ty*v*y2^2
        + be*te*ty*v) * hcol

/-! ## 3. The slack signs the refusal -/

/-- **THE SLACK IS NONNEGATIVE EXACTLY AT THE REFUSAL.**  The clearing factor is
a product of two weights and the second outside atom's squared axis reading, so
it is strictly positive whenever those are. -/
theorem k2ChartRefusalY_nonneg_iff_gapDet_nonpos
    (y1 y2 al be p v ty tz td te : ℝ)
    (hty : 0 < ty) (hte : 0 < te) (hbe : be ≠ 0)
    (hcol : td*al*p + te*be*v = 0)
    (hstar : (ty*(y1*y2))^2
        - (1 - td*p^2 - te*v^2 - ty*y1^2)*(1 - ty*y2^2) = 0) :
    0 ≤ k2ChartRefusalY (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2)
      ↔ (al^2*v^2*y2^2 - al^2*v^2 - al^2*y1^2 - al^2*y2^2 + al^2
          - 2*al*be*p*v*y2^2 + 2*al*be*p*v + be^2*p^2*y2^2 - be^2*p^2
          - be^2*y1^2 - be^2*y2^2 + be^2 - p^2*y2^2 + p^2 - v^2*y2^2 + v^2
          + y1^2 + y2^2 - 1) ≤ 0 := by
  have hpos : 0 < ty*te^2*be^2 := by positivity
  rw [k2ChartRefusalY_eq_gapDet y1 y2 al be p v ty tz td te hcol hstar]
  constructor
  · intro h; nlinarith [h, hpos]
  · intro h; nlinarith [h, hpos]

end Gtz
