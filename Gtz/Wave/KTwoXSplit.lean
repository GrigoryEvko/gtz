/-
# The plane-angle split of the two-zero corner

The corner of `Gtz.KTwoCapSum` carries BOTH quotient floors, `Q1 ≥ 0` and its
mirror.  Measurement says they are never both needed: the plane angle `X`
decides which one does the work.

  On `X ≤ 1/2` the single floor `Q1 ≥ 0` forces the target positive —
  0 failures in 1212080 sampled feasible points.
  On `X ≥ 1/2` the mirror floor alone does it — 0 failures in 1220717.
  The cross assignments fail (11007 and 5845), so the split is exact and not
  an artifact of the sampling.

[`scratchpad/corank1/f26sym/f28split.jl`.]

This module carries that structure into the kernel.  The swap
`ty ↔ tz`, `X ↔ 1 − X` sends `X ≤ 1/2` to `X ≥ 1/2` and exchanges the two
quotients, while fixing the target (`Gtz.k2ChartTarget_swap`) and the caps.
So ONE branch proves both: `Gtz.K2ChartTargetPositivityXHalf` asks for the
target positivity on the low-angle half with the single floor `Q1 ≥ 0`, and
`Gtz.k2ChartDoubleQuotientCorner_of_xHalf` discharges the whole corner from it.

Against `Gtz.K2ChartTargetPositivityHalf` this trades a degree-eight generator
for a degree-one one: the residual now carries ONE quotient and the marker
`1/2 − X`, in place of two quotients and the weight comparison `tz ≤ ty`.
-/
import Gtz.Wave.KTwoCapSum

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

/-! ## 1. The low-angle residual -/

/-- **THE LOW-ANGLE TARGET POSITIVITY.**  On the structured legal domain with
the plane angle at most one half, the four strict chart positives, the two
mixed refusals and the SINGLE quotient floor `Q1 ≥ 0` force the target
positive.  [MEASURED: 0 failures in 1212080 feasible points; the mirror floor
alone fails 11007 times on the same half, so the assignment of floor to half is
exact.] -/
def K2ChartTargetPositivityXHalf : Prop :=
  ∀ ed ee P td te ty tz X : ℝ,
    0 < ty → 0 < tz → 0 < td → 0 < te → 0 < P →
    0 ≤ X → X ≤ 1 → (-1 : ℝ) < ed → (-1 : ℝ) < ee →
    td*ed + te*ee = ty + tz →
    td + te + ty + tz < 1 →
    X ≤ 1/2 →
    0 < X*tz + (1-X)*ty - ty*tz →
    0 < (te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))*((1-X)*tz + X*ty)
        - te*(1+ee)*ty*tz →
    0 < te*(1+ee)*((1-ty)*(1-tz))
        - P*td*(td*(1+ed) + te*(1+ee))*((1-X)*(1-tz) + X*(1-ty)) →
    0 < te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)) →
    0 ≤ k2ChartRefusalY ed ee P td te ty tz X →
    0 ≤ k2ChartRefusalZ ed ee P td te ty tz X →
    0 ≤ k2ChartQuotient ed ee P td te tz X →
    0 < k2ChartTarget ed ee P td te ty tz X

/-! ## 2. The corner discharge -/

/-- **THE CORNER DIES ON THE LOW-ANGLE HALF ALONE.**  The swap sends the high
half to the low half, exchanging the two quotient floors and the two mixed
refusals while fixing the target and both caps, so one branch settles the
corner. -/
theorem k2ChartDoubleQuotientCorner_of_xHalf
    (hpos : K2ChartTargetPositivityXHalf) : K2ChartDoubleQuotientCorner := by
  intro ed ee P td te ty tz X hty htz htd hte hP hX0 hX1 hed hee hE hsum
    hV hU hD hW hS1 hS2 hS3 hS4 hQ1 hQ1m
  have hcap := k2Chart_caps_force_target_nonpos htd hS1 hS2
  rcases le_or_gt X (1/2) with hx | hx
  · exact absurd (hpos ed ee P td te ty tz X hty htz htd hte hP hX0 hX1
      hed hee hE hsum hx hV hU hD hW hS3 hS4 hQ1) (not_lt.mpr hcap)
  · -- the mirror half, through the plane swap
    have hX0' : (0:ℝ) ≤ 1 - X := by linarith
    have hX1' : 1 - X ≤ 1 := by linarith
    have hxhalf : 1 - X ≤ 1/2 := by linarith
    have hE' : td*ed + te*ee = tz + ty := by linarith
    have hsum' : td + te + tz + ty < 1 := by linarith
    have hV' : 0 < (1-X)*ty + (1-(1-X))*tz - tz*ty := by
      have h : (1-X)*ty + (1-(1-X))*tz - tz*ty
          = X*tz + (1-X)*ty - ty*tz := by ring
      rw [h]; exact hV
    have hU' : 0 < (te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))
        *((1-(1-X))*ty + (1-X)*tz) - te*(1+ee)*tz*ty := by
      have h : (te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))
            *((1-(1-X))*ty + (1-X)*tz) - te*(1+ee)*tz*ty
          = (te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))*((1-X)*tz + X*ty)
            - te*(1+ee)*ty*tz := by ring
      rw [h]; exact hU
    have hD' : 0 < te*(1+ee)*((1-tz)*(1-ty))
        - P*td*(td*(1+ed) + te*(1+ee))*((1-(1-X))*(1-ty) + (1-X)*(1-tz)) := by
      have h : te*(1+ee)*((1-tz)*(1-ty))
            - P*td*(td*(1+ed) + te*(1+ee))*((1-(1-X))*(1-ty) + (1-X)*(1-tz))
          = te*(1+ee)*((1-ty)*(1-tz))
            - P*td*(td*(1+ed) + te*(1+ee))*((1-X)*(1-tz) + X*(1-ty)) := by ring
      rw [h]; exact hD
    have hS3' : 0 ≤ k2ChartRefusalY ed ee P td te tz ty (1-X) := by
      rw [k2ChartRefusalY_swap]; exact hS4
    have hS4' : 0 ≤ k2ChartRefusalZ ed ee P td te tz ty (1-X) := by
      rw [k2ChartRefusalZ_swap]; exact hS3
    have htgt := hpos ed ee P td te tz ty (1-X) htz hty htd hte hP hX0' hX1'
      hed hee hE' hsum' hxhalf hV' hU' hD' hW hS3' hS4' hQ1m
    rw [k2ChartTarget_swap] at htgt
    exact absurd htgt (not_lt.mpr hcap)

/-- **THE CHART KILL FROM THE LOW-ANGLE HALF.**  Chaining through the landed
conditional kill: once the low-angle target positivity lands, the four refusal
floors of a `(5,3)` two-zero chart tie are impossible. -/
theorem k2Chart_kill_of_xHalf (hpos : K2ChartTargetPositivityXHalf)
    {ed ee P td te ty tz X : ℝ}
    (hty : 0 < ty) (htz : 0 < tz) (htd : 0 < td) (hte : 0 < te) (hP : 0 < P)
    (hX0 : 0 ≤ X) (hX1 : X ≤ 1) (hed : (-1 : ℝ) < ed) (hee : (-1 : ℝ) < ee)
    (hE : td*ed + te*ee = ty + tz)
    (hsum : td + te + ty + tz < 1)
    (hV : 0 < X*tz + (1-X)*ty - ty*tz)
    (hU : 0 < (te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))*((1-X)*tz + X*ty)
        - te*(1+ee)*ty*tz)
    (hD : 0 < te*(1+ee)*((1-ty)*(1-tz))
        - P*td*(td*(1+ed) + te*(1+ee))*((1-X)*(1-tz) + X*(1-ty)))
    (hW : 0 < te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))
    (hS1 : 0 ≤ k2ChartCapD ed ee P td te ty tz X)
    (hS2 : 0 ≤ k2ChartCapE ed ee P td te ty tz X)
    (hS3 : 0 ≤ k2ChartRefusalY ed ee P td te ty tz X)
    (hS4 : 0 ≤ k2ChartRefusalZ ed ee P td te ty tz X) : False :=
  k2Chart_kill_of_doubleQuotientCorner
    (k2ChartDoubleQuotientCorner_of_xHalf hpos)
    hty htz htd hte hP hX0 hX1 hed hee hE hsum hV hU hD hW hS1 hS2 hS3 hS4

end Gtz
