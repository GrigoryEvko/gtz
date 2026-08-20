/-
# The cap-sum collapse of the `(5,3)` two-zero corner

The double-quotient corner carries four slack floors, two quotient floors,
and four strict chart positives.  This module removes the two excess caps
from the fight, exactly.

THE CAP-SUM LAW (`Gtz.k2Chart_capSum_identity`): with the target

  `TGT := (td·ed + te·ee)·DnC − td·P·G·Vn` ,

the two excess caps satisfy the polynomial identity

  `td·CapD + CapE = −TGT`

IDENTICALLY — with the plane weight `ty` free, not only on the excess
surface.  At the corner both caps are nonnegative and `td > 0`, so the
target is nonpositive (`Gtz.k2Chart_caps_force_target_nonpos`).  The corner
therefore dies the moment the REMAINING hypotheses force `TGT > 0`: the
named statement `Gtz.K2ChartTargetPositivityHalf`, which carries the domain,
the four strict chart positives, the two mixed refusals, the two quotient
floors — and the half-chart normalization `tz ≤ ty`, legitimate because the
whole system is mirror-symmetric: the four chart positives and the target
are invariant under the plane swap `ty ↔ tz`, `X ↔ 1 − X`
(`Gtz.k2ChartTarget_swap`), the caps are invariant, the mixed refusals
interchange, and the two quotient floors interchange.

`Gtz.k2ChartDoubleQuotientCorner_of_targetPositivityHalf` discharges the
corner from the half-chart positivity, and
`Gtz.k2Chart_kill_of_targetPositivityHalf` chains through the landed
conditional kill: the four refusal floors of a `(5,3)` two-zero chart tie
are impossible once the half-chart target positivity lands.  [MEASURED:
`TGT > 0` on all 20881 corner samples with multiplicative margin ≥ 17
percent, `scratchpad/corank1/f26sym/step26.py`.]
-/
import Gtz.Wave.KTwoChartIdentity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

/-! ## 1. The target -/

/-- The corner target: the excess total times the cleared gap determinant,
minus the erased cross mass times the cleared plane form.  At the corner
`td·ed + te·ee = ty + tz`, so the target reads `T·DnC − td·P·G·Vn` there. -/
def k2ChartTarget (ed ee P td te ty tz X : ℝ) : ℝ :=
  (td*ed + te*ee) * (te*(1+ee)*((1-ty)*(1-tz))
      - P*td*(td*(1+ed) + te*(1+ee))*((1-X)*(1-tz) + X*(1-ty)))
    - td*P*(td*(1+ed) + te*(1+ee)) * (X*tz + (1-X)*ty - ty*tz)

/-! ## 2. The cap-sum law -/

/-- **THE CAP-SUM LAW.**  The two excess caps of the chart total exactly the
negative of the target: `td·CapD + CapE = −TGT`, identically in all eight
chart scalars.  One `ring`. -/
theorem k2Chart_capSum_identity (ed ee P td te ty tz X : ℝ) :
    td * k2ChartCapD ed ee P td te ty tz X
      + k2ChartCapE ed ee P td te ty tz X
      = - k2ChartTarget ed ee P td te ty tz X := by
  unfold k2ChartCapD k2ChartCapE k2ChartTarget
  ring

/-- **THE CAPS FORCE THE TARGET DOWN.**  At any point with `td > 0` and both
excess caps nonnegative, the target is nonpositive. -/
theorem k2Chart_caps_force_target_nonpos {ed ee P td te ty tz X : ℝ}
    (htd : 0 < td)
    (hS1 : 0 ≤ k2ChartCapD ed ee P td te ty tz X)
    (hS2 : 0 ≤ k2ChartCapE ed ee P td te ty tz X) :
    k2ChartTarget ed ee P td te ty tz X ≤ 0 := by
  have hid := k2Chart_capSum_identity ed ee P td te ty tz X
  nlinarith [mul_nonneg htd.le hS1]

/-! ## 3. The mirror invariance of the target -/

/-- The target is invariant under the plane swap `ty ↔ tz`, `X ↔ 1 − X`. -/
theorem k2ChartTarget_swap (ed ee P td te ty tz X : ℝ) :
    k2ChartTarget ed ee P td te tz ty (1-X)
      = k2ChartTarget ed ee P td te ty tz X := by
  unfold k2ChartTarget
  ring

/-! ## 4. The half-chart positivity statement -/

/-- **THE HALF-CHART TARGET POSITIVITY.**  The residual of the `(5,3)`
two-zero chart after the cap-sum collapse: on the structured legal domain
with the half-chart normalization `tz ≤ ty`, the four strict chart
positives, the two mixed refusals and the two quotient floors force the
target strictly positive.  [MEASURED true at every corner sample with
multiplicative margin ≥ 17 percent.]  The two excess caps are GONE: the
cap-sum law converts this statement into the emptiness of the whole
corner. -/
def K2ChartTargetPositivityHalf : Prop :=
  ∀ ed ee P td te ty tz X : ℝ,
    0 < ty → 0 < tz → 0 < td → 0 < te → 0 < P →
    0 ≤ X → X ≤ 1 → (-1 : ℝ) < ed → (-1 : ℝ) < ee →
    td*ed + te*ee = ty + tz →
    td + te + ty + tz < 1 →
    tz ≤ ty →
    0 < X*tz + (1-X)*ty - ty*tz →
    0 < (te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))*((1-X)*tz + X*ty)
        - te*(1+ee)*ty*tz →
    0 < te*(1+ee)*((1-ty)*(1-tz))
        - P*td*(td*(1+ed) + te*(1+ee))*((1-X)*(1-tz) + X*(1-ty)) →
    0 < te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)) →
    0 ≤ k2ChartRefusalY ed ee P td te ty tz X →
    0 ≤ k2ChartRefusalZ ed ee P td te ty tz X →
    0 ≤ k2ChartQuotient ed ee P td te tz X →
    0 ≤ k2ChartQuotient ed ee P td te ty (1-X) →
    0 < k2ChartTarget ed ee P td te ty tz X

/-! ## 5. The corner discharge -/

/-- **THE CORNER DIES ON THE HALF-CHART POSITIVITY.**  Given the half-chart
target positivity, the double-quotient corner is empty: on the half chart
the positivity meets the cap-sum bound head on, and the mirror half
transports through the plane swap — the caps are invariant, the mixed
refusals interchange, the quotient floors interchange, and the target is
invariant. -/
theorem k2ChartDoubleQuotientCorner_of_targetPositivityHalf
    (hpos : K2ChartTargetPositivityHalf) : K2ChartDoubleQuotientCorner := by
  intro ed ee P td te ty tz X hty htz htd hte hP hX0 hX1 hed hee hE hsum
    hV hU hD hW hS1 hS2 hS3 hS4 hQ1 hQ1m
  have hcap := k2Chart_caps_force_target_nonpos htd hS1 hS2
  rcases le_or_gt tz ty with hyz | hyz
  · exact absurd (hpos ed ee P td te ty tz X hty htz htd hte hP hX0 hX1
      hed hee hE hsum hyz hV hU hD hW hS3 hS4 hQ1 hQ1m) (not_lt.mpr hcap)
  · -- the mirror half: apply the positivity at the swapped point
    have hX0' : (0:ℝ) ≤ 1 - X := by linarith
    have hX1' : 1 - X ≤ 1 := by linarith
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
    have hQ1m' : 0 ≤ k2ChartQuotient ed ee P td te tz (1-(1-X)) := by
      have h : (1:ℝ) - (1-X) = X := by ring
      rw [h]; exact hQ1
    have htgt := hpos ed ee P td te tz ty (1-X) htz hty htd hte hP hX0' hX1'
      hed hee hE' hsum' hyz.le hV' hU' hD' hW hS3' hS4' hQ1m hQ1m'
    rw [k2ChartTarget_swap] at htgt
    exact absurd htgt (not_lt.mpr hcap)

/-- **THE CHART KILL FROM THE HALF-CHART POSITIVITY.**  Chaining through the
landed conditional kill: once the half-chart target positivity lands, the
four refusal floors of a `(5,3)` two-zero chart tie are impossible. -/
theorem k2Chart_kill_of_targetPositivityHalf
    (hpos : K2ChartTargetPositivityHalf)
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
    (k2ChartDoubleQuotientCorner_of_targetPositivityHalf hpos)
    hty htz htd hte hP hX0 hX1 hed hee hE hsum hV hU hD hW hS1 hS2 hS3 hS4

end Gtz
