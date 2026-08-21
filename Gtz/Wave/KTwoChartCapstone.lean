/-
# The two-zero chart corner, closed

The `(5,3)` two-zero corner of the corank-one arm had been reduced, over
fifteen modules, to two signs on a chart of five scalars: the cross
certificate positive at the half plane angle, and the quotient boundary reading
negative on the low-angle half.  Both signs were measured true at every sampled
point and neither was proved.  This module proves both, discharges every named
statement between them and the corner, and lands the chart kill with no
hypothesis beyond the chart domain.

## The residue was the wrong object

`Gtz.k2ChartCrossCert_half_split` writes twice the half-angle endpoint as
`q·(1 − tz)·(2·base + tz·R)`, with `q = te(1+ee)`, `base` a product of chart
positives, and `R = Gtz.k2ChartCrossHalfResidue`.  The residue `R` was believed
nonnegative on the domain.  It is not.  At the exact rational point
`ed = 65.868, ee = −0.8821, td = 0.0144, te = 0.2452, tz = 0.0140` every domain
hypothesis holds and `R = −0.0201`.  The point sits in the boundary layer
`1 − td − te − T ≈ 0.008`, which a descent of moderate depth never enters.  The
endpoint itself is positive there, at `0.0035`, because the base term
dominates.  The object to sign is the BRACKET `2·base + tz·R`.

## Both signs are sums of products of domain positives

Write `p = td(1+ed)` and `q = te(1+ee)` for the two plane masses.  In the
variables `(p, q, td, te, tz)` the domain is a polytope — every hypothesis is a
linear form — and both brackets have degree six.  Handelman's theorem then
promises certificates over products of the facet forms, and a linear program
over the products of degree at most six of the eight positives

  `p, q, td, te, tz,  ty = p + q − td − te − tz,  w = 1 − p − q,
   g = td·te·(1+ed+ee) = p·te + q·td − td·te`

(with `X` and `1/2 − X` adjoined for the boundary reading) returns EXACT
rational certificates for both:

* the cross bracket is a sum of twenty-eight products, every coefficient one or
  two (`Gtz.k2ChartCrossHalf_certificate`);
* the negated boundary reading is a sum of thirty-four products, every
  coefficient one half, one or two (`Gtz.k2ChartWomBoundary_certificate`).

Each identity is one `ring`, each sign is one `positivity`, and the excess
product is positive by the landed `Gtz.k2Chart_excessSum_pos`.

## The chain to the corner

The two signs are exactly `Gtz.K2ChartCrossCertPositivity`.  Through the landed
`Gtz.k2ChartTargetPositivityXHalf_of_crossCert` that statement gives
`Gtz.K2ChartTargetPositivityXHalf`; through the landed plane swap
`Gtz.k2ChartDoubleQuotientCorner_of_xHalf` it empties
`Gtz.K2ChartDoubleQuotientCorner`; and through the landed conditional kill the
four refusal floors of a `(5,3)` two-zero chart tie are impossible
(`Gtz.k2Chart_kill`).  The named half-chart statement
`Gtz.K2ChartTargetPositivityHalf` is not needed: the low-angle half with one
quotient floor settles the whole corner.

What remains for the design-level kill is outside this chart: the chart-to-
design bridge and the two boundary lemmas.

[MEASURED before proving: a thirty-two thread descent over the domain puts the
multiplicative margin `1 + tz·R/(2·base)` at no less than `0.9950` and the
negated boundary reading strictly positive at every point, with both minimisers
running to the polytope corner where one plane mass tends to one and its weight
to zero.]
-/
import Gtz.Wave.KTwoQuotientCertificate
import Gtz.Wave.KTwoXSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000
set_option maxRecDepth 16000

namespace Gtz

/-! ## 1. The cross bracket at the half angle -/

/-- **THE CROSS BRACKET IS A SUM OF TWENTY-EIGHT PRODUCTS.**  Stated with the
eight positives named, so the identity is readable and the sign is one
`positivity`. -/
theorem k2ChartCrossHalf_certificate (ed ee td te tz : ℝ)
    (P Q TY W G : ℝ)
    (hP : P = td*(1+ed)) (hQ : Q = te*(1+ee))
    (hTY : TY = P + Q - td - te - tz) (hW : W = 1 - P - Q)
    (hG : G = P*te + Q*td - td*te) :
    2 * (td*te*(td*ed + te*ee)*(td*(1+ed) + te*(1+ee))
          * (1 + ed + ee) * (1 - td - te - tz))
      + tz * k2ChartCrossHalfResidue ed ee td te tz
    = tz*tz*G + tz*TY*G + 2*TY*TY*G
      + 2*P*tz*tz*TY + 2*P*tz*W*G + 2*Q*tz*tz*TY + 2*Q*tz*W*G
      + 2*td*te*tz*TY + 2*td*TY*W*G + 2*te*TY*W*G + 2*tz*TY*W*G
      + 2*P*td*tz*TY*TY + 2*P*td*tz*TY*G + 2*P*te*tz*TY*G
      + 2*P*tz*tz*tz*W + 2*P*tz*TY*TY*W
      + 2*Q*td*tz*TY*G + 2*Q*te*tz*TY*TY + 2*Q*te*tz*TY*G
      + 2*Q*tz*tz*tz*W + 2*Q*tz*TY*TY*W
      + 2*td*te*tz*tz*W + tz*tz*W*W*G + tz*TY*W*W*G
      + 2*P*td*tz*tz*TY*W + 2*P*tz*tz*TY*W*W
      + 2*Q*te*tz*tz*TY*W + 2*Q*tz*tz*TY*W*W := by
  subst hP hQ hTY hW hG
  unfold k2ChartCrossHalfResidue
  ring

/-- The twenty-eight products are positive when their factors are. -/
theorem k2ChartCrossHalf_cert_pos {P Q td te tz TY W G : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (htd : 0 < td) (hte : 0 < te) (htz : 0 < tz)
    (hTY : 0 < TY) (hW : 0 < W) (hG : 0 < G) :
    0 < tz*tz*G + tz*TY*G + 2*TY*TY*G
      + 2*P*tz*tz*TY + 2*P*tz*W*G + 2*Q*tz*tz*TY + 2*Q*tz*W*G
      + 2*td*te*tz*TY + 2*td*TY*W*G + 2*te*TY*W*G + 2*tz*TY*W*G
      + 2*P*td*tz*TY*TY + 2*P*td*tz*TY*G + 2*P*te*tz*TY*G
      + 2*P*tz*tz*tz*W + 2*P*tz*TY*TY*W
      + 2*Q*td*tz*TY*G + 2*Q*te*tz*TY*TY + 2*Q*te*tz*TY*G
      + 2*Q*tz*tz*tz*W + 2*Q*tz*TY*TY*W
      + 2*td*te*tz*tz*W + tz*tz*W*W*G + tz*TY*W*W*G
      + 2*P*td*tz*tz*TY*W + 2*P*tz*tz*TY*W*W
      + 2*Q*te*tz*tz*TY*W + 2*Q*tz*tz*TY*W*W := by
  positivity

/-- The four composite positives of the chart domain, from the domain
hypotheses. -/
theorem k2Chart_composites_pos {ed ee td te tz : ℝ}
    (htd : 0 < td) (hte : 0 < te) (htz : 0 < tz)
    (hed : -1 < ed) (hee : -1 < ee)
    (hty : tz < td*ed + te*ee)
    (hbudget : td + te + (td*ed + te*ee) < 1) :
    0 < td*(1+ed) ∧ 0 < te*(1+ee)
      ∧ 0 < td*(1+ed) + te*(1+ee) - td - te - tz
      ∧ 0 < 1 - td*(1+ed) - te*(1+ee)
      ∧ 0 < td*(1+ed)*te + te*(1+ee)*td - td*te := by
  have hT : 0 < td*ed + te*ee := by linarith
  have hsum := k2Chart_excessSum_pos htd hte hed hee hT
  refine ⟨mul_pos htd (by linarith), mul_pos hte (by linarith), ?_, ?_, ?_⟩
  · have h : td*(1+ed) + te*(1+ee) - td - te - tz = (td*ed + te*ee) - tz := by ring
    rw [h]; linarith
  · have h : 1 - td*(1+ed) - te*(1+ee) = 1 - (td + te + (td*ed + te*ee)) := by ring
    rw [h]; linarith
  · have h : td*(1+ed)*te + te*(1+ee)*td - td*te = td*te*(1 + ed + ee) := by ring
    rw [h]; exact mul_pos (mul_pos htd hte) hsum

/-- **THE CROSS BRACKET IS POSITIVE ON THE DOMAIN.** -/
theorem k2ChartCrossHalf_bracket_pos {ed ee td te tz : ℝ}
    (htd : 0 < td) (hte : 0 < te) (htz : 0 < tz)
    (hed : -1 < ed) (hee : -1 < ee)
    (hty : tz < td*ed + te*ee)
    (hbudget : td + te + (td*ed + te*ee) < 1) :
    0 < 2 * (td*te*(td*ed + te*ee)*(td*(1+ed) + te*(1+ee))
          * (1 + ed + ee) * (1 - td - te - tz))
        + tz * k2ChartCrossHalfResidue ed ee td te tz := by
  obtain ⟨hP, hQ, hTY, hW, hG⟩ := k2Chart_composites_pos htd hte htz hed hee hty hbudget
  rw [k2ChartCrossHalf_certificate ed ee td te tz (td*(1+ed)) (te*(1+ee))
    (td*(1+ed) + te*(1+ee) - td - te - tz) (1 - td*(1+ed) - te*(1+ee))
    (td*(1+ed)*te + te*(1+ee)*td - td*te) rfl rfl rfl rfl rfl]
  exact k2ChartCrossHalf_cert_pos hP hQ htd hte htz hTY hW hG

/-- **THE HALF-ANGLE ENDPOINT HOLDS ON THE WHOLE DOMAIN.**  Twice the endpoint
is the plane mass of `e`, times the complementary plane weight, times the
bracket — three positives. -/
theorem k2ChartCrossCertHalfAngle_holds : K2ChartCrossCertHalfAngle := by
  intro ed ee td te tz htd hte htz hed hee hty hbudget
  have hkey := k2ChartCrossCert_half_split ed ee td te tz
  have hbr := k2ChartCrossHalf_bracket_pos htd hte htz hed hee hty hbudget
  have hq : 0 < te*(1+ee) := mul_pos hte (by linarith)
  have htz1 : 0 < 1 - tz := by linarith
  have htwo : 0 < 2 * k2ChartCrossCert ed ee td te (td*ed + te*ee - tz) tz (1/2) := by
    rw [hkey]
    exact mul_pos (mul_pos hq htz1) hbr
  linarith

/-- **THE CROSS CERTIFICATE IS POSITIVE ON THE LOW-ANGLE HALF.**  Affine in the
angle, positive at both endpoints, so positive between them. -/
theorem k2ChartCrossCert_pos_lowAngle {ed ee td te tz X : ℝ}
    (htd : 0 < td) (hte : 0 < te) (hed : -1 < ed) (hee : -1 < ee)
    (htz : 0 < tz) (hX : 0 ≤ X) (hX2 : X ≤ 1/2)
    (hT : 0 < td*ed + te*ee)
    (hty : tz < td*ed + te*ee)
    (hbudget : td + te + (td*ed + te*ee) < 1) :
    0 < k2ChartCrossCert ed ee td te (td*ed + te*ee - tz) tz X :=
  k2ChartCrossCert_pos_of_halfAngle k2ChartCrossCertHalfAngle_holds
    htd hte hed hee htz hX hX2 hT hty hbudget

/-! ## 2. The quotient boundary reading on the low-angle half -/

/-- **THE NEGATED BOUNDARY READING IS A SUM OF THIRTY-FOUR PRODUCTS.**  The
plane angle enters through `X` and its complement to one half, both
nonnegative on the low-angle half. -/
theorem k2ChartWomBoundary_certificate (ed ee td te tz X : ℝ)
    (P Q TY W G XC : ℝ)
    (hP : P = td*(1+ed)) (hQ : Q = te*(1+ee))
    (hTY : TY = P + Q - td - te - tz) (hW : W = 1 - P - Q)
    (hG : G = P*te + Q*td - td*te) (hXC : XC = 1/2 - X) :
    k2ChartQuotientWomBoundary ed ee td te tz X
    = -( (1/2)*P*Q*td*te + P*Q*tz*TY + (1/2)*P*Q*W*G
        + (1/2)*Q*Q*td*te + Q*Q*tz*TY + (1/2)*Q*Q*W*G
        + (1/2)*Q*tz*tz*G + Q*tz*G*XC + (1/2)*Q*TY*TY*G + Q*TY*G*XC
        + (1/2)*P*Q*td*te*TY + P*Q*td*te*XC + 2*P*Q*td*tz*XC
        + (1/2)*P*Q*te*te*tz + (1/2)*P*Q*te*te*TY + P*Q*tz*tz*W
        + (1/2)*Q*Q*td*td*tz + (1/2)*Q*Q*td*td*TY + (1/2)*Q*Q*td*te*TY
        + Q*Q*td*te*XC + 2*Q*Q*te*tz*XC + Q*Q*tz*tz*W
        + (1/2)*Q*td*te*tz*tz + (1/2)*Q*td*te*tz*W + Q*td*te*tz*X
        + (1/2)*Q*td*te*TY*TY + Q*td*W*G*XC + Q*te*W*G*XC
        + Q*tz*TY*W*G + Q*tz*W*W*G
        + P*Q*td*te*TY*XC + Q*Q*td*te*TY*XC
        + Q*td*te*tz*TY*W + Q*td*te*tz*W*XC ) := by
  subst hP hQ hTY hW hG hXC
  unfold k2ChartQuotientWomBoundary k2ChartQuotientSlope k2ChartQuotientBase
  ring

/-- The thirty-four products are positive when their factors are positive and
the two angle factors are nonnegative. -/
theorem k2ChartWomBoundary_cert_pos {P Q td te tz TY W G X XC : ℝ}
    (hP : 0 < P) (hQ : 0 < Q) (htd : 0 < td) (hte : 0 < te) (htz : 0 < tz)
    (hTY : 0 < TY) (hW : 0 < W) (hG : 0 < G) (hX : 0 ≤ X) (hXC : 0 ≤ XC) :
    0 < (1/2)*P*Q*td*te + P*Q*tz*TY + (1/2)*P*Q*W*G
        + (1/2)*Q*Q*td*te + Q*Q*tz*TY + (1/2)*Q*Q*W*G
        + (1/2)*Q*tz*tz*G + Q*tz*G*XC + (1/2)*Q*TY*TY*G + Q*TY*G*XC
        + (1/2)*P*Q*td*te*TY + P*Q*td*te*XC + 2*P*Q*td*tz*XC
        + (1/2)*P*Q*te*te*tz + (1/2)*P*Q*te*te*TY + P*Q*tz*tz*W
        + (1/2)*Q*Q*td*td*tz + (1/2)*Q*Q*td*td*TY + (1/2)*Q*Q*td*te*TY
        + Q*Q*td*te*XC + 2*Q*Q*te*tz*XC + Q*Q*tz*tz*W
        + (1/2)*Q*td*te*tz*tz + (1/2)*Q*td*te*tz*W + Q*td*te*tz*X
        + (1/2)*Q*td*te*TY*TY + Q*td*W*G*XC + Q*te*W*G*XC
        + Q*tz*TY*W*G + Q*tz*W*W*G
        + P*Q*td*te*TY*XC + Q*Q*td*te*TY*XC
        + Q*td*te*tz*TY*W + Q*td*te*tz*W*XC := by
  positivity

/-- **THE BOUNDARY READING IS NEGATIVE ON THE LOW-ANGLE HALF.** -/
theorem k2ChartQuotientWomBoundary_neg {ed ee td te tz X : ℝ}
    (htd : 0 < td) (hte : 0 < te) (htz : 0 < tz)
    (hed : -1 < ed) (hee : -1 < ee)
    (hX : 0 ≤ X) (hX2 : X ≤ 1/2)
    (hty : tz < td*ed + te*ee)
    (hbudget : td + te + (td*ed + te*ee) < 1) :
    k2ChartQuotientWomBoundary ed ee td te tz X < 0 := by
  obtain ⟨hP, hQ, hTY, hW, hG⟩ := k2Chart_composites_pos htd hte htz hed hee hty hbudget
  have hXC : 0 ≤ 1/2 - X := by linarith
  rw [k2ChartWomBoundary_certificate ed ee td te tz X (td*(1+ed)) (te*(1+ee))
    (td*(1+ed) + te*(1+ee) - td - te - tz) (1 - td*(1+ed) - te*(1+ee))
    (td*(1+ed)*te + te*(1+ee)*td - td*te) (1/2 - X) rfl rfl rfl rfl rfl rfl]
  have := k2ChartWomBoundary_cert_pos hP hQ htd hte htz hTY hW hG hX hXC
  linarith

/-! ## 3. The named statements, discharged -/

/-- **THE SCALE-FREE RESIDUAL HOLDS.**  Both signs of
`Gtz.K2ChartCrossCertPositivity` are theorems. -/
theorem k2ChartCrossCertPositivity_holds : K2ChartCrossCertPositivity := by
  intro ed ee td te ty tz X hty htz htd hte hX hX2 hed hee hbudget hT hE
  have hty' : tz < td*ed + te*ee := by linarith
  have hbudget' : td + te + (td*ed + te*ee) < 1 := by linarith
  refine ⟨k2ChartQuotientWomBoundary_neg htd hte htz hed hee hX hX2 hty' hbudget', ?_⟩
  have hcert := k2ChartCrossCert_pos_lowAngle htd hte hed hee htz hX hX2 hT hty' hbudget'
  have hty_eq : ty = td*ed + te*ee - tz := by linarith
  rw [hty_eq]
  exact hcert

/-- **THE LOW-ANGLE TARGET POSITIVITY HOLDS.** -/
theorem k2ChartTargetPositivityXHalf_holds : K2ChartTargetPositivityXHalf := by
  intro ed ee P td te ty tz X hty htz htd hte hP hX0 _hX1 hed hee hE hsum hxhalf
    hV _hU _hD hW _hS3 _hS4 hQ1
  exact k2ChartTargetPositivityXHalf_of_crossCert k2ChartCrossCertPositivity_holds
    ed ee P td te ty tz X hty htz htd hte hP hX0 hxhalf hed hee hE hsum hV hW hQ1

/-- **THE DOUBLE-QUOTIENT CORNER IS EMPTY.** -/
theorem k2ChartDoubleQuotientCorner_holds : K2ChartDoubleQuotientCorner :=
  k2ChartDoubleQuotientCorner_of_xHalf k2ChartTargetPositivityXHalf_holds

/-! ## 4. The chart kill -/

/-- **THE CHART KILL, UNCONDITIONAL.**  On the structured legal domain of the
`(5,3)` two-zero chart, the four strict chart positives together with the two
excess caps and the two mixed refusals are impossible.  No named statement
remains between the chart domain and this conclusion. -/
theorem k2Chart_kill {ed ee P td te ty tz X : ℝ}
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
  k2Chart_kill_of_doubleQuotientCorner k2ChartDoubleQuotientCorner_holds
    hty htz htd hte hP hX0 hX1 hed hee hE hsum hV hU hD hW hS1 hS2 hS3 hS4

end Gtz
