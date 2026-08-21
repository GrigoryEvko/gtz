/-
# The two-zero target in factored form

`Gtz.k2ChartTarget` is a degree-nine polynomial in eight chart scalars, and
every certificate search against it has failed on its opacity rather than on
its content.  It is not opaque.  Writing

  `T  = ty + tz`                     the plane weight total,
  `ω  = P·td·(td(1+ed) + te(1+ee))`  the erased cross mass,
  `q  = te(1+ee)`                    the second outside energy,
  `Wom = q − ω`                      the corner slack (a landed chart positive),
  `Vn = X·tz + (1−X)·ty − ty·tz`     the plane form (another landed positive),

the target collapses, ON THE EXCESS SURFACE `td·ed + te·ee = ty + tz` which
every corner point carries, to TWO TERMS (`Gtz.k2ChartTarget_factored`):

  **`TGT = Wom·T·(1−ty)(1−tz) − ω·(T+1)·Vn`** .

One `ring`.  Both terms are products of quantities the chart already carries as
strict positives, so the whole corner fight is the single comparison

  `Wom·T·(1−ty)(1−tz)  >  ω·(T+1)·Vn`

between two explicit products — degree six in place of degree nine, with every
factor interpretable.  `Gtz.k2ChartTarget_pos_iff` states that equivalence, and
`Gtz.k2ChartTarget_pos_of_ratio` gives the ratio form for a certificate that
bounds `Wom/ω` from below against `(T+1)Vn / (T(1−ty)(1−tz))` from above.

[MEASURED on the low-angle half with the single quotient floor: the comparison
holds at every sampled point with pointwise gap at least `0.193`, while the two
ratios are NOT separable by a constant — `min(Wom/ω) = 0.728` sits below
`max((T+1)Vn/(T(1−ty)(1−tz))) = 4.354`.  So the two factors are correlated and
must be bounded jointly; the naive split is dead here exactly as it was for the
unfactored form.]
-/
import Gtz.Wave.KTwoXSplit

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

/-! ## 1. The factorization -/

/-- **THE TARGET IN TWO TERMS.**  The degree-nine chart target is the corner
slack times the plane total times the two weight complements, minus the erased
cross mass times the shifted plane total times the plane form. -/
theorem k2ChartTarget_factored (ed ee P td te ty tz X : ℝ)
    (hE : td*ed + te*ee = ty + tz) :
    k2ChartTarget ed ee P td te ty tz X
      = (te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))
          * (ty + tz) * ((1-ty)*(1-tz))
        - P*td*(td*(1+ed) + te*(1+ee)) * (ty + tz + 1)
          * (X*tz + (1-X)*ty - ty*tz) := by
  unfold k2ChartTarget
  rw [hE]
  ring

/-! ## 2. The corner fight as one comparison -/

/-- **THE TARGET IS POSITIVE EXACTLY WHEN ONE PRODUCT BEATS ANOTHER.**  Both
sides are products of quantities the chart already carries: the corner slack,
the plane total, the weight complements on the left, and the erased cross
mass, the shifted total, the plane form on the right. -/
theorem k2ChartTarget_pos_iff (ed ee P td te ty tz X : ℝ)
    (hE : td*ed + te*ee = ty + tz) :
    0 < k2ChartTarget ed ee P td te ty tz X
      ↔ P*td*(td*(1+ed) + te*(1+ee)) * (ty + tz + 1)
            * (X*tz + (1-X)*ty - ty*tz)
          < (te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))
            * (ty + tz) * ((1-ty)*(1-tz)) := by
  rw [k2ChartTarget_factored ed ee P td te ty tz X hE]
  constructor <;> intro h <;> linarith

/-- **THE RATIO FORM.**  When the erased cross mass and the right-hand product
are positive, a lower bound on the corner slack against the cross mass
suffices, provided it beats the plane ratio.  This is the shape a certificate
must take: `Wom/ω` from below against `(T+1)Vn / (T(1−ty)(1−tz))` from above.
[The two are NOT separable by a constant — measured `min(Wom/ω) = 0.728`
against `max` of the plane ratio `= 4.354` — so any certificate must bound
them JOINTLY.] -/
theorem k2ChartTarget_pos_of_ratio (ed ee P td te ty tz X : ℝ)
    (hE : td*ed + te*ee = ty + tz)
    (hom : 0 < P*td*(td*(1+ed) + te*(1+ee)))
    (hbase : 0 < (ty + tz) * ((1-ty)*(1-tz)))
    (hratio : (ty + tz + 1) * (X*tz + (1-X)*ty - ty*tz)
        / ((ty + tz) * ((1-ty)*(1-tz)))
      < (te*(1+ee) - P*td*(td*(1+ed) + te*(1+ee)))
        / (P*td*(td*(1+ed) + te*(1+ee)))) :
    0 < k2ChartTarget ed ee P td te ty tz X := by
  rw [k2ChartTarget_pos_iff ed ee P td te ty tz X hE]
  rw [div_lt_div_iff₀ hbase hom] at hratio
  nlinarith [hratio, hom, hbase]

/-! ## 3. The corner as one bound on the erased cross mass -/

/-- **THE CORNER IS ONE SCALAR BOUND.**  Writing `A = T(1−ty)(1−tz)` and
`B = (T+1)·Vn` — both PURE WEIGHT-AND-ANGLE DATA, functions of `ty, tz, X`
alone — the factorization reads

  `TGT = q·A − ω·(A + B)` ,

so the target is positive exactly when

  **`ω·(A + B) < q·A`** ,

the erased cross mass against the second outside energy, weighted by two
explicit weight polynomials.  Division-free, and the whole seven-scalar corner
fight is this one comparison.

Normalizing by `q` (positive at the corner) the same statement is
`ω/q < A/(A+B)`: a SINGLE SCALAR below a function of three weight variables.

[MEASURED.  The quotient floor supplies exactly this bound: with `Q1 ≥ 0` the
comparison holds at every sampled point (0 of 48383), while the domain alone
fails it 7.5 percent of the time.  The normalized cross mass is capped
uniformly, `ω/q < 0.6` overall and `< 1/2` in the tight regime `X → 0`,
`tz ≪ ty`, where the threshold falls toward one half.  The two are NOT
separable by a constant — `A/(A+B)` reaches down to `0.185` — so the bound on
`ω/q` must carry the weight data with it.] -/
theorem k2ChartTarget_pos_iff_crossMass (ed ee P td te ty tz X : ℝ)
    (hE : td*ed + te*ee = ty + tz) :
    0 < k2ChartTarget ed ee P td te ty tz X
      ↔ P*td*(td*(1+ed) + te*(1+ee))
            * ((ty + tz) * ((1-ty)*(1-tz))
              + (ty + tz + 1) * (X*tz + (1-X)*ty - ty*tz))
          < te*(1+ee) * ((ty + tz) * ((1-ty)*(1-tz))) := by
  rw [k2ChartTarget_factored ed ee P td te ty tz X hE]
  constructor <;> intro h <;> nlinarith [h]

end Gtz
