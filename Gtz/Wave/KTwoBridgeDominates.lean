/-
# A negative chart slack exhibits a strict dominator

The four identities of `Gtz.KTwoBridgeRefusalY` and `Gtz.KTwoBridgeSlacks` say
each chart slack is its triple's gap determinant times a positive factor, so a
NEGATIVE slack is a POSITIVE gap determinant.  That is not yet domination: by
Sylvester a triple dominates when all THREE leading principal minors are
positive, and the determinant is only the third.

The sibling theorem `Gtz.tripleGram_posDef_iff_gapDet_pos_of_admissible` closes
exactly that gap.  Its Sylvester chain is ORDERED, so with the pair placed
FIRST the leading minors are `ℓ_a − 1`, `pairGapMinor a b`, `tripleGapDet a b c`
— and on an ADMISSIBLE pair with heavy leading atom the first two are given, so
the determinant alone decides.  Chaining it turns each slack identity into a
producer:

  **slack `< 0`  ⟹  the triple STRICTLY DOMINATES**

(`Gtz.k2ChartRefusalY_neg_dominates` and its three siblings), which is the last
logical joint of the chart-to-design bridge.

## The frame determinants are the gap determinants

Each identity was stated with an explicit coordinate determinant.  Those are
literally `Gtz.tripleGapDet` at the frame vectors
(`Gtz.tripleGapDet_frame_yde` and its three siblings), so the chain is a
rewrite and nothing more.

The pair chosen first is the one the chart makes admissible: the plane atom and
an outside atom for the two mixed refusals, and the plane PAIR for the two caps.
-/
import Gtz.Wave.KTwoBridgeSlacks
import Gtz.Wave.OppositeHornSelect

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

/-! ## 1. The frame determinants are gap determinants -/

/-- The coordinate determinant of the identity for the refusal keeping `y` is
the gap determinant of `{y,d,e}`. -/
theorem tripleGapDet_frame_yde (y1 y2 al be p v : ℝ) :
    tripleGapDet ![y1,y2,0] ![p,0,al] ![v,0,be]
      = al^2*v^2*y2^2 - al^2*v^2 - al^2*y1^2 - al^2*y2^2 + al^2
        - 2*al*be*p*v*y2^2 + 2*al*be*p*v + be^2*p^2*y2^2 - be^2*p^2
        - be^2*y1^2 - be^2*y2^2 + be^2 - p^2*y2^2 + p^2 - v^2*y2^2 + v^2
        + y1^2 + y2^2 - 1 := by
  simp only [tripleGapDet, leverageOf, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The coordinate determinant of the identity for the refusal keeping `z` is
the gap determinant of `{z,d,e}`. -/
theorem tripleGapDet_frame_zde (z1 z2 al be p v : ℝ) :
    tripleGapDet ![z1,z2,0] ![p,0,al] ![v,0,be]
      = al^2*v^2*z2^2 - al^2*v^2 - al^2*z1^2 - al^2*z2^2 + al^2
        - 2*al*be*p*v*z2^2 + 2*al*be*p*v + be^2*p^2*z2^2 - be^2*p^2
        - be^2*z1^2 - be^2*z2^2 + be^2 - p^2*z2^2 + p^2 - v^2*z2^2 + v^2
        + z1^2 + z2^2 - 1 := by
  simp only [tripleGapDet, leverageOf, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## 2. The producers -/

/-- **A NEGATIVE MIXED SLACK EXHIBITS A STRICT DOMINATOR.**  The slack is the
gap determinant times a positive factor, so a negative slack makes the
determinant positive; on an admissible leading pair that IS domination. -/
theorem k2ChartRefusalY_neg_dominates (y1 y2 al be p v ty tz td te : ℝ)
    (hty : 0 < ty) (hte : 0 < te) (hbe : be ≠ 0)
    (hcol : td*al*p + te*be*v = 0)
    (hstar : (ty*(y1*y2))^2
        - (1 - td*p^2 - te*v^2 - ty*y1^2)*(1 - ty*y2^2) = 0)
    (hmin : 0 < pairGapMinor ![y1,y2,0] ![p,0,al])
    (htr : 2 < leverageOf ![y1,y2,0] + leverageOf ![p,0,al])
    (hneg : k2ChartRefusalY (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2) < 0) :
    (tripleGram ![y1,y2,0] ![p,0,al] ![v,0,be] - 1).PosDef := by
  rw [tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr,
    tripleGapDet_frame_yde]
  have hid := k2ChartRefusalY_eq_gapDet y1 y2 al be p v ty tz td te hcol hstar
  have hpos : 0 < ty*te^2*be^2 := by positivity
  nlinarith [hid, hneg, hpos]

/-- **A NEGATIVE MIRROR SLACK EXHIBITS A STRICT DOMINATOR.**  The twin of the
previous theorem, on the other plane atom. -/
theorem k2ChartRefusalZ_neg_dominates
    (y1 y2 z1 z2 al be p v ty tz td te : ℝ)
    (htz : 0 < tz) (hte : 0 < te) (hbe : be ≠ 0) (htzne : tz ≠ 0)
    (h1 : ty*y1^2 + tz*z1^2 + td*p^2 + te*v^2 = 1)
    (h2 : ty*(y1*y2) + tz*(z1*z2) = 0)
    (h3 : ty*y2^2 + tz*z2^2 = 1)
    (hcol : td*al*p + te*be*v = 0)
    (hmin : 0 < pairGapMinor ![z1,z2,0] ![p,0,al])
    (htr : 2 < leverageOf ![z1,z2,0] + leverageOf ![p,0,al])
    (hneg : k2ChartRefusalZ (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2) < 0) :
    (tripleGram ![z1,z2,0] ![p,0,al] ![v,0,be] - 1).PosDef := by
  rw [tripleGram_posDef_iff_gapDet_pos_of_admissible hmin htr,
    tripleGapDet_frame_zde]
  have hid := k2ChartRefusalZ_eq_gapDet y1 y2 z1 z2 al be p v ty tz td te
    htzne h1 h2 h3 hcol
  have hpos : 0 < tz*te^2*be^2 := by positivity
  nlinarith [hid, hneg, hpos]

end Gtz
