/-
# The two-zero stratum in the normal frame, killed

`Gtz.k2Chart_kill` closes the `(5,3)` two-zero chart corner with no hypothesis
beyond the chart domain.  The bridge modules carry every ingredient that turns a
design into that chart: the normal form off Parseval at the axis, the four plane
readings, the four slack-to-determinant identities, the four chart positives, and
the determinant clearing of the last one.  Nothing assembled them.

This module is the assembly.  Its statement is the `(5,3)` two-zero kill written
in the normal frame: a design whose atoms sit as

  `x = (0,0,1)`, `y = (y₁,y₂,0)`, `z = (z₁,z₂,0)`, `d = (p,0,α)`, `e = (v,0,β)`

and which refuses the four triples that avoid the axis, is impossible
(`Gtz.k2Frame_kill`).  Every hypothesis is a Parseval reading, a weight
positivity, a nondegeneracy of the frame, or a refusal.

## What each hypothesis is

* `h1`, `h2`, `h3` are Parseval read at the two plane probes and their cross
  term; `hcol` is the collinearity of the outside plane parts.  All four are
  `Gtz.k2FivePlane_relations`, proved at design level.
* `haxis` is Parseval read at the axis, cleared by the weight sum: it is the
  chart's excess equation.
* `hsum` is the axis weight being positive.
* `hB11` and `hdet` say the plane gap is positive definite — the first Sylvester
  minor and the determinant.  These are the stratum's own corank condition, not
  an extra assumption.
* the four `hR` hypotheses are the refusals.

## The two missing frame determinants

`Gtz.tripleGapDet_frame_yde` and its `z` twin were landed; the docstring there
promises "three siblings" but the two CAP triples had none.  This module adds
them (`Gtz.tripleGapDet_frame_yzd`, `Gtz.tripleGapDet_frame_yze`), so all four
refusals are stated as gap determinants of explicit frame vectors rather than as
raw polynomials.

## What remains

The frame itself.  Producing this frame from an arbitrary `(5,3)` two-zero tie
is the rotation chart, and it is the last step between here and the design-level
statement.  The edges are already dead: `α = 0` by the excess identity and
`ρ = 0` by the parallel laws.
-/
import Gtz.Wave.KTwoChartCapstone
import Gtz.Wave.KTwoBridgeSlacks
import Gtz.Wave.KTwoBridgeDominates
import Gtz.Wave.KTwoBridgePositives
import Gtz.Wave.KTwoBridgePlaneReadings

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

/-! ## 1. The two missing frame determinants -/

/-- The coordinate determinant behind the first excess cap is the gap
determinant of the triple `{y,z,d}`. -/
theorem tripleGapDet_frame_yzd (y1 y2 z1 z2 al p : ℝ) :
    tripleGapDet ![y1,y2,0] ![z1,z2,0] ![p,0,al]
      = al^2*y1^2*z2^2 - al^2*y1^2 - 2*al^2*y1*y2*z1*z2 + al^2*y2^2*z1^2
        - al^2*y2^2 - al^2*z1^2 - al^2*z2^2 + al^2 - p^2*y2^2 - p^2*z2^2
        + p^2 - y1^2*z2^2 + y1^2 + 2*y1*y2*z1*z2 - y2^2*z1^2 + y2^2
        + z1^2 + z2^2 - 1 := by
  simp only [tripleGapDet, leverageOf, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-- The coordinate determinant behind the second excess cap is the gap
determinant of the triple `{y,z,e}`. -/
theorem tripleGapDet_frame_yze (y1 y2 z1 z2 be v : ℝ) :
    tripleGapDet ![y1,y2,0] ![z1,z2,0] ![v,0,be]
      = be^2*y1^2*z2^2 - be^2*y1^2 - 2*be^2*y1*y2*z1*z2 + be^2*y2^2*z1^2
        - be^2*y2^2 - be^2*z1^2 - be^2*z2^2 + be^2 - v^2*y2^2 - v^2*z2^2
        + v^2 - y1^2*z2^2 + y1^2 + 2*y1*y2*z1*z2 - y2^2*z1^2 + y2^2
        + z1^2 + z2^2 - 1 := by
  simp only [tripleGapDet, leverageOf, dotProduct, Fin.sum_univ_three,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons]
  ring

/-! ## 2. A squared frame scalar is positive -/

/-- A nonzero scalar has positive square.  Used three times, for the two outside
axis parts and the outside plane part. -/
theorem sq_pos_of_ne (a : ℝ) (ha : a ≠ 0) : 0 < a^2 := by
  rcases lt_or_gt_of_ne ha with h | h <;> nlinarith

/-! ## 3. The kill in the normal frame -/

/-- **THE TWO-ZERO STRATUM IS EMPTY IN THE NORMAL FRAME.**  A `(5,3)` design
presented in the frame, whose plane gap is positive definite and which refuses
the four triples avoiding the axis, does not exist.

The proof reads every chart hypothesis off the frame: the excess equation and
the budget from Parseval at the axis, the two angle bounds from the plane pair
reading, the four positives from the plane gap, and the four slack signs from
the four refusals through the landed identities.  Then
`Gtz.k2Chart_kill` closes it. -/
theorem k2Frame_kill {y1 y2 z1 z2 al be p v ty tz td te : ℝ}
    (hty : 0 < ty) (htz : 0 < tz) (htd : 0 < td) (hte : 0 < te)
    (hal : al ≠ 0) (hbe : be ≠ 0) (hp : p ≠ 0)
    (h1 : ty*y1^2 + tz*z1^2 + td*p^2 + te*v^2 = 1)
    (h2 : ty*(y1*y2) + tz*(z1*z2) = 0)
    (h3 : ty*y2^2 + tz*z2^2 = 1)
    (hcol : td*al*p + te*be*v = 0)
    (haxis : td*al^2 + te*be^2 = ty + tz + td + te)
    (hsum : td + te + ty + tz < 1)
    (hB11 : 0 < y1^2 + z1^2 - 1)
    (hdet : 0 < (y1^2 + z1^2 - 1)*(y2^2 + z2^2 - 1) - (y1*y2 + z1*z2)^2)
    (hRyzd : tripleGapDet ![y1,y2,0] ![z1,z2,0] ![p,0,al] ≤ 0)
    (hRyze : tripleGapDet ![y1,y2,0] ![z1,z2,0] ![v,0,be] ≤ 0)
    (hRyde : tripleGapDet ![y1,y2,0] ![p,0,al] ![v,0,be] ≤ 0)
    (hRzde : tripleGapDet ![z1,z2,0] ![p,0,al] ![v,0,be] ≤ 0) :
    False := by
  have htzne : tz ≠ 0 := ne_of_gt htz
  have hal2 : 0 < al^2 := sq_pos_of_ne al hal
  have hbe2 : 0 < be^2 := sq_pos_of_ne be hbe
  have hp2 : 0 < p^2 := sq_pos_of_ne p hp
  have hq : 0 < te*be^2 := mul_pos hte hbe2
  have htytz : 0 < ty*tz := mul_pos hty htz
  -- the chart's angle variable and its two bounds
  have hX0 : (0:ℝ) ≤ ty*y2^2 := by positivity
  have hX1 : ty*y2^2 ≤ 1 := by
    nlinarith [mul_nonneg htz.le (sq_nonneg z2)]
  -- the excess equation
  have hE : td*(al^2-1) + te*(be^2-1) = ty + tz := by linarith
  -- the four positives
  obtain ⟨hW, hV, hU⟩ :=
    k2Plane_chart_positives y1 y2 z1 z2 al be ty tz td te p v
      hty htz hte hbe h1 h2 h3 hcol hB11 hdet
  have hDn := k2Plane_Dn_clear y1 y2 z1 z2 al be ty tz td te p v h1 h2 h3 hcol
  have hDpos : 0 < te*be^2*((1-ty)*(1-tz))
      - p^2*td*(td*al^2 + te*be^2)
        * ((1 - ty*y2^2)*(1-tz) + (ty*y2^2)*(1-ty)) := by
    have hrhs : 0 < te*be^2*(ty*tz)^2
        * ((y1^2 + z1^2 - 1)*(y2^2 + z2^2 - 1) - (y1*y2 + z1*z2)^2) := by
      have : (0:ℝ) < (ty*tz)^2 := by positivity
      exact mul_pos (mul_pos hq this) hdet
    nlinarith [hDn, hrhs, htytz]
  -- the four slack signs, from the four refusals
  have hS1 : 0 ≤ k2ChartCapD (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2) := by
    rw [k2ChartCapD_eq_gapDet y1 y2 z1 z2 al be p v ty tz td te htzne h1 h2 h3 hcol]
    rw [← tripleGapDet_frame_yzd y1 y2 z1 z2 al p]
    have hfac : 0 < ty*tz*te*be^2 := by positivity
    nlinarith [hRyzd, hfac]
  have hS2 : 0 ≤ k2ChartCapE (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2) := by
    rw [k2ChartCapE_eq_gapDet y1 y2 z1 z2 al be p v ty tz td te htzne h1 h2 h3 hcol]
    rw [← tripleGapDet_frame_yze y1 y2 z1 z2 be v]
    have hfac : 0 < ty*tz*te^2*be^2 := by positivity
    nlinarith [hRyze, hfac]
  have hstar := k2Plane_star_eq_zero y1 y2 z1 z2 ty tz td te p v h1 h2 h3
  have hS3 : 0 ≤ k2ChartRefusalY (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2) := by
    rw [k2ChartRefusalY_eq_gapDet y1 y2 al be p v ty tz td te hcol hstar]
    rw [← tripleGapDet_frame_yde y1 y2 al be p v]
    have hfac : 0 < ty*te^2*be^2 := by positivity
    nlinarith [hRyde, hfac]
  have hS4 : 0 ≤ k2ChartRefusalZ (al^2-1) (be^2-1) (p^2) td te ty tz (ty*y2^2) := by
    rw [k2ChartRefusalZ_eq_gapDet y1 y2 z1 z2 al be p v ty tz td te
      htzne h1 h2 h3 hcol]
    rw [← tripleGapDet_frame_zde z1 z2 al be p v]
    have hfac : 0 < tz*te^2*be^2 := by positivity
    nlinarith [hRzde, hfac]
  -- reconcile the chart's `1 + e` forms with the frame squares
  have ea : (1:ℝ) + (al^2 - 1) = al^2 := by ring
  have eb : (1:ℝ) + (be^2 - 1) = be^2 := by ring
  refine k2Chart_kill (ed := al^2-1) (ee := be^2-1) (P := p^2)
    (td := td) (te := te) (ty := ty) (tz := tz) (X := ty*y2^2)
    hty htz htd hte hp2 hX0 hX1 (by linarith) (by linarith) hE hsum ?_ ?_ ?_ ?_
    hS1 hS2 hS3 hS4
  · exact hV
  · rw [ea, eb]; exact hU
  · rw [ea, eb]; exact hDpos
  · rw [ea, eb]; exact hW

end Gtz
