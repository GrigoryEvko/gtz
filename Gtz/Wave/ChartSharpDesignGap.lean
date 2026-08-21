/-
# `-(N M⁻¹ N)` IS the chart gap of the sharp design

`Gtz/Wave/ChartGapSharpDuality.lean` computes the conjugated inverse of a chart gap
and finds `Gtz.sharpChartGap D = 1 - diag t - Π`, with `Π = Gtz.totalGapHat`.  It
then identifies that with `Gtz.sharpHat` through the landed resolution of the
identity.  What it does NOT do is say that `Gtz.sharpHat` is the CHART of the sharp
design, because until recently no shipped statement named that design.

The campaign recorded exactly this gap.  `Gtz/Wave/SharpFiveSetCriterion.lean`
lists `Phat = 1 - Π` under "What is measured and NOT proved here", verified to
`2.4e-14`, and gives the reason: `Gtz.exists_naimark_sharp_design` exports
existence only.  `Gtz/Wave/SharpDesignInvolution.lean` has since named the design
(`Gtz.naimarkSharpDesign`), carrying the whitener as data.  This module spends that
and closes the measured item:

  **`Gtz.projectionOfDesign_naimarkSharpDesign`** — the chart of the sharp design
  is `Gtz.sharpHat`, on the nose.

  **`Gtz.chartGapOfDesign_naimarkSharpDesign`** — hence its chart GAP is
  `Gtz.sharpChartGap`.

  **`Gtz.chartGapOfDesign_sharpDual_eq_sharpDesign`** — hence

      `-(N M⁻¹ N)  =  chart gap of the sharp design` ,   `N = diag √(t(1 - t))` .

So the duality of the previous module is not a formula that happens to resemble the
sharp design.  It is that design's own matrix, and the involution and the missing
fixed point are statements about designs and not only about matrices.

## The three steps

* The scaled frame of the sharp design is `Gtz.sharpFrame` times the whitener
  (`Gtz.scaledAtomRows_naimarkSharpDesign`).  The one scalar identity it needs is
  `√t_c · √(t_c/(1 - t_c)) = t_c / √(1 - t_c)`, which is
  `Gtz.sqrtWeight_mul_sharpScale`.
* The whitener's own square is the inverse of the sharp target
  (`Gtz.whiten_mul_transpose_eq_inv`): conjugate `whitenᵀ Θ whiten = 1` by the
  whitener and cancel.
* Then `V_E V_Eᵀ = sharpFrame (whiten whitenᵀ) sharpFrameᵀ = Gtz.sharpHat`.

No square root of a matrix and no eigenvalue appears; the only root is the scalar
`√t_c`, which the frame already carries.

## What this does not say

It says nothing about the hinge.  `Gtz.hinge_not_preserved_by_duality` shows the
sharp duality carries `Gtz.IsTie` and not `Gtz.HasParallelPair`, and naming the
design does not change that.  What it does change is that every statement about
`Gtz.sharpChartGap` — the involution, the absent fixed point, the pair exchange —
is now a statement about a design that the tree can name and iterate.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.ProjectionForm
import Gtz.Wave.SharpShareCoAtom
import Gtz.Wave.SharpDesignInvolution
import Gtz.Wave.ChartQuadraticCore
import Gtz.Wave.ChartGapSharpDuality

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

namespace Gtz

open Matrix Finset

variable {m k r : ℕ}
variable {D : WeightedDesign m k}

/-! ## Part 1 — the one scalar identity

The frame of the sharp design carries `√t_c` from the chart and `√(t_c/(1 - t_c))`
from the construction.  Their product is the co-weighted scalar of
`Gtz.sharpFrame`. -/

/-- **THE TWO ROOTS COMBINE INTO THE SHARP FRAME'S SCALAR.**
`√t_c · √(t_c/(1 - t_c)) = t_c / √(1 - t_c)`. -/
theorem sqrtWeight_mul_sharpScale (D : WeightedDesign m k) (hm : 2 ≤ m) (atomIndex : Fin m) :
    Real.sqrt (D.weight atomIndex) * sharpScale D atomIndex
      = D.weight atomIndex / coRoot D atomIndex := by
  have hpos := D.weight_pos atomIndex
  have hslack : (0 : ℝ) < 1 - D.weight atomIndex := by
    linarith [weight_lt_one D hm atomIndex]
  have hroot : (0 : ℝ) < Real.sqrt (1 - D.weight atomIndex) := Real.sqrt_pos.mpr hslack
  rw [sharpScale, ← Real.sqrt_mul hpos.le, coRoot]
  have hvalue : D.weight atomIndex * (D.weight atomIndex / (1 - D.weight atomIndex))
      = (D.weight atomIndex / Real.sqrt (1 - D.weight atomIndex)) ^ 2 := by
    rw [div_pow, Real.sq_sqrt hslack.le]
    ring
  rw [hvalue, Real.sqrt_sq (by positivity)]

/-! ## Part 2 — the frame of the sharp design -/

/-- **THE SCALED FRAME OF THE SHARP DESIGN IS THE SHARP FRAME, WHITENED.**  The
`√t_c` of the chart and the `√(t_c/(1 - t_c))` of the construction combine into the
`t_c / √(1 - t_c)` that `Gtz.sharpFrame` already carries. -/
theorem scaledAtomRows_naimarkSharpDesign {N : NaimarkDual D r} (F : SharpFrame N)
    (hm : 2 ≤ m) :
    scaledAtomRows (naimarkSharpDesign F hm) = sharpFrame D N * F.whiten := by
  ext atomIndex coord
  rw [Matrix.mul_apply]
  show Real.sqrt (D.weight atomIndex) * naimarkSharpAtom F atomIndex coord = _
  rw [naimarkSharpAtom, Matrix.mulVec, dotProduct, Finset.mul_sum]
  refine Finset.sum_congr rfl fun dualCoord _ => ?_
  rw [Matrix.transpose_apply, Pi.smul_apply, smul_eq_mul, sharpFrame, Matrix.of_apply]
  linear_combination (N.co atomIndex dualCoord * F.whiten dualCoord coord)
    * sqrtWeight_mul_sharpScale D hm atomIndex

/-- **THE WHITENER'S OWN SQUARE IS THE INVERSE OF THE SHARP TARGET.**  Conjugating
`whitenᵀ Θ whiten = 1` by the whitener and cancelling leaves
`(whiten whitenᵀ) Θ = 1`. -/
theorem whiten_mul_transpose_eq_inv {N : NaimarkDual D r} (F : SharpFrame N) (hm : 2 ≤ m) :
    F.whiten * F.whitenᵀ = (naimarkSharpTarget N)⁻¹ := by
  have hcancelRight : F.whiten * F.whiten⁻¹ = 1 := Matrix.mul_nonsing_inv _ F.unit
  have hstep : F.whiten * (F.whitenᵀ * naimarkSharpTarget N * F.whiten) * F.whiten⁻¹ = 1 := by
    rw [F.spec, Matrix.mul_one, hcancelRight]
  have hassoc : F.whiten * (F.whitenᵀ * naimarkSharpTarget N * F.whiten) * F.whiten⁻¹
      = (F.whiten * F.whitenᵀ) * naimarkSharpTarget N * (F.whiten * F.whiten⁻¹) := by
    simp only [Matrix.mul_assoc]
  have hconj : (F.whiten * F.whitenᵀ) * naimarkSharpTarget N = 1 := by
    rw [← hstep, hassoc, hcancelRight, Matrix.mul_one]
  exact (Matrix.inv_eq_left_inv hconj).symm

/-! ## Part 3 — the chart of the sharp design -/

/-- **THE CHART OF THE SHARP DESIGN IS THE SHARP HAT.**  The campaign recorded this
as measured and not proved, at `2.4e-14`, because the design had no name.  It has
one now, and the identification costs two steps. -/
theorem projectionOfDesign_naimarkSharpDesign {N : NaimarkDual D r} (F : SharpFrame N)
    (hm : 2 ≤ m) :
    projectionOfDesign (naimarkSharpDesign F hm) = sharpHat D N := by
  rw [projectionOfDesign, scaledAtomRows_naimarkSharpDesign F hm, sharpHat,
    ← whiten_mul_transpose_eq_inv F hm, Matrix.transpose_mul]
  simp only [Matrix.mul_assoc]

/-- The sharp hat is the complement of the co-weighted hat, read off the landed
resolution of the identity. -/
theorem sharpHat_eq_one_sub_totalGapHat {N : NaimarkDual D r} (hm : 2 ≤ m) :
    sharpHat D N = 1 - totalGapHat D := by
  rw [← totalGapHat_add_sharpHat D N hm]
  abel

/-- **THE CHART GAP OF THE SHARP DESIGN IS `Gtz.sharpChartGap`.**  The sharp design
carries the ORIGINAL weights, so its gap subtracts the same diagonal. -/
theorem chartGapOfDesign_naimarkSharpDesign {N : NaimarkDual D r} (F : SharpFrame N)
    (hm : 2 ≤ m) :
    chartGapOfDesign (naimarkSharpDesign F hm) = sharpChartGap D := by
  have hweight : (naimarkSharpDesign F hm).weight = D.weight := rfl
  rw [chartGapOfDesign, projectionOfDesign_naimarkSharpDesign F hm, hweight,
    sharpHat_eq_one_sub_totalGapHat (D := D) (N := N) hm, sharpChartGap]
  abel

/-- **THE DUALITY MAP LANDS ON THE SHARP DESIGN.**  Conjugating the inverse of a
design's chart gap by `diag √(t(1 - t))` and changing the sign produces exactly the
chart gap of `Gtz.naimarkSharpDesign`.

So `Gtz.negConjInv_negConjInv` and `Gtz.negConjInv_ne_self_of_diagonal_pos` are
statements about designs: sharpening twice returns the original gap, and no design
is its own sharp dual. -/
theorem chartGapOfDesign_sharpDual_eq_sharpDesign {N : NaimarkDual D r} (F : SharpFrame N)
    (hm : 2 ≤ m) :
    negConjInv (pairRootDiagonal D) (chartGapOfDesign D)
      = chartGapOfDesign (naimarkSharpDesign F hm) := by
  rw [chartGapOfDesign_naimarkSharpDesign F hm]
  exact chartGapOfDesign_sharpDual_eq_negConjInv D hm

/-- **THE DUALITY MAP LANDS ON A DESIGN, WITH NO FRAME IN THE STATEMENT.**  Every
design with two or more atoms and a Naimark dual of the complementary rank carries
a design whose chart gap is the conjugated inverse of its own. -/
theorem exists_design_chartGap_eq_sharpDual (D : WeightedDesign m k) (N : NaimarkDual D r)
    (hm : 2 ≤ m) :
    ∃ E : WeightedDesign m r, (∀ atomIndex, E.weight atomIndex = D.weight atomIndex)
      ∧ chartGapOfDesign E = negConjInv (pairRootDiagonal D) (chartGapOfDesign D) := by
  obtain ⟨F⟩ := exists_sharpFrame N hm
  exact ⟨naimarkSharpDesign F hm, fun _ => rfl,
    (chartGapOfDesign_sharpDual_eq_sharpDesign F hm).symm⟩

end Gtz
