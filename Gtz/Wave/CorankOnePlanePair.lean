/-
# The covering pair in the null plane

Rank two is a theorem (`Gtz.gtz_rank_two`), and `Gtz.inPlaneRestriction` turns
any rank-three design into a genuine rank-two design on any orthonormal plane
frame.  This module points that machine at the one plane the tie itself
distinguishes: the orthogonal complement of the null direction of a corank-one
weak dominator.

The output is unconditional: EVERY `(m,3)` design carries, for every nonzero
direction `u`, a pair of labels whose atoms cover all in-plane readings.  At a
corank-one tie the instance at the null direction is the first unconditional
foothold inside the tie — a pair that the tie can not starve in the plane.

## FIELD legality

The chain consumes the sharp rank-two constant one of `Gtz.gtz_rank_two`,
which is REAL-ONLY: over the complex numbers the rank-two constant is
`2 - 2/sqrt 3 < 1`, attained at the four equiangular lines of `C^2`.  The
argument of this module fails over `C` exactly at this step, as a real-only
proof must.

## The frame

`Gtz.planeFirst u` and `Gtz.planeSecond u` (Gtz/Wave/ShareOneForcing.lean) are
an orthonormal basis of the plane `u^perp`, division-free through the cross
product.  `Gtz.frame_expansion` resolves every in-plane vector through the two
frame readings, which is what transports the pair from frame coordinates to
all of `u^perp`.
-/
import Gtz.Wave.ShareOneForcing
import Gtz.Wave.CorankOneNormalForm

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {m : ℕ}

/-- **THE PLANE COVERING PAIR.**  Every rank-three design has, for every
nonzero direction, two labels whose atoms cover every reading in the
orthogonal plane of that direction.  Rank-two GTZ, aimed at one plane. -/
theorem exists_plane_covering_pair (design : WeightedDesign m 3)
    {baseDir : Fin 3 → ℝ} (hbase : baseDir ≠ 0) :
    ∃ pairFirst pairSecond : Fin m, pairFirst ≠ pairSecond ∧
      ∀ inPlane : Fin 3 → ℝ, inPlane ⬝ᵥ baseDir = 0 →
        inPlane ⬝ᵥ inPlane
          ≤ (design.atom pairFirst ⬝ᵥ inPlane) ^ 2
            + (design.atom pairSecond ⬝ᵥ inPlane) ^ 2 := by
  obtain ⟨pairFirst, pairSecond, hne, hcover⟩ :=
    exists_inPlane_dominating_pair design (planeFirst baseDir)
      (planeSecond baseDir) (planeFirst_dotProduct_self baseDir)
      (planeSecond_dotProduct_self hbase)
      (planeFirst_dotProduct_planeSecond baseDir)
  refine ⟨pairFirst, pairSecond, hne, fun inPlane hperp => ?_⟩
  have hexp := frame_expansion hbase inPlane
  rw [hperp, zero_div, zero_smul, zero_add] at hexp
  have hcombo := hcover (inPlane ⬝ᵥ planeFirst baseDir)
    (inPlane ⬝ᵥ planeSecond baseDir)
  rw [← hexp] at hcombo
  exact hcombo

/-- **THE PAIR AT THE NULL DIRECTION.**  A corank-one weak dominator hands its
null direction to the plane machine: some pair of labels covers every reading
in the null plane.  The pair needs no tie hypothesis and no domination — it
exists at every design and every direction — but the null direction is the one
plane the tie itself singles out. -/
theorem exists_nullPlane_covering_pair (design : WeightedDesign m 3)
    (C : Finset (Fin m)) {nullDir : Fin 3 → ℝ}
    (hline : GapNullLine design C nullDir) :
    ∃ pairFirst pairSecond : Fin m, pairFirst ≠ pairSecond ∧
      ∀ inPlane : Fin 3 → ℝ, inPlane ⬝ᵥ nullDir = 0 →
        inPlane ⬝ᵥ inPlane
          ≤ (design.atom pairFirst ⬝ᵥ inPlane) ^ 2
            + (design.atom pairSecond ⬝ᵥ inPlane) ^ 2 :=
  exists_plane_covering_pair design hline.1

end Gtz
