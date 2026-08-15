import Gtz.Design.StarWallJointRegion

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The joint firing region at the two remaining vertex stars

`StarWallJointRegion` reads the three minors of the vertex-a cell in the wall
coordinates and lands the joint firing condition there.  The gauge star wall
carries an axis `z` whose three slots correspond to the three vertices `a`, `b`
and `c`, and the three vertex stars sit one at each slot.  The two clearing
identities `starWall_joint_minorTwo` and `starWall_joint_det` are stated on
opaque scalars, so the same reading holds at the other two stars.

At the star of the slot `i` the cell reads

  `al = kap1 * z i - w - S * dv`,  `be = kap2 * z i - v - S * dw`,
  `ga = z i - v * dv - w * dw`,

where `v` and `w` are the two remaining axis slots, `kap1` and `kap2` are the
boost quotients of the two triangle labels of the star, and `dv`, `dw` are the
dust fractions that the two remaining wall labels cut out of their pinned
floors.  The vertex-a instance is the landed one; this module adds the vertex-b
and vertex-c instances.

The three stars are not the whole atlas.  A directed search finds wall points at
which all three fail, and every one of them is carried by a path or a pendant
tree.  The three instances here are the symmetric core of the gauge wall, not
its closure.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The vertex-b star -/

/-- **THE JOINT FIRING CONDITION OF THE VERTEX-B CELL.**  The star at the middle
axis slot fires as soon as its own three minors read positively.  The boost
quotients `k0` and `k2` of the triangle labels `0` and `2` and the dust
fractions `r` and `q` of the wall labels `3` and `5` are independent.

This is the vertex-a condition with the axis slots permuted: the centre moves
from `z 0` to `z 1`, the two remaining slots are `z 0` and `z 2`, and the pinned
floor moves from label `3` to label `4`. -/
theorem kFourStarBCell_fires_of_wall_jointCondition (point : DirectionChartPoint 6)
    {z : Fin 3 → ℝ} {s k0 k2 r q : ℝ}
    (hz0 : 0 < z 0) (hz1 : 0 < z 1) (hz2 : 0 < z 2) (hs : 0 < s)
    (hm0 : point.mass 0 = s * (z 0 * z 1))
    (hm1 : point.mass 1 = s * (z 0 * z 2))
    (hm2 : point.mass 2 = s * (z 1 * z 2))
    (hm3 : point.mass 3 = s * (z 0 * ((z 0 + z 1 + z 2) * r)))
    (hd4 : point.mass 4 * (1 - point.weight 4)
      = s * (z 1 * (z 0 + z 1 + z 2)) * point.weight 4)
    (hm5 : point.mass 5 = s * (z 2 * ((z 0 + z 1 + z 2) * q)))
    (hw0 : point.weight 0 * (k0 + 1) ≤ 1) (hw2 : point.weight 2 * (k2 + 1) ≤ 1)
    (hcorner : 0 < k0 * z 1 - z 2 - (z 0 + z 1 + z 2) * r)
    (hgap : z 0 * z 2 < (k0 * z 1 - z 2 - (z 0 + z 1 + z 2) * r)
      * (k2 * z 1 - z 0 - (z 0 + z 1 + z 2) * q))
    (hjoint : (z 0 + z 1 + z 2)
        * (z 2 * q ^ 2 * (k0 * z 1 - z 2 - (z 0 + z 1 + z 2) * r)
          + z 0 * r ^ 2 * (k2 * z 1 - z 0 - (z 0 + z 1 + z 2) * q)
          + 2 * (z 0 * z 2) * (r * q))
      < (z 1 - z 0 * r - z 2 * q)
        * ((k0 * z 1 - z 2 - (z 0 + z 1 + z 2) * r)
            * (k2 * z 1 - z 0 - (z 0 + z 1 + z 2) * q) - z 0 * z 2)) :
    KFourUnsignedStarBCellFires point := by
  have hw0pos := point.weight_pos 0
  have hw2pos := point.weight_pos 2
  have hS : (0:ℝ) < z 0 + z 1 + z 2 := by linarith
  set al := k0 * z 1 - z 2 - (z 0 + z 1 + z 2) * r with hal
  set be := k2 * z 1 - z 0 - (z 0 + z 1 + z 2) * q with hbe
  set ga := z 1 - z 0 * r - z 2 * q with hga
  refine ⟨k0 * (s * (z 0 * z 1)), k2 * (s * (z 1 * z 2)),
    s * (z 1 * (z 0 + z 1 + z 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm0]; nlinarith [mul_pos hs (mul_pos hz0 hz1), hw0pos]
  · rw [hm2]; nlinarith [mul_pos hs (mul_pos hz1 hz2), hw2pos]
  · rw [hd4]
  · have hrw : k0 * (s * (z 0 * z 1)) - (point.mass 1 + point.mass 3) = s * (z 0 * al) := by
      rw [hm1, hm3, hal]; ring
    rw [hrw]; positivity
  · have hrwX : k0 * (s * (z 0 * z 1)) - (point.mass 1 + point.mass 3) = s * (z 0 * al) := by
      rw [hm1, hm3, hal]; ring
    have hrwY : k2 * (s * (z 1 * z 2)) - (point.mass 1 + point.mass 5) = s * (z 2 * be) := by
      rw [hm1, hm5, hbe]; ring
    have hrwm : point.mass 1 = s * (z 0 * z 2) := hm1
    rw [hrwX, hrwY, hrwm]
    exact starWall_joint_minorTwo hz0 hz2 hs hgap
  · have hrwX : k0 * (s * (z 0 * z 1)) - (point.mass 1 + point.mass 3) = s * (z 0 * al) := by
      rw [hm1, hm3, hal]; ring
    have hrwY : k2 * (s * (z 1 * z 2)) - (point.mass 1 + point.mass 5) = s * (z 2 * be) := by
      rw [hm1, hm5, hbe]; ring
    have hrwZ : s * (z 1 * (z 0 + z 1 + z 2)) - (point.mass 3 + point.mass 5)
        = s * ((z 0 + z 1 + z 2) * ga) := by
      rw [hm3, hm5, hga]; ring
    have hrwm1 : point.mass 1 = s * (z 0 * z 2) := hm1
    have hrwm3 : point.mass 3 = s * (z 0 * ((z 0 + z 1 + z 2) * r)) := hm3
    have hrwm5 : point.mass 5 = s * (z 2 * ((z 0 + z 1 + z 2) * q)) := hm5
    rw [hrwX, hrwY, hrwZ, hrwm1, hrwm3, hrwm5]
    have hperm : z 1 + z 0 + z 2 = z 0 + z 1 + z 2 := by ring
    have hdet := starWall_joint_det (a := z 1) hz0 hz2 hs (by linarith)
      (by rw [hperm]; exact hjoint)
    exact lt_of_lt_of_le hdet (le_of_eq (by ring))

/-- The vertex-b joint wall condition fires the full minor atlas. -/
theorem kFourAtlas_fires_of_wall_jointConditionB (point : DirectionChartPoint 6)
    {z : Fin 3 → ℝ} {s k0 k2 r q : ℝ}
    (hz0 : 0 < z 0) (hz1 : 0 < z 1) (hz2 : 0 < z 2) (hs : 0 < s)
    (hm0 : point.mass 0 = s * (z 0 * z 1))
    (hm1 : point.mass 1 = s * (z 0 * z 2))
    (hm2 : point.mass 2 = s * (z 1 * z 2))
    (hm3 : point.mass 3 = s * (z 0 * ((z 0 + z 1 + z 2) * r)))
    (hd4 : point.mass 4 * (1 - point.weight 4)
      = s * (z 1 * (z 0 + z 1 + z 2)) * point.weight 4)
    (hm5 : point.mass 5 = s * (z 2 * ((z 0 + z 1 + z 2) * q)))
    (hw0 : point.weight 0 * (k0 + 1) ≤ 1) (hw2 : point.weight 2 * (k2 + 1) ≤ 1)
    (hcorner : 0 < k0 * z 1 - z 2 - (z 0 + z 1 + z 2) * r)
    (hgap : z 0 * z 2 < (k0 * z 1 - z 2 - (z 0 + z 1 + z 2) * r)
      * (k2 * z 1 - z 0 - (z 0 + z 1 + z 2) * q))
    (hjoint : (z 0 + z 1 + z 2)
        * (z 2 * q ^ 2 * (k0 * z 1 - z 2 - (z 0 + z 1 + z 2) * r)
          + z 0 * r ^ 2 * (k2 * z 1 - z 0 - (z 0 + z 1 + z 2) * q)
          + 2 * (z 0 * z 2) * (r * q))
      < (z 1 - z 0 * r - z 2 * q)
        * ((k0 * z 1 - z 2 - (z 0 + z 1 + z 2) * r)
            * (k2 * z 1 - z 0 - (z 0 + z 1 + z 2) * q) - z 0 * z 2)) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inl
    (kFourStarBCell_fires_of_wall_jointCondition point hz0 hz1 hz2 hs hm0 hm1 hm2
      hm3 hd4 hm5 hw0 hw2 hcorner hgap hjoint))))))

/-! ## 2. The vertex-c star -/

/-- **THE JOINT FIRING CONDITION OF THE VERTEX-C CELL.**  The star at the last
axis slot fires as soon as its own three minors read positively.  The boost
quotients `k1` and `k2` of the triangle labels `1` and `2` and the dust
fractions `r` and `p` of the wall labels `3` and `4` are independent. -/
theorem kFourStarCCell_fires_of_wall_jointCondition (point : DirectionChartPoint 6)
    {z : Fin 3 → ℝ} {s k1 k2 r p : ℝ}
    (hz0 : 0 < z 0) (hz1 : 0 < z 1) (hz2 : 0 < z 2) (hs : 0 < s)
    (hm0 : point.mass 0 = s * (z 0 * z 1))
    (hm1 : point.mass 1 = s * (z 0 * z 2))
    (hm2 : point.mass 2 = s * (z 1 * z 2))
    (hm3 : point.mass 3 = s * (z 0 * ((z 0 + z 1 + z 2) * r)))
    (hm4 : point.mass 4 = s * (z 1 * ((z 0 + z 1 + z 2) * p)))
    (hd5 : point.mass 5 * (1 - point.weight 5)
      = s * (z 2 * (z 0 + z 1 + z 2)) * point.weight 5)
    (hw1 : point.weight 1 * (k1 + 1) ≤ 1) (hw2 : point.weight 2 * (k2 + 1) ≤ 1)
    (hcorner : 0 < k1 * z 2 - z 1 - (z 0 + z 1 + z 2) * r)
    (hgap : z 0 * z 1 < (k1 * z 2 - z 1 - (z 0 + z 1 + z 2) * r)
      * (k2 * z 2 - z 0 - (z 0 + z 1 + z 2) * p))
    (hjoint : (z 0 + z 1 + z 2)
        * (z 1 * p ^ 2 * (k1 * z 2 - z 1 - (z 0 + z 1 + z 2) * r)
          + z 0 * r ^ 2 * (k2 * z 2 - z 0 - (z 0 + z 1 + z 2) * p)
          + 2 * (z 0 * z 1) * (r * p))
      < (z 2 - z 0 * r - z 1 * p)
        * ((k1 * z 2 - z 1 - (z 0 + z 1 + z 2) * r)
            * (k2 * z 2 - z 0 - (z 0 + z 1 + z 2) * p) - z 0 * z 1)) :
    KFourUnsignedStarCCellFires point := by
  have hw1pos := point.weight_pos 1
  have hw2pos := point.weight_pos 2
  have hS : (0:ℝ) < z 0 + z 1 + z 2 := by linarith
  set al := k1 * z 2 - z 1 - (z 0 + z 1 + z 2) * r with hal
  set be := k2 * z 2 - z 0 - (z 0 + z 1 + z 2) * p with hbe
  set ga := z 2 - z 0 * r - z 1 * p with hga
  refine ⟨k1 * (s * (z 0 * z 2)), k2 * (s * (z 1 * z 2)),
    s * (z 2 * (z 0 + z 1 + z 2)), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hm1]; nlinarith [mul_pos hs (mul_pos hz0 hz2), hw1pos]
  · rw [hm2]; nlinarith [mul_pos hs (mul_pos hz1 hz2), hw2pos]
  · rw [hd5]
  · have hrw : k1 * (s * (z 0 * z 2)) - (point.mass 0 + point.mass 3) = s * (z 0 * al) := by
      rw [hm0, hm3, hal]; ring
    rw [hrw]; positivity
  · have hrwX : k1 * (s * (z 0 * z 2)) - (point.mass 0 + point.mass 3) = s * (z 0 * al) := by
      rw [hm0, hm3, hal]; ring
    have hrwY : k2 * (s * (z 1 * z 2)) - (point.mass 0 + point.mass 4) = s * (z 1 * be) := by
      rw [hm0, hm4, hbe]; ring
    have hrwm : point.mass 0 = s * (z 0 * z 1) := hm0
    rw [hrwX, hrwY, hrwm]
    exact starWall_joint_minorTwo hz0 hz1 hs hgap
  · have hrwX : k1 * (s * (z 0 * z 2)) - (point.mass 0 + point.mass 3) = s * (z 0 * al) := by
      rw [hm0, hm3, hal]; ring
    have hrwY : k2 * (s * (z 1 * z 2)) - (point.mass 0 + point.mass 4) = s * (z 1 * be) := by
      rw [hm0, hm4, hbe]; ring
    have hrwZ : s * (z 2 * (z 0 + z 1 + z 2)) - (point.mass 3 + point.mass 4)
        = s * ((z 0 + z 1 + z 2) * ga) := by
      rw [hm3, hm4, hga]; ring
    have hrwm0 : point.mass 0 = s * (z 0 * z 1) := hm0
    have hrwm3 : point.mass 3 = s * (z 0 * ((z 0 + z 1 + z 2) * r)) := hm3
    have hrwm4 : point.mass 4 = s * (z 1 * ((z 0 + z 1 + z 2) * p)) := hm4
    rw [hrwX, hrwY, hrwZ, hrwm0, hrwm3, hrwm4]
    have hperm : z 2 + z 0 + z 1 = z 0 + z 1 + z 2 := by ring
    have hdet := starWall_joint_det (a := z 2) hz0 hz1 hs (by linarith)
      (by rw [hperm]; exact hjoint)
    exact lt_of_lt_of_le hdet (le_of_eq (by ring))

/-- The vertex-c joint wall condition fires the full minor atlas. -/
theorem kFourAtlas_fires_of_wall_jointConditionC (point : DirectionChartPoint 6)
    {z : Fin 3 → ℝ} {s k1 k2 r p : ℝ}
    (hz0 : 0 < z 0) (hz1 : 0 < z 1) (hz2 : 0 < z 2) (hs : 0 < s)
    (hm0 : point.mass 0 = s * (z 0 * z 1))
    (hm1 : point.mass 1 = s * (z 0 * z 2))
    (hm2 : point.mass 2 = s * (z 1 * z 2))
    (hm3 : point.mass 3 = s * (z 0 * ((z 0 + z 1 + z 2) * r)))
    (hm4 : point.mass 4 = s * (z 1 * ((z 0 + z 1 + z 2) * p)))
    (hd5 : point.mass 5 * (1 - point.weight 5)
      = s * (z 2 * (z 0 + z 1 + z 2)) * point.weight 5)
    (hw1 : point.weight 1 * (k1 + 1) ≤ 1) (hw2 : point.weight 2 * (k2 + 1) ≤ 1)
    (hcorner : 0 < k1 * z 2 - z 1 - (z 0 + z 1 + z 2) * r)
    (hgap : z 0 * z 1 < (k1 * z 2 - z 1 - (z 0 + z 1 + z 2) * r)
      * (k2 * z 2 - z 0 - (z 0 + z 1 + z 2) * p))
    (hjoint : (z 0 + z 1 + z 2)
        * (z 1 * p ^ 2 * (k1 * z 2 - z 1 - (z 0 + z 1 + z 2) * r)
          + z 0 * r ^ 2 * (k2 * z 2 - z 0 - (z 0 + z 1 + z 2) * p)
          + 2 * (z 0 * z 1) * (r * p))
      < (z 2 - z 0 * r - z 1 * p)
        * ((k1 * z 2 - z 1 - (z 0 + z 1 + z 2) * r)
            * (k2 * z 2 - z 0 - (z 0 + z 1 + z 2) * p) - z 0 * z 1)) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inl (Or.inl (Or.inr (Or.inr (Or.inr (Or.inr
    (kFourStarCCell_fires_of_wall_jointCondition point hz0 hz1 hz2 hs hm0 hm1 hm2
      hm3 hm4 hd5 hw1 hw2 hcorner hgap hjoint))))))

end Gtz
