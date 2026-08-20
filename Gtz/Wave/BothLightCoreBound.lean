import Gtz.Wave.CompoundProbeRelations

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The core of the seven weighted terms, bounded

The both-light obligation is the upper estimate of the seven weighted terms
of the weight-gap determinant law under the seven floors.  At the measured
roof the three terms `det K + t_y·KRy + t_z·KRz` carry more than 97 percent
of the law's mass.  This module bounds exactly that core.

The instrument is an exact identity with no hypotheses beyond the two
four-set positivities: writing `D_y, D_z` for the four-set gap determinants,
the two downdate presentations of the outside gap give
`t_y·D_y = t_y·det K + t_y·KRy` and `t_z·D_z = t_z·det K + t_z·KRz`, so

  `det K + t_y·KRy + t_z·KRz = t_y·D_y + t_z·D_z + (1 − t_y − t_z)·det K` .

On the both-light cell the seventh floor is exactly `det K ≤ 0`, and the
coefficient `1 − t_y − t_z` is positive, so the core is at most
`t_y·D_y + t_z·D_z` (`Gtz.corner_bothLight_core_bound`).

## What remains of the obligation

After this bound the collision reads: on the floors region

  `Π_d(1−t_d)·det M_o ≤ t_y·det A_y + t_z·det A_z + REST` ,

with `REST = t_x·KRx + t_xt_y·CRy + t_xt_z·CRz + t_yt_z(1+λ)·kxx
+ t_xt_yt_z(1+λ)` the five light terms.  The remaining fight is the
comparison of `t_y·det A_y + t_z·det A_z + REST` against the left side —
measured five orders of slack at the roof, carried by the outside floors.
-/

namespace Gtz

open Matrix Finset

/-- The permuted corner triple is the same triple. -/
theorem corner_triple_swap {x y z : Fin 6} :
    ({x, z, y} : Finset (Fin 6)) = {x, y, z} := by
  ext a
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- **THE OUTSIDE GAP DETERMINANT AT THE INSIDE ATOM.**  Erasing the inserted
atom from a positive definite four-set scales the determinant by one minus
its reading: `det K = det A_y·(1 − r_y)`. -/
theorem corner_outside_det_eq_fourSet_scale (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).det
      = (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det
        * (1 - D.atom y ⬝ᵥ
            ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
              *ᵥ D.atom y)) := by
  classical
  have hyK : y ∉ (({x, y, z} : Finset (Fin 6))ᶜ) := by simp
  have hdet : IsUnit (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hAy.det_pos)
  have herase := gapDet_erase D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) hdet
    (Finset.mem_insert_self y _)
  rwa [Finset.erase_insert hyK] at herase

/-- **THE CORE BOUND.**  On the both-light cell, under the seventh floor
`det K ≤ 0`, the heavy core of the weight-gap law is at most the weighted
four-set determinants:

  `det K + t_y·g_yᵀ(adj K)g_y + t_z·g_zᵀ(adj K)g_z
     ≤ t_y·det A_y + t_z·det A_z` . -/
theorem corner_bothLight_core_bound (D : WeightedDesign 6 3)
    {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hK : (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).det ≤ 0) :
    (subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).det
      + D.weight y * (D.atom y ⬝ᵥ
          ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).adjugate
            *ᵥ D.atom y))
      + D.weight z * (D.atom z ⬝ᵥ
          ((subsetSum D (({x, y, z} : Finset (Fin 6))ᶜ) - 1).adjugate
            *ᵥ D.atom z))
      ≤ D.weight y
          * (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det
        + D.weight z
          * (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det := by
  classical
  -- the y-side pieces
  have hKRy := corner_oneAxisZero_heavyInside_KRy_eq D hxy hxz hyz hAy
  have hdKy := corner_outside_det_eq_fourSet_scale D hxy hxz hyz hAy
  -- the z-side pieces, through the permuted triple
  have hxz' : x ≠ z := hxz
  have hzy : z ≠ y := Ne.symm hyz
  have hAz' : (subsetSum D (insert z (({x, z, y} : Finset (Fin 6))ᶜ)) - 1).PosDef := by
    rwa [corner_triple_swap]
  have hKRz := corner_oneAxisZero_heavyInside_KRy_eq D hxz' hxy hzy hAz'
  have hdKz := corner_outside_det_eq_fourSet_scale D hxz' hxy hzy hAz'
  rw [corner_triple_swap] at hKRz hdKz
  -- weights are in the simplex
  have hty : 0 < D.weight y := D.weight_pos y
  have htz : 0 < D.weight z := D.weight_pos z
  have htyz : D.weight y + D.weight z ≤ 1 := by
    have hsum := D.weight_sum_one
    have hle : D.weight y + D.weight z ≤ ∑ c, D.weight c := by
      have hyz' : y ≠ z := hyz
      rw [← Finset.sum_pair hyz']
      exact Finset.sum_le_sum_of_subset_of_nonneg
        (Finset.subset_univ _) (fun c _ _ => (D.weight_pos c).le)
    linarith
  -- assemble: ty*Dy = ty*detK + ty*KRy and tz*Dz = tz*detK + tz*KRz
  nlinarith [hKRy, hKRz, hdKy, hdKz, hK,
    mul_nonneg hty.le (neg_nonneg.mpr hK), mul_nonneg htz.le (neg_nonneg.mpr hK)]

end Gtz
