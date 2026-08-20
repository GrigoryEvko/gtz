import Gtz.Wave.FloorsForceExcess

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The sharpened S-floor with the erased reading eliminated

The sharpened S-floor (`Gtz.corner_oneAxisZero_heavyInside_sFloor_sharp`)
reads

  `(1 − t_y)·ρ² ≤ S·(1 + r_z)` ,  `S = t_x(r_x − 1) + t_z(r_z − 1)` ,

and the erased reading `r_x` is the one quantity of that clause which the
weights already control: on the heavy-inside cell the paid four-set at the
outside TOTAL caps it with no hypotheses at all
(`Gtz.corner_oneAxisZero_heavyInside_erased_cap_auto`):

  `r_x ≤ (1 − t_x − t_y − t_z)/(t_y + t_z)` .

Substituting removes `r_x` from the clause entirely
(`Gtz.corner_oneAxisZero_heavyInside_sFloor_capped`):

  `(1 − t_y)·ρ² ≤ (t_x·((1 − t_x − t_y − t_z)/(t_y + t_z) − 1)
                    + t_z·(r_z − 1))·(1 + r_z)` .

The clause now involves only the weights, the excluded inside reading `r_z`
and the cross reading `ρ`.  For a certificate search this matters twice: the
variable count of the system drops by one, and the eliminated variable was
the one whose channel — the erased direction — carries the largest dynamic
range of the whole cell.
-/

namespace Gtz

open Matrix Finset

/-- **THE CAPPED SHARP FLOOR.**  The sharpened S-floor with the erased
reading replaced by its hypothesis-free cap: at a heavy-inside tie the
squared cross reading is bounded by weights and the excluded inside reading
alone. -/
theorem corner_oneAxisZero_heavyInside_sFloor_capped (D : WeightedDesign 6 3)
    (htie : IsTie D) {x y z : Fin 6} (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    {lam : ℝ} (hlam : 0 < lam) {u : Fin 3 → ℝ} (hunit : u ⬝ᵥ u = 1)
    (hgap : subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u)
    (hax : D.atom x ⬝ᵥ u = 0) (haz : D.atom z ⬝ᵥ u ≠ 0)
    (hnotz : ¬ (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef) :
    (1 - D.weight y)
        * (D.atom y ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z)) ^ 2
      ≤ (D.weight x
            * ((1 - D.weight x - D.weight y - D.weight z)
                / (D.weight y + D.weight z) - 1)
          + D.weight z
            * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z) - 1))
        * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom z)) := by
  have hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  have hsharp := corner_oneAxisZero_heavyInside_sFloor_sharp D htie hxy hxz hyz
    hlam hunit hgap hax haz hnotz
  have hcap := corner_oneAxisZero_heavyInside_erased_cap_auto D hxy hxz hyz
    hlam hunit hgap hax haz hnotz
  have hrz0 : 0 ≤ D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hAy.inv.posSemidef).2
      (D.atom z)
    rwa [star_trivial] at h
  have hpos : (0 : ℝ) < 1 + D.atom z ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom z) := by linarith
  have hstep : D.weight x
        * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
            - 1)⁻¹ *ᵥ D.atom x) - 1)
      ≤ D.weight x
        * ((1 - D.weight x - D.weight y - D.weight z)
            / (D.weight y + D.weight z) - 1) := by
    have := mul_le_mul_of_nonneg_left hcap (D.weight_pos x).le
    linarith
  nlinarith [hsharp, hstep, hpos]

end Gtz
