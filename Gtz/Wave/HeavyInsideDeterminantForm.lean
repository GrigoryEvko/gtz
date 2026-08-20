import Gtz.Wave.ReadingMatrixRelation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The heavy-inside residual with every inverse removed

A member floor is a DETERMINANT SIGN.  For a subset `F` whose gap
`A = S_F − 1` is invertible and a member `d ∈ F`, the erased gap is a
rank-one downdate of `A`, so the determinant lemma gives
(`Gtz.gapDet_erase`)

  `det(S_{F∖d} − 1) = det(S_F − 1) · (1 − r_d)` ,   `r_d = g_dᵀA⁻¹g_d` .

When the gap is positive definite the determinant on the right is positive,
so (`Gtz.member_floor_iff_gapDet_erase_nonpos`)

  `r_d ≥ 1  ↔  det(S_{F∖d} − 1) ≤ 0` .

The floor of a member is exactly the FAILURE of the triple that drops it.

## What this buys the heavy-inside residual

Composed with the residual bridge, the whole target loses its matrix
inverses (`Gtz.oneAxisZeroHeavyInsideResidual_of_determinants`): what is
left is five determinant signs at the corner,

  `S_F − 1 ≻ 0` ,  `det(S_{F'} − 1) ≤ 0` ,  `det(S_{F∖d} − 1) ≤ 0` (three
  outside `d`) ,

with `F = {y} ∪ Cᶜ` the surviving four-set and `F' = {z} ∪ Cᶜ` the failed
one.  Each determinant is a POLYNOMIAL in the atoms — by Cauchy-Binet a
signed sum of squares of Gram minors — so the certificate arena is
polynomial in the atom coordinates and the weights, with no inverse, no
adjugate and no quotient anywhere.

The reading form and the determinant form say the same thing, but only the
determinant form is a Positivstellensatz problem as written.
-/

namespace Gtz

open Matrix Finset

variable {m k : ℕ}

/-! ## 1. The erased gap is a rank-one downdate -/

/-- **THE ERASED GAP DETERMINANT.**  Dropping the member `d` scales the gap
determinant by one minus that member's reading:

  `det(S_{F∖d} − 1) = det(S_F − 1)·(1 − r_d)` . -/
theorem gapDet_erase (D : WeightedDesign m k) (F : Finset (Fin m))
    (hdet : IsUnit (subsetSum D F - 1).det) {d : Fin m} (hd : d ∈ F) :
    (subsetSum D (F.erase d) - 1).det
      = (subsetSum D F - 1).det
        * (1 - D.atom d ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom d)) := by
  have herase : subsetSum D (F.erase d) - 1
      = (subsetSum D F - 1) - atomMatrix (D.atom d) := by
    have hsum := Finset.sum_erase_add F (fun c => atomMatrix (D.atom c)) hd
    rw [subsetSum, subsetSum, ← hsum]
    abel
  rw [herase, det_sub_atomMatrix hdet]

/-- **THE FLOOR IS A DETERMINANT SIGN.**  At a positive definite gap the
member floor `r_d ≥ 1` says exactly that the subset without `d` fails:

  `r_d ≥ 1  ↔  det(S_{F∖d} − 1) ≤ 0` . -/
theorem member_floor_iff_gapDet_erase_nonpos (D : WeightedDesign m k)
    {F : Finset (Fin m)} (hpd : (subsetSum D F - 1).PosDef)
    {d : Fin m} (hd : d ∈ F) :
    1 ≤ D.atom d ⬝ᵥ ((subsetSum D F - 1)⁻¹ *ᵥ D.atom d)
      ↔ (subsetSum D (F.erase d) - 1).det ≤ 0 := by
  have hdet : IsUnit (subsetSum D F - 1).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  rw [gapDet_erase D F hdet hd]
  constructor
  · intro hfloor
    exact mul_nonpos_of_nonneg_of_nonpos hpd.det_pos.le (by linarith)
  · intro hnp
    by_contra hcon
    rw [not_le] at hcon
    exact absurd hnp (not_le.mpr (mul_pos hpd.det_pos (by linarith)))

/-! ## 2. The heavy-inside residual as five determinant signs -/

/-- **THE DETERMINANT FORM OF THE RESIDUAL.**  To discharge the heavy-inside
residual it is enough to refute a system with no matrix inverse in it: the
corner, the surviving four-set positive definite, the failed four-set with
nonpositive gap determinant, and the three outside triples with nonpositive
gap determinants.  The excluded-pair excess is supplied for free, because
the floors force it. -/
theorem oneAxisZeroHeavyInsideResidual_of_determinants
    (hpoly : ∀ (D : WeightedDesign 6 3) (x y z : Fin 6), x ≠ y → x ≠ z → y ≠ z →
      ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 →
      subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u →
      D.atom x ⬝ᵥ u = 0 → D.atom z ⬝ᵥ u ≠ 0 →
      (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef →
      (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).det ≤ 0 →
      0 ≤ D.weight x
            * (D.atom x ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom x) - 1)
          + D.weight z
            * (D.atom z ⬝ᵥ ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ))
                - 1)⁻¹ *ᵥ D.atom z) - 1) →
      (∀ d ∈ (({x, y, z} : Finset (Fin 6))ᶜ),
        (subsetSum D ((insert y (({x, y, z} : Finset (Fin 6))ᶜ)).erase d) - 1).det
          ≤ 0) →
      False) :
    OneAxisZeroHeavyInsideResidual := by
  classical
  refine oneAxisZeroHeavyInsideResidual_of_geometry ?_
  intro D x y z hxy hxz hyz lam hlam u hunit hgap hax haz hnotz hexcess hfloors
  set K : Finset (Fin 6) := (({x, y, z} : Finset (Fin 6))ᶜ) with hK
  have hAy : (subsetSum D (insert y K) - 1).PosDef :=
    (corner_oneAxisZero_fourSet_split D hxy hxz hyz hlam hunit hgap hax
      haz).resolve_left hnotz
  -- the failed four-set is a two-sided update of the surviving one
  have hyK : y ∉ K := by rw [hK]; simp
  have hzK : z ∉ K := by rw [hK]; simp
  have hAzAy : subsetSum D (insert z K) - 1
      = (subsetSum D (insert y K) - 1)
        - atomMatrix (D.atom y) + atomMatrix (D.atom z) := by
    rw [subsetSum_insert_sub_one D hyK, subsetSum_insert_sub_one D hzK]
    abel
  have hself := corner_oneAxisZero_heavyInside_selfRead D hxy hxz hyz hlam hunit
    hgap hax haz hnotz
  have hdetz : (subsetSum D (insert z K) - 1).det ≤ 0 := by
    rw [hAzAy, det_sub_add_atomMatrix_readings hAy]
    have hneg : (1 - D.atom y ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom y))
          * (1 + D.atom z ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom z))
        + (D.atom y ⬝ᵥ ((subsetSum D (insert y K) - 1)⁻¹ *ᵥ D.atom z)) ^ 2
        ≤ 0 := by nlinarith [hself]
    exact mul_nonpos_of_nonneg_of_nonpos hAy.det_pos.le hneg
  -- every outside floor becomes a determinant sign
  have hdets : ∀ d ∈ K,
      (subsetSum D ((insert y K).erase d) - 1).det ≤ 0 := by
    intro d hd
    exact (member_floor_iff_gapDet_erase_nonpos D hAy
      (Finset.mem_insert_of_mem hd)).mp (hfloors d hd)
  exact hpoly D x y z hxy hxz hyz lam hlam u hunit hgap hax haz hAy hdetz
    hexcess hdets

end Gtz
