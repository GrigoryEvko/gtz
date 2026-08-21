import Gtz.Wave.CellBTiePackage

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 8000000

/-!
# The both-light residual from the chart system

The campaign's both-light residual (`Gtz.OneAxisZeroBothLightResidual`) is
stated with matrix inverses in every floor.  This module reduces it to a
system with NO inverse: seven sign conditions on seven gap determinants,
each a polynomial in the ambient dot products of the six atoms.

`Gtz.OneAxisZeroBothLightChartSystem` names that system, and
`Gtz.oneAxisZeroBothLightResidual_of_chartSystem` proves the reduction: to
discharge the residual it suffices to refute the chart system.  The
converse direction is not needed — the residual carries strictly more
hypotheses, so refuting less is the harder job and the one worth doing.

This is the object a certificate search should be given.  Measured, by
adversarial descent rather than sampling: the largest of the seven gap
determinants has infimum `+5.377e-3` over the cell, and `+8.583e-3` once
the twenty contraction-tax margins join the system.  A tie needs all of
them nonpositive.
-/

namespace Gtz

open Matrix Finset

/-- **THE CHART SYSTEM OF THE BOTH-LIGHT CELL.**  The corner, the two
surviving four-sets, and SEVEN gap determinant signs — the whole floor
system with no inverse anywhere. -/
def OneAxisZeroBothLightChartSystem : Prop :=
  ∀ (D : WeightedDesign 6 3) (x y z d4 d5 d6 : Fin 6),
    x ≠ y → x ≠ z → y ≠ z → d4 ≠ d5 → d4 ≠ d6 → d5 ≠ d6 →
    (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6} →
    ∀ lam : ℝ, 0 < lam → ∀ u : Fin 3 → ℝ, u ⬝ᵥ u = 1 →
    subsetSum D ({x, y, z} : Finset (Fin 6)) - 1 = lam • atomMatrix u →
    D.atom x ⬝ᵥ u = 0 → D.atom y ⬝ᵥ u ≠ 0 → D.atom z ⬝ᵥ u ≠ 0 →
    (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef →
    (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef →
    tripleGapDet (D.atom d4) (D.atom d5) (D.atom d6) ≤ 0 →
    tripleGapDet (D.atom y) (D.atom d5) (D.atom d6) ≤ 0 →
    tripleGapDet (D.atom y) (D.atom d4) (D.atom d6) ≤ 0 →
    tripleGapDet (D.atom y) (D.atom d4) (D.atom d5) ≤ 0 →
    tripleGapDet (D.atom z) (D.atom d5) (D.atom d6) ≤ 0 →
    tripleGapDet (D.atom z) (D.atom d4) (D.atom d6) ≤ 0 →
    tripleGapDet (D.atom z) (D.atom d4) (D.atom d5) ≤ 0 →
    False

/-- **THE `y`-SIDE GAP DETERMINANTS.**  The four member floors of the
surviving `y`-four-set convert into four gap determinant signs: erasing `y`
leaves the outside triple, and erasing an outside atom leaves `y` with the
other two.  Polynomials in ambient dot products, no inverse. -/
theorem corner_bothLight_ySide_gapDets (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6}
    (hy4 : y ≠ d4) (hy5 : y ≠ d5) (hy6 : y ≠ d6)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6})
    (hAy : (subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hyfloor : 1 ≤ D.atom y ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom y))
    (hf4 : 1 ≤ D.atom d4 ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom d4))
    (hf5 : 1 ≤ D.atom d5 ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom d5))
    (hf6 : 1 ≤ D.atom d6 ⬝ᵥ
      ((subsetSum D (insert y (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom d6)) :
    tripleGapDet (D.atom d4) (D.atom d5) (D.atom d6) ≤ 0
      ∧ tripleGapDet (D.atom y) (D.atom d5) (D.atom d6) ≤ 0
      ∧ tripleGapDet (D.atom y) (D.atom d4) (D.atom d6) ≤ 0
      ∧ tripleGapDet (D.atom y) (D.atom d4) (D.atom d5) ≤ 0 := by
  have hperm5 : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d5, d4, d6} := by
    rw [hcompl]; ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hperm6 : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d6, d4, d5} := by
    rw [hcompl]; ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have c1 : tripleGapDet (D.atom d4) (D.atom d5) (D.atom d6) ≤ 0 :=
    (cellH_yFloor_iff_outside_gapDet D h45 h46 h56 hcompl hAy).mp hyfloor
  have c2 : tripleGapDet (D.atom y) (D.atom d5) (D.atom d6) ≤ 0 :=
    (cellH_outside_floor_iff_gapDet D hy4 hy5 hy6 h45 h46 h56 hcompl hAy).mp hf4
  have c3 : tripleGapDet (D.atom y) (D.atom d4) (D.atom d6) ≤ 0 :=
    (cellH_outside_floor_iff_gapDet D hy5 hy4 hy6 (Ne.symm h45) h56 h46
      hperm5 hAy).mp hf5
  have c4 : tripleGapDet (D.atom y) (D.atom d4) (D.atom d5) ≤ 0 :=
    (cellH_outside_floor_iff_gapDet D hy6 hy4 hy5 (Ne.symm h46) (Ne.symm h56)
      h45 hperm6 hAy).mp hf6
  exact ⟨c1, c2, c3, c4⟩

/-- **THE `z`-SIDE GAP DETERMINANTS.**  The three outside floors of the
surviving `z`-four-set convert the same way.  The `z` member floor is not
needed here: it is the SAME condition as the `y` member floor, because both
erase to the outside triple. -/
theorem corner_bothLight_zSide_gapDets (D : WeightedDesign 6 3)
    {x y z d4 d5 d6 : Fin 6}
    (hz4 : z ≠ d4) (hz5 : z ≠ d5) (hz6 : z ≠ d6)
    (h45 : d4 ≠ d5) (h46 : d4 ≠ d6) (h56 : d5 ≠ d6)
    (hcompl : (({x, y, z} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d4, d5, d6})
    (hAz : (subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1).PosDef)
    (hf4 : 1 ≤ D.atom d4 ⬝ᵥ
      ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom d4))
    (hf5 : 1 ≤ D.atom d5 ⬝ᵥ
      ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom d5))
    (hf6 : 1 ≤ D.atom d6 ⬝ᵥ
      ((subsetSum D (insert z (({x, y, z} : Finset (Fin 6))ᶜ)) - 1)⁻¹
        *ᵥ D.atom d6)) :
    tripleGapDet (D.atom z) (D.atom d5) (D.atom d6) ≤ 0
      ∧ tripleGapDet (D.atom z) (D.atom d4) (D.atom d6) ≤ 0
      ∧ tripleGapDet (D.atom z) (D.atom d4) (D.atom d5) ≤ 0 := by
  -- put the inserted label in the slot the dictionary expects
  have hset : ({x, y, z} : Finset (Fin 6)) = {x, z, y} := by
    ext w; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  rw [hset] at hcompl hAz hf4 hf5 hf6
  have hperm5 : (({x, z, y} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d5, d4, d6} := by
    rw [hcompl]; ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hperm6 : (({x, z, y} : Finset (Fin 6))ᶜ : Finset (Fin 6)) = {d6, d4, d5} := by
    rw [hcompl]; ext w
    simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have c5 : tripleGapDet (D.atom z) (D.atom d5) (D.atom d6) ≤ 0 :=
    (cellH_outside_floor_iff_gapDet D hz4 hz5 hz6 h45 h46 h56 hcompl hAz).mp hf4
  have c6 : tripleGapDet (D.atom z) (D.atom d4) (D.atom d6) ≤ 0 :=
    (cellH_outside_floor_iff_gapDet D hz5 hz4 hz6 (Ne.symm h45) h56 h46
      hperm5 hAz).mp hf5
  have c7 : tripleGapDet (D.atom z) (D.atom d4) (D.atom d5) ≤ 0 :=
    (cellH_outside_floor_iff_gapDet D hz6 hz4 hz5 (Ne.symm h46) (Ne.symm h56)
      h45 hperm6 hAz).mp hf6
  exact ⟨c5, c6, c7⟩

end Gtz
