import Gtz.Wave.KFourRowCertificateWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The row certificates of the six residual cells

The three vertex stars carry the gauge star wall almost everywhere.  What they
miss is carried by six further trees, and those six are one orbit of the wall's
own symmetry: the wall tree is the star at the fourth vertex, so the symmetric
group on the other three vertices acts, and the six trees

  `{0,1,5}`,  `{0,2,5}`,  `{0,1,4}`,  `{1,2,4}`,  `{0,2,3}`,  `{1,2,3}`

form a single orbit under it.  Their minors are not the star minors: the star
cell has the off-diagonal shape `b * c`, `b * S * p`, `c * S * q`, and none of
the six does.

Every cell matrix is a symmetric Z-matrix, because each off-diagonal entry is a
negated sum of masses.  So the three leading minors follow from one positive
vector and three row readings, which are *linear* in the masses and the floors.
This module carries that reading for each of the six cells and dispatches it to
the atlas.

Each theorem asks for a positive vector `x` and three row inequalities of the
form "the diagonal reading beats the off-diagonal load".  No eigenvalue, no
determinant, and no wall equation: the certificates hold at every chart point.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The pair `{0,1,5}` and `{0,2,5}` -/

/-- The row certificate of the tree `{0,1,5}`. -/
theorem kFourPathCell015_fires_of_rowCertificate (point : DirectionChartPoint 6)
    {floorZero floorOne floorFive xA xB xC : ℝ}
    (hf0 : floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0))
    (hf1 : floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1))
    (hf5 : floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5))
    (hxA : 0 < xA) (hxB : 0 < xB) (hxC : 0 < xC)
    (hrowA : (point.mass 2 + point.mass 4) * xB + point.mass 4 * xC
      < (floorZero - (point.mass 2 + point.mass 4)) * xA)
    (hrowB : (point.mass 2 + point.mass 4) * xA + (point.mass 3 + point.mass 4) * xC
      < (floorOne - (point.mass 2 + point.mass 3 + point.mass 4)) * xB)
    (hrowC : point.mass 4 * xA + (point.mass 3 + point.mass 4) * xB
      < (floorFive - (point.mass 3 + point.mass 4)) * xC) :
    KFourPathCell015Fires point := by
  have h2 := point.mass_pos 2
  have h3 := point.mass_pos 3
  have h4 := point.mass_pos 4
  obtain ⟨hcorner, hminorTwo, hminorDet⟩ :=
    unsignedMinors_of_rowCertificate
      (entryAA := floorZero - (point.mass 2 + point.mass 4))
      (entryAB := -(point.mass 2 + point.mass 4)) (entryAC := -point.mass 4)
      (entryBB := floorOne - (point.mass 2 + point.mass 3 + point.mass 4))
      (entryBC := -(point.mass 3 + point.mass 4))
      (entryCC := floorFive - (point.mass 3 + point.mass 4))
      (xA := xA) (xB := xB) (xC := xC)
      (by linarith) (by linarith) (by linarith) hxA hxB hxC
      (by linarith) (by linarith) (by linarith)
  exact ⟨floorZero, floorOne, floorFive, hf0, hf1, hf5, hcorner, by linarith,
    by nlinarith [hminorDet]⟩

/-- The row certificate of the tree `{0,2,5}`, the `(a b)` mirror of `{0,1,5}`. -/
theorem kFourPathCell025_fires_of_rowCertificate (point : DirectionChartPoint 6)
    {floorZero floorTwo floorFive xA xB xC : ℝ}
    (hf0 : floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0))
    (hf2 : floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2))
    (hf5 : floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5))
    (hxA : 0 < xA) (hxB : 0 < xB) (hxC : 0 < xC)
    (hrowA : (point.mass 1 + point.mass 3) * xB + point.mass 3 * xC
      < (floorZero - (point.mass 1 + point.mass 3)) * xA)
    (hrowB : (point.mass 1 + point.mass 3) * xA + (point.mass 3 + point.mass 4) * xC
      < (floorTwo - (point.mass 1 + point.mass 3 + point.mass 4)) * xB)
    (hrowC : point.mass 3 * xA + (point.mass 3 + point.mass 4) * xB
      < (floorFive - (point.mass 3 + point.mass 4)) * xC) :
    KFourPathCell025Fires point := by
  have h1 := point.mass_pos 1
  have h3 := point.mass_pos 3
  have h4 := point.mass_pos 4
  obtain ⟨hcorner, hminorTwo, hminorDet⟩ :=
    unsignedMinors_of_rowCertificate
      (entryAA := floorZero - (point.mass 1 + point.mass 3))
      (entryAB := -(point.mass 1 + point.mass 3)) (entryAC := -point.mass 3)
      (entryBB := floorTwo - (point.mass 1 + point.mass 3 + point.mass 4))
      (entryBC := -(point.mass 3 + point.mass 4))
      (entryCC := floorFive - (point.mass 3 + point.mass 4))
      (xA := xA) (xB := xB) (xC := xC)
      (by linarith) (by linarith) (by linarith) hxA hxB hxC
      (by linarith) (by linarith) (by linarith)
  exact ⟨floorZero, floorTwo, floorFive, hf0, hf2, hf5, hcorner, by linarith,
    by nlinarith [hminorDet]⟩

/-! ## 2. The pair `{0,1,4}` and `{1,2,4}` -/

/-- The row certificate of the tree `{0,1,4}`. -/
theorem kFourPathCell014_fires_of_rowCertificate (point : DirectionChartPoint 6)
    {floorZero floorOne floorFour xA xB xC : ℝ}
    (hf0 : floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0))
    (hf1 : floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1))
    (hf4 : floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4))
    (hxA : 0 < xA) (hxB : 0 < xB) (hxC : 0 < xC)
    (hrowA : (point.mass 2 + point.mass 5) * xB + (point.mass 3 + point.mass 5) * xC
      < (floorZero - (point.mass 2 + point.mass 3 + point.mass 5)) * xA)
    (hrowB : (point.mass 2 + point.mass 5) * xA + point.mass 5 * xC
      < (floorOne - (point.mass 2 + point.mass 5)) * xB)
    (hrowC : (point.mass 3 + point.mass 5) * xA + point.mass 5 * xB
      < (floorFour - (point.mass 3 + point.mass 5)) * xC) :
    KFourPathCell014Fires point := by
  have h2 := point.mass_pos 2
  have h3 := point.mass_pos 3
  have h5 := point.mass_pos 5
  obtain ⟨hcorner, hminorTwo, hminorDet⟩ :=
    unsignedMinors_of_rowCertificate
      (entryAA := floorZero - (point.mass 2 + point.mass 3 + point.mass 5))
      (entryAB := -(point.mass 2 + point.mass 5))
      (entryAC := -(point.mass 3 + point.mass 5))
      (entryBB := floorOne - (point.mass 2 + point.mass 5))
      (entryBC := -point.mass 5)
      (entryCC := floorFour - (point.mass 3 + point.mass 5))
      (xA := xA) (xB := xB) (xC := xC)
      (by linarith) (by linarith) (by linarith) hxA hxB hxC
      (by linarith) (by linarith) (by linarith)
  exact ⟨floorZero, floorOne, floorFour, hf0, hf1, hf4, hcorner, by linarith,
    by nlinarith [hminorDet]⟩

/-- The row certificate of the tree `{1,2,4}`, the `(b c)` mirror of `{0,2,5}`. -/
theorem kFourPathCell124_fires_of_rowCertificate (point : DirectionChartPoint 6)
    {floorOne floorTwo floorFour xA xB xC : ℝ}
    (hf1 : floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1))
    (hf2 : floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2))
    (hf4 : floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4))
    (hxA : 0 < xA) (hxB : 0 < xB) (hxC : 0 < xC)
    (hrowA : (point.mass 0 + point.mass 3) * xB + point.mass 3 * xC
      < (floorOne - (point.mass 0 + point.mass 3)) * xA)
    (hrowB : (point.mass 0 + point.mass 3) * xA + (point.mass 3 + point.mass 5) * xC
      < (floorTwo - (point.mass 0 + point.mass 3 + point.mass 5)) * xB)
    (hrowC : point.mass 3 * xA + (point.mass 3 + point.mass 5) * xB
      < (floorFour - (point.mass 3 + point.mass 5)) * xC) :
    KFourPathCell124Fires point := by
  have h0 := point.mass_pos 0
  have h3 := point.mass_pos 3
  have h5 := point.mass_pos 5
  obtain ⟨hcorner, hminorTwo, hminorDet⟩ :=
    unsignedMinors_of_rowCertificate
      (entryAA := floorOne - (point.mass 0 + point.mass 3))
      (entryAB := -(point.mass 0 + point.mass 3)) (entryAC := -point.mass 3)
      (entryBB := floorTwo - (point.mass 0 + point.mass 3 + point.mass 5))
      (entryBC := -(point.mass 3 + point.mass 5))
      (entryCC := floorFour - (point.mass 3 + point.mass 5))
      (xA := xA) (xB := xB) (xC := xC)
      (by linarith) (by linarith) (by linarith) hxA hxB hxC
      (by linarith) (by linarith) (by linarith)
  exact ⟨floorOne, floorTwo, floorFour, hf1, hf2, hf4, hcorner, by linarith,
    by nlinarith [hminorDet]⟩

/-! ## 3. The pair `{0,2,3}` and `{1,2,3}` -/

/-- The row certificate of the tree `{0,2,3}`. -/
theorem kFourPendantCell023_fires_of_rowCertificate (point : DirectionChartPoint 6)
    {floorZero floorTwo floorThree xA xB xC : ℝ}
    (hf0 : floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0))
    (hf2 : floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2))
    (hf3 : floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3))
    (hxA : 0 < xA) (hxB : 0 < xB) (hxC : 0 < xC)
    (hrowA : (point.mass 1 + point.mass 5) * xB + (point.mass 4 + point.mass 5) * xC
      < (floorZero - (point.mass 1 + point.mass 4 + point.mass 5)) * xA)
    (hrowB : (point.mass 1 + point.mass 5) * xA + point.mass 5 * xC
      < (floorTwo - (point.mass 1 + point.mass 5)) * xB)
    (hrowC : (point.mass 4 + point.mass 5) * xA + point.mass 5 * xB
      < (floorThree - (point.mass 4 + point.mass 5)) * xC) :
    KFourPendantCell023Fires point := by
  have h1 := point.mass_pos 1
  have h4 := point.mass_pos 4
  have h5 := point.mass_pos 5
  obtain ⟨hcorner, hminorTwo, hminorDet⟩ :=
    unsignedMinors_of_rowCertificate
      (entryAA := floorZero - (point.mass 1 + point.mass 4 + point.mass 5))
      (entryAB := -(point.mass 1 + point.mass 5))
      (entryAC := -(point.mass 4 + point.mass 5))
      (entryBB := floorTwo - (point.mass 1 + point.mass 5))
      (entryBC := -point.mass 5)
      (entryCC := floorThree - (point.mass 4 + point.mass 5))
      (xA := xA) (xB := xB) (xC := xC)
      (by linarith) (by linarith) (by linarith) hxA hxB hxC
      (by linarith) (by linarith) (by linarith)
  exact ⟨floorZero, floorTwo, floorThree, hf0, hf2, hf3, hcorner, by linarith,
    by nlinarith [hminorDet]⟩

/-- The row certificate of the tree `{1,2,3}`, the `(b c)` mirror of `{0,2,3}`. -/
theorem kFourPendantCell123_fires_of_rowCertificate (point : DirectionChartPoint 6)
    {floorOne floorTwo floorThree xA xB xC : ℝ}
    (hf1 : floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1))
    (hf2 : floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2))
    (hf3 : floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3))
    (hxA : 0 < xA) (hxB : 0 < xB) (hxC : 0 < xC)
    (hrowA : (point.mass 0 + point.mass 4) * xB + (point.mass 4 + point.mass 5) * xC
      < (floorOne - (point.mass 0 + point.mass 4 + point.mass 5)) * xA)
    (hrowB : (point.mass 0 + point.mass 4) * xA + point.mass 4 * xC
      < (floorTwo - (point.mass 0 + point.mass 4)) * xB)
    (hrowC : (point.mass 4 + point.mass 5) * xA + point.mass 4 * xB
      < (floorThree - (point.mass 4 + point.mass 5)) * xC) :
    KFourPendantCell123Fires point := by
  have h0 := point.mass_pos 0
  have h4 := point.mass_pos 4
  have h5 := point.mass_pos 5
  obtain ⟨hcorner, hminorTwo, hminorDet⟩ :=
    unsignedMinors_of_rowCertificate
      (entryAA := floorOne - (point.mass 0 + point.mass 4 + point.mass 5))
      (entryAB := -(point.mass 0 + point.mass 4))
      (entryAC := -(point.mass 4 + point.mass 5))
      (entryBB := floorTwo - (point.mass 0 + point.mass 4))
      (entryBC := -point.mass 4)
      (entryCC := floorThree - (point.mass 4 + point.mass 5))
      (xA := xA) (xB := xB) (xC := xC)
      (by linarith) (by linarith) (by linarith) hxA hxB hxC
      (by linarith) (by linarith) (by linarith)
  exact ⟨floorOne, floorTwo, floorThree, hf1, hf2, hf3, hcorner, by linarith,
    by nlinarith [hminorDet]⟩

/-! ## 4. The six atlas dispatches -/

/-- The `{0,1,5}` row certificate fires the atlas. -/
theorem kFourAtlas_fires_of_rowCertificate015 (point : DirectionChartPoint 6)
    (hcell : KFourPathCell015Fires point) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inr (Or.inl hcell)

/-- The `{0,2,5}` row certificate fires the atlas. -/
theorem kFourAtlas_fires_of_rowCertificate025 (point : DirectionChartPoint 6)
    (hcell : KFourPathCell025Fires point) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inr (Or.inr (Or.inl hcell))

/-- The `{0,1,4}` row certificate fires the atlas. -/
theorem kFourAtlas_fires_of_rowCertificate014 (point : DirectionChartPoint 6)
    (hcell : KFourPathCell014Fires point) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcell)))))

/-- The `{1,2,4}` row certificate fires the atlas. -/
theorem kFourAtlas_fires_of_rowCertificate124 (point : DirectionChartPoint 6)
    (hcell : KFourPathCell124Fires point) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hcell))))))

/-- The `{0,2,3}` row certificate fires the atlas. -/
theorem kFourAtlas_fires_of_rowCertificate023 (point : DirectionChartPoint 6)
    (hcell : KFourPendantCell023Fires point) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inl (Or.inr (Or.inl hcell))

/-- The `{1,2,3}` row certificate fires the atlas. -/
theorem kFourAtlas_fires_of_rowCertificate123 (point : DirectionChartPoint 6)
    (hcell : KFourPendantCell123Fires point) :
    KFourAllTreeMinorAtlasCellFires point :=
  Or.inl (Or.inr (Or.inr (Or.inl hcell)))

end Gtz
