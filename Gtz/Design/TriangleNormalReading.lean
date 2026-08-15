import Gtz.Design.StarWallResidualRows

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The triangle-normal readings of the K4 chart

Each of the four triangles of `K4` has a normal direction on which the three
triangle labels read zero.  The chart gap at such a probe therefore keeps only
the three complementary labels, and the reading becomes a scalar inequality
between one boost sum and one mass sum.

* `kFourAllOnes_reading` is the reading at the normal of the triangle
  `{0, 1, 2}`.  The three triangle labels drop out and the gap reads the
  selected boost of the star labels against the star mass.
* `kFourStarBoost_gt_of_posDef` is the necessary condition it produces: a
  positive definite selection carries selected boost above the star mass.
* `kFourSingleStarEdge_boost_gt_of_posDef` is the form the atlas consumes.  A
  spanning tree that meets the star `{3, 4, 5}` in the single label `k` needs
  the boost of `k` alone to exceed the whole star mass.

The three remaining triangles read through the coordinate probes and give the
sibling statements `kFourCoordOne_reading` and its two mirrors.

No wall hypothesis is used anywhere in this module.  The readings hold at every
chart point, so they prune the atlas before any wall analysis begins.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The normal of the triangle `{0, 1, 2}` -/

/-- The normal of the triangle `{0, 1, 2}`. -/
def kFourAllOnes : Fin 3 → ℝ := ![1, 1, 1]

theorem kFourAllOnes_ne_zero : kFourAllOnes ≠ 0 := by
  intro hzero
  have hone : kFourAllOnes 0 = 0 := by rw [hzero]; rfl
  simp [kFourAllOnes] at hone

theorem kFourDirection_dot_allOnes_zero :
    kFourDirection 0 ⬝ᵥ kFourAllOnes = 0 := by
  simp [kFourDirection, kFourAllOnes, dotProduct, Fin.sum_univ_three]

theorem kFourDirection_dot_allOnes_one :
    kFourDirection 1 ⬝ᵥ kFourAllOnes = 0 := by
  simp [kFourDirection, kFourAllOnes, dotProduct, Fin.sum_univ_three]

theorem kFourDirection_dot_allOnes_two :
    kFourDirection 2 ⬝ᵥ kFourAllOnes = 0 := by
  simp [kFourDirection, kFourAllOnes, dotProduct, Fin.sum_univ_three]

theorem kFourDirection_dot_allOnes_three :
    kFourDirection 3 ⬝ᵥ kFourAllOnes = 1 := by
  simp [kFourDirection, kFourAllOnes, dotProduct, Fin.sum_univ_three]

theorem kFourDirection_dot_allOnes_four :
    kFourDirection 4 ⬝ᵥ kFourAllOnes = 1 := by
  simp [kFourDirection, kFourAllOnes, dotProduct, Fin.sum_univ_three]

theorem kFourDirection_dot_allOnes_five :
    kFourDirection 5 ⬝ᵥ kFourAllOnes = 1 := by
  simp [kFourDirection, kFourAllOnes, dotProduct, Fin.sum_univ_three]

/-- **THE ALL-ONES READING.**  At the normal of the triangle `{0, 1, 2}` the
three triangle labels read zero, so the chart gap reads the selected boost of
the star labels against the total star mass. -/
theorem kFourAllOnes_reading (mass weight : Fin 6 → ℝ) (selected : Finset (Fin 6)) :
    kFourAllOnes ⬝ᵥ (directionChartGap kFourDirection mass weight selected
        *ᵥ kFourAllOnes)
      = (∑ label ∈ selected,
          mass label / weight label * (kFourDirection label ⬝ᵥ kFourAllOnes) ^ 2)
        - (mass 3 + mass 4 + mass 5) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  congr 1
  rw [Fin.sum_univ_six, kFourDirection_dot_allOnes_zero, kFourDirection_dot_allOnes_one,
    kFourDirection_dot_allOnes_two, kFourDirection_dot_allOnes_three,
    kFourDirection_dot_allOnes_four, kFourDirection_dot_allOnes_five]
  ring

/-- **THE STAR-MASS FLOOR.**  A positive definite selection carries selected
boost, read at the triangle normal, strictly above the total star mass. -/
theorem kFourStarBoost_gt_of_posDef (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection mass weight selected).PosDef) :
    mass 3 + mass 4 + mass 5
      < ∑ label ∈ selected,
          mass label / weight label * (kFourDirection label ⬝ᵥ kFourAllOnes) ^ 2 := by
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 kFourAllOnes_ne_zero
  rw [star_trivial, kFourAllOnes_reading] at hpos
  linarith

/-! ## 2. The form the atlas consumes -/

/-- **THE SINGLE STAR EDGE.**  A selection meeting the star `{3, 4, 5}` in the
single label `starEdge`, with every other selected label a triangle label,
needs the boost of `starEdge` alone above the whole star mass.

This prunes the atlas before any wall analysis: only a star label whose own
boost clears the star mass can appear in a firing cell. -/
theorem kFourSingleStarEdge_boost_gt_of_posDef (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) (starEdge : Fin 6)
    (hmem : starEdge ∈ selected)
    (hstar : starEdge = 3 ∨ starEdge = 4 ∨ starEdge = 5)
    (htriangle : ∀ label ∈ selected, label ≠ starEdge →
      label = 0 ∨ label = 1 ∨ label = 2)
    (hpd : (directionChartGap kFourDirection mass weight selected).PosDef) :
    mass 3 + mass 4 + mass 5 < mass starEdge / weight starEdge := by
  have hsum : (∑ label ∈ selected,
      mass label / weight label * (kFourDirection label ⬝ᵥ kFourAllOnes) ^ 2)
      = mass starEdge / weight starEdge := by
    rw [Finset.sum_eq_single starEdge]
    · rcases hstar with h | h | h <;> subst h
      · rw [kFourDirection_dot_allOnes_three]; ring
      · rw [kFourDirection_dot_allOnes_four]; ring
      · rw [kFourDirection_dot_allOnes_five]; ring
    · intro label hlabel hne
      rcases htriangle label hlabel hne with h | h | h <;> subst h
      · rw [kFourDirection_dot_allOnes_zero]; ring
      · rw [kFourDirection_dot_allOnes_one]; ring
      · rw [kFourDirection_dot_allOnes_two]; ring
    · intro hnot
      exact absurd hmem hnot
  have hgt := kFourStarBoost_gt_of_posDef mass weight selected hpd
  rw [hsum] at hgt
  exact hgt

/-! ## 3. The sibling triangle `{2, 4, 5}` -/

/-- The normal of the triangle `{2, 4, 5}`. -/
def kFourCoordOne : Fin 3 → ℝ := ![1, 0, 0]

theorem kFourCoordOne_ne_zero : kFourCoordOne ≠ 0 := by
  intro hzero
  have hone : kFourCoordOne 0 = 0 := by rw [hzero]; rfl
  simp [kFourCoordOne] at hone

theorem kFourDirection_dot_coordOne_two :
    kFourDirection 2 ⬝ᵥ kFourCoordOne = 0 := by
  simp [kFourDirection, kFourCoordOne, dotProduct, Fin.sum_univ_three]

theorem kFourDirection_dot_coordOne_four :
    kFourDirection 4 ⬝ᵥ kFourCoordOne = 0 := by
  simp [kFourDirection, kFourCoordOne, dotProduct, Fin.sum_univ_three]

theorem kFourDirection_dot_coordOne_five :
    kFourDirection 5 ⬝ᵥ kFourCoordOne = 0 := by
  simp [kFourDirection, kFourCoordOne, dotProduct, Fin.sum_univ_three]

/-- **THE COORDINATE READING.**  At the normal of the triangle `{2, 4, 5}` the
three labels of that triangle read zero, and the gap reads the selected boost of
the complementary labels against their mass. -/
theorem kFourCoordOne_reading (mass weight : Fin 6 → ℝ) (selected : Finset (Fin 6)) :
    kFourCoordOne ⬝ᵥ (directionChartGap kFourDirection mass weight selected
        *ᵥ kFourCoordOne)
      = (∑ label ∈ selected,
          mass label / weight label * (kFourDirection label ⬝ᵥ kFourCoordOne) ^ 2)
        - (mass 0 + mass 1 + mass 3) := by
  rw [dotProduct_directionChartGap_mulVec_eq]
  congr 1
  rw [Fin.sum_univ_six, kFourDirection_dot_coordOne_two, kFourDirection_dot_coordOne_four,
    kFourDirection_dot_coordOne_five]
  have h0 : kFourDirection 0 ⬝ᵥ kFourCoordOne = 1 := by
    simp [kFourDirection, kFourCoordOne, dotProduct, Fin.sum_univ_three]
  have h1 : kFourDirection 1 ⬝ᵥ kFourCoordOne = 1 := by
    simp [kFourDirection, kFourCoordOne, dotProduct, Fin.sum_univ_three]
  have h3 : kFourDirection 3 ⬝ᵥ kFourCoordOne = 1 := by
    simp [kFourDirection, kFourCoordOne, dotProduct, Fin.sum_univ_three]
  rw [h0, h1, h3]
  ring

/-- The mass floor carried by the sibling triangle normal. -/
theorem kFourCoordOneBoost_gt_of_posDef (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6))
    (hpd : (directionChartGap kFourDirection mass weight selected).PosDef) :
    mass 0 + mass 1 + mass 3
      < ∑ label ∈ selected,
          mass label / weight label * (kFourDirection label ⬝ᵥ kFourCoordOne) ^ 2 := by
  have hpos := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 kFourCoordOne_ne_zero
  rw [star_trivial, kFourCoordOne_reading] at hpos
  linarith

end Gtz
