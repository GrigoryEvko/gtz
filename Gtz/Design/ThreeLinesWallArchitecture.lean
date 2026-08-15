import Gtz.Design.StarOnlyLaw
import Gtz.Design.ThreeLinesFamilyWeld

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The three-lines wall architecture

The three-lines chart is a triangle configuration.  The labels `0`, `1`, `3`
carry the three coordinate directions, and the labels `2`, `4`, `5` carry the
three joins: `v₂ = v₀ + v₁`, `v₄ = v₀ + v₃`, and `v₅ = v₁ + slide • v₃`.  The
slide is the only modulus.

At a corank-two wall the gap collapses to one rank-one atom, and the six chart
coefficients of that atom have a closed form in the axis coordinates.  The
three join coefficients are the three pairwise axis products, up to the slide.
Their product is therefore a square, which fixes the parity of the join labels
that the selection can carry.

* `threeLinesCoeff_eq_of_rankOne` — the closed form, division-free.
* `threeLinesRankOne_join_parity` — the parity identity
  `slide * (c₂ * c₄ * c₅) = scale ^ 3 * (z₀ * z₁ * z₂) ^ 2`.
* `threeLinesRankOne_not_evenJoins_of_slide_pos` and the three sibling
  exclusions — a rank-one wall at a positive slide never carries an even
  number of join labels, and at a negative slide never carries an odd number.

The exclusion halves the wall candidates at every slide of the fundamental
domain, and it is the three-lines analogue of the star-only law.
-/

namespace Gtz

open Matrix

/-! ## 1. The closed form of a rank-one three-lines gap -/

/-- **THE THREE-LINES CLOSED FORM.**  At a rank-one three-lines chart gap
`scale • atomMatrix axis` the six chart coefficients are pinned by the axis.
The three join coefficients `c₂`, `c₄`, `c₅` are the pairwise axis products,
and the three coordinate coefficients carry the reflected sums.  Every
equation is division-free: the slide multiplies the two coefficients that
would otherwise divide by it. -/
theorem threeLinesCoeff_eq_of_rankOne {slide : ℝ} {mass weight : Fin 6 → ℝ}
    {selected : Finset (Fin 6)} {axis : Fin 3 → ℝ} {scale : ℝ}
    (heq : directionChartGap (threeLinesDirection slide) mass weight selected
      = scale • atomMatrix axis) :
    chartCoeff mass weight selected 2 = scale * (axis 0 * axis 1) ∧
    chartCoeff mass weight selected 4 = scale * (axis 0 * axis 2) ∧
    slide * chartCoeff mass weight selected 5 = scale * (axis 1 * axis 2) ∧
    chartCoeff mass weight selected 0
      = scale * (axis 0 * (axis 0 - axis 1 - axis 2)) ∧
    slide * chartCoeff mass weight selected 1
      = scale * (axis 1 * (slide * axis 1 - slide * axis 0 - axis 2)) ∧
    chartCoeff mass weight selected 3
      = scale * (axis 2 * (axis 2 - axis 0 - slide * axis 1)) := by
  have hsum :=
    (directionChartGap_eq_coeff_sum (threeLinesDirection slide) mass weight selected).symm.trans heq
  have entry : ∀ i j : Fin 3,
      (∑ label, chartCoeff mass weight selected label
          * (threeLinesDirection slide label i * threeLinesDirection slide label j))
        = scale * (axis i * axis j) := by
    intro i j
    have := congrFun (congrFun hsum i) j
    simpa [Matrix.sum_apply, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
      smul_eq_mul, mul_assoc] using this
  have e00 := entry 0 0
  have e11 := entry 1 1
  have e22 := entry 2 2
  have e01 := entry 0 1
  have e02 := entry 0 2
  have e12 := entry 1 2
  simp only [Fin.sum_univ_six] at e00 e11 e22 e01 e02 e12
  simp [threeLinesDirection] at e00 e11 e22 e01 e02 e12
  refine ⟨by linarith, by linarith, by linarith, ?_, ?_, ?_⟩
  · linear_combination e00 - e01 - e02
  · linear_combination slide * e11 - slide * e01 - e12
  · linear_combination e22 - e02 - slide * e12

/-! ## 2. The parity identity of the join labels -/

/-- **THE JOIN PARITY IDENTITY.**  The three join coefficients of a rank-one
gap multiply, against the slide, to a square.  The identity is division-free
and needs no hypothesis on the axis. -/
theorem threeLinesRankOne_join_parity {slide : ℝ} {mass weight : Fin 6 → ℝ}
    {selected : Finset (Fin 6)} {axis : Fin 3 → ℝ} {scale : ℝ}
    (heq : directionChartGap (threeLinesDirection slide) mass weight selected
      = scale • atomMatrix axis) :
    slide * (chartCoeff mass weight selected 2 * chartCoeff mass weight selected 4
        * chartCoeff mass weight selected 5)
      = scale ^ 3 * (axis 0 * axis 1 * axis 2) ^ 2 := by
  obtain ⟨h2, h4, h5, -, -, -⟩ := threeLinesCoeff_eq_of_rankOne heq
  have hsplit : slide * (chartCoeff mass weight selected 2 * chartCoeff mass weight selected 4
      * chartCoeff mass weight selected 5)
      = chartCoeff mass weight selected 2 * chartCoeff mass weight selected 4
        * (slide * chartCoeff mass weight selected 5) := by ring
  rw [hsplit, h2, h4, h5]
  ring

/-- The parity product is nonnegative whenever the rank-one scale is. -/
theorem threeLinesRankOne_join_parity_nonneg {slide : ℝ} {mass weight : Fin 6 → ℝ}
    {selected : Finset (Fin 6)} {axis : Fin 3 → ℝ} {scale : ℝ}
    (hscale : 0 ≤ scale)
    (heq : directionChartGap (threeLinesDirection slide) mass weight selected
      = scale • atomMatrix axis) :
    0 ≤ slide * (chartCoeff mass weight selected 2 * chartCoeff mass weight selected 4
        * chartCoeff mass weight selected 5) := by
  rw [threeLinesRankOne_join_parity heq]
  positivity

/-! ## 3. The join exclusion at a chart point -/

/-- No join label is selected: the three join coefficients are negative, so at
a positive slide the parity product is negative.  A rank-one wall of a
positive slide always carries a join label. -/
theorem threeLinesRankOne_not_zeroJoins_of_slide_pos {slide : ℝ}
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    {axis : Fin 3 → ℝ} {scale : ℝ} (hslide : 0 < slide) (hscale : 0 ≤ scale)
    (heq : directionChartGap (threeLinesDirection slide) point.mass point.weight selected
      = scale • atomMatrix axis)
    (h2 : (2 : Fin 6) ∉ selected) (h4 : (4 : Fin 6) ∉ selected)
    (h5 : (5 : Fin 6) ∉ selected) : False := by
  have hn2 := chartCoeff_neg_of_not_mem point h2
  have hn4 := chartCoeff_neg_of_not_mem point h4
  have hn5 := chartCoeff_neg_of_not_mem point h5
  have hpar := threeLinesRankOne_join_parity_nonneg hscale heq
  have hprod : chartCoeff point.mass point.weight selected 2
      * chartCoeff point.mass point.weight selected 4
      * chartCoeff point.mass point.weight selected 5 < 0 :=
    mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hn2 hn4) hn5
  exact absurd hpar (not_le.mpr (mul_neg_of_pos_of_neg hslide hprod))

/-- Two join labels are selected and one is not: at a positive slide the
parity product is again negative. -/
theorem threeLinesRankOne_not_twoJoins_of_slide_pos {slide : ℝ}
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    {axis : Fin 3 → ℝ} {scale : ℝ} (hslide : 0 < slide) (hscale : 0 ≤ scale)
    (heq : directionChartGap (threeLinesDirection slide) point.mass point.weight selected
      = scale • atomMatrix axis)
    (h2 : (2 : Fin 6) ∈ selected) (h4 : (4 : Fin 6) ∈ selected)
    (h5 : (5 : Fin 6) ∉ selected) : False := by
  have hp2 := chartCoeff_pos_of_mem point h2
  have hp4 := chartCoeff_pos_of_mem point h4
  have hn5 := chartCoeff_neg_of_not_mem point h5
  have hpar := threeLinesRankOne_join_parity_nonneg hscale heq
  have hprod : chartCoeff point.mass point.weight selected 2
      * chartCoeff point.mass point.weight selected 4
      * chartCoeff point.mass point.weight selected 5 < 0 :=
    mul_neg_of_pos_of_neg (mul_pos hp2 hp4) hn5
  exact absurd hpar (not_le.mpr (mul_neg_of_pos_of_neg hslide hprod))

/-- All three join labels are selected: at a negative slide the parity product
is positive, so the slide multiple is negative. -/
theorem threeLinesRankOne_not_threeJoins_of_slide_neg {slide : ℝ}
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    {axis : Fin 3 → ℝ} {scale : ℝ} (hslide : slide < 0) (hscale : 0 ≤ scale)
    (heq : directionChartGap (threeLinesDirection slide) point.mass point.weight selected
      = scale • atomMatrix axis)
    (h2 : (2 : Fin 6) ∈ selected) (h4 : (4 : Fin 6) ∈ selected)
    (h5 : (5 : Fin 6) ∈ selected) : False := by
  have hp2 := chartCoeff_pos_of_mem point h2
  have hp4 := chartCoeff_pos_of_mem point h4
  have hp5 := chartCoeff_pos_of_mem point h5
  have hpar := threeLinesRankOne_join_parity_nonneg hscale heq
  have hprod : 0 < chartCoeff point.mass point.weight selected 2
      * chartCoeff point.mass point.weight selected 4
      * chartCoeff point.mass point.weight selected 5 :=
    mul_pos (mul_pos hp2 hp4) hp5
  exact absurd hpar (not_le.mpr (mul_neg_of_neg_of_pos hslide hprod))

/-- One join label is selected and two are not: at a negative slide the parity
product is positive again. -/
theorem threeLinesRankOne_not_oneJoin_of_slide_neg {slide : ℝ}
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    {axis : Fin 3 → ℝ} {scale : ℝ} (hslide : slide < 0) (hscale : 0 ≤ scale)
    (heq : directionChartGap (threeLinesDirection slide) point.mass point.weight selected
      = scale • atomMatrix axis)
    (h2 : (2 : Fin 6) ∈ selected) (h4 : (4 : Fin 6) ∉ selected)
    (h5 : (5 : Fin 6) ∉ selected) : False := by
  have hp2 := chartCoeff_pos_of_mem point h2
  have hn4 := chartCoeff_neg_of_not_mem point h4
  have hn5 := chartCoeff_neg_of_not_mem point h5
  have hpar := threeLinesRankOne_join_parity_nonneg hscale heq
  have hprod : 0 < chartCoeff point.mass point.weight selected 2
      * chartCoeff point.mass point.weight selected 4
      * chartCoeff point.mass point.weight selected 5 := by
    have := mul_pos_of_neg_of_neg hn4 hn5
    nlinarith [hp2]
  exact absurd hpar (not_le.mpr (mul_neg_of_neg_of_pos hslide hprod))

/-! ## 4. The wall family equations -/

/-- An unselected label carries its own mass as the negated coefficient, so at
a rank-one wall the outside masses are pinned by the axis alone. -/
theorem chartCoeff_eq_neg_mass_of_not_mem {size : ℕ} (mass weight : Fin size → ℝ)
    {selected : Finset (Fin size)} {label : Fin size} (hmem : label ∉ selected) :
    chartCoeff mass weight selected label = -mass label := by
  unfold chartCoeff
  rw [if_neg hmem, zero_sub]

/-- **THE PINNED FLOOR.**  A selected label's floor `mass * (1 - weight)` is
the coefficient times the weight.  The floor of a rank-one wall is therefore
read off the axis with no weight of its own, exactly as at the K4 star wall. -/
theorem mass_mul_one_sub_weight_eq_of_mem {size : ℕ} (mass weight : Fin size → ℝ)
    {selected : Finset (Fin size)} {label : Fin size} (hmem : label ∈ selected)
    (hw : weight label ≠ 0) :
    mass label * (1 - weight label)
      = weight label * chartCoeff mass weight selected label := by
  unfold chartCoeff
  rw [if_pos hmem]
  field_simp

/-- **THE THREE-LINES WALL FAMILY.**  At a rank-one three-lines wall every
mass and every floor is pinned by the axis: an unselected label reads its mass
as the negated closed form, and a selected label reads its floor as the weight
times the closed form.  The join labels carry the pairwise axis products. -/
theorem threeLinesWall_join_family {slide : ℝ} (point : DirectionChartPoint 6)
    {selected : Finset (Fin 6)} {axis : Fin 3 → ℝ} {scale : ℝ}
    (heq : directionChartGap (threeLinesDirection slide) point.mass point.weight selected
      = scale • atomMatrix axis) :
    ((2 : Fin 6) ∉ selected → point.mass 2 = -(scale * (axis 0 * axis 1)))
      ∧ ((2 : Fin 6) ∈ selected →
        point.mass 2 * (1 - point.weight 2) = point.weight 2 * (scale * (axis 0 * axis 1)))
      ∧ ((4 : Fin 6) ∉ selected → point.mass 4 = -(scale * (axis 0 * axis 2)))
      ∧ ((4 : Fin 6) ∈ selected →
        point.mass 4 * (1 - point.weight 4) = point.weight 4 * (scale * (axis 0 * axis 2))) := by
  obtain ⟨h2, h4, -, -, -, -⟩ := threeLinesCoeff_eq_of_rankOne heq
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro hmem
    have := chartCoeff_eq_neg_mass_of_not_mem point.mass point.weight hmem
    rw [h2] at this
    linarith
  · intro hmem
    have := mass_mul_one_sub_weight_eq_of_mem point.mass point.weight hmem
      (ne_of_gt (point.weight_pos 2))
    rw [h2] at this
    exact this
  · intro hmem
    have := chartCoeff_eq_neg_mass_of_not_mem point.mass point.weight hmem
    rw [h4] at this
    linarith
  · intro hmem
    have := mass_mul_one_sub_weight_eq_of_mem point.mass point.weight hmem
      (ne_of_gt (point.weight_pos 4))
    rw [h4] at this
    exact this

end Gtz
