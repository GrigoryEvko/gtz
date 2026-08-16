import Gtz.Wave.ThreeLinesStarBracketCover

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The diagonal-dominance route at the three-lines chart, and why it cannot cover

`Gtz.posDef_threeLinesVertex_of_dominates` fires the vertex triple `{0, 1, 3}`
from three entrywise inequalities.  This file states that cell for an ARBITRARY
selection, then proves the route it belongs to is bounded in three ways.

* **The support is two triples.**  On the fundamental domain `1 <= |slide|` the
  first two dominance rows force `0` and `1` into the selection, and a selection
  carrying neither `3` nor `5` can never dominate.  So only `{0, 1, 3}` and
  `{0, 1, 5}` are reachable, out of twenty.
* **`{0, 1, 5}` is empty on the boundary.**  At `|slide| = 1` its third row asks
  for `mass 3 + 2 * mass 4 < 0`.
* **Both survivors die in `slide`.**  `{0, 1, 3}` needs `slide ^ 2 * mass 5` below
  `chartExcess 3`, and `{0, 1, 5}` needs `(|slide| - 1) * chartExcess 5` below
  `chartExcess 1`.  Each is an explicit ceiling in `|slide|`.

The consequence is that the dominance family is not a cover of the fundamental
domain: past an explicit slide every selection fails, while the chart point is
untouched.  The slide enters the gap only through the coefficient of label `5`,
as `slide * c 5` off the diagonal and `slide ^ 2 * c 5` on it, which is the
mechanism behind all three statements.
-/

namespace Gtz

open Finset

/-! ## 1. The dominance cell at an arbitrary selection -/

/-- The chart coefficient of a label, abbreviated for the dominance rows. -/
noncomputable def threeLinesCoeff (mass weight : Fin 6 → ℝ) (selected : Finset (Fin 6))
    (label : Fin 6) : ℝ :=
  threeLinesChartCoefficient mass weight selected label

theorem threeLinesCoeff_of_mem (mass weight : Fin 6 → ℝ) {selected : Finset (Fin 6)}
    {label : Fin 6} (hmem : label ∈ selected) :
    threeLinesCoeff mass weight selected label = chartExcess mass weight label :=
  threeLinesChartCoefficient_of_mem mass weight hmem

theorem threeLinesCoeff_of_notMem (mass weight : Fin 6 → ℝ) {selected : Finset (Fin 6)}
    {label : Fin 6} (hnotMem : label ∉ selected) :
    threeLinesCoeff mass weight selected label = -mass label :=
  threeLinesChartCoefficient_of_notMem mass weight hnotMem

/-- **The dominance cell at an arbitrary selection.**  The three joins `2`, `4`
and `5` occupy the three off-diagonal slots of the universal coefficient matrix,
one each, so entrywise dominance is exactly three inequalities whatever the
selection is. -/
def ThreeLinesDominates (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) : Prop :=
  |threeLinesCoeff mass weight selected 2| + |threeLinesCoeff mass weight selected 4|
      < threeLinesCoeff mass weight selected 0 + threeLinesCoeff mass weight selected 2
        + threeLinesCoeff mass weight selected 4 ∧
    |threeLinesCoeff mass weight selected 2| + |slide * threeLinesCoeff mass weight selected 5|
      < threeLinesCoeff mass weight selected 1 + threeLinesCoeff mass weight selected 2
        + threeLinesCoeff mass weight selected 5 ∧
    |threeLinesCoeff mass weight selected 4| + |slide * threeLinesCoeff mass weight selected 5|
      < threeLinesCoeff mass weight selected 3 + threeLinesCoeff mass weight selected 4
        + slide ^ 2 * threeLinesCoeff mass weight selected 5

/-- **The cell fires at every selection.**  Division-free, and it reads no
determinant.  The vertex cell is the case `selected = {0, 1, 3}`. -/
theorem posDef_threeLines_of_dominates (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0) (selected : Finset (Fin 6))
    (hdom : ThreeLinesDominates slide mass weight selected) :
    (directionChartGap (threeLinesDirection slide) mass weight selected).PosDef := by
  obtain ⟨hzero, hone, hthree⟩ := hdom
  rw [directionChartGap_threeLines_eq slide mass weight hweightNe, threeLinesCoefficientMatrix]
  exact posDef_finThree_of_dominant _ _ _ _ _ _ hzero hone hthree

/-! ## 2. A selection carrying neither `3` nor `5` never dominates -/

/-- **The first structural bound.**  The third dominance row compares `mass 3`
and `slide ^ 2 * mass 5`, both subtracted, against a difference that cannot pay
for them.  No slide and no chart point escapes. -/
theorem not_threeLinesDominates_of_notMem_three_of_notMem_five (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hmassThree : 0 < mass 3) (hmassFive : 0 < mass 5)
    (selected : Finset (Fin 6)) (hthree : (3 : Fin 6) ∉ selected)
    (hfive : (5 : Fin 6) ∉ selected) :
    ¬ ThreeLinesDominates slide mass weight selected := by
  rintro ⟨-, -, hrow⟩
  rw [threeLinesCoeff_of_notMem mass weight hthree,
    threeLinesCoeff_of_notMem mass weight hfive] at hrow
  have habs : threeLinesCoeff mass weight selected 4
      ≤ |threeLinesCoeff mass weight selected 4| := le_abs_self _
  have hnn : (0 : ℝ) ≤ |slide * -mass 5| := abs_nonneg _
  nlinarith [sq_nonneg slide]

/-! ## 3. On the fundamental domain the first two rows pin labels `0` and `1` -/

/-- A selection whose coefficient at a label is positive contains that label. -/
theorem mem_of_threeLinesCoeff_pos (mass weight : Fin 6 → ℝ) (selected : Finset (Fin 6))
    (label : Fin 6) (hmass : 0 < mass label)
    (hpos : 0 < threeLinesCoeff mass weight selected label) : label ∈ selected := by
  by_contra hnot
  rw [threeLinesCoeff_of_notMem mass weight hnot] at hpos
  linarith

/-- **The first row forces label `0`.**  Both joins appear on the right with
their own signs and on the left inside absolute values. -/
theorem mem_zero_of_threeLinesDominates (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hmassZero : 0 < mass 0) (selected : Finset (Fin 6))
    (hdom : ThreeLinesDominates slide mass weight selected) : (0 : Fin 6) ∈ selected := by
  obtain ⟨hrow, -, -⟩ := hdom
  refine mem_of_threeLinesCoeff_pos mass weight selected 0 hmassZero ?_
  have h2 : threeLinesCoeff mass weight selected 2
      ≤ |threeLinesCoeff mass weight selected 2| := le_abs_self _
  have h4 : threeLinesCoeff mass weight selected 4
      ≤ |threeLinesCoeff mass weight selected 4| := le_abs_self _
  linarith

/-- **The second row forces label `1` on the fundamental domain.**  The join at
`5` is amplified by `|slide|`, which is at least one there, so it cannot be paid
for by its own appearance on the right. -/
theorem mem_one_of_threeLinesDominates (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hfund : 1 ≤ |slide|) (hmassOne : 0 < mass 1) (selected : Finset (Fin 6))
    (hdom : ThreeLinesDominates slide mass weight selected) : (1 : Fin 6) ∈ selected := by
  obtain ⟨-, hrow, -⟩ := hdom
  refine mem_of_threeLinesCoeff_pos mass weight selected 1 hmassOne ?_
  have h2 : threeLinesCoeff mass weight selected 2
      ≤ |threeLinesCoeff mass weight selected 2| := le_abs_self _
  have hsplit : |slide * threeLinesCoeff mass weight selected 5|
      = |slide| * |threeLinesCoeff mass weight selected 5| := abs_mul _ _
  have hle : |threeLinesCoeff mass weight selected 5|
      ≤ |slide| * |threeLinesCoeff mass weight selected 5| := by
    nlinarith [abs_nonneg (threeLinesCoeff mass weight selected 5)]
  have hself : threeLinesCoeff mass weight selected 5
      ≤ |threeLinesCoeff mass weight selected 5| := le_abs_self _
  rw [hsplit] at hrow
  linarith

/-! ## 4. The support of the dominance cell is two triples out of twenty -/

/-- The four card-three selections that contain both `0` and `1`. -/
theorem eq_of_card_three_of_mem_zero_of_mem_one (selected : Finset (Fin 6))
    (hcard : selected.card = 3) (hzero : (0 : Fin 6) ∈ selected)
    (hone : (1 : Fin 6) ∈ selected) :
    selected = ({0, 1, 2} : Finset (Fin 6)) ∨ selected = ({0, 1, 3} : Finset (Fin 6)) ∨
      selected = ({0, 1, 4} : Finset (Fin 6)) ∨ selected = ({0, 1, 5} : Finset (Fin 6)) := by
  revert hcard hzero hone
  revert selected
  decide

/-- **THE SUPPORT THEOREM.**  On the fundamental domain the dominance cell can
fire at only two of the twenty card-three selections.  Eighteen are unreachable
for every chart point and every slide. -/
theorem threeLinesDominates_eq_vertex_or_zeroOneFive (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hfund : 1 ≤ |slide|) (hmass : ∀ label, 0 < mass label) (selected : Finset (Fin 6))
    (hcard : selected.card = 3) (hdom : ThreeLinesDominates slide mass weight selected) :
    selected = ({0, 1, 3} : Finset (Fin 6)) ∨ selected = ({0, 1, 5} : Finset (Fin 6)) := by
  have hzero := mem_zero_of_threeLinesDominates slide mass weight (hmass 0) selected hdom
  have hone := mem_one_of_threeLinesDominates slide mass weight hfund (hmass 1) selected hdom
  rcases eq_of_card_three_of_mem_zero_of_mem_one selected hcard hzero hone with
    h | h | h | h
  · exact absurd hdom (by
      rw [h]
      exact not_threeLinesDominates_of_notMem_three_of_notMem_five slide mass weight
        (hmass 3) (hmass 5) _ (by decide) (by decide))
  · exact Or.inl h
  · exact absurd hdom (by
      rw [h]
      exact not_threeLinesDominates_of_notMem_three_of_notMem_five slide mass weight
        (hmass 3) (hmass 5) _ (by decide) (by decide))
  · exact Or.inr h

/-! ## 5. Closed forms at the two survivors -/

/-- The vertex row conditions, with every coefficient resolved. -/
theorem threeLinesDominates_vertex_iff (slide : ℝ) (mass weight : Fin 6 → ℝ) :
    ThreeLinesDominates slide mass weight ({0, 1, 3} : Finset (Fin 6))
      ↔ |(-mass 2)| + |(-mass 4)| < chartExcess mass weight 0 + -mass 2 + -mass 4 ∧
        |(-mass 2)| + |slide * -mass 5| < chartExcess mass weight 1 + -mass 2 + -mass 5 ∧
        |(-mass 4)| + |slide * -mass 5|
          < chartExcess mass weight 3 + -mass 4 + slide ^ 2 * -mass 5 := by
  rw [ThreeLinesDominates,
    threeLinesCoeff_of_mem mass weight (show (0 : Fin 6) ∈ ({0,1,3} : Finset (Fin 6)) by decide),
    threeLinesCoeff_of_mem mass weight (show (1 : Fin 6) ∈ ({0,1,3} : Finset (Fin 6)) by decide),
    threeLinesCoeff_of_mem mass weight (show (3 : Fin 6) ∈ ({0,1,3} : Finset (Fin 6)) by decide),
    threeLinesCoeff_of_notMem mass weight (show (2 : Fin 6) ∉ ({0,1,3} : Finset (Fin 6)) by decide),
    threeLinesCoeff_of_notMem mass weight (show (4 : Fin 6) ∉ ({0,1,3} : Finset (Fin 6)) by decide),
    threeLinesCoeff_of_notMem mass weight (show (5 : Fin 6) ∉ ({0,1,3} : Finset (Fin 6)) by decide)]

/-- The `{0, 1, 5}` row conditions, with every coefficient resolved. -/
theorem threeLinesDominates_zeroOneFive_iff (slide : ℝ) (mass weight : Fin 6 → ℝ) :
    ThreeLinesDominates slide mass weight ({0, 1, 5} : Finset (Fin 6))
      ↔ |(-mass 2)| + |(-mass 4)| < chartExcess mass weight 0 + -mass 2 + -mass 4 ∧
        |(-mass 2)| + |slide * chartExcess mass weight 5|
          < chartExcess mass weight 1 + -mass 2 + chartExcess mass weight 5 ∧
        |(-mass 4)| + |slide * chartExcess mass weight 5|
          < -mass 3 + -mass 4 + slide ^ 2 * chartExcess mass weight 5 := by
  rw [ThreeLinesDominates,
    threeLinesCoeff_of_mem mass weight (show (0 : Fin 6) ∈ ({0,1,5} : Finset (Fin 6)) by decide),
    threeLinesCoeff_of_mem mass weight (show (1 : Fin 6) ∈ ({0,1,5} : Finset (Fin 6)) by decide),
    threeLinesCoeff_of_mem mass weight (show (5 : Fin 6) ∈ ({0,1,5} : Finset (Fin 6)) by decide),
    threeLinesCoeff_of_notMem mass weight (show (2 : Fin 6) ∉ ({0,1,5} : Finset (Fin 6)) by decide),
    threeLinesCoeff_of_notMem mass weight (show (3 : Fin 6) ∉ ({0,1,5} : Finset (Fin 6)) by decide),
    threeLinesCoeff_of_notMem mass weight (show (4 : Fin 6) ∉ ({0,1,5} : Finset (Fin 6)) by decide)]

/-! ## 6. The two survivors die in the slide -/

/-- **`{0, 1, 5}` is empty on the boundary of the fundamental domain.**  At
`|slide| = 1` the amplification `slide ^ 2` exactly cancels the off-diagonal
`|slide|`, and the third row degenerates to `mass 3 + 2 * mass 4 < 0`. -/
theorem not_threeLinesDominates_zeroOneFive_of_abs_slide_le_one (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hslide : |slide| ≤ 1) (hmassThree : 0 < mass 3)
    (hmassFour : 0 < mass 4) (hexcessFive : 0 ≤ chartExcess mass weight 5) :
    ¬ ThreeLinesDominates slide mass weight ({0, 1, 5} : Finset (Fin 6)) := by
  rw [threeLinesDominates_zeroOneFive_iff]
  rintro ⟨-, -, hrow⟩
  rw [abs_neg, abs_of_pos hmassFour, abs_mul] at hrow
  have hsq : slide ^ 2 ≤ |slide| := by
    have : |slide| ^ 2 ≤ |slide| := by nlinarith [abs_nonneg slide]
    rwa [sq_abs] at this
  have habs : |chartExcess mass weight 5| = chartExcess mass weight 5 :=
    abs_of_nonneg hexcessFive
  rw [habs] at hrow
  nlinarith [abs_nonneg slide]

/-- **The vertex cell has a slide ceiling.**  Its third row must pay
`slide ^ 2 * mass 5` out of `chartExcess 3`, so a large enough slide empties it
at every chart point. -/
theorem not_threeLinesDominates_vertex_of_excessThree_le (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hmassFour : 0 < mass 4)
    (hceiling : chartExcess mass weight 3 ≤ slide ^ 2 * mass 5) :
    ¬ ThreeLinesDominates slide mass weight ({0, 1, 3} : Finset (Fin 6)) := by
  rw [threeLinesDominates_vertex_iff]
  rintro ⟨-, -, hrow⟩
  rw [abs_neg, abs_of_pos hmassFour] at hrow
  have hnn : (0 : ℝ) ≤ |slide * -mass 5| := abs_nonneg _
  linarith

/-- **The `{0, 1, 5}` cell has a slide ceiling too.**  Its second row pays
`|slide| * chartExcess 5` out of `chartExcess 1`, which is linear against a
constant. -/
theorem not_threeLinesDominates_zeroOneFive_of_excessOne_le (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hmassTwo : 0 < mass 2)
    (hexcessFive : 0 ≤ chartExcess mass weight 5)
    (hceiling : chartExcess mass weight 1
      ≤ (|slide| - 1) * chartExcess mass weight 5) :
    ¬ ThreeLinesDominates slide mass weight ({0, 1, 5} : Finset (Fin 6)) := by
  rw [threeLinesDominates_zeroOneFive_iff]
  rintro ⟨-, hrow, -⟩
  rw [abs_neg, abs_of_pos hmassTwo, abs_mul, abs_of_nonneg hexcessFive] at hrow
  nlinarith

/-! ## 7. The dominance family is not a cover -/

/-- **THE NO-GO.**  Past an explicit slide, determined by the chart point alone,
NO card-three selection satisfies the dominance cell.  The point itself is
untouched, so what fails is the route and not the statement it was meant to
prove. -/
theorem not_exists_threeLinesDominates_of_slide_large (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hfund : 1 ≤ |slide|) (hmass : ∀ label, 0 < mass label)
    (hexcessFive : 0 ≤ chartExcess mass weight 5)
    (hvertexCeiling : chartExcess mass weight 3 ≤ slide ^ 2 * mass 5)
    (hfiveCeiling : chartExcess mass weight 1
      ≤ (|slide| - 1) * chartExcess mass weight 5) :
    ¬ ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        ThreeLinesDominates slide mass weight selected := by
  rintro ⟨selected, hcard, hdom⟩
  rcases threeLinesDominates_eq_vertex_or_zeroOneFive slide mass weight hfund hmass
    selected hcard hdom with h | h
  · exact not_threeLinesDominates_vertex_of_excessThree_le slide mass weight
      (hmass 4) hvertexCeiling (h ▸ hdom)
  · exact not_threeLinesDominates_zeroOneFive_of_excessOne_le slide mass weight
      (hmass 2) hexcessFive hfiveCeiling (h ▸ hdom)

/-! ### The no-go is not vacuous -/

/-- The uniform chart point: every mass one, every weight one sixth. -/
noncomputable def uniformSixMass : Fin 6 → ℝ := fun _ => 1

/-- The uniform weights, a probability vector on six labels. -/
noncomputable def uniformSixWeight : Fin 6 → ℝ := fun _ => 1 / 6

theorem uniformSixMass_pos (label : Fin 6) : 0 < uniformSixMass label := by
  norm_num [uniformSixMass]

theorem uniformSixWeight_pos (label : Fin 6) : 0 < uniformSixWeight label := by
  norm_num [uniformSixWeight]

theorem uniformSixWeight_sum : ∑ label, uniformSixWeight label = 1 := by
  simp [uniformSixWeight]

/-- Every uniform excess is five. -/
theorem chartExcess_uniformSix (label : Fin 6) :
    chartExcess uniformSixMass uniformSixWeight label = 5 := by
  rw [chartExcess, uniformSixMass, uniformSixWeight]; norm_num

/-- **The no-go bites at an explicit point.**  At the uniform chart point and
slide three, no card-three selection satisfies the dominance cell. -/
theorem not_exists_threeLinesDominates_uniformSix :
    ¬ ∃ selected : Finset (Fin 6), selected.card = 3 ∧
        ThreeLinesDominates 3 uniformSixMass uniformSixWeight selected := by
  refine not_exists_threeLinesDominates_of_slide_large 3 uniformSixMass uniformSixWeight
    (by rw [abs_of_nonneg]; norm_num; norm_num) uniformSixMass_pos ?_ ?_ ?_
  · rw [chartExcess_uniformSix]; norm_num
  · rw [chartExcess_uniformSix, uniformSixMass]; norm_num
  · rw [chartExcess_uniformSix, chartExcess_uniformSix, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 3)]
    norm_num

/-- The cover property the route would need. -/
def ThreeLinesDominanceCovers : Prop :=
  ∀ slide : ℝ, 1 ≤ |slide| → ∀ point : DirectionChartPoint 6,
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      ThreeLinesDominates slide point.mass point.weight selected

/-- **The route is refuted as a cover.**  Any chart point with a positive
excess at `5` supplies a slide that defeats it. -/
theorem not_threeLinesDominanceCovers_of_witness (point : DirectionChartPoint 6)
    (slide : ℝ) (hfund : 1 ≤ |slide|)
    (hexcessFive : 0 ≤ chartExcess point.mass point.weight 5)
    (hvertexCeiling : chartExcess point.mass point.weight 3
      ≤ slide ^ 2 * point.mass 5)
    (hfiveCeiling : chartExcess point.mass point.weight 1
      ≤ (|slide| - 1) * chartExcess point.mass point.weight 5) :
    ¬ ThreeLinesDominanceCovers := by
  intro hcovers
  exact not_exists_threeLinesDominates_of_slide_large slide point.mass point.weight
    hfund point.mass_pos hexcessFive hvertexCeiling hfiveCeiling
    (hcovers slide hfund point)

end Gtz
