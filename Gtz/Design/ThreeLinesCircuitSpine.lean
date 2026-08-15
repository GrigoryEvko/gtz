import Gtz.Design.ThreeLinesAtlas

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The combinatorial spine of the three-lines chart

The three-lines chart has six directions

  `v0 = (1,0,0)  v1 = (0,1,0)  v2 = (1,1,0)  v3 = (0,0,1)  v4 = (1,0,1)  v5 = (0,1,slide)`

and three dependent triples, `{0,1,2}`, `{0,3,4}` and `{1,3,5}`.  Part 7 of
`Gtz.Design.ThreeLinesAtlas` already proves that a dependent triple never even
weakly dominates.  What the campaign never wrote down is the chart's matroid
data, and this module supplies it.

**The circuits.**  Each dependent triple carries an explicit linear relation:
`v2 = v0 + v1`, `v4 = v0 + v3`, and `v5 = v1 + slide * v3`.  The labels `0`, `1`,
`3` are the coordinate axes and the labels `2`, `4`, `5` are the joins.  Each
coordinate label lies on two circuits and each join label lies on one.  That is
where this chart differs from `M(K4)`, whose six labels each lie on two
triangles, and it is why the two charts split their card-four selections
differently.

**The line exclusion, packaged.**  The three landed exclusions each take their
own mass hypotheses.  Read against a chart point they say one thing: a card-three
selection whose gap is positive definite is a basis.

**The type split.**  A card-four selection holds at most one dependent line, so
the fifteen card-four selections split as NINE holding a line and SIX holding
none.  This is not the three-and-twelve split of the `M(K4)` chart, whose
card-four selections are classified by whether the complement is a perfect
matching.
-/

namespace Gtz

open Matrix Finset

/-! ## The circuits -/

/-- The join `2` is the sum of the coordinate axes `0` and `1`. -/
theorem threeLinesCircuit_two (slide : ℝ) :
    threeLinesDirection slide 2
      = threeLinesDirection slide 0 + threeLinesDirection slide 1 := by
  funext coord
  fin_cases coord <;>
    simp [threeLinesDirection_zero, threeLinesDirection_one, threeLinesDirection_two]

/-- The join `4` is the sum of the coordinate axes `0` and `3`. -/
theorem threeLinesCircuit_four (slide : ℝ) :
    threeLinesDirection slide 4
      = threeLinesDirection slide 0 + threeLinesDirection slide 3 := by
  funext coord
  fin_cases coord <;>
    simp [threeLinesDirection_zero, threeLinesDirection_three, threeLinesDirection_four]

/-- The join `5` is the coordinate axis `1` plus `slide` times the axis `3`.
This is the only circuit whose coefficients are not all one, and it is the only
place the slide enters the matroid. -/
theorem threeLinesCircuit_five (slide : ℝ) :
    threeLinesDirection slide 5
      = threeLinesDirection slide 1 + slide • threeLinesDirection slide 3 := by
  funext coord
  fin_cases coord <;>
    simp [threeLinesDirection_one, threeLinesDirection_three, threeLinesDirection_five]

/-! ## The line exclusion at a chart point -/

/-- **THE LINE EXCLUSION.**  A card-three selection whose chart gap is positive
definite is none of the three dependent lines.  Every card-three candidate of the
three-lines chart is therefore one of the seventeen bases, and A2's conclusion
may be read against those alone.

This packages the three landed Part 7 exclusions of
`Gtz.Design.ThreeLinesAtlas` against a chart point, whose positivity fields
discharge all of their separate mass hypotheses at once. -/
theorem threeLines_posDef_cardThree_ne_line (slide : ℝ) (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hposDef : (directionChartGap (threeLinesDirection slide) point.mass
      point.weight selected).PosDef) :
    selected ≠ ({0, 1, 2} : Finset (Fin 6))
      ∧ selected ≠ ({0, 3, 4} : Finset (Fin 6))
      ∧ selected ≠ ({1, 3, 5} : Finset (Fin 6)) := by
  have hweightNe : ∀ label, point.weight label ≠ 0 := fun label =>
    ne_of_gt (point.weight_pos label)
  refine ⟨?_, ?_, ?_⟩ <;> rintro rfl
  · exact directionChartGap_threeLines_firstLine_not_posSemidef slide point.mass
      point.weight hweightNe (point.mass_pos 3) (point.mass_pos 4)
      (le_of_lt (point.mass_pos 5)) hposDef.posSemidef
  · exact directionChartGap_threeLines_secondLine_not_posSemidef slide point.mass
      point.weight hweightNe (point.mass_pos 1) (point.mass_pos 2)
      (point.mass_pos 5) hposDef.posSemidef
  · exact directionChartGap_threeLines_thirdLine_not_posSemidef slide point.mass
      point.weight hweightNe (point.mass_pos 0) (point.mass_pos 2)
      (point.mass_pos 4) hposDef.posSemidef

/-! ## The type split -/

/-- **THE CARD-FOUR TYPE SPLIT.**  A card-four selection of the three-lines chart
holds at most one dependent line.

The three lines pairwise share exactly one label, so the union of any two has
five labels and cannot fit inside a card-four selection.  With the fifteen
card-four selections this gives NINE that hold a line and SIX that hold none. -/
theorem threeLinesCardFour_at_most_one_line :
    ∀ selected : Finset (Fin 6), selected.card = 4 →
      ¬ (({0, 1, 2} : Finset (Fin 6)) ⊆ selected
          ∧ ({0, 3, 4} : Finset (Fin 6)) ⊆ selected)
        ∧ ¬ (({0, 1, 2} : Finset (Fin 6)) ⊆ selected
          ∧ ({1, 3, 5} : Finset (Fin 6)) ⊆ selected)
        ∧ ¬ (({0, 3, 4} : Finset (Fin 6)) ⊆ selected
          ∧ ({1, 3, 5} : Finset (Fin 6)) ⊆ selected) := by
  decide

/-- The six circuit-free card-four selections of the three-lines chart.  Under the
`Z/3` rotation `(0 3 1)(2 4 5)` these form two orbits of three:
`{2,3,4,5} -> {1,2,4,5} -> {0,2,4,5}` and `{1,2,3,4} -> {0,1,4,5} -> {0,2,3,5}`. -/
def threeLinesCircuitFreeCardFour : List (Finset (Fin 6)) :=
  [{1, 2, 3, 4}, {0, 2, 3, 5}, {0, 1, 4, 5}, {0, 2, 4, 5}, {1, 2, 4, 5}, {2, 3, 4, 5}]

/-- **THE CARD-FOUR DICHOTOMY.**  Every card-four selection either holds one of
the three dependent lines, or is one of the six circuit-free selections. -/
theorem threeLinesCardFour_line_or_circuitFree :
    ∀ selected : Finset (Fin 6), selected.card = 4 →
      ({0, 1, 2} : Finset (Fin 6)) ⊆ selected
        ∨ ({0, 3, 4} : Finset (Fin 6)) ⊆ selected
        ∨ ({1, 3, 5} : Finset (Fin 6)) ⊆ selected
        ∨ selected ∈ threeLinesCircuitFreeCardFour := by
  decide

end Gtz
