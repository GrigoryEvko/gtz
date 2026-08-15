import Gtz.Design.ThreeLinesWallArchitecture

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 2000000

/-!
# Classify rank-one weak witnesses in the three-lines chart

The three-lines wall identity says that

`slide * (c₂ * c₄ * c₅)`

is a nonnegative square at every nonnegative rank-one wall.  Chart
coefficients are positive on the selected triple and negative off it, so the
sign of the slide fixes the parity of the three join labels `{2,4,5}`.

This module spends that sign law completely.  After imposing card three and
removing the three dependent line triples, a positive slide leaves exactly
seven rank-one witnesses, while a negative slide leaves exactly ten.  The two
finite classification lemmas are proved by kernel reduction with `decide`;
`native_decide` is not used.
-/

namespace Gtz

open Finset Matrix

/-! ## Join parity -/

/-- A selection carries an odd number of the three join labels `{2,4,5}`. -/
def ThreeLinesOddJoinSelection (selected : Finset (Fin 6)) : Prop :=
  ((2 : Fin 6) ∈ selected ∧ (4 : Fin 6) ∉ selected ∧ (5 : Fin 6) ∉ selected) ∨
  ((2 : Fin 6) ∉ selected ∧ (4 : Fin 6) ∈ selected ∧ (5 : Fin 6) ∉ selected) ∨
  ((2 : Fin 6) ∉ selected ∧ (4 : Fin 6) ∉ selected ∧ (5 : Fin 6) ∈ selected) ∨
  ((2 : Fin 6) ∈ selected ∧ (4 : Fin 6) ∈ selected ∧ (5 : Fin 6) ∈ selected)

/-- A selection carries an even number of the three join labels `{2,4,5}`. -/
def ThreeLinesEvenJoinSelection (selected : Finset (Fin 6)) : Prop :=
  ((2 : Fin 6) ∉ selected ∧ (4 : Fin 6) ∉ selected ∧ (5 : Fin 6) ∉ selected) ∨
  ((2 : Fin 6) ∈ selected ∧ (4 : Fin 6) ∈ selected ∧ (5 : Fin 6) ∉ selected) ∨
  ((2 : Fin 6) ∈ selected ∧ (4 : Fin 6) ∉ selected ∧ (5 : Fin 6) ∈ selected) ∨
  ((2 : Fin 6) ∉ selected ∧ (4 : Fin 6) ∈ selected ∧ (5 : Fin 6) ∈ selected)

/-- At a positive slide, a nonnegative rank-one wall carries an odd number of
join labels. -/
theorem threeLinesRankOne_oddJoins_of_slide_pos {slide : ℝ}
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    {axis : Fin 3 → ℝ} {scale : ℝ} (hslide : 0 < slide) (hscale : 0 ≤ scale)
    (heq : directionChartGap (threeLinesDirection slide) point.mass point.weight selected
      = scale • atomMatrix axis) :
    ThreeLinesOddJoinSelection selected := by
  have hpar := threeLinesRankOne_join_parity_nonneg hscale heq
  by_cases h2 : (2 : Fin 6) ∈ selected
  · by_cases h4 : (4 : Fin 6) ∈ selected
    · by_cases h5 : (5 : Fin 6) ∈ selected
      · exact Or.inr (Or.inr (Or.inr ⟨h2, h4, h5⟩))
      · have hp2 := chartCoeff_pos_of_mem point h2
        have hp4 := chartCoeff_pos_of_mem point h4
        have hn5 := chartCoeff_neg_of_not_mem point h5
        have hprod : chartCoeff point.mass point.weight selected 2
            * chartCoeff point.mass point.weight selected 4
            * chartCoeff point.mass point.weight selected 5 < 0 :=
          mul_neg_of_pos_of_neg (mul_pos hp2 hp4) hn5
        exact False.elim ((not_lt_of_ge hpar) (mul_neg_of_pos_of_neg hslide hprod))
    · by_cases h5 : (5 : Fin 6) ∈ selected
      · have hp2 := chartCoeff_pos_of_mem point h2
        have hn4 := chartCoeff_neg_of_not_mem point h4
        have hp5 := chartCoeff_pos_of_mem point h5
        have hprod : chartCoeff point.mass point.weight selected 2
            * chartCoeff point.mass point.weight selected 4
            * chartCoeff point.mass point.weight selected 5 < 0 :=
          mul_neg_of_neg_of_pos (mul_neg_of_pos_of_neg hp2 hn4) hp5
        exact False.elim ((not_lt_of_ge hpar) (mul_neg_of_pos_of_neg hslide hprod))
      · exact Or.inl ⟨h2, h4, h5⟩
  · by_cases h4 : (4 : Fin 6) ∈ selected
    · by_cases h5 : (5 : Fin 6) ∈ selected
      · have hn2 := chartCoeff_neg_of_not_mem point h2
        have hp4 := chartCoeff_pos_of_mem point h4
        have hp5 := chartCoeff_pos_of_mem point h5
        have hprod : chartCoeff point.mass point.weight selected 2
            * chartCoeff point.mass point.weight selected 4
            * chartCoeff point.mass point.weight selected 5 < 0 :=
          mul_neg_of_neg_of_pos (mul_neg_of_neg_of_pos hn2 hp4) hp5
        exact False.elim ((not_lt_of_ge hpar) (mul_neg_of_pos_of_neg hslide hprod))
      · exact Or.inr (Or.inl ⟨h2, h4, h5⟩)
    · by_cases h5 : (5 : Fin 6) ∈ selected
      · exact Or.inr (Or.inr (Or.inl ⟨h2, h4, h5⟩))
      · have hn2 := chartCoeff_neg_of_not_mem point h2
        have hn4 := chartCoeff_neg_of_not_mem point h4
        have hn5 := chartCoeff_neg_of_not_mem point h5
        have hprod : chartCoeff point.mass point.weight selected 2
            * chartCoeff point.mass point.weight selected 4
            * chartCoeff point.mass point.weight selected 5 < 0 :=
          mul_neg_of_pos_of_neg (mul_pos_of_neg_of_neg hn2 hn4) hn5
        exact False.elim ((not_lt_of_ge hpar) (mul_neg_of_pos_of_neg hslide hprod))

/-- At a negative slide, a nonnegative rank-one wall carries an even number of
join labels. -/
theorem threeLinesRankOne_evenJoins_of_slide_neg {slide : ℝ}
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    {axis : Fin 3 → ℝ} {scale : ℝ} (hslide : slide < 0) (hscale : 0 ≤ scale)
    (heq : directionChartGap (threeLinesDirection slide) point.mass point.weight selected
      = scale • atomMatrix axis) :
    ThreeLinesEvenJoinSelection selected := by
  have hpar := threeLinesRankOne_join_parity_nonneg hscale heq
  by_cases h2 : (2 : Fin 6) ∈ selected
  · by_cases h4 : (4 : Fin 6) ∈ selected
    · by_cases h5 : (5 : Fin 6) ∈ selected
      · have hp2 := chartCoeff_pos_of_mem point h2
        have hp4 := chartCoeff_pos_of_mem point h4
        have hp5 := chartCoeff_pos_of_mem point h5
        have hprod : 0 < chartCoeff point.mass point.weight selected 2
            * chartCoeff point.mass point.weight selected 4
            * chartCoeff point.mass point.weight selected 5 :=
          mul_pos (mul_pos hp2 hp4) hp5
        exact False.elim ((not_lt_of_ge hpar) (mul_neg_of_neg_of_pos hslide hprod))
      · exact Or.inr (Or.inl ⟨h2, h4, h5⟩)
    · by_cases h5 : (5 : Fin 6) ∈ selected
      · exact Or.inr (Or.inr (Or.inl ⟨h2, h4, h5⟩))
      · have hp2 := chartCoeff_pos_of_mem point h2
        have hn4 := chartCoeff_neg_of_not_mem point h4
        have hn5 := chartCoeff_neg_of_not_mem point h5
        have hprod : 0 < chartCoeff point.mass point.weight selected 2
            * chartCoeff point.mass point.weight selected 4
            * chartCoeff point.mass point.weight selected 5 := by
          have hneg := mul_neg_of_pos_of_neg hp2 hn4
          exact mul_pos_of_neg_of_neg hneg hn5
        exact False.elim ((not_lt_of_ge hpar) (mul_neg_of_neg_of_pos hslide hprod))
  · by_cases h4 : (4 : Fin 6) ∈ selected
    · by_cases h5 : (5 : Fin 6) ∈ selected
      · exact Or.inr (Or.inr (Or.inr ⟨h2, h4, h5⟩))
      · have hn2 := chartCoeff_neg_of_not_mem point h2
        have hp4 := chartCoeff_pos_of_mem point h4
        have hn5 := chartCoeff_neg_of_not_mem point h5
        have hprod : 0 < chartCoeff point.mass point.weight selected 2
            * chartCoeff point.mass point.weight selected 4
            * chartCoeff point.mass point.weight selected 5 := by
          have hneg := mul_neg_of_neg_of_pos hn2 hp4
          exact mul_pos_of_neg_of_neg hneg hn5
        exact False.elim ((not_lt_of_ge hpar) (mul_neg_of_neg_of_pos hslide hprod))
    · by_cases h5 : (5 : Fin 6) ∈ selected
      · have hn2 := chartCoeff_neg_of_not_mem point h2
        have hn4 := chartCoeff_neg_of_not_mem point h4
        have hp5 := chartCoeff_pos_of_mem point h5
        have hprod : 0 < chartCoeff point.mass point.weight selected 2
            * chartCoeff point.mass point.weight selected 4
            * chartCoeff point.mass point.weight selected 5 :=
          mul_pos (mul_pos_of_neg_of_neg hn2 hn4) hp5
        exact False.elim ((not_lt_of_ge hpar) (mul_neg_of_neg_of_pos hslide hprod))
      · exact Or.inl ⟨h2, h4, h5⟩

/-! ## Exact finite survivor families -/

/-- The seven off-line card-three selections with odd join parity. -/
def ThreeLinesPositiveRankOneTripleFamily (selected : Finset (Fin 6)) : Prop :=
  selected = {0, 2, 3} ∨ selected = {1, 2, 3} ∨
  selected = {0, 1, 4} ∨ selected = {1, 3, 4} ∨
  selected = {0, 1, 5} ∨ selected = {0, 3, 5} ∨
  selected = {2, 4, 5}

/-- The ten off-line card-three selections with even join parity. -/
def ThreeLinesNegativeRankOneTripleFamily (selected : Finset (Fin 6)) : Prop :=
  selected = {0, 1, 3} ∨
  selected = {0, 2, 4} ∨ selected = {0, 2, 5} ∨ selected = {0, 4, 5} ∨
  selected = {1, 2, 4} ∨ selected = {1, 2, 5} ∨ selected = {1, 4, 5} ∨
  selected = {2, 3, 4} ∨ selected = {2, 3, 5} ∨ selected = {3, 4, 5}

/-- Pure finite census: card three, off all three dependent lines, and odd join
parity is exactly the seven-member positive family. -/
theorem threeLinesPositiveRankOneTripleFamily_of_card_offLines_odd
    (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hfirst : selected ≠ ({0, 1, 2} : Finset (Fin 6)))
    (hsecond : selected ≠ ({0, 3, 4} : Finset (Fin 6)))
    (hthird : selected ≠ ({1, 3, 5} : Finset (Fin 6)))
    (hodd : ThreeLinesOddJoinSelection selected) :
    ThreeLinesPositiveRankOneTripleFamily selected := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    rfl⟩ := Finset.card_eq_three.mp hcard
  fin_cases first <;> fin_cases second <;> fin_cases third <;>
    simp_all [ThreeLinesOddJoinSelection, ThreeLinesPositiveRankOneTripleFamily]
  all_goals
    first
    | exact False.elim (hfirst (by decide))
    | exact False.elim (hsecond (by decide))
    | exact False.elim (hthird (by decide))
    | decide

/-- Pure finite census: card three, off all three dependent lines, and even
join parity is exactly the ten-member negative family. -/
theorem threeLinesNegativeRankOneTripleFamily_of_card_offLines_even
    (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hfirst : selected ≠ ({0, 1, 2} : Finset (Fin 6)))
    (hsecond : selected ≠ ({0, 3, 4} : Finset (Fin 6)))
    (hthird : selected ≠ ({1, 3, 5} : Finset (Fin 6)))
    (heven : ThreeLinesEvenJoinSelection selected) :
    ThreeLinesNegativeRankOneTripleFamily selected := by
  obtain ⟨first, second, third, hfirstSecond, hfirstThird, hsecondThird,
    rfl⟩ := Finset.card_eq_three.mp hcard
  fin_cases first <;> fin_cases second <;> fin_cases third <;>
    simp_all [ThreeLinesEvenJoinSelection, ThreeLinesNegativeRankOneTripleFamily]
  all_goals
    first
    | exact False.elim (hfirst (by decide))
    | exact False.elim (hsecond (by decide))
    | exact False.elim (hthird (by decide))
    | decide

/-- **THE POSITIVE-SLIDE RANK-ONE CENSUS.**  An off-line card-three witness at
a nonnegative rank-one wall belongs to exactly the seven named positive-slide
candidates. -/
theorem threeLinesPositiveRankOneTripleFamily_of_wall {slide : ℝ}
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    {axis : Fin 3 → ℝ} {scale : ℝ} (hslide : 0 < slide) (hscale : 0 ≤ scale)
    (heq : directionChartGap (threeLinesDirection slide) point.mass point.weight selected
      = scale • atomMatrix axis)
    (hcard : selected.card = 3)
    (hfirst : selected ≠ ({0, 1, 2} : Finset (Fin 6)))
    (hsecond : selected ≠ ({0, 3, 4} : Finset (Fin 6)))
    (hthird : selected ≠ ({1, 3, 5} : Finset (Fin 6))) :
    ThreeLinesPositiveRankOneTripleFamily selected :=
  threeLinesPositiveRankOneTripleFamily_of_card_offLines_odd selected hcard
    hfirst hsecond hthird
    (threeLinesRankOne_oddJoins_of_slide_pos point hslide hscale heq)

/-- **THE NEGATIVE-SLIDE RANK-ONE CENSUS.**  An off-line card-three witness at
a nonnegative rank-one wall belongs to exactly the ten named negative-slide
candidates. -/
theorem threeLinesNegativeRankOneTripleFamily_of_wall {slide : ℝ}
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    {axis : Fin 3 → ℝ} {scale : ℝ} (hslide : slide < 0) (hscale : 0 ≤ scale)
    (heq : directionChartGap (threeLinesDirection slide) point.mass point.weight selected
      = scale • atomMatrix axis)
    (hcard : selected.card = 3)
    (hfirst : selected ≠ ({0, 1, 2} : Finset (Fin 6)))
    (hsecond : selected ≠ ({0, 3, 4} : Finset (Fin 6)))
    (hthird : selected ≠ ({1, 3, 5} : Finset (Fin 6))) :
    ThreeLinesNegativeRankOneTripleFamily selected :=
  threeLinesNegativeRankOneTripleFamily_of_card_offLines_even selected hcard
    hfirst hsecond hthird
    (threeLinesRankOne_evenJoins_of_slide_neg point hslide hscale heq)

end Gtz
