import Gtz.Wave.ThreeLinesDominanceNoGo

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The slide enters the three-lines chart as one quadratic

`Gtz.threeLinesCoefficientMatrix` puts the three joins `2`, `4` and `5` in the
three off-diagonal slots and the three vertices `0`, `1` and `3` on the diagonal.
The slide reaches only the coefficient of label `5`, as `slide * c 5` off the
diagonal and `slide ^ 2 * c 5` on it.  This file spends that fact.

* **Two of the three leading minors are slide-free.**  The slide sits in row and
  column `2` alone, so the first and second leading minors never see it.
* **The third is a QUADRATIC in the slide**, and its `slide ^ 2 * (c 5) ^ 2`
  terms cancel.  Its leading coefficient is `c 5` times the second minor with
  `c 5` deleted, written here as `Gtz.threeLinesReducedMinorTwo`.
* **The second minor splits**: `d2 = reduced + d1 * c 5`.  At a selection holding
  label `5` the excess is positive, so a positive reduced minor pays for the
  second minor outright.
* **A division-free threshold cell.**  On the fundamental domain a selection
  holding label `5` is strictly positive definite once the leading coefficient
  beats the other two in absolute value, scaled by `|slide|`.

The cell is a genuine sufficient condition and not the decision procedure: it
gives away the quadratic's roots and asks only that the slide be past a bound
read off the coefficients.
-/

namespace Gtz

open Matrix

/-! ## 1. The three leading minors of the universal coefficient matrix -/

/-- The first leading minor of the three-lines coefficient matrix.  It carries
no slide. -/
noncomputable def threeLinesMinorOne (coefficient : Fin 6 → ℝ) : ℝ :=
  coefficient 0 + coefficient 2 + coefficient 4

/-- The second leading minor of the three-lines coefficient matrix.  It carries
no slide either, because the slide sits in row and column `2` alone. -/
noncomputable def threeLinesMinorTwo (coefficient : Fin 6 → ℝ) : ℝ :=
  threeLinesMinorOne coefficient * (coefficient 1 + coefficient 2 + coefficient 5)
    - coefficient 2 ^ 2

/-- **The second minor with label `5` deleted.**  This is the object that governs
the large-slide behaviour, and it reads only the coefficients `0`, `1`, `2`
and `4`. -/
noncomputable def threeLinesReducedMinorTwo (coefficient : Fin 6 → ℝ) : ℝ :=
  threeLinesMinorOne coefficient * (coefficient 1 + coefficient 2) - coefficient 2 ^ 2

/-- **The second minor splits along label `5`.**  No slide appears on either
side. -/
theorem threeLinesMinorTwo_eq_reduced_add (coefficient : Fin 6 → ℝ) :
    threeLinesMinorTwo coefficient
      = threeLinesReducedMinorTwo coefficient
        + threeLinesMinorOne coefficient * coefficient 5 := by
  simp only [threeLinesMinorTwo, threeLinesReducedMinorTwo, threeLinesMinorOne]
  ring

/-- **The reduced minor pays for the second minor.**  At a selection holding
label `5` the coefficient there is an excess, so a positive first minor and a
positive reduced minor give the second minor for free. -/
theorem threeLinesMinorTwo_pos_of_reduced (coefficient : Fin 6 → ℝ)
    (hone : 0 < threeLinesMinorOne coefficient)
    (hreduced : 0 < threeLinesReducedMinorTwo coefficient)
    (hfive : 0 < coefficient 5) : 0 < threeLinesMinorTwo coefficient := by
  rw [threeLinesMinorTwo_eq_reduced_add]
  have : 0 < threeLinesMinorOne coefficient * coefficient 5 := mul_pos hone hfive
  linarith

/-! ## 2. The three coefficients of the slide quadratic -/

/-- The coefficient of `slide ^ 2` in the third leading minor.  The
`slide ^ 2 * (c 5) ^ 2` contributions cancel, which is why this is the reduced
minor and not the full one. -/
noncomputable def threeLinesSlideSquareCoeff (coefficient : Fin 6 → ℝ) : ℝ :=
  coefficient 5 * threeLinesReducedMinorTwo coefficient

/-- The coefficient of `slide` in the third leading minor.  It is the product of
the three joins, doubled. -/
noncomputable def threeLinesSlideLinearCoeff (coefficient : Fin 6 → ℝ) : ℝ :=
  2 * coefficient 2 * coefficient 4 * coefficient 5

/-- The slide-free part of the third leading minor. -/
noncomputable def threeLinesSlideConstCoeff (coefficient : Fin 6 → ℝ) : ℝ :=
  (coefficient 3 + coefficient 4) * threeLinesMinorTwo coefficient
    - (coefficient 1 + coefficient 2 + coefficient 5) * coefficient 4 ^ 2

/-- The matrix is symmetric, whatever the slide. -/
theorem threeLinesCoefficientMatrix_transpose (slide : ℝ) (coefficient : Fin 6 → ℝ) :
    (threeLinesCoefficientMatrix slide coefficient)ᵀ
      = threeLinesCoefficientMatrix slide coefficient := by
  ext i j
  fin_cases i <;> fin_cases j <;> rfl

/-- **The first leading minor, read off the matrix.**  No slide. -/
theorem threeLinesCoefficientMatrix_minorOne (slide : ℝ) (coefficient : Fin 6 → ℝ) :
    (threeLinesCoefficientMatrix slide coefficient) 0 0
      = threeLinesMinorOne coefficient := rfl

/-- **The second leading minor, read off the matrix.**  No slide. -/
theorem threeLinesCoefficientMatrix_minorTwo (slide : ℝ) (coefficient : Fin 6 → ℝ) :
    (threeLinesCoefficientMatrix slide coefficient) 0 0
        * (threeLinesCoefficientMatrix slide coefficient) 1 1
      - (threeLinesCoefficientMatrix slide coefficient) 0 1 ^ 2
      = threeLinesMinorTwo coefficient := by
  show (coefficient 0 + coefficient 2 + coefficient 4)
      * (coefficient 1 + coefficient 2 + coefficient 5) - coefficient 2 ^ 2 = _
  simp only [threeLinesMinorTwo, threeLinesMinorOne]

/-- **THE DECOMPOSITION.**  The third leading minor is a quadratic in the slide,
with the reduced second minor as its leading coefficient. -/
theorem threeLinesCoefficientMatrix_minorThree (slide : ℝ) (coefficient : Fin 6 → ℝ) :
    (threeLinesCoefficientMatrix slide coefficient) 0 0
          * (threeLinesCoefficientMatrix slide coefficient) 1 1
          * (threeLinesCoefficientMatrix slide coefficient) 2 2
        - (threeLinesCoefficientMatrix slide coefficient) 0 0
          * (threeLinesCoefficientMatrix slide coefficient) 1 2 ^ 2
        - (threeLinesCoefficientMatrix slide coefficient) 0 1 ^ 2
          * (threeLinesCoefficientMatrix slide coefficient) 2 2
        + 2 * (threeLinesCoefficientMatrix slide coefficient) 0 1
          * (threeLinesCoefficientMatrix slide coefficient) 0 2
          * (threeLinesCoefficientMatrix slide coefficient) 1 2
        - (threeLinesCoefficientMatrix slide coefficient) 0 2 ^ 2
          * (threeLinesCoefficientMatrix slide coefficient) 1 1
      = threeLinesSlideSquareCoeff coefficient * slide ^ 2
        + threeLinesSlideLinearCoeff coefficient * slide
        + threeLinesSlideConstCoeff coefficient := by
  show (coefficient 0 + coefficient 2 + coefficient 4)
        * (coefficient 1 + coefficient 2 + coefficient 5)
        * (coefficient 3 + coefficient 4 + slide ^ 2 * coefficient 5)
      - (coefficient 0 + coefficient 2 + coefficient 4) * (slide * coefficient 5) ^ 2
      - coefficient 2 ^ 2 * (coefficient 3 + coefficient 4 + slide ^ 2 * coefficient 5)
      + 2 * coefficient 2 * coefficient 4 * (slide * coefficient 5)
      - coefficient 4 ^ 2 * (coefficient 1 + coefficient 2 + coefficient 5) = _
  simp only [threeLinesSlideSquareCoeff, threeLinesSlideLinearCoeff,
    threeLinesSlideConstCoeff, threeLinesReducedMinorTwo, threeLinesMinorTwo,
    threeLinesMinorOne]
  ring

/-! ## 3. The positivity engine for the quadratic -/

/-- **The tail is dominated past the threshold.**  On the fundamental domain, a
bound on the sum of the two lower coefficients scaled by the slide controls the
whole linear-plus-constant tail against the quadratic term. -/
theorem abs_slide_tail_lt (slide bound linear constant : ℝ) (hfund : 1 ≤ |slide|)
    (hthreshold : |linear| + |constant| < bound * |slide|) :
    |linear * slide + constant| < bound * slide ^ 2 := by
  have hpos : (0 : ℝ) < |slide| := lt_of_lt_of_le one_pos hfund
  have hsq : |slide| * |slide| = slide ^ 2 := by
    rw [← sq_abs]; ring
  have hstep : (|linear| + |constant|) * |slide| < bound * |slide| * |slide| :=
    mul_lt_mul_of_pos_right hthreshold hpos
  have hconst : |constant| ≤ |constant| * |slide| := by
    nlinarith [abs_nonneg constant]
  have htri : |linear * slide + constant| ≤ |linear * slide| + |constant| :=
    abs_add_le _ _
  have hmul : |linear * slide| = |linear| * |slide| := abs_mul _ _
  have hchain : |linear| * |slide| + |constant| ≤ (|linear| + |constant|) * |slide| := by
    nlinarith
  calc |linear * slide + constant| ≤ |linear * slide| + |constant| := htri
    _ = |linear| * |slide| + |constant| := by rw [hmul]
    _ ≤ (|linear| + |constant|) * |slide| := hchain
    _ < bound * |slide| * |slide| := hstep
    _ = bound * slide ^ 2 := by rw [mul_assoc, hsq]

/-- **The threshold makes the quadratic positive.**  A positive leading
coefficient beating the other two in absolute value, scaled by the slide, is
enough.  No square root and no division. -/
theorem quadratic_pos_of_slide_threshold (slide square linear constant : ℝ)
    (hfund : 1 ≤ |slide|) (_hsquare : 0 < square)
    (hthreshold : |linear| + |constant| < square * |slide|) :
    0 < square * slide ^ 2 + linear * slide + constant := by
  have htail := abs_slide_tail_lt slide square linear constant hfund hthreshold
  have hlow : -(square * slide ^ 2) < linear * slide + constant := by
    have := neg_lt_of_abs_lt htail
    linarith
  linarith

/-- **The threshold makes the quadratic NEGATIVE when the leading coefficient
is.**  The same bound, read with the sign reversed.  This is the half that
forbids a selection rather than certifying one. -/
theorem quadratic_neg_of_slide_threshold (slide square linear constant : ℝ)
    (hfund : 1 ≤ |slide|) (_hsquare : square < 0)
    (hthreshold : |linear| + |constant| < -square * |slide|) :
    square * slide ^ 2 + linear * slide + constant < 0 := by
  have htail := abs_slide_tail_lt slide (-square) linear constant hfund hthreshold
  have hhigh : linear * slide + constant < -square * slide ^ 2 := by
    have := lt_of_abs_lt htail
    linarith
  linarith

/-! ## 4. The threshold cell -/

/-- **The slide-threshold cell.**  Four conditions, all division-free: the
fundamental domain, a positive first minor, a positive reduced second minor, a
positive coefficient at label `5`, and the threshold on the slide. -/
def ThreeLinesSlideThreshold (slide : ℝ) (coefficient : Fin 6 → ℝ) : Prop :=
  1 ≤ |slide| ∧ 0 < threeLinesMinorOne coefficient
    ∧ 0 < threeLinesReducedMinorTwo coefficient ∧ 0 < coefficient 5
    ∧ |threeLinesSlideLinearCoeff coefficient| + |threeLinesSlideConstCoeff coefficient|
      < threeLinesSlideSquareCoeff coefficient * |slide|

/-- **The cell fires on the universal matrix.** -/
theorem posDef_threeLinesCoefficientMatrix_of_slideThreshold (slide : ℝ)
    (coefficient : Fin 6 → ℝ) (hcell : ThreeLinesSlideThreshold slide coefficient) :
    (threeLinesCoefficientMatrix slide coefficient).PosDef := by
  obtain ⟨hfund, hone, hreduced, hfive, hthreshold⟩ := hcell
  have hsquare : 0 < threeLinesSlideSquareCoeff coefficient :=
    mul_pos hfive hreduced
  have htwo : 0 < threeLinesMinorTwo coefficient :=
    threeLinesMinorTwo_pos_of_reduced coefficient hone hreduced hfive
  refine (posDef_finThree_iff_leadingMinors _
    (threeLinesCoefficientMatrix_transpose slide coefficient)).mpr ⟨?_, ?_, ?_⟩
  · rw [threeLinesCoefficientMatrix_minorOne]; exact hone
  · rw [threeLinesCoefficientMatrix_minorTwo]; exact htwo
  · rw [threeLinesCoefficientMatrix_minorThree]
    exact quadratic_pos_of_slide_threshold slide _ _ _ hfund hsquare hthreshold

/-- **The cell fires at the chart.** -/
theorem posDef_directionChartGap_threeLines_of_slideThreshold (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hweightNe : ∀ label, weight label ≠ 0)
    (selected : Finset (Fin 6))
    (hcell : ThreeLinesSlideThreshold slide (threeLinesChartCoefficient mass weight selected)) :
    (directionChartGap (threeLinesDirection slide) mass weight selected).PosDef := by
  rw [directionChartGap_threeLines_eq slide mass weight hweightNe]
  exact posDef_threeLinesCoefficientMatrix_of_slideThreshold slide _ hcell

/-! ## 5. Label five supplies the positive coefficient -/

/-- At a selection holding label `5` the coefficient there is the excess, which
is positive whenever the mass is positive and the weight lies strictly between
zero and one. -/
theorem threeLinesChartCoefficient_five_pos (mass weight : Fin 6 → ℝ)
    (selected : Finset (Fin 6)) (hmem : (5 : Fin 6) ∈ selected)
    (hmass : 0 < mass 5) (hweightPos : 0 < weight 5) (hweightLt : weight 5 < 1) :
    0 < threeLinesChartCoefficient mass weight selected 5 := by
  rw [threeLinesChartCoefficient_of_mem mass weight hmem]
  exact chartExcess_pos mass weight 5 hmass hweightPos hweightLt

/-- **The cell at a selection holding label `5`.**  The positivity at `5` is
automatic, so the caller supplies three conditions rather than four. -/
theorem posDef_directionChartGap_threeLines_of_five_of_threshold (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hweightPos : ∀ label, 0 < weight label)
    (hweightLt : ∀ label, weight label < 1) (hmass : ∀ label, 0 < mass label)
    (selected : Finset (Fin 6)) (hmem : (5 : Fin 6) ∈ selected) (hfund : 1 ≤ |slide|)
    (hone : 0 < threeLinesMinorOne (threeLinesChartCoefficient mass weight selected))
    (hreduced :
      0 < threeLinesReducedMinorTwo (threeLinesChartCoefficient mass weight selected))
    (hthreshold :
      |threeLinesSlideLinearCoeff (threeLinesChartCoefficient mass weight selected)|
        + |threeLinesSlideConstCoeff (threeLinesChartCoefficient mass weight selected)|
        < threeLinesSlideSquareCoeff (threeLinesChartCoefficient mass weight selected)
          * |slide|) :
    (directionChartGap (threeLinesDirection slide) mass weight selected).PosDef := by
  refine posDef_directionChartGap_threeLines_of_slideThreshold slide mass weight
    (fun label => ne_of_gt (hweightPos label)) selected ⟨hfund, hone, hreduced, ?_, hthreshold⟩
  exact threeLinesChartCoefficient_five_pos mass weight selected hmem (hmass 5)
    (hweightPos 5) (hweightLt 5)

/-! ## 6. The asymptotic reading -/

/-- **Past an explicit slide the cell fires.**  Given a positive first minor, a
positive reduced minor and a positive coefficient at label `5`, every slide whose
absolute value clears the stated bound puts the selection strictly inside.  This
is the large-slide half of a two-region cover, and the bound is read off the
coefficients alone. -/
theorem posDef_threeLinesCoefficientMatrix_of_slide_large (slide : ℝ)
    (coefficient : Fin 6 → ℝ) (hone : 0 < threeLinesMinorOne coefficient)
    (hreduced : 0 < threeLinesReducedMinorTwo coefficient) (hfive : 0 < coefficient 5)
    (hfund : 1 ≤ |slide|)
    (hlarge : (|threeLinesSlideLinearCoeff coefficient|
        + |threeLinesSlideConstCoeff coefficient|)
        / threeLinesSlideSquareCoeff coefficient < |slide|) :
    (threeLinesCoefficientMatrix slide coefficient).PosDef := by
  have hsquare : 0 < threeLinesSlideSquareCoeff coefficient := mul_pos hfive hreduced
  refine posDef_threeLinesCoefficientMatrix_of_slideThreshold slide coefficient
    ⟨hfund, hone, hreduced, hfive, ?_⟩
  rw [div_lt_iff₀ hsquare] at hlarge
  linarith

/-- **The threshold is attained.**  For every coefficient family with a positive
first minor, a positive reduced minor and a positive label `5`, there is a slide
bound past which the selection is strictly positive definite. -/
theorem exists_slide_bound_of_reducedMinorTwo_pos (coefficient : Fin 6 → ℝ)
    (hone : 0 < threeLinesMinorOne coefficient)
    (hreduced : 0 < threeLinesReducedMinorTwo coefficient) (hfive : 0 < coefficient 5) :
    ∃ bound : ℝ, ∀ slide : ℝ, 1 ≤ |slide| → bound < |slide| →
      (threeLinesCoefficientMatrix slide coefficient).PosDef := by
  refine ⟨(|threeLinesSlideLinearCoeff coefficient|
    + |threeLinesSlideConstCoeff coefficient|)
    / threeLinesSlideSquareCoeff coefficient, fun slide hfund hlarge => ?_⟩
  exact posDef_threeLinesCoefficientMatrix_of_slide_large slide coefficient hone hreduced
    hfive hfund hlarge

/-- **The reduced minor is exactly the obstruction.**  If the reduced second
minor is not positive, the quadratic's leading coefficient is not positive at a
selection holding label `5`, so no slide bound of this shape exists. -/
theorem threeLinesSlideSquareCoeff_nonpos_of_reduced_nonpos (coefficient : Fin 6 → ℝ)
    (hfive : 0 < coefficient 5) (hreduced : threeLinesReducedMinorTwo coefficient ≤ 0) :
    threeLinesSlideSquareCoeff coefficient ≤ 0 := by
  rw [threeLinesSlideSquareCoeff]
  exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hfive) hreduced

/-! ## 7. The converse: a negative coefficient at label five forbids the selection -/

/-- **The anti-cell.**  A selection whose coefficient at label `5` is negative,
and whose reduced second minor is positive, is NOT positive definite past the
threshold.  The third minor runs to minus infinity in the slide. -/
theorem not_posDef_threeLinesCoefficientMatrix_of_slide_threshold (slide : ℝ)
    (coefficient : Fin 6 → ℝ) (hfund : 1 ≤ |slide|)
    (hreduced : 0 < threeLinesReducedMinorTwo coefficient) (hfive : coefficient 5 < 0)
    (hthreshold : |threeLinesSlideLinearCoeff coefficient|
        + |threeLinesSlideConstCoeff coefficient|
      < -threeLinesSlideSquareCoeff coefficient * |slide|) :
    ¬ (threeLinesCoefficientMatrix slide coefficient).PosDef := by
  intro hposDef
  have hsquare : threeLinesSlideSquareCoeff coefficient < 0 := by
    rw [threeLinesSlideSquareCoeff]
    exact mul_neg_of_neg_of_pos hfive hreduced
  have hneg := quadratic_neg_of_slide_threshold slide _ _ _ hfund hsquare hthreshold
  have hminors := (posDef_finThree_iff_leadingMinors _
    (threeLinesCoefficientMatrix_transpose slide coefficient)).mp hposDef
  have hthird := hminors.2.2
  rw [threeLinesCoefficientMatrix_minorThree] at hthird
  linarith

/-- **The large-slide dichotomy.**  At a coefficient family with a positive
reduced second minor, the sign of the coefficient at label `5` decides the
selection past the threshold: positive certifies, negative forbids. -/
theorem threeLinesSlide_dichotomy (slide : ℝ) (coefficient : Fin 6 → ℝ)
    (hfund : 1 ≤ |slide|) (hone : 0 < threeLinesMinorOne coefficient)
    (hreduced : 0 < threeLinesReducedMinorTwo coefficient)
    (hthreshold : |threeLinesSlideLinearCoeff coefficient|
        + |threeLinesSlideConstCoeff coefficient|
      < |threeLinesSlideSquareCoeff coefficient| * |slide|) :
    (0 < coefficient 5 → (threeLinesCoefficientMatrix slide coefficient).PosDef)
      ∧ (coefficient 5 < 0 → ¬ (threeLinesCoefficientMatrix slide coefficient).PosDef) := by
  constructor
  · intro hfive
    have hsquare : 0 < threeLinesSlideSquareCoeff coefficient := mul_pos hfive hreduced
    refine posDef_threeLinesCoefficientMatrix_of_slideThreshold slide coefficient
      ⟨hfund, hone, hreduced, hfive, ?_⟩
    rwa [abs_of_pos hsquare] at hthreshold
  · intro hfive
    have hsquare : threeLinesSlideSquareCoeff coefficient < 0 := by
      rw [threeLinesSlideSquareCoeff]
      exact mul_neg_of_neg_of_pos hfive hreduced
    refine not_posDef_threeLinesCoefficientMatrix_of_slide_threshold slide coefficient
      hfund hreduced hfive ?_
    rwa [abs_of_neg hsquare] at hthreshold

/-! ## 8. The support of the threshold cell -/

/-- The cell forces label `5` into the selection, because the coefficient there
must be positive and a missing label reads minus its mass. -/
theorem mem_five_of_threeLinesSlideThreshold (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hmass : 0 < mass 5) (selected : Finset (Fin 6))
    (hcell : ThreeLinesSlideThreshold slide (threeLinesChartCoefficient mass weight selected)) :
    (5 : Fin 6) ∈ selected := by
  by_contra hnot
  obtain ⟨-, -, -, hfive, -⟩ := hcell
  rw [threeLinesChartCoefficient_of_notMem mass weight hnot] at hfive
  linarith

/-- **A selection missing both `1` and `2` can never fire the cell.**  Their two
coefficients then read minus their masses, so the reduced second minor is a
positive multiple of a negative number minus a square. -/
theorem not_threeLinesSlideThreshold_of_notMem_one_of_notMem_two (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hmassOne : 0 < mass 1) (hmassTwo : 0 < mass 2)
    (selected : Finset (Fin 6)) (hone : (1 : Fin 6) ∉ selected)
    (htwo : (2 : Fin 6) ∉ selected) :
    ¬ ThreeLinesSlideThreshold slide (threeLinesChartCoefficient mass weight selected) := by
  rintro ⟨-, hminorOne, hreduced, -, -⟩
  rw [threeLinesReducedMinorTwo, threeLinesChartCoefficient_of_notMem mass weight hone,
    threeLinesChartCoefficient_of_notMem mass weight htwo] at hreduced
  nlinarith [sq_nonneg (mass 2)]

/-- **THE SUPPORT THEOREM FOR THE THRESHOLD CELL.**  The cell fires only at a
selection that holds label `5` and meets `{1, 2}`.  Of the twenty card-three
selections exactly seven qualify, and one of those is a line. -/
theorem threeLinesSlideThreshold_support (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (selected : Finset (Fin 6))
    (hcell : ThreeLinesSlideThreshold slide (threeLinesChartCoefficient mass weight selected)) :
    (5 : Fin 6) ∈ selected ∧ ((1 : Fin 6) ∈ selected ∨ (2 : Fin 6) ∈ selected) := by
  refine ⟨mem_five_of_threeLinesSlideThreshold slide mass weight (hmass 5) selected hcell, ?_⟩
  by_contra hnot
  push Not at hnot
  exact not_threeLinesSlideThreshold_of_notMem_one_of_notMem_two slide mass weight
    (hmass 1) (hmass 2) selected hnot.1 hnot.2 hcell

/-- The seven card-three selections that hold label `5` and meet `{1, 2}`. -/
theorem eq_of_card_three_of_mem_five_of_meets_oneTwo (selected : Finset (Fin 6))
    (hcard : selected.card = 3) (hfive : (5 : Fin 6) ∈ selected)
    (hmeet : (1 : Fin 6) ∈ selected ∨ (2 : Fin 6) ∈ selected) :
    selected = ({0, 1, 5} : Finset (Fin 6)) ∨ selected = ({0, 2, 5} : Finset (Fin 6)) ∨
      selected = ({1, 2, 5} : Finset (Fin 6)) ∨ selected = ({1, 3, 5} : Finset (Fin 6)) ∨
      selected = ({1, 4, 5} : Finset (Fin 6)) ∨ selected = ({2, 3, 5} : Finset (Fin 6)) ∨
      selected = ({2, 4, 5} : Finset (Fin 6)) := by
  revert hcard hfive hmeet
  revert selected
  decide

/-- **The cell's support, enumerated.**  Thirteen of the twenty card-three
selections are unreachable by the threshold cell for every chart point and every
slide on the fundamental domain. -/
theorem threeLinesSlideThreshold_eq_one_of_seven (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (selected : Finset (Fin 6)) (hcard : selected.card = 3)
    (hcell : ThreeLinesSlideThreshold slide (threeLinesChartCoefficient mass weight selected)) :
    selected = ({0, 1, 5} : Finset (Fin 6)) ∨ selected = ({0, 2, 5} : Finset (Fin 6)) ∨
      selected = ({1, 2, 5} : Finset (Fin 6)) ∨ selected = ({1, 3, 5} : Finset (Fin 6)) ∨
      selected = ({1, 4, 5} : Finset (Fin 6)) ∨ selected = ({2, 3, 5} : Finset (Fin 6)) ∨
      selected = ({2, 4, 5} : Finset (Fin 6)) := by
  obtain ⟨hfive, hmeet⟩ :=
    threeLinesSlideThreshold_support slide mass weight hmass selected hcell
  exact eq_of_card_three_of_mem_five_of_meets_oneTwo selected hcard hfive hmeet

/-- **The three off-line label-five selections the cell can never reach.**  Each
misses both `1` and `2`, so its reduced second minor is negative whatever the
chart point and whatever the slide. -/
theorem not_threeLinesSlideThreshold_zeroThreeFive (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hmassOne : 0 < mass 1) (hmassTwo : 0 < mass 2) :
    ¬ ThreeLinesSlideThreshold slide
      (threeLinesChartCoefficient mass weight ({0, 3, 5} : Finset (Fin 6))) :=
  not_threeLinesSlideThreshold_of_notMem_one_of_notMem_two slide mass weight hmassOne
    hmassTwo _ (by decide) (by decide)

theorem not_threeLinesSlideThreshold_zeroFourFive (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hmassOne : 0 < mass 1) (hmassTwo : 0 < mass 2) :
    ¬ ThreeLinesSlideThreshold slide
      (threeLinesChartCoefficient mass weight ({0, 4, 5} : Finset (Fin 6))) :=
  not_threeLinesSlideThreshold_of_notMem_one_of_notMem_two slide mass weight hmassOne
    hmassTwo _ (by decide) (by decide)

theorem not_threeLinesSlideThreshold_threeFourFive (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hmassOne : 0 < mass 1) (hmassTwo : 0 < mass 2) :
    ¬ ThreeLinesSlideThreshold slide
      (threeLinesChartCoefficient mass weight ({3, 4, 5} : Finset (Fin 6))) :=
  not_threeLinesSlideThreshold_of_notMem_one_of_notMem_two slide mass weight hmassOne
    hmassTwo _ (by decide) (by decide)

/-! ## 9. Why label five is forced: every selection missing it dies in the slide -/

/-- **A selection missing label `5` fails past the threshold.**  Its coefficient
there reads minus the mass, so the quadratic opens downward and the third minor
is eventually negative.  This is the structural reason the cover must be built
from selections holding label `5`. -/
theorem not_posDef_directionChartGap_threeLines_of_notMem_five (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hweightNe : ∀ label, weight label ≠ 0)
    (hmassFive : 0 < mass 5) (selected : Finset (Fin 6)) (hnot : (5 : Fin 6) ∉ selected)
    (hfund : 1 ≤ |slide|)
    (hreduced :
      0 < threeLinesReducedMinorTwo (threeLinesChartCoefficient mass weight selected))
    (hthreshold :
      |threeLinesSlideLinearCoeff (threeLinesChartCoefficient mass weight selected)|
        + |threeLinesSlideConstCoeff (threeLinesChartCoefficient mass weight selected)|
        < -threeLinesSlideSquareCoeff (threeLinesChartCoefficient mass weight selected)
          * |slide|) :
    ¬ (directionChartGap (threeLinesDirection slide) mass weight selected).PosDef := by
  rw [directionChartGap_threeLines_eq slide mass weight hweightNe]
  refine not_posDef_threeLinesCoefficientMatrix_of_slide_threshold slide _ hfund hreduced
    ?_ hthreshold
  rw [threeLinesChartCoefficient_of_notMem mass weight hnot]
  linarith

/-- **The vertex triple dies in the slide.**  `{0, 1, 3}` carries all three
vertices and no join, so its coefficient at label `5` is minus the mass and the
quadratic opens downward.  This strengthens the dominance-level ceiling to a
positive-definiteness-level one. -/
theorem not_posDef_directionChartGap_threeLinesVertex_of_slide_threshold (slide : ℝ)
    (mass weight : Fin 6 → ℝ) (hweightNe : ∀ label, weight label ≠ 0)
    (hmassFive : 0 < mass 5) (hfund : 1 ≤ |slide|)
    (hreduced : 0 < threeLinesReducedMinorTwo
      (threeLinesChartCoefficient mass weight ({0, 1, 3} : Finset (Fin 6))))
    (hthreshold :
      |threeLinesSlideLinearCoeff
          (threeLinesChartCoefficient mass weight ({0, 1, 3} : Finset (Fin 6)))|
        + |threeLinesSlideConstCoeff
          (threeLinesChartCoefficient mass weight ({0, 1, 3} : Finset (Fin 6)))|
        < -threeLinesSlideSquareCoeff
          (threeLinesChartCoefficient mass weight ({0, 1, 3} : Finset (Fin 6))) * |slide|) :
    ¬ (directionChartGap (threeLinesDirection slide) mass weight
      ({0, 1, 3} : Finset (Fin 6))).PosDef :=
  not_posDef_directionChartGap_threeLines_of_notMem_five slide mass weight hweightNe
    hmassFive _ (by decide) hfund hreduced hthreshold

/-- **The label-five dichotomy at the chart.**  With a positive first minor and a
positive reduced second minor, membership of label `5` decides the selection past
the threshold.  Neither half reads a determinant or a root. -/
theorem threeLinesSlide_chart_dichotomy (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightPos : ∀ label, 0 < weight label) (hweightLt : ∀ label, weight label < 1)
    (hmass : ∀ label, 0 < mass label) (selected : Finset (Fin 6)) (hfund : 1 ≤ |slide|)
    (hone : 0 < threeLinesMinorOne (threeLinesChartCoefficient mass weight selected))
    (hreduced :
      0 < threeLinesReducedMinorTwo (threeLinesChartCoefficient mass weight selected))
    (hthreshold :
      |threeLinesSlideLinearCoeff (threeLinesChartCoefficient mass weight selected)|
        + |threeLinesSlideConstCoeff (threeLinesChartCoefficient mass weight selected)|
        < |threeLinesSlideSquareCoeff (threeLinesChartCoefficient mass weight selected)|
          * |slide|) :
    ((5 : Fin 6) ∈ selected →
        (directionChartGap (threeLinesDirection slide) mass weight selected).PosDef)
      ∧ ((5 : Fin 6) ∉ selected →
        ¬ (directionChartGap (threeLinesDirection slide) mass weight selected).PosDef) := by
  have hweightNe : ∀ label, weight label ≠ 0 := fun label => ne_of_gt (hweightPos label)
  have hdich := threeLinesSlide_dichotomy slide
    (threeLinesChartCoefficient mass weight selected) hfund hone hreduced hthreshold
  constructor
  · intro hmem
    rw [directionChartGap_threeLines_eq slide mass weight hweightNe]
    refine hdich.1 ?_
    exact threeLinesChartCoefficient_five_pos mass weight selected hmem (hmass 5)
      (hweightPos 5) (hweightLt 5)
  · intro hnot
    rw [directionChartGap_threeLines_eq slide mass weight hweightNe]
    refine hdich.2 ?_
    rw [threeLinesChartCoefficient_of_notMem mass weight hnot]
    have := hmass 5
    linarith

end Gtz
