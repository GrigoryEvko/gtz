import Gtz.Design.ThreeLinesAxisLaw
import Gtz.LinAlg.ProjectionDiagonalDominance
import Gtz.Wave.ThreeLinesOffLinesWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The star family of the three-lines chart, and the failure of its cover

The Cauchy-Binet law `Gtz.threeLinesBasisDeterminant` weights each independent
triple by its squared bracket.  Twelve triples carry weight `1`.  Four carry
`slide ^ 2`, and the free triple carries `(1 + slide) ^ 2`.  Those five are the
STAR FAMILY, and on the fundamental domain `1 <= |slide|` every star weight is
at least one.  The star is exactly the set of triples whose determinant the
chart amplifies, which is why a census finds them firing more often.

This file proves the star does NOT cover.  At an explicit rational chart point
on the fundamental domain all five star triples fail, and so does every other
triple through the slide-carrying atom `5`, while the vertex triple `{0,1,3}`
is strictly positive definite.  The point is no counterexample to public A2:
what it refutes is the cover.

It also lands two things the corpus lacked.  A general symmetric `3 x 3`
dominance criterion stated on bare entries, and the VERTEX CELL: the vertex
triple is positive definite whenever each coordinate excess beats twice the
joins reaching its axis.  The cell is division-free and reads no determinant.
-/

namespace Gtz

open Finset

/-! ## 1. A dominance criterion on bare entries -/

/-- **Symmetric `3 x 3` dominance.**  Stated on the six entries, so a caller
supplies three inequalities and never touches a matrix. -/
theorem posDef_finThree_of_dominant (a b c d e f : ℝ)
    (h0 : |b| + |c| < a) (h1 : |b| + |e| < d) (h2 : |c| + |e| < f) :
    (!![a, b, c; b, d, e; c, e, f] : Matrix (Fin 3) (Fin 3) ℝ).PosDef := by
  refine posDef_of_diagonallyDominant _ ?_ ?_
  · ext i j; fin_cases i <;> fin_cases j <;> rfl
  · intro i
    fin_cases i <;>
      · rw [Finset.sum_erase_eq_sub (Finset.mem_univ _), Fin.sum_univ_three]
        norm_num [Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
          Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
          Matrix.head_fin_const, Matrix.cons_val_two, Matrix.tail_cons,
          Matrix.head_val', Matrix.of_apply]
        linarith [le_abs_self a, le_abs_self d, le_abs_self f]

/-- A negative determinant refutes positive definiteness. -/
theorem not_posDef_of_det_neg (mat : Matrix (Fin 3) (Fin 3) ℝ) (hdet : mat.det < 0) :
    ¬ mat.PosDef := fun hpos => absurd hpos.det_pos (not_lt.mpr hdet.le)

/-! ## 2. The star family and its amplified brackets -/

/-- The five triples whose Cauchy-Binet bracket the chart amplifies. -/
def threeLinesStarFamily : List (Finset (Fin 6)) :=
  [{0, 1, 5}, {0, 2, 5}, {1, 2, 5}, {1, 4, 5}, {2, 4, 5}]

theorem threeLinesStarFamily_length : threeLinesStarFamily.length = 5 := rfl

theorem threeLinesStarFamily_card (selected : Finset (Fin 6))
    (hmem : selected ∈ threeLinesStarFamily) : selected.card = 3 := by
  fin_cases hmem <;> decide

/-- Every star triple carries the slide atom. -/
theorem threeLinesStarFamily_mem_five (selected : Finset (Fin 6))
    (hmem : selected ∈ threeLinesStarFamily) : (5 : Fin 6) ∈ selected := by
  fin_cases hmem <;> decide

/-- No star triple is one of the three lines. -/
theorem threeLinesStarFamily_not_line (selected : Finset (Fin 6))
    (hmem : selected ∈ threeLinesStarFamily) :
    selected ≠ ({0, 1, 2} : Finset (Fin 6)) ∧
      selected ≠ ({0, 3, 4} : Finset (Fin 6)) ∧
      selected ≠ ({1, 3, 5} : Finset (Fin 6)) := by
  fin_cases hmem <;> exact ⟨by decide, by decide, by decide⟩

/-- The squared bracket the determinant law attaches to a star triple. -/
noncomputable def threeLinesStarWeight (slide : ℝ) (selected : Finset (Fin 6)) : ℝ :=
  if selected = ({2, 4, 5} : Finset (Fin 6)) then (1 + slide) ^ 2 else slide ^ 2

/-- **On the fundamental domain the slide-weighted star triples are amplified.**
Their bracket weight is at least one, which the twelve unit-weight triples never
exceed.  This is the structural reason the star dominates a census. -/
theorem one_le_threeLinesStarWeight_of_fundamental (slide : ℝ) (hfund : 1 ≤ |slide|)
    (selected : Finset (Fin 6)) (hne : selected ≠ ({2, 4, 5} : Finset (Fin 6))) :
    1 ≤ threeLinesStarWeight slide selected := by
  rw [threeLinesStarWeight, if_neg hne, ← sq_abs]
  nlinarith [abs_nonneg slide]

/-! ## 3. The vertex cell -/

/-- **The vertex cell.**  Each coordinate excess beats twice the joins that
reach its axis.  The three joins `2`, `4`, `5` occupy the three off-diagonal
slots of the vertex gap, one each, so dominance is exactly these three
inequalities. -/
def ThreeLinesVertexDominates (slide : ℝ) (mass weight : Fin 6 → ℝ) : Prop :=
  |mass 2| + |mass 4| < chartExcess mass weight 0 - mass 2 - mass 4 ∧
    |mass 2| + |slide * mass 5| < chartExcess mass weight 1 - mass 2 - mass 5 ∧
    |mass 4| + |slide * mass 5| <
      chartExcess mass weight 3 - mass 4 - slide ^ 2 * mass 5

/-- **The vertex cell fires.**  Dominance of the three coordinate excesses makes
the vertex triple strictly positive definite, with no determinant read and no
division. -/
theorem posDef_threeLinesVertex_of_dominates (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (hweightNe : ∀ label, weight label ≠ 0)
    (hdom : ThreeLinesVertexDominates slide mass weight) :
    (directionChartGap (threeLinesDirection slide) mass weight
      ({0, 1, 3} : Finset (Fin 6))).PosDef := by
  classical
  obtain ⟨hzero, hone, hthree⟩ := hdom
  rw [directionChartGap_threeLines_eq slide mass weight hweightNe,
    threeLinesCoefficientMatrix]
  rw [threeLinesChartCoefficient_of_mem _ _ (show (0 : Fin 6) ∈ ({0,1,3} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_mem _ _ (show (1 : Fin 6) ∈ ({0,1,3} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient_of_mem _ _ (show (3 : Fin 6) ∈ ({0,1,3} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient, if_neg (show (2 : Fin 6) ∉ ({0,1,3} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient, if_neg (show (4 : Fin 6) ∉ ({0,1,3} : Finset (Fin 6)) by decide),
    threeLinesChartCoefficient, if_neg (show (5 : Fin 6) ∉ ({0,1,3} : Finset (Fin 6)) by decide)]
  refine posDef_finThree_of_dominant _ _ _ _ _ _ ?_ ?_ ?_
  · rw [abs_neg, abs_neg]; linarith
  · rw [abs_neg, show slide * -mass 5 = -(slide * mass 5) by ring, abs_neg]; linarith
  · rw [abs_neg, show slide * -mass 5 = -(slide * mass 5) by ring, abs_neg]; linarith

/-! ## 4. The witness: the star fails where the vertex succeeds -/

/-- The masses of the star witness. -/
noncomputable def threeLinesStarWitnessMass : Fin 6 → ℝ := ![2, 5, 1, 2, 3, 1]

/-- The weights of the star witness, a probability vector on six labels. -/
noncomputable def threeLinesStarWitnessWeight : Fin 6 → ℝ :=
  ![2/15, 4/15, 1/15, 1/15, 2/15, 1/3]

theorem threeLinesStarWitnessMass_pos (label : Fin 6) :
    0 < threeLinesStarWitnessMass label := by
  fin_cases label <;> norm_num [threeLinesStarWitnessMass]

theorem threeLinesStarWitnessWeight_pos (label : Fin 6) :
    0 < threeLinesStarWitnessWeight label := by
  fin_cases label <;> norm_num [threeLinesStarWitnessWeight]

theorem threeLinesStarWitnessWeight_ne (label : Fin 6) :
    threeLinesStarWitnessWeight label ≠ 0 :=
  ne_of_gt (threeLinesStarWitnessWeight_pos label)

theorem threeLinesStarWitnessWeight_sum :
    ∑ label, threeLinesStarWitnessWeight label = 1 := by
  simp [threeLinesStarWitnessWeight, Fin.sum_univ_six]; norm_num

/-- **The witness chart point**, at slide one, on the fundamental domain. -/
noncomputable def threeLinesStarWitness : DirectionChartPoint 6 where
  mass := threeLinesStarWitnessMass
  weight := threeLinesStarWitnessWeight
  mass_pos := threeLinesStarWitnessMass_pos
  weight_pos := threeLinesStarWitnessWeight_pos
  weight_sum_one := threeLinesStarWitnessWeight_sum

/-- The star triple `{0, 1, 5}` has a negative determinant at the witness. -/
theorem threeLinesStarWitness_det_zeroOneFive :
    (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 1, 5} : Finset (Fin 6))).det = -552 := by
  have h0 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 1, 5} : Finset (Fin 6)) 0 = 13 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h1 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 1, 5} : Finset (Fin 6)) 1 = 55/4 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h2 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 1, 5} : Finset (Fin 6)) 2 = -1 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h3 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 1, 5} : Finset (Fin 6)) 3 = -2 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h4 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 1, 5} : Finset (Fin 6)) 4 = -3 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h5 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 1, 5} : Finset (Fin 6)) 5 = 2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  rw [directionChartGap_threeLines_eq _ _ _ threeLinesStarWitnessWeight_ne,
    det_threeLinesCoefficientMatrix, threeLinesBasisDeterminant, h0, h1, h2, h3, h4, h5]
  norm_num

/-- Hence that star triple is not positive definite at the witness. -/
theorem threeLinesStarWitness_not_posDef_zeroOneFive :
    ¬ (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 1, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_det_neg _ (by rw [threeLinesStarWitness_det_zeroOneFive]; norm_num)

/-- The star triple `{0, 2, 5}` has a negative determinant at the witness. -/
theorem threeLinesStarWitness_det_zeroTwoFive :
    (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 2, 5} : Finset (Fin 6))).det = -567 := by
  have h0 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 2, 5} : Finset (Fin 6)) 0 = 13 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h1 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 2, 5} : Finset (Fin 6)) 1 = -5 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h2 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 2, 5} : Finset (Fin 6)) 2 = 14 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h3 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 2, 5} : Finset (Fin 6)) 3 = -2 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h4 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 2, 5} : Finset (Fin 6)) 4 = -3 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h5 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 2, 5} : Finset (Fin 6)) 5 = 2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  rw [directionChartGap_threeLines_eq _ _ _ threeLinesStarWitnessWeight_ne,
    det_threeLinesCoefficientMatrix, threeLinesBasisDeterminant, h0, h1, h2, h3, h4, h5]
  norm_num

/-- Hence that star triple is not positive definite at the witness. -/
theorem threeLinesStarWitness_not_posDef_zeroTwoFive :
    ¬ (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 2, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_det_neg _ (by rw [threeLinesStarWitness_det_zeroTwoFive]; norm_num)

/-- The star triple `{1, 2, 5}` has a negative determinant at the witness. -/
theorem threeLinesStarWitness_det_oneTwoFive :
    (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 2, 5} : Finset (Fin 6))).det = -687 := by
  have h0 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 2, 5} : Finset (Fin 6)) 0 = -2 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h1 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 2, 5} : Finset (Fin 6)) 1 = 55/4 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h2 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 2, 5} : Finset (Fin 6)) 2 = 14 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h3 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 2, 5} : Finset (Fin 6)) 3 = -2 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h4 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 2, 5} : Finset (Fin 6)) 4 = -3 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h5 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 2, 5} : Finset (Fin 6)) 5 = 2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  rw [directionChartGap_threeLines_eq _ _ _ threeLinesStarWitnessWeight_ne,
    det_threeLinesCoefficientMatrix, threeLinesBasisDeterminant, h0, h1, h2, h3, h4, h5]
  norm_num

/-- Hence that star triple is not positive definite at the witness. -/
theorem threeLinesStarWitness_not_posDef_oneTwoFive :
    ¬ (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 2, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_det_neg _ (by rw [threeLinesStarWitness_det_oneTwoFive]; norm_num)

/-- The star triple `{1, 4, 5}` has a negative determinant at the witness. -/
theorem threeLinesStarWitness_det_oneFourFive :
    (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 4, 5} : Finset (Fin 6))).det = -8211/8 := by
  have h0 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 4, 5} : Finset (Fin 6)) 0 = -2 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h1 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 4, 5} : Finset (Fin 6)) 1 = 55/4 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h2 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 4, 5} : Finset (Fin 6)) 2 = -1 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h3 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 4, 5} : Finset (Fin 6)) 3 = -2 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h4 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 4, 5} : Finset (Fin 6)) 4 = 39/2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h5 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 4, 5} : Finset (Fin 6)) 5 = 2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  rw [directionChartGap_threeLines_eq _ _ _ threeLinesStarWitnessWeight_ne,
    det_threeLinesCoefficientMatrix, threeLinesBasisDeterminant, h0, h1, h2, h3, h4, h5]
  norm_num

/-- Hence that star triple is not positive definite at the witness. -/
theorem threeLinesStarWitness_not_posDef_oneFourFive :
    ¬ (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({1, 4, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_det_neg _ (by rw [threeLinesStarWitness_det_oneFourFive]; norm_num)

/-- The star triple `{2, 4, 5}` has a negative determinant at the witness. -/
theorem threeLinesStarWitness_det_twoFourFive :
    (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 4, 5} : Finset (Fin 6))).det = -282 := by
  have h0 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 4, 5} : Finset (Fin 6)) 0 = -2 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h1 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 4, 5} : Finset (Fin 6)) 1 = -5 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h2 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 4, 5} : Finset (Fin 6)) 2 = 14 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h3 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 4, 5} : Finset (Fin 6)) 3 = -2 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h4 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 4, 5} : Finset (Fin 6)) 4 = 39/2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h5 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 4, 5} : Finset (Fin 6)) 5 = 2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  rw [directionChartGap_threeLines_eq _ _ _ threeLinesStarWitnessWeight_ne,
    det_threeLinesCoefficientMatrix, threeLinesBasisDeterminant, h0, h1, h2, h3, h4, h5]
  norm_num

/-- Hence that star triple is not positive definite at the witness. -/
theorem threeLinesStarWitness_not_posDef_twoFourFive :
    ¬ (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 4, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_det_neg _ (by rw [threeLinesStarWitness_det_twoFourFive]; norm_num)

/-! ## 5. The star cover is false -/

/-- **The star cover.**  At every admissible chart point on the fundamental
domain carrying an off-line weak witness, some star triple is strictly positive
definite. -/
def ThreeLinesStarCovers : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      (∃ selected : Finset (Fin 6), ThreeLinesOffLinesWeakTriple slide point selected) →
      ∃ selected ∈ threeLinesStarFamily,
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef

/-- **The vertex triple fires at the witness**, by the vertex cell. -/
theorem threeLinesStarWitness_vertex_posDef :
    (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 1, 3} : Finset (Fin 6))).PosDef := by
  refine posDef_threeLinesVertex_of_dominates 1 _ _ threeLinesStarWitnessWeight_ne ?_
  refine ⟨?_, ?_, ?_⟩ <;>
    · simp [chartExcess, threeLinesStarWitnessMass, threeLinesStarWitnessWeight]
      norm_num

/-- The witness carries an off-line weak triple, so the antecedent holds. -/
theorem threeLinesStarWitness_weak :
    ∃ selected : Finset (Fin 6),
      ThreeLinesOffLinesWeakTriple 1 threeLinesStarWitness selected := by
  refine ⟨({0, 1, 3} : Finset (Fin 6)), by decide, by decide, by decide, by decide, ?_⟩
  exact threeLinesStarWitness_vertex_posDef.posSemidef

/-- **THE STAR COVER IS FALSE.**  At the witness every star triple fails, while
the vertex triple is strictly positive definite.  The point is therefore no
counterexample to public A2 -- what it refutes is the cover. -/
theorem not_threeLinesStarCovers : ¬ ThreeLinesStarCovers := by
  intro hcover
  obtain ⟨selected, hmem, hposDef⟩ :=
    hcover 1 ⟨by norm_num, by norm_num⟩ (by norm_num) threeLinesStarWitness
      threeLinesStarWitness_weak
  fin_cases hmem
  · exact threeLinesStarWitness_not_posDef_zeroOneFive hposDef
  · exact threeLinesStarWitness_not_posDef_zeroTwoFive hposDef
  · exact threeLinesStarWitness_not_posDef_oneTwoFive hposDef
  · exact threeLinesStarWitness_not_posDef_oneFourFive hposDef
  · exact threeLinesStarWitness_not_posDef_twoFourFive hposDef

/-! ## 6. Every off-line triple through the slide atom fails -/

theorem threeLinesStarWitness_det_zeroThreeFive :
    (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 3, 5} : Finset (Fin 6))).det = -987 := by
  have h0 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 3, 5} : Finset (Fin 6)) 0 = 13 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h1 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 3, 5} : Finset (Fin 6)) 1 = -5 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h2 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 3, 5} : Finset (Fin 6)) 2 = -1 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h3 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 3, 5} : Finset (Fin 6)) 3 = 28 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h4 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 3, 5} : Finset (Fin 6)) 4 = -3 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h5 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 3, 5} : Finset (Fin 6)) 5 = 2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  rw [directionChartGap_threeLines_eq _ _ _ threeLinesStarWitnessWeight_ne,
    det_threeLinesCoefficientMatrix, threeLinesBasisDeterminant, h0, h1, h2, h3, h4, h5]
  norm_num

theorem threeLinesStarWitness_not_posDef_zeroThreeFive :
    ¬ (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 3, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_det_neg _ (by rw [threeLinesStarWitness_det_zeroThreeFive]; norm_num)

theorem threeLinesStarWitness_det_zeroFourFive :
    (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 4, 5} : Finset (Fin 6))).det = -2319/2 := by
  have h0 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 4, 5} : Finset (Fin 6)) 0 = 13 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h1 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 4, 5} : Finset (Fin 6)) 1 = -5 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h2 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 4, 5} : Finset (Fin 6)) 2 = -1 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h3 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 4, 5} : Finset (Fin 6)) 3 = -2 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h4 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 4, 5} : Finset (Fin 6)) 4 = 39/2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h5 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 4, 5} : Finset (Fin 6)) 5 = 2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  rw [directionChartGap_threeLines_eq _ _ _ threeLinesStarWitnessWeight_ne,
    det_threeLinesCoefficientMatrix, threeLinesBasisDeterminant, h0, h1, h2, h3, h4, h5]
  norm_num

theorem threeLinesStarWitness_not_posDef_zeroFourFive :
    ¬ (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({0, 4, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_det_neg _ (by rw [threeLinesStarWitness_det_zeroFourFive]; norm_num)

theorem threeLinesStarWitness_det_twoThreeFive :
    (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 3, 5} : Finset (Fin 6))).det = -2922 := by
  have h0 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 3, 5} : Finset (Fin 6)) 0 = -2 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h1 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 3, 5} : Finset (Fin 6)) 1 = -5 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h2 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 3, 5} : Finset (Fin 6)) 2 = 14 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h3 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 3, 5} : Finset (Fin 6)) 3 = 28 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h4 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 3, 5} : Finset (Fin 6)) 4 = -3 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h5 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 3, 5} : Finset (Fin 6)) 5 = 2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  rw [directionChartGap_threeLines_eq _ _ _ threeLinesStarWitnessWeight_ne,
    det_threeLinesCoefficientMatrix, threeLinesBasisDeterminant, h0, h1, h2, h3, h4, h5]
  norm_num

theorem threeLinesStarWitness_not_posDef_twoThreeFive :
    ¬ (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({2, 3, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_det_neg _ (by rw [threeLinesStarWitness_det_twoThreeFive]; norm_num)

theorem threeLinesStarWitness_det_threeFourFive :
    (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({3, 4, 5} : Finset (Fin 6))).det = -3879/2 := by
  have h0 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({3, 4, 5} : Finset (Fin 6)) 0 = -2 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h1 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({3, 4, 5} : Finset (Fin 6)) 1 = -5 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h2 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({3, 4, 5} : Finset (Fin 6)) 2 = -1 := by
    simp [threeLinesChartCoefficient, threeLinesStarWitnessMass]
  have h3 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({3, 4, 5} : Finset (Fin 6)) 3 = 28 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h4 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({3, 4, 5} : Finset (Fin 6)) 4 = 39/2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  have h5 : threeLinesChartCoefficient threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({3, 4, 5} : Finset (Fin 6)) 5 = 2 := by
    simp [threeLinesChartCoefficient, chartExcess, threeLinesStarWitnessMass,
      threeLinesStarWitnessWeight]
    norm_num
  rw [directionChartGap_threeLines_eq _ _ _ threeLinesStarWitnessWeight_ne,
    det_threeLinesCoefficientMatrix, threeLinesBasisDeterminant, h0, h1, h2, h3, h4, h5]
  norm_num

theorem threeLinesStarWitness_not_posDef_threeFourFive :
    ¬ (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight ({3, 4, 5} : Finset (Fin 6))).PosDef :=
  not_posDef_of_det_neg _ (by rw [threeLinesStarWitness_det_threeFourFive]; norm_num)

/-- The nine off-line triples through the slide-carrying atom `5`. -/
def threeLinesSlideAtomOffLineFamily : List (Finset (Fin 6)) :=
  [{0, 1, 5}, {0, 2, 5}, {0, 3, 5}, {0, 4, 5}, {1, 2, 5},
   {1, 4, 5}, {2, 3, 5}, {2, 4, 5}, {3, 4, 5}]

theorem threeLinesSlideAtomOffLineFamily_length :
    threeLinesSlideAtomOffLineFamily.length = 9 := rfl

theorem threeLinesStarFamily_subset_slideAtom (selected : Finset (Fin 6))
    (hmem : selected ∈ threeLinesStarFamily) :
    selected ∈ threeLinesSlideAtomOffLineFamily := by
  fin_cases hmem <;> decide

/-- **THE SLIDE ATOM IS USELESS AT THE WITNESS.**  Not one of the nine off-line
triples through label `5` is positive definite, so no cover assembled from
slide-atom triples can reach this point.  This strictly strengthens the failure
of the star, which is five of those nine. -/
theorem threeLinesStarWitness_no_slideAtom_posDef (selected : Finset (Fin 6))
    (hmem : selected ∈ threeLinesSlideAtomOffLineFamily) :
    ¬ (directionChartGap (threeLinesDirection 1) threeLinesStarWitnessMass
      threeLinesStarWitnessWeight selected).PosDef := by
  fin_cases hmem
  · exact threeLinesStarWitness_not_posDef_zeroOneFive
  · exact threeLinesStarWitness_not_posDef_zeroTwoFive
  · exact threeLinesStarWitness_not_posDef_zeroThreeFive
  · exact threeLinesStarWitness_not_posDef_zeroFourFive
  · exact threeLinesStarWitness_not_posDef_oneTwoFive
  · exact threeLinesStarWitness_not_posDef_oneFourFive
  · exact threeLinesStarWitness_not_posDef_twoThreeFive
  · exact threeLinesStarWitness_not_posDef_twoFourFive
  · exact threeLinesStarWitness_not_posDef_threeFourFive

end Gtz
