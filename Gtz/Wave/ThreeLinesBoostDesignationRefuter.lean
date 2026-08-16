import Gtz.Design.KFourBandAtlas
import Gtz.Wave.ThreeLinesOffLinesWiring

/-!
# The boost designation fails on the three-lines chart

The residual of `obligationChartTieFreeThreeLinesFundamentalDomain` asks for a
STRICT card-three selection among the seventeen off-line triples.  The cheapest
rule anyone would reach for designates the label of largest boost
`b_c = m_c / w_c` and keeps a triple through it.  This file refutes that rule,
and refutes its set-valued repair, with one exact rational chart point on the
fundamental domain.

The witness is `slide = -3`, weights `(2,1,5,2,2,2)/14` and masses
`(2,2,3,6,3,4)`.  Its boosts are `(14, 28, 42/5, 42, 21, 28)`, so label `3`
is the UNIQUE maximiser.  Every one of the ten triples that hold label `3`
fails, while `{0,1,5}`, `{0,2,5}` and `{1,4,5}` are strictly positive definite.

Two consequences are recorded.  The point is no counterexample to A2, because
strict triples exist.  And the failure is not a tie: the maximiser is unique,
so the set-valued rule that returns EVERY boost-maximal label fails at the same
point.  That closes the repair which the relabelling no-go
(`Gtz/Wave/EquivariantDesignationRefuter.lean`) leaves open for this chart.
-/

namespace Gtz

open Matrix Finset

/-! ## 1. The witness chart point -/

/-- The slide of the witness.  It lies in the fundamental domain `1 <= |slide|`
and is admissible. -/
noncomputable def boostWitnessSlide : ℝ := -3

/-- The weights of the witness, a probability vector with denominator `14`. -/
noncomputable def boostWitnessWeight : Fin 6 → ℝ :=
  ![1/7, 1/14, 5/14, 1/7, 1/7, 1/7]

/-- The masses of the witness. -/
noncomputable def boostWitnessMass : Fin 6 → ℝ := ![2, 2, 3, 6, 3, 4]

theorem boostWitnessWeight_pos (label : Fin 6) : 0 < boostWitnessWeight label := by
  fin_cases label <;> simp [boostWitnessWeight]

theorem boostWitnessMass_pos (label : Fin 6) : 0 < boostWitnessMass label := by
  fin_cases label <;> simp [boostWitnessMass]

theorem boostWitnessWeight_sum_one : ∑ label, boostWitnessWeight label = 1 := by
  simp [boostWitnessWeight, Fin.sum_univ_six]; norm_num

/-- The witness as a chart point of the three-lines chart. -/
noncomputable def boostWitnessPoint : DirectionChartPoint 6 where
  mass := boostWitnessMass
  weight := boostWitnessWeight
  mass_pos := boostWitnessMass_pos
  weight_pos := boostWitnessWeight_pos
  weight_sum_one := boostWitnessWeight_sum_one

/-- The slide is admissible: it is neither `0` nor `-1`. -/
theorem boostWitnessSlide_admissible :
    IsAdmissibleThreeLinesParameter boostWitnessSlide := by
  constructor <;> · simp [boostWitnessSlide]

/-- The slide lies in the fundamental domain. -/
theorem boostWitnessSlide_fundamental : (1 : ℝ) ≤ |boostWitnessSlide| := by
  simp [boostWitnessSlide, abs_of_nonpos]

/-! ## 2. The boost and its unique maximiser

The boost of a chart label is `m_c / w_c`.  It is the coefficient the selection
sum gives that label, and it is the only label-wise scalar the gap reads.
-/

/-- The boost of a chart label. -/
noncomputable def chartBoost (point : DirectionChartPoint 6) (label : Fin 6) : ℝ :=
  point.mass label / point.weight label

/-- The six boosts of the witness. -/
theorem chartBoost_boostWitness :
    chartBoost boostWitnessPoint 0 = 14 ∧ chartBoost boostWitnessPoint 1 = 28 ∧
    chartBoost boostWitnessPoint 2 = 42/5 ∧ chartBoost boostWitnessPoint 3 = 42 ∧
    chartBoost boostWitnessPoint 4 = 21 ∧ chartBoost boostWitnessPoint 5 = 28 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    simp [chartBoost, boostWitnessPoint, boostWitnessMass, boostWitnessWeight] <;> norm_num

/-- **Label `3` is the unique boost maximiser of the witness.**  Every other
label reads a strictly smaller boost, so no tie-breaking rule is involved. -/
theorem chartBoost_boostWitness_lt_three (label : Fin 6) (hlabel : label ≠ 3) :
    chartBoost boostWitnessPoint label < chartBoost boostWitnessPoint 3 := by
  fin_cases label <;>
    simp_all [chartBoost, boostWitnessPoint, boostWitnessMass, boostWitnessWeight] <;> norm_num

/-- The boost maximiser is `3`, stated as a maximum over all labels. -/
theorem chartBoost_boostWitness_le_three (label : Fin 6) :
    chartBoost boostWitnessPoint label ≤ chartBoost boostWitnessPoint 3 := by
  rcases eq_or_ne label 3 with h | h
  · exact le_of_eq (by rw [h])
  · exact le_of_lt (chartBoost_boostWitness_lt_three label h)

/-! ## 3. The gap of the witness, triple by triple

`witnessGap` abbreviates the chart gap of the witness at a selection.  Every
entry is an explicit rational, so every leading minor is decided by `norm_num`.
-/

/-- The chart gap of the witness at a selection. -/
noncomputable def witnessGap (selected : Finset (Fin 6)) : Matrix (Fin 3) (Fin 3) ℝ :=
  directionChartGap (threeLinesDirection boostWitnessSlide)
    boostWitnessPoint.mass boostWitnessPoint.weight selected

theorem witnessGap_symm (selected : Finset (Fin 6)) :
    (witnessGap selected)ᵀ = witnessGap selected :=
  directionChartGap_transpose _ _ _ _

/-- The three leading minors of a symmetric `3x3`, as the bridge states them. -/
noncomputable def minorOne (form : Matrix (Fin 3) (Fin 3) ℝ) : ℝ := form 0 0

noncomputable def minorTwo (form : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  form 0 0 * form 1 1 - form 0 1 ^ 2

noncomputable def minorThree (form : Matrix (Fin 3) (Fin 3) ℝ) : ℝ :=
  form 0 0 * form 1 1 * form 2 2 - form 0 0 * form 1 2 ^ 2
    - form 0 1 ^ 2 * form 2 2 + 2 * form 0 1 * form 0 2 * form 1 2
    - form 0 2 ^ 2 * form 1 1

/-- Positive definiteness of a witness gap is the three leading minors. -/
theorem witnessGap_posDef_iff (selected : Finset (Fin 6)) :
    (witnessGap selected).PosDef ↔
      (0 < minorOne (witnessGap selected) ∧ 0 < minorTwo (witnessGap selected)
        ∧ 0 < minorThree (witnessGap selected)) := by
  rw [posDef_finThree_iff_leadingMinors _ (witnessGap_symm selected)]
  rfl

/-- A single non-positive leading minor refutes positive definiteness. -/
theorem not_posDef_of_minorOne_nonpos (selected : Finset (Fin 6))
    (hminor : minorOne (witnessGap selected) ≤ 0) : ¬ (witnessGap selected).PosDef := by
  rw [witnessGap_posDef_iff]
  exact fun h => absurd h.1 (not_lt.mpr hminor)

theorem not_posDef_of_minorTwo_nonpos (selected : Finset (Fin 6))
    (hminor : minorTwo (witnessGap selected) ≤ 0) : ¬ (witnessGap selected).PosDef := by
  rw [witnessGap_posDef_iff]
  exact fun h => absurd h.2.1 (not_lt.mpr hminor)

theorem not_posDef_of_minorThree_nonpos (selected : Finset (Fin 6))
    (hminor : minorThree (witnessGap selected) ≤ 0) : ¬ (witnessGap selected).PosDef := by
  rw [witnessGap_posDef_iff]
  exact fun h => absurd h.2.2 (not_lt.mpr hminor)

/-- The simp set that evaluates a witness gap entry to an explicit rational. -/
theorem witnessGap_entry (selected : Finset (Fin 6)) (row col : Fin 3) :
    witnessGap selected row col
      = (∑ label ∈ selected, (boostWitnessMass label / boostWitnessWeight label)
            * threeLinesDirection boostWitnessSlide label row
            * threeLinesDirection boostWitnessSlide label col)
        - ∑ label, boostWitnessMass label
            * threeLinesDirection boostWitnessSlide label row
            * threeLinesDirection boostWitnessSlide label col := by
  simp [witnessGap, directionChartGap, boostWitnessPoint, atomMatrix, Matrix.sub_apply,
    Matrix.sum_apply, Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul, mul_assoc]

/-! ### The ten triples that hold the boost maximiser

Each one fails, and the failing minor is named.  The pattern of failure is not
uniform: `{1,3,5}` fails already at the first minor because it is one of the
three dependent lines, four fail at the second minor, and five at the third.
-/

theorem not_posDef_zeroOneThree : ¬ (witnessGap {0, 1, 3}).PosDef := by
  refine not_posDef_of_minorThree_nonpos _ ?_
  simp [minorThree, witnessGap_entry, Fin.sum_univ_six, threeLinesDirection,
    boostWitnessMass, boostWitnessWeight, boostWitnessSlide, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton]
  norm_num

theorem not_posDef_zeroTwoThree : ¬ (witnessGap {0, 2, 3}).PosDef := by
  refine not_posDef_of_minorTwo_nonpos _ ?_
  simp [minorTwo, witnessGap_entry, Fin.sum_univ_six, threeLinesDirection,
    boostWitnessMass, boostWitnessWeight, boostWitnessSlide, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton]
  norm_num

theorem not_posDef_zeroThreeFour : ¬ (witnessGap {0, 3, 4}).PosDef := by
  refine not_posDef_of_minorTwo_nonpos _ ?_
  simp [minorTwo, witnessGap_entry, Fin.sum_univ_six, threeLinesDirection,
    boostWitnessMass, boostWitnessWeight, boostWitnessSlide, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton]
  norm_num

theorem not_posDef_zeroThreeFive : ¬ (witnessGap {0, 3, 5}).PosDef := by
  refine not_posDef_of_minorThree_nonpos _ ?_
  simp [minorThree, witnessGap_entry, Fin.sum_univ_six, threeLinesDirection,
    boostWitnessMass, boostWitnessWeight, boostWitnessSlide, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton]
  norm_num

theorem not_posDef_oneTwoThree : ¬ (witnessGap {1, 2, 3}).PosDef := by
  refine not_posDef_of_minorTwo_nonpos _ ?_
  simp [minorTwo, witnessGap_entry, Fin.sum_univ_six, threeLinesDirection,
    boostWitnessMass, boostWitnessWeight, boostWitnessSlide, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton]
  norm_num

theorem not_posDef_oneThreeFour : ¬ (witnessGap {1, 3, 4}).PosDef := by
  refine not_posDef_of_minorThree_nonpos _ ?_
  simp [minorThree, witnessGap_entry, Fin.sum_univ_six, threeLinesDirection,
    boostWitnessMass, boostWitnessWeight, boostWitnessSlide, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton]
  norm_num

theorem not_posDef_oneThreeFive : ¬ (witnessGap {1, 3, 5}).PosDef := by
  refine not_posDef_of_minorOne_nonpos _ ?_
  simp [minorOne, witnessGap_entry, Fin.sum_univ_six, threeLinesDirection,
    boostWitnessMass, boostWitnessWeight, boostWitnessSlide, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton]
  norm_num

theorem not_posDef_twoThreeFour : ¬ (witnessGap {2, 3, 4}).PosDef := by
  refine not_posDef_of_minorTwo_nonpos _ ?_
  simp [minorTwo, witnessGap_entry, Fin.sum_univ_six, threeLinesDirection,
    boostWitnessMass, boostWitnessWeight, boostWitnessSlide, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton]
  norm_num

theorem not_posDef_twoThreeFive : ¬ (witnessGap {2, 3, 5}).PosDef := by
  refine not_posDef_of_minorTwo_nonpos _ ?_
  simp [minorTwo, witnessGap_entry, Fin.sum_univ_six, threeLinesDirection,
    boostWitnessMass, boostWitnessWeight, boostWitnessSlide, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton]
  norm_num

theorem not_posDef_threeFourFive : ¬ (witnessGap {3, 4, 5}).PosDef := by
  refine not_posDef_of_minorThree_nonpos _ ?_
  simp [minorThree, witnessGap_entry, Fin.sum_univ_six, threeLinesDirection,
    boostWitnessMass, boostWitnessWeight, boostWitnessSlide, Finset.sum_insert,
    Finset.mem_insert, Finset.mem_singleton]
  norm_num

/-! ### Three strict triples of the witness

The point carries strict selections, so it is NOT a counterexample to A2.  What
fails is only the designation.
-/

theorem posDef_zeroOneFive : (witnessGap {0, 1, 5}).PosDef := by
  rw [witnessGap_posDef_iff]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [minorOne, minorTwo, minorThree, witnessGap_entry, Fin.sum_univ_six,
      threeLinesDirection, boostWitnessMass, boostWitnessWeight, boostWitnessSlide,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton] <;> norm_num

theorem posDef_zeroTwoFive : (witnessGap {0, 2, 5}).PosDef := by
  rw [witnessGap_posDef_iff]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [minorOne, minorTwo, minorThree, witnessGap_entry, Fin.sum_univ_six,
      threeLinesDirection, boostWitnessMass, boostWitnessWeight, boostWitnessSlide,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton] <;> norm_num

theorem posDef_oneFourFive : (witnessGap {1, 4, 5}).PosDef := by
  rw [witnessGap_posDef_iff]
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [minorOne, minorTwo, minorThree, witnessGap_entry, Fin.sum_univ_six,
      threeLinesDirection, boostWitnessMass, boostWitnessWeight, boostWitnessSlide,
      Finset.sum_insert, Finset.mem_insert, Finset.mem_singleton] <;> norm_num

/-- The witness carries a strict card-three selection. -/
theorem boostWitness_hasStrictTriple :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap (threeLinesDirection boostWitnessSlide)
        boostWitnessPoint.mass boostWitnessPoint.weight selected).PosDef :=
  ⟨{0, 1, 5}, by decide, posDef_zeroOneFive⟩

/-- The witness carries an off-line weak triple, so the A2 antecedent holds. -/
theorem boostWitness_hasOffLinesWeakTriple :
    ∃ selected : Finset (Fin 6),
      ThreeLinesOffLinesWeakTriple boostWitnessSlide boostWitnessPoint selected := by
  refine ⟨{0, 1, 5}, by decide, by decide, by decide, by decide, ?_⟩
  exact posDef_zeroOneFive.posSemidef

/-! ## 4. Every triple through the boost maximiser fails

A card-three subset of `Fin 6` that holds label `3` is one of exactly ten sets.
The dispatch below is a `decide` over that classification.
-/

/-- The ten card-three subsets of `Fin 6` that hold label `3`. -/
def triplesThroughThree : List (Finset (Fin 6)) :=
  [{0,1,3}, {0,2,3}, {0,3,4}, {0,3,5}, {1,2,3}, {1,3,4}, {1,3,5}, {2,3,4}, {2,3,5}, {3,4,5}]

theorem triplesThroughThree_length : triplesThroughThree.length = 10 := by decide

/-- The classification: a card-three set holding `3` is one of the ten. -/
theorem mem_triplesThroughThree (selected : Finset (Fin 6))
    (hcard : selected.card = 3) (hthree : (3 : Fin 6) ∈ selected) :
    selected ∈ triplesThroughThree := by
  revert hcard hthree
  decide +revert

/-- **No triple through the boost maximiser is strict at the witness.** -/
theorem not_posDef_of_mem_triplesThroughThree (selected : Finset (Fin 6))
    (hmem : selected ∈ triplesThroughThree) : ¬ (witnessGap selected).PosDef := by
  fin_cases hmem
  · exact not_posDef_zeroOneThree
  · exact not_posDef_zeroTwoThree
  · exact not_posDef_zeroThreeFour
  · exact not_posDef_zeroThreeFive
  · exact not_posDef_oneTwoThree
  · exact not_posDef_oneThreeFour
  · exact not_posDef_oneThreeFive
  · exact not_posDef_twoThreeFour
  · exact not_posDef_twoThreeFive
  · exact not_posDef_threeFourFive

/-- **The boost maximiser hosts no strict triple.**  This is the whole refutation
in one statement: label `3` maximises the boost, and every card-three selection
holding it is not positive definite. -/
theorem boostWitness_no_strict_through_three (selected : Finset (Fin 6))
    (hcard : selected.card = 3) (hthree : (3 : Fin 6) ∈ selected) :
    ¬ (directionChartGap (threeLinesDirection boostWitnessSlide)
        boostWitnessPoint.mass boostWitnessPoint.weight selected).PosDef :=
  not_posDef_of_mem_triplesThroughThree selected (mem_triplesThroughThree selected hcard hthree)

/-! ## 5. The designations, and their refutation

Two rules are stated.  The first designates the single boost-maximal label.  The
second designates the SET of boost-maximal labels, which is the repair the
relabelling no-go leaves open.  The witness refutes both, and it refutes the
second because its maximiser is unique rather than because of a tie.
-/

/-- **The boost-argmax designation.**  At every admissible chart point of the
fundamental domain that carries a strict triple, some strict triple holds a
label of maximal boost. -/
def ThreeLinesBoostArgmaxHostsStrictTriple : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      (∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef) →
      ∀ star : Fin 6, (∀ label : Fin 6, chartBoost point label ≤ chartBoost point star) →
        ∃ selected : Finset (Fin 6), selected.card = 3 ∧ star ∈ selected ∧
          (directionChartGap (threeLinesDirection slide) point.mass point.weight
            selected).PosDef

/-- **The boost-argmax designation is false.**  The witness satisfies every
hypothesis and refutes the conclusion. -/
theorem not_threeLinesBoostArgmaxHostsStrictTriple :
    ¬ ThreeLinesBoostArgmaxHostsStrictTriple := by
  intro hrule
  obtain ⟨selected, hcard, hthree, hposDef⟩ :=
    hrule boostWitnessSlide boostWitnessSlide_admissible boostWitnessSlide_fundamental
      boostWitnessPoint boostWitness_hasStrictTriple 3 chartBoost_boostWitness_le_three
  exact boostWitness_no_strict_through_three selected hcard hthree hposDef

/-- **The set-valued repair.**  At every such point, some strict triple holds
SOME boost-maximal label.  This is the rule that survives the relabelling no-go,
because it returns a set rather than a point. -/
def ThreeLinesBoostMaximalSetHostsStrictTriple : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      (∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef) →
      ∃ star : Fin 6, (∀ label : Fin 6, chartBoost point label ≤ chartBoost point star) ∧
        ∃ selected : Finset (Fin 6), selected.card = 3 ∧ star ∈ selected ∧
          (directionChartGap (threeLinesDirection slide) point.mass point.weight
            selected).PosDef

/-- The only boost-maximal label of the witness is `3`. -/
theorem boostWitness_maximal_eq_three (star : Fin 6)
    (hstar : ∀ label : Fin 6, chartBoost boostWitnessPoint label
      ≤ chartBoost boostWitnessPoint star) : star = 3 := by
  by_contra hne
  exact absurd (hstar 3) (not_le.mpr (chartBoost_boostWitness_lt_three star hne))

/-- **The set-valued repair is false too, and not because of a tie.**  The
witness has a unique boost maximiser, so the set the rule returns is the
singleton `{3}`, and every triple through `3` fails. -/
theorem not_threeLinesBoostMaximalSetHostsStrictTriple :
    ¬ ThreeLinesBoostMaximalSetHostsStrictTriple := by
  intro hrule
  obtain ⟨star, hstar, selected, hcard, hmem, hposDef⟩ :=
    hrule boostWitnessSlide boostWitnessSlide_admissible boostWitnessSlide_fundamental
      boostWitnessPoint boostWitness_hasStrictTriple
  rw [boostWitness_maximal_eq_three star hstar] at hmem
  exact boostWitness_no_strict_through_three selected hcard hmem hposDef

/-! ## 6. The general label designation

Any rule that names one label and keeps a triple through it is refuted by a
point at which the named label hosts nothing.  The witness supplies that for
label `3`, so every label rule agreeing with the boost maximiser dies here.
-/

/-- A label designation is a rule that names one label at each chart point. -/
def LabelDesignationHostsStrictTriple (rule : DirectionChartPoint 6 → Fin 6) : Prop :=
  ∀ slide : ℝ, IsAdmissibleThreeLinesParameter slide → 1 ≤ |slide| →
    ∀ point : DirectionChartPoint 6,
      (∃ selected : Finset (Fin 6), selected.card = 3 ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef) →
      ∃ selected : Finset (Fin 6), selected.card = 3 ∧ rule point ∈ selected ∧
        (directionChartGap (threeLinesDirection slide) point.mass point.weight
          selected).PosDef

/-- **Every label designation that names `3` at the witness is false.**  The
boost maximiser is one such rule, but so is any rule agreeing with it there. -/
theorem not_labelDesignationHostsStrictTriple (rule : DirectionChartPoint 6 → Fin 6)
    (hrule : rule boostWitnessPoint = 3) :
    ¬ LabelDesignationHostsStrictTriple rule := by
  intro hdesignation
  obtain ⟨selected, hcard, hmem, hposDef⟩ :=
    hdesignation boostWitnessSlide boostWitnessSlide_admissible
      boostWitnessSlide_fundamental boostWitnessPoint boostWitness_hasStrictTriple
  rw [hrule] at hmem
  exact boostWitness_no_strict_through_three selected hcard hmem hposDef

/-! ## 7. The star family

The three strict triples of the witness all hold label `5`, the slide-carrying
atom.  The family below is the one a census finds firing hardest on the
residual region.  It is recorded with its witness membership, not with a
coverage claim: no theorem here says the family covers the region.
-/

/-- The five triples that a residual-region census finds firing hardest. -/
def threeLinesStarFive : List (Finset (Fin 6)) :=
  [{0,1,5}, {0,2,5}, {1,2,5}, {1,4,5}, {2,4,5}]

theorem threeLinesStarFive_length : threeLinesStarFive.length = 5 := by decide

/-- Every member of the star family holds the slide-carrying label `5`. -/
theorem threeLinesStarFive_mem_five (selected : Finset (Fin 6))
    (hmem : selected ∈ threeLinesStarFive) : (5 : Fin 6) ∈ selected := by
  fin_cases hmem <;> decide

/-- Every member of the star family is a card-three set. -/
theorem threeLinesStarFive_card (selected : Finset (Fin 6))
    (hmem : selected ∈ threeLinesStarFive) : selected.card = 3 := by
  fin_cases hmem <;> decide

/-- No member of the star family is one of the three dependent lines. -/
theorem threeLinesStarFive_offLine (selected : Finset (Fin 6))
    (hmem : selected ∈ threeLinesStarFive) :
    selected ≠ ({0,1,2} : Finset (Fin 6)) ∧ selected ≠ ({0,3,4} : Finset (Fin 6)) ∧
      selected ≠ ({1,3,5} : Finset (Fin 6)) := by
  fin_cases hmem <;> exact ⟨by decide, by decide, by decide⟩

/-- **The star family fires at the witness.**  Some member is strict there, so
the family is not empty on the residual region. -/
theorem threeLinesStarFive_fires_boostWitness :
    ∃ selected ∈ threeLinesStarFive, (witnessGap selected).PosDef :=
  ⟨{0, 1, 5}, by decide, posDef_zeroOneFive⟩

/-- **The star family is disjoint from the boost maximiser at the witness.**
Every member misses label `3`, which is exactly why the boost rule fails while
the family succeeds. -/
theorem threeLinesStarFive_not_mem_three (selected : Finset (Fin 6))
    (hmem : selected ∈ threeLinesStarFive) : (3 : Fin 6) ∉ selected := by
  fin_cases hmem <;> decide

end Gtz
