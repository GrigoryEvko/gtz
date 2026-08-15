/-
# The entry-sum rung at every chart family, and the refutation of its argmax

`Gtz.kFourInvariantOne_eq` reads the first invariant coefficient of a K4 chart
tree gap as a mass-to-weight surplus, and derives a greedy law from it.  Two
things in that development are not K4 content and one conclusion drawn from it
is false.

First the generalization.  `Gtz.invariantOne_directionChartGap` prices each
label by the entry sum of its own atom matrix at EVERY direction family and
every size.  So the rung is a modular set function at every chart, uniform or
not, and the greedy law follows from modularity alone.  The K4 family is the
special case where all six prices equal one.

Second the calibration.  The three-lines family is NOT uniform: its six atom
entry sums are `1, 1, 3, 1, 3` and `1 + slide + slide^2`.  The rung is still
modular there, with those numbers as edge prices, so A2 inherits the greedy law
with a weighted rung rather than the plain mass-to-weight sum.

Third the refutation.  The rung is necessary but it does not order the trees by
quality.  At the chart point below the tree of STRICTLY largest mass-to-weight
sum is not positive definite, while a tree of smaller sum is.  The failure is in
the third coefficient, the spanning-tree polynomial, which the rung cannot see.
So no designation that picks a tree by its rung can close the class, and that
includes the greedy maximum.
-/
import Mathlib
import Gtz.Design.KFourEntrySumRung

namespace Gtz

open Matrix

/-! ## The entry-sum price of a label -/

/-- The price the first invariant coefficient puts on a label: the entry sum of
its own atom matrix.  Never negative. -/
noncomputable def chartAtomWeight {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (label : Fin size) : ℝ :=
  invariantOne (atomMatrix (direction label))

theorem chartAtomWeight_nonneg {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (label : Fin size) : 0 ≤ chartAtomWeight direction label :=
  invariantOne_atomMatrix_nonneg _

/-- The rung of a selection: its mass-to-weight sum, priced by the entry sums. -/
noncomputable def chartRatioSum {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (tree : Finset (Fin size)) : ℝ :=
  ∑ label ∈ tree, mass label / weight label * chartAtomWeight direction label

/-- The threshold of the rung: the total priced mass, independent of the
selection. -/
noncomputable def chartMassTotal {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass : Fin size → ℝ) : ℝ :=
  ∑ label, mass label * chartAtomWeight direction label

/-- **The rung at every chart family.**  The first invariant coefficient is the
priced mass-to-weight surplus of the selection. -/
theorem invariantOne_eq_chartRatioSum_sub {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (tree : Finset (Fin size)) :
    invariantOne (directionChartGap direction mass weight tree)
      = chartRatioSum direction mass weight tree - chartMassTotal direction mass :=
  invariantOne_directionChartGap direction mass weight tree

/-! ## The rung is modular

Modularity is the whole content of the greedy law.  The rung is a sum over the
selection of a fixed per-label price, so it splits over unions and intersections
and grows by one term at a time. -/

theorem chartRatioSum_empty {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) :
    chartRatioSum direction mass weight ∅ = 0 := by
  simp [chartRatioSum]

theorem chartRatioSum_insert {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (tree : Finset (Fin size)) (label : Fin size)
    (hnot : label ∉ tree) :
    chartRatioSum direction mass weight (insert label tree)
      = mass label / weight label * chartAtomWeight direction label
        + chartRatioSum direction mass weight tree := by
  simp [chartRatioSum, Finset.sum_insert hnot]

/-- **The modular identity.**  The rung of a union plus the rung of the
intersection is the sum of the rungs. -/
theorem chartRatioSum_union_add_inter {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (treeA treeB : Finset (Fin size)) :
    chartRatioSum direction mass weight (treeA ∪ treeB)
        + chartRatioSum direction mass weight (treeA ∩ treeB)
      = chartRatioSum direction mass weight treeA
        + chartRatioSum direction mass weight treeB := by
  classical
  simp only [chartRatioSum]
  exact Finset.sum_union_inter

/-- The rung is monotone in the selection, because every price is nonnegative
and every mass-to-weight ratio is. -/
theorem chartRatioSum_le_of_subset {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (hmass : ∀ label, 0 ≤ mass label)
    (hweight : ∀ label, 0 < weight label)
    (treeA treeB : Finset (Fin size)) (hsub : treeA ⊆ treeB) :
    chartRatioSum direction mass weight treeA ≤ chartRatioSum direction mass weight treeB := by
  refine Finset.sum_le_sum_of_subset_of_nonneg hsub ?_
  intro label _ _
  exact mul_nonneg (div_nonneg (hmass label) (hweight label).le) (chartAtomWeight_nonneg _ _)

/-! ## Necessity, the kill and the greedy law, at every chart family -/

/-- **Necessity at every family.**  A positive definite selection gap clears the
rung. -/
theorem chartRatioSum_gt_of_posDef {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (tree : Finset (Fin size))
    (hposDef : (directionChartGap direction mass weight tree).PosDef) :
    chartMassTotal direction mass < chartRatioSum direction mass weight tree := by
  have htriple :=
    (posDef_iff_invariantTriple (directionChartGap_transpose direction mass weight tree)).mp hposDef
  have hone := htriple.1
  rw [invariantOne_eq_chartRatioSum_sub] at hone
  linarith

/-- **The kill at every family.**  A selection whose priced mass-to-weight sum
does not exceed the priced total mass is not positive definite. -/
theorem chartTree_not_posDef_of_ratioSum_le {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (tree : Finset (Fin size))
    (hle : chartRatioSum direction mass weight tree ≤ chartMassTotal direction mass) :
    ¬ (directionChartGap direction mass weight tree).PosDef := by
  intro hposDef
  exact absurd (chartRatioSum_gt_of_posDef direction mass weight tree hposDef) (not_lt.mpr hle)

/-- **The greedy law at every family.**  If the selection of largest rung in a
family fails, no selection of that family is positive definite.  One greedy pass
settles the whole family, because the rung is modular. -/
theorem chartFamily_no_posDef_of_max_ratioSum_le {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (family : Finset (Finset (Fin size))) (best : Finset (Fin size))
    (hmax : ∀ tree ∈ family, chartRatioSum direction mass weight tree
      ≤ chartRatioSum direction mass weight best)
    (hfail : chartRatioSum direction mass weight best ≤ chartMassTotal direction mass) :
    ∀ tree ∈ family, ¬ (directionChartGap direction mass weight tree).PosDef := by
  intro tree hmem
  exact chartTree_not_posDef_of_ratioSum_le direction mass weight tree ((hmax tree hmem).trans hfail)

/-- The contrapositive: a positive definite selection forces the family maximum
above the threshold. -/
theorem chartFamily_max_ratioSum_gt_of_exists_posDef {size : ℕ}
    (direction : Fin size → (Fin 3 → ℝ)) (mass weight : Fin size → ℝ)
    (family : Finset (Finset (Fin size))) (best : Finset (Fin size))
    (hmax : ∀ tree ∈ family, chartRatioSum direction mass weight tree
      ≤ chartRatioSum direction mass weight best)
    (tree : Finset (Fin size)) (hmem : tree ∈ family)
    (hposDef : (directionChartGap direction mass weight tree).PosDef) :
    chartMassTotal direction mass < chartRatioSum direction mass weight best :=
  lt_of_lt_of_le (chartRatioSum_gt_of_posDef direction mass weight tree hposDef) (hmax tree hmem)

/-! ## The K4 family is the uniform case -/

theorem kFourDirection_chartAtomWeight (label : Fin 6) :
    chartAtomWeight kFourDirection label = 1 :=
  kFourDirection_invariantOne label

/-- At K4 the priced rung is the plain mass-to-weight sum. -/
theorem kFour_chartRatioSum_eq (mass weight : Fin 6 → ℝ) (tree : Finset (Fin 6)) :
    chartRatioSum kFourDirection mass weight tree
      = ∑ label ∈ tree, mass label / weight label := by
  simp [chartRatioSum, kFourDirection_chartAtomWeight]

theorem kFour_chartMassTotal_eq (mass : Fin 6 → ℝ) :
    chartMassTotal kFourDirection mass = ∑ label, mass label := by
  simp [chartMassTotal, kFourDirection_chartAtomWeight]

/-! ## The three-lines family is NOT uniform

Its six atom entry sums are `1, 1, 3, 1, 3` and `1 + slide + slide^2`.  Two
labels already disagree, so the shared-value form of the rung does not apply at
A2.  The modular form does, with these numbers as the prices. -/

theorem threeLinesDirection_chartAtomWeight_zero (slide : ℝ) :
    chartAtomWeight (threeLinesDirection slide) 0 = 1 := by
  simp [chartAtomWeight, invariantOne_atomMatrix, threeLinesDirection]

theorem threeLinesDirection_chartAtomWeight_one (slide : ℝ) :
    chartAtomWeight (threeLinesDirection slide) 1 = 1 := by
  simp [chartAtomWeight, invariantOne_atomMatrix, threeLinesDirection]

theorem threeLinesDirection_chartAtomWeight_two (slide : ℝ) :
    chartAtomWeight (threeLinesDirection slide) 2 = 3 := by
  simp [chartAtomWeight, invariantOne_atomMatrix, threeLinesDirection]
  norm_num

theorem threeLinesDirection_chartAtomWeight_three (slide : ℝ) :
    chartAtomWeight (threeLinesDirection slide) 3 = 1 := by
  simp [chartAtomWeight, invariantOne_atomMatrix, threeLinesDirection]

theorem threeLinesDirection_chartAtomWeight_four (slide : ℝ) :
    chartAtomWeight (threeLinesDirection slide) 4 = 3 := by
  simp [chartAtomWeight, invariantOne_atomMatrix, threeLinesDirection]
  norm_num

theorem threeLinesDirection_chartAtomWeight_five (slide : ℝ) :
    chartAtomWeight (threeLinesDirection slide) 5 = 1 + slide + slide ^ 2 := by
  simp [chartAtomWeight, invariantOne_atomMatrix, threeLinesDirection]
  ring

/-- **A2's chart is not uniform.**  No shared entry sum exists at any slide,
because two labels already disagree. -/
theorem threeLinesDirection_not_uniform (slide unit : ℝ) :
    ¬ (∀ label, chartAtomWeight (threeLinesDirection slide) label = unit) := by
  intro huniform
  have h0 := huniform 0
  have h2 := huniform 2
  rw [threeLinesDirection_chartAtomWeight_zero] at h0
  rw [threeLinesDirection_chartAtomWeight_two] at h2
  linarith

/-- The A2 rung in full, with the five constant prices and the one that moves
with the slide. -/
theorem threeLines_chartRatioSum_eq (slide : ℝ) (mass weight : Fin 6 → ℝ)
    (tree : Finset (Fin 6)) :
    chartRatioSum (threeLinesDirection slide) mass weight tree
      = ∑ label ∈ tree, mass label / weight label
          * chartAtomWeight (threeLinesDirection slide) label := rfl

/-! ## The rung is never vacuous, and the third coefficient is where trees die

Two facts frame the refutation below.  The full label set always clears the
rung, because every weight is strictly below one, so the rung never fails for a
trivial reason.  And the selected tree's own monomial in the spanning-tree
polynomial is always positive, so when the third coefficient fails it fails on
the fifteen monomials of the OTHER trees. -/

/-- Every label's mass-to-weight ratio strictly exceeds its mass, because the
weights are a probability vector on six labels. -/
theorem kFour_mass_lt_ratio (point : DirectionChartPoint 6) (label : Fin 6) :
    point.mass label < point.mass label / point.weight label := by
  have hweight := point.weight_pos label
  have hmass := point.mass_pos label
  have hlt := chartPoint_weight_lt_one point label
  rw [lt_div_iff₀ hweight]
  nlinarith

/-- **The rung is never vacuous.**  The full label set always clears it, so a
failure of the rung is a statement about the selection and never about the
point. -/
theorem kFour_univ_ratioSum_gt (point : DirectionChartPoint 6) :
    kFourTotalMass point < kFourRatioSum point Finset.univ := by
  refine Finset.sum_lt_sum_of_nonempty ⟨0, Finset.mem_univ 0⟩ ?_
  intro label _
  exact kFour_mass_lt_ratio point label

/-- **The selected tree's own monomial is positive.**  Every factor is a
selection value at a selected label, and those are strictly positive. -/
theorem selectionValue_prod_pos (point : DirectionChartPoint 6) (tree : Finset (Fin 6)) :
    0 < ∏ label ∈ tree, selectionValue point.mass point.weight tree label := by
  refine Finset.prod_pos ?_
  intro label hmem
  exact selectionValue_pos_of_mem point tree label hmem

/-! ## The rung does not order the trees

The point below has weights `(1,1,1,2,1,3)/9` and masses
`(2/3, 1, 1/2, 2/3, 2/3, 3/2)`.  Its mass-to-weight ratios are `(6, 9, 9/2, 3,
6, 9/2)` and its total mass is `5`.

The tree `{0,1,4}` has mass-to-weight sum `21`, the STRICT maximum over all
sixteen spanning trees -- the next largest is `39/2`.  It clears the first two
coefficients, at `16` and `933/4`, and fails the third at `-55/6`.

The tree `{0,1,5}` has the smaller sum `39/2` and is positive definite, at
`29/2`, `345/2` and `85/3`.

So the greedy maximum of the rung is not a designation. -/

noncomputable def ratioRefuterMass : Fin 6 → ℝ :=
  ![2 / 3, 1, 1 / 2, 2 / 3, 2 / 3, 3 / 2]

noncomputable def ratioRefuterWeight : Fin 6 → ℝ :=
  ![1 / 9, 1 / 9, 1 / 9, 2 / 9, 1 / 9, 1 / 3]

theorem ratioRefuterMass_pos (label : Fin 6) : 0 < ratioRefuterMass label := by
  fin_cases label <;> norm_num [ratioRefuterMass]

theorem ratioRefuterWeight_pos (label : Fin 6) : 0 < ratioRefuterWeight label := by
  fin_cases label <;> norm_num [ratioRefuterWeight]

theorem ratioRefuterWeight_sum : ∑ label, ratioRefuterWeight label = 1 := by
  simp [Fin.sum_univ_six, ratioRefuterWeight]
  norm_num

/-- The chart point of the refutation. -/
noncomputable def ratioRefuterPoint : DirectionChartPoint 6 where
  mass := ratioRefuterMass
  weight := ratioRefuterWeight
  mass_pos := ratioRefuterMass_pos
  weight_pos := ratioRefuterWeight_pos
  weight_sum_one := ratioRefuterWeight_sum

theorem ratioRefuter_totalMass : kFourTotalMass ratioRefuterPoint = 5 := by
  simp [kFourTotalMass, ratioRefuterPoint, Fin.sum_univ_six, ratioRefuterMass]
  norm_num

theorem ratioRefuter_ratioSum_argmax :
    kFourRatioSum ratioRefuterPoint {0, 1, 4} = 21 := by
  simp only [kFourRatioSum, ratioRefuterPoint]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [ratioRefuterMass, ratioRefuterWeight]
  norm_num

theorem ratioRefuter_ratioSum_winner :
    kFourRatioSum ratioRefuterPoint {0, 1, 5} = 39 / 2 := by
  simp only [kFourRatioSum, ratioRefuterPoint]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]
  simp [ratioRefuterMass, ratioRefuterWeight]
  norm_num

/-- The loser has the strictly larger rung. -/
theorem ratioRefuter_rung_strict :
    kFourRatioSum ratioRefuterPoint {0, 1, 5} < kFourRatioSum ratioRefuterPoint {0, 1, 4} := by
  rw [ratioRefuter_ratioSum_argmax, ratioRefuter_ratioSum_winner]
  norm_num

/-! ### The selection values at the two trees -/

theorem ratioRefuter_sv_argmax_zero :
    selectionValue ratioRefuterMass ratioRefuterWeight {0, 1, 4} 0 = 16 / 3 := by
  simp [selectionValue, ratioRefuterMass, ratioRefuterWeight]; norm_num

theorem ratioRefuter_sv_argmax_one :
    selectionValue ratioRefuterMass ratioRefuterWeight {0, 1, 4} 1 = 8 := by
  simp [selectionValue, ratioRefuterMass, ratioRefuterWeight]; norm_num

theorem ratioRefuter_sv_argmax_two :
    selectionValue ratioRefuterMass ratioRefuterWeight {0, 1, 4} 2 = -(1 / 2) := by
  simp [selectionValue, ratioRefuterMass]

theorem ratioRefuter_sv_argmax_three :
    selectionValue ratioRefuterMass ratioRefuterWeight {0, 1, 4} 3 = -(2 / 3) := by
  simp [selectionValue, ratioRefuterMass]

theorem ratioRefuter_sv_argmax_four :
    selectionValue ratioRefuterMass ratioRefuterWeight {0, 1, 4} 4 = 16 / 3 := by
  simp [selectionValue, ratioRefuterMass, ratioRefuterWeight]; norm_num

theorem ratioRefuter_sv_argmax_five :
    selectionValue ratioRefuterMass ratioRefuterWeight {0, 1, 4} 5 = -(3 / 2) := by
  simp [selectionValue, ratioRefuterMass]

theorem ratioRefuter_sv_winner_zero :
    selectionValue ratioRefuterMass ratioRefuterWeight {0, 1, 5} 0 = 16 / 3 := by
  simp [selectionValue, ratioRefuterMass, ratioRefuterWeight]; norm_num

theorem ratioRefuter_sv_winner_one :
    selectionValue ratioRefuterMass ratioRefuterWeight {0, 1, 5} 1 = 8 := by
  simp [selectionValue, ratioRefuterMass, ratioRefuterWeight]; norm_num

theorem ratioRefuter_sv_winner_two :
    selectionValue ratioRefuterMass ratioRefuterWeight {0, 1, 5} 2 = -(1 / 2) := by
  simp [selectionValue, ratioRefuterMass]

theorem ratioRefuter_sv_winner_three :
    selectionValue ratioRefuterMass ratioRefuterWeight {0, 1, 5} 3 = -(2 / 3) := by
  simp [selectionValue, ratioRefuterMass]

theorem ratioRefuter_sv_winner_four :
    selectionValue ratioRefuterMass ratioRefuterWeight {0, 1, 5} 4 = -(2 / 3) := by
  simp [selectionValue, ratioRefuterMass]

theorem ratioRefuter_sv_winner_five :
    selectionValue ratioRefuterMass ratioRefuterWeight {0, 1, 5} 5 = 3 := by
  simp [selectionValue, ratioRefuterMass, ratioRefuterWeight]; norm_num

/-- **The greedy maximum of the rung is not positive definite.**  It clears the
first two invariant coefficients and fails the spanning-tree polynomial. -/
theorem ratioRefuter_argmax_not_posDef :
    ¬ (directionChartGap kFourDirection ratioRefuterMass ratioRefuterWeight {0, 1, 4}).PosDef := by
  rw [kFourTree_posDef_iff_polynomial]
  intro hall
  have hthree := hall.2.2
  rw [kFourTreePolynomial] at hthree
  rw [ratioRefuter_sv_argmax_zero, ratioRefuter_sv_argmax_one, ratioRefuter_sv_argmax_two,
    ratioRefuter_sv_argmax_three, ratioRefuter_sv_argmax_four, ratioRefuter_sv_argmax_five]
    at hthree
  norm_num at hthree

/-- **A tree of smaller rung is positive definite.** -/
theorem ratioRefuter_winner_posDef :
    (directionChartGap kFourDirection ratioRefuterMass ratioRefuterWeight {0, 1, 5}).PosDef := by
  rw [kFourTree_posDef_iff_polynomial]
  refine ⟨?_, ?_, ?_⟩
  · rw [Fin.sum_univ_six, ratioRefuter_sv_winner_zero, ratioRefuter_sv_winner_one,
      ratioRefuter_sv_winner_two, ratioRefuter_sv_winner_three, ratioRefuter_sv_winner_four,
      ratioRefuter_sv_winner_five]
    norm_num
  · rw [kFourPairForm, ratioRefuter_sv_winner_zero, ratioRefuter_sv_winner_one,
      ratioRefuter_sv_winner_two, ratioRefuter_sv_winner_three, ratioRefuter_sv_winner_four,
      ratioRefuter_sv_winner_five]
    norm_num
  · rw [kFourTreePolynomial, ratioRefuter_sv_winner_zero, ratioRefuter_sv_winner_one,
      ratioRefuter_sv_winner_two, ratioRefuter_sv_winner_three, ratioRefuter_sv_winner_four,
      ratioRefuter_sv_winner_five]
    norm_num

/-- **The rung does not order the trees by quality.**  There is a chart point
carrying two spanning trees where the one of strictly larger mass-to-weight sum
fails and the one of smaller sum succeeds.  No designation reading only the rung
can pick a positive definite tree. -/
theorem kFourRatioSum_not_monotone_posDef :
    ∃ point : DirectionChartPoint 6, ∃ loser winner : Finset (Fin 6),
      kFourRatioSum point winner < kFourRatioSum point loser
        ∧ (directionChartGap kFourDirection point.mass point.weight winner).PosDef
        ∧ ¬ (directionChartGap kFourDirection point.mass point.weight loser).PosDef :=
  ⟨ratioRefuterPoint, {0, 1, 4}, {0, 1, 5}, ratioRefuter_rung_strict,
    ratioRefuter_winner_posDef, ratioRefuter_argmax_not_posDef⟩

/-- **The designation, and its refutation.**  A rung-argmax designation asserts
that whenever some selection of a family is positive definite, one of largest
rung is.  The witness above refutes it on the two-element family. -/
def KFourRatioSumArgmaxHostsStrictTree : Prop :=
  ∀ (point : DirectionChartPoint 6) (family : Finset (Finset (Fin 6))) (best : Finset (Fin 6)),
    best ∈ family →
    (∀ tree ∈ family, kFourRatioSum point tree ≤ kFourRatioSum point best) →
    (∃ tree ∈ family,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef) →
    (directionChartGap kFourDirection point.mass point.weight best).PosDef

theorem not_kFourRatioSumArgmaxHostsStrictTree : ¬ KFourRatioSumArgmaxHostsStrictTree := by
  intro hdesignation
  have hmem : ({0, 1, 4} : Finset (Fin 6)) ∈ ({{0, 1, 4}, {0, 1, 5}} : Finset (Finset (Fin 6))) := by
    decide
  have hmax : ∀ tree ∈ ({{0, 1, 4}, {0, 1, 5}} : Finset (Finset (Fin 6))),
      kFourRatioSum ratioRefuterPoint tree ≤ kFourRatioSum ratioRefuterPoint {0, 1, 4} := by
    intro tree htree
    have hcases : tree = ({0, 1, 4} : Finset (Fin 6)) ∨ tree = ({0, 1, 5} : Finset (Fin 6)) := by
      simpa using htree
    rcases hcases with rfl | rfl
    · exact le_rfl
    · exact ratioRefuter_rung_strict.le
  have hexists : ∃ tree ∈ ({{0, 1, 4}, {0, 1, 5}} : Finset (Finset (Fin 6))),
      (directionChartGap kFourDirection ratioRefuterPoint.mass
        ratioRefuterPoint.weight tree).PosDef := by
    refine ⟨{0, 1, 5}, by decide, ?_⟩
    exact ratioRefuter_winner_posDef
  exact ratioRefuter_argmax_not_posDef
    (hdesignation ratioRefuterPoint {{0, 1, 4}, {0, 1, 5}} {0, 1, 4} hmem hmax hexists)

end Gtz
