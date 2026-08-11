import Gtz.Design.KFourChartClosure
import Gtz.Design.KFourDescentLadder

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The forced set of the `M(K4)` chart is a forest

A chart label is FORCED when its boosted slack leverage reaches one,

    kFourMassTreeSum s  ≤  (m_c / w_c) * kFourContractionTreePolynomial s c ,
    s_c = m_c / w_c - m_c   the slack conductance,

which is exactly the negation of the probe inequality that a strictly dominating
subset must satisfy at every label it omits.  A forced label therefore lies inside
EVERY strictly dominating subset.

This file settles what the forced set can be, and the answer bounds the whole
method: it is always a FOREST of `K4`, hence always extends to a spanning tree,
hence the forcing condition can never exclude every candidate.  Forcing prunes;
it cannot decide, and it cannot refute.

The two ingredients are both about the spanning-tree measure of the slack network.
Writing `T` for the tree sum and `Q_c` for the contraction polynomial, the ratio
`s_c Q_c / T` is the probability that `c` lies in a random spanning tree, so:

* **the cycle bound.**  Every spanning tree omits an edge of every cycle, so the
  probabilities along a cycle of length `n` total at most `n - 1`.  At a triangle
  that is the polynomial inequality `sum_tri s_c Q_c ≤ 2 T`, whose defect is the
  explicit seven-monomial positive combination proved below; at a four-cycle it is
  free, because the total over ALL six labels is exactly `3 T`
  (`Gtz.kFourLeverage_sumIdentity`) and the two omitted terms are positive.

* **the weight budget.**  Forcing `c` gives `(1 - w_c) T ≤ s_c Q_c`, so a forced
  cycle of length `n` totals at least `(n - sum of its weights) T`, and its weights
  total strictly below one because the six chart weights are positive and sum to one.

Together `n - 1 ≥ n - (weights) > n - 1`, which is the contradiction.

The combinatorial half — a cycle-free subset of the six `K4` edges sits inside a
spanning tree — is decided by the kernel over the sixty-four subsets of `Fin 6`.
-/

namespace Gtz

open Matrix

/-! ## The arithmetic of a forced cycle -/

/-- Three labels forced at once, against a bound of twice the tree sum, contradict
the weight budget.  Stated over bare reals: `treeSum` is the spanning-tree sum,
each `leverage` is a slack leverage numerator, and `weightRest` is the total weight
of the labels off the cycle. -/
theorem false_of_threeForcedAgainstTwo {treeSum leverageFirst leverageSecond
    leverageThird weightFirst weightSecond weightThird weightRest : ℝ}
    (htreeSum : 0 < treeSum)
    (hbound : leverageFirst + leverageSecond + leverageThird ≤ 2 * treeSum)
    (hfirst : (1 - weightFirst) * treeSum ≤ leverageFirst)
    (hsecond : (1 - weightSecond) * treeSum ≤ leverageSecond)
    (hthird : (1 - weightThird) * treeSum ≤ leverageThird)
    (hrest : 0 < weightRest)
    (hsum : weightFirst + weightSecond + weightThird + weightRest = 1) : False := by
  nlinarith [mul_pos hrest htreeSum]

/-- Four labels forced at once, against a bound of three times the tree sum,
contradict the weight budget. -/
theorem false_of_fourForcedAgainstThree {treeSum leverageFirst leverageSecond
    leverageThird leverageFourth weightFirst weightSecond weightThird weightFourth
    weightRest : ℝ}
    (htreeSum : 0 < treeSum)
    (hbound : leverageFirst + leverageSecond + leverageThird + leverageFourth
      ≤ 3 * treeSum)
    (hfirst : (1 - weightFirst) * treeSum ≤ leverageFirst)
    (hsecond : (1 - weightSecond) * treeSum ≤ leverageSecond)
    (hthird : (1 - weightThird) * treeSum ≤ leverageThird)
    (hfourth : (1 - weightFourth) * treeSum ≤ leverageFourth)
    (hrest : 0 < weightRest)
    (hsum : weightFirst + weightSecond + weightThird + weightFourth + weightRest = 1) :
    False := by
  nlinarith [mul_pos hrest htreeSum]

/-! ## The cycle bounds of the slack spanning-tree measure -/

/-- **The triangle bound.**  A spanning tree of `K4` carries at most two edges of
any triangle, so the three slack leverage numerators of a triangle total at most
twice the tree sum.  The defect is an explicit positive combination of seven tree
monomials, one for each spanning tree that misses at least two triangle edges. -/
theorem kFourTriangleLeverage_le_two_mul_treeSum (slack : Fin 6 → ℝ)
    (hpos : ∀ label, 0 < slack label) {first second third : Fin 6}
    (htriangle : (first = 0 ∧ second = 1 ∧ third = 2)
      ∨ (first = 0 ∧ second = 3 ∧ third = 4)
      ∨ (first = 1 ∧ second = 3 ∧ third = 5)
      ∨ (first = 2 ∧ second = 4 ∧ third = 5)) :
    slack first * kFourContractionTreePolynomial slack first
        + slack second * kFourContractionTreePolynomial slack second
        + slack third * kFourContractionTreePolynomial slack third
      ≤ 2 * kFourMassTreeSum slack := by
  have hzero := hpos 0
  have hone := hpos 1
  have htwo := hpos 2
  have hthree := hpos 3
  have hfour := hpos 4
  have hfive := hpos 5
  rcases htriangle with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl⟩ <;>
    simp only [kFourMassTreeSum, kFourContractionTreePolynomial_zero,
      kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
      kFourContractionTreePolynomial_three, kFourContractionTreePolynomial_four,
      kFourContractionTreePolynomial_five] <;>
    nlinarith [mul_pos (mul_pos hzero hthree) hfive,
      mul_pos (mul_pos hzero hfour) hfive, mul_pos (mul_pos hone hthree) hfour,
      mul_pos (mul_pos hone hfour) hfive, mul_pos (mul_pos htwo hthree) hfour,
      mul_pos (mul_pos htwo hthree) hfive, mul_pos (mul_pos hthree hfour) hfive,
      mul_pos (mul_pos hzero hone) hfive, mul_pos (mul_pos hzero htwo) hfive,
      mul_pos (mul_pos hone htwo) hthree, mul_pos (mul_pos hone htwo) hfour,
      mul_pos (mul_pos hone htwo) hfive, mul_pos (mul_pos htwo hthree) hfive,
      mul_pos (mul_pos hzero hone) hfour, mul_pos (mul_pos hzero htwo) hthree,
      mul_pos (mul_pos hzero htwo) hfour, mul_pos (mul_pos hzero hone) hthree,
      mul_pos (mul_pos hzero hthree) hfour, mul_pos (mul_pos hone hthree) hfive]

/-- **The four-cycle bound.**  A spanning tree of `K4` carries at most three edges
of any four-cycle.  This one costs nothing beyond the landed trace identity: the
six numerators total exactly three times the tree sum, and the two labels off the
cycle contribute positively. -/
theorem kFourFourCycleLeverage_le_three_mul_treeSum (slack : Fin 6 → ℝ)
    (hpos : ∀ label, 0 < slack label) {first second third fourth : Fin 6}
    (hcycle : (first = 0 ∧ second = 2 ∧ third = 3 ∧ fourth = 5)
      ∨ (first = 0 ∧ second = 1 ∧ third = 4 ∧ fourth = 5)
      ∨ (first = 1 ∧ second = 2 ∧ third = 3 ∧ fourth = 4)) :
    slack first * kFourContractionTreePolynomial slack first
        + slack second * kFourContractionTreePolynomial slack second
        + slack third * kFourContractionTreePolynomial slack third
        + slack fourth * kFourContractionTreePolynomial slack fourth
      ≤ 3 * kFourMassTreeSum slack := by
  have hzero := hpos 0
  have hone := hpos 1
  have htwo := hpos 2
  have hthree := hpos 3
  have hfour := hpos 4
  have hfive := hpos 5
  rcases hcycle with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ <;>
    simp only [kFourMassTreeSum, kFourContractionTreePolynomial_zero,
      kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
      kFourContractionTreePolynomial_three, kFourContractionTreePolynomial_four,
      kFourContractionTreePolynomial_five] <;>
    nlinarith [mul_pos (mul_pos hzero hone) hthree, mul_pos (mul_pos hzero htwo) hfour,
      mul_pos (mul_pos hone htwo) hfive, mul_pos (mul_pos hthree hfour) hfive,
      mul_pos (mul_pos hzero hone) hfour, mul_pos (mul_pos hzero hone) hfive,
      mul_pos (mul_pos hzero htwo) hthree, mul_pos (mul_pos hzero htwo) hfive,
      mul_pos (mul_pos hzero hthree) hfive, mul_pos (mul_pos hzero hfour) hfive,
      mul_pos (mul_pos hone htwo) hthree, mul_pos (mul_pos hone htwo) hfour,
      mul_pos (mul_pos hone hthree) hfour, mul_pos (mul_pos hone hfour) hfive,
      mul_pos (mul_pos htwo hthree) hfour, mul_pos (mul_pos htwo hthree) hfive]

/-! ## No cycle of the chart can be forced

The two elementary chart facts this section runs on -- that every chart weight is
below one, and that the slack conductance is positive at every label -- are
`Gtz.chartPoint_weight_lt_one` and `Gtz.chartSlack_pos_of_chartPoint` in
`Gtz/Design/KFourDescentLadder.lean`, where the forced-edge law itself lives.
-/

/-- Forcing a label, rescaled by `1 - w`: the boosted form becomes the SLACK form,
which is the one the cycle bounds are stated in. -/
theorem kFourForcedSlackLeverage_scaled (point : DirectionChartPoint 6)
    (slack : Fin 6 → ℝ)
    (hslack : ∀ label,
      slack label = point.mass label / point.weight label - point.mass label)
    (label : Fin 6)
    (hforced : kFourMassTreeSum slack ≤ point.mass label / point.weight label
      * kFourContractionTreePolynomial slack label) :
    (1 - point.weight label) * kFourMassTreeSum slack
      ≤ slack label * kFourContractionTreePolynomial slack label := by
  have hweightPos := point.weight_pos label
  have hlt := chartPoint_weight_lt_one point label
  have hfactor : (1 - point.weight label) * (point.mass label / point.weight label)
      = slack label := by
    rw [hslack label]
    field_simp
  calc (1 - point.weight label) * kFourMassTreeSum slack
      ≤ (1 - point.weight label)
          * (point.mass label / point.weight label
            * kFourContractionTreePolynomial slack label) :=
        mul_le_mul_of_nonneg_left hforced (by linarith)
    _ = slack label * kFourContractionTreePolynomial slack label := by
        rw [← hfactor]; ring

/-- **No triangle of the chart is forced.**  Three labels forming a `K4` triangle
cannot all reach boosted slack leverage one. -/
theorem not_kFourForcedTriangle (point : DirectionChartPoint 6) (slack : Fin 6 → ℝ)
    (hslack : ∀ label,
      slack label = point.mass label / point.weight label - point.mass label)
    {first second third : Fin 6}
    (htriangle : (first = 0 ∧ second = 1 ∧ third = 2)
      ∨ (first = 0 ∧ second = 3 ∧ third = 4)
      ∨ (first = 1 ∧ second = 3 ∧ third = 5)
      ∨ (first = 2 ∧ second = 4 ∧ third = 5))
    (hfirst : kFourMassTreeSum slack ≤ point.mass first / point.weight first
      * kFourContractionTreePolynomial slack first)
    (hsecond : kFourMassTreeSum slack ≤ point.mass second / point.weight second
      * kFourContractionTreePolynomial slack second)
    (hthird : kFourMassTreeSum slack ≤ point.mass third / point.weight third
      * kFourContractionTreePolynomial slack third) : False := by
  have hslackPos : ∀ label, 0 < slack label := by
    intro label
    rw [hslack label]
    simpa [chartSlack] using chartSlack_pos_of_chartPoint point label
  have htreeSum : 0 < kFourMassTreeSum slack := kFourMassTreeSum_pos slack hslackPos
  have hbound := kFourTriangleLeverage_le_two_mul_treeSum slack hslackPos htriangle
  -- turn each forcing hypothesis into the slack form by multiplying by `1 - w`
  have hscale := kFourForcedSlackLeverage_scaled point slack hslack
  have hsum := point.weight_sum_one
  rw [Fin.sum_univ_six] at hsum
  have hzero := point.weight_pos 0
  have hone := point.weight_pos 1
  have htwo := point.weight_pos 2
  have hthree := point.weight_pos 3
  have hfour := point.weight_pos 4
  have hfive := point.weight_pos 5
  rcases htriangle with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    | ⟨rfl, rfl, rfl⟩
  · exact false_of_threeForcedAgainstTwo htreeSum hbound (hscale 0 hfirst)
      (hscale 1 hsecond) (hscale 2 hthird)
      (by linarith : (0 : ℝ) < point.weight 3 + point.weight 4 + point.weight 5)
      (by linarith)
  · exact false_of_threeForcedAgainstTwo htreeSum hbound (hscale 0 hfirst)
      (hscale 3 hsecond) (hscale 4 hthird)
      (by linarith : (0 : ℝ) < point.weight 1 + point.weight 2 + point.weight 5)
      (by linarith)
  · exact false_of_threeForcedAgainstTwo htreeSum hbound (hscale 1 hfirst)
      (hscale 3 hsecond) (hscale 5 hthird)
      (by linarith : (0 : ℝ) < point.weight 0 + point.weight 2 + point.weight 4)
      (by linarith)
  · exact false_of_threeForcedAgainstTwo htreeSum hbound (hscale 2 hfirst)
      (hscale 4 hsecond) (hscale 5 hthird)
      (by linarith : (0 : ℝ) < point.weight 0 + point.weight 1 + point.weight 3)
      (by linarith)

/-- **No four-cycle of the chart is forced.** -/
theorem not_kFourForcedFourCycle (point : DirectionChartPoint 6) (slack : Fin 6 → ℝ)
    (hslack : ∀ label,
      slack label = point.mass label / point.weight label - point.mass label)
    {first second third fourth : Fin 6}
    (hcycle : (first = 0 ∧ second = 2 ∧ third = 3 ∧ fourth = 5)
      ∨ (first = 0 ∧ second = 1 ∧ third = 4 ∧ fourth = 5)
      ∨ (first = 1 ∧ second = 2 ∧ third = 3 ∧ fourth = 4))
    (hfirst : kFourMassTreeSum slack ≤ point.mass first / point.weight first
      * kFourContractionTreePolynomial slack first)
    (hsecond : kFourMassTreeSum slack ≤ point.mass second / point.weight second
      * kFourContractionTreePolynomial slack second)
    (hthird : kFourMassTreeSum slack ≤ point.mass third / point.weight third
      * kFourContractionTreePolynomial slack third)
    (hfourth : kFourMassTreeSum slack ≤ point.mass fourth / point.weight fourth
      * kFourContractionTreePolynomial slack fourth) : False := by
  have hslackPos : ∀ label, 0 < slack label := by
    intro label
    rw [hslack label]
    simpa [chartSlack] using chartSlack_pos_of_chartPoint point label
  have htreeSum : 0 < kFourMassTreeSum slack := kFourMassTreeSum_pos slack hslackPos
  have hbound := kFourFourCycleLeverage_le_three_mul_treeSum slack hslackPos hcycle
  have hscale := kFourForcedSlackLeverage_scaled point slack hslack
  have hsum := point.weight_sum_one
  rw [Fin.sum_univ_six] at hsum
  have hzero := point.weight_pos 0
  have hone := point.weight_pos 1
  have htwo := point.weight_pos 2
  have hthree := point.weight_pos 3
  have hfour := point.weight_pos 4
  have hfive := point.weight_pos 5
  rcases hcycle with ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl, rfl⟩
  · exact false_of_fourForcedAgainstThree htreeSum hbound (hscale 0 hfirst)
      (hscale 2 hsecond) (hscale 3 hthird) (hscale 5 hfourth)
      (by linarith : (0 : ℝ) < point.weight 1 + point.weight 4) (by linarith)
  · exact false_of_fourForcedAgainstThree htreeSum hbound (hscale 0 hfirst)
      (hscale 1 hsecond) (hscale 4 hthird) (hscale 5 hfourth)
      (by linarith : (0 : ℝ) < point.weight 2 + point.weight 3) (by linarith)
  · exact false_of_fourForcedAgainstThree htreeSum hbound (hscale 1 hfirst)
      (hscale 2 hsecond) (hscale 3 hthird) (hscale 4 hfourth)
      (by linarith : (0 : ℝ) < point.weight 0 + point.weight 5) (by linarith)

/-! ## A cycle-free set of chart labels is inside a spanning tree -/

/-- Kernel-decided over the sixty-four subsets of `Fin 6`: a set of `K4` edges
containing none of the four triangles and none of the three four-cycles is a forest,
hence sits inside one of the sixteen spanning trees. -/
theorem kFourAcyclic_subset_spanningTree (forced : Finset (Fin 6))
    (hfirstTriangle : ¬ ({0, 1, 2} : Finset (Fin 6)) ⊆ forced)
    (hsecondTriangle : ¬ ({0, 3, 4} : Finset (Fin 6)) ⊆ forced)
    (hthirdTriangle : ¬ ({1, 3, 5} : Finset (Fin 6)) ⊆ forced)
    (hfourthTriangle : ¬ ({2, 4, 5} : Finset (Fin 6)) ⊆ forced)
    (hfirstCycle : ¬ ({0, 2, 3, 5} : Finset (Fin 6)) ⊆ forced)
    (hsecondCycle : ¬ ({0, 1, 4, 5} : Finset (Fin 6)) ⊆ forced)
    (hthirdCycle : ¬ ({1, 2, 3, 4} : Finset (Fin 6)) ⊆ forced) :
    ∃ tree ∈ kFourSpanningTreeList, forced ⊆ tree := by
  revert hfirstTriangle hsecondTriangle hthirdTriangle hfourthTriangle
    hfirstCycle hsecondCycle hthirdCycle
  revert forced
  decide

/-! ## The headline: forcing never excludes every candidate -/

/-- **The forced set of a chart point is a forest, so it lies inside a spanning
tree.**  Every label of `forced` is forced; the conclusion exhibits a spanning tree
containing all of them. -/
theorem exists_kFourSpanningTree_superset_of_forced (point : DirectionChartPoint 6)
    (slack : Fin 6 → ℝ)
    (hslack : ∀ label,
      slack label = point.mass label / point.weight label - point.mass label)
    (forced : Finset (Fin 6))
    (hforced : ∀ label ∈ forced, kFourMassTreeSum slack
      ≤ point.mass label / point.weight label
        * kFourContractionTreePolynomial slack label) :
    ∃ tree ∈ kFourSpanningTreeList, forced ⊆ tree := by
  refine kFourAcyclic_subset_spanningTree forced ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact fun hsub => not_kFourForcedTriangle point slack hslack
      (Or.inl ⟨rfl, rfl, rfl⟩) (hforced 0 (hsub (by decide)))
      (hforced 1 (hsub (by decide))) (hforced 2 (hsub (by decide)))
  · exact fun hsub => not_kFourForcedTriangle point slack hslack
      (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩)) (hforced 0 (hsub (by decide)))
      (hforced 3 (hsub (by decide))) (hforced 4 (hsub (by decide)))
  · exact fun hsub => not_kFourForcedTriangle point slack hslack
      (Or.inr (Or.inr (Or.inl ⟨rfl, rfl, rfl⟩))) (hforced 1 (hsub (by decide)))
      (hforced 3 (hsub (by decide))) (hforced 5 (hsub (by decide)))
  · exact fun hsub => not_kFourForcedTriangle point slack hslack
      (Or.inr (Or.inr (Or.inr ⟨rfl, rfl, rfl⟩))) (hforced 2 (hsub (by decide)))
      (hforced 4 (hsub (by decide))) (hforced 5 (hsub (by decide)))
  · exact fun hsub => not_kFourForcedFourCycle point slack hslack
      (Or.inl ⟨rfl, rfl, rfl, rfl⟩) (hforced 0 (hsub (by decide)))
      (hforced 2 (hsub (by decide))) (hforced 3 (hsub (by decide)))
      (hforced 5 (hsub (by decide)))
  · exact fun hsub => not_kFourForcedFourCycle point slack hslack
      (Or.inr (Or.inl ⟨rfl, rfl, rfl, rfl⟩)) (hforced 0 (hsub (by decide)))
      (hforced 1 (hsub (by decide))) (hforced 4 (hsub (by decide)))
      (hforced 5 (hsub (by decide)))
  · exact fun hsub => not_kFourForcedFourCycle point slack hslack
      (Or.inr (Or.inr ⟨rfl, rfl, rfl, rfl⟩)) (hforced 1 (hsub (by decide)))
      (hforced 2 (hsub (by decide))) (hforced 3 (hsub (by decide)))
      (hforced 4 (hsub (by decide)))

/-- **Forcing prunes; it can never decide.**  Whatever the chart point, the labels
it forces still have a three-element superset, so the forcing condition never
excludes every candidate subset and can never by itself refute the class. -/
theorem exists_cardThree_superset_of_forced (point : DirectionChartPoint 6)
    (slack : Fin 6 → ℝ)
    (hslack : ∀ label,
      slack label = point.mass label / point.weight label - point.mass label)
    (forced : Finset (Fin 6))
    (hforced : ∀ label ∈ forced, kFourMassTreeSum slack
      ≤ point.mass label / point.weight label
        * kFourContractionTreePolynomial slack label) :
    ∃ selected : Finset (Fin 6), selected.card = 3 ∧ forced ⊆ selected := by
  obtain ⟨tree, hmem, hsubset⟩ :=
    exists_kFourSpanningTree_superset_of_forced point slack hslack forced hforced
  exact ⟨tree, kFourSpanningTree_card tree hmem, hsubset⟩

/-! ## The triangle bound is sharp: two of three CAN be forced -/

/-- Masses of the two-forced witness. -/
noncomputable def kFourTwoForcedWitnessMass : Fin 6 → ℝ
  | 0 => 50
  | 1 => 50
  | 2 => 1 / 20
  | 3 => 1
  | 4 => 1
  | 5 => 1 / 4

/-- Weights of the two-forced witness. -/
noncomputable def kFourTwoForcedWitnessWeight : Fin 6 → ℝ
  | 0 => 1 / 6
  | 1 => 1 / 9
  | 2 => 2 / 9
  | 3 => 1 / 6
  | 4 => 1 / 6
  | 5 => 1 / 6

/-- Slack conductances of the two-forced witness. -/
noncomputable def kFourTwoForcedWitnessSlack : Fin 6 → ℝ
  | 0 => 250
  | 1 => 400
  | 2 => 7 / 40
  | 3 => 5
  | 4 => 5
  | 5 => 5 / 4

/-- The two-forced witness as a chart point. -/
noncomputable def kFourTwoForcedWitnessPoint : DirectionChartPoint 6 where
  mass := kFourTwoForcedWitnessMass
  weight := kFourTwoForcedWitnessWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [kFourTwoForcedWitnessMass]
  weight_pos := by intro label; fin_cases label <;> norm_num [kFourTwoForcedWitnessWeight]
  weight_sum_one := by
    rw [Fin.sum_univ_six]; norm_num [kFourTwoForcedWitnessWeight]

theorem kFourTwoForcedWitness_slack_eq (label : Fin 6) :
    kFourTwoForcedWitnessSlack label
      = kFourTwoForcedWitnessPoint.mass label / kFourTwoForcedWitnessPoint.weight label
        - kFourTwoForcedWitnessPoint.mass label := by
  fin_cases label <;>
    norm_num [kFourTwoForcedWitnessSlack, kFourTwoForcedWitnessPoint,
      kFourTwoForcedWitnessMass, kFourTwoForcedWitnessWeight]

/-- **The forcing hypothesis is inhabited, and the triangle bound is sharp:** labels
`0` and `1`, two of the three edges of the triangle `{0, 1, 2}`, are both forced at
this point.  The theorems above are therefore about a region that exists. -/
theorem kFourTwoForcedWitness_forces (label : Fin 6) (hlabel : label = 0 ∨ label = 1) :
    kFourMassTreeSum kFourTwoForcedWitnessSlack
      ≤ kFourTwoForcedWitnessPoint.mass label / kFourTwoForcedWitnessPoint.weight label
        * kFourContractionTreePolynomial kFourTwoForcedWitnessSlack label := by
  rcases hlabel with rfl | rfl <;>
    norm_num [kFourMassTreeSum, kFourContractionTreePolynomial_zero,
      kFourContractionTreePolynomial_one, kFourTwoForcedWitnessSlack,
      kFourTwoForcedWitnessPoint, kFourTwoForcedWitnessMass,
      kFourTwoForcedWitnessWeight]

/-- The third edge of that triangle is NOT forced, as `not_kFourForcedTriangle`
requires.  Its boosted slack leverage is `52875/32` against a tree sum of
`36542125/32`, a factor of about seven hundred short. -/
theorem not_kFourTwoForcedWitness_forcesThird :
    ¬ kFourMassTreeSum kFourTwoForcedWitnessSlack
      ≤ kFourTwoForcedWitnessPoint.mass 2 / kFourTwoForcedWitnessPoint.weight 2
        * kFourContractionTreePolynomial kFourTwoForcedWitnessSlack 2 := by
  norm_num [kFourMassTreeSum, kFourContractionTreePolynomial_two,
    kFourTwoForcedWitnessSlack, kFourTwoForcedWitnessPoint,
    kFourTwoForcedWitnessMass, kFourTwoForcedWitnessWeight]

end Gtz
