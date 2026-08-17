/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.PivotWallVacuity
import Gtz.Design.KFourBandAtlas
import Gtz.Wave.KFourFamilySelectionWiring
import Gtz.Wave.KirchhoffSignTower
import Gtz.Wave.DeflatedCellTotal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# The trace floor of the `K4` chart, and the wiring of the knife-band walls

The registered `A3` proposition is
`Gtz.KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict`.  Three
routes reach it and no route carried a producer.  This module proves a new
unconditional law that kills the first of the three forest tests outright, it
collapses the remaining test count at a deflation-produced tree, and it
connects every route to the registered consumers.

## 1. The new law: the trace floor of the sixteen spanning trees

`Gtz.posDef_directionChartGap_iff_forestTriple` reads strict domination of a
listed tree as THREE spanning-forest sums.  The first of the three is the
trace exclusion `Gtz.kFourGapInvariantOne`.  This module proves that the first
test NEVER blocks all sixteen trees at once.

Three polynomial laws carry the proof, and no matrix appears in any of them.

* `Gtz.kFourMassTreeSum_euler` — the sixteen-term tree sum is homogeneous of
  degree three, so the six masses against their own contraction polynomials
  give three times the tree sum.  One `ring` step.
* `Gtz.kFourShare_bounds` — the share `m_c Q_c(m)` of one edge is the sum of
  the eight tree monomials THROUGH that edge, so it never passes the full
  sixteen-term tree sum.  This is the polynomial form of a leverage bound, and
  it needs no resolvent and no moment matrix.
* `Gtz.kFourWeightedShareFloor` — **the floor.**  The six shares divided by
  their weights pass NINE times the tree sum.  The proof is one tangent line:
  `1 / w` passes `6 - 9 w` because `(3 w - 1) ^ 2` is not negative.  The two
  laws above pay for the two remaining sums.

`Gtz.kFourSpanningTreeList_incidence` counts each edge in exactly eight of the
sixteen listed trees.  The floor of nine and the incidence of eight beat the
demand of three sixteen times over, so
`Gtz.exists_kFourSpanningTree_gapInvariantOne_pos` returns a listed tree with
a strictly positive first invariant, at every chart point, with no hypothesis.

## 2. The deflation collapse

`Gtz.kFour_exists_chartDeflatedTree` is unconditional and returns a listed tree
whose strict domination IS one determinant sign.
`Gtz.det_directionChartGap_eq_kFourMassTreeSum` reads that determinant as the
signed tree sum.  `Gtz.kFour_exists_deflatedTree_forestTriple_iff_massTreeSum`
composes the two: at a PRODUCED tree the three forest sums collapse to the
THIRD one, because the deflated bound pays for the other two.

## 3. What remains

`Gtz.KFourAdjugateAndDetTotal` names the exact residual after section 1: the
second invariant and the determinant, at a tree that the trace floor already
admits.  `Gtz.KFourDeflatedMassTreeSumTotal` names the residual after section
2: one polynomial sign at a produced tree.  Each one discharges the registered
`A3` proposition, the registered chart obligation
`Gtz.DirectionChartIsTieFree Gtz.kFourDirection`, the design-side
`Gtz.KFourFamilySelection`, and `Gtz.KFourKnifeBandRefinedWeakToStrict`.

`Gtz.KFourBothWallAtlasFires` names the third route.  Neither
`Gtz.KFourStarWallAtlasFires` nor `Gtz.KFourPivotWallAtlasFires` carries a
producer anywhere in the tree, and this module names the pair as one target.

## 4. The onward path

This module stops at the `K4` propositions.
`Gtz/Wave/WiringAllFiveOnPath.lean` carries the onward path.
`Gtz.gtzWeightedAll_three_of_allFiveOnPath` takes all five registered
propositions to `Gtz.GtzWeightedAll 3`, and the `K4` knife band is one of the
five.

## 5. The two traps

No theorem here hides an equivalence.  `Gtz.KFourAdjugateAndDetTotal` IS
equivalent to `Gtz.KFourUniversalStrictTree`, and the docstring says so, and
the value of section 1 is the unconditional theorem and never the residual
name.  Every other implication is one-directional, and each docstring names
the stronger side.

No antecedent here is refuted.  `Gtz.kFourPencilCell_not_total` kills the
pencil CELL and never the chart obligation, because
`Gtz.pencilCellRefuterPoint_hasStrictTree` exhibits a strictly dominating tree
at that same refuter point.
`Gtz.kFour_deflatedTree_collapse_at_pencilCellRefuter` and
`Gtz.exists_kFourSpanningTree_gapInvariantOne_pos_at_pencilCellRefuter`
inhabit the antecedents of the two produced laws at that point.
-/

namespace Gtz

/-! ## 1. Three polynomial laws of the sixteen-term tree sum -/

/-- **THE EULER LAW OF THE TREE SUM.**  The sixteen-term spanning-tree sum of
`K4` is homogeneous of degree three, and each contraction polynomial is its
partial derivative.  The six shares add to three times the tree sum. -/
theorem kFourMassTreeSum_euler (vec : Fin 6 → ℝ) :
    ∑ label, vec label * kFourContractionTreePolynomial vec label
      = 3 * kFourMassTreeSum vec := by
  simp only [Fin.sum_univ_six, kFourContractionTreePolynomial_zero,
    kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
    kFourContractionTreePolynomial_three, kFourContractionTreePolynomial_four,
    kFourContractionTreePolynomial_five, kFourMassTreeSum]
  ring

/-- **THE SHARE OF ONE EDGE IS A SUB-SUM.**  The share `m_c Q_c(m)` collects
the eight tree monomials THROUGH the edge `c`, and the tree sum collects all
sixteen.  So the share is not negative and never passes the tree sum.  This is
the polynomial form of the leverage bound, with no resolvent and no moment. -/
theorem kFourShare_bounds (vec : Fin 6 → ℝ) (hvec : ∀ label, 0 ≤ vec label)
    (label : Fin 6) :
    0 ≤ vec label * kFourContractionTreePolynomial vec label
      ∧ vec label * kFourContractionTreePolynomial vec label
          ≤ kFourMassTreeSum vec := by
  have h0 := hvec 0
  have h1 := hvec 1
  have h2 := hvec 2
  have h3 := hvec 3
  have h4 := hvec 4
  have h5 := hvec 5
  have m013 : 0 ≤ vec 0 * vec 1 * vec 3 := mul_nonneg (mul_nonneg h0 h1) h3
  have m024 : 0 ≤ vec 0 * vec 2 * vec 4 := mul_nonneg (mul_nonneg h0 h2) h4
  have m125 : 0 ≤ vec 1 * vec 2 * vec 5 := mul_nonneg (mul_nonneg h1 h2) h5
  have m345 : 0 ≤ vec 3 * vec 4 * vec 5 := mul_nonneg (mul_nonneg h3 h4) h5
  have m014 : 0 ≤ vec 0 * vec 1 * vec 4 := mul_nonneg (mul_nonneg h0 h1) h4
  have m015 : 0 ≤ vec 0 * vec 1 * vec 5 := mul_nonneg (mul_nonneg h0 h1) h5
  have m023 : 0 ≤ vec 0 * vec 2 * vec 3 := mul_nonneg (mul_nonneg h0 h2) h3
  have m025 : 0 ≤ vec 0 * vec 2 * vec 5 := mul_nonneg (mul_nonneg h0 h2) h5
  have m035 : 0 ≤ vec 0 * vec 3 * vec 5 := mul_nonneg (mul_nonneg h0 h3) h5
  have m045 : 0 ≤ vec 0 * vec 4 * vec 5 := mul_nonneg (mul_nonneg h0 h4) h5
  have m123 : 0 ≤ vec 1 * vec 2 * vec 3 := mul_nonneg (mul_nonneg h1 h2) h3
  have m124 : 0 ≤ vec 1 * vec 2 * vec 4 := mul_nonneg (mul_nonneg h1 h2) h4
  have m134 : 0 ≤ vec 1 * vec 3 * vec 4 := mul_nonneg (mul_nonneg h1 h3) h4
  have m145 : 0 ≤ vec 1 * vec 4 * vec 5 := mul_nonneg (mul_nonneg h1 h4) h5
  have m234 : 0 ≤ vec 2 * vec 3 * vec 4 := mul_nonneg (mul_nonneg h2 h3) h4
  have m235 : 0 ≤ vec 2 * vec 3 * vec 5 := mul_nonneg (mul_nonneg h2 h3) h5
  have hcases : label = 0 ∨ label = 1 ∨ label = 2 ∨ label = 3 ∨ label = 4
      ∨ label = 5 := by
    revert label
    decide
  rcases hcases with rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [kFourContractionTreePolynomial_zero,
      kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
      kFourContractionTreePolynomial_three, kFourContractionTreePolynomial_four,
      kFourContractionTreePolynomial_five, kFourMassTreeSum] <;>
    constructor <;>
    nlinarith [m013, m024, m125, m345, m014, m015, m023, m025, m035, m045,
      m123, m124, m134, m145, m234, m235]

/-- **THE TANGENT FLOOR OF THE WEIGHTED SHARES.**  At a chart point the six
shares divided by their weights pass NINE times the tree sum.  The proof is one
tangent line at the point `1 / 3`: for a positive weight, `1 / w` passes
`6 - 9 w`, because `(3 w - 1) ^ 2` is not negative.  The Euler law pays the
first block, and the sub-sum bound with the unit weight sum pays the second. -/
theorem kFourWeightedShareFloor (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 ≤ mass label) (hweight : ∀ label, 0 < weight label)
    (hsum : ∑ label, weight label = 1) :
    9 * kFourMassTreeSum mass
      ≤ ∑ label, mass label * kFourContractionTreePolynomial mass label
          / weight label := by
  have hstep : ∀ label : Fin 6,
      6 * (mass label * kFourContractionTreePolynomial mass label)
          - 9 * (mass label * kFourContractionTreePolynomial mass label
              * weight label)
        ≤ mass label * kFourContractionTreePolynomial mass label
            / weight label := by
    intro label
    have hshare := (kFourShare_bounds mass hmass label).1
    have hpos := hweight label
    rw [← sub_nonneg]
    have hid : mass label * kFourContractionTreePolynomial mass label
          / weight label
        - (6 * (mass label * kFourContractionTreePolynomial mass label)
            - 9 * (mass label * kFourContractionTreePolynomial mass label
                * weight label))
        = mass label * kFourContractionTreePolynomial mass label
            * (3 * weight label - 1) ^ 2 / weight label := by
      field_simp
      ring
    rw [hid]
    exact div_nonneg (mul_nonneg hshare (sq_nonneg _)) hpos.le
  have hsumstep : ∑ label, (6 * (mass label
        * kFourContractionTreePolynomial mass label)
      - 9 * (mass label * kFourContractionTreePolynomial mass label
          * weight label))
      ≤ ∑ label, mass label * kFourContractionTreePolynomial mass label
          / weight label :=
    Finset.sum_le_sum fun label _ => hstep label
  have hsplit : ∑ label, (6 * (mass label
        * kFourContractionTreePolynomial mass label)
      - 9 * (mass label * kFourContractionTreePolynomial mass label
          * weight label))
      = 6 * (∑ label, mass label * kFourContractionTreePolynomial mass label)
        - 9 * (∑ label, mass label
            * kFourContractionTreePolynomial mass label * weight label) := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
  have hweighted : ∑ label, mass label
        * kFourContractionTreePolynomial mass label * weight label
      ≤ kFourMassTreeSum mass := by
    calc ∑ label, mass label
          * kFourContractionTreePolynomial mass label * weight label
        ≤ ∑ label, kFourMassTreeSum mass * weight label :=
          Finset.sum_le_sum fun label _ =>
            mul_le_mul_of_nonneg_right (kFourShare_bounds mass hmass label).2
              (hweight label).le
      _ = kFourMassTreeSum mass * ∑ label, weight label := by
          rw [Finset.mul_sum]
      _ = kFourMassTreeSum mass := by rw [hsum, mul_one]
  have heuler := kFourMassTreeSum_euler mass
  linarith [hsumstep, hsplit, heuler, hweighted]

/-! ## 2. The incidence law of the sixteen listed trees -/

/-- A sum over a three-element subset of the six labels. -/
theorem sum_triple_fin_six (vec : Fin 6 → ℝ) (first second third : Fin 6)
    (hone : first ≠ second) (htwo : first ≠ third) (hthree : second ≠ third) :
    ∑ label ∈ ({first, second, third} : Finset (Fin 6)), vec label
      = vec first + vec second + vec third := by
  rw [Finset.sum_insert (by simp [hone, htwo]), Finset.sum_pair hthree]
  ring

/-- **EACH EDGE SITS IN EIGHT OF THE SIXTEEN TREES.**  Summing any reading over
every listed spanning tree gives eight times the total reading. -/
theorem kFourSpanningTreeList_incidence (vec : Fin 6 → ℝ) :
    (kFourSpanningTreeList.map (fun tree => ∑ label ∈ tree, vec label)).sum
      = 8 * ∑ label, vec label := by
  have triple := sum_triple_fin_six vec
  simp only [kFourSpanningTreeList, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil,
    triple 0 1 3 (by decide) (by decide) (by decide),
    triple 0 2 4 (by decide) (by decide) (by decide),
    triple 1 2 5 (by decide) (by decide) (by decide),
    triple 3 4 5 (by decide) (by decide) (by decide),
    triple 0 1 4 (by decide) (by decide) (by decide),
    triple 0 1 5 (by decide) (by decide) (by decide),
    triple 0 2 3 (by decide) (by decide) (by decide),
    triple 0 2 5 (by decide) (by decide) (by decide),
    triple 0 3 5 (by decide) (by decide) (by decide),
    triple 0 4 5 (by decide) (by decide) (by decide),
    triple 1 2 3 (by decide) (by decide) (by decide),
    triple 1 2 4 (by decide) (by decide) (by decide),
    triple 1 3 4 (by decide) (by decide) (by decide),
    triple 1 4 5 (by decide) (by decide) (by decide),
    triple 2 3 4 (by decide) (by decide) (by decide),
    triple 2 3 5 (by decide) (by decide) (by decide),
    Fin.sum_univ_six]
  ring

/-! ## 3. The first invariant in weighted-share form -/

/-- **THE FIRST INVARIANT IS A WEIGHTED SHARE DEFECT.**  The trace exclusion of
a listed selection reads the shares of the selected edges against their
weights, and pays three times the tree sum.  No matrix survives. -/
theorem kFourGapInvariantOne_eq_weightedShareDefect
    (point : DirectionChartPoint 6) (tree : Finset (Fin 6)) :
    kFourGapInvariantOne point.mass point.weight tree
      = (∑ label ∈ tree, point.mass label
            * kFourContractionTreePolynomial point.mass label
            / point.weight label)
        - 3 * kFourMassTreeSum point.mass := by
  rw [kFourGapInvariantOne_eq_forestSum point.mass point.weight
    (fun label _ => (point.weight_pos label).ne')]
  rw [← Finset.sum_add_sum_compl tree]
  have hinside : ∑ label ∈ tree, signedGapWeight point.mass point.weight tree label
        * kFourContractionTreePolynomial point.mass label
      = (∑ label ∈ tree, point.mass label
            * kFourContractionTreePolynomial point.mass label
            / point.weight label)
        - ∑ label ∈ tree, point.mass label
            * kFourContractionTreePolynomial point.mass label := by
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun label hlabel => ?_
    rw [signedGapWeight, if_pos hlabel]
    have hpos := (point.weight_pos label).ne'
    field_simp
  have houtside : ∑ label ∈ treeᶜ,
        signedGapWeight point.mass point.weight tree label
        * kFourContractionTreePolynomial point.mass label
      = -∑ label ∈ treeᶜ, point.mass label
          * kFourContractionTreePolynomial point.mass label := by
    rw [← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun label hlabel => ?_
    rw [signedGapWeight, if_neg (Finset.mem_compl.mp hlabel)]
    ring
  have hwhole : ∑ label ∈ tree, point.mass label
        * kFourContractionTreePolynomial point.mass label
      + ∑ label ∈ treeᶜ, point.mass label
        * kFourContractionTreePolynomial point.mass label
      = 3 * kFourMassTreeSum point.mass := by
    rw [Finset.sum_add_sum_compl]
    exact kFourMassTreeSum_euler point.mass
  rw [hinside, houtside]
  linarith [hwhole]

/-! ## 4. The unconditional trace-admissible tree -/

/-- **THE TREE SUM OF A CHART POINT IS POSITIVE.** -/
theorem kFourMassTreeSum_pos_of_chartPoint (point : DirectionChartPoint 6) :
    0 < kFourMassTreeSum point.mass := by
  have h0 := point.mass_pos 0
  have h1 := point.mass_pos 1
  have h2 := point.mass_pos 2
  have h3 := point.mass_pos 3
  have h4 := point.mass_pos 4
  have h5 := point.mass_pos 5
  simp only [kFourMassTreeSum]
  positivity

/-- **THE FLOOR BEATS THE DEMAND SIXTEEN TIMES OVER.**  At every chart point
some listed spanning tree collects more than three times the tree sum in
weighted shares.  The tangent floor gives nine times the tree sum over the six
edges, the incidence law spreads it as eight copies over the sixteen trees,
and sixteen trees at three times the tree sum each cannot hold that. -/
theorem exists_kFourSpanningTree_weightedShare_gt (point : DirectionChartPoint 6) :
    ∃ tree ∈ kFourSpanningTreeList,
      3 * kFourMassTreeSum point.mass
        < ∑ label ∈ tree, point.mass label
            * kFourContractionTreePolynomial point.mass label
            / point.weight label := by
  by_contra hcon
  push_neg at hcon
  have hfloor := kFourWeightedShareFloor point.mass point.weight
    (fun label => (point.mass_pos label).le) point.weight_pos point.weight_sum_one
  have hincidence := kFourSpanningTreeList_incidence
    (fun label => point.mass label
      * kFourContractionTreePolynomial point.mass label / point.weight label)
  simp only [kFourSpanningTreeList, List.map_cons, List.map_nil, List.sum_cons,
    List.sum_nil] at hincidence
  have hpos := kFourMassTreeSum_pos_of_chartPoint point
  have b0 := hcon {0, 1, 3} (by decide)
  have b1 := hcon {0, 2, 4} (by decide)
  have b2 := hcon {1, 2, 5} (by decide)
  have b3 := hcon {3, 4, 5} (by decide)
  have b4 := hcon {0, 1, 4} (by decide)
  have b5 := hcon {0, 1, 5} (by decide)
  have b6 := hcon {0, 2, 3} (by decide)
  have b7 := hcon {0, 2, 5} (by decide)
  have b8 := hcon {0, 3, 5} (by decide)
  have b9 := hcon {0, 4, 5} (by decide)
  have b10 := hcon {1, 2, 3} (by decide)
  have b11 := hcon {1, 2, 4} (by decide)
  have b12 := hcon {1, 3, 4} (by decide)
  have b13 := hcon {1, 4, 5} (by decide)
  have b14 := hcon {2, 3, 4} (by decide)
  have b15 := hcon {2, 3, 5} (by decide)
  linarith [hfloor, hincidence, hpos, b0, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    b10, b11, b12, b13, b14, b15]

/-- **THE TRACE EXCLUSION NEVER BLOCKS ALL SIXTEEN TREES.**  At every `K4`
chart point some listed spanning tree has a strictly positive first gap
invariant.  The statement carries NO hypothesis at all. -/
theorem exists_kFourSpanningTree_gapInvariantOne_pos
    (point : DirectionChartPoint 6) :
    ∃ tree ∈ kFourSpanningTreeList,
      0 < kFourGapInvariantOne point.mass point.weight tree := by
  obtain ⟨tree, hmem, hgt⟩ := exists_kFourSpanningTree_weightedShare_gt point
  refine ⟨tree, hmem, ?_⟩
  rw [kFourGapInvariantOne_eq_weightedShareDefect point tree]
  linarith

/-- The same law in forest form: some listed tree makes the FIRST of the three
spanning-forest sums strictly positive, with no hypothesis. -/
theorem exists_kFourSpanningTree_firstForestSum_pos
    (point : DirectionChartPoint 6) :
    ∃ tree ∈ kFourSpanningTreeList,
      0 < ∑ label, signedGapWeight point.mass point.weight tree label
          * kFourContractionTreePolynomial point.mass label := by
  obtain ⟨tree, hmem, hpos⟩ := exists_kFourSpanningTree_gapInvariantOne_pos point
  refine ⟨tree, hmem, ?_⟩
  rwa [kFourGapInvariantOne_eq_forestSum point.mass point.weight
    (fun label _ => (point.weight_pos label).ne')] at hpos

/-- **THE FIRST EXCLUSION LAW IS NEVER TOTAL.**  No chart point makes the trace
exclusion refuse every listed spanning tree. -/
theorem not_forall_kFourSpanningTree_gapInvariantOne_nonpos
    (point : DirectionChartPoint 6) :
    ¬ ∀ tree ∈ kFourSpanningTreeList,
        kFourGapInvariantOne point.mass point.weight tree ≤ 0 := by
  intro hall
  obtain ⟨tree, hmem, hpos⟩ := exists_kFourSpanningTree_gapInvariantOne_pos point
  exact absurd (hall tree hmem) (not_le.mpr hpos)

/-- **THE LAW HAS AN INHABITED ANTECEDENT.**  The pencil refuter point is a
chart point, so the trace floor is not a door that never opens. -/
theorem exists_kFourSpanningTree_gapInvariantOne_pos_at_pencilCellRefuter :
    ∃ tree ∈ kFourSpanningTreeList,
      0 < kFourGapInvariantOne pencilCellRefuterPoint.mass
        pencilCellRefuterPoint.weight tree :=
  exists_kFourSpanningTree_gapInvariantOne_pos pencilCellRefuterPoint

/-! ## 4b. The complementary pair law, a sharper form of the floor -/

/-- **THE COMPLEMENTARY PAIR LAW.**  A selection and its complement split the
six weighted shares between them, so their two trace exclusions add to at least
three times the tree sum.  The statement holds for EVERY subset of the six
labels, and it needs no membership in the tree list. -/
theorem kFourGapInvariantOne_add_compl_floor (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) :
    3 * kFourMassTreeSum point.mass
      ≤ kFourGapInvariantOne point.mass point.weight tree
        + kFourGapInvariantOne point.mass point.weight treeᶜ := by
  rw [kFourGapInvariantOne_eq_weightedShareDefect point tree,
    kFourGapInvariantOne_eq_weightedShareDefect point treeᶜ]
  have hfloor := kFourWeightedShareFloor point.mass point.weight
    (fun label => (point.mass_pos label).le) point.weight_pos point.weight_sum_one
  have hsplit := Finset.sum_add_sum_compl tree
    (fun label => point.mass label
      * kFourContractionTreePolynomial point.mass label / point.weight label)
  linarith

/-- **ONE OF EACH COMPLEMENTARY PAIR IS TRACE ADMISSIBLE.**  This localises the
floor: no pair of complementary selections can both fail the trace exclusion,
at any chart point, with no hypothesis. -/
theorem kFourGapInvariantOne_pos_or_compl_pos (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) :
    0 < kFourGapInvariantOne point.mass point.weight tree
      ∨ 0 < kFourGapInvariantOne point.mass point.weight treeᶜ := by
  by_contra hcon
  push_neg at hcon
  have hpair := kFourGapInvariantOne_add_compl_floor point tree
  have hpos := kFourMassTreeSum_pos_of_chartPoint point
  linarith [hcon.1, hcon.2]

/-- **THE TWO NAMED PATHS.**  The path `{0, 1, 4}` and the path `{2, 3, 5}` are
complementary, and both are listed spanning trees.  At every chart point one of
these TWO is trace admissible.  No search over sixteen trees is left. -/
theorem kFourGapInvariantOne_pos_zeroOneFour_or_twoThreeFive
    (point : DirectionChartPoint 6) :
    0 < kFourGapInvariantOne point.mass point.weight {0, 1, 4}
      ∨ 0 < kFourGapInvariantOne point.mass point.weight {2, 3, 5} := by
  have hcompl : (({0, 1, 4} : Finset (Fin 6)))ᶜ = ({2, 3, 5} : Finset (Fin 6)) := by
    decide
  have hpair := kFourGapInvariantOne_pos_or_compl_pos point ({0, 1, 4} : Finset (Fin 6))
  rwa [hcompl] at hpair

/-! ## 5. The deflation producer meets the Kirchhoff sign tower -/

/-- **THE PRODUCED TREE READS ITS DOMINATION AS ONE POLYNOMIAL SIGN.**  At
every chart point and every label the deflation returns a listed spanning tree
that avoids the label and carries the chart deflated bound, and the strict
domination of that tree IS the positivity of the sixteen-term signed tree sum.
No matrix, no determinant, no whitener and no square root survive. -/
theorem kFour_exists_deflatedTree_posDef_iff_massTreeSum
    (point : DirectionChartPoint 6) (dropLabel : Fin 6) :
    ∃ tree ∈ kFourSpanningTreeList, dropLabel ∉ tree ∧
      ChartDeflatedGapBound kFourDirection point.mass point.weight dropLabel tree ∧
      ((directionChartGap kFourDirection point.mass point.weight tree).PosDef
        ↔ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)) := by
  obtain ⟨tree, hmem, hnotMem, hbound, hiff⟩ :=
    kFour_exists_chartDeflatedTree point dropLabel
  refine ⟨tree, hmem, hnotMem, hbound, ?_⟩
  rw [hiff, det_directionChartGap_eq_kFourMassTreeSum point.mass point.weight tree
    (fun label _ => (point.weight_pos label).ne')]

/-- **THE FOREST TRIPLE COLLAPSES AT A PRODUCED TREE.**  The complete forest
criterion asks three spanning-forest sums of a listed tree.  At a tree that the
deflation produces the third sum alone decides, because the deflated bound pays
for the two mixed sums.  This is the exact gain of the deflation over a general
listed tree. -/
theorem kFour_exists_deflatedTree_forestTriple_iff_massTreeSum
    (point : DirectionChartPoint 6) (dropLabel : Fin 6) :
    ∃ tree ∈ kFourSpanningTreeList, dropLabel ∉ tree ∧
      ChartDeflatedGapBound kFourDirection point.mass point.weight dropLabel tree ∧
      ((0 < ∑ label, signedGapWeight point.mass point.weight tree label
              * kFourContractionTreePolynomial point.mass label
          ∧ 0 < ∑ label, point.mass label
              * kFourContractionTreePolynomial
                  (signedGapWeight point.mass point.weight tree) label
          ∧ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree))
        ↔ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)) := by
  obtain ⟨tree, hmem, hnotMem, hbound, hiff⟩ :=
    kFour_exists_deflatedTree_posDef_iff_massTreeSum point dropLabel
  refine ⟨tree, hmem, hnotMem, hbound, ?_⟩
  rw [← posDef_directionChartGap_iff_forestTriple point tree]
  exact hiff

/-- **THE TWO MIXED FOREST SUMS ARE FREE AT A PRODUCED TREE.**  One sign of the
signed tree sum carries the whole forest triple. -/
theorem kFour_exists_deflatedTree_forestTriple_of_massTreeSum
    (point : DirectionChartPoint 6) (dropLabel : Fin 6) :
    ∃ tree ∈ kFourSpanningTreeList, dropLabel ∉ tree ∧
      (0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree) →
        0 < ∑ label, signedGapWeight point.mass point.weight tree label
              * kFourContractionTreePolynomial point.mass label
          ∧ 0 < ∑ label, point.mass label
              * kFourContractionTreePolynomial
                  (signedGapWeight point.mass point.weight tree) label
          ∧ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)) := by
  obtain ⟨tree, hmem, hnotMem, _, hiff⟩ :=
    kFour_exists_deflatedTree_forestTriple_iff_massTreeSum point dropLabel
  exact ⟨tree, hmem, hnotMem, hiff.mpr⟩

/-- **THE COLLAPSE HAS AN INHABITED ANTECEDENT.** -/
theorem kFour_deflatedTree_collapse_at_pencilCellRefuter :
    ∃ tree ∈ kFourSpanningTreeList, (0 : Fin 6) ∉ tree ∧
      ChartDeflatedGapBound kFourDirection pencilCellRefuterPoint.mass
        pencilCellRefuterPoint.weight 0 tree ∧
      ((directionChartGap kFourDirection pencilCellRefuterPoint.mass
          pencilCellRefuterPoint.weight tree).PosDef
        ↔ 0 < kFourMassTreeSum (signedGapWeight pencilCellRefuterPoint.mass
            pencilCellRefuterPoint.weight tree)) :=
  kFour_exists_deflatedTree_posDef_iff_massTreeSum pencilCellRefuterPoint 0

/-! ## 6. The two residual totals -/

/-- **THE RESIDUAL AFTER THE TRACE FLOOR.**  The first conjunct is the test that
`Gtz.exists_kFourSpanningTree_gapInvariantOne_pos` proves satisfiable at every
chart point with no hypothesis.  The residual is the other two tests on that
admitted set.  This proposition IS equivalent to
`Gtz.KFourUniversalStrictTree`, and the equivalence is stated as
`Gtz.kFourUniversalStrictTree_iff_adjugateAndDetTotal`.  The value of this
section is the unconditional law above, and never this name. -/
def KFourAdjugateAndDetTotal : Prop :=
  ∀ point : DirectionChartPoint 6, ∃ tree ∈ kFourSpanningTreeList,
    0 < kFourGapInvariantOne point.mass point.weight tree
      ∧ 0 < kFourGapInvariantTwo point.mass point.weight tree
      ∧ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)

/-- **THE RESIDUAL IS AN EQUIVALENCE, AND THIS THEOREM SAYS SO.**  A hunt
cannot refute the residual without refuting the chart obligation. -/
theorem kFourUniversalStrictTree_iff_adjugateAndDetTotal :
    KFourUniversalStrictTree ↔ KFourAdjugateAndDetTotal := by
  constructor
  · intro hstrict point
    obtain ⟨tree, hmem, hpd⟩ := hstrict point
    refine ⟨tree, hmem, kFourGapInvariantOne_pos_of_posDef point tree hpd,
      kFourGapInvariantTwo_pos_of_posDef point tree hpd, ?_⟩
    rw [← det_directionChartGap_eq_kFourMassTreeSum point.mass point.weight tree
      (fun label _ => (point.weight_pos label).ne')]
    exact hpd.det_pos
  · intro htotal point
    obtain ⟨tree, hmem, hone, htwo, hdet⟩ := htotal point
    refine ⟨tree, hmem, posDef_directionChartGap_of_invariantTriple point tree hone htwo ?_⟩
    rw [det_directionChartGap_eq_kFourMassTreeSum point.mass point.weight tree
      (fun label _ => (point.weight_pos label).ne')]
    exact hdet

/-- **THE ONE-SCALAR TOTAL.**  At every chart point some label makes every tree
that the deflation can produce from it carry a positive signed tree sum.  This
is the whole `K4` chart demand as ONE polynomial sign for each point. -/
def KFourDeflatedMassTreeSumTotal : Prop :=
  ∀ point : DirectionChartPoint 6, ∃ dropLabel : Fin 6,
    ∀ tree ∈ kFourSpanningTreeList, dropLabel ∉ tree →
      ChartDeflatedGapBound kFourDirection point.mass point.weight dropLabel tree →
      0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)

/-- **THE ONE-SCALAR TOTAL FEEDS THE UNFED PAIR.**  The implication runs one
way only.  The total demands a sign at a PRODUCED tree, and the universal
strict tree accepts ANY listed tree, so the total is the stronger side. -/
theorem kFourUniversalStrictTree_of_deflatedMassTreeSumTotal
    (htotal : KFourDeflatedMassTreeSumTotal) : KFourUniversalStrictTree := by
  intro point
  obtain ⟨dropLabel, hdrop⟩ := htotal point
  obtain ⟨tree, hmem, hnotMem, hbound, hiff⟩ :=
    kFour_exists_deflatedTree_posDef_iff_massTreeSum point dropLabel
  exact ⟨tree, hmem, hiff.mpr (hdrop tree hmem hnotMem hbound)⟩

/-- The one-scalar total reaches the residual of section 4. -/
theorem kFourAdjugateAndDetTotal_of_deflatedMassTreeSumTotal
    (htotal : KFourDeflatedMassTreeSumTotal) : KFourAdjugateAndDetTotal :=
  kFourUniversalStrictTree_iff_adjugateAndDetTotal.mp
    (kFourUniversalStrictTree_of_deflatedMassTreeSumTotal htotal)

/-! ## 7. Every registered consumer of the strict tree -/

/-- The universal strict tree IS strict-tree coverage of the `K4` chart. -/
theorem kFourEveryPointHasStrictTree_of_universalStrictTree
    (hstrict : KFourUniversalStrictTree) : KFourEveryPointHasStrictTree :=
  fun point => hstrict point

/-- The universal strict tree gives the design-side family selection. -/
theorem kFourFamilySelection_of_universalStrictTree
    (hstrict : KFourUniversalStrictTree) : KFourFamilySelection :=
  kFourFamilySelection_of_everyPointHasStrictTree
    (kFourEveryPointHasStrictTree_of_universalStrictTree hstrict)

/-- The universal strict tree gives the unrefined knife band. -/
theorem kFourKnifeBandRefinedWeakToStrict_of_universalStrictTree
    (hstrict : KFourUniversalStrictTree) : KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_everyPointHasStrictTree
    (kFourEveryPointHasStrictTree_of_universalStrictTree hstrict)

/-- **THE FOUR REGISTERED CONSUMERS OF THE `K4` STRICT TREE.**  One hypothesis
closes the registered `A3` formula, the registered chart obligation, the
design-side family selection and the unrefined knife band. -/
theorem kFourStrictTree_closes_all (hstrict : KFourUniversalStrictTree) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict
      ∧ DirectionChartIsTieFree kFourDirection
      ∧ KFourFamilySelection
      ∧ KFourKnifeBandRefinedWeakToStrict :=
  ⟨kFourKnifeBandRefinedAllMaxHeavyWall_of_universalStrictTree hstrict,
    directionChartIsTieFree_kFour_of_universalStrictTree hstrict,
    kFourFamilySelection_of_universalStrictTree hstrict,
    kFourKnifeBandRefinedWeakToStrict_of_universalStrictTree hstrict⟩

/-- **THE ONE-SCALAR TOTAL CLOSES ALL FOUR.**  This is the first outward
consumer of `Gtz/Wave/KirchhoffSignTower.lean`. -/
theorem kFourDeflatedMassTreeSumTotal_closes_all
    (htotal : KFourDeflatedMassTreeSumTotal) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict
      ∧ DirectionChartIsTieFree kFourDirection
      ∧ KFourFamilySelection
      ∧ KFourKnifeBandRefinedWeakToStrict :=
  kFourStrictTree_closes_all
    (kFourUniversalStrictTree_of_deflatedMassTreeSumTotal htotal)

/-- **THE RESIDUAL OF SECTION 4 CLOSES ALL FOUR.** -/
theorem kFourAdjugateAndDetTotal_closes_all (htotal : KFourAdjugateAndDetTotal) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict
      ∧ DirectionChartIsTieFree kFourDirection
      ∧ KFourFamilySelection
      ∧ KFourKnifeBandRefinedWeakToStrict :=
  kFourStrictTree_closes_all
    (kFourUniversalStrictTree_iff_adjugateAndDetTotal.mpr htotal)

/-- The forest triple total closes all four, through the landed equivalence. -/
theorem kFourForestTripleTotal_closes_all (htotal : KFourForestTripleTotal) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict
      ∧ DirectionChartIsTieFree kFourDirection
      ∧ KFourFamilySelection
      ∧ KFourKnifeBandRefinedWeakToStrict :=
  kFourStrictTree_closes_all
    (kFourUniversalStrictTree_iff_forestTripleTotal.mpr htotal)

/-! ## 8. The two unfed walls, named as one object -/

/-- **THE EXACT REMAINING GAP OF THE TWO-WALL ROUTE.**  The star wall law and
the pivot wall law together discharge the registered `A3` proposition through
`Gtz.kFourKnifeBandRefinedAllMaxHeavy_of_bothWallsAtlasFire`.  Neither of the
two carries a producer anywhere in the tree.  This object names the pair, so
one search target replaces two. -/
def KFourBothWallAtlasFires : Prop :=
  KFourStarWallAtlasFires ∧ KFourPivotWallAtlasFires

/-- The paired walls discharge the registered `A3` proposition.  The pair is
the stronger side, because it fixes the atlas at every wall inhabitant and the
registered proposition asks only for a strictly dominating tree. -/
theorem kFourKnifeBandRefinedAllMaxHeavy_of_bothWallAtlasFires
    (hwalls : KFourBothWallAtlasFires) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  kFourKnifeBandRefinedAllMaxHeavy_of_bothWallsAtlasFire hwalls.1 hwalls.2

/-- The paired walls also produce the design-side family selection. -/
theorem kFourFamilySelection_of_bothWallAtlasFires
    (hwalls : KFourBothWallAtlasFires) : KFourFamilySelection :=
  kFourFamilySelection_of_bothWallsAtlasFire hwalls.1 hwalls.2

/-- The paired walls close the registered `A3` proposition, the chart
obligation, the family selection and the unrefined knife band. -/
theorem kFourBothWallAtlasFires_closes_all (hwalls : KFourBothWallAtlasFires) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict
      ∧ DirectionChartIsTieFree kFourDirection
      ∧ KFourFamilySelection
      ∧ KFourKnifeBandRefinedWeakToStrict :=
  kFourStrictTree_closes_all
    (kFourFamilySelection_iff_everyPointHasStrictTree.mp
      (kFourFamilySelection_of_bothWallAtlasFires hwalls))

/-! ## 9. The frontier of the knife band -/

/-- **THE FRONTIER.**  Three live routes reach the registered `A3` proposition:
the paired atlas walls, the one-scalar deflated total, and the residual of the
trace floor.  Each side is sufficient, and no side carries a producer. -/
def KFourKnifeBandFrontier : Prop :=
  KFourBothWallAtlasFires ∨ KFourDeflatedMassTreeSumTotal ∨ KFourAdjugateAndDetTotal

/-- **EVERY SIDE OF THE FRONTIER CLOSES ALL FOUR CONSUMERS.**  The registered
proposition is the weaker side of each implication, so this theorem is not an
equivalence. -/
theorem kFourKnifeBandFrontier_closes_all (hfrontier : KFourKnifeBandFrontier) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict
      ∧ DirectionChartIsTieFree kFourDirection
      ∧ KFourFamilySelection
      ∧ KFourKnifeBandRefinedWeakToStrict := by
  rcases hfrontier with hwalls | htotal | hresidual
  · exact kFourBothWallAtlasFires_closes_all hwalls
  · exact kFourDeflatedMassTreeSumTotal_closes_all htotal
  · exact kFourAdjugateAndDetTotal_closes_all hresidual

/-- The frontier from the paired walls. -/
theorem kFourKnifeBandFrontier_of_bothWallAtlasFires
    (hwalls : KFourBothWallAtlasFires) : KFourKnifeBandFrontier :=
  Or.inl hwalls

/-- The frontier from the one-scalar total. -/
theorem kFourKnifeBandFrontier_of_deflatedMassTreeSumTotal
    (htotal : KFourDeflatedMassTreeSumTotal) : KFourKnifeBandFrontier :=
  Or.inr (Or.inl htotal)

/-- The frontier from the residual of the trace floor. -/
theorem kFourKnifeBandFrontier_of_adjugateAndDetTotal
    (htotal : KFourAdjugateAndDetTotal) : KFourKnifeBandFrontier :=
  Or.inr (Or.inr htotal)

/-! ## 10. The trace floor does NOT select a dominating tree

Section 1 proves that some listed tree always passes the trace exclusion.  A
reader can then ask for the obvious selection rule: take a tree that the trace
exclusion admits, or take the tree that maximises the trace exclusion, and
declare it strictly dominating.  BOTH rules are false, and this section refutes
each of them at one exact rational chart point.

The refuter carries masses `(1, 1, 2, 1, 2, 1)` and weights
`(1/8, 1/8, 1/8, 1/8, 3/8, 1/8)`.  Its six weighted shares are
`(120, 128, 176, 128, 176/3, 112)` and its tree sum is `35`.  The tree
`{1, 2, 3}` collects `432`, which is the unique maximum over the sixteen listed
trees, so its trace exclusion is `432 - 105 = 327`.  Its gap determinant is
`-51`, so the tree does not dominate.  An unsatisfiable rule must not be left
standing as an asset. -/

/-- Masses of the point that refutes the two trace selection rules. -/
noncomputable def traceRefuterMass : Fin 6 → ℝ
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 1
  | 4 => 2
  | 5 => 1

/-- Weights of the point that refutes the two trace selection rules. -/
noncomputable def traceRefuterWeight : Fin 6 → ℝ
  | 0 => 1 / 8
  | 1 => 1 / 8
  | 2 => 1 / 8
  | 3 => 1 / 8
  | 4 => 3 / 8
  | 5 => 1 / 8

/-- The refuter is a genuine chart point. -/
noncomputable def traceRefuterPoint : DirectionChartPoint 6 where
  mass := traceRefuterMass
  weight := traceRefuterWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [traceRefuterMass]
  weight_pos := by intro label; fin_cases label <;> norm_num [traceRefuterWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [traceRefuterWeight]

/-- The trace exclusion of the tree `{1, 2, 3}` at the refuter. -/
theorem traceRefuterPoint_gapInvariantOne_oneTwoThree :
    kFourGapInvariantOne traceRefuterPoint.mass traceRefuterPoint.weight
      ({1, 2, 3} : Finset (Fin 6)) = 327 := by
  rw [kFourGapInvariantOne_eq_weightedShareDefect traceRefuterPoint
      ({1, 2, 3} : Finset (Fin 6)),
    sum_triple_fin_six _ 1 2 3 (by decide) (by decide) (by decide)]
  norm_num [traceRefuterPoint, traceRefuterMass, traceRefuterWeight,
    kFourContractionTreePolynomial_one, kFourContractionTreePolynomial_two,
    kFourContractionTreePolynomial_three, kFourMassTreeSum]

/-- The gap determinant of the tree `{1, 2, 3}` at the refuter, as the signed
sixteen-term tree sum. -/
theorem traceRefuterPoint_massTreeSum_oneTwoThree :
    kFourMassTreeSum (signedGapWeight traceRefuterPoint.mass
      traceRefuterPoint.weight ({1, 2, 3} : Finset (Fin 6))) = -51 := by
  norm_num [kFourMassTreeSum, signedGapWeight, traceRefuterPoint, traceRefuterMass,
    traceRefuterWeight, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

/-- The tree `{1, 2, 3}` does not dominate at the refuter. -/
theorem traceRefuterPoint_not_posDef_oneTwoThree :
    ¬ (directionChartGap kFourDirection traceRefuterPoint.mass
        traceRefuterPoint.weight ({1, 2, 3} : Finset (Fin 6))).PosDef := by
  intro hposDef
  have hdet := hposDef.det_pos
  rw [det_directionChartGap_eq_kFourMassTreeSum traceRefuterPoint.mass
      traceRefuterPoint.weight ({1, 2, 3} : Finset (Fin 6))
      (fun label _ => (traceRefuterPoint.weight_pos label).ne'),
    traceRefuterPoint_massTreeSum_oneTwoThree] at hdet
  norm_num at hdet

/-- **THE TREE `{1, 2, 3}` MAXIMISES THE TRACE EXCLUSION AT THE REFUTER.**  All
sixteen listed trees are read, and none passes `327`. -/
theorem traceRefuterPoint_oneTwoThree_maximal (other : Finset (Fin 6))
    (hother : other ∈ kFourSpanningTreeList) :
    kFourGapInvariantOne traceRefuterPoint.mass traceRefuterPoint.weight other
      ≤ kFourGapInvariantOne traceRefuterPoint.mass traceRefuterPoint.weight
          ({1, 2, 3} : Finset (Fin 6)) := by
  have triple := sum_triple_fin_six (fun label => traceRefuterPoint.mass label
    * kFourContractionTreePolynomial traceRefuterPoint.mass label
    / traceRefuterPoint.weight label)
  rw [traceRefuterPoint_gapInvariantOne_oneTwoThree,
    kFourGapInvariantOne_eq_weightedShareDefect traceRefuterPoint other]
  simp only [kFourSpanningTreeList, List.mem_cons, List.not_mem_nil, or_false] at hother
  rcases hother with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [triple 0 1 3 (by decide) (by decide) (by decide),
      triple 0 2 4 (by decide) (by decide) (by decide),
      triple 1 2 5 (by decide) (by decide) (by decide),
      triple 3 4 5 (by decide) (by decide) (by decide),
      triple 0 1 4 (by decide) (by decide) (by decide),
      triple 0 1 5 (by decide) (by decide) (by decide),
      triple 0 2 3 (by decide) (by decide) (by decide),
      triple 0 2 5 (by decide) (by decide) (by decide),
      triple 0 3 5 (by decide) (by decide) (by decide),
      triple 0 4 5 (by decide) (by decide) (by decide),
      triple 1 2 3 (by decide) (by decide) (by decide),
      triple 1 2 4 (by decide) (by decide) (by decide),
      triple 1 3 4 (by decide) (by decide) (by decide),
      triple 1 4 5 (by decide) (by decide) (by decide),
      triple 2 3 4 (by decide) (by decide) (by decide),
      triple 2 3 5 (by decide) (by decide) (by decide)] <;>
    norm_num [traceRefuterPoint, traceRefuterMass, traceRefuterWeight,
      kFourContractionTreePolynomial_zero, kFourContractionTreePolynomial_one,
      kFourContractionTreePolynomial_two, kFourContractionTreePolynomial_three,
      kFourContractionTreePolynomial_four, kFourContractionTreePolynomial_five,
      kFourMassTreeSum]

/-- **THE FIRST FALSE RULE.**  A tree that the trace exclusion admits dominates
strictly. -/
def KFourTraceAdmissibleTreeStrict : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourSpanningTreeList →
    0 < kFourGapInvariantOne point.mass point.weight tree →
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- **THE FIRST RULE IS FALSE.**  The trace floor of section 1 admits a tree
that does not dominate, so the floor alone never closes the chart obligation. -/
theorem not_kFourTraceAdmissibleTreeStrict : ¬ KFourTraceAdmissibleTreeStrict := by
  intro hrule
  refine traceRefuterPoint_not_posDef_oneTwoThree
    (hrule traceRefuterPoint ({1, 2, 3} : Finset (Fin 6)) (by decide) ?_)
  rw [traceRefuterPoint_gapInvariantOne_oneTwoThree]
  norm_num

/-- **THE SECOND FALSE RULE.**  The tree that maximises the trace exclusion
dominates strictly. -/
def KFourTraceMaximalTreeStrict : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourSpanningTreeList →
    (∀ other ∈ kFourSpanningTreeList,
      kFourGapInvariantOne point.mass point.weight other
        ≤ kFourGapInvariantOne point.mass point.weight tree) →
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- **THE SECOND RULE IS FALSE.**  At the refuter the tree `{1, 2, 3}` is the
unique maximiser of the trace exclusion, and its gap determinant is `-51`. -/
theorem not_kFourTraceMaximalTreeStrict : ¬ KFourTraceMaximalTreeStrict := by
  intro hrule
  exact traceRefuterPoint_not_posDef_oneTwoThree
    (hrule traceRefuterPoint ({1, 2, 3} : Finset (Fin 6)) (by decide)
      traceRefuterPoint_oneTwoThree_maximal)

/-- **THE CHART OBLIGATION IS INTACT AT THE REFUTER.**  The refutation is about
the two SELECTION RULES and never about the chart obligation, because the trace
floor still admits a tree there. -/
theorem traceRefuterPoint_hasTraceAdmissibleTree :
    ∃ tree ∈ kFourSpanningTreeList,
      0 < kFourGapInvariantOne traceRefuterPoint.mass traceRefuterPoint.weight tree :=
  exists_kFourSpanningTree_gapInvariantOne_pos traceRefuterPoint

/-! ## 11. The Schur collapse, with no deflated bound

`Gtz.kFourContractionHasWinner` is unconditional and had ZERO consumers.  At
every chart point it returns a spanning tree through edge `5` whose leading
two-by-two gap block is positive definite.  That block is the first TWO leading
minors, and `Gtz.det_directionChartGap_eq_kFourMassTreeSum` reads the third one
as the signed sixteen-term tree sum.  `Gtz.sylvesterLift` joins them.

The outcome is a collapse that costs NOTHING: at a tree whose block is
admissible, strict domination IS one polynomial sign.  Section 5 reaches the
same collapse through the deflated bound, and this section reaches it through
the contracted block instead.

The edge-five list carries the BLOCK and never the sign, so
`Gtz.KFourBlockAdmissibleDetTotal` quantifies over all sixteen listed trees. -/

/-- A symmetric three-by-three matrix in its own upper entries. -/
theorem eta_symm_fin_three {mat : Matrix (Fin 3) (Fin 3) ℝ} (hsymm : mat.transpose = mat) :
    mat = !![mat 0 0, mat 0 1, mat 0 2;
             mat 0 1, mat 1 1, mat 1 2;
             mat 0 2, mat 1 2, mat 2 2] := by
  have hone : mat 1 0 = mat 0 1 := by
    have hentry := congrFun (congrFun hsymm 0) 1
    simpa [Matrix.transpose_apply] using hentry
  have htwo : mat 2 0 = mat 0 2 := by
    have hentry := congrFun (congrFun hsymm 0) 2
    simpa [Matrix.transpose_apply] using hentry
  have hthree : mat 2 1 = mat 1 2 := by
    have hentry := congrFun (congrFun hsymm 1) 2
    simpa [Matrix.transpose_apply] using hentry
  conv_lhs => rw [Matrix.eta_fin_three mat]
  rw [hone, htwo, hthree]

/-- The leading two-by-two block of a symmetric matrix, in its own entries. -/
theorem leadingTwoBlock_symm {mat : Matrix (Fin 3) (Fin 3) ℝ} (hsymm : mat.transpose = mat) :
    leadingTwoBlock mat = !![mat 0 0, mat 0 1; mat 0 1, mat 1 1] := by
  have hone : mat 1 0 = mat 0 1 := by
    have hentry := congrFun (congrFun hsymm 0) 1
    simpa [Matrix.transpose_apply] using hentry
  rw [leadingTwoBlock, hone]

/-- **THE SCHUR LIFT ON AN ABSTRACT SYMMETRIC MATRIX.**  A positive definite
leading block and a positive determinant give positive definiteness. -/
theorem posDef_of_leadingTwoBlock_of_det_pos {mat : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : mat.transpose = mat) (hblock : (leadingTwoBlock mat).PosDef)
    (hdet : 0 < mat.det) : mat.PosDef := by
  have heta := eta_symm_fin_three hsymm
  have hblockRw := leadingTwoBlock_symm hsymm
  rw [hblockRw] at hblock
  have hdetRw : 0 < (!![mat 0 0, mat 0 1, mat 0 2;
      mat 0 1, mat 1 1, mat 1 2;
      mat 0 2, mat 1 2, mat 2 2] : Matrix (Fin 3) (Fin 3) ℝ).det := by
    rw [← heta]
    exact hdet
  rw [heta]
  exact sylvesterLift (mat 0 0) (mat 0 1) (mat 0 2) (mat 1 1) (mat 1 2)
    (mat 2 2) hblock hdetRw

/-- The leading block of a positive definite symmetric matrix is positive
definite. -/
theorem leadingTwoBlock_posDef_of_posDef {mat : Matrix (Fin 3) (Fin 3) ℝ}
    (hsymm : mat.transpose = mat) (hposDef : mat.PosDef) : (leadingTwoBlock mat).PosDef := by
  have heta := eta_symm_fin_three hsymm
  rw [heta] at hposDef
  obtain ⟨hcorner, hminor, -⟩ :=
    (leadingMinors_pos_iff_posDef_fin_three (mat 0 0) (mat 0 1) (mat 0 2)
      (mat 1 1) (mat 1 2) (mat 2 2)).mp hposDef
  rw [leadingTwoBlock_symm hsymm]
  exact posDef_of_leadingMinors_fin_two (mat 0 0) (mat 0 1) (mat 1 1) hcorner hminor

/-- **THE SCHUR COLLAPSE.**  At a listed selection whose leading gap block is
positive definite, strict domination IS the sign of the signed sixteen-term
tree sum.  No deflated bound, no whitener and no square root occur. -/
theorem posDef_directionChartGap_iff_massTreeSum_of_leadingTwoBlock
    (point : DirectionChartPoint 6) (tree : Finset (Fin 6))
    (hblock : (leadingTwoBlock (directionChartGap kFourDirection point.mass
      point.weight tree)).PosDef) :
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef
      ↔ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree) := by
  rw [← det_directionChartGap_eq_kFourMassTreeSum point.mass point.weight tree
    (fun label _ => (point.weight_pos label).ne')]
  exact ⟨fun hposDef => hposDef.det_pos,
    fun hdet => posDef_of_leadingTwoBlock_of_det_pos
      (directionChartGap_transpose kFourDirection point.mass point.weight tree)
      hblock hdet⟩

/-- **THE COLLAPSE RUNS AT EVERY CHART POINT, WITH NO HYPOTHESIS.**  The
contracted winner supplies the block, and the collapse supplies the sign
reading.  This is the first consumer of `Gtz.kFourContractionHasWinner`. -/
theorem exists_kFourTreeThroughEdgeFive_posDef_iff_massTreeSum
    (point : DirectionChartPoint 6) :
    ∃ tree ∈ kFourTreesThroughEdgeFive,
      (leadingTwoBlock (directionChartGap kFourDirection point.mass
        point.weight tree)).PosDef
        ∧ ((directionChartGap kFourDirection point.mass point.weight tree).PosDef
          ↔ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)) := by
  obtain ⟨tree, hmem, hblock⟩ := kFourContractionHasWinner point
  exact ⟨tree, hmem, hblock,
    posDef_directionChartGap_iff_massTreeSum_of_leadingTwoBlock point tree hblock⟩

/-- **THE RESIDUAL OF THE SCHUR COLLAPSE.**  At every chart point some listed
tree carries an admissible block AND a positive signed tree sum.  This
proposition IS equivalent to `Gtz.KFourUniversalStrictTree`, and the next
theorem says so.  Its value is the SHAPE: two conditions, one of which is
unconditionally satisfiable over the eight trees through edge five. -/
def KFourBlockAdmissibleDetTotal : Prop :=
  ∀ point : DirectionChartPoint 6, ∃ tree ∈ kFourSpanningTreeList,
    (leadingTwoBlock (directionChartGap kFourDirection point.mass
      point.weight tree)).PosDef
      ∧ 0 < kFourMassTreeSum (signedGapWeight point.mass point.weight tree)

/-- **THE SCHUR RESIDUAL IS AN EQUIVALENCE, AND THIS THEOREM SAYS SO.** -/
theorem kFourUniversalStrictTree_iff_blockAdmissibleDetTotal :
    KFourUniversalStrictTree ↔ KFourBlockAdmissibleDetTotal := by
  constructor
  · intro hstrict point
    obtain ⟨tree, hmem, hposDef⟩ := hstrict point
    refine ⟨tree, hmem, leadingTwoBlock_posDef_of_posDef
      (directionChartGap_transpose kFourDirection point.mass point.weight tree)
      hposDef, ?_⟩
    rw [← det_directionChartGap_eq_kFourMassTreeSum point.mass point.weight tree
      (fun label _ => (point.weight_pos label).ne')]
    exact hposDef.det_pos
  · intro htotal point
    obtain ⟨tree, hmem, hblock, hdet⟩ := htotal point
    exact ⟨tree, hmem,
      (posDef_directionChartGap_iff_massTreeSum_of_leadingTwoBlock point tree
        hblock).mpr hdet⟩

/-- The Schur residual closes all four registered consumers. -/
theorem kFourBlockAdmissibleDetTotal_closes_all
    (htotal : KFourBlockAdmissibleDetTotal) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict
      ∧ DirectionChartIsTieFree kFourDirection
      ∧ KFourFamilySelection
      ∧ KFourKnifeBandRefinedWeakToStrict :=
  kFourStrictTree_closes_all
    (kFourUniversalStrictTree_iff_blockAdmissibleDetTotal.mpr htotal)

/-! ## 12. The block alone is not the sign -/

/-- The leading gap block of the tree `{1, 2, 3}` at the refuter. -/
theorem traceRefuterPoint_leadingTwoBlock_oneTwoThree :
    leadingTwoBlock (directionChartGap kFourDirection traceRefuterPoint.mass
        traceRefuterPoint.weight ({1, 2, 3} : Finset (Fin 6)))
      = !![(13 : ℝ), 1; 1, 11] := by
  rw [directionChartGap_eq_signedLaplacian _ _ _
    (fun label _ => (traceRefuterPoint.weight_pos label).ne')]
  ext rowIndex colIndex
  fin_cases rowIndex <;> fin_cases colIndex <;>
    norm_num [leadingTwoBlock, signedGapWeight, traceRefuterPoint, traceRefuterMass,
      traceRefuterWeight, Finset.mem_insert, Finset.mem_singleton, Fin.ext_iff]

/-- **THE BLOCK IS ADMISSIBLE AT THE REFUTER, AND THE TREE STILL FAILS.**  The
leading block of `{1, 2, 3}` has corner `13` and minor `142`, and the signed
tree sum is `-51`.  So the block condition of the Schur collapse never carries
the sign, and the residual of section 11 is genuine. -/
theorem traceRefuterPoint_leadingTwoBlock_posDef_oneTwoThree :
    (leadingTwoBlock (directionChartGap kFourDirection traceRefuterPoint.mass
      traceRefuterPoint.weight ({1, 2, 3} : Finset (Fin 6)))).PosDef := by
  rw [traceRefuterPoint_leadingTwoBlock_oneTwoThree]
  exact posDef_of_leadingMinors_fin_two 13 1 11 (by norm_num) (by norm_num)

/-- **THE THIRD FALSE RULE.**  A tree with an admissible leading block
dominates strictly. -/
def KFourBlockAdmissibleTreeStrict : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourSpanningTreeList →
    (leadingTwoBlock (directionChartGap kFourDirection point.mass
      point.weight tree)).PosDef →
    (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- **THE THIRD RULE IS FALSE.** -/
theorem not_kFourBlockAdmissibleTreeStrict : ¬ KFourBlockAdmissibleTreeStrict :=
  fun hrule => traceRefuterPoint_not_posDef_oneTwoThree
    (hrule traceRefuterPoint ({1, 2, 3} : Finset (Fin 6)) (by decide)
      traceRefuterPoint_leadingTwoBlock_posDef_oneTwoThree)

end Gtz
