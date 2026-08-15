/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.GaugeWallAtlasEquivalence
import Gtz.Design.GaugeWallKernelLaw
import Gtz.Design.CardFourStallEquivalence

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 3200000

/-!
# Descend a gauge wall through a triangle-star complement

The gauge-wall pivot sum and the generic five-stall price interact sharply.
For a triangle label `i`, erasing `i` from the full six-label gap is always
positive definite.  If that five-set stalls, its missing pivot is at least
`1 + 1 / w_i`.  The rank-one self-update then forces the full-selection pivot
at `i` to be strictly larger than `2/3`.

But the three triangle pivots sum to exactly `2` on the gauge wall.  Therefore
the three triangle erasures cannot all stall.  One of them drops a second
label.  The gauge-wall rank obstruction forbids that second label from being a
triangle, so it is a star label.  Consequently every gauge wall carries a
positive-definite card-four selection whose complement is exactly one triangle
label and one star label.

The last section packages the result as an exact residual.  The canonical
gauge wall is closed if and only if every stalled positive-definite selection
of this nine-pair form produces a strict tree.  This removes the three-triangle
card-four shapes and the arbitrary descent choice from the wall target.
-/

namespace Gtz

open Matrix

/-! ## 1. A generic five-stall threshold -/

/-- A stalled five-label erasure forces the corresponding full-selection pivot
strictly above `2/3`.

The missing pivot at the five-set is priced by `card_five_stall`.  Reinserting
the missing label sends that pivot `q` to `q / (1 + q)`.  Since every chart
weight is strictly below one, the stall price makes `q > 2`, hence the updated
pivot is above `2/3`. -/
theorem fullPivot_gt_twoThirds_of_erasedFive_stall
    (direction : Fin 6 → (Fin 3 → ℝ)) (point : DirectionChartPoint 6)
    (missing : Fin 6)
    (hpd : (directionChartGap direction point.mass point.weight
      (Finset.univ.erase missing)).PosDef)
    (hstall : ∀ label ∈ Finset.univ.erase missing,
      1 ≤ chartLadderPivot direction point.mass point.weight
        (Finset.univ.erase missing) label) :
    (2 / 3 : ℝ) < chartLadderPivot direction point.mass point.weight
      Finset.univ missing := by
  let erased := (Finset.univ : Finset (Fin 6)).erase missing
  let q := chartLadderPivot direction point.mass point.weight erased missing
  have hprice : 1 + 1 / point.weight missing ≤ q := by
    simpa [erased, q] using card_five_stall direction point hpd hstall
  have hwPos := point.weight_pos missing
  have hwLt := directionChartPoint_weight_lt_one point missing
  have hmul := mul_le_mul_of_nonneg_left hprice hwPos.le
  have hwInv : point.weight missing * (1 / point.weight missing) = 1 := by
    field_simp
  rw [mul_add, mul_one, hwInv] at hmul
  have hqGt : 2 < q := by
    by_contra hnot
    have hqLe : q ≤ 2 := le_of_not_gt hnot
    have hupper := mul_le_mul_of_nonneg_left hqLe hwPos.le
    nlinarith
  have hmissingNotMem : missing ∉ erased := by simp [erased]
  have hself := chartLadderPivot_insert_self direction point.mass point.weight
    point.mass_pos point.weight_pos erased hmissingNotMem hpd
  have hinsert : insert missing erased = (Finset.univ : Finset (Fin 6)) := by
    ext label
    simp [erased]
  rw [hinsert] at hself
  have hqNonneg := chartLadderPivot_nonneg_of_posDef direction point.mass
    point.weight point.mass_pos point.weight_pos erased hpd missing
  have hden : 0 < 1 + q := by linarith
  have hratio : (2 / 3 : ℝ) < q / (1 + q) := by
    rw [lt_div_iff₀ hden]
    nlinarith
  simpa [q] using hself.symm ▸ hratio

/-! ## 2. One triangle erasure must keep descending -/

/-- At a positive rank-one gauge wall, some triangle-label erasure is a
positive-definite five-set which is not stalled. -/
theorem kFourGaugeWall_exists_triangle_erase_nonStalled
    (point : DirectionChartPoint 6) (axis : Fin 3 → ℝ) (scale : ℝ)
    (hscale : 0 < scale)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (hne : axis ⬝ᵥ kFourAllOnes ≠ 0) :
    ∃ missing ∈ kFourTriangleLabels,
      (directionChartGap kFourDirection point.mass point.weight
        (Finset.univ.erase missing)).PosDef ∧
      ∃ dropped ∈ Finset.univ.erase missing,
        chartLadderPivot kFourDirection point.mass point.weight
          (Finset.univ.erase missing) dropped < 1 := by
  have hpd0 := kFourGaugeWall_posDef_erase_triangle point axis scale hscale hwall
    0 1 2 (by decide) (by decide) (by decide)
    (fun probe haxis h1 h2 => by
      refine kFourGaugeWall_span_of_pair axis probe hne haxis ?_ ?_
      · simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons] at h1 h2
        linarith
      · simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons] at h1 h2
        linarith)
  have hpd1 := kFourGaugeWall_posDef_erase_triangle point axis scale hscale hwall
    1 0 2 (by decide) (by decide) (by decide)
    (fun probe haxis h0 h2 => by
      refine kFourGaugeWall_span_of_pair axis probe hne haxis ?_ ?_
      · simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons] at h0 h2
        linarith
      · simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons] at h0 h2
        linarith)
  have hpd2 := kFourGaugeWall_posDef_erase_triangle point axis scale hscale hwall
    2 0 1 (by decide) (by decide) (by decide)
    (fun probe haxis h0 h1 => by
      refine kFourGaugeWall_span_of_pair axis probe hne haxis ?_ ?_
      · simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons] at h0 h1
        linarith
      · simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
          Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
          Matrix.cons_val_two, Matrix.tail_cons] at h0 h1
        linarith)
  by_contra hnone
  push Not at hnone
  have hstall0 : ∀ label ∈ (Finset.univ : Finset (Fin 6)).erase 0,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        (Finset.univ.erase 0) label := by
    intro label hlabel
    exact hnone 0 (by decide) hpd0 label hlabel
  have hstall1 : ∀ label ∈ (Finset.univ : Finset (Fin 6)).erase 1,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        (Finset.univ.erase 1) label := by
    intro label hlabel
    exact hnone 1 (by decide) hpd1 label hlabel
  have hstall2 : ∀ label ∈ (Finset.univ : Finset (Fin 6)).erase 2,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        (Finset.univ.erase 2) label := by
    intro label hlabel
    exact hnone 2 (by decide) hpd2 label hlabel
  have hp0 := fullPivot_gt_twoThirds_of_erasedFive_stall kFourDirection point 0
    hpd0 hstall0
  have hp1 := fullPivot_gt_twoThirds_of_erasedFive_stall kFourDirection point 1
    hpd1 hstall1
  have hp2 := fullPivot_gt_twoThirds_of_erasedFive_stall kFourDirection point 2
    hpd2 hstall2
  have hsum := kFourGaugeWall_triangle_pivot_sum point axis scale hwall hne
  rw [sum_kFourTriangleLabels] at hsum
  linarith

/-! ## 3. The second deletion is necessarily a star -/

/-- Every gauge wall descends to a positive-definite card-four selection whose
complement consists of one triangle label and one star label.

The pivot-sum argument supplies a non-stalled triangle erasure.  Erasing its
sub-one label gives a positive-definite four-set.  If the second erased label
were another triangle, the four-set would contain only one triangle, contrary
to the landed gauge-wall rank obstruction. -/
theorem kFourGaugeWall_exists_triangleStar_cardFour
    (point : DirectionChartPoint 6)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point
      ({3, 4, 5} : Finset (Fin 6))) :
    ∃ triangle ∈ kFourTriangleLabels, ∃ star ∈ kFourStarLabels,
      (directionChartGap kFourDirection point.mass point.weight
        ({triangle, star} : Finset (Fin 6))ᶜ).PosDef := by
  obtain ⟨axis, scale, hwall, hscale, haxis0, haxis1, haxis2⟩ :=
    kFourGaugeStarWall_positive_axis point hpsd hcorank
  have haxisSum : dotProduct axis kFourAllOnes ≠ 0 := by
    simp only [kFourAllOnes, dotProduct, Fin.sum_univ_three,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    linarith
  obtain ⟨triangle, htriangle, hpdFive, star, hstarMem, hstarPivot⟩ :=
    kFourGaugeWall_exists_triangle_erase_nonStalled point axis scale hscale
      hwall haxisSum
  have hpdFour : (directionChartGap kFourDirection point.mass point.weight
      ((Finset.univ.erase triangle).erase star)).PosDef :=
    (posDef_directionChartGap_erase_iff kFourDirection point.mass point.weight
      point.mass_pos point.weight_pos (Finset.univ.erase triangle) hstarMem
      hpdFive).mpr hstarPivot
  have hstarNotTriangle : star ∉ kFourTriangleLabels := by
    intro hstarTriangle
    have htriangleNeStar : triangle ≠ star := by
      intro heq
      subst star
      simp at hstarMem
    have htriangleCard :
        ((((Finset.univ : Finset (Fin 6)).erase triangle).erase star)
          ∩ ({0, 1, 2} : Finset (Fin 6))).card = 1 := by
      revert htriangle hstarTriangle htriangleNeStar
      fin_cases triangle <;> fin_cases star <;> decide
    have htwo := kFourGaugeWall_two_le_triangle_card_of_corank point
      ((Finset.univ.erase triangle).erase star) hcorank hpdFour
    rw [htriangleCard] at htwo
    omega
  have hstar : star ∈ kFourStarLabels := by
    revert hstarNotTriangle
    fin_cases star <;> decide
  have herase :
      ((Finset.univ : Finset (Fin 6)).erase triangle).erase star
        = ({triangle, star} : Finset (Fin 6))ᶜ := by
    ext label
    simp [eq_comm, and_comm]
  refine ⟨triangle, htriangle, star, hstar, ?_⟩
  rwa [← herase]

/-! ## 4. The exact gauge-wall residual -/

/-- The only stall shape that a canonical gauge wall still needs to close.

The selection is the complement of one triangle label and one star label.  It
is already positive definite; the proposition is asked to act only when that
four-set is stalled.  There are exactly nine such complementary pairs. -/
def KFourGaugeWallTriangleStarStallClosure : Prop :=
  ∀ (point : DirectionChartPoint 6),
    (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef →
    KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)) →
    ∀ triangle ∈ kFourTriangleLabels, ∀ star ∈ kFourStarLabels,
      (directionChartGap kFourDirection point.mass point.weight
        ({triangle, star} : Finset (Fin 6))ᶜ).PosDef →
      (∀ label ∈ ({triangle, star} : Finset (Fin 6))ᶜ,
        1 ≤ chartLadderPivot kFourDirection point.mass point.weight
          ({triangle, star} : Finset (Fin 6))ᶜ label) →
      ∃ winner ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight winner).PosDef

/-- Closing the nine triangle-star stalls closes the whole canonical gauge
wall.  The only nontrivial input before the residual is the forced descent
proved above. -/
theorem kFourGaugeStarCorankWallClosure_of_triangleStarStallClosure
    (hclose : KFourGaugeWallTriangleStarStallClosure) :
    KFourGaugeStarCorankWallClosure := by
  intro point hpsd hcorank
  obtain ⟨triangle, htriangle, star, hstar, hpd⟩ :=
    kFourGaugeWall_exists_triangleStar_cardFour point hpsd hcorank
  by_cases hstall : ∀ label ∈ ({triangle, star} : Finset (Fin 6))ᶜ,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        ({triangle, star} : Finset (Fin 6))ᶜ label
  · exact hclose point hpsd hcorank triangle htriangle star hstar hpd hstall
  · push Not at hstall
    obtain ⟨label, hlabel, hpivot⟩ := hstall
    have htriangleNeStar : triangle ≠ star := by
      intro heq
      subst star
      have : triangle ∉ kFourStarLabels := by
        revert htriangle
        fin_cases triangle <;> decide
      exact this hstar
    have hcard : (({triangle, star} : Finset (Fin 6))ᶜ).card = 4 := by
      rw [Finset.card_compl, Finset.card_pair htriangleNeStar,
        Fintype.card_fin]
    exact exists_strictTree_of_nonStalledCardFour point hcard hpd hlabel hpivot

/-- Any full proof of the canonical gauge wall supplies the shaped stall
closure by ignoring the particular stalled four-set and invoking the wall
theorem. -/
theorem kFourGaugeWallTriangleStarStallClosure_of_gaugeStarCorankWallClosure
    (hclose : KFourGaugeStarCorankWallClosure) :
    KFourGaugeWallTriangleStarStallClosure := by
  intro point hpsd hcorank _triangle _htriangle _star _hstar _hpd _hstall
  exact hclose point hpsd hcorank

/-- **THE EXACT GAUGE-WALL REDUCTION.**  Canonical gauge-wall closure is
equivalent to closing only the nine positive-definite stalled four-sets whose
complements contain one triangle and one star.

This is strictly sharper as a proof interface than the old arbitrary shaped
stall target, while remaining logically exact. -/
theorem kFourGaugeStarCorankWallClosure_iff_triangleStarStallClosure :
    KFourGaugeStarCorankWallClosure ↔
      KFourGaugeWallTriangleStarStallClosure :=
  ⟨kFourGaugeWallTriangleStarStallClosure_of_gaugeStarCorankWallClosure,
    kFourGaugeStarCorankWallClosure_of_triangleStarStallClosure⟩

end Gtz
