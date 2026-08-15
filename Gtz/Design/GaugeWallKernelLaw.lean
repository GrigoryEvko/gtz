/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.TriangleNormalReading
import Gtz.Design.StarWallVacuity
import Gtz.Design.PivotBalanceLaw
import Gtz.Design.PivotStallPropagation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The kernel law of the gauge star wall

At a gauge-star corank-two wall point the star gap is the rank-one atom of a
positive axis `z`.  The three triangle directions of the `K4` chart read zero
at the all-ones probe, so the all-ones probe is carried by the axis alone:

* `kFourGaugeWall_univ_mulVec_allOnes` — **THE KERNEL LAW.**  The full-selection
  gap sends the all-ones probe to a positive multiple of the axis.  The whole
  triangle part is blind to that probe.
* `kFourGaugeWall_axis_inv_quadForm` — the inverse reading of the axis is pinned:
  `scale * (axis ⬝ gap⁻¹ axis) = 1`, with no freedom left.
* `kFourGaugeWall_triangle_pivot_sum` — **THE TRIANGLE PIVOT SUM LAW.**  The three
  triangle labels carry full-selection pivots summing to exactly `2`.  The trace
  of the inverse against the triangle part is `3` minus the pinned axis reading.
* `kFourGaugeWall_star_deficiency_eq` — the exact companion at the star: the
  weighted star deficiency is one plus the triangle weight-deficiency sum.
* `kFourGaugeWall_two_star_pivots_lt_one` — **THE TWO-STAR LAW.**  At least two of
  the three star labels carry a full-selection pivot below one, so at least two
  of the three five-label star erasures are positive definite.

The triangle pivot sum law is the wall's own conservation statement.  Off the
wall no such identity holds, because the identity is the pinned axis reading
`scale * (axis ⬝ gap⁻¹ axis) = 1` in disguise, and that reading is pinned only
by the rank-one star gap.
-/

namespace Gtz

open Matrix

/-! ## 1. Small arithmetic of the triangle-label finset -/

/-- The triangle labels of the `K4` chart. -/
def kFourTriangleLabels : Finset (Fin 6) := {0, 1, 2}

/-- The star labels of the `K4` chart. -/
def kFourStarLabels : Finset (Fin 6) := {3, 4, 5}

theorem sum_kFourTriangleLabels (f : Fin 6 → ℝ) :
    ∑ label ∈ kFourTriangleLabels, f label = f 0 + (f 1 + f 2) := by
  rw [kFourTriangleLabels, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

theorem sum_kFourStarLabels (f : Fin 6 → ℝ) :
    ∑ label ∈ kFourStarLabels, f label = f 3 + (f 4 + f 5) := by
  rw [kFourStarLabels, Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_singleton]

/-! ## 2. The wall decomposition of the full-selection gap -/

/-- At a wall point the full-selection gap is the axis atom plus the three
triangle boosts.  The star boosts are already inside the wall atom. -/
theorem kFourGaugeWall_univ_eq (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis) :
    directionChartGap kFourDirection point.mass point.weight Finset.univ
      = scale • atomMatrix axis
        + ((point.mass 0 / point.weight 0) • atomMatrix (kFourDirection 0)
          + ((point.mass 1 / point.weight 1) • atomMatrix (kFourDirection 1)
            + (point.mass 2 / point.weight 2)
              • atomMatrix (kFourDirection 2))) := by
  have hsdiff := directionChartGap_sdiff kFourDirection point.mass point.weight
    Finset.univ ({3, 4, 5} : Finset (Fin 6))
  have hleft : (Finset.univ \ ({3, 4, 5} : Finset (Fin 6)))
      = kFourTriangleLabels := by decide
  have hright : (({3, 4, 5} : Finset (Fin 6)) \ Finset.univ) = ∅ := by decide
  rw [hleft, hright, Finset.sum_empty, sub_zero, hwall] at hsdiff
  have hsum := sum_kFourTriangleLabels (fun label =>
    (point.mass label / point.weight label)
      * (0 : ℝ))
  -- expand the matrix-valued sum over the three triangle labels
  have hexpand : (∑ label ∈ kFourTriangleLabels,
      (point.mass label / point.weight label) • atomMatrix (kFourDirection label))
      = (point.mass 0 / point.weight 0) • atomMatrix (kFourDirection 0)
        + ((point.mass 1 / point.weight 1) • atomMatrix (kFourDirection 1)
          + (point.mass 2 / point.weight 2)
            • atomMatrix (kFourDirection 2)) := by
    rw [kFourTriangleLabels, Finset.sum_insert (by decide),
      Finset.sum_insert (by decide), Finset.sum_singleton]
  rw [hexpand] at hsdiff
  linear_combination (norm := module) hsdiff

/-! ## 4. The kernel law -/

/-- **THE KERNEL LAW OF THE GAUGE WALL.**  The full-selection gap carries the
all-ones probe to a multiple of the axis.  Every triangle direction reads zero
at the all-ones probe, so only the wall atom survives. -/
theorem kFourGaugeWall_univ_mulVec_allOnes (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis) :
    directionChartGap kFourDirection point.mass point.weight Finset.univ
        *ᵥ kFourAllOnes
      = (scale * (axis ⬝ᵥ kFourAllOnes)) • axis := by
  rw [kFourGaugeWall_univ_eq point axis scale hwall]
  simp only [Matrix.add_mulVec, Matrix.smul_mulVec, atomMatrix_mulVec_eq_smul,
    kFourDirection_dot_allOnes_zero, kFourDirection_dot_allOnes_one,
    kFourDirection_dot_allOnes_two, zero_smul, smul_zero, add_zero, smul_smul]

/-- The inverse of the full-selection gap sends the axis to a multiple of the
all-ones probe. -/
theorem kFourGaugeWall_inv_mulVec_axis (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis) :
    (scale * (axis ⬝ᵥ kFourAllOnes))
        • ((directionChartGap kFourDirection point.mass point.weight
          Finset.univ)⁻¹ *ᵥ axis)
      = kFourAllOnes := by
  have hpd := posDef_directionChartGap_univ point
  have hunit : IsUnit (directionChartGap kFourDirection point.mass point.weight
      Finset.univ).det := isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  have hkey := kFourGaugeWall_univ_mulVec_allOnes point axis scale hwall
  have hback : (directionChartGap kFourDirection point.mass point.weight
      Finset.univ)⁻¹ *ᵥ (directionChartGap kFourDirection point.mass
        point.weight Finset.univ *ᵥ kFourAllOnes) = kFourAllOnes := by
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hunit,
      Matrix.one_mulVec]
  rw [hkey, Matrix.mulVec_smul] at hback
  exact hback

/-- **THE PINNED AXIS READING.**  At a wall point the scaled inverse reading of
the axis is exactly one.  No wall point has any freedom in this quantity. -/
theorem kFourGaugeWall_axis_inv_quadForm (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (hne : axis ⬝ᵥ kFourAllOnes ≠ 0) :
    scale * (axis ⬝ᵥ ((directionChartGap kFourDirection point.mass
      point.weight Finset.univ)⁻¹ *ᵥ axis)) = 1 := by
  have hkey := kFourGaugeWall_inv_mulVec_axis point axis scale hwall
  have hdot : axis ⬝ᵥ ((scale * (axis ⬝ᵥ kFourAllOnes))
      • ((directionChartGap kFourDirection point.mass point.weight
        Finset.univ)⁻¹ *ᵥ axis)) = axis ⬝ᵥ kFourAllOnes := by
    rw [hkey]
  rw [dotProduct_smul, smul_eq_mul] at hdot
  have hcancel : (axis ⬝ᵥ kFourAllOnes)
      * (scale * (axis ⬝ᵥ ((directionChartGap kFourDirection point.mass
        point.weight Finset.univ)⁻¹ *ᵥ axis)))
      = (axis ⬝ᵥ kFourAllOnes) * 1 := by
    rw [mul_one]
    linarith [hdot]
  exact mul_left_cancel₀ hne hcancel

/-! ## 5. The triangle pivot sum law -/

/-- **THE TRIANGLE PIVOT SUM LAW.**  At a gauge wall point the three triangle
labels carry full-selection pivots summing to exactly two.

The trace of the inverse gap against the triangle part of the gap is the rank
minus the pinned axis reading, and the axis reading is pinned at one. -/
theorem kFourGaugeWall_triangle_pivot_sum (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (hne : axis ⬝ᵥ kFourAllOnes ≠ 0) :
    ∑ label ∈ kFourTriangleLabels,
        chartLadderPivot kFourDirection point.mass point.weight
          Finset.univ label = 2 := by
  set gapU := directionChartGap kFourDirection point.mass point.weight
    Finset.univ with hgapU
  have hpd := posDef_directionChartGap_univ point
  have hunit : IsUnit gapU.det := isUnit_iff_ne_zero.mpr (ne_of_gt hpd.det_pos)
  -- each pivot is a trace against the corresponding boost atom
  have hterm : ∀ label : Fin 6,
      chartLadderPivot kFourDirection point.mass point.weight Finset.univ label
        = Matrix.trace (gapU⁻¹
            * ((point.mass label / point.weight label)
              • atomMatrix (kFourDirection label))) := by
    intro label
    rw [chartLadderPivot, Matrix.mul_smul, Matrix.trace_smul,
      trace_mul_atomMatrix, smul_eq_mul, hgapU]
  rw [sum_kFourTriangleLabels, hterm 0, hterm 1, hterm 2]
  rw [← Matrix.trace_add, ← Matrix.trace_add, ← Matrix.mul_add, ← Matrix.mul_add]
  have hdecomp := kFourGaugeWall_univ_eq point axis scale hwall
  have htri : ((point.mass 0 / point.weight 0) • atomMatrix (kFourDirection 0)
      + ((point.mass 1 / point.weight 1) • atomMatrix (kFourDirection 1)
        + (point.mass 2 / point.weight 2) • atomMatrix (kFourDirection 2)))
      = gapU - scale • atomMatrix axis := by
    rw [hgapU, hdecomp]; abel
  rw [htri, Matrix.mul_sub, Matrix.trace_sub, Matrix.nonsing_inv_mul _ hunit,
    Matrix.mul_smul, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul]
  have haxis := kFourGaugeWall_axis_inv_quadForm point axis scale hwall hne
  rw [← hgapU] at haxis
  have hone : Matrix.trace (1 : Matrix (Fin 3) (Fin 3) ℝ) = 3 := by
    simp [Matrix.trace_one]
  rw [hone]
  linarith [haxis]

/-- The triangle deficiencies sum to exactly one. -/
theorem kFourGaugeWall_triangle_deficiency_sum (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (hne : axis ⬝ᵥ kFourAllOnes ≠ 0) :
    ∑ label ∈ kFourTriangleLabels,
        (1 - chartLadderPivot kFourDirection point.mass point.weight
          Finset.univ label) = 1 := by
  have hsum := kFourGaugeWall_triangle_pivot_sum point axis scale hwall hne
  rw [sum_kFourTriangleLabels] at hsum ⊢
  linarith

/-! ## 6. Every triangle erasure stays positive definite -/

/-- Three positively scaled atoms whose common orthogonal is trivial give a
positive definite sum. -/
theorem posDef_three_atoms {first second third : Fin 3 → ℝ}
    {alpha beta gamma : ℝ} (halpha : 0 < alpha) (hbeta : 0 < beta)
    (hgamma : 0 < gamma)
    (hspan : ∀ probe : Fin 3 → ℝ, first ⬝ᵥ probe = 0 → second ⬝ᵥ probe = 0 →
      third ⬝ᵥ probe = 0 → probe = 0) :
    (alpha • atomMatrix first
      + (beta • atomMatrix second + gamma • atomMatrix third)).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_of_transpose_eq ?_,
    fun probe hne => ?_⟩
  · simp [Matrix.transpose_add, Matrix.transpose_smul, atomMatrix_transpose]
  · rw [star_trivial]
    simp only [Matrix.add_mulVec, Matrix.smul_mulVec, dotProduct_add,
      dotProduct_smul, smul_eq_mul, dotProduct_atomMatrix_mulVec]
    rcases eq_or_ne (first ⬝ᵥ probe) 0 with hf | hf
    · rcases eq_or_ne (second ⬝ᵥ probe) 0 with hs | hs
      · rcases eq_or_ne (third ⬝ᵥ probe) 0 with ht | ht
        · exact absurd (hspan probe hf hs ht) hne
        · have hp : 0 < (third ⬝ᵥ probe) ^ 2 :=
            lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 ht))
          nlinarith [sq_nonneg (first ⬝ᵥ probe), sq_nonneg (second ⬝ᵥ probe)]
      · have hp : 0 < (second ⬝ᵥ probe) ^ 2 :=
          lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hs))
        nlinarith [sq_nonneg (first ⬝ᵥ probe), sq_nonneg (third ⬝ᵥ probe)]
    · have hp : 0 < (first ⬝ᵥ probe) ^ 2 :=
        lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hf))
      nlinarith [sq_nonneg (second ⬝ᵥ probe), sq_nonneg (third ⬝ᵥ probe)]

/-- Two distinct triangle directions pin a probe to the all-ones line, and the
axis then kills it.  This is the wall's rank-three certificate. -/
theorem kFourGaugeWall_span_of_pair (axis probe : Fin 3 → ℝ)
    (hax : axis ⬝ᵥ kFourAllOnes ≠ 0) (haxis : axis ⬝ᵥ probe = 0)
    (hfirst : probe 0 = probe 2) (hsecond : probe 1 = probe 2) : probe = 0 := by
  have hrep : axis ⬝ᵥ probe = probe 2 * (axis ⬝ᵥ kFourAllOnes) := by
    simp only [dotProduct, Fin.sum_univ_three, kFourAllOnes,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
      Matrix.cons_val_two, Matrix.tail_cons]
    rw [hfirst, hsecond]; ring
  rw [hrep] at haxis
  have htwo : probe 2 = 0 := by
    rcases mul_eq_zero.mp haxis with h | h
    · exact h
    · exact absurd h hax
  funext index
  fin_cases index <;> simp [hfirst, hsecond, htwo]

/-! ## 7. The weighted balance and the star deficiency -/

/-- The full-selection weighted pivot sum is exactly the rank. -/
theorem kFourGaugeWall_univ_weighted_pivot_sum (point : DirectionChartPoint 6) :
    ∑ label, (1 - point.weight label)
        * chartLadderPivot kFourDirection point.mass point.weight
          Finset.univ label = 3 := by
  have hbal := chartCoeff_inv_balance kFourDirection point.mass point.weight
    Finset.univ (posDef_directionChartGap_univ point)
  rw [← hbal]
  refine Finset.sum_congr rfl (fun label _ => ?_)
  have hw := point.weight_pos label
  rw [chartCoeff, if_pos (Finset.mem_univ label), chartLadderPivot]
  field_simp

/-- **THE STAR DEFICIENCY IDENTITY.**  On the wall the weighted star deficiency
is one plus the triangle weight-deficiency sum.  The `1` is the triangle pivot
sum law in disguise. -/
theorem kFourGaugeWall_star_deficiency_eq (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (hne : axis ⬝ᵥ kFourAllOnes ≠ 0) :
    ∑ label ∈ kFourStarLabels, (1 - point.weight label)
        * (1 - chartLadderPivot kFourDirection point.mass point.weight
          Finset.univ label)
      = 1 + ∑ label ∈ kFourTriangleLabels, point.weight label
          * (1 - chartLadderPivot kFourDirection point.mass point.weight
            Finset.univ label) := by
  have hbal := kFourGaugeWall_univ_weighted_pivot_sum point
  have hsum := point.weight_sum_one
  have htri := kFourGaugeWall_triangle_deficiency_sum point axis scale hwall hne
  rw [Fin.sum_univ_six] at hbal hsum
  rw [sum_kFourTriangleLabels] at htri
  rw [sum_kFourStarLabels, sum_kFourTriangleLabels]
  ring_nf at hbal hsum htri ⊢
  linarith [hbal, hsum, htri]

/-! ## 8. The two-star law -/

/-- Erasing a triangle label from the full selection keeps the gap positive
definite: the axis and the two remaining triangle directions still span. -/
theorem kFourGaugeWall_posDef_erase_triangle (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ) (hscale : 0 < scale)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (drop : Fin 6) (keepOne keepTwo : Fin 6)
    (hpair : (Finset.univ.erase drop \ ({3, 4, 5} : Finset (Fin 6)))
      = {keepOne, keepTwo})
    (hempty : (({3, 4, 5} : Finset (Fin 6)) \ Finset.univ.erase drop) = ∅)
    (hnotmem : keepOne ∉ ({keepTwo} : Finset (Fin 6)))
    (hspan : ∀ probe : Fin 3 → ℝ, axis ⬝ᵥ probe = 0 →
      kFourDirection keepOne ⬝ᵥ probe = 0 →
      kFourDirection keepTwo ⬝ᵥ probe = 0 → probe = 0) :
    (directionChartGap kFourDirection point.mass point.weight
      (Finset.univ.erase drop)).PosDef := by
  have hsdiff := directionChartGap_sdiff kFourDirection point.mass point.weight
    (Finset.univ.erase drop) ({3, 4, 5} : Finset (Fin 6))
  rw [hpair, hempty, Finset.sum_empty, sub_zero, hwall,
    Finset.sum_insert hnotmem, Finset.sum_singleton] at hsdiff
  have heq : directionChartGap kFourDirection point.mass point.weight
      (Finset.univ.erase drop)
      = scale • atomMatrix axis
        + ((point.mass keepOne / point.weight keepOne)
            • atomMatrix (kFourDirection keepOne)
          + (point.mass keepTwo / point.weight keepTwo)
            • atomMatrix (kFourDirection keepTwo)) := by
    linear_combination (norm := module) hsdiff
  rw [heq]
  exact posDef_three_atoms hscale
    (div_pos (point.mass_pos keepOne) (point.weight_pos keepOne))
    (div_pos (point.mass_pos keepTwo) (point.weight_pos keepTwo)) hspan

/-- **EVERY TRIANGLE PIVOT IS BELOW ONE ON THE WALL.**  The three triangle
labels each carry a full-selection pivot strictly below one. -/
theorem kFourGaugeWall_triangle_pivot_lt_one (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ) (hscale : 0 < scale)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (hne : axis ⬝ᵥ kFourAllOnes ≠ 0)
    (drop : Fin 6) (hdrop : drop ∈ kFourTriangleLabels) :
    chartLadderPivot kFourDirection point.mass point.weight Finset.univ
      drop < 1 := by
  have hbase := posDef_directionChartGap_univ point
  refine (posDef_directionChartGap_erase_iff kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos Finset.univ
    (Finset.mem_univ drop) hbase).mp ?_
  have hdec : drop = 0 ∨ drop = 1 ∨ drop = 2 := by
    rw [kFourTriangleLabels, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_singleton] at hdrop
    exact hdrop
  rcases hdec with rfl | rfl | rfl
  · refine kFourGaugeWall_posDef_erase_triangle point axis scale hscale hwall
      0 1 2 (by decide) (by decide) (by decide)
      (fun probe h0 h1 h2 => ?_)
    refine kFourGaugeWall_span_of_pair axis probe hne h0 ?_ ?_
    · simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h1; linarith
    · simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h2; linarith
  · refine kFourGaugeWall_posDef_erase_triangle point axis scale hscale hwall
      1 0 2 (by decide) (by decide) (by decide)
      (fun probe h0 h1 h2 => ?_)
    refine kFourGaugeWall_span_of_pair axis probe hne h0 ?_ ?_
    · simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h1 h2; linarith
    · simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h2; linarith
  · refine kFourGaugeWall_posDef_erase_triangle point axis scale hscale hwall
      2 0 1 (by decide) (by decide) (by decide)
      (fun probe h0 h1 h2 => ?_)
    refine kFourGaugeWall_span_of_pair axis probe hne h0 ?_ ?_
    · simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h1 h2; linarith
    · simp only [kFourDirection, dotProduct, Fin.sum_univ_three,
        Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
        Matrix.cons_val_two, Matrix.tail_cons] at h1 h2; linarith

/-- **THE STAR DEFICIENCY FLOOR.**  The weighted star deficiency exceeds one at
every gauge wall point. -/
theorem kFourGaugeWall_star_deficiency_gt_one (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ) (hscale : 0 < scale)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (hne : axis ⬝ᵥ kFourAllOnes ≠ 0) :
    1 < ∑ label ∈ kFourStarLabels, (1 - point.weight label)
        * (1 - chartLadderPivot kFourDirection point.mass point.weight
          Finset.univ label) := by
  rw [kFourGaugeWall_star_deficiency_eq point axis scale hwall hne,
    sum_kFourTriangleLabels]
  have p0 := kFourGaugeWall_triangle_pivot_lt_one point axis scale hscale hwall
    hne 0 (by decide)
  have p1 := kFourGaugeWall_triangle_pivot_lt_one point axis scale hscale hwall
    hne 1 (by decide)
  have p2 := kFourGaugeWall_triangle_pivot_lt_one point axis scale hscale hwall
    hne 2 (by decide)
  have w0 := point.weight_pos 0
  have w1 := point.weight_pos 1
  have w2 := point.weight_pos 2
  nlinarith [mul_pos w0 (sub_pos.mpr p0), mul_pos w1 (sub_pos.mpr p1),
    mul_pos w2 (sub_pos.mpr p2)]

/-- **THE TWO-STAR LAW.**  At least two of the three star labels carry a
full-selection pivot below one.

A star label whose pivot reaches one contributes a nonpositive weighted
deficiency.  A single star label contributes less than one, because its weight
is positive and its pivot is nonnegative.  The star deficiency floor therefore
forbids two labels from reaching one at the same time.

By the ladder rung this says that at least two of the three five-label star
erasures are positive definite. -/
theorem kFourGaugeWall_two_star_pivots_lt_one (point : DirectionChartPoint 6)
    (axis : Fin 3 → ℝ) (scale : ℝ) (hscale : 0 < scale)
    (hwall : directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6)) = scale • atomMatrix axis)
    (hne : axis ⬝ᵥ kFourAllOnes ≠ 0) :
    (chartLadderPivot kFourDirection point.mass point.weight Finset.univ 3 < 1
        ∧ chartLadderPivot kFourDirection point.mass point.weight
          Finset.univ 4 < 1)
      ∨ (chartLadderPivot kFourDirection point.mass point.weight
            Finset.univ 3 < 1
          ∧ chartLadderPivot kFourDirection point.mass point.weight
            Finset.univ 5 < 1)
      ∨ (chartLadderPivot kFourDirection point.mass point.weight
            Finset.univ 4 < 1
          ∧ chartLadderPivot kFourDirection point.mass point.weight
            Finset.univ 5 < 1) := by
  have hfloor := kFourGaugeWall_star_deficiency_gt_one point axis scale hscale
    hwall hne
  rw [sum_kFourStarLabels] at hfloor
  have hbase := posDef_directionChartGap_univ point
  have n3 := chartLadderPivot_nonneg_of_posDef kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos Finset.univ hbase 3
  have n4 := chartLadderPivot_nonneg_of_posDef kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos Finset.univ hbase 4
  have n5 := chartLadderPivot_nonneg_of_posDef kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos Finset.univ hbase 5
  have w3 := point.weight_pos 3
  have w4 := point.weight_pos 4
  have w5 := point.weight_pos 5
  have e3 := directionChartPoint_weight_lt_one point 3
  have e4 := directionChartPoint_weight_lt_one point 4
  have e5 := directionChartPoint_weight_lt_one point 5
  by_contra hcon
  push Not at hcon
  obtain ⟨h34, h35, h45⟩ := hcon
  -- at most one star pivot is below one, so two of them reach one
  rcases lt_or_ge (chartLadderPivot kFourDirection point.mass point.weight
    Finset.univ 3) 1 with hlt3 | hge3
  · have hge4 := h34 hlt3
    have hge5 := h35 hlt3
    nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr e3)) n3]
  · rcases lt_or_ge (chartLadderPivot kFourDirection point.mass point.weight
      Finset.univ 4) 1 with hlt4 | hge4
    · have hge5 := h45 hlt4
      nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr e4)) n4]
    · nlinarith [mul_nonneg (le_of_lt (sub_pos.mpr e5)) n5]

end Gtz
