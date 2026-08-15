import Gtz.Design.ChartReadingLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The chart weight monotonicity and the conical slack

The chart gap reads `sum_C (m_c / w_c) (v_c . x)^2 - sum m_c (v_c . x)^2`, and
the weights enter only through the selected quotients.  A lower weight gives a
larger quotient.  The gap is therefore antitone in each selected weight.

* `directionChartGap_reading_antitone` is the reading comparison.
* `posDef_directionChartGap_antitone_weight` moves strictness down in weight.
* `subOneWeightLift` completes a deficient weight vector to a chart point.
* `exists_posDef_of_coveredChart_of_weight_sum_le` is the transfer: a covering
  of the chart slice covers the full cone of weight sum at most one.

The probe verdict behind the module (exact rationals, calibration on the four
banked test points): the K4 covering FAILS on the open orthant — the symmetric
point `m_c = mu, d_c = d` fires its stars exactly when `d > 4 mu`, so the
symmetric ray is uncovered from weight sum `6/5` up — but adversarial descent
over uncovered points stalls at weight sum `1.0805`, strictly above the chart
slice.  The chart covering therefore carries interior slack in the weight-sum
direction, and certificates that lose less than that slack are admissible.
-/

namespace Gtz

open Matrix

variable {size : ℕ}

/-- The chart reading is antitone in each selected weight: a smaller positive
weight vector gives a reading at least as large, at every probe. -/
theorem directionChartGap_reading_antitone (direction : Fin size → (Fin 3 → ℝ))
    (mass lowWeight highWeight : Fin size → ℝ) (hmass : ∀ label, 0 ≤ mass label)
    (hlowPos : ∀ label, 0 < lowWeight label)
    (hle : ∀ label, lowWeight label ≤ highWeight label)
    (selected : Finset (Fin size)) (probe : Fin 3 → ℝ) :
    probe ⬝ᵥ (directionChartGap direction mass highWeight selected *ᵥ probe)
      ≤ probe ⬝ᵥ (directionChartGap direction mass lowWeight selected *ᵥ probe) := by
  rw [dotProduct_directionChartGap_mulVec_eq, dotProduct_directionChartGap_mulVec_eq]
  refine sub_le_sub_right (Finset.sum_le_sum fun label _ => ?_) _
  have hlow := hlowPos label
  have hhigh : 0 < highWeight label := lt_of_lt_of_le hlow (hle label)
  have hquot : mass label / highWeight label ≤ mass label / lowWeight label :=
    div_le_div_of_nonneg_left (hmass label) (hlowPos label) (hle label)
  exact mul_le_mul_of_nonneg_right hquot (sq_nonneg _)

/-- Strict domination moves down in weight: if the gap is positive definite at
the higher weights, it is positive definite at any lower positive weights. -/
theorem posDef_directionChartGap_antitone_weight (direction : Fin size → (Fin 3 → ℝ))
    (mass lowWeight highWeight : Fin size → ℝ) (hmass : ∀ label, 0 ≤ mass label)
    (hlowPos : ∀ label, 0 < lowWeight label)
    (hle : ∀ label, lowWeight label ≤ highWeight label)
    (selected : Finset (Fin size))
    (hpd : (directionChartGap direction mass highWeight selected).PosDef) :
    (directionChartGap direction mass lowWeight selected).PosDef := by
  refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨?_, fun probe hne => ?_⟩
  · exact isHermitian_of_transpose_eq
      (directionChartGap_transpose direction mass lowWeight selected)
  · rw [star_trivial]
    have hhighRead := (Matrix.posDef_iff_dotProduct_mulVec.mp hpd).2 hne
    rw [star_trivial] at hhighRead
    exact lt_of_lt_of_le hhighRead
      (directionChartGap_reading_antitone direction mass lowWeight highWeight
        hmass hlowPos hle selected probe)

/-- The uniform lift of a deficient weight vector: add one sixth of the deficit
to every label. -/
noncomputable def subOneWeightLift (weight : Fin 6 → ℝ) : Fin 6 → ℝ :=
  fun label => weight label + (1 - ∑ other, weight other) / 6

theorem subOneWeightLift_le (weight : Fin 6 → ℝ)
    (hsum : ∑ label, weight label ≤ 1) (label : Fin 6) :
    weight label ≤ subOneWeightLift weight label := by
  have hdef : 0 ≤ (1 - ∑ other, weight other) / 6 := by
    have := sub_nonneg.mpr hsum
    positivity
  simp only [subOneWeightLift]
  linarith

theorem subOneWeightLift_pos (weight : Fin 6 → ℝ) (hpos : ∀ label, 0 < weight label)
    (hsum : ∑ label, weight label ≤ 1) (label : Fin 6) :
    0 < subOneWeightLift weight label :=
  lt_of_lt_of_le (hpos label) (subOneWeightLift_le weight hsum label)

theorem subOneWeightLift_sum (weight : Fin 6 → ℝ) :
    ∑ label, subOneWeightLift weight label = 1 := by
  simp only [subOneWeightLift, Finset.sum_add_distrib, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-- The lifted chart point of a deficient weight vector. -/
noncomputable def subOneChartPoint (mass weight : Fin 6 → ℝ)
    (hmass : ∀ label, 0 < mass label) (hpos : ∀ label, 0 < weight label)
    (hsum : ∑ label, weight label ≤ 1) : DirectionChartPoint 6 where
  mass := mass
  weight := subOneWeightLift weight
  mass_pos := hmass
  weight_pos := subOneWeightLift_pos weight hpos hsum
  weight_sum_one := subOneWeightLift_sum weight

/-- **The conical transfer.**  A strict covering of the chart slice covers the
full cone of positive weights with sum at most one: the deficient point lifts
to the slice, and strictness comes back down along the antitone law. -/
theorem exists_posDef_of_coveredChart_of_weight_sum_le
    (direction : Fin 6 → (Fin 3 → ℝ)) (trees : List (Finset (Fin 6)))
    (hcover : ∀ point : DirectionChartPoint 6, ∃ selected ∈ trees,
      (directionChartGap direction point.mass point.weight selected).PosDef)
    (mass weight : Fin 6 → ℝ) (hmass : ∀ label, 0 < mass label)
    (hpos : ∀ label, 0 < weight label) (hsum : ∑ label, weight label ≤ 1) :
    ∃ selected ∈ trees,
      (directionChartGap direction mass weight selected).PosDef := by
  obtain ⟨selected, hmem, hpd⟩ :=
    hcover (subOneChartPoint mass weight hmass hpos hsum)
  exact ⟨selected, hmem,
    posDef_directionChartGap_antitone_weight direction mass weight
      (subOneWeightLift weight) (fun label => le_of_lt (hmass label)) hpos
      (subOneWeightLift_le weight hsum) selected hpd⟩

end Gtz
