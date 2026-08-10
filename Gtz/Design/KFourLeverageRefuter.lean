import Gtz.Design.KFourBandAtlas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

noncomputable def leverageRefuterMass : Fin 6 → ℝ
  | 0 => 479719 / 500000
  | 1 => 17661 / 125000
  | 2 => 32673 / 200000
  | 3 => 1
  | 4 => 26689 / 250000
  | 5 => 223709 / 250000

noncomputable def leverageRefuterWeight : Fin 6 → ℝ
  | 0 => 251587 / 1000000
  | 1 => 11193 / 100000
  | 2 => 33001 / 500000
  | 3 => 72469 / 250000
  | 4 => 11159 / 200000
  | 5 => 22481 / 100000

noncomputable def leverageRefuterPoint : DirectionChartPoint 6 where
  mass := leverageRefuterMass
  weight := leverageRefuterWeight
  mass_pos := by intro label; fin_cases label <;> norm_num [leverageRefuterMass]
  weight_pos := by intro label; fin_cases label <;> norm_num [leverageRefuterWeight]
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num [leverageRefuterWeight]

theorem leverageRefuterPoint_mass_eq :
    leverageRefuterPoint.mass = leverageRefuterMass := rfl

theorem leverageRefuterPoint_weight_eq :
    leverageRefuterPoint.weight = leverageRefuterWeight := rfl

theorem leverageRefuter_isMaxLeverageEdge_two :
    IsMaxLeverageEdge leverageRefuterPoint 2 := by
  intro label
  fin_cases label <;>
    norm_num [kFourContractionTreePolynomial, leverageRefuterPoint_mass_eq,
      leverageRefuterPoint_weight_eq, leverageRefuterMass, leverageRefuterWeight]

theorem leverageRefuter_gap_zeroTwoFour_det_neg :
    (directionChartGap kFourDirection leverageRefuterPoint.mass
      leverageRefuterPoint.weight {0, 2, 4}).det < 0 := by
  simp only [directionChartGap, leverageRefuterPoint_mass_eq,
    leverageRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [leverageRefuterMass, leverageRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem leverageRefuter_gap_oneTwoFive_det_neg :
    (directionChartGap kFourDirection leverageRefuterPoint.mass
      leverageRefuterPoint.weight {1, 2, 5}).det < 0 := by
  simp only [directionChartGap, leverageRefuterPoint_mass_eq,
    leverageRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [leverageRefuterMass, leverageRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem leverageRefuter_gap_zeroTwoThree_det_neg :
    (directionChartGap kFourDirection leverageRefuterPoint.mass
      leverageRefuterPoint.weight {0, 2, 3}).det < 0 := by
  simp only [directionChartGap, leverageRefuterPoint_mass_eq,
    leverageRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [leverageRefuterMass, leverageRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem leverageRefuter_gap_zeroTwoFive_det_neg :
    (directionChartGap kFourDirection leverageRefuterPoint.mass
      leverageRefuterPoint.weight {0, 2, 5}).det < 0 := by
  simp only [directionChartGap, leverageRefuterPoint_mass_eq,
    leverageRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [leverageRefuterMass, leverageRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem leverageRefuter_gap_oneTwoThree_det_neg :
    (directionChartGap kFourDirection leverageRefuterPoint.mass
      leverageRefuterPoint.weight {1, 2, 3}).det < 0 := by
  simp only [directionChartGap, leverageRefuterPoint_mass_eq,
    leverageRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [leverageRefuterMass, leverageRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem leverageRefuter_gap_oneTwoFour_det_neg :
    (directionChartGap kFourDirection leverageRefuterPoint.mass
      leverageRefuterPoint.weight {1, 2, 4}).det < 0 := by
  simp only [directionChartGap, leverageRefuterPoint_mass_eq,
    leverageRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [leverageRefuterMass, leverageRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem leverageRefuter_gap_twoThreeFour_det_neg :
    (directionChartGap kFourDirection leverageRefuterPoint.mass
      leverageRefuterPoint.weight {2, 3, 4}).det < 0 := by
  simp only [directionChartGap, leverageRefuterPoint_mass_eq,
    leverageRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [leverageRefuterMass, leverageRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem leverageRefuter_gap_twoThreeFive_det_neg :
    (directionChartGap kFourDirection leverageRefuterPoint.mass
      leverageRefuterPoint.weight {2, 3, 5}).det < 0 := by
  simp only [directionChartGap, leverageRefuterPoint_mass_eq,
    leverageRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [leverageRefuterMass, leverageRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem kFourSpanningTreeThroughTwo_enumeration :
    ∀ tree ∈ kFourSpanningTreeList, (2 : Fin 6) ∈ tree →
      tree = {0, 2, 4} ∨ tree = {1, 2, 5} ∨ tree = {0, 2, 3} ∨
      tree = {0, 2, 5} ∨ tree = {1, 2, 3} ∨ tree = {1, 2, 4} ∨
      tree = {2, 3, 4} ∨ tree = {2, 3, 5} := by decide

theorem leverageRefuter_gap_zeroThreeFive_posDef :
    (directionChartGap kFourDirection leverageRefuterPoint.mass
      leverageRefuterPoint.weight {0, 3, 5}).PosDef := by
  rw [posDef_finThree_iff_cornerBlockDet _
    (directionChartGap_transpose kFourDirection leverageRefuterPoint.mass
      leverageRefuterPoint.weight {0, 3, 5})]
  simp only [directionChartGap, leverageRefuterPoint_mass_eq,
    leverageRefuterPoint_weight_eq]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, Fin.sum_univ_six]
  norm_num [leverageRefuterMass, leverageRefuterWeight, kFourDirection,
    atomMatrix, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.head_cons, Matrix.tail_cons]

theorem kFourLeverageEdgeHostsStrictTree_refuted :
    ¬ KFourLeverageEdgeHostsStrictTree := by
  intro hhost
  obtain ⟨tree, htree, hedge, hposDef⟩ :=
    hhost leverageRefuterPoint 2 leverageRefuter_isMaxLeverageEdge_two
  have hdetPos := hposDef.det_pos
  rcases kFourSpanningTreeThroughTwo_enumeration tree htree hedge with
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · linarith [leverageRefuter_gap_zeroTwoFour_det_neg]
  · linarith [leverageRefuter_gap_oneTwoFive_det_neg]
  · linarith [leverageRefuter_gap_zeroTwoThree_det_neg]
  · linarith [leverageRefuter_gap_zeroTwoFive_det_neg]
  · linarith [leverageRefuter_gap_oneTwoThree_det_neg]
  · linarith [leverageRefuter_gap_oneTwoFour_det_neg]
  · linarith [leverageRefuter_gap_twoThreeFour_det_neg]
  · linarith [leverageRefuter_gap_twoThreeFive_det_neg]

end Gtz
