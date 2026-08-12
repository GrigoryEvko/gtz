import Gtz.Wave.OrbitFourAlignedSelfAdjoint

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unnecessarySeqFocus false

namespace Gtz

open Matrix Finset

/-- **FULL-RANK ALIGNED TYPE-NINE LEAF CLOSED.**  The canonical four active
weighted tight rows cannot have aligned endpoints and a nonsingular pair
plane.  The change to the sparse orthogonal frame turns the captured
rank-two projection into the scalar contradiction in
`false_of_typeNine_aligned_orthogonal_projection`. -/
theorem SixThreeCrux.false_of_orbitFour_aligned_fullRankRows
    (crux : SixThreeCrux)
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = orbitFourFamily)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    {x y a b c e h k z scale : ℝ}
    (hrowZero :
      (orbitFourWeightedTightColumns multiplier tightDir) 0
        = (![0, a, scale * a, 0] : Fin 4 → ℝ))
    (hrowOne :
      (orbitFourWeightedTightColumns multiplier tightDir) 1
        = (![x, b, 0, h] : Fin 4 → ℝ))
    (hrowTwo :
      (orbitFourWeightedTightColumns multiplier tightDir) 2
        = (![y, 0, e, 0] : Fin 4 → ℝ))
    (hrowThree :
      (orbitFourWeightedTightColumns multiplier tightDir) 3
        = (![0, c, scale * c, 0] : Fin 4 → ℝ))
    (hrowFour :
      (orbitFourWeightedTightColumns multiplier tightDir) 4
        = (![0, 0, 0, k] : Fin 4 → ℝ))
    (hrowFive :
      (orbitFourWeightedTightColumns multiplier tightDir) 5
        = (![0, 0, 0, z] : Fin 4 → ℝ))
    (ha : a ≠ 0) (hc : c ≠ 0) (hy : y ≠ 0)
    (hb : b ≠ 0) (he : e ≠ 0) (hk : k ≠ 0) (hz : z ≠ 0)
    (hdet : e * x + scale * b * y ≠ 0) : False := by
  classical
  let point := chartPointOfDesign crux.design
  let P := point.chart
  let B := orbitFourWeightedTightColumns multiplier tightDir
  let value := chartObjective point
  let C := typeNineAlignedChange x y b e h scale
  let T := typeNineAlignedChangeInv x y b e h scale
  let F := orbitFourAlignedFrame a c k z
  change B 0 = (![0, a, scale * a, 0] : Fin 4 → ℝ) at hrowZero
  change B 1 = (![x, b, 0, h] : Fin 4 → ℝ) at hrowOne
  change B 2 = (![y, 0, e, 0] : Fin 4 → ℝ) at hrowTwo
  change B 3 = (![0, c, scale * c, 0] : Fin 4 → ℝ) at hrowThree
  change B 4 = (![0, 0, 0, k] : Fin 4 → ℝ) at hrowFour
  change B 5 = (![0, 0, 0, z] : Fin 4 → ℝ) at hrowFive
  have hdataOrbit : IsChartStationaryData 3 P point.weight value
      orbitFourFamily (id : Finset (Fin 6) → Finset (Fin 6))
      multiplier tightDir := by
    simpa only [P, point, value, hfamily] using hdata
  obtain ⟨L, M, hleft, hPB, hMsymm, hMidem, hMtrace⟩ :=
    crux.exists_orbitFour_coefficientProjection hfamily hdata
  let R := C * M * T
  have hTC : T * C = 1 := by
    simpa only [T, C] using typeNineAlignedChange_inv_mul hdet
  have hBT : B * T = F := by
    simpa only [B, T, F] using orbitFourAlignedColumns_mul_inv_eq_frame B hdet
      hrowZero hrowOne hrowTwo hrowThree hrowFour hrowFive
  have hFC : F * C = B := by
    simpa only [F, C] using orbitFourAlignedFrame_mul_change_eq_columns B hdet hBT
  have hPF : P * F = F * R := by
    simpa only [P, B, F, C, T, R] using
      alignedSimilarity_representation P B F C T M hBT hFC hPB
  obtain ⟨hRidem, hRtrace⟩ : R * R = R ∧ Matrix.trace R = 2 := by
    simpa only [R] using alignedSimilarity_idempotent_trace C T M hTC hMidem hMtrace
  obtain ⟨hself01, hself02, hself12, hself03⟩ :=
    orbitFourAlignedFrame_selfAdjoint_coordinates P R a c k z
      (by simpa only [P] using hdata.isSymmetric) hPF
  have hlocal (label : Fin 4) (atomIndex : Fin 6)
      (hmem : atomIndex ∈ orbitFourLabel label) :
      ((F * R) * C) atomIndex label
        = (value + point.weight atomIndex) * (F * C) atomIndex label := by
    have himage := projection_mul_orbitFourWeightedColumn_apply
      hdataOrbit label atomIndex hmem
    change (P * B) atomIndex label
      = (value + point.weight atomIndex) * B atomIndex label at himage
    calc
      ((F * R) * C) atomIndex label
          = ((P * F) * C) atomIndex label := by rw [hPF]
      _ = (P * (F * C)) atomIndex label := by rw [Matrix.mul_assoc]
      _ = (P * B) atomIndex label := by rw [hFC]
      _ = (value + point.weight atomIndex) * B atomIndex label := himage
      _ = (value + point.weight atomIndex) * (F * C) atomIndex label := by rw [hFC]
  have hp0EndpointRaw := hlocal (0 : Fin 4) (0 : Fin 6) (by
    simp [orbitFourLabel, orbitFourBlockZeroOneTwo])
  have hp0One := hlocal (0 : Fin 4) (1 : Fin 6) (by
    simp [orbitFourLabel, orbitFourBlockZeroOneTwo])
  have hp1EndpointRaw := hlocal (1 : Fin 4) (0 : Fin 6) (by
    simp [orbitFourLabel, orbitFourBlockZeroOneThree])
  have hp1One := hlocal (1 : Fin 4) (1 : Fin 6) (by
    simp [orbitFourLabel, orbitFourBlockZeroOneThree])
  have hp2EndpointRaw := hlocal (2 : Fin 4) (0 : Fin 6) (by
    simp [orbitFourLabel, orbitFourBlockZeroTwoThree])
  have hp2Two := hlocal (2 : Fin 4) (2 : Fin 6) (by
    simp [orbitFourLabel, orbitFourBlockZeroTwoThree])
  have hp3One := hlocal (3 : Fin 4) (1 : Fin 6) (by
    simp [orbitFourLabel, orbitFourBlockOneFourFive])
  have hp3PrivateRaw := hlocal (3 : Fin 4) (4 : Fin 6) (by
    simp [orbitFourLabel, orbitFourBlockOneFourFive])
  have hp1EndpointThreeRaw := hlocal (1 : Fin 4) (3 : Fin 6) (by
    simp [orbitFourLabel, orbitFourBlockZeroOneThree])
  have hp3PrivateFiveRaw := hlocal (3 : Fin 4) (5 : Fin 6) (by
    simp [orbitFourLabel, orbitFourBlockOneFourFive])
  have hFRFive (column : Fin 4) : (F * R) 5 column = z * R 3 column := by
    rw [Matrix.mul_apply, Fin.sum_univ_four]
    have hFrowFive : F 5 = (![0, 0, 0, z] : Fin 4 → ℝ) := by rfl
    simp [hFrowFive, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons]
  norm_num [F, C, orbitFourAlignedFrame, typeNineAlignedChange,
    Matrix.mul_apply, Matrix.vecMul, Matrix.vecMul_apply, dotProduct,
    Fin.sum_univ_four, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four, Matrix.cons_val_succ,
    Matrix.head_cons, Matrix.tail_cons,
    Matrix.empty_val', Matrix.cons_val_fin_one, Matrix.head_fin_const,
    Matrix.of_apply] at hp0EndpointRaw hp0One hp1EndpointRaw hp1One hp2EndpointRaw hp2Two hp3One hp3PrivateRaw hp1EndpointThreeRaw
  rw [hFC] at hp3PrivateFiveRaw
  norm_num [C, typeNineAlignedChange, Matrix.mul_apply, Fin.sum_univ_four,
    hFRFive, hrowFive, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
    Matrix.tail_cons] at hp3PrivateFiveRaw
  change k * R 3 0 * h + k * R 3 3
      = (value + point.weight 4) * k at hp3PrivateRaw
  have hp0Endpoint : x * R 2 0 + y * R 2 1 = 0 := by
    apply (mul_left_cancel₀ ha)
    nlinarith only [hp0EndpointRaw]
  have hp1Endpoint : b * R 2 0 + R 2 2 = value + point.weight 0 := by
    apply (mul_left_cancel₀ ha)
    nlinarith only [hp1EndpointRaw]
  have hp2Endpoint : e * R 2 1 + scale * R 2 2
      = scale * (value + point.weight 0) := by
    apply (mul_left_cancel₀ ha)
    nlinarith only [hp2EndpointRaw]
  have hp3Private : h * R 3 0 + R 3 3 = value + point.weight 4 := by
    apply (mul_left_cancel₀ hk)
    nlinarith only [hp3PrivateRaw]
  have hdThree : value + point.weight 3 = value + point.weight 0 := by
    have hmul : c * ((value + point.weight 3)
        - (value + point.weight 0)) = 0 := by
      linear_combination -hp1EndpointThreeRaw + c * hp1Endpoint
    have hzero := (mul_eq_zero.mp hmul).resolve_left hc
    linarith only [hzero]
  have hdFive : value + point.weight 5 = value + point.weight 4 := by
    have hmul : z * ((value + point.weight 5)
        - (value + point.weight 4)) = 0 := by
      linear_combination -hp3PrivateFiveRaw + z * hp3Private
    have hzero := (mul_eq_zero.mp hmul).resolve_left hz
    linarith only [hzero]
  have hp0One' : x * R 0 0 + y * R 0 1
      = (value + point.weight 1) * x := by
    nlinarith only [hp0One]
  have hp1One' : b * R 0 0 + R 0 2
      = (value + point.weight 1) * b := by
    nlinarith only [hp1One]
  have hp2Two' : e * R 1 1 + scale * R 1 2
      = (value + point.weight 2) * e := by
    nlinarith only [hp2Two]
  have hp3One' : h * R 0 0 + R 0 3
      = (value + point.weight 1) * h := by
    nlinarith only [hp3One]
  have hK : k ^ 2 + z ^ 2 ≠ 0 := by
    have hkSq : 0 < k ^ 2 := sq_pos_of_ne_zero hk
    nlinarith only [hkSq, sq_nonneg z]
  have hshiftedNonneg (atomIndex : Fin 6) :
      0 ≤ value + point.weight atomIndex := by
    have hfloor := weight_ge_neg_value_of_isChartStationaryData hdata atomIndex
    change -value ≤ point.weight atomIndex at hfloor
    linarith
  have hdOneLt : value + point.weight 1 < 1 := by
    have hnegative : value < 0 := by
      simpa only [value, point] using crux.hasNegativeChartValue
    have hweightLt := weight_lt_one crux.design (by norm_num) (1 : Fin 6)
    change value + crux.design.weight 1 < 1
    linarith only [hnegative, hweightLt]
  have hshiftedSum :
      2 * (value + point.weight 0) + (value + point.weight 1)
        + (value + point.weight 2) + 2 * (value + point.weight 4) < 1 := by
    have hsum := hdata.weight_sum_one
    rw [Fin.sum_univ_six] at hsum
    have hnegative : value < 0 := by
      simpa only [value, point] using crux.hasNegativeChartValue
    linarith only [hsum, hnegative, hdThree, hdFive]
  exact false_of_typeNine_aligned_orthogonal_projection hdet hy hb he hK
    hself01 hself02 hself12 hself03 hp0Endpoint hp0One'
    hp1Endpoint hp1One' hp2Endpoint hp2Two' hp3One' hp3Private
    hRidem hRtrace (hshiftedNonneg 0) (hshiftedNonneg 4) hdOneLt hshiftedSum


end Gtz
