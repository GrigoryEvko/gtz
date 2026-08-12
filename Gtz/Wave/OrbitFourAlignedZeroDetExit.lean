import Gtz.Wave.OrbitFourAlignedFullRankExit
import Gtz.Wave.OrbitFourAlignedExchange

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000
set_option linter.unnecessarySeqFocus false

namespace Gtz

open Matrix Finset

/-- Linear, non-normalized version of the local tight-window read.  It lets the
active-exchange bridge consume multiplier-weighted tight columns directly. -/
theorem shiftedFourWindow_mulVec_eq_zero_of_projection_read
    (point : ChartPoint 6 3)
    (ambientVec : Fin 6 → ℝ) (localVec : Fin 4 → ℝ)
    (hspread : ambientVec = selectionInjection chartFirstFourPickSix *ᵥ localVec)
    (localIndex : Fin 4)
    (hread : (point.chart *ᵥ ambientVec) (chartFirstFourPickSix localIndex)
      = (chartObjective point + point.weight (chartFirstFourPickSix localIndex))
          * ambientVec (chartFirstFourPickSix localIndex)) :
    (chartFirstFourShiftedGap point *ᵥ localVec) localIndex = 0 := by
  have hzero :
      ((chartPointGap point
        - chartObjective point • (1 : Matrix (Fin 6) (Fin 6) ℝ)) *ᵥ ambientVec)
          (chartFirstFourPickSix localIndex) = 0 := by
    rw [Matrix.sub_mulVec, Pi.sub_apply, Matrix.smul_mulVec,
      Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, chartPointGap,
      Matrix.sub_mulVec, Pi.sub_apply, Matrix.mulVec_diagonal]
    change (point.chart *ᵥ ambientVec) (chartFirstFourPickSix localIndex)
        - point.weight (chartFirstFourPickSix localIndex)
            * ambientVec (chartFirstFourPickSix localIndex)
        - chartObjective point * ambientVec (chartFirstFourPickSix localIndex) = 0
    rw [hread]
    ring
  rw [hspread] at hzero
  have hwindow := mulVec_selectionInjection_apply
    (chartPointGap point
      - chartObjective point • (1 : Matrix (Fin 6) (Fin 6) ℝ))
    chartFirstFourPickSix localVec localIndex
  rw [Matrix.submatrix_sub, Matrix.submatrix_smul] at hwindow
  change (((chartPointGap point
      - chartObjective point • (1 : Matrix (Fin 6) (Fin 6) ℝ)) *ᵥ
        (selectionInjection chartFirstFourPickSix *ᵥ localVec))
          (chartFirstFourPickSix localIndex)
      = (((chartPointGap point).submatrix chartFirstFourPickSix chartFirstFourPickSix
          - chartObjective point •
            (1 : Matrix (Fin 6) (Fin 6) ℝ).submatrix
              chartFirstFourPickSix chartFirstFourPickSix) *ᵥ localVec)
          localIndex) at hwindow
  rw [Matrix.submatrix_one _ (by decide : Function.Injective chartFirstFourPickSix)] at hwindow
  rw [hwindow] at hzero
  simpa only [chartFirstFourShiftedGap] using hzero

/-- The determinant-zero aligned pair plane is the active-exchange branch: the
residual exchange is a nonzero multiple of the `012` tight column, forcing the
omitted `123` block to be active. -/
theorem SixThreeCrux.false_of_orbitFour_aligned_zeroDetRows
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
    (hy : y ≠ 0) (he : e ≠ 0)
    (hdet : e * x + scale * b * y = 0) : False := by
  classical
  let point := chartPointOfDesign crux.design
  let B := orbitFourWeightedTightColumns multiplier tightDir
  let left : Fin 4 → ℝ := ![a, b, 0, c]
  let right : Fin 4 → ℝ := ![scale * a, 0, e, scale * c]
  let zero : Fin 4 → ℝ := ![0, x, y, 0]
  let pair : Fin 4 → ℝ := right - scale • left
  change B 0 = (![0, a, scale * a, 0] : Fin 4 → ℝ) at hrowZero
  change B 1 = (![x, b, 0, h] : Fin 4 → ℝ) at hrowOne
  change B 2 = (![y, 0, e, 0] : Fin 4 → ℝ) at hrowTwo
  change B 3 = (![0, c, scale * c, 0] : Fin 4 → ℝ) at hrowThree
  change B 4 = (![0, 0, 0, k] : Fin 4 → ℝ) at hrowFour
  change B 5 = (![0, 0, 0, z] : Fin 4 → ℝ) at hrowFive
  have hdataOrbit : IsChartStationaryData 3 point.chart point.weight
      (chartObjective point) orbitFourFamily
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir := by
    simpa only [point, hfamily] using hdata
  have hleftSpread : B.col 1
      = selectionInjection chartFirstFourPickSix *ᵥ left := by
    funext atomIndex
    fin_cases atomIndex <;>
      simp [B, left, selectionInjection, chartFirstFourPickSix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_four, hrowZero, hrowOne,
        hrowTwo, hrowThree, hrowFour, hrowFive]
  have hrightSpread : B.col 2
      = selectionInjection chartFirstFourPickSix *ᵥ right := by
    funext atomIndex
    fin_cases atomIndex <;>
      simp [B, right, selectionInjection, chartFirstFourPickSix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_four, hrowZero, hrowOne,
        hrowTwo, hrowThree, hrowFour, hrowFive]
  have hzeroSpread : B.col 0
      = selectionInjection chartFirstFourPickSix *ᵥ zero := by
    funext atomIndex
    fin_cases atomIndex <;>
      simp [B, zero, selectionInjection, chartFirstFourPickSix,
        Matrix.mulVec, dotProduct, Fin.sum_univ_four, hrowZero, hrowOne,
        hrowTwo, hrowThree, hrowFour, hrowFive]
  have hprojectionRead (label : Fin 4) (atomIndex : Fin 6)
      (hmem : atomIndex ∈ orbitFourLabel label) :
      (point.chart *ᵥ B.col label) atomIndex
        = (chartObjective point + point.weight atomIndex) * B.col label atomIndex := by
    change (point.chart * B) atomIndex label
      = (chartObjective point + point.weight atomIndex) * B atomIndex label
    exact projection_mul_orbitFourWeightedColumn_apply
      hdataOrbit label atomIndex hmem
  have hleftZero := shiftedFourWindow_mulVec_eq_zero_of_projection_read
    point (B.col 1) left hleftSpread 0
      (hprojectionRead 1 0 (by simp [orbitFourLabel, orbitFourBlockZeroOneThree]))
  have hleftThree := shiftedFourWindow_mulVec_eq_zero_of_projection_read
    point (B.col 1) left hleftSpread 3
      (hprojectionRead 1 3 (by simp [orbitFourLabel, orbitFourBlockZeroOneThree]))
  have hrightZero := shiftedFourWindow_mulVec_eq_zero_of_projection_read
    point (B.col 2) right hrightSpread 0
      (hprojectionRead 2 0 (by simp [orbitFourLabel, orbitFourBlockZeroTwoThree]))
  have hrightThree := shiftedFourWindow_mulVec_eq_zero_of_projection_read
    point (B.col 2) right hrightSpread 3
      (hprojectionRead 2 3 (by simp [orbitFourLabel, orbitFourBlockZeroTwoThree]))
  have hzeroOne := shiftedFourWindow_mulVec_eq_zero_of_projection_read
    point (B.col 0) zero hzeroSpread 1
      (hprojectionRead 0 1 (by simp [orbitFourLabel, orbitFourBlockZeroOneTwo]))
  have hzeroTwo := shiftedFourWindow_mulVec_eq_zero_of_projection_read
    point (B.col 0) zero hzeroSpread 2
      (hprojectionRead 0 2 (by simp [orbitFourLabel, orbitFourBlockZeroOneTwo]))
  have hpairDef : pair = right - scale • left := rfl
  have hpairShape : pair = (![0, -(scale * b), e, 0] : Fin 4 → ℝ) := by
    funext coordinate
    fin_cases coordinate <;> simp [pair, left, right]
  have hpairZero : pair = (e / y) • zero := by
    funext coordinate
    fin_cases coordinate <;> simp [pair, left, right, zero, hy] <;>
      field_simp [hy] at hdet ⊢ <;> nlinarith only [hdet]
  have hpairOne : (chartFirstFourShiftedGap point *ᵥ pair) 1 = 0 := by
    rw [hpairZero, Matrix.mulVec_smul, Pi.smul_apply, hzeroOne, smul_eq_mul,
      mul_zero]
  have hpairTwo : (chartFirstFourShiftedGap point *ᵥ pair) 2 = 0 := by
    rw [hpairZero, Matrix.mulVec_smul, Pi.smul_apply, hzeroTwo, smul_eq_mul,
      mul_zero]
  exact false_of_orbitFour_aligned_active_exchange point hfamily
    left right pair scale (-(scale * b)) e hpairDef hpairShape he
    hleftZero hleftThree hrightZero hrightThree hpairOne hpairTwo

/-- The canonical aligned type-nine support pattern is empty, with no generic
or phase hypothesis: the pair-plane determinant is either nonzero (orthogonal
coefficient trace exit) or zero (active exchange). -/
theorem SixThreeCrux.false_of_orbitFour_alignedRows
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
    (hrowZero : (orbitFourWeightedTightColumns multiplier tightDir) 0
      = (![0, a, scale * a, 0] : Fin 4 → ℝ))
    (hrowOne : (orbitFourWeightedTightColumns multiplier tightDir) 1
      = (![x, b, 0, h] : Fin 4 → ℝ))
    (hrowTwo : (orbitFourWeightedTightColumns multiplier tightDir) 2
      = (![y, 0, e, 0] : Fin 4 → ℝ))
    (hrowThree : (orbitFourWeightedTightColumns multiplier tightDir) 3
      = (![0, c, scale * c, 0] : Fin 4 → ℝ))
    (hrowFour : (orbitFourWeightedTightColumns multiplier tightDir) 4
      = (![0, 0, 0, k] : Fin 4 → ℝ))
    (hrowFive : (orbitFourWeightedTightColumns multiplier tightDir) 5
      = (![0, 0, 0, z] : Fin 4 → ℝ))
    (ha : a ≠ 0) (hc : c ≠ 0) (hy : y ≠ 0)
    (hb : b ≠ 0) (he : e ≠ 0) (hk : k ≠ 0) (hz : z ≠ 0) : False := by
  by_cases hdet : e * x + scale * b * y = 0
  · exact crux.false_of_orbitFour_aligned_zeroDetRows hfamily hdata
      hrowZero hrowOne hrowTwo hrowThree hrowFour hrowFive hy he hdet
  · exact crux.false_of_orbitFour_aligned_fullRankRows hfamily hdata
      hrowZero hrowOne hrowTwo hrowThree hrowFour hrowFive
      ha hc hy hb he hk hz hdet

/-- Direct canonical type-nine interface.  Endpoint rigidity first forces the
two `013`/`023` rows to be aligned; the preceding determinant split then
eliminates the resulting configuration. -/
theorem SixThreeCrux.false_of_orbitFour_typeNineRows
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
    {x y a r b c f e h k z : ℝ}
    (hrowZero : (orbitFourWeightedTightColumns multiplier tightDir) 0
      = (![0, a, r, 0] : Fin 4 → ℝ))
    (hrowOne : (orbitFourWeightedTightColumns multiplier tightDir) 1
      = (![x, b, 0, h] : Fin 4 → ℝ))
    (hrowTwo : (orbitFourWeightedTightColumns multiplier tightDir) 2
      = (![y, 0, e, 0] : Fin 4 → ℝ))
    (hrowThree : (orbitFourWeightedTightColumns multiplier tightDir) 3
      = (![0, c, f, 0] : Fin 4 → ℝ))
    (hrowFour : (orbitFourWeightedTightColumns multiplier tightDir) 4
      = (![0, 0, 0, k] : Fin 4 → ℝ))
    (hrowFive : (orbitFourWeightedTightColumns multiplier tightDir) 5
      = (![0, 0, 0, z] : Fin 4 → ℝ))
    (ha : a ≠ 0) (hr : r ≠ 0) (hc : c ≠ 0) (hy : y ≠ 0)
    (hb : b ≠ 0) (he : e ≠ 0) (hk : k ≠ 0) (hz : z ≠ 0) : False := by
  have hendpoint : a * f - r * c = 0 :=
    crux.orbitFour_endpoint_det_eq_zero hfamily hdata hrowZero hrowThree
      hrowFour hk
  obtain ⟨scale, hscale, hrAlign, hfAlign⟩ :=
    exists_nonzero_alignment_of_endpoint_det_eq_zero ha hr hendpoint
  have hrowZeroAligned :
      (orbitFourWeightedTightColumns multiplier tightDir) 0
        = (![0, a, scale * a, 0] : Fin 4 → ℝ) := by
    simpa only [hrAlign] using hrowZero
  have hrowThreeAligned :
      (orbitFourWeightedTightColumns multiplier tightDir) 3
        = (![0, c, scale * c, 0] : Fin 4 → ℝ) := by
    simpa only [hfAlign] using hrowThree
  exact crux.false_of_orbitFour_alignedRows hfamily hdata
    hrowZeroAligned hrowOne hrowTwo hrowThreeAligned hrowFour hrowFive
    ha hc hy hb he hk hz


end Gtz
