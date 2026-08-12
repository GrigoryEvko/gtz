import Gtz.Wave.Index46CFreeExit
import Gtz.Wave.FourFamilyTypeEightExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

def indexFortySixBlockTwoFourFive : Finset (Fin 6) := {2, 4, 5}

def indexFortySixLabel : Fin 4 → Finset (Fin 6) :=
  ![chartZeroOneTwo, chartZeroOneThree, chartZeroFourFive,
    indexFortySixBlockTwoFourFive]

def indexFortySixFamily : Finset (Finset (Fin 6)) :=
  {chartZeroOneTwo, chartZeroOneThree, chartZeroFourFive,
    indexFortySixBlockTwoFourFive}

theorem indexFortySixLabel_range :
    Finset.univ.image indexFortySixLabel = indexFortySixFamily := by
  decide

theorem indexFortySixLabel_injective : Function.Injective indexFortySixLabel := by
  decide

/-- Local tightness for a multiplier-weighted column in an arbitrary
four-family enumeration. -/
theorem projection_mul_fourFamilyWeightedColumn_apply
    {projection : Matrix (Fin 6) (Fin 6) ℝ}
    {weight : Fin 6 → ℝ} {value : ℝ}
    {family : Finset (Finset (Fin 6))}
    (label : Fin 4 → Finset (Fin 6))
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3 projection weight value family
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    (column : Fin 4) (atomIndex : Fin 6)
    (hactive : label column ∈ family)
    (hmem : atomIndex ∈ label column) :
    (projection * fourFamilyWeightedTightColumns label multiplier tightDir)
        atomIndex column
      = (value + weight atomIndex)
          * fourFamilyWeightedTightColumns label multiplier tightDir atomIndex column := by
  have htight := projection_mulVec_tightDir_of_mem hdata hactive hmem
  change (projection *ᵥ
      (fourFamilyWeightedTightColumns label multiplier tightDir).col column) atomIndex = _
  change (projection *ᵥ
      (Real.sqrt (multiplier (label column)) • tightDir (label column))) atomIndex = _
  rw [Matrix.mulVec_smul, Pi.smul_apply, htight]
  simp only [fourFamilyWeightedTightColumns, smul_eq_mul]
  ring

/-- A symmetric ambient projection and a symmetric coefficient representation
make the coefficient operator commute with the column Gram. -/
theorem coefficient_commutes_columnGram
    {ambient coefficient : Type*}
    [Fintype ambient] [DecidableEq ambient]
    [Fintype coefficient] [DecidableEq coefficient]
    {P : Matrix ambient ambient ℝ} {B : Matrix ambient coefficient ℝ}
    {M : Matrix coefficient coefficient ℝ}
    (hP : P.transpose = P) (hM : M.transpose = M)
    (hrepresentation : P * B = B * M) :
    M * (B.transpose * B) = (B.transpose * B) * M := by
  have htranspose := congrArg Matrix.transpose hrepresentation
  rw [Matrix.transpose_mul, Matrix.transpose_mul, hP, hM] at htranspose
  calc
    M * (B.transpose * B) = (M * B.transpose) * B := by
      simp only [Matrix.mul_assoc]
    _ = (B.transpose * P) * B := by rw [← htranspose]
    _ = B.transpose * (P * B) := by simp only [Matrix.mul_assoc]
    _ = B.transpose * (B * M) := by rw [hrepresentation]
    _ = (B.transpose * B) * M := by simp only [Matrix.mul_assoc]

/-- Six equal-norm ambient rows in the index-46 support pattern recover the
cleared row-normalized Gram used by the abstract exit. -/
theorem indexFortySix_scaledGram_eq_smul_columnGram
    {B : Matrix (Fin 6) (Fin 4) ℝ}
    {x0 x1 x2 x3 x4 x5 a b c z : ℝ}
    (hrowZero : B 0 = x0 • indexFortySixRowZero a b)
    (hrowOne : B 1 = x1 • indexFortySixRowOne)
    (hrowTwo : B 2 = x2 • indexFortySixRowTwo c)
    (hrowThree : B 3 = x3 • indexFortySixRowOne)
    (hrowFour : B 4 = x4 • indexFortySixRowWing z)
    (hrowFive : B 5 = x5 • indexFortySixRowWing z)
    (hnorm : ∀ atomIndex : Fin 6, B atomIndex ⬝ᵥ B atomIndex = 1 / 6) :
    indexFortySixScaledGram a b c z =
      (6 * (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * (1 + z ^ 2)) •
        (B.transpose * B) := by
  have hn0 := hnorm (0 : Fin 6)
  have hn1 := hnorm (1 : Fin 6)
  have hn2 := hnorm (2 : Fin 6)
  have hn3 := hnorm (3 : Fin 6)
  have hn4 := hnorm (4 : Fin 6)
  have hn5 := hnorm (5 : Fin 6)
  rw [hrowZero] at hn0
  rw [hrowOne] at hn1
  rw [hrowTwo] at hn2
  rw [hrowThree] at hn3
  rw [hrowFour] at hn4
  rw [hrowFive] at hn5
  norm_num [smul_dotProduct, dotProduct_smul, smul_eq_mul, dotProduct,
    Fin.sum_univ_four, indexFortySixRowZero, indexFortySixRowOne,
    indexFortySixRowTwo, indexFortySixRowWing, Matrix.cons_val',
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.empty_val',
    Matrix.cons_val_fin_one, Matrix.head_fin_const, Matrix.tail_cons,
    Matrix.of_apply] at hn0 hn1 hn2 hn3 hn4 hn5
  have hc0 :
      (6 * (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * (1 + z ^ 2)) * x0 ^ 2
        = (1 + c ^ 2) * (1 + z ^ 2) := by
    linear_combination 6 * (1 + c ^ 2) * (1 + z ^ 2) * hn0
  have hc1 :
      (6 * (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * (1 + z ^ 2)) * x1 ^ 2
        = (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * (1 + z ^ 2) := by
    linear_combination 6 * (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * (1 + z ^ 2) * hn1
  have hc2 :
      (6 * (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * (1 + z ^ 2)) * x2 ^ 2
        = (1 + a ^ 2 + b ^ 2) * (1 + z ^ 2) := by
    linear_combination 6 * (1 + a ^ 2 + b ^ 2) * (1 + z ^ 2) * hn2
  have hc3 :
      (6 * (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * (1 + z ^ 2)) * x3 ^ 2
        = (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * (1 + z ^ 2) := by
    linear_combination 6 * (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * (1 + z ^ 2) * hn3
  have hc4 :
      (6 * (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * (1 + z ^ 2)) * x4 ^ 2
        = (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) := by
    linear_combination 6 * (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * hn4
  have hc5 :
      (6 * (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * (1 + z ^ 2)) * x5 ^ 2
        = (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) := by
    linear_combination 6 * (1 + a ^ 2 + b ^ 2) * (1 + c ^ 2) * hn5
  have hcolumnGram : B.transpose * B =
      x0 ^ 2 • atomMatrix (indexFortySixRowZero a b)
        + x1 ^ 2 • atomMatrix indexFortySixRowOne
        + x2 ^ 2 • atomMatrix (indexFortySixRowTwo c)
        + x3 ^ 2 • atomMatrix indexFortySixRowOne
        + x4 ^ 2 • atomMatrix (indexFortySixRowWing z)
        + x5 ^ 2 • atomMatrix (indexFortySixRowWing z) := by
    ext i j
    simp only [Matrix.mul_apply, Fin.sum_univ_six, Matrix.transpose_apply,
      hrowZero, hrowOne, hrowTwo, hrowThree, hrowFour, hrowFive,
      Matrix.add_apply, Matrix.smul_apply, atomMatrix,
      Matrix.vecMulVec_apply, Pi.smul_apply, smul_eq_mul]
    ring
  rw [hcolumnGram]
  simp only [indexFortySixScaledGram, smul_add, smul_smul]
  rw [hc0, hc1, hc2, hc3, hc4, hc5]
  module

/-- Transport one ambient tightness entry through `P B = B M`, cancelling a
nonzero row scale and using coefficient symmetry. -/
theorem coefficient_mulVec_row_apply_of_local
    {P : Matrix (Fin 6) (Fin 6) ℝ}
    {B : Matrix (Fin 6) (Fin 4) ℝ}
    {M : Matrix (Fin 4) (Fin 4) ℝ}
    {atomIndex : Fin 6} {column : Fin 4}
    {row : Fin 4 → ℝ} {scale shifted : ℝ}
    (hM : M.transpose = M) (hrepresentation : P * B = B * M)
    (hrow : B atomIndex = scale • row) (hscale : scale ≠ 0)
    (hlocal : (P * B) atomIndex column = shifted * B atomIndex column) :
    (M *ᵥ row) column = shifted * row column := by
  have hentry := congrFun (congrFun hrepresentation atomIndex) column
  rw [hlocal, Matrix.mul_apply, hrow, Fin.sum_univ_four] at hentry
  simp only [Pi.smul_apply, smul_eq_mul] at hentry
  have h0 := congrFun (congrFun hM (0 : Fin 4)) column
  have h1 := congrFun (congrFun hM (1 : Fin 4)) column
  have h2 := congrFun (congrFun hM (2 : Fin 4)) column
  have h3 := congrFun (congrFun hM (3 : Fin 4)) column
  simp only [Matrix.transpose_apply] at h0 h1 h2 h3
  apply mul_left_cancel₀ hscale
  change scale * (∑ k : Fin 4, M column k * row k) =
    scale * (shifted * row column)
  rw [Fin.sum_univ_four]
  rw [h0, h1, h2, h3]
  nlinarith only [hentry]

/-- The c-free matrix exit instantiated on actual stationary weighted columns.
The six row equalities are precisely the normalized index-46 support/phase
data; no polynomial certificate or hidden coefficient relation is assumed. -/
theorem SixThreeCrux.false_of_indexFortySix_scaledRows
    (crux : SixThreeCrux)
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design) =
      indexFortySixFamily)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    {x0 x1 x2 x3 x4 x5 a b c z : ℝ}
    (hrowZero : fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir 0 =
      x0 • indexFortySixRowZero a b)
    (hrowOne : fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir 1 =
      x1 • indexFortySixRowOne)
    (hrowTwo : fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir 2 =
      x2 • indexFortySixRowTwo c)
    (hrowThree : fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir 3 =
      x3 • indexFortySixRowOne)
    (hrowFour : fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir 4 =
      x4 • indexFortySixRowWing z)
    (hrowFive : fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir 5 =
      x5 • indexFortySixRowWing z)
    (hx0 : x0 ≠ 0) (hx1 : x1 ≠ 0) (hx2 : x2 ≠ 0)
    (hx3 : x3 ≠ 0) (hx4 : x4 ≠ 0) (hx5 : x5 ≠ 0)
    (ha : a ≠ 0) (hb : b ≠ 0) (hc : c ≠ 0) (hz : z ≠ 0) : False := by
  classical
  let point := chartPointOfDesign crux.design
  let P := point.chart
  let B := fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir
  let value := chartObjective point
  let d (atomIndex : Fin 6) := value + point.weight atomIndex
  change B 0 = x0 • indexFortySixRowZero a b at hrowZero
  change B 1 = x1 • indexFortySixRowOne at hrowOne
  change B 2 = x2 • indexFortySixRowTwo c at hrowTwo
  change B 3 = x3 • indexFortySixRowOne at hrowThree
  change B 4 = x4 • indexFortySixRowWing z at hrowFour
  change B 5 = x5 • indexFortySixRowWing z at hrowFive
  have hdataFamily : IsChartStationaryData 3 P point.weight value
      indexFortySixFamily (id : Finset (Fin 6) → Finset (Fin 6))
      multiplier tightDir := by
    simpa only [P, point, value, hfamily] using hdata
  obtain ⟨L, M, hleft, hrepresentation, hsymm, hidem, htrace⟩ :=
    crux.exists_fourFamily_coefficientProjection indexFortySixFamily
      indexFortySixLabel indexFortySixLabel_range indexFortySixLabel_injective
      hfamily hdata
  have hactive (column : Fin 4) : indexFortySixLabel column ∈ indexFortySixFamily := by
    rw [← indexFortySixLabel_range]
    exact Finset.mem_image.mpr ⟨column, Finset.mem_univ _, rfl⟩
  have himage (column : Fin 4) (atomIndex : Fin 6)
      (hmem : atomIndex ∈ indexFortySixLabel column) :
      (P * B) atomIndex column = d atomIndex * B atomIndex column := by
    exact projection_mul_fourFamilyWeightedColumn_apply indexFortySixLabel
      hdataFamily column atomIndex (hactive column) hmem
  have hlocal (atomIndex : Fin 6) (column : Fin 4)
      (row : Fin 4 → ℝ) (scale : ℝ)
      (hrow : B atomIndex = scale • row) (hscale : scale ≠ 0)
      (hmem : atomIndex ∈ indexFortySixLabel column) :
      (M *ᵥ row) column = d atomIndex * row column :=
    coefficient_mulVec_row_apply_of_local hsymm hrepresentation hrow hscale
      (himage column atomIndex hmem)
  have h00 := hlocal 0 0 (indexFortySixRowZero a b) x0 hrowZero hx0 (by
    simp [indexFortySixLabel, chartZeroOneTwo])
  have h01 := hlocal 0 1 (indexFortySixRowZero a b) x0 hrowZero hx0 (by
    simp [indexFortySixLabel, chartZeroOneThree])
  have h02 := hlocal 0 2 (indexFortySixRowZero a b) x0 hrowZero hx0 (by
    simp [indexFortySixLabel, chartZeroFourFive])
  have h10 := hlocal 1 0 indexFortySixRowOne x1 hrowOne hx1 (by
    simp [indexFortySixLabel, chartZeroOneTwo])
  have h11 := hlocal 1 1 indexFortySixRowOne x1 hrowOne hx1 (by
    simp [indexFortySixLabel, chartZeroOneThree])
  have h20 := hlocal 2 0 (indexFortySixRowTwo c) x2 hrowTwo hx2 (by
    simp [indexFortySixLabel, chartZeroOneTwo])
  have h23 := hlocal 2 3 (indexFortySixRowTwo c) x2 hrowTwo hx2 (by
    simp [indexFortySixLabel, indexFortySixBlockTwoFourFive])
  have h31 := hlocal 3 1 indexFortySixRowOne x3 hrowThree hx3 (by
    simp [indexFortySixLabel, chartZeroOneThree])
  have h42 := hlocal 4 2 (indexFortySixRowWing z) x4 hrowFour hx4 (by
    simp [indexFortySixLabel, chartZeroFourFive])
  have h43 := hlocal 4 3 (indexFortySixRowWing z) x4 hrowFour hx4 (by
    simp [indexFortySixLabel, indexFortySixBlockTwoFourFive])
  have h52 := hlocal 5 2 (indexFortySixRowWing z) x5 hrowFive hx5 (by
    simp [indexFortySixLabel, chartZeroFourFive])
  let alpha := (M *ᵥ indexFortySixRowZero a b) 3
  let h := (M *ᵥ indexFortySixRowOne) 3
  let kappa := (M *ᵥ indexFortySixRowOne) 2 + z * h
  let nu := (M *ᵥ indexFortySixRowTwo c) 2
  let rho := (M *ᵥ indexFortySixRowWing z) 0
  have hrowZeroLocal : M *ᵥ indexFortySixRowZero a b =
      d 0 • indexFortySixRowZero a b + indexFortySixLeakZero alpha := by
    funext column
    fin_cases column
    · simpa [indexFortySixRowZero, indexFortySixLeakZero] using h00
    · simpa [indexFortySixRowZero, indexFortySixLeakZero] using h01
    · simpa [indexFortySixRowZero, indexFortySixLeakZero] using h02
    · simp [alpha, indexFortySixRowZero, indexFortySixLeakZero]
  have hrowOneLocal : M *ᵥ indexFortySixRowOne =
      d 1 • indexFortySixRowOne + indexFortySixLeakOneGeneral z h kappa := by
    funext column
    fin_cases column
    · simpa [indexFortySixRowOne, indexFortySixLeakOneGeneral] using h10
    · simpa [indexFortySixRowOne, indexFortySixLeakOneGeneral] using h11
    · simp [kappa, indexFortySixRowOne, indexFortySixLeakOneGeneral]
    · simp [h, indexFortySixRowOne, indexFortySixLeakOneGeneral]
  have h10sym := congrFun (congrFun hsymm (0 : Fin 4)) (1 : Fin 4)
  have h13sym := congrFun (congrFun hsymm (3 : Fin 4)) (1 : Fin 4)
  have h12sym := congrFun (congrFun hsymm (2 : Fin 4)) (1 : Fin 4)
  simp only [Matrix.transpose_apply] at h10sym h13sym h12sym
  have hM01 : M 0 1 = 0 := by
    simpa [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      indexFortySixRowOne, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.tail_cons, Matrix.of_apply] using h10
  have hhEntry : h = M 3 1 := by
    simp [h, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      indexFortySixRowOne]
  have htwoOne : (M *ᵥ indexFortySixRowTwo c) 1 = c * h := by
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      indexFortySixRowTwo, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.tail_cons, Matrix.of_apply]
    linear_combination h10sym + hM01 + c * h13sym - c * hhEntry
  have hrowTwoLocal : M *ᵥ indexFortySixRowTwo c =
      d 2 • indexFortySixRowTwo c + indexFortySixLeakTwo c h nu := by
    funext column
    fin_cases column
    · simpa [indexFortySixRowTwo, indexFortySixLeakTwo] using h20
    · simpa [indexFortySixRowTwo, indexFortySixLeakTwo] using htwoOne
    · simp [nu, indexFortySixRowTwo, indexFortySixLeakTwo]
    · simpa [indexFortySixRowTwo, indexFortySixLeakTwo] using h23
  have hwingOne : (M *ᵥ indexFortySixRowWing z) 1 = kappa := by
    have hkappaEntry : kappa = M 2 1 + z * M 3 1 := by
      simp [kappa, h, Matrix.mulVec, dotProduct, Fin.sum_univ_four,
        indexFortySixRowOne]
    norm_num [Matrix.mulVec, dotProduct, Fin.sum_univ_four,
      indexFortySixRowWing, Matrix.cons_val', Matrix.cons_val_zero,
      Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
      Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
      Matrix.head_fin_const, Matrix.tail_cons, Matrix.of_apply]
    linear_combination h12sym + z * h13sym - hkappaEntry
  have hrowWingLocal : M *ᵥ indexFortySixRowWing z =
      d 4 • indexFortySixRowWing z + indexFortySixLeakWingGeneral rho kappa := by
    funext column
    fin_cases column
    · simp [rho, indexFortySixRowWing, indexFortySixLeakWingGeneral]
    · simpa [indexFortySixRowWing, indexFortySixLeakWingGeneral] using hwingOne
    · simpa [indexFortySixRowWing, indexFortySixLeakWingGeneral] using h42
    · simpa [indexFortySixRowWing, indexFortySixLeakWingGeneral] using h43
  have hd13 : d 1 = d 3 := by
    norm_num [indexFortySixRowOne] at h11 h31
    linarith only [h11, h31]
  have hd45 : d 4 = d 5 := by
    have h42' : (M *ᵥ indexFortySixRowWing z) 2 = d 4 := by
      simpa [indexFortySixRowWing, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_fin_const, Matrix.tail_cons, Matrix.of_apply] using h42
    have h52' : (M *ᵥ indexFortySixRowWing z) 2 = d 5 := by
      simpa [indexFortySixRowWing, Matrix.cons_val', Matrix.cons_val_zero,
        Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
        Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
        Matrix.head_fin_const, Matrix.tail_cons, Matrix.of_apply] using h52
    linarith only [h42', h52']
  have hnorm (atomIndex : Fin 6) : B atomIndex ⬝ᵥ B atomIndex = 1 / 6 :=
    fourFamilyWeightedTightColumns_row_norm indexFortySixLabel
      indexFortySixLabel_range indexFortySixLabel_injective hdataFamily atomIndex
  have hscaled := indexFortySix_scaledGram_eq_smul_columnGram hrowZero hrowOne
    hrowTwo hrowThree hrowFour hrowFive hnorm
  have hcolumnCommutes := coefficient_commutes_columnGram
    (by simpa only [P] using hdata.isSymmetric) hsymm hrepresentation
  have hscaledCommutes : M * indexFortySixScaledGram a b c z =
      indexFortySixScaledGram a b c z * M := by
    rw [hscaled, Matrix.mul_smul, Matrix.smul_mul, hcolumnCommutes]
  have hd0 : 0 ≤ d 0 := by
    have hfloor := weight_ge_neg_value_of_isChartStationaryData hdata (0 : Fin 6)
    change -value ≤ point.weight 0 at hfloor
    simp only [d]
    linarith
  have hd2 : 0 ≤ d 2 := by
    have hfloor := weight_ge_neg_value_of_isChartStationaryData hdata (2 : Fin 6)
    change -value ≤ point.weight 2 at hfloor
    simp only [d]
    linarith
  have hshiftedSum : d 0 + 2 * d 1 + d 2 + 2 * d 4 < 1 := by
    have hsum := hdata.weight_sum_one
    rw [Fin.sum_univ_six] at hsum
    have hnegative : value < 0 := by
      simpa only [value, point] using crux.hasNegativeChartValue
    simp only [d] at hd13 hd45 ⊢
    linarith only [hsum, hnegative, hd13, hd45]
  exact false_of_indexFortySix_cFree hsymm hidem htrace ha hb hc hz hd0 hd2
    hshiftedSum hrowZeroLocal hrowOneLocal hrowTwoLocal hrowWingLocal
    hscaledCommutes


end Gtz
