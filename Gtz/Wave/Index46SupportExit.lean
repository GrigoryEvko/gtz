import Gtz.Wave.Index46CruxExit
import Gtz.Wave.Index46EndpointTrace
import Gtz.Wave.OrbitFourTypeNineSupportExit
import Gtz.Wave.CriticalBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- The nonsingular endpoint-plane exit, connected to the actual stationary
coefficient projection for the index-46 family. -/
theorem SixThreeCrux.false_of_indexFortySix_endpointRows
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
    {c k p l q : ℝ}
    (hrowOne : fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir 1 =
      (![0, c, 0, 0] : Fin 4 → ℝ))
    (hrowFour : fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir 4 =
      (![0, 0, k, p] : Fin 4 → ℝ))
    (hrowFive : fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir 5 =
      (![0, 0, l, q] : Fin 4 → ℝ))
    (hc : c ≠ 0) (hdet : k * q - p * l ≠ 0) : False := by
  classical
  let point := chartPointOfDesign crux.design
  let P := point.chart
  let B := fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir
  let value := chartObjective point
  let d (atomIndex : Fin 6) := value + point.weight atomIndex
  change B 1 = (![0, c, 0, 0] : Fin 4 → ℝ) at hrowOne
  change B 4 = (![0, 0, k, p] : Fin 4 → ℝ) at hrowFour
  change B 5 = (![0, 0, l, q] : Fin 4 → ℝ) at hrowFive
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
      (row : Fin 4 → ℝ) (hrow : B atomIndex = row)
      (hmem : atomIndex ∈ indexFortySixLabel column) :
      (M *ᵥ row) column = d atomIndex * row column := by
    apply coefficient_mulVec_row_apply_of_local hsymm hrepresentation
      (scale := 1) (row := row)
    · simpa using hrow
    · norm_num
    · exact himage column atomIndex hmem
  let rowOne : Fin 4 → ℝ := ![0, c, 0, 0]
  let rowFour : Fin 4 → ℝ := ![0, 0, k, p]
  let rowFive : Fin 4 → ℝ := ![0, 0, l, q]
  have honeLocal := hlocal 1 1 rowOne (by simpa only [rowOne] using hrowOne) (by
    simp [indexFortySixLabel, chartZeroOneThree])
  have hfourTwoLocal := hlocal 4 2 rowFour (by simpa only [rowFour] using hrowFour) (by
    simp [indexFortySixLabel, chartZeroFourFive])
  have hfourThreeLocal := hlocal 4 3 rowFour (by simpa only [rowFour] using hrowFour) (by
    simp [indexFortySixLabel, indexFortySixBlockTwoFourFive])
  have hfiveTwoLocal := hlocal 5 2 rowFive (by simpa only [rowFive] using hrowFive) (by
    simp [indexFortySixLabel, chartZeroFourFive])
  have hfiveThreeLocal := hlocal 5 3 rowFive (by simpa only [rowFive] using hrowFive) (by
    simp [indexFortySixLabel, indexFortySixBlockTwoFourFive])
  norm_num [rowOne, rowFour, rowFive, Matrix.mulVec, dotProduct,
    Fin.sum_univ_four, Matrix.cons_val', Matrix.cons_val_zero,
    Matrix.cons_val_one, Matrix.cons_val_two, Matrix.cons_val_three,
    Matrix.head_cons, Matrix.empty_val', Matrix.cons_val_fin_one,
    Matrix.head_fin_const, Matrix.tail_cons, Matrix.of_apply] at honeLocal hfourTwoLocal hfourThreeLocal hfiveTwoLocal hfiveThreeLocal
  have h23 := congrFun (congrFun hsymm (2 : Fin 4)) (3 : Fin 4)
  simp only [Matrix.transpose_apply] at h23
  have hdiagOne : M 1 1 = d 1 := honeLocal.resolve_right hc
  have hone : c * M 1 1 = d 1 * c := by
    rw [hdiagOne]
    ring
  have hfourTwo : k * M 2 2 + p * M 3 2 = d 4 * k := by
    linear_combination hfourTwoLocal + p * h23
  have hfourThree : k * M 2 3 + p * M 3 3 = d 4 * p := by
    linear_combination hfourThreeLocal - k * h23
  have hfiveTwo : l * M 2 2 + q * M 3 2 = d 5 * l := by
    linear_combination hfiveTwoLocal + q * h23
  have hfiveThree : l * M 2 3 + q * M 3 3 = d 5 * q := by
    linear_combination hfiveThreeLocal - l * h23
  have hfloor (atomIndex : Fin 6) : 0 ≤ d atomIndex := by
    have h := weight_ge_neg_value_of_isChartStationaryData hdata atomIndex
    change -value ≤ point.weight atomIndex at h
    simp only [d]
    linarith
  have hshiftedSum : d 0 + d 1 + d 2 + d 3 + d 4 + d 5 < 1 := by
    have hsum := hdata.weight_sum_one
    rw [Fin.sum_univ_six] at hsum
    have hnegative : value < 0 := by
      simpa only [value, point] using crux.hasNegativeChartValue
    simp only [d]
    linarith only [hsum, hnegative]
  exact false_of_indexFortySix_endpointPlane hsymm hidem hc hdet
    (hfloor 0) (hfloor 2) (hfloor 3) hone hfourTwo hfourThree
    hfiveTwo hfiveThree htrace hshiftedSum

/-- **SUPPORT-ONLY INDEX-46 EXIT.**  The endpoint determinant splits the two
possible phases.  A nonsingular endpoint plane is killed by trace; a singular
plane makes the two endpoint rows proportional and enters the c-free
commutation exit. -/
theorem SixThreeCrux.false_of_indexFortySix_supports
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
    (hsupportZero : orbitFourWeightedColumnSupport
      (fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir) 0 = {0, 2})
    (hsupportOne : orbitFourWeightedColumnSupport
      (fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir) 1 = {0, 1, 3})
    (hsupportTwo : orbitFourWeightedColumnSupport
      (fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir) 2 = {0, 4, 5})
    (hsupportThree : orbitFourWeightedColumnSupport
      (fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir) 3 = {2, 4, 5}) :
    False := by
  classical
  let B := fourFamilyWeightedTightColumns indexFortySixLabel multiplier tightDir
  change orbitFourWeightedColumnSupport B 0 = {0, 2} at hsupportZero
  change orbitFourWeightedColumnSupport B 1 = {0, 1, 3} at hsupportOne
  change orbitFourWeightedColumnSupport B 2 = {0, 4, 5} at hsupportTwo
  change orbitFourWeightedColumnSupport B 3 = {2, 4, 5} at hsupportThree
  have hzero (label : Fin 4) (atomIndex : Fin 6)
      (hnot : atomIndex ∉ orbitFourWeightedColumnSupport B label) :
      B atomIndex label = 0 :=
    orbitFourWeightedColumn_eq_zero_of_not_mem B label atomIndex hnot
  have hnonzero (label : Fin 4) (atomIndex : Fin 6)
      (hmem : atomIndex ∈ orbitFourWeightedColumnSupport B label) :
      B atomIndex label ≠ 0 :=
    orbitFourWeightedColumn_ne_zero_of_mem B label atomIndex hmem
  have h03 : B 0 3 = 0 := hzero 3 0 (by rw [hsupportThree]; decide)
  have h10 : B 1 0 = 0 := hzero 0 1 (by rw [hsupportZero]; decide)
  have h12 : B 1 2 = 0 := hzero 2 1 (by rw [hsupportTwo]; decide)
  have h13 : B 1 3 = 0 := hzero 3 1 (by rw [hsupportThree]; decide)
  have h21 : B 2 1 = 0 := hzero 1 2 (by rw [hsupportOne]; decide)
  have h22 : B 2 2 = 0 := hzero 2 2 (by rw [hsupportTwo]; decide)
  have h30 : B 3 0 = 0 := hzero 0 3 (by rw [hsupportZero]; decide)
  have h32 : B 3 2 = 0 := hzero 2 3 (by rw [hsupportTwo]; decide)
  have h33 : B 3 3 = 0 := hzero 3 3 (by rw [hsupportThree]; decide)
  have h40 : B 4 0 = 0 := hzero 0 4 (by rw [hsupportZero]; decide)
  have h41 : B 4 1 = 0 := hzero 1 4 (by rw [hsupportOne]; decide)
  have h50 : B 5 0 = 0 := hzero 0 5 (by rw [hsupportZero]; decide)
  have h51 : B 5 1 = 0 := hzero 1 5 (by rw [hsupportOne]; decide)
  have hu : B 0 0 ≠ 0 := hnonzero 0 0 (by rw [hsupportZero]; decide)
  have hv : B 0 1 ≠ 0 := hnonzero 1 0 (by rw [hsupportOne]; decide)
  have hw : B 0 2 ≠ 0 := hnonzero 2 0 (by rw [hsupportTwo]; decide)
  have hs : B 1 1 ≠ 0 := hnonzero 1 1 (by rw [hsupportOne]; decide)
  have hr : B 2 0 ≠ 0 := hnonzero 0 2 (by rw [hsupportZero]; decide)
  have ht : B 2 3 ≠ 0 := hnonzero 3 2 (by rw [hsupportThree]; decide)
  have hs3 : B 3 1 ≠ 0 := hnonzero 1 3 (by rw [hsupportOne]; decide)
  have hk : B 4 2 ≠ 0 := hnonzero 2 4 (by rw [hsupportTwo]; decide)
  have hp : B 4 3 ≠ 0 := hnonzero 3 4 (by rw [hsupportThree]; decide)
  have hl : B 5 2 ≠ 0 := hnonzero 2 5 (by rw [hsupportTwo]; decide)
  have hq : B 5 3 ≠ 0 := hnonzero 3 5 (by rw [hsupportThree]; decide)
  let u := B 0 0
  let v := B 0 1
  let w := B 0 2
  let s := B 1 1
  let r := B 2 0
  let t := B 2 3
  let s3 := B 3 1
  let k := B 4 2
  let p := B 4 3
  let l := B 5 2
  let q := B 5 3
  have hrowOne : B 1 = (![0, s, 0, 0] : Fin 4 → ℝ) := by
    funext column
    fin_cases column <;> simp [s, h10, h12, h13]
  have hrowFour : B 4 = (![0, 0, k, p] : Fin 4 → ℝ) := by
    funext column
    fin_cases column <;> simp [k, p, h40, h41]
  have hrowFive : B 5 = (![0, 0, l, q] : Fin 4 → ℝ) := by
    funext column
    fin_cases column <;> simp [l, q, h50, h51]
  by_cases hdet : k * q - p * l = 0
  · let a := v / u
    let b := w / u
    let c := t / r
    let z := p / k
    have hu' : u ≠ 0 := by simpa only [u] using hu
    have hr' : r ≠ 0 := by simpa only [r] using hr
    have hk' : k ≠ 0 := by simpa only [k] using hk
    have hua : u * a = v := by
      dsimp only [a]
      field_simp
    have hub : u * b = w := by
      dsimp only [b]
      field_simp
    have hrc : r * c = t := by
      dsimp only [c]
      field_simp
    have hkz : k * z = p := by
      dsimp only [z]
      field_simp
    have hrowZero : B 0 = u • indexFortySixRowZero a b := by
      funext column
      fin_cases column <;> simp [u, v, w, indexFortySixRowZero, h03, hua, hub]
    have hrowTwo : B 2 = r • indexFortySixRowTwo c := by
      funext column
      fin_cases column <;> simp [r, t, indexFortySixRowTwo, h21, h22, hrc]
    have hrowThree : B 3 = s3 • indexFortySixRowOne := by
      funext column
      fin_cases column <;> simp [s3, indexFortySixRowOne, h30, h32, h33]
    have hrowFourScaled : B 4 = k • indexFortySixRowWing z := by
      funext column
      fin_cases column <;> simp [k, p, indexFortySixRowWing, h40, h41, hkz]
    have hqRelation : l * z = q := by
      dsimp only [z]
      field_simp [hk']
      nlinarith only [hdet]
    have hrowFiveScaled : B 5 = l • indexFortySixRowWing z := by
      funext column
      fin_cases column <;>
        simp [l, q, indexFortySixRowWing, h50, h51, hqRelation]
    have hrowOneScaled : B 1 = s • indexFortySixRowOne := by
      funext column
      fin_cases column <;> simp [s, indexFortySixRowOne, h10, h12, h13]
    apply crux.false_of_indexFortySix_scaledRows hfamily hdata
      hrowZero hrowOneScaled hrowTwo hrowThree hrowFourScaled hrowFiveScaled
      hu hs hr hs3 hk hl
    · exact div_ne_zero hv hu
    · exact div_ne_zero hw hu
    · exact div_ne_zero ht hr
    · exact div_ne_zero hp hk
  · exact crux.false_of_indexFortySix_endpointRows hfamily hdata
      hrowOne hrowFour hrowFive hs hdet

/-- Positive multiplier scaling preserves the exact ambient support for the
index-46 enumeration. -/
theorem indexFortySixWeightedColumnSupport_eq_totalTightSupport
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (multiplier : Finset (Fin 6) → ℝ)
    (label : Fin 4)
    (hpositive : 0 < multiplier (indexFortySixLabel label)) :
    orbitFourWeightedColumnSupport
        (fourFamilyWeightedTightColumns indexFortySixLabel multiplier
          (ambientTightSelection tightVec)) label
      = totalTightSupport tightVec (indexFortySixLabel label) := by
  classical
  have hcard : (indexFortySixLabel label).card = 3 := by
    fin_cases label <;> decide
  have hroot : Real.sqrt (multiplier (indexFortySixLabel label)) ≠ 0 :=
    ne_of_gt (Real.sqrt_pos.2 hpositive)
  ext atomIndex
  rw [orbitFourWeightedColumnSupport_mem_iff,
    ← totalEigenSquareRow_ne_zero_iff_mem_totalTightSupport tightVec hcard,
    totalEigenSquareRow_eq_ambientTightSelection_mul_self tightVec hcard]
  simp only [fourFamilyWeightedTightColumns]
  constructor
  · intro hproduct
    have hambient :
        ambientTightSelection tightVec (indexFortySixLabel label) atomIndex ≠ 0 := by
      exact (mul_ne_zero_iff.mp hproduct).2
    exact mul_ne_zero hambient hambient
  · intro hsquare
    have hambient :
        ambientTightSelection tightVec (indexFortySixLabel label) atomIndex ≠ 0 := by
      intro hzero
      rw [hzero, zero_mul] at hsquare
      exact hsquare rfl
    exact mul_ne_zero hroot hambient

/-- At a four-active crux all four multipliers are positive, so the local
support language of the second-order spine is exactly the weighted-column
support language used by the index-46 exit. -/
theorem SixThreeCrux.indexFortySixWeightedColumnSupport_eq_totalTightSupport
    (crux : SixThreeCrux)
    {tightVec : Finset (Fin 6) → (Fin 3 → ℝ)}
    {multiplier : Finset (Fin 6) → ℝ}
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design) =
      indexFortySixFamily)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (label : Fin 4) :
    orbitFourWeightedColumnSupport
        (fourFamilyWeightedTightColumns indexFortySixLabel multiplier
          (ambientTightSelection tightVec)) label
      = totalTightSupport tightVec (indexFortySixLabel label) := by
  have hfamilyCard :
      (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4 := by
    rw [hfamily]
    decide
  have hpositive := crux.activeWeight_pos_of_identity_family_card_four
    hdata hfamilyCard
  apply Gtz.indexFortySixWeightedColumnSupport_eq_totalTightSupport
  apply hpositive
  rw [hfamily, ← indexFortySixLabel_range]
  exact Finset.mem_image.mpr ⟨label, Finset.mem_univ _, rfl⟩

/-- Total-support formulation of the complete index-46 phase exit. -/
theorem SixThreeCrux.false_of_indexFortySix_totalSupports
    (crux : SixThreeCrux)
    {tightVec : Finset (Fin 6) → (Fin 3 → ℝ)}
    {multiplier : Finset (Fin 6) → ℝ}
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design) =
      indexFortySixFamily)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (hsupportZero : totalTightSupport tightVec chartZeroOneTwo = {0, 2})
    (hsupportOne : totalTightSupport tightVec chartZeroOneThree = {0, 1, 3})
    (hsupportTwo : totalTightSupport tightVec chartZeroFourFive = {0, 4, 5})
    (hsupportThree : totalTightSupport tightVec indexFortySixBlockTwoFourFive =
      {2, 4, 5}) : False := by
  apply crux.false_of_indexFortySix_supports hfamily hdata
  · rw [crux.indexFortySixWeightedColumnSupport_eq_totalTightSupport
      hfamily hdata 0]
    exact hsupportZero
  · rw [crux.indexFortySixWeightedColumnSupport_eq_totalTightSupport
      hfamily hdata 1]
    exact hsupportOne
  · rw [crux.indexFortySixWeightedColumnSupport_eq_totalTightSupport
      hfamily hdata 2]
    exact hsupportTwo
  · rw [crux.indexFortySixWeightedColumnSupport_eq_totalTightSupport
      hfamily hdata 3]
    exact hsupportThree


end Gtz
