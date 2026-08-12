import Gtz.Quantitative.FourActiveCoefficientProjection
import Gtz.Wave.TypeEightProjectionTraceFloor
import Gtz.Wave.OrbitFourTypeNineSupportExit

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

noncomputable def fourFamilyNormalizedRow
    (columns : Matrix (Fin 6) (Fin 4) ℝ) (atomIndex : Fin 6) : Fin 4 → ℝ :=
  Real.sqrt 6 • columns atomIndex

theorem fourFamilyWeightedTightColumns_row_norm
    {activeFamily : Finset (Finset (Fin 6))}
    {projection : Matrix (Fin 6) (Fin 6) ℝ}
    {weight : Fin 6 → ℝ} {value : ℝ}
    (label : Fin 4 → Finset (Fin 6))
    (hrange : Finset.univ.image label = activeFamily)
    (hinjective : Function.Injective label)
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3 projection weight value activeFamily
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    (atomIndex : Fin 6) :
    (fourFamilyWeightedTightColumns label multiplier tightDir) atomIndex ⬝ᵥ
      (fourFamilyWeightedTightColumns label multiplier tightDir) atomIndex = 1 / 6 := by
  let B := fourFamilyWeightedTightColumns label multiplier tightDir
  have hgram : B * B.transpose =
      chartMultiplierAssembly activeFamily multiplier tightDir := by
    apply fourFamilyWeightedTightColumns_mul_transpose
      activeFamily label hrange hinjective
    exact hdata.activeWeight_nonneg
  have hentry := congrFun (congrFun hgram atomIndex) atomIndex
  have hdiag := hdata.assembly_diagonal atomIndex
  calc
    B atomIndex ⬝ᵥ B atomIndex = (B * B.transpose) atomIndex atomIndex := by
      simp only [dotProduct, Matrix.mul_apply, Matrix.transpose_apply]
    _ = chartMultiplierAssembly activeFamily multiplier tightDir atomIndex atomIndex := hentry
    _ = 1 / 6 := by simpa [one_div] using hdiag

theorem fourFamilyNormalizedRow_unit
    {activeFamily : Finset (Finset (Fin 6))}
    {projection : Matrix (Fin 6) (Fin 6) ℝ}
    {weight : Fin 6 → ℝ} {value : ℝ}
    (label : Fin 4 → Finset (Fin 6))
    (hrange : Finset.univ.image label = activeFamily)
    (hinjective : Function.Injective label)
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3 projection weight value activeFamily
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    (atomIndex : Fin 6) :
    fourFamilyNormalizedRow
        (fourFamilyWeightedTightColumns label multiplier tightDir) atomIndex ⬝ᵥ
      fourFamilyNormalizedRow
        (fourFamilyWeightedTightColumns label multiplier tightDir) atomIndex = 1 := by
  have hnorm := fourFamilyWeightedTightColumns_row_norm
    label hrange hinjective hdata atomIndex
  have hsqrt : (Real.sqrt (6 : ℝ)) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  simp only [fourFamilyNormalizedRow, smul_dotProduct, dotProduct_smul, smul_eq_mul]
  nlinarith

/-- **PERMUTATION-INVARIANT TYPE-EIGHT EXIT.**  Any exact four-active crux
whose multiplier-weighted tight-column supports are a relabeling of
`{12,013,023,045}` has captured trace at least `1/6`, contradicting its
negative chart value. -/
theorem SixThreeCrux.false_of_fourFamily_typeEightSupports
    (crux : SixThreeCrux)
    (family : Finset (Finset (Fin 6)))
    (label : Fin 4 → Finset (Fin 6))
    (hrange : Finset.univ.image label = family)
    (hinjective : Function.Injective label)
    (relabel : Equiv.Perm (Fin 6))
    {multiplier : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design) = family)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir)
    (hsupportZero : orbitFourWeightedColumnSupport
      (fourFamilyWeightedTightColumns label multiplier tightDir) 0
        = {relabel 1, relabel 2})
    (hsupportOne : orbitFourWeightedColumnSupport
      (fourFamilyWeightedTightColumns label multiplier tightDir) 1
        = {relabel 0, relabel 1, relabel 3})
    (hsupportTwo : orbitFourWeightedColumnSupport
      (fourFamilyWeightedTightColumns label multiplier tightDir) 2
        = {relabel 0, relabel 2, relabel 3})
    (hsupportThree : orbitFourWeightedColumnSupport
      (fourFamilyWeightedTightColumns label multiplier tightDir) 3
        = {relabel 0, relabel 4, relabel 5}) :
    False := by
  classical
  let point := chartPointOfDesign crux.design
  let P := point.chart
  let B := fourFamilyWeightedTightColumns label multiplier tightDir
  let row (atomIndex : Fin 6) := fourFamilyNormalizedRow B (relabel atomIndex)
  have hdataFamily : IsChartStationaryData 3 P point.weight
      (chartObjective point) family
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir := by
    simpa only [P, point, hfamily] using hdata
  have hunit (atomIndex : Fin 6) : row atomIndex ⬝ᵥ row atomIndex = 1 := by
    exact fourFamilyNormalizedRow_unit label hrange hinjective hdataFamily (relabel atomIndex)
  obtain ⟨L, M, hleft, hrepresentation, hsymm, hidem, htrace⟩ :=
    crux.exists_fourFamily_coefficientProjection family label hrange hinjective hfamily hdata
  have hzero (column : Fin 4) (atomIndex : Fin 6)
      (hnot : atomIndex ∉ orbitFourWeightedColumnSupport B column) :
      B atomIndex column = 0 :=
    orbitFourWeightedColumn_eq_zero_of_not_mem B column atomIndex hnot
  have hfloor : 1 ≤ Matrix.trace (M *
      (atomMatrix (row 1) + atomMatrix (row 2) + atomMatrix (row 3) +
        atomMatrix (row 4) + atomMatrix (row 5) + atomMatrix (row 0))) := by
    apply typeEight_projection_trace_floor
      (row 1) (row 2) (row 3) (row 4) (row 5) (row 0)
      (hunit 1) (hunit 2) (hunit 3) (hunit 4) (hunit 5)
    · simp [row, fourFamilyNormalizedRow, B,
        hzero 2 (relabel 1) (by rw [hsupportTwo]; simp)]
    · simp [row, fourFamilyNormalizedRow, B,
        hzero 3 (relabel 1) (by rw [hsupportThree]; simp)]
    · simp [row, fourFamilyNormalizedRow, B,
        hzero 1 (relabel 2) (by rw [hsupportOne]; simp)]
    · simp [row, fourFamilyNormalizedRow, B,
        hzero 3 (relabel 2) (by rw [hsupportThree]; simp)]
    · simp [row, fourFamilyNormalizedRow, B,
        hzero 0 (relabel 3) (by rw [hsupportZero]; simp)]
    · simp [row, fourFamilyNormalizedRow, B,
        hzero 3 (relabel 3) (by rw [hsupportThree]; simp)]
    · exact ⟨
        by simp [row, fourFamilyNormalizedRow, B,
          hzero 0 (relabel 4) (by rw [hsupportZero]; simp)],
        by simp [row, fourFamilyNormalizedRow, B,
          hzero 1 (relabel 4) (by rw [hsupportOne]; simp)],
        by simp [row, fourFamilyNormalizedRow, B,
          hzero 2 (relabel 4) (by rw [hsupportTwo]; simp)]⟩
    · exact ⟨
        by simp [row, fourFamilyNormalizedRow, B,
          hzero 0 (relabel 5) (by rw [hsupportZero]; simp)],
        by simp [row, fourFamilyNormalizedRow, B,
          hzero 1 (relabel 5) (by rw [hsupportOne]; simp)],
        by simp [row, fourFamilyNormalizedRow, B,
          hzero 2 (relabel 5) (by rw [hsupportTwo]; simp)]⟩
    · exact hsymm
    · exact hidem
    · exact htrace
  have hsqrt : (Real.sqrt (6 : ℝ)) ^ 2 = 6 := Real.sq_sqrt (by norm_num)
  have hframe :
      atomMatrix (row 1) + atomMatrix (row 2) + atomMatrix (row 3) +
          atomMatrix (row 4) + atomMatrix (row 5) + atomMatrix (row 0)
        = (6 : ℝ) • (B.transpose * B) := by
    calc
      _ = ∑ atomIndex : Fin 6, atomMatrix (row atomIndex) := by
        rw [Fin.sum_univ_six]
        abel
      _ = ∑ atomIndex : Fin 6,
          atomMatrix (fourFamilyNormalizedRow B atomIndex) := by
        exact Equiv.sum_comp relabel
          (fun atomIndex => atomMatrix (fourFamilyNormalizedRow B atomIndex))
      _ = (6 : ℝ) • (B.transpose * B) := by
        rw [transpose_mul_self_eq_sum_rows]
        dsimp only [fourFamilyNormalizedRow]
        simp_rw [atomMatrix_smul, hsqrt]
        rw [Finset.smul_sum]
  rw [hframe, Matrix.mul_smul, Matrix.trace_smul, smul_eq_mul] at hfloor
  have hcoefficientFloor : 1 / 6 ≤ Matrix.trace (M * (B.transpose * B)) := by
    nlinarith
  have htraceTransport :
      Matrix.trace (M * (B.transpose * B)) =
        Matrix.trace (P * (B * B.transpose)) := by
    calc
      Matrix.trace (M * (B.transpose * B))
          = Matrix.trace ((B.transpose * B) * M) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (B.transpose * (B * M)) := by simp only [Matrix.mul_assoc]
      _ = Matrix.trace (B.transpose * (P * B)) := by rw [← hrepresentation]
      _ = Matrix.trace ((P * B) * B.transpose) := Matrix.trace_mul_comm _ _
      _ = Matrix.trace (P * (B * B.transpose)) := by simp only [Matrix.mul_assoc]
  have hgram : B * B.transpose = chartMultiplierAssembly family multiplier tightDir := by
    exact fourFamilyWeightedTightColumns_mul_transpose family label hrange hinjective
      multiplier tightDir hdataFamily.activeWeight_nonneg
  have hcaptured : Matrix.trace (P * (B * B.transpose)) =
      chartObjective point + 1 / 6 := by
    rw [hgram]
    simpa [one_div] using
      trace_projection_mul_multiplier_of_isChartStationaryData hdataFamily
  have hnegative : chartObjective point < 0 := by
    simpa only [point] using crux.hasNegativeChartValue
  rw [htraceTransport, hcaptured] at hcoefficientFloor
  linarith


end Gtz
