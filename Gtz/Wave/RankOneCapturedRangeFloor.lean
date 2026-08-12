import Gtz.Quantitative.ChartStationary
import Gtz.Design.StressFreeNormalizer

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

variable {size : ℕ} {rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → (Fin size → ℝ)}

/-- The squared coefficients of collinear projected tight directions have total
mass equal to `tr(P Xi)`. -/
theorem sum_activeWeight_mul_projectedCoefficient_sq
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (direction : Fin size → ℝ) (coefficient : activeIndex → ℝ)
    (hdirectionUnit : direction ⬝ᵥ direction = 1)
    (himage : ∀ activeLabel ∈ activeSet,
      projection *ᵥ tightDir activeLabel = coefficient activeLabel • direction) :
    ∑ activeLabel ∈ activeSet,
        activeWeight activeLabel * coefficient activeLabel ^ 2
      = value + ((size : ℝ))⁻¹ := by
  rw [← trace_projection_mul_multiplier_of_isChartStationaryData hdata,
    chartMultiplierAssembly, Matrix.mul_sum, Matrix.trace_sum]
  refine Finset.sum_congr rfl fun activeLabel hmem => ?_
  rw [Matrix.mul_smul, Matrix.trace_smul, trace_mul_atomMatrix, smul_eq_mul,
    dotProduct_mulVec_eq_image_dotProduct_self hdata.isSymmetric hdata.isIdempotent,
    himage activeLabel hmem, smul_dotProduct, dotProduct_smul, smul_eq_mul, smul_eq_mul,
    hdirectionUnit]
  ring

/-- A positive projected coefficient must see a coordinate of its active block
strictly above the stationary weight floor. -/
theorem exists_mem_value_add_weight_pos_of_projectedCoefficient_ne_zero
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (direction : Fin size → ℝ) (coefficient : activeIndex → ℝ)
    (hdirectionUnit : direction ⬝ᵥ direction = 1)
    (himage : ∀ activeLabel ∈ activeSet,
      projection *ᵥ tightDir activeLabel = coefficient activeLabel • direction)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (hcoefficient : coefficient activeLabel ≠ 0) :
    ∃ atomIndex ∈ activeSubset activeLabel, 0 < value + weight atomIndex := by
  by_contra hnone
  simp only [not_exists, not_and, not_lt] at hnone
  have hzeroOn : ∀ atomIndex ∈ activeSubset activeLabel,
      (projection *ᵥ tightDir activeLabel) atomIndex = 0 := by
    intro atomIndex hatom
    rw [projection_mulVec_tightDir_of_mem hdata hmem hatom]
    have hfloor := weight_ge_neg_value_of_isChartStationaryData hdata atomIndex
    have : value + weight atomIndex = 0 := by
      have := hnone atomIndex hatom
      linarith
    rw [this, zero_mul]
  have hdotZero : tightDir activeLabel ⬝ᵥ
      (projection *ᵥ tightDir activeLabel) = 0 := by
    rw [dotProduct]
    refine Finset.sum_eq_zero fun atomIndex _ => ?_
    by_cases hatom : atomIndex ∈ activeSubset activeLabel
    · rw [hzeroOn atomIndex hatom, mul_zero]
    · rw [hdata.tightDir_support activeLabel hmem atomIndex hatom, zero_mul]
  have himageNorm := dotProduct_mulVec_eq_image_dotProduct_self
    hdata.isSymmetric hdata.isIdempotent (tightDir activeLabel)
  rw [hdotZero, himage activeLabel hmem, smul_dotProduct, dotProduct_smul,
    smul_eq_mul, smul_eq_mul, hdirectionUnit] at himageNorm
  exact hcoefficient (sq_eq_zero_iff.mp (by nlinarith [himageNorm]))

/-- On a coordinate strictly above the weight floor, collinearity turns the
stationary diagonal into an exact transport law for squared coefficients. -/
theorem sum_incident_projectedCoefficient_sq_eq
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (direction : Fin size → ℝ) (coefficient : activeIndex → ℝ)
    (himage : ∀ activeLabel ∈ activeSet,
      projection *ᵥ tightDir activeLabel = coefficient activeLabel • direction)
    (hproduct : projection * chartMultiplierAssembly activeSet activeWeight tightDir
      = (value + ((size : ℝ))⁻¹) • atomMatrix direction)
    (atomIndex : Fin size) (hpositive : 0 < value + weight atomIndex) :
    ∑ activeLabel ∈ activeSet.filter (fun label => atomIndex ∈ activeSubset label),
        activeWeight activeLabel * coefficient activeLabel ^ 2
      = (value + ((size : ℝ))⁻¹) * (value + weight atomIndex) := by
  let incident := activeSet.filter (fun label => atomIndex ∈ activeSubset label)
  have hsquares :
      ∑ activeLabel ∈ incident,
          activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2
        = ((size : ℝ))⁻¹ := by
    have hrestrict :
        ∑ activeLabel ∈ incident,
            activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2
          = ∑ activeLabel ∈ activeSet,
              activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2 := by
      apply Finset.sum_subset (Finset.filter_subset _ _)
      intro activeLabel hmem hnotIncident
      have hnotSubset : atomIndex ∉ activeSubset activeLabel := by
        intro hcontra
        exact hnotIncident (Finset.mem_filter.mpr ⟨hmem, hcontra⟩)
      rw [hdata.tightDir_support activeLabel hmem atomIndex hnotSubset]
      ring
    rw [hrestrict, ← chartMultiplierAssembly_diagonal,
      hdata.assembly_diagonal atomIndex]
  have hterm : ∀ activeLabel ∈ incident,
      coefficient activeLabel * direction atomIndex
        = (value + weight atomIndex) * tightDir activeLabel atomIndex := by
    intro activeLabel hmem
    have hactive : activeLabel ∈ activeSet := (Finset.mem_filter.mp hmem).1
    have hatom : atomIndex ∈ activeSubset activeLabel := (Finset.mem_filter.mp hmem).2
    have hcoordinate := congrFun (himage activeLabel hactive) atomIndex
    simp only [Pi.smul_apply, smul_eq_mul] at hcoordinate
    rw [projection_mulVec_tightDir_of_mem hdata hactive hatom] at hcoordinate
    exact hcoordinate.symm
  have hscaled : direction atomIndex ^ 2
      * ∑ activeLabel ∈ incident,
          activeWeight activeLabel * coefficient activeLabel ^ 2
      = (value + weight atomIndex) ^ 2 * ((size : ℝ))⁻¹ := by
    calc
      direction atomIndex ^ 2
          * ∑ activeLabel ∈ incident,
              activeWeight activeLabel * coefficient activeLabel ^ 2
          = ∑ activeLabel ∈ incident,
              activeWeight activeLabel
                * (coefficient activeLabel * direction atomIndex) ^ 2 := by
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun activeLabel _ => by ring
      _ = ∑ activeLabel ∈ incident,
              activeWeight activeLabel
                * ((value + weight atomIndex) * tightDir activeLabel atomIndex) ^ 2 := by
                  refine Finset.sum_congr rfl fun activeLabel hmem => by
                    rw [hterm activeLabel hmem]
      _ = (value + weight atomIndex) ^ 2 * ((size : ℝ))⁻¹ := by
                  rw [← hsquares]
                  rw [Finset.mul_sum]
                  refine Finset.sum_congr rfl fun activeLabel _ => by ring
  have hproductDiagonal :=
    diagonal_projection_mul_multiplier_of_isChartStationaryData hdata atomIndex
  rw [hproduct, Matrix.smul_apply, atomMatrix, Matrix.vecMulVec_apply,
    smul_eq_mul] at hproductDiagonal
  have hinvPos : (0 : ℝ) < ((size : ℝ))⁻¹ :=
    inv_pos.mpr (size_cast_pos_of_isChartStationaryData hdata)
  have hdirectionSqPos : 0 < direction atomIndex ^ 2 := by
    have hproductPos : 0 < (value + ((size : ℝ))⁻¹)
        * (direction atomIndex * direction atomIndex) := by
      rw [hproductDiagonal]
      exact mul_pos hpositive hinvPos
    by_contra hnot
    have hzero : direction atomIndex ^ 2 = 0 :=
      le_antisymm (not_lt.mp hnot) (sq_nonneg _)
    have hmulZero : direction atomIndex * direction atomIndex = 0 := by
      nlinarith
    rw [hmulZero, mul_zero] at hproductPos
    exact (lt_irrefl 0 hproductPos)
  nlinarith [hscaled, hproductDiagonal]

/-- **RANK-ONE CAPTURE CANNOT OCCUR AT NEGATIVE VALUE.**  If every projected
tight direction lies on one unit line and the projected multiplier assembly is
the corresponding positive rank-one form, then `value >= 0`.

The proof is a support-mass transport.  Every tight row with nonzero projected
coefficient must meet a coordinate strictly above the weight floor.  At such a
coordinate the forced diagonal identifies the incident coefficient mass with
`(value + 1/size) * (value + weight)`.  Double-counting incidences forces the
total shifted weight to be at least one. -/
theorem value_nonneg_of_projectedMultiplier_rankOne
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (direction : Fin size → ℝ) (coefficient : activeIndex → ℝ)
    (hdirectionUnit : direction ⬝ᵥ direction = 1)
    (himage : ∀ activeLabel ∈ activeSet,
      projection *ᵥ tightDir activeLabel = coefficient activeLabel • direction)
    (hproduct : projection * chartMultiplierAssembly activeSet activeWeight tightDir
      = (value + ((size : ℝ))⁻¹) • atomMatrix direction)
    (htracePos : 0 < value + ((size : ℝ))⁻¹) :
    0 ≤ value := by
  classical
  let shiftedWeight : Fin size → ℝ := fun atomIndex => value + weight atomIndex
  let capturedMass : activeIndex → ℝ := fun activeLabel =>
    activeWeight activeLabel * coefficient activeLabel ^ 2
  let positiveAtoms : Finset (Fin size) :=
    Finset.univ.filter (fun atomIndex => 0 < shiftedWeight atomIndex)
  let positiveDegree : activeIndex → ℕ := fun activeLabel =>
    (positiveAtoms.filter (fun atomIndex => atomIndex ∈ activeSubset activeLabel)).card
  have hmassNonneg : ∀ activeLabel ∈ activeSet, 0 ≤ capturedMass activeLabel := by
    intro activeLabel hmem
    exact mul_nonneg (hdata.activeWeight_nonneg activeLabel hmem) (sq_nonneg _)
  have hmassSum : ∑ activeLabel ∈ activeSet, capturedMass activeLabel
      = value + ((size : ℝ))⁻¹ := by
    exact sum_activeWeight_mul_projectedCoefficient_sq hdata direction coefficient
      hdirectionUnit himage
  have hdegree : ∀ activeLabel ∈ activeSet, 0 < capturedMass activeLabel →
      1 ≤ positiveDegree activeLabel := by
    intro activeLabel hmem hmassPos
    have hcoefficient : coefficient activeLabel ≠ 0 := by
      intro hzero
      simp [capturedMass, hzero] at hmassPos
    obtain ⟨atomIndex, hatom, hpositive⟩ :=
      exists_mem_value_add_weight_pos_of_projectedCoefficient_ne_zero
        hdata direction coefficient hdirectionUnit himage hmem hcoefficient
    have hmemPositive : atomIndex ∈ positiveAtoms := by
      simp only [positiveAtoms, Finset.mem_filter, Finset.mem_univ, true_and]
      exact hpositive
    have hmemDegree : atomIndex ∈
        positiveAtoms.filter (fun otherIndex => otherIndex ∈ activeSubset activeLabel) :=
      Finset.mem_filter.mpr ⟨hmemPositive, hatom⟩
    exact Finset.card_pos.mpr ⟨atomIndex, hmemDegree⟩
  have htransport : ∀ atomIndex ∈ positiveAtoms,
      ∑ activeLabel ∈ activeSet.filter
          (fun label => atomIndex ∈ activeSubset label), capturedMass activeLabel
        = (value + ((size : ℝ))⁻¹) * shiftedWeight atomIndex := by
    intro atomIndex hmem
    have hpositive : 0 < value + weight atomIndex := by
      simpa only [positiveAtoms, shiftedWeight, Finset.mem_filter, Finset.mem_univ,
        true_and] using hmem
    simpa only [capturedMass, shiftedWeight] using
      sum_incident_projectedCoefficient_sq_eq hdata direction coefficient
        himage hproduct atomIndex hpositive
  have hdoubleCount :
      ∑ atomIndex ∈ positiveAtoms,
          ∑ activeLabel ∈ activeSet.filter
            (fun label => atomIndex ∈ activeSubset label), capturedMass activeLabel
        = ∑ activeLabel ∈ activeSet,
            (positiveDegree activeLabel : ℝ) * capturedMass activeLabel := by
    simp_rw [Finset.sum_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun activeLabel hmem => ?_
    have hfilterSum :
        ∑ atomIndex ∈ positiveAtoms,
            (if atomIndex ∈ activeSubset activeLabel then capturedMass activeLabel else 0)
          = ∑ atomIndex ∈ positiveAtoms.filter
              (fun atomIndex => atomIndex ∈ activeSubset activeLabel),
                capturedMass activeLabel := by
      rw [← Finset.sum_filter]
    rw [hfilterSum, Finset.sum_const, nsmul_eq_mul]
  have hpositiveRestriction :
      ∑ atomIndex ∈ positiveAtoms, shiftedWeight atomIndex
        = ∑ atomIndex : Fin size, shiftedWeight atomIndex := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro atomIndex _ hnotPositive
    have hnot : ¬ 0 < shiftedWeight atomIndex := by
      intro hpositive
      exact hnotPositive (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hpositive⟩)
    have hfloor := weight_ge_neg_value_of_isChartStationaryData hdata atomIndex
    dsimp only [shiftedWeight]
    dsimp only [shiftedWeight] at hnot
    linarith
  have hbalance :
      (value + ((size : ℝ))⁻¹) * ∑ atomIndex : Fin size, shiftedWeight atomIndex
        = ∑ activeLabel ∈ activeSet,
            (positiveDegree activeLabel : ℝ) * capturedMass activeLabel := by
    calc
      (value + ((size : ℝ))⁻¹) * ∑ atomIndex : Fin size, shiftedWeight atomIndex
          = ∑ atomIndex ∈ positiveAtoms,
              (value + ((size : ℝ))⁻¹) * shiftedWeight atomIndex := by
                rw [← hpositiveRestriction, Finset.mul_sum]
      _ = ∑ atomIndex ∈ positiveAtoms,
              ∑ activeLabel ∈ activeSet.filter
                (fun label => atomIndex ∈ activeSubset label), capturedMass activeLabel := by
                refine Finset.sum_congr rfl fun atomIndex hmem =>
                  (htransport atomIndex hmem).symm
      _ = ∑ activeLabel ∈ activeSet,
              (positiveDegree activeLabel : ℝ) * capturedMass activeLabel := hdoubleCount
  have hmassLe :
      ∑ activeLabel ∈ activeSet, capturedMass activeLabel
        ≤ ∑ activeLabel ∈ activeSet,
            (positiveDegree activeLabel : ℝ) * capturedMass activeLabel := by
    refine Finset.sum_le_sum fun activeLabel hmem => ?_
    rcases eq_or_lt_of_le (hmassNonneg activeLabel hmem) with hzero | hpositive
    · rw [← hzero]
      simp
    · have hdegreeCast : (1 : ℝ) ≤ (positiveDegree activeLabel : ℝ) := by
        exact_mod_cast hdegree activeLabel hmem hpositive
      nlinarith [hmassNonneg activeLabel hmem]
  have hshiftedSum : ∑ atomIndex : Fin size, shiftedWeight atomIndex
      = (size : ℝ) * (value + ((size : ℝ))⁻¹) := by
    simp only [shiftedWeight, Finset.sum_add_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hdata.weight_sum_one]
    have hsizeNe : (size : ℝ) ≠ 0 :=
      ne_of_gt (size_cast_pos_of_isChartStationaryData hdata)
    field_simp
  have honeLe : 1 ≤ ∑ atomIndex : Fin size, shiftedWeight atomIndex := by
    rw [hmassSum] at hmassLe
    rw [← hbalance] at hmassLe
    nlinarith
  rw [hshiftedSum] at honeLe
  have hsizePos := size_cast_pos_of_isChartStationaryData hdata
  have hsizeNe : (size : ℝ) ≠ 0 := ne_of_gt hsizePos
  have hcancel : (size : ℝ) * ((size : ℝ))⁻¹ = 1 := mul_inv_cancel₀ hsizeNe
  rw [mul_add, hcancel] at honeLe
  nlinarith


end Gtz
