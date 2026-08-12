import Gtz.Quantitative.SixThreeCrux
import Gtz.Uniform.SharedCircuitPair

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz

open Matrix Finset
open scoped BigOperators

/-- A chart-tight direction has zero shifted-gap residual on its chosen block. -/
theorem shiftedGap_mulVec_tightDirection_eq_zero_of_mem
    {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
    {weight tightVec : Fin size → ℝ} {value : ℝ} {chosenSubset : Finset (Fin size)}
    (htight : IsChartTightDirection projection weight value chosenSubset tightVec)
    {atomIndex : Fin size} (hmem : atomIndex ∈ chosenSubset) :
    ((chartStationaryGap projection weight
        - value • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ tightVec) atomIndex = 0 := by
  rw [Matrix.sub_mulVec, Pi.sub_apply, htight.isTight atomIndex hmem,
    Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply, smul_eq_mul, sub_self]

/-- The ambient off-block residual of a chart-tight direction, with the sign convention
`N = P - diag(weight) - value I`. -/
def chartTightLeak {size : ℕ} (projection : Matrix (Fin size) (Fin size) ℝ)
    (weight : Fin size → ℝ) (value : ℝ) (tightVec : Fin size → ℝ) : Fin size → ℝ :=
  (chartStationaryGap projection weight
    - value • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ tightVec

/-- The exact norm of the off-block residual of a tight direction.  Writing
`d_y = value + weight y`, orthogonal-projection geometry gives
`|leak|^2 = sum_y d_y (1-d_y) v_y^2`. -/
theorem dotProduct_shiftedGap_mulVec_self_of_isChartTightDirection
    {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
    {weight tightVec : Fin size → ℝ} {value : ℝ} {chosenSubset : Finset (Fin size)}
    (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection)
    (htight : IsChartTightDirection projection weight value chosenSubset tightVec) :
    let leak := (chartStationaryGap projection weight
      - value • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ tightVec
    leak ⬝ᵥ leak = ∑ atomIndex : Fin size,
      (value + weight atomIndex) * (1 - value - weight atomIndex)
        * tightVec atomIndex ^ 2 := by
  dsimp only
  let leak := (chartStationaryGap projection weight
    - value • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ tightVec
  let image := projection *ᵥ tightVec
  have hleakInside : ∀ atomIndex ∈ chosenSubset, leak atomIndex = 0 := by
    intro atomIndex hmem
    exact shiftedGap_mulVec_tightDirection_eq_zero_of_mem htight hmem
  have horthPointwise : ∀ atomIndex, tightVec atomIndex * leak atomIndex = 0 := by
    intro atomIndex
    by_cases hmem : atomIndex ∈ chosenSubset
    · rw [hleakInside atomIndex hmem, mul_zero]
    · rw [htight.hasSupport atomIndex hmem, zero_mul]
  have hdecompose : ∀ atomIndex,
      image atomIndex = (value + weight atomIndex) * tightVec atomIndex + leak atomIndex := by
    intro atomIndex
    simp only [image, leak, chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply,
      Matrix.mulVec_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
      smul_eq_mul]
    ring
  have hprobeImage : tightVec ⬝ᵥ image = ∑ atomIndex : Fin size,
      (value + weight atomIndex) * tightVec atomIndex ^ 2 := by
    rw [dotProduct]
    apply Finset.sum_congr rfl
    intro atomIndex _
    rw [hdecompose atomIndex]
    have hzero := horthPointwise atomIndex
    nlinarith
  have himageNorm : image ⬝ᵥ image =
      (∑ atomIndex : Fin size, (value + weight atomIndex) ^ 2 * tightVec atomIndex ^ 2)
        + leak ⬝ᵥ leak := by
    rw [dotProduct, dotProduct, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro atomIndex _
    rw [hdecompose atomIndex]
    have hzero := horthPointwise atomIndex
    have hscaledZero :
        (value + weight atomIndex) * tightVec atomIndex * leak atomIndex = 0 := by
      rw [mul_assoc, hzero, mul_zero]
    nlinarith
  have hprojection :=
    dotProduct_mulVec_eq_image_dotProduct_self hsymmetric hidempotent tightVec
  change tightVec ⬝ᵥ image = image ⬝ᵥ image at hprojection
  rw [hprobeImage, himageNorm] at hprojection
  calc
    leak ⬝ᵥ leak =
        (∑ atomIndex : Fin size,
          (value + weight atomIndex) * tightVec atomIndex ^ 2)
          - ∑ atomIndex : Fin size,
            (value + weight atomIndex) ^ 2 * tightVec atomIndex ^ 2 := by linarith
    _ = ∑ atomIndex : Fin size,
        (value + weight atomIndex) * (1 - value - weight atomIndex)
          * tightVec atomIndex ^ 2 := by
      rw [← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro atomIndex _
      ring

/-- Pointwise Pythagoras for one active direction: its projection image splits into
the shifted on-support part and its off-block leak. -/
theorem projectionImage_sq_eq_shifted_sq_add_leak_sq_of_isChartStationaryData
    {size rank : ℕ} {activeIndex : Type*}
    {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value : ℝ}
    {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
    {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {activeLabel : activeIndex} (hactive : activeLabel ∈ activeSet)
    (atomIndex : Fin size) :
    (projection *ᵥ tightDir activeLabel) atomIndex ^ 2
      = (value + weight atomIndex) ^ 2 * tightDir activeLabel atomIndex ^ 2
        + chartTightLeak projection weight value (tightDir activeLabel) atomIndex ^ 2 := by
  by_cases hmem : atomIndex ∈ activeSubset activeLabel
  · have himage := projection_mulVec_tightDir_of_mem hdata hactive hmem
    have hleak : chartTightLeak projection weight value (tightDir activeLabel) atomIndex = 0 := by
      simp only [chartTightLeak, chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply,
        Matrix.mulVec_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
        smul_eq_mul, himage]
      ring
    rw [himage, hleak, zero_pow (by norm_num), add_zero]
    ring
  · have hzero := hdata.tightDir_support activeLabel hactive atomIndex hmem
    have hleak : chartTightLeak projection weight value (tightDir activeLabel) atomIndex
        = (projection *ᵥ tightDir activeLabel) atomIndex := by
      simp only [chartTightLeak, chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply,
        Matrix.mulVec_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec, Pi.smul_apply,
        smul_eq_mul, hzero]
      ring
    rw [hzero, zero_pow (by norm_num), mul_zero, zero_add, hleak]

/-- **THE COMMUTING ASSEMBLY LEAK BUDGET.**  At each atom the multiplier-weighted
sum of squared ambient leaks is exactly
`(value + weight y)(1 - value - weight y)/size`.

This is the direct pointwise bridge from `[Xi,P]=0` to the off-block residuals. -/
theorem sum_activeWeight_mul_chartTightLeak_sq_of_isChartStationaryData
    {size rank : ℕ} {activeIndex : Type*}
    {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ} {value : ℝ}
    {activeSet : Finset activeIndex} {activeSubset : activeIndex → Finset (Fin size)}
    {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (atomIndex : Fin size) :
    ∑ activeLabel ∈ activeSet, activeWeight activeLabel
        * chartTightLeak projection weight value (tightDir activeLabel) atomIndex ^ 2
      = (value + weight atomIndex) * (1 - value - weight atomIndex)
          * ((size : ℝ))⁻¹ := by
  have hsandwichExpand :
      projection * chartMultiplierAssembly activeSet activeWeight tightDir * projection
        = ∑ activeLabel ∈ activeSet, activeWeight activeLabel
            • atomMatrix (projection *ᵥ tightDir activeLabel) := by
    rw [chartMultiplierAssembly, Matrix.mul_sum, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro activeLabel _
    rw [Matrix.mul_smul, Matrix.smul_mul]
    have hconjugate := transpose_mul_atomMatrix_mul projection (tightDir activeLabel)
    rw [hdata.isSymmetric] at hconjugate
    exact congrArg (fun target ↦ activeWeight activeLabel • target) hconjugate
  have hsandwichDiagonal :
      ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * (projection *ᵥ tightDir activeLabel) atomIndex ^ 2
        = (value + weight atomIndex) * ((size : ℝ))⁻¹ := by
    have hforced := diagonal_projection_mul_multiplier_of_isChartStationaryData
      hdata atomIndex
    have hsandwich := projection_mul_multiplier_eq_sandwich_of_isChartStationaryData hdata
    rw [hsandwich, hsandwichExpand] at hforced
    simpa only [Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul, atomMatrix,
      Matrix.vecMulVec_apply, pow_two] using hforced
  have hsplit :
      ∑ activeLabel ∈ activeSet, activeWeight activeLabel
          * (projection *ᵥ tightDir activeLabel) atomIndex ^ 2
        = (value + weight atomIndex) ^ 2 * ((size : ℝ))⁻¹
          + ∑ activeLabel ∈ activeSet, activeWeight activeLabel
              * chartTightLeak projection weight value
                  (tightDir activeLabel) atomIndex ^ 2 := by
    calc
      ∑ activeLabel ∈ activeSet, activeWeight activeLabel
            * (projection *ᵥ tightDir activeLabel) atomIndex ^ 2
          = ∑ activeLabel ∈ activeSet,
              ((value + weight atomIndex) ^ 2
                  * (activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2)
                + activeWeight activeLabel
                  * chartTightLeak projection weight value
                      (tightDir activeLabel) atomIndex ^ 2) := by
            apply Finset.sum_congr rfl
            intro activeLabel hactive
            rw [projectionImage_sq_eq_shifted_sq_add_leak_sq_of_isChartStationaryData
              hdata hactive atomIndex]
            ring
      _ = (value + weight atomIndex) ^ 2
              * (∑ activeLabel ∈ activeSet,
                activeWeight activeLabel * tightDir activeLabel atomIndex ^ 2)
            + ∑ activeLabel ∈ activeSet, activeWeight activeLabel
                * chartTightLeak projection weight value
                    (tightDir activeLabel) atomIndex ^ 2 := by
          rw [Finset.sum_add_distrib, Finset.mul_sum]
      _ = (value + weight atomIndex) ^ 2 * ((size : ℝ))⁻¹
            + ∑ activeLabel ∈ activeSet, activeWeight activeLabel
                * chartTightLeak projection weight value
                    (tightDir activeLabel) atomIndex ^ 2 := by
          rw [← chartMultiplierAssembly_diagonal,
            hdata.assembly_diagonal atomIndex]
  rw [hsplit] at hsandwichDiagonal
  linarith

/-- For a genuinely two-supported tight direction, the ambient leak vanishes exactly
when both supported coordinates saturate the stationary weight floor
`weight y = -value`.  The bounds `0 ≤ value + weight y < 1` are precisely the
projection/weight bounds used in the implication from zero norm to saturation. -/
theorem shiftedGap_mulVec_eq_zero_iff_floor_on_support_pair
    {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
    {weight tightVec : Fin size → ℝ} {value : ℝ} {chosenSubset : Finset (Fin size)}
    (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection)
    (htight : IsChartTightDirection projection weight value chosenSubset tightVec)
    {pairFirst pairSecond : Fin size} (_hpairDistinct : pairFirst ≠ pairSecond)
    (hfirstNonzero : tightVec pairFirst ≠ 0)
    (hsecondNonzero : tightVec pairSecond ≠ 0)
    (hsupport : ∀ atomIndex,
      atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)) → tightVec atomIndex = 0)
    (hlower : ∀ atomIndex, 0 ≤ value + weight atomIndex)
    (hupper : ∀ atomIndex, value + weight atomIndex < 1) :
    (chartStationaryGap projection weight
          - value • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ tightVec = 0
      ↔ value + weight pairFirst = 0 ∧ value + weight pairSecond = 0 := by
  let leak := (chartStationaryGap projection weight
    - value • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ tightVec
  have hnorm := dotProduct_shiftedGap_mulVec_self_of_isChartTightDirection
    hsymmetric hidempotent htight
  change leak ⬝ᵥ leak = ∑ atomIndex : Fin size,
    (value + weight atomIndex) * (1 - value - weight atomIndex)
      * tightVec atomIndex ^ 2 at hnorm
  have htermNonneg : ∀ atomIndex : Fin size,
      0 ≤ (value + weight atomIndex) * (1 - value - weight atomIndex)
        * tightVec atomIndex ^ 2 := by
    intro atomIndex
    exact mul_nonneg
      (mul_nonneg (hlower atomIndex) (le_of_lt (by linarith [hupper atomIndex])))
      (sq_nonneg (tightVec atomIndex))
  constructor
  · intro hleakZero
    change leak = 0 at hleakZero
    have hsumZero : ∑ atomIndex : Fin size,
        (value + weight atomIndex) * (1 - value - weight atomIndex)
          * tightVec atomIndex ^ 2 = 0 := by
      rw [hleakZero, zero_dotProduct] at hnorm
      exact hnorm.symm
    have hallTerms :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun atomIndex (_ : atomIndex ∈ (Finset.univ : Finset (Fin size))) ↦
          htermNonneg atomIndex)).mp hsumZero
    have hfirstTerm := hallTerms pairFirst (Finset.mem_univ pairFirst)
    have hsecondTerm := hallTerms pairSecond (Finset.mem_univ pairSecond)
    have hfirstSqPos : 0 < tightVec pairFirst ^ 2 := sq_pos_iff.mpr hfirstNonzero
    have hsecondSqPos : 0 < tightVec pairSecond ^ 2 := sq_pos_iff.mpr hsecondNonzero
    have hfirstRestPos : 0 < 1 - value - weight pairFirst := by
      linarith [hupper pairFirst]
    have hsecondRestPos : 0 < 1 - value - weight pairSecond := by
      linarith [hupper pairSecond]
    constructor
    · rcases mul_eq_zero.mp hfirstTerm with hproduct | hsquare
      · exact (mul_eq_zero.mp hproduct).resolve_right hfirstRestPos.ne'
      · exact absurd hsquare hfirstSqPos.ne'
    · rcases mul_eq_zero.mp hsecondTerm with hproduct | hsquare
      · exact (mul_eq_zero.mp hproduct).resolve_right hsecondRestPos.ne'
      · exact absurd hsquare hsecondSqPos.ne'
  · rintro ⟨hfirstFloor, hsecondFloor⟩
    have htermZero : ∀ atomIndex : Fin size,
        (value + weight atomIndex) * (1 - value - weight atomIndex)
          * tightVec atomIndex ^ 2 = 0 := by
      intro atomIndex
      by_cases hfirst : atomIndex = pairFirst
      · subst atomIndex
        simp [hfirstFloor]
      · by_cases hsecond : atomIndex = pairSecond
        · subst atomIndex
          simp [hsecondFloor]
        · have hnotMem : atomIndex ∉
              ({pairFirst, pairSecond} : Finset (Fin size)) := by
            simp [hfirst, hsecond]
          rw [hsupport atomIndex hnotMem, zero_pow (by norm_num), mul_zero]
    have hsumZero : ∑ atomIndex : Fin size,
        (value + weight atomIndex) * (1 - value - weight atomIndex)
          * tightVec atomIndex ^ 2 = 0 := by
      rw [Finset.sum_eq_zero]
      intro atomIndex _
      exact htermZero atomIndex
    apply eq_zero_of_dotProduct_self_eq_zero
    rw [hnorm, hsumZero]

/-- Crux-specialized form of the norm identity.  No property of the selected block
beyond tightness is needed: first-order stationarity supplies the lower bound, while
negative value and interior weights make the upper bound strict. -/
theorem SixThreeCrux.shiftedGap_mulVec_eq_zero_iff_weight_eq_neg_on_support_pair
    (crux : SixThreeCrux) {selected : Finset (Fin 6)} {tightVec : Fin 6 → ℝ}
    (htight : IsChartTightDirection (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) selected tightVec)
    {pairFirst pairSecond : Fin 6} (hpairDistinct : pairFirst ≠ pairSecond)
    (hfirstNonzero : tightVec pairFirst ≠ 0)
    (hsecondNonzero : tightVec pairSecond ≠ 0)
    (hsupport : ∀ atomIndex,
      atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin 6)) → tightVec atomIndex = 0) :
    (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          - chartObjective (chartPointOfDesign crux.design)
              • (1 : Matrix (Fin 6) (Fin 6) ℝ)) *ᵥ tightVec = 0
      ↔ crux.design.weight pairFirst
            = -chartObjective (chartPointOfDesign crux.design)
        ∧ crux.design.weight pairSecond
            = -chartObjective (chartPointOfDesign crux.design) := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  have hlower : ∀ atomIndex : Fin 6,
      0 ≤ chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex := by
    intro atomIndex
    have hfloor := weight_ge_neg_value_of_isChartStationaryData hdata atomIndex
    linarith
  have hupper : ∀ atomIndex : Fin 6,
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight atomIndex < 1 := by
    intro atomIndex
    have hweightLt : crux.design.weight atomIndex < 1 :=
      weight_lt_one crux.design (by norm_num) atomIndex
    have hvalueNeg := crux.hasNegativeChartValue
    change chartObjective (chartPointOfDesign crux.design) + crux.design.weight atomIndex < 1
    linarith
  have hiff := shiftedGap_mulVec_eq_zero_iff_floor_on_support_pair hdata.isSymmetric
    hdata.isIdempotent htight hpairDistinct hfirstNonzero hsecondNonzero hsupport
    hlower hupper
  constructor
  · intro hzero
    rcases hiff.mp hzero with ⟨hfirst, hsecond⟩
    constructor
    · change chartObjective (chartPointOfDesign crux.design)
          + crux.design.weight pairFirst = 0 at hfirst
      linarith
    · change chartObjective (chartPointOfDesign crux.design)
          + crux.design.weight pairSecond = 0 at hsecond
      linarith
  · rintro ⟨hfirst, hsecond⟩
    apply hiff.mpr
    constructor
    · change chartObjective (chartPointOfDesign crux.design)
          + crux.design.weight pairFirst = 0
      linarith
    · change chartObjective (chartPointOfDesign crux.design)
          + crux.design.weight pairSecond = 0
      linarith

/-- A negative full-gap eigenvector supported on a pair forces a parallel pair. -/
theorem hasParallelPair_of_negative_fullGapEigenvector_support_pair
    {size rank : ℕ} (hsize : 2 ≤ size) (design : WeightedDesign size rank)
    {value : ℝ} (hvalue : value < 0) {pairFirst pairSecond : Fin size}
    (hpairDistinct : pairFirst ≠ pairSecond) {tightVec : Fin size → ℝ}
    (hunit : tightVec ⬝ᵥ tightVec = 1)
    (hsupport : ∀ atomIndex, atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)) →
      tightVec atomIndex = 0)
    (hglobal : chartStationaryGap (projectionOfDesign design) design.weight *ᵥ tightVec
      = value • tightVec) :
    HasParallelPair design := by
  let kernelVec : Fin size → ℝ :=
    tightVec - projectionOfDesign design *ᵥ tightVec
  have hprojectionEigen : ∀ atomIndex,
      (projectionOfDesign design *ᵥ tightVec) atomIndex
        = (value + design.weight atomIndex) * tightVec atomIndex := by
    intro atomIndex
    have hentry := congrFun hglobal atomIndex
    simp only [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply,
      Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at hentry
    linarith
  have hkernelSupport : ∀ atomIndex,
      atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)) → kernelVec atomIndex = 0 := by
    intro atomIndex hnotMem
    simp only [kernelVec, Pi.sub_apply, hprojectionEigen atomIndex,
      hsupport atomIndex hnotMem]
    ring
  have htightVecNonzero : tightVec ≠ 0 := by
    intro hzero
    rw [hzero, dotProduct_zero] at hunit
    norm_num at hunit
  obtain ⟨witnessLabel, hwitness⟩ := Function.ne_iff.mp htightVecNonzero
  have hkernelEntry : kernelVec witnessLabel
      = (1 - value - design.weight witnessLabel) * tightVec witnessLabel := by
    simp only [kernelVec, Pi.sub_apply, hprojectionEigen witnessLabel]
    ring
  have hkernelNonzero : kernelVec ≠ 0 := by
    intro hzero
    have hentry := congrFun hzero witnessLabel
    rw [hkernelEntry] at hentry
    have hfactorPos : 0 < 1 - value - design.weight witnessLabel := by
      linarith [weight_lt_one design hsize witnessLabel]
    exact hwitness ((mul_eq_zero.mp hentry).resolve_left (ne_of_gt hfactorPos))
  have hprojectionKernel : projectionOfDesign design *ᵥ kernelVec = 0 := by
    change projectionOfDesign design *ᵥ
      (tightVec - projectionOfDesign design *ᵥ tightVec) = 0
    rw [Matrix.mulVec_sub, Matrix.mulVec_mulVec, projectionOfDesign_mul_self, sub_self]
  let dependence : Fin size → ℝ := fun atomIndex =>
    Real.sqrt (design.weight atomIndex) * kernelVec atomIndex
  have hdependenceNonzero : ∃ witnessLabel, dependence witnessLabel ≠ 0 := by
    obtain ⟨label, hlabel⟩ := Function.ne_iff.mp hkernelNonzero
    refine ⟨label, mul_ne_zero ?_ hlabel⟩
    exact (Real.sqrt_pos.mpr (design.weight_pos label)).ne'
  have hdependenceSupport : ∀ atomIndex,
      atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)) → dependence atomIndex = 0 := by
    intro atomIndex hnotMem
    simp only [dependence, hkernelSupport atomIndex hnotMem, mul_zero]
  have hscaledKernel : (scaledAtomRows design)ᵀ *ᵥ kernelVec = 0 := by
    have hframe : (scaledAtomRows design)ᵀ * projectionOfDesign design
        = (scaledAtomRows design)ᵀ := by
      rw [projectionOfDesign, ← Matrix.mul_assoc, transpose_mul_scaledAtomRows,
        Matrix.one_mul]
    have happly := congrArg (fun vec => (scaledAtomRows design)ᵀ *ᵥ vec) hprojectionKernel
    rw [Matrix.mulVec_mulVec, hframe, Matrix.mulVec_zero] at happly
    exact happly
  have hdependenceSum : (∑ atomIndex, dependence atomIndex • design.atom atomIndex) = 0 := by
    funext coord
    have hcoord := congrFun hscaledKernel coord
    simpa [dependence, scaledAtomRows, Matrix.mulVec, dotProduct, mul_assoc,
      mul_comm, mul_left_comm] using hcoord
  by_contra hnoParallel
  have hprimitive : IsPrimitiveDesign design :=
    (isPrimitiveDesign_iff_not_hasParallelPair design).2 hnoParallel
  exact CorankTwo.dependentPair_impossible_of_isPrimitive hsize design hprimitive
    ({pairFirst, pairSecond} : Finset (Fin size))
    (Finset.card_pair hpairDistinct) ⟨dependence, hdependenceNonzero,
      hdependenceSupport, hdependenceSum⟩

/-- The same result in the natural zero-leak form
`(chartStationaryGap - value * I) v = 0`. -/
theorem hasParallelPair_of_negative_zeroLeak_support_pair
    {size rank : ℕ} (hsize : 2 ≤ size) (design : WeightedDesign size rank)
    {value : ℝ} (hvalue : value < 0) {pairFirst pairSecond : Fin size}
    (hpairDistinct : pairFirst ≠ pairSecond) {tightVec : Fin size → ℝ}
    (hunit : tightVec ⬝ᵥ tightVec = 1)
    (hsupport : ∀ atomIndex, atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)) →
      tightVec atomIndex = 0)
    (hzeroLeak :
      (chartStationaryGap (projectionOfDesign design) design.weight
          - value • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ tightVec = 0) :
    HasParallelPair design := by
  have hglobal : chartStationaryGap (projectionOfDesign design) design.weight *ᵥ tightVec
      = value • tightVec := by
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] at hzeroLeak
    exact hzeroLeak
  exact hasParallelPair_of_negative_fullGapEigenvector_support_pair hsize design hvalue
    hpairDistinct hunit hsupport hglobal

/-- At a `SixThreeCrux`, a unit active tight direction supported on a pair cannot have
zero ambient leak.  `IsChartTightDirection` supplies only the block equation; the final
hypothesis is the genuinely stronger full-space equation. -/
theorem SixThreeCrux.false_of_zeroLeak_tightDirection_support_pair
    (crux : SixThreeCrux) {selected : Finset (Fin 6)}
    (_hactive : selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    {tightVec : Fin 6 → ℝ}
    (htight : IsChartTightDirection (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) selected tightVec)
    {pairFirst pairSecond : Fin 6} (hpairDistinct : pairFirst ≠ pairSecond)
    (hsupport : ∀ atomIndex,
      atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin 6)) → tightVec atomIndex = 0)
    (hzeroLeak :
      (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
          - chartObjective (chartPointOfDesign crux.design)
              • (1 : Matrix (Fin 6) (Fin 6) ℝ)) *ᵥ tightVec = 0) :
    False := by
  apply crux.hasNoParallelPair
  exact hasParallelPair_of_negative_zeroLeak_support_pair (by norm_num) crux.design
    crux.hasNegativeChartValue hpairDistinct htight.isUnit hsupport hzeroLeak

/-- Consequently the two atoms supporting a crux-tight pair cannot both saturate the
stationary floor.  Otherwise the norm identity gives zero leak, and the pair becomes
parallel. -/
theorem SixThreeCrux.not_both_weight_eq_neg_of_tightDirection_support_pair
    (crux : SixThreeCrux) {selected : Finset (Fin 6)} {tightVec : Fin 6 → ℝ}
    (hactive : selected ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (htight : IsChartTightDirection (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) selected tightVec)
    {pairFirst pairSecond : Fin 6} (hpairDistinct : pairFirst ≠ pairSecond)
    (hfirstNonzero : tightVec pairFirst ≠ 0)
    (hsecondNonzero : tightVec pairSecond ≠ 0)
    (hsupport : ∀ atomIndex,
      atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin 6)) → tightVec atomIndex = 0) :
    ¬ (crux.design.weight pairFirst
          = -chartObjective (chartPointOfDesign crux.design)
        ∧ crux.design.weight pairSecond
          = -chartObjective (chartPointOfDesign crux.design)) := by
  intro hfloor
  apply crux.false_of_zeroLeak_tightDirection_support_pair hactive htight
    hpairDistinct hsupport
  exact (crux.shiftedGap_mulVec_eq_zero_iff_weight_eq_neg_on_support_pair htight
    hpairDistinct hfirstNonzero hsecondNonzero hsupport).2 hfloor

/-! ## The exact four-row combinatorial residue -/

/-- If a coordinate axis lies in the span of exactly four rows and one of those rows
is genuinely supported on a pair containing that coordinate, then the other three rows
have a nontrivial linear combination supported on the same pair.  This is the finite
support-hypergraph condition left by the second-order row-span witness; it uses no
stationarity approximation. -/
theorem exists_nontrivial_threeRow_cancellation_off_pair
    {activeIndex : Type*} [DecidableEq activeIndex]
    {size : ℕ} (activeSet : Finset activeIndex)
    (hcard : activeSet.card = 4) (row : activeIndex → (Fin size → ℝ))
    {selected : activeIndex} (hselected : selected ∈ activeSet)
    {pairFirst pairSecond : Fin size} (hpairDistinct : pairFirst ≠ pairSecond)
    (_hselectedFirst : row selected pairFirst ≠ 0)
    (hselectedSecond : row selected pairSecond ≠ 0)
    (hselectedSupport : ∀ atomIndex,
      atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)) →
        row selected atomIndex = 0)
    (hcoordinate : ∃ coefficient : activeIndex → ℝ,
      ∑ activeLabel ∈ activeSet, coefficient activeLabel • row activeLabel
        = Pi.single pairFirst (1 : ℝ)) :
    ∃ coefficient : activeIndex → ℝ,
      (activeSet.erase selected).card = 3
        ∧ (∃ activeLabel ∈ activeSet.erase selected, coefficient activeLabel ≠ 0)
        ∧ (∑ activeLabel ∈ activeSet.erase selected,
            coefficient activeLabel • row activeLabel) ≠ 0
        ∧ ∀ atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)),
          ∑ activeLabel ∈ activeSet.erase selected,
            coefficient activeLabel * row activeLabel atomIndex = 0 := by
  classical
  obtain ⟨coefficient, hcoordinate⟩ := hcoordinate
  have heraseCombinationNonzero :
      (∑ activeLabel ∈ activeSet.erase selected,
        coefficient activeLabel • row activeLabel) ≠ 0 := by
    intro heraseZero
    have hsplit := Finset.sum_erase_add activeSet
      (fun activeLabel ↦ coefficient activeLabel • row activeLabel) hselected
    rw [heraseZero, zero_add] at hsplit
    have honlySelected : coefficient selected • row selected
        = Pi.single pairFirst (1 : ℝ) := hsplit.trans hcoordinate
    have hsecondEntry := congrFun honlySelected pairSecond
    simp only [Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne hpairDistinct.symm] at hsecondEntry
    have hcoefficientZero : coefficient selected = 0 :=
      (mul_eq_zero.mp hsecondEntry).resolve_right hselectedSecond
    have hfirstEntry := congrFun honlySelected pairFirst
    simp [hcoefficientZero] at hfirstEntry
  refine ⟨coefficient, ?_, ?_, heraseCombinationNonzero, ?_⟩
  · rw [Finset.card_erase_of_mem hselected, hcard]
  · by_contra hnone
    push Not at hnone
    have heraseZero :
        ∑ activeLabel ∈ activeSet.erase selected,
          coefficient activeLabel • row activeLabel = 0 := by
      apply Finset.sum_eq_zero
      intro activeLabel hactive
      rw [hnone activeLabel hactive, zero_smul]
    exact heraseCombinationNonzero heraseZero
  · intro atomIndex hnotPair
    have hfirstNe : atomIndex ≠ pairFirst := by
      intro heq
      apply hnotPair
      simp [heq]
    have hentry := congrFun hcoordinate atomIndex
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      Pi.single_eq_of_ne hfirstNe] at hentry
    have hsplit := Finset.sum_erase_add activeSet
      (fun activeLabel ↦ coefficient activeLabel * row activeLabel atomIndex) hselected
    rw [hselectedSupport atomIndex hnotPair, mul_zero, add_zero] at hsplit
    exact hsplit.trans hentry

/-- In the cancellation above, an outside-pair atom cannot occur in exactly one row
whose coefficient is nonzero.  Thus every used outside support is shared by another of
the three residual rows. -/
theorem exists_companion_row_of_threeRow_cancellation
    {activeIndex : Type*} [DecidableEq activeIndex]
    {size : ℕ} {remaining : Finset activeIndex}
    {row : activeIndex → (Fin size → ℝ)} {coefficient : activeIndex → ℝ}
    {pairFirst pairSecond : Fin size}
    (hcancellation : ∀ atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)),
      ∑ activeLabel ∈ remaining,
        coefficient activeLabel * row activeLabel atomIndex = 0)
    {activeLabel : activeIndex} (hactive : activeLabel ∈ remaining)
    (hcoefficient : coefficient activeLabel ≠ 0)
    {atomIndex : Fin size}
    (hnotPair : atomIndex ∉ ({pairFirst, pairSecond} : Finset (Fin size)))
    (hrow : row activeLabel atomIndex ≠ 0) :
    ∃ companion ∈ remaining, companion ≠ activeLabel
      ∧ coefficient companion ≠ 0 ∧ row companion atomIndex ≠ 0 := by
  classical
  by_contra hnone
  push Not at hnone
  have hotherZero : ∀ companion ∈ remaining, companion ≠ activeLabel →
      coefficient companion * row companion atomIndex = 0 := by
    intro companion hcompanion hne
    by_cases hcoefficientCompanion : coefficient companion = 0
    · rw [hcoefficientCompanion, zero_mul]
    · have hrowCompanion : row companion atomIndex = 0 :=
        hnone companion hcompanion hne hcoefficientCompanion
      rw [hrowCompanion, mul_zero]
  have hsingle : ∑ companion ∈ remaining,
      coefficient companion * row companion atomIndex
        = coefficient activeLabel * row activeLabel atomIndex := by
    rw [Finset.sum_eq_single activeLabel]
    · exact hotherZero
    · exact fun hnotMem ↦ absurd hactive hnotMem
  have hzero := hcancellation atomIndex hnotPair
  rw [hsingle] at hzero
  exact (mul_ne_zero hcoefficient hrow) hzero

/-- A two-row cancellation has identical nonzero support at every constrained
coordinate. -/
theorem row_ne_zero_iff_of_twoRow_cancellation
    {size : ℕ} {firstRow secondRow : Fin size → ℝ}
    {firstCoefficient secondCoefficient : ℝ}
    (hfirstCoefficient : firstCoefficient ≠ 0)
    (hsecondCoefficient : secondCoefficient ≠ 0)
    {atomIndex : Fin size}
    (hcancellation : firstCoefficient * firstRow atomIndex
      + secondCoefficient * secondRow atomIndex = 0) :
    firstRow atomIndex ≠ 0 ↔ secondRow atomIndex ≠ 0 := by
  constructor
  · intro hfirst hsecondZero
    rw [hsecondZero, mul_zero, add_zero] at hcancellation
    exact (mul_ne_zero hfirstCoefficient hfirst) hcancellation
  · intro hsecond hfirstZero
    rw [hfirstZero, mul_zero, zero_add] at hcancellation
    exact (mul_ne_zero hsecondCoefficient hsecond) hcancellation

/-- Two rows cancelling with fixed nonzero coefficients have every `2 x 2` minor
zero on the constrained coordinates. -/
theorem twoRow_minor_eq_zero_of_cancellation
    {size : ℕ} {firstRow secondRow : Fin size → ℝ}
    {firstCoefficient secondCoefficient : ℝ}
    (hfirstCoefficient : firstCoefficient ≠ 0)
    {firstAtom secondAtom : Fin size}
    (hfirstCancellation : firstCoefficient * firstRow firstAtom
      + secondCoefficient * secondRow firstAtom = 0)
    (hsecondCancellation : firstCoefficient * firstRow secondAtom
      + secondCoefficient * secondRow secondAtom = 0) :
    firstRow firstAtom * secondRow secondAtom
      = firstRow secondAtom * secondRow firstAtom := by
  have hdet : firstCoefficient
      * (firstRow firstAtom * secondRow secondAtom
        - firstRow secondAtom * secondRow firstAtom) = 0 := by
    calc
      firstCoefficient
          * (firstRow firstAtom * secondRow secondAtom
            - firstRow secondAtom * secondRow firstAtom)
        = (firstCoefficient * firstRow firstAtom
              + secondCoefficient * secondRow firstAtom) * secondRow secondAtom
            - (firstCoefficient * firstRow secondAtom
              + secondCoefficient * secondRow secondAtom) * secondRow firstAtom := by ring
      _ = 0 := by rw [hfirstCancellation, hsecondCancellation]; ring
  exact sub_eq_zero.mp ((mul_eq_zero.mp hdet).resolve_left hfirstCoefficient)

end Gtz
