import Gtz.Wave.ZeroLeakPair

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

/-- A block-tight direction is globally tight as soon as its projection image
vanishes off the selected block.  The diagonal terms vanish there because the
direction itself is supported on the block. -/
theorem shiftedGap_mulVec_eq_zero_of_isChartTightDirection_of_projection_zero_off
    {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
    {weight tightVec : Fin size → ℝ} {value : ℝ}
    {chosenSubset : Finset (Fin size)}
    (htight : IsChartTightDirection projection weight value chosenSubset tightVec)
    (hoff : ∀ atomIndex, atomIndex ∉ chosenSubset →
      (Matrix.mulVec projection tightVec) atomIndex = 0) :
    Matrix.mulVec
      (chartStationaryGap projection weight
        - value • (1 : Matrix (Fin size) (Fin size) ℝ)) tightVec = 0 := by
  funext atomIndex
  change _ = (0 : ℝ)
  by_cases hmem : atomIndex ∈ chosenSubset
  · exact shiftedGap_mulVec_tightDirection_eq_zero_of_mem htight hmem
  · have htightZero := htight.hasSupport atomIndex hmem
    simp only [chartStationaryGap, Matrix.sub_mulVec, Pi.sub_apply,
      Matrix.mulVec_diagonal, Matrix.smul_mulVec, Matrix.one_mulVec,
      Pi.smul_apply, smul_eq_mul]
    rw [hoff atomIndex hmem, htightZero]
    ring

/-- A globally zero chart-tight leak pins the stationary floor at every nonzero
coordinate.  This is the support-independent form of the pair lemma. -/
theorem value_add_weight_eq_zero_of_shiftedGap_mulVec_eq_zero_of_nonzero
    {size : ℕ} {projection : Matrix (Fin size) (Fin size) ℝ}
    {weight tightVec : Fin size → ℝ} {value : ℝ} {chosenSubset : Finset (Fin size)}
    (hsymmetric : projectionᵀ = projection)
    (hidempotent : projection * projection = projection)
    (htight : IsChartTightDirection projection weight value chosenSubset tightVec)
    (hlower : ∀ atomIndex, 0 ≤ value + weight atomIndex)
    (hupper : ∀ atomIndex, value + weight atomIndex < 1)
    (hzero : (chartStationaryGap projection weight
      - value • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ tightVec = 0)
    {atomIndex : Fin size} (hnonzero : tightVec atomIndex ≠ 0) :
    value + weight atomIndex = 0 := by
  let leak := (chartStationaryGap projection weight
    - value • (1 : Matrix (Fin size) (Fin size) ℝ)) *ᵥ tightVec
  have hnorm := dotProduct_shiftedGap_mulVec_self_of_isChartTightDirection
    hsymmetric hidempotent htight
  change leak ⬝ᵥ leak = ∑ label : Fin size,
    (value + weight label) * (1 - value - weight label) * tightVec label ^ 2 at hnorm
  have hsumZero : ∑ label : Fin size,
      (value + weight label) * (1 - value - weight label) * tightVec label ^ 2 = 0 := by
    change leak = 0 at hzero
    rw [hzero, zero_dotProduct] at hnorm
    exact hnorm.symm
  have htermNonneg : ∀ label : Fin size,
      0 ≤ (value + weight label) * (1 - value - weight label) * tightVec label ^ 2 := by
    intro label
    exact mul_nonneg
      (mul_nonneg (hlower label) (le_of_lt (by linarith [hupper label])))
      (sq_nonneg (tightVec label))
  have htermZero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun label (_ : label ∈ (Finset.univ : Finset (Fin size))) => htermNonneg label)).mp
      hsumZero atomIndex (Finset.mem_univ atomIndex)
  have hrestPos : 0 < 1 - value - weight atomIndex := by
    linarith [hupper atomIndex]
  have hsquarePos : 0 < tightVec atomIndex ^ 2 := sq_pos_iff.mpr hnonzero
  rcases mul_eq_zero.mp htermZero with hproduct | hsquare
  · exact (mul_eq_zero.mp hproduct).resolve_right hrestPos.ne'
  · exact absurd hsquare hsquarePos.ne'

/-- Crux specialization used by the shared-edge rank-two branch. -/
theorem SixThreeCrux.weight_eq_neg_chartObjective_of_globalTight_nonzero
    (crux : SixThreeCrux) {selected : Finset (Fin 6)} {tightVec : Fin 6 → ℝ}
    (htight : IsChartTightDirection (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) selected tightVec)
    (hzero : (chartStationaryGap (chartPointOfDesign crux.design).chart
          (chartPointOfDesign crux.design).weight
        - chartObjective (chartPointOfDesign crux.design)
            • (1 : Matrix (Fin 6) (Fin 6) ℝ)) *ᵥ tightVec = 0)
    {atomIndex : Fin 6} (hnonzero : tightVec atomIndex ≠ 0) :
    crux.design.weight atomIndex =
      -chartObjective (chartPointOfDesign crux.design) := by
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  have hlower : ∀ label : Fin 6,
      0 ≤ chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight label := by
    intro label
    have hfloor := weight_ge_neg_value_of_isChartStationaryData hdata label
    linarith
  have hupper : ∀ label : Fin 6,
      chartObjective (chartPointOfDesign crux.design)
        + (chartPointOfDesign crux.design).weight label < 1 := by
    intro label
    have hweightLt := weight_lt_one crux.design (by norm_num) label
    have hvalueNeg := crux.hasNegativeChartValue
    change chartObjective (chartPointOfDesign crux.design)
      + crux.design.weight label < 1
    linarith
  have hpinned := value_add_weight_eq_zero_of_shiftedGap_mulVec_eq_zero_of_nonzero
    hdata.isSymmetric hdata.isIdempotent htight hlower hupper hzero hnonzero
  change chartObjective (chartPointOfDesign crux.design)
    + crux.design.weight atomIndex = 0 at hpinned
  linarith


end Gtz
