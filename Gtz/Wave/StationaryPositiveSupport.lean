import Gtz.Quantitative.ChartStationary

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

variable {size rank : ℕ} {activeIndex : Type*}
variable {projection : Matrix (Fin size) (Fin size) ℝ} {weight : Fin size → ℝ}
variable {value : ℝ} {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ} {tightDir : activeIndex → (Fin size → ℝ)}

/-- The labels carrying strictly positive stationary multiplier. -/
noncomputable def positiveActiveSet (activeSet : Finset activeIndex)
    (activeWeight : activeIndex → ℝ) : Finset activeIndex :=
  activeSet.filter fun activeLabel => 0 < activeWeight activeLabel

/-- Outside the positive multiplier support, every multiplier of a stationary
datum is exactly zero. -/
theorem activeWeight_eq_zero_of_not_mem_positiveActiveSet
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    {activeLabel : activeIndex} (hmem : activeLabel ∈ activeSet)
    (hnotMem : activeLabel ∉ positiveActiveSet activeSet activeWeight) :
    activeWeight activeLabel = 0 := by
  rw [positiveActiveSet, Finset.mem_filter, not_and_or] at hnotMem
  rcases hnotMem with hnotActive | hnotPos
  · exact (hnotActive hmem).elim
  · exact le_antisymm (not_lt.mp hnotPos) (hdata.activeWeight_nonneg activeLabel hmem)

/-- Filtering out zero stationary multipliers does not change the multiplier
assembly. -/
theorem chartMultiplierAssembly_positiveActiveSet
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    chartMultiplierAssembly (positiveActiveSet activeSet activeWeight) activeWeight tightDir
      = chartMultiplierAssembly activeSet activeWeight tightDir := by
  classical
  unfold chartMultiplierAssembly
  apply Finset.sum_subset (Finset.filter_subset _ _)
  intro activeLabel hmem hnotMem
  rw [activeWeight_eq_zero_of_not_mem_positiveActiveSet hdata hmem hnotMem, zero_smul]

/-- **ZERO MULTIPLIERS MAY BE DISCARDED.**  Restricting a chart-stationary datum
to its strictly positive multiplier support preserves every field, including
the constant diagonal and the commutation equation. -/
theorem IsChartStationaryData.restrict_positiveActiveSet
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir) :
    IsChartStationaryData rank projection weight value
      (positiveActiveSet activeSet activeWeight) activeSubset activeWeight tightDir := by
  classical
  have hsubset : positiveActiveSet activeSet activeWeight ⊆ activeSet :=
    Finset.filter_subset _ _
  have hassembly := chartMultiplierAssembly_positiveActiveSet hdata
  refine
    { isSymmetric := hdata.isSymmetric
      isIdempotent := hdata.isIdempotent
      hasTraceRank := hdata.hasTraceRank
      weight_pos := hdata.weight_pos
      weight_sum_one := hdata.weight_sum_one
      activeWeight_nonneg := ?_
      activeWeight_sum_one := ?_
      activeSubset_card := ?_
      tightDir_unit := ?_
      tightDir_support := ?_
      tightDir_isTight := ?_
      assembly_diagonal := ?_
      assembly_commutes := ?_ }
  · intro activeLabel hmem
    exact hdata.activeWeight_nonneg activeLabel (hsubset hmem)
  · calc
      ∑ activeLabel ∈ positiveActiveSet activeSet activeWeight, activeWeight activeLabel
          = ∑ activeLabel ∈ activeSet, activeWeight activeLabel := by
              apply Finset.sum_subset hsubset
              intro activeLabel hmem hnotMem
              exact activeWeight_eq_zero_of_not_mem_positiveActiveSet hdata hmem hnotMem
      _ = 1 := hdata.activeWeight_sum_one
  · intro activeLabel hmem
    exact hdata.activeSubset_card activeLabel (hsubset hmem)
  · intro activeLabel hmem
    exact hdata.tightDir_unit activeLabel (hsubset hmem)
  · intro activeLabel hmem
    exact hdata.tightDir_support activeLabel (hsubset hmem)
  · intro activeLabel hmem
    exact hdata.tightDir_isTight activeLabel (hsubset hmem)
  · intro atomIndex
    rw [hassembly]
    exact hdata.assembly_diagonal atomIndex
  · rw [hassembly]
    exact hdata.assembly_commutes


end Gtz
