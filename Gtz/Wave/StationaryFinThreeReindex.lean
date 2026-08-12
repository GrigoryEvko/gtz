import Gtz.Wave.PrivateMultiplierFloor

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

variable {size rank : ℕ} {activeIndex : Type*} [DecidableEq activeIndex]
variable {projection : Matrix (Fin size) (Fin size) ℝ}
variable {weight : Fin size → ℝ} {value : ℝ}
variable {activeSet : Finset activeIndex}
variable {activeSubset : activeIndex → Finset (Fin size)}
variable {activeWeight : activeIndex → ℝ}
variable {tightDir : activeIndex → Fin size → ℝ}

/-- Reindex an exactly-three-label stationary datum by `Fin 3`, in any chosen
order of its three distinct labels. -/
theorem isChartStationaryData_finThreeReindex
    (hdata : IsChartStationaryData rank projection weight value activeSet activeSubset
      activeWeight tightDir)
    (firstLabel middleLabel lastLabel : activeIndex)
    (hfirstMiddle : firstLabel ≠ middleLabel)
    (hfirstLast : firstLabel ≠ lastLabel)
    (hmiddleLast : middleLabel ≠ lastLabel)
    (hactiveSet : activeSet = {firstLabel, middleLabel, lastLabel}) :
    IsChartStationaryData rank projection weight value
      (Finset.univ : Finset (Fin 3))
      (fun index => activeSubset (![firstLabel, middleLabel, lastLabel] index))
      (fun index => activeWeight (![firstLabel, middleLabel, lastLabel] index))
      (fun index => tightDir (![firstLabel, middleLabel, lastLabel] index)) := by
  classical
  let label : Fin 3 → activeIndex := ![firstLabel, middleLabel, lastLabel]
  let reindexedSubset : Fin 3 → Finset (Fin size) := fun index => activeSubset (label index)
  let reindexedWeight : Fin 3 → ℝ := fun index => activeWeight (label index)
  let reindexedDir : Fin 3 → Fin size → ℝ := fun index => tightDir (label index)
  have hlabelMem : ∀ index : Fin 3, label index ∈ activeSet := by
    intro index
    rw [hactiveSet]
    fin_cases index <;> simp [label]
  have hassembly :
      chartMultiplierAssembly (Finset.univ : Finset (Fin 3)) reindexedWeight reindexedDir
        = chartMultiplierAssembly activeSet activeWeight tightDir := by
    rw [hactiveSet]
    simp [chartMultiplierAssembly, reindexedWeight, reindexedDir, label,
      hfirstMiddle, hfirstLast, hmiddleLast, Fin.sum_univ_three, add_assoc]
  have hreindexed :
      IsChartStationaryData rank projection weight value
        (Finset.univ : Finset (Fin 3)) reindexedSubset reindexedWeight reindexedDir := by
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
    · intro index _
      exact hdata.activeWeight_nonneg (label index) (hlabelMem index)
    · have hsum := hdata.activeWeight_sum_one
      rw [hactiveSet] at hsum
      simpa [reindexedWeight, label, hfirstMiddle, hfirstLast, hmiddleLast,
        Fin.sum_univ_three, add_assoc] using hsum
    · intro index _
      exact hdata.activeSubset_card (label index) (hlabelMem index)
    · intro index _
      exact hdata.tightDir_unit (label index) (hlabelMem index)
    · intro index _
      exact hdata.tightDir_support (label index) (hlabelMem index)
    · intro index _
      exact hdata.tightDir_isTight (label index) (hlabelMem index)
    · intro atomIndex
      rw [hassembly]
      exact hdata.assembly_diagonal atomIndex
    · rw [hassembly]
      exact hdata.assembly_commutes
  simpa [reindexedSubset, reindexedWeight, reindexedDir, label] using hreindexed


end Gtz
