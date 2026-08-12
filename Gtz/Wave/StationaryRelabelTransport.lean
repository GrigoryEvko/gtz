import Gtz.Quantitative.CruxRelabel
import Gtz.Wave.WeightedColumnSupportBridge

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! **STATIONARY DATA TRANSPORTS ALONG A RELABELLING.**  Every field of an
identity-labelled stationary datum is a sum or an entry identity, and each
transports along an atom permutation by reindexing: the relabelled crux
carries the composed multipliers and tight directions.  This is the bridge
that fires a family-pinned leaf kill at a stabilizer image of its profile —
the last wiring of the rung-four leaf war. -/

/-- The multiplier assembly of the transported datum is the conjugated
assembly. -/
theorem chartMultiplierAssembly_relabel
    (relabelPerm : Equiv.Perm (Fin 6))
    (activeSet : Finset (Finset (Fin 6)))
    (multiplier : Finset (Fin 6) → ℝ) (tightDir : Finset (Fin 6) → Fin 6 → ℝ) :
    chartMultiplierAssembly (activeSet.image
        (fun block => block.map relabelPerm.symm.toEmbedding))
      (fun block => multiplier (block.map relabelPerm.toEmbedding))
      (fun block atomIndex => tightDir (block.map relabelPerm.toEmbedding)
        (relabelPerm atomIndex))
      = (chartMultiplierAssembly activeSet multiplier tightDir).submatrix
          relabelPerm relabelPerm := by
  classical
  ext rowIndex colIndex
  rw [Matrix.submatrix_apply, chartMultiplierAssembly_apply,
    chartMultiplierAssembly_apply]
  rw [Finset.sum_image (fun blockOne _ blockTwo _ heq =>
    Finset.map_injective relabelPerm.symm.toEmbedding heq)]
  refine Finset.sum_congr rfl fun block _ => ?_
  rw [map_toEmbedding_map_symm_toEmbedding]

/-- **THE TRANSPORT.**  An identity-labelled stationary datum for a crux
yields one for any relabelling of the crux. -/
theorem SixThreeCrux.isChartStationaryData_relabel
    (crux : SixThreeCrux) (relabelPerm : Equiv.Perm (Fin 6))
    {multiplier : Finset (Fin 6) → ℝ} {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier tightDir) :
    IsChartStationaryData 3
      (chartPointOfDesign (crux.relabel relabelPerm).design).chart
      (chartPointOfDesign (crux.relabel relabelPerm).design).weight
      (chartObjective (chartPointOfDesign (crux.relabel relabelPerm).design))
      (chartArgmaxFamily (chartPointOfDesign (crux.relabel relabelPerm).design))
      (id : Finset (Fin 6) → Finset (Fin 6))
      (fun block => multiplier (block.map relabelPerm.toEmbedding))
      (fun block atomIndex => tightDir (block.map relabelPerm.toEmbedding)
        (relabelPerm atomIndex)) := by
  classical
  have hchartEq : (chartPointOfDesign (crux.relabel relabelPerm).design).chart
      = ((chartPointOfDesign crux.design).chart).submatrix relabelPerm relabelPerm := by
    show projectionOfDesign (relabelDesign crux.design relabelPerm)
      = (projectionOfDesign crux.design).submatrix relabelPerm relabelPerm
    exact projectionOfDesign_relabelDesign crux.design relabelPerm
  have hweightEq : (chartPointOfDesign (crux.relabel relabelPerm).design).weight
      = fun atomIndex => (chartPointOfDesign crux.design).weight
          (relabelPerm atomIndex) := rfl
  have hvalueEq : chartObjective (chartPointOfDesign (crux.relabel relabelPerm).design)
      = chartObjective (chartPointOfDesign crux.design) := by
    show chartObjective (chartPointOfDesign (relabelDesign crux.design relabelPerm)) = _
    exact chartObjective_chartPointOfDesign_relabelDesign crux.design relabelPerm
  have hfamilyEq : chartArgmaxFamily (chartPointOfDesign
        (crux.relabel relabelPerm).design)
      = (chartArgmaxFamily (chartPointOfDesign crux.design)).image
          (fun block => block.map relabelPerm.symm.toEmbedding) := by
    show chartArgmaxFamily (chartPointOfDesign (relabelDesign crux.design relabelPerm)) = _
    exact chartArgmaxFamily_relabelDesign crux.design relabelPerm
  have hmemBack : ∀ block ∈ chartArgmaxFamily (chartPointOfDesign
      (crux.relabel relabelPerm).design),
      block.map relabelPerm.toEmbedding
        ∈ chartArgmaxFamily (chartPointOfDesign crux.design) := by
    intro block hblock
    rw [hfamilyEq] at hblock
    obtain ⟨source, hsourceMem, rfl⟩ := Finset.mem_image.mp hblock
    rw [map_toEmbedding_map_symm_toEmbedding]
    exact hsourceMem
  have hassemblyEq := chartMultiplierAssembly_relabel relabelPerm
    (chartArgmaxFamily (chartPointOfDesign crux.design)) multiplier tightDir
  rw [← hfamilyEq] at hassemblyEq
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hchartEq]
    show (((chartPointOfDesign crux.design).chart).submatrix
        relabelPerm relabelPerm)ᵀ = _
    rw [Matrix.transpose_submatrix, hdata.isSymmetric]
  · rw [hchartEq, Matrix.submatrix_mul_equiv, hdata.isIdempotent]
  · rw [hchartEq]
    have htrace : Matrix.trace (((chartPointOfDesign crux.design).chart).submatrix
        relabelPerm relabelPerm)
        = Matrix.trace ((chartPointOfDesign crux.design).chart) := by
      rw [Matrix.trace, Matrix.trace]
      exact Equiv.sum_comp relabelPerm
        ((chartPointOfDesign crux.design).chart.diag)
    rw [htrace]
    exact hdata.hasTraceRank
  · intro atomIndex
    rw [hweightEq]
    exact hdata.weight_pos (relabelPerm atomIndex)
  · rw [hweightEq]
    rw [← hdata.weight_sum_one]
    exact Equiv.sum_comp relabelPerm ((chartPointOfDesign crux.design).weight)
  · intro activeLabel hactive
    exact hdata.activeWeight_nonneg _ (hmemBack activeLabel hactive)
  · rw [hfamilyEq, Finset.sum_image (fun blockOne _ blockTwo _ heq =>
      Finset.map_injective relabelPerm.symm.toEmbedding heq)]
    rw [← hdata.activeWeight_sum_one]
    refine Finset.sum_congr rfl fun block _ => ?_
    rw [map_toEmbedding_map_symm_toEmbedding]
  · intro activeLabel hactive
    show activeLabel.card = 3
    have hsourceCard := hdata.activeSubset_card _ (hmemBack activeLabel hactive)
    simpa [Finset.card_map] using hsourceCard
  · intro activeLabel hactive
    have hsource := hdata.tightDir_unit _ (hmemBack activeLabel hactive)
    rw [← hsource]
    exact Equiv.sum_comp relabelPerm
      (fun atomIndex => tightDir (activeLabel.map relabelPerm.toEmbedding) atomIndex
        * tightDir (activeLabel.map relabelPerm.toEmbedding) atomIndex)
  · intro activeLabel hactive atomIndex hmiss
    refine hdata.tightDir_support _ (hmemBack activeLabel hactive)
      (relabelPerm atomIndex) ?_
    show relabelPerm atomIndex ∉ activeLabel.map relabelPerm.toEmbedding
    intro hmem
    obtain ⟨source, hsourceMem, hsourceEq⟩ := Finset.mem_map.mp hmem
    have hsame : source = atomIndex := relabelPerm.injective hsourceEq
    exact hmiss (by rw [← hsame]; exact hsourceMem)
  · intro activeLabel hactive atomIndex hatomMem
    have hsourceTight := hdata.tightDir_isTight _ (hmemBack activeLabel hactive)
      (relabelPerm atomIndex)
      (by
        show relabelPerm atomIndex ∈ activeLabel.map relabelPerm.toEmbedding
        exact Finset.mem_map_of_mem _ hatomMem)
    rw [hvalueEq]
    have hgapEq : ∀ colIndex : Fin 6,
        chartStationaryGap (chartPointOfDesign (crux.relabel relabelPerm).design).chart
            (chartPointOfDesign (crux.relabel relabelPerm).design).weight
            atomIndex colIndex
          = chartStationaryGap (chartPointOfDesign crux.design).chart
              (chartPointOfDesign crux.design).weight
              (relabelPerm atomIndex) (relabelPerm colIndex) := by
      intro colIndex
      rw [chartStationaryGap, chartStationaryGap, Matrix.sub_apply, Matrix.sub_apply,
        hchartEq, Matrix.submatrix_apply, hweightEq]
      by_cases heq : atomIndex = colIndex
      · subst heq
        simp [Matrix.diagonal_apply_eq]
      · rw [Matrix.diagonal_apply_ne _ heq,
          Matrix.diagonal_apply_ne _ (fun habs => heq (relabelPerm.injective habs))]
    have hmulEq : (chartStationaryGap
          (chartPointOfDesign (crux.relabel relabelPerm).design).chart
          (chartPointOfDesign (crux.relabel relabelPerm).design).weight
        *ᵥ fun colIndex => tightDir (activeLabel.map relabelPerm.toEmbedding)
            (relabelPerm colIndex)) atomIndex
        = (chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
          *ᵥ tightDir (activeLabel.map relabelPerm.toEmbedding))
            (relabelPerm atomIndex) := by
      show ∑ colIndex : Fin 6,
          chartStationaryGap
              (chartPointOfDesign (crux.relabel relabelPerm).design).chart
              (chartPointOfDesign (crux.relabel relabelPerm).design).weight
              atomIndex colIndex
            * tightDir (activeLabel.map relabelPerm.toEmbedding)
                (relabelPerm colIndex)
        = ∑ colIndex : Fin 6,
            chartStationaryGap (chartPointOfDesign crux.design).chart
                (chartPointOfDesign crux.design).weight
                (relabelPerm atomIndex) colIndex
              * tightDir (activeLabel.map relabelPerm.toEmbedding) colIndex
      rw [← Equiv.sum_comp relabelPerm (fun colIndex =>
        chartStationaryGap (chartPointOfDesign crux.design).chart
            (chartPointOfDesign crux.design).weight
            (relabelPerm atomIndex) colIndex
          * tightDir (activeLabel.map relabelPerm.toEmbedding) colIndex)]
      exact Finset.sum_congr rfl fun colIndex _ => by rw [hgapEq colIndex]
    rw [hmulEq, hsourceTight]
  · intro atomIndex
    rw [hassemblyEq, Matrix.submatrix_apply]
    exact hdata.assembly_diagonal (relabelPerm atomIndex)
  · rw [hassemblyEq, hchartEq, Matrix.submatrix_mul_equiv,
      Matrix.submatrix_mul_equiv, hdata.assembly_commutes]

end Gtz
