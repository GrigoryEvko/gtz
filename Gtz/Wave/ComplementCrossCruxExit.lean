import Gtz.Wave.SharedEdgeAmbientWrapper

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

/-- **COMPLEMENTARY FULL-SUPPORT EXIT.**  At a crux, two complementary active
tight directions that are nonzero throughout their respective triples cannot
be separated by a zero projection cross block.  They become global tight
vectors, pin all six weights to `-value`, and force the forbidden endpoint
`value = -1/6`. -/
theorem SixThreeCrux.false_of_complementary_fullSupport_of_projectionCross_eq_zero
    (crux : SixThreeCrux)
    (block : Finset (Fin 6)) (hblockCard : block.card = 3)
    (hcomplementCard : blockᶜ.card = 3)
    (full complement : Fin 6 → ℝ)
    (htightFull : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block full)
    (htightComplement : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) blockᶜ complement)
    (hfullNonzero : ∀ atomIndex ∈ block, full atomIndex ≠ 0)
    (hcomplementNonzero : ∀ atomIndex, atomIndex ∉ block → complement atomIndex ≠ 0)
    (hcross :
      (chartPointOfDesign crux.design).chart.submatrix
        (block.orderEmbOfFin hblockCard)
        (blockᶜ.orderEmbOfFin hcomplementCard) = 0) :
    False := by
  let projection := (chartPointOfDesign crux.design).chart
  have hcomplementCross :
      (projection.submatrix (block.orderEmbOfFin hblockCard)
          (blockᶜ.orderEmbOfFin hcomplementCard)) *ᵥ
        (fun complementIndex =>
          complement (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) = 0 := by
    rw [hcross, Matrix.zero_mulVec]
  have hcomplementProjectionOnBlock : ∀ atomIndex ∈ block,
      (projection *ᵥ complement) atomIndex = 0 := by
    apply projection_mulVec_eq_zero_on_block_of_cross_mulVec_eq_zero
      projection block hblockCard hcomplementCard complement
    · intro atomIndex hmem
      exact htightComplement.hasSupport atomIndex (by
        simp only [Finset.mem_compl, not_not]
        exact hmem)
    · exact hcomplementCross
  have hcomplementProjectionOff : ∀ atomIndex, atomIndex ∉ blockᶜ →
      (projection *ᵥ complement) atomIndex = 0 := by
    intro atomIndex hnotMem
    apply hcomplementProjectionOnBlock atomIndex
    simpa only [Finset.mem_compl, not_not] using hnotMem
  have hcomplementZeroLeak :=
    shiftedGap_mulVec_eq_zero_of_isChartTightDirection_of_projection_zero_off
      htightComplement hcomplementProjectionOff
  have htransposeCross :
      (projection.submatrix (block.orderEmbOfFin hblockCard)
          (blockᶜ.orderEmbOfFin hcomplementCard)).transpose *ᵥ
        (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex)) = 0 := by
    rw [hcross, Matrix.transpose_zero, Matrix.zero_mulVec]
  have hfullProjectionOff : ∀ atomIndex, atomIndex ∉ block →
      (projection *ᵥ full) atomIndex = 0 := by
    apply projection_mulVec_eq_zero_off_block_of_transposeCross_mulVec_eq_zero
      projection block hblockCard hcomplementCard full
        (by simpa only [projection, chartPointOfDesign]
          using projectionOfDesign_transpose crux.design)
    · exact htightFull.hasSupport
    · exact htransposeCross
  have hfullZeroLeak :=
    shiftedGap_mulVec_eq_zero_of_isChartTightDirection_of_projection_zero_off
      htightFull hfullProjectionOff
  have hpinnedAll : ∀ atomIndex : Fin 6,
      crux.design.weight atomIndex =
        -chartObjective (chartPointOfDesign crux.design) := by
    intro atomIndex
    by_cases hmem : atomIndex ∈ block
    · exact crux.weight_eq_neg_chartObjective_of_globalTight_nonzero
        htightFull hfullZeroLeak (hfullNonzero atomIndex hmem)
    · exact crux.weight_eq_neg_chartObjective_of_globalTight_nonzero
        htightComplement hcomplementZeroLeak (hcomplementNonzero atomIndex hmem)
  have hweightSumOne := crux.design.weight_sum_one
  rw [Fin.sum_univ_six, hpinnedAll 0, hpinnedAll 1, hpinnedAll 2,
    hpinnedAll 3, hpinnedAll 4, hpinnedAll 5] at hweightSumOne
  obtain ⟨multiplier, selection, hdata⟩ := crux.exists_multiplier_isChartStationaryData
  have hstrict := neg_inv_size_lt_value_of_isChartStationaryData
    crux.design rfl crux.isChartArgmaxValue hdata
  norm_num at hstrict
  linarith


end Gtz
