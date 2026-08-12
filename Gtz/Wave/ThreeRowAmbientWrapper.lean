import Gtz.Wave.SharedEdgeAmbientWrapper

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset
open scoped BigOperators

/-- **THREE-ROW SPECTRAL EXIT IN AMBIENT CHART COORDINATES.**  A full
selected-side row and any second positive row missing one of its nonzero
coordinates make the half-trace spectral complement strict.  A third row may
have merely nonnegative multiplier.  Commutation then kills both cross leaks,
and the complementary full-support pair pins the forbidden `-1/6` endpoint. -/
theorem SixThreeCrux.false_of_threeRow_spectral_blockData
    (crux : SixThreeCrux) {activeIndex : Type*}
    (activeSet : Finset activeIndex)
    (activeSubset : activeIndex → Finset (Fin 6))
    (activeWeight : activeIndex → ℝ)
    (tightDir : activeIndex → (Fin 6 → ℝ))
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      activeSet activeSubset activeWeight tightDir)
    (block : Finset (Fin 6)) (hblockCard : block.card = 3)
    (hcomplementCard : blockᶜ.card = 3)
    (full complement : Fin 6 → ℝ)
    (pair extra : Fin 3 → ℝ) (missing : Fin 3)
    (fullWeight pairWeight extraWeight : ℝ)
    (htightFull : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block full)
    (htightComplement : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) blockᶜ complement)
    (hfullUnit :
      (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex)) ⬝ᵥ
        (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex)) = 1)
    (hpairUnit : pair ⬝ᵥ pair = 1)
    (hextraUnit : extra ⬝ᵥ extra = 1)
    (hcomplementUnit :
      (fun complementIndex =>
          complement (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) ⬝ᵥ
        (fun complementIndex =>
          complement (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)) = 1)
    (hfullMissing : full (block.orderEmbOfFin hblockCard missing) ≠ 0)
    (hpairMissing : pair missing = 0)
    (hfullWeight : 0 < fullWeight) (hpairWeight : 0 < pairWeight)
    (hextraWeight : 0 ≤ extraWeight)
    (hweightSum : fullWeight + pairWeight + extraWeight = 1 / 2)
    (hfullNonzero : ∀ atomIndex ∈ block, full atomIndex ≠ 0)
    (hcomplementNonzero : ∀ atomIndex, atomIndex ∉ block → complement atomIndex ≠ 0)
    (hassemblyLeft :
      (chartMultiplierAssembly activeSet activeWeight tightDir).submatrix
          (block.orderEmbOfFin hblockCard) (block.orderEmbOfFin hblockCard) =
        fullWeight • atomMatrix
            (fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex))
          + pairWeight • atomMatrix pair + extraWeight • atomMatrix extra)
    (hassemblyCross : ∀ (inside : Fin 6), inside ∈ block →
      ∀ (outside : Fin 6), outside ∉ block →
        chartMultiplierAssembly activeSet activeWeight tightDir inside outside = 0
          ∧ chartMultiplierAssembly activeSet activeWeight tightDir outside inside = 0)
    (hassemblyComplement : ∀ (first : Fin 6), first ∉ block →
      ∀ (second : Fin 6), second ∉ block →
        chartMultiplierAssembly activeSet activeWeight tightDir first second =
          (1 / 2) * complement first * complement second) :
    False := by
  classical
  let projection := (chartPointOfDesign crux.design).chart
  let assembly := chartMultiplierAssembly activeSet activeWeight tightDir
  let cross := projection.submatrix (block.orderEmbOfFin hblockCard)
    (blockᶜ.orderEmbOfFin hcomplementCard)
  let fullRestricted : Fin 3 → ℝ :=
    fun blockIndex => full (block.orderEmbOfFin hblockCard blockIndex)
  let complementRestricted : Fin 3 → ℝ :=
    fun complementIndex =>
      complement (blockᶜ.orderEmbOfFin hcomplementCard complementIndex)
  have hintertwines :
      (fullWeight • atomMatrix fullRestricted + pairWeight • atomMatrix pair
        + extraWeight • atomMatrix extra) * cross =
        cross * ((1 / 2 : ℝ) • atomMatrix complementRestricted) := by
    have hlocalized := submatrix_intertwines_half_atomMatrix_of_commutes_of_blockSplit
      projection assembly block hblockCard hcomplementCard complement
      hdata.assembly_commutes hassemblyCross hassemblyComplement
    change
      (assembly.submatrix (block.orderEmbOfFin hblockCard)
          (block.orderEmbOfFin hblockCard)) * cross =
        cross * ((1 / 2 : ℝ) • atomMatrix complementRestricted) at hlocalized
    rw [hassemblyLeft] at hlocalized
    exact hlocalized
  obtain ⟨hcrossComplement, hcrossFull⟩ :=
    threeAtom_cross_kills_complement_and_full_missingCoordinate
      fullRestricted pair extra complementRestricted missing cross fullWeight
      pairWeight extraWeight hfullUnit hpairUnit hextraUnit hcomplementUnit
      hfullMissing hpairMissing hfullWeight hpairWeight hextraWeight hweightSum
      hintertwines
  have hcomplementProjectionOnBlock : ∀ atomIndex ∈ block,
      (projection *ᵥ complement) atomIndex = 0 := by
    apply projection_mulVec_eq_zero_on_block_of_cross_mulVec_eq_zero
      projection block hblockCard hcomplementCard complement
    · intro atomIndex hmem
      exact htightComplement.hasSupport atomIndex (by
        simp only [Finset.mem_compl, not_not]
        exact hmem)
    · exact hcrossComplement
  have hcomplementProjectionOff : ∀ atomIndex, atomIndex ∉ blockᶜ →
      (projection *ᵥ complement) atomIndex = 0 := by
    intro atomIndex hnotMem
    apply hcomplementProjectionOnBlock atomIndex
    simpa only [Finset.mem_compl, not_not] using hnotMem
  have hcomplementZeroLeak :=
    shiftedGap_mulVec_eq_zero_of_isChartTightDirection_of_projection_zero_off
      htightComplement hcomplementProjectionOff
  have hfullProjectionOff : ∀ atomIndex, atomIndex ∉ block →
      (projection *ᵥ full) atomIndex = 0 := by
    apply projection_mulVec_eq_zero_off_block_of_transposeCross_mulVec_eq_zero
      projection block hblockCard hcomplementCard full hdata.isSymmetric
    · exact htightFull.hasSupport
    · exact hcrossFull
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
  have hstrict := neg_inv_size_lt_value_of_isChartStationaryData
    crux.design rfl crux.isChartArgmaxValue hdata
  norm_num at hstrict
  linarith


end Gtz
