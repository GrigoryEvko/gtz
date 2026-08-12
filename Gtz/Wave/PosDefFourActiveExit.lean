import Gtz.Wave.ComplementCrossCruxExit
import Gtz.Wave.SupportThreeNonzero

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-- **THE POSITIVE-DEFINITE SUPPORT-THREE FOUR-ACTIVE BRANCH IS EMPTY.**
The stationary assembly first splits the chart projection across an active
triple and its active complement.  Their two full-support tight directions then
pin all six weights to the forbidden `-1/6` endpoint. -/
theorem SixThreeCrux.false_of_supportThree_complement_of_assemblyBlock_posDef
    (crux : SixThreeCrux)
    (tightVec : Finset (Fin 6) → (Fin 3 → ℝ))
    (multiplier : Finset (Fin 6) → ℝ)
    (block complementBlock : Finset (Fin 6))
    (hblockCard : block.card = 3) (hcomplementCard : blockᶜ.card = 3)
    (hsupportCard : (totalTightSupport tightVec block).card = 3)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (hblockMem : block ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hcomplementMem : complementBlock ∈
      chartArgmaxFamily (chartPointOfDesign crux.design))
    (hcomplementEq : complementBlock = blockᶜ)
    (hcomplementRow : totalEigenSquareRow tightVec complementBlock =
      (fun atomIndex => if atomIndex ∈ block then 0 else 1 / 3))
    (hcomplementMultiplier : multiplier complementBlock = 1 / 2)
    (hotherZero : ∀ otherBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design),
      otherBlock ≠ complementBlock → ∀ atomIndex, atomIndex ∉ block →
        totalEigenSquareRow tightVec otherBlock atomIndex = 0)
    (hleftPosDef :
      ((chartMultiplierAssembly
        (chartArgmaxFamily (chartPointOfDesign crux.design)) multiplier
        (ambientTightSelection tightVec)).submatrix
          (block.orderEmbOfFin hblockCard)
          (block.orderEmbOfFin hblockCard)).PosDef) :
    False := by
  let selection := ambientTightSelection tightVec
  have htightFull : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) block
      (selection block) :=
    { isUnit := hdata.tightDir_unit block hblockMem
      hasSupport := by
        intro atomIndex hnotMem
        exact hdata.tightDir_support block hblockMem atomIndex hnotMem
      isTight := by
        intro atomIndex hmem
        exact hdata.tightDir_isTight block hblockMem atomIndex hmem }
  have htightComplementRaw : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) complementBlock
      (selection complementBlock) :=
    { isUnit := hdata.tightDir_unit complementBlock hcomplementMem
      hasSupport := by
        intro atomIndex hnotMem
        exact hdata.tightDir_support complementBlock hcomplementMem atomIndex hnotMem
      isTight := by
        intro atomIndex hmem
        exact hdata.tightDir_isTight complementBlock hcomplementMem atomIndex hmem }
  have htightComplement : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) blockᶜ
      (selection complementBlock) := by
    simpa only [hcomplementEq] using htightComplementRaw
  have hfullNonzero : ∀ atomIndex ∈ block, selection block atomIndex ≠ 0 := by
    intro atomIndex hmem
    exact ambientTightSelection_ne_zero_of_mem_of_support_card_three
      tightVec block hblockCard hsupportCard hmem
  have hcomplementBlockCard : complementBlock.card = 3 := by
    rw [hcomplementEq]
    exact hcomplementCard
  have hcomplementNonzero : ∀ atomIndex, atomIndex ∉ block →
      selection complementBlock atomIndex ≠ 0 := by
    intro atomIndex hnotMem
    exact ambientTightSelection_ne_zero_of_uniform_complement_row
      tightVec block complementBlock hcomplementBlockCard hcomplementRow hnotMem
  have hcross :=
    crux.projectionCross_eq_zero_of_complement_of_assemblyBlock_posDef
      tightVec multiplier block complementBlock hblockCard hcomplementCard hdata
      hcomplementMem hcomplementEq hcomplementMultiplier hotherZero hleftPosDef
  exact crux.false_of_complementary_fullSupport_of_projectionCross_eq_zero
    block hblockCard hcomplementCard (selection block) (selection complementBlock)
      htightFull htightComplement hfullNonzero hcomplementNonzero hcross


end Gtz
