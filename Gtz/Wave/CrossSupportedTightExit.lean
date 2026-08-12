import Gtz.Wave.ActiveBlockKernelPromotion
import Gtz.Wave.PositiveRowSpanRankFloor
import Gtz.Wave.SupportThreePositiveCollapse
import Gtz.Wave.SupportProfileCombinatorics

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix Finset

/-! **THE CROSS-SUPPORTED TIGHT EXIT.**  The orbit-four duplicate and thin
shared-pair kills, freed from their family literals.  A card-four crux family
cannot select the same tight direction at two of its blocks: the positive rows
would collapse into three images against the four-dimensional positive-row-span
floor.  Consequently a tight direction of one block supported inside ANOTHER
block promotes to a tight direction there, duplicating the selection.  The
support-profile dispatch fires this at every branch whose selected pair lies
inside a second active block. -/

/-- Duplicating a tight direction across two of the four active blocks collapses
the positive rows into at most three images, contradicting the four-dimensional
positive-row-span floor. -/
theorem SixThreeCrux.false_of_duplicate_tightDirection_of_card_four
    (crux : SixThreeCrux)
    {firstBlock secondBlock : Finset (Fin 6)}
    {activeWeight : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hfamilyCard : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4)
    (hfirstMem : firstBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hsecondMem : secondBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hblocksNe : firstBlock ≠ secondBlock)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) activeWeight tightDir)
    (hduplicate : tightDir firstBlock = tightDir secondBlock) :
    False := by
  classical
  let family := chartArgmaxFamily (chartPointOfDesign crux.design)
  let positiveSet := positiveActiveSet family activeWeight
  let rows := positiveSet.image tightDir
  let survivorRows := (family.erase secondBlock).image tightDir
  have hrowsSubset : rows ⊆ survivorRows := by
    intro row hrow
    obtain ⟨block, hblockPositive, rfl⟩ := Finset.mem_image.mp hrow
    have hblockActive : block ∈ family := (Finset.filter_subset _ _) hblockPositive
    by_cases hsecond : block = secondBlock
    · subst hsecond
      exact Finset.mem_image.mpr ⟨firstBlock,
        Finset.mem_erase.mpr ⟨hblocksNe, hfirstMem⟩, hduplicate⟩
    · exact Finset.mem_image.mpr ⟨block,
        Finset.mem_erase.mpr ⟨hsecond, hblockActive⟩, rfl⟩
  have hupper : Module.finrank ℝ
      (Submodule.span ℝ (rows : Set (Fin 6 → ℝ))) ≤ 3 := by
    refine (finrank_span_finset_le_card rows).trans ?_
    refine (Finset.card_le_card hrowsSubset).trans ?_
    refine Finset.card_image_le.trans ?_
    rw [Finset.card_erase_of_mem hsecondMem, hfamilyCard]
  have hlower := crux.four_le_positiveTightRowSpan_finrank hdata
  change 4 ≤ Module.finrank ℝ (Submodule.span ℝ (rows : Set (Fin 6 → ℝ))) at hlower
  omega

/-- The three tight fields of an identity-labelled stationary datum, packaged
as a tight direction of the given active block. -/
theorem isChartTightDirection_of_isChartStationaryData
    {projection : Matrix (Fin 6) (Fin 6) ℝ} {weight : Fin 6 → ℝ} {value : ℝ}
    {activeSet : Finset (Finset (Fin 6))} {activeWeight : Finset (Fin 6) → ℝ}
    {tightDir : Finset (Fin 6) → Fin 6 → ℝ}
    (hdata : IsChartStationaryData 3 projection weight value activeSet
      (id : Finset (Fin 6) → Finset (Fin 6)) activeWeight tightDir)
    {block : Finset (Fin 6)} (hblockMem : block ∈ activeSet) :
    IsChartTightDirection projection weight value block (tightDir block) :=
  { isUnit := hdata.tightDir_unit block hblockMem
    hasSupport := hdata.tightDir_support block hblockMem
    isTight := hdata.tightDir_isTight block hblockMem }

/-- **THE THIN CROSS-SUPPORT EXIT.**  A tight direction of one active block
that is supported inside a SECOND active block promotes there by the Rayleigh
argument, and the resulting duplicated selection dies on the row-span floor. -/
theorem SixThreeCrux.false_of_crossSupported_tightDirection
    (crux : SixThreeCrux)
    {hostBlock neighborBlock : Finset (Fin 6)}
    {thin : Fin 6 → ℝ}
    (hfamilyCard : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4)
    (hhostMem : hostBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hneighborMem : neighborBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hblocksNe : hostBlock ≠ neighborBlock)
    (hthin : IsChartTightDirection
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design)) hostBlock thin)
    (hthinNeighborSupport : ∀ atomIndex : Fin 6,
      atomIndex ∉ neighborBlock → thin atomIndex = 0) :
    False := by
  classical
  let point := chartPointOfDesign crux.design
  let value := chartObjective point
  obtain ⟨hneighborCard, hneighborFloor⟩ :=
    (mem_chartArgmaxFamily_iff point neighborBlock).mp hneighborMem
  have hneighborDominates : ChartBlockDominatesAtValue
      point.chart point.weight value neighborBlock :=
    chartBlockDominatesAtValue_of_le_chartBlockValue point hneighborCard hneighborFloor
  have hthinRayleigh :
      thin ⬝ᵥ (chartStationaryGap point.chart point.weight *ᵥ thin)
        = value * (thin ⬝ᵥ thin) :=
    dotProduct_chartStationaryGap_mulVec_of_isChartTightVector
      (isChartTightVector_of_isChartTightDirection hthin)
  have hthinNeighborVector : IsChartTightVector point.chart point.weight value
      neighborBlock thin :=
    isChartTightVector_of_dominatesAtValue_of_rayleigh_eq
      crux.isChartStrongStationaryData.isSymmetric hneighborDominates
      hthinNeighborSupport hthinRayleigh
  have hthinNeighbor : IsChartTightDirection point.chart point.weight value
      neighborBlock thin :=
    { isUnit := hthin.isUnit
      hasSupport := hthinNeighborVector.hasSupport
      isTight := hthinNeighborVector.isTight }
  choose fallback hfallback using crux.isChartStrongStationaryData.exists_tightDir
  let selection : Finset (Fin 6) → (Fin 6 → ℝ) := fun block =>
    if block = hostBlock then thin
    else if block = neighborBlock then thin
    else if hmem : block ∈ chartArgmaxFamily point then fallback block hmem else 0
  have hselection : ∀ block ∈ chartArgmaxFamily point,
      IsChartTightDirection point.chart point.weight value block (selection block) := by
    intro block hmem
    by_cases hhost : block = hostBlock
    · subst hhost
      simpa [selection] using hthin
    by_cases hneighbor : block = neighborBlock
    · subst hneighbor
      simpa [selection, hhost] using hthinNeighbor
    · simpa [selection, hhost, hneighbor, hmem] using hfallback block hmem
  obtain ⟨activeWeight, hdata⟩ :=
    exists_multiplier_isChartStationaryData_of_isChartStrongStationaryData
      crux.isChartStrongStationaryData selection hselection
  apply crux.false_of_duplicate_tightDirection_of_card_four hfamilyCard
    hhostMem hneighborMem hblocksNe hdata
  show selection hostBlock = selection neighborBlock
  simp [selection, Ne.symm hblocksNe]

/-- **THE SUPPORT-PROFILE FORM.**  A block whose total tight support lies
inside a second active block dies: the ambient tight selection is such a
cross-supported thin direction. -/
theorem SixThreeCrux.false_of_totalTightSupport_subset_neighbor
    (crux : SixThreeCrux)
    {tightVec : Finset (Fin 6) → (Fin 3 → ℝ)} {multiplier : Finset (Fin 6) → ℝ}
    {hostBlock neighborBlock : Finset (Fin 6)}
    (hfamilyCard : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4)
    (hhostMem : hostBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hneighborMem : neighborBlock ∈ chartArgmaxFamily (chartPointOfDesign crux.design))
    (hblocksNe : hostBlock ≠ neighborBlock)
    (hdata : IsChartStationaryData 3
      (chartPointOfDesign crux.design).chart
      (chartPointOfDesign crux.design).weight
      (chartObjective (chartPointOfDesign crux.design))
      (chartArgmaxFamily (chartPointOfDesign crux.design))
      (id : Finset (Fin 6) → Finset (Fin 6)) multiplier
      (ambientTightSelection tightVec))
    (hsupportSubset : totalTightSupport tightVec hostBlock ⊆ neighborBlock) :
    False := by
  have hhostCard : hostBlock.card = 3 :=
    ((mem_chartArgmaxFamily_iff (chartPointOfDesign crux.design) hostBlock).mp hhostMem).1
  apply crux.false_of_crossSupported_tightDirection hfamilyCard hhostMem
    hneighborMem hblocksNe (isChartTightDirection_of_isChartStationaryData hdata hhostMem)
  intro atomIndex hmiss
  have hnotSupport : atomIndex ∉ totalTightSupport tightVec hostBlock :=
    fun hmem => hmiss (hsupportSubset hmem)
  exact ambientTightSelection_eq_zero_of_totalEigenSquareRow_eq_zero tightVec hostBlock
    hhostCard atomIndex
    (totalEigenSquareRow_eq_zero_of_notMem_totalTightSupport tightVec hhostCard hnotSupport)

end Gtz
