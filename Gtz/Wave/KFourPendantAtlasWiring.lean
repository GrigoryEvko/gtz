import Gtz.Design.CoverageRefuters
import Gtz.Wave.KFourUnsignedTraceWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spend the four pendant cells in the K4 residual

`CoverageRefuters` lands the four minor certificates around matching
`{2,3}`.  This module packages their hypotheses as chart cells, dispatches
them to the four named spanning trees, and removes their union from the exact
K4 registry residual.  The second coverage refuter proves the new region is
inhabited.
-/

namespace Gtz

open Matrix Finset

def KFourPendantCell023Fires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorZero floorTwo floorThree : ℝ,
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2) ∧
    floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3) ∧
    0 < floorZero - (point.mass 1 + point.mass 4 + point.mass 5) ∧
    0 < (floorZero - (point.mass 1 + point.mass 4 + point.mass 5))
      * (floorTwo - (point.mass 1 + point.mass 5))
        - (point.mass 1 + point.mass 5) ^ 2 ∧
    0 < (floorZero - (point.mass 1 + point.mass 4 + point.mass 5))
        * (floorTwo - (point.mass 1 + point.mass 5))
        * (floorThree - (point.mass 4 + point.mass 5))
      - (floorZero - (point.mass 1 + point.mass 4 + point.mass 5)) * point.mass 5 ^ 2
      - (point.mass 1 + point.mass 5) ^ 2
          * (floorThree - (point.mass 4 + point.mass 5))
      + 2 * (-(point.mass 1 + point.mass 5)) * (-(point.mass 4 + point.mass 5))
          * (-(point.mass 5))
      - (point.mass 4 + point.mass 5) ^ 2
          * (floorTwo - (point.mass 1 + point.mass 5))

def KFourPendantCell123Fires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorOne floorTwo floorThree : ℝ,
    floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1) ∧
    floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2) ∧
    floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3) ∧
    0 < floorOne - (point.mass 0 + point.mass 4 + point.mass 5) ∧
    0 < (floorOne - (point.mass 0 + point.mass 4 + point.mass 5))
      * (floorTwo - (point.mass 0 + point.mass 4))
        - (point.mass 0 + point.mass 4) ^ 2 ∧
    0 < (floorOne - (point.mass 0 + point.mass 4 + point.mass 5))
        * (floorTwo - (point.mass 0 + point.mass 4))
        * (floorThree - (point.mass 4 + point.mass 5))
      - (floorOne - (point.mass 0 + point.mass 4 + point.mass 5)) * point.mass 4 ^ 2
      - (point.mass 0 + point.mass 4) ^ 2
          * (floorThree - (point.mass 4 + point.mass 5))
      + 2 * (-(point.mass 0 + point.mass 4)) * (-(point.mass 4 + point.mass 5))
          * (-(point.mass 4))
      - (point.mass 4 + point.mass 5) ^ 2
          * (floorTwo - (point.mass 0 + point.mass 4))

def KFourPendantCell234Fires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorTwo floorThree floorFour : ℝ,
    floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2) ∧
    floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    0 < floorTwo - (point.mass 1 + point.mass 5) ∧
    0 < (floorTwo - (point.mass 1 + point.mass 5))
      * (floorThree - (point.mass 0 + point.mass 1)) - point.mass 1 ^ 2 ∧
    0 < (floorTwo - (point.mass 1 + point.mass 5))
        * (floorThree - (point.mass 0 + point.mass 1))
        * (floorFour - (point.mass 0 + point.mass 1 + point.mass 5))
      - (floorTwo - (point.mass 1 + point.mass 5)) * (point.mass 0 + point.mass 1) ^ 2
      - point.mass 1 ^ 2 * (floorFour - (point.mass 0 + point.mass 1 + point.mass 5))
      + 2 * (-(point.mass 1)) * (-(point.mass 1 + point.mass 5))
          * (-(point.mass 0 + point.mass 1))
      - (point.mass 1 + point.mass 5) ^ 2
          * (floorThree - (point.mass 0 + point.mass 1))

def KFourPendantCell235Fires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorTwo floorThree floorFive : ℝ,
    floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2) ∧
    floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorTwo - (point.mass 0 + point.mass 4) ∧
    0 < (floorTwo - (point.mass 0 + point.mass 4))
      * (floorThree - (point.mass 0 + point.mass 1)) - point.mass 0 ^ 2 ∧
    0 < (floorTwo - (point.mass 0 + point.mass 4))
        * (floorThree - (point.mass 0 + point.mass 1))
        * (floorFive - (point.mass 0 + point.mass 1 + point.mass 4))
      - (floorTwo - (point.mass 0 + point.mass 4)) * (point.mass 0 + point.mass 1) ^ 2
      - point.mass 0 ^ 2 * (floorFive - (point.mass 0 + point.mass 1 + point.mass 4))
      + 2 * (-(point.mass 0)) * (-(point.mass 0 + point.mass 4))
          * (-(point.mass 0 + point.mass 1))
      - (point.mass 0 + point.mass 4) ^ 2
          * (floorThree - (point.mass 0 + point.mass 1))

def KFourPendantAtlasCellFires (point : DirectionChartPoint 6) : Prop :=
  KFourPendantCell023Fires point ∨ KFourPendantCell123Fires point ∨
    KFourPendantCell234Fires point ∨ KFourPendantCell235Fires point

def KFourFullMinorAtlasCellFires (point : DirectionChartPoint 6) : Prop :=
  KFourExpandedUnsignedCellFires point ∨ KFourPendantAtlasCellFires point

theorem kFourAtlas_hasStrictTree_of_pendantCell023
    (point : DirectionChartPoint 6) (hcell : KFourPendantCell023Fires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorZero, floorTwo, floorThree, hfloorZero, hfloorTwo, hfloorThree,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{0, 2, 3}, pendantTrees_mem_kFourSpanningTreeList.1,
    posDef_kFour_pendantCell_zeroTwoThree point.mass point.weight
      point.mass_pos point.weight_pos hfloorZero hfloorTwo hfloorThree
      hcorner hminorTwo hminorDet⟩

theorem kFourAtlas_hasStrictTree_of_pendantCell123
    (point : DirectionChartPoint 6) (hcell : KFourPendantCell123Fires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorOne, floorTwo, floorThree, hfloorOne, hfloorTwo, hfloorThree,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{1, 2, 3}, pendantTrees_mem_kFourSpanningTreeList.2.1,
    posDef_kFour_pendantCell_oneTwoThree point.mass point.weight
      point.mass_pos point.weight_pos hfloorOne hfloorTwo hfloorThree
      hcorner hminorTwo hminorDet⟩

theorem kFourAtlas_hasStrictTree_of_pendantCell234
    (point : DirectionChartPoint 6) (hcell : KFourPendantCell234Fires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorTwo, floorThree, floorFour, hfloorTwo, hfloorThree, hfloorFour,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{2, 3, 4}, pendantTrees_mem_kFourSpanningTreeList.2.2.1,
    posDef_kFour_pendantCell_twoThreeFour point.mass point.weight
      point.mass_pos point.weight_pos hfloorTwo hfloorThree hfloorFour
      hcorner hminorTwo hminorDet⟩

theorem kFourAtlas_hasStrictTree_of_pendantCell235
    (point : DirectionChartPoint 6) (hcell : KFourPendantCell235Fires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorTwo, floorThree, floorFive, hfloorTwo, hfloorThree, hfloorFive,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{2, 3, 5}, pendantTrees_mem_kFourSpanningTreeList.2.2.2,
    posDef_kFour_pendantCell_twoThreeFive point.mass point.weight
      point.mass_pos point.weight_pos hfloorTwo hfloorThree hfloorFive
      hcorner hminorTwo hminorDet⟩

theorem kFourAtlas_hasStrictTree_of_pendantAtlasCell
    (point : DirectionChartPoint 6) (hcell : KFourPendantAtlasCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  rcases hcell with h023 | h123 | h234 | h235
  · exact kFourAtlas_hasStrictTree_of_pendantCell023 point h023
  · exact kFourAtlas_hasStrictTree_of_pendantCell123 point h123
  · exact kFourAtlas_hasStrictTree_of_pendantCell234 point h234
  · exact kFourAtlas_hasStrictTree_of_pendantCell235 point h235

theorem kFourAtlas_hasStrictTree_of_fullMinorAtlasCell
    (point : DirectionChartPoint 6) (hcell : KFourFullMinorAtlasCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  rcases hcell with hprevious | hpendant
  · exact kFourAtlas_hasStrictTree_of_expandedUnsignedCell point hprevious
  · exact kFourAtlas_hasStrictTree_of_pendantAtlasCell point hpendant

noncomputable def KFourKnifeBandRefinedPendantBlindWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourFullMinorAtlasCellFires point →
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef) →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem kFourKnifeBandRefinedTraceBlind_of_pendantBlind
    (hblind : KFourKnifeBandRefinedPendantBlindWeakToStrict) :
    KFourKnifeBandRefinedTraceBlindWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotPrevious hweak
  rcases Classical.em (KFourPendantAtlasCellFires point) with hcell | hcell
  · exact kFourAtlas_hasStrictTree_of_pendantAtlasCell point hcell
  · apply hblind point hnotLayerA hnotExchange
    · intro hfull
      rcases hfull with hprevious | hpendant
      · exact hnotPrevious hprevious
      · exact hcell hpendant
    · exact hweak

theorem pendantBlindKFourKnifeBandRefined_of_traceBlind
    (hblind : KFourKnifeBandRefinedTraceBlindWeakToStrict) :
    KFourKnifeBandRefinedPendantBlindWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotFull hweak
  have hnotPrevious : ¬ KFourExpandedUnsignedCellFires point := by
    intro hprevious
    exact hnotFull (Or.inl hprevious)
  exact hblind point hnotLayerA hnotExchange hnotPrevious hweak

theorem kFourKnifeBandRefinedPendantBlind_iff_traceBlind :
    KFourKnifeBandRefinedPendantBlindWeakToStrict ↔
      KFourKnifeBandRefinedTraceBlindWeakToStrict :=
  ⟨kFourKnifeBandRefinedTraceBlind_of_pendantBlind,
    pendantBlindKFourKnifeBandRefined_of_traceBlind⟩

theorem kFourKnifeBandRefinedPendantBlind_iff :
    KFourKnifeBandRefinedPendantBlindWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedPendantBlind_iff_traceBlind.trans
    kFourKnifeBandRefinedTraceBlind_iff

theorem coverageRefuterTwo_pendantCell123Fires :
    KFourPendantCell123Fires
      { mass := coverageRefuterTwoMass
        weight := coverageRefuterTwoWeight
        mass_pos := fun label => by
          fin_cases label <;> norm_num [coverageRefuterTwoMass]
        weight_pos := fun label => by
          fin_cases label <;> norm_num [coverageRefuterTwoWeight]
        weight_sum_one := coverageRefuterTwoWeight_sum } := by
  refine ⟨253 / 105, 667 / 210, 29, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [coverageRefuterTwoMass, coverageRefuterTwoWeight]

end Gtz
