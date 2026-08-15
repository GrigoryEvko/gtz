import Gtz.Design.UnsignedTraceCell
import Gtz.Wave.KFourUnsignedCycleWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spend the unsigned trace atlas in the K4 knife band

The first unsigned wiring spends the gauge star and one band tree through
their three leading minors.  `UnsignedTraceCell` adds a one-inequality trace
certificate for the gauge star and the three other vertex stars.  This module
packages those four new regions, dispatches each one to its named spanning
tree, and removes their union from the exact K4 registry residual.

The new blind formula is equivalent to the preceding unsigned-cycle-blind
formula: a point in the expanded atlas has a strict tree by theorem, while a
point outside it is handed to the new residual.  No coverage assertion and no
new inhabitant are introduced.
-/

namespace Gtz

open Matrix Finset

/-! ## Four newly available cells -/

/-- The one-inequality trace certificate for the gauge star `{3,4,5}`. -/
def KFourUnsignedStarTraceCellFires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorThree floorFour floorFive : ℝ,
    floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorThree ∧ 0 < floorFour ∧ 0 < floorFive ∧
    point.mass 0 * (floorFour * floorFive + floorThree * floorFive)
        + point.mass 1 * (floorFour * floorFive + floorThree * floorFour)
        + point.mass 2 * (floorThree * floorFive + floorThree * floorFour)
      < floorThree * (floorFour * floorFive)

/-- The three-minor certificate for the vertex-a star `{0,1,3}`. -/
def KFourUnsignedStarACellFires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorZero floorOne floorThree : ℝ,
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1) ∧
    floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3) ∧
    0 < floorZero - (point.mass 2 + point.mass 4) ∧
    0 < (floorZero - (point.mass 2 + point.mass 4))
        * (floorOne - (point.mass 2 + point.mass 5)) - point.mass 2 ^ 2 ∧
    0 < (floorZero - (point.mass 2 + point.mass 4))
          * (floorOne - (point.mass 2 + point.mass 5))
          * (floorThree - (point.mass 4 + point.mass 5))
        - (floorZero - (point.mass 2 + point.mass 4)) * point.mass 5 ^ 2
        - point.mass 2 ^ 2 * (floorThree - (point.mass 4 + point.mass 5))
        - 2 * point.mass 2 * point.mass 4 * point.mass 5
        - point.mass 4 ^ 2 * (floorOne - (point.mass 2 + point.mass 5))

/-- The three-minor certificate for the vertex-b star `{0,2,4}`. -/
def KFourUnsignedStarBCellFires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorZero floorTwo floorFour : ℝ,
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    0 < floorZero - (point.mass 1 + point.mass 3) ∧
    0 < (floorZero - (point.mass 1 + point.mass 3))
        * (floorTwo - (point.mass 1 + point.mass 5)) - point.mass 1 ^ 2 ∧
    0 < (floorZero - (point.mass 1 + point.mass 3))
          * (floorTwo - (point.mass 1 + point.mass 5))
          * (floorFour - (point.mass 3 + point.mass 5))
        - (floorZero - (point.mass 1 + point.mass 3)) * point.mass 5 ^ 2
        - point.mass 1 ^ 2 * (floorFour - (point.mass 3 + point.mass 5))
        - 2 * point.mass 1 * point.mass 3 * point.mass 5
        - point.mass 3 ^ 2 * (floorTwo - (point.mass 1 + point.mass 5))

/-- The three-minor certificate for the vertex-c star `{1,2,5}`. -/
def KFourUnsignedStarCCellFires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorOne floorTwo floorFive : ℝ,
    floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1) ∧
    floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorOne - (point.mass 0 + point.mass 3) ∧
    0 < (floorOne - (point.mass 0 + point.mass 3))
        * (floorTwo - (point.mass 0 + point.mass 4)) - point.mass 0 ^ 2 ∧
    0 < (floorOne - (point.mass 0 + point.mass 3))
          * (floorTwo - (point.mass 0 + point.mass 4))
          * (floorFive - (point.mass 3 + point.mass 4))
        - (floorOne - (point.mass 0 + point.mass 3)) * point.mass 4 ^ 2
        - point.mass 0 ^ 2 * (floorFive - (point.mass 3 + point.mass 4))
        - 2 * point.mass 0 * point.mass 3 * point.mass 4
        - point.mass 3 ^ 2 * (floorTwo - (point.mass 0 + point.mass 4))

/-- The four cells supplied by `UnsignedTraceCell`. -/
def KFourUnsignedTraceAtlasCellFires (point : DirectionChartPoint 6) : Prop :=
  KFourUnsignedStarTraceCellFires point ∨ KFourUnsignedStarACellFires point ∨
    KFourUnsignedStarBCellFires point ∨ KFourUnsignedStarCCellFires point

/-- The preceding two unsigned cells together with the four new trace-atlas
cells. -/
def KFourExpandedUnsignedCellFires (point : DirectionChartPoint 6) : Prop :=
  KFourUnsignedCycleCellFires point ∨ KFourUnsignedTraceAtlasCellFires point

/-! ## Dispatch to the five named trees -/

/-- The gauge-star trace cell supplies the gauge star. -/
theorem kFourAtlas_hasStrictTree_of_unsignedStarTraceCell
    (point : DirectionChartPoint 6) (hcell : KFourUnsignedStarTraceCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorThree, floorFour, floorFive, hfloorThree, hfloorFour, hfloorFive,
    hposThree, hposFour, hposFive, htrace⟩ := hcell
  exact ⟨{3, 4, 5}, starTree_mem_kFourSpanningTreeList,
    posDef_kFour_starTrace point.mass point.weight point.mass_pos point.weight_pos
      hfloorThree hfloorFour hfloorFive hposThree hposFour hposFive htrace⟩

/-- The vertex-a cell supplies `{0,1,3}`. -/
theorem kFourAtlas_hasStrictTree_of_unsignedStarACell
    (point : DirectionChartPoint 6) (hcell : KFourUnsignedStarACellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorZero, floorOne, floorThree, hfloorZero, hfloorOne, hfloorThree,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{0, 1, 3}, starTreeA_mem_kFourSpanningTreeList,
    posDef_kFour_starCellA point.mass point.weight point.mass_pos point.weight_pos
      hfloorZero hfloorOne hfloorThree hcorner hminorTwo hminorDet⟩

/-- The vertex-b cell supplies `{0,2,4}`. -/
theorem kFourAtlas_hasStrictTree_of_unsignedStarBCell
    (point : DirectionChartPoint 6) (hcell : KFourUnsignedStarBCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorZero, floorTwo, floorFour, hfloorZero, hfloorTwo, hfloorFour,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{0, 2, 4}, starTreeB_mem_kFourSpanningTreeList,
    posDef_kFour_starCellB point.mass point.weight point.mass_pos point.weight_pos
      hfloorZero hfloorTwo hfloorFour hcorner hminorTwo hminorDet⟩

/-- The vertex-c cell supplies `{1,2,5}`. -/
theorem kFourAtlas_hasStrictTree_of_unsignedStarCCell
    (point : DirectionChartPoint 6) (hcell : KFourUnsignedStarCCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorOne, floorTwo, floorFive, hfloorOne, hfloorTwo, hfloorFive,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{1, 2, 5}, starTreeC_mem_kFourSpanningTreeList,
    posDef_kFour_starCellC point.mass point.weight point.mass_pos point.weight_pos
      hfloorOne hfloorTwo hfloorFive hcorner hminorTwo hminorDet⟩

/-- Any new trace-atlas cell supplies a strict spanning tree. -/
theorem kFourAtlas_hasStrictTree_of_unsignedTraceAtlasCell
    (point : DirectionChartPoint 6) (hcell : KFourUnsignedTraceAtlasCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  rcases hcell with htrace | hstarA | hstarB | hstarC
  · exact kFourAtlas_hasStrictTree_of_unsignedStarTraceCell point htrace
  · exact kFourAtlas_hasStrictTree_of_unsignedStarACell point hstarA
  · exact kFourAtlas_hasStrictTree_of_unsignedStarBCell point hstarB
  · exact kFourAtlas_hasStrictTree_of_unsignedStarCCell point hstarC

/-- Any cell in the expanded unsigned atlas supplies a strict spanning tree. -/
theorem kFourAtlas_hasStrictTree_of_expandedUnsignedCell
    (point : DirectionChartPoint 6) (hcell : KFourExpandedUnsignedCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  rcases hcell with hcycle | htrace
  · exact kFourAtlas_hasStrictTree_of_unsignedCycleCell point hcycle
  · exact kFourAtlas_hasStrictTree_of_unsignedTraceAtlasCell point htrace

/-! ## The exact smaller K4 residual -/

/-- The knife-band residual outside Layer A, the exchange star, and all six
unsigned certificate cells. -/
noncomputable def KFourKnifeBandRefinedTraceBlindWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourExpandedUnsignedCellFires point →
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef) →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- Spend the expanded atlas and reconstruct the preceding unsigned-blind
residual. -/
theorem kFourKnifeBandRefinedUnsignedBlind_of_traceBlind
    (hblind : KFourKnifeBandRefinedTraceBlindWeakToStrict) :
    KFourKnifeBandRefinedUnsignedBlindWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotCycle hweak
  rcases Classical.em (KFourExpandedUnsignedCellFires point) with hcell | hcell
  · exact kFourAtlas_hasStrictTree_of_expandedUnsignedCell point hcell
  · exact hblind point hnotLayerA hnotExchange hcell hweak

/-- The preceding unsigned-blind residual restricts to the complement of the
expanded atlas. -/
theorem traceBlindKFourKnifeBandRefined_of_unsignedBlind
    (hblind : KFourKnifeBandRefinedUnsignedBlindWeakToStrict) :
    KFourKnifeBandRefinedTraceBlindWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotExpanded hweak
  have hnotCycle : ¬ KFourUnsignedCycleCellFires point := by
    intro hcycle
    exact hnotExpanded (Or.inl hcycle)
  exact hblind point hnotLayerA hnotExchange hnotCycle hweak

/-- Removing the four newly landed cells is an exact formula sharpening. -/
theorem kFourKnifeBandRefinedTraceBlind_iff_unsignedBlind :
    KFourKnifeBandRefinedTraceBlindWeakToStrict ↔
      KFourKnifeBandRefinedUnsignedBlindWeakToStrict :=
  ⟨kFourKnifeBandRefinedUnsignedBlind_of_traceBlind,
    traceBlindKFourKnifeBandRefined_of_unsignedBlind⟩

/-- The expanded-atlas-blind residual remains equivalent to the public refined
knife band. -/
theorem kFourKnifeBandRefinedTraceBlind_iff :
    KFourKnifeBandRefinedTraceBlindWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedTraceBlind_iff_unsignedBlind.trans
    kFourKnifeBandRefinedUnsignedBlind_iff

end Gtz
