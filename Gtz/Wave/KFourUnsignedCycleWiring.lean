import Gtz.Design.UnsignedCycleCells

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spend the unsigned-cycle cells in the K4 knife band

The unsigned-cycle engine proves strictness from three explicit leading-minor
inequalities, without the nine allocation variables carried by the older
budget certificate.  This file packages its two K4 instances as chart cells,
spends them after Layer A and the exchange star, and removes the redundant
`1 / 10` chart-weight antecedent.

The new residual is exactly equivalent to the preceding tenth-heavy knife
band.  It is smaller as a formula: points in either unsigned cell are closed by
a named strict spanning tree.  In particular the former canonical band
inhabitant lies in the band-tree cell, so it no longer witnesses non-vacuity of
the live residual.  No replacement inhabitant is asserted here.
-/

namespace Gtz

open Matrix Finset

/-! ## Named unsigned-cycle cells -/

/-- The exact three-minor hypotheses consumed by the unsigned gauge-star
certificate at the spanning tree `{3, 4, 5}`. -/
def KFourUnsignedStarCellFires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorThree floorFour floorFive : ℝ,
    floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorThree - (point.mass 0 + point.mass 1) ∧
    0 < (floorThree - (point.mass 0 + point.mass 1))
        * (floorFour - (point.mass 0 + point.mass 2)) - point.mass 0 ^ 2 ∧
    0 < (floorThree - (point.mass 0 + point.mass 1))
          * (floorFour - (point.mass 0 + point.mass 2))
          * (floorFive - (point.mass 1 + point.mass 2))
        - (floorThree - (point.mass 0 + point.mass 1)) * point.mass 2 ^ 2
        - point.mass 0 ^ 2 * (floorFive - (point.mass 1 + point.mass 2))
        - 2 * point.mass 0 * point.mass 1 * point.mass 2
        - point.mass 1 ^ 2 * (floorFour - (point.mass 0 + point.mass 2))

/-- The exact three-minor hypotheses consumed by the unsigned band-tree
certificate at the spanning tree `{1, 3, 4}`. -/
def KFourUnsignedBandTreeCellFires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorOne floorThree floorFour : ℝ,
    floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1) ∧
    floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    0 < floorOne - (point.mass 2 + point.mass 5) ∧
    0 < (floorOne - (point.mass 2 + point.mass 5))
        * (floorThree - (point.mass 0 + point.mass 2 + point.mass 5))
        - (point.mass 2 + point.mass 5) ^ 2 ∧
    0 < (floorOne - (point.mass 2 + point.mass 5))
          * (floorThree - (point.mass 0 + point.mass 2 + point.mass 5))
          * (floorFour - (point.mass 0 + point.mass 2))
        - (floorOne - (point.mass 2 + point.mass 5))
          * (point.mass 0 + point.mass 2) ^ 2
        - (point.mass 2 + point.mass 5) ^ 2
          * (floorFour - (point.mass 0 + point.mass 2))
        - 2 * (point.mass 2 + point.mass 5) * point.mass 2
          * (point.mass 0 + point.mass 2)
        - point.mass 2 ^ 2
          * (floorThree - (point.mass 0 + point.mass 2 + point.mass 5))

/-- Either allocation-free K4 cycle cell fires. -/
def KFourUnsignedCycleCellFires (point : DirectionChartPoint 6) : Prop :=
  KFourUnsignedStarCellFires point ∨ KFourUnsignedBandTreeCellFires point

/-! ## Cell dispatchers -/

/-- The unsigned star cell supplies its named strict spanning tree. -/
theorem kFourAtlas_hasStrictTree_of_unsignedStarCell
    (point : DirectionChartPoint 6) (hcell : KFourUnsignedStarCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorThree, floorFour, floorFive, hfloorThree, hfloorFour, hfloorFive,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{3, 4, 5}, starTree_mem_kFourSpanningTreeList,
    posDef_kFour_starCell point.mass point.weight point.mass_pos point.weight_pos
      hfloorThree hfloorFour hfloorFive hcorner hminorTwo hminorDet⟩

/-- The unsigned band cell supplies its named strict spanning tree. -/
theorem kFourAtlas_hasStrictTree_of_unsignedBandTreeCell
    (point : DirectionChartPoint 6) (hcell : KFourUnsignedBandTreeCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorOne, floorThree, floorFour, hfloorOne, hfloorThree, hfloorFour,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{1, 3, 4}, bandTree_mem_kFourSpanningTreeList,
    posDef_kFour_bandTreeCell point.mass point.weight point.mass_pos point.weight_pos
      hfloorOne hfloorThree hfloorFour hcorner hminorTwo hminorDet⟩

/-- Either unsigned cell supplies a strict spanning tree. -/
theorem kFourAtlas_hasStrictTree_of_unsignedCycleCell
    (point : DirectionChartPoint 6) (hcell : KFourUnsignedCycleCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  rcases hcell with hstar | hband
  · exact kFourAtlas_hasStrictTree_of_unsignedStarCell point hstar
  · exact kFourAtlas_hasStrictTree_of_unsignedBandTreeCell point hband

/-! ## The exact smaller knife-band residual -/

/-- The K4 residual after Layer A, the exchange star, and both unsigned-cycle
cells have fired.  The chart-heavy antecedent is omitted because every six-label
chart point has a weight at least `1 / 10`. -/
noncomputable def KFourKnifeBandRefinedUnsignedBlindWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourUnsignedCycleCellFires point →
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef) →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- Spend the two unsigned cells and reconstruct the preceding tenth-heavy
knife band. -/
theorem kFourKnifeBandRefinedTenthHeavy_of_unsignedBlind
    (hblind : KFourKnifeBandRefinedUnsignedBlindWeakToStrict) :
    KFourKnifeBandRefinedTenthHeavyWeakToStrict := by
  intro point hnotLayerA hnotExchange _hheavy hweak
  rcases Classical.em (KFourUnsignedCycleCellFires point) with hcell | hcell
  · exact kFourAtlas_hasStrictTree_of_unsignedCycleCell point hcell
  · exact hblind point hnotLayerA hnotExchange hcell hweak

/-- The preceding tenth-heavy knife band restricts to the unsigned-cell blind
region.  The heavy witness is supplied by the chart weight sum, not assumed. -/
theorem unsignedBlindKFourKnifeBandRefined_of_tenthHeavy
    (hheavy : KFourKnifeBandRefinedTenthHeavyWeakToStrict) :
    KFourKnifeBandRefinedUnsignedBlindWeakToStrict := by
  intro point hnotLayerA hnotExchange _hnotUnsigned hweak
  exact hheavy point hnotLayerA hnotExchange
    (directionChartPoint_exists_tenthHeavy point) hweak

/-- Removing the two unsigned cells and the redundant weight gate is an exact
formula sharpening of the committed A3 residual. -/
theorem kFourKnifeBandRefinedUnsignedBlind_iff_tenthHeavy :
    KFourKnifeBandRefinedUnsignedBlindWeakToStrict ↔
      KFourKnifeBandRefinedTenthHeavyWeakToStrict :=
  ⟨kFourKnifeBandRefinedTenthHeavy_of_unsignedBlind,
    unsignedBlindKFourKnifeBandRefined_of_tenthHeavy⟩

/-- The unsigned-cell blind residual is also equivalent to the former public
refined knife band. -/
theorem kFourKnifeBandRefinedUnsignedBlind_iff :
    KFourKnifeBandRefinedUnsignedBlindWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedUnsignedBlind_iff_tenthHeavy.trans
    kFourKnifeBandRefinedTenthHeavy_iff

/-! ## Exact removal of the former canonical inhabitant -/

/-- The former canonical band inhabitant satisfies the new unsigned band-cell
predicate with floors `144`, `45`, and `7`. -/
theorem bandResidualWitnessPoint_unsignedBandTreeCellFires :
    KFourUnsignedBandTreeCellFires bandResidualWitnessPoint := by
  refine ⟨144, 45, 7, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [bandResidualWitnessPoint, bandResidualWitnessMass,
      bandResidualWitnessWeight]

/-- Consequently the former canonical band inhabitant is removed by the new
combined unsigned-cycle cell. -/
theorem bandResidualWitnessPoint_unsignedCycleCellFires :
    KFourUnsignedCycleCellFires bandResidualWitnessPoint :=
  Or.inr bandResidualWitnessPoint_unsignedBandTreeCellFires

end Gtz
