import Gtz.Design.RowCertificateAtlas
import Gtz.Wave.KFourPendantAtlasWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Spend the seven missing K4 path cells

`RowCertificateAtlas` supplies exact unsigned-minor producers for the seven
path trees absent from the preceding atlas.  This module packages their broad
minor hypotheses as chart cells, dispatches all seven to strict spanning trees,
and removes their union from the exact A3 residual.  After this step every one
of the sixteen K4 spanning trees carries at least one moduli-only cell.
-/

namespace Gtz

open Matrix Finset

/-! ## The seven missing path cells -/

def KFourPathCell015Fires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorZero floorOne floorFive : ℝ,
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorZero - (point.mass 2 + point.mass 4) ∧
    0 < (floorZero - (point.mass 2 + point.mass 4))
      * (floorOne - (point.mass 2 + point.mass 3 + point.mass 4))
        - (point.mass 2 + point.mass 4) ^ 2 ∧
    0 < (floorZero - (point.mass 2 + point.mass 4))
        * (floorOne - (point.mass 2 + point.mass 3 + point.mass 4))
        * (floorFive - (point.mass 3 + point.mass 4))
      - (floorZero - (point.mass 2 + point.mass 4)) * (point.mass 3 + point.mass 4) ^ 2
      - (point.mass 2 + point.mass 4) ^ 2
          * (floorFive - (point.mass 3 + point.mass 4))
      + 2 * (-(point.mass 2 + point.mass 4)) * (-(point.mass 4))
          * (-(point.mass 3 + point.mass 4))
      - point.mass 4 ^ 2
          * (floorOne - (point.mass 2 + point.mass 3 + point.mass 4))

def KFourPathCell025Fires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorZero floorTwo floorFive : ℝ,
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorZero - (point.mass 1 + point.mass 3) ∧
    0 < (floorZero - (point.mass 1 + point.mass 3))
      * (floorTwo - (point.mass 1 + point.mass 3 + point.mass 4))
        - (point.mass 1 + point.mass 3) ^ 2 ∧
    0 < (floorZero - (point.mass 1 + point.mass 3))
        * (floorTwo - (point.mass 1 + point.mass 3 + point.mass 4))
        * (floorFive - (point.mass 3 + point.mass 4))
      - (floorZero - (point.mass 1 + point.mass 3)) * (point.mass 3 + point.mass 4) ^ 2
      - (point.mass 1 + point.mass 3) ^ 2
          * (floorFive - (point.mass 3 + point.mass 4))
      + 2 * (-(point.mass 1 + point.mass 3)) * (-(point.mass 3))
          * (-(point.mass 3 + point.mass 4))
      - point.mass 3 ^ 2
          * (floorTwo - (point.mass 1 + point.mass 3 + point.mass 4))

def KFourPathCell035Fires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorZero floorThree floorFive : ℝ,
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorThree * point.weight 3 ≤ point.mass 3 * (1 - point.weight 3) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorZero - (point.mass 2 + point.mass 4) ∧
    0 < (floorZero - (point.mass 2 + point.mass 4))
      * (floorThree - (point.mass 1 + point.mass 2 + point.mass 4))
        - (point.mass 2 + point.mass 4) ^ 2 ∧
    0 < (floorZero - (point.mass 2 + point.mass 4))
        * (floorThree - (point.mass 1 + point.mass 2 + point.mass 4))
        * (floorFive - (point.mass 1 + point.mass 2))
      - (floorZero - (point.mass 2 + point.mass 4)) * (point.mass 1 + point.mass 2) ^ 2
      - (point.mass 2 + point.mass 4) ^ 2
          * (floorFive - (point.mass 1 + point.mass 2))
      + 2 * (-(point.mass 2 + point.mass 4)) * (-(point.mass 2))
          * (-(point.mass 1 + point.mass 2))
      - point.mass 2 ^ 2
          * (floorThree - (point.mass 1 + point.mass 2 + point.mass 4))

def KFourPathCell045Fires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorZero floorFour floorFive : ℝ,
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorZero - (point.mass 1 + point.mass 3) ∧
    0 < (floorZero - (point.mass 1 + point.mass 3))
      * (floorFour - (point.mass 1 + point.mass 2 + point.mass 3))
        - (point.mass 1 + point.mass 3) ^ 2 ∧
    0 < (floorZero - (point.mass 1 + point.mass 3))
        * (floorFour - (point.mass 1 + point.mass 2 + point.mass 3))
        * (floorFive - (point.mass 1 + point.mass 2))
      - (floorZero - (point.mass 1 + point.mass 3)) * (point.mass 1 + point.mass 2) ^ 2
      - (point.mass 1 + point.mass 3) ^ 2
          * (floorFive - (point.mass 1 + point.mass 2))
      + 2 * (-(point.mass 1 + point.mass 3)) * (-(point.mass 1))
          * (-(point.mass 1 + point.mass 2))
      - point.mass 1 ^ 2
          * (floorFour - (point.mass 1 + point.mass 2 + point.mass 3))

def KFourPathCell014Fires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorZero floorOne floorFour : ℝ,
    floorZero * point.weight 0 ≤ point.mass 0 * (1 - point.weight 0) ∧
    floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    0 < floorZero - (point.mass 2 + point.mass 3 + point.mass 5) ∧
    0 < (floorZero - (point.mass 2 + point.mass 3 + point.mass 5))
      * (floorOne - (point.mass 2 + point.mass 5))
        - (point.mass 2 + point.mass 5) ^ 2 ∧
    0 < (floorZero - (point.mass 2 + point.mass 3 + point.mass 5))
        * (floorOne - (point.mass 2 + point.mass 5))
        * (floorFour - (point.mass 3 + point.mass 5))
      - (floorZero - (point.mass 2 + point.mass 3 + point.mass 5)) * point.mass 5 ^ 2
      - (point.mass 2 + point.mass 5) ^ 2
          * (floorFour - (point.mass 3 + point.mass 5))
      + 2 * (-(point.mass 2 + point.mass 5)) * (-(point.mass 3 + point.mass 5))
          * (-(point.mass 5))
      - (point.mass 3 + point.mass 5) ^ 2
          * (floorOne - (point.mass 2 + point.mass 5))

def KFourPathCell124Fires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorOne floorTwo floorFour : ℝ,
    floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1) ∧
    floorTwo * point.weight 2 ≤ point.mass 2 * (1 - point.weight 2) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    0 < floorOne - (point.mass 0 + point.mass 3) ∧
    0 < (floorOne - (point.mass 0 + point.mass 3))
      * (floorTwo - (point.mass 0 + point.mass 3 + point.mass 5))
        - (point.mass 0 + point.mass 3) ^ 2 ∧
    0 < (floorOne - (point.mass 0 + point.mass 3))
        * (floorTwo - (point.mass 0 + point.mass 3 + point.mass 5))
        * (floorFour - (point.mass 3 + point.mass 5))
      - (floorOne - (point.mass 0 + point.mass 3)) * (point.mass 3 + point.mass 5) ^ 2
      - (point.mass 0 + point.mass 3) ^ 2
          * (floorFour - (point.mass 3 + point.mass 5))
      + 2 * (-(point.mass 0 + point.mass 3)) * (-(point.mass 3))
          * (-(point.mass 3 + point.mass 5))
      - point.mass 3 ^ 2
          * (floorTwo - (point.mass 0 + point.mass 3 + point.mass 5))

def KFourPathCell145Fires (point : DirectionChartPoint 6) : Prop :=
  ∃ floorOne floorFour floorFive : ℝ,
    floorOne * point.weight 1 ≤ point.mass 1 * (1 - point.weight 1) ∧
    floorFour * point.weight 4 ≤ point.mass 4 * (1 - point.weight 4) ∧
    floorFive * point.weight 5 ≤ point.mass 5 * (1 - point.weight 5) ∧
    0 < floorOne - (point.mass 0 + point.mass 3) ∧
    0 < (floorOne - (point.mass 0 + point.mass 3))
      * (floorFour - (point.mass 0 + point.mass 2)) - point.mass 0 ^ 2 ∧
    0 < (floorOne - (point.mass 0 + point.mass 3))
        * (floorFour - (point.mass 0 + point.mass 2))
        * (floorFive - (point.mass 0 + point.mass 2 + point.mass 3))
      - (floorOne - (point.mass 0 + point.mass 3)) * (point.mass 0 + point.mass 2) ^ 2
      - point.mass 0 ^ 2 * (floorFive - (point.mass 0 + point.mass 2 + point.mass 3))
      + 2 * (-(point.mass 0)) * (-(point.mass 0 + point.mass 3))
          * (-(point.mass 0 + point.mass 2))
      - (point.mass 0 + point.mass 3) ^ 2
          * (floorFour - (point.mass 0 + point.mass 2))

def KFourMissingPathMinorAtlasCellFires (point : DirectionChartPoint 6) : Prop :=
  KFourPathCell015Fires point ∨ KFourPathCell025Fires point ∨
    KFourPathCell035Fires point ∨ KFourPathCell045Fires point ∨
    KFourPathCell014Fires point ∨ KFourPathCell124Fires point ∨
    KFourPathCell145Fires point

def KFourAllTreeMinorAtlasCellFires (point : DirectionChartPoint 6) : Prop :=
  KFourFullMinorAtlasCellFires point ∨ KFourMissingPathMinorAtlasCellFires point

/-! ## Dispatchers -/

theorem kFourAtlas_hasStrictTree_of_pathCell015
    (point : DirectionChartPoint 6) (hcell : KFourPathCell015Fires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorZero, floorOne, floorFive, hfloorZero, hfloorOne, hfloorFive,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{0, 1, 5}, pathTree_zeroOneFive_mem,
    posDef_kFour_pathCell_zeroOneFive point.mass point.weight point.mass_pos
      point.weight_pos hfloorZero hfloorOne hfloorFive hcorner hminorTwo hminorDet⟩

theorem kFourAtlas_hasStrictTree_of_pathCell025
    (point : DirectionChartPoint 6) (hcell : KFourPathCell025Fires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorZero, floorTwo, floorFive, hfloorZero, hfloorTwo, hfloorFive,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{0, 2, 5}, pathTree_zeroTwoFive_mem,
    posDef_kFour_pathCell_zeroTwoFive point.mass point.weight point.mass_pos
      point.weight_pos hfloorZero hfloorTwo hfloorFive hcorner hminorTwo hminorDet⟩

theorem kFourAtlas_hasStrictTree_of_pathCell035
    (point : DirectionChartPoint 6) (hcell : KFourPathCell035Fires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorZero, floorThree, floorFive, hfloorZero, hfloorThree, hfloorFive,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{0, 3, 5}, pathTree_zeroThreeFive_mem,
    posDef_kFour_pathCell_zeroThreeFive point.mass point.weight point.mass_pos
      point.weight_pos hfloorZero hfloorThree hfloorFive hcorner hminorTwo hminorDet⟩

theorem kFourAtlas_hasStrictTree_of_pathCell045
    (point : DirectionChartPoint 6) (hcell : KFourPathCell045Fires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorZero, floorFour, floorFive, hfloorZero, hfloorFour, hfloorFive,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{0, 4, 5}, pathTree_zeroFourFive_mem,
    posDef_kFour_pathCell_zeroFourFive point.mass point.weight point.mass_pos
      point.weight_pos hfloorZero hfloorFour hfloorFive hcorner hminorTwo hminorDet⟩

theorem kFourAtlas_hasStrictTree_of_pathCell014
    (point : DirectionChartPoint 6) (hcell : KFourPathCell014Fires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorZero, floorOne, floorFour, hfloorZero, hfloorOne, hfloorFour,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{0, 1, 4}, pathTree_zeroOneFour_mem,
    posDef_kFour_pathCell_zeroOneFour point.mass point.weight point.mass_pos
      point.weight_pos hfloorZero hfloorOne hfloorFour hcorner hminorTwo hminorDet⟩

theorem kFourAtlas_hasStrictTree_of_pathCell124
    (point : DirectionChartPoint 6) (hcell : KFourPathCell124Fires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorOne, floorTwo, floorFour, hfloorOne, hfloorTwo, hfloorFour,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{1, 2, 4}, pathTree_oneTwoFour_mem,
    posDef_kFour_pathCell_oneTwoFour point.mass point.weight point.mass_pos
      point.weight_pos hfloorOne hfloorTwo hfloorFour hcorner hminorTwo hminorDet⟩

theorem kFourAtlas_hasStrictTree_of_pathCell145
    (point : DirectionChartPoint 6) (hcell : KFourPathCell145Fires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨floorOne, floorFour, floorFive, hfloorOne, hfloorFour, hfloorFive,
    hcorner, hminorTwo, hminorDet⟩ := hcell
  exact ⟨{1, 4, 5}, pathTree_oneFourFive_mem,
    posDef_kFour_pathCell_oneFourFive point.mass point.weight point.mass_pos
      point.weight_pos hfloorOne hfloorFour hfloorFive hcorner hminorTwo hminorDet⟩

theorem kFourAtlas_hasStrictTree_of_missingPathMinorAtlasCell
    (point : DirectionChartPoint 6)
    (hcell : KFourMissingPathMinorAtlasCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  rcases hcell with h015 | h025 | h035 | h045 | h014 | h124 | h145
  · exact kFourAtlas_hasStrictTree_of_pathCell015 point h015
  · exact kFourAtlas_hasStrictTree_of_pathCell025 point h025
  · exact kFourAtlas_hasStrictTree_of_pathCell035 point h035
  · exact kFourAtlas_hasStrictTree_of_pathCell045 point h045
  · exact kFourAtlas_hasStrictTree_of_pathCell014 point h014
  · exact kFourAtlas_hasStrictTree_of_pathCell124 point h124
  · exact kFourAtlas_hasStrictTree_of_pathCell145 point h145

theorem kFourAtlas_hasStrictTree_of_allTreeMinorAtlasCell
    (point : DirectionChartPoint 6) (hcell : KFourAllTreeMinorAtlasCellFires point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  rcases hcell with hprevious | hpath
  · exact kFourAtlas_hasStrictTree_of_fullMinorAtlasCell point hprevious
  · exact kFourAtlas_hasStrictTree_of_missingPathMinorAtlasCell point hpath

/-! ## The exact all-tree-atlas residual -/

noncomputable def KFourKnifeBandRefinedAllTreeBlindWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    (∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef) →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem kFourKnifeBandRefinedPendantBlind_of_allTreeBlind
    (hblind : KFourKnifeBandRefinedAllTreeBlindWeakToStrict) :
    KFourKnifeBandRefinedPendantBlindWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotPrevious hweak
  rcases Classical.em (KFourMissingPathMinorAtlasCellFires point) with
    hcell | hnotCell
  · exact kFourAtlas_hasStrictTree_of_missingPathMinorAtlasCell point hcell
  · apply hblind point hnotLayerA hnotExchange
    · intro hall
      rcases hall with hprevious | hpath
      · exact hnotPrevious hprevious
      · exact hnotCell hpath
    · exact hweak

theorem allTreeBlindKFourKnifeBandRefined_of_pendantBlind
    (hblind : KFourKnifeBandRefinedPendantBlindWeakToStrict) :
    KFourKnifeBandRefinedAllTreeBlindWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAll hweak
  apply hblind point hnotLayerA hnotExchange
  · intro hprevious
    exact hnotAll (Or.inl hprevious)
  · exact hweak

theorem kFourKnifeBandRefinedAllTreeBlind_iff_pendantBlind :
    KFourKnifeBandRefinedAllTreeBlindWeakToStrict ↔
      KFourKnifeBandRefinedPendantBlindWeakToStrict :=
  ⟨kFourKnifeBandRefinedPendantBlind_of_allTreeBlind,
    allTreeBlindKFourKnifeBandRefined_of_pendantBlind⟩

theorem kFourKnifeBandRefinedAllTreeBlind_iff :
    KFourKnifeBandRefinedAllTreeBlindWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedAllTreeBlind_iff_pendantBlind.trans
    kFourKnifeBandRefinedPendantBlind_iff

/-! ## Nonvacuity -/

noncomputable def pathCell015WitnessPoint : DirectionChartPoint 6 where
  mass
    | 0 => 100
    | 1 => 100
    | 2 => 1
    | 3 => 1
    | 4 => 1
    | 5 => 100
  weight := fun _ => 1 / 6
  mass_pos label := by fin_cases label <;> norm_num
  weight_pos _ := by norm_num
  weight_sum_one := by rw [Fin.sum_univ_six]; norm_num

theorem pathCell015WitnessPoint_fires :
    KFourPathCell015Fires pathCell015WitnessPoint := by
  refine ⟨400, 400, 400, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;>
    norm_num [pathCell015WitnessPoint]

end Gtz
