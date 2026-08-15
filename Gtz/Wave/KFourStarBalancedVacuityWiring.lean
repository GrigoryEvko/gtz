import Gtz.Design.StarWallVacuity
import Gtz.Wave.KFourStarSingleExchangeRefusal

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# Spend the balanced star-wall vacuity theorem in A3

`StarWallVacuity` proves that one explicit region of the gauge-star corank-two
wall fires the unsigned minor atlas.  The A3 residual already assumes that the
atlas is silent, but that consequence was not present in its data.

This module wires the theorem into the residual.  At the gauge star the wall
family now carries the exact alternative forced by atlas silence:

* the first positive axis coordinate is not maximal; or
* one of the four weights read by the vertex-a cell is greater than `1/6`.

The refined A3 proposition is exactly equivalent to the preceding
refused-exchange proposition.  No new assumption is introduced.
-/

namespace Gtz

open Matrix

/-! ## The family and its atlas-blind residue -/

/-- The six equations and four positivity facts of the gauge-star wall family,
packaged for downstream consumers. -/
def KFourGaugeStarWallFamilyData (point : DirectionChartPoint 6)
    (z : Fin 3 → ℝ) (s : ℝ) : Prop :=
  0 < z 0 ∧ 0 < z 1 ∧ 0 < z 2 ∧ 0 < s ∧
  point.mass 0 = s * (z 0 * z 1) ∧
  point.mass 1 = s * (z 0 * z 2) ∧
  point.mass 2 = s * (z 1 * z 2) ∧
  point.mass 3 * (1 - point.weight 3)
    = s * (z 0 * (z 0 + z 1 + z 2)) * point.weight 3 ∧
  point.mass 4 * (1 - point.weight 4)
    = s * (z 1 * (z 0 + z 1 + z 2)) * point.weight 4 ∧
  point.mass 5 * (1 - point.weight 5)
    = s * (z 2 * (z 0 + z 1 + z 2)) * point.weight 5

/-- At an atlas-blind gauge-star wall, either coordinate zero is not maximal or
one of the four weights used by the balanced vertex-a certificate is heavy. -/
def KFourGaugeStarWallAtlasBlindData (point : DirectionChartPoint 6) : Prop :=
  ∃ (z : Fin 3 → ℝ) (s : ℝ),
    KFourGaugeStarWallFamilyData point z s ∧
    (z 0 < z 1 ∨ z 0 < z 2 ∨
      1 < 6 * point.weight 0 ∨ 1 < 6 * point.weight 1 ∨
      1 < 6 * point.weight 4 ∨ 1 < 6 * point.weight 5)

/-- The balanced atlas theorem, contraposed against the atlas-silence premise
that is already present in A3. -/
theorem kFourGaugeStarWallAtlasBlindData_of_atlasSilent
    (point : DirectionChartPoint 6)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point
      ({3, 4, 5} : Finset (Fin 6)))
    (hnotAtlas : ¬ KFourAllTreeMinorAtlasCellFires point) :
    KFourGaugeStarWallAtlasBlindData point := by
  obtain ⟨z, s, hz0, hz1, hz2, hs, hm0, hm1, hm2, hd3, hd4, hd5⟩ :=
    kFourGaugeStarWall_family point hpsd hcorank
  refine ⟨z, s, ⟨hz0, hz1, hz2, hs, hm0, hm1, hm2, hd3, hd4, hd5⟩, ?_⟩
  by_cases hmax1 : z 1 ≤ z 0
  · by_cases hmax2 : z 2 ≤ z 0
    · by_cases hw0 : 6 * point.weight 0 ≤ 1
      · by_cases hw1 : 6 * point.weight 1 ≤ 1
        · by_cases hw4 : 6 * point.weight 4 ≤ 1
          · by_cases hw5 : 6 * point.weight 5 ≤ 1
            · exfalso
              exact hnotAtlas (kFourAtlas_fires_of_wall_balanced point
                hz0 hz1 hz2 hs hm0 hm1 hm2 hd3 hd4 hd5 hmax1 hmax2
                hw0 hw1 hw4 hw5)
            · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
                (lt_of_not_ge hw5)))))
          · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
              (lt_of_not_ge hw4)))))
        · exact Or.inr (Or.inr (Or.inr (Or.inl (lt_of_not_ge hw1))))
      · exact Or.inr (Or.inr (Or.inl (lt_of_not_ge hw0)))
    · exact Or.inr (Or.inl (lt_of_not_ge hmax2))
  · exact Or.inl (lt_of_not_ge hmax1)

/-! ## Refine the exact star residual -/

/-- The refused-exchange wall, with the landed balanced-vacuity consequence
attached whenever its tree is the gauge star. -/
def KFourTreeStarRefusedAtlasBlindWallData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  KFourTreeStarRefusedExchangeWallData point tree ∧
  (tree = ({3, 4, 5} : Finset (Fin 6)) →
    KFourGaugeStarWallAtlasBlindData point)

def KFourWeakTreeStarRefusedAtlasBlindWallResidual
    (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList,
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourTreeWindowData point tree ∧
    (KFourTreeWindowAllPivotWallData point tree ∨
      KFourTreeStarRefusedAtlasBlindWallData point tree)

/-- Spend atlas silence to attach the balanced-vacuity consequence to a gauge
star witness. -/
theorem kFourWeakTreeStarRefusedAtlasBlindWallResidual_of_refusedExchangeResidual
    (point : DirectionChartPoint 6)
    (hnotAtlas : ¬ KFourAllTreeMinorAtlasCellFires point)
    (hwitness : KFourWeakTreeStarRefusedExchangeWallResidual point) :
    KFourWeakTreeStarRefusedAtlasBlindWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · refine ⟨tree, htree, hgap, hwindow, Or.inr ⟨hstar, ?_⟩⟩
    intro htreeEq
    subst tree
    exact kFourGaugeStarWallAtlasBlindData_of_atlasSilent point hgap
      hstar.1.2.1 hnotAtlas

/-- Forgetting the atlas-blind family alternative recovers the preceding exact
residual. -/
theorem kFourWeakTreeStarRefusedExchangeWallResidual_of_atlasBlindResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeStarRefusedAtlasBlindWallResidual point) :
    KFourWeakTreeStarRefusedExchangeWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hgap, hwindow, Or.inr hstar.1⟩

/-! ## The exact A3 joint -/

/-- **THE BALANCED-VACUITY A3 JOINT.**  The gauge-star branch explicitly lies
outside the balanced region already killed by the unsigned atlas. -/
noncomputable def KFourKnifeBandRefinedTreeStarRefusedAtlasBlindWallWeakToStrict :
    Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakTreeStarRefusedAtlasBlindWallResidual point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem kFourKnifeBandRefinedTreeStarRefusedAtlasBlindWall_iff_refusedExchange :
    KFourKnifeBandRefinedTreeStarRefusedAtlasBlindWallWeakToStrict ↔
      KFourKnifeBandRefinedTreeStarRefusedExchangeWallWeakToStrict := by
  constructor
  · intro hblind point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hblind point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarRefusedAtlasBlindWallResidual_of_refusedExchangeResidual
        point hnotAtlas hwitness)
  · intro hrefused point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hrefused point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarRefusedExchangeWallResidual_of_atlasBlindResidual
        point hwitness)

theorem kFourKnifeBandRefinedTreeStarRefusedAtlasBlindWall_iff :
    KFourKnifeBandRefinedTreeStarRefusedAtlasBlindWallWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedAtlasBlindWall_iff_refusedExchange.trans
    kFourKnifeBandRefinedTreeStarRefusedExchangeWall_iff

theorem kFourFamilySelection_iff_treeStarRefusedAtlasBlindWall :
    KFourFamilySelection ↔
      KFourKnifeBandRefinedTreeStarRefusedAtlasBlindWallWeakToStrict :=
  kFourFamilySelection_iff_treeStarRefusedExchangeWall.trans
    kFourKnifeBandRefinedTreeStarRefusedAtlasBlindWall_iff_refusedExchange.symm

end Gtz
