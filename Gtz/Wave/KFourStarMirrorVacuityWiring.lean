import Gtz.Design.StarWallMirrors
import Gtz.Wave.KFourStarBalancedVacuityWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# Spend all three balanced star-wall mirrors

The first vacuity wiring used only the vertex-a certificate.  The two mirror
certificates complete the maximal-axis split.  At an atlas-silent gauge-star
wall, whichever positive axis coordinate is maximal has a heavy weight in the
four slots read by its corresponding vertex-star certificate.

This is stronger than the bare existence of a weight above `1/6`: it retains
the coupling between the maximal coordinate and the precise four-slot cover.
The final section attaches that data to the exact A3 residual and proves the
usual equivalence with the preceding registered proposition.
-/

namespace Gtz

open Matrix

/-! ## A small order-theoretic dispatcher -/

theorem fourWay_lt_of_not_all_le {a b c d bound : ℝ}
    (hnot : ¬ (a ≤ bound ∧ b ≤ bound ∧ c ≤ bound ∧ d ≤ bound)) :
    bound < a ∨ bound < b ∨ bound < c ∨ bound < d := by
  by_cases ha : a ≤ bound
  · by_cases hb : b ≤ bound
    · by_cases hc : c ≤ bound
      · by_cases hd : d ≤ bound
        · exact False.elim (hnot ⟨ha, hb, hc, hd⟩)
        · exact Or.inr (Or.inr (Or.inr (lt_of_not_ge hd)))
      · exact Or.inr (Or.inr (Or.inl (lt_of_not_ge hc)))
    · exact Or.inr (Or.inl (lt_of_not_ge hb))
  · exact Or.inl (lt_of_not_ge ha)

/-! ## The maximal-axis/heavy-slot law -/

/-- The complete balanced-complement data at the gauge star.  One of the
three coordinates is maximal, and atlas silence forces a heavy weight in the
four slots read by that coordinate's vertex-star certificate. -/
def KFourGaugeStarWallMaxHeavyData (point : DirectionChartPoint 6) : Prop :=
  ∃ (z : Fin 3 → ℝ) (s : ℝ), KFourGaugeStarWallFamilyData point z s ∧
    ((z 1 ≤ z 0 ∧ z 2 ≤ z 0 ∧
        (1 < 6 * point.weight 0 ∨ 1 < 6 * point.weight 1 ∨
          1 < 6 * point.weight 4 ∨ 1 < 6 * point.weight 5)) ∨
      (z 0 ≤ z 1 ∧ z 2 ≤ z 1 ∧
        (1 < 6 * point.weight 0 ∨ 1 < 6 * point.weight 2 ∨
          1 < 6 * point.weight 3 ∨ 1 < 6 * point.weight 5)) ∨
      (z 0 ≤ z 2 ∧ z 1 ≤ z 2 ∧
        (1 < 6 * point.weight 1 ∨ 1 < 6 * point.weight 2 ∨
          1 < 6 * point.weight 3 ∨ 1 < 6 * point.weight 4)))

/-- The three balanced atlas certificates exhaust the maximal-axis cases, so
atlas silence forces the coupled heavy-slot alternative. -/
theorem kFourGaugeStarWallMaxHeavyData_of_atlasSilent
    (point : DirectionChartPoint 6)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point
      ({3, 4, 5} : Finset (Fin 6)))
    (hnotAtlas : ¬ KFourAllTreeMinorAtlasCellFires point) :
    KFourGaugeStarWallMaxHeavyData point := by
  obtain ⟨z, s, hz0, hz1, hz2, hs, hm0, hm1, hm2, hd3, hd4, hd5⟩ :=
    kFourGaugeStarWall_family point hpsd hcorank
  have hfamily : KFourGaugeStarWallFamilyData point z s :=
    ⟨hz0, hz1, hz2, hs, hm0, hm1, hm2, hd3, hd4, hd5⟩
  refine ⟨z, s, hfamily, ?_⟩
  by_cases hmaxA1 : z 1 ≤ z 0
  · by_cases hmaxA2 : z 2 ≤ z 0
    · refine Or.inl ⟨hmaxA1, hmaxA2, fourWay_lt_of_not_all_le ?_⟩
      intro hsmall
      exact hnotAtlas (kFourAtlas_fires_of_wall_balanced point
        hz0 hz1 hz2 hs hm0 hm1 hm2 hd3 hd4 hd5 hmaxA1 hmaxA2
        hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2)
    · have hmaxC0 : z 0 ≤ z 2 := (lt_of_not_ge hmaxA2).le
      have hmaxC1 : z 1 ≤ z 2 := le_trans hmaxA1 hmaxC0
      refine Or.inr (Or.inr ⟨hmaxC0, hmaxC1, fourWay_lt_of_not_all_le ?_⟩)
      intro hsmall
      exact hnotAtlas (kFourAtlas_fires_of_wall_balancedC point
        hz0 hz1 hz2 hs hm0 hm1 hm2 hd3 hd4 hd5 hmaxC0 hmaxC1
        hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2)
  · have hmaxB0 : z 0 ≤ z 1 := (lt_of_not_ge hmaxA1).le
    by_cases hmaxB2 : z 2 ≤ z 1
    · refine Or.inr (Or.inl ⟨hmaxB0, hmaxB2, fourWay_lt_of_not_all_le ?_⟩)
      intro hsmall
      exact hnotAtlas (kFourAtlas_fires_of_wall_balancedB point
        hz0 hz1 hz2 hs hm0 hm1 hm2 hd3 hd4 hd5 hmaxB0 hmaxB2
        hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2)
    · have hmaxC1 : z 1 ≤ z 2 := (lt_of_not_ge hmaxB2).le
      have hmaxC0 : z 0 ≤ z 2 := le_trans hmaxB0 hmaxC1
      refine Or.inr (Or.inr ⟨hmaxC0, hmaxC1, fourWay_lt_of_not_all_le ?_⟩)
      intro hsmall
      exact hnotAtlas (kFourAtlas_fires_of_wall_balancedC point
        hz0 hz1 hz2 hs hm0 hm1 hm2 hd3 hd4 hd5 hmaxC0 hmaxC1
        hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2)

/-- In particular, every atlas-silent gauge-star wall has a weight strictly
above `1/6`. -/
theorem exists_weight_gt_one_sixth_of_gaugeStarWall_atlasSilent
    (point : DirectionChartPoint 6)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point
      ({3, 4, 5} : Finset (Fin 6)))
    (hnotAtlas : ¬ KFourAllTreeMinorAtlasCellFires point) :
    ∃ label : Fin 6, 1 < 6 * point.weight label := by
  obtain ⟨z, s, hfamily, hA | hB | hC⟩ :=
    kFourGaugeStarWallMaxHeavyData_of_atlasSilent point hpsd hcorank hnotAtlas
  · rcases hA.2.2 with h0 | h1 | h4 | h5
    · exact ⟨0, h0⟩
    · exact ⟨1, h1⟩
    · exact ⟨4, h4⟩
    · exact ⟨5, h5⟩
  · rcases hB.2.2 with h0 | h2 | h3 | h5
    · exact ⟨0, h0⟩
    · exact ⟨2, h2⟩
    · exact ⟨3, h3⟩
    · exact ⟨5, h5⟩
  · rcases hC.2.2 with h1 | h2 | h3 | h4
    · exact ⟨1, h1⟩
    · exact ⟨2, h2⟩
    · exact ⟨3, h3⟩
    · exact ⟨4, h4⟩

/-! ## Attach the complete mirror consequence to A3 -/

def KFourTreeStarRefusedMaxHeavyWallData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  KFourTreeStarRefusedAtlasBlindWallData point tree ∧
  (tree = ({3, 4, 5} : Finset (Fin 6)) →
    KFourGaugeStarWallMaxHeavyData point)

def KFourWeakTreeStarRefusedMaxHeavyWallResidual
    (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList,
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourTreeWindowData point tree ∧
    (KFourTreeWindowAllPivotWallData point tree ∨
      KFourTreeStarRefusedMaxHeavyWallData point tree)

theorem kFourWeakTreeStarRefusedMaxHeavyWallResidual_of_atlasBlindResidual
    (point : DirectionChartPoint 6)
    (hnotAtlas : ¬ KFourAllTreeMinorAtlasCellFires point)
    (hwitness : KFourWeakTreeStarRefusedAtlasBlindWallResidual point) :
    KFourWeakTreeStarRefusedMaxHeavyWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · refine ⟨tree, htree, hgap, hwindow, Or.inr ⟨hstar, ?_⟩⟩
    intro htreeEq
    subst tree
    exact kFourGaugeStarWallMaxHeavyData_of_atlasSilent point hgap
      hstar.1.1.2.1 hnotAtlas

theorem kFourWeakTreeStarRefusedAtlasBlindWallResidual_of_maxHeavyResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeStarRefusedMaxHeavyWallResidual point) :
    KFourWeakTreeStarRefusedAtlasBlindWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hgap, hwindow, Or.inr hstar.1⟩

noncomputable def KFourKnifeBandRefinedTreeStarRefusedMaxHeavyWallWeakToStrict :
    Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakTreeStarRefusedMaxHeavyWallResidual point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem kFourKnifeBandRefinedTreeStarRefusedMaxHeavyWall_iff_atlasBlind :
    KFourKnifeBandRefinedTreeStarRefusedMaxHeavyWallWeakToStrict ↔
      KFourKnifeBandRefinedTreeStarRefusedAtlasBlindWallWeakToStrict := by
  constructor
  · intro hheavy point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hheavy point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarRefusedMaxHeavyWallResidual_of_atlasBlindResidual
        point hnotAtlas hwitness)
  · intro hblind point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hblind point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarRefusedAtlasBlindWallResidual_of_maxHeavyResidual
        point hwitness)

theorem kFourKnifeBandRefinedTreeStarRefusedMaxHeavyWall_iff :
    KFourKnifeBandRefinedTreeStarRefusedMaxHeavyWallWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedMaxHeavyWall_iff_atlasBlind.trans
    kFourKnifeBandRefinedTreeStarRefusedAtlasBlindWall_iff

theorem kFourFamilySelection_iff_treeStarRefusedMaxHeavyWall :
    KFourFamilySelection ↔
      KFourKnifeBandRefinedTreeStarRefusedMaxHeavyWallWeakToStrict :=
  kFourFamilySelection_iff_treeStarRefusedAtlasBlindWall.trans
    kFourKnifeBandRefinedTreeStarRefusedMaxHeavyWall_iff_atlasBlind.symm

end Gtz
