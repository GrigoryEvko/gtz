import Gtz.Wave.KFourStarMirrorVacuityWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# Retain every maximal-axis star certificate on the K4 gauge wall

`KFourGaugeStarWallMaxHeavyData` records one maximal coordinate and the heavy
weight forced by its vertex-star certificate.  At a tie between axis
coordinates, however, atlas silence makes more than one certificate available.
Choosing a single disjunct loses that information.

This module retains all three certificates as implications over the same wall
coordinates.  It then spends their overlap geometry:

* if two coordinates tie for the maximum, either their two certificates use
  distinct heavy labels or their common heavy label lies on the exact opposite
  edge pair given by the intersection of the two four-slot covers;
* if all three coordinates are equal, at least two distinct labels are heavy,
  because the three four-slot covers have empty total intersection.

The final section attaches the simultaneous data to the live A3 residual and
proves equivalence with the preceding residual under the already-present atlas
silence hypothesis.
-/

namespace Gtz

open Matrix

/-! ## The three exact heavy covers -/

/-- A raw chart weight is heavy at the balanced threshold. -/
def KFourWeightHeavy (point : DirectionChartPoint 6) (label : Fin 6) : Prop :=
  1 < 6 * point.weight label

/-- The four labels read by the vertex-a balanced star certificate. -/
def kFourStarAHeavyCover : Finset (Fin 6) := {0, 1, 4, 5}

/-- The four labels read by the vertex-b balanced star certificate. -/
def kFourStarBHeavyCover : Finset (Fin 6) := {0, 2, 3, 5}

/-- The four labels read by the vertex-c balanced star certificate. -/
def kFourStarCHeavyCover : Finset (Fin 6) := {1, 2, 3, 4}

/-- The exact intersection of the a- and b-star heavy covers. -/
def kFourStarABOppositeCover : Finset (Fin 6) := {0, 5}

/-- The exact intersection of the a- and c-star heavy covers. -/
def kFourStarACOppositeCover : Finset (Fin 6) := {1, 4}

/-- The exact intersection of the b- and c-star heavy covers. -/
def kFourStarBCOppositeCover : Finset (Fin 6) := {2, 3}

/-- Two distinct labels carry weight strictly above one sixth. -/
def KFourHasTwoDistinctHeavyWeights (point : DirectionChartPoint 6) : Prop :=
  ∃ first second : Fin 6, first ≠ second ∧
    KFourWeightHeavy point first ∧ KFourWeightHeavy point second

/-! ## Simultaneous maximal-axis data -/

/-- The gauge-wall family together with all three conditional balanced
certificates.  Unlike `KFourGaugeStarWallMaxHeavyData`, no maximal-axis
certificate is discarded when two coordinates tie. -/
structure KFourGaugeStarWallAllMaxHeavyWitness
    (point : DirectionChartPoint 6) where
  z : Fin 3 → ℝ
  s : ℝ
  family : KFourGaugeStarWallFamilyData point z s
  heavyA : (z 1 ≤ z 0 ∧ z 2 ≤ z 0) →
    ∃ label ∈ kFourStarAHeavyCover, KFourWeightHeavy point label
  heavyB : (z 0 ≤ z 1 ∧ z 2 ≤ z 1) →
    ∃ label ∈ kFourStarBHeavyCover, KFourWeightHeavy point label
  heavyC : (z 0 ≤ z 2 ∧ z 1 ≤ z 2) →
    ∃ label ∈ kFourStarCHeavyCover, KFourWeightHeavy point label

/-- Mere existence of one wall witness carrying all three maximal-axis
certificates. -/
def KFourGaugeStarWallAllMaxHeavyData (point : DirectionChartPoint 6) : Prop :=
  Nonempty (KFourGaugeStarWallAllMaxHeavyWitness point)

/-- A stable representative of the simultaneous wall data.  This is used only
to state consequences about equal coordinates of the retained witness. -/
noncomputable def kFourGaugeStarWallAllMaxHeavyWitness
    (point : DirectionChartPoint 6)
    (hdata : KFourGaugeStarWallAllMaxHeavyData point) :
    KFourGaugeStarWallAllMaxHeavyWitness point :=
  Classical.choice hdata

/-- Atlas silence supplies all three maximal-axis certificates over the one
wall-family witness. -/
theorem kFourGaugeStarWallAllMaxHeavyData_of_atlasSilent
    (point : DirectionChartPoint 6)
    (hpsd : (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point
      ({3, 4, 5} : Finset (Fin 6)))
    (hnotAtlas : ¬ KFourAllTreeMinorAtlasCellFires point) :
    KFourGaugeStarWallAllMaxHeavyData point := by
  obtain ⟨z, s, hz0, hz1, hz2, hs, hm0, hm1, hm2, hd3, hd4, hd5⟩ :=
    kFourGaugeStarWall_family point hpsd hcorank
  have hfamily : KFourGaugeStarWallFamilyData point z s :=
    ⟨hz0, hz1, hz2, hs, hm0, hm1, hm2, hd3, hd4, hd5⟩
  refine ⟨⟨z, s, hfamily, ?_, ?_, ?_⟩⟩
  · rintro ⟨hmax1, hmax2⟩
    have hheavy := fourWay_lt_of_not_all_le (a := 6 * point.weight 0)
      (b := 6 * point.weight 1) (c := 6 * point.weight 4)
      (d := 6 * point.weight 5) (bound := 1) (by
        intro hsmall
        exact hnotAtlas (kFourAtlas_fires_of_wall_balanced point
          hz0 hz1 hz2 hs hm0 hm1 hm2 hd3 hd4 hd5 hmax1 hmax2
          hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2))
    rcases hheavy with h0 | h1 | h4 | h5
    · exact ⟨0, by decide, h0⟩
    · exact ⟨1, by decide, h1⟩
    · exact ⟨4, by decide, h4⟩
    · exact ⟨5, by decide, h5⟩
  · rintro ⟨hmax0, hmax2⟩
    have hheavy := fourWay_lt_of_not_all_le (a := 6 * point.weight 0)
      (b := 6 * point.weight 2) (c := 6 * point.weight 3)
      (d := 6 * point.weight 5) (bound := 1) (by
        intro hsmall
        exact hnotAtlas (kFourAtlas_fires_of_wall_balancedB point
          hz0 hz1 hz2 hs hm0 hm1 hm2 hd3 hd4 hd5 hmax0 hmax2
          hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2))
    rcases hheavy with h0 | h2 | h3 | h5
    · exact ⟨0, by decide, h0⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨3, by decide, h3⟩
    · exact ⟨5, by decide, h5⟩
  · rintro ⟨hmax0, hmax1⟩
    have hheavy := fourWay_lt_of_not_all_le (a := 6 * point.weight 1)
      (b := 6 * point.weight 2) (c := 6 * point.weight 3)
      (d := 6 * point.weight 4) (bound := 1) (by
        intro hsmall
        exact hnotAtlas (kFourAtlas_fires_of_wall_balancedC point
          hz0 hz1 hz2 hs hm0 hm1 hm2 hd3 hd4 hd5 hmax0 hmax1
          hsmall.1 hsmall.2.1 hsmall.2.2.1 hsmall.2.2.2))
    rcases hheavy with h1 | h2 | h3 | h4
    · exact ⟨1, by decide, h1⟩
    · exact ⟨2, by decide, h2⟩
    · exact ⟨3, by decide, h3⟩
    · exact ⟨4, by decide, h4⟩

/-- Forgetting tied-axis information recovers the preceding maximal-axis
disjunction. -/
theorem kFourGaugeStarWallMaxHeavyData_of_allMaxHeavyData
    (point : DirectionChartPoint 6)
    (hdata : KFourGaugeStarWallAllMaxHeavyData point) :
    KFourGaugeStarWallMaxHeavyData point := by
  obtain ⟨⟨z, s, hfamily, hA, hB, hC⟩⟩ := hdata
  refine ⟨z, s, hfamily, ?_⟩
  by_cases hmaxA1 : z 1 ≤ z 0
  · by_cases hmaxA2 : z 2 ≤ z 0
    · obtain ⟨label, hmem, hheavy⟩ := hA ⟨hmaxA1, hmaxA2⟩
      refine Or.inl ⟨hmaxA1, hmaxA2, ?_⟩
      fin_cases label <;>
        simp_all [kFourStarAHeavyCover, KFourWeightHeavy]
    · have hmaxC0 : z 0 ≤ z 2 := (lt_of_not_ge hmaxA2).le
      have hmaxC1 : z 1 ≤ z 2 := hmaxA1.trans hmaxC0
      obtain ⟨label, hmem, hheavy⟩ := hC ⟨hmaxC0, hmaxC1⟩
      refine Or.inr (Or.inr ⟨hmaxC0, hmaxC1, ?_⟩)
      fin_cases label <;>
        simp_all [kFourStarCHeavyCover, KFourWeightHeavy]
  · have hmaxB0 : z 0 ≤ z 1 := (lt_of_not_ge hmaxA1).le
    by_cases hmaxB2 : z 2 ≤ z 1
    · obtain ⟨label, hmem, hheavy⟩ := hB ⟨hmaxB0, hmaxB2⟩
      refine Or.inr (Or.inl ⟨hmaxB0, hmaxB2, ?_⟩)
      fin_cases label <;>
        simp_all [kFourStarBHeavyCover, KFourWeightHeavy]
    · have hmaxC1 : z 1 ≤ z 2 := (lt_of_not_ge hmaxB2).le
      have hmaxC0 : z 0 ≤ z 2 := hmaxB0.trans hmaxC1
      obtain ⟨label, hmem, hheavy⟩ := hC ⟨hmaxC0, hmaxC1⟩
      refine Or.inr (Or.inr ⟨hmaxC0, hmaxC1, ?_⟩)
      fin_cases label <;>
        simp_all [kFourStarCHeavyCover, KFourWeightHeavy]

/-! ## The tied-axis consequences -/

/-- If the first two axes tie for the maximum, the a- and b-star certificates
either choose distinct heavy labels or their common label lies on the opposite
edge pair `{0,5}`. -/
theorem oppositeABHeavy_or_twoDistinct_of_equalMax
    (point : DirectionChartPoint 6)
    (hdata : KFourGaugeStarWallAllMaxHeavyData point)
    (heq : (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 0 =
      (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 1)
    (hmax : (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 2 ≤
      (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 0) :
    (∃ label ∈ kFourStarABOppositeCover, KFourWeightHeavy point label) ∨
      KFourHasTwoDistinctHeavyWeights point := by
  let witness := kFourGaugeStarWallAllMaxHeavyWitness point hdata
  obtain ⟨a, haMem, ha⟩ := witness.heavyA ⟨heq.ge, hmax⟩
  obtain ⟨b, hbMem, hb⟩ := witness.heavyB ⟨heq.le, by linarith⟩
  by_cases hab : a = b
  · left
    subst b
    refine ⟨a, ?_, ha⟩
    fin_cases a <;>
      simp [kFourStarAHeavyCover, kFourStarBHeavyCover,
        kFourStarABOppositeCover] at haMem hbMem ⊢
  · exact Or.inr ⟨a, b, hab, ha, hb⟩

/-- If the first and third axes tie for the maximum, the common-label residue
is the opposite edge pair `{1,4}`. -/
theorem oppositeACHeavy_or_twoDistinct_of_equalMax
    (point : DirectionChartPoint 6)
    (hdata : KFourGaugeStarWallAllMaxHeavyData point)
    (heq : (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 0 =
      (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 2)
    (hmax : (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 1 ≤
      (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 0) :
    (∃ label ∈ kFourStarACOppositeCover, KFourWeightHeavy point label) ∨
      KFourHasTwoDistinctHeavyWeights point := by
  let witness := kFourGaugeStarWallAllMaxHeavyWitness point hdata
  obtain ⟨a, haMem, ha⟩ := witness.heavyA ⟨hmax, heq.ge⟩
  obtain ⟨c, hcMem, hc⟩ := witness.heavyC ⟨heq.le, by linarith⟩
  by_cases hac : a = c
  · left
    subst c
    refine ⟨a, ?_, ha⟩
    fin_cases a <;>
      simp [kFourStarAHeavyCover, kFourStarCHeavyCover,
        kFourStarACOppositeCover] at haMem hcMem ⊢
  · exact Or.inr ⟨a, c, hac, ha, hc⟩

/-- If the second and third axes tie for the maximum, the common-label residue
is the opposite edge pair `{2,3}`. -/
theorem oppositeBCHeavy_or_twoDistinct_of_equalMax
    (point : DirectionChartPoint 6)
    (hdata : KFourGaugeStarWallAllMaxHeavyData point)
    (heq : (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 1 =
      (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 2)
    (hmax : (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 0 ≤
      (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 1) :
    (∃ label ∈ kFourStarBCOppositeCover, KFourWeightHeavy point label) ∨
      KFourHasTwoDistinctHeavyWeights point := by
  let witness := kFourGaugeStarWallAllMaxHeavyWitness point hdata
  obtain ⟨b, hbMem, hb⟩ := witness.heavyB ⟨hmax, heq.ge⟩
  obtain ⟨c, hcMem, hc⟩ := witness.heavyC ⟨by linarith, heq.le⟩
  by_cases hbc : b = c
  · left
    subst c
    refine ⟨b, ?_, hb⟩
    fin_cases b <;>
      simp [kFourStarBHeavyCover, kFourStarCHeavyCover,
        kFourStarBCOppositeCover] at hbMem hcMem ⊢
  · exact Or.inr ⟨b, c, hbc, hb, hc⟩

/-- On the fully symmetric axis, the three heavy covers cannot all be served by
one label: their total intersection is empty. -/
theorem exists_twoDistinctHeavy_of_equalAxes
    (point : DirectionChartPoint 6)
    (hdata : KFourGaugeStarWallAllMaxHeavyData point)
    (heq01 : (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 0 =
      (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 1)
    (heq02 : (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 0 =
      (kFourGaugeStarWallAllMaxHeavyWitness point hdata).z 2) :
    KFourHasTwoDistinctHeavyWeights point := by
  let witness := kFourGaugeStarWallAllMaxHeavyWitness point hdata
  obtain ⟨a, haMem, ha⟩ := witness.heavyA ⟨heq01.ge, heq02.ge⟩
  obtain ⟨b, hbMem, hb⟩ := witness.heavyB ⟨heq01.le, by linarith⟩
  obtain ⟨c, hcMem, hc⟩ := witness.heavyC ⟨heq02.le, by linarith⟩
  by_cases hab : a = b
  · by_cases hac : a = c
    · subst b
      subst c
      fin_cases a <;>
        simp [kFourStarAHeavyCover, kFourStarBHeavyCover,
          kFourStarCHeavyCover] at haMem hbMem hcMem
    · exact ⟨a, c, hac, ha, hc⟩
  · exact ⟨a, b, hab, ha, hb⟩

/-! ## Attach the simultaneous data to A3 -/

def KFourTreeStarRefusedAllMaxHeavyWallData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  KFourTreeStarRefusedAtlasBlindWallData point tree ∧
  (tree = ({3, 4, 5} : Finset (Fin 6)) →
    KFourGaugeStarWallAllMaxHeavyData point)

def KFourWeakTreeStarRefusedAllMaxHeavyWallResidual
    (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList,
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourTreeWindowData point tree ∧
    (KFourTreeWindowAllPivotWallData point tree ∨
      KFourTreeStarRefusedAllMaxHeavyWallData point tree)

theorem kFourWeakTreeStarRefusedAllMaxHeavyWallResidual_of_maxHeavyResidual
    (point : DirectionChartPoint 6)
    (hnotAtlas : ¬ KFourAllTreeMinorAtlasCellFires point)
    (hwitness : KFourWeakTreeStarRefusedMaxHeavyWallResidual point) :
    KFourWeakTreeStarRefusedAllMaxHeavyWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · refine ⟨tree, htree, hgap, hwindow, Or.inr ⟨hstar.1, ?_⟩⟩
    intro htreeEq
    subst tree
    exact kFourGaugeStarWallAllMaxHeavyData_of_atlasSilent point hgap
      hstar.1.1.1.2.1 hnotAtlas

theorem kFourWeakTreeStarRefusedMaxHeavyWallResidual_of_allMaxHeavyResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeStarRefusedAllMaxHeavyWallResidual point) :
    KFourWeakTreeStarRefusedMaxHeavyWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl hpivot⟩
  · refine ⟨tree, htree, hgap, hwindow, Or.inr ⟨hstar.1, ?_⟩⟩
    intro htreeEq
    exact kFourGaugeStarWallMaxHeavyData_of_allMaxHeavyData point
      (hstar.2 htreeEq)

noncomputable def KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :
    Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakTreeStarRefusedAllMaxHeavyWallResidual point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_iff_maxHeavy :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict ↔
      KFourKnifeBandRefinedTreeStarRefusedMaxHeavyWallWeakToStrict := by
  constructor
  · intro hall point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hall point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarRefusedAllMaxHeavyWallResidual_of_maxHeavyResidual
        point hnotAtlas hwitness)
  · intro hmax point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hmax point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarRefusedMaxHeavyWallResidual_of_allMaxHeavyResidual
        point hwitness)

theorem kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_iff :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_iff_maxHeavy.trans
    kFourKnifeBandRefinedTreeStarRefusedMaxHeavyWall_iff

theorem kFourFamilySelection_iff_treeStarRefusedAllMaxHeavyWall :
    KFourFamilySelection ↔
      KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  kFourFamilySelection_iff_treeStarRefusedMaxHeavyWall.trans
    kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_iff_maxHeavy.symm

end Gtz
