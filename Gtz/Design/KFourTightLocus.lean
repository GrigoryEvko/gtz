import Gtz.Design.KFourBandAtlas

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-- A K4 chart point on the tight boundary: one spanning-tree gap is PSD and
singular, while no spanning-tree gap is positive definite. -/
def KFourHasTightNoStrictPoint : Prop :=
  exists point : DirectionChartPoint 6,
    exists tightTree : Finset (Fin 6),
      tightTree ∈ kFourSpanningTreeList ∧
        (directionChartGap kFourDirection point.mass point.weight tightTree).PosSemidef ∧
        exists tightDir : Fin 3 -> Real,
          tightDir ≠ 0 ∧
            (directionChartGap kFourDirection point.mass point.weight tightTree) *ᵥ tightDir = 0 ∧
            ∀ candidate, candidate ∈ kFourSpanningTreeList ->
              ¬ (directionChartGap kFourDirection point.mass point.weight candidate).PosDef

/-- A PSD but non-PD K4 tree gap supplies an explicit nonzero kernel vector. -/
theorem exists_kFourTightDirection_of_posSemidef_not_posDef
    (point : DirectionChartPoint 6) (tree : Finset (Fin 6))
    (hpsd : (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef)
    (hnotPosDef :
      ¬ (directionChartGap kFourDirection point.mass point.weight tree).PosDef) :
    exists tightDir : Fin 3 -> Real, tightDir ≠ 0 ∧
      (directionChartGap kFourDirection point.mass point.weight tree) *ᵥ tightDir = 0 := by
  let gap := directionChartGap kFourDirection point.mass point.weight tree
  have hnotPositive :
      ¬ (∀ x : Fin 3 -> Real, x ≠ 0 -> 0 < star x ⬝ᵥ (gap *ᵥ x)) := by
    intro hpositive
    exact hnotPosDef
      (Matrix.posDef_iff_dotProduct_mulVec.mpr <| And.intro hpsd.1 hpositive)
  push Not at hnotPositive
  obtain ⟨tightDir, htightNe, htightLe⟩ := hnotPositive
  have htightGe : 0 <= star tightDir ⬝ᵥ (gap *ᵥ tightDir) :=
    (Matrix.posSemidef_iff_dotProduct_mulVec.mp hpsd).2 tightDir
  have htightEq : star tightDir ⬝ᵥ (gap *ᵥ tightDir) = 0 :=
    le_antisymm htightLe htightGe
  exact ⟨tightDir, htightNe,
    (Matrix.PosSemidef.dotProduct_mulVec_zero_iff hpsd tightDir).mp htightEq⟩

/-- Excluding tight nowhere-strict points gives the ordinary K4 chart
tie-freeness statement. -/
theorem directionChartIsTieFree_kFour_of_no_tightNoStrict
    (hnoTight : ¬ KFourHasTightNoStrictPoint) :
    DirectionChartIsTieFree kFourDirection := by
  intro point hweak
  by_contra hnoStrict
  push Not at hnoStrict
  obtain ⟨weakSet, hweakCard, hweakPsd⟩ := hweak
  have hweakTree : weakSet ∈ kFourSpanningTreeList := by
    rcases cardThreeSubset_isSpanningTreeOrDependentTriple weakSet hweakCard with htree | hdep
    · exact htree
    · exact False.elim
        (kFourDependentTriple_gap_not_posSemidef point weakSet hdep hweakPsd)
  have hallNoStrict : ∀ candidate, candidate ∈ kFourSpanningTreeList ->
      ¬ (directionChartGap kFourDirection point.mass point.weight candidate).PosDef := by
    intro candidate hcandidate hcandidatePosDef
    exact hnoStrict candidate (kFourSpanningTree_card candidate hcandidate) hcandidatePosDef
  obtain ⟨tightDir, htightNe, htightKernel⟩ :=
    exists_kFourTightDirection_of_posSemidef_not_posDef point weakSet hweakPsd
      (hallNoStrict weakSet hweakTree)
  exact hnoTight ⟨point, weakSet, hweakTree, hweakPsd, tightDir, htightNe,
    htightKernel, hallNoStrict⟩

/-- K4 chart tie-freeness already implies the antecedent-free statement, by
the connectedness collapse proved in `KFourBandAtlas`. -/
theorem everyPointHasStrictTree_of_directionChartIsTieFree_kFour
    (htieFree : DirectionChartIsTieFree kFourDirection) :
    KFourEveryPointHasStrictTree := by
  apply everyPointHasStrictTree_of_kFourKnifeBandRefined
  intro point _ _ hweakTree
  have hweak : exists selected : Finset (Fin 6), selected.card = 3 ∧
      (directionChartGap kFourDirection point.mass point.weight selected).PosSemidef := by
    obtain ⟨tree, htree, hpsd⟩ := hweakTree
    exact ⟨tree, kFourSpanningTree_card tree htree, hpsd⟩
  obtain ⟨selected, hcard, hposDef⟩ := htieFree point hweak
  exact ⟨selected, kFourStrictTriple_isSpanningTree point selected hcard hposDef, hposDef⟩

/-- The precise K4 tight-point reduction proposed by the research plan. -/
theorem kFourEveryPointHasStrictTree_iff_no_tightNoStrict :
    KFourEveryPointHasStrictTree ↔ ¬ KFourHasTightNoStrictPoint := by
  constructor
  · intro hstrict htight
    obtain ⟨point, _, _, _, _, _, _, hallNoStrict⟩ := htight
    obtain ⟨tree, htree, htreePosDef⟩ := hstrict point
    exact hallNoStrict tree htree htreePosDef
  · intro hnoTight
    exact everyPointHasStrictTree_of_directionChartIsTieFree_kFour
      (directionChartIsTieFree_kFour_of_no_tightNoStrict hnoTight)

end Gtz
