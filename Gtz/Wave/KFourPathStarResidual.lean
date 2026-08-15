import Gtz.Wave.KFourPriorPathDualSaturation

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# The exact K4 path-or-star residual

The K4 spanning-tree list consists of four vertex stars and twelve paths.  The
preceding saturation modules prove that, outside the complete minor atlas,
every weak path carries a nonzero tight direction obtained from its explicit
nonnegative Z-kernel.  This file spends that fact at the actual weak witness.

The resulting A3 formula no longer carries twelve unrelated conditional
saturation hypotheses beside an opaque sixteen-tree existential.  Its final
antecedent is the exact dichotomy:

* a weak path together with its pulled-back dual-kernel data; or
* a weak vertex star.

Thus the four stars are exposed as the only sign-frustrated branch.  The new
formula remains exactly equivalent to the public K4 residual and hence to the
design-side family selector.
-/

namespace Gtz

open Matrix

/-! ## Witness packages -/

/-- A weak path whose explicit unsigned Z-kernel has been pulled back to a
nonzero kernel direction of the actual chart gap. -/
def KFourWeakPathKernelWitness (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList, tree ∉ kFourStarList ∧
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    ∃ zMatrix : Matrix (Fin 3) (Fin 3) ℝ,
      ∃ probe : (Fin 3 → ℝ) → (Fin 3 → ℝ),
        KFourPathDualTightData point tree zMatrix probe

/-- A weak witness in the only remaining sign-frustrated tree orbit. -/
def KFourWeakStarWitness (point : DirectionChartPoint 6) : Prop :=
  ∃ star ∈ kFourStarList,
    (directionChartGap kFourDirection point.mass point.weight star).PosSemidef

/-- The exhaustive weak-tree dichotomy after all twelve paths are saturated. -/
def KFourWeakPathKernelOrStar (point : DirectionChartPoint 6) : Prop :=
  KFourWeakPathKernelWitness point ∨ KFourWeakStarWitness point

/-! ## Classify the realized weak tree -/

/-- The twelve-path saturation ledger classifies an arbitrary weak spanning
tree: the first four literal trees are stars, while each of the remaining
twelve has its corresponding concrete Z-matrix and pullback probe. -/
theorem kFourWeakPathKernelOrStar_of_allPathLedger
    (point : DirectionChartPoint 6)
    (hallPaths : KFourAllPathDualSaturationLedger point)
    (hweak : ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef) :
    KFourWeakPathKernelOrStar point := by
  obtain ⟨tree, htree, htreeWeak⟩ := hweak
  simp only [kFourSpanningTreeList, List.mem_cons, List.not_mem_nil, or_false] at htree
  rcases htree with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact Or.inr ⟨{0, 1, 3}, by decide, htreeWeak⟩
  · exact Or.inr ⟨{0, 2, 4}, by decide, htreeWeak⟩
  · exact Or.inr ⟨{1, 2, 5}, by decide, htreeWeak⟩
  · exact Or.inr ⟨{3, 4, 5}, by decide, htreeWeak⟩
  · exact Or.inl ⟨{0, 1, 4}, by decide, by decide, htreeWeak,
      kFourPath014ZMatrix point, kFourPath014Probe,
      hallPaths.2.2.2.2.2.1 htreeWeak⟩
  · exact Or.inl ⟨{0, 1, 5}, by decide, by decide, htreeWeak,
      kFourPath015ZMatrix point, kFourPath015Probe, hallPaths.2.1 htreeWeak⟩
  · exact Or.inl ⟨{0, 2, 3}, by decide, by decide, htreeWeak,
      kFourPendant023ZMatrix point, kFourPendant023Probe,
      hallPaths.1.2.1 htreeWeak⟩
  · exact Or.inl ⟨{0, 2, 5}, by decide, by decide, htreeWeak,
      kFourPath025ZMatrix point, kFourPath025Probe, hallPaths.2.2.1 htreeWeak⟩
  · exact Or.inl ⟨{0, 3, 5}, by decide, by decide, htreeWeak,
      kFourPath035ZMatrix point, kFourPath035Probe, hallPaths.2.2.2.1 htreeWeak⟩
  · exact Or.inl ⟨{0, 4, 5}, by decide, by decide, htreeWeak,
      kFourPath045ZMatrix point, kFourPath045Probe, hallPaths.2.2.2.2.1 htreeWeak⟩
  · exact Or.inl ⟨{1, 2, 3}, by decide, by decide, htreeWeak,
      kFourPendant123ZMatrix point, kFourPendant123Probe,
      hallPaths.1.2.2.1 htreeWeak⟩
  · exact Or.inl ⟨{1, 2, 4}, by decide, by decide, htreeWeak,
      kFourPath124ZMatrix point, kFourPath124Probe,
      hallPaths.2.2.2.2.2.2.1 htreeWeak⟩
  · exact Or.inl ⟨{1, 3, 4}, by decide, by decide, htreeWeak,
      kFourBand134ZMatrix point, kFourBand134Probe, hallPaths.1.1 htreeWeak⟩
  · exact Or.inl ⟨{1, 4, 5}, by decide, by decide, htreeWeak,
      kFourPath145ZMatrix point, kFourPath145Probe,
      hallPaths.2.2.2.2.2.2.2 htreeWeak⟩
  · exact Or.inl ⟨{2, 3, 4}, by decide, by decide, htreeWeak,
      kFourPendant234ZMatrix point, kFourPendant234Probe,
      hallPaths.1.2.2.2.1 htreeWeak⟩
  · exact Or.inl ⟨{2, 3, 5}, by decide, by decide, htreeWeak,
      kFourPendant235ZMatrix point, kFourPendant235Probe,
      hallPaths.1.2.2.2.2 htreeWeak⟩

/-- Forgetting the path kernel data, either branch is an ordinary weak
spanning-tree witness. -/
theorem exists_weakTree_of_kFourWeakPathKernelOrStar
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakPathKernelOrStar point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef := by
  rcases hwitness with hpath | hstar
  · obtain ⟨tree, htree, _, hweak, _⟩ := hpath
    exact ⟨tree, htree, hweak⟩
  · obtain ⟨star, hstar, hweak⟩ := hstar
    exact ⟨star, kFourStarList_subset_treeList star hstar, hweak⟩

/-! ## The exact A3 consumer -/

/-- The sharpened A3 residual after classifying the realized weak tree.  A
path arrives with its actual tight direction already attached.  A star is the
only remaining branch on which the unsigned dual cannot yet be pulled back. -/
noncomputable def KFourKnifeBandRefinedPathKernelOrStarWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakPathKernelOrStar point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem pathKernelOrStarKFourKnifeBandRefined_of_allPathSaturated
    (hallPaths : KFourKnifeBandRefinedAllPathSaturatedWeakToStrict) :
    KFourKnifeBandRefinedPathKernelOrStarWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hwitness
  exact hallPaths point hnotLayerA hnotExchange hnotAtlas hledger
    (kFourAllPathDualSaturationLedger_of_allTreeBlind point hnotAtlas)
    (exists_weakTree_of_kFourWeakPathKernelOrStar point hwitness)

theorem allPathSaturatedKFourKnifeBandRefined_of_pathKernelOrStar
    (hbranch : KFourKnifeBandRefinedPathKernelOrStarWeakToStrict) :
    KFourKnifeBandRefinedAllPathSaturatedWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hallPaths hweak
  exact hbranch point hnotLayerA hnotExchange hnotAtlas hledger
    (kFourWeakPathKernelOrStar_of_allPathLedger point hallPaths hweak)

theorem kFourKnifeBandRefinedPathKernelOrStar_iff_allPathSaturated :
    KFourKnifeBandRefinedPathKernelOrStarWeakToStrict ↔
      KFourKnifeBandRefinedAllPathSaturatedWeakToStrict :=
  ⟨allPathSaturatedKFourKnifeBandRefined_of_pathKernelOrStar,
    pathKernelOrStarKFourKnifeBandRefined_of_allPathSaturated⟩

theorem kFourKnifeBandRefinedPathKernelOrStar_iff :
    KFourKnifeBandRefinedPathKernelOrStarWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedPathKernelOrStar_iff_allPathSaturated.trans
    kFourKnifeBandRefinedAllPathSaturated_iff

theorem kFourFamilySelection_iff_pathKernelOrStar :
    KFourFamilySelection ↔ KFourKnifeBandRefinedPathKernelOrStarWeakToStrict :=
  kFourFamilySelection_iff_allPathSaturated.trans
    kFourKnifeBandRefinedPathKernelOrStar_iff_allPathSaturated.symm

end Gtz
