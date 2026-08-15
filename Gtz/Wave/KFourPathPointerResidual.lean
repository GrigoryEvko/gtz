import Gtz.Wave.KFourPathStarResidual
import Gtz.Design.KernelPointer

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# Point every saturated K4 path at its repair label

The path/star residual exposes a nonzero null vector whenever its realized weak
tree is a path.  The kernel-pointer theorem can be applied to that same vector,
without choosing a new failed direction.  It produces an outside label such
that every selection containing the label reads strictly positively at the
path's null vector.

This module records the composition and makes it the exact A3 consumer.  The
path branch now contains both sides of a repair step:

* the old path is zero in the tight direction;
* every selection through the outside pointer is positive in that direction.

The vertex-star branch is unchanged.  The resulting formula is again exactly
equivalent to the public K4 residual and the whitening-family selector.
-/

namespace Gtz

open Matrix

/-! ## The path pointer package -/

/-- The consumer-facing repair data attached to one saturated path. -/
def KFourPathPointerData (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) : Prop :=
  ∃ (tightDirection : Fin 3 → ℝ) (pointer : Fin 6),
    tightDirection ≠ 0 ∧ pointer ∉ selected ∧
    directionChartGap kFourDirection point.mass point.weight selected *ᵥ tightDirection = 0 ∧
    ∀ swap : Finset (Fin 6), pointer ∈ swap →
      0 < tightDirection ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight swap *ᵥ tightDirection)

/-- A concrete pulled-back Z-kernel on a K4 path supplies a pointer for the
same tight direction. -/
theorem kFourPathPointerData_of_dualTightData (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (htree : selected ∈ kFourSpanningTreeList)
    (zMatrix : Matrix (Fin 3) (Fin 3) ℝ)
    (probe : (Fin 3 → ℝ) → (Fin 3 → ℝ))
    (hdata : KFourPathDualTightData point selected zMatrix probe) :
    KFourPathPointerData point selected := by
  rcases hdata with
    ⟨yOne, yTwo, yThree, _, _, _, _, _, hprobeNe, hgapKernel⟩
  let y : Fin 3 → ℝ := ![yOne, yTwo, yThree]
  let tightDirection : Fin 3 → ℝ := probe y
  have htightNe : tightDirection ≠ 0 := by
    simpa only [tightDirection, y] using hprobeNe
  have htightKernel : directionChartGap kFourDirection point.mass point.weight selected
      *ᵥ tightDirection = 0 := by
    simpa only [tightDirection, y] using hgapKernel
  have hcardThree : selected.card = 3 := by
    have hall : ∀ tree ∈ kFourSpanningTreeList, tree.card = 3 := by decide
    exact hall selected htree
  have hcardTwo : 2 ≤ selected.card := by omega
  have hnonpos : tightDirection ⬝ᵥ
      (directionChartGap kFourDirection point.mass point.weight selected
        *ᵥ tightDirection) ≤ 0 := by
    rw [htightKernel, dotProduct_zero]
  obtain ⟨pointer, hpointerOut, hpointerReads⟩ :=
    exists_outside_pointer_of_nonpos_reading kFourDirection point.mass point.weight
      point.mass_pos point.weight_pos point.weight_sum_one kFourDirection_span
      hcardTwo htightNe hnonpos
  exact ⟨tightDirection, pointer, htightNe, hpointerOut, htightKernel, hpointerReads⟩

/-- The realized weak path, now carrying its null direction and outside repair
pointer rather than the internal Z-coordinate witness. -/
def KFourWeakPathPointerWitness (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList, tree ∉ kFourStarList ∧
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourPathPointerData point tree

/-- The exact weak branch after composing path saturation with the pointer
theorem. -/
def KFourWeakPathPointerOrStar (point : DirectionChartPoint 6) : Prop :=
  KFourWeakPathPointerWitness point ∨ KFourWeakStarWitness point

theorem kFourWeakPathPointerOrStar_of_kernelOrStar
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakPathKernelOrStar point) :
    KFourWeakPathPointerOrStar point := by
  rcases hwitness with hpath | hstar
  · obtain ⟨tree, htree, hnotStar, hweak, zMatrix, probe, hdata⟩ := hpath
    exact Or.inl ⟨tree, htree, hnotStar, hweak,
      kFourPathPointerData_of_dualTightData point tree htree zMatrix probe hdata⟩
  · exact Or.inr hstar

/-- Forgetting the pointer data recovers an ordinary weak spanning tree. -/
theorem exists_weakTree_of_kFourWeakPathPointerOrStar
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakPathPointerOrStar point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef := by
  rcases hwitness with hpath | hstar
  · obtain ⟨tree, htree, _, hweak, _⟩ := hpath
    exact ⟨tree, htree, hweak⟩
  · obtain ⟨star, hstar, hweak⟩ := hstar
    exact ⟨star, kFourStarList_subset_treeList star hstar, hweak⟩

/-! ## Spend the pointer package in A3 -/

/-- The exact K4 residual with the realized path repair step fully attached.
Only a weak vertex star avoids the pointer package. -/
noncomputable def KFourKnifeBandRefinedPathPointerOrStarWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakPathPointerOrStar point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem pathPointerOrStarKFourKnifeBandRefined_of_pathKernelOrStar
    (hkernel : KFourKnifeBandRefinedPathKernelOrStarWeakToStrict) :
    KFourKnifeBandRefinedPathPointerOrStarWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hwitness
  have hallPaths := kFourAllPathDualSaturationLedger_of_allTreeBlind point hnotAtlas
  have hkernelOrStar := kFourWeakPathKernelOrStar_of_allPathLedger point hallPaths
    (exists_weakTree_of_kFourWeakPathPointerOrStar point hwitness)
  exact hkernel point hnotLayerA hnotExchange hnotAtlas hledger hkernelOrStar

theorem pathKernelOrStarKFourKnifeBandRefined_of_pathPointerOrStar
    (hpointer : KFourKnifeBandRefinedPathPointerOrStarWeakToStrict) :
    KFourKnifeBandRefinedPathKernelOrStarWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hwitness
  exact hpointer point hnotLayerA hnotExchange hnotAtlas hledger
    (kFourWeakPathPointerOrStar_of_kernelOrStar point hwitness)

theorem kFourKnifeBandRefinedPathPointerOrStar_iff_pathKernelOrStar :
    KFourKnifeBandRefinedPathPointerOrStarWeakToStrict ↔
      KFourKnifeBandRefinedPathKernelOrStarWeakToStrict :=
  ⟨pathKernelOrStarKFourKnifeBandRefined_of_pathPointerOrStar,
    pathPointerOrStarKFourKnifeBandRefined_of_pathKernelOrStar⟩

theorem kFourKnifeBandRefinedPathPointerOrStar_iff :
    KFourKnifeBandRefinedPathPointerOrStarWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedPathPointerOrStar_iff_pathKernelOrStar.trans
    kFourKnifeBandRefinedPathKernelOrStar_iff

theorem kFourFamilySelection_iff_pathPointerOrStar :
    KFourFamilySelection ↔ KFourKnifeBandRefinedPathPointerOrStarWeakToStrict :=
  kFourFamilySelection_iff_pathKernelOrStar.trans
    kFourKnifeBandRefinedPathPointerOrStar_iff_pathKernelOrStar.symm

end Gtz
