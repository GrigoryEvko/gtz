import Gtz.Wave.KFourPathWindowDichotomy
import Gtz.Design.StarSignRigidity

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# Remove the K4 path/star split at the pointer window

The path-window residual still treated a weak vertex star as an opaque second
branch.  The star-sign module lands the two generic facts needed to remove that
distinction:

* a positive-semidefinite, non-positive-definite `3 x 3` gap has a nonzero
  kernel vector;
* every nonzero kernel vector of a K4 selection gap hands an outside pointer.

Neither fact depends on the tree orbit.  Consequently every weak K4 spanning
tree is either already strict or carries the same pointer-window package.  The
window trichotomy then leaves only its two honest walls:

* a positive-definite four-edge window whose three deletion pivots are at
  least one;
* a singular four-edge window with a second kernel direction independent of
  the original tree kernel.

The final section makes this orbit-free residual the exact A3 consumer.  The
proof is an equivalence with the preceding path-window-or-star formula, so this
is a formula sharpening rather than a new assumption.
-/

namespace Gtz

open Matrix

/-! ## A pointer window for every weak non-strict K4 tree -/

/-- Orbit-free name for the pointer-window package.  The underlying theorem was
first proved on paths, but its statement and proof are generic in the selected
tree. -/
abbrev KFourTreeWindowData (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) : Prop :=
  KFourPathWindowData point selected

/-- Orbit-free name for the positive-definite final-pivot wall. -/
abbrev KFourTreeWindowPivotWallData (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) : Prop :=
  KFourPathWindowPivotWallData point selected

/-- Orbit-free name for the independent second-kernel wall. -/
abbrev KFourTreeWindowCorankTwoData (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) : Prop :=
  KFourPathWindowCorankTwoData point selected

/-- Any weak but non-strict K4 spanning tree carries the pointer-window data.
The construction is orbit-free: obtain a nonzero gap kernel, point it outside
the tree, and spend the pointer on the four-edge window. -/
theorem kFourTreeWindowData_of_posSemidef_not_posDef
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (htree : tree ∈ kFourSpanningTreeList)
    (hweak : (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef)
    (hnotStrict : ¬ (directionChartGap kFourDirection point.mass point.weight tree).PosDef) :
    KFourTreeWindowData point tree := by
  obtain ⟨tightDirection, htightNe, htightKernel⟩ :=
    exists_kernelVec_of_posSemidef_not_posDef
      (directionChartGap_transpose kFourDirection point.mass point.weight tree)
      hweak hnotStrict
  have hcardTwo : 2 ≤ tree.card := by
    rw [kFourSpanningTree_card tree htree]
    omega
  obtain ⟨pointer, hpointerOut, hpointerReads⟩ :=
    kFour_pointer_of_kernel point hcardTwo htightNe htightKernel
  exact kFourPathWindowData_of_pointerData point tree hweak
    ⟨tightDirection, pointer, htightNe, hpointerOut, htightKernel, hpointerReads⟩

/-! ## The orbit-free residual -/

/-- A weak K4 spanning tree after all successful pointer-window deletions have
been spent.  No path/star classifier remains in this package. -/
def KFourWeakTreeWindowResidual (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList,
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourTreeWindowData point tree ∧
    (KFourTreeWindowPivotWallData point tree ∨
      KFourTreeWindowCorankTwoData point tree)

/-- Every ordinary weak K4 spanning-tree witness either is already strict or
enters one of the two orbit-free pointer-window walls. -/
theorem exists_strictTree_or_kFourWeakTreeWindowResidual
    (point : DirectionChartPoint 6)
    (hweak : ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef) :
    (∃ strictTree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight strictTree).PosDef) ∨
    KFourWeakTreeWindowResidual point := by
  obtain ⟨tree, htree, htreeWeak⟩ := hweak
  by_cases htreeStrict :
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef
  · exact Or.inl ⟨tree, htree, htreeStrict⟩
  · have hwindow := kFourTreeWindowData_of_posSemidef_not_posDef
      point htree htreeWeak htreeStrict
    rcases exists_strictTree_or_windowPivotWall_or_corankTwo point htree hwindow with
      hstrict | hpivot | hcorankTwo
    · exact Or.inl hstrict
    · exact Or.inr ⟨tree, htree, htreeWeak, hwindow, Or.inl hpivot⟩
    · exact Or.inr ⟨tree, htree, htreeWeak, hwindow, Or.inr hcorankTwo⟩

/-- Forgetting the pointer-window deductions recovers an ordinary weak
spanning-tree witness. -/
theorem exists_weakTree_of_kFourWeakTreeWindowResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeWindowResidual point) :
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef := by
  obtain ⟨tree, htree, hweak, _hwindow, _hwall⟩ := hwitness
  exact ⟨tree, htree, hweak⟩

/-- The orbit-free residual still refines the preceding path-window-or-star
witness: classify only the selected tree, not its analytic construction. -/
theorem kFourWeakPathWindowResidualOrStar_of_treeWindowResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeWindowResidual point) :
    KFourWeakPathWindowResidualOrStar point := by
  obtain ⟨tree, htree, hweak, hwindow, hwall⟩ := hwitness
  by_cases hstar : tree ∈ kFourStarList
  · exact Or.inr ⟨tree, hstar, hweak⟩
  · exact Or.inl ⟨tree, htree, hstar, hweak, hwindow, hwall⟩

/-! ## Make the orbit-free residual the exact A3 consumer -/

/-- **THE ORBIT-FREE A3 JOINT.**  The registered axiom sees neither paths nor
stars.  Its only analytic alternatives are the exact pivot wall and the
corank-two pointer window. -/
noncomputable def KFourKnifeBandRefinedTreeWindowResidualWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakTreeWindowResidual point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- The preceding path-window-or-star residual proves the orbit-free one by
forgetting only the selected tree's orbit. -/
theorem treeWindowResidualKFourKnifeBandRefined_of_pathWindowResidualOrStar
    (hprevious : KFourKnifeBandRefinedPathWindowResidualOrStarWeakToStrict) :
    KFourKnifeBandRefinedTreeWindowResidualWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hwitness
  exact hprevious point hnotLayerA hnotExchange hnotAtlas hledger
    (kFourWeakPathWindowResidualOrStar_of_treeWindowResidual point hwitness)

/-- Conversely, split an arbitrary weak path-or-star witness through the
orbit-free tree window.  A successful window closes immediately; otherwise the
new residual is exactly the remaining input. -/
theorem pathWindowResidualOrStarKFourKnifeBandRefined_of_treeWindowResidual
    (horbitFree : KFourKnifeBandRefinedTreeWindowResidualWeakToStrict) :
    KFourKnifeBandRefinedPathWindowResidualOrStarWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hwitness
  have hwindowOrStar := kFourWeakPathWindowOrStar_of_residualOrStar point hwitness
  have hpointerOrStar := kFourWeakPathPointerOrStar_of_windowOrStar point hwindowOrStar
  have hweak := exists_weakTree_of_kFourWeakPathPointerOrStar point hpointerOrStar
  rcases exists_strictTree_or_kFourWeakTreeWindowResidual point hweak with
    hstrict | hresidual
  · exact hstrict
  · exact horbitFree point hnotLayerA hnotExchange hnotAtlas hledger hresidual

/-- Removing the path/star split preserves the exact preceding A3 formula. -/
theorem kFourKnifeBandRefinedTreeWindowResidual_iff_pathWindowResidualOrStar :
    KFourKnifeBandRefinedTreeWindowResidualWeakToStrict ↔
      KFourKnifeBandRefinedPathWindowResidualOrStarWeakToStrict :=
  ⟨pathWindowResidualOrStarKFourKnifeBandRefined_of_treeWindowResidual,
    treeWindowResidualKFourKnifeBandRefined_of_pathWindowResidualOrStar⟩

/-- The orbit-free pointer-window residual is exactly the public refined K4
knife band. -/
theorem kFourKnifeBandRefinedTreeWindowResidual_iff :
    KFourKnifeBandRefinedTreeWindowResidualWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedTreeWindowResidual_iff_pathWindowResidualOrStar.trans
    kFourKnifeBandRefinedPathWindowResidualOrStar_iff

/-- The design-side K4 family selector is exactly the orbit-free pointer-window
residual. -/
theorem kFourFamilySelection_iff_treeWindowResidual :
    KFourFamilySelection ↔ KFourKnifeBandRefinedTreeWindowResidualWeakToStrict :=
  kFourFamilySelection_iff_pathWindowResidualOrStar.trans
    kFourKnifeBandRefinedTreeWindowResidual_iff_pathWindowResidualOrStar.symm

end Gtz
