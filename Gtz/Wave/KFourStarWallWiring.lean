import Gtz.Wave.KFourPathCorankCollapse
import Gtz.Design.WallCollapse
import Gtz.Design.StarOnlyLaw

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# Wire the two K4 walls to their landed structure

The star-only A3 residual still records its two final walls in their original
interfaces.  Two later design modules prove strictly stronger data:

* a pivot window has all four deletion pivots at least one, including the
  incoming pointer;
* a corank-two tree is a vertex star whose gap is a nonnegative rank-one atom,
  and its two kernel directions produce two distinct outside pointers.

This module packages those consequences and proves that the resulting residual
is pointwise equivalent to the preceding star-only residual.  The registered
A3 proposition can therefore consume the four-pivot wall or the fully exposed
rank-one/two-pointer star wall without acquiring a new assumption.
-/

namespace Gtz

open Matrix

/-! ## The positive-definite window wall has four large pivots -/

/-- The final positive-definite window wall after including the incoming
pointer's deletion pivot. -/
def KFourTreeWindowAllPivotWallData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  ∃ pointer : Fin 6, pointer ∉ tree ∧
    (directionChartGap kFourDirection point.mass point.weight
      (insert pointer tree)).PosDef ∧
    ∀ label ∈ insert pointer tree,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        (insert pointer tree) label

/-- The pointer-window package itself proves that its base tree is not
positive definite. -/
theorem not_posDef_of_kFourTreeWindowData (point : DirectionChartPoint 6)
    {tree : Finset (Fin 6)} (hwindow : KFourTreeWindowData point tree) :
    ¬ (directionChartGap kFourDirection point.mass point.weight tree).PosDef := by
  obtain ⟨tightDirection, pointer, htightNe, hpointerOut, htightKernel,
    hpointerReads, hwindowPsd, hwindowRead, hwindowCase⟩ := hwindow
  intro hposDef
  have hpositive := hposDef.dotProduct_mulVec_pos htightNe
  rw [htightKernel, dotProduct_zero] at hpositive
  exact (lt_irrefl 0) hpositive

/-- The landed pivot-wall sharpening supplies the fourth pivot. -/
theorem kFourTreeWindowAllPivotWallData_of_pivotWall
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hwindow : KFourTreeWindowData point tree)
    (hpivot : KFourTreeWindowPivotWallData point tree) :
    KFourTreeWindowAllPivotWallData point tree :=
  pivotWall_all_pivots_ge_one point
    (not_posDef_of_kFourTreeWindowData point hwindow) hpivot

/-- Forgetting the incoming pointer's pivot recovers the old wall. -/
theorem kFourTreeWindowPivotWallData_of_allPivotWall
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hpivot : KFourTreeWindowAllPivotWallData point tree) :
    KFourTreeWindowPivotWallData point tree := by
  obtain ⟨pointer, hpointerOut, hwindow, hpivots⟩ := hpivot
  exact ⟨pointer, hpointerOut, hwindow,
    fun label hlabel => hpivots label (Finset.mem_insert_of_mem hlabel)⟩

/-! ## The star corank wall is rank one and carries two pointers -/

/-- The original tree gap after the two-kernel rank collapse. -/
def KFourTreeRankOneGapData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  ∃ (axis : Fin 3 → ℝ) (scale : ℝ),
    axis ≠ 0 ∧ 0 ≤ scale ∧
    directionChartGap kFourDirection point.mass point.weight tree
      = scale • atomMatrix axis

/-- The transverse pointer package extracted from the two tree-kernel
directions. -/
def KFourTreeSecondPointerData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  ∃ (firstPointer secondPointer : Fin 6)
    (tightDirection secondDirection : Fin 3 → ℝ),
    firstPointer ∉ tree ∧ secondPointer ∉ tree ∧
    secondPointer ≠ firstPointer ∧
    tightDirection ≠ 0 ∧ secondDirection ≠ 0 ∧
    directionChartGap kFourDirection point.mass point.weight tree
      *ᵥ tightDirection = 0 ∧
    directionChartGap kFourDirection point.mass point.weight tree
      *ᵥ secondDirection = 0 ∧
    kFourDirection firstPointer ⬝ᵥ secondDirection = 0 ∧
    (¬ ∃ scale : ℝ, secondDirection = scale • tightDirection) ∧
    (∀ swap : Finset (Fin 6), firstPointer ∈ swap →
      0 < tightDirection ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight swap
          *ᵥ tightDirection)) ∧
    (∀ swap : Finset (Fin 6), secondPointer ∈ swap →
      0 < secondDirection ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight swap
          *ᵥ secondDirection))

/-- Two independent kernels of a symmetric PSD three-by-three gap expose its
nonnegative rank-one normal form. -/
theorem kFourTreeRankOneGapData_of_gapCorankTwo
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point tree) :
    KFourTreeRankOneGapData point tree := by
  obtain ⟨tightDirection, secondDirection, pointer, htightNe,
    hpointerOut, htightKernel, hpointerReads, hsecondNe, hsecondKernel,
    hpointerOrthogonal, hnotCollinear⟩ := hcorank
  have hcrossNe : crossProduct tightDirection secondDirection ≠ 0 := by
    intro hcrossZero
    obtain ⟨scale, hscale⟩ :=
      eq_smul_of_crossProduct_eq_zero htightNe hcrossZero
    exact hnotCollinear ⟨scale, hscale⟩
  obtain ⟨scale, hgapEq⟩ := exists_rankOne_of_symm_twoKernel
    (directionChartGap_transpose kFourDirection point.mass point.weight tree)
    htightKernel hsecondKernel hcrossNe
  exact ⟨crossProduct tightDirection secondDirection, scale, hcrossNe,
    scale_nonneg_of_posSemidef_smul_atom hgap hcrossNe hgapEq, hgapEq⟩

/-- The original-gap corank package reconstructs the singular window, after
which the landed wall theorem supplies the distinct second pointer. -/
theorem kFourTreeSecondPointerData_of_gapCorankTwo
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (htree : tree ∈ kFourSpanningTreeList)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point tree) :
    KFourTreeSecondPointerData point tree :=
  corankTwo_exists_second_pointer point htree hgap
    (windowCorankTwo_of_kFourTreeGapCorankTwoData point hcorank)

/-- Everything now known at the singular wall: the selected tree is a star,
the old corank package remains available, the gap has rank-one form, and two
distinct outside pointers repair the two transverse kernel directions. -/
def KFourTreeStarCorankWallData (point : DirectionChartPoint 6)
    (tree : Finset (Fin 6)) : Prop :=
  tree ∈ kFourStarList ∧
  KFourTreeGapCorankTwoData point tree ∧
  KFourTreeRankOneGapData point tree ∧
  KFourTreeSecondPointerData point tree

/-- Assemble the full star-wall package from the current corank branch. -/
theorem kFourTreeStarCorankWallData_of_gapCorankTwo
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (htree : tree ∈ kFourSpanningTreeList)
    (hstar : tree ∈ kFourStarList)
    (hgap : (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef)
    (hcorank : KFourTreeGapCorankTwoData point tree) :
    KFourTreeStarCorankWallData point tree :=
  ⟨hstar, hcorank,
    kFourTreeRankOneGapData_of_gapCorankTwo point hgap hcorank,
    kFourTreeSecondPointerData_of_gapCorankTwo point htree hgap hcorank⟩

/-! ## The exact fully exposed residual -/

/-- The K4 A3 residual with both final walls stated at their strongest landed
interfaces. -/
def KFourWeakTreeStarWallResidual (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList,
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourTreeWindowData point tree ∧
    (KFourTreeWindowAllPivotWallData point tree ∨
      KFourTreeStarCorankWallData point tree)

/-- Spend the wall-collapse and star-only producers on the preceding
star-corank residual. -/
theorem kFourWeakTreeStarWallResidual_of_starCorankResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeGapStarCorankResidual point) :
    KFourWeakTreeStarWallResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | ⟨hstar, hcorank⟩⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl
      (kFourTreeWindowAllPivotWallData_of_pivotWall point hwindow hpivot)⟩
  · exact ⟨tree, htree, hgap, hwindow, Or.inr
      (kFourTreeStarCorankWallData_of_gapCorankTwo point htree hstar hgap
        hcorank)⟩

/-- Forget the derived fourth pivot, rank-one form, and second-pointer package. -/
theorem kFourWeakTreeGapStarCorankResidual_of_starWallResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeStarWallResidual point) :
    KFourWeakTreeGapStarCorankResidual point := by
  obtain ⟨tree, htree, hgap, hwindow, hpivot | hstar⟩ := hwitness
  · exact ⟨tree, htree, hgap, hwindow, Or.inl
      (kFourTreeWindowPivotWallData_of_allPivotWall point hpivot)⟩
  · exact ⟨tree, htree, hgap, hwindow, Or.inr ⟨hstar.1, hstar.2.1⟩⟩

theorem kFourWeakTreeStarWallResidual_iff_starCorankResidual
    (point : DirectionChartPoint 6) :
    KFourWeakTreeStarWallResidual point ↔
      KFourWeakTreeGapStarCorankResidual point :=
  ⟨kFourWeakTreeGapStarCorankResidual_of_starWallResidual point,
    kFourWeakTreeStarWallResidual_of_starCorankResidual point⟩

/-- **THE FULLY EXPOSED A3 JOINT.**  The open branch now receives either all
four large window pivots or the rank-one/two-pointer vertex-star package. -/
noncomputable def KFourKnifeBandRefinedTreeStarWallWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakTreeStarWallResidual point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- The fully exposed wall formula is exactly the star-only formula. -/
theorem kFourKnifeBandRefinedTreeStarWall_iff_starCorankResidual :
    KFourKnifeBandRefinedTreeStarWallWeakToStrict ↔
      KFourKnifeBandRefinedTreeGapStarCorankResidualWeakToStrict := by
  constructor
  · intro hwall point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hwall point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeStarWallResidual_of_starCorankResidual point hwitness)
  · intro hstar point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hstar point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeGapStarCorankResidual_of_starWallResidual point hwitness)

/-- The fully exposed residual is exactly the public refined K4 knife band. -/
theorem kFourKnifeBandRefinedTreeStarWall_iff :
    KFourKnifeBandRefinedTreeStarWallWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedTreeStarWall_iff_starCorankResidual.trans
    kFourKnifeBandRefinedTreeGapStarCorankResidual_iff

/-- The design-side K4 selector is exactly the fully exposed residual. -/
theorem kFourFamilySelection_iff_treeStarWall :
    KFourFamilySelection ↔ KFourKnifeBandRefinedTreeStarWallWeakToStrict :=
  kFourFamilySelection_iff_treeGapStarCorankResidual.trans
    kFourKnifeBandRefinedTreeStarWall_iff_starCorankResidual.symm

end Gtz
