import Gtz.Wave.KFourTreeWindowResidual

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# Pull the second pointer-window kernel back to the original K4 tree

The orbit-free K4 residual left a singular four-edge pointer window with a
second kernel direction.  This module shows that the direction is already a
kernel of the original positive-semidefinite three-edge tree gap.  Moreover,
it is orthogonal to the incoming pointer atom.  The reason is rigid: in the
window quadratic form, a nonnegative old-gap term plus a positive multiple of
the squared pointer reading sums to zero, so both terms vanish.

The resulting package has two independent kernels of the original tree gap.
The final section replaces the window-corank branch in A3 by this sharper
original-gap branch and proves exact equivalence with the preceding formula.
-/

namespace Gtz

open Matrix

/-! ## A singular window cannot cancel its positive pointer atom -/

/-- A kernel direction of the singular pointer window is already a kernel of
the original PSD tree gap and is orthogonal to the incoming pointer atom. -/
theorem treeGap_kernel_and_pointer_orthogonal_of_window_kernel
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    {pointer : Fin 6} (hpointerOut : pointer ∉ selected)
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      selected).PosSemidef)
    {secondDirection : Fin 3 → ℝ}
    (hwindowKernel : directionChartGap kFourDirection point.mass point.weight
      (insert pointer selected) *ᵥ secondDirection = 0) :
    directionChartGap kFourDirection point.mass point.weight selected
        *ᵥ secondDirection = 0 ∧
      kFourDirection pointer ⬝ᵥ secondDirection = 0 := by
  let baseGap := directionChartGap kFourDirection point.mass point.weight selected
  let pointerReading := kFourDirection pointer ⬝ᵥ secondDirection
  let boost := point.mass pointer / point.weight pointer
  have hboostPos : 0 < boost := by
    exact div_pos (point.mass_pos pointer) (point.weight_pos pointer)
  have hbaseNonneg : 0 ≤ secondDirection ⬝ᵥ (baseGap *ᵥ secondDirection) := by
    have h := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hweak).2 secondDirection
    rwa [star_trivial] at h
  have hwindowQuad : secondDirection ⬝ᵥ
      (directionChartGap kFourDirection point.mass point.weight
        (insert pointer selected) *ᵥ secondDirection) = 0 := by
    rw [hwindowKernel, dotProduct_zero]
  have hdecomp : secondDirection ⬝ᵥ (baseGap *ᵥ secondDirection)
      + boost * pointerReading ^ 2 = 0 := by
    rw [directionChartGap_insert kFourDirection point.mass point.weight selected
      hpointerOut] at hwindowQuad
    simpa only [baseGap, boost, pointerReading, Matrix.add_mulVec,
      Matrix.smul_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul,
      dotProduct_atomMatrix_mulVec_pair, pow_two] using hwindowQuad
  have hbaseZero : secondDirection ⬝ᵥ (baseGap *ᵥ secondDirection) = 0 := by
    nlinarith [sq_nonneg pointerReading]
  have hpointerSq : pointerReading ^ 2 = 0 := by
    nlinarith
  constructor
  · exact mulVec_eq_zero_of_quadForm_eq_zero
      (directionChartGap_transpose kFourDirection point.mass point.weight selected)
      hweak hbaseZero
  · exact (pow_eq_zero_iff (two_ne_zero)).mp hpointerSq

/-! ## Replace the window kernel by original-gap data -/

/-- The honest content of the singular pointer-window branch, expressed on
the original weak tree: two nonzero noncollinear kernel directions, with the
second direction invisible to the incoming pointer atom. -/
def KFourTreeGapCorankTwoData (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) : Prop :=
  ∃ (tightDirection secondDirection : Fin 3 → ℝ) (pointer : Fin 6),
    tightDirection ≠ 0 ∧ pointer ∉ selected ∧
    directionChartGap kFourDirection point.mass point.weight selected
        *ᵥ tightDirection = 0 ∧
    (∀ swap : Finset (Fin 6), pointer ∈ swap →
      0 < tightDirection ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight swap
          *ᵥ tightDirection)) ∧
    secondDirection ≠ 0 ∧
    directionChartGap kFourDirection point.mass point.weight selected
        *ᵥ secondDirection = 0 ∧
    kFourDirection pointer ⬝ᵥ secondDirection = 0 ∧
    ¬ ∃ scale : ℝ, secondDirection = scale • tightDirection

/-- The singular-window package implies the sharper original-gap package.
Positive semidefiniteness prevents cancellation between the old gap and the
positive pointer atom. -/
theorem kFourTreeGapCorankTwoData_of_windowCorankTwo
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      selected).PosSemidef)
    (hcorank : KFourTreeWindowCorankTwoData point selected) :
    KFourTreeGapCorankTwoData point selected := by
  obtain ⟨tightDirection, secondDirection, pointer, htightNe,
    hpointerOut, htightKernel, hpointerReads, hsecondNe,
    hwindowKernel, hnotCollinear⟩ := hcorank
  obtain ⟨hsecondKernel, hpointerOrthogonal⟩ :=
    treeGap_kernel_and_pointer_orthogonal_of_window_kernel point
      hpointerOut hweak hwindowKernel
  exact ⟨tightDirection, secondDirection, pointer, htightNe,
    hpointerOut, htightKernel, hpointerReads, hsecondNe,
    hsecondKernel, hpointerOrthogonal, hnotCollinear⟩

/-- Conversely, an original-gap kernel invisible to the pointer remains a
kernel after the positive pointer atom is inserted. -/
theorem windowCorankTwo_of_kFourTreeGapCorankTwoData
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    (hcorank : KFourTreeGapCorankTwoData point selected) :
    KFourTreeWindowCorankTwoData point selected := by
  obtain ⟨tightDirection, secondDirection, pointer, htightNe,
    hpointerOut, htightKernel, hpointerReads, hsecondNe,
    hsecondKernel, hpointerOrthogonal, hnotCollinear⟩ := hcorank
  refine ⟨tightDirection, secondDirection, pointer, htightNe,
    hpointerOut, htightKernel, hpointerReads, hsecondNe, ?_,
    hnotCollinear⟩
  rw [directionChartGap_insert kFourDirection point.mass point.weight
    selected hpointerOut, Matrix.add_mulVec, Matrix.smul_mulVec,
    atomMatrix_mulVec_eq_smul, hsecondKernel, hpointerOrthogonal,
    zero_smul, smul_zero, add_zero]

/-- On a weak tree the window and original-gap formulations of the corank-two
wall are exactly equivalent. -/
theorem kFourTreeWindowCorankTwoData_iff_gapCorankTwo
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    (hweak : (directionChartGap kFourDirection point.mass point.weight
      selected).PosSemidef) :
    KFourTreeWindowCorankTwoData point selected ↔
      KFourTreeGapCorankTwoData point selected :=
  ⟨kFourTreeGapCorankTwoData_of_windowCorankTwo point hweak,
    windowCorankTwo_of_kFourTreeGapCorankTwoData point⟩

/-! ## Make the original-gap formulation the exact A3 residual -/

/-- The K4 residual after replacing the singular window kernel by the sharper
original-tree two-kernel package. -/
def KFourWeakTreeGapCorankResidual (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList,
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourTreeWindowData point tree ∧
    (KFourTreeWindowPivotWallData point tree ∨
      KFourTreeGapCorankTwoData point tree)

/-- Replace the singular window kernel by the two original-gap kernels. -/
theorem kFourWeakTreeGapCorankResidual_of_windowResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeWindowResidual point) :
    KFourWeakTreeGapCorankResidual point := by
  obtain ⟨tree, htree, hweak, hwindow, hpivot | hcorank⟩ := hwitness
  · exact ⟨tree, htree, hweak, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hweak, hwindow, Or.inr
      (kFourTreeGapCorankTwoData_of_windowCorankTwo point hweak hcorank)⟩

/-- The original-gap package reconstructs the singular window kernel, so no
logical strength is lost. -/
theorem kFourWeakTreeWindowResidual_of_gapCorankResidual
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakTreeGapCorankResidual point) :
    KFourWeakTreeWindowResidual point := by
  obtain ⟨tree, htree, hweak, hwindow, hpivot | hcorank⟩ := hwitness
  · exact ⟨tree, htree, hweak, hwindow, Or.inl hpivot⟩
  · exact ⟨tree, htree, hweak, hwindow, Or.inr
      (windowCorankTwo_of_kFourTreeGapCorankTwoData point hcorank)⟩

/-- The two formulations of the orbit-free K4 residual are pointwise exact. -/
theorem kFourWeakTreeGapCorankResidual_iff_windowResidual
    (point : DirectionChartPoint 6) :
    KFourWeakTreeGapCorankResidual point ↔ KFourWeakTreeWindowResidual point :=
  ⟨kFourWeakTreeWindowResidual_of_gapCorankResidual point,
    kFourWeakTreeGapCorankResidual_of_windowResidual point⟩

/-- **THE ORIGINAL-GAP A3 JOINT.**  On the singular side the registered K4
axiom now receives two independent kernels of the original PSD tree gap and
the incoming pointer's orthogonality to the second kernel. -/
noncomputable def KFourKnifeBandRefinedTreeGapCorankResidualWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakTreeGapCorankResidual point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- The original-gap A3 formula is exactly the preceding window formula. -/
theorem kFourKnifeBandRefinedTreeGapCorankResidual_iff_treeWindowResidual :
    KFourKnifeBandRefinedTreeGapCorankResidualWeakToStrict ↔
      KFourKnifeBandRefinedTreeWindowResidualWeakToStrict := by
  constructor
  · intro hgap point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hgap point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeGapCorankResidual_of_windowResidual point hwitness)
  · intro hwindow point hnotLayerA hnotExchange hnotAtlas hledger hwitness
    exact hwindow point hnotLayerA hnotExchange hnotAtlas hledger
      (kFourWeakTreeWindowResidual_of_gapCorankResidual point hwitness)

/-- The original-gap residual is exactly the public refined K4 knife band. -/
theorem kFourKnifeBandRefinedTreeGapCorankResidual_iff :
    KFourKnifeBandRefinedTreeGapCorankResidualWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedTreeGapCorankResidual_iff_treeWindowResidual.trans
    kFourKnifeBandRefinedTreeWindowResidual_iff

/-- The design-side K4 selector is exactly the original-gap residual. -/
theorem kFourFamilySelection_iff_treeGapCorankResidual :
    KFourFamilySelection ↔
      KFourKnifeBandRefinedTreeGapCorankResidualWeakToStrict :=
  kFourFamilySelection_iff_treeWindowResidual.trans
    kFourKnifeBandRefinedTreeGapCorankResidual_iff_treeWindowResidual.symm

end Gtz
