import Gtz.Wave.KFourPathPointerResidual
import Gtz.Design.KFourDescentLadder

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

/-!
# Spend the K4 path pointer on its four-edge window

A saturated K4 path now carries a nonzero gap-kernel direction and an outside
pointer whose every host reads positively on that same direction.  This module
performs the next matrix step instead of merely renaming that package.

Adding the pointer gives a positive-semidefinite four-edge window which is
strictly positive on the old path kernel.  Consequently exactly one of the
following useful branches is available:

* the window is positive definite, and the landed descent ladder deletes an
  old path edge precisely when its current pivot is below one;
* the window is singular, and it has a second kernel direction which cannot be
  collinear with the old one.

Thus a saturated path either produces a strict K4 spanning tree immediately,
reaches the exact final-rung pivot wall, or enters an explicit corank-two
window.  The vertex-star alternative is unchanged.  The final section makes
this enriched package the exact A3 consumer while proving that no logical
strength was smuggled into the registry formula.
-/

namespace Gtz

open Matrix

/-! ## Add the pointer atom -/

/-- Adding one label to a chart selection adds its boosted rank-one atom. -/
theorem directionChartGap_insert {size : ℕ} (direction : Fin size → (Fin 3 → ℝ))
    (mass weight : Fin size → ℝ) (selected : Finset (Fin size)) {label : Fin size}
    (hlabel : label ∉ selected) :
    directionChartGap direction mass weight (insert label selected)
      = directionChartGap direction mass weight selected
        + (mass label / weight label) • atomMatrix (direction label) := by
  unfold directionChartGap
  rw [Finset.sum_insert hlabel]
  abel

/-- The path pointer after adding the pointer edge.  The new four-edge window is
PSD and reads positively on the old path kernel.  It is therefore either PD or
has a second kernel vector not collinear with the old one. -/
def KFourPathWindowData (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) : Prop :=
  ∃ (tightDirection : Fin 3 → ℝ) (pointer : Fin 6),
    tightDirection ≠ 0 ∧ pointer ∉ selected ∧
    directionChartGap kFourDirection point.mass point.weight selected *ᵥ tightDirection = 0 ∧
    (∀ swap : Finset (Fin 6), pointer ∈ swap →
      0 < tightDirection ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight swap *ᵥ tightDirection)) ∧
    (directionChartGap kFourDirection point.mass point.weight
      (insert pointer selected)).PosSemidef ∧
    0 < tightDirection ⬝ᵥ
      (directionChartGap kFourDirection point.mass point.weight
        (insert pointer selected) *ᵥ tightDirection) ∧
    ((directionChartGap kFourDirection point.mass point.weight
        (insert pointer selected)).PosDef ∨
      (∃ secondDirection : Fin 3 → ℝ, secondDirection ≠ 0 ∧
        directionChartGap kFourDirection point.mass point.weight
          (insert pointer selected) *ᵥ secondDirection = 0 ∧
        ¬ ∃ scale : ℝ, secondDirection = scale • tightDirection))

/-- A weak path and its pointer produce the exact window dichotomy. -/
theorem kFourPathWindowData_of_pointerData (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6))
    (hweak : (directionChartGap kFourDirection point.mass point.weight selected).PosSemidef)
    (hpointer : KFourPathPointerData point selected) :
    KFourPathWindowData point selected := by
  obtain ⟨tightDirection, pointer, htightNe, hpointerOut, htightKernel,
    hpointerReads⟩ := hpointer
  let window := directionChartGap kFourDirection point.mass point.weight
    (insert pointer selected)
  have hwindowEq : window =
      directionChartGap kFourDirection point.mass point.weight selected
        + (point.mass pointer / point.weight pointer) • atomMatrix (kFourDirection pointer) := by
    exact directionChartGap_insert kFourDirection point.mass point.weight selected hpointerOut
  have hwindowPsd : window.PosSemidef := by
    rw [hwindowEq]
    exact hweak.add ((posSemidef_atomMatrix (kFourDirection pointer)).smul
      (div_pos (point.mass_pos pointer) (point.weight_pos pointer)).le)
  have hwindowRead : 0 < tightDirection ⬝ᵥ (window *ᵥ tightDirection) :=
    hpointerReads _ (Finset.mem_insert_self pointer selected)
  by_cases hwindowPosDef : window.PosDef
  · exact ⟨tightDirection, pointer, htightNe, hpointerOut, htightKernel,
      hpointerReads, hwindowPsd, hwindowRead, Or.inl hwindowPosDef⟩
  · have hdetZero : window.det = 0 := by
      by_contra hdetNe
      exact hwindowPosDef (hwindowPsd.posDef_iff_det_ne_zero.mpr hdetNe)
    obtain ⟨secondDirection, hsecondNe, hsecondKernel⟩ :=
      Matrix.exists_mulVec_eq_zero_iff.mpr hdetZero
    have hnotCollinear : ¬ ∃ scale : ℝ, secondDirection = scale • tightDirection := by
      rintro ⟨scale, hscale⟩
      have hscaleNe : scale ≠ 0 := by
        intro hzero
        apply hsecondNe
        rw [hscale, hzero, zero_smul]
      have htightWindowKernel : window *ᵥ tightDirection = 0 := by
        have hscaled : scale • (window *ᵥ tightDirection) = 0 := by
          simpa [hscale, Matrix.mulVec_smul] using hsecondKernel
        exact (smul_eq_zero.mp hscaled).resolve_left hscaleNe
      rw [htightWindowKernel, dotProduct_zero] at hwindowRead
      exact (lt_irrefl 0) hwindowRead
    exact ⟨tightDirection, pointer, htightNe, hpointerOut,
      htightKernel, hpointerReads, hwindowPsd, hwindowRead,
      Or.inr ⟨secondDirection, hsecondNe, hsecondKernel, hnotCollinear⟩⟩

/-! ## Spend the positive-definite window -/

/-- On the PD side of the window dichotomy, the landed chart ladder is exact:
an outgoing edge gives a strict repaired tree precisely when its window pivot is
below one. -/
theorem kFourPathWindow_exchange_posDef_iff_pivot_lt_one
    (point : DirectionChartPoint 6) {selected : Finset (Fin 6)}
    {pointer outLabel : Fin 6} (hpointerOut : pointer ∉ selected)
    (hout : outLabel ∈ selected)
    (hwindow : (directionChartGap kFourDirection point.mass point.weight
      (insert pointer selected)).PosDef) :
    (directionChartGap kFourDirection point.mass point.weight
        (insert pointer (selected.erase outLabel))).PosDef
      ↔ chartLadderPivot kFourDirection point.mass point.weight
        (insert pointer selected) outLabel < 1 := by
  have hpointerNe : pointer ≠ outLabel := by
    intro heq
    exact hpointerOut (heq ▸ hout)
  have herase : (insert pointer selected).erase outLabel =
      insert pointer (selected.erase outLabel) := by
    ext label
    simp only [Finset.mem_erase, Finset.mem_insert]
    constructor
    · rintro ⟨hlabelNe, hlabelPointer | hlabelSelected⟩
      · exact Or.inl hlabelPointer
      · exact Or.inr ⟨hlabelNe, hlabelSelected⟩
    · rintro (hlabelPointer | ⟨hlabelNe, hlabelSelected⟩)
      · exact ⟨hlabelPointer ▸ hpointerNe, Or.inl hlabelPointer⟩
      · exact ⟨hlabelNe, Or.inr hlabelSelected⟩
  rw [← herase]
  exact posDef_directionChartGap_erase_iff kFourDirection point.mass point.weight
    point.mass_pos point.weight_pos (insert pointer selected)
      (Finset.mem_insert_of_mem hout) hwindow

/-- A successful final pivot on a PD pointer window is already a strict K4
spanning tree, not merely an arbitrary card-three selection. -/
theorem exists_strictTree_of_kFourPathWindow_pivot_lt_one
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (htree : tree ∈ kFourSpanningTreeList) {pointer outLabel : Fin 6}
    (hpointerOut : pointer ∉ tree) (hout : outLabel ∈ tree)
    (hwindow : (directionChartGap kFourDirection point.mass point.weight
      (insert pointer tree)).PosDef)
    (hpivot : chartLadderPivot kFourDirection point.mass point.weight
      (insert pointer tree) outLabel < 1) :
    ∃ repaired ∈ kFourSpanningTreeList,
      repaired = insert pointer (tree.erase outLabel) ∧
      (directionChartGap kFourDirection point.mass point.weight repaired).PosDef := by
  let repaired := insert pointer (tree.erase outLabel)
  have hrepairedPosDef : (directionChartGap kFourDirection point.mass point.weight
      repaired).PosDef := by
    exact (kFourPathWindow_exchange_posDef_iff_pivot_lt_one point hpointerOut hout
      hwindow).mpr hpivot
  have htreeCard : tree.card = 3 := kFourSpanningTree_card tree htree
  have hrepairedCard : repaired.card = 3 := by
    simpa only [repaired] using
      (directionChartGap_exchange_card hout hpointerOut).trans htreeCard
  rcases cardThreeSubset_isSpanningTreeOrDependentTriple repaired hrepairedCard with
    hrepairedTree | hrepairedTriangle
  · exact ⟨repaired, hrepairedTree, rfl, hrepairedPosDef⟩
  · exact absurd hrepairedPosDef.posSemidef
      (kFourDependentTriple_gap_not_posSemidef point repaired hrepairedTriangle)

/-! ## The two honest residual branches -/

/-- The window is positive definite, but every deletion of an old path edge
stops at the final-rung pivot wall. -/
def KFourPathWindowPivotWallData (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) : Prop :=
  ∃ pointer : Fin 6, pointer ∉ selected ∧
    (directionChartGap kFourDirection point.mass point.weight
      (insert pointer selected)).PosDef ∧
    ∀ outLabel ∈ selected,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        (insert pointer selected) outLabel

/-- The pointer bump does not make the path window positive definite.  Its
failure is witnessed by a second kernel direction independent of the old path
kernel, while the pointer still repairs the old direction. -/
def KFourPathWindowCorankTwoData (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) : Prop :=
  ∃ (tightDirection secondDirection : Fin 3 → ℝ) (pointer : Fin 6),
    tightDirection ≠ 0 ∧ pointer ∉ selected ∧
    directionChartGap kFourDirection point.mass point.weight selected *ᵥ tightDirection = 0 ∧
    (∀ swap : Finset (Fin 6), pointer ∈ swap →
      0 < tightDirection ⬝ᵥ
        (directionChartGap kFourDirection point.mass point.weight swap *ᵥ tightDirection)) ∧
    secondDirection ≠ 0 ∧
    directionChartGap kFourDirection point.mass point.weight
      (insert pointer selected) *ᵥ secondDirection = 0 ∧
    ¬ ∃ scale : ℝ, secondDirection = scale • tightDirection

/-- **THE WINDOW TRICHOTOMY.**  A saturated weak K4 path with its pointer
either already yields a strict spanning tree, reaches the exact final-rung
pivot wall, or produces two independent tight directions in the pointer
window. -/
theorem exists_strictTree_or_windowPivotWall_or_corankTwo
    (point : DirectionChartPoint 6) {tree : Finset (Fin 6)}
    (htree : tree ∈ kFourSpanningTreeList)
    (hdata : KFourPathWindowData point tree) :
    (∃ strictTree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight strictTree).PosDef) ∨
    KFourPathWindowPivotWallData point tree ∨
    KFourPathWindowCorankTwoData point tree := by
  obtain ⟨tightDirection, pointer, htightNe, hpointerOut, htightKernel,
    hpointerReads, _hwindowPsd, _hwindowRead, hwindowCase⟩ := hdata
  rcases hwindowCase with hwindowPosDef | hcorankTwo
  · by_cases hpivot : ∃ outLabel ∈ tree,
        chartLadderPivot kFourDirection point.mass point.weight
          (insert pointer tree) outLabel < 1
    · obtain ⟨outLabel, hout, hpivotLt⟩ := hpivot
      obtain ⟨strictTree, hstrictTree, _hrepaired, hstrict⟩ :=
        exists_strictTree_of_kFourPathWindow_pivot_lt_one point htree
          hpointerOut hout hwindowPosDef hpivotLt
      exact Or.inl ⟨strictTree, hstrictTree, hstrict⟩
    · refine Or.inr (Or.inl ⟨pointer, hpointerOut, hwindowPosDef, ?_⟩)
      intro outLabel hout
      exact le_of_not_gt (fun hpivotLt => hpivot ⟨outLabel, hout, hpivotLt⟩)
  · obtain ⟨secondDirection, hsecondNe, hsecondKernel, hnotCollinear⟩ := hcorankTwo
    exact Or.inr (Or.inr ⟨tightDirection, secondDirection, pointer, htightNe,
      hpointerOut, htightKernel, hpointerReads, hsecondNe, hsecondKernel,
      hnotCollinear⟩)

/-! ## Make the enriched package the exact A3 consumer -/

/-- A realized weak path carrying the pointer-window dichotomy. -/
def KFourWeakPathWindowWitness (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList, tree ∉ kFourStarList ∧
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourPathWindowData point tree

/-- The exact weak branch after spending the pointer on its four-edge window. -/
def KFourWeakPathWindowOrStar (point : DirectionChartPoint 6) : Prop :=
  KFourWeakPathWindowWitness point ∨ KFourWeakStarWitness point

/-- Forgetting the window deductions recovers the original pointer package. -/
theorem kFourPathPointerData_of_windowData (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (hdata : KFourPathWindowData point selected) :
    KFourPathPointerData point selected := by
  obtain ⟨tightDirection, pointer, htightNe, hpointerOut, htightKernel,
    hpointerReads, _hwindowPsd, _hwindowRead, _hwindowCase⟩ := hdata
  exact ⟨tightDirection, pointer, htightNe, hpointerOut, htightKernel, hpointerReads⟩

/-- Enrich every path branch of the prior exact residual. -/
theorem kFourWeakPathWindowOrStar_of_pointerOrStar
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakPathPointerOrStar point) :
    KFourWeakPathWindowOrStar point := by
  rcases hwitness with hpath | hstar
  · obtain ⟨tree, htree, hnotStar, hweak, hpointer⟩ := hpath
    exact Or.inl ⟨tree, htree, hnotStar, hweak,
      kFourPathWindowData_of_pointerData point tree hweak hpointer⟩
  · exact Or.inr hstar

/-- The enriched package still contains all of the prior pointer data. -/
theorem kFourWeakPathPointerOrStar_of_windowOrStar
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakPathWindowOrStar point) :
    KFourWeakPathPointerOrStar point := by
  rcases hwitness with hpath | hstar
  · obtain ⟨tree, htree, hnotStar, hweak, hwindow⟩ := hpath
    exact Or.inl ⟨tree, htree, hnotStar, hweak,
      kFourPathPointerData_of_windowData point tree hwindow⟩
  · exact Or.inr hstar

/-- The K4 residual after the path pointer has been spent on its window. -/
noncomputable def KFourKnifeBandRefinedPathWindowOrStarWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakPathWindowOrStar point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem pathWindowOrStarKFourKnifeBandRefined_of_pathPointerOrStar
    (hpointer : KFourKnifeBandRefinedPathPointerOrStarWeakToStrict) :
    KFourKnifeBandRefinedPathWindowOrStarWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hwitness
  exact hpointer point hnotLayerA hnotExchange hnotAtlas hledger
    (kFourWeakPathPointerOrStar_of_windowOrStar point hwitness)

theorem pathPointerOrStarKFourKnifeBandRefined_of_pathWindowOrStar
    (hwindow : KFourKnifeBandRefinedPathWindowOrStarWeakToStrict) :
    KFourKnifeBandRefinedPathPointerOrStarWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hwitness
  exact hwindow point hnotLayerA hnotExchange hnotAtlas hledger
    (kFourWeakPathWindowOrStar_of_pointerOrStar point hwitness)

theorem kFourKnifeBandRefinedPathWindowOrStar_iff_pathPointerOrStar :
    KFourKnifeBandRefinedPathWindowOrStarWeakToStrict ↔
      KFourKnifeBandRefinedPathPointerOrStarWeakToStrict :=
  ⟨pathPointerOrStarKFourKnifeBandRefined_of_pathWindowOrStar,
    pathWindowOrStarKFourKnifeBandRefined_of_pathPointerOrStar⟩

theorem kFourKnifeBandRefinedPathWindowOrStar_iff :
    KFourKnifeBandRefinedPathWindowOrStarWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedPathWindowOrStar_iff_pathPointerOrStar.trans
    kFourKnifeBandRefinedPathPointerOrStar_iff

theorem kFourFamilySelection_iff_pathWindowOrStar :
    KFourFamilySelection ↔ KFourKnifeBandRefinedPathWindowOrStarWeakToStrict :=
  kFourFamilySelection_iff_pathPointerOrStar.trans
    kFourKnifeBandRefinedPathWindowOrStar_iff_pathPointerOrStar.symm

/-! ## Remove the path cases already closed by the window trichotomy -/

/-- A weak path only after every successful window deletion has been spent.
The retained branch is exactly the pivot wall or the corank-two window. -/
def KFourWeakPathWindowResidualWitness (point : DirectionChartPoint 6) : Prop :=
  ∃ tree ∈ kFourSpanningTreeList, tree ∉ kFourStarList ∧
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef ∧
    KFourPathWindowData point tree ∧
    (KFourPathWindowPivotWallData point tree ∨
      KFourPathWindowCorankTwoData point tree)

/-- The final weak K4 witness after the path window has fired: a residual path
at one of its two exact walls, or a weak vertex star. -/
def KFourWeakPathWindowResidualOrStar (point : DirectionChartPoint 6) : Prop :=
  KFourWeakPathWindowResidualWitness point ∨ KFourWeakStarWitness point

/-- Spending the window trichotomy either solves the chart point immediately
or produces the exact residual witness. -/
theorem exists_strictTree_or_kFourWeakPathWindowResidualOrStar
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakPathWindowOrStar point) :
    (∃ strictTree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight strictTree).PosDef) ∨
    KFourWeakPathWindowResidualOrStar point := by
  rcases hwitness with hpath | hstar
  · obtain ⟨tree, htree, hnotStar, hweak, hwindow⟩ := hpath
    rcases exists_strictTree_or_windowPivotWall_or_corankTwo point htree hwindow with
      hstrict | hpivot | hcorankTwo
    · exact Or.inl hstrict
    · exact Or.inr (Or.inl ⟨tree, htree, hnotStar, hweak, hwindow, Or.inl hpivot⟩)
    · exact Or.inr (Or.inl ⟨tree, htree, hnotStar, hweak, hwindow, Or.inr hcorankTwo⟩)
  · exact Or.inr (Or.inr hstar)

/-- Forgetting which of the two remaining path walls fired recovers the
enriched window witness. -/
theorem kFourWeakPathWindowOrStar_of_residualOrStar
    (point : DirectionChartPoint 6)
    (hwitness : KFourWeakPathWindowResidualOrStar point) :
    KFourWeakPathWindowOrStar point := by
  rcases hwitness with hpath | hstar
  · obtain ⟨tree, htree, hnotStar, hweak, hwindow, _hresidual⟩ := hpath
    exact Or.inl ⟨tree, htree, hnotStar, hweak, hwindow⟩
  · exact Or.inr hstar

/-- **THE SHARPENED A3 JOINT.**  Successful pointer-window deletions are now
theorems.  The axiom sees only a weak star, a PD window whose three old-edge
pivots are all at least one, or a window with two independent kernel
directions. -/
noncomputable def KFourKnifeBandRefinedPathWindowResidualOrStarWeakToStrict : Prop :=
  ∀ point : DirectionChartPoint 6, ¬ KFourLayerACellFires point →
    ¬ KFourExchangeStarCellFires point →
    ¬ KFourAllTreeMinorAtlasCellFires point →
    KFourAllTreeObstructionLedger point →
    KFourWeakPathWindowResidualOrStar point →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

theorem pathWindowResidualOrStarKFourKnifeBandRefined_of_pathWindowOrStar
    (hwindow : KFourKnifeBandRefinedPathWindowOrStarWeakToStrict) :
    KFourKnifeBandRefinedPathWindowResidualOrStarWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hwitness
  exact hwindow point hnotLayerA hnotExchange hnotAtlas hledger
    (kFourWeakPathWindowOrStar_of_residualOrStar point hwitness)

theorem pathWindowOrStarKFourKnifeBandRefined_of_pathWindowResidualOrStar
    (hresidual : KFourKnifeBandRefinedPathWindowResidualOrStarWeakToStrict) :
    KFourKnifeBandRefinedPathWindowOrStarWeakToStrict := by
  intro point hnotLayerA hnotExchange hnotAtlas hledger hwitness
  rcases exists_strictTree_or_kFourWeakPathWindowResidualOrStar point hwitness with
    hstrict | hresidualWitness
  · exact hstrict
  · exact hresidual point hnotLayerA hnotExchange hnotAtlas hledger hresidualWitness

theorem kFourKnifeBandRefinedPathWindowResidualOrStar_iff_pathWindowOrStar :
    KFourKnifeBandRefinedPathWindowResidualOrStarWeakToStrict ↔
      KFourKnifeBandRefinedPathWindowOrStarWeakToStrict :=
  ⟨pathWindowOrStarKFourKnifeBandRefined_of_pathWindowResidualOrStar,
    pathWindowResidualOrStarKFourKnifeBandRefined_of_pathWindowOrStar⟩

theorem kFourKnifeBandRefinedPathWindowResidualOrStar_iff :
    KFourKnifeBandRefinedPathWindowResidualOrStarWeakToStrict ↔
      KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedPathWindowResidualOrStar_iff_pathWindowOrStar.trans
    kFourKnifeBandRefinedPathWindowOrStar_iff

theorem kFourFamilySelection_iff_pathWindowResidualOrStar :
    KFourFamilySelection ↔
      KFourKnifeBandRefinedPathWindowResidualOrStarWeakToStrict :=
  kFourFamilySelection_iff_pathWindowOrStar.trans
    kFourKnifeBandRefinedPathWindowResidualOrStar_iff_pathWindowOrStar.symm

end Gtz
