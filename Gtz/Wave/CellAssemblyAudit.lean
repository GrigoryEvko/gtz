import Gtz.Wave.AtomMassOneLadder
import Gtz.Wave.AtomDeepCutRigidity
import Gtz.Wave.WideSpectralAtomForm
import Gtz.Wave.CaptureLinePairKill
import Gtz.Wave.SharedPrivateComplementEigen
import Gtz.Reduction.PolarGapDeterminant

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# The cell assembly audit: the three routes compose at HEAD

This module is the finish-line audit of the `(6,3)` campaign.  Each
theorem takes a CURRENT frontier Prop as its hypothesis and concludes
the final results of the cell.  The module adds no new mathematics: it
certifies, in one compiled file, that every open frontier of the three
routes composes to `Gtz.GtzWeighted 6 3` and `Gtz.GtzWeightedAll 3`
through the landed bridges, with no bit-rotted link.

## Route A — the atom blocked residue

The residue `Gtz.AtomBlockedPairClosed` closes the cell through the
landed dispatch.  The lossless splits narrow the open work to the three
sharp parts: the window between the trine cut and the single cut, the
deep part with a single-budget pivot, and the doubly blocked part.  The
mass-one selection `Gtz.AtomTripleBoundaryClosed` closes the same
residue from the boundary.

## Route B — the atom triple ceiling spine

The ceiling `Gtz.AtomTripleCeilingClosed` closes the cell ALONE: the
crux kill of `Gtz/Wave/DenseCeilingCollapse.lean` consumes no upper
closure.  The six-upper-closure spine is therefore redundant on the
ceiling route, and this module records that fact as a theorem.  The
wide-residue route still needs the six upper closures, and the
shared-private pair of them reduces to the four circuit residues of the
impure lattice.

## Route C — the polar selection targets

Each polar frontier Prop closes the cell, all of rank three and the
hinge at the deciding cell.  The weakness order of the six shipped
targets collapses to the arithmetic selection target, and this module
records that collapse as one disjunction theorem.

## The one-statement audit of the atom lane

The five faces of the atom lane are ONE Prop: the blocked residue, the
triple ceiling, the mass-one boundary, the pivot pair residue and the
Sylvester residue are pairwise equivalent through the landed bridges.
The three sharp parts of the split are together equivalent to the
ceiling.  As a result no face of the atom lane is a weaker target than
one other face, which is the machine form of the sharpness discovery.

## PROVED here (no `sorry`, no `axiom`, no `native_decide`)

* `Gtz.cellAssembly_sixThree_of_blockedPair`,
  `Gtz.cellAssembly_sixThree_of_three_parts`,
  `Gtz.cellAssembly_sixThree_of_massOneBoundary` — **ROUTE A**.
* `Gtz.cellAssembly_blockedPair_iff_ceiling`,
  `Gtz.cellAssembly_ceiling_iff_sylvester`,
  `Gtz.cellAssembly_boundary_iff_pivotPair`,
  `Gtz.cellAssembly_three_parts_iff_ceiling` — **THE FACE CYCLE**.
* `Gtz.cellAssembly_sixThree_of_ceiling`,
  `Gtz.cellAssembly_ceiling_needs_no_upper_closures`,
  `Gtz.cellAssembly_sixThree_of_wideResidue_of_circuitResidues` —
  **ROUTE B**.
* `Gtz.cellAssembly_sixThree_of_polarWrap`,
  `Gtz.cellAssembly_sixThree_of_polarShadowBudget`,
  `Gtz.cellAssembly_sixThree_of_polarHeavyShadow`,
  `Gtz.cellAssembly_sixThree_of_polarWrapBudget`,
  `Gtz.cellAssembly_sixThree_of_polarGap`,
  `Gtz.cellAssembly_sixThree_of_polarWrapGap`,
  `Gtz.cellAssembly_polar_frontiers_to_schur` — **ROUTE C**.

## The registry boundary

The rank-three hinge arms follow from every polar target through the
landed arm bundles.  The two registry obligations at rank four and up
consume `Gtz.PolarTiltSelection` at every rank through the landed
theorems of `Gtz/Reduction/PolarCoverDescent.lean`, and the rank-three
targets of this module do not reach them.  The skeleton side of the
boundary belongs to `Skeleton/SixThreeConditional.lean`, where the one
cell releases the whole tree.

## Vacuity

Every theorem of this module is an implication between named Props of
the tree, and every proof consumes a landed bridge.  The hypothesis
packages of the atom Props are satisfiable: the icosahedral frame at a
window mass satisfies the blocked package, and the ceiling package holds
at every Parseval frame with a subunit scale mass.  The polar packages
quantify over primitive ties, whose emptiness at `(6,3)` is exactly the
open question, thus none of the implications is decided by vacuity.
-/

namespace Gtz

/-! ## Layer 1 — Route A, the blocked residue to the cell -/

/-- **ROUTE A, THE RESIDUE FORM.**  The blocked residue closes the
deciding cell and all of rank three. -/
theorem cellAssembly_sixThree_of_blockedPair
    (hresidue : AtomBlockedPairClosed) :
    GtzWeighted 6 3 ∧ GtzWeightedAll 3 :=
  ⟨gtzWeighted_six_three_of_blockedPair hresidue,
    gtzWeightedAll_three_of_blockedPair hresidue⟩

/-- **ROUTE A, THE SHARP SPLIT FORM.**  The three sharp parts of the
lossless split close the deciding cell and all of rank three. -/
theorem cellAssembly_sixThree_of_three_parts
    (hwindow : AtomBlockedWindowClosed)
    (hbudget : AtomSingleBudgetDeepClosed)
    (hdouble : AtomDoublyBlockedClosed) :
    GtzWeighted 6 3 ∧ GtzWeightedAll 3 :=
  ⟨gtzWeighted_six_three_of_three_parts hwindow hbudget hdouble,
    gtzWeightedAll_three_of_three_parts hwindow hbudget hdouble⟩

/-- **ROUTE A, THE BOUNDARY FORM.**  The non-strict selection at scale
mass exactly one closes the deciding cell and all of rank three. -/
theorem cellAssembly_sixThree_of_massOneBoundary
    (hboundary : AtomTripleBoundaryClosed) :
    GtzWeighted 6 3 ∧ GtzWeightedAll 3 :=
  cellAssembly_sixThree_of_blockedPair
    (atomBlockedPairClosed_of_atomTripleBoundary hboundary)

/-! ## Layer 2 — the face cycle of the atom lane

The five faces are pairwise equivalent.  The cycle runs: blocked pair to
Sylvester, Sylvester to ceiling, ceiling to boundary, boundary to pivot
pair, pivot pair to blocked pair.  Every edge is a landed bridge. -/

/-- **FACE EQUIVALENCE ONE.**  The blocked residue and the triple
ceiling are one statement. -/
theorem cellAssembly_blockedPair_iff_ceiling :
    AtomBlockedPairClosed ↔ AtomTripleCeilingClosed :=
  ⟨atomTripleCeilingClosed_of_blockedPair,
    fun hceiling => atomBlockedPairClosed_of_atomTripleBoundary
      (atomTripleBoundaryClosed_of_atomTripleCeiling hceiling)⟩

/-- **FACE EQUIVALENCE TWO.**  The triple ceiling and the polynomial
Sylvester residue are one statement. -/
theorem cellAssembly_ceiling_iff_sylvester :
    AtomTripleCeilingClosed ↔ AtomTripleSylvesterClosed :=
  ⟨fun hceiling => atomTripleSylvesterClosed_of_blockedPair
      (cellAssembly_blockedPair_iff_ceiling.mpr hceiling),
    atomTripleCeilingClosed_of_sylvester⟩

/-- **FACE EQUIVALENCE THREE.**  The mass-one boundary and the pivot
pair residue are one statement. -/
theorem cellAssembly_boundary_iff_pivotPair :
    AtomTripleBoundaryClosed ↔ AtomPivotPairClosed :=
  ⟨atomPivotPairClosed_of_atomTripleBoundary,
    fun hpivot => atomTripleBoundaryClosed_of_atomTripleCeiling
      (atomTripleCeilingClosed_of_blockedPair
        (atomBlockedPairClosed_of_pivotPair hpivot))⟩

/-- **THE SPLIT MEETS THE CEILING.**  The three sharp parts are together
equivalent to the triple ceiling, thus the open work of route A and the
open work of route B are one statement. -/
theorem cellAssembly_three_parts_iff_ceiling :
    (AtomBlockedWindowClosed ∧ AtomSingleBudgetDeepClosed
        ∧ AtomDoublyBlockedClosed)
      ↔ AtomTripleCeilingClosed :=
  atomBlockedPairClosed_iff_three_parts.symm.trans
    cellAssembly_blockedPair_iff_ceiling

/-! ## Layer 3 — Route B, the ceiling spine to the cell -/

/-- **ROUTE B, THE CEILING ALONE.**  The triple ceiling closes the
deciding cell and all of rank three with NO upper closure. -/
theorem cellAssembly_sixThree_of_ceiling
    (hceiling : AtomTripleCeilingClosed) :
    GtzWeighted 6 3 ∧ GtzWeightedAll 3 :=
  ⟨gtzWeighted_six_three_of_atomTripleCeiling hceiling,
    gtzWeightedAll_three_of_atomTripleCeiling hceiling⟩

/-- **THE SIX UPPER CLOSURES ARE REDUNDANT ON THE CEILING ROUTE.**  The
ceiling supplies the wide spectral interface and the cell by itself,
thus the six-hypothesis spine dispatch asks for more than the route
needs. -/
theorem cellAssembly_ceiling_needs_no_upper_closures
    (hceiling : AtomTripleCeilingClosed) :
    WideSpectralSelectionClosed ∧ GtzWeighted 6 3 :=
  ⟨wideSpectralSelectionClosed_of_atomTripleCeiling hceiling,
    gtzWeighted_six_three_of_atomTripleCeiling hceiling⟩

/-- **THE WIDE-RESIDUE ROUTE FROM THE SMALLEST NAMED PIECES.**  The
shared-private pair of the six upper closures reduces to the four
circuit residues of the impure lattice, thus the wide route rests on the
wide residue, the four rung closures and the four circuit residues. -/
theorem cellAssembly_sixThree_of_wideResidue_of_circuitResidues
    (hwide : RankFourCaptureLineWideFlooredClosed)
    (hfiveOne : RankFiveSupportTwoClosed)
    (hfiveDense : RankFiveDenseClosed)
    (hsixOne : RankSixSupportTwoClosed)
    (hsixDense : RankSixDenseClosed)
    (hidentical : SharedPrivateCircuitPairIdenticalImpureClosed)
    (hwedgeLive : SharedPrivateCircuitSplitWedgeImpureClosed)
    (hwedgeDead : SharedPrivateCircuitSplitPairSaturatedClosed)
    (hwideCircuit : SharedPrivateCircuitWideDistinctClosed) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_wideResidue_of_upperClosures hwide hfiveOne
    (rankFiveSharedPrivateClosed_of_impure_circuit hidentical hwedgeLive
      hwedgeDead hwideCircuit)
    hfiveDense hsixOne
    (rankSixSharedPrivateClosed_of_impure_circuit hidentical hwedgeLive
      hwedgeDead hwideCircuit)
    hsixDense

/-! ## Layer 4 — Route C, the polar targets to the cell -/

/-- **ROUTE C, THE WRAPPING KILL.**  The wrapping selection closes the
deciding cell, all of rank three and the hinge at the deciding cell. -/
theorem cellAssembly_sixThree_of_polarWrap
    (hwrap : PolarWrapSelection 6) :
    (GtzWeighted 6 3 ∧ GtzWeightedAll 3) ∧ HingeHoldsAtSize 6 3 :=
  ⟨⟨gtzWeighted_six_three_of_polarWrapSelection hwrap,
      gtzWeightedAll_three_of_polarWrapSelection hwrap⟩,
    hingeHoldsAtSize_of_polarWrapSelection hwrap⟩

/-- **ROUTE C, THE COUPLING BUDGET TARGET.** -/
theorem cellAssembly_sixThree_of_polarShadowBudget
    (hbudget : PolarShadowBudgetSelection 6) :
    (GtzWeighted 6 3 ∧ GtzWeightedAll 3) ∧ HingeHoldsAtSize 6 3 :=
  ⟨⟨gtzWeighted_six_three_of_polarShadowBudgetSelection hbudget,
      gtzWeightedAll_three_of_polarShadowBudgetSelection hbudget⟩,
    hingeHoldsAtSize_of_polarShadowBudgetSelection hbudget⟩

/-- **ROUTE C, THE HEAVY SHADOW TARGET.** -/
theorem cellAssembly_sixThree_of_polarHeavyShadow
    (hheavy : PolarHeavyShadowSelection 6) :
    (GtzWeighted 6 3 ∧ GtzWeightedAll 3) ∧ HingeHoldsAtSize 6 3 :=
  ⟨⟨gtzWeighted_six_three_of_polarHeavyShadowSelection hheavy,
      gtzWeightedAll_three_of_polarHeavyShadowSelection hheavy⟩,
    hingeHoldsAtSize_of_polarHeavyShadowSelection hheavy⟩

/-- **ROUTE C, THE WRAPPING BUDGET TARGET.** -/
theorem cellAssembly_sixThree_of_polarWrapBudget
    (hwrap : PolarWrapBudgetSelection 6) :
    (GtzWeighted 6 3 ∧ GtzWeightedAll 3) ∧ HingeHoldsAtSize 6 3 :=
  ⟨⟨gtzWeighted_six_three_of_polarWrapBudgetSelection hwrap,
      gtzWeightedAll_three_of_polarWrapBudgetSelection hwrap⟩,
    hingeHoldsAtSize_of_polarWrapSelection
      (polarWrapSelection_of_polarWrapBudgetSelection hwrap)⟩

/-- **ROUTE C, THE GAP DETERMINANT TARGET.** -/
theorem cellAssembly_sixThree_of_polarGap
    (hgap : PolarGapSelection 6) :
    (GtzWeighted 6 3 ∧ GtzWeightedAll 3) ∧ HingeHoldsAtSize 6 3 :=
  ⟨⟨gtzWeighted_six_three_of_polarGapSelection hgap,
      gtzWeightedAll_three_of_polarGapSelection hgap⟩,
    hingeHoldsAtSize_of_polarGapSelection hgap⟩

/-- **ROUTE C, THE WRAPPING GAP TARGET.** -/
theorem cellAssembly_sixThree_of_polarWrapGap
    (hwrap : PolarWrapGapSelection 6) :
    (GtzWeighted 6 3 ∧ GtzWeightedAll 3) ∧ HingeHoldsAtSize 6 3 :=
  ⟨⟨gtzWeighted_six_three_of_polarWrapGapSelection hwrap,
      gtzWeightedAll_three_of_polarWrapGapSelection hwrap⟩,
    hingeHoldsAtSize_of_polarWrapSelection
      (polarWrapSelection_of_polarWrapGapSelection hwrap)⟩

/-- **THE WEAKNESS ORDER OF THE POLAR TARGETS.**  Each of the six
shipped targets implies the arithmetic selection target, thus the lane
has one weakest interface and every landing feeds it. -/
theorem cellAssembly_polar_frontiers_to_schur
    (htarget : PolarWrapGapSelection 6 ∨ PolarWrapBudgetSelection 6
      ∨ PolarHeavyShadowSelection 6 ∨ PolarShadowBudgetSelection 6
      ∨ PolarWrapSelection 6 ∨ PolarGapSelection 6) :
    PolarShadowSchurSelection 6 := by
  rcases htarget with hcase | hcase | hcase | hcase | hcase | hcase
  · exact polarShadowSchurSelection_of_polarWrapSelection
      (polarWrapSelection_of_polarWrapGapSelection hcase)
  · exact polarShadowSchurSelection_of_polarWrapSelection
      (polarWrapSelection_of_polarWrapBudgetSelection hcase)
  · exact polarShadowSchurSelection_of_polarHeavyShadowSelection hcase
  · exact polarShadowSchurSelection_of_polarShadowBudgetSelection hcase
  · exact polarShadowSchurSelection_of_polarWrapSelection hcase
  · exact polarShadowSchurSelection_of_polarGapSelection hcase

end Gtz
