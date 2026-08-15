import Gtz.Design.StratumSqueeze
import Gtz.Design.KFourBandAtlas
import Gtz.Wave.KFourAllTreeZMatrixWiring

/-!
# The exact K4 family-selection weld

`KFourFamilySelection` was introduced as the design-side consumer of the
chart whitening.  Its landed direction sends a family selection to a strict
tree at every chart point.  The converse is just as important: the same
whitening equivalence transports a strict chart tree back to the realizing
design.  Thus the family selector is neither a stronger global selection nor
a new obligation.  It is exactly the public K4 residual, and therefore exactly
the all-sixteen-tree Z-obstructed residual registered as A3.

This module keeps that identification out of the original producer files and
provides both directions as callable bridges.
-/

namespace Gtz

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-- A strict tree at every chart point transports through the supplied
whitening equivalence and gives the design-side family selection. -/
theorem kFourFamilySelection_of_everyPointHasStrictTree
    (hstrict : KFourEveryPointHasStrictTree) : KFourFamilySelection := by
  intro point design _ hbridge
  obtain ⟨tree, htree, hchart⟩ := hstrict point
  have hcard : tree.card = 3 := by
    have hall : ∀ candidate ∈ kFourSpanningTreeList, candidate.card = 3 := by decide
    exact hall tree htree
  exact ⟨tree, hcard, (hbridge tree).mpr hchart⟩

/-- The whitened family selection is exactly strict-tree coverage of the K4
chart. -/
theorem kFourFamilySelection_iff_everyPointHasStrictTree :
    KFourFamilySelection ↔ KFourEveryPointHasStrictTree :=
  ⟨kFourStrictTree_of_familySelection,
    kFourFamilySelection_of_everyPointHasStrictTree⟩

/-- The design-side family selector is exactly the public refined knife-band
statement. -/
theorem kFourFamilySelection_iff_refined :
    KFourFamilySelection ↔ KFourKnifeBandRefinedWeakToStrict :=
  kFourFamilySelection_iff_everyPointHasStrictTree.trans
    kFourKnifeBandRefined_iff_everyPointHasStrictTree.symm

/-- The design-side family selector is exactly the registered all-tree
Z-obstructed A3 residual.  In particular, the full dual-witness ledger can be
consumed without introducing a second design-level conjecture. -/
theorem kFourFamilySelection_iff_allTreeZObstructed :
    KFourFamilySelection ↔
      KFourKnifeBandRefinedAllTreeZObstructedWeakToStrict :=
  kFourFamilySelection_iff_refined.trans
    kFourKnifeBandRefinedAllTreeZObstructed_iff.symm

/-- A proof of the whitened family selector closes the exact registered A3
formula. -/
theorem kFourAllTreeZObstructed_of_familySelection
    (hsel : KFourFamilySelection) :
    KFourKnifeBandRefinedAllTreeZObstructedWeakToStrict :=
  kFourFamilySelection_iff_allTreeZObstructed.mp hsel

/-- Conversely, the registered all-tree residual recovers the design-side
family selector, so downstream design arguments may consume it directly. -/
theorem kFourFamilySelection_of_allTreeZObstructed
    (hall : KFourKnifeBandRefinedAllTreeZObstructedWeakToStrict) :
    KFourFamilySelection :=
  kFourFamilySelection_iff_allTreeZObstructed.mpr hall

end Gtz
