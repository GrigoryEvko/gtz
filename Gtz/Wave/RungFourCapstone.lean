import Gtz.Wave.PencilFamilyClosure
import Gtz.Wave.ChairFamilyClosure
import Gtz.Wave.TridentFamilyClosure
import Gtz.Wave.FivePathFamilyClosure
import Gtz.Wave.ThreeTripleFamilyClosure
import Gtz.Wave.DoubleDoubleFamilyClosure
import Gtz.Wave.ZigzagFamilyClosure
import Gtz.Wave.TwinPairsFamilyClosure
import Gtz.Wave.HookFamilyClosure
import Gtz.Wave.DoublePathFamilyClosure
import Gtz.Wave.TetrahedronFamilyClosure
import Gtz.Wave.TriangleEdgeFamilyClosure
import Gtz.Wave.PendantForkFamilyClosure
import Gtz.Wave.PendantSplitFamilyClosure
import Gtz.Wave.NestedFamilyClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Finset

/-! **THE RUNG-FOUR CAPSTONE.**  Every card-four crux relabels onto one of the
fifteen canonical covering four-families, and each family is dead: the ten
engine-free closures, the tetrahedron, the triangle edge, the pendant fork,
and — through one more relabelling each — the pendant split on its index-46
representative and the nested family on its orbit-four representative.  No
crux has an argmax family of four blocks. -/

/-- The pendant-split family dies through its index-46 representative. -/
theorem SixThreeCrux.false_of_family_canonicalPendantSplitFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = canonicalPendantSplitFamily) :
    False := by
  apply SixThreeCrux.false_of_family_indexFortySixFamily
    (crux.relabel (⟨![0, 1, 2, 5, 3, 4], ![0, 1, 2, 4, 5, 3],
      by decide, by decide⟩ : Equiv.Perm (Fin 6)))
  have hbridge := chartArgmaxFamily_relabelDesign crux.design
    (⟨![0, 1, 2, 5, 3, 4], ![0, 1, 2, 4, 5, 3],
      by decide, by decide⟩ : Equiv.Perm (Fin 6))
  rw [hfamily] at hbridge
  exact hbridge.trans (by decide)

/-- The nested family dies through its orbit-four representative. -/
theorem SixThreeCrux.false_of_family_canonicalNestedFamily
    (crux : SixThreeCrux)
    (hfamily : chartArgmaxFamily (chartPointOfDesign crux.design)
      = canonicalNestedFamily) :
    False := by
  apply SixThreeCrux.false_of_family_orbitFourFamily
    (crux.relabel (⟨![1, 0, 2, 3, 4, 5], ![1, 0, 2, 3, 4, 5],
      by decide, by decide⟩ : Equiv.Perm (Fin 6)))
  have hbridge := chartArgmaxFamily_relabelDesign crux.design
    (⟨![1, 0, 2, 3, 4, 5], ![1, 0, 2, 3, 4, 5],
      by decide, by decide⟩ : Equiv.Perm (Fin 6))
  rw [hfamily] at hbridge
  exact hbridge.trans (by decide)

/-- **RUNG FOUR IS CLOSED.**  No crux has a four-block argmax family. -/
theorem SixThreeCrux.false_of_card_chartArgmaxFamily_eq_four
    (crux : SixThreeCrux)
    (hfour : (chartArgmaxFamily (chartPointOfDesign crux.design)).card = 4) :
    False := by
  obtain ⟨relabelPerm, hdoor⟩ :=
    crux.exists_relabel_family_canonical_of_card_four hfour
  rcases hdoor with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalEdgePencil h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalChairFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalFivePathFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalTriangleEdgeFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalThreeTripleFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalTetrahedronFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalDoubleDoubleFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalTridentFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalZigzagFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalTwinPairsFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalHookFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalNestedFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalDoublePathFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalPendantSplitFamily h
  · exact (crux.relabel relabelPerm).false_of_family_canonicalPendantForkFamily h

end Gtz
