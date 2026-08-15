import Gtz.Design.PivotEndpointOrthogonality
import Gtz.Wave.KFourPivotStallPropagationWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Wire the orthogonal pivot endpoint into A3

The previous propagation interface retained an opaque priced five-set endpoint.
The design-side collapse now proves that every such endpoint lies on one exact
zero-cross locus: its inserted edge is orthogonal to the original tight
direction and preserves that direction as a kernel of the exchanged four-set.

This module replaces the old endpoint closure by that strictly narrower input,
proves exact equivalence with the old propagation closure, and carries the
replacement through the gauge-star conjunction to A3 and K4 family selection.
-/

namespace Gtz

/-! ## The sharpened endpoint closure -/

/-- Close only the geometric endpoint that the producer can actually reach. -/
def KFourPivotWallPricedOrthogonalEndpointClosure : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourSpanningTreeList →
    (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef →
    KFourTreeWindowData point tree →
    KFourTreeWindowAllPivotWallData point tree →
    KFourPivotWallPricedOrthogonalEndpointData point tree →
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef

/-- The old endpoint closure trivially handles the narrowed endpoint by
forgetting its proved orthogonality fields. -/
theorem kFourPivotWallPricedOrthogonalEndpointClosure_of_pricedEndpointClosure
    (hclose : KFourPivotWallPricedEndpointClosure) :
    KFourPivotWallPricedOrthogonalEndpointClosure := by
  intro point tree htree hgap hwindow hwall data
  exact hclose point tree htree hgap hwindow hwall data.endpoint

/-- Conversely, the orthogonality producer turns every old endpoint into the
narrowed one before invoking its closure. -/
theorem kFourPivotWallPricedEndpointClosure_of_orthogonalEndpointClosure
    (hclose : KFourPivotWallPricedOrthogonalEndpointClosure) :
    KFourPivotWallPricedEndpointClosure := by
  intro point tree htree hgap hwindow hwall data
  obtain ⟨orthogonalData⟩ :=
    kFourPivotWall_pricedOrthogonalEndpointData point hgap hwindow data
  exact hclose point tree htree hgap hwindow hwall orthogonalData

/-- The replacement is exact, not a stronger assumption. -/
theorem kFourPivotWallPricedEndpointClosure_iff_orthogonalEndpointClosure :
    KFourPivotWallPricedEndpointClosure ↔
      KFourPivotWallPricedOrthogonalEndpointClosure :=
  ⟨kFourPivotWallPricedOrthogonalEndpointClosure_of_pricedEndpointClosure,
    kFourPivotWallPricedEndpointClosure_of_orthogonalEndpointClosure⟩

/-! ## Replace the endpoint throughout the propagation route -/

/-- The recurrent four-stall remains, but the five-set arm is now the exact
orthogonal endpoint rather than arbitrary priced endpoint data. -/
def KFourPivotWallOrthogonalPropagationClosure : Prop :=
  KFourPivotWallRecurrentStallClosure ∧
    KFourPivotWallPricedOrthogonalEndpointClosure

/-- Exact replacement of the previous two-arm propagation closure. -/
theorem kFourPivotWallPropagationClosure_iff_orthogonalPropagation :
    KFourPivotWallPropagationClosure ↔
      KFourPivotWallOrthogonalPropagationClosure := by
  rw [KFourPivotWallPropagationClosure,
    KFourPivotWallOrthogonalPropagationClosure,
    kFourPivotWallPricedEndpointClosure_iff_orthogonalEndpointClosure]

/-- The independent pivot component itself is now exactly the conjunction of
the recurrent stall and the orthogonal endpoint closures. -/
theorem kFourWindowAllPivotWallClosure_iff_orthogonalPropagation :
    KFourWindowAllPivotWallClosure ↔
      KFourPivotWallOrthogonalPropagationClosure :=
  kFourWindowAllPivotWallClosure_iff_propagation.trans
    kFourPivotWallPropagationClosure_iff_orthogonalPropagation

/-- The complete K4 wall route with the sharpened pivot component. -/
def KFourGaugeAndPivotOrthogonalPropagationClosure : Prop :=
  KFourPivotWallOrthogonalPropagationClosure ∧
    KFourGaugeStarCorankWallClosure

/-- Exact replacement at the gauge-star/pivot joint. -/
theorem kFourGaugeAndPivotWallClosure_iff_orthogonalPropagation :
    KFourGaugeAndPivotWallClosure ↔
      KFourGaugeAndPivotOrthogonalPropagationClosure := by
  rw [KFourGaugeAndPivotWallClosure,
    KFourGaugeAndPivotOrthogonalPropagationClosure,
    kFourWindowAllPivotWallClosure_iff_orthogonalPropagation]

/-! ## Live consumers -/

/-- The sharpened conjunction discharges the live all-max-heavy A3 formula. -/
theorem kFourKnifeBandRefinedAllMaxHeavy_of_gaugeAndPivotOrthogonalPropagation
    (hclose : KFourGaugeAndPivotOrthogonalPropagationClosure) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_orthogonalPropagation.mpr hclose)

/-- The sharpened conjunction discharges the public refined K4 knife band. -/
theorem kFourKnifeBandRefined_of_gaugeAndPivotOrthogonalPropagation
    (hclose : KFourGaugeAndPivotOrthogonalPropagationClosure) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_orthogonalPropagation.mpr hclose)

/-- The same route produces the design-side K4 family selection. -/
theorem kFourFamilySelection_of_gaugeAndPivotOrthogonalPropagation
    (hclose : KFourGaugeAndPivotOrthogonalPropagationClosure) :
    KFourFamilySelection :=
  kFourFamilySelection_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_orthogonalPropagation.mpr hclose)

/-- It also produces a strict K4 tree at every chart point. -/
theorem kFourEveryPointHasStrictTree_of_gaugeAndPivotOrthogonalPropagation
    (hclose : KFourGaugeAndPivotOrthogonalPropagationClosure) :
    KFourEveryPointHasStrictTree :=
  kFourEveryPointHasStrictTree_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_orthogonalPropagation.mpr hclose)

end Gtz
