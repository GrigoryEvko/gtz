import Gtz.Design.PivotStallPropagation
import Gtz.Wave.KFourGaugeStarTransportWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# Wire pivot-stall propagation into the K4 A3 consumer

The previous pivot-wall obligation asked for a strict spanning tree directly at
every four-pivot window.  `PivotStallPropagation` now spends the exact centered
balance and the rank-one insertion law before that obligation reaches the
registry.  Three outcomes remain:

* one further erasure already produces a strict spanning tree;
* the exchanged positive-definite four-set is itself stalled;
* the five-set reaches the strict half-priced endpoint.

This module names only the latter two residual closures and proves that their
conjunction is *equivalent* to the former pivot-wall closure.  It then composes
that exact decomposition with the independent gauge-star closure and the live
K4 family selector.
-/

namespace Gtz

open Matrix

/-! ## The two exact residual closures -/

/-- Close the recurrent arm: after the pivot-wall exchange, the resulting
positive-definite four-set still has all four deletion pivots at least one. -/
def KFourPivotWallRecurrentStallClosure : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourSpanningTreeList →
    (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef →
    KFourTreeWindowData point tree →
    KFourTreeWindowAllPivotWallData point tree →
    KFourPivotWallRecurrentStallData point tree →
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef

/-- Close the endpoint arm: the inserted label has self-pivot in `[1/2,1)`,
all four old pivots remain at least one, and the missing label is priced above
`1 + 1/(2w)`.  The statement asks only for a strict tree, so an endpoint proof
may either contradict the data or construct a winner elsewhere. -/
def KFourPivotWallPricedEndpointClosure : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourSpanningTreeList →
    (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef →
    KFourTreeWindowData point tree →
    KFourTreeWindowAllPivotWallData point tree →
    KFourPivotWallPricedEndpointData point tree →
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef

/-- The two residual arms left after spending pivot-stall propagation. -/
def KFourPivotWallPropagationClosure : Prop :=
  KFourPivotWallRecurrentStallClosure ∧
    KFourPivotWallPricedEndpointClosure

/-! ## Exact identification with the old wall closure -/

/-- Any proof of the old direct wall closure closes each narrowed propagation
arm by forgetting its additional data. -/
theorem kFourPivotWallPropagationClosure_of_windowClosure
    (hclose : KFourWindowAllPivotWallClosure) :
    KFourPivotWallPropagationClosure := by
  constructor
  · intro point tree htree hgap hwindow hwall _hrecurrent
    exact hclose point tree htree hgap hwindow hwall
  · intro point tree htree hgap hwindow hwall _hendpoint
    exact hclose point tree htree hgap hwindow hwall

/-- Conversely, the propagation capstone discharges the old wall closure from
the two narrowed arms; its first branch is already a strict tree. -/
theorem kFourWindowAllPivotWallClosure_of_propagation
    (hclose : KFourPivotWallPropagationClosure) :
    KFourWindowAllPivotWallClosure := by
  intro point tree htree hgap hwindow hwall
  rcases kFourPivotWall_strictTree_or_recurrentStall_or_pricedEndpoint point
      htree hgap hwindow hwall with hstrict | hrecurrent | hendpoint
  · exact hstrict
  · exact hclose.1 point tree htree hgap hwindow hwall hrecurrent
  · obtain ⟨endpoint⟩ := hendpoint
    exact hclose.2 point tree htree hgap hwindow hwall endpoint

/-- **THE PIVOT-WALL RESIDUAL IDENTIFICATION.**  Closing every four-pivot
window is exactly closing the recurrent exchanged four-set and the strict
half-priced endpoint. -/
theorem kFourWindowAllPivotWallClosure_iff_propagation :
    KFourWindowAllPivotWallClosure ↔ KFourPivotWallPropagationClosure :=
  ⟨kFourPivotWallPropagationClosure_of_windowClosure,
    kFourWindowAllPivotWallClosure_of_propagation⟩

/-! ## Compose with the gauge-star component and A3 -/

/-- The terminal K4 component pair in its narrowed pivot-wall formulation. -/
def KFourGaugeAndPivotPropagationClosure : Prop :=
  KFourPivotWallPropagationClosure ∧ KFourGaugeStarCorankWallClosure

/-- The old and narrowed component pairs are exactly equivalent. -/
theorem kFourGaugeAndPivotWallClosure_iff_propagation :
    KFourGaugeAndPivotWallClosure ↔ KFourGaugeAndPivotPropagationClosure := by
  rw [KFourGaugeAndPivotWallClosure, KFourGaugeAndPivotPropagationClosure,
    kFourWindowAllPivotWallClosure_iff_propagation]

/-- The narrowed pivot residuals plus the canonical gauge-star wall discharge
the live tied-axis A3 proposition. -/
theorem kFourKnifeBandRefinedAllMaxHeavy_of_gaugeAndPivotPropagation
    (hclose : KFourGaugeAndPivotPropagationClosure) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_propagation.mpr hclose)

/-- The same two residual pivot arms and gauge-star closure reach the public K4
chart selection statement. -/
theorem kFourKnifeBandRefined_of_gaugeAndPivotPropagation
    (hclose : KFourGaugeAndPivotPropagationClosure) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_propagation.mpr hclose)

/-- **THE REGISTRY CONSUMER.**  Gauge-star closure plus the two propagated
pivot residual closures produce the design-side K4 family selector. -/
theorem kFourFamilySelection_of_gaugeAndPivotPropagation
    (hclose : KFourGaugeAndPivotPropagationClosure) : KFourFamilySelection :=
  kFourFamilySelection_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_propagation.mpr hclose)

/-- Equivalently, the narrowed component package supplies a strict K4 spanning
tree at every chart point. -/
theorem kFourEveryPointHasStrictTree_of_gaugeAndPivotPropagation
    (hclose : KFourGaugeAndPivotPropagationClosure) :
    KFourEveryPointHasStrictTree :=
  kFourEveryPointHasStrictTree_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_propagation.mpr hclose)

end Gtz
