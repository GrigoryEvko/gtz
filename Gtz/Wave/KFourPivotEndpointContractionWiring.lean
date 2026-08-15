import Gtz.Design.PivotEndpointContraction
import Gtz.Wave.KFourPivotEndpointOrthogonalityWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Wire the exact K4 endpoint contraction into A3

The former endpoint interface retained only that the inserted edge was
orthogonal to the old tight direction.  The K4 voltage and determinant
classification now proves that it is the unique orthogonal edge.  Thus the
residual lives on a genuine one-edge contraction, not on a union of triangle
and opposite-pair degeneracies.

This module replaces the orthogonal endpoint closure by that exact contracted
interface, proves equivalence with every previous closure, and propagates the
replacement to all live K4/A3 consumers.
-/

namespace Gtz

/-! ## Replace the endpoint closure -/

/-- Close only the one-edge contraction endpoint that the producer can
actually reach. -/
def KFourPivotWallPricedContractedEndpointClosure : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourSpanningTreeList →
    (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef →
    KFourTreeWindowData point tree →
    KFourTreeWindowAllPivotWallData point tree →
    KFourPivotWallPricedContractedEndpointData point tree →
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef

/-- Forgetting uniqueness turns any contracted endpoint proof into the former
orthogonal endpoint proof. -/
theorem kFourPivotWallPricedContractedEndpointClosure_of_orthogonalEndpointClosure
    (hclose : KFourPivotWallPricedOrthogonalEndpointClosure) :
    KFourPivotWallPricedContractedEndpointClosure := by
  intro point tree htree hgap hwindow hwall data
  exact hclose point tree htree hgap hwindow hwall data.endpoint

/-- The exact contraction producer upgrades every orthogonal endpoint before
invoking the contracted closure. -/
theorem kFourPivotWallPricedOrthogonalEndpointClosure_of_contractedEndpointClosure
    (hclose : KFourPivotWallPricedContractedEndpointClosure) :
    KFourPivotWallPricedOrthogonalEndpointClosure := by
  intro point tree htree hgap hwindow hwall data
  obtain ⟨contracted⟩ := kFourPivotWall_pricedContractedEndpointData data
  exact hclose point tree htree hgap hwindow hwall contracted

/-- Exact replacement of the endpoint closure. -/
theorem kFourPivotWallPricedOrthogonalEndpointClosure_iff_contractedEndpointClosure :
    KFourPivotWallPricedOrthogonalEndpointClosure ↔
      KFourPivotWallPricedContractedEndpointClosure :=
  ⟨kFourPivotWallPricedContractedEndpointClosure_of_orthogonalEndpointClosure,
    kFourPivotWallPricedOrthogonalEndpointClosure_of_contractedEndpointClosure⟩

/-- The original opaque priced endpoint is equivalent to the exact contracted
endpoint as a closure obligation. -/
theorem kFourPivotWallPricedEndpointClosure_iff_contractedEndpointClosure :
    KFourPivotWallPricedEndpointClosure ↔
      KFourPivotWallPricedContractedEndpointClosure :=
  kFourPivotWallPricedEndpointClosure_iff_orthogonalEndpointClosure.trans
    kFourPivotWallPricedOrthogonalEndpointClosure_iff_contractedEndpointClosure

/-! ## Replace the propagation closure -/

/-- The recurrent four-stall remains; the five-label arm is now a literal
one-edge contraction endpoint. -/
def KFourPivotWallContractedPropagationClosure : Prop :=
  KFourPivotWallRecurrentStallClosure ∧
    KFourPivotWallPricedContractedEndpointClosure

/-- Exact replacement of the orthogonal propagation interface. -/
theorem kFourPivotWallOrthogonalPropagationClosure_iff_contractedPropagation :
    KFourPivotWallOrthogonalPropagationClosure ↔
      KFourPivotWallContractedPropagationClosure := by
  rw [KFourPivotWallOrthogonalPropagationClosure,
    KFourPivotWallContractedPropagationClosure,
    kFourPivotWallPricedOrthogonalEndpointClosure_iff_contractedEndpointClosure]

/-- Exact replacement of the original propagation interface. -/
theorem kFourPivotWallPropagationClosure_iff_contractedPropagation :
    KFourPivotWallPropagationClosure ↔
      KFourPivotWallContractedPropagationClosure := by
  rw [KFourPivotWallPropagationClosure,
    KFourPivotWallContractedPropagationClosure,
    kFourPivotWallPricedEndpointClosure_iff_contractedEndpointClosure]

/-- Closing every four-pivot window is now exactly closing the recurrent stall
and the unique-edge contraction endpoint. -/
theorem kFourWindowAllPivotWallClosure_iff_contractedPropagation :
    KFourWindowAllPivotWallClosure ↔
      KFourPivotWallContractedPropagationClosure :=
  kFourWindowAllPivotWallClosure_iff_orthogonalPropagation.trans
    kFourPivotWallOrthogonalPropagationClosure_iff_contractedPropagation

/-! ## Gauge-star joint and live consumers -/

/-- The terminal K4 component pair with the exact endpoint contraction. -/
def KFourGaugeAndPivotContractedPropagationClosure : Prop :=
  KFourPivotWallContractedPropagationClosure ∧
    KFourGaugeStarCorankWallClosure

/-- Exact replacement at the gauge-star/pivot joint. -/
theorem kFourGaugeAndPivotWallClosure_iff_contractedPropagation :
    KFourGaugeAndPivotWallClosure ↔
      KFourGaugeAndPivotContractedPropagationClosure := by
  rw [KFourGaugeAndPivotWallClosure,
    KFourGaugeAndPivotContractedPropagationClosure,
    kFourWindowAllPivotWallClosure_iff_contractedPropagation]

/-- The contracted conjunction discharges the live all-max-heavy A3 formula. -/
theorem kFourKnifeBandRefinedAllMaxHeavy_of_gaugeAndPivotContractedPropagation
    (hclose : KFourGaugeAndPivotContractedPropagationClosure) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_contractedPropagation.mpr hclose)

/-- The contracted conjunction discharges the public refined K4 knife band. -/
theorem kFourKnifeBandRefined_of_gaugeAndPivotContractedPropagation
    (hclose : KFourGaugeAndPivotContractedPropagationClosure) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_contractedPropagation.mpr hclose)

/-- The same route produces the design-side K4 family selection. -/
theorem kFourFamilySelection_of_gaugeAndPivotContractedPropagation
    (hclose : KFourGaugeAndPivotContractedPropagationClosure) :
    KFourFamilySelection :=
  kFourFamilySelection_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_contractedPropagation.mpr hclose)

/-- It also produces a strict K4 tree at every chart point. -/
theorem kFourEveryPointHasStrictTree_of_gaugeAndPivotContractedPropagation
    (hclose : KFourGaugeAndPivotContractedPropagationClosure) :
    KFourEveryPointHasStrictTree :=
  kFourEveryPointHasStrictTree_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_contractedPropagation.mpr hclose)

end Gtz
