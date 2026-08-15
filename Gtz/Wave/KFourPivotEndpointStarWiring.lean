import Gtz.Design.PivotEndpointStarClassification
import Gtz.Wave.KFourPivotEndpointContractionWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Wire the star classification of the K4 priced endpoint into A3

The exact contraction endpoint is more rigid than its former interface records.
The old weak tree is necessarily one of the four vertex stars, and it contains
the edge opposite the unique zero-voltage contraction edge.  This module makes
that classification available to the live closure obligation without changing
its logical strength.

It also exposes the requested two-argument atlas adapter.  Once the canonical
gauge-star atlas law and the pivot-wall atlas law are proved, the public K4
knife-band statement, the family selector, and the every-point strict-tree law
follow by direct application; no atlas-invariance theorem is involved.
-/

namespace Gtz

/-! ## Replace the endpoint closure by the star endpoint -/

/-- Close only the classified endpoint actually produced by the priced arm:
the old tree is a vertex star and contains the edge opposite the inserted
contraction edge. -/
def KFourPivotWallPricedStarEndpointClosure : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourSpanningTreeList →
    (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef →
    KFourTreeWindowData point tree →
    KFourTreeWindowAllPivotWallData point tree →
    ∀ data : KFourPivotWallPricedContractedEndpointData point tree,
      tree ∈ kFourStarList →
      kFourOppositeEdge data.endpoint.endpoint.added ∈ tree →
      ∃ winner ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight winner).PosDef

/-- Any proof of the former contracted endpoint immediately handles the
classified star endpoint. -/
theorem kFourPivotWallPricedStarEndpointClosure_of_contractedEndpointClosure
    (hclose : KFourPivotWallPricedContractedEndpointClosure) :
    KFourPivotWallPricedStarEndpointClosure := by
  intro point tree htree hgap hwindow hwall data _hstar _hopposite
  exact hclose point tree htree hgap hwindow hwall data

/-- The endpoint classifier supplies both extra hypotheses before invoking a
star-endpoint proof. -/
theorem kFourPivotWallPricedContractedEndpointClosure_of_starEndpointClosure
    (hclose : KFourPivotWallPricedStarEndpointClosure) :
    KFourPivotWallPricedContractedEndpointClosure := by
  intro point tree htree hgap hwindow hwall data
  have hshape := data.tree_star_and_opposite_mem htree hgap
  exact hclose point tree htree hgap hwindow hwall data hshape.1 hshape.2

/-- Exact replacement of the contracted endpoint by its star normal form. -/
theorem kFourPivotWallPricedContractedEndpointClosure_iff_starEndpointClosure :
    KFourPivotWallPricedContractedEndpointClosure ↔
      KFourPivotWallPricedStarEndpointClosure :=
  ⟨kFourPivotWallPricedStarEndpointClosure_of_contractedEndpointClosure,
    kFourPivotWallPricedContractedEndpointClosure_of_starEndpointClosure⟩

/-- The original opaque priced endpoint is therefore equivalent to closing
only the classified star endpoint. -/
theorem kFourPivotWallPricedEndpointClosure_iff_starEndpointClosure :
    KFourPivotWallPricedEndpointClosure ↔
      KFourPivotWallPricedStarEndpointClosure :=
  kFourPivotWallPricedEndpointClosure_iff_contractedEndpointClosure.trans
    kFourPivotWallPricedContractedEndpointClosure_iff_starEndpointClosure

/-! ## Propagate the replacement to the live joints -/

/-- The pivot residual after the star classification: a recurrent card-four
stall, or the classified priced star endpoint. -/
def KFourPivotWallStarPropagationClosure : Prop :=
  KFourPivotWallRecurrentStallClosure ∧ KFourPivotWallPricedStarEndpointClosure

/-- Exact replacement of the contracted propagation interface. -/
theorem kFourPivotWallContractedPropagationClosure_iff_starPropagation :
    KFourPivotWallContractedPropagationClosure ↔
      KFourPivotWallStarPropagationClosure := by
  rw [KFourPivotWallContractedPropagationClosure,
    KFourPivotWallStarPropagationClosure,
    kFourPivotWallPricedContractedEndpointClosure_iff_starEndpointClosure]

/-- Exact replacement of the public four-pivot wall closure. -/
theorem kFourWindowAllPivotWallClosure_iff_starPropagation :
    KFourWindowAllPivotWallClosure ↔ KFourPivotWallStarPropagationClosure :=
  kFourWindowAllPivotWallClosure_iff_contractedPropagation.trans
    kFourPivotWallContractedPropagationClosure_iff_starPropagation

/-- The terminal A3 pair after the endpoint star classification. -/
def KFourGaugeAndPivotStarPropagationClosure : Prop :=
  KFourPivotWallStarPropagationClosure ∧ KFourGaugeStarCorankWallClosure

/-- Exact replacement at the gauge-star/pivot joint. -/
theorem kFourGaugeAndPivotWallClosure_iff_starPropagation :
    KFourGaugeAndPivotWallClosure ↔
      KFourGaugeAndPivotStarPropagationClosure := by
  rw [KFourGaugeAndPivotWallClosure,
    KFourGaugeAndPivotStarPropagationClosure,
    kFourWindowAllPivotWallClosure_iff_starPropagation]

/-- The classified terminal conjunction discharges the public K4 knife band. -/
theorem kFourKnifeBandRefined_of_gaugeAndPivotStarPropagation
    (hclose : KFourGaugeAndPivotStarPropagationClosure) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_starPropagation.mpr hclose)

/-- The classified terminal conjunction also yields the design-side family
selector. -/
theorem kFourFamilySelection_of_gaugeAndPivotStarPropagation
    (hclose : KFourGaugeAndPivotStarPropagationClosure) :
    KFourFamilySelection :=
  kFourFamilySelection_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_starPropagation.mpr hclose)

/-! ## Flip-ready atlas adapters -/

/-- **THE TWO-ARGUMENT A3 ADAPTER.**  Canonical gauge-star atlas firing and
pivot-wall atlas firing discharge the public K4 knife-band statement directly.
No transport theorem for the atlas predicate is assumed. -/
theorem kFourKnifeBandRefined_of_gaugeStarAtlasFires_of_pivotAtlasFires
    (hgauge : KFourGaugeStarWallAtlasFires)
    (hpivot : KFourPivotWallAtlasFires) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_atlasFires ⟨hgauge, hpivot⟩)

/-- The same explicit pair discharges the K4 family selector. -/
theorem kFourFamilySelection_of_gaugeStarAtlasFires_of_pivotAtlasFires
    (hgauge : KFourGaugeStarWallAtlasFires)
    (hpivot : KFourPivotWallAtlasFires) : KFourFamilySelection :=
  kFourFamilySelection_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_atlasFires ⟨hgauge, hpivot⟩)

/-- The same explicit pair gives a strict K4 tree at every chart point. -/
theorem kFourEveryPointHasStrictTree_of_gaugeStarAtlasFires_of_pivotAtlasFires
    (hgauge : KFourGaugeStarWallAtlasFires)
    (hpivot : KFourPivotWallAtlasFires) : KFourEveryPointHasStrictTree :=
  kFourEveryPointHasStrictTree_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_atlasFires ⟨hgauge, hpivot⟩)

end Gtz
