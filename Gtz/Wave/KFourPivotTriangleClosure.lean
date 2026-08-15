import Gtz.Wave.KFourPivotRecurrentTriangleWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The K4 pivot wall is exactly the triangle-stall closure

The priced endpoint left by pivot propagation is not independent of the
triangle-stall branch.  Its weak tree is classified as a vertex star, while
the endpoint already carries a positive-definite pointer window.  A vertex
star plus any edge outside it contains a triangle.  Descending that window
therefore either produces a strict spanning tree immediately or exposes the
same triangle stall consumed by the recurrent branch.

Consequently one contextual proposition closes both terminal arms of the
pivot wall:

* recurrent stalls reduce to triangle stalls by the adjacent-four-set law;
* priced star endpoints reduce to triangle stalls through their pointer
  window.

The final equivalence removes the priced endpoint closure from the live A3
interface altogether.
-/

namespace Gtz

/-! ## A star plus a chord contains a triangle -/

/-- In `K4`, adjoining any edge outside a vertex star creates a triangle. -/
theorem kFour_star_insert_containsTriangle (tree : Finset (Fin 6))
    (htree : tree ∈ kFourStarList) (added : Fin 6) (hadded : added ∉ tree) :
    KFourContainsTriangle (insert added tree) := by
  simp [kFourStarList] at htree
  rcases htree with rfl | rfl | rfl | rfl <;>
    fin_cases added <;> simp_all [KFourContainsTriangle] <;> decide

/-! ## The priced endpoint feeds the triangle branch -/

/-- **THE PRICED ENDPOINT IS NOT A SEPARATE LEAF.**  A contextual
triangle-stall closure also closes every classified priced star endpoint.

The endpoint's pointer window is already positive definite.  Since the old
tree is a star and the pointer lies outside it, that window contains a
triangle.  Card-four descent either finds a strict tree or returns the window
as the triangle stall. -/
theorem kFourPivotWallPricedStarEndpointClosure_of_triangleStallClosure
    (hclose : KFourPivotWallTriangleStallClosure) :
    KFourPivotWallPricedStarEndpointClosure := by
  intro point tree htree hgap hwindow hwall data hstar _hopposite
  let selected := insert data.endpoint.endpoint.pointer tree
  have hpointer : data.endpoint.endpoint.pointer ∉ tree :=
    data.endpoint.endpoint.pointer_notMem
  have hcard : selected.card = 4 := by
    simp only [selected]
    rw [Finset.card_insert_of_notMem hpointer,
      kFourSpanningTree_card tree htree]
  have hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef := by
    exact data.endpoint.endpoint.window_posDef
  have htriangle : KFourContainsTriangle selected := by
    exact kFour_star_insert_containsTriangle tree hstar
      data.endpoint.endpoint.pointer hpointer
  rcases exists_strictTree_or_cardFour_stall_of_posDef point hcard hpd with
    hstrict | hstall
  · exact hstrict
  · exact hclose point tree htree hgap hwindow hwall selected hcard hpd
      hstall htriangle

/-! ## Collapse the whole pivot wall -/

/-- One triangle-stall closure supplies both components of the classified
pivot propagation package. -/
theorem kFourPivotWallStarPropagationClosure_of_triangleStallClosure
    (hclose : KFourPivotWallTriangleStallClosure) :
    KFourPivotWallStarPropagationClosure :=
  ⟨kFourPivotWallRecurrentStallClosure_of_triangleStallClosure hclose,
    kFourPivotWallPricedStarEndpointClosure_of_triangleStallClosure hclose⟩

/-- The contextual triangle-stall closure closes the complete four-pivot
window wall.  The formerly independent priced endpoint is discharged through
its positive-definite pointer window. -/
theorem kFourWindowAllPivotWallClosure_of_triangleStallClosure
    (hclose : KFourPivotWallTriangleStallClosure) :
    KFourWindowAllPivotWallClosure :=
  kFourWindowAllPivotWallClosure_iff_starPropagation.mpr
    (kFourPivotWallStarPropagationClosure_of_triangleStallClosure hclose)

/-- Conversely, a closed pivot wall trivially closes each contextual triangle
stall by returning the wall's strict-tree witness. -/
theorem kFourPivotWallTriangleStallClosure_of_windowAllPivotWallClosure
    (hclose : KFourWindowAllPivotWallClosure) :
    KFourPivotWallTriangleStallClosure := by
  intro point tree htree hgap hwindow hwall _selected _hcard _hpd _hstall
    _htriangle
  exact hclose point tree htree hgap hwindow hwall

/-- **THE PIVOT-WALL COLLAPSE.**  Closing the four-pivot wall is exactly
closing its triangle-containing card-four stalls. -/
theorem kFourWindowAllPivotWallClosure_iff_triangleStallClosure :
    KFourWindowAllPivotWallClosure ↔ KFourPivotWallTriangleStallClosure :=
  ⟨kFourPivotWallTriangleStallClosure_of_windowAllPivotWallClosure,
    kFourWindowAllPivotWallClosure_of_triangleStallClosure⟩

/-! ## Registry-facing composition -/

/-- The two genuinely independent A3 inputs after the pivot collapse: the
contextual triangle-stall closure and the canonical gauge-star closure. -/
def KFourGaugeTriangleClosure : Prop :=
  KFourPivotWallTriangleStallClosure ∧ KFourGaugeStarCorankWallClosure

/-- Exact replacement of the former gauge-plus-pivot package. -/
theorem kFourGaugeAndPivotWallClosure_iff_gaugeTriangleClosure :
    KFourGaugeAndPivotWallClosure ↔ KFourGaugeTriangleClosure := by
  rw [KFourGaugeAndPivotWallClosure, KFourGaugeTriangleClosure,
    kFourWindowAllPivotWallClosure_iff_triangleStallClosure]

/-- Triangle stalls plus the gauge wall discharge the public K4 knife band. -/
theorem kFourKnifeBandRefined_of_gaugeTriangleClosure
    (hclose : KFourGaugeTriangleClosure) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_gaugeTriangleClosure.mpr hclose)

/-- Triangle stalls plus the gauge wall produce the design-side selector used
by the registry. -/
theorem kFourFamilySelection_of_gaugeTriangleClosure
    (hclose : KFourGaugeTriangleClosure) : KFourFamilySelection :=
  kFourFamilySelection_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_gaugeTriangleClosure.mpr hclose)

/-- The same reduced pair gives a strict K4 tree at every chart point. -/
theorem kFourEveryPointHasStrictTree_of_gaugeTriangleClosure
    (hclose : KFourGaugeTriangleClosure) : KFourEveryPointHasStrictTree :=
  kFourEveryPointHasStrictTree_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_iff_gaugeTriangleClosure.mpr hclose)

end Gtz
