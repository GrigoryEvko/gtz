import Gtz.Design.StallTypeSplit
import Gtz.Wave.KFourPivotEndpointStarWiring

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Reduce the recurrent K4 pivot arm to triangle stalls

The recurrent pivot package contains more structure than an arbitrary
positive-definite four-set.  It records two adjacent four-edge selections:

* the original positive-definite pointer window; and
* the positive-definite set obtained by inserting one edge and erasing another.

Two adjacent four-edge selections of `K4` cannot both be four-cycles.  Their
two-edge complements share the label omitted by their common five-set, whereas
the three perfect matchings of `K4` are pairwise disjoint.  Hence one of the
two selections contains a triangle.  If the pointer window is not stalled, it
already deletes to a strict tree; otherwise it is itself the triangle stall.

Thus the recurrent matching-complement/type-A branch is not an independent
obligation.  A closure theorem for triangle/type-B stalls closes the whole
recurrent arm.  The final section wires that reduction together with the
classified priced-star endpoint and the gauge-star component into A3.
-/

namespace Gtz

/-! ## The adjacent-four-set combinatorics -/

/-- A four-edge selection contains one of the four triangles of `K4`. -/
def KFourContainsTriangle (selected : Finset (Fin 6)) : Prop :=
  {0, 1, 2} ⊆ selected ∨ {0, 3, 4} ⊆ selected ∨
    {1, 3, 5} ⊆ selected ∨ {2, 4, 5} ⊆ selected

/-- The three perfect matchings of `K4` are pairwise disjoint.  Consequently
two of them containing a common edge are the same matching. -/
theorem kFour_matching_eq_of_common_mem (first second : Finset (Fin 6))
    (hfirst : first = {0, 5} ∨ first = {1, 4} ∨ first = {2, 3})
    (hsecond : second = {0, 5} ∨ second = {1, 4} ∨ second = {2, 3})
    (edge : Fin 6) (hfirstMem : edge ∈ first) (hsecondMem : edge ∈ second) :
    first = second := by
  rcases hfirst with rfl | rfl | rfl <;>
    rcases hsecond with rfl | rfl | rfl <;> simp_all <;>
      rcases hfirstMem with rfl | rfl <;> simp_all

/-- Two adjacent four-edge selections of `K4` cannot both be four-cycles.
The pointer window or the four-set obtained by one exchange contains a
triangle. -/
theorem kFour_exchange_window_or_result_contains_triangle
    (tree : Finset (Fin 6)) (htree : tree ∈ kFourSpanningTreeList)
    (pointer : Fin 6) (hpointer : pointer ∉ tree)
    (added : Fin 6) (hadded : added ∉ insert pointer tree)
    (dropped : Fin 6) (hdropped : dropped ∈ insert pointer tree) :
    KFourContainsTriangle (insert pointer tree) ∨
      KFourContainsTriangle
        ((insert added (insert pointer tree)).erase dropped) := by
  let window := insert pointer tree
  let result := (insert added window).erase dropped
  have hwindowCard : window.card = 4 := by
    simp only [window]
    rw [Finset.card_insert_of_notMem hpointer,
      kFourSpanningTree_card tree htree]
  have hdroppedInsert : dropped ∈ insert added window :=
    Finset.mem_insert_of_mem hdropped
  have hresultCard : result.card = 4 := by
    simp only [result]
    rw [Finset.card_erase_of_mem hdroppedInsert,
      Finset.card_insert_of_notMem hadded, hwindowCard]
  rcases kFourCardFour_matchingCompl_or_triangle window hwindowCard with
    hwindowMatching | hwindowTriangle
  · rcases kFourCardFour_matchingCompl_or_triangle result hresultCard with
      hresultMatching | hresultTriangle
    · exfalso
      have haddedComp : added ∈ windowᶜ := Finset.mem_compl.mpr hadded
      have hcompCard : windowᶜ.card = 2 := by
        rw [Finset.card_compl, hwindowCard]
        norm_num
      have heraseCard : (windowᶜ.erase added).card = 1 := by
        rw [Finset.card_erase_of_mem haddedComp, hcompCard]
      obtain ⟨shared, hsharedErase⟩ : (windowᶜ.erase added).Nonempty := by
        rw [← Finset.card_pos, heraseCard]
        norm_num
      have hsharedWindow : shared ∈ windowᶜ :=
        Finset.mem_of_mem_erase hsharedErase
      have hsharedNe : shared ≠ added := (Finset.mem_erase.mp hsharedErase).1
      have hsharedResult : shared ∈ resultᶜ := by
        rw [Finset.mem_compl]
        simp [result, hsharedNe, Finset.mem_compl.mp hsharedWindow]
      have hcomplEq : windowᶜ = resultᶜ :=
        kFour_matching_eq_of_common_mem windowᶜ resultᶜ hwindowMatching
          hresultMatching shared hsharedWindow hsharedResult
      have haddedNeDropped : added ≠ dropped := by
        intro heq
        exact hadded (heq ▸ hdropped)
      have haddedResult : added ∈ result := by
        simp [result, haddedNeDropped]
      have hnotResult : added ∉ result := by
        have hmem : added ∈ resultᶜ := hcomplEq ▸ haddedComp
        exact Finset.mem_compl.mp hmem
      exact hnotResult haddedResult
    · exact Or.inr hresultTriangle
  · exact Or.inl hwindowTriangle

/-! ## Extract a triangle stall from the recurrent package -/

/-- The pointer window retained by an exchange package is positive definite:
erasing the inserted label from the positive-definite five-set returns it. -/
theorem KFourPivotWallExchangeData.window_posDef
    {point : DirectionChartPoint 6} {tree : Finset (Fin 6)}
    (data : KFourPivotWallExchangeData point tree) :
    (directionChartGap kFourDirection point.mass point.weight
      (insert data.pointer tree)).PosDef := by
  have hmem : data.added ∈ insert data.added (insert data.pointer tree) :=
    Finset.mem_insert_self _ _
  have herase := (posDef_directionChartGap_erase_iff kFourDirection point.mass
    point.weight point.mass_pos point.weight_pos
      (insert data.added (insert data.pointer tree)) hmem data.five_posDef).mpr
        data.added_pivot_lt_one
  rw [Finset.erase_insert data.added_notMem] at herase
  exact herase

/-- **THE RECURRENT TYPE-A ESCAPE.**  A recurrent pivot stall either already
yields a strict tree, or exposes a triangle-containing stall.

If the exchanged set contains a triangle, its recurrent stall is the witness.
If the original pointer window contains a triangle, that positive-definite
window either deletes to a strict tree or is itself the witness. -/
theorem KFourPivotWallRecurrentStallData.strictTree_or_exists_triangle_stall
    {point : DirectionChartPoint 6} {tree : Finset (Fin 6)}
    (htree : tree ∈ kFourSpanningTreeList)
    (hrecurrent : KFourPivotWallRecurrentStallData point tree) :
    (∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef)
      ∨ ∃ selected : Finset (Fin 6),
      selected.card = 4 ∧
      (directionChartGap kFourDirection point.mass point.weight
        selected).PosDef ∧
      (∀ label ∈ selected,
        1 ≤ chartLadderPivot kFourDirection point.mass point.weight
          selected label) ∧
        KFourContainsTriangle selected := by
  obtain ⟨exchange, hexchangeStall⟩ := hrecurrent
  have hshape := kFour_exchange_window_or_result_contains_triangle tree htree
    exchange.pointer exchange.pointer_notMem exchange.added exchange.added_notMem
      exchange.dropped exchange.dropped_mem
  rcases hshape with hwindowTriangle | hexchangeTriangle
  · have hwindowCard : (insert exchange.pointer tree).card = 4 := by
      rw [Finset.card_insert_of_notMem exchange.pointer_notMem,
        kFourSpanningTree_card tree htree]
    rcases exists_strictTree_or_cardFour_stall_of_posDef point hwindowCard
      exchange.window_posDef with hstrict | hwindowStall
    · exact Or.inl hstrict
    · exact Or.inr ⟨insert exchange.pointer tree, hwindowCard,
        exchange.window_posDef, hwindowStall, hwindowTriangle⟩
  · exact Or.inr ⟨(insert exchange.added (insert exchange.pointer tree)).erase
        exchange.dropped, exchange.exchange_card, exchange.exchange_posDef,
      hexchangeStall, hexchangeTriangle⟩

/-! ## Minimal closure targets and the A3 composition -/

/-- A global closure theorem for triangle-containing card-four stalls. -/
def KFourTriangleStallClosure : Prop :=
  ∀ (point : DirectionChartPoint 6) (selected : Finset (Fin 6)),
    selected.card = 4 →
    (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef →
    (∀ label ∈ selected,
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        selected label) →
    KFourContainsTriangle selected →
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef

/-- The weaker, exact closure target used by the pivot-wall consumer.  It keeps
all original wall data available to a proof of the triangle-stall case. -/
def KFourPivotWallTriangleStallClosure : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourSpanningTreeList →
    (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef →
    KFourTreeWindowData point tree →
    KFourTreeWindowAllPivotWallData point tree →
    ∀ selected : Finset (Fin 6),
      selected.card = 4 →
      (directionChartGap kFourDirection point.mass point.weight
        selected).PosDef →
      (∀ label ∈ selected,
        1 ≤ chartLadderPivot kFourDirection point.mass point.weight
          selected label) →
      KFourContainsTriangle selected →
      ∃ winner ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight winner).PosDef

/-- The object-level version of the contextual target.  Instead of returning a
tree, it returns exactly the non-stalled positive-definite four-set appearing
in `strictTree_iff_exists_nonStalledCardFour`.  This is the natural consumer for
a global stall-escape theorem. -/
def KFourPivotWallTriangleEscapeClosure : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourSpanningTreeList →
    (directionChartGap kFourDirection point.mass point.weight
      tree).PosSemidef →
    KFourTreeWindowData point tree →
    KFourTreeWindowAllPivotWallData point tree →
    ∀ selected : Finset (Fin 6),
      selected.card = 4 →
      (directionChartGap kFourDirection point.mass point.weight
        selected).PosDef →
      (∀ label ∈ selected,
        1 ≤ chartLadderPivot kFourDirection point.mass point.weight
          selected label) →
      KFourContainsTriangle selected →
      ∃ escaped : Finset (Fin 6), escaped.card = 4 ∧
        (directionChartGap kFourDirection point.mass point.weight
          escaped).PosDef ∧
        ∃ label ∈ escaped,
          chartLadderPivot kFourDirection point.mass point.weight
            escaped label < 1

/-- The global triangle-stall law implies the exact contextual target. -/
theorem kFourPivotWallTriangleStallClosure_of_triangleStallClosure
    (hclose : KFourTriangleStallClosure) :
    KFourPivotWallTriangleStallClosure := by
  intro point tree _htree _hgap _hwindow _hwall selected
  exact hclose point selected

/-- The object-level escape target implies the contextual strict-tree target by
the landed card-four equivalence. -/
theorem kFourPivotWallTriangleStallClosure_of_escapeClosure
    (hclose : KFourPivotWallTriangleEscapeClosure) :
    KFourPivotWallTriangleStallClosure := by
  intro point tree htree hgap hwindow hwall selected hcard hpd hstall htriangle
  exact (strictTree_iff_exists_nonStalledCardFour point).mpr
    (hclose point tree htree hgap hwindow hwall selected hcard hpd hstall
      htriangle)

/-- A contextual triangle-stall closure closes the entire recurrent arm.  No
independent matching-complement/type-A closure remains in that arm. -/
theorem kFourPivotWallRecurrentStallClosure_of_triangleStallClosure
    (hclose : KFourPivotWallTriangleStallClosure) :
    KFourPivotWallRecurrentStallClosure := by
  intro point tree htree hgap hwindow hwall hrecurrent
  rcases hrecurrent.strictTree_or_exists_triangle_stall htree with
    hstrict | ⟨selected, hcard, hpd, hstall, htriangle⟩
  · exact hstrict
  · exact hclose point tree htree hgap hwindow hwall selected hcard hpd hstall
      htriangle

/-- The two genuinely independent pivot inputs after both Codex reductions:
triangle stalls for the recurrent arm, and the classified priced-star endpoint. -/
def KFourPivotWallTriangleStarClosure : Prop :=
  KFourPivotWallTriangleStallClosure ∧
    KFourPivotWallPricedStarEndpointClosure

/-- Triangle-stall closure plus the star endpoint supplies the exact star
propagation package consumed by the pivot wall. -/
theorem kFourPivotWallStarPropagationClosure_of_triangleStarClosure
    (hclose : KFourPivotWallTriangleStarClosure) :
    KFourPivotWallStarPropagationClosure :=
  ⟨kFourPivotWallRecurrentStallClosure_of_triangleStallClosure hclose.1,
    hclose.2⟩

/-- The narrowed pair closes every four-pivot wall. -/
theorem kFourWindowAllPivotWallClosure_of_triangleStarClosure
    (hclose : KFourPivotWallTriangleStarClosure) :
    KFourWindowAllPivotWallClosure :=
  kFourWindowAllPivotWallClosure_iff_starPropagation.mpr
    (kFourPivotWallStarPropagationClosure_of_triangleStarClosure hclose)

/-- The final sufficient package for A3 after removing recurrent type A. -/
def KFourGaugeTriangleStarClosure : Prop :=
  KFourPivotWallTriangleStarClosure ∧ KFourGaugeStarCorankWallClosure

/-- The gauge wall, contextual triangle stalls, and the classified star endpoint
discharge the public K4 knife-band statement. -/
theorem kFourKnifeBandRefined_of_gaugeTriangleStarClosure
    (hclose : KFourGaugeTriangleStarClosure) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_gaugeAndPivot
    ⟨kFourWindowAllPivotWallClosure_of_triangleStarClosure hclose.1, hclose.2⟩

/-- The same package reaches the design-side family selector consumed by the
registry. -/
theorem kFourFamilySelection_of_gaugeTriangleStarClosure
    (hclose : KFourGaugeTriangleStarClosure) : KFourFamilySelection :=
  kFourFamilySelection_of_gaugeAndPivot
    ⟨kFourWindowAllPivotWallClosure_of_triangleStarClosure hclose.1, hclose.2⟩

/-- Explicit three-argument form for independent producers. -/
theorem kFourFamilySelection_of_triangleStall_starEndpoint_gauge
    (htriangle : KFourPivotWallTriangleStallClosure)
    (hendpoint : KFourPivotWallPricedStarEndpointClosure)
    (hgauge : KFourGaugeStarCorankWallClosure) : KFourFamilySelection :=
  kFourFamilySelection_of_gaugeTriangleStarClosure
    ⟨⟨htriangle, hendpoint⟩, hgauge⟩

/-- Flip-ready form for the unified stall-escape plan: an object-level escape
at triangle stalls, the classified endpoint, and the gauge wall suffice for the
K4 family selector. -/
theorem kFourFamilySelection_of_triangleEscape_starEndpoint_gauge
    (htriangle : KFourPivotWallTriangleEscapeClosure)
    (hendpoint : KFourPivotWallPricedStarEndpointClosure)
    (hgauge : KFourGaugeStarCorankWallClosure) : KFourFamilySelection :=
  kFourFamilySelection_of_triangleStall_starEndpoint_gauge
    (kFourPivotWallTriangleStallClosure_of_escapeClosure htriangle) hendpoint
      hgauge

end Gtz
