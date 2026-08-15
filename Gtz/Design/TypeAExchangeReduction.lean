/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.TypeAExchangeObstruction
import Gtz.Design.CardFourStallEquivalence

/-!
# The type-A exchange reduction

A card-four selection of the `K4` chart is **type A** when its complement is one
of the three perfect matchings `{0, 5}`, `{1, 4}`, `{2, 3}`.  A one-label
exchange out of such a selection always lands on a selection containing a
triangle, by `Gtz.kFourMatchingCompl_exchange_containsTriangle`.

This module turns that combinatorial fact into a reduction.  Give a type-A stall
one positive definite exchange and the type-A case is finished: either the
exchange drops to a strict spanning tree, or the exchange is itself a stall, and
it contains a triangle, so the triangle-stall closure receives it.

The reduction consumes no wall data and no chart geometry.  It is stated for an
arbitrary chart point.

## The status of the exchange hypothesis

The hypothesis "some one-label exchange is positive definite" is **false both
in general and on the canonical gauge wall**.  The reduction below remains a
valid conditional theorem, but the named wall hypothesis is retained only as a
compatibility boundary.  The exact gauge-wall refutation is mechanized in
`Gtz.Design.GaugeWallTypeAExchangeRefutation`.

The historical measurements were:

* On the general chart a probe found 2610 type-A stalls at which no one-label
  exchange is positive definite.  One witness, in the weights
  `(18, 9, 30, 16, 15, 16) / 104` and the masses
  `(5/7, 3/4, 9/2, 9/2, 1, 12/11)`, has the type-A stall `{0, 1, 4, 5}` with all
  eight exchanges failing.  This is why
  `Gtz.kFourMatchingCompl_exchange_not_compl_subset` records an obstruction.
* On the canonical gauge wall, a probe over 2132430 sampled type-A stalls found
  an exchange at every sampled point.  That empirical statement missed a thin
  exact stratum.  The refuter has the complete corank-two wall package, a
  positive-definite stalled four-cycle, and all eight adjacent exchanges
  non-positive-definite.  It nevertheless has two nonlocal strict spanning
  trees, so it refutes the exchange route rather than the K4 conclusion.

The wall hypothesis is therefore named here as `Gtz.KFourGaugeWallTypeAExchange`
for compatibility with the conditional reduction.  It is inconsistent, and
nothing in this module assumes it.
-/

namespace Gtz

/-! ## A one-label exchange keeps card four -/

/-- A one-label exchange out of a card-four selection has card four. -/
theorem kFourExchange_card (selected : Finset (Fin 6)) (hcard : selected.card = 4)
    (leaving : Fin 6) (hleaving : leaving ∈ selected)
    (entering : Fin 6) (hentering : entering ∉ selected) :
    (insert entering (selected.erase leaving)).card = 4 := by
  have hnotMem : entering ∉ selected.erase leaving := fun hmem =>
    hentering (Finset.mem_of_mem_erase hmem)
  rw [Finset.card_insert_of_notMem hnotMem,
    Finset.card_erase_of_mem hleaving, hcard]

/-! ## The reduction -/

/-- **THE TYPE-A EXCHANGE REDUCTION.**  One positive definite exchange finishes
the type-A case.

Either the exchange is not a stall, and the landed card-four descent drops it to
a strict spanning tree, or the exchange is a stall.  In the second branch the
exchange contains a triangle, because an exchange out of a four-cycle is never a
four-cycle, so it is exactly the input a triangle-stall closure consumes.

No wall data and no geometry enter.  The only hypothesis beyond the type-A shape
is that one exchange is positive definite. -/
theorem kFourTypeAStall_tree_or_triangleStall (point : DirectionChartPoint 6)
    (selected : Finset (Fin 6)) (hcard : selected.card = 4)
    (hmatching : selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3})
    (leaving : Fin 6) (hleaving : leaving ∈ selected)
    (entering : Fin 6) (hentering : entering ∉ selected)
    (hexchange : (directionChartGap kFourDirection point.mass point.weight
      (insert entering (selected.erase leaving))).PosDef) :
    (∃ winner ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight winner).PosDef)
      ∨ (∃ other : Finset (Fin 6), other.card = 4
          ∧ (directionChartGap kFourDirection point.mass point.weight
              other).PosDef
          ∧ (∀ label ∈ other, 1 ≤ chartLadderPivot kFourDirection point.mass
              point.weight other label)
          ∧ ({0, 1, 2} ⊆ other ∨ {0, 3, 4} ⊆ other ∨ {1, 3, 5} ⊆ other
              ∨ {2, 4, 5} ⊆ other)) := by
  have hcardExchange := kFourExchange_card selected hcard leaving hleaving
    entering hentering
  by_cases hstall : ∀ label ∈ insert entering (selected.erase leaving),
      1 ≤ chartLadderPivot kFourDirection point.mass point.weight
        (insert entering (selected.erase leaving)) label
  · exact Or.inr ⟨insert entering (selected.erase leaving), hcardExchange,
      hexchange, hstall,
      kFourMatchingCompl_exchange_containsTriangle selected hcard hmatching
        leaving hleaving entering hentering⟩
  · push Not at hstall
    obtain ⟨label, hmem, hlt⟩ := hstall
    exact Or.inl (exists_strictTree_of_nonStalledCardFour point hcardExchange
      hexchange hmem hlt)

/-- The reduction in consumable form: with a triangle-stall closure available, a
positive definite exchange out of a type-A stall produces a strict spanning
tree. -/
theorem kFourTypeAStall_tree_of_exchange_of_triangleClosure
    (hclose : ∀ (point : DirectionChartPoint 6) (other : Finset (Fin 6)),
      other.card = 4 →
      (directionChartGap kFourDirection point.mass point.weight other).PosDef →
      (∀ label ∈ other, 1 ≤ chartLadderPivot kFourDirection point.mass
        point.weight other label) →
      ({0, 1, 2} ⊆ other ∨ {0, 3, 4} ⊆ other ∨ {1, 3, 5} ⊆ other
        ∨ {2, 4, 5} ⊆ other) →
      ∃ winner ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight winner).PosDef)
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hcard : selected.card = 4)
    (hmatching : selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3})
    (leaving : Fin 6) (hleaving : leaving ∈ selected)
    (entering : Fin 6) (hentering : entering ∉ selected)
    (hexchange : (directionChartGap kFourDirection point.mass point.weight
      (insert entering (selected.erase leaving))).PosDef) :
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef := by
  rcases kFourTypeAStall_tree_or_triangleStall point selected hcard hmatching
    leaving hleaving entering hentering hexchange with
    htree | ⟨other, hcardOther, hpdOther, hstallOther, htriangleOther⟩
  · exact htree
  · exact hclose point other hcardOther hpdOther hstallOther htriangleOther

/-! ## The named gauge-wall hypothesis -/

/-- **THE OBSOLETE GAUGE-WALL TYPE-A EXCHANGE.**  At a type-A stall on the
canonical gauge wall some one-label exchange is positive definite.

This statement is false.  `Gtz.not_kFourGaugeWallTypeAExchange` gives an exact
rational refutation satisfying the full wall antecedent.  The proposition stays
named because the conditional exchange reduction remains useful and existing
consumers can be mapped into the repaired nonlocal interface. -/
def KFourGaugeWallTypeAExchange : Prop :=
  ∀ (point : DirectionChartPoint 6) (selected : Finset (Fin 6)),
    selected.card = 4 →
    (selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3}) →
    KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)) →
    (directionChartGap kFourDirection point.mass point.weight selected).PosDef →
    (∀ label ∈ selected, 1 ≤ chartLadderPivot kFourDirection point.mass
      point.weight selected label) →
    ∃ leaving ∈ selected, ∃ entering, entering ∉ selected ∧
      (directionChartGap kFourDirection point.mass point.weight
        (insert entering (selected.erase leaving))).PosDef

/-- **THE TYPE-A BRANCH OF THE GAUGE WALL.**  The gauge-wall exchange hypothesis
and a triangle-stall closure together discharge every type-A stall on the
wall. -/
theorem kFourGaugeWallTypeAStall_tree_of_exchange_of_triangleClosure
    (hexchange : KFourGaugeWallTypeAExchange)
    (hclose : ∀ (point : DirectionChartPoint 6) (other : Finset (Fin 6)),
      other.card = 4 →
      (directionChartGap kFourDirection point.mass point.weight other).PosDef →
      (∀ label ∈ other, 1 ≤ chartLadderPivot kFourDirection point.mass
        point.weight other label) →
      ({0, 1, 2} ⊆ other ∨ {0, 3, 4} ⊆ other ∨ {1, 3, 5} ⊆ other
        ∨ {2, 4, 5} ⊆ other) →
      ∃ winner ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight winner).PosDef)
    (point : DirectionChartPoint 6) (selected : Finset (Fin 6))
    (hcard : selected.card = 4)
    (hmatching : selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3})
    (hcorank : KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)))
    (hpd : (directionChartGap kFourDirection point.mass point.weight
      selected).PosDef)
    (hstall : ∀ label ∈ selected, 1 ≤ chartLadderPivot kFourDirection point.mass
      point.weight selected label) :
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef := by
  obtain ⟨leaving, hleaving, entering, hentering, hpdExchange⟩ :=
    hexchange point selected hcard hmatching hcorank hpd hstall
  exact kFourTypeAStall_tree_of_exchange_of_triangleClosure hclose point selected
    hcard hmatching leaving hleaving entering hentering hpdExchange

end Gtz
