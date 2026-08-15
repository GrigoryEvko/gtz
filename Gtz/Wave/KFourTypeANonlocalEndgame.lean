/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.GaugeWallTypeAExchangeRefutation
import Gtz.Wave.KFourTriangleEndgame

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# Repair the K4 endgame after the type-A exchange refutation

The former two-input endgame asked for one positive-definite exchange adjacent
to every type-A stall on the canonical gauge wall.  The exact fixture in
`Gtz.Design.GaugeWallTypeAExchangeRefutation` proves that request false under
its complete hypotheses, while exhibiting strict trees elsewhere at the same
point.

The correct producer is therefore nonlocal.  `KFourGaugeWallTypeAStallClosure`
retains every piece of wall and stall data but asks directly for the strict
spanning tree consumed by A3.  Together with the independent global
triangle-stall closure it is neither a hidden exchange statement nor the whole
K4 theorem:

* descent restricts it to the canonical corank-two gauge wall;
* the type split restricts it to matching-complement four-cycles;
* triangle stalls remain a separate producer shared with the pivot wall.

This module proves all composition directions, supplies the compatibility map
from the old interface, and records in the kernel that the old endgame
proposition is false.
-/

namespace Gtz

/-! ## 1. The honest type-A wall producer -/

/-- **THE NONLOCAL TYPE-A WALL CLOSURE.**  At a canonical gauge-wall point, a
stalled positive-definite four-cycle produces some strict K4 spanning tree.

The positive-semidefinite wall gap and full corank package are retained.  The
conclusion is deliberately nonlocal: the exact refuter proves that no adjacent
exchange need be positive definite. -/
def KFourGaugeWallTypeAStallClosure : Prop :=
  ∀ (point : DirectionChartPoint 6),
    (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef →
    KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)) →
    ∀ selected : Finset (Fin 6),
      selected.card = 4 →
      (selectedᶜ = {0, 5} ∨ selectedᶜ = {1, 4} ∨ selectedᶜ = {2, 3}) →
      (directionChartGap kFourDirection point.mass point.weight
        selected).PosDef →
      (∀ label ∈ selected,
        1 ≤ chartLadderPivot kFourDirection point.mass point.weight
          selected label) →
      ∃ winner ∈ kFourSpanningTreeList,
        (directionChartGap kFourDirection point.mass point.weight
          winner).PosDef

/-- A closed gauge wall trivially closes its type-A stalls. -/
theorem kFourGaugeWallTypeAStallClosure_of_gaugeStarClosure
    (hgauge : KFourGaugeStarCorankWallClosure) :
    KFourGaugeWallTypeAStallClosure := by
  intro point hpsd hcorank _selected _hcard _hmatching _hpd _hstall
  exact hgauge point hpsd hcorank

/-- The former exchange producer plus triangle-stall closure implies the new
nonlocal producer.  This theorem preserves source compatibility for any
stronger future hypothesis, despite the exact refutation of the named global
exchange proposition. -/
theorem kFourGaugeWallTypeAStallClosure_of_exchange_of_triangleClosure
    (hexchange : KFourGaugeWallTypeAExchange)
    (htriangle : KFourTriangleStallClosure) :
    KFourGaugeWallTypeAStallClosure := by
  intro point _hpsd hcorank selected hcard hmatching hpd hstall
  exact kFourGaugeWallTypeAStall_tree_of_exchange_of_triangleClosure
    hexchange htriangle point selected hcard hmatching hcorank hpd hstall

/-! ## 2. Exact gauge-wall composition -/

/-- Triangle stalls and the nonlocal type-A producer close the canonical gauge
wall.  The landed card-four descent and type split are the only intermediate
steps. -/
theorem kFourGaugeStarCorankWallClosure_of_triangleStallClosure_of_typeAStallClosure
    (htriangle : KFourTriangleStallClosure)
    (htypeA : KFourGaugeWallTypeAStallClosure) :
    KFourGaugeStarCorankWallClosure := by
  intro point hpsd hcorank
  rcases kFour_strictTree_or_cardFour_stall point with
    hstrict | ⟨selected, hcard, hpd, hstall⟩
  · exact hstrict
  · rcases kFourCardFour_matchingCompl_or_triangle selected hcard with
      hmatching | htriangleShape
    · exact htypeA point hpsd hcorank selected hcard hmatching hpd hstall
    · exact htriangle point selected hcard hpd hstall htriangleShape

/-- With triangle stalls fixed, the canonical gauge wall is exactly its
matching-complement branch.  This is the sharp replacement for the false
exchange-based reduction. -/
theorem kFourGaugeStarCorankWallClosure_iff_typeAStallClosure
    (htriangle : KFourTriangleStallClosure) :
    KFourGaugeStarCorankWallClosure ↔ KFourGaugeWallTypeAStallClosure :=
  ⟨kFourGaugeWallTypeAStallClosure_of_gaugeStarClosure,
    kFourGaugeStarCorankWallClosure_of_triangleStallClosure_of_typeAStallClosure
      htriangle⟩

/-! ## 3. The repaired two-input endgame -/

/-- The exact surviving pair of mathematical producers: global triangle-stall
closure and nonlocal type-A closure on the canonical gauge wall. -/
def KFourNonlocalTypeAEndgameClosure : Prop :=
  KFourTriangleStallClosure ∧ KFourGaugeWallTypeAStallClosure

/-- The repaired endgame closes the pivot wall through the triangle producer
and the gauge wall through the type split. -/
theorem kFourGaugeAndPivotWallClosure_of_nonlocalTypeAEndgame
    (hclose : KFourNonlocalTypeAEndgameClosure) :
    KFourGaugeAndPivotWallClosure :=
  ⟨kFourWindowAllPivotWallClosure_of_triangleStallClosure
      (kFourPivotWallTriangleStallClosure_of_triangleStallClosure hclose.1),
    kFourGaugeStarCorankWallClosure_of_triangleStallClosure_of_typeAStallClosure
      hclose.1 hclose.2⟩

/-- The repaired endgame discharges the public refined K4 knife band. -/
theorem kFourKnifeBandRefined_of_nonlocalTypeAEndgame
    (hclose : KFourNonlocalTypeAEndgameClosure) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_nonlocalTypeAEndgame hclose)

/-- The repaired endgame reaches the design-side selector consumed by the
registry. -/
theorem kFourFamilySelection_of_nonlocalTypeAEndgame
    (hclose : KFourNonlocalTypeAEndgameClosure) : KFourFamilySelection :=
  kFourFamilySelection_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_nonlocalTypeAEndgame hclose)

/-- The same pair gives a strict spanning tree at every K4 chart point. -/
theorem kFourEveryPointHasStrictTree_of_nonlocalTypeAEndgame
    (hclose : KFourNonlocalTypeAEndgameClosure) : KFourEveryPointHasStrictTree :=
  kFourEveryPointHasStrictTree_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_nonlocalTypeAEndgame hclose)

/-! ## 4. Compatibility and the false old route -/

/-- The former endgame proposition implies the repaired one.  This implication
is useful for compatibility only: the next theorem proves the former
proposition false. -/
theorem kFourNonlocalTypeAEndgameClosure_of_triangleEndgame
    (hclose : KFourTriangleEndgameClosure) :
    KFourNonlocalTypeAEndgameClosure :=
  ⟨hclose.1,
    kFourGaugeWallTypeAStallClosure_of_exchange_of_triangleClosure
      hclose.2 hclose.1⟩

/-- The old two-input endgame is uninhabited because its exchange component is
false.  This prevents a future consumer from mistaking the obsolete sufficient
route for a plausible open target. -/
theorem not_kFourTriangleEndgameClosure : ¬ KFourTriangleEndgameClosure := by
  intro hclose
  exact not_kFourGaugeWallTypeAExchange hclose.2

/-- The exact fixture inhabits the new type-A conclusion while refuting the old
local mechanism: it has a strict tree, but no adjacent exchange of its stalled
four-cycle is positive definite. -/
theorem gaugeTypeAExchangeRefuter_nonlocal_separation :
    (∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
        gaugeTypeAExchangeRefuterPoint.weight winner).PosDef) ∧
    (∀ leaving ∈ gaugeTypeAExchangeRefuterSelection, ∀ entering : Fin 6,
      entering ∉ gaugeTypeAExchangeRefuterSelection →
      ¬ (directionChartGap kFourDirection gaugeTypeAExchangeRefuterPoint.mass
        gaugeTypeAExchangeRefuterPoint.weight
          (insert entering
            (gaugeTypeAExchangeRefuterSelection.erase leaving))).PosDef) :=
  ⟨gaugeTypeAExchangeRefuter_hasStrictTree,
    gaugeTypeAExchangeRefuter_no_posDef_exchange⟩

end Gtz
