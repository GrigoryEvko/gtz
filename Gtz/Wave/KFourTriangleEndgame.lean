import Gtz.Wave.KFourPivotTriangleClosure
import Gtz.Design.TypeAExchangeReduction

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The obsolete exchange-based K4 triangle endgame

This module records the original two-input composition:

1. a global closure theorem for triangle-containing card-four stalls; and
2. one positive exchange from every type-A stall on the canonical gauge wall.

The first input closes the pivot wall outright.  On the gauge wall, the landed
card-four type split is exhaustive.  A type-B stall is already a triangle
stall.  A type-A stall uses the second input once; the exchange either descends
to a strict tree or becomes a triangle stall, by the landed type-A reduction.

The second producer is false, by the exact rational gauge-wall point in
`Gtz.Design.GaugeWallTypeAExchangeRefutation`.  Consequently this file is now a
compatibility layer, not a viable endgame.  The repaired composition is
`Gtz.Wave.KFourTypeANonlocalEndgame`: it replaces the adjacent-exchange claim by
a direct nonlocal type-A wall closure and retains maps from every theorem below.
-/

namespace Gtz

/-- **THE GAUGE WALL FROM THE TWO RESIDUAL PRODUCERS.**  Global triangle-stall
closure and the gauge-wall type-A exchange close the canonical corank-two star
wall. -/
theorem kFourGaugeStarCorankWallClosure_of_triangleStallClosure_of_typeAExchange
    (htriangle : KFourTriangleStallClosure)
    (htypeA : KFourGaugeWallTypeAExchange) :
    KFourGaugeStarCorankWallClosure := by
  intro point _hpsd hcorank
  rcases kFour_strictTree_or_cardFour_stall point with
    hstrict | ⟨selected, hcard, hpd, hstall⟩
  · exact hstrict
  · rcases kFourCardFour_matchingCompl_or_triangle selected hcard with
      hmatching | hcontains
    · obtain ⟨leaving, hleaving, entering, hentering, hexchange⟩ :=
        htypeA point selected hcard hmatching hcorank hpd hstall
      exact kFourTypeAStall_tree_of_exchange_of_triangleClosure htriangle point
        selected hcard hmatching leaving hleaving entering hentering hexchange
    · exact htriangle point selected hcard hpd hstall hcontains

/-- The obsolete pair of residual statements.  Its second conjunct is false;
the definition is retained to preserve the old conditional API. -/
def KFourTriangleEndgameClosure : Prop :=
  KFourTriangleStallClosure ∧ KFourGaugeWallTypeAExchange

/-- The triangle endgame pair closes both terminal A3 walls. -/
theorem kFourGaugeAndPivotWallClosure_of_triangleEndgame
    (hclose : KFourTriangleEndgameClosure) :
    KFourGaugeAndPivotWallClosure :=
  ⟨kFourWindowAllPivotWallClosure_of_triangleStallClosure
      (kFourPivotWallTriangleStallClosure_of_triangleStallClosure hclose.1),
    kFourGaugeStarCorankWallClosure_of_triangleStallClosure_of_typeAExchange
      hclose.1 hclose.2⟩

/-- The two residual producers discharge the public refined K4 knife band. -/
theorem kFourKnifeBandRefined_of_triangleEndgame
    (hclose : KFourTriangleEndgameClosure) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_triangleEndgame hclose)

/-- The two residual producers discharge the design-side selector consumed by
the registry. -/
theorem kFourFamilySelection_of_triangleEndgame
    (hclose : KFourTriangleEndgameClosure) : KFourFamilySelection :=
  kFourFamilySelection_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_triangleEndgame hclose)

/-- The same pair gives a strict spanning tree at every K4 chart point. -/
theorem kFourEveryPointHasStrictTree_of_triangleEndgame
    (hclose : KFourTriangleEndgameClosure) : KFourEveryPointHasStrictTree :=
  kFourEveryPointHasStrictTree_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_triangleEndgame hclose)

end Gtz
