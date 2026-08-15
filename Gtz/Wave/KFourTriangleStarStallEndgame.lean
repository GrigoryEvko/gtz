/-
Copyright (c) 2026 Grigory Evko. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Gtz.Design.GaugeWallTriangleStarDescent
import Gtz.Wave.KFourPivotTriangleClosure

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The exact triangle-star stall endgame for K4

The two terminal A3 walls now admit exact residual formulations.

* The four-pivot wall is equivalent to its contextual triangle-containing
  card-four stalls.
* The canonical gauge wall is equivalent to the nine stalled positive-definite
  card-four selections whose complements contain one triangle label and one
  star label.

This module packages precisely those two propositions.  It contains no atlas
cover, no local exchange hypothesis, and no arbitrary card-four case split.
The main equivalence identifies the package with the existing gauge-plus-pivot
wall closure, after which the public knife-band, family-selection, and
every-point consumers are immediate.
-/

namespace Gtz

/-- **THE EXACT TWO-WALL ENDGAME.**  The pivot wall consumes only contextual
triangle stalls; the gauge wall consumes only its nine triangle-star
complementary stalls. -/
def KFourTriangleStarStallEndgameClosure : Prop :=
  KFourPivotWallTriangleStallClosure ∧
    KFourGaugeWallTriangleStarStallClosure

/-- The exact residual package produces both terminal wall closures. -/
theorem kFourGaugeAndPivotWallClosure_of_triangleStarStallEndgame
    (hclose : KFourTriangleStarStallEndgameClosure) :
    KFourGaugeAndPivotWallClosure :=
  ⟨kFourWindowAllPivotWallClosure_of_triangleStallClosure hclose.1,
    kFourGaugeStarCorankWallClosure_of_triangleStarStallClosure hclose.2⟩

/-- Conversely, the two closed walls supply their exact residual statements.
This direction is useful for keeping the replacement logically honest: the
new package is not stronger than the old terminal target. -/
theorem kFourTriangleStarStallEndgameClosure_of_gaugeAndPivotWallClosure
    (hclose : KFourGaugeAndPivotWallClosure) :
    KFourTriangleStarStallEndgameClosure :=
  ⟨kFourPivotWallTriangleStallClosure_of_windowAllPivotWallClosure hclose.1,
    kFourGaugeWallTriangleStarStallClosure_of_gaugeStarCorankWallClosure
      hclose.2⟩

/-- **THE TERMINAL-WALL IDENTIFICATION.**  Closing the two A3 walls is exactly
closing the contextual pivot triangle stalls and the nine gauge triangle-star
stalls. -/
theorem kFourGaugeAndPivotWallClosure_iff_triangleStarStallEndgame :
    KFourGaugeAndPivotWallClosure ↔ KFourTriangleStarStallEndgameClosure :=
  ⟨kFourTriangleStarStallEndgameClosure_of_gaugeAndPivotWallClosure,
    kFourGaugeAndPivotWallClosure_of_triangleStarStallEndgame⟩

/-- The exact package is also the sharpened form of the previously landed
`KFourGaugeTriangleClosure`: its second component has been reduced from the
whole gauge wall to the nine shaped stalls. -/
theorem kFourGaugeTriangleClosure_iff_triangleStarStallEndgame :
    KFourGaugeTriangleClosure ↔ KFourTriangleStarStallEndgameClosure := by
  rw [KFourGaugeTriangleClosure, KFourTriangleStarStallEndgameClosure,
    kFourGaugeStarCorankWallClosure_iff_triangleStarStallClosure]

/-! ## Public A3 consumers -/

/-- The exact two-wall residual discharges the public refined K4 knife band. -/
theorem kFourKnifeBandRefined_of_triangleStarStallEndgame
    (hclose : KFourTriangleStarStallEndgameClosure) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefined_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_triangleStarStallEndgame hclose)

/-- The exact two-wall residual reaches the design-side family selector
consumed by the rank-three registry. -/
theorem kFourFamilySelection_of_triangleStarStallEndgame
    (hclose : KFourTriangleStarStallEndgameClosure) : KFourFamilySelection :=
  kFourFamilySelection_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_triangleStarStallEndgame hclose)

/-- The same residual gives a strict spanning tree at every K4 chart point. -/
theorem kFourEveryPointHasStrictTree_of_triangleStarStallEndgame
    (hclose : KFourTriangleStarStallEndgameClosure) :
    KFourEveryPointHasStrictTree :=
  kFourEveryPointHasStrictTree_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_triangleStarStallEndgame hclose)

/-- Explicit producer form for lanes that prove the pivot and gauge residuals
independently. -/
theorem kFourFamilySelection_of_pivotTriangle_of_gaugeTriangleStarStall
    (hpivot : KFourPivotWallTriangleStallClosure)
    (hgauge : KFourGaugeWallTriangleStarStallClosure) :
    KFourFamilySelection :=
  kFourFamilySelection_of_triangleStarStallEndgame ⟨hpivot, hgauge⟩

end Gtz
