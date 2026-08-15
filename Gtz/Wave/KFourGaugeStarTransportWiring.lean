import Gtz.Design.PivotWallVacuity
import Gtz.Design.StarWallTransport

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1600000

/-!
# Reduce the four K4 star walls to one gauge wall

The live A3 residual has two genuinely different terminal branches:

* a positive-definite window whose four deletion pivots are all at least one;
* a corank-two vertex-star gap.

`StarWallTransport` proves that the four vertex stars form one orbit under an
exact chart congruence, but its reduction theorem had no named proposition and
did not feed the live A3 consumer.  This module supplies that wiring.

The result is deliberately a sufficient route, not a claimed reformulation of
the registry.  A proof of the canonical gauge-star wall and a proof of the
four-pivot wall together discharge A3.  Conversely, the all-star wall law is
exactly equivalent to the gauge-star law, because the gauge tree itself is one
of the four stars.
-/

namespace Gtz

open Matrix

/-! ## Atlas firing at one canonical star -/

/-- Atlas firing only at the canonical gauge-star corank-two wall.  This is
strictly cheaper than `KFourStarWallAtlasFires`: no statement about the atlas
predicate at the other three, differently gauged chart points is required. -/
def KFourGaugeStarWallAtlasFires : Prop :=
  ∀ point : DirectionChartPoint 6,
    (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef →
    KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)) →
    KFourAllTreeMinorAtlasCellFires point

/-! ## One canonical star wall versus all four -/

/-- Strict-tree closure of the canonical gauge-star corank-two wall. -/
def KFourGaugeStarCorankWallClosure : Prop :=
  ∀ point : DirectionChartPoint 6,
    (directionChartGap kFourDirection point.mass point.weight
      ({3, 4, 5} : Finset (Fin 6))).PosSemidef →
    KFourTreeGapCorankTwoData point ({3, 4, 5} : Finset (Fin 6)) →
    ∃ tree ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight tree).PosDef

/-- Strict-tree closure of every vertex-star corank-two wall. -/
def KFourAllStarCorankWallClosure : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourStarList →
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef →
    KFourTreeGapCorankTwoData point tree →
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef

/-- The exact four-cycle transport turns one gauge-wall proof into all four
star-wall proofs. -/
theorem kFourAllStarCorankWallClosure_of_gauge
    (hgauge : KFourGaugeStarCorankWallClosure) :
    KFourAllStarCorankWallClosure := by
  intro point tree hstar hpsd hcorank
  exact kFourStarWall_strictTree_of_gauge hgauge point tree hstar hpsd hcorank

/-- The all-star law contains the gauge star as one of its four cases. -/
theorem kFourGaugeStarCorankWallClosure_of_all
    (hall : KFourAllStarCorankWallClosure) :
    KFourGaugeStarCorankWallClosure := by
  intro point hpsd hcorank
  exact hall point ({3, 4, 5} : Finset (Fin 6)) (by decide) hpsd hcorank

/-- **THE STAR-ORBIT IDENTIFICATION.**  The four corank-two star walls are one
canonical gauge-wall problem, with no loss in either direction. -/
theorem kFourAllStarCorankWallClosure_iff_gauge :
    KFourAllStarCorankWallClosure ↔ KFourGaugeStarCorankWallClosure :=
  ⟨kFourGaugeStarCorankWallClosure_of_all,
    kFourAllStarCorankWallClosure_of_gauge⟩

/-- Firing the atlas at the canonical wall gives a strict tree there. -/
theorem kFourGaugeStarCorankWallClosure_of_atlasFires
    (hfire : KFourGaugeStarWallAtlasFires) :
    KFourGaugeStarCorankWallClosure := by
  intro point hpsd hcorank
  exact kFourAtlas_hasStrictTree_of_allTreeMinorAtlasCell point
    (hfire point hpsd hcorank)

/-- **THE GAUGE-ONLY ATLAS REDUCTION.**  Atlas firing needs to be proved only
at the gauge wall.  The atlas dispatcher supplies a strict gauge-tree witness,
and exact congruence transports that witness to every other star wall. -/
theorem kFourAllStarCorankWallClosure_of_gaugeAtlasFires
    (hfire : KFourGaugeStarWallAtlasFires) :
    KFourAllStarCorankWallClosure :=
  kFourAllStarCorankWallClosure_of_gauge
    (kFourGaugeStarCorankWallClosure_of_atlasFires hfire)

/-! ## The other terminal wall -/

/-- Closure of the four-pivot window wall.  The statement retains the selected
tree, its weak gap, and the complete window data so downstream proofs can use
the exact final-rung identities rather than a weakened numerical summary. -/
def KFourWindowAllPivotWallClosure : Prop :=
  ∀ (point : DirectionChartPoint 6) (tree : Finset (Fin 6)),
    tree ∈ kFourSpanningTreeList →
    (directionChartGap kFourDirection point.mass point.weight tree).PosSemidef →
    KFourTreeWindowData point tree →
    KFourTreeWindowAllPivotWallData point tree →
    ∃ winner ∈ kFourSpanningTreeList,
      (directionChartGap kFourDirection point.mass point.weight winner).PosDef

/-- The two independent closure obligations at the end of the current K4
reduction: one window wall and one canonical star wall. -/
def KFourGaugeAndPivotWallClosure : Prop :=
  KFourWindowAllPivotWallClosure ∧ KFourGaugeStarCorankWallClosure

/-- The two atlas-vacuity targets in their minimal useful form: the canonical
gauge star only, plus the independent four-pivot wall. -/
def KFourGaugeStarAndPivotWallAtlasFires : Prop :=
  KFourGaugeStarWallAtlasFires ∧ KFourPivotWallAtlasFires

/-- The landed pivot atlas target supplies the strict-tree closure needed by
the component decomposition. -/
theorem kFourWindowAllPivotWallClosure_of_atlasFires
    (hfire : KFourPivotWallAtlasFires) :
    KFourWindowAllPivotWallClosure := by
  intro point tree htree hpsd hwindow hpivot
  exact kFourAtlas_hasStrictTree_of_allTreeMinorAtlasCell point
    (hfire point tree htree hpsd hwindow hpivot)

/-- Gauge-star atlas firing and pivot-wall atlas firing produce the two direct
strict-tree closure laws. -/
theorem kFourGaugeAndPivotWallClosure_of_atlasFires
    (hfire : KFourGaugeStarAndPivotWallAtlasFires) :
    KFourGaugeAndPivotWallClosure :=
  ⟨kFourWindowAllPivotWallClosure_of_atlasFires hfire.2,
    kFourGaugeStarCorankWallClosure_of_atlasFires hfire.1⟩

/-! ## Consume the two closures in A3 -/

/-- Gauge-star closure handles every star branch by transport; four-pivot
closure handles the other branch.  All atlas, ledger, refusal, and heavy-axis
data in the live residual remain available but are no longer needed by this
particular sufficient route. -/
theorem kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_of_gaugeAndPivot
    (hclose : KFourGaugeAndPivotWallClosure) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict := by
  intro point _hnotLayerA _hnotExchange _hnotAtlas _hledger hwitness
  obtain ⟨tree, htree, hpsd, hwindow, hpivot | hstar⟩ := hwitness
  · exact hclose.1 point tree htree hpsd hwindow hpivot
  · exact kFourStarWall_strictTree_of_gauge hclose.2 point tree
      hstar.1.1.1.1 hpsd hstar.1.1.1.2.1

/-- The two terminal wall closures discharge the public refined K4 chart
selection statement. -/
theorem kFourKnifeBandRefined_of_gaugeAndPivot
    (hclose : KFourGaugeAndPivotWallClosure) :
    KFourKnifeBandRefinedWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_iff.mp
    (kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_of_gaugeAndPivot hclose)

/-- The same component pair reaches the design-side K4 family selector. -/
theorem kFourFamilySelection_of_gaugeAndPivot
    (hclose : KFourGaugeAndPivotWallClosure) : KFourFamilySelection :=
  kFourFamilySelection_iff_treeStarRefusedAllMaxHeavyWall.mpr
    (kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_of_gaugeAndPivot hclose)

/-- Equivalently, the component pair gives a strict K4 spanning tree at every
chart point. -/
theorem kFourEveryPointHasStrictTree_of_gaugeAndPivot
    (hclose : KFourGaugeAndPivotWallClosure) : KFourEveryPointHasStrictTree :=
  kFourFamilySelection_iff_everyPointHasStrictTree.mp
    (kFourFamilySelection_of_gaugeAndPivot hclose)

/-! ## The minimal two-atlas route to A3 -/

/-- The canonical gauge-star atlas law and the pivot-wall atlas law discharge
the live tied-axis A3 formula.  No relabeling law for the atlas predicate is
used or needed. -/
theorem kFourKnifeBandRefinedAllMaxHeavy_of_gaugeStarAndPivotAtlasFires
    (hfire : KFourGaugeStarAndPivotWallAtlasFires) :
    KFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWallWeakToStrict :=
  kFourKnifeBandRefinedTreeStarRefusedAllMaxHeavyWall_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_atlasFires hfire)

/-- The minimal two-atlas route reaches the design-side family selector. -/
theorem kFourFamilySelection_of_gaugeStarAndPivotAtlasFires
    (hfire : KFourGaugeStarAndPivotWallAtlasFires) : KFourFamilySelection :=
  kFourFamilySelection_of_gaugeAndPivot
    (kFourGaugeAndPivotWallClosure_of_atlasFires hfire)

end Gtz
