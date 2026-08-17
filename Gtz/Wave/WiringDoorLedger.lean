/-
# The door ledger: what the selector lanes cost, and which doors cannot open

## 1.  No selector door reduces the cell.  Each one is all of rank three

Eighteen theorems named `Gtz.allFiveOnPath_of_*` conclude the five on-path
registry Props at once.  Fifteen of them funnel through one Prop,
`Gtz.ConsolidatedStrictTripleDesign` (Gtz/Wave/ConsolidatedStrictTriple.lean:135),
by way of `Gtz.allFiveOnPath_of_consolidatedStrictTripleDesign`
(Gtz/Wave/ChartDesignGauge.lean:209).

`Gtz.gtzWeightedAll_three_of_consolidatedStrictTripleDesign` below shows that the
same Prop gives rank-three GTZ at EVERY size.  So a selector door is not a
reduction of the `(6,3)` cell.  It is at least the whole rank-three conjecture.
The three landed steps were all unconditional and nobody composed them:

* `Gtz.isPrimitiveDesign_iff_not_hasParallelPair` (Gtz/Design/PrimitiveTightClassification.lean),
* `Gtz.hingeHoldsAtSize_six_three_iff_no_parallelFree_tie` (Gtz/Reduction/HingeFunnel.lean:70),
* `Gtz.gtzWeightedAll_three_of_hinge` (Gtz/Reduction/ParallelFreeReach.lean:1111).

Read the ranking of doors with this law beside it.  A door ranked "closest to a
proof" is still worth the whole conjecture.

## 2.  Two doors whose hypothesis the tree already refutes

A door that cannot open type-checks and reads as an asset.  Two doors to
`Gtz.GtzWeighted 6 3` carry a hypothesis that a hypothesis-free theorem of this
same tree refutes.  Neither refutation is wired to the door it kills.

* `Gtz.gtzWeighted_six_three_of_livePivotPlaneCover` (Gtz/Wave/HeavyPivotFoil.lean:297)
  asks for `Gtz.AtomLivePivotPlaneCoverClosed`.
  `Gtz.not_atomLivePivotPlaneCoverClosed` (Gtz/Wave/PlaneRouteFoil.lean:348) refutes it.
* `Gtz.gtzWeighted_six_three_of_dropScalar` (Gtz/Wave/QuadCoverSelection.lean:1504)
  asks for `Gtz.AtomQuadDropScalarClosed`.
  `Gtz.not_atomQuadDropScalarClosed` (Gtz/Wave/QuadDropSign.lean:710) refutes it.

`Gtz.unopenableAtomDoors` records the pair in one place.

## 3.  A re-derivation the tree does not record

The strictly light branch of a tie is proved twice, three layers deep, under
names that do not collide.

* `Gtz.exists_posDef_of_lightAtom` (Gtz/Design/StratumEmptinessLedger.lean:509)
  and `Gtz.posDef_of_strictly_light_atom` (Gtz/Reduction/Deflation.lean:207),
* `Gtz.not_isTie_of_lightAtom` (:544) and
  `Gtz.not_isTie_of_strictly_light_atom` (Gtz/Wave/WedgeLeakCriterion.lean:1310),
* `Gtz.leverage_one_le_of_isTie` (:557) and
  `Gtz.forall_one_le_leverage_of_isTie` (Gtz/Wave/WedgeLeakCriterion.lean:1333).

`Gtz.lightAtomFloors_agree` states the top pair as one theorem.  Only the
statements collide, and a name scan does not catch that.

## 4.  The all-heavy residual, reached from two directions

`Gtz.hinge_of_predecessor_on_strictlyLightBranch` (Gtz/Wave/WedgeLeakCriterion.lean:1349)
closes the light branch of the two off-path registry axioms.
`Gtz.obligationSubThresholdBandHinge_of_heavyTie` (Gtz/Wave/LightAtomTieFloor.lean:108)
closes the same axiom on the complementary branch.  The two forks split one
dichotomy and neither cites the other.  `Gtz.hingeHoldsAtSize_of_heavyBranch`
puts the split in one statement.
-/
import Gtz.Wave.ConsolidatedStrictTriple
import Gtz.Wave.WedgeLeakCriterion
import Gtz.Wave.LightAtomTieFloor
import Gtz.Wave.HeavyPivotFoil
import Gtz.Wave.PlaneRouteFoil
import Gtz.Wave.QuadCoverSelection
import Gtz.Wave.QuadDropSign
import Gtz.Reduction.HingeFunnel
import Gtz.Reduction.ParallelFreeReach

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ### 1.  The level-one law of the selector lanes -/

/-- **A STRICT TRIPLE AT EVERY PRIMITIVE `(6,3)` DESIGN GIVES THE HINGE.**  A tie
that carries no parallel pair is primitive, and the strict triple the selector
supplies contradicts the tie. -/
theorem hingeHoldsAtSize_six_three_of_consolidatedStrictTripleDesign
    (hselector : ConsolidatedStrictTripleDesign) : HingeHoldsAtSize 6 3 := by
  refine hingeHoldsAtSize_six_three_iff_no_parallelFree_tie.mpr ?_
  rintro ⟨design, htie, hnoPair⟩
  obtain ⟨selected, hcard, hposDef⟩ :=
    hselector design ((isPrimitiveDesign_iff_not_hasParallelPair design).mpr hnoPair)
  exact htie.2 selected hcard hposDef

/-- **NO SELECTOR DOOR REDUCES THE CELL.**  The Prop that fifteen of the eighteen
`Gtz.allFiveOnPath_of_*` doors funnel through gives rank-three GTZ at every size.
A door of that lane is at least the whole rank-three conjecture. -/
theorem gtzWeightedAll_three_of_consolidatedStrictTripleDesign
    (hselector : ConsolidatedStrictTripleDesign) : GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_hinge
    (hingeHoldsAtSize_six_three_of_consolidatedStrictTripleDesign hselector)

/-! ### 2.  Doors whose hypothesis is refuted in this tree -/

/-- **TWO DOORS TO THE `(6,3)` CELL THAT CANNOT OPEN.**  Each hypothesis carries a
hypothesis-free refutation elsewhere in the tree.  Neither refutation was wired
to the door it kills. -/
theorem unopenableAtomDoors :
    ¬ AtomLivePivotPlaneCoverClosed ∧ ¬ AtomQuadDropScalarClosed :=
  ⟨not_atomLivePivotPlaneCoverClosed, not_atomQuadDropScalarClosed⟩

/-! ### 3.  The re-derived leverage floor -/

/-- **THE TWO LEVERAGE FLOORS ARE ONE STATEMENT.**  Two forks landed the same
theorem under names that do not collide. -/
theorem lightAtomFloors_agree {predSize rank : ℕ}
    (design : WeightedDesign (predSize + 1) rank) (hpred : 1 ≤ predSize)
    (hrecursion : GtzWeighted predSize rank) (htie : IsTie design) :
    (∀ label : Fin (predSize + 1), 1 ≤ leverageOf (design.atom label))
      ∧ (∀ label : Fin (predSize + 1), 1 ≤ leverageOf (design.atom label)) :=
  ⟨forall_one_le_leverage_of_isTie design hpred hrecursion htie,
    fun label => leverage_one_le_of_isTie design hpred hrecursion htie label⟩

/-! ### 4.  The dichotomy the two off-path forks split between them -/

/-- **THE HINGE AT A GENERAL SIZE, FROM THE ALL-HEAVY BRANCH ALONE.**  The
strictly light branch is a landed theorem, so a producer for either off-path
registry axiom needs only the all-heavy region.  Fork 175 closed the light
branch and fork 177 reduced to the heavy one.  Neither cites the other. -/
theorem hingeHoldsAtSize_of_heavyBranch {size rank : ℕ} (hsize : 2 ≤ size)
    (hpredecessor : GtzWeighted (size - 1) rank)
    (hheavy : ∀ design : WeightedDesign size rank,
      (∀ label, 1 ≤ leverageOf (design.atom label)) →
        IsTie design → HasParallelPair design) :
    HingeHoldsAtSize size rank := by
  intro design htie
  by_cases hlight : ∃ lightLabel : Fin size, leverageOf (design.atom lightLabel) < 1
  · exact hinge_of_predecessor_on_strictlyLightBranch hsize hpredecessor design hlight htie
  · push Not at hlight
    exact hheavy design (fun label => hlight label) htie

end Gtz
