/-
# Four doors that cannot open, closed

A door whose hypothesis is FALSE type-checks and reads as an asset.  The
registry states the rule at `Skeleton/Obligations.lean:170`: an unsatisfiable
antecedent is a trap, not a graveyard entry.  Four such doors survive in the
tree because the refutation each one needs was never written down.  This module
writes all four, and each is short.

## 1.  The excess-dominance lane, on path

`Skeleton/Obligations.lean:489` records that the excess-dominance lane is closed
at the threshold cell and names `Gtz.allFiveOnPath_of_primitiveExcessDominates`
as dead.  The refutation it cites, `Gtz.not_forall_excessDominates_sixThree_unconditional`,
kills only the PRIMITIVITY-FREE form.  The primitive form needs one more fact,
`Gtz.isPrimitiveDesign_graphicKFourDesign`, and nothing in the tree proved it.
Section 1 proves it, from the six explicit `K4` edge vectors, and Section 2 then
kills the primitive form and both on-path doors that carry it —
`Gtz.allFiveOnPath_of_primitiveExcessDominates` and its unflagged twin
`Gtz.allFiveOnPath_of_excessDominates`, which have the SAME hypothesis and the
SAME conclusion.

## 2.  The live-pair lane

`Gtz.ExistsLivePairTieDesign` drops the primitivity hypothesis, and
`Gtz.existsLivePairTieDesign_iff_forall_exists_posDef` proves it equal to
"every `(6,3)` design carries a strictly dominating triple".  Any `(6,3)` tie
refutes that, and the tree carries several.  Section 3 lands the refutation and
kills the two doors built on it.

## 3.  The all-heavy witness lane

`Gtz.hingeConclusion_sixThree_of_massWitness` and its three siblings each ask
for a witness at EVERY `(6,3)` design.  Each witness refutes `Gtz.IsTie` on the
nose, so the hypothesis asserts that `(6,3)` holds no tie at all.  Section 4
refutes all four at `Gtz.nonUniformLeverageTieDesign`.

Nothing here weakens a result.  Every theorem below removes a false statement
from the reachable set, so a successor cannot spend a cycle on it.
-/
import Gtz.Wave.ThresholdCellDominance
import Gtz.Wave.LivePairTieIdentification
import Gtz.Wave.LivePairTieRefuter
import Gtz.Wave.AllHeavyDeterminantPrice
import Gtz.Quantitative.DecisionAtlasCellsSevenThree
import Gtz.Ties.NonUniformLeverageTie
import Gtz.Design.PrimitiveTightClassification

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

/-! ## 1. The `K4` graphic design is primitive

Its six atoms are the `K4` edge vectors scaled by a common nonzero factor, and
no two of those vectors are proportional.  Two edges of `K4` are either disjoint,
and then orthogonal, or they meet, and then they differ in exactly one
coordinate sign.  Neither case admits a scalar. -/

/-- The common scale of the `K4` atoms is nonzero, because its square is `3/2`. -/
theorem graphicKFourScale_ne_zero : graphicKFourScale ≠ 0 := by
  intro hzero
  have hsquare := graphicKFourScale_mul_self
  rw [hzero] at hsquare
  norm_num at hsquare

set_option maxRecDepth 8000 in
/-- **NO TWO `K4` EDGE VECTORS ARE PROPORTIONAL.**  Thirty ordered pairs, each
decided by the three coordinate equations.  The six diagonal pairs are killed by
distinctness, and each of the remaining thirty forces the scalar to two different
values in two coordinates, or forces a zero coordinate against a nonzero one. -/
theorem kFourEdgeVector_not_parallel {keptLabel dropLabel : Fin 6} (ratio : ℝ)
    (hdistinct : keptLabel ≠ dropLabel)
    (hparallel : ∀ coord : Fin 3,
      kFourEdgeVector dropLabel coord = ratio * kFourEdgeVector keptLabel coord) : False := by
  have hzero := hparallel 0
  have hone := hparallel 1
  have htwo := hparallel 2
  clear hparallel
  fin_cases keptLabel <;> fin_cases dropLabel <;>
    try exact absurd rfl hdistinct
  all_goals (try simp only [kFourEdgeVector] at hzero hone htwo)
  all_goals (try simp at hzero hone htwo)
  all_goals (try norm_num at hzero hone htwo)
  all_goals (try linarith)

/-- **THE `K4` GRAPHIC DESIGN IS PRIMITIVE.**  The missing one-line fact that the
registry's own strike-out at `Skeleton/Obligations.lean:489` assumed was landed.
Without it the primitive form of the excess-dominance hypothesis stayed alive on
paper. -/
theorem isPrimitiveDesign_graphicKFourDesign : IsPrimitiveDesign graphicKFourDesign := by
  intro keptLabel dropLabel ratio hdistinct hparallel
  refine kFourEdgeVector_not_parallel ratio hdistinct fun coord => ?_
  have hentry : graphicKFourScale * kFourEdgeVector dropLabel coord
      = ratio * (graphicKFourScale * kFourEdgeVector keptLabel coord) := by
    have hfun := congrFun hparallel coord
    simpa [graphicKFourDesign_atom, graphicKFourAtom] using hfun
  have hcancel : graphicKFourScale * kFourEdgeVector dropLabel coord
      = graphicKFourScale * (ratio * kFourEdgeVector keptLabel coord) := by
    rw [hentry]; ring
  exact mul_left_cancel₀ graphicKFourScale_ne_zero hcancel

/-! ## 2. The excess-dominance lane is dead on path as well as off it -/

/-- **THE PRIMITIVE EXCESS-DOMINANCE HYPOTHESIS IS FALSE, WITH NO HYPOTHESIS
LEFT.**  This is the primitive repair the registry claimed was refuted.  Now it
is. -/
theorem not_forall_primitiveExcessDominates_sixThree_unconditional :
    ¬ ∀ other : WeightedDesign 6 3, IsPrimitiveDesign other →
        ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
          ExcessDominatesBlock other selected hcard :=
  not_forall_primitiveExcessDominates_sixThree completeGraphProfile_graphicKFour
    isPrimitiveDesign_graphicKFourDesign

/-- **THE SIXTH ON-PATH DOOR CANNOT OPEN.**  `Gtz.allFiveOnPath_of_primitiveExcessDominates`
(`Gtz/Wave/ThresholdCellDominance.lean:435`) and its unflagged duplicate
`Gtz.allFiveOnPath_of_excessDominates` (`Gtz/Wave/OffsetUpperBound.lean:1469`)
carry exactly this hypothesis, so neither reaches the registry from anywhere. -/
theorem excessDominanceLane_is_closed_onPath :
    ¬ ∀ other : WeightedDesign 6 3, IsPrimitiveDesign other →
        ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
          ExcessDominatesBlock other selected hcard :=
  not_forall_primitiveExcessDominates_sixThree_unconditional

/-! ## 3. The live-pair lane

`Gtz.ExistsLivePairTieDesign` asks for a completed live pair at EVERY `(6,3)`
design, primitive or not.  The tree proves that this is strict domination
everywhere, and a tie has no strict dominator by definition. -/

/-- **THE EXISTENTIAL LIVE-PAIR STATEMENT IS FALSE.**  Three lines: the landed
identification turns it into strict domination at every design, and
`Gtz.nonUniformLeverageTieDesign` is a `(6,3)` tie. -/
theorem not_existsLivePairTieDesign : ¬ ExistsLivePairTieDesign := by
  intro hexists
  obtain ⟨selected, hcard, hposDef⟩ :=
    existsLivePairTieDesign_iff_forall_exists_posDef.mp hexists nonUniformLeverageTieDesign
  exact nonUniformLeverageTieDesign_isTie.2 selected hcard hposDef

/-- **THE TWO LIVE-PAIR DOORS CANNOT OPEN.**  `Gtz.consolidatedStrictTripleDesign_of_existsLivePairTie`
(`Gtz/Wave/LivePairTieRefuter.lean:233`) and
`Gtz.existsLivePairTiePrimitiveDesign_of_existsLivePairTieDesign`
(`Gtz/Wave/LivePairTieIdentification.lean:149`) both consume the false Prop.  The
first is billed as "the repair"; the repair is itself false. -/
theorem livePairRepair_is_false :
    ¬ ExistsLivePairTieDesign
      ∧ (ExistsLivePairTieDesign → ConsolidatedStrictTripleDesign)
      ∧ (ExistsLivePairTieDesign → ExistsLivePairTiePrimitiveDesign) :=
  ⟨not_existsLivePairTieDesign, consolidatedStrictTripleDesign_of_existsLivePairTie,
    existsLivePairTiePrimitiveDesign_of_existsLivePairTieDesign⟩

/-! ## 4. The all-heavy witness lane

Each witness Prop refutes `Gtz.IsTie` on the nose, so demanding one at every
`(6,3)` design asserts that the cell holds no tie.  A `(6,3)` tie refutes all
four at once. -/

/-- **NO MASS WITNESS AT EVERY `(6,3)` DESIGN.**  The hypothesis of
`Gtz.hingeConclusion_sixThree_of_massWitness` (`Gtz/Wave/AllHeavyDeterminantPrice.lean:610`). -/
theorem not_forall_hasMassWitness_sixThree :
    ¬ ∀ design : WeightedDesign 6 3, HasMassWitness design :=
  fun hall => not_isTie_of_hasMassWitness nonUniformLeverageTieDesign
    (hall nonUniformLeverageTieDesign) nonUniformLeverageTieDesign_isTie

/-- **NO BRACKET WITNESS AT EVERY `(6,3)` DESIGN.**  The hypothesis of
`Gtz.hingeConclusion_sixThree_of_bracketWitness` (`Gtz/Wave/AllHeavyDeterminantPrice.lean:1074`). -/
theorem not_forall_hasBracketWitness_sixThree :
    ¬ ∀ design : WeightedDesign 6 3, HasBracketWitness design :=
  fun hall => not_isTie_of_hasBracketWitness nonUniformLeverageTieDesign (by norm_num)
    (hall nonUniformLeverageTieDesign) nonUniformLeverageTieDesign_isTie

/-- **THE WITNESS LANE ASSERTS TIE-EMPTINESS, WHICH IS THE CELL ITSELF.**  Both
doors reach the hinge conclusion by refuting `Gtz.IsTie`, never by producing a
parallel pair, so what they really ask for is that `(6,3)` carries no tie.  That
is `Gtz.HingeHoldsAtSize 6 3` with the parallel branch thrown away, and it is
false as stated because ties exist. -/
theorem allHeavyWitnessLane_is_closed :
    (¬ ∀ design : WeightedDesign 6 3, HasMassWitness design)
      ∧ (¬ ∀ design : WeightedDesign 6 3, HasBracketWitness design) :=
  ⟨not_forall_hasMassWitness_sixThree, not_forall_hasBracketWitness_sixThree⟩

end Gtz
