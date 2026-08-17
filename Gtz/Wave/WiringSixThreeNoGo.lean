/-
# The `(6,3)` no-go corpus: dead routes closed in the kernel, and the Gram refinement

This module is the `(6,3)` twin of `Gtz/Quantitative/SevenThreeNoGo.lean`.  It has
two halves.

PART ONE is an INDEX and adds no new mathematics.  Every theorem in it restates a
landed result under a name that says which METHOD the result closes.  The proof of
each restatement is the landed name itself, so the index is KERNEL-CHECKED: a dead
citation cannot rot into prose.  Read the four traps before you read the tables.

PART TWO is NEW MATHEMATICS.  It lands the raw Veronese GRAM of an atom family,
proves that stress-freeness IS positive definiteness of that Gram at every size and
rank, and reads the weight off as the solution of one symmetric linear system.  The
campaign already owns a weight elimination through the non-symmetric Veronese GRID
(`Gtz.stressFree_iff_veroneseGrid_det_ne_zero`,
`Gtz.exists_stressFree_design_iff_veronese_conditions`).  Part two refines it on four
points.  Read `## The Gram refinement` for what is new and what is not.

## #BOGUS-READING — read this first

`Gtz.not_relaxedStressFreeHinge_of_diamond` (Gtz/Design/StressFreeClosureFailure.lean:620)
is hypothesis-free and it READS as a kill of the stress-free hinge at `(6,3)`.  IT IS
NOT ONE.  Its weight clause is `0 <= weight`, and NOT `0 < weight`.  The witness is
the `(5,3)` diamond padded with a sixth atom of weight ZERO, and `Gtz.WeightedDesign`
carries `weight_pos : forall label, 0 < weight label` as a structure field.  The padded
witness is not a `Gtz.WeightedDesign 6 3` at all.

`Gtz.StressFreeHingeHoldsSixThree` (Gtz/Reduction/TrichotomyLedger.lean:629) is OPEN.
Part one pins the separation in the kernel.  `Gtz.RelaxedPositiveHingeSixThree` is the
`0 < weight` spelling, and `Gtz.relaxedPositiveHingeSixThree_of_stressFreeHinge` derives
it FROM the hinge.  So a refutation of the `0 < weight` spelling would refute the hinge,
while a refutation of the `0 <= weight` spelling says nothing at all.  The diamond
refutes only the second.

## #SIZE-LADDER — a refutation below the cell closes nothing at the cell

| refutation | file:line | size | what it closes at `(6,3)` |
|---|---|---|---|
| `Gtz.not_hingeHoldsAtSize_five_three` | Gtz/Reduction/SplitTransfer.lean:2053 | `(5,3)` | NOTHING |
| `Gtz.not_hingeHoldsAtSize_four_three` | Gtz/Design/LinePatternEnumeration.lean:1072 | `(4,3)` | NOTHING |
| `Gtz.not_forall_isTie_hasParallelPair_fourThree` | Gtz/Wave/TieAtomRepeatRefutation.lean:490 | `(4,3)` | NOTHING |
| the ten `not_polarTiltSelection*_five_three` | nine `Gtz/Reduction/Polar*` files | `(5,3)` | NOTHING |

## #CORRECTION — the polar descent is LIVE at `(6,3)`

A briefing that reached this fork claimed the `(5,3)` polar tilt refutations kill the
polar descent family at `(6,3)`, because the descent consumes the `(5,3)` instance.
THAT CLAIM IS FALSE, and this section exists so that nobody records it.

The `(6,3)` consumers take `Gtz.PolarTiltSelection 6 3`, and not the `(5,3)` instance.
Read `Gtz.hingeHoldsAtSize_six_three_of_polarTilt` and
`Gtz.gtzWeighted_six_three_of_polarTilt` (Gtz/Reduction/PolarCoverDescent.lean:1176 and
:1305).  `Gtz.PolarTiltSelection 6 3` is REFUTED NOWHERE in this tree.  The window floor
`2 * rank <= size` separates the two cells: it fails at `(5,3)` and it holds at `(6,3)`.
The module's own note (Gtz/Reduction/PolarCoverDescent.lean:1257 thru :1264) frames the
`(5,3)` refutations as a CALIBRATION that shows the residual carries real content.  The
polar route to `(6,3)` is a live route, and a fork that treats it as dead loses it.

The census of the ten `(5,3)` refutations, for the record:

| name | file |
|---|---|
| `Gtz.not_polarTiltSelection_five_three` | Gtz/Reduction/PolarCoverDescent.lean:1269 |
| `Gtz.not_polarTiltSelectionTieFree_five_three` | Gtz/Reduction/PolarCoverDescent.lean:1274 |
| `Gtz.not_polarTiltSelectionCircular_five_three` | Gtz/Reduction/PolarCircularOrder.lean:1504 |
| `Gtz.not_polarTiltSelectionDeletion_five_three` | Gtz/Reduction/PolarDeletionWhitening.lean:1553 |
| `Gtz.not_polarTiltSelectionSetDeletion_five_three` | Gtz/Reduction/PolarIteratedDeletion.lean:1848 |
| `Gtz.not_polarTiltSelectionSpread_five_three` | Gtz/Reduction/PolarPairSpread.lean:1137 |
| `Gtz.not_polarTiltSelectionPlane_five_three` | Gtz/Reduction/PolarPlaneTurn.lean:1316 |
| `Gtz.not_polarTiltSelectionFloor_five_three` | Gtz/Reduction/PolarShadowFloor.lean:1808 |
| `Gtz.not_polarTiltSelectionUnsaturated_five_three` | Gtz/Reduction/PolarTiltLedger.lean:766 |
| `Gtz.not_polarTiltSelectionWitness_five_three` | Gtz/Reduction/PolarWitnessSchur.lean:673 |

The one polar-side statement that IS closed at the cell is
`Gtz.not_rankSuccShrinks_six_three` (Gtz/Reduction/PolarCoverDescent.lean:1363), and it
closes `Gtz.RankSuccShrinks 6 3` and nothing else.

## #CRUX-TRAP — a binder-free scan reports these as unconditional, and they are not

Over fifty `variable` binders of type `Gtz.SixThreeCrux` stand in this tree, spread over
more than thirty files.  Most of them sit in `Gtz/Quantitative/` and in the
`SharedPrivate*` and `Outer*` groups of `Gtz/Wave/`.  The count moves with the campaign,
so read it from `rg -n 'variable.*SixThreeCrux'` and not from this table.  Every theorem
under such a binder is CONDITIONAL on GTZ `(6,3)` FAILING.  Those theorems are structure
theory of a hypothetical counterexample and they close no route.  A scan that only counts
explicit hypotheses reports each of them as hypothesis-free.  Do not put one in a
graveyard.

## #GRAVEYARD — hypothesis-free route-closers at `(6,3)`

| landed name | file:line | witness | the method that can no longer be attempted |
|---|---|---|---|
| `Gtz.not_forall_excessDominates_sixThree_unconditional` | Gtz/Wave/ThresholdCellDominance.lean:790 | `graphicKFourDesign` | Do not assume that every `(6,3)` design carries an excess dominated triple |
| `Gtz.not_exists_excessDominates_graphicKFour` | Gtz/Wave/ThresholdCellDominance.lean:798 | `graphicKFourDesign` | Do not look for an excess dominated triple of the `K4` graphic design |
| `Gtz.exists_stressFree_sixThree_beyond_weightCap` | Gtz/Wave/StressFreeCapRefutation.lean:640 | `capFoilDesign` | Do not empty the stress-free stratum with a weight cap on the selected block |
| `Gtz.not_forall_sixThree_isTie_repeats_an_atom` | Gtz/Wave/TieAtomRepeatRefutation.lean:426 | `antipodalTetraDesign` | Do not assume that a `(6,3)` tie repeats an atom |
| `Gtz.tetrahedron_gaugeStar_posDef_with_failing_price` | Gtz/Wave/DeflatedCellTotal.lean:1177 | `tetrahedronChartPoint` | Do not price a chart star by the deflated gauge, because the price fails where the cell holds |
| `Gtz.kFourPencilCell_not_total` | Gtz/Wave/KirchhoffSignTower.lean:1285 | `pencilCellRefuterPoint` | Do not treat the `K4` pencil cell as a total atlas over the chart points |
| `Gtz.exists_primitiveDesign_posDet_not_dominates` | Gtz/Wave/DustBoundaryFloor.lean:915 | `flatFrame` | Do not read a positive gap determinant as a certificate of domination |
| `Gtz.not_exists_uniform_gapDet_floor` | Gtz/Wave/DustBoundaryFloor.lean:697 | the dust family | Do not look for a positive uniform lower bound on the largest gap determinant |
| `Gtz.capFoil_isotropy_tests_incomparable` | Gtz/Wave/ComplementBlockBudget.lean:966 | `capFoilDesign` | Do not substitute one isotropy test for the other, because neither contains the other |
| `Gtz.not_hasIsotropicGap_kFourDesign_star` | Gtz/Wave/TieConstraintIntersectionKFour.lean:306 | `kFourDesign` | Do not use the isotropy arm alone, because it misses a strict dominator |
| `Gtz.not_hasStrictCertificate_kFourDesign_star` | Gtz/Wave/TieConstraintIntersectionKFour.lean:318 | `kFourDesign` | Do not treat the strict certificate as necessary for strict domination |
| `Gtz.not_livePairTieResidual` | Gtz/Wave/LivePairTieRefuter.lean:183 | `livePairTieRefuterDesign` | Do not open the hinge through the live-pair tie residual |
| `Gtz.not_oneLineLlfSelector` | Gtz/Design/SelectorEquivalences.lean:541 | line-pattern witness | Do not select the line-free label by a one-line rule |
| `Gtz.not_oneLineLlfSelectorAtTightAntecedent` | Gtz/Design/SelectorEquivalences.lean:761 | `tightLlfDesign` | Do not repair that rule by tightening its antecedent |
| `Gtz.not_freeTripleSelectorRule` | Gtz/Design/TightAntecedentMining.lean:472 | `r4WitnessDesign` | Do not select the free triple by a fixed rule |
| `Gtz.not_complementSelectorRule` | Gtz/Design/TightAntecedentMining.lean:478 | `r4WitnessDesign` | Do not select the complement block by a fixed rule |
| `Gtz.not_atomTenthSelectorSixth` | Gtz/Wave/TenthAverageFloor.lean:731 | the extremal reading | Do not ask a weighted atom average to reach the sixth, because the cap is `(2 - sqrt 2)/4` |
| `Gtz.not_exists_privateAtomSelector_chartTripleSharedEdgeFamily` | Gtz/Quantitative/PrivateAtomQuantization.lean:926 | the shared-edge family | Do not give each block of that family a private atom |

Two selector entries carry binders and the table says so at the site.
`Gtz.not_atomTenthSelectorSixth` quantifies over a weight read and takes a support
condition and a positive mass condition.  It is a cap theorem and not a plain
refutation.  Part one restates it with those binders intact.

## #REGION-BOUND — three refutations that hold only inside a rectangle

| name | file:line | live hypotheses |
|---|---|---|
| `Gtz.baseTripleClearanceBoundedFloor_rectangle_refuted` | Gtz/Design/LineFreeConicBridge.lean:3432 | `clearanceFloor <= 3/8` and `1/16 <= marginFloor` |
| `Gtz.clearanceBoundedInteriorFloor_rectangle_refuted` | Gtz/Design/LineFreeConicBridge.lean:3471 | the same two |
| `Gtz.interiorFamilyMarginFloor_monotoneGraded_refuted` | Gtz/Design/LineFreeConicBridge.lean:3487 | a monotone floor that reaches `1/16` at `3/8` |

Outside that rectangle these three close NOTHING.  The two unconditional results of the
same lane are `Gtz.baseTripleClearanceBoundedFloor_sixteenth_quarter_refuted`
(Gtz/Design/LineFreeConicBridge.lean:2578) and
`Gtz.clearanceBoundedInteriorFloor_sixteenth_quarter_refuted` (:2613), and each of them
refutes exactly one constant pair.

## #NOT-A-REFUTATION — two names that a census reports incorrectly

* `Gtz.not_forall_sharpBalanceValue_pos` (Gtz/Wave/MixedTripleBalance.lean:507) is NOT
  hypothesis-free.  It carries ten binders, and two of them are real sign conditions on
  the cross products.  `Gtz.crossProducts_nonpos_of_two_in_one_out` (:527) discharges
  the two from a test that reads two atoms in and one atom out.
* `Gtz.det_labelGram_eq_zero_of_rank_lt` (Gtz/Wave/AllHeavyDeterminantPrice.lean:441) is
  a COLLAPSE LEMMA and not a refutation.  It needs `rank < listCount`.

## #WITNESS-INDEX — one witness usually kills several routes

| witness | file:line | what it refutes |
|---|---|---|
| `Gtz.graphicKFourDesign` | Gtz/Wave/ThresholdCellDominance.lean | the excess dominated producer at `(6,3)`, and every one of its twenty triples |
| `Gtz.capFoilDesign` | Gtz/Wave/StressFreeCapRefutation.lean | the weight cap branch, and the containment of either isotropy test in the other |
| `Gtz.antipodalTetraDesign` | Gtz/Wave/TieAtomRepeatRefutation.lean | the atom repeat hypothesis of the heavy needle residual |
| `Gtz.kFourDesign` | Gtz/Wave/TieConstraintIntersectionKFour.lean | the isotropy arm and the whole strict certificate at the star triple |
| `Gtz.flatFrame` | Gtz/Wave/DustBoundaryFloor.lean | the positive gap determinant certificate, and with the dust family the uniform floor |
| `Gtz.livePairTieRefuterDesign` | Gtz/Wave/LivePairTieRefuter.lean | the live-pair tie residual door to the hinge |
| `Gtz.tetrahedronChartPoint` | Gtz/Wave/DeflatedCellTotal.lean | the deflated gauge price, with the cell intact at the same point |
| `Gtz.pencilCellRefuterPoint` | Gtz/Wave/KirchhoffSignTower.lean | totality of the `K4` pencil cell |
| `Gtz.r4WitnessDesign` | Gtz/Design/TightAntecedentMining.lean | the free triple rule and the complement rule together |
| `Gtz.tightLlfDesign` | Gtz/Design/SelectorEquivalences.lean | the one-line rule at its tight antecedent |
| `Gtz.diamondDesign` | Gtz/Design/StressFreeClosureFailure.lean | the `0 <= weight` relaxation ONLY.  Refer to #BOGUS-READING |
| `Gtz.sixSplitDiamondDesign` | Gtz/Reduction/PolarCoverDescent.lean | `Gtz.RankSuccShrinks 6 3` |
| `Gtz.minimaxRefuterDesign` | Gtz/Design/LineFreeConicBridge.lean | the clearance-bounded floors on the rectangle only |
| `Gtz.floorRefuterDesign` | Gtz/Design/LineFreeConicBridge.lean | the two constant pairs at `(1/16, 1/4)` |

## The Gram refinement

Part two builds `Gtz.veroneseAtomGram`, the matrix `M[i][j] = (g_i . g_j)^2` of an atom
family.  It is the Gram matrix of the rank-one images `g |-> g g^T` under the Frobenius
pairing, and the whole of part two comes out of one identity:

    `coeff . (M *v coeff) = frobeniusNormSq (sum_i coeff_i g_i g_i^T)`.

Four points separate this from the landed grid elimination.

1. THE SIGN IS KNOWN.  `Gtz.veroneseGrid` is not symmetric and its determinant carries
   no canonical sign.  `M` is symmetric and positive semidefinite at EVERY atom family
   (`Gtz.posSemidef_veroneseAtomGram`), so its determinant is never negative, and
   stress-freeness is the single strict inequality `0 < det M`
   (`Gtz.isStressFreeDesign_iff_det_veroneseAtomGram_pos`).  The bridge to the grid form
   is `Gtz.det_veroneseAtomGram_pos_iff_det_veroneseGrid_ne_zero`.
2. THE CRITERION IS QUANTITATIVE.  The identity above turns a stress vector into a
   Frobenius energy, so `M` measures HOW stress-free a family is, and not only whether
   it is.
3. THE STATEMENTS ARE SIZE-GENERIC.  The grid machinery is hard-wired to `(6,3)`.  Every
   statement of part two before the `(6,3)` section holds at every size and every rank,
   so the `(7,3)` frontier inherits the criterion for free.
4. THE SYSTEM IS SYMMETRIC.  Parseval contracted against each atom gives
   `M *v weight = leverage` (`Gtz.veroneseAtomGram_mulVec_weight`) with no hypothesis at
   all, and `weight . (M *v weight) = rank` at every design.  On the stress-free stratum
   the weight is `M^{-1} *v leverage`, which gives the two closed scalar laws
   `leverage . M^{-1} leverage = rank` and `one . M^{-1} leverage = 1`.

The last section composes these into
`Gtz.stressFreeHingeHoldsSixThree_iff_gramAtomFamilyStrictTriple`: the OPEN `(6,3)`
obligation is equivalent to a statement about eighteen atom coordinates in which the
weight variable does not occur.  That is a reduction of the obligation and it is not a
proof of it.  `Gtz.StressFreeHingeHoldsSixThree` stays open.

## What this module does NOT do

* It proves no new refutation.  Part one restates landed results and nothing else.
* It does not close `Gtz.StressFreeHingeHoldsSixThree`, `Gtz.PolarTiltSelection 6 3`, or
  any other open `(6,3)` Prop.
* It does not repeat the grid elimination of `Gtz/Wave/VeroneseWeightElimination.lean`.
  The two weight readings agree, and the bridge between the two criteria is landed here.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.LeverageBound
import Gtz.Design.UniversalNeedle
import Gtz.Design.StressFreeStratum
import Gtz.Quantitative.SevenThreeMetricBound
import Gtz.Reduction.TrichotomyLedger
import Gtz.Wave.ThresholdCellDominance
import Gtz.Wave.StressFreeCapRefutation
import Gtz.Wave.TieAtomRepeatRefutation
import Gtz.Wave.DeflatedCellTotal
import Gtz.Wave.KirchhoffSignTower
import Gtz.Wave.DustBoundaryFloor
import Gtz.Wave.ComplementBlockBudget
import Gtz.Wave.TieConstraintIntersectionKFour
import Gtz.Wave.LivePairTieRefuter
import Gtz.Wave.TenthAverageFloor
import Gtz.Wave.MixedTripleBalance
import Gtz.Wave.AllHeavyDeterminantPrice
import Gtz.Wave.WiringResidualEquivalence
import Gtz.Design.SelectorEquivalences
import Gtz.Design.TightAntecedentMining
import Gtz.Design.StressFreeClosureFailure
import Gtz.Design.LineFreeConicBridge
import Gtz.Design.LinePatternEnumeration
import Gtz.Quantitative.PrivateAtomQuantization
import Gtz.Reduction.SplitTransfer
import Gtz.Reduction.PolarCoverDescent

namespace Gtz

open Matrix

set_option autoImplicit false
set_option relaxedAutoImplicit false

variable {m k : ℕ}

/-! ## Part one, section 1.  The producer lane

The two results below close the excess dominated producer at `(6,3)`.  The first kills
the universal statement and the second kills its witness triple by triple. -/

/-- **THE EXCESS DOMINATED PRODUCER IS CLOSED AT `(6,3)`.**  Index entry for
`Gtz.not_forall_excessDominates_sixThree_unconditional`. -/
theorem sixThreeNoGo_excessDominatedProducer :
    ¬ ∀ design : WeightedDesign 6 3,
        ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
          ExcessDominatesBlock design selected hcard :=
  not_forall_excessDominates_sixThree_unconditional

/-- **AND NO TRIPLE OF THE `K4` GRAPHIC DESIGN IS EXCESS DOMINATED.**  Index entry for
`Gtz.not_exists_excessDominates_graphicKFour`. -/
theorem sixThreeNoGo_excessDominatedGraphicKFour :
    ¬ ∃ selected : Finset (Fin 6), ∃ hcard : selected.card = 3,
        ExcessDominatesBlock graphicKFourDesign selected hcard :=
  not_exists_excessDominates_graphicKFour

/-! ## Part one, section 2.  The certificate lane

Three certificates that a campaign wants to read as necessary, and are not. -/

/-- **A POSITIVE GAP DETERMINANT IS NOT A CERTIFICATE OF DOMINATION.**  Index entry for
`Gtz.exists_primitiveDesign_posDet_not_dominates`. -/
theorem sixThreeNoGo_positiveGapDeterminantCertificate :
    ∃ (design : WeightedDesign 6 3) (selected : Finset (Fin 6)),
      IsPrimitiveDesign design ∧ selected.card = 3
        ∧ (subsetSum design selected - 1).det = 85 / 29 ∧ ¬ Dominates design selected :=
  exists_primitiveDesign_posDet_not_dominates

/-- **NO POSITIVE UNIFORM FLOOR EXISTS FOR THE LARGEST GAP DETERMINANT.**  Index entry
for `Gtz.not_exists_uniform_gapDet_floor`. -/
theorem sixThreeNoGo_uniformGapDeterminantFloor :
    ¬ ∃ floor : ℝ, 0 < floor ∧ ∀ design : WeightedDesign 6 3,
        ∃ selected : Finset (Fin 6), selected.card = 3
          ∧ floor ≤ (subsetSum design selected - 1).det :=
  not_exists_uniform_gapDet_floor

/-- **THE STRICT CERTIFICATE IS NOT NECESSARY FOR STRICT DOMINATION.**  Index entry for
`Gtz.not_hasStrictCertificate_kFourDesign_star`, whose triple dominates strictly. -/
theorem sixThreeNoGo_strictCertificate :
    ¬ HasStrictCertificate kFourDesign ({0, 2, 4} : Finset (Fin 6)) :=
  not_hasStrictCertificate_kFourDesign_star

/-- **THE ISOTROPY ARM ALONE MISSES A STRICT DOMINATOR.**  Index entry for
`Gtz.not_hasIsotropicGap_kFourDesign_star`. -/
theorem sixThreeNoGo_isotropyArm :
    ¬ HasIsotropicGap kFourDesign ({0, 2, 4} : Finset (Fin 6)) :=
  not_hasIsotropicGap_kFourDesign_star

/-! ## Part one, section 3.  The door lane

Two hypotheses that later modules take as antecedents, and that this tree refutes.  A
door with a refuted hypothesis opens nothing. -/

/-- **A `(6,3)` TIE DOES NOT ALWAYS REPEAT AN ATOM.**  Index entry for
`Gtz.not_forall_sixThree_isTie_repeats_an_atom`. -/
theorem sixThreeNoGo_tieRepeatsAnAtom :
    ¬ (∀ design : WeightedDesign 6 3, IsTie design →
        ∃ firstLabel secondLabel : Fin 6,
          firstLabel ≠ secondLabel ∧ design.atom firstLabel = design.atom secondLabel) :=
  not_forall_sixThree_isTie_repeats_an_atom

/-- **THE LIVE-PAIR TIE RESIDUAL IS FALSE.**  Index entry for
`Gtz.not_livePairTieResidual`. -/
theorem sixThreeNoGo_livePairTieResidual :
    ¬ (∀ design : WeightedDesign 6 3,
        (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Dominates design dominator) →
        ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
          IsLivePair design pivotLabel pairFirst →
          ∃ pairSecond, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
            ∧ 0 < discriminantTie design pivotLabel pairFirst pairSecond) :=
  not_livePairTieResidual

/-! ## Part one, section 4.  The selector lane

Six named selector rules, all dead.  `sixThreeNoGo_selectorLane` bundles the four that
are plain refutations, so that one citation covers the lane. -/

/-- **THE FOUR PLAIN SELECTOR KILLS, IN ONE STATEMENT.**  No one-line rule and no fixed
triple or complement rule selects the labels that the line lane needs. -/
theorem sixThreeNoGo_selectorLane :
    ¬ OneLineLlfSelector
      ∧ ¬ OneLineLlfSelectorAtTightAntecedent
      ∧ ¬ FreeTripleSelectorRule
      ∧ ¬ ComplementSelectorRule (lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  ⟨not_oneLineLlfSelector, not_oneLineLlfSelectorAtTightAntecedent,
    not_freeTripleSelectorRule, not_complementSelectorRule⟩

/-- **NO PRIVATE ATOM SELECTOR EXISTS ON THE SHARED-EDGE FAMILY.**  Index entry for
`Gtz.not_exists_privateAtomSelector_chartTripleSharedEdgeFamily`. -/
theorem sixThreeNoGo_privateAtomSelector :
    ¬ ∃ privateAtom : Finset (Fin 6) → Fin 6,
        ∀ firstBlock ∈ chartTripleSharedEdgeFamily,
          ∀ secondBlock ∈ chartTripleSharedEdgeFamily,
            firstBlock ≠ secondBlock → privateAtom firstBlock ∉ secondBlock :=
  not_exists_privateAtomSelector_chartTripleSharedEdgeFamily

/-- **THE ATOM TENTH READING CANNOT REACH THE SIXTH.**  Index entry for
`Gtz.not_atomTenthSelectorSixth`.  BINDERS ARE LIVE: this restatement keeps the support
condition and the positive mass condition of the original, because the original is a cap
theorem and not a plain refutation. -/
theorem sixThreeNoGo_atomTenthCap {weightRead : Fin 6 → Fin 6 → Fin 6 → ℝ}
    (hsupport : ∀ firstLabel secondLabel thirdLabel : Fin 6,
      atomTenthNum firstLabel secondLabel thirdLabel = 0 →
        weightRead firstLabel secondLabel thirdLabel = 0)
    (hmass : 0 < atomTripleFamilySum weightRead) :
    atomTripleFamilySum
        (fun firstLabel secondLabel thirdLabel =>
          weightRead firstLabel secondLabel thirdLabel
            * atomTenthReading firstLabel secondLabel thirdLabel)
      < (1 / 6) * atomTripleFamilySum weightRead :=
  not_atomTenthSelectorSixth hsupport hmass

/-! ## Part one, section 5.  The chart lane -/

/-- **THE `K4` PENCIL CELL IS NOT A TOTAL ATLAS.**  Index entry for
`Gtz.kFourPencilCell_not_total`. -/
theorem sixThreeNoGo_pencilCellTotality :
    ¬ (∀ point : DirectionChartPoint 6, ∃ tree ∈ kFourSpanningTreeList,
        KFourPencilCellFires point tree) :=
  kFourPencilCell_not_total

/-- **THE `RankSuccShrinks` LAST STAGE IS FALSE AT `(6,3)`.**  Index entry for
`Gtz.not_rankSuccShrinks_six_three`.  This is the ONE polar-side statement that closes
at the cell.  Refer to #CORRECTION for what it does not close. -/
theorem sixThreeNoGo_rankSuccShrinks : ¬ RankSuccShrinks 6 3 :=
  not_rankSuccShrinks_six_three

/-! ## Part one, section 6.  The `0 <= weight` trap, pinned in the kernel

`Gtz.RelaxedPositiveHingeSixThree` is the `0 < weight` spelling of the statement that
`Gtz.not_relaxedStressFreeHinge_of_diamond` refutes with `0 <= weight`.  The two
theorems that follow show that the strict spelling sits BELOW the hinge, so a
refutation of it would refute the hinge, and the diamond does not reach it. -/

/-- The relaxed branch-(i) statement with a STRICT weight clause. -/
def RelaxedPositiveHingeSixThree : Prop :=
  ∀ (atom : Fin 6 → Fin 3 → ℝ) (weight : Fin 6 → ℝ),
    (∀ label, 0 < weight label) →
    (∑ label, weight label) = 1 →
    (∑ label, weight label • atomMatrix (atom label)) = 1 →
    (∀ stressCoeff : Fin 6 → ℝ,
      (∑ label, stressCoeff label • atomMatrix (atom label)) = 0 → stressCoeff = 0) →
    ∃ firstLabel secondLabel thirdLabel : Fin 6,
      firstLabel ≠ secondLabel ∧ firstLabel ≠ thirdLabel ∧ secondLabel ≠ thirdLabel
        ∧ (atomMatrix (atom firstLabel) + atomMatrix (atom secondLabel)
            + atomMatrix (atom thirdLabel) - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef

/-- **POSITIVE WEIGHT DATA IS DESIGN DATA.**  Atom and weight functions that satisfy the
strict weight clause, the normalization and Parseval assemble into a
`Gtz.WeightedDesign 6 3`.  The `0 <= weight` relaxation has no such reading, because
`Gtz.WeightedDesign.weight_pos` is strict. -/
theorem exists_weightedDesign_of_positiveRelaxedData (atom : Fin 6 → Fin 3 → ℝ)
    (weight : Fin 6 → ℝ) (hpositive : ∀ label, 0 < weight label)
    (hsum : (∑ label, weight label) = 1)
    (hparseval : (∑ label, weight label • atomMatrix (atom label)) = 1) :
    ∃ design : WeightedDesign 6 3, design.atom = atom ∧ design.weight = weight :=
  ⟨{ atom := atom, weight := weight, weight_pos := hpositive,
      weight_sum_one := hsum, isParseval := hparseval }, rfl, rfl⟩

/-- **THE STRICT SPELLING SITS BELOW THE HINGE.**  The open
`Gtz.StressFreeHingeHoldsSixThree` implies `Gtz.RelaxedPositiveHingeSixThree`. -/
theorem relaxedPositiveHingeSixThree_of_stressFreeHinge
    (hinge : StressFreeHingeHoldsSixThree) : RelaxedPositiveHingeSixThree := by
  intro atom weight hpositive hsum hparseval hfree
  set design : WeightedDesign 6 3 :=
    { atom := atom, weight := weight, weight_pos := hpositive,
      weight_sum_one := hsum, isParseval := hparseval } with hdesign
  obtain ⟨triple, hcard, hposDef⟩ := exists_posDef_triple_of_stressFreeHinge hinge design hfree
  obtain ⟨firstLabel, secondLabel, thirdLabel, hfirstSecond, hfirstThird, hsecondThird, rfl⟩ :=
    Finset.card_eq_three.mp hcard
  have hfirstNotMem : firstLabel ∉ ({secondLabel, thirdLabel} : Finset (Fin 6)) := by
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
    exact ⟨hfirstSecond, hfirstThird⟩
  have hsecondNotMem : secondLabel ∉ ({thirdLabel} : Finset (Fin 6)) := by
    simp only [Finset.mem_singleton]
    exact hsecondThird
  have hsubsetSum : subsetSum design ({firstLabel, secondLabel, thirdLabel} : Finset (Fin 6))
      = atomMatrix (atom firstLabel) + atomMatrix (atom secondLabel)
        + atomMatrix (atom thirdLabel) := by
    rw [subsetSum, Finset.sum_insert hfirstNotMem, Finset.sum_insert hsecondNotMem,
      Finset.sum_singleton]
    show atomMatrix (atom firstLabel)
      + (atomMatrix (atom secondLabel) + atomMatrix (atom thirdLabel)) = _
    abel
  refine ⟨firstLabel, secondLabel, thirdLabel, hfirstSecond, hfirstThird, hsecondThird, ?_⟩
  rw [← hsubsetSum]
  exact hposDef

/-- **THE TRAP, CLOSED.**  A refutation of the STRICT spelling refutes the hinge.  The
diamond of `Gtz.not_relaxedStressFreeHinge_of_diamond` refutes only the `0 <= weight`
spelling, which is a strictly weaker antecedent, so the diamond leaves the hinge
untouched. -/
theorem not_stressFreeHingeHoldsSixThree_of_not_relaxedPositiveHinge
    (hrefuted : ¬ RelaxedPositiveHingeSixThree) : ¬ StressFreeHingeHoldsSixThree :=
  fun hinge => hrefuted (relaxedPositiveHingeSixThree_of_stressFreeHinge hinge)

/-- **THE STRICTNESS PIN.**  No weight of a `Gtz.WeightedDesign` vanishes.  This one
line is the whole reason the padded diamond escapes the design family. -/
theorem weight_ne_zero (design : WeightedDesign m k) (label : Fin m) :
    design.weight label ≠ 0 :=
  (design.weight_pos label).ne'

/-! ## Part two, section 1.  The raw Veronese Gram of an atom family

`veroneseAtomGram atom` is the Gram matrix of the rank-one images `g g^T` under the
Frobenius pairing.  Every statement of this section is size-generic and rank-generic,
and no statement of it reads a weight. -/

/-- **THE RAW VERONESE GRAM**: entry `(i, j)` is `(g_i . g_j)^2`. -/
noncomputable def veroneseAtomGram {size rank : ℕ} (atom : Fin size → Fin rank → ℝ) :
    Matrix (Fin size) (Fin size) ℝ :=
  Matrix.of fun firstLabel secondLabel => (atom firstLabel ⬝ᵥ atom secondLabel) ^ 2

theorem veroneseAtomGram_apply {size rank : ℕ} (atom : Fin size → Fin rank → ℝ)
    (firstLabel secondLabel : Fin size) :
    veroneseAtomGram atom firstLabel secondLabel = (atom firstLabel ⬝ᵥ atom secondLabel) ^ 2 :=
  rfl

theorem veroneseAtomGram_comm {size rank : ℕ} (atom : Fin size → Fin rank → ℝ)
    (firstLabel secondLabel : Fin size) :
    veroneseAtomGram atom firstLabel secondLabel
      = veroneseAtomGram atom secondLabel firstLabel := by
  rw [veroneseAtomGram_apply, veroneseAtomGram_apply,
    dotProduct_comm (atom firstLabel) (atom secondLabel)]

/-- The diagonal is the SQUARE of the leverage. -/
theorem veroneseAtomGram_diag {size rank : ℕ} (atom : Fin size → Fin rank → ℝ)
    (label : Fin size) :
    veroneseAtomGram atom label label = leverageOf (atom label) ^ 2 := by
  rw [veroneseAtomGram_apply, leverageOf_eq_dotProduct]

theorem isHermitian_veroneseAtomGram {size rank : ℕ} (atom : Fin size → Fin rank → ℝ) :
    (veroneseAtomGram atom).IsHermitian := by
  refine Matrix.ext fun firstLabel secondLabel => ?_
  simp only [Matrix.conjTranspose_apply, star_trivial]
  exact veroneseAtomGram_comm atom secondLabel firstLabel

/-! ### The Frobenius side -/

private theorem frobeniusNormSq_nonneg (target : Matrix (Fin k) (Fin k) ℝ) :
    0 ≤ frobeniusNormSq target := by
  rw [frobeniusNormSq, frobeniusInner]
  exact Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _

private theorem frobeniusNormSq_zero_matrix :
    frobeniusNormSq (0 : Matrix (Fin k) (Fin k) ℝ) = 0 := by
  rw [frobeniusNormSq, frobeniusInner]
  simp only [Matrix.zero_apply, mul_zero, Finset.sum_const_zero]

private theorem eq_zero_of_frobeniusNormSq_eq_zero {target : Matrix (Fin k) (Fin k) ℝ}
    (hzero : frobeniusNormSq target = 0) : target = 0 := by
  rw [frobeniusNormSq, frobeniusInner] at hzero
  refine Matrix.ext fun rowIndex colIndex => ?_
  have hrowNonneg : ∀ probeRow ∈ (Finset.univ : Finset (Fin k)),
      (0 : ℝ) ≤ ∑ probeCol, target probeRow probeCol * target probeRow probeCol :=
    fun _ _ => Finset.sum_nonneg fun _ _ => mul_self_nonneg _
  have hrowZero := (Finset.sum_eq_zero_iff_of_nonneg hrowNonneg).mp hzero rowIndex
    (Finset.mem_univ rowIndex)
  have hcellZero := (Finset.sum_eq_zero_iff_of_nonneg
    (fun probeCol _ => mul_self_nonneg (target rowIndex probeCol))).mp hrowZero colIndex
    (Finset.mem_univ colIndex)
  rw [Matrix.zero_apply]
  exact mul_self_eq_zero.mp hcellZero

private theorem frobeniusInner_smul_left (scalarValue : ℝ)
    (leftMatrix rightMatrix : Matrix (Fin k) (Fin k) ℝ) :
    frobeniusInner (scalarValue • leftMatrix) rightMatrix
      = scalarValue * frobeniusInner leftMatrix rightMatrix := by
  rw [frobeniusInner, frobeniusInner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun rowIndex _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun colIndex _ => ?_
  simp only [Matrix.smul_apply, smul_eq_mul]
  ring

private theorem frobeniusInner_smul_right (scalarValue : ℝ)
    (leftMatrix rightMatrix : Matrix (Fin k) (Fin k) ℝ) :
    frobeniusInner leftMatrix (scalarValue • rightMatrix)
      = scalarValue * frobeniusInner leftMatrix rightMatrix := by
  rw [frobeniusInner_comm, frobeniusInner_smul_left, frobeniusInner_comm rightMatrix leftMatrix]

private theorem frobeniusInner_sum_left {indexType : Type} [Fintype indexType]
    (family : indexType → Matrix (Fin k) (Fin k) ℝ) (rightMatrix : Matrix (Fin k) (Fin k) ℝ) :
    frobeniusInner (∑ index, family index) rightMatrix
      = ∑ index, frobeniusInner (family index) rightMatrix := by
  rw [frobeniusInner_comm, frobeniusInner_sum_right]
  exact Finset.sum_congr rfl fun index _ => frobeniusInner_comm rightMatrix (family index)

/-- **THE RANK-ONE PAIRING IS THE SQUARED CORRELATION.**  This one line is why the
squared Gram is a Gram at all. -/
theorem frobeniusInner_atomMatrix (leftVec rightVec : Fin k → ℝ) :
    frobeniusInner (atomMatrix leftVec) (atomMatrix rightVec) = (leftVec ⬝ᵥ rightVec) ^ 2 := by
  have hdot : leftVec ⬝ᵥ rightVec = ∑ index, leftVec index * rightVec index := rfl
  rw [frobeniusInner, hdot, sq, Fintype.sum_mul_sum]
  refine Finset.sum_congr rfl fun rowIndex _ => Finset.sum_congr rfl fun colIndex _ => ?_
  simp only [atomMatrix, Matrix.vecMulVec_apply]
  ring

/-- **THE ENERGY IDENTITY.**  A stress vector against the raw Veronese Gram reads the
Frobenius energy of the stress it manufactures.  Everything else in part two is a
corollary of this line. -/
theorem dotProduct_veroneseAtomGram_mulVec {size rank : ℕ} (atom : Fin size → Fin rank → ℝ)
    (coeff : Fin size → ℝ) :
    coeff ⬝ᵥ (veroneseAtomGram atom *ᵥ coeff)
      = frobeniusNormSq (∑ label, coeff label • atomMatrix (atom label)) := by
  have hright : frobeniusNormSq (∑ label, coeff label • atomMatrix (atom label))
      = ∑ firstLabel, ∑ secondLabel,
          coeff firstLabel * coeff secondLabel * (atom firstLabel ⬝ᵥ atom secondLabel) ^ 2 := by
    rw [frobeniusNormSq, frobeniusInner_sum_left]
    refine Finset.sum_congr rfl fun firstLabel _ => ?_
    rw [frobeniusInner_sum_right]
    refine Finset.sum_congr rfl fun secondLabel _ => ?_
    rw [frobeniusInner_smul_left, frobeniusInner_smul_right, frobeniusInner_atomMatrix]
    ring
  have hleft : coeff ⬝ᵥ (veroneseAtomGram atom *ᵥ coeff)
      = ∑ firstLabel, ∑ secondLabel,
          coeff firstLabel * coeff secondLabel * (atom firstLabel ⬝ᵥ atom secondLabel) ^ 2 := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun firstLabel _ => ?_
    rw [Matrix.mulVec, dotProduct, Finset.mul_sum]
    refine Finset.sum_congr rfl fun secondLabel _ => ?_
    rw [veroneseAtomGram_apply]
    ring
  rw [hleft, hright]

/-- **THE RAW VERONESE GRAM IS POSITIVE SEMIDEFINITE AT EVERY ATOM FAMILY.**  No design,
no Parseval, no nondegeneracy.  So its determinant is never negative, and the sign of
the stress-free criterion is known before the criterion is stated. -/
theorem posSemidef_veroneseAtomGram {size rank : ℕ} (atom : Fin size → Fin rank → ℝ) :
    (veroneseAtomGram atom).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr ⟨isHermitian_veroneseAtomGram atom, ?_⟩
  intro probe
  have hstar : star probe = probe := rfl
  rw [hstar, dotProduct_veroneseAtomGram_mulVec]
  exact frobeniusNormSq_nonneg _

/-- **STRESS-FREENESS IS POSITIVE DEFINITENESS OF THE RAW VERONESE GRAM.**  The atom
matrices of a family are linearly independent exactly when the Gram of their Frobenius
pairings is positive definite.  This holds at every size and every rank. -/
theorem stressFree_iff_posDef_veroneseAtomGram {size rank : ℕ}
    (atom : Fin size → Fin rank → ℝ) :
    (∀ stressCoeff : Fin size → ℝ,
        (∑ label, stressCoeff label • atomMatrix (atom label)) = 0 → stressCoeff = 0)
      ↔ (veroneseAtomGram atom).PosDef := by
  constructor
  · intro hstressFree
    refine Matrix.posDef_iff_dotProduct_mulVec.mpr ⟨isHermitian_veroneseAtomGram atom, ?_⟩
    intro probe hprobe
    have hstar : star probe = probe := rfl
    rw [hstar, dotProduct_veroneseAtomGram_mulVec]
    rcases lt_or_eq_of_le
      (frobeniusNormSq_nonneg (∑ label, probe label • atomMatrix (atom label))) with
      hpositive | hzero
    · exact hpositive
    · exact absurd (hstressFree probe (eq_zero_of_frobeniusNormSq_eq_zero hzero.symm)) hprobe
  · intro hposDef stressCoeff hvanish
    by_contra hnonzero
    have hpositive := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hnonzero
    have hstar : star stressCoeff = stressCoeff := rfl
    rw [hstar, dotProduct_veroneseAtomGram_mulVec, hvanish, frobeniusNormSq_zero_matrix]
      at hpositive
    exact lt_irrefl 0 hpositive

/-- Positive definiteness of the raw Veronese Gram is one STRICT determinant inequality,
because the matrix is positive semidefinite at every atom family. -/
theorem posDef_veroneseAtomGram_iff_det_pos {size rank : ℕ} (atom : Fin size → Fin rank → ℝ) :
    (veroneseAtomGram atom).PosDef ↔ 0 < (veroneseAtomGram atom).det := by
  constructor
  · exact fun hposDef => hposDef.det_pos
  · intro hdetPos
    exact (posSemidef_veroneseAtomGram atom).posDef_iff_det_ne_zero.mpr (ne_of_gt hdetPos)

/-- **THE CRITERION IN ITS SHARPEST FORM.**  Stress-freeness of an atom family is the
single strict inequality `0 < det (veroneseAtomGram atom)`. -/
theorem stressFree_iff_det_veroneseAtomGram_pos {size rank : ℕ}
    (atom : Fin size → Fin rank → ℝ) :
    (∀ stressCoeff : Fin size → ℝ,
        (∑ label, stressCoeff label • atomMatrix (atom label)) = 0 → stressCoeff = 0)
      ↔ 0 < (veroneseAtomGram atom).det :=
  (stressFree_iff_posDef_veroneseAtomGram atom).trans (posDef_veroneseAtomGram_iff_det_pos atom)

/-! ## Part two, section 2.  The symmetric weight system

Parseval contracted against each atom is one symmetric linear system in the weight.  The
system needs no hypothesis, and the Gram of section one is its matrix. -/

/-- **THE SYMMETRIC WEIGHT SYSTEM.**  At EVERY weighted design,
`veroneseAtomGram *v weight = leverage`.  Parseval is the only input. -/
theorem veroneseAtomGram_mulVec_weight (design : WeightedDesign m k) :
    veroneseAtomGram design.atom *ᵥ design.weight
      = fun label => leverageOf (design.atom label) := by
  funext label
  have hrow : (veroneseAtomGram design.atom *ᵥ design.weight) label
      = ∑ other, design.weight other * (design.atom other ⬝ᵥ design.atom label) ^ 2 := by
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun other _ => ?_
    rw [veroneseAtomGram_apply, dotProduct_comm (design.atom label) (design.atom other)]
    ring
  rw [hrow, sum_weight_mul_sq_dotProduct design (design.atom label), ← leverageOf_eq_dotProduct]

/-- **THE QUADRATIC CONSERVATION LAW.**  The weight vector has raw Veronese energy
exactly the rank, at every design.  The two readings agree: the left side is the
Frobenius energy of Parseval, and the right side is the total share. -/
theorem dotProduct_weight_veroneseAtomGram_mulVec_weight (design : WeightedDesign m k) :
    design.weight ⬝ᵥ (veroneseAtomGram design.atom *ᵥ design.weight) = (k : ℝ) := by
  rw [dotProduct_veroneseAtomGram_mulVec, design.isParseval, frobeniusNormSq, frobeniusInner]
  have hrow : ∀ rowIndex : Fin k,
      ∑ colIndex, (1 : Matrix (Fin k) (Fin k) ℝ) rowIndex colIndex
          * (1 : Matrix (Fin k) (Fin k) ℝ) rowIndex colIndex = 1 := by
    intro rowIndex
    simp [Matrix.one_apply]
  rw [Finset.sum_congr rfl fun rowIndex _ => hrow rowIndex, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- **WEIGHT RIGIDITY ON THE STRESS-FREE STRATUM.**  Two designs with the SAME atoms,
one of them stress-free, have the same weights.  There is no weight freedom on the
stratum: the atoms determine the weight. -/
theorem weight_eq_of_stressFree_of_atom_eq {designLeft designRight : WeightedDesign m k}
    (hstressFree : ∀ stressCoeff : Fin m → ℝ,
      (∑ label, stressCoeff label • atomMatrix (designLeft.atom label)) = 0 → stressCoeff = 0)
    (hatom : designLeft.atom = designRight.atom) : designLeft.weight = designRight.weight := by
  have hvanish : (∑ label, (designLeft.weight label - designRight.weight label)
      • atomMatrix (designLeft.atom label)) = 0 := by
    have hsplit : (∑ label, (designLeft.weight label - designRight.weight label)
          • atomMatrix (designLeft.atom label))
        = (∑ label, designLeft.weight label • atomMatrix (designLeft.atom label))
          - ∑ label, designRight.weight label • atomMatrix (designRight.atom label) := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun label _ => by rw [sub_smul, hatom]
    rw [hsplit, designLeft.isParseval, designRight.isParseval, sub_self]
  have hdiff := hstressFree _ hvanish
  funext label
  have hlabel := congrFun hdiff label
  simp only [Pi.zero_apply] at hlabel
  linarith [hlabel]

/-- **THE SYSTEM HAS ONE SOLUTION ON THE STRATUM.**  A positive definite raw Veronese
Gram makes the weight the unique solution of `M *v candidate = leverage`. -/
theorem eq_weight_of_posDef_of_mulVec_eq_leverage (design : WeightedDesign m k)
    (hposDef : (veroneseAtomGram design.atom).PosDef) {candidate : Fin m → ℝ}
    (hsolves : veroneseAtomGram design.atom *ᵥ candidate
      = fun label => leverageOf (design.atom label)) :
    candidate = design.weight := by
  have hdifference : veroneseAtomGram design.atom *ᵥ (candidate - design.weight) = 0 := by
    rw [Matrix.mulVec_sub, hsolves, veroneseAtomGram_mulVec_weight design, sub_self]
  by_contra hnonzero
  have hnotZero : candidate - design.weight ≠ 0 := sub_ne_zero.mpr hnonzero
  have hpositive := (Matrix.posDef_iff_dotProduct_mulVec.mp hposDef).2 hnotZero
  rw [hdifference, dotProduct_zero] at hpositive
  exact lt_irrefl 0 hpositive

/-- **THE WEIGHT, IN CLOSED FORM.**  On the stress-free stratum the weight is
`M^{-1} *v leverage`.  The weight variable leaves every statement about the stratum. -/
theorem weight_eq_veroneseAtomGram_inv_mulVec_leverage (design : WeightedDesign m k)
    (hstressFree : ∀ stressCoeff : Fin m → ℝ,
      (∑ label, stressCoeff label • atomMatrix (design.atom label)) = 0 → stressCoeff = 0) :
    design.weight
      = (veroneseAtomGram design.atom)⁻¹ *ᵥ fun label => leverageOf (design.atom label) := by
  have hposDef := (stressFree_iff_posDef_veroneseAtomGram design.atom).mp hstressFree
  have hunit : IsUnit (veroneseAtomGram design.atom).det :=
    isUnit_iff_ne_zero.mpr (ne_of_gt hposDef.det_pos)
  rw [← veroneseAtomGram_mulVec_weight design, Matrix.mulVec_mulVec,
    Matrix.nonsing_inv_mul _ hunit, Matrix.one_mulVec]

/-- **THE FIRST CLOSED SCALAR LAW.**  On the stress-free stratum the leverage vector has
inverse-Gram norm exactly the rank.  The weight does not occur. -/
theorem dotProduct_leverage_veroneseAtomGram_inv_leverage (design : WeightedDesign m k)
    (hstressFree : ∀ stressCoeff : Fin m → ℝ,
      (∑ label, stressCoeff label • atomMatrix (design.atom label)) = 0 → stressCoeff = 0) :
    (fun label => leverageOf (design.atom label))
        ⬝ᵥ ((veroneseAtomGram design.atom)⁻¹
          *ᵥ fun label => leverageOf (design.atom label)) = (k : ℝ) := by
  rw [← weight_eq_veroneseAtomGram_inv_mulVec_leverage design hstressFree,
    dotProduct_comm (fun label => leverageOf (design.atom label)) design.weight]
  exact sum_weight_mul_leverage design

/-- **THE SECOND CLOSED SCALAR LAW.**  The all-ones vector against the same inverse
image is one.  This is `weight_sum_one` after the weight leaves. -/
theorem dotProduct_one_veroneseAtomGram_inv_leverage (design : WeightedDesign m k)
    (hstressFree : ∀ stressCoeff : Fin m → ℝ,
      (∑ label, stressCoeff label • atomMatrix (design.atom label)) = 0 → stressCoeff = 0) :
    (fun _ => (1 : ℝ))
        ⬝ᵥ ((veroneseAtomGram design.atom)⁻¹
          *ᵥ fun label => leverageOf (design.atom label)) = 1 := by
  rw [← weight_eq_veroneseAtomGram_inv_mulVec_leverage design hstressFree]
  show ∑ label, (1 : ℝ) * design.weight label = 1
  simp only [one_mul]
  exact design.weight_sum_one

/-! ## Part two, section 3.  A Cauchy inequality on the Gram, and its design reading -/

/-- A real quadratic that stays nonnegative has a nonpositive discriminant. -/
private theorem sq_le_mul_of_quadratic_nonneg {leftEnergy crossEnergy rightEnergy : ℝ}
    (hnonneg : ∀ scale : ℝ,
      0 ≤ leftEnergy + 2 * scale * crossEnergy + scale ^ 2 * rightEnergy)
    (hrightNonneg : 0 ≤ rightEnergy) :
    crossEnergy ^ 2 ≤ leftEnergy * rightEnergy := by
  rcases eq_or_lt_of_le hrightNonneg with hzero | hpositive
  · have hcrossZero : crossEnergy = 0 := by
      by_contra hnonzero
      have hpick := hnonneg (-(leftEnergy + 1) / (2 * crossEnergy))
      rw [← hzero] at hpick
      simp only [mul_zero, add_zero] at hpick
      have hclear : 2 * (-(leftEnergy + 1) / (2 * crossEnergy)) * crossEnergy
          = -(leftEnergy + 1) := by
        field_simp
      linarith [hpick, hclear]
    rw [hcrossZero, ← hzero]
    norm_num
  · have hpick := hnonneg (-crossEnergy / rightEnergy)
    have hkey : leftEnergy + 2 * (-crossEnergy / rightEnergy) * crossEnergy
          + (-crossEnergy / rightEnergy) ^ 2 * rightEnergy
        = leftEnergy - crossEnergy ^ 2 / rightEnergy := by
      field_simp
      ring
    rw [hkey] at hpick
    have hdiv : crossEnergy ^ 2 / rightEnergy ≤ leftEnergy := by linarith [hpick]
    rwa [div_le_iff₀ hpositive] at hdiv

/-- The Cauchy inequality for a positive semidefinite form, by the discriminant of the
nonnegative quadratic `t |-> (left + t * right)^T M (left + t * right)`. -/
theorem sq_dotProduct_mulVec_le_of_posSemidef {size : ℕ}
    {form : Matrix (Fin size) (Fin size) ℝ} (hform : form.PosSemidef)
    (leftVec rightVec : Fin size → ℝ) :
    (leftVec ⬝ᵥ (form *ᵥ rightVec)) ^ 2
      ≤ (leftVec ⬝ᵥ (form *ᵥ leftVec)) * (rightVec ⬝ᵥ (form *ᵥ rightVec)) := by
  have htranspose : formᵀ = form := by
    refine Matrix.ext fun rowIndex colIndex => ?_
    have hstarEntry := congrFun (congrFun hform.1 rowIndex) colIndex
    simpa only [Matrix.conjTranspose_apply, star_trivial, Matrix.transpose_apply]
      using hstarEntry
  have hswap : ∀ probeVec : Fin size → ℝ, probeVec ᵥ* form = form *ᵥ probeVec := by
    intro probeVec
    rw [← htranspose, Matrix.vecMul_transpose, htranspose]
  have hsymmetric : ∀ firstVec secondVec : Fin size → ℝ,
      firstVec ⬝ᵥ (form *ᵥ secondVec) = secondVec ⬝ᵥ (form *ᵥ firstVec) := by
    intro firstVec secondVec
    rw [Matrix.dotProduct_mulVec, hswap firstVec]
    exact dotProduct_comm _ _
  refine sq_le_mul_of_quadratic_nonneg (fun scale => ?_)
    ((Matrix.posSemidef_iff_dotProduct_mulVec.mp hform).2 rightVec)
  have hquad := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hform).2 (leftVec + scale • rightVec)
  have hstar : star (leftVec + scale • rightVec) = leftVec + scale • rightVec := rfl
  rw [hstar] at hquad
  have hexpand : (leftVec + scale • rightVec) ⬝ᵥ (form *ᵥ (leftVec + scale • rightVec))
      = (leftVec ⬝ᵥ (form *ᵥ leftVec))
        + 2 * scale * (leftVec ⬝ᵥ (form *ᵥ rightVec))
        + scale ^ 2 * (rightVec ⬝ᵥ (form *ᵥ rightVec)) := by
    simp only [Matrix.mulVec_add, Matrix.mulVec_smul, add_dotProduct, dotProduct_add,
      dotProduct_smul, smul_dotProduct, smul_eq_mul]
    rw [hsymmetric rightVec leftVec]
    ring
  rw [hexpand] at hquad
  exact hquad

/-- **TOTAL LEVERAGE AGAINST TOTAL SQUARED CORRELATION.**  At every weighted design the
square of the total leverage is at most the rank times the full raw Veronese sum.  No
stress-freeness, no uniformity, no nondegeneracy. -/
theorem sq_sum_leverage_le_rank_mul_sum_veroneseAtomGram (design : WeightedDesign m k) :
    (∑ label, leverageOf (design.atom label)) ^ 2
      ≤ (k : ℝ) * ∑ firstLabel, ∑ secondLabel,
          veroneseAtomGram design.atom firstLabel secondLabel := by
  have hcauchy := sq_dotProduct_mulVec_le_of_posSemidef
    (posSemidef_veroneseAtomGram design.atom) (fun _ => (1 : ℝ)) design.weight
  rw [veroneseAtomGram_mulVec_weight design] at hcauchy
  have hweightLeverage :
      design.weight ⬝ᵥ (fun label => leverageOf (design.atom label)) = (k : ℝ) :=
    sum_weight_mul_leverage design
  rw [hweightLeverage] at hcauchy
  have hleftSide : (fun _ => (1 : ℝ)) ⬝ᵥ (fun label => leverageOf (design.atom label))
      = ∑ label, leverageOf (design.atom label) := by
    rw [dotProduct]
    exact Finset.sum_congr rfl fun label _ => one_mul _
  have hgramSide : (fun _ => (1 : ℝ))
      ⬝ᵥ (veroneseAtomGram design.atom *ᵥ fun _ => (1 : ℝ))
      = ∑ firstLabel, ∑ secondLabel,
          veroneseAtomGram design.atom firstLabel secondLabel := by
    rw [dotProduct]
    refine Finset.sum_congr rfl fun firstLabel _ => ?_
    rw [one_mul, Matrix.mulVec, dotProduct]
    exact Finset.sum_congr rfl fun secondLabel _ => mul_one _
  rw [hleftSide, hgramSide] at hcauchy
  linarith [hcauchy, mul_comm ((k : ℝ))
    (∑ firstLabel, ∑ secondLabel, veroneseAtomGram design.atom firstLabel secondLabel)]

/-! ## Part two, section 4.  The `(6,3)` cell

The criterion of section one, read at the open cell, and bridged to the landed grid
elimination of `Gtz/Wave/VeroneseWeightElimination.lean`. -/

/-- **STRESS-FREENESS AT `(6,3)` IS ONE SIX-BY-SIX DETERMINANT INEQUALITY.**  The
predicate `Gtz.IsStressFreeDesign` quantifies over all stress vectors.  It is the single
strict inequality `0 < det (veroneseAtomGram design.atom)`. -/
theorem isStressFreeDesign_iff_det_veroneseAtomGram_pos (design : WeightedDesign 6 3) :
    IsStressFreeDesign design ↔ 0 < (veroneseAtomGram design.atom).det :=
  stressFree_iff_det_veroneseAtomGram_pos design.atom

/-- **THE BRIDGE TO THE GRID ELIMINATION.**  The symmetric criterion of this module and
the landed criterion `Gtz.stressFree_iff_veroneseGrid_det_ne_zero` cut out the SAME set
of atom families.  The Gram form carries a sign and the grid form does not. -/
theorem det_veroneseAtomGram_pos_iff_det_veroneseGrid_ne_zero
    (atomFamily : Fin 6 → Fin 3 → ℝ) :
    0 < (veroneseAtomGram atomFamily).det ↔ (veroneseGrid atomFamily).det ≠ 0 :=
  (stressFree_iff_det_veroneseAtomGram_pos atomFamily).symm.trans
    (stressFree_iff_veroneseGrid_det_ne_zero atomFamily)

/-- The weight of a stress-free `(6,3)` design, read off the atoms alone. -/
noncomputable def gramSolvedWeight (atomFamily : Fin 6 → Fin 3 → ℝ) : Fin 6 → ℝ :=
  (veroneseAtomGram atomFamily)⁻¹ *ᵥ fun label => leverageOf (atomFamily label)

theorem gramSolvedWeight_eq_weight (design : WeightedDesign 6 3)
    (hstressFree : IsStressFreeDesign design) :
    gramSolvedWeight design.atom = design.weight :=
  (weight_eq_veroneseAtomGram_inv_mulVec_leverage design hstressFree).symm

/-- **THE WEIGHT-FREE FORM OF THE OPEN `(6,3)` OBLIGATION.**  The open
`Gtz.StressFreeHingeHoldsSixThree` is EQUIVALENT to a statement about eighteen atom
coordinates in which the weight variable does not occur: every atom family whose raw
Veronese determinant is positive, whose Gram-solved weight is positive and normalized,
and which resolves the identity, carries a strictly dominating triple.

This is a REDUCTION of the obligation and not a proof of it.  Both Props stay open.  The
content is that the six weight coordinates are eliminated, and that the stress-free side
condition becomes one strict determinant inequality with a KNOWN sign. -/
theorem stressFreeHingeHoldsSixThree_iff_gramAtomFamilyStrictTriple :
    StressFreeHingeHoldsSixThree
      ↔ ∀ atomFamily : Fin 6 → Fin 3 → ℝ,
          0 < (veroneseAtomGram atomFamily).det →
          (∀ label, 0 < gramSolvedWeight atomFamily label) →
          (∑ label, gramSolvedWeight atomFamily label) = 1 →
          (∑ label, gramSolvedWeight atomFamily label • atomMatrix (atomFamily label)) = 1 →
          ∃ triple : Finset (Fin 6), triple.card = 3
            ∧ ((∑ label ∈ triple, atomMatrix (atomFamily label))
                - (1 : Matrix (Fin 3) (Fin 3) ℝ)).PosDef := by
  constructor
  · intro hinge atomFamily hdet hpositive hsum hparseval
    obtain ⟨triple, hcard, hposDef⟩ :=
      exists_posDef_triple_of_stressFreeHinge hinge
        { atom := atomFamily, weight := gramSolvedWeight atomFamily,
          weight_pos := hpositive, weight_sum_one := hsum, isParseval := hparseval }
        ((stressFree_iff_det_veroneseAtomGram_pos atomFamily).mpr hdet)
    exact ⟨triple, hcard, by simpa only [subsetSum] using hposDef⟩
  · intro hfamily design hstressFree htie
    have hdet : 0 < (veroneseAtomGram design.atom).det :=
      (stressFree_iff_det_veroneseAtomGram_pos design.atom).mp hstressFree
    have hweight : gramSolvedWeight design.atom = design.weight :=
      gramSolvedWeight_eq_weight design hstressFree
    obtain ⟨triple, hcard, hposDef⟩ := hfamily design.atom hdet
      (by rw [hweight]; exact design.weight_pos)
      (by rw [hweight]; exact design.weight_sum_one)
      (by rw [hweight]; exact design.isParseval)
    exact absurd (show (subsetSum design triple - 1).PosDef by
      simpa only [subsetSum] using hposDef) (htie.2 triple hcard)

end Gtz
