import Skeleton.SixThreeConditional

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The endgame assembly

This module pins the composition map of the campaign in kernel-checked form, so
the day a cell lane lands its residual, the capstone at every rank composes in
one application and not in a session.

## The map

The registry holds seven obligations.  Five are the rank-three class residuals
and two are the hinges.  The `(6,3)` cell splits them:

* IF `Gtz.GtzWeighted 6 3` lands, THEN `Gtz.GtzWeightedAll` at every rank needs
  EXACTLY the two hinges, `Skeleton.obligationSubThresholdBandHinge` and
  `Skeleton.obligationThresholdCellHingeRankFourAndUp`, and none of the five
  class residuals.  Section 1 states this composition once for each residual
  that the active lanes attack, and each theorem carries a
  `#gtz_frontier_exactly` gate that the kernel re-proves on every build.
* IF the polar nine-bundle residual `Gtz.PolarTiltSelectionFloor` lands across
  the sharp windows of every rank, THEN the capstone needs ZERO obligations.
  Section 2 proves that route in full, on the shared rung engine
  `closesSharpWindow_ofClosures` and the closed reach obligation.
* IF the cell lands by rank-three tools AND the polar residual lands only at
  rank four and up, THEN the capstone still needs ZERO obligations.  Section 3
  proves that hybrid, which is the likeliest actual endgame.

## The shared reduction across two class residuals

Section 5 records a structural fact about the registry that no earlier module
states.  Two of the five class residuals reduce, through their own landed
producers, to ONE scalar criterion: at a live pair of a design, some third label
gives a positive `Gtz.discriminantTie`.  The K4 residual reduces to it through
`Gtz.kFourKnifeBandRefined_of_livePairCompletes` and the `U(3,6)` residual
through `Gtz.baseTripleTightLineFreeOffConicWeakToStrict_of_heavyBaseTripleShareLivePairTie`.
The engine under both is `Gtz.exists_posDef_cardThree_of_forall_livePair`, which
is PATTERN-GENERIC and size-generic, so the same criterion also reaches the two
chartless line residuals with the pattern hypothesis unused.  Section 5 spends
that observation where it is cheapest and exactly checkable: ONE Prop that
retires the two chartless residuals TOGETHER, with a kernel gate on the count.

## Why the compositions are safe to bank

Every theorem below is an implication whose hypotheses are landed named Props
and whose bridges are landed `Gtz` theorems.  No axiom is added, the registry is
untouched, and the gates of `Skeleton.Report` do not move.  A lane that proves
its residual converts its own capstone by one application of the matching
theorem of this file.
-/

namespace Skeleton.GeneralRank

/-! ## 1. The cell compositions, one per active frontier residual

Each theorem reaches exactly the two hinge obligations, and the gates of
section 4 make the kernel check that count on every build.  The residuals below
are the current narrowest named targets of the three cell lanes. -/

/-- The atom flagship.  The triple ceiling closes the cell with no side
hypothesis, thus it closes every rank modulo the two hinges. -/
theorem skeletonGtzWeightedAllEveryRank_ofAtomTripleCeiling
    (hceiling : Gtz.AtomTripleCeilingClosed) : ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree
    (Gtz.gtzWeighted_six_three_of_atomTripleCeiling hceiling)

/-- The blocked pair form of the atom residue, the lane's live attack shape. -/
theorem skeletonGtzWeightedAllEveryRank_ofBlockedPair
    (hblocked : Gtz.AtomBlockedPairClosed) : ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree
    (Gtz.gtzWeighted_six_three_of_blockedPair hblocked)

/-- The pivot pair form, the deflated Sylvester test at one pivot. -/
theorem skeletonGtzWeightedAllEveryRank_ofPivotPair
    (hpivot : Gtz.AtomPivotPairClosed) : ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree
    (Gtz.gtzWeighted_six_three_of_pivotPair hpivot)

/-- The mass-one boundary form, the non-strict selection theorem with ties. -/
theorem skeletonGtzWeightedAllEveryRank_ofAtomTripleBoundary
    (hboundary : Gtz.AtomTripleBoundaryClosed) : ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree
    (Gtz.gtzWeighted_six_three_of_atomTripleBoundary hboundary)

/-- The polar nine-bundle residual at the deciding cell. -/
theorem skeletonGtzWeightedAllEveryRank_ofPolarTiltFloorCell
    (htilt : Gtz.PolarTiltSelectionFloor 6 3) : ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree
    (Gtz.gtzWeighted_six_three_of_polarTiltFloor htilt)

/-- The heavy shadow target of the polar lane. -/
theorem skeletonGtzWeightedAllEveryRank_ofPolarHeavyShadowSelection
    (hheavy : Gtz.PolarHeavyShadowSelection 6) : ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree
    (Gtz.gtzWeighted_six_three_of_polarHeavyShadowSelection hheavy)

/-- The shadow budget target of the polar lane. -/
theorem skeletonGtzWeightedAllEveryRank_ofPolarShadowBudgetSelection
    (hbudget : Gtz.PolarShadowBudgetSelection 6) : ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree
    (Gtz.gtzWeighted_six_three_of_polarShadowBudgetSelection hbudget)

/-- The wrap budget target of the polar lane. -/
theorem skeletonGtzWeightedAllEveryRank_ofPolarWrapBudgetSelection
    (hwrap : Gtz.PolarWrapBudgetSelection 6) : ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree
    (Gtz.gtzWeighted_six_three_of_polarWrapBudgetSelection hwrap)

/-- The gap determinant target of the polar lane. -/
theorem skeletonGtzWeightedAllEveryRank_ofPolarGapSelection
    (hgap : Gtz.PolarGapSelection 6) : ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree
    (Gtz.gtzWeighted_six_three_of_polarGapSelection hgap)

/-- The wrapping gap target of the polar lane. -/
theorem skeletonGtzWeightedAllEveryRank_ofPolarWrapGapSelection
    (hwrap : Gtz.PolarWrapGapSelection 6) : ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree
    (Gtz.gtzWeighted_six_three_of_polarWrapGapSelection hwrap)

/-- The rank spine.  Three of the eleven assembly closures are theorems
(`Gtz.rankFourKFourClosed_holds`, `Gtz.rankFourCycleIndependentClosed_holds`,
`Gtz.rankFourBothParallelClosed_holds`), thus the spine composition takes the
EIGHT open closures only. -/
theorem skeletonGtzWeightedAllEveryRank_ofUpperClosures
    (hfourOne : Gtz.RankFourSupportTwoClosed)
    (hfourTwo : Gtz.RankFourSharedPrivateClosed)
    (hfiveOne : Gtz.RankFiveSupportTwoClosed)
    (hfiveTwo : Gtz.RankFiveSharedPrivateClosed)
    (hfiveDense : Gtz.RankFiveDenseClosed)
    (hsixOne : Gtz.RankSixSupportTwoClosed)
    (hsixTwo : Gtz.RankSixSharedPrivateClosed)
    (hsixDense : Gtz.RankSixDenseClosed) : ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree
    (Gtz.gtzWeighted_six_three_of_closures hfourOne hfourTwo
      Gtz.rankFourKFourClosed_holds Gtz.rankFourCycleIndependentClosed_holds
      Gtz.rankFourBothParallelClosed_holds hfiveOne hfiveTwo hfiveDense
      hsixOne hsixTwo hsixDense)

/-- The 1997 statement off the atom flagship, as the sample original-form
composition.  Every other residual converts the same way through
`skeletonGtzOriginalEveryRank_ofSixThree`. -/
theorem skeletonGtzOriginalEveryRank_ofAtomTripleCeiling
    (hceiling : Gtz.AtomTripleCeilingClosed) :
    ∀ size rank : ℕ, 0 < size → Gtz.GtzOriginal size rank :=
  skeletonGtzOriginalEveryRank_ofSixThree
    (Gtz.gtzWeighted_six_three_of_atomTripleCeiling hceiling)

/-! ## 2. The zero-obligation route: the polar residual across the windows

The reach obligation is closed at every rank, thus the ladder needs only the
hinge.  The polar nine-bundle residual supplies the hinge at every window cell,
with the free bundles manufactured from tie-ness by the landed suppliers.  The
capstone below therefore reaches NO registry obligation, and the gate of
section 4 makes the kernel prove that. -/

/-- The polar supply across the sharp windows: the nine-bundle residual at every
window cell of every rank at least three.  This is the shape the polar lane's
general-rank program produces, in the vocabulary of
`Gtz.sharpWindowHinge_of_polarTiltFloor`. -/
def PolarFloorAcrossWindows : Prop :=
  ∀ rank size : ℕ, 3 ≤ rank → 2 * rank ≤ size → size ≤ Gtz.thresholdSize rank →
    Gtz.PolarTiltSelectionFloor size rank

/-- The hinge closure of one rank, off the window supply. -/
theorem hingeHoldsAcrossSharpWindow_ofPolarFloor {rank : ℕ}
    (hrankAtLeastThree : 3 ≤ rank) (hpredecessorRank : Gtz.GtzWeightedAll (rank - 1))
    (hfloor : PolarFloorAcrossWindows) : HingeHoldsAcrossSharpWindow rank := by
  rintro size ⟨hwindowFloor, hceiling⟩ _hpredecessorCell
  have hceilingSize : size ≤ Gtz.thresholdSize rank := hceiling
  exact Gtz.hingeHoldsAtSize_of_polarTiltFloor (by omega) hpredecessorRank (by omega)
    (hfloor rank size hrankAtLeastThree hwindowFloor hceilingSize)

/-- The induction step off the window supply.  Two branches: the corank floor
below rank three, the ladder from rank three on.  Rank three needs no special
case, because the supply covers its single window cell, size six. -/
theorem uniformInductionStep_ofPolarFloor (hfloor : PolarFloorAcrossWindows) (rank : ℕ)
    (hsmallerRanksClosed : ∀ smaller : ℕ, smaller < rank → Gtz.GtzWeightedAll smaller) :
    Gtz.GtzWeightedAll rank := by
  refine Gtz.gtzWeightedAll_of_veroneseTop rank ?_
  rcases Nat.lt_or_ge rank 3 with hrankSmall | hrankLarge
  · exact closesThresholdCell_ofSmallRank (by omega)
  · have hpredecessorRank := hsmallerRanksClosed (rank - 1) (by omega)
    exact closesSharpWindow_ofClosures hrankLarge
      (hingeHoldsAcrossSharpWindow_ofPolarFloor hrankLarge hpredecessorRank hfloor)
      (anchorReachesAcrossSharpWindow_ofRegistry hrankLarge) hpredecessorRank
      (thresholdCell rank) ⟨twoRank_le_thresholdCell hrankLarge, le_refl _⟩

/-- **THE ZERO-OBLIGATION CAPSTONE.**  Weighted GTZ at every rank and every
size, from the polar window supply and nothing else. -/
theorem skeletonGtzWeightedAllEveryRank_ofPolarFloor (hfloor : PolarFloorAcrossWindows) :
    ∀ rank : ℕ, Gtz.GtzWeightedAll rank := by
  have hclosedUpTo : ∀ bound rank : ℕ, rank ≤ bound → Gtz.GtzWeightedAll rank := by
    intro bound
    induction bound with
    | zero =>
        intro rank hrankBound
        exact uniformInductionStep_ofPolarFloor hfloor rank
          (fun smaller hsmaller => absurd hsmaller (by omega))
    | succ previousBound closedUpToPrevious =>
        intro rank hrankBound
        exact uniformInductionStep_ofPolarFloor hfloor rank
          (fun smaller hsmaller => closedUpToPrevious smaller (by omega))
  exact fun rank => hclosedUpTo rank rank (le_refl rank)

/-- The 1997 statement at every rank, off the polar window supply alone. -/
theorem skeletonGtzOriginalEveryRank_ofPolarFloor (hfloor : PolarFloorAcrossWindows) :
    ∀ size rank : ℕ, 0 < size → Gtz.GtzOriginal size rank :=
  fun size rank hsizePositive =>
    (Gtz.gtzWeightedAll_iff_forall_gtzOriginal rank).mp
      (skeletonGtzWeightedAllEveryRank_ofPolarFloor hfloor rank) size hsizePositive

/-! ## 3. The hybrid endgame: the cell plus the high-rank polar supply

The likeliest landing order: the `(6,3)` cell closes by rank-three tools, and
the polar program closes the windows at rank four and up SUBSEQUENTLY.  The
hybrid needs the supply only there, and it still reaches no obligation. -/

/-- The polar supply at rank four and up only. -/
def PolarFloorAcrossHighWindows : Prop :=
  ∀ rank size : ℕ, 4 ≤ rank → 2 * rank ≤ size → size ≤ Gtz.thresholdSize rank →
    Gtz.PolarTiltSelectionFloor size rank

/-- The full supply restricts to the high supply. -/
theorem polarFloorAcrossHighWindows_ofAcrossWindows (hfloor : PolarFloorAcrossWindows) :
    PolarFloorAcrossHighWindows :=
  fun rank size hrank hlow hhigh => hfloor rank size (by omega) hlow hhigh

/-- The hinge closure at rank four and up, off the high supply. -/
theorem hingeHoldsAcrossSharpWindow_ofPolarFloorHigh {rank : ℕ}
    (hrankAtLeastFour : 4 ≤ rank) (hpredecessorRank : Gtz.GtzWeightedAll (rank - 1))
    (hfloor : PolarFloorAcrossHighWindows) : HingeHoldsAcrossSharpWindow rank := by
  rintro size ⟨hwindowFloor, hceiling⟩ _hpredecessorCell
  have hceilingSize : size ≤ Gtz.thresholdSize rank := hceiling
  exact Gtz.hingeHoldsAtSize_of_polarTiltFloor (by omega) hpredecessorRank (by omega)
    (hfloor rank size hrankAtLeastFour hwindowFloor hceilingSize)

/-- The hybrid induction step.  Three branches: the corank floor, the hypothesis
cell at rank three, the ladder off the high supply at rank four and up. -/
theorem uniformInductionStep_ofSixThree_ofPolarFloorHigh
    (hcellSixThree : Gtz.GtzWeighted 6 3) (hfloor : PolarFloorAcrossHighWindows) (rank : ℕ)
    (hsmallerRanksClosed : ∀ smaller : ℕ, smaller < rank → Gtz.GtzWeightedAll smaller) :
    Gtz.GtzWeightedAll rank := by
  refine Gtz.gtzWeightedAll_of_veroneseTop rank ?_
  rcases Nat.lt_or_ge rank 3 with hrankSmall | hrankAtLeastThree
  · exact closesThresholdCell_ofSmallRank (by omega)
  · rcases Nat.lt_or_ge rank 4 with hrankBelowFour | hrankAtLeastFour
    · have hrankIsThree : rank = 3 := by omega
      subst hrankIsThree
      exact closesThresholdCell_three_ofSixThree hcellSixThree
    · have hpredecessorRank := hsmallerRanksClosed (rank - 1) (by omega)
      exact closesSharpWindow_ofClosures (by omega)
        (hingeHoldsAcrossSharpWindow_ofPolarFloorHigh hrankAtLeastFour hpredecessorRank hfloor)
        (anchorReachesAcrossSharpWindow_ofRegistry (by omega)) hpredecessorRank
        (thresholdCell rank) ⟨twoRank_le_thresholdCell (by omega), le_refl _⟩

/-- **THE HYBRID CAPSTONE.**  Weighted GTZ at every rank from the cell and the
high-rank polar supply, with no obligation. -/
theorem skeletonGtzWeightedAllEveryRank_ofSixThree_ofPolarFloorHigh
    (hcellSixThree : Gtz.GtzWeighted 6 3) (hfloor : PolarFloorAcrossHighWindows) :
    ∀ rank : ℕ, Gtz.GtzWeightedAll rank := by
  have hclosedUpTo : ∀ bound rank : ℕ, rank ≤ bound → Gtz.GtzWeightedAll rank := by
    intro bound
    induction bound with
    | zero =>
        intro rank hrankBound
        exact uniformInductionStep_ofSixThree_ofPolarFloorHigh hcellSixThree hfloor rank
          (fun smaller hsmaller => absurd hsmaller (by omega))
    | succ previousBound closedUpToPrevious =>
        intro rank hrankBound
        exact uniformInductionStep_ofSixThree_ofPolarFloorHigh hcellSixThree hfloor rank
          (fun smaller hsmaller => closedUpToPrevious smaller (by omega))
  exact fun rank => hclosedUpTo rank rank (le_refl rank)

/-- The 1997 statement at every rank, off the hybrid. -/
theorem skeletonGtzOriginalEveryRank_ofSixThree_ofPolarFloorHigh
    (hcellSixThree : Gtz.GtzWeighted 6 3) (hfloor : PolarFloorAcrossHighWindows) :
    ∀ size rank : ℕ, 0 < size → Gtz.GtzOriginal size rank :=
  fun size rank hsizePositive =>
    (Gtz.gtzWeightedAll_iff_forall_gtzOriginal rank).mp
      (skeletonGtzWeightedAllEveryRank_ofSixThree_ofPolarFloorHigh hcellSixThree hfloor rank)
      size hsizePositive

/-! ## 4. The gates

Every cell composition must reach exactly the two hinges.  Both zero-obligation
routes must reach none.  A drift in either direction fails the build and names
the exact difference. -/

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofAtomTripleCeiling expects
  generalRankObligationNames

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofBlockedPair expects
  generalRankObligationNames

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofPivotPair expects
  generalRankObligationNames

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofAtomTripleBoundary expects
  generalRankObligationNames

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofPolarTiltFloorCell expects
  generalRankObligationNames

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofPolarHeavyShadowSelection expects
  generalRankObligationNames

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofPolarShadowBudgetSelection expects
  generalRankObligationNames

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofPolarWrapBudgetSelection expects
  generalRankObligationNames

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofPolarGapSelection expects
  generalRankObligationNames

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofPolarWrapGapSelection expects
  generalRankObligationNames

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofUpperClosures expects
  generalRankObligationNames

#gtz_frontier_exactly skeletonGtzOriginalEveryRank_ofAtomTripleCeiling expects
  generalRankObligationNames

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofPolarFloor expects noObligationName

#gtz_frontier_exactly skeletonGtzOriginalEveryRank_ofPolarFloor expects noObligationName

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofSixThree_ofPolarFloorHigh expects
  noObligationName

#gtz_frontier_exactly skeletonGtzOriginalEveryRank_ofSixThree_ofPolarFloorHigh expects
  noObligationName

/-! ## 5. The shared live-pair criterion of the two chartless residuals

`Gtz.exists_posDef_cardThree_of_forall_livePair` closes the conclusion of a
class residual from ONE scalar sign: a live pair whose third label makes
`Gtz.discriminantTie` positive.  A live pair always exists
(`Gtz.exists_isLivePair_rankThree`, unconditional at every size), and the
producer uses neither the line pattern nor the weak dominator.  So the criterion
below, stated once, discharges the two chartless class residuals TOGETHER.

The criterion is a genuine strengthening of each residual it discharges, not a
sharpening of it: the residual asks that SOME live pair complete, and the
criterion asks that EVERY live pair complete.  It is therefore recorded here as
a joint SUFFICIENT condition, in the same spirit as the polar window supply of
section 2, and it is NOT proposed as a registry entry.  What it buys is the
count: one statement in place of two axioms, with the kernel checking the
count. -/

/-- **The shared criterion.**  At every heavy `(6,3)` design that carries a
weakly dominating triple, every live pair completes to a positive discriminant
tie.  Six scalars, one sign, no pattern, no chart, no probe quantifier. -/
def LivePairCompletesOnHeavyWeak : Prop :=
  ∀ design : Gtz.WeightedDesign 6 3,
    (∀ label : Fin 6, 1 ≤ Gtz.leverageOf (design.atom label)) →
    (∃ dominator : Finset (Fin 6), dominator.card = 3 ∧ Gtz.Dominates design dominator) →
    ∀ pivotLabel pairFirst : Fin 6, pivotLabel ≠ pairFirst →
      Gtz.IsLivePair design pivotLabel pairFirst →
      ∃ pairSecond : Fin 6, pivotLabel ≠ pairSecond ∧ pairFirst ≠ pairSecond
        ∧ 0 < Gtz.discriminantTie design pivotLabel pairFirst pairSecond

/-- The criterion discharges the heavy weak-to-strict upgrade at EVERY line
pattern of six labels, because the producer never reads the pattern. -/
theorem patternHeavyWeakToStrict_ofLivePairCompletion (pattern : Gtz.LinePattern 6)
    (hcomplete : LivePairCompletesOnHeavyWeak) : Gtz.PatternHeavyWeakToStrict pattern :=
  fun design _hpattern hheavy hweak =>
    Gtz.exists_posDef_cardThree_of_forall_livePair design
      fun pivotLabel pairFirst hdistinct hlive =>
        hcomplete design hheavy hweak pivotLabel pairFirst hdistinct hlive

/-- The former one-line class statement, off the shared criterion.  The
registry now stores an equivalent, more deeply wired residual. -/
theorem heavyWeakToStrictOneLine_ofLivePairCompletion
    (hcomplete : LivePairCompletesOnHeavyWeak) :
    Gtz.PatternHeavyWeakToStrict (Gtz.lineFamilyPattern [[(0 : Fin 6), 1, 2]]) :=
  patternHeavyWeakToStrict_ofLivePairCompletion _ hcomplete

/-- The former two-meeting-lines class statement, off the SAME criterion.  The
registry now stores an equivalent four-transversal residual. -/
theorem heavyWeakToStrictTwoMeetingLines_ofLivePairCompletion
    (hcomplete : LivePairCompletesOnHeavyWeak) :
    Gtz.PatternHeavyWeakToStrict
      (Gtz.lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]]) :=
  patternHeavyWeakToStrict_ofLivePairCompletion _ hcomplete

/-- The `(6,3)` stress-free hinge with the two chartless residuals REPLACED by
the shared criterion.  The remaining three class residuals are unchanged, and
the assembly is the registry's own
`Gtz.stressFreeHingeHoldsSixThree_of_residualFamilies`. -/
theorem stressFreeHingeSixThree_ofLivePairCompletion
    (hcomplete : LivePairCompletesOnHeavyWeak) : Gtz.StressFreeHingeHoldsSixThree :=
  Gtz.stressFreeHingeHoldsSixThree_of_residualFamilies Gtz.linearSpaceListIsComplete_six
    (by
      intro lines hlines
      simp only [Gtz.stressFreeResidualFamiliesSix, List.mem_cons, List.not_mem_nil,
        or_false] at hlines
      rcases hlines with rfl | rfl | rfl | rfl | rfl
      · exact Skeleton.obligationTieFreeUThreeSix
      · exact Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree _
          (Gtz.stratumIsTieFree_of_tightDominatedCoverProperty
            (Gtz.patternTightDominatedCoverProperty_of_heavyWeakToStrict _
              (heavyWeakToStrictOneLine_ofLivePairCompletion hcomplete)))
      · exact Gtz.stressFreeStratumIsTieFree_of_stratumIsTieFree _
          (Gtz.stratumIsTieFree_of_tightDominatedCoverProperty
            (Gtz.patternTightDominatedCoverProperty_of_heavyWeakToStrict _
              (heavyWeakToStrictTwoMeetingLines_ofLivePairCompletion hcomplete)))
      · exact Skeleton.obligationTieFreeThreeLines
      · exact Skeleton.obligationTieFreeKFour)

/-- **THE COUNT, as a capstone.**  Rank three of the 1997 statement off the
shared criterion and the three remaining class residuals.  The gate below proves
that this root reaches exactly THREE registry obligations where
`Skeleton.skeletonGtzOriginalRankThree` reaches five. -/
theorem skeletonGtzOriginalRankThree_ofLivePairCompletion
    (hcomplete : LivePairCompletesOnHeavyWeak) :
    ∀ size : ℕ, 0 < size → Gtz.GtzOriginal size 3 :=
  Gtz.gtz_original_rank_three_of_six_three
    (Gtz.gtzWeighted_six_three_of_hinge_of_reach
      (Gtz.hingeHoldsAtSize_sixThree_of_stressFreeHinge
        Gtz.twoPoleStratumSelection_six_unconditional
        (Gtz.balancedStratumCapstone_of_balancedStratumSelection
          Gtz.balancedStratumSelection_six_holds)
        (stressFreeHingeSixThree_ofLivePairCompletion hcomplete))
      Gtz.parallelFreeReachesAnchor_six_three)

/-- The three class residuals that survive the shared criterion. -/
def livePairSurvivingObligationNames : List Lean.Name :=
  [`Skeleton.obligationBaseTripleTightUThreeSix,
   `Skeleton.obligationChartTieFreeThreeLinesFundamentalDomain,
   `Skeleton.obligationKnifeBandRefinedKFour]

#gtz_frontier_exactly skeletonGtzOriginalRankThree_ofLivePairCompletion expects
  livePairSurvivingObligationNames

end Skeleton.GeneralRank
