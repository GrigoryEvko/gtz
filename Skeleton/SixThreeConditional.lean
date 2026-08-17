import Skeleton.RankThree
import Skeleton.GeneralRank

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The general-rank capstone under the `(6,3)` cell

`Skeleton.GeneralRank.skeletonGtzWeightedAllEveryRank` uses all SEVEN registry
obligations.  Five of the seven are the rank-three class residuals.  This module
proves the SAME conclusion at every rank from `Gtz.GtzWeighted 6 3` together
with the TWO general-rank obligations, and from nothing else.  The five class
residuals leave the chain.

## Why the five leave

`Skeleton.GeneralRank.uniformInductionStep` divides each rank into two branches
on the arithmetic dichotomy `thresholdCell rank <= rank + 2`.  Rank three lands
in the large-rank branch, and that branch calls
`Skeleton.obligationThresholdCellHinge`.  That name is a THEOREM, and its proof
term contains its own rank-three instance, which is the `(6,3)` hinge, thus the
five class residuals.  The kernel walks proof terms and never instances, so
EVERY rank of the unconditional capstone reaches all five.

`uniformInductionStep_ofSixThree` divides each rank into three branches:

* rank at most two -- the corank floor `Gtz.InductionStep.corankFloor_holds`,
  which is unconditional at every rank;
* rank three -- the hypothesis `Gtz.GtzWeighted 6 3`, through
  `thresholdCell_three`, because `ClosesThresholdCell 3` IS that cell;
* rank four and up -- the ladder, on the two rank-four-and-up obligations and
  the sub-threshold band obligation.

The rank-three hinge is never called.  Thus the five class residuals never enter
the proof term, and `#gtz_frontier_exactly` below makes the kernel prove that
rather than a docstring claim it.

## Rank four is not a special case

The predecessor hypothesis of rank four is `Gtz.GtzWeightedAll 3`.  The strong
induction supplies it from the rank-three branch, which is the hypothesis cell
again.  So the hypothesis pays for rank three exactly one time, and the ladder
above rank three is unchanged.

## The single cell decides the whole conjecture, modulo two obligations

`everyRank_iff_sixThree` is the sharp reading.  The forward direction is
unconditional and free -- `Gtz.GtzWeightedAll 3` at size six IS the cell.  The
backward direction is this module.  So under the two general-rank obligations
the whole rank-uniform statement and the single cell `(6,3)` are ONE statement,
and the campaign that attacks that cell attacks every rank at the same time.

## What lands the day the cell lands

`Gtz.GtzWeighted 6 3` is not a theorem of the tree on 2026-08-13.  The parallel
`Gtz/Wave` campaign attacks it directly.  The day it lands under the name
`Gtz.gtzWeighted_six_three`, ONE line converts the conditional capstone into an
unconditional one:

    theorem skeletonGtzWeightedAllEveryRankUnconditional :
        ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
      skeletonGtzWeightedAllEveryRank_ofSixThree Gtz.gtzWeighted_six_three

Section 8 kernel-checks the shape of that line against a local hypothesis of
exactly that name and exactly that type, so the conversion cannot be wrong about
the interface.  The registry then holds two obligations for the general-rank
root, and the five class residuals become dead weight that
`Skeleton.Report`'s gate reports.
-/

namespace Skeleton.GeneralRank

/-! ## 1. The rank-three branch, off the cell itself

`ClosesThresholdCell 3` is `Gtz.GtzWeighted (thresholdCell 3) 3` by definition,
and `thresholdCell 3 = 6`.  So the rank-three branch of the induction IS the
hypothesis, with no hinge and no ladder between them. -/

/-- **The rank-three branch.**  The threshold cell at rank three is six, thus
the hypothesis closes that rank outright. -/
theorem closesThresholdCell_three_ofSixThree (hcellSixThree : Gtz.GtzWeighted 6 3) :
    ClosesThresholdCell 3 := by
  show Gtz.GtzWeighted (thresholdCell 3) 3
  rw [thresholdCell_three]
  exact hcellSixThree

/-- The converse, unconditional: the rank-three branch of the induction gives
the cell back.  So the hypothesis of this module is exactly the rank-three
branch and nothing more. -/
theorem sixThree_of_closesThresholdCell_three (hthreshold : ClosesThresholdCell 3) :
    Gtz.GtzWeighted 6 3 := by
  have hcell : Gtz.GtzWeighted (thresholdCell 3) 3 := hthreshold
  rwa [thresholdCell_three] at hcell

/-- **The rank-three branch, as an equivalence.**  Unconditional, and it is the
whole finding in one line: the cell the `Gtz/Wave` campaign attacks IS the
rank-three branch of the general-rank induction. -/
theorem closesThresholdCell_three_iff_sixThree :
    ClosesThresholdCell 3 ↔ Gtz.GtzWeighted 6 3 :=
  ⟨sixThree_of_closesThresholdCell_three, closesThresholdCell_three_ofSixThree⟩

/-! ## 2. The two closures at rank four and up

The same two closures as section 4 of `Skeleton.GeneralRank`, but discharged
from the RANK-FOUR-AND-UP registry axioms directly.  Neither proof term touches
`Skeleton.obligationThresholdCellHinge`, and that is the whole mechanism by
which the five class residuals leave. -/

/-- The hinge closure at rank four and up.  The threshold cell is the top of the
window, so the case split is exactly the split between
`Skeleton.obligationThresholdCellHingeRankFourAndUp` and
`Skeleton.obligationSubThresholdBandHinge` -- the two registry AXIOMS, with the
rank-three-discharging theorem between them removed. -/
theorem hingeHoldsAcrossSharpWindow_ofRankFourAndUp {rank : ℕ} (hrankAtLeastFour : 4 ≤ rank) :
    HingeHoldsAcrossSharpWindow rank := by
  rintro size ⟨hfloor, hceiling⟩ hpredecessorCell
  rcases eq_or_lt_of_le hceiling with hattop | hbelow
  · subst hattop
    exact Skeleton.obligationThresholdCellHingeRankFourAndUp rank hrankAtLeastFour
      hpredecessorCell
  · exact Skeleton.obligationSubThresholdBandHinge rank (by omega) size hfloor hbelow
      hpredecessorCell

/-- The reach closure at rank four and up, from the registry axiom directly.
The rank-three half is a theorem (`Gtz.icosaDesign`), so this branch sheds
nothing -- it is stated for symmetry with the hinge and to keep the chain's
inputs uniform. -/
theorem anchorReachesAcrossSharpWindow_ofRankFourAndUp {rank : ℕ} (hrankAtLeastFour : 4 ≤ rank) :
    AnchorReachesAcrossSharpWindow rank := by
  rintro size ⟨hfloor, hceiling⟩
  exact Skeleton.obligationSharpWindowAnchorReachRankFourAndUp rank hrankAtLeastFour size hfloor
    hceiling

/-! ## 3. The ladder above rank three -/

/-- The sharp window closed at rank four and up, on the shared rung engine
`closesSharpWindow_ofClosures` fed by the two rank-four-and-up closures. -/
theorem closesSharpWindow_ofRankFourAndUp {rank : ℕ} (hrankAtLeastFour : 4 ≤ rank)
    (hpredecessorRank : Gtz.GtzWeightedAll (rank - 1)) : ClosesSharpWindow rank :=
  closesSharpWindow_ofClosures (by omega)
    (hingeHoldsAcrossSharpWindow_ofRankFourAndUp hrankAtLeastFour)
    (anchorReachesAcrossSharpWindow_ofRankFourAndUp hrankAtLeastFour) hpredecessorRank

/-- The threshold cell at rank four and up, the top rung of that ladder. -/
theorem closesThresholdCell_ofRankFourAndUp {rank : ℕ} (hrankAtLeastFour : 4 ≤ rank)
    (hpredecessorRank : Gtz.GtzWeightedAll (rank - 1)) : ClosesThresholdCell rank :=
  closesSharpWindow_ofRankFourAndUp hrankAtLeastFour hpredecessorRank (thresholdCell rank)
    ⟨twoRank_le_thresholdCell (by omega), le_refl _⟩

/-! ## 4. The conditional induction step -/

/-- **THE STEP, under the cell.**  Every rank strictly below this one closed
implies this one closed.  Three branches, and each one is an arithmetic
comparison rather than an enumeration:

* `rank <= 2` -- the corank floor reaches the threshold cell;
* `rank = 3` -- the threshold cell IS the hypothesis cell;
* `4 <= rank` -- the ladder, on the three general-rank obligations.

Compare `Skeleton.GeneralRank.uniformInductionStep`, which has two branches and
sends rank three into the ladder, where the threshold-cell hinge supplies the
rank-three instance from the five class residuals. -/
theorem uniformInductionStep_ofSixThree (hcellSixThree : Gtz.GtzWeighted 6 3) (rank : ℕ)
    (hsmallerRanksClosed : ∀ smaller : ℕ, smaller < rank → Gtz.GtzWeightedAll smaller) :
    Gtz.GtzWeightedAll rank := by
  refine Gtz.gtzWeightedAll_of_veroneseTop rank ?_
  rcases Nat.lt_or_ge rank 3 with hrankSmall | hrankAtLeastThree
  · exact closesThresholdCell_ofSmallRank (by omega)
  · rcases Nat.lt_or_ge rank 4 with hrankBelowFour | hrankAtLeastFour
    · have hrankIsThree : rank = 3 := by omega
      subst hrankIsThree
      exact closesThresholdCell_three_ofSixThree hcellSixThree
    · exact closesThresholdCell_ofRankFourAndUp hrankAtLeastFour
        (hsmallerRanksClosed (rank - 1) (by omega))

/-! ## 5. The conditional capstones -/

/-- **THE CONDITIONAL GENERAL-RANK CAPSTONE.**  Weighted GTZ at every rank and
every size, from the single cell `(6,3)` and the three general-rank obligations.

The strong induction is the same one the unconditional capstone runs: an outer
induction on a bound, so each rank receives every smaller rank.  Rank four
receives `Gtz.GtzWeightedAll 3` from the rank-three branch, which is the
hypothesis cell again, so the hypothesis is spent one time only. -/
theorem skeletonGtzWeightedAllEveryRank_ofSixThree (hcellSixThree : Gtz.GtzWeighted 6 3) :
    ∀ rank : ℕ, Gtz.GtzWeightedAll rank := by
  have hclosedUpTo : ∀ bound rank : ℕ, rank ≤ bound → Gtz.GtzWeightedAll rank := by
    intro bound
    induction bound with
    | zero =>
        intro rank hrankBound
        exact uniformInductionStep_ofSixThree hcellSixThree rank
          (fun smaller hsmaller => absurd hsmaller (by omega))
    | succ previousBound closedUpToPrevious =>
        intro rank hrankBound
        exact uniformInductionStep_ofSixThree hcellSixThree rank
          (fun smaller hsmaller => closedUpToPrevious smaller (by omega))
  exact fun rank => hclosedUpTo rank rank (le_refl rank)

/-- The single deciding cell of every rank, closed under the hypothesis. -/
theorem closesThresholdCell_everyRank_ofSixThree (hcellSixThree : Gtz.GtzWeighted 6 3)
    (rank : ℕ) : ClosesThresholdCell rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree hcellSixThree rank (thresholdCell rank)

/-- **THE 1997 STATEMENT, at every rank, under the cell.**  Routed through the
converse bridge `Gtz.gtzWeightedAll_iff_forall_gtzOriginal`, so the original
conjecture itself is reached and not merely its weighted reformulation. -/
theorem skeletonGtzOriginalEveryRank_ofSixThree (hcellSixThree : Gtz.GtzWeighted 6 3) :
    ∀ size rank : ℕ, 0 < size → Gtz.GtzOriginal size rank :=
  fun size rank hsizePositive =>
    (Gtz.gtzWeightedAll_iff_forall_gtzOriginal rank).mp
      (skeletonGtzWeightedAllEveryRank_ofSixThree hcellSixThree rank) size hsizePositive

/-- The same conclusion off the SINGLE threshold cell of each rank, through the
bridge's sharp form. -/
theorem skeletonGtzOriginalFromThresholdCell_ofSixThree (hcellSixThree : Gtz.GtzWeighted 6 3)
    (rank : ℕ) : ∀ size : ℕ, 0 < size → Gtz.GtzOriginal size rank :=
  (Gtz.gtzWeighted_veroneseTop_iff_forall_gtzOriginal rank).mp
    (closesThresholdCell_everyRank_ofSixThree hcellSixThree rank)

/-- The tree's own canonical window closure at every rank, under the cell.  It
is stated one cell wider than the sharp window, and that extra cell is
redundant. -/
theorem closesCanonicalWindow_everyRank_ofSixThree (hcellSixThree : Gtz.GtzWeighted 6 3)
    (rank : ℕ) : Gtz.InductionStep.ClosesCanonicalWindow rank :=
  fun size _ => skeletonGtzWeightedAllEveryRank_ofSixThree hcellSixThree rank size

/-! ## 6. The whole conjecture is the single cell, modulo two obligations -/

/-- **THE SHARP READING.**  Under the two general-rank obligations, weighted
GTZ at EVERY rank and the single cell `(6,3)` are one statement.

The forward direction is free and unconditional: `Gtz.GtzWeightedAll 3` at size
six is the cell.  The backward direction is this module.  So the `Gtz/Wave`
campaign, which attacks that one cell, attacks every rank at the same time. -/
theorem everyRank_iff_sixThree :
    (∀ rank : ℕ, Gtz.GtzWeightedAll rank) ↔ Gtz.GtzWeighted 6 3 :=
  ⟨fun heveryRank => heveryRank 3 6, skeletonGtzWeightedAllEveryRank_ofSixThree⟩

/-- The same equivalence in the 1997 coordinates.  The forward direction rides
the unconditional `Gtz.gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three`,
so the coordinate change stays free here too. -/
theorem originalEveryRank_iff_sixThree :
    (∀ size rank : ℕ, 0 < size → Gtz.GtzOriginal size rank) ↔ Gtz.GtzWeighted 6 3 :=
  ⟨fun heveryRank =>
    Gtz.gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three.mpr
      fun size hsizePositive => heveryRank size 3 hsizePositive,
   skeletonGtzOriginalEveryRank_ofSixThree⟩

/-! ## 7. The rank-three capstone sheds EVERYTHING

`Skeleton.skeletonGtzOriginalRankThree` uses the five class residuals.  Under
the hypothesis it uses NO obligation at all, because the tree's own
`Gtz.gtz_original_rank_three_of_six_three` carries the whole rank from the cell.
This is the second Skeleton capstone the hypothesis clears, and it clears it
completely rather than partially. -/

/-- Rank three of the 1997 statement, under the cell, with ZERO obligations.
Compare `Skeleton.skeletonGtzOriginalRankThree`, which uses five. -/
theorem skeletonGtzOriginalRankThree_ofSixThree (hcellSixThree : Gtz.GtzWeighted 6 3) :
    ∀ size : ℕ, 0 < size → Gtz.GtzOriginal size 3 :=
  Gtz.gtz_original_rank_three_of_six_three hcellSixThree

/-- The rank-three capstone of `Skeleton.RankThree` and the rank-three slice of
the conditional general-rank capstone agree, and the agreement is free: both
sides are the cell.  Unconditional, thus zero obligations. -/
theorem rankThreeSliceAgrees_ofSixThree (hcellSixThree : Gtz.GtzWeighted 6 3) :
    Gtz.GtzWeightedAll 3 :=
  skeletonGtzWeightedAllEveryRank_ofSixThree hcellSixThree 3

/-! ## 8. The conversion, kernel-checked in shape

The day `Gtz.gtzWeighted_six_three` lands, the conditional capstone becomes
unconditional in one application.  The example below is that line with the
future theorem replaced by a local hypothesis of exactly its name and exactly
its type, so the interface is checked at the current build and cannot drift. -/

/-- The one-line conversion, with the future theorem as a hypothesis.
Anonymous and off the chain. -/
example (gtzWeighted_six_three : Gtz.GtzWeighted 6 3) : ∀ rank : ℕ, Gtz.GtzWeightedAll rank :=
  skeletonGtzWeightedAllEveryRank_ofSixThree gtzWeighted_six_three

/-- The same for the 1997 statement. -/
example (gtzWeighted_six_three : Gtz.GtzWeighted 6 3) :
    ∀ size rank : ℕ, 0 < size → Gtz.GtzOriginal size rank :=
  skeletonGtzOriginalEveryRank_ofSixThree gtzWeighted_six_three

/-! ## 9. The expected frontiers, as closed lists

Two lists and one command.  The command FAILS the build unless the kernel walk
of a named root reaches exactly the registry obligations of a named list.  A
printed frontier is not enough: the whole finding here is a claim about which
obligations are ABSENT, and an absence that only prints is an absence nobody
notices when it returns. -/

/-- The two general-rank obligations: what the conditional capstone must reach,
and all it must reach.  Both are hinges.  The reach obligation left this list on
2026-08-13, when `Gtz.GeneralRankReach.sharpWindowAnchorReachRankFourAndUp`
discharged it. -/
def generalRankObligationNames : List Lean.Name :=
  [`Skeleton.obligationSubThresholdBandHinge,
   `Skeleton.obligationThresholdCellHingeRankFourAndUp]

/-- All seven registry obligations: what the UNCONDITIONAL capstone reaches.
The difference between this list and `generalRankObligationNames` is the five
rank-three class residuals, which is the finding of this module. -/
def everyObligationName : List Lean.Name :=
  [`Skeleton.obligationBaseTripleTightUThreeSix,
   `Skeleton.obligationSeededLineSparseOneLine,
   `Skeleton.obligationSeededTransversalTwoMeetingLines,
   `Skeleton.obligationChartTieFreeThreeLinesFundamentalDomain,
   `Skeleton.obligationKnifeBandRefinedKFour,
   `Skeleton.obligationSubThresholdBandHinge,
   `Skeleton.obligationThresholdCellHingeRankFourAndUp]

/-- The empty frontier, for the roots that must reach no obligation at all. -/
def noObligationName : List Lean.Name := []

section FrontierGate

open Lean Elab Command

/-- Decode a closed `List Lean.Name` definition out of the environment. -/
def readExpectedNames (env : Environment) (listName : Name) : CommandElabM (List Name) := do
  let some listInfo := env.find? listName
    | throwError "#gtz_frontier_exactly: the list {listName} is missing."
  let some listValue := listInfo.value? (allowOpaque := true)
    | throwError "#gtz_frontier_exactly: the list {listName} has no value."
  let some listNames := Skeleton.Frontier.decodeNameListExpr listValue
    | throwError "#gtz_frontier_exactly: {listName} must be a closed list of name literals."
  return listNames

/-- Fail unless the registry obligations reachable from `root` are EXACTLY the
names of `expected`.  Reports the two differences by name, so a build failure
names the exact edit that repairs it.

This is stricter than `#gtz_frontier`, which fails only on an axiom outside the
registry and prints the rest.  Here a MISSING obligation is a failure too, which
is what makes the shedding claim of this module falsifiable. -/
elab "#gtz_frontier_exactly " rootIdent:ident " expects " expectedIdent:ident : command => do
  let roots ← Skeleton.Frontier.resolveRootNames #[rootIdent]
  let expectedName ← liftCoreM <| realizeGlobalConstNoOverloadWithInfo expectedIdent
  let env ← getEnv
  let expected ← readExpectedNames env expectedName
  let expectedSet : NameSet :=
    expected.foldl (init := ({} : NameSet)) (fun accumulated name => accumulated.insert name)
  let declaredSet : NameSet :=
    (Skeleton.Frontier.declaredObligations env).foldl (init := ({} : NameSet))
      (fun accumulated name => accumulated.insert name)
  let (reached, divergences) ← Skeleton.Frontier.reachedAxiomsOfRoots roots
  let reachedObligations := reached.toList.filter declaredSet.contains
  let foreign :=
    reached.toList.filter fun axiomName =>
      !Skeleton.Frontier.standardFoundationAxioms.contains axiomName
        && !declaredSet.contains axiomName
  let unexpected := (reachedObligations.filter fun name => !expectedSet.contains name).toArray
  let absent := (expected.filter fun name => !reached.contains name).toArray
  let mut report : MessageData :=
    m!"GTZ EXACT FRONTIER of {roots.toList}\n  expected {expected.length}, reached {reachedObligations.length}"
  for obligationName in (reachedObligations.toArray.qsort Name.lt).toList do
    report := report ++ m!"\n    {obligationName}"
  if reachedObligations.isEmpty then
    report := report ++ m!"\n    (none -- this constant is unconditional)"
  unless divergences.isEmpty do
    report := report ++ m!"\n  WARNING worklist and collectAxioms disagreed:"
    for divergence in divergences do
      report := report ++ m!"\n  {divergence}"
  logInfo report
  unless foreign.isEmpty do
    throwError "#gtz_frontier_exactly: {roots.toList} reaches unregistered axioms {(foreign.toArray.qsort Name.lt).toList}."
  unless unexpected.isEmpty && absent.isEmpty do
    let mut complaint : MessageData :=
      m!"#gtz_frontier_exactly FAILED for {roots.toList} against {expectedName}:"
    unless unexpected.isEmpty do
      complaint := complaint ++
        m!"\n  * UNEXPECTED {(unexpected.qsort Name.lt).toList} -- reached but not listed. Either the chain regressed, or the list is stale."
    unless absent.isEmpty do
      complaint := complaint ++
        m!"\n  * ABSENT {(absent.qsort Name.lt).toList} -- listed but not reached. The obligation was discharged, or the list is stale."
    throwError complaint

end FrontierGate

/-! ## 10. The frontier, before and after

Six kernel prints and five gates.  The before and after are computed in the same
elaboration, so the comparison is a kernel fact of this build.

BEFORE.  `skeletonGtzWeightedAllEveryRank` reaches all eight obligations.
AFTER.  `skeletonGtzWeightedAllEveryRank_ofSixThree` reaches the three
general-rank obligations, and none of the five class residuals.
FREE.  `skeletonGtzOriginalRankThree_ofSixThree` reaches none at all. -/

#print axioms skeletonGtzWeightedAllEveryRank

#print axioms skeletonGtzOriginalEveryRank

#print axioms skeletonGtzWeightedAllEveryRank_ofSixThree

#print axioms skeletonGtzOriginalEveryRank_ofSixThree

#print axioms everyRank_iff_sixThree

#print axioms skeletonGtzOriginalRankThree_ofSixThree

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank expects everyObligationName

#gtz_frontier_exactly skeletonGtzWeightedAllEveryRank_ofSixThree expects generalRankObligationNames

#gtz_frontier_exactly skeletonGtzOriginalEveryRank_ofSixThree expects generalRankObligationNames

#gtz_frontier_exactly everyRank_iff_sixThree expects generalRankObligationNames

#gtz_frontier_exactly skeletonGtzOriginalRankThree_ofSixThree expects noObligationName

#gtz_frontier_all skeletonGtzWeightedAllEveryRank_ofSixThree
  skeletonGtzOriginalEveryRank_ofSixThree

end Skeleton.GeneralRank
