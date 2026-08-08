import Skeleton.RankThree
import Skeleton.GeneralRank

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# The frontier report and the anti-drift gate

This is the module the operator runs.  It imports both capstones, prints the
current frontier from the kernel, and then FAILS THE BUILD on any of the three
ways the scaffold can rot:

* an obligation is declared but no capstone spends it (dead weight);
* a capstone reaches an axiom that is neither foundational nor registered;
* the obligation count moved without a matching ledger entry.

`Skeleton.Frontier` already reports the first two.  Reporting is not enough: a
printed warning nobody reads is exactly the failure this scaffold exists to
prevent, so `#gtz_gate` throws instead.

## The ledger, and why the count cannot drift

Three closed lists below are the whole audit trail.

* `baselineObligationNames` -- the registry as it stood when the scaffold was
  built.  Four names.
* `retiredObligationNames` -- every obligation since removed, whether discharged
  outright or split away.  A name here must NOT be a declared axiom any more.
* `introducedObligationNames` -- every obligation added after the baseline.  A
  name here MUST be a declared axiom.

The gate enforces the accounting identity

  `baseline.length + introduced.length = declared.size + retired.length`

so the registry cannot change size at all without a ledger edit, and the two
membership conditions mean neither list can be padded with fiction: you cannot
claim to have retired something that is still declared, nor claim to have
introduced something that does not exist.

One more rule closes the last hole.  Adding axioms while retiring nothing is a
NEW ASSUMPTION, not a split, so the gate rejects it outright.  A genuine split
always retires its parent -- that is what makes the parent survive downstream as
a theorem -- so a real split passes and a quiet strengthening does not.

## What the operator actually types

    bash scripts/gtz-frontier

which rebuilds the Skeleton library and elaborates this file.
-/

namespace Skeleton.Report

open Lean Elab Command

/-! ### The ledger -/

/-- The registry as built by stage three.  Editing this list is how you declare
that the frontier itself grew, which is a different and much more serious event
than a split; it must never be edited to accommodate one. -/
def baselineObligationNames : List Name :=
  [`Skeleton.obligationStressFreeHingeSixThree,
   `Skeleton.obligationSubThresholdBandHinge,
   `Skeleton.obligationThresholdCellHinge,
   `Skeleton.obligationSharpWindowAnchorReach]

/-- Obligations removed since the baseline, by discharge or by split.  Each name
must no longer be a declared axiom; the gate checks that. -/
def retiredObligationNames : List Name :=
  [-- 2026-08-07: split into the five matroid classes; survives as a theorem
   -- assembled from them (lossless -- the tie-emptiness reading of the hinge
   -- carries no pattern hypothesis).
   `Skeleton.obligationStressFreeHingeSixThree,
   -- 2026-08-07: split by rank; survives as a theorem assembled from the two
   -- halves.
   `Skeleton.obligationSharpWindowAnchorReach,
   -- 2026-08-07: introduced by the rank split and discharged in the same edit
   -- (Gtz.icosaDesign; the sharp window at rank three is the single cell six).
   `Skeleton.obligationSharpWindowAnchorReachRankThree,
   -- 2026-08-08: the five class obligations SHARPENED one landed reduction
   -- each -- every class statement survives as a theorem discharged from the
   -- exact residual Prop the campaign attacks (refinement in the sufficient
   -- direction; no converse claimed).
   `Skeleton.obligationTieFreeUThreeSix,
   `Skeleton.obligationTieFreeOneLine,
   `Skeleton.obligationTieFreeTwoMeetingLines,
   `Skeleton.obligationTieFreeThreeLines,
   `Skeleton.obligationTieFreeKFour,
   -- 2026-08-08: split by rank -- the rank-three instance IS the (6,3) hinge,
   -- i.e. the five class obligations in a strictly stronger wrapper; it is now
   -- DISCHARGED from them, and the axiom survives only at rank four and up.
   `Skeleton.obligationThresholdCellHinge,
   -- 2026-08-08, second sharpening round: three of the five class residuals
   -- pushed BELOW the landed producers rather than merely below the class
   -- bridges -- the two chartless strata onto the reduced cover property
   -- (`Gtz.stratumIsTieFree_of_reducedCoverProperty` spends the uniform Schur
   -- producer), and the K4 chart onto the knife band
   -- (`Gtz.directionChartIsTieFree_kFour_of_knifeBandWeakToStrict` spends all
   -- twenty landed Layer-A cells).  Each survives as a theorem.
   `Skeleton.obligationStratumTieFreeOneLine,
   `Skeleton.obligationStratumTieFreeTwoMeetingLines,
   `Skeleton.obligationChartTieFreeKFour,
   -- 2026-08-08, round 3: the DEFECT REPAIR, and the campaign's first
   -- retirement that is a DELETION rather than a demotion.  The round-2
   -- chartless entries were STRICTLY STRONGER than the class statements they
   -- served -- unconditioned on ties, `Gtz.PatternReducedCoverProperty`
   -- forces a strictly dominating card-3 subset at every design of the
   -- stratum (`Gtz.hasStrictDominator_of_reducedCoverProperty`), i.e. the
   -- stratum-restricted strict half of the conclusion the campaign is
   -- proving.  They CANNOT survive as theorems, because the repaired Prop
   -- does not imply them; that non-implication IS the repair.  Nothing
   -- downstream moves: the capstone consumes
   -- `obligationStratumTieFree{OneLine,TwoMeetingLines}`, which stay theorems
   -- of exactly their old types.
   `Skeleton.obligationReducedCoverOneLine,
   `Skeleton.obligationReducedCoverTwoMeetingLines]

/-- Obligations added since the baseline.  Each name must be a declared axiom;
the gate checks that.  Adding to this list with `retiredObligationNames` still
empty is rejected: that is a new assumption, not a split. -/
def introducedObligationNames : List Name :=
  [-- 2026-08-07: the five-class split of the rank-three obligation, one axiom
   -- per entry of `Gtz.stressFreeResidualFamiliesSix`.
   `Skeleton.obligationTieFreeUThreeSix,
   `Skeleton.obligationTieFreeOneLine,
   `Skeleton.obligationTieFreeTwoMeetingLines,
   `Skeleton.obligationTieFreeThreeLines,
   `Skeleton.obligationTieFreeKFour,
   -- 2026-08-07: the rank split of the reach obligation.  The rank-three half
   -- was discharged in the same edit, so it also appears in the retired list.
   `Skeleton.obligationSharpWindowAnchorReachRankThree,
   `Skeleton.obligationSharpWindowAnchorReachRankFourAndUp,
   -- 2026-08-08: the five sharpened class residuals, one landed reduction
   -- below the class statements they replace.
   `Skeleton.obligationWeakToStrictUThreeSix,
   `Skeleton.obligationStratumTieFreeOneLine,
   `Skeleton.obligationStratumTieFreeTwoMeetingLines,
   `Skeleton.obligationChartTieFreeThreeLines,
   `Skeleton.obligationChartTieFreeKFour,
   -- 2026-08-08: the rank-four-and-up half of the threshold-cell hinge; the
   -- rank-three half is discharged from the class obligations.
   `Skeleton.obligationThresholdCellHingeRankFourAndUp,
   -- 2026-08-08, second sharpening round: the reduced cover property at the
   -- two chartless patterns and the K4 knife band -- each one landed ENGINE
   -- below the residual it replaces, not merely one landed bridge.
   `Skeleton.obligationReducedCoverOneLine,
   `Skeleton.obligationReducedCoverTwoMeetingLines,
   `Skeleton.obligationKnifeBandKFour,
   -- 2026-08-08, round 3: the repaired chartless residuals, carrying the same
   -- weak-domination antecedent the other three residuals already carry, plus
   -- heaviness and the tie's own tight direction -- three landed engines spent
   -- instead of re-demanded, and kernel-EQUIVALENT to the class statement.
   `Skeleton.obligationTightDominatedCoverOneLine,
   `Skeleton.obligationTightDominatedCoverTwoMeetingLines]

/-! ### The gate -/

/-- Read a ledger list out of the environment and decode it back to names. -/
def readLedgerList (env : Environment) (ledgerName : Name) : CommandElabM (List Name) := do
  let some ledgerInfo := env.find? ledgerName
    | throwError "#gtz_gate: the ledger {ledgerName} is missing."
  let some ledgerValue := ledgerInfo.value? (allowOpaque := true)
    | throwError "#gtz_gate: the ledger {ledgerName} has no value."
  let some ledgerNames := Skeleton.Frontier.decodeNameListExpr ledgerValue
    | throwError "#gtz_gate: {ledgerName} must be a closed list of name literals."
  return ledgerNames

/-- The whole-scaffold gate.  Prints a one-screen status line and throws on any
drift.  Every failure message names the exact edit that repairs it. -/
elab "#gtz_gate " capstoneIdents:ident+ : command => do
  let capstones ← Skeleton.Frontier.resolveRootNames capstoneIdents
  let env ← getEnv
  let declared := Skeleton.Frontier.declaredObligations env
  let declaredSet : NameSet :=
    declared.foldl (init := ({} : NameSet)) (fun accumulated name => accumulated.insert name)
  let baseline ← readLedgerList env ``baselineObligationNames
  let retired ← readLedgerList env ``retiredObligationNames
  let introduced ← readLedgerList env ``introducedObligationNames
  let (reached, divergences) ← Skeleton.Frontier.reachedAxiomsOfRoots capstones

  -- (b) every reachable axiom is foundational or registered
  let foreign :=
    reached.toList.filter fun axiomName =>
      !Skeleton.Frontier.standardFoundationAxioms.contains axiomName
        && !declaredSet.contains axiomName
  -- (a) every declared obligation is spent by some capstone
  let dead := declared.filter fun obligationName => !reached.contains obligationName
  -- (c) the count moved only as the ledger says
  let ledgerBalances := baseline.length + introduced.length == declared.size + retired.length
  let phantomRetirements := retired.filter fun name => declaredSet.contains name
  -- An introduced obligation may legitimately be discharged later, in which case
  -- it is no longer declared but IS recorded as retired.  Only a name that is
  -- neither is fiction.
  let phantomIntroductions :=
    introduced.filter fun name => !declaredSet.contains name && !retired.contains name
  let unaccountedBaseline :=
    baseline.filter fun name => !declaredSet.contains name && !retired.contains name
  let isBareStrengthening := !introduced.isEmpty && retired.isEmpty

  let mut failures : Array MessageData := #[]
  unless foreign.isEmpty do
    let diagnosis :=
      if foreign.contains ``sorryAx then
        "a proof is incomplete. Replace the `sorry` with a registry obligation carrying the five-field docstring."
      else
        "declare it in Skeleton.Obligations with the five-field docstring and add it to introducedObligationNames, or eliminate it."
    failures := failures.push
      m!"FOREIGN AXIOM: {capstones} reaches {foreign} -- {diagnosis}"
  unless dead.isEmpty do
    failures := failures.push
      m!"DEAD OBLIGATION: {dead.toList} is declared but no capstone spends it. Either wire it into a capstone or retire it (delete the axiom and add its name to retiredObligationNames)."
  unless phantomRetirements.isEmpty do
    failures := failures.push
      m!"PHANTOM RETIREMENT: {phantomRetirements} appears in retiredObligationNames but is still a declared axiom. Delete the axiom, or remove the ledger entry."
  unless phantomIntroductions.isEmpty do
    failures := failures.push
      m!"PHANTOM INTRODUCTION: {phantomIntroductions} appears in introducedObligationNames but is neither a declared axiom nor recorded in retiredObligationNames. Remove the ledger entry, or record the retirement."
  unless unaccountedBaseline.isEmpty do
    failures := failures.push
      m!"UNACCOUNTED BASELINE OBLIGATION: {unaccountedBaseline} vanished from the registry with no entry in retiredObligationNames. Record the retirement."
  unless ledgerBalances do
    failures := failures.push
      m!"LEDGER IMBALANCE: baseline {baseline.length} + introduced {introduced.length} != declared {declared.size} + retired {retired.length}. The registry changed size without a ledger entry."
  if isBareStrengthening then
    failures := failures.push
      m!"BARE STRENGTHENING: axioms were introduced while retiredObligationNames is empty. A split always retires its parent -- that is what keeps the parent alive downstream as a theorem. If the frontier genuinely grew, say so by editing baselineObligationNames and recording why in the commit message."

  let mut report : MessageData :=
    m!"GTZ GATE over {capstones}"
  report := report ++ m!"\n  declared obligations : {declared.size}"
  report := report ++
    m!"\n  ledger : baseline {baseline.length}, introduced {introduced.length}, retired {retired.length}"
  report := report ++ m!"\n  dead obligations : {dead.size}"
  report := report ++ m!"\n  foreign axioms : {foreign.length}"
  unless divergences.isEmpty do
    report := report ++ m!"\n  WARNING worklist and collectAxioms disagreed:"
    for divergence in divergences do
      report := report ++ m!"\n  {divergence}"
  if failures.isEmpty then
    report := report ++ m!"\n  GATE PASS"
    logInfo report
  else
    let mut complaint : MessageData := m!"#gtz_gate FAILED ({failures.size} problem(s)):"
    for failure in failures do
      complaint := complaint ++ m!"\n  * {failure}"
    logInfo report
    throwError complaint

end Skeleton.Report

/-! ### The report itself

Union first -- that is the answer to "what is left" -- then the per-capstone
breakdown, then the index check, then the gate.

`Skeleton.skeletonGtzOriginalRankThree` is `Skeleton.RankThree`'s capstone;
`Skeleton.GeneralRank.skeletonGtzWeightedAllEveryRank` is the general-rank one.  Between them they must spend every declared
obligation, or the gate reports dead weight. -/

#gtz_frontier Skeleton.skeletonGtzOriginalRankThree
  Skeleton.GeneralRank.skeletonGtzWeightedAllEveryRank

#gtz_frontier Skeleton.skeletonGtzOriginalRankThree

#gtz_frontier Skeleton.GeneralRank.skeletonGtzWeightedAllEveryRank

#gtz_registry_check

#gtz_gate Skeleton.skeletonGtzOriginalRankThree
  Skeleton.GeneralRank.skeletonGtzWeightedAllEveryRank
