/-
# The primitive-tight stratum ledger: what is discharged, what the residual is,
# and the leverage floor that narrows every open entry

`Gtz.Design.PrimitiveTightClassification` reduces the campaign's one
nature-facing gap — the HINGE at `(6,3)` and `(7,3)` — to a finite ledger of
per-matroid emptiness statements, THIRTY-TWO isomorphism classes (nine at six
points, twenty-three at seven).  This file does four things to that ledger and
claims nothing beyond them.

1. It records the discharged entries as a STRUCTURAL peel rather than a list of
   names: `hingeHoldsAtSize_of_residualLedger` and its size-seven sibling take a
   complete enumeration and ask tie-freeness only of the patterns that are
   neither a near pencil nor a Fano.  So the residual obligation the campaign
   owes is exactly the open classes, and no bookkeeping step stands between the
   discharged ones and the hinge.  The recognizers compare patterns only on
   DISTINCT triples, which is all `Gtz.HasLinePattern` constrains — see the
   normalization warning below, and `not_isRelabelOf_nearPencilStrictPattern`
   for why comparing total functions would silently drop both near-pencil
   entries.
2. It proves a LEVERAGE FLOOR: at `(6,3)`, unconditionally, every atom of a tie
   has `|g_c|^2 >= 1`.  Hence `StratumIsTieFreeAmongHeavy` — tie-freeness asked
   only of designs all of whose atoms are heavy — already implies
   `StratumIsTieFree` at size six.  That strictly shrinks the semialgebraic
   system every one of the open entries has to solve, and it is not a
   criticality argument: it runs through the landed `GtzWeighted 5 3`.
3. It splits the floor against the repository's own strict predicate
   `Gtz.AllHeavy` (`1 < |g_c|^2`), which is what the shipped heavy machinery
   consumes.  The floor gives only `1 <=`, so the honest statement is a
   DICHOTOMY — every `(6,3)` tie is all-heavy or carries an atom of leverage
   EXACTLY one (`allHeavy_or_exists_leverage_eq_one_of_isTie_sixThree`) — and the
   per-class obligation splits accordingly into an all-heavy half and a named
   unit-leverage boundary residue.
4. It sharpens the repo's light-atom deflation from WEAK to STRICT domination,
   which is what the floor is extracted from, and keeps the quantitative gap
   bound the weak form discards.

## The gap bound, and why the floor follows

Fix a design of size `m + 1` and a label `d` whose SHARE `t_d |g_d|^2` is
strictly below one.  Whitening the surviving atoms against
`P = I - t_d g_d g_d^T` produces a design of size `m`
(`Gtz.deflatedDesign`), and `GtzWeighted m k` hands back a dominating subset
`C` of the survivors.  Pulling the domination back through the congruence gives
not merely `S_C >= I` but the sharp

  (1 - t_d) (S_C - I)  >=  t_d (I - g_d g_d^T)     (Loewner, division-free)

— `exists_deflatedGapBound`.  The right-hand side is positive definite exactly
when `|g_d|^2 < 1`, so a strictly light atom yields a STRICTLY dominating subset
(`exists_posDef_of_lightAtom`), and a tie therefore has no strictly light atom
(`leverage_one_le_of_isTie`).  Even when `|g_d|^2 > 1` the bound still says the
gap is positive definite on the plane orthogonal to `g_d` with margin
`t_d/(1 - t_d)` — `posDef_on_orthogonal_of_deflatedGapBound`.

The floor is UNCONDITIONAL at size six because the input is `GtzWeighted 5 3`
(`Gtz.gtzWeighted_of_le_five`).  At size seven the same argument needs
`GtzWeighted 6 3`, which is open, so every size-seven statement here carries it
as a named hypothesis and none of them is used elsewhere.

## Why the floor stops at `1 <=`, and what that costs

At leverage exactly one the summand `I - g_d g_d^T` is positive SEMIdefinite and
SINGULAR, so `exists_deflatedGapBound` yields only weak domination — which a tie
already satisfies.  The method therefore cannot reach `1 <`, and the difference
is not cosmetic: the repository's heavy toolkit is stated against
`Gtz.AllHeavy`, the STRICT predicate.  Hence the split in point 3 above, and
hence `StratumIsTieFreeAtUnitLeverage` as a named, still-open residue rather
than a silent gap.  It is a small residue — a tie with an atom of leverage
exactly one has that atom's share equal to its weight — but it is not empty by
anything proved here.

## A normalization warning that is load-bearing for the peel

`Gtz.HasLinePattern` is an iff over DISTINCT triples only, so two patterns
differing on degenerate triples define the SAME stratum.  The two representatives
already shipped disagree there: `nearPencilLinePattern pole label label label` is
TRUE for `label /= pole` (`nearPencilLinePattern_self_of_ne`) while
`fanoLinePattern label label label` is FALSE at every label
(`not_fanoLinePattern_diagonal`).  There is no convention a ledger author could
guess.  Every recognizer here therefore compares patterns through
`AgreesOnDistinctTriples`, never by equality of total functions.  That this
matters is proved, not asserted: `nearPencilStrictPattern` defines exactly the
near-pencil stratum (`agreesOnDistinctTriples_nearPencilStrictPattern`) and IS
recognized (`isNearPencilClass_nearPencilStrictPattern`), yet it is a
relabelling of NO pole's near pencil as a total function
(`not_isRelabelOf_nearPencilStrictPattern`).  Under an equality-based recognizer
a ledger presenting the near pencil in that normal form would lose both
near-pencil entries and, by the same slip, the Fano.

## PROVED here, kernel-checked, unconditional

* `posDef_one_sub_atomMatrix_of_leverage_lt_one` — `I - g g^T` is positive
  definite exactly at a strictly light atom.  Rides
  `Gtz.posDef_sub_vecMulVec_iff` at `N = I`.
* **`exists_deflatedGapBound`** — the sharp deflation transport, stated
  division-free.  The subset it returns AVOIDS the deflated label.  Its
  whitening step consumes the shipped
  `Gtz.posDef_one_sub_smul_atomMatrix_of_share_lt_one`
  (`Gtz.Reduction.SplitTransfer`) — the pivot `I - t g g^T` is positive definite
  when the SHARE `t |g|^2` is below one, which is weaker than lightness and fails
  exactly at a near-pencil pole, where the share is one
  (`Gtz.soleOffPlane_share_eq_one`).
* `posDef_on_orthogonal_of_deflatedGapBound` — the two-dimensional half of the
  bound, valid at every label whatever its leverage.
* **`exists_posDef_of_lightAtom`**, `not_isTie_of_lightAtom` — the strict
  upgrade of `Gtz.dominating_of_light_atom`, whose conclusion is only weak
  domination and so cannot exclude a tie.
* **`leverage_one_le_of_isTie`** and **`leverage_one_le_of_isTie_sixThree`** —
  the leverage floor, the second unconditional at `(6,3)`.
  `leverage_one_le_of_isTie_fourThree` / `_fiveThree` are the same statement at
  the two rungs below, where ties provably exist.
* **`allHeavy_or_exists_leverage_eq_one_of_isTie`** and its `(6,3)` form — the
  dichotomy against the repository's strict `Gtz.AllHeavy`.  This is the sharpest
  honest form of the floor and the one that connects it to the shipped heavy
  machinery.
* `share_bracket_of_isTie` — the floor against the shipped ceiling
  `Gtz.weighted_leverage_le_one`: at a tie each share sits in `[t_c, 1]`.
  `sum_weighted_leverage_excess_of_isTie` — the same two facts as a
  normalization: the excesses `|g_c|^2 - 1` (the repository's `heavyExcess`) are
  pointwise NONNEGATIVE at a tie and carry weighted total exactly `k - 1`.
* `design_mem_collaredSet_of_isTie_sixThree` — every `(6,3)` tie's configuration
  lies in `Gtz.collaredSet`, whose all-heavy leverage hypothesis is exactly what
  the floor supplies.  Compactness (`Gtz.isCompact_collaredSet`) additionally
  needs a POSITIVE weight floor, which a tie does not supply on its own; the
  statement is therefore parameterized on that floor.
* `AgreesOnDistinctTriples`, `agreesOnDistinctTriples_refl`,
  `hasLinePattern_of_agreesOnDistinctTriples`,
  **`stratumIsTieFree_of_agreesOnDistinctTriples`** — the stratum-level
  vocabulary: patterns agreeing on distinct triples define the same stratum.
* `IsRelabelOf`, `isRelabelOf_refl`, `stratumIsTieFree_of_isRelabelOf`,
  `IsRelabelOfOnDistinctTriples`, `isRelabelOfOnDistinctTriples_of_isRelabelOf`,
  **`stratumIsTieFree_of_isRelabelOfOnDistinctTriples`** — the up-to-relabelling
  vocabulary in both the strict and the stratum-correct form, riding the landed
  `Gtz.stratumIsTieFree_comp_relabel`.
* `StratumIsTieFreeAmongHeavy`, `stratumIsTieFreeAmongHeavy_of_stratumIsTieFree`,
  **`stratumIsTieFree_of_amongHeavy_sixThree`** — the narrowed per-class
  obligation and the reduction that makes it sufficient at size six.
  `stratumIsTieFree_of_amongHeavy_sevenThree` is the size-seven form and carries
  `GtzWeighted 6 3`.
* `StratumIsTieFreeAmongAllHeavy`, `StratumIsTieFreeAtUnitLeverage`,
  `stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage`,
  **`stratumIsTieFree_of_allHeavy_and_unitLeverage_sixThree`** — the split into
  the repository's strict-heavy predicate plus the unit-leverage boundary.
* `IsNearPencilClass`, `IsFanoClass`, `stratumIsTieFree_of_isNearPencilClass`,
  `stratumIsTieFree_of_isFanoClass` — the three discharged entries as
  recognizers on patterns.  `nearPencilLinePattern_comp_relabel` and
  `isNearPencilClass_iff_exists_pole` record that the near-pencil family is
  already closed under relabelling, so that entry needs no transport at all.
* `isPrimitiveDesign_iff_not_hasParallelPair` — the bridge the classification
  header says a wiring module needs, exercised rather than described.  Because
  this file imports `Gtz.Reduction.SplitTransfer`, every assembly below concludes
  `Gtz.HingeHoldsAtSize size 3` ON THE NOSE rather than its body written out.
* **`hingeHoldsAtSize_of_residualLedger`**,
  **`hingeHoldsAtSize_of_residualLedger_sevenThree`**,
  **`hingeHoldsAtSize_of_heavyResidualLedger_sixThree`**,
  `hingeHoldsAtSize_of_heavyResidualLedger_sevenThree`,
  **`hingeHoldsAtSize_of_allHeavyResidualLedger_sixThree`** — the assemblies.
  The last is the sharpest honest form: the hinge at six points follows from a
  complete enumeration plus, per non-near-pencil class, tie-freeness among
  `Gtz.AllHeavy` designs AND tie-freeness at unit leverage.
* Controls.  `not_isNearPencilClass_lineFree` — the peel is not secretly
  everything: the line-free stratum `U(3,size)` survives it at every size `>= 4`,
  so `U(3,6)` and `U(3,7)` are still owed.
  `nearPencilLinePattern_self_of_ne`, `not_fanoLinePattern_diagonal`,
  `not_isRelabelOf_nearPencilStrictPattern` — the normalization warning above,
  proved.  `tetraDesign_forall_leverage_one_le`,
  `diamondDesign_forall_leverage_one_le`,
  **`splitTetraDesign_forall_leverage_one_le`** — the heavy restriction does not
  throw the phenomenon away: the `(4,3)` tetrahedron tie, the `(5,3)` diamond
  tie, and the whole two-parameter `(6,3)` split-tetrahedron family of ties are
  all heavy, the last AT THE HINGE'S OWN LOWER SIZE.
  `splitTetraDesign_allHeavy` puts that family in the STRICT-heavy branch of the
  dichotomy, and `splitTetraDesign_hasParallelPair` records why it does not
  refute the hinge: it is not primitive, its atoms `2` and `3` coinciding.
  `nearPencilSixDesign_hasNearPencilLinePattern` and
  `nearPencilSixDesign_allHeavy` witness that a discharged hinge stratum carries
  an all-heavy design, so the narrowed obligation is not vacuous there either.
  `not_stratumIsTieFreeAmongHeavy_fourThree_lineFree` — the narrowed obligation
  is a genuine condition, refutable at `(4,3)`.

## What this file does NOT do

It discharges NONE of the twenty-nine open classes.  No entry of the ledger
moves from open to empty here; what moves is the SHAPE of the residual.  In
particular `M(K4)` (`q6m8`) is untouched: its infimum is one, not attained, and
approached along the boundary where one atom's weight and length go to zero
together, so the leverage floor does not reach it — the floor is a necessary
condition on ties, not a positive margin.

No statement here assumes total tie, criticality of the maximum, or any
first-order condition at a tie.  Per `Gtz.Ties.TotalTieCorankOne` a proof through
criticality would prove `GtzWeighted` at the same size and be circular; the only
inputs used are `GtzWeighted` at STRICTLY SMALLER size, which is what makes the
size-six statements unconditional and the size-seven ones honestly hypothetical.

## CITED, not reproved here

* `Gtz.deflatedDesign` and `Gtz.dominating_of_light_atom`
  (`Gtz.Reduction.Deflation`) — the whitening construction and the weak
  light-atom conclusion this file sharpens.  The gap bound below reuses the
  construction verbatim and replaces only the final assembly.
* `Gtz.AllHeavy`, `Gtz.GtzWeightedHeavy`, `Gtz.gtzWeightedAll_of_heavy`,
  `Gtz.gtzWeightedAll_of_heavy_bounded`, `Gtz.rank_three_of_heavy_residuals`
  (`Gtz.Reduction.Reductions`) — the CLOSEST PRIOR ART to the floor, and the
  reason the dichotomy above is stated rather than a bare inequality.  Those
  theorems already reduce rank three to `GtzWeightedHeavy 6 3` and
  `GtzWeightedHeavy 7 3` by the same light/heavy split that
  `exists_posDef_of_lightAtom` sharpens; what is new here is that the split
  applies to TIES with no size-`m` heaviness hypothesis, and that the surviving
  side is `1 <=` rather than `1 <`.
* `Gtz.collaredSet`, `Gtz.design_mem_collaredSet`, `Gtz.isCompact_collaredSet`
  (`Gtz.Design.CollaredCompact`) — the immediate consumer of the floor, whose
  leverage hypothesis is literally `forall c, 1 <= leverageOf (D.atom c)`.
* `Gtz.posDef_one_sub_smul_atomMatrix_of_share_lt_one`, `Gtz.HasParallelPair`,
  `Gtz.HingeHoldsAtSize`, `Gtz.not_hingeHoldsAtSize_five_three`
  (`Gtz.Reduction.SplitTransfer`) — the share-form deflation pivot, the hinge
  predicate, and the fact that it is FALSE one size below.
* `Gtz.gtzWeighted_of_le_five` (`Gtz.Reduction.Reductions`) — weighted GTZ at
  every size at most five, itself resting on the corank-one and corank-two laws.
  This is the sole reason the size-six statements are unconditional.
* `Gtz.stratumIsTieFree_nearPencil`, `Gtz.nearPencilLinePattern`
  (`Gtz.Design.NearPencilStrictDomination`) — the near-pencil entry, at every
  size and every pole.  An independent mechanization of the same class exists at
  `Gtz.stratumIsTieFree_solePoleLinePattern`
  (`Gtz.Design.NearPencilTransport`), by the same rank-two transport with a
  different weight bookkeeping; this file consumes only the first for the peel,
  so that entry is doubly certified but singly depended on.  The two files'
  patterns are the SAME function, which
  `nearPencilLinePattern_eq_solePoleLinePattern` records — that reconciliation
  is what lets the second file's exact rational witnesses discharge the first
  file's non-vacuity question.  One caution, since the transport is cited and not
  reproved: the classification file's description of it (planar weights
  `tau_c = t_c/poleShare` with strictness factor `1/poleShare`) is NOT the shipped
  construction and cannot be — those weights already sum to one over the non-pole
  labels, leaving the pole weight zero, which `weight_pos` forbids.  The shipped
  `Gtz.nearPencilPlaneDesign` keeps the pole at HALF its weight and inflates the
  planar weights to `t_c (1 - t/2)/(1 - t)`, giving deflation
  `Gtz.poleDeflation = (1 - t)/(1 - t/2)` and strictness factor `(1 - t/2)/(1 - t)`
  — weaker than `1/(1 - t)` but still above one, which is all the argument needs.
  The DIRECTION claim in that file is right; only the weights are misdescribed.
* `Gtz.nearPencilSixDesign`, `Gtz.nearPencilSixDesign_hasLinePattern`,
  `Gtz.solePoleLinePattern` (`Gtz.Design.NearPencilTransport`) — the exact
  rational near pencil at six points, reused here as the non-vacuity witness.
* `Gtz.stratumIsTieFree_fano`, `Gtz.stratumIsTieFree_comp_relabel`,
  `Gtz.hingeHoldsAtSize_of_relabelLedger`, `Gtz.LinePattern`,
  `Gtz.HasLinePattern`, `Gtz.StratumIsTieFree`, `Gtz.fanoLinePattern`,
  `Gtz.PatternListIsCompleteUpToRelabel` (`Gtz.Design.PrimitiveTightClassification`).
* `Gtz.tetraDesign_isTie` (`Gtz.Ties.TetrahedronCertifiedTie`),
  `Gtz.diamondDesign_isTie` (`Gtz.Design.DiamondPrimitive`),
  `Gtz.splitTetraDesign_isTie`, `Gtz.splitTetraAtom`, `Gtz.splitTetraDirIndex`
  (`Gtz.Ties.SplitTetrahedronTie`), `Gtz.tetraAtom_dot_self`
  (`Gtz.Design.StressCertificate`) — the three ties at, below, and at the
  hinge's lower size, used only as controls.
* `Gtz.posDef_sub_vecMulVec_iff` (`Gtz.LinAlg.SchurRankOne`),
  `Gtz.posSemidef_congr_right` / `Gtz.exists_congruence_to_one`
  (`Gtz.LinAlg.PsdKit`), `Gtz.weight_lt_one` / `Gtz.sum_weighted_leverage`
  (`Gtz.Core.Sanity`), `Gtz.weighted_leverage_le_one` /
  `Gtz.leverageOf_eq_dotProduct` (`Gtz.Design.LeverageBound`).

## MEASURED, outside Lean — the ledger's state, and it is NOT closed

The count after the near-pencil transport landed is THREE of thirty-two
isomorphism classes mechanized and TWENTY-NINE open:

* mechanized: `F7` at seven points (`Gtz.stratumIsTieFree_fano`, one class,
  equivalently thirty labelled strata) and the two near pencils `q6m3` (a
  five-point line among six) and `q7m4` (a six-point line among seven), the
  latter two via `Gtz.stratumIsTieFree_nearPencil`;
* attained and OUTSIDE the hinge: `U(3,4)` at four points and the diamond
  `M(K4 - e)` at five, both already in the repository, which is why the hinge is
  asserted from six points on;
* open: the remaining twenty-nine — EIGHT of the nine at six points (all but
  `q6m3`) and TWENTY-ONE of the twenty-three at seven (all but `q7m4` and the
  Fano `q7m22`).  Eight plus twenty-one is twenty-nine.

Two independent exact-rational sweeps agree on the enumeration: class counts
`2, 4, 9, 23` at four through seven points, labelled-stratum counts `352` at six
and `8389` at seven, `|Aut(F7)| = 168` with `7!/168 = 30` labellings.  A third,
fully independent enumeration (linear spaces as families of at-least-three-point
subsets pairwise meeting in at most one point, canonicalized under all `n!`
relabellings) reproduced every one of those numbers and landed on the same
indices for all five named entries, so no class is missing by omission.  Beyond
the counts, three findings bear on how the open entries can be attacked, all
measured and none proved here.

* Exact rational realizations exist for all thirty-one non-Fano classes, so
  `F7` is the ONLY class that dies by non-representability over the reals.  There
  is no second free win of that shape at these sizes.
* The complex-emptiness route is DEAD on every realizable class: for each one a
  pair of rational endpoints was exhibited between which `det(S_B - I)` changes
  sign along a segment interior to the open stratum, so the tie-EQUATION variety
  has real points and the ideal does not contain one.  The inequation and
  definiteness half is load-bearing everywhere, exactly as the classification
  file says.
* `M(K4)` has value exactly `1/(1 - eps)` on the family that switches its sixth
  edge on with weight `eps`, confirmed at eighty digits and then in exact
  rationals; the boundary point is the `(5,3)` diamond tie.  So its infimum is
  inherited from one size down and no argument continuous up to the closure can
  work there.  Two bookkeeping cautions on the sequence quoted in the
  classification file (`6345, 498.88, 161.67, 11.23, 1.0842`): those are
  determinants of the LAPLACIAN-FORM CONGRUENT gap
  `sum_e (c_e/t_e) b_e b_e^T - L`, reproduced exactly as
  `6345, 79821/160, 65477/405, 605496767/53905500, ...`; the literal
  `det(S_B - I) = det(gap)/det(L)` is `32.538, 2.735, 0.8952, 0.0624, 0.006024`.
  Both are positive throughout, so the no-tie conclusion is unaffected, but the
  two sequences must not be confused.  Separately, the floor above kills that
  family's entire `eps`-branch outright — its minimum leverages are
  `2/13, 10/301, 100/30001, 1000/3000001`, all far below one — without touching
  the rest of the stratum, which is why `M(K4)` stays open.

Naimark duality yields no reduction of the ledger: at six points the involution
fixes six of the nine classes and sends the other three to non-simple matroids,
so there is no dual PAIR to exploit, and at seven points it exports to rank four
and off this rung.  Confirmed exactly by matroid duality on all nine classes.

`PatternListIsCompleteUpToRelabel` — the enumeration itself — was unproved and
listless when this file was written, and both gaps have since closed at six
points.  `Gtz.linePatternListSix` and `Gtz.linePatternListSeven` ship in
`Gtz.Design.LinePatternEnumeration`; `Gtz.patternListIsCompleteUpToRelabel_six`
and `Gtz.linearSpaceListIsComplete_six` are hypothesis-free theorems in
`Gtz.Design.LinePatternSixCasesTwo`, as is the four-point sibling.  Seven points
is still open.  Every assembly below still takes the enumeration as a named
hypothesis, which is now dischargeable at six points and genuine at seven.  A boundary-behaviour measurement worth recording because it
constrains attacks rather than settling anything: with the design constrained
only by Parseval (Stiefel rows) and a barrier holding the non-line brackets off
zero, both known-tie classes register as INTERIOR ties (all constraints slack)
while every size-six class tested registers as boundary-pinned, at excesses down
to `6.1e-07` — the collar-boundary signature is uniform across the size-six
classes, not special to `M(K4)`.  At those located near-optima the minimum
leverage is at least `1.0003`, so it is the bracket barrier and not the leverage
floor that stops the descent: the floor shrinks each open entry's system as a
statement, and does not bind at the points the search actually reaches.

No tie was found on any class the ledger calls empty.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Core.Sanity
import Gtz.LinAlg.PsdKit
import Gtz.LinAlg.SchurRankOne
import Gtz.Design.LeverageBound
import Gtz.Design.CollaredCompact
import Gtz.Design.DiamondPrimitive
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.NearPencilStrictDomination
import Gtz.Design.NearPencilTransport
import Gtz.Reduction.Deflation
import Gtz.Reduction.Reductions
import Gtz.Reduction.SplitTransfer
import Gtz.Ties.TetrahedronCertifiedTie
import Gtz.Ties.SplitTetrahedronTie

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz

open Matrix

variable {m k : ℕ}

/-! ## The two rank-one definiteness pivots

Deflating at a label needs its pivot `I - t g g^T` positive definite, and
reading strictness back off the transported gap needs `I - g g^T` positive
definite.  The two conditions are the share and the leverage falling strictly
below one, and they are genuinely different: at a near-pencil pole the share is
exactly one while the leverage is `1/t > 1`. -/

/-- **A strictly light atom has a positive-definite complement.**  `I - g g^T`
is positive definite exactly when `|g|^2 < 1`; this is the summand that turns a
transported weak domination into a strict one. -/
theorem posDef_one_sub_atomMatrix_of_leverage_lt_one (atomVec : Fin k → ℝ)
    (hlight : leverageOf atomVec < 1) :
    ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix atomVec).PosDef := by
  rw [atomMatrix, posDef_sub_vecMulVec_iff _ Matrix.PosDef.one, inv_one,
    Matrix.one_mulVec, ← leverageOf_eq_dotProduct]
  exact hlight

/-! ## The sharp deflation transport

`Gtz.dominating_of_light_atom` throws away the quantitative content of the
pullback: its conclusion is `S_C >= I`, which a tie already satisfies, so it
cannot exclude one.  The pullback actually proves a Loewner INEQUALITY between
the gap and the deflated atom's complement, and that inequality is what the rest
of this file runs on.  Stated multiplied through by `1 - t_d` so no division
appears. -/

/-- **The deflated gap bound.**  Whitening away the label `dropLabel`, whose
share is below one, and importing a dominating subset of the smaller design
yields a subset `selected` of the SURVIVORS with

  `(1 - t_d) (S_selected - I) >= t_d (I - g_d g_d^T)` .

Both the membership statement (`dropLabel` is absent) and the Loewner bound are
new relative to `Gtz.dominating_of_light_atom`, whose conclusion is the weaker
`S_selected >= I` and only under the stronger hypothesis `|g_d|^2 <= 1`. -/
theorem exists_deflatedGapBound (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (dropLabel : Fin (m + 1))
    (hshare : D.weight dropLabel * leverageOf (D.atom dropLabel) < 1) :
    ∃ selected : Finset (Fin (m + 1)), selected.card = k ∧ dropLabel ∉ selected ∧
      (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
        - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))).PosSemidef := by
  classical
  have hweightPos := D.weight_pos dropLabel
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hSurvivingMass : (0 : ℝ) < 1 - D.weight dropLabel := by linarith
  have hPivotPosDef :
      ((1 : Matrix (Fin k) (Fin k) ℝ) - D.weight dropLabel • atomMatrix (D.atom dropLabel)).PosDef :=
    posDef_one_sub_smul_atomMatrix_of_share_lt_one hweightPos hshare
  obtain ⟨whitener, hwhitenerUnit, hwhitenerPivot⟩ := exists_congruence_to_one hPivotPosDef
  obtain ⟨smallerSubset, hsmallerCard, hsmallerDominates⟩ :=
    hsmaller (deflatedDesign D dropLabel whitener hSurvivingMass hwhitenerPivot)
  have hEmbeddingInjective : Function.Injective dropLabel.succAbove :=
    Fin.succAbove_right_injective
  refine ⟨smallerSubset.image dropLabel.succAbove, ?_, ?_, ?_⟩
  · rw [Finset.card_image_of_injective _ hEmbeddingInjective, hsmallerCard]
  · intro hMem
    obtain ⟨survivor, _, hsurvivor⟩ := Finset.mem_image.mp hMem
    exact Fin.succAbove_ne dropLabel survivor hsurvivor
  · -- the deflated domination, in explicit-sum form
    have hDeflatedDominates : ((∑ survivor ∈ smallerSubset,
        atomMatrix (Real.sqrt (1 - D.weight dropLabel)
          • (whitenerᵀ *ᵥ D.atom (dropLabel.succAbove survivor)))) - 1).PosSemidef :=
      hsmallerDominates
    -- that sum is the congruated, scaled primal subset sum
    have hScaledSum : ∑ survivor ∈ smallerSubset,
          atomMatrix (Real.sqrt (1 - D.weight dropLabel)
            • (whitenerᵀ *ᵥ D.atom (dropLabel.succAbove survivor)))
        = whitenerᵀ * (((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (smallerSubset.image dropLabel.succAbove)) * whitener := by
      rw [subsetSum, Finset.sum_image fun a _ b _ hab => hEmbeddingInjective hab,
        Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_sum, Matrix.sum_mul,
        Finset.smul_sum]
      exact Finset.sum_congr rfl fun survivor _ => by
        rw [atomMatrix_smul, Real.sq_sqrt hSurvivingMass.le, transpose_mul_atomMatrix_mul]
    have hShiftedSymmetric : ((((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (smallerSubset.image dropLabel.succAbove))
          - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel)))ᵀ
        = (((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (smallerSubset.image dropLabel.succAbove))
          - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel)) := by
      rw [Matrix.transpose_sub, Matrix.transpose_smul, subsetSum_transpose,
        Matrix.transpose_sub, Matrix.transpose_one, Matrix.transpose_smul,
        transpose_eq_of_isHermitian (posSemidef_atomMatrix (D.atom dropLabel)).1]
    have hShiftedPosSemidef : ((((1 : ℝ) - D.weight dropLabel)
        • subsetSum D (smallerSubset.image dropLabel.succAbove))
        - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel))).PosSemidef := by
      refine (posSemidef_congr_right hShiftedSymmetric hwhitenerUnit).mpr ?_
      have hExpand : whitenerᵀ * ((((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (smallerSubset.image dropLabel.succAbove))
            - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel))) * whitener
          = (∑ survivor ∈ smallerSubset,
              atomMatrix (Real.sqrt (1 - D.weight dropLabel)
                • (whitenerᵀ *ᵥ D.atom (dropLabel.succAbove survivor)))) - 1 := by
        rw [Matrix.mul_sub, Matrix.sub_mul, hwhitenerPivot, ← hScaledSum]
      rw [hExpand]
      exact hDeflatedDominates
    have hRearranged : ((1 : ℝ) - D.weight dropLabel)
          • (subsetSum D (smallerSubset.image dropLabel.succAbove) - 1)
          - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))
        = (((1 : ℝ) - D.weight dropLabel)
            • subsetSum D (smallerSubset.image dropLabel.succAbove))
          - (1 - D.weight dropLabel • atomMatrix (D.atom dropLabel)) := by
      module
    rw [hRearranged]
    exact hShiftedPosSemidef

/-- **The gap bound's two-dimensional half.**  Whatever the deflated label's
leverage, the transported gap is strictly positive on every direction orthogonal
to that label's atom, with margin `t_d/(1 - t_d)` after undoing the scaling.  So
a singular direction of the gap must pair nontrivially against `g_d`, which is
the structural content the leverage floor below extracts. -/
theorem posDef_on_orthogonal_of_deflatedGapBound (D : WeightedDesign (m + 1) k)
    (dropLabel : Fin (m + 1)) (selected : Finset (Fin (m + 1)))
    (hbound : (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
      - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))).PosSemidef)
    (hsize : 1 ≤ m) (probeVec : Fin k → ℝ) (hProbeNe : probeVec ≠ 0)
    (hOrthogonal : D.atom dropLabel ⬝ᵥ probeVec = 0) :
    0 < probeVec ⬝ᵥ ((subsetSum D selected - 1) *ᵥ probeVec) := by
  have hweightPos := D.weight_pos dropLabel
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hSurvivingMass : (0 : ℝ) < 1 - D.weight dropLabel := by linarith
  have hProbePos : 0 < probeVec ⬝ᵥ probeVec := dotProduct_self_pos hProbeNe
  have hInnerComplement : probeVec ⬝ᵥ
        (((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel)) *ᵥ probeVec)
      = probeVec ⬝ᵥ probeVec := by
    rw [Matrix.sub_mulVec, dotProduct_sub, Matrix.one_mulVec, atomMatrix,
      vecMulVec_mulVec_eq, dotProduct_smul, smul_eq_mul,
      dotProduct_comm probeVec (D.atom dropLabel), hOrthogonal, mul_zero, sub_zero]
  have hBoundForm := (Matrix.posSemidef_iff_dotProduct_mulVec.mp hbound).2 probeVec
  rw [star_trivial, Matrix.sub_mulVec, dotProduct_sub, Matrix.smul_mulVec,
    dotProduct_smul, smul_eq_mul, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul,
    hInnerComplement] at hBoundForm
  nlinarith [hBoundForm, mul_pos hweightPos hProbePos, hSurvivingMass]

/-! ## Strict light-atom deflation, and the leverage floor at a tie

`Gtz.dominating_of_light_atom` concludes weak domination from `|g_d|^2 <= 1`.
Under the strict hypothesis the deflated atom's complement is positive definite,
so the gap bound upgrades to positive definiteness and the design cannot be a
tie.  Contrapositive: at a tie every atom is heavy. -/

/-- **Strictly light means strictly dominating.**  An atom of leverage below one
forces a `k`-subset of the OTHER labels whose gap is positive definite, granted
weighted GTZ one size down.  Strictly stronger than
`Gtz.dominating_of_light_atom`, and the strictness is what excludes a tie. -/
theorem exists_posDef_of_lightAtom (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (dropLabel : Fin (m + 1))
    (hlight : leverageOf (D.atom dropLabel) < 1) :
    ∃ selected : Finset (Fin (m + 1)), selected.card = k ∧ dropLabel ∉ selected ∧
      (subsetSum D selected - 1).PosDef := by
  have hweightPos := D.weight_pos dropLabel
  have hweightLtOne : D.weight dropLabel < 1 := weight_lt_one D (by omega) dropLabel
  have hSurvivingMass : (0 : ℝ) < 1 - D.weight dropLabel := by linarith
  have hLeverageNonneg : 0 ≤ leverageOf (D.atom dropLabel) :=
    Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hshare : D.weight dropLabel * leverageOf (D.atom dropLabel) < 1 := by
    nlinarith [hweightPos, hweightLtOne, hlight, hLeverageNonneg]
  obtain ⟨selected, hcard, hAvoidsDrop, hbound⟩ :=
    exists_deflatedGapBound D hsize hsmaller dropLabel hshare
  refine ⟨selected, hcard, hAvoidsDrop, ?_⟩
  have hComplementPosDef :
      (D.weight dropLabel • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel))).PosDef :=
    (posDef_one_sub_atomMatrix_of_leverage_lt_one _ hlight).smul hweightPos
  have hScaledGapPosDef :
      (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)).PosDef := by
    have hSplit : ((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
        = D.weight dropLabel • ((1 : Matrix (Fin k) (Fin k) ℝ) - atomMatrix (D.atom dropLabel))
          + (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)
            - D.weight dropLabel • (1 - atomMatrix (D.atom dropLabel))) := by
      module
    rw [hSplit]
    exact hComplementPosDef.add_posSemidef hbound
  have hUnscale : subsetSum D selected - 1
      = (((1 : ℝ) - D.weight dropLabel)⁻¹)
        • (((1 : ℝ) - D.weight dropLabel) • (subsetSum D selected - 1)) := by
    rw [smul_smul, inv_mul_cancel₀ hSurvivingMass.ne', one_smul]
  rw [hUnscale]
  exact hScaledGapPosDef.smul (inv_pos.mpr hSurvivingMass)

/-- **A design with a strictly light atom is not a tie.** -/
theorem not_isTie_of_lightAtom (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (dropLabel : Fin (m + 1))
    (hlight : leverageOf (D.atom dropLabel) < 1) : ¬ IsTie D := by
  intro htie
  obtain ⟨selected, hcard, _, hposDef⟩ :=
    exists_posDef_of_lightAtom D hsize hsmaller dropLabel hlight
  exact htie.2 selected hcard hposDef

/-- **The leverage floor at a tie.**  Every atom of a tie has leverage at least
one, granted weighted GTZ one size down.  Combined with the per-atom ceiling
`Gtz.weighted_leverage_le_one` this pins each share into `(t_c, 1]`
(`share_bracket_of_isTie`); combined with `Gtz.sum_weighted_leverage` the shares
still sum to the rank, so the floor constrains a tie without deciding it. -/
theorem leverage_one_le_of_isTie (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (htie : IsTie D) (label : Fin (m + 1)) :
    1 ≤ leverageOf (D.atom label) := by
  by_contra hlight
  exact not_isTie_of_lightAtom D hsize hsmaller label (lt_of_not_ge hlight) htie

/-! ## The floor at the hinge's lower size, unconditionally

At six points the input is `GtzWeighted 5 3`, which is landed, so the floor is a
theorem with no hypothesis.  At seven points the same argument needs
`GtzWeighted 6 3`; that instance is open and appears as a named hypothesis in
every size-seven statement below. -/

/-- **Every atom of a `(6,3)` tie is heavy**, unconditionally.  The input is
`Gtz.gtzWeighted_of_le_five` at five points, so no open instance is assumed and
no criticality argument is used.  The conclusion is `1 <= |g|^2`; the strict
`Gtz.AllHeavy` needs the dichotomy below. -/
theorem leverage_one_le_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    (label : Fin 6) : 1 ≤ leverageOf (D.atom label) :=
  leverage_one_le_of_isTie (m := 5) (k := 3) D (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) htie label

/-- **Every atom of a `(7,3)` tie is heavy**, granted the open `GtzWeighted 6 3`. -/
theorem leverage_one_le_of_isTie_sevenThree (hsixThree : GtzWeighted 6 3)
    (D : WeightedDesign 7 3) (htie : IsTie D) (label : Fin 7) :
    1 ≤ leverageOf (D.atom label) :=
  leverage_one_le_of_isTie (m := 6) (k := 3) D (by norm_num) hsixThree htie label

/-- **Every atom of a `(4,3)` tie is heavy** — the same statement one rung below
the hinge, where a tie provably exists (`Gtz.tetraDesign_isTie`).  Kept so the
floor is visibly a statement about an inhabited situation. -/
theorem leverage_one_le_of_isTie_fourThree (D : WeightedDesign 4 3) (htie : IsTie D)
    (label : Fin 4) : 1 ≤ leverageOf (D.atom label) :=
  leverage_one_le_of_isTie (m := 3) (k := 3) D (by norm_num)
    (gtzWeighted_of_le_five 3 3 (by norm_num) (by norm_num)) htie label

/-- **Every atom of a `(5,3)` tie is heavy** — the diamond's rung. -/
theorem leverage_one_le_of_isTie_fiveThree (D : WeightedDesign 5 3) (htie : IsTie D)
    (label : Fin 5) : 1 ≤ leverageOf (D.atom label) :=
  leverage_one_le_of_isTie (m := 4) (k := 3) D (by norm_num)
    (gtzWeighted_of_le_five 4 3 (by norm_num) (by norm_num)) htie label

/-! ## The floor against the repository's strict predicate

`Gtz.AllHeavy` is `forall c, 1 < leverageOf (D.atom c)` and is what every shipped
heavy theorem consumes — `Gtz.GtzWeightedHeavy`, `Gtz.gtzWeightedAll_of_heavy`,
`Gtz.rank_three_of_heavy_residuals`.  The floor delivers only `1 <=`, and the
method cannot do better: at leverage exactly one the deflated complement is
singular and the transport yields weak domination, which a tie already has.  The
honest statement is therefore a dichotomy, and the residue it names is a
BOUNDARY, not an oversight. -/

/-- **Every tie is all-heavy, or has an atom of leverage exactly one.**  The
first alternative is the repository's `Gtz.AllHeavy`; the second is the boundary
the floor cannot cross. -/
theorem allHeavy_or_exists_leverage_eq_one_of_isTie (D : WeightedDesign (m + 1) k)
    (hsize : 1 ≤ m) (hsmaller : GtzWeighted m k) (htie : IsTie D) :
    AllHeavy D ∨ ∃ label : Fin (m + 1), leverageOf (D.atom label) = 1 := by
  classical
  by_cases hstrict : ∀ label : Fin (m + 1), 1 < leverageOf (D.atom label)
  · exact Or.inl hstrict
  · obtain ⟨label, hlabel⟩ := not_forall.mp hstrict
    exact Or.inr ⟨label, le_antisymm (not_lt.mp hlabel)
      (leverage_one_le_of_isTie D hsize hsmaller htie label)⟩

/-- **The dichotomy at `(6,3)`, unconditionally.** -/
theorem allHeavy_or_exists_leverage_eq_one_of_isTie_sixThree (D : WeightedDesign 6 3)
    (htie : IsTie D) : AllHeavy D ∨ ∃ label : Fin 6, leverageOf (D.atom label) = 1 :=
  allHeavy_or_exists_leverage_eq_one_of_isTie (m := 5) (k := 3) D (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) htie

/-- **The dichotomy at `(7,3)`**, granted the open `GtzWeighted 6 3`. -/
theorem allHeavy_or_exists_leverage_eq_one_of_isTie_sevenThree (hsixThree : GtzWeighted 6 3)
    (D : WeightedDesign 7 3) (htie : IsTie D) :
    AllHeavy D ∨ ∃ label : Fin 7, leverageOf (D.atom label) = 1 :=
  allHeavy_or_exists_leverage_eq_one_of_isTie (m := 6) (k := 3) D (by norm_num) hsixThree htie

/-- **The share bracket at a tie.**  The floor from this file against the shipped
ceiling `Gtz.weighted_leverage_le_one`: each share `t_c |g_c|^2` sits between the
weight and one, so the weight never exceeds its own share. -/
theorem share_bracket_of_isTie (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (htie : IsTie D) (label : Fin (m + 1)) :
    D.weight label ≤ D.weight label * leverageOf (D.atom label) ∧
      D.weight label * leverageOf (D.atom label) ≤ 1 := by
  refine ⟨?_, weighted_leverage_le_one D label⟩
  have hfloor := leverage_one_le_of_isTie D hsize hsmaller htie label
  nlinarith [D.weight_pos label]

/-- **The excess normalization at a tie.**  The leverage excesses `|g_c|^2 - 1`
(the repository's `heavyExcess`) are pointwise nonnegative at a tie, and their
weighted total is exactly `k - 1`.  So the floor turns the Parseval trace
identity into a genuine probability-weighted normalization of a NONNEGATIVE
vector, which is the form an open entry can use. -/
theorem sum_weighted_leverage_excess_of_isTie (D : WeightedDesign (m + 1) k) (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m k) (htie : IsTie D) :
    (∑ label, D.weight label * (leverageOf (D.atom label) - 1)) = (k : ℝ) - 1 ∧
      ∀ label : Fin (m + 1), 0 ≤ D.weight label * (leverageOf (D.atom label) - 1) := by
  refine ⟨?_, fun label => mul_nonneg (D.weight_pos label).le ?_⟩
  · have hsplit : (∑ label, D.weight label * (leverageOf (D.atom label) - 1))
        = (∑ label, D.weight label * leverageOf (D.atom label))
          - ∑ label : Fin (m + 1), D.weight label := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun label _ => by ring
    rw [hsplit, sum_weighted_leverage D, D.weight_sum_one]
  · have hfloor := leverage_one_le_of_isTie D hsize hsmaller htie label
    linarith

/-- **Every `(6,3)` tie's configuration is collared.**  `Gtz.collaredSet`'s
leverage hypothesis is literally the floor, so the floor discharges it outright.
The weight floor stays a hypothesis: `Gtz.isCompact_collaredSet` needs it
POSITIVE, and a tie supplies only strict positivity per label, not a uniform
bound across a family. -/
theorem design_mem_collaredSet_of_isTie_sixThree (D : WeightedDesign 6 3) (htie : IsTie D)
    {weightFloor : ℝ} (hweights : ∀ label : Fin 6, weightFloor ≤ D.weight label) :
    (D.atom, D.weight) ∈ collaredSet 6 3 weightFloor :=
  design_mem_collaredSet D hweights (leverage_one_le_of_isTie_sixThree D htie)

/-! ## The narrowed per-class obligation

A ledger entry asks tie-freeness of a whole stratum.  The floor lets it ask only
of the ALL-HEAVY designs on that stratum, which is a strictly smaller
semialgebraic set: the inequalities `|g_c|^2 >= 1` may be added to every open
entry's system for free.  The reduction is unconditional at six points. -/

/-- Tie-freeness asked only of the designs whose every atom is heavy.  Weaker
than `Gtz.StratumIsTieFree`, and by the floor equivalent to it at the hinge's
sizes.  The inequality is non-strict; `StratumIsTieFreeAmongAllHeavy` below is
the strict form that matches `Gtz.AllHeavy`. -/
def StratumIsTieFreeAmongHeavy {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∀ D : WeightedDesign size 3, HasLinePattern D pattern →
    (∀ label : Fin size, 1 ≤ leverageOf (D.atom label)) → ¬ IsTie D

/-- The narrowed obligation is genuinely weaker: full tie-freeness implies it. -/
theorem stratumIsTieFreeAmongHeavy_of_stratumIsTieFree {size : ℕ}
    {pattern : LinePattern size} (hfree : StratumIsTieFree pattern) :
    StratumIsTieFreeAmongHeavy pattern :=
  fun D hpattern _ => hfree D hpattern

/-- **The narrowed obligation suffices**, at any size one above a settled one. -/
theorem stratumIsTieFree_of_amongHeavy {m : ℕ} (hsize : 1 ≤ m)
    (hsmaller : GtzWeighted m 3) {pattern : LinePattern (m + 1)}
    (hheavyFree : StratumIsTieFreeAmongHeavy pattern) : StratumIsTieFree pattern :=
  fun D hpattern htie =>
    hheavyFree D hpattern (fun label => leverage_one_le_of_isTie D hsize hsmaller htie label) htie

/-- **At six points the narrowing is free.**  An open ledger entry at `(6,3)` may
assume every atom heavy with no extra hypothesis anywhere. -/
theorem stratumIsTieFree_of_amongHeavy_sixThree {pattern : LinePattern 6}
    (hheavyFree : StratumIsTieFreeAmongHeavy pattern) : StratumIsTieFree pattern :=
  stratumIsTieFree_of_amongHeavy (m := 5) (by norm_num)
    (gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num)) hheavyFree

/-- The size-seven form of the narrowing, which needs the open `GtzWeighted 6 3`. -/
theorem stratumIsTieFree_of_amongHeavy_sevenThree (hsixThree : GtzWeighted 6 3)
    {pattern : LinePattern 7} (hheavyFree : StratumIsTieFreeAmongHeavy pattern) :
    StratumIsTieFree pattern :=
  stratumIsTieFree_of_amongHeavy (m := 6) (by norm_num) hsixThree hheavyFree

/-! ## The narrowed obligation split along the repository's strict predicate

`StratumIsTieFreeAmongHeavy` carries `1 <= |g_c|^2`, which plugs into none of the
shipped heavy theorems — those want `Gtz.AllHeavy`.  Splitting the obligation at
the boundary hands an open entry the strict predicate, and hence the whole heavy
toolkit, at the cost of one extra clause about the measure-zero face where some
leverage equals one exactly. -/

/-- Tie-freeness asked only of `Gtz.AllHeavy` designs — the STRICT heavy
restriction, the one the shipped heavy machinery is stated against. -/
def StratumIsTieFreeAmongAllHeavy {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∀ D : WeightedDesign size 3, HasLinePattern D pattern → AllHeavy D → ¬ IsTie D

/-- Tie-freeness on the boundary face the floor cannot cross: some atom of
leverage exactly one.  This is the residue the split names. -/
def StratumIsTieFreeAtUnitLeverage {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∀ D : WeightedDesign size 3, HasLinePattern D pattern →
    (∃ label : Fin size, leverageOf (D.atom label) = 1) → ¬ IsTie D

/-- **The split.**  Strict-heavy tie-freeness plus unit-leverage tie-freeness give
the non-strict form, because a heavy design failing `Gtz.AllHeavy` has an atom of
leverage exactly one. -/
theorem stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage {size : ℕ}
    {pattern : LinePattern size}
    (hallHeavyFree : StratumIsTieFreeAmongAllHeavy pattern)
    (hunitFree : StratumIsTieFreeAtUnitLeverage pattern) :
    StratumIsTieFreeAmongHeavy pattern := by
  classical
  intro D hpattern hheavy htie
  by_cases hstrict : ∀ label : Fin size, 1 < leverageOf (D.atom label)
  · exact hallHeavyFree D hpattern hstrict htie
  · obtain ⟨label, hlabel⟩ := not_forall.mp hstrict
    exact hunitFree D hpattern ⟨label, le_antisymm (not_lt.mp hlabel) (hheavy label)⟩ htie

/-- **The sharpest reduction at six points.**  A `(6,3)` ledger entry may be
discharged by treating the `Gtz.AllHeavy` designs and the unit-leverage face
separately, with no hypothesis anywhere. -/
theorem stratumIsTieFree_of_allHeavy_and_unitLeverage_sixThree {pattern : LinePattern 6}
    (hallHeavyFree : StratumIsTieFreeAmongAllHeavy pattern)
    (hunitFree : StratumIsTieFreeAtUnitLeverage pattern) : StratumIsTieFree pattern :=
  stratumIsTieFree_of_amongHeavy_sixThree
    (stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage hallHeavyFree hunitFree)

/-- The size-seven form of the split reduction. -/
theorem stratumIsTieFree_of_allHeavy_and_unitLeverage_sevenThree (hsixThree : GtzWeighted 6 3)
    {pattern : LinePattern 7} (hallHeavyFree : StratumIsTieFreeAmongAllHeavy pattern)
    (hunitFree : StratumIsTieFreeAtUnitLeverage pattern) : StratumIsTieFree pattern :=
  stratumIsTieFree_of_amongHeavy_sevenThree hsixThree
    (stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage hallHeavyFree hunitFree)

/-! ## Patterns that define the same stratum

`Gtz.HasLinePattern` is an iff over DISTINCT triples only, so a pattern's values
on degenerate triples are invisible to the stratum it cuts out.  Recognizers must
therefore compare patterns on distinct triples, never as total functions; the two
representatives already in the repository disagree on the diagonal, so no
normalization convention is available to assume. -/

/-- Two patterns agree wherever `Gtz.HasLinePattern` can see them, hence define
the same stratum. -/
def AgreesOnDistinctTriples {size : ℕ} (pattern basePattern : LinePattern size) : Prop :=
  ∀ leftLabel midLabel rightLabel : Fin size,
    leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
      (pattern leftLabel midLabel rightLabel ↔ basePattern leftLabel midLabel rightLabel)

/-- Agreement on distinct triples is reflexive. -/
theorem agreesOnDistinctTriples_refl {size : ℕ} (pattern : LinePattern size) :
    AgreesOnDistinctTriples pattern pattern :=
  fun _ _ _ _ _ _ => Iff.rfl

/-- **The stratum only sees distinct triples.**  A design realizing one pattern
realizes every pattern agreeing with it on distinct triples. -/
theorem hasLinePattern_of_agreesOnDistinctTriples {size : ℕ} {D : WeightedDesign size 3}
    {pattern basePattern : LinePattern size} (hpattern : HasLinePattern D pattern)
    (hagree : AgreesOnDistinctTriples pattern basePattern) :
    HasLinePattern D basePattern :=
  fun leftLabel midLabel rightLabel hleftMid hleftRight hmidRight =>
    (hpattern leftLabel midLabel rightLabel hleftMid hleftRight hmidRight).trans
      (hagree leftLabel midLabel rightLabel hleftMid hleftRight hmidRight)

/-- **Tie-freeness transports along agreement on distinct triples.** -/
theorem stratumIsTieFree_of_agreesOnDistinctTriples {size : ℕ}
    {pattern basePattern : LinePattern size}
    (hagree : AgreesOnDistinctTriples pattern basePattern)
    (hbaseFree : StratumIsTieFree basePattern) : StratumIsTieFree pattern :=
  fun D hpattern => hbaseFree D (hasLinePattern_of_agreesOnDistinctTriples hpattern hagree)

/-! ## The discharged entries as recognizers

A ledger is a list of patterns, and the discharged classes should be peeled off
it structurally rather than matched against three names by hand.  `IsRelabelOf`
names "same pattern up to relabelling" and
`IsRelabelOfOnDistinctTriples` names "same STRATUM up to relabelling", which is
the correct notion; the two recognizers below are the near pencil and the Fano,
and each carries its own tie-freeness. -/

/-- One pattern is a relabelling of another, as total functions.
`Gtz.stratumIsTieFree_comp_relabel` is exactly what makes tie-freeness invariant
under this.  Too strict for a ledger — see
`IsRelabelOfOnDistinctTriples`. -/
def IsRelabelOf {size : ℕ} (pattern basePattern : LinePattern size) : Prop :=
  ∃ relabel : Equiv.Perm (Fin size),
    pattern = fun leftLabel midLabel rightLabel =>
      basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)

/-- Relabelling-equivalence is reflexive, witnessed by the identity. -/
theorem isRelabelOf_refl {size : ℕ} (pattern : LinePattern size) :
    IsRelabelOf pattern pattern :=
  ⟨Equiv.refl _, rfl⟩

/-- **Tie-freeness transports along a relabelling.** -/
theorem stratumIsTieFree_of_isRelabelOf {size : ℕ} {pattern basePattern : LinePattern size}
    (hrelabel : IsRelabelOf pattern basePattern) (hbaseFree : StratumIsTieFree basePattern) :
    StratumIsTieFree pattern := by
  obtain ⟨relabel, hpattern⟩ := hrelabel
  rw [hpattern]
  exact stratumIsTieFree_comp_relabel basePattern relabel hbaseFree

/-- One pattern cuts out the same stratum as a relabelling of another.  This is
the recognizer notion: it is invariant under everything `Gtz.HasLinePattern`
cannot distinguish. -/
def IsRelabelOfOnDistinctTriples {size : ℕ} (pattern basePattern : LinePattern size) : Prop :=
  ∃ relabel : Equiv.Perm (Fin size),
    AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
      basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel))

/-- The strict notion implies the stratum-correct one. -/
theorem isRelabelOfOnDistinctTriples_of_isRelabelOf {size : ℕ}
    {pattern basePattern : LinePattern size} (hrelabel : IsRelabelOf pattern basePattern) :
    IsRelabelOfOnDistinctTriples pattern basePattern := by
  obtain ⟨relabel, hpattern⟩ := hrelabel
  refine ⟨relabel, ?_⟩
  rw [hpattern]
  exact agreesOnDistinctTriples_refl _

/-- **Tie-freeness transports along the stratum-correct relabelling notion.** -/
theorem stratumIsTieFree_of_isRelabelOfOnDistinctTriples {size : ℕ}
    {pattern basePattern : LinePattern size}
    (hrelabel : IsRelabelOfOnDistinctTriples pattern basePattern)
    (hbaseFree : StratumIsTieFree basePattern) : StratumIsTieFree pattern := by
  obtain ⟨relabel, hagree⟩ := hrelabel
  exact stratumIsTieFree_of_agreesOnDistinctTriples hagree
    (stratumIsTieFree_comp_relabel basePattern relabel hbaseFree)

/-- The near-pencil classes: same stratum as some relabelling of some pole's near
pencil. -/
def IsNearPencilClass {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∃ poleLabel : Fin size, IsRelabelOfOnDistinctTriples pattern (nearPencilLinePattern poleLabel)

/-- The Fano class at seven points. -/
def IsFanoClass (pattern : LinePattern 7) : Prop :=
  IsRelabelOfOnDistinctTriples pattern fanoLinePattern

/-- **A relabelled near pencil is a near pencil**, at the moved pole.  So the
near-pencil family needs no relabelling closure: recognizing it up to
relabelling is the same as recognizing it on the nose. -/
theorem nearPencilLinePattern_comp_relabel {size : ℕ} (poleLabel : Fin size)
    (relabel : Equiv.Perm (Fin size)) :
    (fun leftLabel midLabel rightLabel =>
        nearPencilLinePattern poleLabel (relabel leftLabel) (relabel midLabel)
          (relabel rightLabel))
      = nearPencilLinePattern (relabel.symm poleLabel) := by
  funext leftLabel midLabel rightLabel
  have hmoved : ∀ label : Fin size,
      (relabel label ≠ poleLabel) = (label ≠ relabel.symm poleLabel) := by
    intro label
    exact propext (not_congr (relabel.apply_eq_iff_eq_symm_apply))
  rw [nearPencilLinePattern, nearPencilLinePattern, hmoved, hmoved, hmoved]

/-- **The near-pencil recognizer is pole-matching up to degeneracy.** -/
theorem isNearPencilClass_iff_exists_pole {size : ℕ} (pattern : LinePattern size) :
    IsNearPencilClass pattern ↔ ∃ poleLabel : Fin size,
      AgreesOnDistinctTriples pattern (nearPencilLinePattern poleLabel) := by
  constructor
  · rintro ⟨poleLabel, relabel, hagree⟩
    rw [nearPencilLinePattern_comp_relabel] at hagree
    exact ⟨relabel.symm poleLabel, hagree⟩
  · rintro ⟨poleLabel, hagree⟩
    exact ⟨poleLabel, Equiv.refl _, hagree⟩

/-- **The near-pencil entries are discharged**, at every size at least three and
whatever the pole.  Rides `Gtz.stratumIsTieFree_nearPencil`, whose proof is the
rank-two transport. -/
theorem stratumIsTieFree_of_isNearPencilClass {size : ℕ} (hsize : 3 ≤ size)
    {pattern : LinePattern size} (hclass : IsNearPencilClass pattern) :
    StratumIsTieFree pattern := by
  obtain ⟨poleLabel, hrelabel⟩ := hclass
  exact stratumIsTieFree_of_isRelabelOfOnDistinctTriples hrelabel
    (stratumIsTieFree_nearPencil hsize poleLabel)

/-- **The Fano entry is discharged.**  Rides `Gtz.stratumIsTieFree_fano`, whose
proof is that no seven vectors of three-space realize the Fano plane. -/
theorem stratumIsTieFree_of_isFanoClass {pattern : LinePattern 7}
    (hclass : IsFanoClass pattern) : StratumIsTieFree pattern :=
  stratumIsTieFree_of_isRelabelOfOnDistinctTriples hclass stratumIsTieFree_fano

/-! ## The degeneracy convention is not canonical, and the peel depends on it

Three facts, all proved: the two shipped representatives disagree on degenerate
triples, so no normalization is available to assume; and a pattern in the natural
normal form — false on every degenerate triple — cuts out exactly the near-pencil
stratum yet is a relabelling of NO pole's near pencil as a total function.  An
equality-based recognizer would therefore drop that presentation of the entry
silently. -/

/-- The near pencil is TRUE on the degenerate triple `(label, label, label)` for
every label off the pole. -/
theorem nearPencilLinePattern_self_of_ne {size : ℕ} {poleLabel witnessLabel : Fin size}
    (hne : witnessLabel ≠ poleLabel) :
    nearPencilLinePattern poleLabel witnessLabel witnessLabel witnessLabel :=
  ⟨hne, hne, hne⟩

/-- The Fano pattern is FALSE on every degenerate triple: the exclusive-or of
three equal nonzero labels is that label again. -/
theorem not_fanoLinePattern_diagonal (label : Fin 7) :
    ¬ fanoLinePattern label label label := by
  revert label
  decide

/-- The near pencil in normal form: false on every degenerate triple. -/
def nearPencilStrictPattern {size : ℕ} (poleLabel : Fin size) : LinePattern size :=
  fun leftLabel midLabel rightLabel =>
    leftLabel ≠ midLabel ∧ leftLabel ≠ rightLabel ∧ midLabel ≠ rightLabel ∧
      leftLabel ≠ poleLabel ∧ midLabel ≠ poleLabel ∧ rightLabel ≠ poleLabel

/-- **The normal form cuts out exactly the near-pencil stratum.** -/
theorem agreesOnDistinctTriples_nearPencilStrictPattern {size : ℕ} (poleLabel : Fin size) :
    AgreesOnDistinctTriples (nearPencilStrictPattern poleLabel)
      (nearPencilLinePattern poleLabel) := by
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight
  constructor
  · rintro ⟨-, -, -, hleft, hmid, hright⟩
    exact ⟨hleft, hmid, hright⟩
  · rintro ⟨hleft, hmid, hright⟩
    exact ⟨hleftMid, hleftRight, hmidRight, hleft, hmid, hright⟩

/-- **The recognizer accepts the normal form.** -/
theorem isNearPencilClass_nearPencilStrictPattern {size : ℕ} (poleLabel : Fin size) :
    IsNearPencilClass (nearPencilStrictPattern poleLabel) :=
  (isNearPencilClass_iff_exists_pole _).mpr
    ⟨poleLabel, agreesOnDistinctTriples_nearPencilStrictPattern poleLabel⟩

/-- **An equality-based recognizer would NOT accept it.**  The normal form is a
relabelling of no pole's near pencil as a total function, so building the peel on
`IsRelabelOf` rather than `IsRelabelOfOnDistinctTriples` would lose the entry
whenever a ledger presented it this way. -/
theorem not_isRelabelOf_nearPencilStrictPattern {size : ℕ} (hsize : 2 ≤ size)
    (poleLabel otherPole : Fin size) :
    ¬ IsRelabelOf (nearPencilStrictPattern poleLabel) (nearPencilLinePattern otherPole) := by
  rintro ⟨relabel, hpattern⟩
  rw [nearPencilLinePattern_comp_relabel] at hpattern
  obtain ⟨witnessLabel, hwitness⟩ := Fintype.exists_ne_of_one_lt_card
    (by simp only [Fintype.card_fin]; omega) (relabel.symm otherPole)
  have hstrict : nearPencilStrictPattern poleLabel witnessLabel witnessLabel witnessLabel := by
    rw [hpattern]
    exact nearPencilLinePattern_self_of_ne hwitness
  simp only [nearPencilStrictPattern] at hstrict
  exact hstrict.1 rfl

/-! ## The residual assemblies

Each theorem here is `Gtz.hingeHoldsAtSize_of_relabelLedger` with the discharged
recognizers already discharged, so the hypothesis it still takes is exactly the
residual obligation.  Nothing is claimed about whether the enumeration
hypothesis holds: `Gtz.PatternListIsCompleteUpToRelabel` is unproved in Lean and
is passed through untouched.

The conclusion is `Gtz.HingeHoldsAtSize size 3` on the nose.  The classification
file writes the hinge's body out because it does not import
`Gtz.Reduction.SplitTransfer`; this file does, so the correspondence its header
describes as definitional is exercised rather than described —
`isPrimitiveDesign_iff_not_hasParallelPair` records the other half of that
dictionary explicitly. -/

/-- **Primitivity is exactly the absence of a parallel pair.**  The two
predicates are the same statement with the negation pushed in;
`Gtz.IsPrimitiveDesign` lives in the classification file and
`Gtz.HasParallelPair` in the split-transfer file, and this is the bridge the
classification header says a wiring module needs. -/
theorem isPrimitiveDesign_iff_not_hasParallelPair {size rank : ℕ}
    (D : WeightedDesign size rank) : IsPrimitiveDesign D ↔ ¬ HasParallelPair D := by
  constructor
  · rintro hprimitive ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩
    exact hprimitive keptLabel dropLabel ratio hdistinct hparallel
  · intro hnoParallelPair keptLabel dropLabel ratio hdistinct hparallel
    exact hnoParallelPair ⟨keptLabel, dropLabel, ratio, hdistinct, hparallel⟩

/-- **The hinge from the residual ledger.**  A complete enumeration up to
relabelling plus tie-freeness of every listed class that is NOT a near pencil
gives `Gtz.HingeHoldsAtSize size 3`.  The near-pencil entries are paid by
`stratumIsTieFree_of_isNearPencilClass`.

At `size = 4` and `size = 5` the conclusion is FALSE
(`Gtz.not_hingeHoldsAtSize_five_three`; `Gtz.tetraDesign_isTie` and
`Gtz.diamondDesign_isTie` are primitive ties), so any use must supply enumeration
data that genuinely fails there. -/
theorem hingeHoldsAtSize_of_residualLedger {size : ℕ} (hsize : 3 ≤ size)
    (patterns : List (LinePattern size))
    (hcomplete : PatternListIsCompleteUpToRelabel size patterns)
    (hresidual : ∀ pattern ∈ patterns, ¬ IsNearPencilClass pattern →
      StratumIsTieFree pattern) :
    HingeHoldsAtSize size 3 := by
  classical
  refine hingeHoldsAtSize_of_relabelLedger patterns hcomplete fun pattern hmem => ?_
  by_cases hnearPencil : IsNearPencilClass pattern
  · exact stratumIsTieFree_of_isNearPencilClass hsize hnearPencil
  · exact hresidual pattern hmem hnearPencil

/-- **The hinge at seven points from the residual ledger**, with BOTH discharged
recognizers peeled: the residual is asked only of the classes that are neither a
near pencil nor a Fano.  Against the isomorphism-class ledger that leaves
twenty-one of the twenty-three entries at seven points. -/
theorem hingeHoldsAtSize_of_residualLedger_sevenThree
    (patterns : List (LinePattern 7))
    (hcomplete : PatternListIsCompleteUpToRelabel 7 patterns)
    (hresidual : ∀ pattern ∈ patterns, ¬ IsNearPencilClass pattern →
      ¬ IsFanoClass pattern → StratumIsTieFree pattern) :
    HingeHoldsAtSize 7 3 := by
  classical
  refine hingeHoldsAtSize_of_residualLedger (by norm_num) patterns hcomplete
    fun pattern hmem hnearPencil => ?_
  by_cases hfano : IsFanoClass pattern
  · exact stratumIsTieFree_of_isFanoClass hfano
  · exact hresidual pattern hmem hnearPencil hfano

/-- **The heavy form at six points.**  The hinge at `(6,3)` follows from a
complete enumeration plus, for each listed class that is not a near pencil,
tie-freeness RESTRICTED to designs of leverage at least one.  Both peels are
unconditional: the near pencils by the rank-two transport, the heaviness by
`GtzWeighted 5 3`.  Against the isomorphism-class ledger that leaves eight of the
nine entries at six points, each with the leverage floor already granted. -/
theorem hingeHoldsAtSize_of_heavyResidualLedger_sixThree
    (patterns : List (LinePattern 6))
    (hcomplete : PatternListIsCompleteUpToRelabel 6 patterns)
    (hresidual : ∀ pattern ∈ patterns, ¬ IsNearPencilClass pattern →
      StratumIsTieFreeAmongHeavy pattern) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_residualLedger (by norm_num) patterns hcomplete
    fun pattern hmem hnearPencil =>
      stratumIsTieFree_of_amongHeavy_sixThree (hresidual pattern hmem hnearPencil)

/-- The same at seven points, with the Fano peeled too and the leverage floor
bought with the open `GtzWeighted 6 3`. -/
theorem hingeHoldsAtSize_of_heavyResidualLedger_sevenThree (hsixThree : GtzWeighted 6 3)
    (patterns : List (LinePattern 7))
    (hcomplete : PatternListIsCompleteUpToRelabel 7 patterns)
    (hresidual : ∀ pattern ∈ patterns, ¬ IsNearPencilClass pattern →
      ¬ IsFanoClass pattern → StratumIsTieFreeAmongHeavy pattern) :
    HingeHoldsAtSize 7 3 :=
  hingeHoldsAtSize_of_residualLedger_sevenThree patterns hcomplete
    fun pattern hmem hnearPencil hfano =>
      stratumIsTieFree_of_amongHeavy_sevenThree hsixThree
        (hresidual pattern hmem hnearPencil hfano)

/-- **The sharpest honest form at six points.**  Each open class is asked for two
things: tie-freeness among `Gtz.AllHeavy` designs — which is where the shipped
heavy machinery applies — and tie-freeness on the unit-leverage face.  Both peels
and the split are unconditional. -/
theorem hingeHoldsAtSize_of_allHeavyResidualLedger_sixThree
    (patterns : List (LinePattern 6))
    (hcomplete : PatternListIsCompleteUpToRelabel 6 patterns)
    (hallHeavy : ∀ pattern ∈ patterns, ¬ IsNearPencilClass pattern →
      StratumIsTieFreeAmongAllHeavy pattern)
    (hunitLeverage : ∀ pattern ∈ patterns, ¬ IsNearPencilClass pattern →
      StratumIsTieFreeAtUnitLeverage pattern) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_heavyResidualLedger_sixThree patterns hcomplete
    fun pattern hmem hnearPencil =>
      stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage
        (hallHeavy pattern hmem hnearPencil) (hunitLeverage pattern hmem hnearPencil)

/-- The same at seven points. -/
theorem hingeHoldsAtSize_of_allHeavyResidualLedger_sevenThree (hsixThree : GtzWeighted 6 3)
    (patterns : List (LinePattern 7))
    (hcomplete : PatternListIsCompleteUpToRelabel 7 patterns)
    (hallHeavy : ∀ pattern ∈ patterns, ¬ IsNearPencilClass pattern →
      ¬ IsFanoClass pattern → StratumIsTieFreeAmongAllHeavy pattern)
    (hunitLeverage : ∀ pattern ∈ patterns, ¬ IsNearPencilClass pattern →
      ¬ IsFanoClass pattern → StratumIsTieFreeAtUnitLeverage pattern) :
    HingeHoldsAtSize 7 3 :=
  hingeHoldsAtSize_of_heavyResidualLedger_sevenThree hsixThree patterns hcomplete
    fun pattern hmem hnearPencil hfano =>
      stratumIsTieFreeAmongHeavy_of_allHeavy_and_unitLeverage
        (hallHeavy pattern hmem hnearPencil hfano)
        (hunitLeverage pattern hmem hnearPencil hfano)

/-! ## Controls: the peel is not everything, and the narrowing keeps the ties

Three failure modes would make the statements above worthless.  The peel could
accidentally cover the whole ledger, making the residual hypothesis vacuous; the
heavy restriction could exclude every tie, making `StratumIsTieFreeAmongHeavy`
vacuous; and a discharged stratum could be empty of designs, making its
tie-freeness vacuous.  All three are ruled out here, the last by reusing the
exact rational near pencil shipped in `Gtz.Design.NearPencilTransport`. -/

/-- **The line-free stratum survives the peel.**  At four or more labels the
uniform matroid's pattern — no dependent triple at all — is not a near-pencil
class, because a near pencil at that size has a dependent triple of DISTINCT
labels avoiding its pole.  So `U(3,6)` and `U(3,7)` remain in the residual and
the peel is not secretly total. -/
theorem not_isNearPencilClass_lineFree {size : ℕ} (hsize : 4 ≤ size) :
    ¬ IsNearPencilClass (size := size) (fun _ _ _ => False) := by
  classical
  intro hclass
  obtain ⟨poleLabel, hagree⟩ := (isNearPencilClass_iff_exists_pole _).mp hclass
  have hcomplement : 3 ≤ ({poleLabel}ᶜ : Finset (Fin size)).card := by
    rw [Finset.card_compl, Finset.card_singleton, Fintype.card_fin]
    omega
  obtain ⟨witnessTriple, hsubset, hcard⟩ := Finset.exists_subset_card_eq hcomplement
  obtain ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight, hshape⟩ :=
    Finset.card_eq_three.mp hcard
  have hoff : ∀ label : Fin size, label ∈ witnessTriple → label ≠ poleLabel := by
    intro label hmem
    simpa only [Finset.mem_compl, Finset.mem_singleton] using hsubset hmem
  have hdependent : nearPencilLinePattern poleLabel leftLabel midLabel rightLabel :=
    ⟨hoff leftLabel (by rw [hshape]; simp), hoff midLabel (by rw [hshape]; simp),
      hoff rightLabel (by rw [hshape]; simp)⟩
  exact (hagree leftLabel midLabel rightLabel hleftMid hleftRight hmidRight).mpr hdependent

/-- **The tetrahedron tie is heavy** — the leverage floor realized at the `(4,3)`
tie, so the heavy restriction is not vacuous by excluding every tie. -/
theorem tetraDesign_forall_leverage_one_le (label : Fin 4) :
    1 ≤ leverageOf (tetraDesign.atom label) :=
  leverage_one_le_of_isTie_fourThree tetraDesign tetraDesign_isTie label

/-- **The diamond tie is heavy** — the same at the `(5,3)` tie, which is the
primitive one sitting on `M(K4)`'s boundary.  So the leverage floor does not
exclude the very phenomenon the open entries have to survive; it is a necessary
condition on ties, not a margin. -/
theorem diamondDesign_forall_leverage_one_le (label : Fin 5) :
    1 ≤ leverageOf (diamondDesign.atom label) :=
  leverage_one_le_of_isTie_fiveThree diamondDesign diamondDesign_isTie label

/-- **The split-tetrahedron ties are heavy** — the control AT THE HINGE'S OWN
LOWER SIZE.  `Gtz.splitTetraDesign` is a two-parameter family of exact `(6,3)`
ties, and the floor applies to every member, so the size-six narrowing retains a
whole family of ties rather than being non-vacuous only one or two rungs down. -/
theorem splitTetraDesign_forall_leverage_one_le (splitA splitB : ℝ) (hAPos : 0 < splitA)
    (hALt : splitA < 1 / 4) (hBPos : 0 < splitB) (hBLt : splitB < 1 / 4) (label : Fin 6) :
    1 ≤ leverageOf ((splitTetraDesign splitA splitB hAPos hALt hBPos hBLt).atom label) :=
  leverage_one_le_of_isTie_sixThree _
    (splitTetraDesign_isTie splitA splitB hAPos hALt hBPos hBLt) label

/-- **The split-tetrahedron ties are STRICTLY heavy**, every leverage being three.
So the `(6,3)` ties known to the repository sit in the `Gtz.AllHeavy` branch of
the dichotomy, not on the unit-leverage face: `StratumIsTieFreeAmongAllHeavy` is
the branch that still has to survive a tie. -/
theorem splitTetraDesign_allHeavy (splitA splitB : ℝ) (hAPos : 0 < splitA)
    (hALt : splitA < 1 / 4) (hBPos : 0 < splitB) (hBLt : splitB < 1 / 4) :
    AllHeavy (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) := by
  intro label
  rw [leverageOf_eq_dotProduct, splitTetraDesign_atom,
    show splitTetraAtom label = tetraAtom (splitTetraDirIndex label) from rfl,
    tetraAtom_dot_self]
  norm_num

/-- **The split-tetrahedron ties do not refute the hinge**: they are not
primitive, atoms `2` and `3` carrying the same tetrahedron direction.  Recorded
because a `(6,3)` tie would otherwise look like a counterexample to
`HingeHoldsAtSize 6 3`, whose conclusion is exactly that a tie has a parallel
pair. -/
theorem splitTetraDesign_hasParallelPair (splitA splitB : ℝ) (hAPos : 0 < splitA)
    (hALt : splitA < 1 / 4) (hBPos : 0 < splitB) (hBLt : splitB < 1 / 4) :
    HasParallelPair (splitTetraDesign splitA splitB hAPos hALt hBPos hBLt) := by
  refine ⟨2, 3, 1, by decide, ?_⟩
  rw [splitTetraDesign_atom, one_smul]
  rfl

/-- **The narrowed obligation is inhabited on both sides at `(4,3)`.**  The
line-free stratum there is NOT tie-free even among heavy designs — the
tetrahedron witnesses it — so `StratumIsTieFreeAmongHeavy` is a genuine
condition and not provable outright at every pattern. -/
theorem not_stratumIsTieFreeAmongHeavy_fourThree_lineFree :
    ¬ StratumIsTieFreeAmongHeavy (size := 4) (fun _ _ _ => False) := fun hheavyFree =>
  hheavyFree tetraDesign tetraDesign_hasUniformLinePattern
    tetraDesign_forall_leverage_one_le tetraDesign_isTie

/-! ## The near-pencil entry is not vacuous, and it carries heavy designs

`Gtz.Design.NearPencilTransport` ships exact rational near pencils at six and
seven points, under the name `solePoleLinePattern`.  That pattern is THE SAME
FUNCTION as `Gtz.nearPencilLinePattern`, which the two files do not record; with
the identification in hand, the second file's witnesses answer the first file's
non-vacuity question directly. -/

/-- **The two files' near-pencil patterns are one function.**  The reconciliation
`Gtz.Design.NearPencilTransport`'s header leaves open, and the reason its designs
witness `Gtz.nearPencilLinePattern` strata. -/
theorem nearPencilLinePattern_eq_solePoleLinePattern {size : ℕ} (poleLabel : Fin size) :
    nearPencilLinePattern poleLabel = solePoleLinePattern poleLabel := rfl

/-- **The `(6,3)` near-pencil stratum carries a design.**  So
`Gtz.stratumIsTieFree_nearPencil` at size six is not vacuously true, and neither
is the peel that rides it. -/
theorem nearPencilSixDesign_hasNearPencilLinePattern :
    HasLinePattern nearPencilSixDesign (nearPencilLinePattern (5 : Fin 6)) :=
  nearPencilSixDesign_hasLinePattern

/-- **The `(7,3)` near-pencil stratum carries a design.** -/
theorem nearPencilSevenDesign_hasNearPencilLinePattern :
    HasLinePattern nearPencilSevenDesign (nearPencilLinePattern (6 : Fin 7)) :=
  nearPencilSevenDesign_hasLinePattern

/-- **That design is strictly heavy.**  Its leverages are `4, 4, 2, 2, 5, 4`, so a
discharged hinge stratum carries an `Gtz.AllHeavy` design and the heavy
restrictions above are not vacuous on it either. -/
theorem nearPencilSixDesign_allHeavy : AllHeavy nearPencilSixDesign := by
  intro label
  have hatom : nearPencilSixDesign.atom label = nearPencilSixAtom label := rfl
  rw [leverageOf_eq_dotProduct, hatom]
  fin_cases label <;>
    norm_num [nearPencilSixAtom, dotProduct, Fin.sum_univ_three, Matrix.cons_val_two,
      Matrix.tail_cons, Matrix.head_cons]

/-- **The `(6,3)` near-pencil entry, all three halves**: the stratum is inhabited,
the design on it is strictly heavy, and the stratum is empty of ties.  The first
two rule out vacuity of the emptiness claim and of the heavy narrowing; the third
is the discharged entry. -/
theorem nearPencilSixEntry_isInhabitedHeavyAndTieFree :
    HasLinePattern nearPencilSixDesign (nearPencilLinePattern (5 : Fin 6)) ∧
      AllHeavy nearPencilSixDesign ∧
      StratumIsTieFree (nearPencilLinePattern (5 : Fin 6)) :=
  ⟨nearPencilSixDesign_hasNearPencilLinePattern, nearPencilSixDesign_allHeavy,
    stratumIsTieFree_nearPencil (by omega) 5⟩

end Gtz
