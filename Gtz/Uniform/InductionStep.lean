/-
# The uniform GTZ induction step: corank floor, step skeleton, grand conditional

Everything here is uniform in the rank; specific ranks appear only as
cross-check instances.  Three layers, in order:

1. **The corank floor** (`corankFloor_holds`): `GtzWeighted size rank` for
   every `size <= rank + 2`, every rank.  Pure assembly — the below-rank
   vacuity (`Gtz.rank_le_of_design`), the square (`Gtz.gtzWeighted_square`),
   and the corank-1/2 duality descents (`Gtz.gtzWeighted_corank_one` /
   `Gtz.gtzWeighted_corank_two`).  No tie classification is consumed: the
   corank-2 VALUE descends by Naimark duality to the proven rank 2; the
   corank-2 tie laws are needed only for the finer structure inside window
   closures, never for the floor.

2. **The step skeleton** (`inductionStep_of_windowClosure` and its mechanism
   twin `inductionStep_viaDescentLadder`): rank `>= 3`, from
   `GtzWeightedAll (rank - 1)` and `ClosesCanonicalWindow rank` to
   `GtzWeightedAll rank`.  HONEST FINDING: at the `GtzWeightedAll` level the
   predecessor hypothesis is REDUNDANT — the top-cell collapse
   (`Gtz.gtzWeightedAll_of_top`, fully rank-generic) derives the whole rank
   from the window closure alone, because size monotonicity
   (`Gtz.gtzWeighted_of_le`) covers the below-window band and the square
   without any duality descent.  The recursion of route (a) therefore lives
   ENTIRELY inside the production of the window closure (the named gaps
   below), not in the value-level step.  The mechanism twin proves the same
   statement along the classical ladder (crystallization + square + duality
   descent + floor), genuinely consuming the predecessor via the uniform
   rank-descent `gtzWeightedAll_of_higherRank` (iterated spike padding,
   `Gtz.gtzWeighted_of_spike`).

3. **The grand conditional** (`forall_gtzWeighted_of_windowClosures`): the
   window closures at all ranks `>= 3` imply weighted GTZ at every size and
   every rank `>= 1` — and hence the original 1997 statement for every
   `(n, k)` (`forall_gtzOriginal_of_windowClosures`).  The whole conjecture
   rests on the sequence of per-rank window closures, each equivalent to its
   single top cell (`closesCanonicalWindow_iff_top`).

Named gaps (load-bearing open Props, each with its rank-3 instantiation):
`WindowArrowFromPredecessorWeighted`, `RouteAWindowArrow`,
`RouteAHingeProduction`, `RankHingeUniformPosition 2` — see the docstrings.
-/
import Mathlib
import Gtz.Reduction.RankFourWindow
import Gtz.Reduction.BalancedStratumClosure
import Gtz.Reduction.RankThreeEquivalenceHub

set_option autoImplicit false
set_option relaxedAutoImplicit false

namespace Gtz
namespace InductionStep

/-! ## The corank floor, uniform in the rank

The floor every induction step stands on: every cell of corank at most two is
a theorem, at every rank.  The corank-2 tie classifications are NOT needed
here: the corank-2 VALUE was already uniform via duality descent into the
proven rank 2 — ties (which do exist at corank 2: the diamond) are compatible
with WEAK domination, which is all `GtzWeighted` asks.  The tie
classifications matter one level deeper, for the strict-domination structure
inside window closures. -/

/-- **The corank floor.**  `GtzWeighted size rank` for every `size <= rank + 2`,
every rank: below the rank there are no designs (`Gtz.rank_le_of_design`), at
the rank the square dominates
(`Gtz.gtzWeighted_square`), corank 1 descends to the pigeonhole
(`Gtz.gtzWeighted_corank_one`), and corank 2 descends to the proven rank 2
(`Gtz.gtzWeighted_corank_two`; at rank 1 the corank-2 cell `(3,1)` is
`Gtz.gtz_rank_one 3`, and at rank 0 every cell is vacuous). -/
theorem corankFloor_holds :
    ∀ rank size : ℕ, size ≤ rank + 2 → GtzWeighted size rank := by
  intro rank size hsize
  rcases Nat.eq_zero_or_pos rank with hrankZero | hrankPos
  · rw [hrankZero]
    exact gtzWeighted_dim_zero size
  rcases lt_or_ge size rank with hbelowRank | hatLeastRank
  · exact fun design => absurd (rank_le_of_design design) (by omega)
  have hcorankSplit : size = rank ∨ size = rank + 1 ∨ size = rank + 2 := by omega
  rcases hcorankSplit with hsquare | hcorankOne | hcorankTwo
  · rw [hsquare]
    exact gtzWeighted_square rank
  · rw [hcorankOne]
    exact gtzWeighted_corank_one rank hrankPos
  · rw [hcorankTwo]
    rcases lt_or_ge rank 2 with hrankLow | hrankGeTwo
    · have hrankOne : rank = 1 := by omega
      rw [hrankOne]
      exact gtz_rank_one 3
    · exact gtzWeighted_corank_two rank hrankGeTwo

/-- Mechanism-parity cross-check: the floor plus the two proven base ranks
rederives `Gtz.gtzWeighted_of_le_five` — five atoms force rank `<= 2` or
corank `<= 2`. -/
theorem gtzWeighted_of_le_five_rederived (size rank : ℕ) (hrank : 1 ≤ rank)
    (hsize : size ≤ 5) : GtzWeighted size rank := by
  rcases le_or_gt rank 2 with hrankLow | hrankHigh
  · interval_cases rank
    · exact gtz_rank_one size
    · exact gtz_rank_two size
  · exact corankFloor_holds rank size (by omega)

/-- The corank floor reaches the canonical window `2 * rank <= size` only at
rank `<= 2` — at every higher rank the floor and the window are disjoint, so
the floor closes no window cell. -/
theorem corankFloor_meetsWindow_iff (rank : ℕ) :
    2 * rank ≤ rank + 2 ↔ rank ≤ 2 := by omega

/-! ## The step skeleton, uniform in the rank -/

/-- Size `size` lies inside the canonical (crystallization) window at rank
`rank`: not dispatched by the generic ledger.  Below `2 * rank` duality
descends to a smaller rank (`Gtz.gtzWeighted_of_dual_rank`); above
`rank * (rank + 1) / 2 + 1` crystallization caps the support
(`Gtz.crystallization`).  At rank 3 the window is `{6, 7}`. -/
def IsInsideCanonicalWindow (size rank : ℕ) : Prop :=
  2 * rank ≤ size ∧ size ≤ rank * (rank + 1) / 2 + 1

/-- The window closure at rank `rank` — the exact content an induction step
must supply beyond the generic ledger.  `Gtz.gtz_iff_top_of_each_rank` is
fully rank-generic, so this Prop collapses to its single top cell at every
rank (`closesCanonicalWindow_iff_top` below); nothing about the collapse is
rank-3-bound. -/
def ClosesCanonicalWindow (rank : ℕ) : Prop :=
  ∀ size : ℕ, IsInsideCanonicalWindow size rank → GtzWeighted size rank

/-- The top cell `M(rank) = rank * (rank + 1) / 2 + 1` lies inside the window
at EVERY rank: `2 * rank <= M(rank)` is `(rank - 1) * (rank - 2) >= 0`. -/
theorem topCell_isInsideCanonicalWindow (rank : ℕ) :
    IsInsideCanonicalWindow (rank * (rank + 1) / 2 + 1) rank := by
  refine ⟨?_, le_refl _⟩
  rcases le_or_gt rank 2 with hrankLow | hrankHigh
  · interval_cases rank <;> norm_num
  · have hmomentBound : rank * 4 ≤ rank * (rank + 1) :=
      Nat.mul_le_mul (le_refl rank) (by omega)
    set moment := rank * (rank + 1) with hmomentDef
    omega

/-- **The window closure IS its top cell** — the uniform packaging of the
one-object-per-rank collapse (`Gtz.gtzWeighted_window_of_top` plus the top
cell's own membership). -/
theorem closesCanonicalWindow_iff_top (rank : ℕ) :
    ClosesCanonicalWindow rank ↔ GtzWeighted (rank * (rank + 1) / 2 + 1) rank := by
  constructor
  · intro hwindow
    exact hwindow _ (topCell_isInsideCanonicalWindow rank)
  · intro htop size hinside
    exact gtzWeighted_of_le hinside.2 htop

/-- Degenerate cross-check: rank 1 closes its window (the window is `{2}`;
the pigeonhole closes every size). -/
theorem closesCanonicalWindow_one : ClosesCanonicalWindow 1 :=
  fun size _ => gtz_rank_one size

/-- Degenerate cross-check: rank 2 closes its window (the window is `{4}`;
the proven rank 2 closes every size). -/
theorem closesCanonicalWindow_two : ClosesCanonicalWindow 2 :=
  fun size _ => gtz_rank_two size

/-! ### The uniform rank-descent ladder

`Gtz.gtzWeighted_of_spike` descends ONE rank at matched size shift
(previously consumed only in instances, e.g.
`Gtz.gtzWeighted_ten_three_of_eleven_four`).  Here it is iterated into the
uniform law: the weighted conjecture is ANTITONE in the rank —
`GtzWeightedAll` at any rank carries every positive rank below it.  This is
what lets the step consume only the IMMEDIATE predecessor
`GtzWeightedAll (rank - 1)` where the classical ladder
(`Gtz.gtz_of_canonical_list`) needed all lower ranks at once. -/

/-- Iterated spike descent: `GtzWeighted` transfers down a whole gap of ranks
at the matching size shift. -/
theorem gtzWeighted_of_spike_chain :
    ∀ (gap : ℕ) {size rank : ℕ}, 1 ≤ rank → rank ≤ size →
      GtzWeighted (size + gap) (rank + gap) → GtzWeighted size rank := by
  intro gap
  induction gap with
  | zero =>
      intro size rank _ _ hgtz
      exact hgtz
  | succ prevGap ih =>
      intro size rank hrankPos hrankLe hgtz
      exact ih hrankPos hrankLe
        (gtzWeighted_of_spike (by omega) (by omega) hgtz)

/-- **The conjecture is antitone in the rank**: `GtzWeightedAll` at
`upperRank` yields `GtzWeightedAll` at every rank `1 <= lowerRank <=
upperRank`.  Sizes below the lower rank are vacuous; all others ride the spike
chain with gap `upperRank - lowerRank`. -/
theorem gtzWeightedAll_of_higherRank {upperRank : ℕ}
    (hupper : GtzWeightedAll upperRank) {lowerRank : ℕ}
    (hlowerPos : 1 ≤ lowerRank) (hlowerLe : lowerRank ≤ upperRank) :
    GtzWeightedAll lowerRank := by
  intro size
  rcases lt_or_ge size lowerRank with hsmall | hlarge
  · exact fun design => absurd (rank_le_of_design design) (by omega)
  · have hshift : lowerRank + (upperRank - lowerRank) = upperRank := by omega
    refine gtzWeighted_of_spike_chain (upperRank - lowerRank) hlowerPos hlarge ?_
    rw [hshift]
    exact hupper (size + (upperRank - lowerRank))

/-! ### The step -/

/-- **The window closure alone carries the whole rank** — the value-level step
with the predecessor hypothesis stripped.  This is the top-cell collapse
(`Gtz.gtzWeightedAll_of_top`) read through `closesCanonicalWindow_iff_top`:
size monotonicity covers the square and the whole below-window band, so no
duality descent and no lower rank is consumed. -/
theorem gtzWeightedAll_of_closesCanonicalWindow (rank : ℕ)
    (hwindow : ClosesCanonicalWindow rank) : GtzWeightedAll rank :=
  gtzWeightedAll_of_top rank ((closesCanonicalWindow_iff_top rank).mp hwindow)

/-- **THE INDUCTION STEP, uniform.**  Rank `>= 3`: the predecessor's weighted
theorem plus the window closure yield the rank's weighted theorem.

HONESTY: the `GtzWeightedAll (rank - 1)` premise is NOT CONSUMED — the window
closure alone suffices (`gtzWeightedAll_of_closesCanonicalWindow`).  Route
(a)'s recursion therefore lives entirely inside the PRODUCTION of
`ClosesCanonicalWindow rank` from lower-rank material (the named gap
`WindowArrowFromPredecessorWeighted` / `RouteAWindowArrow` below), exactly as
the rank-3 evidence has it: the trichotomy branch closures consume the rank-2
hinge on Naimark duals and companions INSIDE the (6,3)/(7,3) closure, not
around it.  The premise is kept so the statement has the step shape;
`inductionStep_viaDescentLadder` proves the same statement along the classical
mechanism, consuming the premise genuinely. -/
theorem inductionStep_of_windowClosure :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ClosesCanonicalWindow rank → GtzWeightedAll rank :=
  fun rank _ _ hwindow => gtzWeightedAll_of_closesCanonicalWindow rank hwindow

/-- The same step along the classical descent ladder, as a mechanism witness:
crystallization caps the size, the below-rank band is vacuous, the square
dominates, the band `rank < size < 2 * rank` descends by Naimark duality to
the dual rank `size - rank <= rank - 1` — supplied by the PREDECESSOR through
the antitone ladder `gtzWeightedAll_of_higherRank` — and the window band is
the hypothesis.  This is `Gtz.gtz_of_canonical_list` sharpened to consume only
`GtzWeightedAll (rank - 1)` instead of all lower ranks. -/
theorem inductionStep_viaDescentLadder :
    ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) →
      ClosesCanonicalWindow rank → GtzWeightedAll rank := by
  intro rank hrank hpredecessor hwindow
  refine crystallization rank fun size hsize => ?_
  rcases lt_or_ge size rank with hbelowRank | hatLeastRank
  · exact fun design => absurd (rank_le_of_design design) (by omega)
  rcases eq_or_lt_of_le hatLeastRank with hsquare | hstrict
  · rw [← hsquare]
    exact gtzWeighted_square rank
  rcases lt_or_ge size (2 * rank) with hdualBand | hwindowBand
  · refine gtzWeighted_of_dual_rank (by omega) (by omega) ?_
    exact gtzWeightedAll_of_higherRank hpredecessor (by omega) (by omega) size
  · exact hwindow size ⟨hwindowBand, hsize⟩

/-! ### The rank-3 cross-check

`ClosesCanonicalWindow 3` is exactly the open rank-3 content, and the
trichotomy chain delivers it from the stress-free hinge alone: the capstone
`Gtz.forall_gtzOriginal_rank_three_of_stressFreeHingeAlone` IS the composition
`balancedStratumSelection_six_holds` (branch (ii)) +
`twoPoleStratumSelection_six_unconditional` (branch (iii)) + the hinge
(branch (i)) through the trichotomy; the hub equivalences
(`Gtz.gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three` and
`Gtz.gtzWeighted_six_three_iff_seven_three`) pull it back to the top cell
`(7,3)`, which is the window by `closesCanonicalWindow_iff_top`. -/

/-- **Rank-3 window closure from the stress-free hinge** — the trichotomy
chain, repackaged as the `ClosesCanonicalWindow 3` instance. -/
theorem closesCanonicalWindow_three_of_stressFreeHinge
    (hhinge : StressFreeHingeHoldsSixThree) : ClosesCanonicalWindow 3 := by
  refine (closesCanonicalWindow_iff_top 3).mpr ?_
  have htopCell : 3 * (3 + 1) / 2 + 1 = 7 := by norm_num
  rw [htopCell]
  exact gtzWeighted_six_three_iff_seven_three.mp
    (gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three.mpr
      (forall_gtzOriginal_rank_three_of_stressFreeHingeAlone hhinge))

/-- The step instantiated at rank 3: predecessor = the proven rank 2, window
closure = the hinge-conditional chain.  Conclusion: rank 3 in full. -/
theorem gtzWeightedAll_three_of_stressFreeHinge_viaStep
    (hhinge : StressFreeHingeHoldsSixThree) : GtzWeightedAll 3 :=
  inductionStep_of_windowClosure 3 (by norm_num) gtz_rank_two
    (closesCanonicalWindow_three_of_stressFreeHinge hhinge)

/-- The rank-3 instance of the step REPRODUCES the capstone byte-for-byte in
its conclusion: the same hypothesis (`Gtz.StressFreeHingeHoldsSixThree`), the
same conclusion shape as
`Gtz.forall_gtzOriginal_rank_three_of_stressFreeHingeAlone`. -/
theorem forall_gtzOriginal_rank_three_viaStep
    (hhinge : StressFreeHingeHoldsSixThree) :
    ∀ sizeParam : ℕ, 0 < sizeParam → GtzOriginal sizeParam 3 :=
  fun sizeParam hsizePos =>
    original_of_weighted 3
      (gtzWeightedAll_three_of_stressFreeHinge_viaStep hhinge) sizeParam hsizePos

/-! ## The grand conditional

The full conjecture rests on the sequence of per-rank window closures.  Ranks
1 and 2 are theorems; each rank `>= 3` is its window closure through the step;
sizes off the window ride crystallization and size monotonicity inside
`gtzWeightedAll_of_closesCanonicalWindow`.  The composition below runs the
LITERAL induction (base ranks + step); the redundancy of the predecessor
premise means it also collapses to a per-rank application, with no induction
— both readings are true of the same proof term's statement. -/

/-- **The grand conditional, rank form**: window closures at every rank `>= 3`
give the weighted conjecture at every rank `>= 1`. -/
theorem forall_gtzWeightedAll_of_windowClosures
    (hclosures : ∀ rank : ℕ, 3 ≤ rank → ClosesCanonicalWindow rank) :
    ∀ rank : ℕ, 1 ≤ rank → GtzWeightedAll rank := by
  intro rank
  induction rank with
  | zero =>
      intro habsurd
      exact absurd habsurd (by omega)
  | succ prevRank ih =>
      intro _
      rcases lt_or_ge prevRank 2 with hbase | hstep
      · interval_cases prevRank
        · exact gtz_rank_one
        · exact gtz_rank_two
      · exact inductionStep_of_windowClosure (prevRank + 1) (by omega)
          (ih (by omega)) (hclosures (prevRank + 1) (by omega))

/-- **THE GRAND CONDITIONAL.**  The window closures at all ranks `>= 3` yield
weighted GTZ at every size and every rank `>= 1` — the whole conjecture rests
on one sequence of window closures, each of which is a single top cell
(`closesCanonicalWindow_iff_top`). -/
theorem forall_gtzWeighted_of_windowClosures
    (hclosures : ∀ rank : ℕ, 3 ≤ rank → ClosesCanonicalWindow rank) :
    ∀ size rank : ℕ, 1 ≤ rank → rank ≤ size → GtzWeighted size rank :=
  fun size rank hrankPos _ =>
    forall_gtzWeightedAll_of_windowClosures hclosures rank hrankPos size

/-- The grand conditional in the original 1997 coordinates: window closures at
all ranks `>= 3` give `GtzOriginal n k` for every `n >= 1`, `k >= 1`. -/
theorem forall_gtzOriginal_of_windowClosures
    (hclosures : ∀ rank : ℕ, 3 ≤ rank → ClosesCanonicalWindow rank) :
    ∀ sizeParam rank : ℕ, 1 ≤ rank → 0 < sizeParam →
      GtzOriginal sizeParam rank :=
  fun sizeParam rank hrankPos hsizePos =>
    original_of_weighted rank
      (forall_gtzWeightedAll_of_windowClosures hclosures rank hrankPos)
      sizeParam hsizePos

/-! ## The named gaps

Everything above is unconditional (or conditional only on the quantified
window closures).  What is OPEN is the per-rank production of
`ClosesCanonicalWindow rank` from lower-rank material.  The gaps are stated as
load-bearing Props, each with its rank-3 instantiation recorded. -/

/-- **NAMED GAP 1 — the weighted window arrow.**  The predecessor's weighted
theorem alone produces the window closure, at every rank `>= 3`.  This single
uniform arrow is the whole residual of route (a) at the value level:
`forall_gtzWeightedAll_of_windowArrow` below composes it into the full
conjecture with NO other hypothesis.

Rank-3 instantiation: the arrow's rank-3 instance follows from
`Gtz.StressFreeHingeHoldsSixThree` (constant in the `GtzWeightedAll 2`
premise) via `closesCanonicalWindow_three_of_stressFreeHinge`; the premise
`GtzWeightedAll 2` is `Gtz.gtz_rank_two`.  No converse is claimed: a window
closure does not obviously return the hinge (ties satisfy weak domination,
so `GtzWeighted 6 3` does not exclude them). -/
def WindowArrowFromPredecessorWeighted : Prop :=
  ∀ rank : ℕ, 3 ≤ rank → GtzWeightedAll (rank - 1) → ClosesCanonicalWindow rank

/-- **The whole conjecture rests on the single uniform arrow**: gap 1 alone
implies the full weighted conjecture at every rank. -/
theorem forall_gtzWeightedAll_of_windowArrow
    (harrow : WindowArrowFromPredecessorWeighted) :
    ∀ rank : ℕ, 1 ≤ rank → GtzWeightedAll rank := by
  intro rank
  induction rank with
  | zero =>
      intro habsurd
      exact absurd habsurd (by omega)
  | succ prevRank ih =>
      intro _
      rcases lt_or_ge prevRank 2 with hbase | hstep
      · interval_cases prevRank
        · exact gtz_rank_one
        · exact gtz_rank_two
      · exact gtzWeightedAll_of_closesCanonicalWindow (prevRank + 1)
          (harrow (prevRank + 1) (by omega) (ih (by omega)))

/-- **No free lunch, recorded in kernel**: the quantified gap arrow is
EQUIVALENT to the full weighted conjecture — as any true-conjecture
conditional must be (`Gtz/Reduction/LiftingLemma.lean` and
`Gtz/Reduction/StrengthenedInductionHypothesis.lean` record the analogous
collapses).  The arrow's value is per-rank workability — one window closure
at a time, each a single top cell — not logical weakness.  Nothing here is
lifting-shaped: the composition routes through crystallization, size
monotonicity and Naimark duality, never through `Gtz.LiftingLemma` or a
downstairs lifting-subset predicate. -/
theorem windowArrow_iff_forall_gtzWeightedAll :
    WindowArrowFromPredecessorWeighted ↔
      ∀ rank : ℕ, 1 ≤ rank → GtzWeightedAll rank := by
  constructor
  · exact forall_gtzWeightedAll_of_windowArrow
  · intro htarget rank hrank _
    exact (closesCanonicalWindow_iff_top rank).mpr
      (htarget rank (by omega) (rank * (rank + 1) / 2 + 1))

/-- The rank-3 instance of gap 1 is implied by the stress-free hinge — the
open rank-3 Prop `Gtz.StressFreeHingeHoldsSixThree` delivers exactly the
arrow's rank-3 obligation. -/
theorem windowArrow_three_of_stressFreeHinge
    (hhinge : StressFreeHingeHoldsSixThree) :
    GtzWeightedAll 2 → ClosesCanonicalWindow 3 :=
  fun _ => closesCanonicalWindow_three_of_stressFreeHinge hhinge

/-! ### The route-(a) strengthened form of the gaps

The strengthened hypothesis H(k) carries a second slot — the uniform-position
hinge — because the rank-3 branch closures consumed the rank-2 hinge on
companions (`Gtz/Design/CompanionConstruction.lean`) and on Naimark duals
(`Gtz/Ties/SpikeMatroidObstruction.lean`). -/

/-- A selection of atom labels is DEPENDENT: some coefficient vector supported
inside the selection, not identically zero, kills the atoms (`Gtz.pairBracket`
/ `Gtz.atomBracket` are its width-specific determinant forms). -/
def IsDependentSelection {size rank : ℕ} (design : WeightedDesign size rank)
    (chosen : Finset (Fin size)) : Prop :=
  ∃ dependence : Fin size → ℝ,
    (∃ witnessLabel, dependence witnessLabel ≠ 0)
      ∧ (∀ label, label ∉ chosen → dependence label = 0)
      ∧ (∑ label, dependence label • design.atom label) = 0

/-- A chosen family of atoms is in UNIFORM POSITION: every rank-sized
subselection is independent. -/
def IsUniformPositionFamily {size rank : ℕ} (design : WeightedDesign size rank)
    (chosen : Finset (Fin size)) : Prop :=
  ∀ subset : Finset (Fin size), subset ⊆ chosen → subset.card = rank →
    ¬ IsDependentSelection design subset

/-- The rank-k direction hinge: any `rank + 2` labels in uniform position admit
a strictly dominating rank-subset.  k = 2 is morally
`Gtz.rankTwoFourDirectionHinge_holds`; see `RankHingeUniformPosition 2` under
NAMED GAP 4 for the honest delta.  OPEN at every rank `>= 3`. -/
def RankHingeUniformPosition (rank : ℕ) : Prop :=
  ∀ (size : ℕ) (design : WeightedDesign size rank)
    (chosen : Finset (Fin size)),
    chosen.card = rank + 2 →
    IsUniformPositionFamily design chosen →
    ∃ dominating : Finset (Fin size),
      dominating.card = rank ∧ (subsetSum design dominating - 1).PosDef

/-- The strengthened induction hypothesis H(k): the weighted theorem plus the
uniform-position hinge — what the rank-3 chain actually consumed from
rank 2. -/
structure StrengthenedHypothesis (rank : ℕ) : Prop where
  hasWeightedAll : GtzWeightedAll rank
  hasUniformPositionHinge : RankHingeUniformPosition rank

/-- **NAMED GAP 2 — the route-(a) window arrow.**  Weaker than gap 1 (its
premise is stronger): H(rank - 1) produces the window closure.  Rank-3
instantiation: same as gap 1 — the hinge delivers it with the H(2) premise
unused (`windowArrow_three_of_stressFreeHinge`); the honest expectation is
that a UNIFORM proof will consume `hasUniformPositionHinge` on the coplanar
stratum's companion, as rank 3 did. -/
def RouteAWindowArrow : Prop :=
  ∀ rank : ℕ, 3 ≤ rank → StrengthenedHypothesis (rank - 1) →
    ClosesCanonicalWindow rank

/-- Gap 1 implies gap 2 by weakening the premise. -/
theorem routeAWindowArrow_of_windowArrow
    (harrow : WindowArrowFromPredecessorWeighted) : RouteAWindowArrow :=
  fun rank hrank hhypothesis => harrow rank hrank hhypothesis.hasWeightedAll

/-- **NAMED GAP 3 — the hinge production.**  To RECURSE, route (a) must also
produce `RankHingeUniformPosition rank` at the new rank; nothing in the tree
produces any hinge from lower-rank material (the rank-3 hinge sibling is
open).  Without this arrow the route-(a) package does not iterate — that is
precisely why gap 1, whose composition needs no hinge, is the sharper
target. -/
def RouteAHingeProduction : Prop :=
  ∀ rank : ℕ, 3 ≤ rank → StrengthenedHypothesis (rank - 1) →
    ClosesCanonicalWindow rank → RankHingeUniformPosition rank

/-- **NAMED GAP 4 — the rank-2 uniform-position bridge.**  H(2)'s hinge slot.
Morally this IS `Gtz.rankTwoFourDirectionHinge_holds`: at rank 2, uniform
position of four labels is pairwise independence, i.e. all six pair brackets
nonzero.  The missing kernel content is only the DICTIONARY between
`IsUniformPositionFamily` and the six nonzero `Gtz.pairBracket`s (the
`pairBracket = 0 <-> dependent pair` conversion at general size);
`CorankTwo.dependence_of_completion_mix` carries that dictionary on the
rank-2 NAIMARK DUAL side, but the direct rank-2 surface form is not proved
here.  Stated as a gap rather than silently claimed. -/
def RankTwoUniformPositionBridge : Prop := RankHingeUniformPosition 2

/-- **Route (a), composed**: gaps 2 + 3 + 4 produce H(rank) for every rank
`>= 2` — the strengthened hypothesis propagates up the whole tower. -/
theorem forall_strengthenedHypothesis_of_routeA
    (harrow : RouteAWindowArrow) (hproduction : RouteAHingeProduction)
    (hbridge : RankTwoUniformPositionBridge) :
    ∀ rank : ℕ, 2 ≤ rank → StrengthenedHypothesis rank := by
  intro rank
  induction rank with
  | zero =>
      intro habsurd
      exact absurd habsurd (by omega)
  | succ prevRank ih =>
      intro hge
      rcases lt_or_ge prevRank 2 with hbase | hstep
      · have hrankTwo : prevRank + 1 = 2 := by omega
        rw [hrankTwo]
        exact ⟨gtz_rank_two, hbridge⟩
      · have hprevHypothesis : StrengthenedHypothesis prevRank := ih hstep
        have hwindow : ClosesCanonicalWindow (prevRank + 1) :=
          harrow (prevRank + 1) (by omega) hprevHypothesis
        exact ⟨gtzWeightedAll_of_closesCanonicalWindow (prevRank + 1) hwindow,
          hproduction (prevRank + 1) (by omega) hprevHypothesis hwindow⟩

/-- Route (a)'s target from its three gaps: the full weighted conjecture. -/
theorem forall_gtzWeightedAll_of_routeA
    (harrow : RouteAWindowArrow) (hproduction : RouteAHingeProduction)
    (hbridge : RankTwoUniformPositionBridge) :
    ∀ rank : ℕ, 1 ≤ rank → GtzWeightedAll rank := by
  intro rank hrankPos
  rcases lt_or_ge rank 2 with hbase | hstep
  · interval_cases rank
    exact gtz_rank_one
  · exact (forall_strengthenedHypothesis_of_routeA harrow hproduction hbridge
      rank hstep).hasWeightedAll

/-! ### Route (b)'s per-rank payoff shape, for the record -/

/-- **Route (b)'s per-rank payoff at the top cell**: every tie at
`(M(rank), rank)` has a parallel pair.  Under the numerical SP-converse of
arXiv:2511.02387 (Table 1 evidence, NOT a theorem) this is pure graph
counting: `M(rank)` edges exceed the simple-graph capacity on `rank + 1`
vertices.  The funnel (`Gtz.dominating_of_parallel_pair`) is rank-generic,
but composing this Prop into `ClosesCanonicalWindow rank` still needs the
tie-reduction at the top cell (a failing cell must yield a tie), which the
tree owns only through the rank-3 compactness machinery — the route-(b)
wiring is therefore NOT stated as a theorem here. -/
def ParallelPairAtTopCellTie (rank : ℕ) : Prop :=
  ∀ design : WeightedDesign (rank * (rank + 1) / 2 + 1) rank,
    IsTie design → HasParallelPair design

end InductionStep
end Gtz
