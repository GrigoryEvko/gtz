import Skeleton.Frontier

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 4000000

/-!
# The general-rank capstone

`Gtz.GtzWeightedAll rank` at EVERY rank, and the 1997 statement
`Gtz.GtzOriginal size rank` at every rank and every positive size, from the
three general-rank obligations of `Skeleton.Obligations` and nothing else.

## The hypothesis on the rank is empty, and that is a result, not an oversight

The capstone below is `forall rank : Nat, Gtz.GtzWeightedAll rank` with no
guard.  No rank is excluded and no rank is a hand-worked special case:

* rank zero, one and two are discharged by the SAME step that discharges every
  other rank, because `thresholdCell rank <= rank + 2` exactly when `rank <= 2`
  (`thresholdCell_le_corankFloor_iff`) and the corank floor
  `Gtz.InductionStep.corankFloor_holds` closes every cell up to `rank + 2`
  unconditionally at every rank;
* the sharp window is EMPTY at ranks one and two
  (`sharpWindowIsEmptyBelowRankThree`), which is why the two window closures
  are guarded by `3 <= rank` without that guard excluding anything.

Nothing here uses `Gtz.gtz_rank_one`, `Gtz.gtz_rank_two` or
`Gtz.gtzWeighted_dim_zero`.  Those three are the tree's per-rank base cases; the
induction below does not need them, so the base is uniform rather than
enumerated.

## The shape of the induction

One step, `uniformInductionStep`, quantified over every rank:

  every smaller rank is closed  ==>  this rank is closed.

Inside it the rank splits not by an enumeration of small values but by a single
arithmetic dichotomy on where the threshold cell sits relative to the corank
floor.  The named closures are

* `ClosesCorankFloor` -- every cell of corank at most two, unconditional at
  every rank (`Gtz.InductionStep.corankFloor_holds`);
* `HingeHoldsAcrossSharpWindow` and `AnchorReachesAcrossSharpWindow` -- the two
  obligations, discharged from the registry for `3 <= rank`;
* `ClosesSharpWindow` -- what the ladder produces from them;
* `ClosesThresholdCell` -- the single cell per rank that decides that rank.

## Why the threshold axis and not the corank-three axis

The rank-three argument in the tree is carried by
`Gtz.StressFreeHingeHoldsAtCorankThree`, which reads the rank-three cell as
`rank + 3`.  That reading is an accident of rank three:
`corankThreeCell_eq_thresholdCell_iff` proves the two axes agree at rank three
and at NO other positive rank, and `corankThreeCell_belowSharpWindow` proves
that from rank four on the corank-three cell lies strictly below the window's
floor `2 * rank`, so a carrier read along it constrains no obligation cell.

This file therefore uses the rank-generic replacement, the threshold cell
`thresholdCell rank = rank * (rank + 1) / 2 = dim Sym(rank)`, which stays inside
the sharp window at every rank at least three and keeps the atom count equal to
the dimension of the ambient symmetric space.  No separate coincidence
obligation is declared, because none is used.

## Rank three costs exactly the rank-three currency

Before 2026-08-08 the registry's threshold-cell hinge covered `3 <= rank`, so
its rank-three instance silently assumed the whole `(6,3)` frontier a second
time -- the general capstone paid for rank three with a strictly stronger
axiom.  The rank split removed that: `Skeleton.obligationThresholdCellHinge`
is now a THEOREM whose rank-three instance is discharged from the five class
residuals through the trichotomy assembly, and the axiom survives only as
`Skeleton.obligationThresholdCellHingeRankFourAndUp`.  So
`skeletonGtzWeightedAllEveryRank` now reaches ALL SEVEN registry obligations:
the five sharpened class residuals (its rank-three price, identical to the
rank-three capstone's) plus the two genuinely general-rank assumptions, which
are the two hinges.  The reach obligation left the registry on 2026-08-13,
discharged by `Gtz.GeneralRankReach.sharpWindowAnchorReachRankFourAndUp`.

## The five rank-three residuals are a hypothesis, not a fixture

They enter through ONE branch.  `uniformInductionStep` sends rank three into the
ladder, the ladder calls `Skeleton.obligationThresholdCellHinge`, and that
theorem contains its own rank-three instance in its proof term.  Supply
`Gtz.GtzWeighted 6 3` instead and the branch never runs, so the five leave the
whole chain: `Skeleton.SixThreeConditional` proves the same conclusion at every
rank from that cell and the THREE general-rank obligations alone, kernel-checked
by `#gtz_frontier_exactly`.  The cell is exactly what the `Gtz/Wave` campaign
attacks, because `thresholdCell 3 = 6`.
-/

namespace Skeleton.GeneralRank

/-! ## 1. The two candidate axes for "the cell that decides a rank" -/

/-- The sharp Veronese top, `dim Sym(rank)`.  Closing this one cell closes the
whole rank, by `Gtz.gtzWeightedAll_of_veroneseTop`. -/
def thresholdCell (rank : ℕ) : ℕ := rank * (rank + 1) / 2

/-- The corank-three cell, the axis along which the tree's rank-three carrier
`Gtz.StressFreeHingeHoldsAtCorankThree` is written. -/
def corankThreeCell (rank : ℕ) : ℕ := rank + 3

/-- The triangular number linearises: doubling it recovers the product, so every
downstream bound can be handed to `omega` once this is in context. -/
theorem thresholdCell_twice (rank : ℕ) : 2 * thresholdCell rank = rank * (rank + 1) := by
  obtain ⟨half, hhalf⟩ := Nat.even_mul_succ_self rank
  have hproductEven : rank * (rank + 1) = 2 * half := by omega
  show 2 * (rank * (rank + 1) / 2) = rank * (rank + 1)
  rw [hproductEven, Nat.mul_div_cancel_left _ (by norm_num : 0 < 2)]

/-- Below rank three the threshold cell is already inside the corank floor, so
the floor alone decides those ranks.  This is the whole content of the
induction's base. -/
theorem thresholdCell_le_corankFloor {rank : ℕ} (hrankSmall : rank ≤ 2) :
    thresholdCell rank ≤ rank + 2 := by
  interval_cases rank <;> decide

/-- From rank three on the threshold cell sits at or above the window floor. -/
theorem twoRank_le_thresholdCell {rank : ℕ} (hrankAtLeastThree : 3 ≤ rank) :
    2 * rank ≤ thresholdCell rank := by
  have htwice := thresholdCell_twice rank
  have hproductBound : rank * 4 ≤ rank * (rank + 1) := Nat.mul_le_mul (le_refl rank) (by omega)
  omega

/-- From rank three on the threshold cell has escaped the corank floor. -/
theorem corankFloor_lt_thresholdCell {rank : ℕ} (hrankAtLeastThree : 3 ≤ rank) :
    rank + 2 < thresholdCell rank := by
  have hwindowFloor := twoRank_le_thresholdCell hrankAtLeastThree
  omega

/-- **The dichotomy the induction turns on, exactly.**  The corank floor reaches
the threshold cell precisely below rank three.  This is the whole case split in
`uniformInductionStep`: not an enumeration of small ranks, one arithmetic
threshold. -/
theorem thresholdCell_le_corankFloor_iff (rank : ℕ) :
    thresholdCell rank ≤ rank + 2 ↔ rank ≤ 2 := by
  refine ⟨fun hreached => ?_, fun hrankSmall => thresholdCell_le_corankFloor hrankSmall⟩
  by_contra hrankBig
  have hescaped := corankFloor_lt_thresholdCell (by omega : 3 ≤ rank)
  omega

/-- At ranks one and two the threshold cell falls strictly below the window
floor, i.e. the sharp window is empty there. -/
theorem thresholdCell_lt_twoRank_belowRankThree {rank : ℕ}
    (hrankPositive : 1 ≤ rank) (hrankSmall : rank ≤ 2) : thresholdCell rank < 2 * rank := by
  interval_cases rank <;> decide

/-! ## 2. The rank-three coincidence, recorded rather than relied upon -/

/-- **The coincidence, exactly.**  The corank-three axis and the threshold axis
name the same cell at rank three and at no other positive rank. -/
theorem corankThreeCell_eq_thresholdCell_iff {rank : ℕ} (hrankPositive : 1 ≤ rank) :
    corankThreeCell rank = thresholdCell rank ↔ rank = 3 := by
  constructor
  · intro hcoincide
    have htwice := thresholdCell_twice rank
    have hcorank : corankThreeCell rank = rank + 3 := rfl
    by_contra hnotThree
    rcases lt_or_ge rank 4 with hrankSmall | hrankBig
    · interval_cases rank <;> simp_all [corankThreeCell, thresholdCell]
    · have hproductBound : rank * 5 ≤ rank * (rank + 1) := Nat.mul_le_mul (le_refl rank) (by omega)
      omega
  · rintro rfl
    decide

/-- **The coincidence does not survive.**  From rank four on the corank-three
cell lies strictly below the window floor `2 * rank`, so it is not an obligation
cell and a carrier written along that axis constrains none of them. -/
theorem corankThreeCell_belowSharpWindow {rank : ℕ} (hrankAtLeastFour : 4 ≤ rank) :
    corankThreeCell rank < 2 * rank := by
  show rank + 3 < 2 * rank
  omega

/-! ## 3. The named closures

A membership predicate and five closures.  `ClosesCorankFloor` is a theorem at
every rank.  `HingeHoldsAcrossSharpWindow` and `AnchorReachesAcrossSharpWindow`
are the two registry obligations, restated in the shape the ladder consumes.
`ClosesSharpWindow` is what the ladder produces from them, and
`ClosesThresholdCell` is its top cell, the one that decides the rank. -/

/-- A cell of the sharp window: at least the Naimark floor `2 * rank`, at most
the threshold cell.  Note this is the SHARP window; the tree's
`Gtz.InductionStep.IsInsideCanonicalWindow` allows one more cell on top, which
`Gtz.gtzWeightedAll_of_veroneseTop` shows is redundant. -/
def IsInsideSharpWindow (size rank : ℕ) : Prop :=
  2 * rank ≤ size ∧ size ≤ thresholdCell rank

/-- **The corank closure.**  Every cell of corank at most two is closed
outright.  Discharged, at every rank, with no obligation. -/
def ClosesCorankFloor (rank : ℕ) : Prop :=
  ∀ size : ℕ, size ≤ rank + 2 → Gtz.GtzWeighted size rank

/-- **The hinge closure.**  Every tie at every cell of the sharp window has a
parallel pair, given that the cell below it is already closed. -/
def HingeHoldsAcrossSharpWindow (rank : ℕ) : Prop :=
  ∀ size : ℕ, IsInsideSharpWindow size rank →
    Gtz.GtzWeighted (size - 1) rank → Gtz.HingeHoldsAtSize size rank

/-- **The reach closure.**  Every cell of the sharp window carries an anchor
with a strictly dominating rank-subset that the parallel-free locus reaches. -/
def AnchorReachesAcrossSharpWindow (rank : ℕ) : Prop :=
  ∀ size : ℕ, IsInsideSharpWindow size rank →
    ∃ anchor : Gtz.WeightedDesign size rank,
      Gtz.HasStrictlyDominatingSubset anchor ∧ Gtz.ParallelFreeReachesAnchor size rank anchor

/-- **The window closure.**  What the two obligations buy: every cell of the
sharp window closed. -/
def ClosesSharpWindow (rank : ℕ) : Prop :=
  ∀ size : ℕ, IsInsideSharpWindow size rank → Gtz.GtzWeighted size rank

/-- **The threshold closure.**  The single cell that decides a rank. -/
def ClosesThresholdCell (rank : ℕ) : Prop :=
  Gtz.GtzWeighted (thresholdCell rank) rank

/-- The sharp window is empty at ranks one and two.  This, not an enumeration of
small cases, is why guarding the two window obligations by `3 <= rank` excludes
no obligation cell. -/
theorem sharpWindowIsEmptyBelowRankThree {rank size : ℕ}
    (hrankPositive : 1 ≤ rank) (hrankSmall : rank ≤ 2) : ¬ IsInsideSharpWindow size rank := by
  have hgap := thresholdCell_lt_twoRank_belowRankThree hrankPositive hrankSmall
  rintro ⟨hfloor, hceiling⟩
  omega

/-! ## 4. Discharging the closures -/

/-- The corank closure is a theorem at every rank, with no obligation. -/
theorem closesCorankFloor_everyRank (rank : ℕ) : ClosesCorankFloor rank :=
  Gtz.InductionStep.corankFloor_holds rank

/-- The hinge closure.  The threshold cell is the top of the window, so the
case split is exactly the split between `Skeleton.obligationThresholdCellHinge`
(a theorem since the 2026-08-08 rank split: rank three from the class
residuals, rank four and up from the registry) and
`Skeleton.obligationSubThresholdBandHinge`. -/
theorem hingeHoldsAcrossSharpWindow_ofRegistry {rank : ℕ} (hrankAtLeastThree : 3 ≤ rank) :
    HingeHoldsAcrossSharpWindow rank := by
  rintro size ⟨hfloor, hceiling⟩ hpredecessorCell
  rcases eq_or_lt_of_le hceiling with hattop | hbelow
  · subst hattop
    exact Skeleton.obligationThresholdCellHinge rank hrankAtLeastThree hpredecessorCell
  · exact Skeleton.obligationSubThresholdBandHinge rank hrankAtLeastThree size hfloor hbelow
      hpredecessorCell

/-- The reach closure, from the registry. -/
theorem anchorReachesAcrossSharpWindow_ofRegistry {rank : ℕ} (hrankAtLeastThree : 3 ≤ rank) :
    AnchorReachesAcrossSharpWindow rank := by
  rintro size ⟨hfloor, hceiling⟩
  exact Skeleton.obligationSharpWindowAnchorReach rank hrankAtLeastThree size hfloor hceiling

/-! ## 5. The ladder: window closure from the two obligations -/

/-- **The rung engine, on the two closures alone.**  From the Naimark floor
`2 * rank - 1`, supplied by the predecessor rank, climb one cell at a time to
the top of the sharp window.  Each rung is
`Gtz.UniformPositionBridge.gtzWeighted_succ_of_hinge_of_reach`, fed by the two
closures.

The closures are HYPOTHESES here and not registry calls.  That is what lets
`Skeleton.SixThreeConditional` run the same ladder off the rank-four-and-up
obligations alone, without the rank-three instance that
`Skeleton.obligationThresholdCellHinge` contains in its proof term. -/
theorem closesSharpWindow_ofClosures {rank : ℕ} (hrankAtLeastThree : 3 ≤ rank)
    (hhinge : HingeHoldsAcrossSharpWindow rank)
    (hreach : AnchorReachesAcrossSharpWindow rank)
    (hpredecessorRank : Gtz.GtzWeightedAll (rank - 1)) : ClosesSharpWindow rank := by
  have hfloorLeThreshold := twoRank_le_thresholdCell hrankAtLeastThree
  have hnaimarkFloor : Gtz.GtzWeighted (2 * rank - 1) rank :=
    Gtz.UniformPositionBridge.gtzWeighted_belowWindow_of_predecessor hrankAtLeastThree
      hpredecessorRank
  have hfloorSucc : 2 * rank - 1 + 1 = 2 * rank := by omega
  have hbottomCell : Gtz.GtzWeighted (2 * rank) rank := by
    have hfirstRung := Gtz.UniformPositionBridge.gtzWeighted_succ_of_hinge_of_reach
      (predSize := 2 * rank - 1) (rank := rank)
      (by
        rw [hfloorSucc]
        exact hhinge (2 * rank) ⟨le_refl _, hfloorLeThreshold⟩ hnaimarkFloor)
      (by
        rw [hfloorSucc]
        exact hreach (2 * rank) ⟨le_refl _, hfloorLeThreshold⟩)
      hnaimarkFloor
    rwa [hfloorSucc] at hfirstRung
  have hclimb : ∀ offset : ℕ, 2 * rank + offset ≤ thresholdCell rank →
      Gtz.GtzWeighted (2 * rank + offset) rank := by
    intro offset
    induction offset with
    | zero => intro _; simpa using hbottomCell
    | succ previousOffset climbedSoFar =>
        intro hceiling
        have hpreviousCell : Gtz.GtzWeighted (2 * rank + previousOffset) rank :=
          climbedSoFar (by omega)
        have hregroup : 2 * rank + (previousOffset + 1) = 2 * rank + previousOffset + 1 := by omega
        rw [hregroup]
        refine Gtz.UniformPositionBridge.gtzWeighted_succ_of_hinge_of_reach ?_ ?_ hpreviousCell
        · refine hhinge (2 * rank + previousOffset + 1) ⟨by omega, by omega⟩ ?_
          have hshift : 2 * rank + previousOffset + 1 - 1 = 2 * rank + previousOffset := by omega
          rw [hshift]
          exact hpreviousCell
        · exact hreach (2 * rank + previousOffset + 1) ⟨by omega, by omega⟩
  rintro size ⟨hfloor, hceiling⟩
  have hclimbed := hclimb (size - 2 * rank) (by omega)
  have hrecover : 2 * rank + (size - 2 * rank) = size := by omega
  rwa [hrecover] at hclimbed

/-- The ladder driven by the registry closures, the form the unconditional
capstone consumes. -/
theorem closesSharpWindow_ofLargeRank {rank : ℕ} (hrankAtLeastThree : 3 ≤ rank)
    (hpredecessorRank : Gtz.GtzWeightedAll (rank - 1)) : ClosesSharpWindow rank :=
  closesSharpWindow_ofClosures hrankAtLeastThree
    (hingeHoldsAcrossSharpWindow_ofRegistry hrankAtLeastThree)
    (anchorReachesAcrossSharpWindow_ofRegistry hrankAtLeastThree) hpredecessorRank

/-! ## 6. The threshold closure at every rank, in two uniform branches -/

/-- Below rank three the corank floor already reaches the threshold cell.  No
obligation, no enumeration of ranks -- one arithmetic bound. -/
theorem closesThresholdCell_ofSmallRank {rank : ℕ} (hrankSmall : rank ≤ 2) :
    ClosesThresholdCell rank :=
  closesCorankFloor_everyRank rank (thresholdCell rank) (thresholdCell_le_corankFloor hrankSmall)

/-- From rank three on the threshold cell is the top of the sharp window, so the
ladder delivers it. -/
theorem closesThresholdCell_ofLargeRank {rank : ℕ} (hrankAtLeastThree : 3 ≤ rank)
    (hpredecessorRank : Gtz.GtzWeightedAll (rank - 1)) : ClosesThresholdCell rank :=
  closesSharpWindow_ofLargeRank hrankAtLeastThree hpredecessorRank (thresholdCell rank)
    ⟨twoRank_le_thresholdCell hrankAtLeastThree, le_refl _⟩

/-! ## 7. The uniform induction step -/

/-- **THE STEP, quantified over every rank.**  Every rank strictly below this
one closed implies this one closed.  There is no per-rank case analysis: the
single branch is the arithmetic dichotomy of section 1, on whether the threshold
cell has escaped the corank floor yet. -/
theorem uniformInductionStep (rank : ℕ)
    (hsmallerRanksClosed : ∀ smaller : ℕ, smaller < rank → Gtz.GtzWeightedAll smaller) :
    Gtz.GtzWeightedAll rank := by
  refine Gtz.gtzWeightedAll_of_veroneseTop rank ?_
  rcases Nat.lt_or_ge rank 3 with hrankSmall | hrankLarge
  · exact closesThresholdCell_ofSmallRank (by omega)
  · exact closesThresholdCell_ofLargeRank hrankLarge (hsmallerRanksClosed (rank - 1) (by omega))

/-! ## 8. Non-vacuity controls for the obligation-free base

Three ranks that the tree closes by named per-rank theorems, reproved here
through the small-rank branch alone.  Each carries its own `#gtz_frontier` at
the foot of the file and must report ZERO obligations: that is the machine check
that the base of the induction is genuinely free, rather than an obligation in
disguise.  An empty base would typecheck just as well, so the controls are what
make the claim falsifiable. -/

/-- Rank zero, from the corank floor rather than `Gtz.gtzWeighted_dim_zero`. -/
theorem gtzWeightedAllRankZero_ofCorankFloor : Gtz.GtzWeightedAll 0 :=
  Gtz.gtzWeightedAll_of_veroneseTop 0 (closesThresholdCell_ofSmallRank (by norm_num))

/-- Rank one, from the corank floor rather than `Gtz.gtz_rank_one`. -/
theorem gtzWeightedAllRankOne_ofCorankFloor : Gtz.GtzWeightedAll 1 :=
  Gtz.gtzWeightedAll_of_veroneseTop 1 (closesThresholdCell_ofSmallRank (by norm_num))

/-- Rank two, from the corank floor rather than `Gtz.gtz_rank_two`.  The tree's
rank-two argument is a substantial development; under the sharp reading it is
redundant, because `thresholdCell 2 = 3` is a corank-one cell. -/
theorem gtzWeightedAllRankTwo_ofCorankFloor : Gtz.GtzWeightedAll 2 :=
  Gtz.gtzWeightedAll_of_veroneseTop 2 (closesThresholdCell_ofSmallRank (by norm_num))

/-! ## 9. The capstones -/

/-- **THE GENERAL-RANK CAPSTONE.**  Weighted GTZ at every rank and every size.

No hypothesis on the rank: the correct hypothesis, read off the verified chain,
is vacuous.  Ranks zero, one and two are proved by the same step as every other
rank -- see the module docstring. -/
theorem skeletonGtzWeightedAllEveryRank : ∀ rank : ℕ, Gtz.GtzWeightedAll rank := by
  have hclosedUpTo : ∀ bound rank : ℕ, rank ≤ bound → Gtz.GtzWeightedAll rank := by
    intro bound
    induction bound with
    | zero =>
        intro rank hrankBound
        exact uniformInductionStep rank (fun smaller hsmaller => absurd hsmaller (by omega))
    | succ previousBound closedUpToPrevious =>
        intro rank hrankBound
        exact uniformInductionStep rank
          (fun smaller hsmaller => closedUpToPrevious smaller (by omega))
  exact fun rank => hclosedUpTo rank rank (le_refl rank)

/-- The single deciding cell, closed at every rank. -/
theorem closesThresholdCell_everyRank (rank : ℕ) : ClosesThresholdCell rank :=
  skeletonGtzWeightedAllEveryRank rank (thresholdCell rank)

/-- **THE 1997 STATEMENT, at every rank.**  Routed through the converse bridge
`Gtz.gtzWeightedAll_iff_forall_gtzOriginal` of `Gtz/Reduction/ConverseBridge.lean`,
so the original conjecture itself is reached and not merely its weighted
reformulation.

No hypothesis on the rank; the positivity `0 < size` is the 1997 statement's own
side condition on the number of points, not an exclusion of ranks. -/
theorem skeletonGtzOriginalEveryRank :
    ∀ size rank : ℕ, 0 < size → Gtz.GtzOriginal size rank :=
  fun size rank hsizePositive =>
    (Gtz.gtzWeightedAll_iff_forall_gtzOriginal rank).mp
      (skeletonGtzWeightedAllEveryRank rank) size hsizePositive

/-- The same conclusion off the SINGLE threshold cell, through the bridge's
sharp form `Gtz.gtzWeighted_veroneseTop_iff_forall_gtzOriginal`: for each rank
the whole 1997 statement is decided by `Gtz.GtzWeighted (dim Sym rank) rank`. -/
theorem skeletonGtzOriginalFromThresholdCell (rank : ℕ) :
    ∀ size : ℕ, 0 < size → Gtz.GtzOriginal size rank :=
  (Gtz.gtzWeighted_veroneseTop_iff_forall_gtzOriginal rank).mp (closesThresholdCell_everyRank rank)

/-! ## 10. Rank three costs exactly the rank-three currency -/

/-- Rank three of the 1997 statement, out of the general capstone.  Its
threshold cell is `thresholdCell 3 = 6`, so this is the `(6,3)` frontier reached
by the rank-generic route rather than by the rank-three carrier. -/
theorem skeletonGtzOriginalRankThree : ∀ size : ℕ, 0 < size → Gtz.GtzOriginal size 3 :=
  skeletonGtzOriginalFromThresholdCell 3

/-- The threshold cell at rank three is six -- the coincidence, computed. -/
theorem thresholdCell_three : thresholdCell 3 = 6 := by decide

/-- **The general route pays for rank three with the rank-three currency.**
Before the 2026-08-08 rank split this derivation showed the registry's
threshold-cell hinge SUBSUMED the whole rank-three frontier -- assuming the
`(6,3)` hinge a second time inside a general-rank axiom.
`Skeleton.obligationThresholdCellHinge` is now a theorem whose rank-three
instance is discharged from the five class residuals, so this same derivation
now reaches exactly those five plus nothing else at rank three: the detour
and the rank-three capstone spend the identical currency. -/
theorem rankThreeSpendsClassResiduals : Gtz.StressFreeHingeHoldsSixThree :=
  Skeleton.stressFreeHingeSixThree_of_thresholdCellHinge Skeleton.obligationThresholdCellHinge

/-! ## 11. Discharging the tree's own residual -/

/-- The tree's canonical window closure, `Gtz.InductionStep.ClosesCanonicalWindow`,
at every rank.  It is stated one cell wider than the sharp window; that extra
cell is redundant, which is why closing the sharp window suffices. -/
theorem closesCanonicalWindow_everyRank (rank : ℕ) :
    Gtz.InductionStep.ClosesCanonicalWindow rank :=
  fun size _ => skeletonGtzWeightedAllEveryRank rank size

/-- The sharp window, closed at every rank, in the file's own vocabulary. -/
theorem closesSharpWindow_everyRank (rank : ℕ) : ClosesSharpWindow rank :=
  fun size _ => skeletonGtzWeightedAllEveryRank rank size

/-! ## 12. The frontier

The printed lists below are the whole point of the scaffold: the kernel's own
answer to "what is still assumed", recomputed on every build.

The three base-rank controls must each report ZERO obligations.  The two
capstones must each report ALL SEVEN registry obligations: the five sharpened
class residuals (the rank-three price, paid through the discharged rank-three
instance of the threshold-cell hinge) plus the two genuinely general-rank
assumptions.  Since the 2026-08-08 rank split there is no subsumption and no
dead weight from either root alone: `Skeleton.RankThree` spends the five class
residuals, this file spends all seven. -/

#gtz_frontier gtzWeightedAllRankZero_ofCorankFloor

#gtz_frontier gtzWeightedAllRankOne_ofCorankFloor

#gtz_frontier gtzWeightedAllRankTwo_ofCorankFloor

#gtz_frontier skeletonGtzWeightedAllEveryRank

#gtz_frontier skeletonGtzOriginalEveryRank

#gtz_frontier_all skeletonGtzWeightedAllEveryRank skeletonGtzOriginalEveryRank

end Skeleton.GeneralRank
