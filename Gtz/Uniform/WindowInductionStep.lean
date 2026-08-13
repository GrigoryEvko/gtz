/-
# The window induction step, with the topological side discharged

`SpectralWhitening` closed the reach at every window cell, and the connectedness
route then runs on the hinge and the parallel branch alone
(`gtzWeighted_of_hinge_of_parallelBranch`).  This file removes the second of
those two: inside the window the parallel branch is FREE, because the shipped
margin-free merge `Gtz.dominating_of_parallel_pair` reads it off the previous
cell.

WHAT IS LEFT OF THE INDUCTION.  One statement per cell:

* `gtzWeighted_of_hinge_of_predecessor` — at a window cell, the hinge plus the
  previous cell give the cell.  No anchor, no path, no domination estimate, and
  no parallel branch appears.

Chaining that step over the sizes gives `gtzWeighted_aboveFloor_of_hinges`: at
every rank of three or more, the Naimark floor plus the hinge at every size of
`2 * rank` or more closes EVERY size from the floor up.  The floor itself is
free from the previous rank (`gtzWeighted_belowWindow_of_predecessor`), so
`gtzWeightedAboveFloor_of_predecessorRank` states the whole rank step on the
hinges alone.

THE DECIDING CELL.  `ThresholdCellHingeMap` supplies the hinge at
`thresholdSize rank = rank * (rank + 1) / 2` from three named arms.  Feeding it
here gives `gtzWeighted_thresholdCell_of_arms`.  At rank three the previous cell
is the decided `Gtz.gtzWeighted_of_le_five`, thus `gtzWeighted_six_three_of_arms`
proves the campaign's central cell from the three arms and nothing else — no
reach hypothesis, no named anchor, no icosahedron.
-/
import Gtz.Uniform.SpectralWhitening
import Gtz.Reduction.ThresholdCellHingeMap

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxHeartbeats 1000000

namespace Gtz
namespace GeneralRankReach

open Matrix Finset

/-! ## The parallel branch is free inside the window -/

/-- **THE PARALLEL BRANCH FROM THE PREVIOUS CELL.**  A design carrying a
parallel pair merges the pair and inherits a dominating subset one size down.
No quantitative hypothesis, no rank hypothesis. -/
theorem parallelBranch_of_predecessor {predSize rank : ℕ}
    (hpredecessor : GtzWeighted predSize rank)
    (design : WeightedDesign (predSize + 1) rank) (hparallel : HasParallelPair design) :
    ∃ chosen : Finset (Fin (predSize + 1)), chosen.card = rank ∧ Dominates design chosen := by
  obtain ⟨keptLabel, dropLabel, ratio, hdistinct, hpair⟩ := hparallel
  exact dominating_of_parallel_pair design hpredecessor hdistinct hpair

/-! ## The step -/

/-- **THE WINDOW INDUCTION STEP.**  Inside the window the hinge and the previous
cell give the cell.  The anchor, the path and the parallel branch are all
theorems now, so nothing else enters. -/
theorem gtzWeighted_of_hinge_of_predecessor {predSize rank : ℕ} (hrank : 3 ≤ rank)
    (hwindow : 2 * rank ≤ predSize + 1) (hhinge : HingeHoldsAtSize (predSize + 1) rank)
    (hpredecessor : GtzWeighted predSize rank) : GtzWeighted (predSize + 1) rank :=
  gtzWeighted_of_hinge_of_parallelBranch hrank hwindow hhinge
    (parallelBranch_of_predecessor hpredecessor)

/-- The same step stated on a size that is already known to sit above the
floor. -/
theorem gtzWeighted_of_hinge_of_predecessor' {size rank : ℕ} (hrank : 3 ≤ rank)
    (hfloor : 2 * rank ≤ size) (hhinge : HingeHoldsAtSize size rank)
    (hpredecessor : GtzWeighted (size - 1) rank) : GtzWeighted size rank := by
  have hpositive : 1 ≤ size := by omega
  have hsplit : size - 1 + 1 = size := by omega
  have hstep := gtzWeighted_of_hinge_of_predecessor (predSize := size - 1) hrank
    (by omega) (by rwa [hsplit]) hpredecessor
  rwa [hsplit] at hstep

/-! ## The chain over the sizes -/

/-- **THE SIZE CHAIN.**  From the floor cell, the hinge at every size of
`2 * rank` or more closes every size from the floor up.  The induction is one
step per size, each riding the previous cell into the parallel branch. -/
theorem gtzWeighted_aboveFloor_of_hinges {rank : ℕ} (hrank : 3 ≤ rank)
    (hfloorCell : GtzWeighted (2 * rank - 1) rank)
    (hhinge : ∀ size : ℕ, 2 * rank ≤ size → HingeHoldsAtSize size rank)
    (size : ℕ) (hsize : 2 * rank - 1 ≤ size) : GtzWeighted size rank := by
  have hclimb : ∀ extra : ℕ, GtzWeighted (2 * rank - 1 + extra) rank := by
    intro extra
    induction extra with
    | zero => simpa using hfloorCell
    | succ prevExtra ih =>
        have hshift : 2 * rank - 1 + (prevExtra + 1) = (2 * rank - 1 + prevExtra) + 1 := by omega
        rw [hshift]
        exact gtzWeighted_of_hinge_of_predecessor hrank (by omega)
          (hhinge _ (by omega)) ih
  have hrewrite : 2 * rank - 1 + (size - (2 * rank - 1)) = size := by omega
  have hreached := hclimb (size - (2 * rank - 1))
  rwa [hrewrite] at hreached

/-- **THE RANK STEP, ON THE HINGES ALONE.**  The previous rank supplies the
floor by Naimark duality, so at every rank of three or more the hinges close
every size from the floor up. -/
theorem gtzWeighted_aboveFloor_of_predecessorRank {rank : ℕ} (hrank : 3 ≤ rank)
    (hpredecessorRank : GtzWeightedAll (rank - 1))
    (hhinge : ∀ size : ℕ, 2 * rank ≤ size → HingeHoldsAtSize size rank)
    (size : ℕ) (hsize : 2 * rank - 1 ≤ size) : GtzWeighted size rank :=
  gtzWeighted_aboveFloor_of_hinges hrank
    (UniformPositionBridge.gtzWeighted_belowWindow_of_predecessor hrank hpredecessorRank)
    hhinge size hsize

/-- **THE CANONICAL WINDOW, FROM THE HINGES.**  Every cell of the canonical
window sits above the floor, so the window closure follows. -/
theorem closesCanonicalWindow_of_hinges {rank : ℕ} (hrank : 3 ≤ rank)
    (hpredecessorRank : GtzWeightedAll (rank - 1))
    (hhinge : ∀ size : ℕ, 2 * rank ≤ size → HingeHoldsAtSize size rank) :
    InductionStep.ClosesCanonicalWindow rank :=
  fun size hinside =>
    gtzWeighted_aboveFloor_of_predecessorRank hrank hpredecessorRank hhinge size
      (by have := hinside.1; omega)

/-! ## The deciding cell of a rank

`thresholdSize rank = rank * (rank + 1) / 2` is inside the window at every rank
of three or more (`two_mul_le_thresholdSize`), so the step applies there and the
three arms of `ThresholdCellHingeMap` reach the cell. -/

/-- **THE DECIDING CELL FROM THE THREE ARMS.**  The stress-free arm, the
balanced arm and the degenerate arm, plus the previous cell, give weighted GTZ
at the deciding cell of the rank. -/
theorem gtzWeighted_thresholdCell_of_arms {rank : ℕ} (hrank : 3 ≤ rank)
    (hpredecessor : GtzWeighted (thresholdSize rank - 1) rank)
    (hfreeArm : ThresholdStressFreeArm rank) (hbalancedArm : ThresholdBalancedArm rank)
    (hdegenerateArm : ThresholdDegenerateArm rank) :
    GtzWeighted (thresholdSize rank) rank := by
  have hfloor : 2 * rank ≤ thresholdSize rank := two_mul_le_thresholdSize rank hrank
  exact gtzWeighted_of_hinge_of_predecessor' hrank hfloor
    (hingeHoldsAtSize_thresholdCell_of_arms rank hfreeArm hbalancedArm hdegenerateArm)
    hpredecessor

/-- **THE CENTRAL CELL FROM THE ARMS ALONE.**  At rank three the previous cell
is the decided `Gtz.gtzWeighted_of_le_five`, so `GtzWeighted 6 3` rests on the
three hinge arms and nothing else.  No reach hypothesis, no named anchor. -/
theorem gtzWeighted_six_three_of_arms (hfreeArm : ThresholdStressFreeArm 3)
    (hbalancedArm : ThresholdBalancedArm 3) (hdegenerateArm : ThresholdDegenerateArm 3) :
    GtzWeighted 6 3 := by
  have hcell := gtzWeighted_thresholdCell_of_arms (rank := 3) (by norm_num)
    (by rw [thresholdSize_three]; exact gtzWeighted_of_le_five 5 3 (by norm_num) (by norm_num))
    hfreeArm hbalancedArm hdegenerateArm
  rwa [thresholdSize_three] at hcell

/-- All of rank three from the three arms: the shipped crystallization carries
the central cell to every size. -/
theorem gtzWeightedAll_three_of_arms (hfreeArm : ThresholdStressFreeArm 3)
    (hbalancedArm : ThresholdBalancedArm 3) (hdegenerateArm : ThresholdDegenerateArm 3) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_arms hfreeArm hbalancedArm hdegenerateArm)

/-! ## The band and the top cell, named

The registry splits the window hinge into the sub-threshold band and the
deciding cell.  Both feed the size chain above, and the reach half of each has
left the hypothesis list. -/

/-- **THE BAND CELLS.**  The sub-threshold band hinge, relativized to the
previous cell exactly as the registry states it, closes every band cell once the
floor is in hand. -/
theorem gtzWeighted_band_of_bandHinge {rank : ℕ} (hrank : 3 ≤ rank)
    (hfloorCell : GtzWeighted (2 * rank - 1) rank)
    (hbandHinge : ∀ size : ℕ, 2 * rank ≤ size → size < thresholdSize rank →
      GtzWeighted (size - 1) rank → HingeHoldsAtSize size rank)
    (size : ℕ) (hfloor : 2 * rank - 1 ≤ size) (hband : size < thresholdSize rank) :
    GtzWeighted size rank := by
  have hclimb : ∀ extra : ℕ, 2 * rank - 1 + extra < thresholdSize rank →
      GtzWeighted (2 * rank - 1 + extra) rank := by
    intro extra
    induction extra with
    | zero => intro _; simpa using hfloorCell
    | succ prevExtra ih =>
        intro hbelow
        have hshift : 2 * rank - 1 + (prevExtra + 1) = (2 * rank - 1 + prevExtra) + 1 := by omega
        rw [hshift]
        have hprev := ih (by omega)
        refine gtzWeighted_of_hinge_of_predecessor hrank (by omega) ?_ hprev
        refine hbandHinge _ (by omega) (by omega) ?_
        simpa using hprev
  have hrewrite : 2 * rank - 1 + (size - (2 * rank - 1)) = size := by omega
  have hreached := hclimb (size - (2 * rank - 1)) (by omega)
  rwa [hrewrite] at hreached

/-- **THE DECIDING CELL FROM THE BAND.**  The band closes every cell below the
deciding cell, thus the deciding cell needs only its own hinge. -/
theorem gtzWeighted_thresholdCell_of_band_of_hinge {rank : ℕ} (hrank : 3 ≤ rank)
    (hfloorCell : GtzWeighted (2 * rank - 1) rank)
    (hbandHinge : ∀ size : ℕ, 2 * rank ≤ size → size < thresholdSize rank →
      GtzWeighted (size - 1) rank → HingeHoldsAtSize size rank)
    (hthresholdHinge : HingeHoldsAtSize (thresholdSize rank) rank) :
    GtzWeighted (thresholdSize rank) rank := by
  have hfloor : 2 * rank ≤ thresholdSize rank := two_mul_le_thresholdSize rank hrank
  refine gtzWeighted_of_hinge_of_predecessor' hrank hfloor hthresholdHinge ?_
  exact gtzWeighted_band_of_bandHinge hrank hfloorCell hbandHinge (thresholdSize rank - 1)
    (by omega) (by omega)

/-! ## Cross-checks -/

/-- The rank-four deciding cell is `(10,4)`, and it sits above the window
floor. -/
theorem thresholdCell_four_above_floor : 2 * 4 ≤ thresholdSize 4 := by
  rw [thresholdSize_four]
  norm_num

/-- The rank-four deciding cell from its arms and its previous cell. -/
theorem gtzWeighted_ten_four_of_arms (hpredecessor : GtzWeighted 9 4)
    (hfreeArm : ThresholdStressFreeArm 4) (hbalancedArm : ThresholdBalancedArm 4)
    (hdegenerateArm : ThresholdDegenerateArm 4) : GtzWeighted 10 4 := by
  have hcell := gtzWeighted_thresholdCell_of_arms (rank := 4) (by norm_num)
    (by rw [thresholdSize_four]; exact hpredecessor) hfreeArm hbalancedArm hdegenerateArm
  rwa [thresholdSize_four] at hcell

end GeneralRankReach
end Gtz
