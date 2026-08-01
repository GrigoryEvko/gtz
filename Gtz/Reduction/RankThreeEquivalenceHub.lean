/-
# Every mechanized form of the open cell, against the literal 1997 conjecture

`Gtz.GtzOriginal n 3` is the Goreinov-Tyrtyshnikov-Zamarashkin statement as written in
1997: every real `n x 3` matrix with orthonormal columns has an injective three-row pick
whose smallest singular value is at least `1 / sqrt n`.  Until this campaign no theorem
in the tree took it as a HYPOTHESIS, so the weighted programme could only ever imply it.
`Gtz.gtzWeightedAll_iff_forall_gtzOriginal` closed that gap and made the frame an
equivalence, and three rank-three termini were connected to it at once.

The remaining forms were not.  They accumulated across independent lanes -- a stress
walk to size seven, an all-heavy restriction, a value-zero deformation obligation, a
covering of the weight simplex, two floored-covering families -- each proved equivalent
to `Gtz.GtzWeighted 6 3` in its own module and none connected to the 1997 statement.
This file closes every one of them.

## Honest accounting

**EVERY THEOREM BELOW IS A SINGLE `Iff.trans` OF TWO SHIPPED EQUIVALENCES AND CARRIES NO
NEW MATHEMATICS.**  The file is a census, not a result.  It exists for three reasons.

* The composition fell between two authors.  The lane that landed the 1997 arrow and the
  lane that landed the size-seven collapse each identified it and each recorded it as
  belonging to the other, so neither built it.

* A form whose equivalence is untracked goes silently inert.  Five shipped theorems in
  this tree acquired jointly contradictory hypotheses the moment
  `Gtz.gtzWeighted_six_three_iff_seven_three` landed, and stayed that way across two
  campaigns because nothing recorded that the two sides had become one.  A census in one
  place is the direct mitigation: anything proved about any Prop named here is a
  statement about the 1997 conjecture at rank three, and a hypothesis pairing any of them
  with the failure of another is empty.

* The campaign's target is the 1997 conjecture, not a weighted proxy for it.  Stating
  each form against `Gtz.GtzOriginal` removes the last place a reader has to chain two
  theorems by hand to see what is actually open.

## What this does NOT do

It does not move `Gtz.GtzWeighted 6 3` and does not pretend to.  Every Prop named here
is exactly as open as it was; what changes is that the list of things equivalent to the
1997 conjecture at rank three is now readable in one place instead of assembled from six
modules.  Nothing here is a reduction: an equivalence is not progress, and several of
these forms were originally advertised as reductions before being shown to be the cell
itself.
-/
import Gtz.Reduction.ConverseBridge
import Gtz.Reduction.CoveringForm
import Gtz.Reduction.StressWalk
import Gtz.Quantitative.SevenThreeCollapse
import Gtz.Quantitative.DeformationAndCurvature
import Gtz.Quantitative.ValueLaneBandExclusion

namespace Gtz

/-! ## The size-seven forms -/

/-- **THE SEVEN-ATOM CELL IS THE 1997 CONJECTURE AT RANK THREE.**  The stress walk makes
`Gtz.GtzWeighted 7 3` equivalent to the six-atom cell; the converse bridge makes the
six-atom cell equivalent to the literal statement. -/
theorem gtzWeighted_seven_three_iff_forall_gtzOriginal_rank_three :
    GtzWeighted 7 3 ↔ ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  gtzWeighted_six_three_iff_seven_three.symm.trans
    gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three

/-- **THE ALL-HEAVY SIX-ATOM BOX IS THE 1997 CONJECTURE AT RANK THREE.**  Heaviness is
not a restriction at the frontier size: the deflation induction consumes it. -/
theorem gtzWeightedHeavy_six_three_iff_forall_gtzOriginal_rank_three :
    GtzWeightedHeavy 6 3 ↔ ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  gtzWeightedHeavy_six_three_iff_gtzWeighted_six_three.trans
    gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three

/-- **THE ALL-HEAVY SEVEN-ATOM BOX IS THE 1997 CONJECTURE AT RANK THREE.**  This is the
form most worth having on record: it is the weakest-looking of the six, and it is
exactly the statement whose pairing with a six-atom hypothesis silently emptied five
shipped theorems. -/
theorem gtzWeightedHeavy_seven_three_iff_forall_gtzOriginal_rank_three :
    GtzWeightedHeavy 7 3 ↔ ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  gtzWeightedHeavy_seven_three_iff_gtzWeighted_six_three.trans
    gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three

/-! ## The chart forms -/

/-- **THE VALUE-ZERO DEFORMATION OBLIGATION IS THE 1997 CONJECTURE AT RANK THREE.**  The
first leaf of the value-zero route was advertised as a reduction of the cell and is in
fact equivalent to it, because a crux can never satisfy `Gtz.IsChartValueZeroLimit` --
that predicate demands a dominating triple and a crux has none.  Chaining through the
converse bridge shows the obligation is the 1997 statement itself, which is the sharpest
available warning against reading it as a target. -/
theorem hasChartValueZeroLimitAtEveryCrux_iff_forall_gtzOriginal_rank_three :
    HasChartValueZeroLimitAtEveryCrux ↔ ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  hasChartValueZeroLimitAtEveryCrux_iff_gtzWeighted_six_three.trans
    gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three

/-- **THE COVERING FORM IS THE 1997 CONJECTURE AT RANK THREE.**  For every rank-three
projection on six coordinates the twenty spectrahedra `Gtz.CoversSimplex` names must
cover the weight simplex.  This is the combinatorially most explicit form the campaign
owns and it is, exactly, the 1997 statement. -/
theorem forall_coversSimplex_iff_forall_gtzOriginal_rank_three :
    (∀ chart : Matrix (Fin 6) (Fin 6) ℝ, chart.transpose = chart → chart * chart = chart →
        chart.trace = 3 → CoversSimplex chart 3)
      ↔ ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  gtzWeighted_six_three_iff_forall_coversSimplex.symm.trans
    gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three

/-! ## The floored-covering families -/

/-- **THE ALL-FLOORS WEIGHT-FLOORED COVERING IS THE 1997 CONJECTURE AT RANK THREE.**  The
value lane's slogan asked for a covering valid at the crux's own weight floor; because a
crux supplies its own floor, the family quantified over ALL positive floors is the cell,
hence the 1997 statement.  Recorded so the slogan cannot be mistaken for a sub-goal. -/
theorem forall_weightFlooredCovering_iff_forall_gtzOriginal_rank_three :
    (∀ floor : ℝ, 0 < floor → WeightFlooredCovering floor)
      ↔ ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  forall_weightFlooredCovering_iff_gtzWeighted_six_three.trans
    gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three

/-- **THE SAME AT THE TREE'S OWN COVERING PREDICATE.**  `Gtz.FlooredSpreadCovering` is
the shipped notion, strictly stronger than the weight-floored one (it also assumes
all-heaviness and a spread bound).  At zero spread and over all positive floors it too is
the 1997 statement, so the collapse is a property of the quantifier rather than of the
predicate. -/
theorem forall_flooredSpreadCovering_iff_forall_gtzOriginal_rank_three :
    (∀ floor : ℝ, 0 < floor → FlooredSpreadCovering 0 floor)
      ↔ ∀ n : ℕ, 0 < n → GtzOriginal n 3 :=
  forall_flooredSpreadCovering_iff_gtzWeighted_six_three.trans
    gtzWeighted_six_three_iff_forall_gtzOriginal_rank_three

end Gtz
