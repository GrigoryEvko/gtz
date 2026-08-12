import Gtz.Wave.RungFourCapstone

set_option autoImplicit false
set_option relaxedAutoImplicit false

/-!
# What the fourth rung buys the index ladder

The rung is an exclusion, but the ladder's floor was already four, so excluding four
RAISES THE FLOOR rather than merely deleting a case.  Everything in this file is that
one observation composed with what the spine already had.

## Why the floor was not five before

`Gtz.SixThreeCrux.four_le_card_chartArgmaxFamily_strong` is unconditional and stops at
four.  Every five-floor in the repository carried a hypothesis:
`Gtz.SixThreeCrux.five_le_card_chartArgmaxFamily_of_fullSupport` and its active-block
refinement need a full-support least eigenvector at every active block;
`Gtz.SixThreeCrux.five_le_card_chartArgmaxFamily_of_forall_totalTightSupport_ne_two`
needs the same fact in support language;
`Gtz.five_le_card_chartArgmaxFamily_of_isSixThreeActiveTightSupportFull` needs the
support rung itself.  None of those hypotheses is discharged anywhere.  The fourth rung
discharges the CONCLUSION instead, so the five-floor lands with no hypothesis at all and
all four conditional forms are subsumed.

## What it costs the support rung

`Gtz.IsSixThreeActiveTightSupportFull` was worth two things: the five-floor, and the
count-four exclusion through
`Gtz.isSixThreeActiveCountExcluded_four_of_isSixThreeActiveTightSupportFull`.  Both are
now theorems, so the rung's remaining value is entirely in the second route --- it is
one of the two inputs of
`Gtz.gtzWeighted_six_three_of_isSixThreeActiveTightSupportFull_of_flatPairSeparated`,
whose other input is `Gtz.IsSixThreeFlatPairSeparated`.

## What it costs the count-four residual

`Gtz.SixThreeCrux.not_forall_exists_fullSupport_activeEigenvector_of_card_eq_four` and
`Gtz.SixThreeCrux.exists_active_coordinate_zero_on_tightEigenspace_of_card_eq_four` are
now VACUOUS: their common hypothesis is refuted by
`Gtz.SixThreeCrux.false_of_card_chartArgmaxFamily_eq_four`.  That matters because the
first of them is the sole recorded obstruction to the support rung --- the spine's own
docstring for `Gtz.IsSixThreeActiveTightSupportFull` cites it as proof that the rung
fails at count four.  It cannot fail there, because nothing sits there.  The same
applies to the whole count-four layer:
`Gtz.SixThreeCrux.exists_argmaxBlock_totalTightSupport_eq_two_of_card_eq_four`,
`Gtz.SixThreeCrux.exists_positive_stationary_supportTwo_of_four`, and the card-four
cancellation core of `Gtz.Wave.CriticalBridge` are all vacuous now, so none of them can
be reused as evidence about a counterexample.

## Vacuity

Every statement here is quantified over `Gtz.SixThreeCrux`, which is conjecturally
empty, so all of it is VACUOUSLY TRUE IF GTZ HOLDS.
-/

namespace Gtz

/-- **THE FIVE-BLOCK FLOOR, WITH NO HYPOTHESIS.**  A `(6,3)` counterexample has at least
five active blocks.  The unconditional four-floor and the fourth rung meet: the floor
forbids three or fewer, the rung forbids exactly four. -/
theorem SixThreeCrux.five_le_card_chartArgmaxFamily (crux : SixThreeCrux) :
    5 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card := by
  have hfloor := crux.four_le_card_chartArgmaxFamily_strong
  have hnotFour := isSixThreeActiveCountExcluded_four crux
  omega

/-- Every count below five is excluded outright.  This strengthens
`Gtz.isSixThreeActiveCountExcluded_of_lt_four` by exactly the fourth rung. -/
theorem isSixThreeActiveCountExcluded_of_lt_five (count : ℕ) (hcount : count < 5) :
    IsSixThreeActiveCountExcluded count := by
  intro crux hequal
  have hfloor := crux.five_le_card_chartArgmaxFamily
  omega

/-- **THE NARROWED INDEX WINDOW.**  The active count of a counterexample lies in
`[5, 20]`: sixteen values, against the seventeen of
`Gtz.SixThreeCrux.card_chartArgmaxFamily_mem_indexWindow`. -/
theorem SixThreeCrux.card_chartArgmaxFamily_mem_narrowedIndexWindow (crux : SixThreeCrux) :
    5 ≤ (chartArgmaxFamily (chartPointOfDesign crux.design)).card ∧
      (chartArgmaxFamily (chartPointOfDesign crux.design)).card ≤ 20 :=
  ⟨crux.five_le_card_chartArgmaxFamily, crux.card_chartArgmaxFamily_le_twenty⟩

/-- Excluding the sixteen surviving counts leaves a counterexample with nowhere to sit. -/
theorem false_of_sixThreeCrux_of_forall_isSixThreeActiveCountExcluded_five_to_twenty
    (hladder : ∀ count : ℕ, 5 ≤ count → count ≤ 20 → IsSixThreeActiveCountExcluded count)
    (crux : SixThreeCrux) : False := by
  obtain ⟨hfloor, hceiling⟩ := crux.card_chartArgmaxFamily_mem_narrowedIndexWindow
  exact hladder (chartArgmaxFamily (chartPointOfDesign crux.design)).card hfloor hceiling
    crux rfl

/-- **THE SPINE, ONE RUNG SHORTER.**  Sixteen rungs `5, ..., 20` prove the cell.  The
seventeen-rung form `Gtz.gtzWeighted_six_three_of_forall_isSixThreeActiveCountExcluded`
is recovered by feeding it this theorem together with
`Gtz.isSixThreeActiveCountExcluded_four`, so nothing is lost by quoting the shorter
list. -/
theorem gtzWeighted_six_three_of_forall_isSixThreeActiveCountExcluded_five_to_twenty
    (hladder : ∀ count : ℕ, 5 ≤ count → count ≤ 20 → IsSixThreeActiveCountExcluded count) :
    GtzWeighted 6 3 :=
  gtzWeighted_six_three_of_isEmpty_sixThreeCrux
    ⟨false_of_sixThreeCrux_of_forall_isSixThreeActiveCountExcluded_five_to_twenty hladder⟩

/-- **THE RANK-THREE PAYOFF FROM THE SHORTER LIST.**  Sixteen rungs close rank three at
every size, through the landed `Gtz.gtzWeightedAll_three_of_six_three`. -/
theorem gtzWeightedAll_three_of_forall_isSixThreeActiveCountExcluded_five_to_twenty
    (hladder : ∀ count : ℕ, 5 ≤ count → count ≤ 20 → IsSixThreeActiveCountExcluded count) :
    GtzWeightedAll 3 :=
  gtzWeightedAll_three_of_six_three
    (gtzWeighted_six_three_of_forall_isSixThreeActiveCountExcluded_five_to_twenty hladder)

/-- **THE SHORTER LIST IS STILL LOSSLESS, AND THEREFORE STILL BUYS NOTHING BY ITSELF.**
The sixteen rungs are jointly EQUIVALENT to the cell, exactly as the seventeen were.
Deleting a rung shortens the residual; it does not make the residual easier. -/
theorem forall_isSixThreeActiveCountExcluded_five_to_twenty_iff_gtzWeighted_six_three :
    (∀ count : ℕ, 5 ≤ count → count ≤ 20 → IsSixThreeActiveCountExcluded count)
      ↔ GtzWeighted 6 3 := by
  constructor
  · exact gtzWeighted_six_three_of_forall_isSixThreeActiveCountExcluded_five_to_twenty
  · intro hcell count _ _ crux
    exact absurd hcell (not_gtzWeighted_six_three_of_sixThreeCrux crux)

end Gtz
