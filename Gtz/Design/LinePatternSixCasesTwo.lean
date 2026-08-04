/-
# The five middle six-point line patterns, and the enumeration closed

`Gtz.Design.LinePatternSixCases` cuts the six-point enumeration to five classes
and leaves them as two explicit hypotheses,
`Gtz.LinearSpaceThreePointLineCasesSix` (catalogue `#2`–`#5`) and
`Gtz.LinearSpaceFourPointLineCasesSix` (catalogue `#7`).  Both are proved here, so
`Gtz.LinearSpaceListIsComplete 6 Gtz.linePatternListSix` and
`Gtz.PatternListIsCompleteUpToRelabel 6 Gtz.linePatternListSix` hold with no
hypotheses at all.

## What that closes, and what it does not

The combinatorial input of `Gtz.hingeHoldsAtSize_of_linearSpaceEnumeration_sixThree`
is discharged.  The hinge itself is NOT: `Gtz.hingeHoldsAtSize_sixThree_of_tieFreeResidual`
still takes the eight tie-freeness obligations, one per non-near-pencil entry of
`Gtz.lineFamiliesSix`, and nothing here touches them.  Seven points is untouched
too, and remains off the critical path because
`Gtz.hingeHoldsAtSize_of_linearSpaceEnumeration_sevenThree` already carries the
open `Gtz.GtzWeighted 6 3`.

## The two lemmas the whole classification runs on

`Gtz.mem_threePointLine_of_two_mem` — with no four-point line a pair carries at
most one further label, so a dependent triple with two labels on a three-point
line has its third label there too.  Two distinct lines therefore meet in at most
one point, and that single fact replaces every incidence count in the informal
argument.

`Gtz.exists_meetLabel_or_allOutside` — a dependent triple not inside a closed set
either meets it exactly once, in which case the lemma hands back the meeting label
and the two outside labels in a normalized order, or misses it entirely.  Applied
to the seed line it splits `#2` from `#3`–`#5`; applied again to the second line it
proves `Gtz.exists_thirdLineShape`, which forces every further line through the one
label off both.  Since two lines through that label would share it and one more,
there are at most four lines in all — the counting bound of the informal proof,
obtained without counting.

## The five classes

* `#2` two disjoint three-point lines — `linearSpaceListIsComplete_six_disjointLinesCase`.
  Completeness is PROVED: a third line would need two labels on one of them.
* `#3` two meeting three-point lines — `linearSpaceListIsComplete_six_meetingLinesCase`.
* `#4` the triangle — `linearSpaceListIsComplete_six_triangleCase`.
* `#5` the graphic matroid `M(K4)` — `linearSpaceListIsComplete_six_graphicKFourCase`.
  Completeness is PROVED: a fifth line would run through the apex and share two
  labels with the third or the fourth.
* `#7` a four-point line meeting a three-point line —
  `linearSpaceListIsComplete_six_fourAndThreeCase`.

`#3` and `#4` take their completeness as a hypothesis, and the assembly supplies
it by `by_cases` on the existence of one more line; `#2` and `#5` are the two ends
of that chain and prove theirs.

## Two recorded facts

`Gtz.linearSpaceFourPointLineCasesSix_holds` and
`Gtz.linearSpaceThreePointLineCasesSix_holds` do NOT use the near-pencil clause
their statements offer.  In the four-point branch a chord is answered rather than
contradicted — `Gtz.linearSpaceListIsComplete_six_chordedFourPointLineCase` returns
the near pencil — and in the three-point branch there is no four-point line, hence
no five-point line, hence no pole to exclude.

`Gtz.forall_mem_fivePointLine_pattern` completes the family
`Gtz.forall_mem_threePointLine_pattern` / `Gtz.forall_mem_fourPointLine_pattern`
and carries the same recorded negative: `Gtz.pattern_of_forall_pattern_pivot`
cannot supply it, because it would need a degenerate value the three axioms do not
give.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.LinePatternEnumeration
import Gtz.Design.LinePatternSixCases
import Gtz.Quantitative.HingeStressNarrowing

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Gtz

/-! ## Labels of `Fin 6` -/


/-- Six pairwise distinct labels of `Fin 6` exhaust `Fin 6`. -/
theorem forall_eq_of_sixDistinctLabels
    (slotZero slotOne slotTwo slotThree slotFour slotFive : Fin 6)
    (hzeroOne : slotZero ≠ slotOne) (hzeroTwo : slotZero ≠ slotTwo)
    (hzeroThree : slotZero ≠ slotThree) (hzeroFour : slotZero ≠ slotFour)
    (hzeroFive : slotZero ≠ slotFive) (honeTwo : slotOne ≠ slotTwo)
    (honeThree : slotOne ≠ slotThree) (honeFour : slotOne ≠ slotFour)
    (honeFive : slotOne ≠ slotFive) (htwoThree : slotTwo ≠ slotThree)
    (htwoFour : slotTwo ≠ slotFour) (htwoFive : slotTwo ≠ slotFive)
    (hthreeFour : slotThree ≠ slotFour) (hthreeFive : slotThree ≠ slotFive)
    (hfourFive : slotFour ≠ slotFive) :
    ∀ label : Fin 6, label = slotZero ∨ label = slotOne ∨ label = slotTwo ∨
      label = slotThree ∨ label = slotFour ∨ label = slotFive := by
  classical
  have hcard : ({slotZero, slotOne, slotTwo, slotThree, slotFour, slotFive} :
      Finset (Fin 6)).card = 6 := by
    rw [Finset.card_insert_of_notMem
        (by simp [hzeroOne, hzeroTwo, hzeroThree, hzeroFour, hzeroFive]),
      Finset.card_insert_of_notMem (by simp [honeTwo, honeThree, honeFour, honeFive]),
      Finset.card_insert_of_notMem (by simp [htwoThree, htwoFour, htwoFive]),
      Finset.card_insert_of_notMem (by simp [hthreeFour, hthreeFive]),
      Finset.card_insert_of_notMem (by simp [hfourFive]), Finset.card_singleton]
  have huniv := eq_univ_of_six_distinct hcard
  intro label
  have hmem : label ∈ ({slotZero, slotOne, slotTwo, slotThree, slotFour, slotFive} :
      Finset (Fin 6)) := by rw [huniv]; exact Finset.mem_univ label
  simpa using hmem

/-- Five pairwise distinct labels of `Fin 6` leave a sixth. -/
theorem exists_sixthLabel (slotZero slotOne slotTwo slotThree slotFour : Fin 6)
    (hzeroOne : slotZero ≠ slotOne) (hzeroTwo : slotZero ≠ slotTwo)
    (hzeroThree : slotZero ≠ slotThree) (hzeroFour : slotZero ≠ slotFour)
    (honeTwo : slotOne ≠ slotTwo) (honeThree : slotOne ≠ slotThree)
    (honeFour : slotOne ≠ slotFour) (htwoThree : slotTwo ≠ slotThree)
    (htwoFour : slotTwo ≠ slotFour) (hthreeFour : slotThree ≠ slotFour) :
    ∃ slotFive : Fin 6, slotFive ≠ slotZero ∧ slotFive ≠ slotOne ∧ slotFive ≠ slotTwo ∧
      slotFive ≠ slotThree ∧ slotFive ≠ slotFour := by
  classical
  have hcard : ({slotZero, slotOne, slotTwo, slotThree, slotFour} : Finset (Fin 6)).card = 5 := by
    rw [Finset.card_insert_of_notMem (by simp [hzeroOne, hzeroTwo, hzeroThree, hzeroFour]),
      Finset.card_insert_of_notMem (by simp [honeTwo, honeThree, honeFour]),
      Finset.card_insert_of_notMem (by simp [htwoThree, htwoFour]),
      Finset.card_insert_of_notMem (by simp [hthreeFour]), Finset.card_singleton]
  have hcomplementCard :
      (({slotZero, slotOne, slotTwo, slotThree, slotFour} : Finset (Fin 6))ᶜ).card = 1 := by
    rw [Finset.card_compl, hcard, Fintype.card_fin]
  obtain ⟨slotFive, hcomplement⟩ := Finset.card_eq_one.mp hcomplementCard
  have hmem : slotFive ∈ (({slotZero, slotOne, slotTwo, slotThree, slotFour} :
      Finset (Fin 6))ᶜ) := by rw [hcomplement]; exact Finset.mem_singleton_self slotFive
  have hnot := Finset.mem_compl.mp hmem
  exact ⟨slotFive, by simpa [not_or] using hnot⟩


/-! ## Line soundness and the three-point closure -/


/-- **A five-point line is sound.**  Three dependent triples sharing the pivot
pair give the remaining seven by line closure, and the hundred-and-twenty-five
slot assignments follow.  The same recorded negative as at four points applies:
`Gtz.pattern_of_forall_pattern_pivot` cannot be used, because it would need a
degenerate value the three axioms do not supply. -/
theorem forall_mem_fivePointLine_pattern {size : ℕ} {pattern : LinePattern size}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (pivotFirst pivotSecond memberThird memberFourth memberFifth : Fin size)
    (hpivotDistinct : pivotFirst ≠ pivotSecond) (hthirdPivotFirst : memberThird ≠ pivotFirst)
    (hthird : pattern pivotFirst pivotSecond memberThird)
    (hfourth : pattern pivotFirst pivotSecond memberFourth)
    (hfifth : pattern pivotFirst pivotSecond memberFifth) :
    ∀ leftLabel ∈ [pivotFirst, pivotSecond, memberThird, memberFourth, memberFifth],
      ∀ midLabel ∈ [pivotFirst, pivotSecond, memberThird, memberFourth, memberFifth],
        ∀ rightLabel ∈ [pivotFirst, pivotSecond, memberThird, memberFourth, memberFifth],
          leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
            pattern leftLabel midLabel rightLabel := by
  have hfirstThirdFourth : pattern pivotFirst memberThird memberFourth :=
    haxioms.hasLineClosure pivotFirst pivotSecond memberThird memberFourth hpivotDistinct
      hthird hfourth
  have hfirstThirdFifth : pattern pivotFirst memberThird memberFifth :=
    haxioms.hasLineClosure pivotFirst pivotSecond memberThird memberFifth hpivotDistinct
      hthird hfifth
  have hfirstFourthFifth : pattern pivotFirst memberFourth memberFifth :=
    haxioms.hasLineClosure pivotFirst pivotSecond memberFourth memberFifth hpivotDistinct
      hfourth hfifth
  have hsecondThirdFourth : pattern pivotSecond memberThird memberFourth :=
    haxioms.hasLineClosure pivotSecond pivotFirst memberThird memberFourth
      (Ne.symm hpivotDistinct) (haxioms.isLeftSwapClosed _ _ _ hthird)
      (haxioms.isLeftSwapClosed _ _ _ hfourth)
  have hsecondThirdFifth : pattern pivotSecond memberThird memberFifth :=
    haxioms.hasLineClosure pivotSecond pivotFirst memberThird memberFifth
      (Ne.symm hpivotDistinct) (haxioms.isLeftSwapClosed _ _ _ hthird)
      (haxioms.isLeftSwapClosed _ _ _ hfifth)
  have hsecondFourthFifth : pattern pivotSecond memberFourth memberFifth :=
    haxioms.hasLineClosure pivotSecond pivotFirst memberFourth memberFifth
      (Ne.symm hpivotDistinct) (haxioms.isLeftSwapClosed _ _ _ hfourth)
      (haxioms.isLeftSwapClosed _ _ _ hfifth)
  have hthirdFourthFifth : pattern memberThird memberFourth memberFifth :=
    haxioms.hasLineClosure memberThird pivotFirst memberFourth memberFifth hthirdPivotFirst
      (haxioms.isLeftSwapClosed _ _ _ hfirstThirdFourth)
      (haxioms.isLeftSwapClosed _ _ _ hfirstThirdFifth)
  obtain ⟨ha1, ha2, ha3, ha4, ha5, ha6⟩ :=
    pattern_allSlotOrders haxioms pivotFirst pivotSecond memberThird hthird
  obtain ⟨hb1, hb2, hb3, hb4, hb5, hb6⟩ :=
    pattern_allSlotOrders haxioms pivotFirst pivotSecond memberFourth hfourth
  obtain ⟨hc1, hc2, hc3, hc4, hc5, hc6⟩ :=
    pattern_allSlotOrders haxioms pivotFirst pivotSecond memberFifth hfifth
  obtain ⟨hd1, hd2, hd3, hd4, hd5, hd6⟩ :=
    pattern_allSlotOrders haxioms pivotFirst memberThird memberFourth hfirstThirdFourth
  obtain ⟨he1, he2, he3, he4, he5, he6⟩ :=
    pattern_allSlotOrders haxioms pivotFirst memberThird memberFifth hfirstThirdFifth
  obtain ⟨hf1, hf2, hf3, hf4, hf5, hf6⟩ :=
    pattern_allSlotOrders haxioms pivotFirst memberFourth memberFifth hfirstFourthFifth
  obtain ⟨hg1, hg2, hg3, hg4, hg5, hg6⟩ :=
    pattern_allSlotOrders haxioms pivotSecond memberThird memberFourth hsecondThirdFourth
  obtain ⟨hh1, hh2, hh3, hh4, hh5, hh6⟩ :=
    pattern_allSlotOrders haxioms pivotSecond memberThird memberFifth hsecondThirdFifth
  obtain ⟨hi1, hi2, hi3, hi4, hi5, hi6⟩ :=
    pattern_allSlotOrders haxioms pivotSecond memberFourth memberFifth hsecondFourthFifth
  obtain ⟨hj1, hj2, hj3, hj4, hj5, hj6⟩ :=
    pattern_allSlotOrders haxioms memberThird memberFourth memberFifth hthirdFourthFifth
  intro leftLabel hleftMem midLabel hmidMem rightLabel hrightMem hleftMid hleftRight hmidRight
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hleftMem hmidMem hrightMem
  rcases hleftMem with rfl | rfl | rfl | rfl | rfl <;>
    rcases hmidMem with rfl | rfl | rfl | rfl | rfl <;>
      rcases hrightMem with rfl | rfl | rfl | rfl | rfl <;>
        first
          | exact absurd rfl hleftMid
          | exact absurd rfl hleftRight
          | exact absurd rfl hmidRight
          | assumption



/-- **Every long line has exactly three points**: no pair of labels carries two
distinct further dependent labels.  This is verbatim the second hypothesis of
`Gtz.LinearSpaceThreePointLineCasesSix`, named so the four classes below can state
it once. -/
def HasNoFourPointLine {size : ℕ} (pattern : LinePattern size) : Prop :=
  ∀ pivotFirst pivotSecond thirdLabel fourthLabel : Fin size, pivotFirst ≠ pivotSecond →
    thirdLabel ≠ fourthLabel → thirdLabel ≠ pivotFirst → thirdLabel ≠ pivotSecond →
      fourthLabel ≠ pivotFirst → fourthLabel ≠ pivotSecond →
        pattern pivotFirst pivotSecond thirdLabel → ¬ pattern pivotFirst pivotSecond fourthLabel

/-- **The third point of a pair is unique.**  With no four-point line, a pair
dependent with two labels is dependent with only one. -/
theorem eq_of_pattern_of_hasNoFourPointLine {size : ℕ} {pattern : LinePattern size}
    (hnoFour : HasNoFourPointLine pattern) (pairFirst pairSecond knownLabel testLabel : Fin size)
    (hpairDistinct : pairFirst ≠ pairSecond) (hknownFirst : knownLabel ≠ pairFirst)
    (hknownSecond : knownLabel ≠ pairSecond) (htestFirst : testLabel ≠ pairFirst)
    (htestSecond : testLabel ≠ pairSecond) (hknown : pattern pairFirst pairSecond knownLabel)
    (htest : pattern pairFirst pairSecond testLabel) : testLabel = knownLabel := by
  by_contra hdifferent
  exact hnoFour pairFirst pairSecond knownLabel testLabel hpairDistinct
    (fun hequal => hdifferent hequal.symm) hknownFirst hknownSecond htestFirst htestSecond
    hknown htest

/-- **A three-point line is closed.**  A dependent triple with two labels on a
named three-point line has its third label there too, so two distinct lines meet
in at most one point. -/
theorem mem_threePointLine_of_two_mem {size : ℕ} {pattern : LinePattern size}
    (haxioms : IsSpanningLinearSpacePattern pattern) (hnoFour : HasNoFourPointLine pattern)
    (lineFirst lineSecond lineThird : Fin size) (hfirstSecond : lineFirst ≠ lineSecond)
    (hfirstThird : lineFirst ≠ lineThird) (hsecondThird : lineSecond ≠ lineThird)
    (hline : pattern lineFirst lineSecond lineThird)
    (leftLabel midLabel rightLabel : Fin size) (hleftMid : leftLabel ≠ midLabel)
    (hleftRight : leftLabel ≠ rightLabel) (hmidRight : midLabel ≠ rightLabel)
    (hleftMem : leftLabel = lineFirst ∨ leftLabel = lineSecond ∨ leftLabel = lineThird)
    (hmidMem : midLabel = lineFirst ∨ midLabel = lineSecond ∨ midLabel = lineThird)
    (hpattern : pattern leftLabel midLabel rightLabel) :
    rightLabel = lineFirst ∨ rightLabel = lineSecond ∨ rightLabel = lineThird := by
  obtain ⟨hone, htwo, hthree, hfour, hfive, hsix⟩ :=
    pattern_allSlotOrders haxioms lineFirst lineSecond lineThird hline
  have hsecondFirst : lineSecond ≠ lineFirst := Ne.symm hfirstSecond
  have hthirdFirst : lineThird ≠ lineFirst := Ne.symm hfirstThird
  have hthirdSecond : lineThird ≠ lineSecond := Ne.symm hsecondThird
  have hmidLeft : midLabel ≠ leftLabel := Ne.symm hleftMid
  have hrightLeft : rightLabel ≠ leftLabel := Ne.symm hleftRight
  have hrightMid : rightLabel ≠ midLabel := Ne.symm hmidRight
  rcases hleftMem with rfl | rfl | rfl <;> rcases hmidMem with rfl | rfl | rfl <;>
    first
      | exact absurd rfl hleftMid
      | (refine Or.inl (eq_of_pattern_of_hasNoFourPointLine hnoFour _ _ lineFirst rightLabel
          ?_ ?_ ?_ ?_ ?_ ?_ hpattern) <;> assumption)
      | (refine Or.inr (Or.inl (eq_of_pattern_of_hasNoFourPointLine hnoFour _ _ lineSecond
          rightLabel ?_ ?_ ?_ ?_ ?_ ?_ hpattern)) <;> assumption)
      | (refine Or.inr (Or.inr (eq_of_pattern_of_hasNoFourPointLine hnoFour _ _ lineThird
          rightLabel ?_ ?_ ?_ ?_ ?_ ?_ hpattern)) <;> assumption)



/-- **A chord drags the whole four-point line onto its far label.**  If a
dependent triple has two of its labels on a four-point line and the third off it,
then EVERY pair of the line is dependent with that third label, so the line has
grown a fifth point. -/
theorem pattern_of_mem_fourPointLine_of_chord {size : ℕ} {pattern : LinePattern size}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (lineFirst lineSecond lineThird lineFourth chordLabel : Fin size)
    (hfirstSecond : lineFirst ≠ lineSecond)
    (hthird : pattern lineFirst lineSecond lineThird)
    (hfourth : pattern lineFirst lineSecond lineFourth)
    (chordFirst chordSecond : Fin size)
    (hchordFirstMem : chordFirst ∈ [lineFirst, lineSecond, lineThird, lineFourth])
    (hchordSecondMem : chordSecond ∈ [lineFirst, lineSecond, lineThird, lineFourth])
    (hchordDistinct : chordFirst ≠ chordSecond)
    (hlabelChordFirst : chordLabel ≠ chordFirst) (hlabelChordSecond : chordLabel ≠ chordSecond)
    (hchord : pattern chordFirst chordSecond chordLabel) :
    ∀ leftLabel ∈ [lineFirst, lineSecond, lineThird, lineFourth],
      ∀ midLabel ∈ [lineFirst, lineSecond, lineThird, lineFourth],
        leftLabel ≠ midLabel → chordLabel ≠ leftLabel → chordLabel ≠ midLabel →
          pattern leftLabel midLabel chordLabel := by
  have hlineSound := forall_mem_fourPointLine_pattern haxioms lineFirst lineSecond lineThird
    lineFourth hfirstSecond hthird hfourth
  have hthroughChordFirst : ∀ memberLabel ∈ [lineFirst, lineSecond, lineThird, lineFourth],
      memberLabel ≠ chordFirst → chordLabel ≠ memberLabel →
        pattern chordFirst memberLabel chordLabel := by
    intro memberLabel hmemberMem hmemberChordFirst hlabelMember
    by_cases hmemberChordSecond : memberLabel = chordSecond
    · subst hmemberChordSecond; exact hchord
    · have hspread : pattern chordFirst chordSecond memberLabel :=
        hlineSound chordFirst hchordFirstMem chordSecond hchordSecondMem memberLabel hmemberMem
          hchordDistinct (Ne.symm hmemberChordFirst) (Ne.symm hmemberChordSecond)
      exact haxioms.isRightSwapClosed _ _ _ (haxioms.hasLineClosure chordFirst chordSecond
        chordLabel memberLabel hchordDistinct hchord hspread)
  intro leftLabel hleftMem midLabel hmidMem hleftMid hlabelLeft hlabelMid
  by_cases hleftChordFirst : leftLabel = chordFirst
  · subst hleftChordFirst
    exact hthroughChordFirst midLabel hmidMem (Ne.symm hleftMid) hlabelMid
  · have hleftPair : pattern leftLabel chordFirst chordLabel :=
      haxioms.isLeftSwapClosed _ _ _
        (hthroughChordFirst leftLabel hleftMem hleftChordFirst hlabelLeft)
    by_cases hmidChordFirst : midLabel = chordFirst
    · subst hmidChordFirst; exact hleftPair
    · have hleftChordMid : pattern leftLabel chordFirst midLabel :=
        hlineSound leftLabel hleftMem chordFirst hchordFirstMem midLabel hmidMem
          hleftChordFirst hleftMid (Ne.symm hmidChordFirst)
      exact haxioms.isRightSwapClosed _ _ _ (haxioms.hasLineClosure leftLabel chordFirst
        chordLabel midLabel hleftChordFirst hleftPair hleftChordMid)


/-! ## Catalogue `#7`: a four-point line meeting a three-point line -/

/-- **A four-point line with a chord is the near pencil.**  A dependent triple
with two labels on a four-point line and the third off it grows the line to five
points, and the sixth label is then a pole. -/
theorem linearSpaceListIsComplete_six_chordedFourPointLineCase {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (lineFirst lineSecond lineThird lineFourth chordLabel : Fin 6)
    (hfirstSecond : lineFirst ≠ lineSecond) (hfirstThird : lineFirst ≠ lineThird)
    (hfirstFourth : lineFirst ≠ lineFourth) (hsecondThird : lineSecond ≠ lineThird)
    (hsecondFourth : lineSecond ≠ lineFourth) (hthirdFourth : lineThird ≠ lineFourth)
    (hlabelFirst : chordLabel ≠ lineFirst) (hlabelSecond : chordLabel ≠ lineSecond)
    (hlabelThird : chordLabel ≠ lineThird) (hlabelFourth : chordLabel ≠ lineFourth)
    (hthird : pattern lineFirst lineSecond lineThird)
    (hfourth : pattern lineFirst lineSecond lineFourth)
    (chordFirst chordSecond : Fin 6)
    (hchordFirstMem : chordFirst ∈ [lineFirst, lineSecond, lineThird, lineFourth])
    (hchordSecondMem : chordSecond ∈ [lineFirst, lineSecond, lineThird, lineFourth])
    (hchordDistinct : chordFirst ≠ chordSecond)
    (hlabelChordFirst : chordLabel ≠ chordFirst) (hlabelChordSecond : chordLabel ≠ chordSecond)
    (hchord : pattern chordFirst chordSecond chordLabel) :
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  have hspread := pattern_of_mem_fourPointLine_of_chord haxioms lineFirst lineSecond lineThird
    lineFourth chordLabel hfirstSecond hthird hfourth chordFirst chordSecond hchordFirstMem
    hchordSecondMem hchordDistinct hlabelChordFirst hlabelChordSecond hchord
  have hfifth : pattern lineFirst lineSecond chordLabel :=
    hspread lineFirst (by simp) lineSecond (by simp) hfirstSecond hlabelFirst hlabelSecond
  have hsound := forall_mem_fivePointLine_pattern haxioms lineFirst lineSecond lineThird
    lineFourth chordLabel hfirstSecond (Ne.symm hfirstThird) hthird hfourth hfifth
  obtain ⟨poleLabel, hpoleFirst, hpoleSecond, hpoleThird, hpoleFourth, hpoleLabel⟩ :=
    exists_sixthLabel lineFirst lineSecond lineThird lineFourth chordLabel hfirstSecond
      hfirstThird hfirstFourth (Ne.symm hlabelFirst) hsecondThird hsecondFourth
      (Ne.symm hlabelSecond) hthirdFourth (Ne.symm hlabelThird) (Ne.symm hlabelFourth)
  have hcover := forall_eq_of_sixDistinctLabels lineFirst lineSecond lineThird lineFourth
    chordLabel poleLabel hfirstSecond hfirstThird hfirstFourth (Ne.symm hlabelFirst)
    (Ne.symm hpoleFirst) hsecondThird hsecondFourth (Ne.symm hlabelSecond) (Ne.symm hpoleSecond)
    hthirdFourth (Ne.symm hlabelThird) (Ne.symm hpoleThird) (Ne.symm hlabelFourth)
    (Ne.symm hpoleFourth) (Ne.symm hpoleLabel)
  have hmemOfNePole : ∀ label : Fin 6, label ≠ poleLabel →
      label ∈ [lineFirst, lineSecond, lineThird, lineFourth, chordLabel] := by
    intro label hlabel
    rcases hcover label with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | exact absurd rfl hlabel | simp
  refine linearSpaceListIsComplete_six_nearPencilCase haxioms poleLabel ?_
  intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hleftPole hmidPole hrightPole
  exact hsound leftLabel (hmemOfNePole leftLabel hleftPole) midLabel
    (hmemOfNePole midLabel hmidPole) rightLabel (hmemOfNePole rightLabel hrightPole)
    hleftMid hleftRight hmidRight

/-- **Catalogue `#7`, closed.**  A four-point line and a three-point line meeting
it in one point, with nothing else dependent, is the seventh entry after
relabelling. -/
theorem linearSpaceListIsComplete_six_fourAndThreeCase {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (meetLabel lineSecond lineThird lineFourth offFirst offSecond : Fin 6)
    (hmeetSecond : meetLabel ≠ lineSecond) (hmeetThird : meetLabel ≠ lineThird)
    (hmeetFourth : meetLabel ≠ lineFourth) (hmeetOffFirst : meetLabel ≠ offFirst)
    (hmeetOffSecond : meetLabel ≠ offSecond) (hsecondThird : lineSecond ≠ lineThird)
    (hsecondFourth : lineSecond ≠ lineFourth) (hsecondOffFirst : lineSecond ≠ offFirst)
    (hsecondOffSecond : lineSecond ≠ offSecond) (hthirdFourth : lineThird ≠ lineFourth)
    (hthirdOffFirst : lineThird ≠ offFirst) (hthirdOffSecond : lineThird ≠ offSecond)
    (hfourthOffFirst : lineFourth ≠ offFirst) (hfourthOffSecond : lineFourth ≠ offSecond)
    (hoffDistinct : offFirst ≠ offSecond)
    (hlongThird : pattern meetLabel lineSecond lineThird)
    (hlongFourth : pattern meetLabel lineSecond lineFourth)
    (hshort : pattern meetLabel offFirst offSecond)
    (honly : ∀ leftLabel midLabel rightLabel : Fin 6,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel →
          ((leftLabel = meetLabel ∨ leftLabel = lineSecond ∨ leftLabel = lineThird ∨
              leftLabel = lineFourth) ∧
            (midLabel = meetLabel ∨ midLabel = lineSecond ∨ midLabel = lineThird ∨
              midLabel = lineFourth) ∧
            (rightLabel = meetLabel ∨ rightLabel = lineSecond ∨ rightLabel = lineThird ∨
              rightLabel = lineFourth)) ∨
          ((leftLabel = meetLabel ∨ leftLabel = offFirst ∨ leftLabel = offSecond) ∧
            (midLabel = meetLabel ∨ midLabel = offFirst ∨ midLabel = offSecond) ∧
            (rightLabel = meetLabel ∨ rightLabel = offFirst ∨ rightLabel = offSecond))) :
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  have hinjective := injective_sixLabelMap_of_pairwise (slotZero := meetLabel)
    (slotOne := lineSecond) (slotTwo := lineThird) (slotThree := lineFourth)
    (slotFour := offFirst) (slotFive := offSecond) hmeetSecond hmeetThird hmeetFourth
    hmeetOffFirst hmeetOffSecond hsecondThird hsecondFourth hsecondOffFirst hsecondOffSecond
    hthirdFourth hthirdOffFirst hthirdOffSecond hfourthOffFirst hfourthOffSecond hoffDistinct
  obtain ⟨relabel, hrelabel⟩ := exists_relabel_agreesOnDistinctTriples_of_labelledFamily
    (pattern := pattern) hinjective [[0, 1, 2, 3], [0, 4, 5]] (by
      have hmapped : ([[(0 : Fin 6), 1, 2, 3], [0, 4, 5]].map (List.map (sixLabelMap meetLabel
          lineSecond lineThird lineFourth offFirst offSecond)))
            = [[meetLabel, lineSecond, lineThird, lineFourth], [meetLabel, offFirst, offSecond]] :=
        rfl
      rw [hmapped]
      refine agreesOnDistinctTriples_lineFamilyPattern_of_sound_complete (pattern := pattern)
        [[meetLabel, lineSecond, lineThird, lineFourth], [meetLabel, offFirst, offSecond]] ?_ ?_
      · intro line hline
        have hlineEq : line = [meetLabel, lineSecond, lineThird, lineFourth] ∨
            line = [meetLabel, offFirst, offSecond] := by simpa using hline
        rcases hlineEq with rfl | rfl
        · exact forall_mem_fourPointLine_pattern haxioms meetLabel lineSecond lineThird
            lineFourth hmeetSecond hlongThird hlongFourth
        · exact forall_mem_threePointLine_pattern haxioms meetLabel offFirst offSecond hshort
      · intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
        rcases honly leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern with
          ⟨hleft, hmid, hright⟩ | ⟨hleft, hmid, hright⟩
        · exact ⟨[meetLabel, lineSecond, lineThird, lineFourth], by simp, by simpa using hleft,
            by simpa using hmid, by simpa using hright⟩
        · exact ⟨[meetLabel, offFirst, offSecond], by simp, by simpa using hleft,
            by simpa using hmid, by simpa using hright⟩)
  exact ⟨lineFamilyPattern [[0, 1, 2, 3], [0, 4, 5]],
    List.mem_map.mpr ⟨[[0, 1, 2, 3], [0, 4, 5]], by decide, rfl⟩, relabel, hrelabel⟩


/-- **Catalogue `#7`, discharged.**  A four-point line together with a dependent
triple outside it is either a near pencil — when the outside triple has two of its
labels on the line — or the seventh entry.  The pole clause of
`Gtz.LinearSpaceFourPointLineCasesSix` is not used: the near-pencil branch is
answered rather than contradicted. -/
theorem linearSpaceFourPointLineCasesSix_holds : LinearSpaceFourPointLineCasesSix := by
  classical
  intro pattern haxioms lineFirst lineSecond lineThird lineFourth hfirstSecond hfirstThird
    hfirstFourth hsecondThird hsecondFourth hthirdFourth hthird hfourth hextra _hnoPole
  by_cases hchord : ∃ chordFirst chordSecond chordLabel : Fin 6,
      chordFirst ≠ chordSecond ∧ chordLabel ≠ chordFirst ∧ chordLabel ≠ chordSecond ∧
        chordFirst ∈ [lineFirst, lineSecond, lineThird, lineFourth] ∧
        chordSecond ∈ [lineFirst, lineSecond, lineThird, lineFourth] ∧
        chordLabel ≠ lineFirst ∧ chordLabel ≠ lineSecond ∧ chordLabel ≠ lineThird ∧
        chordLabel ≠ lineFourth ∧ pattern chordFirst chordSecond chordLabel
  · obtain ⟨chordFirst, chordSecond, chordLabel, hchordDistinct, hlabelChordFirst,
      hlabelChordSecond, hchordFirstMem, hchordSecondMem, hlabelFirst, hlabelSecond,
      hlabelThird, hlabelFourth, hchordPattern⟩ := hchord
    exact linearSpaceListIsComplete_six_chordedFourPointLineCase haxioms lineFirst lineSecond
      lineThird lineFourth chordLabel hfirstSecond hfirstThird hfirstFourth hsecondThird
      hsecondFourth hthirdFourth hlabelFirst hlabelSecond hlabelThird hlabelFourth hthird
      hfourth chordFirst chordSecond hchordFirstMem hchordSecondMem hchordDistinct
      hlabelChordFirst hlabelChordSecond hchordPattern
  · have hlineSound := forall_mem_fourPointLine_pattern haxioms lineFirst lineSecond lineThird
      lineFourth hfirstSecond hthird hfourth
    have hnoChord : ∀ leftLabel midLabel rightLabel : Fin 6, leftLabel ≠ midLabel →
        rightLabel ≠ leftLabel → rightLabel ≠ midLabel →
        (leftLabel = lineFirst ∨ leftLabel = lineSecond ∨ leftLabel = lineThird ∨
          leftLabel = lineFourth) →
        (midLabel = lineFirst ∨ midLabel = lineSecond ∨ midLabel = lineThird ∨
          midLabel = lineFourth) → pattern leftLabel midLabel rightLabel →
          (rightLabel = lineFirst ∨ rightLabel = lineSecond ∨ rightLabel = lineThird ∨
            rightLabel = lineFourth) := by
      intro leftLabel midLabel rightLabel hleftMid hrightLeft hrightMid hleftMem hmidMem hpattern
      by_contra hrightMem
      simp only [not_or] at hrightMem
      exact hchord ⟨leftLabel, midLabel, rightLabel, hleftMid, hrightLeft, hrightMid,
        by simpa using hleftMem, by simpa using hmidMem, hrightMem.1, hrightMem.2.1,
        hrightMem.2.2.1, hrightMem.2.2.2, hpattern⟩
    obtain ⟨offFirst, offSecond, hoffDistinct, hoffAvoids⟩ :=
      exists_offFourPointLine_pair lineFirst lineSecond lineThird lineFourth hfirstSecond
        hfirstThird hfirstFourth hsecondThird hsecondFourth hthirdFourth
    obtain ⟨hoffFirstOne, hoffFirstTwo, hoffFirstThree, hoffFirstFour⟩ :=
      hoffAvoids offFirst (Or.inl rfl)
    obtain ⟨hoffSecondOne, hoffSecondTwo, hoffSecondThree, hoffSecondFour⟩ :=
      hoffAvoids offSecond (Or.inr rfl)
    have hfirstOffFirst : lineFirst ≠ offFirst := Ne.symm hoffFirstOne
    have hsecondOffFirstLine : lineSecond ≠ offFirst := Ne.symm hoffFirstTwo
    have hthirdOffFirstLine : lineThird ≠ offFirst := Ne.symm hoffFirstThree
    have hfourthOffFirstLine : lineFourth ≠ offFirst := Ne.symm hoffFirstFour
    have hfirstOffSecond : lineFirst ≠ offSecond := Ne.symm hoffSecondOne
    have hsecondOffSecondLine : lineSecond ≠ offSecond := Ne.symm hoffSecondTwo
    have hthirdOffSecondLine : lineThird ≠ offSecond := Ne.symm hoffSecondThree
    have hfourthOffSecondLine : lineFourth ≠ offSecond := Ne.symm hoffSecondFour
    have hcover := forall_eq_of_sixDistinctLabels lineFirst lineSecond lineThird lineFourth
      offFirst offSecond hfirstSecond hfirstThird hfirstFourth (Ne.symm hoffFirstOne)
      (Ne.symm hoffSecondOne) hsecondThird hsecondFourth (Ne.symm hoffFirstTwo)
      (Ne.symm hoffSecondTwo) hthirdFourth (Ne.symm hoffFirstThree) (Ne.symm hoffSecondThree)
      (Ne.symm hoffFirstFour) (Ne.symm hoffSecondFour) hoffDistinct
    have hoffMem : ∀ label : Fin 6,
        ¬ (label = lineFirst ∨ label = lineSecond ∨ label = lineThird ∨
          label = lineFourth) → label = offFirst ∨ label = offSecond := by
      intro label hlabel
      rcases hcover label with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | (exact absurd (by simp) hlabel) | simp
    have hnotThreeOff : ∀ leftLabel midLabel rightLabel : Fin 6, leftLabel ≠ midLabel →
        leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        ¬ (leftLabel = lineFirst ∨ leftLabel = lineSecond ∨ leftLabel = lineThird ∨
          leftLabel = lineFourth) →
        ¬ (midLabel = lineFirst ∨ midLabel = lineSecond ∨ midLabel = lineThird ∨
          midLabel = lineFourth) →
        ¬ (rightLabel = lineFirst ∨ rightLabel = lineSecond ∨ rightLabel = lineThird ∨
          rightLabel = lineFourth) → False := by
      intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hleft hmid hright
      rcases hoffMem leftLabel hleft with rfl | rfl <;>
        rcases hoffMem midLabel hmid with rfl | rfl <;>
          rcases hoffMem rightLabel hright with rfl | rfl <;>
            first
              | exact absurd rfl hleftMid
              | exact absurd rfl hleftRight
              | exact absurd rfl hmidRight
    have hshortOf : ∀ meetLabel leftLabel rightLabel : Fin 6, leftLabel ≠ rightLabel →
        ¬ (leftLabel = lineFirst ∨ leftLabel = lineSecond ∨ leftLabel = lineThird ∨
          leftLabel = lineFourth) →
        ¬ (rightLabel = lineFirst ∨ rightLabel = lineSecond ∨ rightLabel = lineThird ∨
          rightLabel = lineFourth) → pattern meetLabel leftLabel rightLabel →
          pattern meetLabel offFirst offSecond := by
      intro meetLabel leftLabel rightLabel hleftRight hleft hright hpattern
      rcases hoffMem leftLabel hleft with rfl | rfl <;>
        rcases hoffMem rightLabel hright with rfl | rfl <;>
          first
            | exact absurd rfl hleftRight
            | exact hpattern
            | exact haxioms.isRightSwapClosed _ _ _ hpattern
    have hmeetOf : ∀ leftLabel midLabel rightLabel : Fin 6, leftLabel ≠ midLabel →
        leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel →
        ¬ ((leftLabel = lineFirst ∨ leftLabel = lineSecond ∨ leftLabel = lineThird ∨
              leftLabel = lineFourth) ∧
            (midLabel = lineFirst ∨ midLabel = lineSecond ∨ midLabel = lineThird ∨
              midLabel = lineFourth) ∧
            (rightLabel = lineFirst ∨ rightLabel = lineSecond ∨ rightLabel = lineThird ∨
              rightLabel = lineFourth)) →
        ∃ meetLabel : Fin 6, (meetLabel = lineFirst ∨ meetLabel = lineSecond ∨
            meetLabel = lineThird ∨ meetLabel = lineFourth) ∧
          pattern meetLabel offFirst offSecond ∧
          (leftLabel = meetLabel ∨ leftLabel = offFirst ∨ leftLabel = offSecond) ∧
          (midLabel = meetLabel ∨ midLabel = offFirst ∨ midLabel = offSecond) ∧
          (rightLabel = meetLabel ∨ rightLabel = offFirst ∨ rightLabel = offSecond) := by
      intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern houtside
      by_cases hleft : leftLabel = lineFirst ∨ leftLabel = lineSecond ∨
          leftLabel = lineThird ∨ leftLabel = lineFourth
      · by_cases hmid : midLabel = lineFirst ∨ midLabel = lineSecond ∨
            midLabel = lineThird ∨ midLabel = lineFourth
        · exact absurd ⟨hleft, hmid, hnoChord leftLabel midLabel rightLabel hleftMid
            (Ne.symm hleftRight) (Ne.symm hmidRight) hleft hmid hpattern⟩ houtside
        · by_cases hright : rightLabel = lineFirst ∨ rightLabel = lineSecond ∨
              rightLabel = lineThird ∨ rightLabel = lineFourth
          · exact absurd (hnoChord leftLabel rightLabel midLabel hleftRight (Ne.symm hleftMid)
              hmidRight hleft hright (haxioms.isRightSwapClosed _ _ _ hpattern)) hmid
          · exact ⟨leftLabel, hleft, hshortOf leftLabel midLabel rightLabel hmidRight hmid hright
              hpattern, Or.inl rfl, Or.inr (hoffMem midLabel hmid),
              Or.inr (hoffMem rightLabel hright)⟩
      · by_cases hmid : midLabel = lineFirst ∨ midLabel = lineSecond ∨
            midLabel = lineThird ∨ midLabel = lineFourth
        · by_cases hright : rightLabel = lineFirst ∨ rightLabel = lineSecond ∨
              rightLabel = lineThird ∨ rightLabel = lineFourth
          · exact absurd (hnoChord midLabel rightLabel leftLabel hmidRight hleftMid hleftRight
              hmid hright (pattern_rotate_of_isSpanningLinearSpacePattern haxioms _ _ _
                hpattern)) hleft
          · exact ⟨midLabel, hmid, hshortOf midLabel leftLabel rightLabel hleftRight hleft hright
              (haxioms.isLeftSwapClosed _ _ _ hpattern), Or.inr (hoffMem leftLabel hleft),
              Or.inl rfl, Or.inr (hoffMem rightLabel hright)⟩
        · by_cases hright : rightLabel = lineFirst ∨ rightLabel = lineSecond ∨
              rightLabel = lineThird ∨ rightLabel = lineFourth
          · exact ⟨rightLabel, hright, hshortOf rightLabel leftLabel midLabel hleftMid hleft hmid
              (haxioms.isLeftSwapClosed _ _ _ (haxioms.isRightSwapClosed _ _ _ hpattern)),
              Or.inr (hoffMem leftLabel hleft), Or.inr (hoffMem midLabel hmid), Or.inl rfl⟩
          · exact absurd (hnotThreeOff leftLabel midLabel rightLabel hleftMid hleftRight
              hmidRight hleft hmid hright) (by simp)
    obtain ⟨extraLeft, extraMid, extraRight, hextraLeftMid, hextraLeftRight, hextraMidRight,
      hextraPattern, hextraOutside⟩ := hextra
    obtain ⟨meetLabel, hmeetMem, hmeetShort, -, -, -⟩ := hmeetOf extraLeft extraMid extraRight
      hextraLeftMid hextraLeftRight hextraMidRight hextraPattern hextraOutside
    have hmeetOffFirst : meetLabel ≠ offFirst := by
      rcases hmeetMem with rfl | rfl | rfl | rfl <;> assumption
    have hmeetOffSecond : meetLabel ≠ offSecond := by
      rcases hmeetMem with rfl | rfl | rfl | rfl <;> assumption
    have hmeetUnique : ∀ otherLabel : Fin 6, (otherLabel = lineFirst ∨ otherLabel = lineSecond ∨
        otherLabel = lineThird ∨ otherLabel = lineFourth) →
        pattern otherLabel offFirst offSecond → otherLabel = meetLabel := by
      intro otherLabel hotherMem hotherShort
      by_contra hdifferent
      have hotherOffFirst : offFirst ≠ otherLabel := by
        rcases hotherMem with rfl | rfl | rfl | rfl <;> assumption
      have hotherRotated : pattern offFirst offSecond otherLabel :=
        pattern_rotate_of_isSpanningLinearSpacePattern haxioms _ _ _ hotherShort
      have hmeetRotated : pattern offFirst offSecond meetLabel :=
        pattern_rotate_of_isSpanningLinearSpacePattern haxioms _ _ _ hmeetShort
      have hjoined : pattern otherLabel meetLabel offFirst :=
        pattern_rotate_of_isSpanningLinearSpacePattern haxioms _ _ _
          (haxioms.hasLineClosure offFirst offSecond otherLabel meetLabel hoffDistinct
            hotherRotated hmeetRotated)
      have hoffFirstMem := hnoChord otherLabel meetLabel offFirst hdifferent hotherOffFirst
        (Ne.symm hmeetOffFirst) hotherMem hmeetMem hjoined
      rcases hoffFirstMem with h | h | h | h
      exacts [hoffFirstOne h, hoffFirstTwo h, hoffFirstThree h, hoffFirstFour h]
    obtain ⟨lineSecond', lineThird', lineFourth', hsecondThird', hsecondFourth', hthirdFourth',
      hremainingAvoids, hremainingCover⟩ :=
      exists_offLine_triple meetLabel offFirst offSecond hmeetOffFirst hmeetOffSecond hoffDistinct
    obtain ⟨hsecondMeet, hsecondOffFirst, hsecondOffSecond⟩ := hremainingAvoids lineSecond'
      (Or.inl rfl)
    obtain ⟨hthirdMeet, hthirdOffFirst, hthirdOffSecond⟩ := hremainingAvoids lineThird'
      (Or.inr (Or.inl rfl))
    obtain ⟨hfourthMeet, hfourthOffFirst, hfourthOffSecond⟩ := hremainingAvoids lineFourth'
      (Or.inr (Or.inr rfl))
    have hinLine : ∀ label : Fin 6, label ≠ offFirst → label ≠ offSecond →
        (label = lineFirst ∨ label = lineSecond ∨ label = lineThird ∨ label = lineFourth) := by
      intro label hfirstNe hsecondNe
      rcases hcover label with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | (exact absurd rfl hfirstNe) | (exact absurd rfl hsecondNe) | simp
    have hsecondMemLine := hinLine lineSecond' hsecondOffFirst hsecondOffSecond
    have hthirdMemLine := hinLine lineThird' hthirdOffFirst hthirdOffSecond
    have hfourthMemLine := hinLine lineFourth' hfourthOffFirst hfourthOffSecond
    have hmemList : ∀ label : Fin 6, (label = lineFirst ∨ label = lineSecond ∨
        label = lineThird ∨ label = lineFourth) →
        label ∈ [lineFirst, lineSecond, lineThird, lineFourth] := by
      intro label hlabel; simpa using hlabel
    have hlongThird : pattern meetLabel lineSecond' lineThird' :=
      hlineSound meetLabel (hmemList _ hmeetMem) lineSecond' (hmemList _ hsecondMemLine)
        lineThird' (hmemList _ hthirdMemLine) (Ne.symm hsecondMeet) (Ne.symm hthirdMeet)
        hsecondThird'
    have hlongFourth : pattern meetLabel lineSecond' lineFourth' :=
      hlineSound meetLabel (hmemList _ hmeetMem) lineSecond' (hmemList _ hsecondMemLine)
        lineFourth' (hmemList _ hfourthMemLine) (Ne.symm hsecondMeet) (Ne.symm hfourthMeet)
        hsecondFourth'
    have hlineMemNew : ∀ label : Fin 6, (label = lineFirst ∨ label = lineSecond ∨
        label = lineThird ∨ label = lineFourth) →
        (label = meetLabel ∨ label = lineSecond' ∨ label = lineThird' ∨ label = lineFourth') := by
      intro label hlabel
      have hfirstNe : label ≠ offFirst := by
        rcases hlabel with rfl | rfl | rfl | rfl <;> assumption
      have hsecondNe : label ≠ offSecond := by
        rcases hlabel with rfl | rfl | rfl | rfl <;> assumption
      rcases hremainingCover label with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first | (exact absurd rfl hfirstNe) | (exact absurd rfl hsecondNe) | simp
    refine linearSpaceListIsComplete_six_fourAndThreeCase haxioms meetLabel lineSecond'
      lineThird' lineFourth' offFirst offSecond (Ne.symm hsecondMeet) (Ne.symm hthirdMeet)
      (Ne.symm hfourthMeet) hmeetOffFirst hmeetOffSecond hsecondThird' hsecondFourth'
      hsecondOffFirst hsecondOffSecond hthirdFourth' hthirdOffFirst hthirdOffSecond
      hfourthOffFirst hfourthOffSecond hoffDistinct hlongThird hlongFourth hmeetShort ?_
    intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
    by_cases hall : (leftLabel = lineFirst ∨ leftLabel = lineSecond ∨ leftLabel = lineThird ∨
          leftLabel = lineFourth) ∧
        (midLabel = lineFirst ∨ midLabel = lineSecond ∨ midLabel = lineThird ∨
          midLabel = lineFourth) ∧
        (rightLabel = lineFirst ∨ rightLabel = lineSecond ∨ rightLabel = lineThird ∨
          rightLabel = lineFourth)
    · exact Or.inl ⟨hlineMemNew _ hall.1, hlineMemNew _ hall.2.1, hlineMemNew _ hall.2.2⟩
    · obtain ⟨otherLabel, hotherMem, hotherShort, hleft, hmid, hright⟩ :=
        hmeetOf leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern hall
      have hotherEq : otherLabel = meetLabel := hmeetUnique otherLabel hotherMem hotherShort
      subst hotherEq
      exact Or.inr ⟨hleft, hmid, hright⟩


/-! ## The peeling lemma shared by every multi-line case -/

/-- **A dependent triple not inside a closed set meets it at most once.**  Either
exactly one of its labels lies inside, and the lemma returns that label together
with the two outside ones in a normalized order, or none of them does. -/
theorem exists_meetLabel_or_allOutside {size : ℕ} {pattern : LinePattern size}
    (haxioms : IsSpanningLinearSpacePattern pattern) (isInside : Fin size → Prop)
    (hclosed : ∀ leftLabel midLabel rightLabel : Fin size, leftLabel ≠ midLabel →
      leftLabel ≠ rightLabel → midLabel ≠ rightLabel → isInside leftLabel → isInside midLabel →
        pattern leftLabel midLabel rightLabel → isInside rightLabel)
    (leftLabel midLabel rightLabel : Fin size) (hleftMid : leftLabel ≠ midLabel)
    (hleftRight : leftLabel ≠ rightLabel) (hmidRight : midLabel ≠ rightLabel)
    (hpattern : pattern leftLabel midLabel rightLabel)
    (houtside : ¬ (isInside leftLabel ∧ isInside midLabel ∧ isInside rightLabel)) :
    (∃ meetLabel outFirst outSecond : Fin size, isInside meetLabel ∧ ¬ isInside outFirst ∧
        ¬ isInside outSecond ∧ outFirst ≠ outSecond ∧ pattern meetLabel outFirst outSecond ∧
        (leftLabel = meetLabel ∨ leftLabel = outFirst ∨ leftLabel = outSecond) ∧
        (midLabel = meetLabel ∨ midLabel = outFirst ∨ midLabel = outSecond) ∧
        (rightLabel = meetLabel ∨ rightLabel = outFirst ∨ rightLabel = outSecond)) ∨
      (¬ isInside leftLabel ∧ ¬ isInside midLabel ∧ ¬ isInside rightLabel) := by
  classical
  by_cases hleft : isInside leftLabel
  · by_cases hmid : isInside midLabel
    · exact absurd ⟨hleft, hmid, hclosed leftLabel midLabel rightLabel hleftMid hleftRight
        hmidRight hleft hmid hpattern⟩ houtside
    · by_cases hright : isInside rightLabel
      · exact absurd (hclosed leftLabel rightLabel midLabel hleftRight hleftMid
          (Ne.symm hmidRight) hleft hright (haxioms.isRightSwapClosed _ _ _ hpattern)) hmid
      · exact Or.inl ⟨leftLabel, midLabel, rightLabel, hleft, hmid, hright, hmidRight, hpattern,
          Or.inl rfl, Or.inr (Or.inl rfl), Or.inr (Or.inr rfl)⟩
  · by_cases hmid : isInside midLabel
    · by_cases hright : isInside rightLabel
      · exact absurd (hclosed midLabel rightLabel leftLabel hmidRight (Ne.symm hleftMid)
          (Ne.symm hleftRight) hmid hright
          (pattern_rotate_of_isSpanningLinearSpacePattern haxioms _ _ _ hpattern)) hleft
      · exact Or.inl ⟨midLabel, leftLabel, rightLabel, hmid, hleft, hright, hleftRight,
          haxioms.isLeftSwapClosed _ _ _ hpattern, Or.inr (Or.inl rfl), Or.inl rfl,
          Or.inr (Or.inr rfl)⟩
    · by_cases hright : isInside rightLabel
      · exact Or.inl ⟨rightLabel, leftLabel, midLabel, hright, hleft, hmid, hleftMid,
          haxioms.isLeftSwapClosed _ _ _ (haxioms.isRightSwapClosed _ _ _ hpattern),
          Or.inr (Or.inl rfl), Or.inr (Or.inr rfl), Or.inl rfl⟩
      · exact Or.inr ⟨hleft, hmid, hright⟩

/-! ## Catalogue `#2` and `#3`: two three-point lines -/

/-- **Catalogue `#2`, closed.**  Two disjoint three-point lines partitioning the
six labels carry no further dependent triple, so completeness is proved here
rather than assumed: a third line would need two labels on one of them. -/
theorem linearSpaceListIsComplete_six_disjointLinesCase {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern) (hnoFour : HasNoFourPointLine pattern)
    (firstLeft firstMid firstRight secondLeft secondMid secondRight : Fin 6)
    (hfirstLeftMid : firstLeft ≠ firstMid) (hfirstLeftRight : firstLeft ≠ firstRight)
    (hfirstLeftSecondLeft : firstLeft ≠ secondLeft)
    (hfirstLeftSecondMid : firstLeft ≠ secondMid)
    (hfirstLeftSecondRight : firstLeft ≠ secondRight) (hfirstMidRight : firstMid ≠ firstRight)
    (hfirstMidSecondLeft : firstMid ≠ secondLeft) (hfirstMidSecondMid : firstMid ≠ secondMid)
    (hfirstMidSecondRight : firstMid ≠ secondRight)
    (hfirstRightSecondLeft : firstRight ≠ secondLeft)
    (hfirstRightSecondMid : firstRight ≠ secondMid)
    (hfirstRightSecondRight : firstRight ≠ secondRight)
    (hsecondLeftMid : secondLeft ≠ secondMid) (hsecondLeftRight : secondLeft ≠ secondRight)
    (hsecondMidRight : secondMid ≠ secondRight)
    (hlineFirst : pattern firstLeft firstMid firstRight)
    (hlineSecond : pattern secondLeft secondMid secondRight) :
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  classical
  have hcover := forall_eq_of_sixDistinctLabels firstLeft firstMid firstRight secondLeft
    secondMid secondRight hfirstLeftMid hfirstLeftRight hfirstLeftSecondLeft
    hfirstLeftSecondMid hfirstLeftSecondRight hfirstMidRight hfirstMidSecondLeft
    hfirstMidSecondMid hfirstMidSecondRight hfirstRightSecondLeft hfirstRightSecondMid
    hfirstRightSecondRight hsecondLeftMid hsecondLeftRight hsecondMidRight
  have hclosedFirst : ∀ leftLabel midLabel rightLabel : Fin 6, leftLabel ≠ midLabel →
      leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
      (leftLabel = firstLeft ∨ leftLabel = firstMid ∨ leftLabel = firstRight) →
      (midLabel = firstLeft ∨ midLabel = firstMid ∨ midLabel = firstRight) →
      pattern leftLabel midLabel rightLabel →
      (rightLabel = firstLeft ∨ rightLabel = firstMid ∨ rightLabel = firstRight) :=
    fun leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hleft hmid hpattern =>
      mem_threePointLine_of_two_mem haxioms hnoFour firstLeft firstMid firstRight hfirstLeftMid
        hfirstLeftRight hfirstMidRight hlineFirst leftLabel midLabel rightLabel hleftMid
        hleftRight hmidRight hleft hmid hpattern
  have hclosedSecond : ∀ leftLabel midLabel rightLabel : Fin 6, leftLabel ≠ midLabel →
      leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
      (leftLabel = secondLeft ∨ leftLabel = secondMid ∨ leftLabel = secondRight) →
      (midLabel = secondLeft ∨ midLabel = secondMid ∨ midLabel = secondRight) →
      pattern leftLabel midLabel rightLabel →
      (rightLabel = secondLeft ∨ rightLabel = secondMid ∨ rightLabel = secondRight) :=
    fun leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hleft hmid hpattern =>
      mem_threePointLine_of_two_mem haxioms hnoFour secondLeft secondMid secondRight
        hsecondLeftMid hsecondLeftRight hsecondMidRight hlineSecond leftLabel midLabel rightLabel
        hleftMid hleftRight hmidRight hleft hmid hpattern
  have hotherLine : ∀ label : Fin 6,
      ¬ (label = firstLeft ∨ label = firstMid ∨ label = firstRight) →
        (label = secondLeft ∨ label = secondMid ∨ label = secondRight) := by
    intro label hlabel
    rcases hcover label with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | (exact absurd (by simp) hlabel) | simp
  have hdisjoint : ∀ label : Fin 6,
      (label = firstLeft ∨ label = firstMid ∨ label = firstRight) →
        ¬ (label = secondLeft ∨ label = secondMid ∨ label = secondRight) := by
    intro label hlabel hother
    rcases hlabel with rfl | rfl | rfl <;> rcases hother with heq | heq | heq <;>
      first
        | exact hfirstLeftSecondLeft heq | exact hfirstLeftSecondMid heq
        | exact hfirstLeftSecondRight heq | exact hfirstMidSecondLeft heq
        | exact hfirstMidSecondMid heq | exact hfirstMidSecondRight heq
        | exact hfirstRightSecondLeft heq | exact hfirstRightSecondMid heq
        | exact hfirstRightSecondRight heq
  have hinjective := injective_sixLabelMap_of_pairwise (slotZero := firstLeft)
    (slotOne := firstMid) (slotTwo := firstRight) (slotThree := secondLeft)
    (slotFour := secondMid) (slotFive := secondRight) hfirstLeftMid hfirstLeftRight
    hfirstLeftSecondLeft hfirstLeftSecondMid hfirstLeftSecondRight hfirstMidRight
    hfirstMidSecondLeft hfirstMidSecondMid hfirstMidSecondRight hfirstRightSecondLeft
    hfirstRightSecondMid hfirstRightSecondRight hsecondLeftMid hsecondLeftRight
    hsecondMidRight
  obtain ⟨relabel, hrelabel⟩ := exists_relabel_agreesOnDistinctTriples_of_labelledFamily
    (pattern := pattern) hinjective [[0, 1, 2], [3, 4, 5]] (by
      have hmapped : ([[(0 : Fin 6), 1, 2], [3, 4, 5]].map (List.map (sixLabelMap firstLeft
          firstMid firstRight secondLeft secondMid secondRight)))
            = [[firstLeft, firstMid, firstRight], [secondLeft, secondMid, secondRight]] := rfl
      rw [hmapped]
      refine agreesOnDistinctTriples_lineFamilyPattern_of_sound_complete (pattern := pattern)
        [[firstLeft, firstMid, firstRight], [secondLeft, secondMid, secondRight]] ?_ ?_
      · intro line hline
        have hlineEq : line = [firstLeft, firstMid, firstRight] ∨
            line = [secondLeft, secondMid, secondRight] := by simpa using hline
        rcases hlineEq with rfl | rfl
        · exact forall_mem_threePointLine_pattern haxioms firstLeft firstMid firstRight
            hlineFirst
        · exact forall_mem_threePointLine_pattern haxioms secondLeft secondMid secondRight
            hlineSecond
      · intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
        obtain ⟨hone, htwo, hthree, hfour, hfive, hsix⟩ :=
          pattern_allSlotOrders haxioms leftLabel midLabel rightLabel hpattern
        have hfinish : ((leftLabel = firstLeft ∨ leftLabel = firstMid ∨
              leftLabel = firstRight) ∧
            (midLabel = firstLeft ∨ midLabel = firstMid ∨ midLabel = firstRight) ∧
            (rightLabel = firstLeft ∨ rightLabel = firstMid ∨ rightLabel = firstRight)) ∨
          ((leftLabel = secondLeft ∨ leftLabel = secondMid ∨ leftLabel = secondRight) ∧
            (midLabel = secondLeft ∨ midLabel = secondMid ∨ midLabel = secondRight) ∧
            (rightLabel = secondLeft ∨ rightLabel = secondMid ∨
              rightLabel = secondRight)) := by
          by_cases hleftFirst : leftLabel = firstLeft ∨ leftLabel = firstMid ∨
              leftLabel = firstRight
          · by_cases hmidFirst : midLabel = firstLeft ∨ midLabel = firstMid ∨
                midLabel = firstRight
            · exact Or.inl ⟨hleftFirst, hmidFirst, hclosedFirst leftLabel midLabel rightLabel
                hleftMid hleftRight hmidRight hleftFirst hmidFirst hpattern⟩
            · by_cases hrightFirst : rightLabel = firstLeft ∨ rightLabel = firstMid ∨
                  rightLabel = firstRight
              · exact absurd (hclosedFirst leftLabel rightLabel midLabel hleftRight hleftMid
                  (Ne.symm hmidRight) hleftFirst hrightFirst htwo) hmidFirst
              · exact absurd (hclosedSecond midLabel rightLabel leftLabel hmidRight
                  (Ne.symm hleftMid) (Ne.symm hleftRight) (hotherLine midLabel hmidFirst)
                  (hotherLine rightLabel hrightFirst) hfour) (hdisjoint leftLabel hleftFirst)
          · by_cases hmidFirst : midLabel = firstLeft ∨ midLabel = firstMid ∨
                midLabel = firstRight
            · by_cases hrightFirst : rightLabel = firstLeft ∨ rightLabel = firstMid ∨
                  rightLabel = firstRight
              · exact absurd (hclosedFirst midLabel rightLabel leftLabel hmidRight
                  (Ne.symm hleftMid) (Ne.symm hleftRight) hmidFirst hrightFirst hfour)
                  hleftFirst
              · exact absurd (hclosedSecond leftLabel rightLabel midLabel hleftRight hleftMid
                  (Ne.symm hmidRight) (hotherLine leftLabel hleftFirst)
                  (hotherLine rightLabel hrightFirst) htwo) (hdisjoint midLabel hmidFirst)
            · by_cases hrightFirst : rightLabel = firstLeft ∨ rightLabel = firstMid ∨
                  rightLabel = firstRight
              · exact absurd (hclosedSecond leftLabel midLabel rightLabel hleftMid hleftRight
                  hmidRight (hotherLine leftLabel hleftFirst) (hotherLine midLabel hmidFirst)
                  hpattern) (hdisjoint rightLabel hrightFirst)
              · exact Or.inr ⟨hotherLine leftLabel hleftFirst, hotherLine midLabel hmidFirst,
                  hotherLine rightLabel hrightFirst⟩
        rcases hfinish with ⟨hleft, hmid, hright⟩ | ⟨hleft, hmid, hright⟩
        · exact ⟨[firstLeft, firstMid, firstRight], by simp, by simpa using hleft,
            by simpa using hmid, by simpa using hright⟩
        · exact ⟨[secondLeft, secondMid, secondRight], by simp, by simpa using hleft,
            by simpa using hmid, by simpa using hright⟩)
  exact ⟨lineFamilyPattern [[0, 1, 2], [3, 4, 5]],
    List.mem_map.mpr ⟨[[0, 1, 2], [3, 4, 5]], by decide, rfl⟩, relabel, hrelabel⟩


/-! ## The meeting configuration, and catalogue `#3` through `#5`

Two three-point lines meeting at `meetLabel`, with `apexLabel` off both.  Which of
the four remaining entries a pattern is depends only on how many further lines it
carries, and `exists_thirdLineShape` forces every further line through
`apexLabel`, so there are at most two of them. -/

/-- **The shape of a third line.**  A dependent triple inside neither of two
meeting three-point lines takes one label from each line, off their common point,
together with the label off both. -/
theorem exists_thirdLineShape {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern) (hnoFour : HasNoFourPointLine pattern)
    (meetLabel firstArm firstTip secondArm secondTip apexLabel : Fin 6)
    (hmeetFirstArm : meetLabel ≠ firstArm) (hmeetFirstTip : meetLabel ≠ firstTip)
    (hmeetSecondArm : meetLabel ≠ secondArm) (hmeetSecondTip : meetLabel ≠ secondTip)
    (hmeetApex : meetLabel ≠ apexLabel) (hfirstArmTip : firstArm ≠ firstTip)
    (hfirstArmSecondArm : firstArm ≠ secondArm) (hfirstArmSecondTip : firstArm ≠ secondTip)
    (hfirstArmApex : firstArm ≠ apexLabel) (hfirstTipSecondArm : firstTip ≠ secondArm)
    (hfirstTipSecondTip : firstTip ≠ secondTip) (hfirstTipApex : firstTip ≠ apexLabel)
    (hsecondArmTip : secondArm ≠ secondTip) (hsecondArmApex : secondArm ≠ apexLabel)
    (hsecondTipApex : secondTip ≠ apexLabel)
    (hlineFirst : pattern meetLabel firstArm firstTip)
    (hlineSecond : pattern meetLabel secondArm secondTip)
    (leftLabel midLabel rightLabel : Fin 6) (hleftMid : leftLabel ≠ midLabel)
    (hleftRight : leftLabel ≠ rightLabel) (hmidRight : midLabel ≠ rightLabel)
    (hpattern : pattern leftLabel midLabel rightLabel)
    (houtsideFirst : ¬ ((leftLabel = meetLabel ∨ leftLabel = firstArm ∨ leftLabel = firstTip) ∧
      (midLabel = meetLabel ∨ midLabel = firstArm ∨ midLabel = firstTip) ∧
      (rightLabel = meetLabel ∨ rightLabel = firstArm ∨ rightLabel = firstTip)))
    (houtsideSecond : ¬ ((leftLabel = meetLabel ∨ leftLabel = secondArm ∨
        leftLabel = secondTip) ∧
      (midLabel = meetLabel ∨ midLabel = secondArm ∨ midLabel = secondTip) ∧
      (rightLabel = meetLabel ∨ rightLabel = secondArm ∨ rightLabel = secondTip))) :
    ∃ armLabel oppositeLabel : Fin 6, (armLabel = firstArm ∨ armLabel = firstTip) ∧
      (oppositeLabel = secondArm ∨ oppositeLabel = secondTip) ∧
      pattern armLabel oppositeLabel apexLabel ∧
      (leftLabel = armLabel ∨ leftLabel = oppositeLabel ∨ leftLabel = apexLabel) ∧
      (midLabel = armLabel ∨ midLabel = oppositeLabel ∨ midLabel = apexLabel) ∧
      (rightLabel = armLabel ∨ rightLabel = oppositeLabel ∨ rightLabel = apexLabel) := by
  classical
  have hcover := forall_eq_of_sixDistinctLabels meetLabel firstArm firstTip secondArm
    secondTip apexLabel hmeetFirstArm hmeetFirstTip hmeetSecondArm hmeetSecondTip hmeetApex
    hfirstArmTip hfirstArmSecondArm hfirstArmSecondTip hfirstArmApex hfirstTipSecondArm
    hfirstTipSecondTip hfirstTipApex hsecondArmTip hsecondArmApex hsecondTipApex
  have hclosedFirst : ∀ leftOne midOne rightOne : Fin 6, leftOne ≠ midOne → leftOne ≠ rightOne →
      midOne ≠ rightOne → (leftOne = meetLabel ∨ leftOne = firstArm ∨ leftOne = firstTip) →
      (midOne = meetLabel ∨ midOne = firstArm ∨ midOne = firstTip) →
      pattern leftOne midOne rightOne →
        (rightOne = meetLabel ∨ rightOne = firstArm ∨ rightOne = firstTip) :=
    fun leftOne midOne rightOne hone htwo hthree hleft hmid hpat =>
      mem_threePointLine_of_two_mem haxioms hnoFour meetLabel firstArm firstTip hmeetFirstArm
        hmeetFirstTip hfirstArmTip hlineFirst leftOne midOne rightOne hone htwo hthree hleft
        hmid hpat
  have hclosedSecond : ∀ leftOne midOne rightOne : Fin 6, leftOne ≠ midOne →
      leftOne ≠ rightOne → midOne ≠ rightOne →
      (leftOne = meetLabel ∨ leftOne = secondArm ∨ leftOne = secondTip) →
      (midOne = meetLabel ∨ midOne = secondArm ∨ midOne = secondTip) →
      pattern leftOne midOne rightOne →
        (rightOne = meetLabel ∨ rightOne = secondArm ∨ rightOne = secondTip) :=
    fun leftOne midOne rightOne hone htwo hthree hleft hmid hpat =>
      mem_threePointLine_of_two_mem haxioms hnoFour meetLabel secondArm secondTip hmeetSecondArm
        hmeetSecondTip hsecondArmTip hlineSecond leftOne midOne rightOne hone htwo hthree hleft
        hmid hpat
  have hapexNotSecond : ¬ (apexLabel = meetLabel ∨ apexLabel = secondArm ∨
      apexLabel = secondTip) := by
    simp only [not_or]
    exact ⟨Ne.symm hmeetApex, Ne.symm hsecondArmApex, Ne.symm hsecondTipApex⟩
  have hnotFirstMem : ∀ label : Fin 6,
      ¬ (label = meetLabel ∨ label = firstArm ∨ label = firstTip) →
        (label = secondArm ∨ label = secondTip ∨ label = apexLabel) := by
    intro label hlabel
    rcases hcover label with rfl | rfl | rfl | rfl | rfl | rfl <;>
      first | (exact absurd (by simp) hlabel) | simp
  have hoffToSecond : ∀ label : Fin 6,
      ¬ (label = meetLabel ∨ label = firstArm ∨ label = firstTip) → label ≠ apexLabel →
        (label = meetLabel ∨ label = secondArm ∨ label = secondTip) := by
    intro label hlabel hapex
    rcases hnotFirstMem label hlabel with heq | heq | heq
    exacts [Or.inr (Or.inl heq), Or.inr (Or.inr heq), absurd heq hapex]
  have honlyMeet : ∀ label : Fin 6,
      (label = meetLabel ∨ label = firstArm ∨ label = firstTip) →
      (label = meetLabel ∨ label = secondArm ∨ label = secondTip) → label = meetLabel := by
    intro label hfirst hsecond
    rcases hfirst with rfl | rfl | rfl
    · rfl
    · rcases hsecond with heq | heq | heq
      exacts [heq, absurd heq hfirstArmSecondArm, absurd heq hfirstArmSecondTip]
    · rcases hsecond with heq | heq | heq
      exacts [heq, absurd heq hfirstTipSecondArm, absurd heq hfirstTipSecondTip]
  rcases exists_meetLabel_or_allOutside haxioms
      (fun label => label = meetLabel ∨ label = firstArm ∨ label = firstTip) hclosedFirst
      leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern houtsideFirst with
    ⟨armLabel, outFirst, outSecond, harmMem, houtFirstNot, houtSecondNot, houtDistinct,
      harmPattern, hleftMem, hmidMem, hrightMem⟩ | ⟨hleftNot, hmidNot, hrightNot⟩
  · have harmMemClean : armLabel = meetLabel ∨ armLabel = firstArm ∨ armLabel = firstTip :=
      harmMem
    have houtFirstClean : ¬ (outFirst = meetLabel ∨ outFirst = firstArm ∨
      outFirst = firstTip) := houtFirstNot
    have houtSecondClean : ¬ (outSecond = meetLabel ∨ outSecond = firstArm ∨
      outSecond = firstTip) := houtSecondNot
    have harmOutFirst : armLabel ≠ outFirst := fun heq => houtFirstClean (heq ▸ harmMemClean)
    have harmOutSecond : armLabel ≠ outSecond := fun heq => houtSecondClean (heq ▸ harmMemClean)
    have harmNotApex : ∀ oppositeLabel : Fin 6,
        (oppositeLabel = secondArm ∨ oppositeLabel = secondTip) →
        pattern armLabel oppositeLabel apexLabel → armLabel ≠ apexLabel →
        oppositeLabel ≠ apexLabel → armLabel ≠ oppositeLabel →
          (armLabel = firstArm ∨ armLabel = firstTip) := by
      intro oppositeLabel hopposite hpat harmApex hoppositeApex harmOpposite
      rcases harmMemClean with rfl | heq | heq
      · exact absurd (hclosedSecond armLabel oppositeLabel apexLabel harmOpposite harmApex
          hoppositeApex (Or.inl rfl) (Or.inr hopposite) hpat) hapexNotSecond
      · exact Or.inl heq
      · exact Or.inr heq
    by_cases hfirstApex : outFirst = apexLabel
    · have hoppositeMem : outSecond = secondArm ∨ outSecond = secondTip := by
        rcases hnotFirstMem outSecond houtSecondClean with heq | heq | heq
        exacts [Or.inl heq, Or.inr heq, absurd (hfirstApex.trans heq.symm) houtDistinct]
      have hswapped : pattern armLabel outSecond apexLabel := by
        rw [← hfirstApex]; exact haxioms.isRightSwapClosed _ _ _ harmPattern
      have hoppositeApex : outSecond ≠ apexLabel := fun heq =>
        houtDistinct (hfirstApex.trans heq.symm)
      refine ⟨armLabel, outSecond, harmNotApex outSecond hoppositeMem hswapped ?_ hoppositeApex
        harmOutSecond, hoppositeMem, hswapped, ?_, ?_, ?_⟩
      · rw [← hfirstApex]; exact harmOutFirst
      · rw [hfirstApex] at hleftMem
        rcases hleftMem with heq | heq | heq
        exacts [Or.inl heq, Or.inr (Or.inr heq), Or.inr (Or.inl heq)]
      · rw [hfirstApex] at hmidMem
        rcases hmidMem with heq | heq | heq
        exacts [Or.inl heq, Or.inr (Or.inr heq), Or.inr (Or.inl heq)]
      · rw [hfirstApex] at hrightMem
        rcases hrightMem with heq | heq | heq
        exacts [Or.inl heq, Or.inr (Or.inr heq), Or.inr (Or.inl heq)]
    · by_cases hsecondApex : outSecond = apexLabel
      · have hoppositeMem : outFirst = secondArm ∨ outFirst = secondTip := by
          rcases hnotFirstMem outFirst houtFirstClean with heq | heq | heq
          exacts [Or.inl heq, Or.inr heq, absurd heq hfirstApex]
        have hshifted : pattern armLabel outFirst apexLabel := by
          rw [← hsecondApex]; exact harmPattern
        refine ⟨armLabel, outFirst, harmNotApex outFirst hoppositeMem hshifted ?_ ?_
          harmOutFirst, hoppositeMem, hshifted, ?_, ?_, ?_⟩
        · rw [← hsecondApex]; exact harmOutSecond
        · rw [← hsecondApex]; exact houtDistinct
        · rw [hsecondApex] at hleftMem; exact hleftMem
        · rw [hsecondApex] at hmidMem; exact hmidMem
        · rw [hsecondApex] at hrightMem; exact hrightMem
      · exfalso
        have hfirstIn : outFirst = meetLabel ∨ outFirst = secondArm ∨ outFirst = secondTip :=
          hoffToSecond outFirst houtFirstClean hfirstApex
        have hsecondIn : outSecond = meetLabel ∨ outSecond = secondArm ∨
            outSecond = secondTip := hoffToSecond outSecond houtSecondClean hsecondApex
        have harmIn : armLabel = meetLabel ∨ armLabel = secondArm ∨ armLabel = secondTip :=
          hclosedSecond outFirst outSecond armLabel houtDistinct (Ne.symm harmOutFirst)
            (Ne.symm harmOutSecond) hfirstIn hsecondIn
            (pattern_rotate_of_isSpanningLinearSpacePattern haxioms _ _ _ harmPattern)
        refine houtsideSecond ⟨?_, ?_, ?_⟩
        · rcases hleftMem with rfl | rfl | rfl <;> assumption
        · rcases hmidMem with rfl | rfl | rfl <;> assumption
        · rcases hrightMem with rfl | rfl | rfl <;> assumption
  · have hleftClean : ¬ (leftLabel = meetLabel ∨ leftLabel = firstArm ∨
      leftLabel = firstTip) := hleftNot
    have hmidClean : ¬ (midLabel = meetLabel ∨ midLabel = firstArm ∨
      midLabel = firstTip) := hmidNot
    have hrightClean : ¬ (rightLabel = meetLabel ∨ rightLabel = firstArm ∨
      rightLabel = firstTip) := hrightNot
    exfalso
    by_cases hleftApex : leftLabel = apexLabel
    · have hmidApex : midLabel ≠ apexLabel := fun heq => hleftMid (hleftApex.trans heq.symm)
      have hrightApex : rightLabel ≠ apexLabel := fun heq => hleftRight (hleftApex.trans heq.symm)
      have hmidIn := hoffToSecond midLabel hmidClean hmidApex
      have hrightIn := hoffToSecond rightLabel hrightClean hrightApex
      exact houtsideSecond ⟨hclosedSecond midLabel rightLabel leftLabel hmidRight
        (Ne.symm hleftMid) (Ne.symm hleftRight) hmidIn hrightIn
        (pattern_rotate_of_isSpanningLinearSpacePattern haxioms _ _ _ hpattern),
        hmidIn, hrightIn⟩
    · by_cases hmidApex : midLabel = apexLabel
      · have hrightApex : rightLabel ≠ apexLabel := fun heq =>
          hmidRight (hmidApex.trans heq.symm)
        have hleftIn := hoffToSecond leftLabel hleftClean hleftApex
        have hrightIn := hoffToSecond rightLabel hrightClean hrightApex
        exact houtsideSecond ⟨hleftIn, hclosedSecond leftLabel rightLabel midLabel hleftRight
          hleftMid (Ne.symm hmidRight) hleftIn hrightIn
          (haxioms.isRightSwapClosed _ _ _ hpattern), hrightIn⟩
      · have hleftIn := hoffToSecond leftLabel hleftClean hleftApex
        have hmidIn := hoffToSecond midLabel hmidClean hmidApex
        exact houtsideSecond ⟨hleftIn, hmidIn, hclosedSecond leftLabel midLabel rightLabel
          hleftMid hleftRight hmidRight hleftIn hmidIn hpattern⟩


/-- **Catalogue `#3`, closed.**  Two three-point lines meeting in one point, with
nothing else dependent, is the third entry after relabelling. -/
theorem linearSpaceListIsComplete_six_meetingLinesCase {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (meetLabel firstArm firstTip secondArm secondTip apexLabel : Fin 6)
    (hmeetFirstArm : meetLabel ≠ firstArm) (hmeetFirstTip : meetLabel ≠ firstTip)
    (hmeetSecondArm : meetLabel ≠ secondArm) (hmeetSecondTip : meetLabel ≠ secondTip)
    (hmeetApex : meetLabel ≠ apexLabel) (hfirstArmTip : firstArm ≠ firstTip)
    (hfirstArmSecondArm : firstArm ≠ secondArm) (hfirstArmSecondTip : firstArm ≠ secondTip)
    (hfirstArmApex : firstArm ≠ apexLabel) (hfirstTipSecondArm : firstTip ≠ secondArm)
    (hfirstTipSecondTip : firstTip ≠ secondTip) (hfirstTipApex : firstTip ≠ apexLabel)
    (hsecondArmTip : secondArm ≠ secondTip) (hsecondArmApex : secondArm ≠ apexLabel)
    (hsecondTipApex : secondTip ≠ apexLabel)
    (hlineFirst : pattern meetLabel firstArm firstTip)
    (hlineSecond : pattern meetLabel secondArm secondTip)
    (honly : ∀ leftLabel midLabel rightLabel : Fin 6, leftLabel ≠ midLabel →
      leftLabel ≠ rightLabel → midLabel ≠ rightLabel → pattern leftLabel midLabel rightLabel →
        ((leftLabel = meetLabel ∨ leftLabel = firstArm ∨ leftLabel = firstTip) ∧
          (midLabel = meetLabel ∨ midLabel = firstArm ∨ midLabel = firstTip) ∧
          (rightLabel = meetLabel ∨ rightLabel = firstArm ∨ rightLabel = firstTip)) ∨
        ((leftLabel = meetLabel ∨ leftLabel = secondArm ∨ leftLabel = secondTip) ∧
          (midLabel = meetLabel ∨ midLabel = secondArm ∨ midLabel = secondTip) ∧
          (rightLabel = meetLabel ∨ rightLabel = secondArm ∨ rightLabel = secondTip))) :
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  have hinjective := injective_sixLabelMap_of_pairwise (slotZero := meetLabel)
    (slotOne := firstArm) (slotTwo := firstTip) (slotThree := secondArm)
    (slotFour := secondTip) (slotFive := apexLabel) hmeetFirstArm hmeetFirstTip hmeetSecondArm
    hmeetSecondTip hmeetApex hfirstArmTip hfirstArmSecondArm hfirstArmSecondTip hfirstArmApex
    hfirstTipSecondArm hfirstTipSecondTip hfirstTipApex hsecondArmTip hsecondArmApex
    hsecondTipApex
  obtain ⟨relabel, hrelabel⟩ := exists_relabel_agreesOnDistinctTriples_of_labelledFamily
    (pattern := pattern) hinjective [[0, 1, 2], [0, 3, 4]] (by
      have hmapped : ([[(0 : Fin 6), 1, 2], [0, 3, 4]].map (List.map (sixLabelMap meetLabel
          firstArm firstTip secondArm secondTip apexLabel)))
            = [[meetLabel, firstArm, firstTip], [meetLabel, secondArm, secondTip]] := rfl
      rw [hmapped]
      refine agreesOnDistinctTriples_lineFamilyPattern_of_sound_complete (pattern := pattern)
        [[meetLabel, firstArm, firstTip], [meetLabel, secondArm, secondTip]] ?_ ?_
      · intro line hline
        have hlineEq : line = [meetLabel, firstArm, firstTip] ∨
            line = [meetLabel, secondArm, secondTip] := by simpa using hline
        rcases hlineEq with rfl | rfl
        · exact forall_mem_threePointLine_pattern haxioms meetLabel firstArm firstTip hlineFirst
        · exact forall_mem_threePointLine_pattern haxioms meetLabel secondArm secondTip
            hlineSecond
      · intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
        rcases honly leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern with
          ⟨hleft, hmid, hright⟩ | ⟨hleft, hmid, hright⟩
        · exact ⟨[meetLabel, firstArm, firstTip], by simp, by simpa using hleft,
            by simpa using hmid, by simpa using hright⟩
        · exact ⟨[meetLabel, secondArm, secondTip], by simp, by simpa using hleft,
            by simpa using hmid, by simpa using hright⟩)
  exact ⟨lineFamilyPattern [[0, 1, 2], [0, 3, 4]],
    List.mem_map.mpr ⟨[[0, 1, 2], [0, 3, 4]], by decide, rfl⟩, relabel, hrelabel⟩

/-- **Catalogue `#4`, closed.**  Three three-point lines pairwise meeting in three
distinct points — the triangle — with nothing else dependent. -/
theorem linearSpaceListIsComplete_six_triangleCase {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (meetLabel firstArm firstTip secondArm secondTip apexLabel : Fin 6)
    (hmeetFirstArm : meetLabel ≠ firstArm) (hmeetFirstTip : meetLabel ≠ firstTip)
    (hmeetSecondArm : meetLabel ≠ secondArm) (hmeetSecondTip : meetLabel ≠ secondTip)
    (hmeetApex : meetLabel ≠ apexLabel) (hfirstArmTip : firstArm ≠ firstTip)
    (hfirstArmSecondArm : firstArm ≠ secondArm) (hfirstArmSecondTip : firstArm ≠ secondTip)
    (hfirstArmApex : firstArm ≠ apexLabel) (hfirstTipSecondArm : firstTip ≠ secondArm)
    (hfirstTipSecondTip : firstTip ≠ secondTip) (hfirstTipApex : firstTip ≠ apexLabel)
    (hsecondArmTip : secondArm ≠ secondTip) (hsecondArmApex : secondArm ≠ apexLabel)
    (hsecondTipApex : secondTip ≠ apexLabel)
    (hlineFirst : pattern meetLabel firstArm firstTip)
    (hlineSecond : pattern meetLabel secondArm secondTip)
    (hlineThird : pattern firstArm secondArm apexLabel)
    (honly : ∀ leftLabel midLabel rightLabel : Fin 6, leftLabel ≠ midLabel →
      leftLabel ≠ rightLabel → midLabel ≠ rightLabel → pattern leftLabel midLabel rightLabel →
        ((leftLabel = meetLabel ∨ leftLabel = firstArm ∨ leftLabel = firstTip) ∧
          (midLabel = meetLabel ∨ midLabel = firstArm ∨ midLabel = firstTip) ∧
          (rightLabel = meetLabel ∨ rightLabel = firstArm ∨ rightLabel = firstTip)) ∨
        ((leftLabel = meetLabel ∨ leftLabel = secondArm ∨ leftLabel = secondTip) ∧
          (midLabel = meetLabel ∨ midLabel = secondArm ∨ midLabel = secondTip) ∧
          (rightLabel = meetLabel ∨ rightLabel = secondArm ∨ rightLabel = secondTip)) ∨
        ((leftLabel = firstArm ∨ leftLabel = secondArm ∨ leftLabel = apexLabel) ∧
          (midLabel = firstArm ∨ midLabel = secondArm ∨ midLabel = apexLabel) ∧
          (rightLabel = firstArm ∨ rightLabel = secondArm ∨ rightLabel = apexLabel))) :
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  have hinjective := injective_sixLabelMap_of_pairwise (slotZero := meetLabel)
    (slotOne := firstArm) (slotTwo := firstTip) (slotThree := secondArm)
    (slotFour := secondTip) (slotFive := apexLabel) hmeetFirstArm hmeetFirstTip hmeetSecondArm
    hmeetSecondTip hmeetApex hfirstArmTip hfirstArmSecondArm hfirstArmSecondTip hfirstArmApex
    hfirstTipSecondArm hfirstTipSecondTip hfirstTipApex hsecondArmTip hsecondArmApex
    hsecondTipApex
  obtain ⟨relabel, hrelabel⟩ := exists_relabel_agreesOnDistinctTriples_of_labelledFamily
    (pattern := pattern) hinjective [[0, 1, 2], [0, 3, 4], [1, 3, 5]] (by
      have hmapped : ([[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5]].map (List.map
          (sixLabelMap meetLabel firstArm firstTip secondArm secondTip apexLabel)))
            = [[meetLabel, firstArm, firstTip], [meetLabel, secondArm, secondTip],
              [firstArm, secondArm, apexLabel]] := rfl
      rw [hmapped]
      refine agreesOnDistinctTriples_lineFamilyPattern_of_sound_complete (pattern := pattern)
        [[meetLabel, firstArm, firstTip], [meetLabel, secondArm, secondTip],
          [firstArm, secondArm, apexLabel]] ?_ ?_
      · intro line hline
        have hlineEq : line = [meetLabel, firstArm, firstTip] ∨
            line = [meetLabel, secondArm, secondTip] ∨
            line = [firstArm, secondArm, apexLabel] := by simpa using hline
        rcases hlineEq with rfl | rfl | rfl
        · exact forall_mem_threePointLine_pattern haxioms meetLabel firstArm firstTip hlineFirst
        · exact forall_mem_threePointLine_pattern haxioms meetLabel secondArm secondTip
            hlineSecond
        · exact forall_mem_threePointLine_pattern haxioms firstArm secondArm apexLabel
            hlineThird
      · intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
        rcases honly leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern with
          ⟨hleft, hmid, hright⟩ | ⟨hleft, hmid, hright⟩ | ⟨hleft, hmid, hright⟩
        · exact ⟨[meetLabel, firstArm, firstTip], by simp, by simpa using hleft,
            by simpa using hmid, by simpa using hright⟩
        · exact ⟨[meetLabel, secondArm, secondTip], by simp, by simpa using hleft,
            by simpa using hmid, by simpa using hright⟩
        · exact ⟨[firstArm, secondArm, apexLabel], by simp, by simpa using hleft,
            by simpa using hmid, by simpa using hright⟩)
  exact ⟨lineFamilyPattern [[0, 1, 2], [0, 3, 4], [1, 3, 5]],
    List.mem_map.mpr ⟨[[0, 1, 2], [0, 3, 4], [1, 3, 5]], by decide, rfl⟩, relabel, hrelabel⟩


/-- **Catalogue `#5`, closed.**  The graphic matroid `M(K4)`: four three-point
lines on six labels, every label on exactly two of them.  Completeness is PROVED
here rather than assumed — a fifth line would have to run through `apexLabel` and
share two labels with the third or the fourth. -/
theorem linearSpaceListIsComplete_six_graphicKFourCase {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern) (hnoFour : HasNoFourPointLine pattern)
    (meetLabel firstArm firstTip secondArm secondTip apexLabel : Fin 6)
    (hmeetFirstArm : meetLabel ≠ firstArm) (hmeetFirstTip : meetLabel ≠ firstTip)
    (hmeetSecondArm : meetLabel ≠ secondArm) (hmeetSecondTip : meetLabel ≠ secondTip)
    (hmeetApex : meetLabel ≠ apexLabel) (hfirstArmTip : firstArm ≠ firstTip)
    (hfirstArmSecondArm : firstArm ≠ secondArm) (hfirstArmSecondTip : firstArm ≠ secondTip)
    (hfirstArmApex : firstArm ≠ apexLabel) (hfirstTipSecondArm : firstTip ≠ secondArm)
    (hfirstTipSecondTip : firstTip ≠ secondTip) (hfirstTipApex : firstTip ≠ apexLabel)
    (hsecondArmTip : secondArm ≠ secondTip) (hsecondArmApex : secondArm ≠ apexLabel)
    (hsecondTipApex : secondTip ≠ apexLabel)
    (hlineFirst : pattern meetLabel firstArm firstTip)
    (hlineSecond : pattern meetLabel secondArm secondTip)
    (hlineThird : pattern firstArm secondArm apexLabel)
    (hlineFourth : pattern firstTip secondTip apexLabel) :
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  classical
  have hinjective := injective_sixLabelMap_of_pairwise (slotZero := meetLabel)
    (slotOne := firstArm) (slotTwo := firstTip) (slotThree := secondArm)
    (slotFour := secondTip) (slotFive := apexLabel) hmeetFirstArm hmeetFirstTip hmeetSecondArm
    hmeetSecondTip hmeetApex hfirstArmTip hfirstArmSecondArm hfirstArmSecondTip hfirstArmApex
    hfirstTipSecondArm hfirstTipSecondTip hfirstTipApex hsecondArmTip hsecondArmApex
    hsecondTipApex
  have hclosedThird : ∀ leftOne midOne rightOne : Fin 6, leftOne ≠ midOne → leftOne ≠ rightOne →
      midOne ≠ rightOne → (leftOne = firstArm ∨ leftOne = secondArm ∨ leftOne = apexLabel) →
      (midOne = firstArm ∨ midOne = secondArm ∨ midOne = apexLabel) →
      pattern leftOne midOne rightOne →
        (rightOne = firstArm ∨ rightOne = secondArm ∨ rightOne = apexLabel) :=
    fun leftOne midOne rightOne hone htwo hthree hleft hmid hpat =>
      mem_threePointLine_of_two_mem haxioms hnoFour firstArm secondArm apexLabel
        hfirstArmSecondArm hfirstArmApex hsecondArmApex hlineThird leftOne midOne rightOne hone
        htwo hthree hleft hmid hpat
  obtain ⟨relabel, hrelabel⟩ := exists_relabel_agreesOnDistinctTriples_of_labelledFamily
    (pattern := pattern) hinjective [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]] (by
      have hmapped : ([[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]].map (List.map
          (sixLabelMap meetLabel firstArm firstTip secondArm secondTip apexLabel)))
            = [[meetLabel, firstArm, firstTip], [meetLabel, secondArm, secondTip],
              [firstArm, secondArm, apexLabel], [firstTip, secondTip, apexLabel]] := rfl
      rw [hmapped]
      refine agreesOnDistinctTriples_lineFamilyPattern_of_sound_complete (pattern := pattern)
        [[meetLabel, firstArm, firstTip], [meetLabel, secondArm, secondTip],
          [firstArm, secondArm, apexLabel], [firstTip, secondTip, apexLabel]] ?_ ?_
      · intro line hline
        have hlineEq : line = [meetLabel, firstArm, firstTip] ∨
            line = [meetLabel, secondArm, secondTip] ∨
            line = [firstArm, secondArm, apexLabel] ∨
            line = [firstTip, secondTip, apexLabel] := by simpa using hline
        rcases hlineEq with rfl | rfl | rfl | rfl
        · exact forall_mem_threePointLine_pattern haxioms meetLabel firstArm firstTip hlineFirst
        · exact forall_mem_threePointLine_pattern haxioms meetLabel secondArm secondTip
            hlineSecond
        · exact forall_mem_threePointLine_pattern haxioms firstArm secondArm apexLabel
            hlineThird
        · exact forall_mem_threePointLine_pattern haxioms firstTip secondTip apexLabel
            hlineFourth
      · intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
        by_cases hfirst : (leftLabel = meetLabel ∨ leftLabel = firstArm ∨
              leftLabel = firstTip) ∧
            (midLabel = meetLabel ∨ midLabel = firstArm ∨ midLabel = firstTip) ∧
            (rightLabel = meetLabel ∨ rightLabel = firstArm ∨ rightLabel = firstTip)
        · exact ⟨[meetLabel, firstArm, firstTip], by simp, by simpa using hfirst.1,
            by simpa using hfirst.2.1, by simpa using hfirst.2.2⟩
        · by_cases hsecond : (leftLabel = meetLabel ∨ leftLabel = secondArm ∨
                leftLabel = secondTip) ∧
              (midLabel = meetLabel ∨ midLabel = secondArm ∨ midLabel = secondTip) ∧
              (rightLabel = meetLabel ∨ rightLabel = secondArm ∨ rightLabel = secondTip)
          · exact ⟨[meetLabel, secondArm, secondTip], by simp, by simpa using hsecond.1,
              by simpa using hsecond.2.1, by simpa using hsecond.2.2⟩
          · obtain ⟨armLabel, oppositeLabel, harmMem, hoppositeMem, hshapePattern, hleft, hmid,
              hright⟩ := exists_thirdLineShape haxioms hnoFour meetLabel firstArm firstTip
                secondArm secondTip apexLabel hmeetFirstArm hmeetFirstTip hmeetSecondArm
                hmeetSecondTip hmeetApex hfirstArmTip hfirstArmSecondArm hfirstArmSecondTip
                hfirstArmApex hfirstTipSecondArm hfirstTipSecondTip hfirstTipApex hsecondArmTip
                hsecondArmApex hsecondTipApex hlineFirst hlineSecond leftLabel midLabel
                rightLabel hleftMid hleftRight hmidRight hpattern hfirst hsecond
            rcases harmMem with rfl | rfl
            · rcases hoppositeMem with rfl | rfl
              · exact ⟨[armLabel, oppositeLabel, apexLabel], by simp, by simpa using hleft,
                  by simpa using hmid, by simpa using hright⟩
              · exfalso
                have hpushed := hclosedThird armLabel apexLabel oppositeLabel hfirstArmApex
                  hfirstArmSecondTip (Ne.symm hsecondTipApex) (Or.inl rfl)
                  (Or.inr (Or.inr rfl)) (haxioms.isRightSwapClosed _ _ _ hshapePattern)
                rcases hpushed with heq | heq | heq
                exacts [hfirstArmSecondTip heq.symm, hsecondArmTip heq.symm, hsecondTipApex heq]
            · rcases hoppositeMem with rfl | rfl
              · exfalso
                have hpushed := hclosedThird oppositeLabel apexLabel armLabel hsecondArmApex
                  (Ne.symm hfirstTipSecondArm) (Ne.symm hfirstTipApex) (Or.inr (Or.inl rfl))
                  (Or.inr (Or.inr rfl)) (haxioms.isRightSwapClosed _ _ _
                    (haxioms.isLeftSwapClosed _ _ _ hshapePattern))
                rcases hpushed with heq | heq | heq
                exacts [hfirstArmTip heq.symm, hfirstTipSecondArm heq, hfirstTipApex heq]
              · exact ⟨[armLabel, oppositeLabel, apexLabel], by simp, by simpa using hleft,
                  by simpa using hmid, by simpa using hright⟩)
  exact ⟨lineFamilyPattern [[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]],
    List.mem_map.mpr ⟨[[0, 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]], by decide, rfl⟩, relabel,
    hrelabel⟩

/-- **Three lines or four.**  Given two meeting three-point lines and a third
through the label off both, the pattern is the triangle or, if it carries one more
dependent triple, `M(K4)`; there is no room for a fifth line. -/
theorem linearSpaceListIsComplete_six_triangleOrGraphicCase {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern) (hnoFour : HasNoFourPointLine pattern)
    (meetLabel firstArm firstTip secondArm secondTip apexLabel : Fin 6)
    (hmeetFirstArm : meetLabel ≠ firstArm) (hmeetFirstTip : meetLabel ≠ firstTip)
    (hmeetSecondArm : meetLabel ≠ secondArm) (hmeetSecondTip : meetLabel ≠ secondTip)
    (hmeetApex : meetLabel ≠ apexLabel) (hfirstArmTip : firstArm ≠ firstTip)
    (hfirstArmSecondArm : firstArm ≠ secondArm) (hfirstArmSecondTip : firstArm ≠ secondTip)
    (hfirstArmApex : firstArm ≠ apexLabel) (hfirstTipSecondArm : firstTip ≠ secondArm)
    (hfirstTipSecondTip : firstTip ≠ secondTip) (hfirstTipApex : firstTip ≠ apexLabel)
    (hsecondArmTip : secondArm ≠ secondTip) (hsecondArmApex : secondArm ≠ apexLabel)
    (hsecondTipApex : secondTip ≠ apexLabel)
    (hlineFirst : pattern meetLabel firstArm firstTip)
    (hlineSecond : pattern meetLabel secondArm secondTip)
    (hlineThird : pattern firstArm secondArm apexLabel) :
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  classical
  by_cases hfourthLine : ∃ extraLeft extraMid extraRight : Fin 6, extraLeft ≠ extraMid ∧
      extraLeft ≠ extraRight ∧ extraMid ≠ extraRight ∧ pattern extraLeft extraMid extraRight ∧
      ¬ ((extraLeft = meetLabel ∨ extraLeft = firstArm ∨ extraLeft = firstTip) ∧
          (extraMid = meetLabel ∨ extraMid = firstArm ∨ extraMid = firstTip) ∧
          (extraRight = meetLabel ∨ extraRight = firstArm ∨ extraRight = firstTip)) ∧
      ¬ ((extraLeft = meetLabel ∨ extraLeft = secondArm ∨ extraLeft = secondTip) ∧
          (extraMid = meetLabel ∨ extraMid = secondArm ∨ extraMid = secondTip) ∧
          (extraRight = meetLabel ∨ extraRight = secondArm ∨ extraRight = secondTip)) ∧
      ¬ ((extraLeft = firstArm ∨ extraLeft = secondArm ∨ extraLeft = apexLabel) ∧
          (extraMid = firstArm ∨ extraMid = secondArm ∨ extraMid = apexLabel) ∧
          (extraRight = firstArm ∨ extraRight = secondArm ∨ extraRight = apexLabel))
  · obtain ⟨extraLeft, extraMid, extraRight, hextraLeftMid, hextraLeftRight, hextraMidRight,
      hextraPattern, hnotFirst, hnotSecond, hnotThird⟩ := hfourthLine
    have hclosedThird : ∀ leftOne midOne rightOne : Fin 6, leftOne ≠ midOne →
        leftOne ≠ rightOne → midOne ≠ rightOne →
        (leftOne = firstArm ∨ leftOne = secondArm ∨ leftOne = apexLabel) →
        (midOne = firstArm ∨ midOne = secondArm ∨ midOne = apexLabel) →
        pattern leftOne midOne rightOne →
          (rightOne = firstArm ∨ rightOne = secondArm ∨ rightOne = apexLabel) :=
      fun leftOne midOne rightOne hone htwo hthree hleft hmid hpat =>
        mem_threePointLine_of_two_mem haxioms hnoFour firstArm secondArm apexLabel
          hfirstArmSecondArm hfirstArmApex hsecondArmApex hlineThird leftOne midOne rightOne
          hone htwo hthree hleft hmid hpat
    obtain ⟨armLabel, oppositeLabel, harmMem, hoppositeMem, hshapePattern, hleft, hmid,
      hright⟩ := exists_thirdLineShape haxioms hnoFour meetLabel firstArm firstTip secondArm
        secondTip apexLabel hmeetFirstArm hmeetFirstTip hmeetSecondArm hmeetSecondTip hmeetApex
        hfirstArmTip hfirstArmSecondArm hfirstArmSecondTip hfirstArmApex hfirstTipSecondArm
        hfirstTipSecondTip hfirstTipApex hsecondArmTip hsecondArmApex hsecondTipApex hlineFirst
        hlineSecond extraLeft extraMid extraRight hextraLeftMid hextraLeftRight hextraMidRight
        hextraPattern hnotFirst hnotSecond
    have hlineFourth : pattern firstTip secondTip apexLabel := by
      rcases harmMem with rfl | rfl
      · rcases hoppositeMem with rfl | rfl
        · exact absurd ⟨hleft, hmid, hright⟩ hnotThird
        · exfalso
          have hpushed := hclosedThird armLabel apexLabel oppositeLabel hfirstArmApex
            hfirstArmSecondTip (Ne.symm hsecondTipApex) (Or.inl rfl) (Or.inr (Or.inr rfl))
            (haxioms.isRightSwapClosed _ _ _ hshapePattern)
          rcases hpushed with heq | heq | heq
          exacts [hfirstArmSecondTip heq.symm, hsecondArmTip heq.symm, hsecondTipApex heq]
      · rcases hoppositeMem with rfl | rfl
        · exfalso
          have hpushed := hclosedThird oppositeLabel apexLabel armLabel hsecondArmApex
            (Ne.symm hfirstTipSecondArm) (Ne.symm hfirstTipApex) (Or.inr (Or.inl rfl))
            (Or.inr (Or.inr rfl)) (haxioms.isRightSwapClosed _ _ _
              (haxioms.isLeftSwapClosed _ _ _ hshapePattern))
          rcases hpushed with heq | heq | heq
          exacts [hfirstArmTip heq.symm, hfirstTipSecondArm heq, hfirstTipApex heq]
        · exact hshapePattern
    exact linearSpaceListIsComplete_six_graphicKFourCase haxioms hnoFour meetLabel firstArm
      firstTip secondArm secondTip apexLabel hmeetFirstArm hmeetFirstTip hmeetSecondArm
      hmeetSecondTip hmeetApex hfirstArmTip hfirstArmSecondArm hfirstArmSecondTip hfirstArmApex
      hfirstTipSecondArm hfirstTipSecondTip hfirstTipApex hsecondArmTip hsecondArmApex
      hsecondTipApex hlineFirst hlineSecond hlineThird hlineFourth
  · refine linearSpaceListIsComplete_six_triangleCase haxioms meetLabel firstArm firstTip
      secondArm secondTip apexLabel hmeetFirstArm hmeetFirstTip hmeetSecondArm hmeetSecondTip
      hmeetApex hfirstArmTip hfirstArmSecondArm hfirstArmSecondTip hfirstArmApex
      hfirstTipSecondArm hfirstTipSecondTip hfirstTipApex hsecondArmTip hsecondArmApex
      hsecondTipApex hlineFirst hlineSecond hlineThird ?_
    intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
    by_contra hnone
    simp only [not_or] at hnone
    exact hfourthLine ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight,
      hpattern, hnone.1, hnone.2.1, hnone.2.2⟩



/-! ## The assembly

The four three-point classes are peeled by counting lines: the second line either
misses the first entirely — and then no third line fits — or meets it in one
point, after which every further line runs through the label off both. -/

/-- **Catalogue `#2` through `#5`, discharged.**  The pole clause of
`Gtz.LinearSpaceThreePointLineCasesSix` is not used: with no four-point line there
is no five-point line either, so no pattern in range is a near pencil. -/
theorem linearSpaceThreePointLineCasesSix_holds : LinearSpaceThreePointLineCasesSix := by
  classical
  intro pattern haxioms hnoFourRaw seedLeft seedMid seedRight hseedLeftMid hseedLeftRight
    hseedMidRight hseed hextra _hnoPole
  have hnoFour : HasNoFourPointLine pattern := hnoFourRaw
  obtain ⟨extraLeft, extraMid, extraRight, hextraLeftMid, hextraLeftRight, hextraMidRight,
    hextraPattern, hextraOutside⟩ := hextra
  have hseedClosed : ∀ leftOne midOne rightOne : Fin 6, leftOne ≠ midOne → leftOne ≠ rightOne →
      midOne ≠ rightOne → (leftOne = seedLeft ∨ leftOne = seedMid ∨ leftOne = seedRight) →
      (midOne = seedLeft ∨ midOne = seedMid ∨ midOne = seedRight) →
      pattern leftOne midOne rightOne →
        (rightOne = seedLeft ∨ rightOne = seedMid ∨ rightOne = seedRight) :=
    fun leftOne midOne rightOne hone htwo hthree hleft hmid hpat =>
      mem_threePointLine_of_two_mem haxioms hnoFour seedLeft seedMid seedRight hseedLeftMid
        hseedLeftRight hseedMidRight hseed leftOne midOne rightOne hone htwo hthree hleft hmid
        hpat
  have hseedSound := forall_mem_threePointLine_pattern haxioms seedLeft seedMid seedRight hseed
  rcases exists_meetLabel_or_allOutside haxioms
      (fun label => label = seedLeft ∨ label = seedMid ∨ label = seedRight) hseedClosed
      extraLeft extraMid extraRight hextraLeftMid hextraLeftRight hextraMidRight hextraPattern
      hextraOutside with
    ⟨meetLabel, outFirst, outSecond, hmeetRaw, houtFirstRaw, houtSecondRaw, houtDistinct,
      hsecondLine, -, -, -⟩ | ⟨hleftRaw, hmidRaw, hrightRaw⟩
  · have hmeetMem : meetLabel = seedLeft ∨ meetLabel = seedMid ∨ meetLabel = seedRight := hmeetRaw
    have houtFirstNot : ¬ (outFirst = seedLeft ∨ outFirst = seedMid ∨ outFirst = seedRight) :=
      houtFirstRaw
    have houtSecondNot : ¬ (outSecond = seedLeft ∨ outSecond = seedMid ∨
      outSecond = seedRight) := houtSecondRaw
    simp only [not_or] at houtFirstNot houtSecondNot
    obtain ⟨houtFirstSeedLeft, houtFirstSeedMid, houtFirstSeedRight⟩ := houtFirstNot
    obtain ⟨houtSecondSeedLeft, houtSecondSeedMid, houtSecondSeedRight⟩ := houtSecondNot
    obtain ⟨apexLabel, hapexSeedLeft, hapexSeedMid, hapexSeedRight, hapexOutFirst,
      hapexOutSecond⟩ := exists_sixthLabel seedLeft seedMid seedRight outFirst outSecond
        hseedLeftMid hseedLeftRight (Ne.symm houtFirstSeedLeft) (Ne.symm houtSecondSeedLeft)
        hseedMidRight (Ne.symm houtFirstSeedMid) (Ne.symm houtSecondSeedMid)
        (Ne.symm houtFirstSeedRight) (Ne.symm houtSecondSeedRight) houtDistinct
    have hcover := forall_eq_of_sixDistinctLabels seedLeft seedMid seedRight outFirst outSecond
      apexLabel hseedLeftMid hseedLeftRight (Ne.symm houtFirstSeedLeft)
      (Ne.symm houtSecondSeedLeft) (Ne.symm hapexSeedLeft) hseedMidRight
      (Ne.symm houtFirstSeedMid) (Ne.symm houtSecondSeedMid) (Ne.symm hapexSeedMid)
      (Ne.symm houtFirstSeedRight) (Ne.symm houtSecondSeedRight) (Ne.symm hapexSeedRight)
      houtDistinct (Ne.symm hapexOutFirst) (Ne.symm hapexOutSecond)
    have hmeetOutFirst : meetLabel ≠ outFirst := by
      rcases hmeetMem with rfl | rfl | rfl <;>
        first
          | exact Ne.symm houtFirstSeedLeft | exact Ne.symm houtFirstSeedMid
          | exact Ne.symm houtFirstSeedRight
    have hmeetOutSecond : meetLabel ≠ outSecond := by
      rcases hmeetMem with rfl | rfl | rfl <;>
        first
          | exact Ne.symm houtSecondSeedLeft | exact Ne.symm houtSecondSeedMid
          | exact Ne.symm houtSecondSeedRight
    have hmeetApex : meetLabel ≠ apexLabel := by
      rcases hmeetMem with rfl | rfl | rfl <;>
        first
          | exact Ne.symm hapexSeedLeft | exact Ne.symm hapexSeedMid
          | exact Ne.symm hapexSeedRight
    obtain ⟨firstArm, firstTip, harmTip, hpairAvoids⟩ := exists_offFourPointLine_pair meetLabel
      outFirst outSecond apexLabel hmeetOutFirst hmeetOutSecond hmeetApex houtDistinct
      (Ne.symm hapexOutFirst) (Ne.symm hapexOutSecond)
    obtain ⟨harmMeet, harmOutFirst, harmOutSecond, harmApex⟩ := hpairAvoids firstArm (Or.inl rfl)
    obtain ⟨htipMeet, htipOutFirst, htipOutSecond, htipApex⟩ := hpairAvoids firstTip (Or.inr rfl)
    have hinSeed : ∀ label : Fin 6, label ≠ outFirst → label ≠ outSecond → label ≠ apexLabel →
        (label = seedLeft ∨ label = seedMid ∨ label = seedRight) := by
      intro label hone htwo hthree
      rcases hcover label with rfl | rfl | rfl | rfl | rfl | rfl <;>
        first
          | (exact absurd rfl hone) | (exact absurd rfl htwo) | (exact absurd rfl hthree) | simp
    have hmemSeedList : ∀ label : Fin 6,
        (label = seedLeft ∨ label = seedMid ∨ label = seedRight) →
          label ∈ [seedLeft, seedMid, seedRight] := by
      intro label hlabel; simpa using hlabel
    have hlineFirst : pattern meetLabel firstArm firstTip :=
      hseedSound meetLabel (hmemSeedList _ hmeetMem) firstArm
        (hmemSeedList _ (hinSeed firstArm harmOutFirst harmOutSecond harmApex)) firstTip
        (hmemSeedList _ (hinSeed firstTip htipOutFirst htipOutSecond htipApex))
        (Ne.symm harmMeet) (Ne.symm htipMeet) harmTip
    have hmeetArm : meetLabel ≠ firstArm := Ne.symm harmMeet
    have hmeetTip : meetLabel ≠ firstTip := Ne.symm htipMeet
    have harmMeetSym : firstArm ≠ meetLabel := harmMeet
    have htipMeetSym : firstTip ≠ meetLabel := htipMeet
    have harmOutFirstSym : outFirst ≠ firstArm := Ne.symm harmOutFirst
    have harmOutSecondSym : outSecond ≠ firstArm := Ne.symm harmOutSecond
    have harmApexSym : apexLabel ≠ firstArm := Ne.symm harmApex
    have htipOutFirstSym : outFirst ≠ firstTip := Ne.symm htipOutFirst
    have htipOutSecondSym : outSecond ≠ firstTip := Ne.symm htipOutSecond
    have htipApexSym : apexLabel ≠ firstTip := Ne.symm htipApex
    have htipArm : firstTip ≠ firstArm := Ne.symm harmTip
    have houtSecondFirst : outSecond ≠ outFirst := Ne.symm houtDistinct
    have hapexOutFirstSym : outFirst ≠ apexLabel := Ne.symm hapexOutFirst
    have hapexOutSecondSym : outSecond ≠ apexLabel := Ne.symm hapexOutSecond
    have hmeetOutFirstSym : outFirst ≠ meetLabel := Ne.symm hmeetOutFirst
    have hmeetOutSecondSym : outSecond ≠ meetLabel := Ne.symm hmeetOutSecond
    have hmeetApexSym : apexLabel ≠ meetLabel := Ne.symm hmeetApex
    by_cases hthirdLine : ∃ thirdLeft thirdMid thirdRight : Fin 6, thirdLeft ≠ thirdMid ∧
        thirdLeft ≠ thirdRight ∧ thirdMid ≠ thirdRight ∧ pattern thirdLeft thirdMid thirdRight ∧
        ¬ ((thirdLeft = meetLabel ∨ thirdLeft = firstArm ∨ thirdLeft = firstTip) ∧
            (thirdMid = meetLabel ∨ thirdMid = firstArm ∨ thirdMid = firstTip) ∧
            (thirdRight = meetLabel ∨ thirdRight = firstArm ∨ thirdRight = firstTip)) ∧
        ¬ ((thirdLeft = meetLabel ∨ thirdLeft = outFirst ∨ thirdLeft = outSecond) ∧
            (thirdMid = meetLabel ∨ thirdMid = outFirst ∨ thirdMid = outSecond) ∧
            (thirdRight = meetLabel ∨ thirdRight = outFirst ∨ thirdRight = outSecond))
    · obtain ⟨thirdLeft, thirdMid, thirdRight, hthirdLeftMid, hthirdLeftRight, hthirdMidRight,
        hthirdPattern, hnotFirst, hnotSecond⟩ := hthirdLine
      obtain ⟨armLabel, oppositeLabel, harmMem, hoppositeMem, hshapePattern, -, -, -⟩ :=
        exists_thirdLineShape haxioms hnoFour meetLabel firstArm firstTip outFirst outSecond
          apexLabel hmeetArm hmeetTip hmeetOutFirst hmeetOutSecond hmeetApex harmTip
          harmOutFirst harmOutSecond harmApex htipOutFirst htipOutSecond htipApex houtDistinct
          hapexOutFirstSym hapexOutSecondSym hlineFirst hsecondLine thirdLeft thirdMid
          thirdRight hthirdLeftMid hthirdLeftRight hthirdMidRight hthirdPattern hnotFirst
          hnotSecond
      rcases harmMem with heq | heq <;> rcases hoppositeMem with heqTwo | heqTwo <;>
        rw [heq, heqTwo] at hshapePattern
      · exact linearSpaceListIsComplete_six_triangleOrGraphicCase haxioms hnoFour meetLabel
          firstArm firstTip outFirst outSecond apexLabel hmeetArm hmeetTip hmeetOutFirst
          hmeetOutSecond hmeetApex harmTip harmOutFirst harmOutSecond harmApex htipOutFirst
          htipOutSecond htipApex houtDistinct hapexOutFirstSym hapexOutSecondSym hlineFirst
          hsecondLine hshapePattern
      · exact linearSpaceListIsComplete_six_triangleOrGraphicCase haxioms hnoFour meetLabel
          firstArm firstTip outSecond outFirst apexLabel hmeetArm hmeetTip hmeetOutSecond
          hmeetOutFirst hmeetApex harmTip harmOutSecond harmOutFirst harmApex htipOutSecond
          htipOutFirst htipApex houtSecondFirst hapexOutSecondSym hapexOutFirstSym hlineFirst
          (haxioms.isRightSwapClosed _ _ _ hsecondLine) hshapePattern
      · exact linearSpaceListIsComplete_six_triangleOrGraphicCase haxioms hnoFour meetLabel
          firstTip firstArm outFirst outSecond apexLabel hmeetTip hmeetArm hmeetOutFirst
          hmeetOutSecond hmeetApex htipArm htipOutFirst htipOutSecond htipApex harmOutFirst
          harmOutSecond harmApex houtDistinct hapexOutFirstSym hapexOutSecondSym
          (haxioms.isRightSwapClosed _ _ _ hlineFirst) hsecondLine hshapePattern
      · exact linearSpaceListIsComplete_six_triangleOrGraphicCase haxioms hnoFour meetLabel
          firstTip firstArm outSecond outFirst apexLabel hmeetTip hmeetArm hmeetOutSecond
          hmeetOutFirst hmeetApex htipArm htipOutSecond htipOutFirst htipApex harmOutSecond
          harmOutFirst harmApex houtSecondFirst hapexOutSecondSym hapexOutFirstSym
          (haxioms.isRightSwapClosed _ _ _ hlineFirst)
          (haxioms.isRightSwapClosed _ _ _ hsecondLine) hshapePattern
    · refine linearSpaceListIsComplete_six_meetingLinesCase haxioms meetLabel firstArm firstTip
        outFirst outSecond apexLabel hmeetArm hmeetTip hmeetOutFirst hmeetOutSecond hmeetApex
        harmTip harmOutFirst harmOutSecond harmApex htipOutFirst htipOutSecond htipApex
        houtDistinct hapexOutFirstSym hapexOutSecondSym hlineFirst hsecondLine ?_
      intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
      by_contra hneither
      simp only [not_or] at hneither
      exact hthirdLine ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight,
        hpattern, hneither.1, hneither.2⟩
  · have hleftNot : ¬ (extraLeft = seedLeft ∨ extraLeft = seedMid ∨
      extraLeft = seedRight) := hleftRaw
    have hmidNot : ¬ (extraMid = seedLeft ∨ extraMid = seedMid ∨
      extraMid = seedRight) := hmidRaw
    have hrightNot : ¬ (extraRight = seedLeft ∨ extraRight = seedMid ∨
      extraRight = seedRight) := hrightRaw
    simp only [not_or] at hleftNot hmidNot hrightNot
    obtain ⟨hleftSeedLeft, hleftSeedMid, hleftSeedRight⟩ := hleftNot
    obtain ⟨hmidSeedLeft, hmidSeedMid, hmidSeedRight⟩ := hmidNot
    obtain ⟨hrightSeedLeft, hrightSeedMid, hrightSeedRight⟩ := hrightNot
    exact linearSpaceListIsComplete_six_disjointLinesCase haxioms hnoFour seedLeft seedMid
      seedRight extraLeft extraMid extraRight hseedLeftMid hseedLeftRight
      (Ne.symm hleftSeedLeft) (Ne.symm hmidSeedLeft) (Ne.symm hrightSeedLeft) hseedMidRight
      (Ne.symm hleftSeedMid) (Ne.symm hmidSeedMid) (Ne.symm hrightSeedMid)
      (Ne.symm hleftSeedRight) (Ne.symm hmidSeedRight) (Ne.symm hrightSeedRight)
      hextraLeftMid hextraLeftRight hextraMidRight hseed hextraPattern


/-! ## The six-point enumeration, unconditional

Both residuals of `Gtz.Design.LinePatternSixCases` are now theorems, so every
statement that file offers conditionally holds outright, and gap `7a` at six
labels is closed.  What remains between here and `Gtz.HingeHoldsAtSize 6 3` is
gap `7b` alone: the eight tie-freeness obligations, which this file does not
touch. -/

/-- **The six-point enumeration.**  Every spanning linear space on `Fin 6` is one
of the nine listed patterns after relabelling.  No hypotheses. -/
theorem linearSpaceListIsComplete_six : LinearSpaceListIsComplete 6 linePatternListSix :=
  linearSpaceListIsComplete_six_of_lineSizeCases linearSpaceThreePointLineCasesSix_holds
    linearSpaceFourPointLineCasesSix_holds

/-- The six-class cut, discharged. -/
theorem linearSpaceMultiLineCasesSix_holds : LinearSpaceMultiLineCasesSix :=
  fun pattern haxioms _ _ _ _ _ _ _ _ _ => linearSpaceListIsComplete_six pattern haxioms

/-- The seven-class cut, discharged. -/
theorem linearSpaceMiddleCasesSix_holds : LinearSpaceMiddleCasesSix :=
  fun pattern haxioms _ _ => linearSpaceListIsComplete_six pattern haxioms

/-- **The enumeration hypothesis at six labels, unconditional.**  This is the
combinatorial input of `Gtz.hingeHoldsAtSize_of_linearSpaceEnumeration_sixThree`,
and it is no longer an input. -/
theorem patternListIsCompleteUpToRelabel_six :
    PatternListIsCompleteUpToRelabel 6 linePatternListSix :=
  patternListIsCompleteUpToRelabel_of_linearSpaceListIsComplete (by omega) _
    linearSpaceListIsComplete_six

/-- **The hinge at six points from tie-freeness alone.**  The combinatorial half
of `Gtz.hingeHoldsAtSize_of_lineSizeCases_sixThree` is discharged; the eight
ledger entries are all that is left. -/
theorem hingeHoldsAtSize_sixThree_of_tieFreeResidual
    (hresidual : HingeStratumObligationSix) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_linearSpaceEnumeration_sixThree linearSpaceListIsComplete_six hresidual

/-- The same with each ledger entry narrowed by balanced stress. -/
theorem hingeHoldsAtSize_sixThree_of_balancedStressResidual
    (hresidual : ∀ lines ∈ lineFamiliesSix, ¬ IsNearPencilFamily lines →
      StratumIsTieFreeAmongHeavyAtBalancedStress (lineFamilyPattern lines)) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_multiLineCases_balancedStress_sixThree linearSpaceMultiLineCasesSix_holds
    hresidual

/-- The same with the unit-leverage split applied: sixteen obligations, each
narrowed by heaviness and by balanced stress, and nothing else. -/
theorem hingeHoldsAtSize_sixThree_of_splitBalancedStressResidual
    (hallHeavyFree : ∀ lines ∈ lineFamiliesSix, ¬ IsNearPencilFamily lines →
      StratumIsTieFreeAmongAllHeavyAtBalancedStress (lineFamilyPattern lines))
    (hunitFree : ∀ lines ∈ lineFamiliesSix, ¬ IsNearPencilFamily lines →
      StratumIsTieFreeAtUnitLeverageAtBalancedStress (lineFamilyPattern lines)) :
    HingeHoldsAtSize 6 3 :=
  hingeHoldsAtSize_of_multiLineCases_splitBalancedStress_sixThree
    linearSpaceMultiLineCasesSix_holds hallHeavyFree hunitFree

/-! ## Non-vacuity

`Gtz.linearSpaceListIsComplete_six` quantifies over spanning linear space
patterns, and the nine listed families are themselves such patterns, so the
statement has content: below it recognizes `M(K4)`, the class whose completeness
this file had to prove rather than assume. -/

example : ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
    AgreesOnDistinctTriples (lineFamilyPattern graphicKFourFamily)
      (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) :=
  linearSpaceListIsComplete_six (lineFamilyPattern graphicKFourFamily)
    (isSpanningLinearSpacePattern_lineFamilyPattern (by decide))

end Gtz
