/-
# The line pattern forces primitivity: a stratum hypothesis pays for its own
# non-degeneracy

Every on-path residual of the rank-three campaign carries a stratum hypothesis
of the form `Gtz.HasLinePattern design (Gtz.lineFamilyPattern lines)`.  Every
consolidated statement that could replace those residuals carries a
non-degeneracy hypothesis, because a design with two parallel atoms reads as
five projective points and the count of strict card-three selections collapses.
Until this file the two were separate: a wiring theorem had to assume
primitivity a second time, or carry it as an extra antecedent.

This file shows the stratum hypothesis **already contains** the non-degeneracy
one.  A design that realizes a line family has no parallel pair, for every one
of the five on-path line families, with nothing assumed.

## The argument, in one paragraph

Let `a` and `b` be parallel atoms.  For every third label `x` the bracket
`atomBracket design a b x` vanishes, because a determinant with two parallel
rows is zero (`Gtz.tripleBracket_eq_zero_of_parallel`).  `HasLinePattern` reads
each vanishing bracket at distinct labels as membership in a listed line, so
every one of the four remaining labels lies on a line through both `a` and `b`.
A three-point line through `a` and `b` supplies exactly one such label.  Two
distinct listed lines meet in at most one point in all five families, so at most
one of the four labels is covered.  Four labels, one slot: contradiction.

## PROVED here, kernel-checked, unconditional

* `Gtz.isPrimitiveDesign_of_hasLinePattern_lineFamily` — the bridge, generic in
  the size and in the line list.  Its combinatorial hypothesis is a statement
  about `List (List (Fin size))` alone, with no real number in it.
* `Gtz.not_hasParallelPair_of_hasLinePattern_lineFamily` — the same bridge in
  the `Gtz.HasParallelPair` phrasing.
* Five instantiations, one for each on-path stratum: the empty family, the one
  line, the two meeting lines, the three lines, and the K4 family.  Each
  discharges the combinatorial hypothesis by `decide`.

## The decidability boundary

The combinatorial hypothesis is decidable and the five instantiations close by
`decide`.  The bridge itself is not decidable and does not try to be.
`Gtz.HasLinePattern` relates a real determinant to a list membership, and
`Gtz.Dominates` is a `Matrix.PosSemidef` statement over the reals.  Neither
carries a decision procedure, and none can be written.  The split is exact: the
list arithmetic is `decide`, the bracket step is
`Gtz.tripleBracket_eq_zero_of_parallel`, and the step that joins them is the
real-arithmetic proof below.
-/
import Gtz.Design.LinePatternEnumeration
import Gtz.Design.StratumEmptinessLedger

namespace Gtz

open Finset

/-! ## The combinatorial half

The predicate below says the listed lines are too thin to carry a parallel
pair.  It mentions no real number and no design: it is a statement about a
`List (List (Fin size))`, and the five on-path families satisfy it by `decide`.
-/

/-- **A line list is pair-thin** when every pair of distinct labels misses at
least one third label, in the sense that no listed line holds all three.

A three-point line through a pair supplies exactly one third label.  At size six
a pair leaves four third labels.  So a family in which two distinct lines share
at most one point is pair-thin with room to spare. -/
def LineListIsPairThin {size : ℕ} (lines : List (List (Fin size))) : Prop :=
  ∀ keptLabel dropLabel : Fin size, keptLabel ≠ dropLabel →
    ∃ otherLabel : Fin size, otherLabel ≠ keptLabel ∧ otherLabel ≠ dropLabel ∧
      ¬ ∃ line ∈ lines, keptLabel ∈ line ∧ dropLabel ∈ line ∧ otherLabel ∈ line

instance decidableLineListIsPairThin {size : ℕ} (lines : List (List (Fin size))) :
    Decidable (LineListIsPairThin lines) := by
  unfold LineListIsPairThin
  infer_instance

/-! ## The bridge

Real arithmetic joins the combinatorial half to the design.  The parallel pair
makes a bracket vanish, the pattern reads the vanishing bracket as a line, and
pair-thinness has no line to offer.
-/

/-- **A design that realizes a pair-thin line family is primitive.**

The proof spends one landed lemma and one landed definition.
`tripleBracket_eq_zero_of_parallel` kills the bracket of a triple whose middle
atom is a multiple of its first.  `HasLinePattern` then reads that vanishing
bracket, at three distinct labels, as membership in a listed line.  Pair-thinness
produces a third label with no such line, and the two readings disagree. -/
theorem isPrimitiveDesign_of_hasLinePattern_lineFamily {size : ℕ}
    (design : WeightedDesign size 3) (lines : List (List (Fin size)))
    (hpattern : HasLinePattern design (lineFamilyPattern lines))
    (hthin : LineListIsPairThin lines) :
    IsPrimitiveDesign design := by
  intro keptLabel dropLabel ratio hdistinct hparallel
  obtain ⟨otherLabel, hotherKept, hotherDrop, hnoline⟩ := hthin keptLabel dropLabel hdistinct
  refine hnoline ?_
  have hvanish : atomBracket design keptLabel dropLabel otherLabel = 0 :=
    tripleBracket_eq_zero_of_parallel (design.atom keptLabel) (design.atom otherLabel)
      ratio hparallel
  exact (hpattern keptLabel dropLabel otherLabel hdistinct
    (Ne.symm hotherKept) (Ne.symm hotherDrop)).mp hvanish

/-- **The same bridge in the parallel-pair phrasing.**  `IsPrimitiveDesign` and
`¬ HasParallelPair` are the same statement with the negation pushed in, and
`isPrimitiveDesign_iff_not_hasParallelPair` is the dictionary. -/
theorem not_hasParallelPair_of_hasLinePattern_lineFamily {size : ℕ}
    (design : WeightedDesign size 3) (lines : List (List (Fin size)))
    (hpattern : HasLinePattern design (lineFamilyPattern lines))
    (hthin : LineListIsPairThin lines) :
    ¬ HasParallelPair design :=
  (isPrimitiveDesign_iff_not_hasParallelPair design).mp
    (isPrimitiveDesign_of_hasLinePattern_lineFamily design lines hpattern hthin)

/-! ## The five on-path strata

Each stratum supplies its line list and closes the combinatorial hypothesis by
`decide`.  The enumeration is thirty ordered pairs of distinct labels, each
scanning at most four lines of three labels: two orders of magnitude below the
kernel's working ceiling.
-/

/-- The empty family, the stratum of `A1`.  No line exists, so no pair has a
line at all. -/
theorem lineListIsPairThin_empty :
    LineListIsPairThin ([] : List (List (Fin 6))) := by decide

/-- The one line `{0,1,2}`, the stratum of the one-line survivor. -/
theorem lineListIsPairThin_oneLine :
    LineListIsPairThin [[(0 : Fin 6), 1, 2]] := by decide

/-- The two lines meeting at `0`, the stratum of the tenth-heavy residual. -/
theorem lineListIsPairThin_twoMeetingLines :
    LineListIsPairThin [[(0 : Fin 6), 1, 2], [0, 3, 4]] := by decide

/-- The three lines, the stratum of `A2`. -/
theorem lineListIsPairThin_threeLines :
    LineListIsPairThin [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5]] := by decide

/-- The four lines of the K4 family, the stratum of `A3`. -/
theorem lineListIsPairThin_kFour :
    LineListIsPairThin [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]] := by decide

/-! ## The five primitivity readings

Each theorem below says one stratum hypothesis pays for its own non-degeneracy.
A consolidated statement may therefore carry primitivity as an antecedent and
still be usable at every stratum, with no extra assumption anywhere.
-/

/-- The `A1` stratum forces primitivity. -/
theorem isPrimitiveDesign_of_emptyPattern (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern ([] : List (List (Fin 6))))) :
    IsPrimitiveDesign design :=
  isPrimitiveDesign_of_hasLinePattern_lineFamily design _ hpattern lineListIsPairThin_empty

/-- The one-line stratum forces primitivity. -/
theorem isPrimitiveDesign_of_oneLinePattern (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design (lineFamilyPattern [[(0 : Fin 6), 1, 2]])) :
    IsPrimitiveDesign design :=
  isPrimitiveDesign_of_hasLinePattern_lineFamily design _ hpattern lineListIsPairThin_oneLine

/-- The two-meeting-lines stratum forces primitivity. -/
theorem isPrimitiveDesign_of_twoMeetingLinesPattern (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4]])) :
    IsPrimitiveDesign design :=
  isPrimitiveDesign_of_hasLinePattern_lineFamily design _ hpattern
    lineListIsPairThin_twoMeetingLines

/-- The three-lines stratum forces primitivity. -/
theorem isPrimitiveDesign_of_threeLinesPattern (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5]])) :
    IsPrimitiveDesign design :=
  isPrimitiveDesign_of_hasLinePattern_lineFamily design _ hpattern
    lineListIsPairThin_threeLines

/-- The K4 stratum forces primitivity. -/
theorem isPrimitiveDesign_of_kFourPattern (design : WeightedDesign 6 3)
    (hpattern : HasLinePattern design
      (lineFamilyPattern [[(0 : Fin 6), 1, 2], [0, 3, 4], [1, 3, 5], [2, 4, 5]])) :
    IsPrimitiveDesign design :=
  isPrimitiveDesign_of_hasLinePattern_lineFamily design _ hpattern lineListIsPairThin_kFour

end Gtz
