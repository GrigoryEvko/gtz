/-
# A size-generic relabelling kit, and the seven-point enumeration peeled by
# its longest line

`Gtz.LinearSpaceListIsComplete 7 linePatternListSeven` is the combinatorial input
of `Gtz.hingeHoldsAtSize_of_linearSpaceEnumeration_sevenThree`.  Its six-point
sibling is a theorem; this file attacks the seven-point statement with machinery
that is generic in the number of labels.

## The kit

`Gtz.Design.LinePatternSixCases` manufactures its `Equiv.Perm (Fin 6)` from a
tabulated `![...]` of six named labels, injective through fifteen explicit
disequalities and a forty-nine-way `fin_cases`.  That shape does not survive a
change of size: seven labels want twenty-one disequalities and a
sixty-four-way split, and the line whose labels are being named has a length
that varies from class to class.

`labelOrdering` replaces the tabulation.  It takes the line as a LIST, appends
every label the line omits, and reads the result as a permutation: index `i`
names the `i`-th label.  Injectivity comes from one `Nodup` fact rather than
from a quadratic pile of disequalities, and the length is forced by the list
exhausting `Fin size`.  Nothing in the kit mentions a numeral or a size.

* `labelOrdering`, `labelOrderingMap` — the ordering and the map it tabulates;
* `nodup_labelOrdering`, `length_labelOrdering` — the ordering is a
  repetition-free enumeration of every label;
* `injective_labelOrderingMap`, `map_finRange_labelOrderingMap` — the map is
  injective and tabulates to the ordering itself;
* `map_take_labelOrderingMap` — the canonical prefix `[0, 1, ..., k-1]` maps
  onto the line, which is the identity that lets a class name its own labels;
* `exists_relabel_agreesOnDistinctTriples_of_lines` — the case closer for an
  arbitrary injective map, generalizing the six-label
  `Gtz.exists_relabel_agreesOnDistinctTriples_of_labelledFamily`;
* `exists_relabel_agreesOnDistinctTriples_singleLine` — ONE theorem for a
  pattern whose dependent triples all lie inside a single line, at any size and
  ANY line length.  The shipped tree carries three separate lemmas for lengths
  three, four and five and no statement covering all of them.

## The seven-point peel

`linearSpaceListIsComplete_seven_of_multiLineCases` cuts
`Gtz.LinearSpaceListIsComplete 7 linePatternListSeven` down to
`LinearSpaceMultiLineCasesSeven`, the classes carrying two or more long lines.
Five of the twenty-three catalogue classes fall out of the cut, ordered by
longest line: `#0` with no dependent triple, `#1` with a three-point line, `#14`
with a four-point line, `#20` with a five-point line, and `#22`, the near pencil,
with a six-point line.  All five go through the single-line theorem, which is
why they cost one branch each rather than one file each.

The residual is eighteen classes: `#2`-`#13` (every line has three points, at
least two of them), `#15`-`#19` (a four-point line and more), and `#21` (a
five-point line and a three-point line).  It is stated as a single `Prop` and
is NOT discharged here.

## Measured, not assumed

An independent enumeration of every spanning partial linear space, by
depth-first search over the dependent-triple set under the constraint that each
four-subset carries `0`, `1` or `4` dependent triples, then partitioned into
`S_n` orbits, reproduces `2, 4, 9, 23` isomorphism classes at four through seven
labels and `352`, `8389` labelled solutions at six and seven.  Both shipped
lists are complete and irredundant against it, entry by entry, and the
dependent-triple vectors agree with the counts recorded in
`Gtz.Design.LinePatternEnumeration`.  So the seven-point statement is true and
the only question is its proof.

## Cited, not reproved

`Gtz.LinePattern`, `Gtz.AgreesOnDistinctTriples`,
`Gtz.IsSpanningLinearSpacePattern`, `Gtz.lineFamilyPattern`,
`Gtz.lineFamiliesSeven`, `Gtz.linePatternListSeven`,
`Gtz.LinearSpaceListIsComplete`, `Gtz.lineFamilyPattern_map_iff`,
`Gtz.agreesOnDistinctTriples_lineFamilyPattern_of_sound_complete`,
`Gtz.agreesOnDistinctTriples_nearPencil_of_forall_pattern_off_pole`,
`Gtz.nearPencilLinePattern`, `Gtz.nearPencilLinePattern_comp_swap_iff`,
`Gtz.forall_mem_threePointLine_pattern`, `Gtz.forall_mem_fourPointLine_pattern`.
-/
import Mathlib
import Gtz.Core.Basic
import Gtz.Design.PrimitiveTightClassification
import Gtz.Design.StratumEmptinessLedger
import Gtz.Design.NearPencilStrictDomination
import Gtz.Design.LinePatternEnumeration
import Gtz.Design.LinePatternSixCases

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option maxRecDepth 100000

namespace Gtz

/-! ## The ordering named by a line

A structural case names a long line and then has to hand the enumeration a
permutation carrying the canonical prefix `[0, 1, ..., k-1]` onto that line.
`labelOrdering` builds the permutation as a LIST — the line, then everything it
omits — so the whole bridge rests on one `Nodup` fact. -/

/-- The labels of `line` in order, followed by every label the line omits. -/
def labelOrdering {size : ℕ} (line : List (Fin size)) : List (Fin size) :=
  line ++ (List.finRange size).filter (fun label => decide (label ∉ line))

/-- Every label occurs in the ordering: it is in the line or in the remainder. -/
theorem mem_labelOrdering {size : ℕ} (line : List (Fin size)) (label : Fin size) :
    label ∈ labelOrdering line := by
  by_cases hmem : label ∈ line
  · exact List.mem_append_left _ hmem
  · exact List.mem_append_right _ (List.mem_filter.mpr ⟨by simp, by simpa using hmem⟩)

/-- The ordering repeats no label: the line is repetition-free by hypothesis, the
remainder by construction, and the two are disjoint by the filter. -/
theorem nodup_labelOrdering {size : ℕ} {line : List (Fin size)} (hnodup : line.Nodup) :
    (labelOrdering line).Nodup := by
  refine List.Nodup.append hnodup ((List.nodup_finRange size).filter _) ?_
  intro label hlineMem hfilterMem
  have homitted : label ∉ line := by simpa using (List.mem_filter.mp hfilterMem).2
  exact homitted hlineMem

/-- The ordering exhausts the labels. -/
theorem toFinset_labelOrdering {size : ℕ} (line : List (Fin size)) :
    (labelOrdering line).toFinset = Finset.univ :=
  Finset.eq_univ_of_forall fun label => List.mem_toFinset.mpr (mem_labelOrdering line label)

/-- A repetition-free enumeration of every label has exactly `size` entries. -/
theorem length_labelOrdering {size : ℕ} {line : List (Fin size)} (hnodup : line.Nodup) :
    (labelOrdering line).length = size := by
  rw [← List.toFinset_card_of_nodup (nodup_labelOrdering hnodup), toFinset_labelOrdering]
  simp

/-- **The relabelling named by a line.**  Index `i` is the `i`-th label of the
ordering, so the canonical prefix lands on the line and the rest lands on its
complement.  Total by construction: out-of-range indices fall back on themselves,
which never happens once `Gtz.length_labelOrdering` applies. -/
def labelOrderingMap {size : ℕ} (line : List (Fin size)) : Fin size → Fin size :=
  fun index => (labelOrdering line).getD index.val index

/-- Every index is in range once the ordering exhausts the labels. -/
theorem lt_length_labelOrdering {size : ℕ} {line : List (Fin size)} (hnodup : line.Nodup)
    (index : Fin size) : index.val < (labelOrdering line).length := by
  rw [length_labelOrdering hnodup]
  exact index.isLt

/-- Inside range the fallback never fires. -/
theorem labelOrderingMap_apply {size : ℕ} {line : List (Fin size)} (hnodup : line.Nodup)
    (index : Fin size) :
    labelOrderingMap line index =
      (labelOrdering line)[index.val]'(lt_length_labelOrdering hnodup index) :=
  List.getD_eq_getElem _ _ _

/-- **The map tabulates to the ordering.**  Reading the map at `0, 1, ...` in
turn returns the ordering itself, which is the identity every statement below
runs on. -/
theorem map_finRange_labelOrderingMap {size : ℕ} {line : List (Fin size)}
    (hnodup : line.Nodup) :
    (List.finRange size).map (labelOrderingMap line) = labelOrdering line := by
  refine List.ext_getElem (by simp [length_labelOrdering hnodup]) ?_
  intro index hleftBound hrightBound
  rw [List.getElem_map, labelOrderingMap_apply hnodup]
  congr 1
  simp

/-- **The canonical prefix names the line.**  This is the identity that lets a
case hand the enumeration `[0, 1, ..., k-1]` while reasoning about its own
labels. -/
theorem map_take_labelOrderingMap {size : ℕ} {line : List (Fin size)}
    (hnodup : line.Nodup) :
    ((List.finRange size).take line.length).map (labelOrderingMap line) = line := by
  calc ((List.finRange size).take line.length).map (labelOrderingMap line)
      = ((List.finRange size).map (labelOrderingMap line)).take line.length := by
        rw [List.map_take]
    _ = (labelOrdering line).take line.length := by rw [map_finRange_labelOrderingMap hnodup]
    _ = line := List.take_left' rfl

/-- **The map is injective**, from the single fact that the ordering repeats no
label. -/
theorem injective_labelOrderingMap {size : ℕ} {line : List (Fin size)}
    (hnodup : line.Nodup) : Function.Injective (labelOrderingMap line) := by
  intro leftIndex rightIndex hequal
  have hnodupTabulation : ((List.finRange size).map (labelOrderingMap line)).Nodup := by
    rw [map_finRange_labelOrderingMap hnodup]
    exact nodup_labelOrdering hnodup
  exact List.inj_on_of_nodup_map hnodupTabulation (by simp) (by simp) hequal

/-! ## The case closer, size-generic

`Gtz.exists_relabel_agreesOnDistinctTriples_of_labelledFamily` does this at six
labels for the tabulated six-label map.  Nothing in the argument needs either
restriction: any injective self-map of a finite type is a permutation, and
`Gtz.lineFamilyPattern_map_iff` is already size-generic. -/

/-- **The case closer.**  Agreement with a family whose labels are named through
an injective map becomes agreement with the unnamed family after relabelling. -/
theorem exists_relabel_agreesOnDistinctTriples_of_lines {size : ℕ}
    {pattern : LinePattern size} {labelMap : Fin size → Fin size}
    (hinjective : Function.Injective labelMap) (lines : List (List (Fin size)))
    (hagree : AgreesOnDistinctTriples pattern
      (lineFamilyPattern (lines.map (List.map labelMap)))) :
    ∃ relabel : Equiv.Perm (Fin size), AgreesOnDistinctTriples pattern
      (fun leftLabel midLabel rightLabel =>
        lineFamilyPattern lines (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  classical
  refine ⟨(Equiv.ofBijective labelMap (Finite.injective_iff_bijective.mp hinjective)).symm,
    fun leftLabel midLabel rightLabel hleftMid hleftRight hmidRight =>
      (hagree leftLabel midLabel rightLabel hleftMid hleftRight hmidRight).trans ?_⟩
  exact lineFamilyPattern_map_iff lines
    (Equiv.ofBijective labelMap (Finite.injective_iff_bijective.mp hinjective))
    leftLabel midLabel rightLabel

/-- **One theorem for every single-line class, at every size and every line
length.**  A pattern whose dependent distinct triples are exactly those inside
one repetition-free line is the canonical prefix of that length, after
relabelling.  The shipped tree covers lengths three, four and five by three
separate lemmas at fixed label counts; this covers all lengths at all sizes. -/
theorem exists_relabel_agreesOnDistinctTriples_singleLine {size : ℕ}
    {pattern : LinePattern size} (line : List (Fin size)) (hnodup : line.Nodup)
    (hsound : ∀ leftLabel ∈ line, ∀ midLabel ∈ line, ∀ rightLabel ∈ line,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel)
    (hcomplete : ∀ leftLabel midLabel rightLabel : Fin size,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel →
          leftLabel ∈ line ∧ midLabel ∈ line ∧ rightLabel ∈ line) :
    ∃ relabel : Equiv.Perm (Fin size), AgreesOnDistinctTriples pattern
      (fun leftLabel midLabel rightLabel =>
        lineFamilyPattern [(List.finRange size).take line.length]
          (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  refine exists_relabel_agreesOnDistinctTriples_of_lines (injective_labelOrderingMap hnodup)
    [(List.finRange size).take line.length] ?_
  have hnamed : ([(List.finRange size).take line.length].map
      (List.map (labelOrderingMap line))) = [line] := by
    rw [List.map_cons, List.map_nil, map_take_labelOrderingMap hnodup]
  rw [hnamed]
  refine agreesOnDistinctTriples_lineFamilyPattern_of_sound_complete [line] ?_ ?_
  · intro someLine hsomeLine
    have hlineEq : someLine = line := by simpa using hsomeLine
    subst hlineEq
    exact hsound
  · intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
    obtain ⟨hleftMem, hmidMem, hrightMem⟩ :=
      hcomplete leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
    exact ⟨line, by simp, hleftMem, hmidMem, hrightMem⟩

/-! ## How long a covering line can be

A line carrying every dependent triple is pinned between three labels and all
but one: it holds a dependent triple, so it has at least three labels, and if it
held every label then soundness would make every distinct triple dependent,
which spanning forbids.  Both bounds are size-generic and both are what turns
the single-line theorem into a finite case split on the line's length. -/

/-- A repetition-free line holding three distinct labels has at least three. -/
theorem three_le_length_of_memTriple {size : ℕ} {line : List (Fin size)}
    (hnodup : line.Nodup) {seedLeft seedMid seedRight : Fin size}
    (hleftMid : seedLeft ≠ seedMid) (hleftRight : seedLeft ≠ seedRight)
    (hmidRight : seedMid ≠ seedRight) (hleftMem : seedLeft ∈ line)
    (hmidMem : seedMid ∈ line) (hrightMem : seedRight ∈ line) : 3 ≤ line.length := by
  classical
  have hsubset : ({seedLeft, seedMid, seedRight} : Finset (Fin size)) ⊆ line.toFinset := by
    intro label hlabel
    simp only [Finset.mem_insert, Finset.mem_singleton] at hlabel
    rcases hlabel with rfl | rfl | rfl
    · exact List.mem_toFinset.mpr hleftMem
    · exact List.mem_toFinset.mpr hmidMem
    · exact List.mem_toFinset.mpr hrightMem
  have hcardTriple : ({seedLeft, seedMid, seedRight} : Finset (Fin size)).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [hleftMid, hleftRight]),
      Finset.card_insert_of_notMem (by simp [hmidRight]), Finset.card_singleton]
  calc 3 = ({seedLeft, seedMid, seedRight} : Finset (Fin size)).card := hcardTriple.symm
    _ ≤ line.toFinset.card := Finset.card_le_card hsubset
    _ = line.length := List.toFinset_card_of_nodup hnodup

/-- **A sound line omits a label.**  Were it to hold every label, soundness would
make every distinct triple dependent and the pattern would not span. -/
theorem length_lt_size_of_soundLine {size : ℕ} {pattern : LinePattern size}
    {line : List (Fin size)} (hnodup : line.Nodup)
    (haxioms : IsSpanningLinearSpacePattern pattern)
    (hsound : ∀ leftLabel ∈ line, ∀ midLabel ∈ line, ∀ rightLabel ∈ line,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel) : line.length < size := by
  classical
  obtain ⟨witnessLeft, witnessMid, witnessRight, hleftMid, hleftRight, hmidRight,
    hnotPattern⟩ := haxioms.isSpanning
  have hcard : line.toFinset.card = line.length := List.toFinset_card_of_nodup hnodup
  have hle : line.length ≤ size := by
    rw [← hcard]
    simpa using Finset.card_le_univ line.toFinset
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exfalso
    have huniv : line.toFinset = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [hcard, heq]; simp)
    have hmem : ∀ label : Fin size, label ∈ line := by
      intro label
      have hinFinset : label ∈ line.toFinset := by
        rw [huniv]
        exact Finset.mem_univ label
      exact List.mem_toFinset.mp hinFinset
    exact hnotPattern (hsound witnessLeft (hmem _) witnessMid (hmem _) witnessRight (hmem _)
      hleftMid hleftRight hmidRight)

/-! ## Seven labels

`Gtz.lineFamiliesSeven` lists the twenty-three classes.  Five of them carry at
most one long line: `#0` none, then `#1`, `#14`, `#20` and `#22` with lines of
three, four, five and six labels.  Those five are the canonical prefixes of
`Gtz.List.finRange 7`, so the single-line theorem closes all five at once and the
near pencil `#22` needs no separate treatment — its covering line is the
complement of its pole. -/

/-- The line-free entry is in the seven-label list. -/
theorem lineFree_mem_linePatternListSeven :
    lineFamilyPattern (size := 7) [] ∈ linePatternListSeven :=
  List.mem_map.mpr ⟨[], by decide, rfl⟩

/-- Every canonical prefix of length three through six is a listed family: these
are catalogue `#1`, `#14`, `#20` and `#22`. -/
theorem canonicalPrefix_mem_lineFamiliesSeven (lineLength : ℕ)
    (hlower : 3 ≤ lineLength) (hupper : lineLength < 7) :
    [(List.finRange 7).take lineLength] ∈ lineFamiliesSeven := by
  interval_cases lineLength <;> decide

/-- **Catalogue `#0` at seven labels.**  A pattern with no dependent distinct
triple is the line-free entry, with the identity relabelling. -/
theorem linearSpaceListIsComplete_seven_lineFreeCase {pattern : LinePattern 7}
    (hlineFree : ∀ leftLabel midLabel rightLabel : Fin 7,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        ¬ pattern leftLabel midLabel rightLabel) :
    ∃ basePattern ∈ linePatternListSeven, ∃ relabel : Equiv.Perm (Fin 7),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  refine ⟨lineFamilyPattern [], lineFree_mem_linePatternListSeven, Equiv.refl _,
    agreesOnDistinctTriples_of_forall fun leftLabel midLabel rightLabel hleftMid hleftRight
      hmidRight => ⟨fun hpattern => absurd hpattern
        (hlineFree leftLabel midLabel rightLabel hleftMid hleftRight hmidRight), ?_⟩⟩
  rintro ⟨line, hline, -⟩
  exact absurd hline (by simp)

/-- **Catalogue `#1`, `#14`, `#20` and `#22`, closed together.**  A pattern whose
dependent distinct triples all lie inside one repetition-free line, and which has
at least one of them, is a listed entry after relabelling.  Which entry is
decided by the line's length, and the length is pinned to three, four, five or
six by the two bounds above. -/
theorem linearSpaceListIsComplete_seven_singleLineCase {pattern : LinePattern 7}
    (haxioms : IsSpanningLinearSpacePattern pattern) (line : List (Fin 7))
    (hnodup : line.Nodup)
    (hsound : ∀ leftLabel ∈ line, ∀ midLabel ∈ line, ∀ rightLabel ∈ line,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel)
    (hcomplete : ∀ leftLabel midLabel rightLabel : Fin 7,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel →
          leftLabel ∈ line ∧ midLabel ∈ line ∧ rightLabel ∈ line)
    (seedLeft seedMid seedRight : Fin 7) (hseedLeftMid : seedLeft ≠ seedMid)
    (hseedLeftRight : seedLeft ≠ seedRight) (hseedMidRight : seedMid ≠ seedRight)
    (hseed : pattern seedLeft seedMid seedRight) :
    ∃ basePattern ∈ linePatternListSeven, ∃ relabel : Equiv.Perm (Fin 7),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  obtain ⟨hleftMem, hmidMem, hrightMem⟩ :=
    hcomplete seedLeft seedMid seedRight hseedLeftMid hseedLeftRight hseedMidRight hseed
  have hlower : 3 ≤ line.length := three_le_length_of_memTriple hnodup hseedLeftMid
    hseedLeftRight hseedMidRight hleftMem hmidMem hrightMem
  have hupper : line.length < 7 := length_lt_size_of_soundLine hnodup haxioms hsound
  obtain ⟨relabel, hrelabel⟩ :=
    exists_relabel_agreesOnDistinctTriples_singleLine line hnodup hsound hcomplete
  exact ⟨lineFamilyPattern [(List.finRange 7).take line.length],
    List.mem_map.mpr ⟨[(List.finRange 7).take line.length],
      canonicalPrefix_mem_lineFamiliesSeven line.length hlower hupper, rfl⟩, relabel, hrelabel⟩

/-! ## The residual: the eighteen classes with two or more long lines

What survives the cut is a pattern carrying a dependent triple for which NO
repetition-free line is both sound and covering — equivalently, a pattern with
at least two long lines.  That is catalogue `#2`-`#13` (every line three points,
at least two lines), `#15`-`#19` (a four-point line and more) and `#21` (a
five-point line meeting a three-point line): eighteen of the twenty-three
classes.  It is UNDISCHARGED. -/

/-- The eighteen open seven-label classes, stated so that a prover may assume a
dependent triple exists and that every sound line misses one. -/
def LinearSpaceMultiLineCasesSeven : Prop :=
  ∀ pattern : LinePattern 7, IsSpanningLinearSpacePattern pattern →
    (∃ seedLeft seedMid seedRight : Fin 7, seedLeft ≠ seedMid ∧ seedLeft ≠ seedRight ∧
      seedMid ≠ seedRight ∧ pattern seedLeft seedMid seedRight) →
    (∀ line : List (Fin 7), line.Nodup →
      (∀ leftLabel ∈ line, ∀ midLabel ∈ line, ∀ rightLabel ∈ line,
        leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
          pattern leftLabel midLabel rightLabel) →
      ∃ outsideLeft outsideMid outsideRight : Fin 7, outsideLeft ≠ outsideMid ∧
        outsideLeft ≠ outsideRight ∧ outsideMid ≠ outsideRight ∧
          pattern outsideLeft outsideMid outsideRight ∧
            ¬ (outsideLeft ∈ line ∧ outsideMid ∈ line ∧ outsideRight ∈ line)) →
    ∃ basePattern ∈ linePatternListSeven, ∃ relabel : Equiv.Perm (Fin 7),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel))

/-- **The seven-point enumeration, cut to eighteen classes.**  CONDITIONAL on the
residual, which is not proved anywhere.  What this contributes is the two-way
peel — no dependent triple, or one line carrying all of them — which discharges
catalogue `#0`, `#1`, `#14`, `#20` and `#22` through one theorem. -/
theorem linearSpaceListIsComplete_seven_of_multiLineCases
    (hmulti : LinearSpaceMultiLineCasesSeven) :
    LinearSpaceListIsComplete 7 linePatternListSeven := by
  classical
  intro pattern haxioms
  by_cases hlineFree : ∀ leftLabel midLabel rightLabel : Fin 7,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        ¬ pattern leftLabel midLabel rightLabel
  · exact linearSpaceListIsComplete_seven_lineFreeCase hlineFree
  · push Not at hlineFree
    obtain ⟨seedLeft, seedMid, seedRight, hseedLeftMid, hseedLeftRight, hseedMidRight,
      hseed⟩ := hlineFree
    by_cases hcovered : ∃ line : List (Fin 7), line.Nodup ∧
        (∀ leftLabel ∈ line, ∀ midLabel ∈ line, ∀ rightLabel ∈ line,
          leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
            pattern leftLabel midLabel rightLabel) ∧
        (∀ leftLabel midLabel rightLabel : Fin 7,
          leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
            pattern leftLabel midLabel rightLabel →
              leftLabel ∈ line ∧ midLabel ∈ line ∧ rightLabel ∈ line)
    · obtain ⟨line, hnodup, hsound, hcomplete⟩ := hcovered
      exact linearSpaceListIsComplete_seven_singleLineCase haxioms line hnodup hsound hcomplete
        seedLeft seedMid seedRight hseedLeftMid hseedLeftRight hseedMidRight hseed
    · refine hmulti pattern haxioms ⟨seedLeft, seedMid, seedRight, hseedLeftMid,
        hseedLeftRight, hseedMidRight, hseed⟩ ?_
      intro line hnodup hsound
      by_contra hnoOutside
      refine hcovered ⟨line, hnodup, hsound, ?_⟩
      intro leftLabel midLabel rightLabel hleftMid hleftRight hmidRight hpattern
      by_contra houtside
      exact hnoOutside ⟨leftLabel, midLabel, rightLabel, hleftMid, hleftRight, hmidRight,
        hpattern, houtside⟩

/-- **The seven-point hinge from the multi-line residual.**  The combinatorial
input of `Gtz.hingeHoldsAtSize_of_linearSpaceEnumeration_sevenThree` is weakened
from all twenty-three classes to the eighteen carrying two or more lines.  The
other two inputs are untouched: the open `Gtz.GtzWeighted 6 3` that buys the
leverage floor, and the twenty-one tie-freeness obligations. -/
theorem hingeHoldsAtSize_sevenThree_of_multiLineCases (hsixThree : GtzWeighted 6 3)
    (hmulti : LinearSpaceMultiLineCasesSeven) (hresidual : HingeStratumObligationSeven) :
    HingeHoldsAtSize 7 3 :=
  hingeHoldsAtSize_of_linearSpaceEnumeration_sevenThree hsixThree
    (linearSpaceListIsComplete_seven_of_multiLineCases hmulti) hresidual

/-! ## The same peel at six labels

The kit is generic, so the six-point instance costs a length bound and nothing
else.  `Gtz.Design.LinePatternSixCases` reaches the same four classes — `#0`,
`#1`, `#6` and `#8` — through a tabulated six-label permutation, fifteen
disequalities, two complement helpers and three soundness lemmas at fixed line
widths.  Below, the four fall out of one theorem.  This is a cross-check on the
kit rather than a new result: six labels are already closed unconditionally by
`Gtz.linearSpaceListIsComplete_six`. -/

/-- Every canonical prefix of length three through five is a listed six-label
family: catalogue `#1`, `#6` and `#8`. -/
theorem canonicalPrefix_mem_lineFamiliesSix (lineLength : ℕ)
    (hlower : 3 ≤ lineLength) (hupper : lineLength < 6) :
    [(List.finRange 6).take lineLength] ∈ lineFamiliesSix := by
  interval_cases lineLength <;> decide

/-- **Catalogue `#1`, `#6` and `#8` at six labels, from the generic kit.**  The
near pencil `#8` needs no separate pole argument here: its covering line is the
complement of the pole, and the length bound sends it to the right entry. -/
theorem linearSpaceListIsComplete_six_coveringLineCase {pattern : LinePattern 6}
    (haxioms : IsSpanningLinearSpacePattern pattern) (line : List (Fin 6))
    (hnodup : line.Nodup)
    (hsound : ∀ leftLabel ∈ line, ∀ midLabel ∈ line, ∀ rightLabel ∈ line,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel)
    (hcomplete : ∀ leftLabel midLabel rightLabel : Fin 6,
      leftLabel ≠ midLabel → leftLabel ≠ rightLabel → midLabel ≠ rightLabel →
        pattern leftLabel midLabel rightLabel →
          leftLabel ∈ line ∧ midLabel ∈ line ∧ rightLabel ∈ line)
    (seedLeft seedMid seedRight : Fin 6) (hseedLeftMid : seedLeft ≠ seedMid)
    (hseedLeftRight : seedLeft ≠ seedRight) (hseedMidRight : seedMid ≠ seedRight)
    (hseed : pattern seedLeft seedMid seedRight) :
    ∃ basePattern ∈ linePatternListSix, ∃ relabel : Equiv.Perm (Fin 6),
      AgreesOnDistinctTriples pattern (fun leftLabel midLabel rightLabel =>
        basePattern (relabel leftLabel) (relabel midLabel) (relabel rightLabel)) := by
  obtain ⟨hleftMem, hmidMem, hrightMem⟩ :=
    hcomplete seedLeft seedMid seedRight hseedLeftMid hseedLeftRight hseedMidRight hseed
  have hlower : 3 ≤ line.length := three_le_length_of_memTriple hnodup hseedLeftMid
    hseedLeftRight hseedMidRight hleftMem hmidMem hrightMem
  have hupper : line.length < 6 := length_lt_size_of_soundLine hnodup haxioms hsound
  obtain ⟨relabel, hrelabel⟩ :=
    exists_relabel_agreesOnDistinctTriples_singleLine line hnodup hsound hcomplete
  exact ⟨lineFamilyPattern [(List.finRange 6).take line.length],
    List.mem_map.mpr ⟨[(List.finRange 6).take line.length],
      canonicalPrefix_mem_lineFamiliesSix line.length hlower hupper, rfl⟩, relabel, hrelabel⟩

/-! ## The peel is exactly the shipped one

At six labels the entries with at most one line are catalogue `#0`, `#1`, `#6`
and `#8`, and the five with two or more are `#2`-`#5` and `#7` — precisely the
five-class residual of `Gtz.Design.LinePatternSixCases`.  At seven labels the
split is five against eighteen.  Both counts are decided, not asserted. -/

example : (lineFamiliesSix.filter (fun lines => decide (lines.length ≤ 1))).length = 4 := by
  decide

example : (lineFamiliesSix.filter (fun lines => decide (2 ≤ lines.length))).length = 5 := by
  decide

example : (lineFamiliesSeven.filter (fun lines => decide (lines.length ≤ 1))).length = 5 := by
  decide

example : (lineFamiliesSeven.filter (fun lines => decide (2 ≤ lines.length))).length = 18 := by
  decide

/-- The near pencil at seven labels IS the canonical six-label prefix, so the
single-line theorem reaches catalogue `#22` with no pole argument. -/
example : nearPencilSevenFamily = [(List.finRange 7).take 6] := by decide

/-- The near pencil at six labels IS the canonical five-label prefix. -/
example : nearPencilSixFamily = [(List.finRange 6).take 5] := by decide

end Gtz
